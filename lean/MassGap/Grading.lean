import MassGap.Steinberg
import MassGap.Row
import MassGap.Adjchar
import MassGap.Channels
import MassGap.Stableentries
/-!
`lem:grading` — the tower rows repeat off the collar.  The collar
is the label set at a consecutive row-list gap below two, its read
`collarAt` the occupancy fold (`con:places`: the occupancies are
the row list's consecutive gaps), and the deep-row read `rowRead`
is the tie's gap of the target's display against the label's read
at `lem:adjchar`'s content formula — the one row the adjoint's
content list, the sum's unit at an absent tie.  The theorem
`deepRow` closes the display `N^{λ+ν}_{θλ} = mult_θ(ν)` at every
label off the collar at the declared count's frame `2 ≤ d`
(`con:places`, the fundamental count the residue's successor):
every place permutation but the identity drops from
`cor:steinberg`'s graded sum, since a label off the collar reads
its display gaps at three or beyond while an adjoint content's
entries sit at or below two, so a permuted display's reversed
adjacent pair survives every content move against the strictly
decreasing target display; the identity's tie is the row, on the
even side.  On the collar the walk's own diagonal differs, the
`θ`-support count against the residue (`prop:row`).
-/

namespace grading
open ground places

/-- The collar read: a consecutive row-list gap below two — the
occupancy read at a key below the top, the occupancies the row
list's consecutive gaps (`con:places`). -/
def collarAt (s : Shape) : Prop :=
  ((List.range (s.length - 1)).any (fun i => ground.getAt 0 s i < 2))
    = true

instance (s : Shape) : Decidable (collarAt s) :=
  inferInstanceAs (Decidable (_ = _))

/-- The deep row's read: the tie's gap at `lem:adjchar`'s content
formula, the one row the adjoint's content list, the sum's unit at
an absent tie. -/
def rowRead (d : Nat) (lam c : Shape) : Nat :=
  match ground.tieGap (places.display c) (places.display lam) with
  | some m => adjchar.multRead d m
  | none => 0

/-- A label off the collar reads every consecutive occupancy at two
or beyond. -/
private theorem deep_read (s : Shape) (hdeep : ¬ collarAt s) :
    ∀ i, i + 1 < s.length → 2 ≤ ground.getAt 0 s i := by
  intro i hi
  have hfalse : ((List.range (s.length - 1)).any
      (fun i => ground.getAt 0 s i < 2)) = false := by
    cases hany : ((List.range (s.length - 1)).any
        (fun i => ground.getAt 0 s i < 2)) with
    | false => rfl
    | true => exact absurd hany hdeep
  have hpos : 0 < s.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le (i + 1)) hi
  have hlen : s.length - 1 + 1 = s.length :=
    Nat.succ_pred_eq_of_pos hpos
  have hi' : i < s.length - 1 :=
    Nat.lt_of_succ_lt_succ
      (show i + 1 < (s.length - 1) + 1 from by rw [hlen]; exact hi)
  have hall := ground.all_range_read (s.length - 1)
    (ground.all_not_of_any_false _ _ hfalse) i hi'
  cases Nat.lt_or_ge (ground.getAt 0 s i) 2 with
  | inl hlt =>
    rw [decide_eq_true hlt] at hall
    exact Bool.noConfusion hall
  | inr hge => exact hge

/-- Off the collar the display's consecutive gap clears three. -/
private theorem deep_gap (lam : Shape) (hdeep : ¬ collarAt lam) :
    ∀ i, i + 1 < lam.length →
    ground.getAt 0 (display lam) (i + 1) + 3
      ≤ ground.getAt 0 (display lam) i := by
  intro i hi
  have hocc := deep_read lam hdeep i hi
  have hd1 : ground.getAt 0 (display lam) i
      = ground.getAt 0 (rowList lam) i + (lam.length - i) :=
    getAt_display lam i (Nat.lt_of_succ_lt hi)
  have hd2 : ground.getAt 0 (display lam) (i + 1)
      = ground.getAt 0 (rowList lam) (i + 1)
        + (lam.length - (i + 1)) :=
    getAt_display lam (i + 1) hi
  have hsub : lam.length - i = (lam.length - (i + 1)) + 1 := by
    have hgi : (i + 1) + (lam.length - (i + 1)) = lam.length :=
      ground.natAddSubCancel (Nat.le_of_lt hi)
    have hii : i + (lam.length - i) = lam.length :=
      ground.natAddSubCancel (Nat.le_of_lt (Nat.lt_of_succ_lt hi))
    refine ground.addCancelL i ?_
    have hsw : i + ((lam.length - (i + 1)) + 1)
        = (i + 1) + (lam.length - (i + 1)) := by
      rw [Nat.add_comm (lam.length - (i + 1)) 1,
        ← Nat.add_assoc i 1 (lam.length - (i + 1))]
    rw [hii, hsw, hgi]
  have hjoin : ground.getAt 0 (display lam) i
      = ground.getAt 0 (display lam) (i + 1)
        + (ground.getAt 0 lam i + 1) := by
    rw [hd1, hd2, hsub,
      rowList_gap lam i (Nat.lt_of_succ_lt hi)]
    rw [Nat.add_assoc (ground.getAt 0 lam i)
        (ground.getAt 0 (rowList lam) (i + 1))
        ((lam.length - (i + 1)) + 1),
      Nat.add_comm (ground.getAt 0 lam i)
        (ground.getAt 0 (rowList lam) (i + 1)
          + ((lam.length - (i + 1)) + 1)),
      Nat.add_assoc (ground.getAt 0 (rowList lam) (i + 1))
        ((lam.length - (i + 1)) + 1) (ground.getAt 0 lam i),
      Nat.add_assoc (lam.length - (i + 1)) 1 (ground.getAt 0 lam i),
      Nat.add_comm 1 (ground.getAt 0 lam i),
      ← Nat.add_assoc (ground.getAt 0 (rowList lam) (i + 1))
        (lam.length - (i + 1)) (ground.getAt 0 lam i + 1)]
  rw [hjoin]
  refine Nat.add_le_add_left ?_ _
  exact Nat.succ_le_succ hocc

/-- The deep gap chains across every index pair: a later place's
display clears an earlier's by three. -/
private theorem deep_chain (lam : Shape) (hdeep : ¬ collarAt lam)
    (i j : Nat) (hij : i < j) (hj : j < lam.length) :
    ground.getAt 0 (display lam) j + 3
      ≤ ground.getAt 0 (display lam) i := by
  cases Nat.eq_or_lt_of_le hij with
  | inl he =>
    have hstep := deep_gap lam hdeep i
      (show i + 1 < lam.length from by
        rw [show i + 1 = j from he]
        exact hj)
    rw [← show i + 1 = j from he]
    exact hstep
  | inr hlt =>
    have hstep := deep_gap lam hdeep i (Nat.lt_trans hlt hj)
    have hdesc : ground.getAt 0 (display lam) j
        < ground.getAt 0 (display lam) (i + 1) :=
      desc_lt (fun k hk =>
          display_desc lam k (by rw [length_display] at hk; exact hk))
        j (i + 1) hlt (by rw [length_display]; exact hj)
    exact Nat.le_trans
      (Nat.add_le_add_right (Nat.le_of_lt hdesc) 3) hstep

private theorem exclusion (d : Nat) (lam c : Shape)
    (hld : lam.length = d) (hcd : c.length = d)
    (hdeep : ¬ collarAt lam) (p : List Nat)
    (hp : 0 < ground.countOf p
      (monomialsAt (List.replicate d 1)))
    (hne : p ≠ List.range d) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (p.map (ground.getAt 0 (places.display lam))) = some m) :
    adjchar.multRead d m = 0 := by
  match Nat.eq_zero_or_pos (adjchar.multRead d m) with
  | Or.inl hz => exact hz
  | Or.inr hpos =>
    obtain ⟨hent, _⟩ := adjchar.multRead_flat d m hpos
    obtain ⟨hplen, hdist, hval, _⟩ := perm_member_reads hp
    cases hfr : firstRev p with
    | none =>
      exact absurd (sorted_eq_range d p hplen hdist hval hfr) hne
    | some k =>
      obtain ⟨hk1, hrev⟩ := firstRev_some p k hfr
      have hkp : k < p.length := Nat.lt_of_succ_lt hk1
      have hA : ground.getAt 0 p k < d :=
        hval _ (ground.countOf_getAt_pos 0 p k hkp)
      have hq1 : ground.getAt 0
          (p.map (ground.getAt 0 (places.display lam))) k
          = ground.getAt 0 (places.display lam)
            (ground.getAt 0 p k) :=
        ground.getAt_map 0 0 _ p k hkp
      have hq2 : ground.getAt 0
          (p.map (ground.getAt 0 (places.display lam))) (k + 1)
          = ground.getAt 0 (places.display lam)
            (ground.getAt 0 p (k + 1)) :=
        ground.getAt_map 0 0 _ p (k + 1) hk1
      obtain ⟨hml, hql, hent2⟩ :=
        ground.tieGap_reads _ _ m htie
      have hcul : (places.display c).length = d := by
        rw [length_display]
        exact hcd
      have hkd : k + 1 < d := by
        rw [← hplen]
        exact hk1
      have hchain : ground.getAt 0 (places.display lam)
            (ground.getAt 0 p k) + 3
          ≤ ground.getAt 0 (places.display lam)
            (ground.getAt 0 p (k + 1)) := by
        refine deep_chain lam hdeep _ _ hrev ?_
        rw [hld]
        exact hA
      have he1 : ground.getAt 0 m k
            + ground.getAt 0
              (p.map (ground.getAt 0 (places.display lam))) k
          = ground.getAt 0 (places.display c) k := by
        refine hent2 k ?_
        rw [hcul]
        exact Nat.lt_of_succ_lt hkd
      have he2 : ground.getAt 0 m (k + 1)
            + ground.getAt 0
              (p.map (ground.getAt 0 (places.display lam))) (k + 1)
          = ground.getAt 0 (places.display c) (k + 1) := by
        refine hent2 (k + 1) ?_
        rw [hcul]
        exact hkd
      have hup : ground.getAt 0 (places.display c) k
          < ground.getAt 0 (places.display c) (k + 1) := by
        rw [← he1, ← he2, hq1, hq2]
        refine Nat.lt_of_le_of_lt (Nat.add_le_add_right
          (hent k) _) ?_
        refine Nat.lt_of_lt_of_le ?_ (Nat.le_trans hchain
          (Nat.le_add_left _ (ground.getAt 0 m (k + 1))))
        rw [Nat.add_comm 2 (ground.getAt 0 (places.display lam)
          (ground.getAt 0 p k))]
        exact Nat.lt_succ_self _
      have hdn : ground.getAt 0 (places.display c) (k + 1)
          < ground.getAt 0 (places.display c) k := by
        refine display_desc c k ?_
        rw [hcd]
        exact hkd
      exact absurd (Nat.lt_trans hup hdn)
        (Nat.lt_irrefl _)

/-- The seeded sum's pick: the family fold's read at the hoisted
seed. -/
private theorem sumsWith_deep (d : Nat) (lam c : Shape)
    (hld : lam.length = d) (hcd : c.length = d)
    (hdeep : ¬ collarAt lam) :
    steinberg.sumsWith (adjchar.multRead d) d lam c
      = (rowRead d lam c, 0) := by
  have hoff : ∀ p ∈ monomialsAt (List.replicate d 1),
      ¬ p = List.range d → ∀ acc : Nat × Nat,
      (match ground.tieGap (places.display c)
          (p.map (ground.getAt 0 (places.display lam))) with
        | none => acc
        | some m =>
          if parity p then (acc.1, acc.2 + adjchar.multRead d m)
          else (acc.1 + adjchar.multRead d m, acc.2)) = acc := by
    intro p hp hne acc
    cases htie : ground.tieGap (places.display c)
        (p.map (ground.getAt 0 (places.display lam))) with
    | none => rfl
    | some m =>
      show (if parity p then (acc.1, acc.2 + adjchar.multRead d m)
        else (acc.1 + adjchar.multRead d m, acc.2)) = acc
      rw [exclusion d lam c hld hcd hdeep p
        (ground.countOf_pos_of_mem hp) hne m htie]
      cases parity p with
      | true =>
        show ((acc.1, acc.2 + 0) : Nat × Nat) = acc
        rw [Nat.add_zero]
      | false =>
        show ((acc.1 + 0, acc.2) : Nat × Nat) = acc
        rw [Nat.add_zero]
  have hat : ∀ acc : Nat × Nat,
      (match ground.tieGap (places.display c)
          ((List.range d).map (ground.getAt 0 (places.display lam))) with
        | none => acc
        | some m =>
          if parity (List.range d) then
            (acc.1, acc.2 + adjchar.multRead d m)
          else (acc.1 + adjchar.multRead d m, acc.2))
        = (acc.1 + rowRead d lam c, acc.2) := by
    intro acc
    rw [show (List.range d).map (ground.getAt 0 (places.display lam))
        = places.display lam
      from ground.range_map_getAt 0 d (places.display lam)
        ((places.length_display lam).trans hld),
      parity_range d]
    cases htie : ground.tieGap (places.display c)
        (places.display lam) with
    | none =>
      have hz : rowRead d lam c = 0 := by
        show (match ground.tieGap (places.display c)
            (places.display lam) with
          | some m => adjchar.multRead d m
          | none => 0) = 0
        rw [htie]
      show acc = (acc.1 + rowRead d lam c, acc.2)
      rw [hz, Nat.add_zero]
    | some m =>
      have hv : rowRead d lam c = adjchar.multRead d m := by
        show (match ground.tieGap (places.display c)
            (places.display lam) with
          | some m => adjchar.multRead d m
          | none => 0) = adjchar.multRead d m
        rw [htie]
      show ((acc.1 + adjchar.multRead d m, acc.2) : Nat × Nat)
        = (acc.1 + rowRead d lam c, acc.2)
      rw [hv]
  show (monomialsAt (List.replicate d 1)).foldl
      (fun acc p =>
        match ground.tieGap (places.display c)
          (p.map (ground.getAt 0 (places.display lam))) with
        | none => acc
        | some m =>
          if parity p then (acc.1, acc.2 + adjchar.multRead d m)
          else (acc.1 + adjchar.multRead d m, acc.2))
      (0, 0) = (rowRead d lam c, 0)
  rw [ground.foldl_pick _ (List.range d)
      (fun acc => (acc.1 + rowRead d lam c, acc.2)) hat
      (monomialsAt (List.replicate d 1)) hoff
      (places.countRangePerms d) (0, 0)]
  show ((0 + rowRead d lam c, 0) : Nat × Nat) = (rowRead d lam c, 0)
  rw [Nat.zero_add]


/-- `lem:grading`'s tower display at the label calculus: off the
collar the adjoint fusion count is the content list's read at the
tie, at the declared count's frame (`con:places`) with the
identity with `def:blockcount`'s carrier (`lem:adjchar`) and
`cor:steinberg`'s display the stated reads. -/
theorem deepRow (d : Nat) (lam c : Shape)
    (hd : 2 ≤ d) (hld : lam.length = d) (hcd : c.length = d)
    (hdeep : ¬ collarAt lam) :
    blockcount.fusionCount (adjchar.theta d) lam c
      = rowRead d lam c := by
  have hth : (adjchar.theta d).length = d := by
    show (ground.bumpAt 0
      (ground.bumpAt (d - 2) (List.replicate d 0))).length = d
    rw [ground.length_bumpAt, ground.length_bumpAt,
      ground.length_replicate]
  have hst : steinberg.read (adjchar.theta d) lam c :=
    steinberg.readAll (adjchar.theta d) lam c
      (hld.trans hth.symm) (hcd.trans hth.symm)
  have hgs : steinberg.gradedSums (adjchar.theta d) lam c
      = (rowRead d lam c, 0) :=
    (channels.sumsWith_agree d lam c hd hcd).trans
      (sumsWith_deep d lam c hld hcd hdeep)
  have hst' : blockcount.fusionCount (adjchar.theta d) lam c
      + (steinberg.gradedSums (adjchar.theta d) lam c).2
      = (steinberg.gradedSums (adjchar.theta d) lam c).1 := hst
  rw [hgs] at hst'
  exact hst'

/-! The index grading: the band components with their contents and
the separation read.  A class's support decomposes at the band's
coupling — two links adjacent where one plaquette's boundary meets
both links' ends (`lem:stableentries`'s reach) — the components'
contents the electric diagonal's per-part reads, and two supports
separated beyond the band where their reach neighborhoods are
disjoint.  The pencil's rows read the grading in three shapes: the
diagonal at the content read (`carrier.contentN`), the stencil
rows at the near plaquettes with the changed edge kept off the
boundary (`stableentries.nearPlaq`; `algebra.plaqRow_keep`), and
the border rows at the far plaquettes (`stableentries.farRead`),
the created loop's corners at the unit law with the fiber
dimension multiplying over the parts
(`stableentries.fibProd_join`). -/

/-- Band adjacency: one plaquette's boundary meets both links'
ends, the coupling's own reach. -/
def bandAdj (R : lattice.Region) (l1 l2 : Nat) : Bool :=
  R.plaqs.any (fun p =>
    stableentries.nearLink R p l1 && stableentries.nearLink R p l2)

private def insertComp (R : lattice.Region) (l : Nat)
    (cs : List (List Nat)) : List (List Nat) :=
  match cs.foldl (fun nf c =>
      if c.any (fun l' => bandAdj R l l') then (nf.1 ++ c, nf.2)
      else (nf.1, nf.2 ++ [c])) (([l], []) :
        List Nat × List (List Nat)) with
  | (near, far) => near :: far

/-- The band components: the support's parts at the coupling's
closure, one fold in the key order. -/
def components {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) : List (List Nat) :=
  (carrier.support F R a).foldl (fun cs l => insertComp R l cs) []

/-- A component's content: the electric diagonal's per-part read. -/
def compContent {L : Type} (F : fusion.Data L) (a : List L)
    (c : List Nat) : Nat :=
  carrier.contentN F (c.map (ground.getAt F.unit a))

private def bandVerts {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) : List Nat :=
  (List.range R.verts).filter (fun v =>
    R.plaqs.any (fun p =>
      stableentries.nearPlaq F R a p
        && p.any (fun e =>
          lattice.startOf R e == v || lattice.endOf R e == v)))

/-- The separation read: two supports beyond the band where their
reach neighborhoods are disjoint. -/
def sepBeyond {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) : Prop :=
  ((bandVerts F R a).all (fun v =>
    !((bandVerts F R b).any (fun w => w == v)))) = true

instance {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) : Decidable (sepBeyond F R a b) :=
  inferInstanceAs (Decidable (_ = _))

/-! The member rows: at a member's weight table the adjoint fusion
row is the member's `θ` content list, `N^{λ+ν}_{θλ} = mult_θ(ν)`.
A member of the graded image list off the top key holds a positive
root whose doubled inversion pairing clears the count's successor
against the occupied square (`offTopAt`), the content magnitudes
sit at or below the count's multiple of that square (`magAt`), and
the two reads part every tie off the top: the tie's pairing splits
at the form's additivity and the ρ-length read closes the
clearance against the square's positivity.  The graded fold then
reads its one occupied member — the top, on the even side — and
the inner fold reads the content list's count at the withdrawn key
(`lem:grading`). -/

/-- The off-top read: every member off the top holds a positive
root at the doubled inversion pairing clearing the count's
successor against the square — the clearance's transport to the
orbit, the square's positivity the ρ-length read's own
(`con:sertables`; `prop:row`). -/
def offTopAt (t : gentable.Table) (F : sertables.FundData)
    (W : List (List BPair × Bool)) (K : Nat)
    (kap : List BPair) : Prop :=
  ∀ vp ∈ W, vp.1 ≠ kap →
    ∃ j, j + 1 < t.posFolds.length + 1
      ∧ BPair.add
          (BPair.add
            (sertables.dotB F vp.1 (sertables.posCorootV t j))
            (sertables.dotB F vp.1 (sertables.posCorootV t j)))
          (BPair.mul (BPair.ofNat (K + 1))
            (sertables.dotB F (sertables.posCorootV t j)
              (sertables.posCorootV t j)))
        ≤ BPair.unit

instance (t : gentable.Table) (F : sertables.FundData)
    (W : List (List BPair × Bool)) (K : Nat) (kap : List BPair) :
    Decidable (offTopAt t F W K kap) :=
  inferInstanceAs (Decidable (∀ vp ∈ W, vp.1 ≠ kap →
    ∃ j, j + 1 < t.posFolds.length + 1 ∧ _))

/-- The content magnitudes' clearance: every member's doubled
pairing at or below the count's multiple of the square — the
member's largest coroot magnitude, `lem:grading`'s cap. -/
def magAt (t : gentable.Table) (F : sertables.FundData)
    (L : List (List BPair)) (K : Nat) : Prop :=
  ∀ mu ∈ L, ∀ j, j < t.posFolds.length →
    BPair.add (sertables.dotB F mu (sertables.posCorootV t j))
        (sertables.dotB F mu (sertables.posCorootV t j))
      ≤ BPair.mul (BPair.ofNat K)
        (sertables.dotB F (sertables.posCorootV t j)
          (sertables.posCorootV t j))

instance (t : gentable.Table) (F : sertables.FundData)
    (L : List (List BPair)) (K : Nat) : Decidable (magAt t F L K) :=
  inferInstanceAs (Decidable (∀ mu ∈ L, ∀ j,
    j < t.posFolds.length → _ ≤ _))


/-- The clearance's refutation at the pairings: the tie's split
against the count's successor and the content's cap forces the
occupied square at or below the sum's unit, its positivity the
contradiction (`prop:row`'s ρ-length read). -/
private theorem clearRefute {du dmu dc drho dgg : BPair} (K : Nat)
    (hsq : BPair.unit < dgg)
    (hneg : du + du + BPair.ofNat (K + 1) * dgg ≤ BPair.unit)
    (hmg : dmu + dmu ≤ BPair.ofNat K * dgg)
    (hB : (du + dmu).oneValue (dc + drho))
    (hrl : dgg ≤ drho + drho)
    (hdc : BPair.unit ≤ dc) : False := by
  have hsum : du + du + BPair.ofNat (K + 1) * dgg + (dmu + dmu)
      ≤ BPair.unit + BPair.ofNat K * dgg := ground.leB_add hneg hmg
  have e1 : du + du + BPair.ofNat (K + 1) * dgg + (dmu + dmu)
      = du + dmu + (du + dmu) + BPair.ofNat (K + 1) * dgg := by
    rw [BPair.add_assoc (du + du) (BPair.ofNat (K + 1) * dgg)
        (dmu + dmu),
      BPair.add_comm (BPair.ofNat (K + 1) * dgg) (dmu + dmu),
      ← BPair.add_assoc (du + du) (dmu + dmu)
        (BPair.ofNat (K + 1) * dgg),
      BPair.add_add_comm du du dmu dmu]
  have h3 : dc + drho + (dc + drho) + BPair.ofNat (K + 1) * dgg
      ≤ BPair.unit + BPair.ofNat K * dgg :=
    ground.leB_congr_left
      (BPair.add_congr (BPair.add_congr hB hB)
        (BPair.oneValue_refl (BPair.ofNat (K + 1) * dgg)))
      (ground.leB_congr_left (BPair.oneValue_of_eq e1) hsum)
  have hLB : dgg ≤ dc + drho + (dc + drho) :=
    ground.leB_congr
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.unit_add BPair.unit)
          (BPair.oneValue_refl dgg))
        (BPair.unit_add dgg))
      (BPair.oneValue_of_eq (BPair.add_add_comm dc dc drho drho))
      (ground.leB_add (ground.leB_add hdc hdc) hrl)
  have h5 : BPair.ofNat K * dgg + (dgg + dgg)
      ≤ BPair.ofNat K * dgg + BPair.unit :=
    ground.leB_congr
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl dgg) (ground.ofNat_succ_mul K dgg))
        (BPair.oneValue_of_eq
          (BPair.add_left_comm dgg (BPair.ofNat K * dgg) dgg)))
      (BPair.oneValue_of_eq
        (BPair.add_comm BPair.unit (BPair.ofNat K * dgg)))
      (ground.leB_trans
        (ground.leB_add hLB
          (ground.leB_refl (BPair.ofNat (K + 1) * dgg))) h3)
  exact absurd (ground.unitLtAdd hsq (ground.leB_of_lt hsq))
    (ground.leB_not_lt (ground.leB_cancelL h5))

/-- The tie's refutation: a member off the top key joins no content
to the top's own shifted key — the clearance's positive root reads
the tie's pairing at the form's additivity against the ρ-length
read (`lem:grading`). -/
private theorem tieRefute (t : gentable.Table)
    (F : sertables.FundData) (hshape : sertables.fundShape t F)
    (hgsym : sertables.gramSymRead F)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (lamV cV : List BPair) (K : Nat) (hcV : cV.length = t.rank)
    (hwsh : sertables.wShapeRead t W)
    (hoff : offTopAt t F W K
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))))
    (hmsh : memberchar.mShapeRead t L) (hmag : magAt t F L K)
    (hrho : row.rhoLenRead t F)
    (hdomC : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ sertables.dotB F cV (sertables.posCorootV t j))
    (vp : List BPair × Bool) (hvp : vp ∈ W)
    (hne : vp.1 ≠ poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)))
    (mu : List BPair) (hmu : mu ∈ L)
    (hte : poly.pnorm (elim.vecAdd vp.1 mu)
      = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))) :
    False := by
  obtain ⟨j, hj, hneg⟩ := hoff vp hvp hne
  have hjlt : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj
  have hsq : BPair.unit < sertables.dotB F (sertables.posCorootV t j)
      (sertables.posCorootV t j) := (hrho j hjlt).1
  have hvl : vp.1.length = t.rank := (hwsh vp hvp).1
  have hml : mu.length = t.rank := (hmsh mu hmu).1
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hov : poly.oneValue (elim.vecAdd vp.1 mu)
      (elim.vecAdd cV (sertables.rhoV t)) := by
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (poly.pnorm_oneValue (elim.vecAdd vp.1 mu))) ?_
    rw [hte]
    exact poly.pnorm_oneValue _
  have hcg := sertables.dotB_congrL F _ _
    (sertables.posCorootV t j) hov
  have hB : (sertables.dotB F vp.1 (sertables.posCorootV t j)
      + sertables.dotB F mu (sertables.posCorootV t j)).oneValue
      (sertables.dotB F cV (sertables.posCorootV t j)
        + sertables.dotB F (sertables.rhoV t)
            (sertables.posCorootV t j)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (sertables.dotB_addL t F hshape vp.1 mu
          (sertables.posCorootV t j) hvl hml))
      (BPair.oneValue_trans hcg
        (sertables.dotB_addL t F hshape cV (sertables.rhoV t)
          (sertables.posCorootV t j) hcV hrl))
  have hsw := assembly.dotB_swap t F hshape hgsym
    (sertables.posCorootV t j) (sertables.rhoV t)
    (sertables.posCorootV_length t j) hrl
  exact clearRefute K hsq hneg (hmag mu hmu j hjlt) hB
    (ground.leB_congr_right (BPair.add_congr hsw hsw)
      (hrho j hjlt).2.1)
    (hdomC j hjlt)

/-- The withdrawn key: the target's shifted key parts the top's own
at the members' difference, the shift's join dropping. -/
private theorem gapRead (t : gentable.Table) (lamV cV : List BPair)
    (hlam : lamV.length = t.rank) (hcV : cV.length = t.rank) :
    poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t)))
        (poly.neg
          (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)))))
      = poly.pnorm (elim.vecAdd cV (poly.neg lamV)) := by
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hnl : (poly.neg lamV).length = t.rank :=
    (ground.length_map BPair.swap lamV).trans hlam
  have hnr : (poly.neg (sertables.rhoV t)).length = t.rank :=
    (ground.length_map BPair.swap (sertables.rhoV t)).trans hrl
  have hA : (elim.vecAdd cV (sertables.rhoV t)).length = t.rank :=
    elim.length_vecAdd cV (sertables.rhoV t) t.rank hcV hrl
  have hBl : (elim.vecAdd lamV (sertables.rhoV t)).length = t.rank :=
    elim.length_vecAdd lamV (sertables.rhoV t) t.rank hlam hrl
  have hnB : (poly.neg (elim.vecAdd lamV (sertables.rhoV t))).length
      = t.rank :=
    (ground.length_map BPair.swap _).trans hBl
  have hnpB : (poly.neg (poly.pnorm
      (elim.vecAdd lamV (sertables.rhoV t)))).length = t.rank :=
    (ground.length_map BPair.swap _).trans
      ((poly.pnorm_length _).trans hBl)
  have hcn : (elim.vecAdd cV (poly.neg lamV)).length = t.rank :=
    elim.length_vecAdd cV (poly.neg lamV) t.rank hcV hnl
  have hZ : poly.unitTail (elim.vecAdd (sertables.rhoV t)
      (poly.neg (sertables.rhoV t))) := by
    refine poly.oneValue_unitTail ?_
      (poly.unitTail_replicate
        (poly.neg (sertables.rhoV t)).length)
    have h := assembly.vecAdd_swap_self (poly.neg (sertables.rhoV t))
    rw [poly.neg_neg (sertables.rhoV t)] at h
    exact h
  have hZl : (elim.vecAdd (sertables.rhoV t)
      (poly.neg (sertables.rhoV t))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hrl hnr
  have h1 : poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t)))
        (poly.neg
          (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)))))
      = poly.pnorm (elim.vecAdd
        (elim.vecAdd cV (sertables.rhoV t))
        (poly.neg (elim.vecAdd lamV (sertables.rhoV t)))) := by
    refine poly.pnorm_congr _ _ ?_ ?_
    · rw [elim.length_vecAdd _ _ t.rank
        ((poly.pnorm_length _).trans hA) hnpB,
        elim.length_vecAdd _ _ t.rank hA hnB]
    · exact elim.polyOne_vecAdd _ _ _ _ (poly.pnorm_oneValue _)
        (poly.swapMap_oneValue (poly.pnorm_oneValue _))
        (poly.pnorm_length _) (hnpB.trans hnB.symm)
  rw [h1, assembly.neg_vecAdd lamV (sertables.rhoV t),
    elim.vecAdd_comm (poly.neg lamV) (poly.neg (sertables.rhoV t)),
    elim.vecAdd_assoc cV (sertables.rhoV t)
      (elim.vecAdd (poly.neg (sertables.rhoV t)) (poly.neg lamV)),
    ← elim.vecAdd_assoc (sertables.rhoV t)
      (poly.neg (sertables.rhoV t)) (poly.neg lamV),
    elim.vecAdd_comm (elim.vecAdd (sertables.rhoV t)
      (poly.neg (sertables.rhoV t))) (poly.neg lamV),
    ← elim.vecAdd_assoc cV (poly.neg lamV)
      (elim.vecAdd (sertables.rhoV t)
        (poly.neg (sertables.rhoV t)))]
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [elim.length_vecAdd _ _ t.rank hcn hZl, hcn]
  · exact elim.vecAdd_null_right _ _ (hcn.trans hZl.symm) hZ

/-- The inner fold at the top's shifted key reads the content
list's count at the withdrawn key. -/
private theorem innerTop (t : gentable.Table)
    (L : List (List BPair)) (lamV cV : List BPair)
    (hlam : lamV.length = t.rank) (hcV : cV.length = t.rank)
    (hmsh : memberchar.mShapeRead t L) :
    ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))) nu)
          = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))
          then 1 else 0) L
      = ground.countOf
          (poly.pnorm (elim.vecAdd cV (poly.neg lamV))) L := by
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hkl : (poly.pnorm
      (elim.vecAdd lamV (sertables.rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd lamV (sertables.rhoV t) t.rank hlam hrl)
  have hyl : (poly.pnorm
      (elim.vecAdd cV (sertables.rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd cV (sertables.rhoV t) t.rank hcV hrl)
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun nu => if poly.pnorm (elim.vecAdd cV (poly.neg lamV)) = nu
      then 1 else 0) L ?_)
    (ground.countOf_fold _ L).symm
  intro mu hmuc
  have hmu := ground.mem_of_countOf_pos mu L hmuc
  have hiff := assembly.addKey_iff t.rank
    (poly.pnorm (elim.vecAdd cV (sertables.rhoV t)))
    (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))) mu
    hyl (poly.pnorm_pnorm _) hkl (hmsh mu hmu).1 (hmsh mu hmu).2
  rw [gapRead t lamV cV hlam hcV] at hiff
  by_cases hc : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))) mu)
    = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun he => hc (hiff.mpr he))]

/-- The graded fold at a stated side: the top's own count against
the content list's count at the withdrawn key, every further
member's tie refused. -/
private theorem convSide (t : gentable.Table)
    (F : sertables.FundData) (hshape : sertables.fundShape t F)
    (hgsym : sertables.gramSymRead F)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (lamV cV : List BPair) (K : Nat)
    (hlam : lamV.length = t.rank) (hcV : cV.length = t.rank)
    (hwsh : sertables.wShapeRead t W)
    (hoff : offTopAt t F W K
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))))
    (hmsh : memberchar.mShapeRead t L) (hmag : magAt t F L K)
    (hrho : row.rhoLenRead t F)
    (hdomC : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ sertables.dotB F cV (sertables.posCorootV t j))
    (side : Bool) :
    memberchar.convCount W L
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t))) side
      = ground.countOf
          (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)), side) W
        * ground.countOf
          (poly.pnorm (elim.vecAdd cV (poly.neg lamV))) L := by
  have hz : ∀ x ∈ W,
      x ≠ (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)), side) →
      (if x.2 = side then ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd x.1 nu)
          = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))
          then 1 else 0) L else 0) = 0 := by
    intro vp hvp hne
    by_cases hs : vp.2 = side
    · have hvk : vp.1
          ≠ poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)) := by
        intro hv
        refine hne ?_
        rw [← hv, ← hs]
      rw [if_pos hs]
      refine ground.famFold_null_ov ground.natFoldLaws _ L ?_
      intro mu hmuc
      have hmu := ground.mem_of_countOf_pos mu L hmuc
      refine if_neg ?_
      intro hte
      exact tieRefute t F hshape hgsym W L lamV cV K hcV hwsh hoff
        hmsh hmag hrho hdomC vp hvp hvk mu hmu hte
    · rw [if_neg hs]
  have hpick := ground.famFold_off
    (fun vp : List BPair × Bool => if vp.2 = side then
      ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu)
          = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))
          then 1 else 0) L else 0)
    (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)), side) W hz
  show ground.famFold Nat.add 0
      (fun vp : List BPair × Bool => if vp.2 = side then
        ground.famFold Nat.add 0
          (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu)
            = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))
            then 1 else 0) L else 0) W = _
  rw [hpick]
  show ground.countOf
        (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t)), side) W
      * (if side = side then ground.famFold Nat.add 0
          (fun nu => if poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))) nu)
            = poly.pnorm (elim.vecAdd cV (sertables.rhoV t))
            then 1 else 0) L else 0)
    = _
  rw [if_pos rfl, innerTop t L lamV cV hlam hcV hmsh]

/-- The member rows: at the stated orbit reads — the top once
even, every further member at the off-top clearance — with the
content list at the magnitude cap and a dominant target, the
graded convolution folds read the member's `θ` content list at
the tie on the even side with the odd side vacant
(`lem:grading`'s display `N^{λ+ν}_{θλ} = mult_θ(ν)`, the
clearance entering as the orbit's own read). -/
theorem memberRows (t : gentable.Table) (F : sertables.FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (lamV cV : List BPair) (K : Nat)
    (hshape : sertables.fundShape t F)
    (hgsym : sertables.gramSymRead F)
    (hlam : lamV.length = t.rank) (hcV : cV.length = t.rank)
    (hwsh : sertables.wShapeRead t W)
    (htop : assembly.wTopAt W
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))))
    (hoff : offTopAt t F W K
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))))
    (hmsh : memberchar.mShapeRead t L) (hmag : magAt t F L K)
    (hrho : row.rhoLenRead t F)
    (hdomC : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ sertables.dotB F cV (sertables.posCorootV t j)) :
    memberchar.convCount W L
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t))) false
      = ground.countOf
          (poly.pnorm (elim.vecAdd cV (poly.neg lamV))) L
    ∧ memberchar.convCount W L
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t))) true = 0 := by
  refine ⟨?_, ?_⟩
  · rw [convSide t F hshape hgsym W L lamV cV K hlam hcV hwsh hoff
      hmsh hmag hrho hdomC false, htop.1, Nat.one_mul]
  · rw [convSide t F hshape hgsym W L lamV cV K hlam hcV hwsh hoff
      hmsh hmag hrho hdomC true, htop.2, Nat.zero_mul]

/-- The member row read back at the exhaustion: the member's own
count in the stated list is the `θ` content list's count at the
withdrawn key (`lem:grading`, `cor:steinberg`'s member tie). -/
theorem memberRow (t : gentable.Table) (F : sertables.FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (lamV cV : List BPair) (K : Nat)
    (hshape : sertables.fundShape t F)
    (hgsym : sertables.gramSymRead F)
    (hlam : lamV.length = t.rank) (hcV : cV.length = t.rank)
    (hwsh : sertables.wShapeRead t W)
    (htop : assembly.wTopAt W
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))))
    (hoff : offTopAt t F W K
      (poly.pnorm (elim.vecAdd lamV (sertables.rhoV t))))
    (hmsh : memberchar.mShapeRead t L) (hmag : magAt t F L K)
    (hrho : row.rhoLenRead t F)
    (hdomC : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ sertables.dotB F cV (sertables.posCorootV t j))
    (cVs : List (List BPair))
    (hmem : steinberg.memberAt t W L cVs cV) :
    ground.countOf cV cVs
      = ground.countOf
          (poly.pnorm (elim.vecAdd cV (poly.neg lamV))) L := by
  have h := memberRows t F W L lamV cV K hshape hgsym hlam hcV hwsh
    htop hoff hmsh hmag hrho hdomC
  have hm : ground.countOf cV cVs
      + memberchar.convCount W L
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t))) true
      = memberchar.convCount W L
        (poly.pnorm (elim.vecAdd cV (sertables.rhoV t))) false := hmem
  rw [h.1, h.2, Nat.add_zero] at hm
  exact hm

end grading
