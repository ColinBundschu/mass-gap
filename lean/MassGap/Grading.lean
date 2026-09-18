import MassGap.Steinberg
import MassGap.Row
import MassGap.Adjchar
import MassGap.Channels
import MassGap.Stableentries
/-!
`lem:grading` — the fiber's grading and the tower rows' repetition
off the collar.  The index grading is the first tier: the band
components at the band adjacency's closures (`components`), their
contents, the band neighborhood (`bandVerts`) with the separation
read (`sepBeyond`), and the two direction reads at a head bound,
the tower's (`towerAt`, a component's content at or beyond the
bound) and the slab's (`slabAt`, a component pair separated beyond
the band), the head their joint refusal (`headAt`) and the graded
index a stated index's partition at it (`gradedIdx`); the rows'
three shapes read at the index (`support_target` the stencil row's
reach, `components_border` the border row's one further component).
The collar is the label set at a consecutive row-list gap below
two, its read `collarAt` the occupancy fold (`con:places`: the
occupancies are the row list's consecutive gaps), and the deep-row
read `rowRead` is the tie's gap of the target's display against the
label's read at `lem:adjchar`'s content formula — the one row the
adjoint's content list, the sum's unit at an absent tie.  The
theorem `deepRow` closes the display `N^{λ+ν}_{θλ} = mult_θ(ν)` at
every label off the collar at the declared count's frame `2 ≤ d`
(`con:places`, the fundamental count the residue's successor):
every place permutation but the identity drops from
`cor:steinberg`'s graded sum, since a label off the collar reads
its display gaps at three or beyond while an adjoint content's
entries sit at or below two, so a permuted display's reversed
adjacent pair survives every content move against the strictly
decreasing target display; the identity's tie is the row, on the
even side.  On the collar the walk's own diagonal differs, the
`θ`-support count against the residue (`prop:row`).  The member
rows close the module at the weight tables (`memberRows`).
-/

namespace grading
open ground places

/-- The collar read: a consecutive row-list gap below two — the
occupancy read at a key below the top, the occupancies the row
list's consecutive gaps (`con:places`). -/
def collarAt (s : Shape) : Prop :=
  ((List.range (s.length - 1)).any (fun i => ground.getAt 0 s i < 2))
    = true

instance instGrading1 (s : Shape) : Decidable (collarAt s) :=
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

/-! The index grading: the band components with their contents, the
band neighborhood with the separation read, and the graded index at
a head bound.  Two links are band-adjacent where one plaquette's
boundary meets both links' ends (`bandAdj`, `lem:stableentries`'s
reach); a link's closure within the support is the band steps'
saturation from it (`closure`: the step `stepAdd` joins the
support's members off the reached list and adjacent to a reached
member, the walk stopping at a step with the vacant join and within
the region's link count of steps), its component the support's
members in the closure in the support's own order (`compOf`), and
the components are the closures from the least link off the earlier
components in turn (`components` at `partsGo`), each closure
stationary within the support's count of steps (`closure_stationary`
at the support's distinct keys), the closures'
partition of the support (`components_countOf`) with the class's
content the components' contents' sum (`contentN_components`,
`compContent_le_contentN`).  The band neighborhood is the vertex
neighborhood joined to the vertices of the plaquettes meeting it
(`bandVerts`), a plaquette meeting a vertex list at an end of a
boundary entry (`meetsB`), two configurations separated beyond the
band where every plaquette of the region meets at most one of their
band neighborhoods (`sepBeyond`, `sepBeyond_read` its read at one
plaquette, `meetsB_of_near` the vertex neighborhood's plaquettes
among them), a component's own
configuration its labels at its links (`compConf`); the grading's
two reads are a component's content at or beyond the head bound
(`towerAt`) and a component pair separated beyond the band
(`slabAt`), the head their joint refusal (`headAt`, `headAt_read`
its two clauses, `tower_content` the tower's electric floor), and
the graded index at a stated index is its partition at the head
read (`gradedIdx`, the head and tail lists at their reads with the
concatenation the index's members, `gradedIdx_head`,
`gradedIdx_tail`, `gradedIdx_countOf`).  The closures are classes:
saturated at the adjacency (`closure_sat`), each holding its members'
closures (`closure_trans`) and reading its start back from every
member (`closure_symm`), so the components are the support members'
components (`components_compOf`, `compOf_mem_components`,
`compOf_eq_of_mem`, `compOf_drop`) at distinct places disjoint
(`components_disjoint`), each transporting along a region action
(`bandAdj_perm`, `closure_perm`, `compOf_perm`, `meetsB_move`); and a
component's link count against a floor of the
window labels' Casimirs sits at or below its content (`comp_floor`),
every head class's component below the bound at that price
(`head_floor`).  The rows: a target keeps
every label off the plaquette's boundary, so its support sits
within the class's support joined to the plaquette's links
(`support_target`, the stencil row's reach), and at a plaquette off
the band neighborhood (`offBand`) the far row's one target
(`stableentries.farConf`) reads the class's components with one
further component, the plaquette's links in the region's key order,
the loop's links pairwise adjacent at the plaquette's own boundary
and off every support link's adjacency (`components_border`, the
border row, `components_border_length` its count). -/

/-- Band adjacency: one plaquette's boundary meets both links'
ends, the coupling's own reach. -/
def bandAdj (R : lattice.Region) (l1 l2 : Nat) : Bool :=
  R.plaqs.any (fun p =>
    stableentries.nearLink R p l1 && stableentries.nearLink R p l2)

/-- Band adjacency exchanges its two links, the conjunction's
exchange at every plaquette. -/
theorem bandAdj_comm (R : lattice.Region) (l1 l2 : Nat) :
    bandAdj R l1 l2 = bandAdj R l2 l1 :=
  any_congr_all _ _ (fun p => by
    cases stableentries.nearLink R p l1 <;>
      cases stableentries.nearLink R p l2 <;> rfl) R.plaqs

/-- One band step's guard: a support member off the reached list
and band-adjacent to a reached member. -/
def stepP (R : lattice.Region) (acc : List Nat) (l : Nat) : Bool :=
  !(ground.containsB acc l) && acc.any (fun m => bandAdj R m l)

/-- One band step's joined members: the support's members at the
step's guard. -/
def stepAdd (R : lattice.Region) (S acc : List Nat) : List Nat :=
  S.filter (stepP R acc)

/-- The band steps' saturation from a reached list within a stated
count of steps, the walk stopping at a step with the vacant join. -/
def closeGo (R : lattice.Region) (S : List Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | k + 1, acc =>
    match stepAdd R S acc with
    | [] => acc
    | _ :: _ => closeGo R S k (acc ++ stepAdd R S acc)

/-- A link's closure within the support: the saturation from the
link within the region's link count of steps. -/
def closure (R : lattice.Region) (S : List Nat) (l : Nat) : List Nat :=
  closeGo R S R.links [l]

/-- The component of a link: the support's members in the link's
closure, in the support's own order. -/
def compOf (R : lattice.Region) (S : List Nat) (l : Nat) : List Nat :=
  S.filter (ground.containsB (closure R S l))

/-- The parts of a link list within a stated count: the head link's
component with the parts of the further links; at the support, the
range filter, the head is the least link. -/
def partsGo (R : lattice.Region) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, l :: rest =>
    compOf R (l :: rest) l
      :: partsGo R k ((l :: rest).filter (fun x =>
        !(ground.containsB (compOf R (l :: rest) l) x)))

/-- The band components: the support's parts at the adjacency's
closures, in the links' order. -/
def components {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) : List (List Nat) :=
  partsGo R R.links (carrier.support F R a)

/-- A component's content: the electric diagonal's per-part read. -/
def compContent {L : Type} (F : fusion.Data L) (a : List L)
    (c : List Nat) : Nat :=
  carrier.contentN F (c.map (ground.getAt F.unit a))

/-- A component's own configuration: the class's labels at the
component's links, the unit off them. -/
def compConf {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (c : List Nat) : List L :=
  (List.range R.links).map (fun l =>
    if ground.containsB c l then ground.getAt F.unit a l else F.unit)

/-- The band neighborhood: the vertex neighborhood joined to the
vertices of the plaquettes meeting it, `lem:stableentries`'s
reach. -/
def bandVerts {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) : List Nat :=
  (List.range R.verts).filter (fun v =>
    ground.containsB (carrier.touched F R a) v
      || R.plaqs.any (fun p =>
        stableentries.nearPlaq F R a p
          && p.any (fun e =>
            lattice.startOf R e == v || lattice.endOf R e == v)))

/-- A plaquette meets a vertex list: an end of a boundary entry sits
in it. -/
def meetsB (R : lattice.Region) (vs : List Nat) (p : List (Nat × Bool)) :
    Bool :=
  p.any (fun e =>
    ground.containsB vs (lattice.startOf R e)
      || ground.containsB vs (lattice.endOf R e))

/-- The separation read: two configurations beyond the band where
every plaquette of the region meets at most one of their band
neighborhoods. -/
def sepBeyond {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) : Prop :=
  (R.plaqs.all (fun p =>
    !(meetsB R (bandVerts F R a) p) || !(meetsB R (bandVerts F R b) p))) = true

instance instGrading2 {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) : Decidable (sepBeyond F R a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- A plaquette off the band neighborhood: it meets none of its
vertices. -/
def offBand {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (p : List (Nat × Bool)) : Bool :=
  !(meetsB R (bandVerts F R a) p)

/-- The tower read: a band component's content at or beyond the
head bound. -/
def towerAt {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (a : List L) : Bool :=
  (components F R a).any (fun c => lamH ≤ compContent F a c)

/-- The slab read: a pair of band components separated beyond the
band, the pairs at ascending places. -/
def slabAt {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) : Bool :=
  (List.range (components F R a).length).any (fun i =>
    (List.range (components F R a).length).any (fun j =>
      i < j && sepBeyond F R
        (compConf F R a (ground.getAt [] (components F R a) i))
        (compConf F R a (ground.getAt [] (components F R a) j))))

/-- The head read: the two direction reads' joint refusal, every
component's content below the bound and every pair within the
band. -/
def headAt {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (a : List L) : Prop :=
  (towerAt F R lamH a || slabAt F R a) = false

instance instGrading5 {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (a : List L) : Decidable (headAt F R lamH a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The graded index at a stated index and head bound: the head
classes and the tail, the classes in a direction, the index's
partition at the head read. -/
def gradedIdx {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (ix : List (List L)) : List (List L) × List (List L) :=
  (ix.filter (fun a => !(towerAt F R lamH a || slabAt F R a)),
   ix.filter (fun a => towerAt F R lamH a || slabAt F R a))

/-- The head list's members read the head. -/
theorem gradedIdx_head {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (ix : List (List L)) (a : List L)
    (ha : a ∈ (gradedIdx F R lamH ix).1) : headAt F R lamH a := by
  have h := (ground.mem_filter_of _ ix a ha).2
  show (towerAt F R lamH a || slabAt F R a) = false
  cases hb : (towerAt F R lamH a || slabAt F R a) with
  | false => rfl
  | true => rw [hb] at h; exact Bool.noConfusion h

/-- The tail list's members refuse the head. -/
theorem gradedIdx_tail {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (ix : List (List L)) (a : List L)
    (ha : a ∈ (gradedIdx F R lamH ix).2) : ¬ headAt F R lamH a := by
  have h := (ground.mem_filter_of _ ix a ha).2
  intro hh
  have hh' : (towerAt F R lamH a || slabAt F R a) = false := hh
  rw [hh'] at h
  exact Bool.noConfusion h

/-- The two lists' concatenation reads the index member for member,
the partition's own count. -/
theorem gradedIdx_countOf {L : Type} [DecidableEq L] (F : fusion.Data L)
    (R : lattice.Region) (lamH : Nat) (ix : List (List L)) (a : List L) :
    ground.countOf a ((gradedIdx F R lamH ix).1 ++ (gradedIdx F R lamH ix).2)
      = ground.countOf a ix := by
  show ground.countOf a
      (ix.filter (fun a => !(towerAt F R lamH a || slabAt F R a))
        ++ ix.filter (fun a => towerAt F R lamH a || slabAt F R a))
    = ground.countOf a ix
  rw [ground.countOf_append, ground.countOf_filter, ground.countOf_filter]
  cases hb : (towerAt F R lamH a || slabAt F R a) with
  | true =>
    show 0 + ground.countOf a ix = ground.countOf a ix
    exact Nat.zero_add _
  | false =>
    show ground.countOf a ix + 0 = ground.countOf a ix
    exact Nat.add_zero _

/-- The head's two clauses: every component's content below the
bound, and the slab read refused. -/
theorem headAt_read {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (a : List L) :
    headAt F R lamH a
      ↔ (∀ c, c ∈ components F R a → compContent F a c < lamH)
        ∧ slabAt F R a = false := by
  constructor
  · intro h
    have h' : (towerAt F R lamH a || slabAt F R a) = false := h
    have ht : towerAt F R lamH a = false := (or_false_split h').1
    have hs : slabAt F R a = false := (or_false_split h').2
    refine ⟨fun c hc => ?_, hs⟩
    have hall := ground.all_of_mem _ _
      (ground.all_not_of_any_false _ (components F R a) ht) c hc
    cases hlt : decide (lamH ≤ compContent F a c) with
    | true =>
      rw [hlt] at hall
      exact Bool.noConfusion hall
    | false =>
      exact Nat.lt_of_not_le (of_decide_eq_false hlt)
  · intro h
    have ht : towerAt F R lamH a = false := by
      refine ground.any_false_of_all_not _ (components F R a)
        (ground.all_of_mem_intro _ (components F R a) (fun c hc => ?_))
      rw [decide_eq_false (Nat.not_le_of_lt (h.1 c hc))]
      rfl
    show (towerAt F R lamH a || slabAt F R a) = false
    rw [ht, h.2]
    rfl

/-! The partition: the parts' concatenation reads the support
member for member, and the class's content is the components'
contents' sum. -/

private theorem closeGo_succ (R : lattice.Region) (S : List Nat)
    (k : Nat) (acc : List Nat) :
    closeGo R S (k + 1) acc
      = match stepAdd R S acc with
        | [] => acc
        | _ :: _ => closeGo R S k (acc ++ stepAdd R S acc) := rfl

private theorem partsGo_succ (R : lattice.Region) (k : Nat) (l : Nat)
    (rest : List Nat) :
    partsGo R (k + 1) (l :: rest)
      = compOf R (l :: rest) l
        :: partsGo R k ((l :: rest).filter (fun x =>
          !(ground.containsB (compOf R (l :: rest) l) x))) := rfl

/-- A reached member stays reached along the walk. -/
private theorem mem_closeGo (R : lattice.Region) (S : List Nat) :
    ∀ (k : Nat) (acc : List Nat) (x : Nat), x ∈ acc →
      x ∈ closeGo R S k acc
  | 0, _, _, hx => hx
  | k + 1, acc, x, hx => by
    rw [closeGo_succ]
    cases hst : stepAdd R S acc with
    | nil => exact hx
    | cons y t =>
      exact mem_closeGo R S k (acc ++ y :: t) x (ground.mem_append_left _ hx)

/-- A link sits in its own component within a list holding it. -/
private theorem mem_compOf_self (R : lattice.Region) (S : List Nat)
    (l : Nat) (hl : l ∈ S) : l ∈ compOf R S l :=
  ground.mem_filter_to _ hl
    (containsB_of_mem (mem_closeGo R S R.links [l] l (List.Mem.head [])))

/-- The remainder past the head's component is at most the tail. -/
private theorem rest_length (l : Nat) (rest : List Nat)
    (c : List Nat) (hl : l ∈ c) :
    ((l :: rest).filter (fun x => !(ground.containsB c x))).length
      ≤ rest.length := by
  rw [@ground.filter_cons_false Nat (fun x => !(ground.containsB c x)) l rest
    (by rw [containsB_of_mem hl]; rfl)]
  exact length_filter_le _ rest

/-- The part count is stable in the fuel past the list's length. -/
private theorem partsGo_fuel (R : lattice.Region) :
    ∀ (k : Nat) (S : List Nat), S.length ≤ k →
      partsGo R (k + 1) S = partsGo R k S
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _ => rfl
  | k + 1, l :: rest, h => by
    rw [partsGo_succ, partsGo_succ,
      partsGo_fuel R k _ (Nat.le_trans
        (rest_length l rest _ (mem_compOf_self R (l :: rest) l (List.Mem.head rest)))
        (Nat.le_of_succ_le_succ h))]

/-- The parts' concatenation reads the list member for member. -/
private theorem partsGo_countOf (R : lattice.Region) :
    ∀ (k : Nat) (S : List Nat), S.length ≤ k → ∀ x : Nat,
      ground.countOf x ((partsGo R k S).flatMap (fun c => c))
        = ground.countOf x S
  | 0, [], _, _ => rfl
  | 0, _ :: _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _ => rfl
  | k + 1, l :: rest, h, x => by
    rw [partsGo_succ]
    show ground.countOf x (compOf R (l :: rest) l
        ++ (partsGo R k ((l :: rest).filter (fun x =>
          !(ground.containsB (compOf R (l :: rest) l) x)))).flatMap
            (fun c => c))
      = ground.countOf x (l :: rest)
    rw [ground.countOf_append, partsGo_countOf R k _ (Nat.le_trans
        (rest_length l rest _ (mem_compOf_self R (l :: rest) l (List.Mem.head rest)))
        (Nat.le_of_succ_le_succ h)) x]
    show ground.countOf x ((l :: rest).filter
        (ground.containsB (closure R (l :: rest) l)))
      + ground.countOf x ((l :: rest).filter (fun x =>
          !(ground.containsB (compOf R (l :: rest) l) x)))
      = ground.countOf x (l :: rest)
    rw [ground.countOf_filter, ground.countOf_filter]
    cases hc : ground.countOf x (l :: rest) with
    | zero =>
      cases ground.containsB (closure R (l :: rest) l) x <;>
        cases ground.containsB (compOf R (l :: rest) l) x <;> rfl
    | succ n =>
      have hx : x ∈ l :: rest :=
        ground.mem_of_countOf_pos x (l :: rest) (by rw [hc]; exact Nat.succ_pos n)
      rw [show compOf R (l :: rest) l
          = (l :: rest).filter (ground.containsB (closure R (l :: rest) l))
          from rfl,
        containsB_filter_mem _ (l :: rest) x hx]
      cases ground.containsB (closure R (l :: rest) l) x with
      | true =>
        show (n + 1) + 0 = n + 1
        exact Nat.add_zero _
      | false =>
        show 0 + (n + 1) = n + 1
        exact Nat.zero_add _

/-- The support sits within the region's link count. -/
private theorem support_length_le {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) :
    (carrier.support F R a).length ≤ R.links := by
  show ((List.range R.links).filter (fun l =>
    !(F.eqL (ground.getAt F.unit a l) F.unit))).length ≤ R.links
  exact Nat.le_trans (length_filter_le _ (List.range R.links))
    (Nat.le_of_eq (ground.length_range R.links))

/-- The components' concatenation reads the support member for
member, the closures' partition. -/
theorem components_countOf {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (x : Nat) :
    ground.countOf x ((components F R a).flatMap (fun c => c))
      = ground.countOf x (carrier.support F R a) :=
  partsGo_countOf R R.links (carrier.support F R a)
    (support_length_le F R a) x

/-- The class's content is the components' contents' sum: the
support's Casimir fold read across the closures' partition. -/
theorem contentN_components {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (ha : a.length = R.links) :
    carrier.contentN F a
      = ground.famFold Nat.add 0 (compContent F a) (components F R a) := by
  have hg : carrier.contentN F a
      = ground.famFold Nat.add 0
        (fun l => if F.eqL (ground.getAt F.unit a l) F.unit then 0
          else F.c2N (ground.getAt F.unit a l)) (carrier.support F R a) := by
    rw [carrier.contentN_range F a, ha]
    refine (ground.famFold_add_filter _
      (fun l => !(F.eqL (ground.getAt F.unit a l) F.unit)) ?_
      (List.range R.links)).symm
    intro v hv
    have hv' : F.eqL (ground.getAt F.unit a v) F.unit = true := by
      cases he : F.eqL (ground.getAt F.unit a v) F.unit with
      | true => rfl
      | false => rw [he] at hv; exact Bool.noConfusion hv
    rw [if_pos hv']
  have hcov : ∀ x, x ∈ (components F R a).flatMap (fun c => c) →
      x ∈ carrier.support F R a := by
    intro x hx
    refine ground.mem_of_countOf_pos x _ ?_
    rw [← components_countOf F R a x]
    exact ground.countOf_pos_of_mem hx
  have h1 : ground.famFold Nat.add 0 (compContent F a) (components F R a)
      = ground.famFold Nat.add 0 (fun c => ground.famFold Nat.add 0
        (fun l => if F.eqL (ground.getAt F.unit a l) F.unit then 0
          else F.c2N (ground.getAt F.unit a l)) c) (components F R a) := by
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun c => ?_) (components F R a)
    show carrier.contentN F (c.map (ground.getAt F.unit a)) = _
    rw [carrier.contentN_fam, ground.famFold_map]
  have h2 : ground.famFold Nat.add 0 (fun c => ground.famFold Nat.add 0
        (fun l => if F.eqL (ground.getAt F.unit a l) F.unit then 0
          else F.c2N (ground.getAt F.unit a l)) c) (components F R a)
      = ground.famFold Nat.add 0
        (fun l => if F.eqL (ground.getAt F.unit a l) F.unit then 0
          else F.c2N (ground.getAt F.unit a l))
        ((components F R a).flatMap (fun c => c)) :=
    (ground.famFold_flatMap _ (fun c => c) (components F R a)).symm
  have h3 : ground.famFold Nat.add 0
        (fun l => if F.eqL (ground.getAt F.unit a l) F.unit then 0
          else F.c2N (ground.getAt F.unit a l))
        ((components F R a).flatMap (fun c => c))
      = ground.famFold Nat.add 0 (fun k =>
          ground.countOf k ((components F R a).flatMap (fun c => c))
            * (if F.eqL (ground.getAt F.unit a k) F.unit then 0
              else F.c2N (ground.getAt F.unit a k)))
        (carrier.support F R a) :=
    ground.famFold_partition _ _ (carrier.support F R a)
      (carrier.support_distinct F R a) hcov
  have h4 : ground.famFold Nat.add 0 (fun k =>
          ground.countOf k ((components F R a).flatMap (fun c => c))
            * (if F.eqL (ground.getAt F.unit a k) F.unit then 0
              else F.c2N (ground.getAt F.unit a k)))
        (carrier.support F R a)
      = ground.famFold Nat.add 0 (fun k =>
          ground.countOf k (carrier.support F R a)
            * (if F.eqL (ground.getAt F.unit a k) F.unit then 0
              else F.c2N (ground.getAt F.unit a k)))
        (carrier.support F R a) :=
    ground.famFold_congr_all Nat.add 0 _ _
      (fun k => by rw [components_countOf F R a k]) (carrier.support F R a)
  have h5 : ground.famFold Nat.add 0
        (fun l => if F.eqL (ground.getAt F.unit a l) F.unit then 0
          else F.c2N (ground.getAt F.unit a l)) (carrier.support F R a)
      = ground.famFold Nat.add 0 (fun k =>
          ground.countOf k (carrier.support F R a)
            * (if F.eqL (ground.getAt F.unit a k) F.unit then 0
              else F.c2N (ground.getAt F.unit a k)))
        (carrier.support F R a) :=
    ground.famFold_partition _ (carrier.support F R a) (carrier.support F R a)
      (carrier.support_distinct F R a) (fun x hx => hx)
  rw [hg, h5, h1, h2, h3, h4]

/-- A component's content sits at or below the class's. -/
theorem compContent_le_contentN {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (ha : a.length = R.links)
    (c : List Nat) (hc : c ∈ components F R a) :
    compContent F a c ≤ carrier.contentN F a := by
  rw [contentN_components F R a ha]
  exact ground.famFold_mem_le _ (components F R a) c hc

/-- The tower direction's electric floor: a class with a component
at or beyond the head bound reads its content at or beyond it. -/
theorem tower_content {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (lamH : Nat) (a : List L) (ha : a.length = R.links)
    (ht : towerAt F R lamH a = true) : lamH ≤ carrier.contentN F a := by
  obtain ⟨c, hc, hle⟩ := ground.mem_of_any _ (components F R a) ht
  exact Nat.le_trans (of_decide_eq_true hle)
    (compContent_le_contentN F R a ha c hc)

/-! The rows.  A target keeps every label off the plaquette's
boundary, so its support sits within the class's support joined to
the plaquette's links; and at a plaquette off the band neighborhood
the far target reads one further component. -/

/-- The stencil row's reach: a target's occupied link is the class's
own or a boundary link of the plaquette. -/
theorem support_target {L : Type} [DecidableEq L] (F : fusion.Data L)
    (R : lattice.Region) (p : List (Nat × Bool)) (a b : List L)
    (hb : 0 < ground.countOf b (algebra.plaqRow F R p a))
    (l : Nat) (hl : l ∈ carrier.support F R b) :
    l ∈ carrier.support F R a ∨ (p.any (fun e => e.1 == l)) = true := by
  obtain ⟨hlr, hocc⟩ := ground.mem_filter_of _ (List.range R.links) l hl
  cases hp : (p.any (fun e => e.1 == l)) with
  | true => exact Or.inr rfl
  | false =>
    refine Or.inl (ground.mem_filter_to _ hlr ?_)
    rw [← algebra.plaqRow_keep F R p a b hb l (ground.ltOfMemRange hlr)
      (ground.all_not_of_any_false _ p hp)]
    exact hocc

/-- A touched vertex sits in the band neighborhood. -/
theorem mem_bandVerts_of_touched {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (v : Nat)
    (hv : v ∈ carrier.touched F R a) : v ∈ bandVerts F R a := by
  refine ground.mem_filter_to _
    (ground.mem_filter_of _ (List.range R.verts) v hv).1 ?_
  show (ground.containsB (carrier.touched F R a) v || _) = true
  rw [containsB_of_mem hv]
  rfl

/-- A vertex of a plaquette meeting the vertex neighborhood sits in
the band neighborhood. -/
theorem mem_bandVerts_of_near {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (q : List (Nat × Bool))
    (hq : q ∈ R.plaqs) (hn : stableentries.nearPlaq F R a q = true)
    (v : Nat) (hv : v < R.verts)
    (hpass : (q.any (fun e =>
      lattice.startOf R e == v || lattice.endOf R e == v)) = true) :
    v ∈ bandVerts F R a := by
  refine ground.mem_filter_to _ (ground.memRange hv) ?_
  show (ground.containsB (carrier.touched F R a) v
    || R.plaqs.any (fun p => stableentries.nearPlaq F R a p
      && p.any (fun e => lattice.startOf R e == v || lattice.endOf R e == v)))
    = true
  have hB : R.plaqs.any (fun p => stableentries.nearPlaq F R a p
      && p.any (fun e => lattice.startOf R e == v || lattice.endOf R e == v))
      = true := by
    refine ground.any_of_mem _ hq ?_
    rw [hn, hpass]
    rfl
  rw [hB]
  cases ground.containsB (carrier.touched F R a) v <;> rfl

/-- Off the band neighborhood every boundary entry's two ends read
the membership test false. -/
private theorem offBand_ends {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (p : List (Nat × Bool))
    (hoff : offBand F R a p = true) (e : Nat × Bool) (he : e ∈ p) :
    ground.containsB (bandVerts F R a) (lattice.startOf R e) = false
      ∧ ground.containsB (bandVerts F R a) (lattice.endOf R e) = false := by
  have hm : meetsB R (bandVerts F R a) p = false := ground.boolFalseOfNot hoff
  constructor
  · cases hc : ground.containsB (bandVerts F R a) (lattice.startOf R e) with
    | false => rfl
    | true =>
      have h := ground.any_of_mem (fun e =>
        ground.containsB (bandVerts F R a) (lattice.startOf R e)
          || ground.containsB (bandVerts F R a) (lattice.endOf R e)) he
        (by rw [hc]; rfl)
      exact Bool.noConfusion (hm.symm.trans h)
  · cases hc : ground.containsB (bandVerts F R a) (lattice.endOf R e) with
    | false => rfl
    | true =>
      have h := ground.any_of_mem (fun e =>
        ground.containsB (bandVerts F R a) (lattice.startOf R e)
          || ground.containsB (bandVerts F R a) (lattice.endOf R e)) he
        (by rw [hc]; exact Bool.or_true _)
      exact Bool.noConfusion (hm.symm.trans h)

/-- A plaquette meeting the vertex neighborhood meets the band
neighborhood. -/
theorem meetsB_of_near {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (q : List (Nat × Bool))
    (hn : stableentries.nearPlaq F R a q = true) :
    meetsB R (bandVerts F R a) q = true := by
  obtain ⟨v, hv, hqv⟩ := ground.mem_of_any _ (carrier.touched F R a) hn
  obtain ⟨e, he, hev⟩ := ground.mem_of_any _ q hqv
  have hb := containsB_of_mem (mem_bandVerts_of_touched F R a v hv)
  refine ground.any_of_mem _ he ?_
  cases ground.orSplitB hev with
  | inl h1 => rw [ground.beqEqOf h1, hb]; rfl
  | inr h2 => rw [ground.beqEqOf h2, hb]; exact Bool.or_true _

/-- At two configurations separated beyond the band a plaquette of
the region meets at most one band neighborhood. -/
theorem sepBeyond_read {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) (hs : sepBeyond F R a b) (q : List (Nat × Bool))
    (hq : q ∈ R.plaqs) :
    ¬ (meetsB R (bandVerts F R a) q = true
      ∧ meetsB R (bandVerts F R b) q = true) := by
  intro h
  have hall := ground.all_of_mem _ _ hs q hq
  rw [h.1, h.2] at hall
  exact Bool.noConfusion hall

/-- A plaquette off the band neighborhood sits off the vertex
neighborhood: the far read. -/
theorem offBand_far {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (p : List (Nat × Bool)) (hoff : offBand F R a p = true) :
    stableentries.nearPlaq F R a p = false := by
  cases hn : stableentries.nearPlaq F R a p with
  | false => rfl
  | true =>
    have h := meetsB_of_near F R a p hn
    have hoff' : (!(meetsB R (bandVerts F R a) p)) = true := hoff
    rw [h] at hoff'
    exact Bool.noConfusion hoff'

/-- A plaquette meeting an end of an occupied link meets the vertex
neighborhood. -/
private theorem near_of_link {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (hw : lattice.wellRead R) (a : List L)
    (q : List (Nat × Bool)) (x : Nat) (hx : x < R.links)
    (hocc : F.eqL (ground.getAt F.unit a x) F.unit = false)
    (hnl : stableentries.nearLink R q x = true) :
    stableentries.nearPlaq F R a q = true := by
  obtain ⟨e, he, hev⟩ := ground.mem_of_any _ q hnl
  have ht := carrier.end_touched F R hw a x hx hocc
  have hcase : ∀ v : Nat, v ∈ carrier.touched F R a →
      (lattice.startOf R e = v ∨ lattice.endOf R e = v) →
      stableentries.nearPlaq F R a q = true := by
    intro v hv hor
    refine ground.any_of_mem _ hv (ground.any_of_mem _ he ?_)
    cases hor with
    | inl h => rw [h, ground.eqBeqOf rfl]; exact Bool.true_or _
    | inr h => rw [h, ground.eqBeqOf rfl]; exact Bool.or_true _
  cases ground.orSplitB hev with
  | inl h3 =>
    cases ground.orSplitB h3 with
    | inl h2 =>
      cases ground.orSplitB h2 with
      | inl h1 => exact hcase _ ht.1 (Or.inl (ground.beqEqOf h1))
      | inr h1 => exact hcase _ ht.2 (Or.inl (ground.beqEqOf h1))
    | inr h2 => exact hcase _ ht.1 (Or.inr (ground.beqEqOf h2))
  | inr h3 => exact hcase _ ht.2 (Or.inr (ground.beqEqOf h3))

/-- Off the band neighborhood a boundary link is band-adjacent to
no occupied link of the class: the adjacency's plaquette meets the
vertex neighborhood, so the boundary link's ends sit in the band
neighborhood against the plaquette's position off it. -/
private theorem offBand_nonadj {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (hw : lattice.wellRead R) (a : List L)
    (p : List (Nat × Bool)) (hoff : offBand F R a p = true)
    (x : Nat) (hx : x < R.links)
    (hocc : F.eqL (ground.getAt F.unit a x) F.unit = false)
    (e : Nat × Bool) (he : e ∈ p) (hek : e.1 < R.links) :
    bandAdj R x e.1 = false := by
  cases hadj : bandAdj R x e.1 with
  | false => rfl
  | true =>
    obtain ⟨q, hq, hqq⟩ := ground.mem_of_any _ R.plaqs hadj
    have hs := ground.andSplitB hqq
    have hnear := near_of_link F R hw a q x hx hocc hs.1
    obtain ⟨e', he', hev⟩ := ground.mem_of_any _ q hs.2
    have hends := lattice.endLt R hw e.1 hek
    have hoffe := offBand_ends F R a p hoff e he
    have hoffT : ground.containsB (bandVerts F R a) (ground.getAt 0 R.tail e.1)
        = false ∧ ground.containsB (bandVerts F R a) (ground.getAt 0 R.head e.1)
        = false := by
      cases lattice.edge_ends R e with
      | inl h =>
        rw [h.1] at hoffe
        rw [h.2] at hoffe
        exact ⟨hoffe.1, hoffe.2⟩
      | inr h =>
        rw [h.1] at hoffe
        rw [h.2] at hoffe
        exact ⟨hoffe.2, hoffe.1⟩
    have hin : ∀ v : Nat, v < R.verts →
        (lattice.startOf R e' = v ∨ lattice.endOf R e' = v) →
        v ∈ bandVerts F R a := by
      intro v hv hor
      refine mem_bandVerts_of_near F R a q hq hnear v hv
        (ground.any_of_mem _ he' ?_)
      cases hor with
      | inl h => rw [h, ground.eqBeqOf rfl]; exact Bool.true_or _
      | inr h => rw [h, ground.eqBeqOf rfl]; exact Bool.or_true _
    have hT : ¬ ground.getAt 0 R.tail e.1 ∈ bandVerts F R a := fun hm =>
      Bool.noConfusion ((containsB_of_mem hm).symm.trans hoffT.1)
    have hH : ¬ ground.getAt 0 R.head e.1 ∈ bandVerts F R a := fun hm =>
      Bool.noConfusion ((containsB_of_mem hm).symm.trans hoffT.2)
    cases ground.orSplitB hev with
    | inl h3 =>
      cases ground.orSplitB h3 with
      | inl h2 =>
        cases ground.orSplitB h2 with
        | inl h1 => exact absurd (hin _ hends.1 (Or.inl (ground.beqEqOf h1))) hT
        | inr h1 => exact absurd (hin _ hends.2 (Or.inl (ground.beqEqOf h1))) hH
      | inr h2 => exact absurd (hin _ hends.1 (Or.inr (ground.beqEqOf h2))) hT
    | inr h3 => exact absurd (hin _ hends.2 (Or.inr (ground.beqEqOf h3))) hH

/-- A plaquette's boundary meets its own links' ends. -/
private theorem nearLink_self (R : lattice.Region) (p : List (Nat × Bool))
    (e : Nat × Bool) (he : e ∈ p) :
    stableentries.nearLink R p e.1 = true := by
  refine ground.any_of_mem _ he ?_
  cases lattice.edge_ends R e with
  | inl h => rw [h.1, ground.eqBeqOf rfl, Bool.true_or, Bool.true_or, Bool.true_or]
  | inr h => rw [h.1, ground.eqBeqOf rfl, Bool.or_true, Bool.true_or, Bool.true_or]

/-- Two boundary links of one plaquette of the region are
band-adjacent at the plaquette itself. -/
private theorem plaq_adj (R : lattice.Region) (p : List (Nat × Bool))
    (hpm : p ∈ R.plaqs) (e e' : Nat × Bool) (he : e ∈ p) (he' : e' ∈ p) :
    bandAdj R e.1 e'.1 = true := by
  refine ground.any_of_mem _ hpm ?_
  rw [nearLink_self R p e he, nearLink_self R p e' he']
  rfl

/-! The closure at a two-part list: the parts pairwise off each
other's adjacency, one part a clique.  The walk from a member of the
first part keeps to it, and the walk from a member of the second
reads the whole second part. -/

/-- The step's joined members sit in the support. -/
private theorem stepAdd_sub (R : lattice.Region) (S acc : List Nat)
    (x : Nat) (hx : x ∈ stepAdd R S acc) : x ∈ S :=
  (ground.mem_filter_of _ S x hx).1

/-- A step's joined member is off the reached list and band-adjacent
to a reached member. -/
private theorem stepAdd_read (R : lattice.Region) (S acc : List Nat)
    (x : Nat) (hx : x ∈ stepAdd R S acc) :
    ¬ x ∈ acc ∧ ∃ m, m ∈ acc ∧ bandAdj R m x = true := by
  have h := (ground.mem_filter_of _ S x hx).2
  have hs := ground.andSplitB h
  refine ⟨fun hm => ?_, ?_⟩
  · have h1 := hs.1
    rw [containsB_of_mem hm] at h1
    exact Bool.noConfusion h1
  · obtain ⟨m, hm, hb⟩ := ground.mem_of_any _ acc hs.2
    exact ⟨m, hm, hb⟩

/-- The reached list's invariant across one step: every member in
the support and in the first part. -/
private theorem step_inS (R : lattice.Region) (S : List Nat)
    (inS : Nat → Bool)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
      bandAdj R x y = false)
    (acc : List Nat) (hacc : ∀ x ∈ acc, x ∈ S ∧ inS x = true) :
    ∀ z ∈ acc ++ stepAdd R S acc, z ∈ S ∧ inS z = true := by
  intro z hz
  cases ground.mem_append_of _ _ hz with
  | inl hza => exact hacc z hza
  | inr hzt =>
    have hzS := stepAdd_sub R S acc z hzt
    obtain ⟨_, m, hm, hb⟩ := stepAdd_read R S acc z hzt
    refine ⟨hzS, ?_⟩
    cases hz' : inS z with
    | true => rfl
    | false =>
      have hc := hcross m (hacc m hm).1 z hzS (hacc m hm).2 hz'
      rw [hc] at hb
      exact Bool.noConfusion hb

/-- The walk from the first part keeps to it. -/
private theorem closeGo_inS (R : lattice.Region) (S : List Nat)
    (inS : Nat → Bool)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
      bandAdj R x y = false) :
    ∀ (k : Nat) (acc : List Nat), (∀ x ∈ acc, x ∈ S ∧ inS x = true) →
      ∀ x ∈ closeGo R S k acc, x ∈ S ∧ inS x = true
  | 0, _, hacc, x, hx => hacc x hx
  | k + 1, acc, hacc, x, hx => by
    rw [closeGo_succ] at hx
    have h2 := step_inS R S inS hcross acc hacc
    cases hst : stepAdd R S acc with
    | nil =>
      rw [hst] at hx
      exact hacc x hx
    | cons y t =>
      rw [hst] at hx h2
      exact closeGo_inS R S inS hcross k (acc ++ y :: t) h2 x hx

/-- The step at a reached list inside the first part reads the
first part's own step: the second part's members join at no
adjacency. -/
private theorem stepAdd_inS (R : lattice.Region) (S : List Nat)
    (inS : Nat → Bool)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
      bandAdj R x y = false)
    (acc : List Nat) (hacc : ∀ x ∈ acc, x ∈ S ∧ inS x = true) :
    stepAdd R S acc = stepAdd R (S.filter inS) acc := by
  show S.filter (stepP R acc) = (S.filter inS).filter (stepP R acc)
  rw [filter_filter]
  refine ground.filter_congr_mem _ _ S ?_
  intro x hx
  cases hp : stepP R acc x with
  | false => cases inS x <;> rfl
  | true =>
    have hxm : x ∈ stepAdd R S acc :=
      ground.mem_filter_to _ (ground.mem_of_countOf_pos x S hx) hp
    have := (step_inS R S inS hcross acc hacc x
      (ground.mem_append_right acc hxm)).2
    rw [this]
    rfl

/-- The walk from the first part is the first part's own walk. -/
private theorem closeGo_congr (R : lattice.Region) (S : List Nat)
    (inS : Nat → Bool)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
      bandAdj R x y = false) :
    ∀ (k : Nat) (acc : List Nat), (∀ x ∈ acc, x ∈ S ∧ inS x = true) →
      closeGo R S k acc = closeGo R (S.filter inS) k acc
  | 0, _, _ => rfl
  | k + 1, acc, hacc => by
    rw [closeGo_succ, closeGo_succ, ← stepAdd_inS R S inS hcross acc hacc]
    have h2 := step_inS R S inS hcross acc hacc
    cases hst : stepAdd R S acc with
    | nil => rfl
    | cons y t =>
      rw [hst] at h2
      exact closeGo_congr R S inS hcross k (acc ++ y :: t) h2

/-- The walk stops at a reached list with the vacant join. -/
private theorem closeGo_stable (R : lattice.Region) (S : List Nat)
    (acc : List Nat) (hst : stepAdd R S acc = []) :
    ∀ k : Nat, closeGo R S k acc = acc
  | 0 => rfl
  | k + 1 => by
    rw [closeGo_succ, hst]

/-- The first step from a member of the second part joins the second
part's further members exactly. -/
private theorem stepAdd_offS (R : lattice.Region) (S : List Nat)
    (inS : Nat → Bool)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
      bandAdj R x y = false)
    (hcliq : ∀ x ∈ S, ∀ y ∈ S, inS x = false → inS y = false → x ≠ y →
      bandAdj R x y = true)
    (l : Nat) (hl : l ∈ S) (hlS : inS l = false) :
    stepAdd R S [l] = S.filter (fun x => !(decide (x = l)) && !(inS x)) := by
  refine ground.filter_congr_mem _ _ S ?_
  intro x hx
  have hxS := ground.mem_of_countOf_pos x S hx
  show (!(ground.containsB [l] x) && [l].any (fun m => bandAdj R m x))
    = (!(decide (x = l)) && !(inS x))
  by_cases hxl : x = l
  · rw [hxl, ground.containsB_head, decide_eq_true rfl]
    rfl
  · rw [containsB_of_not_mem (fun hm => by
        cases hm with
        | head => exact hxl rfl
        | tail _ h => exact nomatch h),
      decide_eq_false hxl]
    show (true && (bandAdj R l x || false)) = (true && !(inS x))
    cases hxi : inS x with
    | true =>
      rw [bandAdj_comm R l x, hcross x hxS l hl hxi hlS]
      rfl
    | false =>
      rw [hcliq l hl x hxS hlS hxi (fun h => hxl h.symm)]
      rfl

/-- The walk from a member of the second part reads the second part:
every further member joins at the first step, and the walk stops
there. -/
private theorem closeGo_offS (R : lattice.Region) (S : List Nat)
    (inS : Nat → Bool)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
      bandAdj R x y = false)
    (hcliq : ∀ x ∈ S, ∀ y ∈ S, inS x = false → inS y = false → x ≠ y →
      bandAdj R x y = true)
    (l : Nat) (hl : l ∈ S) (hlS : inS l = false) (k : Nat) (hk : 0 < k)
    (x : Nat) : x ∈ closeGo R S k [l] ↔ (x ∈ S ∧ inS x = false) := by
  cases k with
  | zero => exact absurd hk (Nat.lt_irrefl 0)
  | succ n =>
    rw [closeGo_succ, stepAdd_offS R S inS hcross hcliq l hl hlS]
    have hmemA : ∀ y, y ∈ S.filter (fun x => !(decide (x = l)) && !(inS x))
        ↔ (y ∈ S ∧ y ≠ l ∧ inS y = false) := by
      intro y
      constructor
      · intro hy
        obtain ⟨hyS, hyp⟩ := ground.mem_filter_of _ S y hy
        have hs := ground.andSplitB hyp
        refine ⟨hyS, fun h => ?_, ?_⟩
        · have h1 := hs.1
          rw [decide_eq_true h] at h1
          exact Bool.noConfusion h1
        · exact ground.boolFalseOfNot hs.2
      · intro ⟨hyS, hyl, hyi⟩
        refine ground.mem_filter_to _ hyS ?_
        rw [decide_eq_false hyl, hyi]
        rfl
    cases hA : S.filter (fun x => !(decide (x = l)) && !(inS x)) with
    | nil =>
      constructor
      · intro hx
        cases hx with
        | head => exact ⟨hl, hlS⟩
        | tail _ h => exact nomatch h
      · intro ⟨hxS, hxi⟩
        by_cases hxl : x = l
        · rw [hxl]; exact List.Mem.head []
        · have hm := (hmemA x).2 ⟨hxS, hxl, hxi⟩
          rw [hA] at hm
          exact nomatch hm
    | cons y t =>
      have hacc : ∀ z, z ∈ [l] ++ y :: t → z ∈ S ∧ inS z = false := by
        intro z hz
        cases ground.mem_append_of _ _ hz with
        | inl h1 =>
          cases h1 with
          | head => exact ⟨hl, hlS⟩
          | tail _ h => exact nomatch h
        | inr h2 =>
          rw [← hA] at h2
          have := (hmemA z).1 h2
          exact ⟨this.1, this.2.2⟩
      have hstop : stepAdd R S ([l] ++ y :: t) = [] := by
        refine ground.filter_false _ S ?_
        intro z hzS
        show (!(ground.containsB ([l] ++ y :: t) z)
          && ([l] ++ y :: t).any (fun m => bandAdj R m z)) = false
        cases hzi : inS z with
        | false =>
          have hzm : z ∈ [l] ++ y :: t := by
            by_cases hzl : z = l
            · rw [hzl]; exact List.Mem.head _
            · refine ground.mem_append_right [l] ?_
              have hm := (hmemA z).2 ⟨hzS, hzl, hzi⟩
              rw [hA] at hm
              exact hm
          rw [containsB_of_mem hzm]
          rfl
        | true =>
          have hany : ([l] ++ y :: t).any (fun m => bandAdj R m z) = false := by
            refine ground.any_false_of_all_not _ _
              (ground.all_of_mem_intro _ _ (fun m hm => ?_))
            have hmr := hacc m hm
            rw [bandAdj_comm R m z, hcross z hzS m hmr.1 hzi hmr.2]
            rfl
          rw [hany]
          cases ground.containsB ([l] ++ y :: t) z <;> rfl
      show x ∈ closeGo R S n ([l] ++ y :: t) ↔ _
      rw [closeGo_stable R S _ hstop n]
      constructor
      · exact hacc x
      · intro ⟨hxS, hxi⟩
        by_cases hxl : x = l
        · rw [hxl]; exact List.Mem.head _
        · refine ground.mem_append_right [l] ?_
          have hm := (hmemA x).2 ⟨hxS, hxl, hxi⟩
          rw [hA] at hm
          exact hm

/-! The closure is stationary: an occupied step joins a support
member off the reached list, the reached list stays distinct inside
the support, so the walk closes within the support's count of
steps. -/

/-- The walk's members sit in the support at a reached list inside
it. -/
private theorem closeGo_sub (R : lattice.Region) (S : List Nat) :
    ∀ (k : Nat) (acc : List Nat), (∀ x ∈ acc, x ∈ S) →
      ∀ x ∈ closeGo R S k acc, x ∈ S
  | 0, _, hacc, x, hx => hacc x hx
  | k + 1, acc, hacc, x, hx => by
    rw [closeGo_succ] at hx
    have h2 : ∀ z ∈ acc ++ stepAdd R S acc, z ∈ S := by
      intro z hz
      cases ground.mem_append_of _ _ hz with
      | inl h => exact hacc z h
      | inr h => exact stepAdd_sub R S acc z h
    cases hst : stepAdd R S acc with
    | nil =>
      rw [hst] at hx
      exact hacc x hx
    | cons y t =>
      rw [hst] at hx h2
      exact closeGo_sub R S k (acc ++ y :: t) h2 x hx

/-- The reached list stays distinct: a joined member sits off it and
the joined list is a filter of the distinct support. -/
private theorem closeGo_distinct (R : lattice.Region) (S : List Nat)
    (hd : ground.distinctList S) :
    ∀ (k : Nat) (acc : List Nat), ground.distinctList acc →
      ground.distinctList (closeGo R S k acc)
  | 0, _, hacc => hacc
  | k + 1, acc, hacc => by
    rw [closeGo_succ]
    have h2 : ground.distinctList (acc ++ stepAdd R S acc) :=
      distinctList_append_disjoint acc _ hacc (distinctList_filter _ S hd)
        (fun x hx hxs => (stepAdd_read R S acc x hxs).1 hx)
    cases hst : stepAdd R S acc with
    | nil => exact hacc
    | cons y t =>
      rw [hst] at h2
      exact closeGo_distinct R S hd k (acc ++ y :: t) h2

/-- An occupied step grows the reached list: the walk is stationary
or its list has grown by the step count. -/
private theorem closeGo_grow (R : lattice.Region) (S : List Nat) :
    ∀ (k : Nat) (acc : List Nat),
      stepAdd R S (closeGo R S k acc) = []
        ∨ acc.length + k ≤ (closeGo R S k acc).length
  | 0, acc => Or.inr (Nat.le_of_eq (Nat.add_zero _))
  | k + 1, acc => by
    rw [closeGo_succ]
    cases hst : stepAdd R S acc with
    | nil => exact Or.inl hst
    | cons y t =>
      cases closeGo_grow R S k (acc ++ y :: t) with
      | inl h => exact Or.inl h
      | inr h =>
        refine Or.inr (Nat.le_trans ?_ h)
        rw [ground.length_append]
        show acc.length + (k + 1) ≤ acc.length + (t.length + 1) + k
        rw [← Nat.add_assoc, Nat.add_right_comm acc.length k 1]
        exact Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le t.length)) _) k

/-- The closure's step joins the vacant list: the walk closes within
the support's count of steps at the support's distinct keys, the
count at or below the region's links. -/
theorem closure_stationary (R : lattice.Region) (S : List Nat) (l : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links) :
    stepAdd R S (closure R S l) = [] := by
  cases closeGo_grow R S R.links [l] with
  | inl h => exact h
  | inr h =>
    have hsing : ∀ x ∈ [l], x ∈ S := by
      intro x hx
      cases hx with
      | head => exact hl
      | tail _ h' => exact nomatch h'
    have hsub := closeGo_sub R S R.links [l] hsing
    have hdist : ground.distinctList (closeGo R S R.links [l]) :=
      closeGo_distinct R S hd R.links [l] (by
        intro x hx
        cases hx with
        | head =>
          rw [ground.countOf_head]
          exact Nat.le_refl 1
        | tail _ h' => exact nomatch h')
    have hle : (closeGo R S R.links [l]).length ≤ S.length :=
      ground.length_le_of_distinct_mem _ S (fun x => by
        cases hc : ground.countOf x (closeGo R S R.links [l]) with
        | zero => exact Nat.zero_le 1
        | succ n =>
          rw [← hc]
          exact hdist x (ground.mem_of_countOf_pos x _
            (by rw [hc]; exact Nat.succ_pos n))) hsub hd
    have h1 : R.links + 1 ≤ R.links := by
      rw [← Nat.add_comm]
      exact Nat.le_trans h (Nat.le_trans hle hS)
    exact absurd h1 (Nat.not_succ_le_self R.links)

/-! The closures as classes: a link's closure within a distinct
support of the region's count is saturated at the adjacency
(`closure_sat`), holds every closure of its members
(`closure_trans`) and reads its start back from every member
(`closure_symm`), so two members of one closure read one closure
(`closure_eq_of_mem`) and one component (`compOf_eq_of_mem`), and a
support member off a stated component reads its component within
the support past that component (`compOf_drop`).  The components
are the members' components: every part is some member's component
(`components_compOf`), every support member's component is a part
(`compOf_mem_components`), and two parts at distinct places share
no member (`components_disjoint`).  The head's price: a component's
link count against a floor of the window labels' Casimirs sits at or
below its content (`comp_floor`), so a head class's every component
sits below the head bound at that price (`head_floor`), the head
finite at the bound. -/

/-- The start sits in its own closure. -/
theorem mem_closure_self (R : lattice.Region) (S : List Nat) (l : Nat) :
    l ∈ closure R S l :=
  mem_closeGo R S R.links [l] l (List.Mem.head [])

/-- A closure from a support member stays in the support. -/
theorem closure_sub (R : lattice.Region) (S : List Nat) (l : Nat)
    (hl : l ∈ S) (x : Nat) (hx : x ∈ closure R S l) : x ∈ S :=
  closeGo_sub R S R.links [l] (fun y hy => by
    rw [ground.eq_of_mem_single hy]; exact hl) x hx

/-- The closure is saturated: a support member band-adjacent to a
closure member sits in the closure. -/
theorem closure_sat (R : lattice.Region) (S : List Nat) (l : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links)
    (x y : Nat) (hx : x ∈ closure R S l) (hy : y ∈ S)
    (hadj : bandAdj R x y = true) : y ∈ closure R S l := by
  have hst := closure_stationary R S l hl hd hS
  cases hc : ground.containsB (closure R S l) y with
  | true => exact mem_of_containsB hc
  | false =>
    have hy' : y ∈ stepAdd R S (closure R S l) := by
      refine ground.mem_filter_to _ hy ?_
      show (!(ground.containsB (closure R S l) y)
        && (closure R S l).any (fun m => bandAdj R m y)) = true
      rw [hc, ground.any_of_mem _ hx hadj]
      rfl
    rw [hst] at hy'
    exact nomatch hy'

/-- The walk from a list inside a saturated list stays inside it. -/
private theorem closeGo_least (R : lattice.Region) (S T : List Nat)
    (hT : ∀ x y, x ∈ T → y ∈ S → bandAdj R x y = true → y ∈ T) :
    ∀ (k : Nat) (acc : List Nat), (∀ x ∈ acc, x ∈ T) →
      ∀ x ∈ closeGo R S k acc, x ∈ T
  | 0, _, hacc, x, hx => hacc x hx
  | k + 1, acc, hacc, x, hx => by
    rw [closeGo_succ] at hx
    have h2 : ∀ z ∈ acc ++ stepAdd R S acc, z ∈ T := by
      intro z hz
      cases ground.mem_append_of _ _ hz with
      | inl h => exact hacc z h
      | inr h =>
        obtain ⟨_, m, hm, hb⟩ := stepAdd_read R S acc z h
        exact hT m z (hacc m hm) (stepAdd_sub R S acc z h) hb
    cases hst : stepAdd R S acc with
    | nil =>
      rw [hst] at hx
      exact hacc x hx
    | cons y u =>
      rw [hst] at hx h2
      exact closeGo_least R S T hT k (acc ++ y :: u) h2 x hx

/-- A closure holds every closure of its members. -/
theorem closure_trans (R : lattice.Region) (S : List Nat) (l x : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links)
    (hx : x ∈ closure R S l) (y : Nat) (hy : y ∈ closure R S x) :
    y ∈ closure R S l :=
  closeGo_least R S (closure R S l)
    (fun p q hp hq hpq => closure_sat R S l hl hd hS p q hp hq hpq)
    R.links [x] (fun z hz => by rw [ground.eq_of_mem_single hz]; exact hx) y hy

/-- A closure reads its start back from every member. -/
theorem closure_symm (R : lattice.Region) (S : List Nat) (l x : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links)
    (hx : x ∈ closure R S l) : l ∈ closure R S x := by
  have hsat : ∀ y z, y ∈ (closure R S l).filter
        (fun y => ground.containsB (closure R S y) l) → z ∈ S →
      bandAdj R y z = true →
      z ∈ (closure R S l).filter (fun y => ground.containsB (closure R S y) l) := by
    intro y z hy hz hadj
    obtain ⟨hy1, hy2⟩ := ground.mem_filter_of _ _ y hy
    have hyS : y ∈ S := closure_sub R S l hl y hy1
    have hyz : y ∈ closure R S z :=
      closure_sat R S z hz hd hS z y (mem_closure_self R S z) hyS
        (by rw [bandAdj_comm]; exact hadj)
    refine ground.mem_filter_to _ (closure_sat R S l hl hd hS y z hy1 hz hadj) ?_
    exact containsB_of_mem
      (closure_trans R S z y hz hd hS hyz l (mem_of_containsB hy2))
  have hxU := closeGo_least R S _ hsat R.links [l] (fun z hz => by
    rw [ground.eq_of_mem_single hz]
    exact ground.mem_filter_to _ (mem_closure_self R S l)
      (containsB_of_mem (mem_closure_self R S l))) x hx
  exact mem_of_containsB (ground.mem_filter_of _ _ x hxU).2

/-- Two members of one closure read one closure. -/
theorem closure_eq_of_mem (R : lattice.Region) (S : List Nat) (l x : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links)
    (hx : x ∈ closure R S l) (y : Nat) :
    y ∈ closure R S x ↔ y ∈ closure R S l :=
  ⟨fun hy => closure_trans R S l x hl hd hS hx y hy,
   fun hy => closure_trans R S x l (closure_sub R S l hl x hx) hd hS
     (closure_symm R S l x hl hd hS hx) y hy⟩

/-- Two members of one component read one component. -/
theorem compOf_eq_of_mem (R : lattice.Region) (S : List Nat) (l x : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links)
    (hx : x ∈ compOf R S l) : compOf R S x = compOf R S l := by
  have hxc : x ∈ closure R S l :=
    mem_of_containsB (ground.mem_filter_of _ S x hx).2
  refine ground.filter_congr_mem _ _ S (fun y _ => ?_)
  cases hc : ground.containsB (closure R S l) y with
  | true =>
    exact containsB_of_mem
      ((closure_eq_of_mem R S l x hl hd hS hxc y).2 (mem_of_containsB hc))
  | false =>
    refine containsB_of_not_mem (fun hm => ?_)
    have h2 := containsB_of_mem ((closure_eq_of_mem R S l x hl hd hS hxc y).1 hm)
    rw [hc] at h2
    exact Bool.noConfusion h2

/-- A support member off a stated component reads its component
within the support past that component. -/
theorem compOf_drop (R : lattice.Region) (S : List Nat) (l m : Nat)
    (hl : l ∈ S) (hd : ground.distinctList S) (hS : S.length ≤ R.links)
    (hm : m ∈ S) (hnot : ¬ m ∈ compOf R S l) :
    compOf R (S.filter (fun x => !(ground.containsB (compOf R S l) x))) m
      = compOf R S m := by
  have hcross : ∀ x ∈ S, ∀ y ∈ S,
      (!(ground.containsB (compOf R S l) x)) = true →
      (!(ground.containsB (compOf R S l) y)) = false →
      bandAdj R x y = false := by
    intro x hx y hy hxi hyi
    have hyc : y ∈ compOf R S l := mem_of_containsB (by
      cases hc : ground.containsB (compOf R S l) y with
      | true => rfl
      | false => rw [hc] at hyi; exact Bool.noConfusion hyi)
    cases hadj : bandAdj R x y with
    | false => rfl
    | true =>
      have hycl : y ∈ closure R S l :=
        mem_of_containsB (ground.mem_filter_of _ S y hyc).2
      have hxcl : x ∈ closure R S l :=
        closure_sat R S l hl hd hS y x hycl hx (by rw [bandAdj_comm]; exact hadj)
      have h2 : ground.containsB (compOf R S l) x = true :=
        containsB_of_mem (ground.mem_filter_to _ hx (containsB_of_mem hxcl))
      rw [h2] at hxi
      exact Bool.noConfusion hxi
  have hmi : (!(ground.containsB (compOf R S l) m)) = true := by
    rw [containsB_of_not_mem hnot]
    rfl
  have hacc : ∀ x ∈ [m], x ∈ S ∧ (!(ground.containsB (compOf R S l) x)) = true :=
    fun x hx => by rw [ground.eq_of_mem_single hx]; exact ⟨hm, hmi⟩
  have hcl : closure R (S.filter (fun x => !(ground.containsB (compOf R S l) x))) m
      = closure R S m :=
    (closeGo_congr R S _ hcross R.links [m] hacc).symm
  show (S.filter (fun x => !(ground.containsB (compOf R S l) x))).filter
      (ground.containsB (closure R
        (S.filter (fun x => !(ground.containsB (compOf R S l) x))) m))
    = S.filter (ground.containsB (closure R S m))
  rw [hcl, filter_filter]
  refine ground.filter_congr_mem _ _ S (fun x hx => ?_)
  have hxS : x ∈ S := ground.mem_of_countOf_pos x S hx
  show (!(ground.containsB (compOf R S l) x) && ground.containsB (closure R S m) x)
    = ground.containsB (closure R S m) x
  cases hc : ground.containsB (closure R S m) x with
  | false => cases ground.containsB (compOf R S l) x <;> rfl
  | true =>
    have hxm : x ∈ closure R S m := mem_of_containsB hc
    have hxl : ground.containsB (compOf R S l) x = false := by
      refine containsB_of_not_mem (fun hxc => ?_)
      have hxcl : x ∈ closure R S l :=
        mem_of_containsB (ground.mem_filter_of _ S x hxc).2
      have hmx : m ∈ closure R S x := closure_symm R S m x hm hd hS hxm
      have hml : m ∈ closure R S l := closure_trans R S l x hl hd hS hxcl m hmx
      exact hnot (ground.mem_filter_to _ hm (containsB_of_mem hml))
    rw [hxl]
    rfl

/-- Every part of a distinct list within the count is some member's
component. -/
private theorem partsGo_compOf (R : lattice.Region) :
    ∀ (k : Nat) (S : List Nat), S.length ≤ k → S.length ≤ R.links →
      ground.distinctList S →
      ∀ c ∈ partsGo R k S, ∃ l, l ∈ c ∧ c = compOf R S l
  | 0, [], _, _, _, _, hc => nomatch hc
  | 0, _ :: _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _, _, _, hc => nomatch hc
  | k + 1, l :: rest, hk, hR, hd, c, hc => by
    rw [partsGo_succ] at hc
    have hlc : l ∈ compOf R (l :: rest) l :=
      mem_compOf_self R (l :: rest) l (List.Mem.head rest)
    cases hc with
    | head => exact ⟨l, hlc, rfl⟩
    | tail _ hc' =>
      obtain ⟨m, hm, hcm⟩ := partsGo_compOf R k _
        (Nat.le_trans (rest_length l rest _ hlc) (Nat.le_of_succ_le_succ hk))
        (Nat.le_trans (rest_length l rest _ hlc) (Nat.le_trans (Nat.le_succ _) hR))
        (distinctList_filter _ _ hd) c hc'
      have hmS : m ∈ (l :: rest).filter (fun x =>
          !(ground.containsB (compOf R (l :: rest) l) x)) := by
        rw [hcm] at hm
        exact (ground.mem_filter_of _ _ m hm).1
      obtain ⟨hmS', hmi⟩ := ground.mem_filter_of _ (l :: rest) m hmS
      have hnot : ¬ m ∈ compOf R (l :: rest) l := fun hmc => by
        rw [containsB_of_mem hmc] at hmi
        exact Bool.noConfusion hmi
      refine ⟨m, hm, ?_⟩
      rw [hcm]
      exact compOf_drop R (l :: rest) l m (List.Mem.head rest) hd hR hmS' hnot

/-- Every member's component is a part. -/
private theorem partsGo_mem (R : lattice.Region) :
    ∀ (k : Nat) (S : List Nat), S.length ≤ k → S.length ≤ R.links →
      ground.distinctList S →
      ∀ m ∈ S, ∃ c, c ∈ partsGo R k S ∧ c = compOf R S m
  | 0, [], _, _, _, _, hm => nomatch hm
  | 0, _ :: _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _, _, _, hm => nomatch hm
  | k + 1, l :: rest, hk, hR, hd, m, hm => by
    rw [partsGo_succ]
    have hlc : l ∈ compOf R (l :: rest) l :=
      mem_compOf_self R (l :: rest) l (List.Mem.head rest)
    cases hmc : ground.containsB (compOf R (l :: rest) l) m with
    | true =>
      exact ⟨compOf R (l :: rest) l, List.Mem.head _,
        (compOf_eq_of_mem R (l :: rest) l m (List.Mem.head rest) hd hR
          (mem_of_containsB hmc)).symm⟩
    | false =>
      have hnot : ¬ m ∈ compOf R (l :: rest) l := fun h => by
        rw [containsB_of_mem h] at hmc
        exact Bool.noConfusion hmc
      have hmS : m ∈ (l :: rest).filter (fun x =>
          !(ground.containsB (compOf R (l :: rest) l) x)) :=
        ground.mem_filter_to _ hm (by rw [hmc]; rfl)
      obtain ⟨c, hc, hcm⟩ := partsGo_mem R k _
        (Nat.le_trans (rest_length l rest _ hlc) (Nat.le_of_succ_le_succ hk))
        (Nat.le_trans (rest_length l rest _ hlc) (Nat.le_trans (Nat.le_succ _) hR))
        (distinctList_filter _ _ hd) m hmS
      refine ⟨c, List.Mem.tail _ hc, ?_⟩
      rw [hcm]
      exact compOf_drop R (l :: rest) l m (List.Mem.head rest) hd hR hm hnot

/-- Every band component is some support member's component. -/
theorem components_compOf {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (c : List Nat) (hc : c ∈ components F R a) :
    ∃ l, l ∈ c ∧ c = compOf R (carrier.support F R a) l :=
  partsGo_compOf R R.links _ (support_length_le F R a) (support_length_le F R a)
    (carrier.support_distinct F R a) c hc

/-- Every support member's component is a band component. -/
theorem compOf_mem_components {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (m : Nat)
    (hm : m ∈ carrier.support F R a) :
    ∃ c, c ∈ components F R a ∧ c = compOf R (carrier.support F R a) m :=
  partsGo_mem R R.links _ (support_length_le F R a) (support_length_le F R a)
    (carrier.support_distinct F R a) m hm

/-- Two band components at distinct places share no member: the
parts' concatenation reads the distinct support member for
member. -/
theorem components_disjoint {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) (i j : Nat)
    (hij : i < j) (hj : j < (components F R a).length) (x : Nat)
    (hxi : x ∈ ground.getAt [] (components F R a) i)
    (hxj : x ∈ ground.getAt [] (components F R a) j) : False := by
  have hcount := components_countOf F R a x
  rw [ground.countOf_flatMap x (fun c => c) (components F R a)] at hcount
  have h2 : 2 ≤ ground.famFold Nat.add 0 (fun c => ground.countOf x c)
      (components F R a) :=
    Nat.le_trans (Nat.add_le_add (ground.countOf_pos_of_mem hxi)
      (ground.countOf_pos_of_mem hxj))
      (ground.famFold_two_le (fun c => ground.countOf x c) [] _ i j hij hj)
  rw [hcount] at h2
  have hle : ground.countOf x (carrier.support F R a) ≤ 1 := by
    cases hc : ground.countOf x (carrier.support F R a) with
    | zero => exact Nat.zero_le 1
    | succ n =>
      rw [← hc]
      exact carrier.support_distinct F R a x
        (ground.mem_of_countOf_pos x _ (by rw [hc]; exact Nat.succ_pos n))
  exact absurd (Nat.le_trans h2 hle) (by decide)

/-- A component's link count against the window's floor read
(`fusion.belowFloor`) sits at or below its content: every occupied
link's label sits among the below-cutoff labels and reads its
Casimir at or beyond the floor. -/
theorem comp_floor {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (ha : a.length = R.links) (K fl : Nat)
    (hlab : ∀ l, l ∈ a → l ∈ F.unit :: F.below K)
    (hfl : fusion.belowFloor F K fl)
    (c : List Nat) (hc : c ∈ components F R a) :
    c.length * fl ≤ compContent F a c := by
  obtain ⟨_, _, hcl⟩ := components_compOf F R a c hc
  have hsub : ∀ x, x ∈ c → x ∈ carrier.support F R a := fun x hx => by
    rw [hcl] at hx
    exact (ground.mem_filter_of _ _ x hx).1
  show c.length * fl ≤ carrier.contentN F (c.map (ground.getAt F.unit a))
  rw [carrier.contentN_fam, ground.famFold_map, ← ground.famFold_const fl c]
  refine ground.famFold_le _ _ c (fun x hx => ?_)
  obtain ⟨hxr, hocc⟩ := ground.mem_filter_of _ _ x (hsub x hx)
  have hxl : x < a.length := by
    rw [ha]
    exact ground.ltOfMemRange hxr
  have hmem : ground.getAt F.unit a x ∈ [F.unit] ++ F.below K :=
    hlab _ (ground.mem_getAt F.unit a x hxl)
  have hne : F.eqL (ground.getAt F.unit a x) F.unit = false :=
    ground.boolFalseOfNot hocc
  show fl ≤ (if F.eqL (ground.getAt F.unit a x) F.unit then 0
    else F.c2N (ground.getAt F.unit a x))
  rw [if_neg (fun h => by rw [hne] at h; exact Bool.noConfusion h)]
  cases ground.mem_append_of _ _ hmem with
  | inl h1 =>
    rw [ground.eq_of_mem_single h1, F.eqLRefl] at hne
    exact Bool.noConfusion hne
  | inr h2 => exact of_decide_eq_true (ground.all_of_mem _ _ hfl _ h2)

/-- At a head class every component's link count against the floor
sits below the head bound. -/
theorem head_floor {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (ha : a.length = R.links) (K fl lamH : Nat)
    (hlab : ∀ l, l ∈ a → l ∈ F.unit :: F.below K)
    (hfl : fusion.belowFloor F K fl)
    (hh : headAt F R lamH a) (c : List Nat) (hc : c ∈ components F R a) :
    c.length * fl < lamH :=
  Nat.lt_of_le_of_lt (comp_floor F R a ha K fl hlab hfl c hc)
    (((headAt_read F R lamH a).1 hh).1 c hc)

/-! The transport along a region action: the band adjacency, the
closures, the components and the meeting read move along the link
and vertex maps with the plaquette list reindexed at the action's
permutation (`lattice.plaqPerm_any`), so a class's components are
one family across the action, member for member. -/

/-- The band adjacency transports along a region action. -/
theorem bandAdj_perm (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (l1 l2 : Nat)
    (h1 : l1 < R.links) (h2 : l2 < R.links) :
    bandAdj R (t l1) (t l2) = bandAdj R l1 l2 := by
  show R.plaqs.any _ = R.plaqs.any _
  refine lattice.plaqPerm_any R t (fun _ => false) pm pm' hpm _ _ (fun q hq => ?_)
  have hc := (lattice.plaqPermRead_at R t _ pm pm' hpm q hq).2.2.2.2
  have hkeys : ((ground.getAt [] R.plaqs q).all (fun e => e.1 < R.links)) = true :=
    (lattice.plaqRead_word R hpr _ (ground.mem_getAt [] R.plaqs q hq)).2
  have e1 : ∀ l, l < R.links →
      stableentries.nearLink R (ground.getAt [] R.plaqs (pm q)) (t l)
        = stableentries.nearLink R (ground.getAt [] R.plaqs q) l := by
    intro l hl
    rw [← stableentries.nearLink_cyc R _ _ hc (t l),
      stableentries.nearLink_move R hw t s v w h _ hkeys l hl]
  show (stableentries.nearLink R (ground.getAt [] R.plaqs (pm q)) (t l1)
      && stableentries.nearLink R (ground.getAt [] R.plaqs (pm q)) (t l2))
    = (stableentries.nearLink R (ground.getAt [] R.plaqs q) l1
      && stableentries.nearLink R (ground.getAt [] R.plaqs q) l2)
  rw [e1 l1 h1, e1 l2 h2]

/-- The one-step guard transports: at a reached list moved along the
action the guard at the moved link reads the guard at the link. -/
private theorem stepP_perm (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (acc acc' : List Nat)
    (hacc : ∀ x, x < R.links → (x ∈ acc' ↔ s x ∈ acc))
    (haccR : ∀ x ∈ acc, x < R.links) (hacc'R : ∀ x ∈ acc', x < R.links)
    (l : Nat) (hl : l < R.links) : stepP R acc' (t l) = stepP R acc l := by
  have hiso := lattice.linkIso_all R t s h.1
  have htl : t l < R.links := (hiso l hl).2.2.1
  have hc : ground.containsB acc' (t l) = ground.containsB acc l := by
    cases hm : ground.containsB acc l with
    | true =>
      refine containsB_of_mem ((hacc (t l) htl).2 ?_)
      rw [(hiso l hl).1]
      exact mem_of_containsB hm
    | false =>
      refine containsB_of_not_mem (fun hin => ?_)
      have h2 := (hacc (t l) htl).1 hin
      rw [(hiso l hl).1] at h2
      rw [containsB_of_mem h2] at hm
      exact Bool.noConfusion hm
  have ha : acc'.any (fun m => bandAdj R m (t l)) = acc.any (fun m => bandAdj R m l) := by
    cases hb : acc.any (fun m => bandAdj R m l) with
    | true =>
      obtain ⟨m, hm, hmb⟩ := ground.mem_of_any _ acc hb
      have hmR := haccR m hm
      refine ground.any_of_mem _ ((hacc (t m) (hiso m hmR).2.2.1).2 ?_) ?_
      · rw [(hiso m hmR).1]
        exact hm
      · rw [bandAdj_perm R hw hpr t s v w pm pm' h hpm m l hmR hl]
        exact hmb
    | false =>
      refine ground.any_false_of_all_not _ _ (ground.all_of_mem_intro _ _ (fun m' hm' => ?_))
      have hm'R := hacc'R m' hm'
      have hsm : s m' ∈ acc := (hacc m' hm'R).1 hm'
      have hall := ground.all_of_mem _ _ (ground.all_not_of_any_false _ acc hb) _ hsm
      have e : bandAdj R m' (t l) = bandAdj R (s m') l := by
        rw [← bandAdj_perm R hw hpr t s v w pm pm' h hpm (s m') l (hiso m' hm'R).2.2.2 hl,
          (hiso m' hm'R).2.1]
      show (!(bandAdj R m' (t l))) = true
      rw [e]
      exact hall
  show (!(ground.containsB acc' (t l)) && acc'.any (fun m => bandAdj R m (t l)))
    = (!(ground.containsB acc l) && acc.any (fun m => bandAdj R m l))
  rw [hc, ha]

/-- One step's joined members transport. -/
private theorem stepAdd_perm (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (S S' acc acc' : List Nat)
    (hS : ∀ x, x < R.links → (x ∈ S' ↔ s x ∈ S))
    (hacc : ∀ x, x < R.links → (x ∈ acc' ↔ s x ∈ acc))
    (haccR : ∀ x ∈ acc, x < R.links) (hacc'R : ∀ x ∈ acc', x < R.links)
    (x : Nat) (hx : x < R.links) :
    x ∈ stepAdd R S' acc' ↔ s x ∈ stepAdd R S acc := by
  have hiso := lattice.linkIso_all R t s h.1
  have hsx : s x < R.links := (hiso x hx).2.2.2
  have hp : stepP R acc' x = stepP R acc (s x) := by
    rw [← stepP_perm R hw hpr t s v w pm pm' h hpm acc acc' hacc haccR hacc'R (s x) hsx,
      (hiso x hx).2.1]
  constructor
  · intro hm
    obtain ⟨h1, h2⟩ := ground.mem_filter_of _ _ x hm
    refine ground.mem_filter_to _ ((hS x hx).1 h1) ?_
    rw [← hp]
    exact h2
  · intro hm
    obtain ⟨h1, h2⟩ := ground.mem_filter_of _ _ (s x) hm
    refine ground.mem_filter_to _ ((hS x hx).2 h1) ?_
    rw [hp]
    exact h2

/-- One step's vacancy transports. -/
private theorem stepAdd_perm_nil (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (S S' acc acc' : List Nat)
    (hS : ∀ x, x < R.links → (x ∈ S' ↔ s x ∈ S))
    (hSR : ∀ x ∈ S, x < R.links) (hS'R : ∀ x ∈ S', x < R.links)
    (hacc : ∀ x, x < R.links → (x ∈ acc' ↔ s x ∈ acc))
    (haccR : ∀ x ∈ acc, x < R.links) (hacc'R : ∀ x ∈ acc', x < R.links) :
    stepAdd R S' acc' = [] ↔ stepAdd R S acc = [] := by
  have hiso := lattice.linkIso_all R t s h.1
  constructor
  · intro hn
    refine ground.nil_of_not_mem _ (fun y hy => ?_)
    have hyR := hSR y (ground.mem_filter_of _ S y hy).1
    have h2 : t y ∈ stepAdd R S' acc' := by
      refine (stepAdd_perm R hw hpr t s v w pm pm' h hpm S S' acc acc' hS hacc haccR
        hacc'R (t y) (hiso y hyR).2.2.1).2 ?_
      rw [(hiso y hyR).1]
      exact hy
    rw [hn] at h2
    exact nomatch h2
  · intro hn
    refine ground.nil_of_not_mem _ (fun y hy => ?_)
    have hyR := hS'R y (ground.mem_filter_of _ S' y hy).1
    have h2 := (stepAdd_perm R hw hpr t s v w pm pm' h hpm S S' acc acc' hS hacc haccR
      hacc'R y hyR).1 hy
    rw [hn] at h2
    exact nomatch h2

/-- The walk transports along the action, member for member. -/
private theorem closeGo_perm (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (S S' : List Nat)
    (hS : ∀ x, x < R.links → (x ∈ S' ↔ s x ∈ S))
    (hSR : ∀ x ∈ S, x < R.links) (hS'R : ∀ x ∈ S', x < R.links) :
    ∀ (k : Nat) (acc acc' : List Nat),
      (∀ x, x < R.links → (x ∈ acc' ↔ s x ∈ acc)) →
      (∀ x ∈ acc, x < R.links) → (∀ x ∈ acc', x < R.links) →
      ∀ x, x < R.links → (x ∈ closeGo R S' k acc' ↔ s x ∈ closeGo R S k acc)
  | 0, _, _, hacc, _, _, x, hx => hacc x hx
  | k + 1, acc, acc', hacc, haccR, hacc'R, x, hx => by
    rw [closeGo_succ, closeGo_succ]
    have hnil := stepAdd_perm_nil R hw hpr t s v w pm pm' h hpm S S' acc acc' hS hSR
      hS'R hacc haccR hacc'R
    have hstep := stepAdd_perm R hw hpr t s v w pm pm' h hpm S S' acc acc' hS hacc
      haccR hacc'R
    cases hst : stepAdd R S acc with
    | nil =>
      rw [hnil.2 hst]
      exact hacc x hx
    | cons y u =>
      cases hst' : stepAdd R S' acc' with
      | nil =>
        have h2 := hnil.1 hst'
        rw [hst] at h2
        exact nomatch h2
      | cons y' u' =>
        have hacc2 : ∀ z, z < R.links → (z ∈ acc' ++ y' :: u' ↔ s z ∈ acc ++ y :: u) := by
          intro z hz
          rw [← hst, ← hst']
          constructor
          · intro hm
            cases ground.mem_append_of _ _ hm with
            | inl h1 => exact ground.mem_append_left _ ((hacc z hz).1 h1)
            | inr h2 => exact ground.mem_append_right _ ((hstep z hz).1 h2)
          · intro hm
            cases ground.mem_append_of _ _ hm with
            | inl h1 => exact ground.mem_append_left _ ((hacc z hz).2 h1)
            | inr h2 => exact ground.mem_append_right _ ((hstep z hz).2 h2)
        have haccR2 : ∀ z ∈ acc ++ y :: u, z < R.links := by
          intro z hz
          rw [← hst] at hz
          cases ground.mem_append_of _ _ hz with
          | inl h1 => exact haccR z h1
          | inr h2 => exact hSR z (ground.mem_filter_of _ S z h2).1
        have hacc'R2 : ∀ z ∈ acc' ++ y' :: u', z < R.links := by
          intro z hz
          rw [← hst'] at hz
          cases ground.mem_append_of _ _ hz with
          | inl h1 => exact hacc'R z h1
          | inr h2 => exact hS'R z (ground.mem_filter_of _ S' z h2).1
        exact closeGo_perm R hw hpr t s v w pm pm' h hpm S S' hS hSR hS'R k
          (acc ++ y :: u) (acc' ++ y' :: u') hacc2 haccR2 hacc'R2 x hx

/-- A closure transports along the action: the moved link's closure
within the moved support is the link's closure moved, member for
member. -/
theorem closure_perm (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (S S' : List Nat)
    (hS : ∀ x, x < R.links → (x ∈ S' ↔ s x ∈ S))
    (hSR : ∀ x ∈ S, x < R.links) (hS'R : ∀ x ∈ S', x < R.links)
    (l : Nat) (hl : l < R.links) (x : Nat) (hx : x < R.links) :
    x ∈ closure R S' (t l) ↔ s x ∈ closure R S l := by
  have hiso := lattice.linkIso_all R t s h.1
  refine closeGo_perm R hw hpr t s v w pm pm' h hpm S S' hS hSR hS'R R.links [l] [t l]
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_) x hx
  · constructor
    · intro hm
      rw [ground.eq_of_mem_single hm, (hiso l hl).1]
      exact List.Mem.head []
    · intro hm
      have hz' : z = t l := by
        rw [← ground.eq_of_mem_single hm, (hiso z hz).2.1]
      rw [hz']
      exact List.Mem.head []
  · rw [ground.eq_of_mem_single hz]
    exact hl
  · rw [ground.eq_of_mem_single hz]
    exact (hiso l hl).2.2.1

/-- A component transports along the action, member for member. -/
theorem compOf_perm (R : lattice.Region) (hw : lattice.wellRead R)
    (hpr : lattice.plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : lattice.isoRead R R t s v w (fun _ => false))
    (hpm : lattice.plaqPermRead R t (fun _ => false) pm pm') (S S' : List Nat)
    (hS : ∀ x, x < R.links → (x ∈ S' ↔ s x ∈ S))
    (hSR : ∀ x ∈ S, x < R.links) (hS'R : ∀ x ∈ S', x < R.links)
    (l : Nat) (hl : l < R.links) (x : Nat) (hx : x < R.links) :
    x ∈ compOf R S' (t l) ↔ s x ∈ compOf R S l := by
  have hcl := closure_perm R hw hpr t s v w pm pm' h hpm S S' hS hSR hS'R l hl x hx
  constructor
  · intro hm
    obtain ⟨h1, h2⟩ := ground.mem_filter_of _ S' x hm
    exact ground.mem_filter_to _ ((hS x hx).1 h1)
      (containsB_of_mem (hcl.1 (mem_of_containsB h2)))
  · intro hm
    obtain ⟨h1, h2⟩ := ground.mem_filter_of _ S (s x) hm
    exact ground.mem_filter_to _ ((hS x hx).2 h1)
      (containsB_of_mem (hcl.2 (mem_of_containsB h2)))

/-- A band component is a distinct key list below the region's
count. -/
theorem components_shape {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (c : List Nat) (hc : c ∈ components F R a) :
    ground.distinctList c ∧ ∀ x ∈ c, x < R.links := by
  obtain ⟨_, _, hcl⟩ := components_compOf F R a c hc
  rw [hcl]
  exact ⟨distinctList_filter _ _ (carrier.support_distinct F R a),
    fun x hx => ground.ltOfMemRange
      (ground.mem_filter_of _ _ x (ground.mem_filter_of _ _ x hx).1).1⟩

/-- A band component holds a member. -/
theorem components_occupied {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a : List L) (c : List Nat) (hc : c ∈ components F R a) : ∃ y, y ∈ c :=
  match components_compOf F R a c hc with
  | ⟨l, hl, _⟩ => ⟨l, hl⟩

/-- A plaquette's meeting of a vertex list, read at the keys. -/
private def keyMeet (R : lattice.Region) (vs : List Nat) (k : Nat) : Bool :=
  ground.containsB vs (ground.getAt 0 R.tail k)
    || ground.containsB vs (ground.getAt 0 R.head k)

private theorem meetsB_keys (R : lattice.Region) (vs : List Nat)
    (p : List (Nat × Bool)) : meetsB R vs p = p.any (fun e => keyMeet R vs e.1) := by
  refine ground.any_congr_all _ _ (fun e => ?_) p
  cases e with
  | mk k b =>
    cases b with
    | true => rfl
    | false =>
      show (ground.containsB vs (ground.getAt 0 R.head k)
          || ground.containsB vs (ground.getAt 0 R.tail k))
        = (ground.containsB vs (ground.getAt 0 R.tail k)
          || ground.containsB vs (ground.getAt 0 R.head k))
      rw [Bool.or_comm]

/-- The meeting read is one value across a plaquette's cyclic
readings. -/
theorem meetsB_cyc (R : lattice.Region) (vs : List Nat) (w w' : List (Nat × Bool))
    (hc : lattice.cycEq w w' = true) : meetsB R vs w = meetsB R vs w' := by
  rw [meetsB_keys, meetsB_keys]
  exact lattice.cycEq_any_keys (fun k => keyMeet R vs k) w w' hc

/-- The meeting read transports: a vertex list moved along the vertex
map meets the moved plaquette exactly where the list meets the
plaquette. -/
theorem meetsB_move (R : lattice.Region) (hw : lattice.wellRead R)
    (t s v w : Nat → Nat) (h : lattice.isoRead R R t s v w (fun _ => false))
    (vs vs' : List Nat) (hvs : ∀ y, y < R.verts → (v y ∈ vs' ↔ y ∈ vs))
    (p : List (Nat × Bool)) (hp : (p.all (fun e => e.1 < R.links)) = true) :
    meetsB R vs' (lattice.moveWord t (fun _ => false) p) = meetsB R vs p := by
  have hcb : ∀ y, y < R.verts → ground.containsB vs' (v y) = ground.containsB vs y := by
    intro y hy
    cases hm : ground.containsB vs y with
    | true => exact containsB_of_mem ((hvs y hy).2 (mem_of_containsB hm))
    | false =>
      refine containsB_of_not_mem (fun hin => ?_)
      rw [containsB_of_mem ((hvs y hy).1 hin)] at hm
      exact Bool.noConfusion hm
  rw [meetsB_keys, meetsB_keys]
  show (p.map (fun e => (t e.1, xor e.2 ((fun _ => false) e.1)))).any
      (fun e => keyMeet R vs' e.1) = _
  rw [ground.any_map]
  refine ground.any_congr_of_mem _ _ p (fun e he => ?_)
  have hk : e.1 < R.links := of_decide_eq_true (ground.all_of_mem _ p hp e he)
  show (ground.containsB vs' (ground.getAt 0 R.tail (t e.1))
      || ground.containsB vs' (ground.getAt 0 R.head (t e.1)))
    = (ground.containsB vs (ground.getAt 0 R.tail e.1)
      || ground.containsB vs (ground.getAt 0 R.head e.1))
  rw [(lattice.endsMoved_vac R t v h.2.2 e.1 hk).1,
    (lattice.endsMoved_vac R t v h.2.2 e.1 hk).2,
    hcb _ (lattice.endLt R hw e.1 hk).1, hcb _ (lattice.endLt R hw e.1 hk).2]

/-- The separation read exchanges its two configurations. -/
theorem sepBeyond_comm {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) : sepBeyond F R a b ↔ sepBeyond F R b a := by
  have key : ∀ (P Q : List (Nat × Bool) → Bool),
      R.plaqs.all (fun p => !(P p) || !(Q p)) = true →
      R.plaqs.all (fun p => !(Q p) || !(P p)) = true := by
    intro P Q hb
    refine ground.all_of_mem_intro _ _ (fun p hp => ?_)
    have h2 := ground.all_of_mem _ _ hb p hp
    show (!(Q p) || !(P p)) = true
    rw [Bool.or_comm]
    exact h2
  exact ⟨fun hs => key _ _ hs, fun hs => key _ _ hs⟩

/-- The slab read's members: a pair of components at ascending places
separated beyond the band. -/
theorem slabAt_iff {L : Type} (F : fusion.Data L) (R : lattice.Region) (a : List L) :
    slabAt F R a = true ↔ ∃ i j, i < j ∧ j < (components F R a).length
      ∧ sepBeyond F R (compConf F R a (ground.getAt [] (components F R a) i))
          (compConf F R a (ground.getAt [] (components F R a) j)) := by
  constructor
  · intro hb
    obtain ⟨i, _, hi'⟩ := ground.mem_of_any _ _ hb
    obtain ⟨j, hj, hij⟩ := ground.mem_of_any _ _ hi'
    have hs := ground.andSplitB hij
    exact ⟨i, j, of_decide_eq_true hs.1, ground.ltOfMemRange hj, of_decide_eq_true hs.2⟩
  · intro ⟨i, j, hij, hj, hsep⟩
    refine ground.any_of_mem _ (ground.memRange (Nat.lt_trans hij hj))
      (ground.any_of_mem _ (ground.memRange hj) ?_)
    show (decide (i < j) && decide (sepBeyond F R _ _)) = true
    rw [decide_eq_true hij, decide_eq_true hsep]
    rfl

/-- The parts at a two-part list: the parts inside the first part
are the first part's own, and the parts off it are the second part
at its occupancy. -/
private theorem partsGo_split (R : lattice.Region) (inS : Nat → Bool) :
    ∀ (k : Nat) (S : List Nat), S.length ≤ k → S.length ≤ R.links →
      (∀ x ∈ S, ∀ y ∈ S, inS x = true → inS y = false →
        bandAdj R x y = false) →
      (∀ x ∈ S, ∀ y ∈ S, inS x = false → inS y = false → x ≠ y →
        bandAdj R x y = true) →
      (partsGo R k S).filter (fun c => c.any inS)
          = partsGo R k (S.filter inS)
        ∧ (partsGo R k S).filter (fun c => !(c.any inS))
          = (if (S.filter (fun x => !(inS x))).length = 0 then []
            else [S.filter (fun x => !(inS x))])
  | 0, [], _, _, _, _ => ⟨rfl, rfl⟩
  | 0, _ :: _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _, _, _ => ⟨rfl, rfl⟩
  | k + 1, l :: rest, hk, hR, hcross, hcliq => by
    have hsingle : ∀ x ∈ [l], x ∈ l :: rest ∧ inS x = inS l := by
      intro x hx
      cases hx with
      | head => exact ⟨List.Mem.head rest, rfl⟩
      | tail _ h => exact nomatch h
    have hsub : ∀ (P : Nat → Bool) (x : Nat), x ∈ (l :: rest).filter P →
        x ∈ l :: rest := fun P x hx => (ground.mem_filter_of P _ x hx).1
    have hlc : l ∈ compOf R (l :: rest) l :=
      mem_compOf_self R (l :: rest) l (List.Mem.head rest)
    have hlen : ((l :: rest).filter (fun x =>
        !(ground.containsB (compOf R (l :: rest) l) x))).length ≤ rest.length :=
      rest_length l rest _ hlc
    have hIH := partsGo_split R inS k
      ((l :: rest).filter (fun x =>
        !(ground.containsB (compOf R (l :: rest) l) x)))
      (Nat.le_trans hlen (Nat.le_of_succ_le_succ hk))
      (Nat.le_trans hlen (Nat.le_trans (Nat.le_succ _) hR))
      (fun x hx y hy => hcross x (hsub _ x hx) y (hsub _ y hy))
      (fun x hx y hy => hcliq x (hsub _ x hx) y (hsub _ y hy))
    cases hl : inS l with
    | true =>
      have hacc : ∀ x ∈ [l], x ∈ l :: rest ∧ inS x = true := fun x hx =>
        ⟨(hsingle x hx).1, (hsingle x hx).2.trans hl⟩
      have hclS : ∀ x ∈ closure R (l :: rest) l, x ∈ l :: rest ∧ inS x = true :=
        closeGo_inS R (l :: rest) inS hcross R.links [l] hacc
      have hfc : (l :: rest).filter inS = l :: rest.filter inS :=
        ground.filter_cons_true hl
      have hc' : compOf R (l :: rest.filter inS) l = compOf R (l :: rest) l := by
        rw [← hfc]
        show ((l :: rest).filter inS).filter
            (ground.containsB (closure R ((l :: rest).filter inS) l))
          = (l :: rest).filter (ground.containsB (closure R (l :: rest) l))
        rw [show closure R ((l :: rest).filter inS) l = closure R (l :: rest) l
          from (closeGo_congr R (l :: rest) inS hcross R.links [l] hacc).symm,
          filter_filter]
        refine ground.filter_congr_mem _ _ (l :: rest) ?_
        intro x _
        cases hcx : ground.containsB (closure R (l :: rest) l) x with
        | true =>
          rw [(hclS x (mem_of_containsB hcx)).2]
          rfl
        | false => cases inS x <;> rfl
      have hcany : (compOf R (l :: rest) l).any inS = true :=
        ground.any_of_mem _ hlc hl
      have hL2 : ((l :: rest).filter (fun x =>
            !(ground.containsB (compOf R (l :: rest) l) x))).filter inS
          = (l :: rest.filter inS).filter (fun x =>
            !(ground.containsB (compOf R (l :: rest) l) x)) := by
        rw [← hfc, filter_filter, filter_filter]
        refine ground.filter_congr _ _ (fun x => ?_) (l :: rest)
        cases ground.containsB (compOf R (l :: rest) l) x <;> cases inS x <;> rfl
      have hind : ((l :: rest).filter (fun x =>
            !(ground.containsB (compOf R (l :: rest) l) x))).filter
              (fun x => !(inS x))
          = (l :: rest).filter (fun x => !(inS x)) := by
        rw [filter_filter]
        refine ground.filter_congr_mem _ _ (l :: rest) ?_
        intro x _
        cases hxi : inS x with
        | true => cases ground.containsB (compOf R (l :: rest) l) x <;> rfl
        | false =>
          have hcx : ground.containsB (compOf R (l :: rest) l) x = false := by
            refine containsB_of_not_mem (fun hm => ?_)
            have h2 := (hclS x (mem_of_containsB
              (ground.mem_filter_of _ (l :: rest) x hm).2)).2
            rw [hxi] at h2
            exact Bool.noConfusion h2
          rw [hcx]
          rfl
      refine ⟨?_, ?_⟩
      · rw [partsGo_succ, hfc, partsGo_succ, hc', ← hL2,
          @ground.filter_cons_true (List Nat) (fun c : List Nat => c.any inS) _ _ hcany,
          hIH.1]
      · rw [partsGo_succ,
          @ground.filter_cons_false (List Nat) (fun c : List Nat => !(c.any inS)) _ _
            (by rw [hcany]; rfl),
          hIH.2, hind]
    | false =>
      have hpos : 0 < R.links :=
        Nat.lt_of_lt_of_le (Nat.succ_pos rest.length) hR
      have hchar : ∀ x, x ∈ closure R (l :: rest) l ↔
          (x ∈ l :: rest ∧ inS x = false) :=
        closeGo_offS R (l :: rest) inS hcross hcliq l (List.Mem.head rest) hl
          R.links hpos
      have hcEq : compOf R (l :: rest) l = (l :: rest).filter (fun x => !(inS x)) := by
        refine ground.filter_congr_mem _ _ (l :: rest) ?_
        intro x hx
        have hxm := ground.mem_of_countOf_pos x _ hx
        cases hxi : inS x with
        | true =>
          refine containsB_of_not_mem (fun hm => ?_)
          have h2 := ((hchar x).1 hm).2
          rw [hxi] at h2
          exact Bool.noConfusion h2
        | false => exact containsB_of_mem ((hchar x).2 ⟨hxm, hxi⟩)
      have hL' : (l :: rest).filter (fun x =>
            !(ground.containsB (compOf R (l :: rest) l) x))
          = (l :: rest).filter inS := by
        refine ground.filter_congr_mem _ _ (l :: rest) ?_
        intro x hx
        have hxm := ground.mem_of_countOf_pos x _ hx
        rw [hcEq, containsB_filter_mem _ (l :: rest) x hxm]
        cases inS x <;> rfl
      have hcany : (compOf R (l :: rest) l).any inS = false := by
        rw [hcEq]
        refine ground.any_false_of_all_not _ _ (ground.all_of_mem_intro _ _ ?_)
        intro x hx
        have h2 := (ground.mem_filter_of _ (l :: rest) x hx).2
        cases hxi : inS x with
        | false => rfl
        | true => rw [hxi] at h2; exact Bool.noConfusion h2
      have hfc : (l :: rest).filter inS = rest.filter inS :=
        ground.filter_cons_false hl
      have hfuel : partsGo R (k + 1) (rest.filter inS)
          = partsGo R k (rest.filter inS) :=
        partsGo_fuel R k _ (Nat.le_trans (length_filter_le _ rest)
          (Nat.le_of_succ_le_succ hk))
      have hidem : ((l :: rest).filter inS).filter inS = (l :: rest).filter inS := by
        rw [filter_filter]
        exact ground.filter_congr _ _ (fun x => by cases inS x <;> rfl) (l :: rest)
      have hvac : ((l :: rest).filter inS).filter (fun x => !(inS x)) = [] := by
        rw [filter_filter]
        exact ground.filter_false _ (l :: rest) (fun x _ => by cases inS x <;> rfl)
      have hind : (l :: rest).filter (fun x => !(inS x))
          = l :: rest.filter (fun x => !(inS x)) :=
        ground.filter_cons_true (by rw [hl]; rfl)
      rw [hL'] at hIH
      rw [partsGo_succ, hL']
      refine ⟨?_, ?_⟩
      · rw [@ground.filter_cons_false (List Nat) (fun c : List Nat => c.any inS) _ _ hcany,
          hIH.1, hidem, hfc, hfuel]
      · rw [@ground.filter_cons_true (List Nat) (fun c : List Nat => !(c.any inS)) _ _
            (by rw [hcany]; rfl),
          hIH.2, hvac, if_pos (show ([] : List Nat).length = 0 from rfl),
          hcEq, hind, if_neg (fun h => Nat.noConfusion h)]

/-- The border row: at a plaquette of the region off the class's
band neighborhood, the far row's one target reads the class's
components with one further component, the plaquette's links in the
region's key order; the loop's links are pairwise adjacent at the
plaquette's own boundary and off every occupied link's adjacency. -/
theorem components_border {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (hw : lattice.wellRead R) (hpr : lattice.plaqRead R)
    (a : List L) (p : List (Nat × Bool)) (hpm : p ∈ R.plaqs)
    (hth : F.eqL F.theta F.unit = false) (hoff : offBand F R a p = true) :
    (components F R (stableentries.farConf F R a p)).filter (fun c =>
        c.any (fun x => !(F.eqL (ground.getAt F.unit a x) F.unit)))
      = components F R a
    ∧ (components F R (stableentries.farConf F R a p)).filter (fun c =>
        !(c.any (fun x => !(F.eqL (ground.getAt F.unit a x) F.unit))))
      = [(List.range R.links).filter (fun l => p.any (fun e => e.1 == l))] := by
  have hpw := lattice.plaqRead_word R hpr p hpm
  have hpk : (p.all (fun e => e.1 < R.links)) = true := hpw.2
  have hfar := offBand_far F R a p hoff
  have hlab : ∀ x, x < R.links →
      ground.getAt F.unit (stableentries.farConf F R a p) x
        = if p.any (fun e => e.1 == x) then F.theta
          else ground.getAt F.unit a x := by
    intro x hx
    show ground.getAt F.unit ((List.range R.links).map (fun l =>
      if p.any (fun e => e.1 == l) then F.theta
      else ground.getAt F.unit a l)) x = _
    rw [ground.getAt_map 0 F.unit _ (List.range R.links) x
        (by rw [ground.length_range]; exact hx),
      ground.getAt_range R.links x hx]
  have hon : ∀ x, x < R.links → (p.any (fun e => e.1 == x)) = true →
      F.eqL (ground.getAt F.unit a x) F.unit = true :=
    fun x hx hxp => stableentries.far_unit F R p a hw hfar x hx hxp
  have hoccB : ∀ x, x < R.links →
      (!(F.eqL (ground.getAt F.unit (stableentries.farConf F R a p) x) F.unit))
        = ((p.any (fun e => e.1 == x))
          || !(F.eqL (ground.getAt F.unit a x) F.unit)) := by
    intro x hx
    rw [hlab x hx]
    cases hxp : (p.any (fun e => e.1 == x)) with
    | true =>
      rw [if_pos rfl, hth, hon x hx hxp]
      rfl
    | false => rw [if_neg (fun h => Bool.noConfusion h)]; rfl
  have hmemS : ∀ x, x ∈ carrier.support F R (stableentries.farConf F R a p) →
      x < R.links ∧ ((p.any (fun e => e.1 == x))
        || !(F.eqL (ground.getAt F.unit a x) F.unit)) = true := by
    intro x hx
    obtain ⟨hxr, hxo⟩ := ground.mem_filter_of _ (List.range R.links) x hx
    have hxl := ground.ltOfMemRange hxr
    rw [hoccB x hxl] at hxo
    exact ⟨hxl, hxo⟩
  have hcross : ∀ x ∈ carrier.support F R (stableentries.farConf F R a p),
      ∀ y ∈ carrier.support F R (stableentries.farConf F R a p),
      (!(F.eqL (ground.getAt F.unit a x) F.unit)) = true →
      (!(F.eqL (ground.getAt F.unit a y) F.unit)) = false →
      bandAdj R x y = false := by
    intro x hx y hy hxi hyi
    obtain ⟨hxl, _⟩ := hmemS x hx
    obtain ⟨hyl, hyo⟩ := hmemS y hy
    rw [hyi] at hyo
    have hyp : (p.any (fun e => e.1 == y)) = true := by
      cases hq : (p.any (fun e => e.1 == y)) with
      | true => rfl
      | false => rw [hq] at hyo; exact Bool.noConfusion hyo
    obtain ⟨e, he, hey⟩ := ground.mem_of_any _ p hyp
    rw [← ground.beqEqOf hey]
    exact offBand_nonadj F R hw a p hoff x hxl
      (ground.boolFalseOfNot hxi) e he
      (of_decide_eq_true (ground.all_of_mem _ p hpk e he))
  have hcliq : ∀ x ∈ carrier.support F R (stableentries.farConf F R a p),
      ∀ y ∈ carrier.support F R (stableentries.farConf F R a p),
      (!(F.eqL (ground.getAt F.unit a x) F.unit)) = false →
      (!(F.eqL (ground.getAt F.unit a y) F.unit)) = false →
      x ≠ y → bandAdj R x y = true := by
    intro x hx y hy hxi hyi _
    have hxp : (p.any (fun e => e.1 == x)) = true := by
      have hxo := (hmemS x hx).2
      rw [hxi] at hxo
      cases hq : (p.any (fun e => e.1 == x)) with
      | true => rfl
      | false => rw [hq] at hxo; exact Bool.noConfusion hxo
    have hyp : (p.any (fun e => e.1 == y)) = true := by
      have hyo := (hmemS y hy).2
      rw [hyi] at hyo
      cases hq : (p.any (fun e => e.1 == y)) with
      | true => rfl
      | false => rw [hq] at hyo; exact Bool.noConfusion hyo
    obtain ⟨e, he, hex⟩ := ground.mem_of_any _ p hxp
    obtain ⟨e', he', hey⟩ := ground.mem_of_any _ p hyp
    rw [← ground.beqEqOf hex, ← ground.beqEqOf hey]
    exact plaq_adj R p hpm e e' he he'
  have hsplit := partsGo_split R
    (fun x => !(F.eqL (ground.getAt F.unit a x) F.unit)) R.links
    (carrier.support F R (stableentries.farConf F R a p))
    (support_length_le F R _) (support_length_le F R _) hcross hcliq
  have hS : (carrier.support F R (stableentries.farConf F R a p)).filter
      (fun x => !(F.eqL (ground.getAt F.unit a x) F.unit))
      = carrier.support F R a := by
    show ((List.range R.links).filter (fun l =>
      !(F.eqL (ground.getAt F.unit (stableentries.farConf F R a p) l) F.unit))).filter
        (fun x => !(F.eqL (ground.getAt F.unit a x) F.unit))
      = (List.range R.links).filter (fun l =>
        !(F.eqL (ground.getAt F.unit a l) F.unit))
    rw [filter_filter]
    refine ground.filter_congr_mem _ _ (List.range R.links) ?_
    intro x hx
    have hxl := ground.ltOfMem hx
    rw [hoccB x hxl]
    cases hxi : (!(F.eqL (ground.getAt F.unit a x) F.unit)) with
    | false => cases (p.any (fun e => e.1 == x)) <;> rfl
    | true =>
      have hxp : (p.any (fun e => e.1 == x)) = false := by
        cases hq : (p.any (fun e => e.1 == x)) with
        | false => rfl
        | true =>
          have h1 := hon x hxl hq
          rw [h1] at hxi
          exact Bool.noConfusion hxi
      rw [hxp]
      rfl
  have hQ : (carrier.support F R (stableentries.farConf F R a p)).filter
      (fun x => !(!(F.eqL (ground.getAt F.unit a x) F.unit)))
      = (List.range R.links).filter (fun l => p.any (fun e => e.1 == l)) := by
    show ((List.range R.links).filter (fun l =>
      !(F.eqL (ground.getAt F.unit (stableentries.farConf F R a p) l) F.unit))).filter
        (fun x => !(!(F.eqL (ground.getAt F.unit a x) F.unit)))
      = (List.range R.links).filter (fun l => p.any (fun e => e.1 == l))
    rw [filter_filter]
    refine ground.filter_congr_mem _ _ (List.range R.links) ?_
    intro x hx
    have hxl := ground.ltOfMem hx
    rw [hoccB x hxl]
    cases hxp : (p.any (fun e => e.1 == x)) with
    | true =>
      rw [hon x hxl hxp]
      rfl
    | false => cases F.eqL (ground.getAt F.unit a x) F.unit <;> rfl
  have hne : ¬ ((List.range R.links).filter
      (fun l => p.any (fun e => e.1 == l))).length = 0 := by
    have hpn : 0 < p.length := by rw [hpw.1]; exact Nat.succ_pos 3
    have he : ground.getAt (0, true) p 0 ∈ p := ground.mem_getAt (0, true) p 0 hpn
    have hek : (ground.getAt (0, true) p 0).1 < R.links :=
      of_decide_eq_true (ground.all_of_mem _ p hpk _ he)
    have hmem : (ground.getAt (0, true) p 0).1
        ∈ (List.range R.links).filter (fun l => p.any (fun e => e.1 == l)) :=
      ground.mem_filter_to _ (ground.memRange hek)
        (ground.any_of_mem _ he (ground.eqBeqOf rfl))
    intro h0
    cases hl : (List.range R.links).filter (fun l => p.any (fun e => e.1 == l)) with
    | nil => rw [hl] at hmem; exact nomatch hmem
    | cons z t => rw [hl] at h0; exact Nat.noConfusion h0
  show (partsGo R R.links (carrier.support F R (stableentries.farConf F R a p))).filter _
      = partsGo R R.links (carrier.support F R a)
    ∧ (partsGo R R.links (carrier.support F R (stableentries.farConf F R a p))).filter _
      = _
  rw [hsplit.1, hsplit.2, hS, hQ, if_neg hne]
  exact ⟨rfl, rfl⟩

/-- The border row's count: one further component. -/
theorem components_border_length {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (hw : lattice.wellRead R) (hpr : lattice.plaqRead R)
    (a : List L) (p : List (Nat × Bool)) (hpm : p ∈ R.plaqs)
    (hth : F.eqL F.theta F.unit = false) (hoff : offBand F R a p = true) :
    (components F R (stableentries.farConf F R a p)).length
      = (components F R a).length + 1 := by
  have h := components_border F R hw hpr a p hpm hth hoff
  rw [← length_filter_split (fun c => c.any (fun x =>
      !(F.eqL (ground.getAt F.unit a x) F.unit)))
      (components F R (stableentries.farConf F R a p)), h.1, h.2]
  rfl


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

instance instGrading3 (t : gentable.Table) (F : sertables.FundData)
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

instance instGrading4 (t : gentable.Table) (F : sertables.FundData)
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
