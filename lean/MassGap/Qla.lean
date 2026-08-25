import MassGap.Chargedcell
import MassGap.Leastwindow
/-!
`def:qla` — the quasi-local algebra's two reads at the counts.
The filtration clause: every element sits in the local algebra at
any window beyond its least one, read off the index support —
membership at a window pair is every member configuration's
support links below the bound with its content at or below the
cutoff (`memberAt`, over `leastwindow.suppLinks` and
`carrier.contentN`), an element over a region's index is a member
at the region's own link count and its members' largest content
(`member_self`, the self-window read at `prop:leastwindow`'s two
counts), and membership is monotone in both coordinates
(`member_of_le`, the directed union's read) — the colimit's
summand injections stay at the prose, the reads the counts.  The
winding clause: a torus-cycle support crosses every transverse
cut of the grading (`windSupp` — per cut a crossing link,
occupied, its tail at the cut's grade and its head off it), and a
configuration of finite support winds through no count beyond it
(`noWind`): the crossing links at distinct cuts are distinct
occupied keys, one per cut, so a winding at the count reads the
count into the support (`ground.length_le_of_distinct_mem`, the
pigeonhole at the distinct host `carrier.support`), and winding
operators sit outside every local algebra — `def:carrier`'s
finite support the one premise, the flux tier staying
`lem:chargedcell`'s.
-/

namespace qla
open ground

/-- Membership at a window pair: every member configuration's
support links sit below the bound and its content at or below the
cutoff, the filtration's decidable read over
`leastwindow.suppLinks` and `carrier.contentN`. -/
def memberAt {L : Type} (F : fusion.Data L) (bound C : Nat)
    (as : List (List L)) : Prop :=
  (as.all (fun a =>
    ((leastwindow.suppLinks F a).all (fun l => l < bound))
      && decide (carrier.contentN F a ≤ C))) = true

instance {L : Type} (F : fusion.Data L) (bound C : Nat)
    (as : List (List L)) : Decidable (memberAt F bound C as) :=
  inferInstanceAs (Decidable (_ = _))

/-- A member's content sits at or below the fold's own value, the
max fold read from any seed. -/
private theorem le_contentFold {L : Type} (F : fusion.Data L) :
    ∀ (as : List (List L)) (m : Nat) (k : Nat), k < as.length →
      carrier.contentN F (ground.getAt [] as k)
        ≤ as.foldl (fun m a => Nat.max m (carrier.contentN F a)) m
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | a :: t, m, 0, _ => by
    show carrier.contentN F a
      ≤ t.foldl _ (Nat.max m (carrier.contentN F a))
    exact Nat.le_trans (ground.le_max_right m _) (seedFold F t _)
  | a :: t, m, k + 1, hk =>
    le_contentFold F t (Nat.max m (carrier.contentN F a)) k
      (Nat.lt_of_succ_lt_succ hk)
where
  /-- The seed rides the max fold. -/
  seedFold {L : Type} (F : fusion.Data L) :
      ∀ (as : List (List L)) (m : Nat),
        m ≤ as.foldl (fun m a => Nat.max m (carrier.contentN F a)) m
    | [], m => Nat.le_refl m
    | a :: t, m =>
      Nat.le_trans (ground.le_max_left m (carrier.contentN F a))
        (seedFold F t (Nat.max m (carrier.contentN F a)))

/-- The self-window read: an element over a region's index is a
member at the region's own link count and its members' largest
content — the support links filter the key range at the width, and
each content sits at or below the max fold.  The width tie `hw` is
the window index's list shape, refutable: a too-long configuration
carries a support key at or beyond the link count, the check
module's pinned refusal. -/
theorem member_self {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (as : List (List L))
    (hw : (as.all (fun a => a.length == R.links)) = true) :
    memberAt F R.links (leastwindow.windowContent F as) as := by
  show (as.all (fun a =>
    ((leastwindow.suppLinks F a).all (fun l => l < R.links))
      && decide (carrier.contentN F a
        ≤ leastwindow.windowContent F as))) = true
  refine ground.all_of_getAt ([] : List L) _ as (fun k hk => ?_)
  refine ground.andIntroB ?_ (decide_eq_true
    (le_contentFold F as 0 k hk))
  have hlen : (ground.getAt ([] : List L) as k).length = R.links :=
    ground.beqEqOf (ground.all_getAt ([] : List L) as hw k hk)
  refine ground.all_of_getAt 0 _ _ (fun j hj => ?_)
  have hmem := ground.mem_getAt 0
    (leastwindow.suppLinks F (ground.getAt ([] : List L) as k)) j hj
  have hm2 := ground.mem_filter_of _ _ _ hmem
  have hlt : ground.getAt 0
      (leastwindow.suppLinks F (ground.getAt ([] : List L) as k)) j
      < (ground.getAt ([] : List L) as k).length :=
    ground.ltOfMemRange hm2.1
  rw [hlen] at hlt
  exact decide_eq_true hlt

/-- The filtration's directedness: membership at a window pair is
membership at every larger one in both coordinates, the union's own
read.  Every binder is LOAD-BEARING — the check module refuses the
dropped bound order, the dropped cutoff order and the dropped
membership each at a small fixture. -/
theorem member_of_le {L : Type} (F : fusion.Data L)
    {b b' C C' : Nat} (hb : b ≤ b') (hC : C ≤ C')
    (as : List (List L)) (h : memberAt F b C as) :
    memberAt F b' C' as := by
  show (as.all (fun a =>
    ((leastwindow.suppLinks F a).all (fun l => l < b'))
      && decide (carrier.contentN F a ≤ C'))) = true
  refine ground.all_of_getAt ([] : List L) _ as (fun k hk => ?_)
  have hin := ground.andSplitB
    (ground.all_getAt ([] : List L) as h k hk)
  refine ground.andIntroB ?_ (decide_eq_true
    (Nat.le_trans (of_decide_eq_true hin.2) hC))
  refine ground.all_of_getAt 0 _ _ (fun j hj => ?_)
  exact decide_eq_true (Nat.lt_of_lt_of_le
    (of_decide_eq_true (ground.all_getAt 0 _ hin.1 j hj)) hb)

/-- The winding support read: every transverse cut of the grading
is crossed — per cut below the count a link of the region,
occupied at the configuration, its tail at the cut's grade and
its head off the tail's. -/
def windSupp {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (g : Nat → Nat) (c : Nat) (a : List L) : Prop :=
  ((List.range c).all (fun x =>
    (List.range R.links).any (fun l =>
      (!(F.eqL (ground.getAt F.unit a l) F.unit))
        && (g (ground.getAt 0 R.tail l) == x)
        && (!(g (ground.getAt 0 R.head l)
              == g (ground.getAt 0 R.tail l)))))) = true

instance {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (g : Nat → Nat) (c : Nat) (a : List L) :
    Decidable (windSupp F R g c a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The cut's crossing pick: the first occupied crossing link of
the support at the cut's grade. -/
private def pickAt {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (g : Nat → Nat) (a : List L) (x : Nat) :
    Nat :=
  ground.getAt 0 ((carrier.support F R a).filter (fun l =>
    g (ground.getAt 0 R.tail l) == x)) 0

/-- The support is a distinct key family, the range filter's own
counts. -/
private theorem support_distinct {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a : List L) :
    ground.distinctList (carrier.support F R a) := by
  intro x hx
  have h := ground.mem_filter_of _ _ _ hx
  rw [show carrier.support F R a
      = (List.range R.links).filter (fun l =>
        !(F.eqL (ground.getAt F.unit a l) F.unit)) from rfl,
    ground.countOf_filter _ x (List.range R.links), if_pos h.2,
    ground.countOf_range x R.links]
  cases hlt : decide (x < R.links) with
  | true => rw [if_pos (of_decide_eq_true hlt)]; exact Nat.le_refl 1
  | false =>
    rw [if_neg (fun hc => Bool.noConfusion
      ((decide_eq_true hc).symm.trans hlt))]
    exact Nat.le_succ 0

/-- A winding's pick at a cut sits in the support at the cut's own
grade, the crossing witness's filter read. -/
private theorem pick_read {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (g : Nat → Nat) (c : Nat) (a : List L)
    (hws : windSupp F R g c a) (x : Nat) (hx : x < c) :
    pickAt F R g a x ∈ carrier.support F R a
      ∧ g (ground.getAt 0 R.tail (pickAt F R g a x)) = x := by
  have htop := ground.all_range_read c hws x hx
  obtain ⟨l, hlmem, hpred⟩ := ground.mem_of_any _ _ htop
  have hsp := ground.andSplitB hpred
  have hsp2 := ground.andSplitB hsp.1
  have hlsupp : l ∈ carrier.support F R a := by
    refine ground.mem_of_countOf_pos l (carrier.support F R a) ?_
    rw [show carrier.support F R a
        = (List.range R.links).filter (fun l =>
          !(F.eqL (ground.getAt F.unit a l) F.unit)) from rfl,
      ground.countOf_filter _ l (List.range R.links),
      if_pos hsp2.1]
    rw [ground.countOf_range_one
      (ground.ltOfMemRange hlmem)]
    exact Nat.succ_pos 0
  have hlfx : l ∈ (carrier.support F R a).filter (fun l =>
      g (ground.getAt 0 R.tail l) == x) := by
    refine ground.mem_of_countOf_pos l _ ?_
    rw [ground.countOf_filter _ l (carrier.support F R a),
      if_pos hsp2.2]
    exact ground.countOf_pos_of_mem hlsupp
  have hpos : 0 < ((carrier.support F R a).filter (fun l =>
      g (ground.getAt 0 R.tail l) == x)).length := by
    cases hFx : (carrier.support F R a).filter (fun l =>
        g (ground.getAt 0 R.tail l) == x) with
    | nil =>
      have hcp := ground.countOf_pos_of_mem hlfx
      rw [hFx] at hcp
      exact absurd hcp (Nat.lt_irrefl 0)
    | cons y t => exact Nat.succ_pos t.length
  have hpmem := ground.mem_getAt 0 _ 0 hpos
  have hp2 := ground.mem_filter_of _ _ _ hpmem
  exact ⟨hp2.1, ground.beqEqOf hp2.2⟩

/-- The picks' counts: at most one occurrence per key, and an
occupied count reads the pick into the support — the grade reads
the cut back, so distinct cuts pick distinct keys. -/
private theorem picks_count {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (g : Nat → Nat) (c : Nat) (a : List L)
    (hws : windSupp F R g c a) (v : Nat) :
    ground.countOf v ((List.range c).map (pickAt F R g a)) ≤ 1
      ∧ (0 < ground.countOf v
            ((List.range c).map (pickAt F R g a))
          → v ∈ carrier.support F R a) := by
  cases hb : (List.range c).any (fun x => pickAt F R g a x == v) with
  | true =>
    obtain ⟨x0, hx0mem, hx0⟩ := ground.mem_of_any _ _ hb
    have hx0lt : x0 < c :=
      ground.ltOfMemRange hx0mem
    have hveq : pickAt F R g a x0 = v := ground.beqEqOf hx0
    have hiff : ∀ w, 0 < ground.countOf w (List.range c) →
        (v = pickAt F R g a w ↔ x0 = w) := by
      intro w hw
      have hwlt : w < c := by
        rw [ground.countOf_range w c] at hw
        cases hlt : decide (w < c) with
        | true => exact of_decide_eq_true hlt
        | false =>
          rw [if_neg (fun hc' => Bool.noConfusion
            ((decide_eq_true hc').symm.trans hlt))] at hw
          exact absurd hw (Nat.lt_irrefl 0)
      constructor
      · intro hvw
        have h1 := (pick_read F R g c a hws w hwlt).2
        have h2 := (pick_read F R g c a hws x0 hx0lt).2
        rw [← hvw] at h1
        rw [hveq] at h2
        exact h2.symm.trans h1
      · intro hxw
        rw [← hxw]
        exact hveq.symm
    refine ⟨?_, fun _ => ?_⟩
    · rw [ground.countOf_map_iff (pickAt F R g a) (List.range c)
        v x0 hiff, ground.countOf_range_one hx0lt]
      exact Nat.le_refl 1
    · rw [← hveq]
      exact (pick_read F R g c a hws x0 hx0lt).1
  | false =>
    have hiff : ∀ w, 0 < ground.countOf w (List.range c) →
        (v = pickAt F R g a w ↔ c = w) := by
      intro w hw
      have hwlt : w < c := by
        rw [ground.countOf_range w c] at hw
        cases hlt : decide (w < c) with
        | true => exact of_decide_eq_true hlt
        | false =>
          rw [if_neg (fun hc' => Bool.noConfusion
            ((decide_eq_true hc').symm.trans hlt))] at hw
          exact absurd hw (Nat.lt_irrefl 0)
      constructor
      · intro hvw
        have hany := ground.any_of_mem
          (fun x => pickAt F R g a x == v)
          (ground.memRange hwlt)
          (ground.eqBeqOf hvw.symm)
        exact absurd (hany.symm.trans hb) Bool.noConfusion
      · intro hcw
        exact absurd hwlt (hcw ▸ Nat.lt_irrefl w)
    have hz : ground.countOf v
        ((List.range c).map (pickAt F R g a)) = 0 := by
      rw [ground.countOf_map_iff (pickAt F R g a) (List.range c)
        v c hiff, ground.countOf_range c c,
        if_neg (Nat.lt_irrefl c)]
    rw [hz]
    exact ⟨Nat.le_succ 0, fun hp => absurd hp (Nat.lt_irrefl 0)⟩

/-- The winding exclusion (`def:qla`): a configuration of finite
support winds through no count beyond it — the crossing links at
distinct cuts are distinct occupied keys, one per cut, so a winding
at the count reads the count into the support, against the stated
bound.  The binder `h` is `def:carrier`'s finite support read,
LOAD-BEARING: the torus winding string at support seven refuses the
conclusion at count three, the check module's pin. -/
theorem noWind {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (g : Nat → Nat) (c : Nat) (a : List L)
    (h : (carrier.support F R a).length < c) :
    ¬ windSupp F R g c a := by
  intro hws
  have hle : ((List.range c).map (pickAt F R g a)).length
      ≤ (carrier.support F R a).length :=
    ground.length_le_of_distinct_mem _ _
      (fun v => (picks_count F R g c a hws v).1)
      (fun v hv => (picks_count F R g c a hws v).2
        (ground.countOf_pos_of_mem hv))
      (support_distinct F R a)
  rw [ground.length_mapRange] at hle
  exact Nat.lt_irrefl c (Nat.lt_of_le_of_lt hle h)

end qla
