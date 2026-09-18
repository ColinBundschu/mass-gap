import MassGap.Grading
import MassGap.Pairpencil
import MassGap.Fusionfinite
/-!
`lem:grading` — the pencil's rows at the window's entries, the three
shapes.  The diagonal is the electric member's own, the window
list's contents (`pairpencil.pencilRead`'s form at `slotDiag`,
`def:pencil`).  A plaquette term's entry off the sum's unit sits at
a position pair across the plaquette's changed edge, one position's
configuration equal at the interface equality to a target on the
other's row (`entryShape` at `pairpencil.termSupport`, `def:algebra`'s
changed edge), the shapes read at that row member.  The stencil row:
every target on a plaquette's row keeps its support within the
class's support joined to the plaquette's links and at every link its
label on the link's row at `θ` (`stencilAt`, the reads
`support_target` and `algebra.plaqRow_target` at `def:algebra`'s
changed edge; `stencilRow`), and its content sits within the fusion
stencil, at a boundary link the label's cleared Casimir at or below
the Cartan product's with `θ` at the row's ball (`stencilContent` at
`fusionfinite.rowBall`, `prop:fusionfinite`) and off the boundary the
class's own label.  The border row: at a plaquette off the class's
band neighborhood every target on the row is the far target, the
`θ`-loop on the boundary with the configuration kept
(`stableentries.farRow`), at one further band component, the class's
components kept and the plaquette's links the further one
(`borderRow` at `components_border`), its entry at every relative
position beyond the band one repeated datum at the label-graph
isomorphism's transport, the read `fiberdec.termsTransport` at the
region's own action.  The tower rows repeat off the collar at the
window's loop entries: at two loops of the plaquette the entry is the
fusion count at the window's clearing (`pairpencil.entryAt_loop`),
and at the label calculus the count into a label at the matched
degree from a label off the collar is the content list's read at the
tie, `N^{λ+ν}_{θλ} = mult_θ(ν)` (`towerEntry` at `deepRow` through
the matched-degree lift).
-/

namespace grading
open ground lattice fusion elim

/-- The stencil row's two reads at a target: the target's support
sits within the class's support joined to the plaquette's links, and
at every link its label sits on the link's row at `θ`
(`def:algebra`'s changed edge). -/
def stencilAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (a b : List L) : Prop :=
  ((carrier.support F R b).all (fun l =>
      containsB (carrier.support F R a) l || p.any (fun e => e.1 == l))
    && (List.range R.links).all (fun l =>
      decide (0 < countOf (getAt F.unit b l) (algebra.linkTargets F p a l))))
    = true

instance instGradingrows1 {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (a b : List L) : Decidable (stencilAt F R p a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- Every target on a plaquette's row reads the stencil row's two
reads (`lem:grading`'s rows). -/
theorem stencilRow {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (a b : List L)
    (hb : 0 < countOf b (algebra.plaqRow F R p a)) : stencilAt F R p a b := by
  show ((carrier.support F R b).all (fun l =>
      containsB (carrier.support F R a) l || p.any (fun e => e.1 == l))
    && (List.range R.links).all (fun l =>
      decide (0 < countOf (getAt F.unit b l) (algebra.linkTargets F p a l)))) = true
  have h1 : (carrier.support F R b).all (fun l =>
      containsB (carrier.support F R a) l || p.any (fun e => e.1 == l)) = true := by
    refine all_of_mem_intro _ _ (fun l hl => ?_)
    cases support_target F R p a b hb l hl with
    | inl h => rw [containsB_of_mem h]; rfl
    | inr h => rw [h]; exact Bool.or_true _
  have h2 : (List.range R.links).all (fun l =>
      decide (0 < countOf (getAt F.unit b l) (algebra.linkTargets F p a l))) = true :=
    all_range_intro _ (fun l hl => decide_eq_true (algebra.plaqRow_target F R p a b hb l hl))
  rw [h1, h2]
  rfl

/-- The stencil row's content read: at the row's ball at every link
(`prop:fusionfinite`), a target's label on a boundary link is the
unit or reads its cleared Casimir at or below the Cartan product's
with `θ`, and off the boundary it is the class's own label
(`def:algebra`'s changed edge). -/
theorem stencilContent {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (a b : List L)
    (hb : 0 < countOf b (algebra.plaqRow F R p a))
    (hball : ∀ l, l < R.links → fusionfinite.rowBall F (getAt F.unit a l) F.theta)
    (l : Nat) (hl : l < R.links) :
    ((p.any (fun e => e.1 == l)) = true →
      F.eqL (getAt F.unit b l) F.unit = true
        ∨ F.c2N (getAt F.unit b l) ≤ F.c2N (F.add (getAt F.unit a l) F.theta))
    ∧ ((p.all (fun e => e.1 != l)) = true → getAt F.unit b l = getAt F.unit a l) := by
  refine ⟨fun hkp => ?_, fun hoff => algebra.plaqRow_keep F R p a b hb l hl hoff⟩
  have hk := algebra.plaqRow_target F R p a b hb l hl
  have hrow : algebra.linkTargets F p a l = F.row (getAt F.unit a l) F.theta := by
    show (if p.any (fun e => e.1 == l) then F.row (getAt F.unit a l) F.theta
      else [getAt F.unit a l]) = _
    rw [hkp, if_pos rfl]
  rw [hrow] at hk
  have hm := all_of_mem _ _ (hball l hl) _ (mem_of_countOf_pos _ _ hk)
  cases orSplitB hm with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (of_decide_eq_true h)

/-- The border row: at a plaquette off the class's band neighborhood
every target on the row is the far target, the `θ`-loop on the
boundary with the configuration kept, at one further band component,
the class's components kept and the plaquette's links the further
one (`lem:grading`'s rows). -/
theorem borderRow {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R)
    (hth : F.eqL F.theta F.unit = false) (hrow : unitRowLaw F F.theta)
    (a : List L) (hlen : a.length = R.links) (hun : oneUnit F a)
    (p : List (Nat × Bool)) (hp : p ∈ R.plaqs) (hoff : offBand F R a p = true)
    (b : List L) (hb : 0 < countOf b (algebra.plaqRow F R p a)) :
    b = stableentries.farConf F R a p
    ∧ (components F R b).filter (fun c =>
        c.any (fun x => !(F.eqL (getAt F.unit a x) F.unit)))
      = components F R a
    ∧ (components F R b).filter (fun c =>
        !(c.any (fun x => !(F.eqL (getAt F.unit a x) F.unit))))
      = [(List.range R.links).filter (fun l => p.any (fun e => e.1 == l))] := by
  have hb' : b = stableentries.farConf F R a p :=
    stableentries.farRow F R hw hrow a hlen hun p (offBand_far F R a p hoff) b hb
  refine ⟨hb', ?_⟩
  rw [hb']
  exact components_border F R hw hpr a p hp hth hoff

/-- A plaquette term's entry off the sum's unit at the window sits
across the plaquette's changed edge: one position's configuration
is, at the interface equality, a target on the other's row
(`pairpencil.termSupport`, `def:algebra`'s changed-edge read), the
row member's shape `stencilRow`'s and, off the band neighborhood,
`borderRow`'s. -/
theorem entryShape {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (p : List (Nat × Bool)) (M : Mat)
    (hsup : pairpencil.termSupport F R n ix p M) (i j : Nat) (hi : i < n) (hj : j < n)
    (hM : ¬ (getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit) :
    (∃ b, 0 < countOf b (algebra.plaqRow F R p (pairpencil.posConf F R ix i))
        ∧ carrier.eqConf F (pairpencil.posConf F R ix j) b = true)
    ∨ (∃ b, 0 < countOf b (algebra.plaqRow F R p (pairpencil.posConf F R ix j))
        ∧ carrier.eqConf F (pairpencil.posConf F R ix i) b = true) := by
  have hrow : pairpencil.rowPair F R ix p i j = true := by
    have h := all_range_read n (all_range_read n hsup i hi) j hj
    cases hd : decide ((getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit) with
    | true => exact absurd (of_decide_eq_true hd) hM
    | false => rw [hd] at h; exact h
  cases orSplitB hrow with
  | inl h => exact Or.inl (carrier.confMem_to F _ _ h)
  | inr h => exact Or.inr (carrier.confMem_to F _ _ h)

/-- The tower display at the label calculus: the adjoint's fusion
count into a label at the matched degree from a label off the
collar reads the content list's read at the tie,
`N^{λ+ν}_{θλ} = mult_θ(ν)`, the label count at the matched-degree
lift the block count (`labels.countL_matched`) and the block count
the deep row's read (`deepRow`). -/
theorem towerEntry (d : Nat) (hd : 2 ≤ d) (lam c : places.Shape)
    (hld : lam.length = d) (hcd : c.length = d)
    (hdeg : places.degree (adjchar.theta d) + places.degree lam = places.degree c)
    (hdeep : ¬ collarAt lam) :
    (dataA d).count (adjchar.theta d) lam c = rowRead d lam c := by
  show labels.countL (adjchar.theta d) lam c = rowRead d lam c
  rw [labels.countL_matched _ _ _ (hld.trans (adjchar.length_theta d).symm)
    (hcd.trans (adjchar.length_theta d).symm) hdeg]
  exact deepRow d lam c hd hld hcd hdeep

end grading
