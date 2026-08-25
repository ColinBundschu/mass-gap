import MassGap.Carrier
import MassGap.Wg
/-!
`def:algebra` — the product's read layer at the label index: the
plaquette multiplication's matrix elements are the label-index
reads on the changed edge alone, and the row's index support is
`plaqRow` — per boundary link the fusion row at `θ`, the
off-boundary labels kept, at the occupied members — the window
matrix's row shape; the all-unit target is the unit line's own
coordinate, its entry the unit read `Eval` (`evalConf`, one at the
unit assignment and the sum's unit at an occupied support); and the
involution is contour reversal at the index, the labels dualized
linkwise (`conj`, the orientation the labels' duality read,
`con:lattice`).  The entries' values are the presentation's — the
evaluation identity and the stated factor lists land at `prop:wg`'s
layer with `con:fusion`'s evaluation and presentation fields — and
`prop:algebra`'s laws are the structure-constant identities the
interface already pins (`fusion.commLaw`, `assocLaw`, `unitLaw` at
the instantiation's check module), and the determination reads two
ways at `prop:algebra`'s own sentence: the carrier's window list is
orthonormal with the coordinate reads direct, and a presentation's
wiring list spans the window at its own Gram, the adjugate solve
against the determinant (`windowGram`, `prodSolve`,
`lem:genericlift`(ii)) with the pairing identity's verification the
read whole (`prodRead`), a window at or beyond the target solving
to the one element; the verification's instance decides the Gram's
determinant at the pair carrier's descent on an occupied square
site (`elim.pairDetD_eq`, the multiplier slot moved across the
walk's value at the occupied members' cancellation), the fold
branch its complement.
-/

namespace algebra
open ground lattice fusion

/-- One key's target list under the plaquette term: the fusion row
at `θ` on the boundary's own links, the kept label's singleton off
them. -/
def linkTargets {L : Type} (F : Data L)
    (p : List (Nat × Bool)) (a : List L) (l : Nat) : List L :=
  if p.any (fun e => e.1 == l) then F.row (getAt F.unit a l) F.theta
  else [getAt F.unit a l]

/-- The plaquette multiplication's row at a configuration, the
changed edge's index support: per boundary link the fusion row at
`θ`, the off-boundary labels kept, at the occupied members; the
all-unit target reads the unit line's coordinate beside the list. -/
def plaqRow {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (a : List L) : List (List L) :=
  ((List.range R.links).foldr (fun l acc =>
    (linkTargets F p a l).flatMap (fun c => acc.map (fun b => c :: b)))
    [[]]).filter (fun b =>
      (b.any (fun l => !(F.eqL l F.unit))) && carrier.occupied F R b)

/-- The involution at the index, contour reversal: the labels
dualized linkwise. -/
def conj {L : Type} (F : Data L) (a : List L) : List L := a.map F.dual

/-- The unit-coordinate read at an index element: one at the unit
assignment, the sum's unit at an occupied support. -/
def evalConf {L : Type} (F : Data L) (a : List L) : Nat :=
  if a.all (fun l => F.eqL l F.unit) then 1 else 0

/-! `def:algebra`'s changed-edge clause at the row's index support:
the row's targets differ from the source at the plaquette's boundary
alone, so a target keeps every off-boundary label — the product's
per-key read at the off-boundary singleton. -/

/-- The row's product read at one key: an occupied target's entry
sits in that key's own target list. -/
theorem prodKeep {L : Type} [DecidableEq L] (F : Data L)
    (p : List (Nat × Bool)) (a : List L) :
    ∀ (K : List Nat) (b : List L),
    0 < countOf b (K.foldr (fun k acc =>
        (linkTargets F p a k).flatMap
          (fun c => acc.map (fun t => c :: t))) [[]]) →
    ∀ j, j < K.length →
      0 < countOf (getAt F.unit b j) (linkTargets F p a (getAt 0 K j))
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k :: K, b, hb, j, hj => by
    have hb' : 0 < countOf b ((linkTargets F p a k).flatMap
        (fun c => (K.foldr (fun m acc =>
            (linkTargets F p a m).flatMap
              (fun d => acc.map (fun t => d :: t))) [[]]).map
          (fun t => c :: t))) := hb
    rw [countOf_flatMap] at hb'
    obtain ⟨c, hc, hbc⟩ :=
      famFold_pos_witness _ (linkTargets F p a k) hb'
    cases b with
    | nil =>
      rw [countOf_nil_consMap] at hbc
      exact absurd hbc (Nat.lt_irrefl 0)
    | cons x b' =>
      rw [countOf_consMap x c _ b'] at hbc
      by_cases hxc : x = c
      · rw [if_pos hxc] at hbc
        cases j with
        | zero =>
          show 0 < countOf x (linkTargets F p a k)
          rw [hxc]
          exact hc
        | succ j' =>
          show 0 < countOf (getAt F.unit b' j')
            (linkTargets F p a (getAt 0 K j'))
          exact prodKeep F p a K b' hbc j'
            (Nat.lt_of_succ_lt_succ hj)
      · rw [if_neg hxc] at hbc
        exact absurd hbc (Nat.lt_irrefl 0)

/-- A row target's entry at every key sits in that key's own target
list: the product's per-key read walked through the occupancy
filter. -/
theorem plaqRow_target {L : Type} [DecidableEq L] (F : Data L)
    (R : Region) (p : List (Nat × Bool)) (a b : List L)
    (hb : 0 < ground.countOf b (plaqRow F R p a))
    (l : Nat) (hl : l < R.links) :
    0 < ground.countOf (ground.getAt F.unit b l)
      (linkTargets F p a l) := by
  have hb1 : 0 < countOf b (((List.range R.links).foldr (fun k acc =>
      (linkTargets F p a k).flatMap
        (fun c => acc.map (fun t => c :: t))) [[]]).filter
    (fun t => (t.any (fun m => !(F.eqL m F.unit)))
      && carrier.occupied F R t)) := hb
  rw [countOf_filter] at hb1
  cases hf : ((b.any (fun m => !(F.eqL m F.unit)))
      && carrier.occupied F R b) with
  | false =>
    rw [if_neg (boolNe hf)] at hb1
    exact absurd hb1 (Nat.lt_irrefl 0)
  | true =>
    rw [if_pos hf] at hb1
    have hlen : l < (List.range R.links).length := by
      rw [ground.length_range]
      exact hl
    have hk := prodKeep F p a (List.range R.links) b hb1 l hlen
    rw [ground.getAt_range R.links l hl] at hk
    exact hk

/-- `def:algebra`'s changed-edge clause: a row target keeps every
label off the plaquette's boundary, the product's off-boundary key
reading the source's own label. -/
theorem plaqRow_keep {L : Type} [DecidableEq L] (F : Data L)
    (R : Region) (p : List (Nat × Bool)) (a b : List L)
    (hb : 0 < ground.countOf b (plaqRow F R p a))
    (l : Nat) (hl : l < R.links)
    (hoff : (p.all (fun e => e.1 != l)) = true) :
    ground.getAt F.unit b l = ground.getAt F.unit a l := by
  have hk := plaqRow_target F R p a b hb l hl
  have hoff' : (p.all (fun e => !((fun d : Nat × Bool =>
      d.1 == l) e))) = true := hoff
  have hsing : linkTargets F p a l = [getAt F.unit a l] := by
    show (if p.any (fun e => e.1 == l)
        then F.row (getAt F.unit a l) F.theta
        else [getAt F.unit a l]) = [getAt F.unit a l]
    rw [if_neg (boolNe (ground.any_false_of_all_not
      (fun d : Nat × Bool => d.1 == l) p hoff'))]
  rw [hsing] at hk
  exact ground.countOf_single hk

/-! The determination at the presentation Gram (`prop:algebra`):
the product's coordinate vector over a stated window list, the
adjugate solve against the determinant with the pairing identity's
verification the read whole (`lem:genericlift`(ii)); a window at
or beyond the target solves the identity to the one element, the
agreement's cleared comparison the check module's pin. -/

/-- The window Gram at a stated state list, the presentation
pairing's matrix (`prop:wg`). -/
def windowGram (F : states.FList) (ws : List states.Comb) :
    genericlift.PPMat :=
  ws.map (fun v => ws.map (fun w => wg.pairFull F F v w))

/-- The pairing identity's right side: the product state's pairing
against every window-list member, `Eval(Φ̄_v Φ_a Φ_u)` at the
concatenated site. -/
def prodRhs (F Fa Fu : states.FList) (ws : List states.Comb)
    (a u : states.Comb) : List poly.PPair :=
  ws.map (fun v => wg.pairFull F (Fa ++ Fu) v (states.mulComb a u))

/-- The determination's produced solve: the adjugate against the
window Gram at the right side, the coordinates cleared at the
determinant. -/
def prodSolve (F Fa Fu : states.FList) (ws : List states.Comb)
    (a u : states.Comb) : List poly.PPair :=
  genericlift.ppmatVec (genericlift.ppadj (windowGram F ws))
    (prodRhs F Fa Fu ws a u)

/-- The pairing identity's verification at stated data, whole:
`G x` reads the determinant's multiple of the right side,
entrywise at the cross reads — the general form the composed read
instantiates, a check module binding the Gram once. -/
def prodReadAt (G : genericlift.PPMat) (m : poly.PPair)
    (rhs x : List poly.PPair) : Prop :=
  genericlift.pprowEq (genericlift.ppmatVec G x)
    (rhs.map (fun e => poly.pMul m e))

instance (G : genericlift.PPMat) (m : poly.PPair)
    (rhs x : List poly.PPair) :
    Decidable (prodReadAt G m rhs x) :=
  genericlift.decPprowEq _ _

/-- The composed verification at the window's own data: the body's
read at the window Gram, its determinant and the product's right
side. -/
def prodRead (F Fa Fu : states.FList) (ws : List states.Comb)
    (a u : states.Comb) (x : List poly.PPair) : Prop :=
  prodReadAt (windowGram F ws)
    (genericlift.ppminor (windowGram F ws))
    (prodRhs F Fa Fu ws a u) x

/-- The multiplier slot's one-way transport: the walk value's read
moves onto the fold's at the shared factors, the occupied second
member withdrawing at the cancellation. -/
private theorem slot_half {m W : poly.PPair}
    (hm : poly.oneValue (poly.mul W.1 m.2) (poly.mul m.1 W.2))
    (hWden : ¬ poly.unitTail W.2) (v e : poly.PPair)
    (h : poly.oneValue (poly.mul v.1 (poly.pMul W e).2)
      (poly.mul (poly.pMul W e).1 v.2)) :
    poly.oneValue (poly.mul v.1 (poly.pMul m e).2)
      (poly.mul (poly.pMul m e).1 v.2) := by
  refine elim.pMulCancel hWden ?_
  show poly.oneValue
    (poly.mul W.2 (poly.mul v.1 (poly.mul m.2 e.2)))
    (poly.mul W.2 (poly.mul (poly.mul m.1 e.1) v.2))
  refine poly.oneValue_trans (poly.mul_left_comm W.2 v.1 (poly.mul m.2 e.2)) ?_
  refine poly.oneValue_trans
    (poly.mul_congr v.1 (poly.mul_left_comm W.2 m.2 e.2)) ?_
  refine poly.oneValue_trans (poly.mul_left_comm v.1 m.2 (poly.mul W.2 e.2)) ?_
  refine poly.oneValue_trans
    (poly.mul_congr m.2 (show poly.oneValue
      (poly.mul v.1 (poly.mul W.2 e.2))
      (poly.mul (poly.mul W.1 e.1) v.2) from h)) ?_
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (poly.mul_assoc m.2 (poly.mul W.1 e.1) v.2)) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left
      (poly.oneValue_symm (poly.mul_assoc m.2 W.1 e.1)) v.2) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left
      (poly.mul_congr_left (poly.mul_comm m.2 W.1) e.1) v.2) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left
      (poly.mul_congr_left hm e.1) v.2) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left
      (poly.mul_congr_left (poly.mul_comm m.1 W.2) e.1) v.2) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left (poly.mul_assoc W.2 m.1 e.1) v.2) ?_
  exact poly.mul_assoc W.2 (poly.mul m.1 e.1) v.2

/-- The slot transport both ways at the two occupied members. -/
private theorem slot_congr {m W : poly.PPair}
    (hm : poly.oneValue (poly.mul W.1 m.2) (poly.mul m.1 W.2))
    (hmden : ¬ poly.unitTail m.2) (hWden : ¬ poly.unitTail W.2)
    (v e : poly.PPair) :
    genericlift.crossNull v (poly.pMul W e)
      ↔ genericlift.crossNull v (poly.pMul m e) :=
  ⟨fun h => (genericlift.crossNull_ov v (poly.pMul m e)).mpr
      (slot_half hm hWden v e
        ((genericlift.crossNull_ov v (poly.pMul W e)).mp h)),
   fun h => (genericlift.crossNull_ov v (poly.pMul W e)).mpr
      (slot_half (poly.oneValue_symm hm) hmden v e
        ((genericlift.crossNull_ov v (poly.pMul m e)).mp h))⟩

/-- The row read at the moved multiplier, entry by entry. -/
private theorem prodRow_iff {m W : poly.PPair}
    (hm : poly.oneValue (poly.mul W.1 m.2) (poly.mul m.1 W.2))
    (hmden : ¬ poly.unitTail m.2) (hWden : ¬ poly.unitTail W.2) :
    ∀ (l : List poly.PPair) (rhs : List poly.PPair),
    genericlift.pprowEq l (rhs.map (fun e => poly.pMul W e))
      ↔ genericlift.pprowEq l (rhs.map (fun e => poly.pMul m e))
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | v :: l, e :: rhs =>
    ⟨fun x => ⟨(slot_congr hm hmden hWden v e).mp x.1,
      (prodRow_iff hm hmden hWden l rhs).mp x.2⟩,
     fun x => ⟨(slot_congr hm hmden hWden v e).mpr x.1,
      (prodRow_iff hm hmden hWden l rhs).mpr x.2⟩⟩

instance (F Fa Fu : states.FList) (ws : List states.Comb)
    (a u : states.Comb) (x : List poly.PPair) :
    Decidable (prodRead F Fa Fu ws a u x) :=
  let G := windowGram F ws
  match elim.decRowsLen G.length G with
  | isFalse _ => inferInstanceAs (Decidable (prodReadAt _ _ _ _))
  | isTrue hsq =>
    match hocc : elim.matOcc G with
    | false => inferInstanceAs (Decidable (prodReadAt _ _ _ _))
    | true =>
      decidable_of_iff
        (prodReadAt G (elim.pairDetD G) (prodRhs F Fa Fu ws a u) x)
        (prodRow_iff (elim.pairDetD_eq G hsq)
          (elim.pairMinor_den G hocc) (elim.pairDetD_den G hocc)
          (genericlift.ppmatVec G x) (prodRhs F Fa Fu ws a u))

end algebra
