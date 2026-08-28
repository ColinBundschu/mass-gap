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
  refine poly.pmul_cancel W.2 _ _ hWden ?_
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


/-! `prop:algebra`'s commutativity at the presentation carrier: the
two block orders of a concatenated site are one state at the word
index — the block swap a letter-preserving relabeling of the site
and its wiring (`rem:kernel`) — so the pairing against a product
state reads one value either way (`prodComm`), and the pairing
identity's right side carries it row by row (`prodRhsComm`). -/

section
attribute [local irreducible] genericlift.pReduce


/-- The pair read with its site datum: the cross read joined to
the second members' shared occupancy — the composition the cross
read alone refuses at a vacant middle. -/
private def pEq (x y : poly.PPair) : Prop :=
  genericlift.crossNull x y
    ∧ (poly.unitTail x.2 ↔ poly.unitTail y.2)

/-- The joined read at its two data. -/
private theorem pEq_mk {x y : poly.PPair}
    (h1 : genericlift.crossNull x y)
    (h2 : poly.unitTail x.2 ↔ poly.unitTail y.2) : pEq x y :=
  ⟨h1, h2⟩

/-- The joined read at one pair. -/
private theorem pEq_refl (x : poly.PPair) : pEq x x :=
  ⟨poly.add_neg (poly.mul x.1 x.2), Iff.rfl⟩

/-- The joined read exchanges its pairs. -/
private theorem pEq_symm {x y : poly.PPair} (h : pEq x y) : pEq y x :=
  ⟨(genericlift.crossNull_ov y x).mpr
      (poly.oneValue_symm ((genericlift.crossNull_ov x y).mp h.1)),
    h.2.symm⟩

/-- Two pairs at vacant second members read one value: each
product carries a unit-tailed factor. -/
private theorem crossNull_of_vac {x y : poly.PPair}
    (hx : poly.unitTail x.2) (hy : poly.unitTail y.2) :
    genericlift.crossNull x y :=
  (genericlift.crossNull_ov x y).mpr
    (poly.unitTail_oneValue (poly.mul_unitTail x.1 hy)
      (poly.mul_unitTail y.1 hx))

/-- The joined read composes: at an occupied middle the cross
read's own composition, at a vacant one the two ends' vacancy. -/
private theorem pEq_trans {x y z : poly.PPair} (h1 : pEq x y)
    (h2 : pEq y z) : pEq x z := by
  refine ⟨?_, h1.2.trans h2.2⟩
  by_cases hy : poly.unitTail y.2
  · exact crossNull_of_vac (h1.2.mpr hy) (h2.2.mp hy)
  · exact (genericlift.crossNull_ov x z).mpr
      (elim.cross_trans hy ((genericlift.crossNull_ov x y).mp h1.1)
        ((genericlift.crossNull_ov y z).mp h2.1))

/-- The displayed sum's joined read at two joined reads, the
second members' occupancy the product's integral read. -/
private theorem pEq_pAdd {x x' y y' : poly.PPair} (h1 : pEq x x')
    (h2 : pEq y y') : pEq (poly.pAdd x y) (poly.pAdd x' y') := by
  refine ⟨(genericlift.crossNull_ov _ _).mpr
    (poly.pAdd_cross ((genericlift.crossNull_ov x x').mp h1.1)
      ((genericlift.crossNull_ov y y').mp h2.1)), ?_⟩
  constructor
  · intro h
    exact poly.of_unitTail_mul
      ((poly.unitTail_mul_of h).elim
        (fun a => Or.inl (h1.2.mp a)) (fun a => Or.inr (h2.2.mp a)))
  · intro h
    exact poly.of_unitTail_mul
      ((poly.unitTail_mul_of h).elim
        (fun a => Or.inl (h1.2.mpr a)) (fun a => Or.inr (h2.2.mpr a)))

/-- The displayed product's joined read at two joined reads. -/
private theorem pEq_pMul {x x' y y' : poly.PPair} (h1 : pEq x x')
    (h2 : pEq y y') : pEq (poly.pMul x y) (poly.pMul x' y') := by
  refine ⟨(genericlift.crossNull_ov _ _).mpr
    (poly.pMul_cross ((genericlift.crossNull_ov x x').mp h1.1)
      ((genericlift.crossNull_ov y y').mp h2.1)), ?_⟩
  constructor
  · intro h
    exact poly.of_unitTail_mul
      ((poly.unitTail_mul_of h).elim
        (fun a => Or.inl (h1.2.mp a)) (fun a => Or.inr (h2.2.mp a)))
  · intro h
    exact poly.of_unitTail_mul
      ((poly.unitTail_mul_of h).elim
        (fun a => Or.inl (h1.2.mpr a)) (fun a => Or.inr (h2.2.mpr a)))



/-- A rescaled family's tail read is the family's own. -/
private theorem mapScale_unitTail (w : ground.Pos) (p : poly.Poly) :
    poly.unitTail (p.map (fun e => e.scale w)) ↔ poly.unitTail p := by
  constructor
  · intro h
    exact (poly.unitTail_mul_of
      (poly.oneValue_unitTail (poly.ofPos_scale w p) h)).elim
      (fun hb => (ground.BPair.ofPos_off w hb.1).elim) id
  · intro h
    exact poly.unitTail_oneValue_right
      (poly.mul_unitTail [ground.BPair.ofPos w] h) (poly.ofPos_scale w p)

/-- A topped family sits off the sum's unit. -/
private theorem topped_occ : ∀ (g : poly.Poly) (t : ground.Pos),
    ¬ poly.unitTail (poly.topped g t)
  | [], t => fun h => ground.BPair.ofPos_off t h.1
  | _ :: g, t => fun h => topped_occ g t h.2

/-- The certified reduction keeps the second member's occupancy
both ways: at the guard's firing the reduced second member is the
cofactor scaled, tied to the pair's own through the topped gcd's
occupied top; at its refusal the pair is unchanged. -/
private theorem pEq_pReduce_den (x : poly.PPair) :
    poly.unitTail (genericlift.pReduce x).2 ↔ poly.unitTail x.2 := by
  have key : ∀ d : windowsep.GcdData,
      (poly.unitTail
        (if decide (stagesplit.gcdRead x.1 x.2 d.g d.A d.B d.u d.v
            d.top d.cA d.cB d.c)
         then (d.A.map (fun e => e.scale d.cB),
               d.B.map (fun e => e.scale d.cA))
         else x).2 ↔ poly.unitTail x.2) := by
    intro d
    by_cases hc : stagesplit.gcdRead x.1 x.2 d.g d.A d.B d.u d.v
        d.top d.cA d.cB d.c
    · rw [if_pos (decide_eq_true hc)]
      show poly.unitTail (d.B.map (fun e => e.scale d.cA))
        ↔ poly.unitTail x.2
      have F2 : poly.oneValue
          (poly.mul (poly.topped d.g d.top) d.B)
          (x.2.map (fun y => y.scale d.cB)) := hc.2.1
      constructor
      · intro h
        exact (mapScale_unitTail d.cB x.2).mp
          (poly.unitTail_oneValue_right
            (poly.mul_unitTail (poly.topped d.g d.top)
              ((mapScale_unitTail d.cA d.B).mp h)) F2)
      · intro h
        exact (mapScale_unitTail d.cA d.B).mpr
          ((poly.unitTail_mul_of (poly.oneValue_unitTail F2
            ((mapScale_unitTail d.cB x.2).mpr h))).elim
            (fun hg => (topped_occ d.g d.top hg).elim) id)
    · rw [if_neg (fun h => hc (of_decide_eq_true h))]
  rw [genericlift.pReduce]
  generalize windowsep.gcdD x.1 x.2 = d
  exact key d



/-- Two pairs at memberwise one-value reads join. -/
private theorem pEq_of_parts {x y : poly.PPair}
    (hn : poly.oneValue x.1 y.1) (hd : poly.oneValue x.2 y.2) :
    pEq x y :=
  ⟨(genericlift.crossNull_ov x y).mpr
      (poly.oneValue_trans (poly.mul_congr_left hn y.2)
        (poly.mul_congr y.1 (poly.oneValue_symm hd))),
    ⟨fun h => poly.unitTail_oneValue_right h hd,
     fun h => poly.oneValue_unitTail hd h⟩⟩

/-- The sum's exchange at the pair carrier. -/
private theorem pEq_addComm (x y : poly.PPair) :
    pEq (poly.pAdd x y) (poly.pAdd y x) :=
  pEq_of_parts (poly.add_comm _ _) (poly.mul_comm x.2 y.2)

/-- The sum's unit on the right. -/
private theorem pEq_addZeroR (x : poly.PPair) :
    pEq (poly.pAdd x poly.pZero) x := by
  refine pEq_of_parts ?_ ?_
  · show poly.oneValue
      (poly.add (poly.mul x.1 poly.one) (poly.mul [] x.2)) x.1
    show poly.oneValue
      (poly.add (poly.mul x.1 poly.one) []) x.1
    rw [poly.add_nil]
    exact poly.oneValue_trans (poly.mul_comm x.1 poly.one)
      (poly.one_mul x.1)
  · exact poly.oneValue_trans (poly.mul_comm x.2 poly.one)
      (poly.one_mul x.2)

/-- The sum's association at the pair carrier. -/
private theorem pEq_addAssoc (x y z : poly.PPair) :
    pEq (poly.pAdd (poly.pAdd x y) z)
      (poly.pAdd x (poly.pAdd y z)) := by
  refine pEq_of_parts ?_ (poly.mul_assoc x.2 y.2 z.2)
  show poly.oneValue
    (poly.add (poly.mul (poly.add (poly.mul x.1 y.2)
      (poly.mul y.1 x.2)) z.2) (poly.mul z.1 (poly.mul x.2 y.2)))
    (poly.add (poly.mul x.1 (poly.mul y.2 z.2))
      (poly.mul (poly.add (poly.mul y.1 z.2)
        (poly.mul z.1 y.2)) x.2))
  refine poly.oneValue_trans
    (poly.add_congr (poly.sum_mul (poly.mul x.1 y.2)
      (poly.mul y.1 x.2) z.2) (poly.oneValue_refl _)) ?_
  refine poly.oneValue_trans
    (poly.oneValue_symm (poly.add_join _ _ _)) ?_
  refine poly.oneValue_trans ?_
    (poly.add_congr (poly.oneValue_refl _)
      (poly.oneValue_symm (poly.sum_mul (poly.mul y.1 z.2)
        (poly.mul z.1 y.2) x.2)))
  refine poly.add_congr (poly.mul_assoc x.1 y.2 z.2) ?_
  refine poly.add_congr ?_ ?_
  · exact poly.oneValue_trans (poly.mul_assoc y.1 x.2 z.2)
      (poly.oneValue_trans (poly.mul_congr y.1
        (poly.mul_comm x.2 z.2))
        (poly.oneValue_symm (poly.mul_assoc y.1 z.2 x.2)))
  · exact poly.oneValue_trans (poly.mul_congr z.1
      (poly.mul_comm x.2 y.2))
      (poly.oneValue_symm (poly.mul_assoc z.1 y.2 x.2))



/-- The reduction reads with its pair, occupancy included. -/
private theorem pEq_pReduce (x : poly.PPair) :
    pEq (genericlift.pReduce x) x :=
  pEq_mk (genericlift.pReduce_read x) (pEq_pReduce_den x)

/-- The accumulating sum reads with the displayed sum. -/
private theorem pEq_pAddR (x y : poly.PPair) :
    pEq (genericlift.pAddR x y) (poly.pAdd x y) :=
  pEq_pReduce (poly.pAdd x y)

/-- The accumulating sum's joined read at two joined reads. -/
private theorem pEq_addR {x x' y y' : poly.PPair} (h1 : pEq x x')
    (h2 : pEq y y') :
    pEq (genericlift.pAddR x y) (genericlift.pAddR x' y') :=
  pEq_trans (pEq_pAddR x y)
    (pEq_trans (pEq_pAdd h1 h2) (pEq_symm (pEq_pAddR x' y')))

/-- Two pair lists read memberwise. -/
private def pEqL : List poly.PPair → List poly.PPair → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | x :: t, y :: s => pEq x y ∧ pEqL t s

/-- Two accumulating folds at memberwise reads and a joined
start read alike. -/
private theorem foldR_congr : ∀ (l l' : List poly.PPair), pEqL l l' →
    ∀ acc acc' : poly.PPair, pEq acc acc' →
      pEq (l.foldl genericlift.pAddR acc)
        (l'.foldl genericlift.pAddR acc')
  | [], [], _, _, _, h => h
  | [], _ :: _, hl, _, _, _ => hl.elim
  | _ :: _, [], hl, _, _, _ => hl.elim
  | _ :: t, _ :: s, hl, _, _, h =>
    foldR_congr t s hl.2 _ _ (pEq_addR h hl.1)

/-- The pair list's displayed sum at the certified reduction. -/
private def sumL (l : List poly.PPair) : poly.PPair :=
  l.foldl genericlift.pAddR poly.pZero

/-- The accumulation from the sum's unit reads the summand. -/
private theorem pEq_addRZero (x : poly.PPair) :
    pEq (genericlift.pAddR poly.pZero x) x :=
  pEq_trans (pEq_pAddR poly.pZero x)
    (pEq_trans (pEq_addComm poly.pZero x) (pEq_addZeroR x))

/-- The accumulating fold reads the start joined to the list's
own sum. -/
private theorem foldR_split : ∀ (l : List poly.PPair) (acc : poly.PPair),
    pEq (l.foldl genericlift.pAddR acc) (poly.pAdd acc (sumL l))
  | [], acc => pEq_symm (pEq_addZeroR acc)
  | x :: t, acc =>
    pEq_trans (foldR_split t (genericlift.pAddR acc x))
      (pEq_trans (pEq_pAdd (pEq_pAddR acc x) (pEq_refl (sumL t)))
        (pEq_trans (pEq_addAssoc acc x (sumL t))
          (pEq_pAdd (pEq_refl acc)
            (pEq_symm (pEq_trans
              (foldR_split t (genericlift.pAddR poly.pZero x))
              (pEq_pAdd (pEq_addRZero x) (pEq_refl (sumL t))))))))

/-- The consed list's sum reads the head joined to the tail's. -/
private theorem sumL_cons (x : poly.PPair) (l : List poly.PPair) :
    pEq (sumL (x :: l)) (poly.pAdd x (sumL l)) :=
  pEq_trans (foldR_split l (genericlift.pAddR poly.pZero x))
    (pEq_pAdd (pEq_addRZero x) (pEq_refl (sumL l)))

/-- The joined list's sum reads the two sums' own sum. -/
private theorem sumL_append (l1 l2 : List poly.PPair) :
    pEq (sumL (l1 ++ l2)) (poly.pAdd (sumL l1) (sumL l2)) := by
  show pEq ((l1 ++ l2).foldl genericlift.pAddR poly.pZero)
    (poly.pAdd (sumL l1) (sumL l2))
  rw [ground.foldl_append genericlift.pAddR l1 l2 poly.pZero]
  exact foldR_split l2 (sumL l1)

/-- Two accumulating folds at equal sums and a joined start read
alike. -/
private theorem foldR_of_sum (l l' : List poly.PPair)
    (hs : pEq (sumL l) (sumL l')) (acc acc' : poly.PPair)
    (h : pEq acc acc') :
    pEq (l.foldl genericlift.pAddR acc)
      (l'.foldl genericlift.pAddR acc') :=
  pEq_trans (foldR_split l acc)
    (pEq_trans (pEq_pAdd h hs) (pEq_symm (foldR_split l' acc')))

/-- The four summands' exchange at the pair carrier. -/
private theorem pEq_add4 (a b c d : poly.PPair) :
    pEq (poly.pAdd (poly.pAdd a b) (poly.pAdd c d))
      (poly.pAdd (poly.pAdd a c) (poly.pAdd b d)) :=
  pEq_trans (pEq_addAssoc a b (poly.pAdd c d))
    (pEq_trans (pEq_pAdd (pEq_refl a)
      (pEq_symm (pEq_addAssoc b c d)))
      (pEq_trans (pEq_pAdd (pEq_refl a)
        (pEq_pAdd (pEq_addComm b c) (pEq_refl d)))
        (pEq_trans (pEq_pAdd (pEq_refl a) (pEq_addAssoc c b d))
          (pEq_symm (pEq_addAssoc a c (poly.pAdd b d))))))


/-- Two memberwise-reading lists have one sum. -/
private theorem sumL_congr (l l' : List poly.PPair) (h : pEqL l l') :
    pEq (sumL l) (sumL l') :=
  foldR_congr l l' h poly.pZero poly.pZero (pEq_refl poly.pZero)

/-- Two mapped families at memberwise reads read memberwise. -/
private theorem pEqL_map {β : Type} (F G : β → poly.PPair) :
    ∀ (bs : List β), (∀ w ∈ bs, pEq (F w) (G w)) →
      pEqL (bs.map F) (bs.map G)
  | [], _ => trivial
  | w :: r, h =>
    ⟨h w (List.Mem.head r),
     pEqL_map F G r (fun x hx => h x (List.Mem.tail w hx))⟩

/-- A keyed union of consed blocks splits: the heads' sum joined
to the tails' union's. -/
private theorem sumL_flatCons {β : Type} (c : β → poly.PPair)
    (d : β → List poly.PPair) :
    ∀ bs : List β,
    pEq (sumL (bs.flatMap (fun w => c w :: d w)))
      (poly.pAdd (sumL (bs.map c)) (sumL (bs.flatMap d)))
  | [] => pEq_symm (pEq_addZeroR poly.pZero)
  | w :: r =>
    pEq_trans
      (sumL_append (c w :: d w) (r.flatMap (fun z => c z :: d z)))
      (pEq_trans
        (pEq_pAdd (sumL_cons (c w) (d w)) (sumL_flatCons c d r))
        (pEq_trans
          (pEq_add4 (c w) (sumL (d w)) (sumL (r.map c))
            (sumL (r.flatMap d)))
          (pEq_symm (pEq_pAdd (sumL_cons (c w) (r.map c))
            (sumL_append (d w) (r.flatMap d))))))

/-- The rectangle's two orders have one sum: the row-major keyed
union and the column-major one at memberwise reads. -/
private theorem sumL_transpose {α β : Type} (f : α → β → poly.PPair)
    (g : β → α → poly.PPair) (bs : List β) :
    ∀ (as : List α),
      (∀ u ∈ as, ∀ w ∈ bs, pEq (f u w) (g w u)) →
      pEq (sumL (as.flatMap (fun u => bs.map (f u))))
        (sumL (bs.flatMap (fun w => as.map (g w))))
  | [], _ => by
    have hv : bs.flatMap (fun w => ([] : List α).map (g w)) = [] :=
      ground.flatMap_nil _ bs (fun _ _ => rfl)
    show pEq (sumL (([] : List α).flatMap (fun u => bs.map (f u))))
      (sumL (bs.flatMap (fun w => ([] : List α).map (g w))))
    rw [hv]
    exact pEq_refl (sumL [])
  | u :: t, h =>
    pEq_trans
      (sumL_append (bs.map (f u)) (t.flatMap (fun z => bs.map (f z))))
      (pEq_trans
        (pEq_pAdd
          (sumL_congr (bs.map (f u)) (bs.map (fun w => g w u))
            (pEqL_map (f u) (fun w => g w u) bs
              (fun w hw => h u (List.Mem.head t) w hw)))
          (sumL_transpose f g bs t
            (fun x hx => h x (List.Mem.tail u hx))))
        (pEq_symm (sumL_flatCons (fun w => g w u)
          (fun w => t.map (g w)) bs)))

/-- The termwise accumulation is the mapped list's own fold. -/
private theorem foldT {α : Type} (T : α → poly.PPair) :
    ∀ (l : List α) (acc : poly.PPair),
      l.foldl (fun a e => genericlift.pAddR a (T e)) acc
        = (l.map T).foldl genericlift.pAddR acc
  | [], _ => rfl
  | e :: t, acc => foldT T t (genericlift.pAddR acc (T e))




/-- A key below a three-block count sits in one of the blocks. -/
private theorem ixCases {n a b : Nat} (i : Nat)
    (h : i < n + (b + a)) :
    i < n ∨ (∃ r, r < b ∧ i = n + r)
      ∨ (∃ s, s < a ∧ i = n + (b + s)) := by
  match Nat.lt_or_ge i n with
  | .inl hi => exact Or.inl hi
  | .inr hge =>
    obtain ⟨d, hd⟩ := Nat.le.dest hge
    match Nat.lt_or_ge d b with
    | .inl hdb => exact Or.inr (Or.inl ⟨d, hdb, hd.symm⟩)
    | .inr hgeb =>
      obtain ⟨e, he⟩ := Nat.le.dest hgeb
      have h1 : n + (b + e) < n + (b + a) := by
        rw [he, hd]
        exact h
      refine Or.inr (Or.inr ⟨e,
        Nat.lt_of_add_lt_add_left (Nat.lt_of_add_lt_add_left h1),
        ?_⟩)
      rw [he, hd]

/-- A join's entry below the first block's count is the first
block's own. -/
private theorem app_low {α : Type} (d : α) (u v : List α)
    (m i : Nat) (hm : u.length = m) (h : i < m) :
    ground.getAt d (u ++ v) i = ground.getAt d u i := by
  rw [ground.getAt_append d u v i, if_pos (by rw [hm]; exact h)]

/-- A join's entry past the first block's count is the second
block's own. -/
private theorem app_high {α : Type} (d : α) (u v : List α)
    (m r : Nat) (hm : u.length = m) :
    ground.getAt d (u ++ v) (m + r) = ground.getAt d v r := by
  rw [← hm]
  exact ground.getAt_append_add d u v r

/-- The concatenated site's two orders are one relabeling: the
swapped site reads the site at the block swap's own keys. -/
private theorem site_swap (F Fa Fb : states.FList) :
    wg.conjF F ++ (Fb ++ Fa)
      = (states.swapW F.length Fa.length Fb.length).map
        (fun j => ground.getAt ((false, false) : states.Factor)
          (wg.conjF F ++ (Fa ++ Fb)) j) := by
  have hcl : (wg.conjF F).length = F.length := by
    show (F.map (fun f => (f.1, !f.2))).length = F.length
    rw [ground.length_map]
  have hlen : (wg.conjF F ++ (Fb ++ Fa)).length
      = F.length + (Fb.length + Fa.length) := by
    rw [ground.length_append, hcl, ground.length_append]
  have hswl : (states.swapW F.length Fa.length Fb.length).length
      = F.length + (Fb.length + Fa.length) :=
    states.length_swapW F.length Fa.length Fb.length
  refine ground.getAt_ext ((false, false) : states.Factor) _ _ ?_ ?_
  · rw [hlen, ground.length_map, hswl]
  · intro i hi
    rw [hlen] at hi
    have hrd : ∀ k, k < F.length + (Fb.length + Fa.length) →
        ground.getAt ((false, false) : states.Factor)
          ((states.swapW F.length Fa.length Fb.length).map
            (fun j => ground.getAt ((false, false) : states.Factor)
              (wg.conjF F ++ (Fa ++ Fb)) j)) k
          = ground.getAt ((false, false) : states.Factor)
            (wg.conjF F ++ (Fa ++ Fb))
            (ground.getAt 0
              (states.swapW F.length Fa.length Fb.length) k) := by
      intro k hk
      exact ground.getAt_map 0 ((false, false) : states.Factor) _
        (states.swapW F.length Fa.length Fb.length) k
        (by rw [hswl]; exact hk)
    match ixCases (n := F.length) (b := Fb.length) (a := Fa.length)
        i hi with
    | .inl hk =>
      rw [hrd i (Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)),
        states.getAt_swapW_low F.length Fa.length Fb.length i hk,
        app_low ((false, false) : states.Factor) (wg.conjF F)
          (Fb ++ Fa) F.length i hcl hk,
        app_low ((false, false) : states.Factor) (wg.conjF F)
          (Fa ++ Fb) F.length i hcl hk]
    | .inr (.inl ⟨r, hr, hir⟩) =>
      rw [hir]
      have hlt : F.length + r < F.length + (Fb.length + Fa.length) :=
        Nat.add_lt_add_left
          (Nat.lt_of_lt_of_le hr (Nat.le_add_right _ _)) F.length
      rw [hrd (F.length + r) hlt,
        states.getAt_swapW_mid F.length Fa.length Fb.length r hr,
        app_high ((false, false) : states.Factor) (wg.conjF F)
          (Fb ++ Fa) F.length r hcl,
        app_low ((false, false) : states.Factor) Fb Fa
          Fb.length r rfl hr,
        app_high ((false, false) : states.Factor) (wg.conjF F)
          (Fa ++ Fb) F.length (Fa.length + r) hcl,
        app_high ((false, false) : states.Factor) Fa Fb
          Fa.length r rfl]
    | .inr (.inr ⟨s, hs, his⟩) =>
      rw [his]
      have hlt : F.length + (Fb.length + s)
          < F.length + (Fb.length + Fa.length) :=
        Nat.add_lt_add_left (Nat.add_lt_add_left hs Fb.length)
          F.length
      rw [hrd (F.length + (Fb.length + s)) hlt,
        states.getAt_swapW_high F.length Fa.length Fb.length s hs,
        app_high ((false, false) : states.Factor) (wg.conjF F)
          (Fb ++ Fa) F.length (Fb.length + s) hcl,
        app_high ((false, false) : states.Factor) Fb Fa
          Fb.length s rfl,
        app_high ((false, false) : states.Factor) (wg.conjF F)
          (Fa ++ Fb) F.length s hcl,
        app_low ((false, false) : states.Factor) Fa Fb
          Fa.length s rfl hs]



/-- The shifted wiring's entry is the wiring's own shifted. -/
private theorem getAt_shiftW (m : Nat) (π : List Nat) (i : Nat)
    (h : i < π.length) :
    ground.getAt 0 (states.shiftW m π) i
      = ground.getAt 0 π i + m := by
  show ground.getAt 0 (π.map (fun j => j + m)) i
    = ground.getAt 0 π i + m
  rw [ground.getAt_map 0 0 (fun j => j + m) π i h]

/-- The blocked wiring's entry below the head's count is the
flipped key's own. -/
private theorem wire_readLow (n : Nat) (kv X : List Nat)
    (i : Nat) (hi : i < n) :
    ground.getAt 0 (places.invPerm n kv ++ states.shiftW n X) i
      = ground.getAt 0 (places.invPerm n kv) i := by
  rw [ground.getAt_append 0 (places.invPerm n kv) _ i,
    places.length_invPerm, if_pos hi]

/-- The blocked wiring's entry past the head's count is the
second block's own shifted. -/
private theorem wire_read (n : Nat) (kv X : List Nat)
    (r : Nat) (hr : r < X.length) :
    ground.getAt 0 (places.invPerm n kv ++ states.shiftW n X) (n + r)
      = ground.getAt 0 X r + n := by
  have hk := ground.getAt_append_add 0 (places.invPerm n kv)
    (states.shiftW n X) r
  rw [places.length_invPerm] at hk
  rw [hk, getAt_shiftW n X r hr]



/-- The concatenated wiring's two orders are the block swap's
conjugate at the site relabeling. -/
private theorem wire_swap (n a b : Nat) {kv ka kb : List Nat}
    (hv : states.permAt kv n) (ha : states.permAt ka a)
    (hb : states.permAt kb b) :
    places.invPerm n kv ++ states.shiftW n (kb ++ states.shiftW b ka)
      = (states.swapW n a b).map
        (fun j => ground.getAt 0
          (places.invPerm (n + (a + b)) (states.swapW n a b))
          (ground.getAt 0 (places.invPerm n kv
            ++ states.shiftW n (ka ++ states.shiftW a kb)) j)) := by
  have hRm : 0 < ground.countOf (states.swapW n a b)
      (places.perms (n + (a + b))) :=
    states.permAt_member (states.permAt_swapW n a b)
  have hRlen : (states.swapW n a b).length = n + (b + a) :=
    states.length_swapW n a b
  have hXlen : (ka ++ states.shiftW a kb).length = a + b := by
    rw [ground.length_append, ha.1, states.length_shiftW, hb.1]
  have hYlen : (kb ++ states.shiftW b ka).length = b + a := by
    rw [ground.length_append, hb.1, states.length_shiftW, ha.1]
  have hiv : states.permAt (places.invPerm n kv) n :=
    states.member_permAt
      (places.invPerm_member n (states.permAt_member hv))
  have hpl : ∀ i, i < n + (a + b) →
      ground.getAt 0 (places.invPerm (n + (a + b))
          (states.swapW n a b))
        (ground.getAt 0 (states.swapW n a b) i) = i :=
    fun i hi => places.perm_left (n + (a + b)) hRm i hi
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_append, places.length_invPerm,
      states.length_shiftW, hYlen, ground.length_map, hRlen]
  · intro i hi
    rw [ground.length_append, places.length_invPerm,
      states.length_shiftW, hYlen] at hi
    have hrd : ∀ k, k < n + (b + a) →
        ground.getAt 0 ((states.swapW n a b).map
          (fun j => ground.getAt 0
            (places.invPerm (n + (a + b)) (states.swapW n a b))
            (ground.getAt 0 (places.invPerm n kv
              ++ states.shiftW n (ka ++ states.shiftW a kb)) j))) k
          = ground.getAt 0
            (places.invPerm (n + (a + b)) (states.swapW n a b))
            (ground.getAt 0 (places.invPerm n kv
              ++ states.shiftW n (ka ++ states.shiftW a kb))
              (ground.getAt 0 (states.swapW n a b) k)) := by
      intro k hk
      exact ground.getAt_map 0 0 _ (states.swapW n a b) k
        (by rw [hRlen]; exact hk)
    match ixCases (n := n) (b := b) (a := a) i hi with
    | .inl hk =>
      have hp : ground.getAt 0 (places.invPerm n kv) i < n :=
        places.perm_lt _ (states.permAt_member hiv) i hk
      have hkey := hpl
        (ground.getAt 0 (places.invPerm n kv) i)
        (Nat.lt_of_lt_of_le hp (Nat.le_add_right n (a + b)))
      rw [states.getAt_swapW_low n a b _ hp] at hkey
      rw [hrd i (Nat.lt_of_lt_of_le hk (Nat.le_add_right n (b + a))),
        states.getAt_swapW_low n a b i hk,
        wire_readLow n kv (ka ++ states.shiftW a kb) i hk,
        wire_readLow n kv (kb ++ states.shiftW b ka) i hk]
      exact hkey.symm
    | .inr (.inl ⟨t, ht, hit⟩) =>
      have htY : t < (kb ++ states.shiftW b ka).length := by
        rw [hYlen]
        exact Nat.lt_of_lt_of_le ht (Nat.le_add_right b a)
      have hq : ground.getAt 0 kb t < b := places.perm_lt _ (states.permAt_member hb) t ht
      have hkey := hpl
        (n + ground.getAt 0 kb t)
        (Nat.add_lt_add_left
          (Nat.lt_of_lt_of_le hq (Nat.le_add_left b a)) n)
      rw [states.getAt_swapW_mid n a b _ hq] at hkey
      rw [hit, wire_read n kv (kb ++ states.shiftW b ka) t htY,
        app_low 0 kb (states.shiftW b ka) b t hb.1 ht,
        hrd (n + t) (Nat.add_lt_add_left
          (Nat.lt_of_lt_of_le ht (Nat.le_add_right b a)) n),
        states.getAt_swapW_mid n a b t ht,
        wire_read n kv (ka ++ states.shiftW a kb) (a + t)
          (by rw [hXlen]; exact Nat.add_lt_add_left ht a),
        app_high 0 ka (states.shiftW a kb) a t ha.1,
        getAt_shiftW a kb t (by rw [hb.1]; exact ht),
        show ground.getAt 0 kb t + a + n
          = n + (a + ground.getAt 0 kb t) from by
          rw [Nat.add_comm (ground.getAt 0 kb t) a,
            Nat.add_comm (a + ground.getAt 0 kb t) n],
        hkey, Nat.add_comm n (ground.getAt 0 kb t)]
    | .inr (.inr ⟨s, hs, his⟩) =>
      have hsY : b + s < (kb ++ states.shiftW b ka).length := by
        rw [hYlen]
        exact Nat.add_lt_add_left hs b
      have hq : ground.getAt 0 ka s < a := places.perm_lt _ (states.permAt_member ha) s hs
      have hkey := hpl
        (n + (b + ground.getAt 0 ka s))
        (Nat.add_lt_add_left
          (by rw [Nat.add_comm a b]; exact Nat.add_lt_add_left hq b)
          n)
      rw [states.getAt_swapW_high n a b _ hq] at hkey
      rw [his, wire_read n kv (kb ++ states.shiftW b ka) (b + s) hsY,
        app_high 0 kb (states.shiftW b ka) b s hb.1,
        getAt_shiftW b ka s (by rw [ha.1]; exact hs),
        hrd (n + (b + s)) (Nat.add_lt_add_left
          (Nat.add_lt_add_left hs b) n),
        states.getAt_swapW_high n a b s hs,
        wire_read n kv (ka ++ states.shiftW a kb) s
          (by rw [hXlen]
              exact Nat.lt_of_lt_of_le hs (Nat.le_add_right a b)),
        app_low 0 ka (states.shiftW a kb) a s ha.1 hs,
        show ground.getAt 0 ka s + n = n + ground.getAt 0 ka s from
          Nat.add_comm (ground.getAt 0 ka s) n,
        hkey, Nat.add_comm (ground.getAt 0 ka s) b,
        Nat.add_comm (b + ground.getAt 0 ka s) n]


/-- The pairing reads the concatenated generator at either block
order: the two sites are one state at the word index, and the
relabeling carries the evaluation. -/
private theorem pairPhi_swap (F Fa Fb : states.FList)
    {kv ka kb : List Nat} (hv : states.permAt kv F.length)
    (ha : states.permAt ka Fa.length)
    (hb : states.permAt kb Fb.length) :
    genericlift.crossNull
      (wg.pairPhi F (Fb ++ Fa) kv (kb ++ states.shiftW Fb.length ka))
      (wg.pairPhi F (Fa ++ Fb) kv
        (ka ++ states.shiftW Fa.length kb)) := by
  have hcl : (wg.conjF F).length = F.length := by
    show (F.map (fun f => (f.1, !f.2))).length = F.length
    rw [ground.length_map]
  have hlen : (wg.conjF F ++ (Fa ++ Fb)).length
      = F.length + (Fa.length + Fb.length) := by
    rw [ground.length_append, hcl, ground.length_append]
  have hiv : states.permAt (places.invPerm F.length kv) F.length :=
    states.member_permAt
      (places.invPerm_member F.length (states.permAt_member hv))
  have hpi := states.permAt_member
    (states.permAt_concat hiv (states.permAt_concat ha hb))
  have hrm := states.permAt_member
    (states.permAt_swapW F.length Fa.length Fb.length)
  have ht := wg.evalPhi_transport (wg.conjF F ++ (Fa ++ Fb))
    (places.invPerm F.length kv ++ states.shiftW F.length
      (ka ++ states.shiftW Fa.length kb))
    (states.swapW F.length Fa.length Fb.length)
    (by rw [hlen]; exact hpi) (by rw [hlen]; exact hrm)
  rw [hlen, ← site_swap F Fa Fb,
    ← wire_swap F.length Fa.length Fb.length hv ha hb] at ht
  exact ht


/-- The product's exchange at the pair carrier. -/
private theorem pEq_mulComm (x y : poly.PPair) :
    pEq (poly.pMul x y) (poly.pMul y x) :=
  pEq_of_parts (poly.mul_comm x.1 y.1) (poly.mul_comm x.2 y.2)

/-- A branched pair's second member stays occupied where both
factors do. -/
private theorem den_ite (c : Bool) (A p q : poly.Poly)
    (hp : ¬ poly.unitTail p) (hq : ¬ poly.unitTail q) :
    ¬ poly.unitTail
      (if c then (A, poly.mul p q) else poly.pZero).2 := by
  cases c with
  | false =>
    exact fun h => ground.BPair.ofPos_off ground.Pos.one h.1
  | true => exact fun h => (poly.unitTail_mul_of h).elim hp hq

/-- The generator's evaluation carries an occupied second
member: the Gram determinants sit off the sum's unit. -/
private theorem evalPhi_den (G : states.FList) (π : List Nat) :
    ¬ poly.unitTail (wg.evalPhi G π).2 :=
  den_ite _ _ _ _ (wg.gramWg_detOcc _) (wg.gramWg_detOcc _)

/-- The pairing carries an occupied second member. -/
private theorem pairPhi_den (Fu Fw : states.FList)
    (πa πb : List Nat) :
    ¬ poly.unitTail (wg.pairPhi Fu Fw πa πb).2 :=
  evalPhi_den _ _

/-- One triple's term reads at either block order: the
coefficients exchange and the pairing transports. -/
private theorem term_swap (F Fa Fb : states.FList)
    {kv ka kb : List Nat} (hv : states.permAt kv F.length)
    (ha : states.permAt ka Fa.length)
    (hb : states.permAt kb Fb.length) (cv cx cy : poly.PPair) :
    pEq (poly.pMul (poly.pMul cv (poly.pMul cx cy))
        (wg.pairPhi F (Fa ++ Fb) kv
          (ka ++ states.shiftW Fa.length kb)))
      (poly.pMul (poly.pMul cv (poly.pMul cy cx))
        (wg.pairPhi F (Fb ++ Fa) kv
          (kb ++ states.shiftW Fb.length ka))) := by
  refine pEq_pMul (pEq_pMul (pEq_refl cv) (pEq_mulComm cx cy)) ?_
  refine pEq_mk ?_ ⟨fun h => absurd h (pairPhi_den _ _ _ _),
    fun h => absurd h (pairPhi_den _ _ _ _)⟩
  exact (genericlift.crossNull_ov _ _).mpr (poly.oneValue_symm
    ((genericlift.crossNull_ov _ _).mp
      (pairPhi_swap F Fa Fb hv ha hb)))

/-- The product state's termwise images are the row-major keyed
union of the factor states' own. -/
private theorem prod_map (F Fu Fw : states.FList) (a b : states.Comb)
    (ev : List Nat × poly.PPair) :
    (states.mulComb a b).map (fun e =>
        poly.pMul (poly.pMul ev.2 e.2)
          (wg.pairPhi F (Fu ++ Fw) ev.1 e.1))
      = a.flatMap (fun ea => b.map (fun eb =>
        poly.pMul (poly.pMul ev.2 (poly.pMul ea.2 eb.2))
          (wg.pairPhi F (Fu ++ Fw) ev.1
            (ea.1 ++ states.shiftW ea.1.length eb.1)))) := by
  show ((a.flatMap (fun ea => b.map (fun eb =>
      (ea.1 ++ states.shiftW ea.1.length eb.1,
        poly.pMul ea.2 eb.2)))).map (fun e =>
      poly.pMul (poly.pMul ev.2 e.2)
        (wg.pairPhi F (Fu ++ Fw) ev.1 e.1))) = _
  rw [ground.map_flatMap]
  refine ground.flatMap_congr_all _ _ (fun ea => ?_) a
  rw [ground.map_map]

/-- Two termwise accumulations at equal sums and a joined start
read alike. -/
private theorem foldT_of_sum {α β : Type} (C : List α) (C' : List β)
    (T : α → poly.PPair) (T' : β → poly.PPair)
    (hs : pEq (sumL (C.map T)) (sumL (C'.map T')))
    (acc acc' : poly.PPair) (h : pEq acc acc') :
    pEq (C.foldl (fun q e => genericlift.pAddR q (T e)) acc)
      (C'.foldl (fun q e => genericlift.pAddR q (T' e)) acc') := by
  rw [foldT T C acc, foldT T' C' acc']
  exact foldR_of_sum _ _ hs acc acc' h

/-- The window fold carries the inner folds' reads. -/
private theorem outer_fold {α β : Type} (C : List α) (C' : List β)
    (T : List Nat × poly.PPair → α → poly.PPair)
    (T' : List Nat × poly.PPair → β → poly.PPair) :
    ∀ (v : states.Comb),
      (∀ ev ∈ v, ∀ acc acc' : poly.PPair, pEq acc acc' →
        pEq (C.foldl (fun q e => genericlift.pAddR q (T ev e)) acc)
          (C'.foldl (fun q e => genericlift.pAddR q (T' ev e)) acc'))
      → ∀ acc acc' : poly.PPair, pEq acc acc' →
        pEq (v.foldl (fun q ev =>
            C.foldl (fun r e => genericlift.pAddR r (T ev e)) q) acc)
          (v.foldl (fun q ev =>
            C'.foldl (fun r e => genericlift.pAddR r (T' ev e)) q)
            acc')
  | [], _, _, _, h => h
  | ev :: t, hL, acc, acc', h =>
    outer_fold C C' T T' t (fun x hx => hL x (List.Mem.tail ev hx))
      _ _ (hL ev (List.Mem.head t) acc acc' h)

/-- `prop:algebra`'s commutativity at the presentation carrier:
the pairing against a product state reads one value at either
block order, the block swap a letter-preserving relabeling of the
concatenated site and its wiring (`con:states`' block-exchange
clause at `rem:kernel`'s word index). -/
theorem prodComm (F Fa Fb : states.FList) (v a b : states.Comb)
    (hv : (v.all (fun e =>
      decide (states.permAt e.1 F.length))) = true)
    (ha : (a.all (fun e =>
      decide (states.permAt e.1 Fa.length))) = true)
    (hb : (b.all (fun e =>
      decide (states.permAt e.1 Fb.length))) = true) :
    genericlift.crossNull
      (wg.pairFull F (Fa ++ Fb) v (states.mulComb a b))
      (wg.pairFull F (Fb ++ Fa) v (states.mulComb b a)) := by
  have key : pEq (wg.pairFull F (Fa ++ Fb) v (states.mulComb a b))
      (wg.pairFull F (Fb ++ Fa) v (states.mulComb b a)) := by
    show pEq (v.foldl (fun q ev =>
        (states.mulComb a b).foldl (fun r e =>
          genericlift.pAddR r (poly.pMul (poly.pMul ev.2 e.2)
            (wg.pairPhi F (Fa ++ Fb) ev.1 e.1))) q) poly.pZero)
      (v.foldl (fun q ev =>
        (states.mulComb b a).foldl (fun r e =>
          genericlift.pAddR r (poly.pMul (poly.pMul ev.2 e.2)
            (wg.pairPhi F (Fb ++ Fa) ev.1 e.1))) q) poly.pZero)
    refine outer_fold (states.mulComb a b) (states.mulComb b a)
      (fun ev e => poly.pMul (poly.pMul ev.2 e.2)
        (wg.pairPhi F (Fa ++ Fb) ev.1 e.1))
      (fun ev e => poly.pMul (poly.pMul ev.2 e.2)
        (wg.pairPhi F (Fb ++ Fa) ev.1 e.1))
      v ?_ poly.pZero poly.pZero (pEq_refl poly.pZero)
    intro ev hev acc acc' hacc
    have hpv : states.permAt ev.1 F.length :=
      of_decide_eq_true (ground.all_of_mem _ v hv ev hev)
    refine foldT_of_sum _ _ _ _ ?_ acc acc' hacc
    rw [prod_map F Fa Fb a b ev, prod_map F Fb Fa b a ev]
    refine sumL_transpose _ _ b a ?_
    intro ea hea eb heb
    have hpa : states.permAt ea.1 Fa.length :=
      of_decide_eq_true (ground.all_of_mem _ a ha ea hea)
    have hpb : states.permAt eb.1 Fb.length :=
      of_decide_eq_true (ground.all_of_mem _ b hb eb heb)
    rw [hpa.1, hpb.1]
    exact term_swap F Fa Fb hpv hpa hpb ev.2 ea.2 eb.2
  exact key.1


/-- The window list's rows exchange one row at a time. -/
private theorem rhs_rows (F Fa Fb : states.FList) (a b : states.Comb)
    (ha : (a.all (fun e =>
      decide (states.permAt e.1 Fa.length))) = true)
    (hb : (b.all (fun e =>
      decide (states.permAt e.1 Fb.length))) = true) :
    ∀ ws : List states.Comb,
      (ws.all (fun v => v.all (fun e =>
        decide (states.permAt e.1 F.length)))) = true →
      genericlift.pprowEq
        (ws.map (fun v =>
          wg.pairFull F (Fa ++ Fb) v (states.mulComb a b)))
        (ws.map (fun v =>
          wg.pairFull F (Fb ++ Fa) v (states.mulComb b a)))
  | [], _ => trivial
  | v :: t, h => by
    have hsplit : ((v.all (fun e =>
        decide (states.permAt e.1 F.length)))
      && (t.all (fun w => w.all (fun e =>
        decide (states.permAt e.1 F.length))))) = true := h
    obtain ⟨h1, h2⟩ := ground.andSplitB hsplit
    exact ⟨prodComm F Fa Fb v a b h1 ha hb,
      rhs_rows F Fa Fb a b ha hb t h2⟩

/-- `prop:algebra`'s commutativity at the pairing identity's right
side: the window list's coordinates read one value at either block
order. -/
theorem prodRhsComm (F Fa Fb : states.FList)
    (ws : List states.Comb) (a b : states.Comb)
    (hw : (ws.all (fun v => v.all (fun e =>
      decide (states.permAt e.1 F.length)))) = true)
    (ha : (a.all (fun e =>
      decide (states.permAt e.1 Fa.length))) = true)
    (hb : (b.all (fun e =>
      decide (states.permAt e.1 Fb.length))) = true) :
    genericlift.pprowEq
      (algebra.prodRhs F Fa Fb ws a b)
      (algebra.prodRhs F Fb Fa ws b a) :=
  rhs_rows F Fa Fb a b ha hb ws hw

end

end algebra
