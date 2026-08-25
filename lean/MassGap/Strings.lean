import MassGap.Lowerspan
import MassGap.Tops
/-!
`lem:strings` — the pairs' orthogonal string exhaustion at the
span: per letter pair the span splits into sl2 strings, each a
top with its depth run, the members pairwise perpendicular across
strings, one member per content per string, the per-content
members an independent list spanning the content group's span.
The construction is the residual walk over the pool's contents
at the pair's height descending (`lem:strings`' walk clause): at
each content, a group member refusing the residual against the
collected members names a new top, the residual vector itself,
perpendicular to the collected list by the solve's identity.  The
semantic tier is landed: every collected string good — sized, at
the genuine gap (`tops.top_gap`, the pairing's read), its top
raising-free at the processed maximality (`top_propL`) and off
the sum's unit inside its group's span — the members pairwise
perpendicular and off the unit at every content (`walk_perp`,
`walk_off`), the sl2 kit at the fold's read (`iterAct_raise`,
`iterAct_term`, `iterAct_selfpair` at `coeffProd`), and the
string count reading the span occupancy at every content
(`walk_count`, the exchange read `elim.span_count_eq` closing
the comparison with the fuel bound its own contrapositive).  The
trace tier's string data lands beside them (`thm:weylchar`'s
string-by-string trace): at a collected member the pair's two
ordered words read the depth's own coefficients — the
raising-after-lowering `E_ij E_ji` at `(b+1)(h-b)`, the further
lowering the string's next member and the raising back the
scale (`iterAct_raise`), and the lowering-after-raising
`E_ji E_ij` at `b(h-b+1)`, the raising the shallower member at
its scale and the lowering back the member itself — the vacant
letter's branches (the height's own depth on the raising side,
the top's own depth on the lowering side) reading the sum's unit
against the coefficient's zero, so `lem:tops`(ii)'s fold enters
twice at the words `F^{b+1}` and `F^b`.  The weights collect
along `membersAt`'s own spine, one entry per collected member
(`weightList` at its stated coefficient, its width the members'
own by `weightList_length`), and the two side sums are
`stringWeightUp` and `stringWeightDn`, the reads exported at the
exhaustion's own strings (`walk_traceUp`, `walk_traceDn`,
the depth run's per-string alignment folded to the collected
list).  The content symmetry lands on top of them
(`symRead_def`, `lem:strings`' closing clause): at a good string
the depth run reverses under the letter transposition — the
depth-`(h-b)` member's content is the depth-`b` member's
transposed, the top's gap the join of the two entry identities
(`member_mirrorL`) — so the picks at a content and at its
transposition match depth for depth, their collected counts agree
under the range reversal (`sumTo_revL`), and summing string by
string the string count is transposition-invariant, the span
occupancy with it through `walk_count`.  The trace tier's
collection lands on top of them (`stringCollect`, `lem:casimir`'s
per-string identity read at the exhaustion, `thm:weylchar`'s
"Collecting string by string" clause): the two side weights with
the moved folds `weylchar.gSnd`/`gFst` at the span's multiplicity
and the two letters' counts read one identity at every content —
the multiplicity the string count at every content (`blockcount.span_countOf`
into `walk_count`), the moved folds exchanged into per-string
folds, and per string the trichotomy one hit read at the ladder
line (`onLineL`, the hit the depth join `hit_iffL`): a through
content at its depth's gap identity, a content below the ladder at
the depth run's reversal with the paired depths summing to equal
members, every further content at the count's unit.  The
remainder: the display's pair fold at `thm:weylchar`'s `recRead`.
The carrier, coordinate and pool-group reads the walk consumes
live at their owners — `def:elim`'s one-value tier
and orthogonal join, `con:units`' letter reads, and
`def:blockcount`'s group and occupancy kit — so this module holds
the string machinery alone.
-/

namespace strings
open ground places blockcount

/-- The pair's lowering iterate on a homogeneous vector: the
letter-pair action `E_ji` run a stated number of times. -/
def iterAct (i j : Nat) : Nat → HVec → HVec
  | 0, v => v
  | b + 1, v => iterAct i j b (act j i v)

/-- The pair's height key at a content: the first letter's count
against the second's, shifted by the degree so the read is a
natural at every content, descending in the pair's dominance
direction. -/
def hKey (i j : Nat) (mu : List Nat) : Nat :=
  ground.getAt 0 mu i + (sumNat mu - ground.getAt 0 mu j)

/-- The pair's height at a content, the string length's read:
the first letter's count against the second's at the truncated
gap. -/
def hAt (i j : Nat) (mu : List Nat) : Nat :=
  ground.getAt 0 mu i - ground.getAt 0 mu j

/-- The pool's distinct contents sorted by descending height key. -/
def contentsByKey (i j : Nat) (pool : List HVec) : List (List Nat) :=
  (pool.foldl
    (fun acc v =>
      if 0 < ground.countOf v.content acc then acc
      else v.content :: acc) []).foldl
    (fun acc mu => ground.insertKeyDesc (hKey i j) mu acc) []

set_option genInjectivity false in
/-- A string: its top with the height, the members the lowering
iterates through the depth run. -/
structure PairString where
  top : HVec
  ht : Nat

/-- Decidable equality on the strings, the top's and the height's
own (hand-written: the generated `injEq` route is disabled with
the injectivity lemmas). -/
def PairString.decEq : (a b : PairString) → Decidable (a = b)
  | ⟨t1, h1⟩, ⟨t2, h2⟩ =>
    if ht : t1 = t2 then
      if hh : h1 = h2 then isTrue (by rw [ht, hh])
      else isFalse (fun he => hh (congrArg PairString.ht he))
    else isFalse (fun he => ht (congrArg PairString.top he))

instance : DecidableEq PairString := PairString.decEq

/-- The string's member at a depth. -/
def memberAt (i j : Nat) (s : PairString) (b : Nat) : HVec :=
  iterAct i j b s.top

/-- The collected members at a content: one per string holding the
content among its depths. -/
def membersAt (i j : Nat) (strs : List PairString)
    (nu : List Nat) : elim.Mat :=
  strs.flatMap (fun s =>
    (List.range (s.ht + 1)).flatMap (fun b =>
      let w := memberAt i j s b
      if w.content = nu then [w.coords] else []))

/-- One content's collection step: group members refusing the
residual against the collected members name new tops, the
residual vectors themselves, until every member passes. -/
def collectAt (i j : Nat) (pool : List HVec) (nu : List Nat) :
    Nat → List PairString → List PairString
  | 0, strs => strs
  | fuel + 1, strs =>
    let grp := groupAt pool nu
    let coll := membersAt i j strs nu
    match grp.find? (fun g =>
      ¬ poly.unitTail (elim.residV g.length coll g)) with
    | none => strs
    | some g =>
      let w := elim.residV g.length coll g
      collectAt i j pool nu fuel
        (strs ++ [⟨⟨nu, w⟩, hAt i j nu⟩])

/-- The pair's exhaustion: the collector at one member joined per
refusal over the pool's contents at descending height key. -/
def walk (i j : Nat) (pool : List HVec) : List PairString :=
  (contentsByKey i j pool).foldl
    (fun strs nu =>
      collectAt i j pool nu (groupAt pool nu).length strs)
    []

/-- The string count at a content over the exhaustion, the
occupancy's string read. -/
def stringCount (i j : Nat) (strs : List PairString)
    (nu : List Nat) : Nat :=
  (membersAt i j strs nu).length

/-! The string kit: the iterate's content reads, the sl2
coefficient identity at a top — `E F^{b+1} = (b+1)(h-b) F^b`, the
crossed-scalar exchange folded down the depth — its zero at the
height reading the termination through the pairing's adjoint, and
the self-pairing's telescoped product, the off-unit persistence. -/

/-- The iterate's step read at the outer end: the depth run is the
lowering applied last, the fold's own associativity. -/
private theorem iterAct_succ' (i j : Nat) : ∀ (b : Nat) (v : HVec),
    iterAct i j (b + 1) v = act j i (iterAct i j b v)
  | 0, _ => rfl
  | b + 1, v => by
    show iterAct i j (b + 1) (act j i v)
      = act j i (iterAct i j (b + 1) v)
    rw [iterAct_succ' i j b (act j i v)]
    rfl

/-- The iterate's content reads by the depth descent, the
occupancy at the first letter read off the height at every depth
the run reaches. -/
private theorem iterAct_reads (i j : Nat) (hij : ¬ i = j)
    (v : HVec) (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length) :
    ∀ b : Nat, b ≤ h →
      (iterAct i j b v).content.length = v.content.length
      ∧ ground.getAt 0 (iterAct i j b v).content i + b
          = ground.getAt 0 v.content i
      ∧ ground.getAt 0 (iterAct i j b v).content j
          = ground.getAt 0 v.content j + b
      ∧ (∀ x, ¬ x = i → ¬ x = j →
          ground.getAt 0 (iterAct i j b v).content x
            = ground.getAt 0 v.content x)
  | 0, _ => ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | b + 1, hb => by
    have ih := iterAct_reads i j hij v h hgap hi hj b
      (Nat.le_of_succ_le hb)
    have hocc : 0 < ground.getAt 0 (iterAct i j b v).content i := by
      match Nat.eq_zero_or_pos
          (ground.getAt 0 (iterAct i j b v).content i) with
      | .inr hp => exact hp
      | .inl h0 =>
        have hbi : b = ground.getAt 0 v.content j + h := by
          rw [← hgap, ← ih.2.1, h0, Nat.zero_add]
        exact absurd (Nat.le_trans hb
          (Nat.le_trans (Nat.le_add_left h _)
            (Nat.le_of_eq hbi.symm)))
          (Nat.not_succ_le_self b)
    have hjc : j < (dipAt i (iterAct i j b v).content).length := by
      rw [length_dipAt, ih.1]
      exact hj
    have hstep := iterAct_succ' i j b v
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstep]
      show (moveAt j i (iterAct i j b v).content).length
        = v.content.length
      rw [length_moveAt, ih.1]
    · rw [hstep]
      show ground.getAt 0
          (bumpAt j (dipAt i (iterAct i j b v).content)) i + (b + 1)
        = ground.getAt 0 v.content i
      rw [getAt_bumpAt_ne j (dipAt i (iterAct i j b v).content) i
          hij,
        show b + 1 = 1 + b from Nat.add_comm b 1, ← Nat.add_assoc,
        getAt_dipAt_self i (iterAct i j b v).content hocc]
      exact ih.2.1
    · rw [hstep]
      show ground.getAt 0
          (bumpAt j (dipAt i (iterAct i j b v).content)) j
        = ground.getAt 0 v.content j + (b + 1)
      rw [getAt_bumpAt_self j _ hjc,
        getAt_dipAt_ne i (iterAct i j b v).content j
          (fun he => hij he.symm),
        ih.2.2.1, Nat.add_assoc]
    · intro x hxi hxj
      rw [hstep]
      show ground.getAt 0
          (bumpAt j (dipAt i (iterAct i j b v).content)) x
        = ground.getAt 0 v.content x
      rw [getAt_bumpAt_ne j _ x hxj,
        getAt_dipAt_ne i (iterAct i j b v).content x hxi]
      exact ih.2.2.2 x hxi hxj

/-- The iterate's content reads: the first letter's count descends
one per step, the second's ascends, every further letter kept, the
length fixed. -/
theorem iterAct_content (i j : Nat) (hij : ¬ i = j) (b : Nat)
    (v : HVec) (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hb : b ≤ h) (hi : i < v.content.length)
    (hj : j < v.content.length) :
    (iterAct i j b v).content.length = v.content.length
      ∧ ground.getAt 0 (iterAct i j b v).content i + b
          = ground.getAt 0 v.content i
      ∧ ground.getAt 0 (iterAct i j b v).content j
          = ground.getAt 0 v.content j + b
      ∧ (∀ x, ¬ x = i → ¬ x = j →
          ground.getAt 0 (iterAct i j b v).content x
            = ground.getAt 0 v.content x) :=
  iterAct_reads i j hij v h hgap hi hj b hb

/-- The iterate keeps the width read. -/
theorem iterAct_sized (i j : Nat) (v : HVec)
    (hsz : sized v) (b : Nat) : sized (iterAct i j b v) := by
  match b with
  | 0 => exact hsz
  | c + 1 =>
    rw [iterAct_succ' i j c v]
    exact act_sized j i (iterAct i j c v)

/-- The coefficient product at a height, the self-pairing's
telescope: the depth run's factors `(b+1)(h-b)` collected. -/
def coeffProd (h : Nat) : Nat → Nat
  | 0 => 1
  | b + 1 => coeffProd h b * ((b + 1) * (h - b))

/-! The action's null and round-trip widths at the letter pair —
the carrier and coordinate reads beneath them are their owners'
public kit (`def:elim`'s one-value tier, `con:units`' letter
reads). -/

/-! The counting kit the coefficient identity rides: the
successors' subtraction, the sum's own withdrawal, the sum's right
cancellation, and the crossed collection at the depth's step. -/

private theorem crossSum (X Y m g : Nat) :
    X + Y + (m + g) = Y + g + (m + X) := by
  rw [Nat.add_assoc Y g (m + X), Nat.add_comm g (m + X),
    ← Nat.add_assoc Y (m + X) g, ← Nat.add_assoc (X + Y) m g,
    Nat.add_comm X Y, Nat.add_assoc Y X m, Nat.add_comm X m]

private theorem coeffCross (b g m : Nat) :
    (b + 1) * ((b + 1 + g) - b) + (m + g)
      = (b + 1 + 1) * ((b + 1 + g) - (b + 1)) + (m + (b + 1)) := by
  rw [Nat.add_assoc b 1 g, addSubSelfL b (1 + g),
    ← Nat.add_assoc b 1 g, addSubSelfL (b + 1) g,
    Nat.left_distrib (b + 1) 1 g, Nat.mul_one,
    ground.mulAddR (b + 1) 1 g, Nat.one_mul g]
  exact crossSum (b + 1) ((b + 1) * g) m g

private theorem raise_exch_top (i j : Nat) (hij : ¬ i = j)
    (y : HVec) (hocc : 0 < ground.getAt 0 y.content i)
    (hz : ground.getAt 0 y.content j = 0)
    (hiy : i < y.content.length) (hjy : j < y.content.length)
    (hszy : sized y) :
    poly.oneValue (act i j (act j i y)).coords
      (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
        y.coords) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hmuA : moveAt i j (moveAt j i y.content) = y.content :=
    moveAt_round_at i j y.content hocc
  have hiA : i < (moveAt j i y.content).length := by
    rw [length_moveAt]
    exact hiy
  have hUp := blockcount.out_gen (moveAt j i y.content) i j hiA hij
  rw [hmuA] at hUp
  have hUp' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt y.content) →
      0 < ground.countOf m (units.unitAct i j s) →
      m.length = sumNat ([] : List Nat)
        ∧ content ([] : List Nat).length m = ([] : List Nat) := by
    intro s m hs hm
    rw [units.unitAct_nil_of_zero i j s
      (letter_zero y.content j hz s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  have hDn' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt ([] : List Nat)) →
      0 < ground.countOf m (units.unitAct j i s) →
      m.length = sumNat y.content
        ∧ content y.content.length m = y.content := by
    intro s m hs hm
    rw [units.unitAct_nil_of_zero j i s
      (letter_zero ([] : List Nat) i rfl s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  have hkey := units.matVec_gpair_read y.content
    (moveAt j i y.content) ([] : List Nat) i j
    (blockcount.out_gen y.content j i hjy hji) hUp
    hUp' hDn' y.coords hszy
  have hLlen : (act i j (act j i y)).coords.length
      = (places.monomialsAt y.content).length :=
    tops.len_act2 i j y hocc
  have hSlen : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 y.content j)) y.coords).length
      = (places.monomialsAt y.content).length := by
    rw [elim.length_vecScale]
    exact hszy
  have hRlen : (elim.matVec (units.matUnitAt y.content
      ([] : List Nat) j i)
      (elim.matVec (units.matUnitAt ([] : List Nat) y.content i j)
        y.coords)).length
      = (places.monomialsAt y.content).length := by
    rw [units.matVec_matUnitAt_length]
  have hClen : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 y.content i)) y.coords).length
      = (places.monomialsAt y.content).length := by
    rw [elim.length_vecScale]
    exact hszy
  have hnullS : poly.unitTail (elim.vecScale
      (BPair.ofNat (ground.getAt 0 y.content j)) y.coords) := by
    refine elim.unitTail_vecScale_unit ?_ _
    rw [hz]
    exact BPair.oneValue_refl BPair.unit
  have hnullR : poly.unitTail (elim.matVec
      (units.matUnitAt y.content ([] : List Nat) j i)
      (elim.matVec (units.matUnitAt ([] : List Nat) y.content i j)
        y.coords)) :=
    units.matVec_null_unocc y.content ([] : List Nat) j i rfl _
  refine poly.oneValue_trans
    (poly.oneValue_symm (elim.vecAdd_null_right _ _
      (by rw [hLlen, hSlen]) hnullS)) ?_
  refine poly.oneValue_trans ?_
    (elim.vecAdd_null_left _ _ (by rw [hRlen, hClen]) hnullR)
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
          ([] : List Nat) j i)
        (elim.matVec (units.matUnitAt ([] : List Nat)
          y.content i j) y.coords))
      (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
        y.coords))
  rw [hmuA]
  exact hkey

/-- The identity's seed at the top: the raising through one
lowering reads the height's multiple, the top's own raising
dropping at the sum's unit. -/
private theorem raise_base (i j : Nat) (hij : ¬ i = j) (v : HVec)
    (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords) :
    poly.oneValue (act i j (act j i v)).coords
      (elim.vecScale (BPair.ofNat h) v.coords) := by
  by_cases hocc : 0 < ground.getAt 0 v.content i
  · have hLlen : (act i j (act j i v)).coords.length
        = (places.monomialsAt v.content).length :=
      tops.len_act2 i j v hocc
    have hkey : poly.oneValue
        (elim.vecAdd (act i j (act j i v)).coords
          (elim.vecScale
            (BPair.ofNat (ground.getAt 0 v.content j)) v.coords))
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content i)) v.coords) := by
      by_cases hcj : 0 < ground.getAt 0 v.content j
      · refine poly.oneValue_trans
          (tops.raise_exch i j hij v hocc hcj hi hj hsz)
          (elim.vecAdd_null_left _ _ ?_ (elim.matVec_null _ _ htop))
        rw [units.matVec_matUnitAt_length,
          elim.length_vecScale]
        exact hsz.symm
      · have hz : ground.getAt 0 v.content j = 0 :=
          match Nat.eq_zero_or_pos (ground.getAt 0 v.content j) with
          | .inl h0 => h0
          | .inr hp => absurd hp hcj
        refine poly.oneValue_trans (elim.vecAdd_null_right _ _ ?_ ?_)
          (raise_exch_top i j hij v hocc hz hi hj hsz)
        · rw [hLlen, elim.length_vecScale]
          exact hsz.symm
        · refine elim.unitTail_vecScale_unit ?_ _
          rw [hz]
          exact BPair.oneValue_refl BPair.unit
    rw [hgap] at hkey
    have hsplit : poly.oneValue
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content j + h)) v.coords)
        (elim.vecAdd (elim.vecScale (BPair.ofNat h) v.coords)
          (elim.vecScale
            (BPair.ofNat (ground.getAt 0 v.content j))
            v.coords)) := by
      refine poly.oneValue_trans (elim.vecScale_congr
        (BPair.oneValue_trans
          (BPair.ofNat_add (ground.getAt 0 v.content j) h)
          (BPair.oneValue_of_eq (BPair.add_comm _ _))) v.coords) ?_
      rw [elim.vecScale_add]
      exact poly.oneValue_refl _
    refine elim.vecAdd_cancel_right (act i j (act j i v)).coords
      (elim.vecScale (BPair.ofNat h) v.coords)
      (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content j))
        v.coords) ?_ ?_ (poly.oneValue_trans hkey hsplit)
    · rw [hLlen, elim.length_vecScale]
      exact hsz.symm
    · rw [hLlen, elim.length_vecScale]
      exact hsz.symm
  · have hz : ground.getAt 0 v.content i = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 v.content i) with
      | .inl h0 => h0
      | .inr hp => absurd hp hocc
    have hh : h = 0 := by
      refine (ground.addZeroN
        (a := ground.getAt 0 v.content j) ?_).2
      rw [← hgap, hz]
    refine poly.unitTail_oneValue
      (elim.matVec_null _ _ (tops.act_null j i v hz)) ?_
    refine elim.unitTail_vecScale_unit ?_ _
    rw [hh]
    exact BPair.oneValue_refl BPair.unit

/-- The identity down the depth run: the exchange at the depth's
own content with the shallower read supplied by the descent. -/
private theorem iterAct_raiseGo (i j : Nat) (hij : ¬ i = j)
    (v : HVec) (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords) :
    ∀ b : Nat, b ≤ h →
      poly.oneValue (act i j (iterAct i j (b + 1) v)).coords
        (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
          (iterAct i j b v).coords)
  | 0, _ => by
    show poly.oneValue (act i j (act j i v)).coords
      (elim.vecScale (BPair.ofNat (1 * h)) v.coords)
    rw [Nat.one_mul h]
    exact raise_base i j hij v h hgap hi hj hsz htop
  | b + 1, hb => by
    have hble : b ≤ h := Nat.le_of_succ_le hb
    have cu := iterAct_reads i j hij v h hgap hi hj b hble
    have cy := iterAct_reads i j hij v h hgap hi hj (b + 1) hb
    have hszu : sized (iterAct i j b v) :=
      iterAct_sized i j v hsz b
    have hszy : sized (iterAct i j (b + 1) v) :=
      iterAct_sized i j v hsz (b + 1)
    have hstep1 : iterAct i j (b + 1) v
        = act j i (iterAct i j b v) := iterAct_succ' i j b v
    have hstep2 : iterAct i j (b + 1 + 1) v
        = act j i (iterAct i j (b + 1) v) :=
      iterAct_succ' i j (b + 1) v
    by_cases hocc :
        0 < ground.getAt 0 (iterAct i j (b + 1) v).content i
    · have hiy : i < (iterAct i j (b + 1) v).content.length := by
        rw [cy.1]
        exact hi
      have hjy : j < (iterAct i j (b + 1) v).content.length := by
        rw [cy.1]
        exact hj
      have hcj : 0 < ground.getAt 0
          (iterAct i j (b + 1) v).content j := by
        rw [cy.2.2.1]
        exact Nat.succ_pos _
      have hoccu : 0 < ground.getAt 0 (iterAct i j b v).content i := by
        match Nat.eq_zero_or_pos
            (ground.getAt 0 (iterAct i j b v).content i) with
        | .inr hp => exact hp
        | .inl h0 =>
          have hbi : b = ground.getAt 0 v.content j + h := by
            rw [← hgap, ← cu.2.1, h0, Nat.zero_add]
          exact absurd (Nat.le_trans hb
            (Nat.le_trans (Nat.le_add_left h _)
              (Nat.le_of_eq hbi.symm)))
            (Nat.not_succ_le_self b)
      have hmu : moveAt i j (iterAct i j (b + 1) v).content
          = (iterAct i j b v).content := by
        rw [hstep1]
        exact moveAt_round_at i j (iterAct i j b v).content hoccu
      have hIH := iterAct_raiseGo i j hij v h hgap hi hj hsz htop b
        hble
      have hMy : elim.matVec (units.matUnitAt
          (iterAct i j (b + 1) v).content
          (iterAct i j b v).content j i) (iterAct i j b v).coords
          = (iterAct i j (b + 1) v).coords := by
        rw [hstep1]
        rfl
      have hFy : poly.oneValue
          (elim.matVec (units.matUnitAt
            (iterAct i j (b + 1) v).content
            (moveAt i j (iterAct i j (b + 1) v).content) j i)
            (act i j (iterAct i j (b + 1) v)).coords)
          (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
            (iterAct i j (b + 1) v).coords) := by
        rw [hmu]
        refine poly.oneValue_trans (elim.matVec_congr _ _ _ hIH)
          (poly.oneValue_trans
            (elim.matVec_vecScale _
              (places.monomialsAt (iterAct i j b v).content).length
              (units.rowsLen_matUnitAt _ _ j i) _ _ hszu) ?_)
        rw [hMy]
        exact poly.oneValue_refl _
      have hlenFy : (elim.matVec (units.matUnitAt
          (iterAct i j (b + 1) v).content
          (moveAt i j (iterAct i j (b + 1) v).content) j i)
          (act i j (iterAct i j (b + 1) v)).coords).length
          = (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
            (iterAct i j (b + 1) v).coords).length := by
        rw [units.matVec_matUnitAt_length,
          elim.length_vecScale, hszy]
      have hstepA := poly.oneValue_trans
        (tops.raise_exch i j hij (iterAct i j (b + 1) v)
          hocc hcj hiy hjy hszy)
        (elim.vecAdd_congr _ _ _ hlenFy hFy)
      have hnat : (b + 1) * (h - b)
            + ground.getAt 0 (iterAct i j (b + 1) v).content i
          = (b + 1 + 1) * (h - (b + 1))
            + ground.getAt 0 (iterAct i j (b + 1) v).content j := by
        match Nat.le.dest hb with
        | ⟨g, hg⟩ =>
          have hci : ground.getAt 0 (iterAct i j (b + 1) v).content i
              = ground.getAt 0 v.content j + g := by
            refine ground.addCancelR (b + 1) ?_
            rw [cy.2.1, hgap, ← hg,
              Nat.add_assoc (ground.getAt 0 v.content j) g (b + 1),
              Nat.add_comm (b + 1) g]
          rw [hci, cy.2.2.1, ← hg]
          exact coeffCross b g (ground.getAt 0 v.content j)
      have hsplit2 : poly.oneValue
          (elim.vecAdd
            (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
              (iterAct i j (b + 1) v).coords)
            (elim.vecScale (BPair.ofNat (ground.getAt 0
                (iterAct i j (b + 1) v).content i))
              (iterAct i j (b + 1) v).coords))
          (elim.vecAdd
            (elim.vecScale
              (BPair.ofNat ((b + 1 + 1) * (h - (b + 1))))
              (iterAct i j (b + 1) v).coords)
            (elim.vecScale (BPair.ofNat (ground.getAt 0
                (iterAct i j (b + 1) v).content j))
              (iterAct i j (b + 1) v).coords)) := by
        rw [← elim.vecScale_add (BPair.ofNat ((b + 1) * (h - b)))
            (BPair.ofNat (ground.getAt 0
              (iterAct i j (b + 1) v).content i))
            (iterAct i j (b + 1) v).coords,
          ← elim.vecScale_add
            (BPair.ofNat ((b + 1 + 1) * (h - (b + 1))))
            (BPair.ofNat (ground.getAt 0
              (iterAct i j (b + 1) v).content j))
            (iterAct i j (b + 1) v).coords]
        refine poly.oneValue_trans
          (elim.vecScale_congr
            (BPair.oneValue_symm (BPair.ofNat_add _ _)) _)
          (poly.oneValue_trans ?_
            (elim.vecScale_congr (BPair.ofNat_add _ _) _))
        rw [hnat]
        exact poly.oneValue_refl _
      rw [hstep2]
      refine elim.vecAdd_cancel_right _ _ _ ?_ ?_
        (poly.oneValue_trans hstepA hsplit2)
      · rw [tops.len_act2 i j (iterAct i j (b + 1) v) hocc,
          elim.length_vecScale, hszy]
      · rw [tops.len_act2 i j (iterAct i j (b + 1) v) hocc,
          elim.length_vecScale, hszy]
    · have hz : ground.getAt 0 (iterAct i j (b + 1) v).content i
          = 0 :=
        match Nat.eq_zero_or_pos
            (ground.getAt 0 (iterAct i j (b + 1) v).content i) with
        | .inl h0 => h0
        | .inr hp => absurd hp hocc
      have hhb : h = b + 1 := by
        have h1 : b + 1 = ground.getAt 0 v.content j + h := by
          rw [← hgap, ← cy.2.1, hz, Nat.zero_add]
        exact Nat.le_antisymm
          (Nat.le_trans (Nat.le_add_left h _)
            (Nat.le_of_eq h1.symm)) hb
      refine poly.unitTail_oneValue ?_ ?_
      · rw [hstep2]
        exact elim.matVec_null _ _
          (tops.act_null j i (iterAct i j (b + 1) v) hz)
      · refine elim.unitTail_vecScale_unit ?_ _
        rw [hhb, Nat.sub_self, Nat.mul_zero]
        exact BPair.oneValue_refl BPair.unit

/-- The sl2 coefficient identity at a top: the raising through the
depth run reads the scaled shallower member, `E F^{b+1} w` the
`(b+1)(h-b)`-multiple of `F^b w`, the crossed-scalar exchange
folded down the depth with the top's raising the unit — the
coefficient reading the sum's unit at the height's own depth. -/
theorem iterAct_raise (i j : Nat) (hij : ¬ i = j) (v : HVec)
    (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords)
    (b : Nat) (hb : b ≤ h) :
    poly.oneValue (act i j (iterAct i j (b + 1) v)).coords
      (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
        (iterAct i j b v).coords) :=
  iterAct_raiseGo i j hij v h hgap hi hj hsz htop b hb

/-- The string terminates at the height: the further lowering
reads the sum's unit, the self-pairing collapsing through the
adjoint at the coefficient's zero. -/
theorem iterAct_term (i j : Nat) (hij : ¬ i = j) (v : HVec)
    (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords) :
    poly.unitTail (iterAct i j (h + 1) v).coords := by
  have hji : ¬ j = i := fun he => hij he.symm
  have cu := iterAct_reads i j hij v h hgap hi hj h (Nat.le_refl h)
  have hszu : sized (iterAct i j h v) :=
    iterAct_sized i j v hsz h
  have hstep : iterAct i j (h + 1) v = act j i (iterAct i j h v) :=
    iterAct_succ' i j h v
  by_cases hocc : 0 < ground.getAt 0 (iterAct i j h v).content i
  · have hiu : i < (iterAct i j h v).content.length := by
      rw [cu.1]
      exact hi
    have hju : j < (iterAct i j h v).content.length := by
      rw [cu.1]
      exact hj
    have hmu : moveAt i j (moveAt j i (iterAct i j h v).content)
        = (iterAct i j h v).content :=
      moveAt_round_at i j (iterAct i j h v).content hocc
    have hiA : i < (moveAt j i (iterAct i j h v).content).length := by
      rw [length_moveAt]
      exact hiu
    have hout' := blockcount.out_gen
      (moveAt j i (iterAct i j h v).content) i j hiA hij
    rw [hmu] at hout'
    have htrans := units.matUnit_transpose_read
      (moveAt j i (iterAct i j h v).content)
      (iterAct i j h v).content j i
      (blockcount.out_gen (iterAct i j h v).content j i hju hji)
      hout'
    have hE0 : poly.unitTail
        (act i j (act j i (iterAct i j h v))).coords := by
      have hr := iterAct_raise i j hij v h hgap hi hj hsz htop h
        (Nat.le_refl h)
      rw [hstep] at hr
      refine poly.oneValue_unitTail hr ?_
      refine elim.unitTail_vecScale_unit ?_ _
      rw [Nat.sub_self, Nat.mul_zero]
      exact BPair.oneValue_refl BPair.unit
    have hEnull : poly.unitTail (elim.matVec
        (units.matUnitAt (iterAct i j h v).content
          (moveAt j i (iterAct i j h v).content) i j)
        (act j i (iterAct i j h v)).coords) := by
      have hE0' : poly.unitTail (elim.matVec
          (units.matUnitAt
            (moveAt i j (moveAt j i (iterAct i j h v).content))
            (moveAt j i (iterAct i j h v).content) i j)
          (act j i (iterAct i j h v)).coords) := hE0
      rw [hmu] at hE0'
      exact hE0'
    rw [hstep]
    refine elim.dotP_self_null _ ?_
    refine BPair.oneValue_trans
      (elim.dotP_matVec_transpose
        (places.monomialsAt (iterAct i j h v).content).length
        (units.matUnitAt (moveAt j i (iterAct i j h v).content)
          (iterAct i j h v).content j i)
        (iterAct i j h v).coords
        (act j i (iterAct i j h v)).coords
        (units.rowsLen_matUnitAt _ _ j i) hszu
        (elim.matVec_length
          (units.matUnitAt (moveAt j i (iterAct i j h v).content)
            (iterAct i j h v).content j i)
          (iterAct i j h v).coords)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right (iterAct i j h v).coords _ _
        (elim.matVec_matOne _ _ _ htrans)) ?_
    exact elim.dotP_null_tail_right _ _ hEnull
  · have hz : ground.getAt 0 (iterAct i j h v).content i = 0 :=
      match Nat.eq_zero_or_pos
          (ground.getAt 0 (iterAct i j h v).content i) with
      | .inl h0 => h0
      | .inr hp => absurd hp hocc
    rw [hstep]
    exact tops.act_null j i (iterAct i j h v) hz

/-- The telescope down the depth run: each step's self-pairing
against the shallower one's through the adjoint, the coefficient
the raising's own. -/
private theorem iterAct_selfpairGo (i j : Nat) (hij : ¬ i = j)
    (v : HVec) (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords) :
    ∀ b : Nat, b ≤ h →
      (elim.dotP (iterAct i j b v).coords
          (iterAct i j b v).coords).oneValue
        (BPair.ofNat (coeffProd h b)
          * elim.dotP v.coords v.coords)
  | 0, _ => by
    show (elim.dotP v.coords v.coords).oneValue
      (BPair.ofNat 1 * elim.dotP v.coords v.coords)
    exact BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_comm (BPair.ofNat 1)
            (elim.dotP v.coords v.coords)))
        (BPair.mul_ofNat_one (elim.dotP v.coords v.coords)))
  | b + 1, hb => by
    have hji : ¬ j = i := fun he => hij he.symm
    have hble : b ≤ h := Nat.le_of_succ_le hb
    have cu := iterAct_reads i j hij v h hgap hi hj b hble
    have hszu : sized (iterAct i j b v) :=
      iterAct_sized i j v hsz b
    have hstep : iterAct i j (b + 1) v
        = act j i (iterAct i j b v) := iterAct_succ' i j b v
    have hoccu : 0 < ground.getAt 0 (iterAct i j b v).content i := by
      match Nat.eq_zero_or_pos
          (ground.getAt 0 (iterAct i j b v).content i) with
      | .inr hp => exact hp
      | .inl h0 =>
        have hbi : b = ground.getAt 0 v.content j + h := by
          rw [← hgap, ← cu.2.1, h0, Nat.zero_add]
        exact absurd (Nat.le_trans hb
          (Nat.le_trans (Nat.le_add_left h _)
            (Nat.le_of_eq hbi.symm)))
          (Nat.not_succ_le_self b)
    have hiu : i < (iterAct i j b v).content.length := by
      rw [cu.1]
      exact hi
    have hju : j < (iterAct i j b v).content.length := by
      rw [cu.1]
      exact hj
    have hmu : moveAt i j (moveAt j i (iterAct i j b v).content)
        = (iterAct i j b v).content :=
      moveAt_round_at i j (iterAct i j b v).content hoccu
    have hiA : i < (moveAt j i (iterAct i j b v).content).length := by
      rw [length_moveAt]
      exact hiu
    have hout' := blockcount.out_gen
      (moveAt j i (iterAct i j b v).content) i j hiA hij
    rw [hmu] at hout'
    have htrans := units.matUnit_transpose_read
      (moveAt j i (iterAct i j b v).content)
      (iterAct i j b v).content j i
      (blockcount.out_gen (iterAct i j b v).content j i hju hji)
      hout'
    have hraise : poly.oneValue (elim.matVec
        (units.matUnitAt (iterAct i j b v).content
          (moveAt j i (iterAct i j b v).content) i j)
        (act j i (iterAct i j b v)).coords)
        (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
          (iterAct i j b v).coords) := by
      have hr := iterAct_raise i j hij v h hgap hi hj hsz htop b hble
      rw [hstep] at hr
      have hr' : poly.oneValue (elim.matVec
          (units.matUnitAt
            (moveAt i j (moveAt j i (iterAct i j b v).content))
            (moveAt j i (iterAct i j b v).content) i j)
          (act j i (iterAct i j b v)).coords)
          (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
            (iterAct i j b v).coords) := hr
      rw [hmu] at hr'
      exact hr'
    have hIH := iterAct_selfpairGo i j hij v h hgap hi hj hsz htop b
      hble
    rw [hstep]
    refine BPair.oneValue_trans
      (elim.dotP_matVec_transpose
        (places.monomialsAt (iterAct i j b v).content).length
        (units.matUnitAt (moveAt j i (iterAct i j b v).content)
          (iterAct i j b v).content j i)
        (iterAct i j b v).coords
        (act j i (iterAct i j b v)).coords
        (units.rowsLen_matUnitAt _ _ j i) hszu
        (elim.matVec_length
          (units.matUnitAt (moveAt j i (iterAct i j b v).content)
            (iterAct i j b v).content j i)
          (iterAct i j b v).coords)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right (iterAct i j b v).coords _ _
        (elim.matVec_matOne _ _ _ htrans)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right (iterAct i j b v).coords _ _ hraise) ?_
    refine BPair.oneValue_trans
      (elim.dotP_vecScale_right (iterAct i j b v).coords
        (iterAct i j b v).coords
        (BPair.ofNat ((b + 1) * (h - b)))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hIH) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    exact BPair.mul_congr_left
      (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.ofNat_mul (coeffProd h b) ((b + 1) * (h - b)))
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))))

/-- The self-pairing's telescope: the depth-`b` member's
self-pairing reads the coefficient product against the top's. -/
theorem iterAct_selfpair (i j : Nat) (hij : ¬ i = j) (v : HVec)
    (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords)
    (b : Nat) (hb : b ≤ h) :
    (elim.dotP (iterAct i j b v).coords
        (iterAct i j b v).coords).oneValue
      (BPair.ofNat (coeffProd h b)
        * elim.dotP v.coords v.coords) :=
  iterAct_selfpairGo i j hij v h hgap hi hj hsz htop b hb


/-! The exhaustion's semantics: every collected string is good —
sized, at the stated gap, its top raising-free and off the sum's
unit inside its group's span — the members pairwise perpendicular
and off the unit at every content, and the string count reading
the span occupancy content by content, the exchange read closing
the comparison. -/

/-- A good string at a pool: the top sized at the stated content
length, the height the genuine letter gap, the raising image the
sum's unit, the top off the unit inside its own group's span. -/
def goodString (i j d : Nat) (pool : List HVec)
    (str : PairString) : Prop :=
  sized str.top
    ∧ str.top.content.length = d
    ∧ ground.getAt 0 str.top.content i
        = ground.getAt 0 str.top.content j + str.ht
    ∧ poly.unitTail (act i j str.top).coords
    ∧ ¬ poly.unitTail str.top.coords
    ∧ elim.spanRel (monomialsAt str.top.content).length
        (groupAt pool str.top.content) str.top.coords

instance (i j d : Nat) (pool : List HVec) (str : PairString) :
    Decidable (goodString i j d pool str) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! The height's positivity kit: the product of two positives and
the coefficient product's own descent, the gap at a strict
comparison `ground.subPos`. -/

private theorem coeffProd_posGo (h : Nat) : ∀ b : Nat, b ≤ h →
    0 < coeffProd h b
  | 0, _ => Nat.succ_pos 0
  | b + 1, hb => by
    show 0 < coeffProd h b * ((b + 1) * (h - b))
    exact Nat.mul_pos (coeffProd_posGo h b (Nat.le_of_succ_le hb))
      (Nat.mul_pos (Nat.succ_pos b) (ground.subPos hb))

/-- The coefficient product is positive through the height. -/
theorem coeffProd_pos (h b : Nat) (hb : b ≤ h) : 0 < coeffProd h b :=
  coeffProd_posGo h b hb


/-! The exhaustion's carrier kit: the family predicate over a
mapped range, and the collected members read as the group of the
strings' own member pool — the pool group's cons, join, width,
rows and occupancy reads are `def:blockcount`'s public kit. -/

private theorem memAll_mapRangeL (P : HVec → Prop) (g : Nat → HVec) :
    ∀ n : Nat, (∀ b, b < n → P (g b)) →
      ∀ v ∈ (List.range n).map g, P v
  | 0, _ => memAll_nil
  | n + 1, h => by
    rw [range_succ n, ground.map_append]
    exact memAll_append
      (memAll_mapRangeL P g n
        (fun b hb => h b (Nat.lt_of_lt_of_le hb (Nat.le_succ n))))
      (memAll_cons (h n (Nat.le_refl (n + 1))) memAll_nil)

/-- A refused kernel comparison refuses the equality. -/
private theorem beqFalseNeL {x y : List Nat}
    (hb : (x == y) = false) : ¬ x = y := fun hee => by
  rw [hee, ground.listEqBeq y] at hb
  exact Bool.noConfusion hb

/-- The strings' member pool: every string's depth run listed. -/
private def memPool (i j : Nat) (strs : List PairString) :
    List HVec :=
  strs.flatMap (fun s => (List.range (s.ht + 1)).map (memberAt i j s))

private theorem groupAt_mapL {α : Type} (g : α → HVec)
    (nu : List Nat) :
    ∀ l : List α, groupAt (l.map g) nu
      = l.flatMap (fun b =>
          if (g b).content = nu then [(g b).coords] else [])
  | [] => rfl
  | a :: t => by
    show groupAt (g a :: t.map g) nu
      = (if (g a).content = nu then [(g a).coords] else [])
        ++ t.flatMap (fun b =>
          if (g b).content = nu then [(g b).coords] else [])
    rw [groupAt_cons (g a) (t.map g) nu, groupAt_mapL g nu t]
    cases hb : (g a).content == nu with
    | true =>
      rw [if_pos (ground.listBeqEq hb)]
      rfl
    | false =>
      rw [if_neg (beqFalseNeL hb)]
      rfl

private theorem membersAt_eqL (i j : Nat) (nu : List Nat) :
    ∀ strs : List PairString,
      membersAt i j strs nu = groupAt (memPool i j strs) nu
  | [] => rfl
  | s :: t => by
    show (List.range (s.ht + 1)).flatMap (fun b =>
        if (memberAt i j s b).content = nu then
          [(memberAt i j s b).coords] else [])
        ++ membersAt i j t nu
      = groupAt (((List.range (s.ht + 1)).map (memberAt i j s))
          ++ memPool i j t) nu
    rw [groupAt_append, ← groupAt_mapL (memberAt i j s) nu,
      membersAt_eqL i j nu t]

/-! The guard's own read: the Boolean search's found member with
its position and the exhausted search's refusal at every position,
both by structural induction — the core list kit stays out. -/

private theorem findConsTrueL {α : Type} (p : α → Bool) (x : α)
    (t : List α) (hb : p x = true) : (x :: t).find? p = some x := by
  show (match p x with
    | true => some x
    | false => List.find? p t) = some x
  rw [hb]

private theorem findConsFalseL {α : Type} (p : α → Bool) (x : α)
    (t : List α) (hb : p x = false) :
    (x :: t).find? p = t.find? p := by
  show (match p x with
    | true => some x
    | false => List.find? p t) = List.find? p t
  rw [hb]

private theorem findB_someL {α : Type} (d : α) (p : α → Bool) :
    ∀ (l : List α) (g : α), l.find? p = some g →
      p g = true ∧ ∃ k, k < l.length ∧ ground.getAt d l k = g
  | [], _, h => nomatch h
  | x :: t, g, h => by
    cases hb : p x with
    | true =>
      rw [findConsTrueL p x t hb] at h
      have hx : x = g := Option.some.inj h
      refine ⟨?_, 0, Nat.succ_pos _, hx⟩
      rw [← hx]
      exact hb
    | false =>
      rw [findConsFalseL p x t hb] at h
      match findB_someL d p t g h with
      | ⟨hp, k, hk, hg⟩ =>
        exact ⟨hp, k + 1, Nat.succ_lt_succ hk, hg⟩

private theorem findB_noneL {α : Type} (d : α) (p : α → Bool) :
    ∀ (l : List α), l.find? p = none →
      ∀ k, k < l.length → p (ground.getAt d l k) = false
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | x :: t, h, k, hk => by
    cases hb : p x with
    | true =>
      rw [findConsTrueL p x t hb] at h
      exact nomatch h
    | false =>
      rw [findConsFalseL p x t hb] at h
      match k with
      | 0 => exact hb
      | k' + 1 =>
        exact findB_noneL d p t h k' (Nat.lt_of_succ_lt_succ hk)

private theorem unitTail_of_decFalseL {u : List BPair}
    (h : decide (¬ poly.unitTail u) = false) : poly.unitTail u :=
  match poly.decUnitTail u with
  | isTrue ht => ht
  | isFalse hf => by
    rw [decide_eq_true hf] at h
    exact Bool.noConfusion h


/-! The content order the join walk consumes: the insertion's
count and sortedness reads, the distinct collection's cover, and
the pool's contents sorted by descending height key. -/

private def sortedKeyL (i j : Nat) : List (List Nat) → Prop
  | [] => True
  | mu :: t => (∀ nu, 0 < ground.countOf nu t →
      hKey i j nu ≤ hKey i j mu) ∧ sortedKeyL i j t

private theorem countOf_insertL (i j : Nat) (mu x : List Nat) :
    ∀ l : List (List Nat),
      ground.countOf x (ground.insertKeyDesc (hKey i j) mu l)
        = ground.countOf x (mu :: l)
  | [] => rfl
  | nu :: t => by
    show ground.countOf x
        (if hKey i j nu < hKey i j mu then mu :: nu :: t
         else nu :: ground.insertKeyDesc (hKey i j) mu t)
      = ground.countOf x (mu :: nu :: t)
    by_cases hc : hKey i j nu < hKey i j mu
    · rw [if_pos hc]
    · rw [if_neg hc]
      rw [ground.countOf_cons x nu (ground.insertKeyDesc (hKey i j) mu t),
        ground.countOf_cons x mu (nu :: t),
        ground.countOf_cons x nu t,
        countOf_insertL i j mu x t, ground.countOf_cons x mu t]
      show (if x = nu then 1 else 0)
          + ((if x = mu then 1 else 0) + ground.countOf x t)
        = (if x = mu then 1 else 0)
          + ((if x = nu then 1 else 0) + ground.countOf x t)
      rw [Nat.add_left_comm]

private theorem sorted_insertL (i j : Nat) (mu : List Nat) :
    ∀ l : List (List Nat), sortedKeyL i j l →
      sortedKeyL i j (ground.insertKeyDesc (hKey i j) mu l)
  | [], _ => ⟨fun _ hnu => absurd hnu (Nat.lt_irrefl 0), trivial⟩
  | nu :: t, hs => by
    by_cases hc : hKey i j nu < hKey i j mu
    · show sortedKeyL i j (if hKey i j nu < hKey i j mu then
        mu :: nu :: t else nu :: ground.insertKeyDesc (hKey i j) mu t)
      rw [if_pos hc]
      refine ⟨?_, hs⟩
      intro x hx
      by_cases hxn : x = nu
      · rw [hxn]
        exact Nat.le_of_lt hc
      · exact Nat.le_trans
          (hs.1 x (by rw [← ground.countOf_head_ne hxn t]; exact hx))
          (Nat.le_of_lt hc)
    · show sortedKeyL i j (if hKey i j nu < hKey i j mu then
        mu :: nu :: t else nu :: ground.insertKeyDesc (hKey i j) mu t)
      rw [if_neg hc]
      refine ⟨?_, sorted_insertL i j mu t hs.2⟩
      intro x hx
      rw [countOf_insertL i j mu x t] at hx
      by_cases hxm : x = mu
      · rw [hxm]
        match Nat.lt_or_ge (hKey i j nu) (hKey i j mu) with
        | .inl hlt => exact absurd hlt hc
        | .inr hge => exact hge
      · exact hs.1 x
          (by rw [← ground.countOf_head_ne hxm t]; exact hx)

private theorem sorted_foldL (i j : Nat) :
    ∀ (l acc : List (List Nat)), sortedKeyL i j acc →
      sortedKeyL i j
        (l.foldl (fun a mu => ground.insertKeyDesc (hKey i j) mu a) acc)
  | [], _, hs => hs
  | mu :: t, acc, hs =>
    sorted_foldL i j t (ground.insertKeyDesc (hKey i j) mu acc)
      (sorted_insertL i j mu acc hs)

private theorem countOf_foldL (i j : Nat) (x : List Nat) :
    ∀ l acc : List (List Nat),
      ground.countOf x
          (l.foldl (fun a mu => ground.insertKeyDesc (hKey i j) mu a) acc)
        = ground.countOf x l + ground.countOf x acc
  | [], acc => (Nat.zero_add _).symm
  | mu :: t, acc => by
    show ground.countOf x
        (t.foldl (fun a mu => ground.insertKeyDesc (hKey i j) mu a)
          (ground.insertKeyDesc (hKey i j) mu acc))
      = ground.countOf x (mu :: t) + ground.countOf x acc
    rw [countOf_foldL i j x t (ground.insertKeyDesc (hKey i j) mu acc),
      countOf_insertL i j mu x acc]
    rw [ground.countOf_cons x mu acc, ground.countOf_cons x mu t,
      ← Nat.add_assoc,
      Nat.add_comm (ground.countOf x t) (if x = mu then 1 else 0)]

private theorem dedup_monoL (mu : List Nat) :
    ∀ (l : List HVec) (acc : List (List Nat)),
      0 < ground.countOf mu acc →
      0 < ground.countOf mu (l.foldl
        (fun acc v => if 0 < ground.countOf v.content acc then acc
          else v.content :: acc) acc)
  | [], _, h => h
  | v :: t, acc, h => by
    show 0 < ground.countOf mu (t.foldl
      (fun acc v => if 0 < ground.countOf v.content acc then acc
        else v.content :: acc)
      (if 0 < ground.countOf v.content acc then acc
        else v.content :: acc))
    by_cases hc : 0 < ground.countOf v.content acc
    · rw [if_pos hc]
      exact dedup_monoL mu t acc h
    · rw [if_neg hc]
      refine dedup_monoL mu t (v.content :: acc) ?_
      rw [ground.countOf_cons]
      exact Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)

private theorem dedup_coverL (mu : List Nat) :
    ∀ (l : List HVec) (acc : List (List Nat)), 0 < occ mu l →
      0 < ground.countOf mu (l.foldl
        (fun acc v => if 0 < ground.countOf v.content acc then acc
          else v.content :: acc) acc)
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | v :: t, acc, h => by
    show 0 < ground.countOf mu (t.foldl
      (fun acc v => if 0 < ground.countOf v.content acc then acc
        else v.content :: acc)
      (if 0 < ground.countOf v.content acc then acc
        else v.content :: acc))
    by_cases hvm : v.content = mu
    · refine dedup_monoL mu t _ ?_
      by_cases hc : 0 < ground.countOf v.content acc
      · rw [if_pos hc, ← hvm]
        exact hc
      · rw [if_neg hc]
        rw [ground.countOf_cons, if_pos hvm.symm]
        exact Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_add_right 1 _)
    · refine dedup_coverL mu t _ ?_
      have h' : 0 < (if v.content = mu then 1 else 0) + occ mu t := h
      rw [if_neg hvm, Nat.zero_add] at h'
      exact h'

private theorem contentsByKey_sortedL (i j : Nat)
    (pool : List HVec) : sortedKeyL i j (contentsByKey i j pool) :=
  sorted_foldL i j _ [] trivial

private theorem contentsByKey_coverL (i j : Nat) (pool : List HVec)
    (mu : List Nat) (h : 0 < occupancyAt pool mu) :
    0 < ground.countOf mu (contentsByKey i j pool) := by
  rw [occupancyAt_eq_occ] at h
  show 0 < ground.countOf mu ((pool.foldl
    (fun acc v => if 0 < ground.countOf v.content acc then acc
      else v.content :: acc) []).foldl
    (fun a mu => ground.insertKeyDesc (hKey i j) mu a) [])
  rw [countOf_foldL i j mu _ []]
  exact Nat.lt_of_lt_of_le (dedup_coverL mu pool [] h)
    (Nat.le_add_right _ _)

/-! The height key's reads: the total kept by the letter-pair move
at an occupied second letter, an entry below the total, and the
key's rise of two per raise with its fall per lowering. -/

private theorem hKey_moveAtL (i j : Nat) (hij : ¬ i = j)
    (mu : List Nat) (hi : i < mu.length)
    (hocc : 0 < ground.getAt 0 mu j) :
    hKey i j (moveAt i j mu) = hKey i j mu + 2 := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hS : sumNat (moveAt i j mu) = sumNat mu :=
    blockcount.sumNat_moveAt i j mu hi hocc
  have hI : ground.getAt 0 (moveAt i j mu) i
      = ground.getAt 0 mu i + 1 := by
    show ground.getAt 0 (bumpAt i (dipAt j mu)) i = _
    rw [getAt_bumpAt_self i (dipAt j mu)
        (by rw [length_dipAt]; exact hi),
      getAt_dipAt_ne j mu i hij]
  have hJ : ground.getAt 0 (moveAt i j mu) j + 1
      = ground.getAt 0 mu j := by
    show ground.getAt 0 (bumpAt i (dipAt j mu)) j + 1 = _
    rw [getAt_bumpAt_ne i (dipAt j mu) j hji,
      getAt_dipAt_self j mu hocc]
  match Nat.le.dest (getAt_le_sumNat mu j) with
  | ⟨k, hk⟩ =>
    have h1 : sumNat mu - ground.getAt 0 mu j = k := by
      rw [← hk]
      exact addSubSelfL (ground.getAt 0 mu j) k
    have h2 : sumNat mu - ground.getAt 0 (moveAt i j mu) j
        = k + 1 := by
      rw [← hk, ← hJ, Nat.add_assoc,
        addSubSelfL (ground.getAt 0 (moveAt i j mu) j) (1 + k),
        Nat.add_comm 1 k]
    show ground.getAt 0 (moveAt i j mu) i
        + (sumNat (moveAt i j mu)
          - ground.getAt 0 (moveAt i j mu) j)
      = ground.getAt 0 mu i + (sumNat mu - ground.getAt 0 mu j) + 2
    rw [hS, h1, h2, hI, Nat.add_assoc (ground.getAt 0 mu i) 1 (k + 1),
      Nat.add_comm 1 (k + 1), Nat.add_assoc (ground.getAt 0 mu i) k 2]

private theorem hKey_moveDnL (i j : Nat) (hij : ¬ i = j)
    (mu : List Nat) (hi : i < mu.length) (hj : j < mu.length)
    (hocc : 0 < ground.getAt 0 mu i) :
    hKey i j (moveAt j i mu) + 2 = hKey i j mu := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hround : moveAt i j (moveAt j i mu) = mu :=
    moveAt_round_at i j mu hocc
  have hjA : 0 < ground.getAt 0 (moveAt j i mu) j := by
    show 0 < ground.getAt 0 (bumpAt j (dipAt i mu)) j
    rw [getAt_bumpAt_self j (dipAt i mu)
      (by rw [length_dipAt]; exact hj)]
    exact Nat.succ_pos _
  have hiA : i < (moveAt j i mu).length := by
    rw [length_moveAt]
    exact hi
  have hkey := hKey_moveAtL i j hij (moveAt j i mu) hiA hjA
  rw [hround] at hkey
  exact hkey.symm


/-! The balance carrier's order kit: the upper side transported at
one value and kept by a count's multiple — the residual's own
arithmetic is `def:elim`'s public kit. -/

/-! The member pool's two-way reads: a family predicate at every
depth of every string against the pool's own conjunction, and the
group's positional read against the pool's guarded one. -/

private theorem memAll_mapRange_getL (P : HVec → Prop)
    (g : Nat → HVec) :
    ∀ n : Nat, (∀ v ∈ (List.range n).map g, P v) →
      ∀ b, b < n → P (g b)
  | 0, _, b, hb => absurd hb (Nat.not_lt_zero b)
  | n + 1, h, b, hb => by
    rw [range_succ n, ground.map_append] at h
    have hs := memAll_split (P := P) (a := (List.range n).map g)
      (b := ([n] : List Nat).map g) h
    by_cases hbn : b = n
    · rw [hbn]
      exact memAll_head hs.2
    · refine memAll_mapRange_getL P g n hs.1 b ?_
      match Nat.lt_or_ge b n with
      | .inl hlt => exact hlt
      | .inr hge =>
        exact absurd (Nat.le_antisymm (Nat.le_of_succ_le_succ hb) hge)
          hbn

private theorem memAllS_of_memPoolL (P : HVec → Prop) (i j : Nat) :
    ∀ strs : List PairString, (∀ v ∈ memPool i j strs, P v) →
      ∀ str ∈ strs, ∀ b, b ≤ str.ht → P (memberAt i j str b)
  | [], _ => memAll_nil
  | str :: t, h => by
    have hsp := memAll_split (P := P)
      (a := (List.range (str.ht + 1)).map (memberAt i j str))
      (b := memPool i j t) h
    exact memAll_cons
      (fun b hb => memAll_mapRange_getL P (memberAt i j str)
        (str.ht + 1) hsp.1 b (Nat.succ_le_succ hb))
      (memAllS_of_memPoolL P i j t hsp.2)

private theorem memPool_of_memAllSL (P : HVec → Prop) (i j : Nat) :
    ∀ strs : List PairString,
      (∀ str ∈ strs, ∀ b, b ≤ str.ht → P (memberAt i j str b)) →
      ∀ v ∈ memPool i j strs, P v
  | [], _ => memAll_nil
  | str :: t, h =>
    memAll_append
      (memAll_mapRangeL P (memberAt i j str) (str.ht + 1)
        (fun b hb => memAll_head h b (Nat.le_of_succ_le_succ hb)))
      (memPool_of_memAllSL P i j t (memAll_tail h))

private theorem memAll_of_groupAtL (Q : List BPair → Prop)
    (mu : List Nat) :
    ∀ pool : List HVec,
      (∀ q, q < (groupAt pool mu).length →
        Q (ground.getAt ([] : List BPair) (groupAt pool mu) q)) →
      ∀ v ∈ pool, v.content = mu → Q v.coords
  | [], _ => memAll_nil
  | v :: t, h => by
    have hg := groupAt_cons v t mu
    cases hb : v.content == mu with
    | true =>
      rw [hb] at hg
      refine memAll_cons (fun _ => ?_)
        (memAll_of_groupAtL Q mu t (fun q hq => ?_))
      · have h0 := h 0 (by rw [hg]; exact Nat.succ_pos _)
        rw [hg] at h0
        exact h0
      · have h1 := h (q + 1) (by rw [hg]; exact Nat.succ_lt_succ hq)
        rw [hg] at h1
        exact h1
    | false =>
      rw [hb] at hg
      refine memAll_cons (fun he => absurd he (beqFalseNeL hb))
        (memAll_of_groupAtL Q mu t (fun q hq => ?_))
      have h1 := h q (by rw [hg]; exact hq)
      rw [hg] at h1
      exact h1

private theorem groupAt_of_memAllL (Q : List BPair → Prop)
    (mu : List Nat) (pool : List HVec)
    (h : ∀ v ∈ pool, v.content = mu → Q v.coords)
    (q : Nat) (hq : q < (groupAt pool mu).length) :
    Q (ground.getAt ([] : List BPair) (groupAt pool mu) q) :=
  match groupAt_rows _ pool h mu q hq with
  | ⟨_, hP, hc, hget⟩ => by
    rw [hget]
    exact hP hc

/-! The string's own member reads at a good string: the width, the
content descent with the height key's fall of two per depth, the
group span kept along the run, and the depth member off the sum's
unit at the coefficient product's positivity. -/

private theorem member_contentL (i j d : Nat) (hij : ¬ i = j)
    (hi : i < d) (hj : j < d) (pool : List HVec) (str : PairString)
    (hg : goodString i j d pool str) (b : Nat) (hb : b ≤ str.ht) :
    (memberAt i j str b).content.length = d
      ∧ ground.getAt 0 (memberAt i j str b).content i + b
          = ground.getAt 0 str.top.content i
      ∧ ground.getAt 0 (memberAt i j str b).content j
          = ground.getAt 0 str.top.content j + b := by
  have hiL : i < str.top.content.length := by
    rw [hg.2.1]
    exact hi
  have hjL : j < str.top.content.length := by
    rw [hg.2.1]
    exact hj
  have hc := iterAct_content i j hij b str.top str.ht hg.2.2.1 hb
    hiL hjL
  exact ⟨by rw [show (memberAt i j str b).content
      = (iterAct i j b str.top).content from rfl, hc.1, hg.2.1],
    hc.2.1, hc.2.2.1⟩

private theorem member_occL (i j d : Nat) (hij : ¬ i = j)
    (hi : i < d) (hj : j < d) (pool : List HVec) (str : PairString)
    (hg : goodString i j d pool str) (b : Nat) (hb : b < str.ht) :
    0 < ground.getAt 0 (memberAt i j str b).content i := by
  have hc := member_contentL i j d hij hi hj pool str hg b
    (Nat.le_of_succ_le hb)
  match Nat.eq_zero_or_pos
      (ground.getAt 0 (memberAt i j str b).content i) with
  | .inr hp => exact hp
  | .inl h0 =>
    have hbi : b = ground.getAt 0 str.top.content j + str.ht := by
      rw [← hg.2.2.1, ← hc.2.1, h0, Nat.zero_add]
    exact absurd (Nat.le_trans hb
      (Nat.le_trans (Nat.le_add_left str.ht _)
        (Nat.le_of_eq hbi.symm)))
      (Nat.lt_irrefl b)

private theorem member_keyL (i j d : Nat) (hij : ¬ i = j)
    (hi : i < d) (hj : j < d) (pool : List HVec) (str : PairString)
    (hg : goodString i j d pool str) :
    ∀ b : Nat, b ≤ str.ht →
      hKey i j (memberAt i j str b).content + 2 * b
        = hKey i j str.top.content
  | 0, _ => by
    show hKey i j str.top.content + 2 * 0 = hKey i j str.top.content
    rw [Nat.mul_zero, Nat.add_zero]
  | b + 1, hb => by
    have hble : b < str.ht := hb
    have hc := member_contentL i j d hij hi hj pool str hg b
      (Nat.le_of_succ_le hb)
    have hstep : memberAt i j str (b + 1)
        = act j i (memberAt i j str b) := iterAct_succ' i j b str.top
    have hkey := hKey_moveDnL i j hij (memberAt i j str b).content
      (by rw [hc.1]; exact hi) (by rw [hc.1]; exact hj)
      (member_occL i j d hij hi hj pool str hg b hble)
    have hcc : (memberAt i j str (b + 1)).content
        = moveAt j i (memberAt i j str b).content := by
      rw [hstep]
      rfl
    rw [hcc, Nat.mul_succ,
      ← Nat.add_assoc
        (hKey i j (moveAt j i (memberAt i j str b).content))
        (2 * b) 2,
      Nat.add_right_comm
        (hKey i j (moveAt j i (memberAt i j str b).content)) (2 * b) 2,
      hkey]
    exact member_keyL i j d hij hi hj pool str hg b
      (Nat.le_of_succ_le hb)

private theorem member_key_ltL (i j d : Nat) (hij : ¬ i = j)
    (hi : i < d) (hj : j < d) (pool : List HVec) (str : PairString)
    (hg : goodString i j d pool str) (b : Nat) (hb : b ≤ str.ht)
    (hb0 : 0 < b) :
    hKey i j (memberAt i j str b).content
      < hKey i j str.top.content := by
  have hk := member_keyL i j d hij hi hj pool str hg b hb
  match b, hb0 with
  | b' + 1, _ =>
    rw [← hk, Nat.mul_succ]
    exact Nat.add_le_add_left
      (Nat.succ_le_succ (Nat.zero_le (2 * b' + 1))) _

private theorem member_spanL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (str : PairString)
    (hg : goodString i j s.length (blockSpan s) str) :
    ∀ b : Nat,
      elim.spanRel (monomialsAt (memberAt i j str b).content).length
        (groupAt (blockSpan s) (memberAt i j str b).content)
        (memberAt i j str b).coords
  | 0 => hg.2.2.2.2.2
  | b + 1 => by
    have hstep : memberAt i j str (b + 1)
        = act j i (memberAt i j str b) := iterAct_succ' i j b str.top
    rw [hstep]
    exact lowerspan.act_span_def s j i hj hi (fun he => hij he.symm)
      (memberAt i j str b).content (memberAt i j str b).coords
      (iterAct_sized i j str.top hg.1 b)
      (member_spanL s i j hi hj hij str hg b)

private theorem member_offL (i j d : Nat) (hij : ¬ i = j)
    (hi : i < d) (hj : j < d) (pool : List HVec) (str : PairString)
    (hg : goodString i j d pool str) (b : Nat) (hb : b ≤ str.ht) :
    ¬ poly.unitTail (memberAt i j str b).coords := by
  intro hu
  have hiL : i < str.top.content.length := by
    rw [hg.2.1]
    exact hi
  have hjL : j < str.top.content.length := by
    rw [hg.2.1]
    exact hj
  have hsp := iterAct_selfpair i j hij str.top str.ht hg.2.2.1 hiL
    hjL hg.1 hg.2.2.2.1 b hb
  have hnull : (elim.dotP (memberAt i j str b).coords
      (memberAt i j str b).coords).oneValue BPair.unit :=
    elim.dotP_null_tail_right _ _ hu
  refine hg.2.2.2.2.1 (elim.dotP_self_null str.top.coords ?_)
  refine ground.mul_cancel_unit
    (BPair.ofNat_off_unit (coeffProd str.ht b)
      (coeffProd_pos str.ht b hb)) ?_
  exact BPair.oneValue_trans (BPair.oneValue_symm hsp) hnull

/-! The top's two structural reads: the raising image at the sum's
unit against the processed content's own members, and the genuine
letter gap at the top — the crossed exchange paired with the top
against the pairing's definiteness. -/


/-! The raising image against the collected members: the adjoint
sends a member at the raised content to the string's next member,
a collected one below the height and the sum's unit at it. -/

private theorem memberAt_succL (i j : Nat) (str : PairString)
    (b : Nat) :
    memberAt i j str (b + 1) = act j i (memberAt i j str b) :=
  iterAct_succ' i j b str.top

private theorem member_perp_upL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) (hnu : nu.length = s.length)
    (hcj : 0 < ground.getAt 0 nu j)
    (w : List BPair) (hw : w.length = (monomialsAt nu).length)
    (str : PairString)
    (hg : goodString i j s.length (blockSpan s) str)
    (hcoll : ∀ b, b ≤ str.ht →
      (memberAt i j str b).content = nu →
      (elim.dotP w (memberAt i j str b).coords).oneValue BPair.unit)
    (b : Nat) (hb : b ≤ str.ht)
    (hcon : (memberAt i j str b).content = moveAt i j nu) :
    (elim.dotP (act i j (HVec.mk nu w)).coords
      (memberAt i j str b).coords).oneValue BPair.unit := by
  have hiN : i < nu.length := by
    rw [hnu]
    exact hi
  have hjN : j < nu.length := by
    rw [hnu]
    exact hj
  have hround : moveAt j i (moveAt i j nu) = nu :=
    moveAt_round_at j i nu hcj
  have hszb : sized (memberAt i j str b) :=
    iterAct_sized i j str.top hg.1 b
  have hulen : (memberAt i j str b).coords.length
      = (monomialsAt (moveAt i j nu)).length := by
    have h1 : (memberAt i j str b).coords.length
        = (monomialsAt (memberAt i j str b).content).length := hszb
    rw [h1, hcon]
  have heqF : elim.matVec (units.matUnitAt nu (moveAt i j nu) j i)
      (memberAt i j str b).coords
      = (memberAt i j str (b + 1)).coords := by
    rw [memberAt_succL i j str b]
    show elim.matVec (units.matUnitAt nu (moveAt i j nu) j i)
        (memberAt i j str b).coords
      = elim.matVec (units.matUnitAt
          (moveAt j i (memberAt i j str b).content)
          (memberAt i j str b).content j i)
        (memberAt i j str b).coords
    rw [hcon, hround]
  have hnext : (elim.dotP w
      (memberAt i j str (b + 1)).coords).oneValue BPair.unit := by
    match Nat.lt_or_ge b str.ht with
    | .inl hlt =>
      refine hcoll (b + 1) hlt ?_
      have hcc : (memberAt i j str (b + 1)).content
          = moveAt j i (memberAt i j str b).content := by
        rw [memberAt_succL i j str b]
        rfl
      rw [hcc, hcon, hround]
    | .inr hge =>
      have hbe : b = str.ht := Nat.le_antisymm hb hge
      refine elim.dotP_null_tail_right _ _ ?_
      rw [hbe]
      exact iterAct_term i j hij str.top str.ht hg.2.2.1
        (by rw [hg.2.1]; exact hi) (by rw [hg.2.1]; exact hj)
        hg.1 hg.2.2.2.1
  refine BPair.oneValue_trans
    (blockcount.unit_adjoint i j nu hiN hjN hij hcj w
      (memberAt i j str b).coords hw hulen) ?_
  rw [heqF]
  exact hnext

private theorem members_perp_upL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) (hnu : nu.length = s.length)
    (hcj : 0 < ground.getAt 0 nu j)
    (w : List BPair) (hw : w.length = (monomialsAt nu).length)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (hwperp : ∀ q, q < (membersAt i j strs nu).length →
      (elim.dotP w
          (ground.getAt [] (membersAt i j strs nu) q)).oneValue
        BPair.unit) :
    ∀ q, q < (membersAt i j strs (moveAt i j nu)).length →
      (elim.dotP (act i j (HVec.mk nu w)).coords
          (ground.getAt []
            (membersAt i j strs (moveAt i j nu)) q)).oneValue
        BPair.unit := by
  have hcollAll := memAllS_of_memPoolL
    (fun v => v.content = nu →
      (elim.dotP w v.coords).oneValue BPair.unit) i j strs
    (memAll_of_groupAtL (fun x => (elim.dotP w x).oneValue BPair.unit)
      nu (memPool i j strs)
      (by
        rw [← membersAt_eqL i j nu strs]
        exact hwperp))
  intro q hq
  rw [membersAt_eqL i j (moveAt i j nu) strs] at hq ⊢
  refine groupAt_of_memAllL
    (fun x => (elim.dotP (act i j (HVec.mk nu w)).coords x).oneValue
      BPair.unit)
    (moveAt i j nu) (memPool i j strs) ?_ q hq
  refine memPool_of_memAllSL _ i j strs ?_
  exact fun str hs b hb hcon =>
    member_perp_upL s i j hi hj hij nu hnu hcj w hw str
      (hgood str hs) (hcollAll str hs) b hb hcon

private theorem top_propL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) (w : List BPair)
    (hw : w.length = (monomialsAt nu).length)
    (hwsp : elim.spanRel (monomialsAt nu).length
      (groupAt (blockSpan s) nu) w)
    (M : elim.Mat)
    (hMn : elim.rowsLen (monomialsAt (moveAt i j nu)).length M)
    (hgrp : ∀ k,
      k < (groupAt (blockSpan s) (moveAt i j nu)).length →
      elim.spanRel (monomialsAt (moveAt i j nu)).length M
        (ground.getAt []
          (groupAt (blockSpan s) (moveAt i j nu)) k))
    (hperp : ∀ q, q < M.length →
      (elim.dotP (act i j (HVec.mk nu w)).coords
        (ground.getAt [] M q)).oneValue BPair.unit) :
    poly.unitTail (act i j (HVec.mk nu w)).coords := by
  have hEw : elim.spanRel (monomialsAt (moveAt i j nu)).length
      (groupAt (blockSpan s) (moveAt i j nu))
      (act i j (HVec.mk nu w)).coords :=
    lowerspan.act_span_def s i j hi hj hij nu w hw hwsp
  have hlen : (act i j (HVec.mk nu w)).coords.length
      = (monomialsAt (moveAt i j nu)).length :=
    act_sized i j (HVec.mk nu w)
  refine elim.dotP_self_null _ ?_
  refine elim.perp_span (monomialsAt (moveAt i j nu)).length M _ _
    hMn hlen hperp ?_
  exact elim.spanRel_trans _ _ M _
    (rowsLen_groupAt (moveAt i j nu) (blockSpan s)
      (lowerspan.spanReads s).1) hMn hgrp hEw


/-! The lowering image against the collected members: the adjoint
sends a member at the lowered content to the string's raising
image, the coefficient identity reading it back at the shallower
depth — the top's own raising the sum's unit. -/

private theorem member_perp_dnL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (v : HVec) (hvlen : v.content.length = s.length)
    (hvsz : sized v) (str : PairString)
    (hg : goodString i j s.length (blockSpan s) str)
    (hcoll : ∀ b, b ≤ str.ht →
      (memberAt i j str b).content = v.content →
      (elim.dotP v.coords (memberAt i j str b).coords).oneValue
        BPair.unit)
    (b : Nat) (hb : b ≤ str.ht)
    (hcon : (memberAt i j str b).content = moveAt j i v.content) :
    (elim.dotP (act j i v).coords
      (memberAt i j str b).coords).oneValue BPair.unit := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hiV : i < v.content.length := by
    rw [hvlen]
    exact hi
  have hjV : j < v.content.length := by
    rw [hvlen]
    exact hj
  by_cases hocc : 0 < ground.getAt 0 v.content i
  · have hround : moveAt i j (moveAt j i v.content) = v.content :=
      moveAt_round_at i j v.content hocc
    have hiB : i < (moveAt j i v.content).length := by
      rw [length_moveAt]
      exact hiV
    have hout' := blockcount.out_gen (moveAt j i v.content) i j hiB
      hij
    rw [hround] at hout'
    have htrans := units.matUnit_transpose_read
      (moveAt j i v.content) v.content j i
      (blockcount.out_gen v.content j i hjV hji) hout'
    have hszb : sized (memberAt i j str b) :=
      iterAct_sized i j str.top hg.1 b
    have hulen : (memberAt i j str b).coords.length
        = (units.matUnitAt (moveAt j i v.content) v.content j
            i).length := by
      rw [units.length_matUnitAt]
      have h1 : (memberAt i j str b).coords.length
          = (monomialsAt (memberAt i j str b).content).length := hszb
      rw [h1, hcon]
    have heqE : elim.matVec (units.matUnitAt v.content
        (moveAt j i v.content) i j) (memberAt i j str b).coords
        = (act i j (memberAt i j str b)).coords := by
      show _ = elim.matVec (units.matUnitAt
          (moveAt i j (memberAt i j str b).content)
          (memberAt i j str b).content i j)
        (memberAt i j str b).coords
      rw [hcon, hround]
    have hnext : (elim.dotP v.coords
        (act i j (memberAt i j str b)).coords).oneValue
        BPair.unit := by
      match b with
      | 0 => exact elim.dotP_null_tail_right _ _ hg.2.2.2.1
      | b' + 1 =>
        have hb' : b' ≤ str.ht := Nat.le_of_succ_le hb
        have hraise := iterAct_raise i j hij str.top str.ht hg.2.2.1
          (by rw [hg.2.1]; exact hi) (by rw [hg.2.1]; exact hj)
          hg.1 hg.2.2.2.1 b' hb'
        have hocc' : 0 < ground.getAt 0
            (memberAt i j str b').content i :=
          member_occL i j s.length hij hi hj (blockSpan s) str hg b'
            hb
        have hstep : (memberAt i j str (b' + 1)).content
            = moveAt j i (memberAt i j str b').content := by
          rw [memberAt_succL i j str b']
          rfl
        have hcb' : (memberAt i j str b').content = v.content := by
          have h2 : moveAt j i (memberAt i j str b').content
              = moveAt j i v.content := by
            rw [← hstep]
            exact hcon
          rw [← moveAt_round_at i j (memberAt i j str b').content
              hocc', h2, hround]
        refine BPair.oneValue_trans
          (elim.dotP_oneValue_right v.coords _ _ hraise) ?_
        refine BPair.oneValue_trans
          (elim.dotP_vecScale_right v.coords _ _) ?_
        exact elim.oneValue_mul_unit _ _ (hcoll b' hb' hcb')
    refine BPair.oneValue_trans
      (elim.dotP_matVec_transpose (monomialsAt v.content).length
        (units.matUnitAt (moveAt j i v.content) v.content j i)
        v.coords (memberAt i j str b).coords
        (units.rowsLen_matUnitAt _ _ j i) hvsz hulen) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right v.coords _ _
        (elim.matVec_matOne _ _ _ htrans)) ?_
    rw [heqE]
    exact hnext
  · have hz : ground.getAt 0 v.content i = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 v.content i) with
      | .inl h0 => h0
      | .inr hp => absurd hp hocc
    exact elim.dotP_null_tail_left _ _ (tops.act_null j i v hz)

private theorem members_perp_dnL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (v : HVec) (hvlen : v.content.length = s.length)
    (hvsz : sized v) (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (hperp : ∀ q, q < (membersAt i j strs v.content).length →
      (elim.dotP v.coords
          (ground.getAt [] (membersAt i j strs v.content) q)).oneValue
        BPair.unit) :
    ∀ q, q < (membersAt i j strs (moveAt j i v.content)).length →
      (elim.dotP (act j i v).coords
          (ground.getAt []
            (membersAt i j strs (moveAt j i v.content)) q)).oneValue
        BPair.unit := by
  have hcollAll := memAllS_of_memPoolL
    (fun u => u.content = v.content →
      (elim.dotP v.coords u.coords).oneValue BPair.unit) i j strs
    (memAll_of_groupAtL
      (fun x => (elim.dotP v.coords x).oneValue BPair.unit)
      v.content (memPool i j strs)
      (by
        rw [← membersAt_eqL i j v.content strs]
        exact hperp))
  intro q hq
  rw [membersAt_eqL i j (moveAt j i v.content) strs] at hq ⊢
  refine groupAt_of_memAllL
    (fun x => (elim.dotP (act j i v).coords x).oneValue BPair.unit)
    (moveAt j i v.content) (memPool i j strs) ?_ q hq
  refine memPool_of_memAllSL _ i j strs ?_
  exact fun str hs b hb hcon =>
    member_perp_dnL s i j hi hj hij v hvlen hvsz str
      (hgood str hs) (hcollAll str hs) b hb hcon

/-! The collected members' derived reads at a good string list: the
width, the off-unit entries, the group span, and the independence
the residual's certificates consume. -/

private theorem members_rowsLenL (s : Shape) (i j : Nat)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (mu : List Nat) :
    elim.rowsLen (monomialsAt mu).length
      (membersAt i j strs mu) := by
  rw [membersAt_eqL i j mu strs]
  refine rowsLen_groupAt mu (memPool i j strs) ?_
  exact memPool_of_memAllSL sized i j strs
    (fun str hs b _ => iterAct_sized i j str.top (hgood str hs).1 b)

private theorem members_off_getL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (mu : List Nat) (p : Nat)
    (hp : p < (membersAt i j strs mu).length) :
    ¬ poly.unitTail
      (ground.getAt [] (membersAt i j strs mu) p) := by
  rw [membersAt_eqL i j mu strs] at hp ⊢
  refine groupAt_of_memAllL (fun x => ¬ poly.unitTail x) mu
    (memPool i j strs) ?_ p hp
  refine memPool_of_memAllSL _ i j strs ?_
  exact fun str hs b hb _ =>
    member_offL i j s.length hij hi hj (blockSpan s) str
      (hgood str hs) b hb

private theorem members_span_getL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (mu : List Nat) (p : Nat)
    (hp : p < (membersAt i j strs mu).length) :
    elim.spanRel (monomialsAt mu).length (groupAt (blockSpan s) mu)
      (ground.getAt [] (membersAt i j strs mu) p) := by
  rw [membersAt_eqL i j mu strs] at hp ⊢
  refine groupAt_of_memAllL _ mu (memPool i j strs) ?_ p hp
  refine memPool_of_memAllSL _ i j strs ?_
  refine fun str hs b _ hcon => ?_
  have h := member_spanL s i j hi hj hij str (hgood str hs) b
  rw [hcon] at h
  exact h

private theorem members_indepL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (mu : List Nat) (hperp : elim.perpAll (membersAt i j strs mu)) :
    elim.indepRows (monomialsAt mu).length
      (membersAt i j strs mu) :=
  elim.indep_of_orth (monomialsAt mu).length (membersAt i j strs mu)
    (members_rowsLenL s i j strs hgood mu)
    (fun p q hp hq hpq => hperp p hp q hq hpq)
    (members_off_getL s i j hi hj hij strs hgood mu)

/-! The occupancy's arithmetic over the depth run: the join, the
absent content, the hit, and the cap of one at distinct contents —
the new string contributes one member at its own content and none
at any processed one. -/

private theorem occL_appendL (mu : List Nat) :
    ∀ a b : List HVec, occ mu (a ++ b) = occ mu a + occ mu b
  | [], _ => (Nat.zero_add _).symm
  | v :: t, b => by
    show (if v.content = mu then 1 else 0) + occ mu (t ++ b)
      = (if v.content = mu then 1 else 0) + occ mu t + occ mu b
    rw [occL_appendL mu t b, Nat.add_assoc]

private theorem occL_zeroL (mu : List Nat) :
    ∀ pool : List HVec, (∀ v ∈ pool, ¬ v.content = mu) →
      occ mu pool = 0
  | [], _ => rfl
  | v :: t, h => by
    show (if v.content = mu then 1 else 0) + occ mu t = 0
    rw [if_neg (h v (List.Mem.head t)), Nat.zero_add,
      occL_zeroL mu t (fun x hx => h x (List.Mem.tail v hx))]

private theorem occL_posL (g : Nat → HVec) (mu : List Nat) :
    ∀ (n b : Nat), b < n → (g b).content = mu →
      0 < occ mu ((List.range n).map g)
  | 0, _, hb, _ => absurd hb (Nat.not_lt_zero _)
  | n + 1, b, hb, hc => by
    rw [range_succ n, ground.map_append, occL_appendL]
    by_cases hbn : b = n
    · refine Nat.lt_of_lt_of_le ?_
        (Nat.le_add_left (occ mu (([n] : List Nat).map g)) _)
      show 0 < (if (g n).content = mu then 1 else 0) + occ mu []
      rw [if_pos (by rw [← hbn]; exact hc)]
      exact Nat.succ_pos 0
    · refine Nat.lt_of_lt_of_le
        (occL_posL g mu n b ?_ hc) (Nat.le_add_right _ _)
      match Nat.lt_or_ge b n with
      | .inl hlt => exact hlt
      | .inr hge =>
        exact absurd (Nat.le_antisymm (Nat.le_of_succ_le_succ hb) hge)
          hbn

private theorem occL_le1L (g : Nat → HVec) :
    ∀ n : Nat, (∀ b b', b < n → b' < n →
        (g b).content = (g b').content → b = b') →
      ∀ mu, occ mu ((List.range n).map g) ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | n + 1, hinj, mu => by
    rw [range_succ n, ground.map_append, occL_appendL]
    by_cases hgn : (g n).content = mu
    · have hz : occ mu ((List.range n).map g) = 0 := by
        refine occL_zeroL mu _
          (memAll_mapRangeL _ g n (fun b hb hcb => ?_))
        have hbn : b = n := hinj b n
          (Nat.lt_of_lt_of_le hb (Nat.le_succ n))
          (Nat.le_refl (n + 1)) (by rw [hcb, hgn])
        exact absurd hb (by rw [hbn]; exact Nat.lt_irrefl n)
      rw [hz, Nat.zero_add]
      show (if (g n).content = mu then 1 else 0) + occ mu [] ≤ 1
      rw [if_pos hgn]
      exact Nat.le_refl 1
    · have h1 : occ mu (([n] : List Nat).map g) = 0 := by
        show (if (g n).content = mu then 1 else 0) + occ mu [] = 0
        rw [if_neg hgn, Nat.zero_add]
        rfl
      rw [h1, Nat.add_zero]
      exact occL_le1L g n (fun b b' hb hb' hc => hinj b b'
        (Nat.lt_of_lt_of_le hb (Nat.le_succ n))
        (Nat.lt_of_lt_of_le hb' (Nat.le_succ n)) hc) mu

private theorem member_content_injL (i j d : Nat) (hij : ¬ i = j)
    (hi : i < d) (hj : j < d) (pool : List HVec) (str : PairString)
    (hg : goodString i j d pool str) (b b' : Nat)
    (hb : b ≤ str.ht) (hb' : b' ≤ str.ht)
    (hc : (memberAt i j str b).content
      = (memberAt i j str b').content) : b = b' := by
  have h1 := (member_contentL i j d hij hi hj pool str hg b hb).2.1
  have h2 := (member_contentL i j d hij hi hj pool str hg b' hb').2.1
  rw [hc] at h1
  refine ground.addCancelR (a := b) (b := b')
    (ground.getAt 0 (memberAt i j str b').content i) ?_
  rw [Nat.add_comm b _, Nat.add_comm b' _]
  exact h1.trans h2.symm

private theorem memPool_singleL (i j : Nat) (str : PairString) :
    memPool i j [str]
      = (List.range (str.ht + 1)).map (memberAt i j str) := by
  show (List.range (str.ht + 1)).map (memberAt i j str) ++ [] = _
  rw [ground.append_nil]

/-! The new string's goodness: the residual sized at the content's
enumeration, off the sum's unit by the guard's refusal, inside the
content group's span, its raising image the sum's unit against the
processed content's members, and the truncated gap the genuine
one. -/

private theorem new_goodL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) (hnu : nu.length = s.length)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (hperpM : ∀ mu, elim.perpAll (membersAt i j strs mu))
    (hup : 0 < ground.getAt 0 nu j → ∀ kk,
      kk < (groupAt (blockSpan s) (moveAt i j nu)).length →
      poly.unitTail (elim.residV
        (monomialsAt (moveAt i j nu)).length
        (membersAt i j strs (moveAt i j nu))
        (ground.getAt []
          (groupAt (blockSpan s) (moveAt i j nu)) kk)))
    (g : List BPair) (hg : g.length = (monomialsAt nu).length)
    (hgsp : elim.spanRel (monomialsAt nu).length
      (groupAt (blockSpan s) nu) g)
    (hrefuse : ¬ poly.unitTail (elim.residV (monomialsAt nu).length
      (membersAt i j strs nu) g)) :
    goodString i j s.length (blockSpan s)
      ⟨⟨nu, elim.residV (monomialsAt nu).length
        (membersAt i j strs nu) g⟩, hAt i j nu⟩ := by
  have hcolln : elim.rowsLen (monomialsAt nu).length
      (membersAt i j strs nu) := members_rowsLenL s i j strs hgood nu
  have hwlen : (elim.residV (monomialsAt nu).length
      (membersAt i j strs nu) g).length = (monomialsAt nu).length :=
    elim.length_residV _ _ g hcolln hg
  have hwsp : elim.spanRel (monomialsAt nu).length
      (groupAt (blockSpan s) nu)
      (elim.residV (monomialsAt nu).length
        (membersAt i j strs nu) g) :=
    elim.spanRel_residV (monomialsAt nu).length
      (membersAt i j strs nu) (groupAt (blockSpan s) nu) g hcolln hg
      (rowsLen_groupAt nu (blockSpan s) (lowerspan.spanReads s).1)
      (members_span_getL s i j hi hj hij strs hgood nu) hgsp
  have hwperp : ∀ q, q < (membersAt i j strs nu).length →
      (elim.dotP (elim.residV (monomialsAt nu).length
          (membersAt i j strs nu) g)
        (ground.getAt [] (membersAt i j strs nu) q)).oneValue
        BPair.unit := by
    intro q hq
    rw [elim.dotP_comm]
    exact elim.resid_perp (monomialsAt nu).length
      (membersAt i j strs nu) g hcolln hg q hq
  have hiN : i < nu.length := by
    rw [hnu]
    exact hi
  have hjN : j < nu.length := by
    rw [hnu]
    exact hj
  have htop : poly.unitTail (act i j (HVec.mk nu
      (elim.residV (monomialsAt nu).length
        (membersAt i j strs nu) g))).coords := by
    by_cases hcj : 0 < ground.getAt 0 nu j
    · refine top_propL s i j hi hj hij nu _ hwlen hwsp
        (membersAt i j strs (moveAt i j nu))
        (members_rowsLenL s i j strs hgood (moveAt i j nu)) ?_
        (members_perp_upL s i j hi hj hij nu hnu hcj _ hwlen strs
          hgood hwperp)
      intro kk hkk
      refine elim.resid_sound (monomialsAt (moveAt i j nu)).length
        (membersAt i j strs (moveAt i j nu)) _
        (members_rowsLenL s i j strs hgood (moveAt i j nu))
        (elim.rowsLen_getAt (groupAt (blockSpan s) (moveAt i j nu))
          kk
          (rowsLen_groupAt (moveAt i j nu) (blockSpan s)
            (lowerspan.spanReads s).1) hkk)
        ?_ (hup hcj kk hkk)
      exact elim.indep_det (monomialsAt (moveAt i j nu)).length
        (membersAt i j strs (moveAt i j nu))
        (members_indepL s i j hi hj hij strs hgood (moveAt i j nu)
          (hperpM (moveAt i j nu)))
    · have hz : ground.getAt 0 nu j = 0 :=
        match Nat.eq_zero_or_pos (ground.getAt 0 nu j) with
        | .inl h0 => h0
        | .inr hp => absurd hp hcj
      exact tops.act_null i j (HVec.mk nu _) hz
  have hgapLe := tops.top_gap i j hij (HVec.mk nu
      (elim.residV (monomialsAt nu).length
        (membersAt i j strs nu) g))
    hiN hjN hwlen htop hrefuse
  exact ⟨hwlen, hnu,
    (ground.natAddSubCancel hgapLe).symm, htop, hrefuse, hwsp⟩


/-! The walk's state and its step: the collected strings good, the
members pairwise perpendicular at every content, and every group
row at a processed content passing the residual — kept by one
refusal join, whose new string contributes one member at its own
content and none at any processed one. -/

private def StateL (s : Shape) (i j : Nat) (strs : List PairString)
    (done : List (List Nat)) : Prop :=
  (∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    ∧ (∀ mu, elim.perpAll (membersAt i j strs mu))
    ∧ (∀ mu, 0 < ground.countOf mu done →
        ∀ k, k < (groupAt (blockSpan s) mu).length →
          poly.unitTail (elim.residV (monomialsAt mu).length
            (membersAt i j strs mu)
            (ground.getAt [] (groupAt (blockSpan s) mu) k)))

private theorem membersAt_appendL (i j : Nat)
    (a b : List PairString) (mu : List Nat) :
    membersAt i j (a ++ b) mu
      = membersAt i j a mu ++ membersAt i j b mu :=
  ground.flatMap_append _ a b

private theorem member_lenL (i j : Nat) (str : PairString) :
    ∀ b : Nat, (memberAt i j str b).content.length
      = str.top.content.length
  | 0 => rfl
  | b + 1 => by
    rw [memberAt_succL i j str b]
    show (moveAt j i (memberAt i j str b).content).length
      = str.top.content.length
    rw [length_moveAt]
    exact member_lenL i j str b

private theorem groupAt_nilL (mu : List Nat) :
    ∀ pool : List HVec, (∀ v ∈ pool, ¬ v.content = mu) →
      groupAt pool mu = []
  | [], _ => rfl
  | v :: t, h => by
    rw [groupAt_cons v t mu]
    cases hb : v.content == mu with
    | true => exact absurd (ground.listBeqEq hb) (h v (List.Mem.head t))
    | false =>
      exact groupAt_nilL mu t (fun x hx => h x (List.Mem.tail v hx))

private theorem countOf_cons_posL {α : Type} [DecidableEq α]
    {x a : α} {t : List α} (h : 0 < ground.countOf x (a :: t)) :
    x = a ∨ 0 < ground.countOf x t := by
  by_cases he : x = a
  · exact Or.inl he
  · refine Or.inr ?_
    rw [← ground.countOf_head_ne he t]
    exact h

private theorem newAt_len_oneL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (new : PairString)
    (hgnew : goodString i j s.length (blockSpan s) new) :
    (membersAt i j [new] new.top.content).length = 1 := by
  rw [membersAt_eqL i j new.top.content [new], memPool_singleL,
    length_groupAt]
  refine Nat.le_antisymm
    (occL_le1L (memberAt i j new) (new.ht + 1) ?_ new.top.content)
    (occL_posL (memberAt i j new) new.top.content (new.ht + 1) 0
      (Nat.succ_pos _) rfl)
  intro b b' hb hb' hc
  exact member_content_injL i j s.length hij hi hj (blockSpan s) new
    hgnew b b' (Nat.le_of_succ_le_succ hb)
    (Nat.le_of_succ_le_succ hb') hc

private theorem newAt_nilL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (new : PairString)
    (hgnew : goodString i j s.length (blockSpan s) new)
    (mu : List Nat) (hne : ¬ new.top.content = mu)
    (hkey : hKey i j new.top.content ≤ hKey i j mu) :
    membersAt i j [new] mu = [] := by
  rw [membersAt_eqL i j mu [new], memPool_singleL]
  refine groupAt_nilL mu _
    (memAll_mapRangeL _ (memberAt i j new) (new.ht + 1) ?_)
  intro b hb hcon
  match b with
  | 0 => exact hne hcon
  | b' + 1 =>
    have hlt := member_key_ltL i j s.length hij hi hj (blockSpan s)
      new hgnew (b' + 1) (Nat.le_of_succ_le_succ hb)
      (Nat.succ_pos b')
    rw [hcon] at hlt
    exact absurd (Nat.lt_of_lt_of_le hlt hkey) (Nat.lt_irrefl _)

private theorem new_perp_depthL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (new : PairString)
    (hnewlen : new.top.content.length = s.length)
    (hnewsz : sized new.top)
    (hbase : ∀ q, q < (membersAt i j strs new.top.content).length →
      (elim.dotP new.top.coords (ground.getAt []
        (membersAt i j strs new.top.content) q)).oneValue
        BPair.unit) :
    ∀ b : Nat, ∀ q,
      q < (membersAt i j strs (memberAt i j new b).content).length →
      (elim.dotP (memberAt i j new b).coords (ground.getAt []
        (membersAt i j strs (memberAt i j new b).content)
        q)).oneValue BPair.unit
  | 0 => hbase
  | b + 1 => by
    have hih := new_perp_depthL s i j hi hj hij strs hgood new
      hnewlen hnewsz hbase b
    have hstep := members_perp_dnL s i j hi hj hij
      (memberAt i j new b)
      (by rw [member_lenL]; exact hnewlen)
      (iterAct_sized i j new.top hnewsz b) strs hgood hih
    rw [memberAt_succL i j new b]
    exact hstep

private theorem step_invL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (done : List (List Nat)) (strs : List PairString)
    (hgood : ∀ str ∈ strs, goodString i j s.length (blockSpan s) str)
    (hperpM : ∀ mu, elim.perpAll (membersAt i j strs mu))
    (hB : ∀ mu, 0 < ground.countOf mu done → ∀ k,
      k < (groupAt (blockSpan s) mu).length →
      poly.unitTail (elim.residV (monomialsAt mu).length
        (membersAt i j strs mu)
        (ground.getAt [] (groupAt (blockSpan s) mu) k)))
    (new : PairString)
    (hgnew : goodString i j s.length (blockSpan s) new)
    (hbase : ∀ q, q < (membersAt i j strs new.top.content).length →
      (elim.dotP new.top.coords (ground.getAt []
        (membersAt i j strs new.top.content) q)).oneValue
        BPair.unit)
    (hnotdone : ¬ 0 < ground.countOf new.top.content done)
    (hdom : ∀ mu, 0 < ground.countOf mu done →
      hKey i j new.top.content ≤ hKey i j mu) :
    StateL s i j (strs ++ [new]) done
      ∧ (membersAt i j (strs ++ [new]) new.top.content).length
          = (membersAt i j strs new.top.content).length + 1 := by
  have hinj : ∀ b b', b < new.ht + 1 → b' < new.ht + 1 →
      (memberAt i j new b).content
        = (memberAt i j new b').content → b = b' := by
    intro b b' hb hb' hc
    exact member_content_injL i j s.length hij hi hj (blockSpan s)
      new hgnew b b' (Nat.le_of_succ_le_succ hb)
      (Nat.le_of_succ_le_succ hb') hc
  have hallP := memAll_mapRangeL
    (fun v => ∀ q, q < (membersAt i j strs v.content).length →
      (elim.dotP v.coords (ground.getAt []
        (membersAt i j strs v.content) q)).oneValue BPair.unit)
    (memberAt i j new) (new.ht + 1)
    (fun b _ => new_perp_depthL s i j hi hj hij strs hgood new
      hgnew.2.1 hgnew.1 hbase b)
  refine ⟨⟨memAll_append hgood (memAll_cons hgnew memAll_nil),
    ?_, ?_⟩, ?_⟩
  · intro mu
    rw [membersAt_appendL i j strs [new] mu]
    refine elim.perpAll_append _ _ (hperpM mu) ?_ ?_
    · refine elim.perpAll_le1 _ ?_
      rw [membersAt_eqL i j mu [new], memPool_singleL,
        length_groupAt]
      exact occL_le1L (memberAt i j new) (new.ht + 1) hinj mu
    · intro p q hp hq
      rw [membersAt_eqL i j mu [new], memPool_singleL] at hq ⊢
      match groupAt_rows _ _ hallP mu q hq with
      | ⟨v, hPv, hcv, hgetv⟩ =>
        rw [hgetv, elim.dotP_comm]
        have hpv := hPv p (by rw [hcv]; exact hp)
        rw [hcv] at hpv
        exact hpv
  · intro mu hmu k hk
    have hnil : membersAt i j [new] mu = [] :=
      newAt_nilL s i j hi hj hij new hgnew mu
        (fun he => hnotdone (by rw [he]; exact hmu))
        (hdom mu hmu)
    rw [membersAt_appendL i j strs [new] mu, hnil,
      ground.append_nil]
    exact hB mu hmu k hk
  · rw [membersAt_appendL i j strs [new] new.top.content,
      ground.length_append,
      newAt_len_oneL s i j hi hj hij new hgnew]


/-! The content's collection run: the fuel counts the group's rows,
each refusal joining one member at the content, and the run closes
with every group row passing — the exchange bound the fuel's own
guarantee. -/

private theorem hup_ofL (s : Shape) (i j : Nat) (hi : i < s.length)
    (hij : ¬ i = j) (nu : List Nat) (hnu : nu.length = s.length)
    (done rest : List (List Nat)) (strs : List PairString)
    (hst : StateL s i j strs done)
    (hsorted : sortedKeyL i j (nu :: rest))
    (hcov : ∀ mu, 0 < occupancyAt (blockSpan s) mu →
      0 < ground.countOf mu done
        ∨ 0 < ground.countOf mu (nu :: rest))
    (hcj : 0 < ground.getAt 0 nu j) :
    ∀ kk, kk < (groupAt (blockSpan s) (moveAt i j nu)).length →
      poly.unitTail (elim.residV
        (monomialsAt (moveAt i j nu)).length
        (membersAt i j strs (moveAt i j nu))
        (ground.getAt []
          (groupAt (blockSpan s) (moveAt i j nu)) kk)) := by
  intro kk hkk
  have hocc : 0 < occupancyAt (blockSpan s) (moveAt i j nu) := by
    rw [← groupAt_occupancy]
    exact Nat.lt_of_le_of_lt (Nat.zero_le kk) hkk
  match hcov (moveAt i j nu) hocc with
  | .inl hd => exact hst.2.2 (moveAt i j nu) hd kk hkk
  | .inr hr =>
    exfalso
    have hle : hKey i j (moveAt i j nu) ≤ hKey i j nu :=
      match countOf_cons_posL hr with
      | .inl he => Nat.le_of_eq (by rw [he])
      | .inr hrest => hsorted.1 _ hrest
    rw [hKey_moveAtL i j hij nu (by rw [hnu]; exact hi) hcj] at hle
    exact Nat.not_succ_le_self (hKey i j nu)
      (Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) hle)

private theorem collectAt_succL (i j : Nat) (pool : List HVec)
    (nu : List Nat) (fuel : Nat) (strs : List PairString) :
    collectAt i j pool nu (fuel + 1) strs
      = match (groupAt pool nu).find? (fun g =>
          ¬ poly.unitTail (elim.residV g.length
            (membersAt i j strs nu) g)) with
        | none => strs
        | some g => collectAt i j pool nu fuel
            (strs ++ [⟨⟨nu, elim.residV g.length
              (membersAt i j strs nu) g⟩, hAt i j nu⟩]) := rfl

private theorem nu_lenL (s : Shape) (nu : List Nat) (k : Nat)
    (hk : k < (groupAt (blockSpan s) nu).length) :
    nu.length = s.length :=
  match groupAt_rows (fun v => v.content.length = s.length)
      (blockSpan s) (blockcount.blockSpan_width s) nu k hk with
  | ⟨_, hlen, hc, _⟩ => by
    rw [← hc]
    exact hlen

private theorem collect_fuelL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) (done rest : List (List Nat))
    (hsorted : sortedKeyL i j (nu :: rest))
    (hdom : ∀ mu, 0 < ground.countOf mu done →
      hKey i j nu ≤ hKey i j mu)
    (hcov : ∀ mu, 0 < occupancyAt (blockSpan s) mu →
      0 < ground.countOf mu done
        ∨ 0 < ground.countOf mu (nu :: rest)) :
    ∀ (fuel : Nat) (strs : List PairString),
      StateL s i j strs done →
      (groupAt (blockSpan s) nu).length
          ≤ (membersAt i j strs nu).length + fuel →
      StateL s i j (collectAt i j (blockSpan s) nu fuel strs) done
        ∧ (∀ k, k < (groupAt (blockSpan s) nu).length →
            poly.unitTail (elim.residV (monomialsAt nu).length
              (membersAt i j
                (collectAt i j (blockSpan s) nu fuel strs) nu)
              (ground.getAt [] (groupAt (blockSpan s) nu) k)))
  | 0, strs, hst, hb => by
    refine ⟨hst, ?_⟩
    intro k hk
    by_cases hpass : poly.unitTail (elim.residV
        (monomialsAt nu).length (membersAt i j strs nu)
        (ground.getAt [] (groupAt (blockSpan s) nu) k))
    · exact hpass
    · exfalso
      have hgn : (ground.getAt ([] : List BPair)
          (groupAt (blockSpan s) nu) k).length
          = (monomialsAt nu).length :=
        elim.rowsLen_getAt (groupAt (blockSpan s) nu) k
          (rowsLen_groupAt nu (blockSpan s)
            (lowerspan.spanReads s).1) hk
      have hns : ¬ elim.spanRel (monomialsAt nu).length
          (membersAt i j strs nu)
          (ground.getAt [] (groupAt (blockSpan s) nu) k) :=
        fun hsp => hpass (elim.resid_complete _ _ _
          (members_rowsLenL s i j strs hst.1 nu) hgn hsp)
      have hle := elim.span_count_le (monomialsAt nu).length
        (membersAt i j strs nu
          ++ [ground.getAt [] (groupAt (blockSpan s) nu) k])
        (groupAt (blockSpan s) nu)
        (elim.rowsLen_append _
          (members_rowsLenL s i j strs hst.1 nu) ⟨hgn, trivial⟩)
        (rowsLen_groupAt nu (blockSpan s)
          (lowerspan.spanReads s).1)
        (elim.indep_extend (monomialsAt nu).length
          (membersAt i j strs nu) _
          (members_rowsLenL s i j strs hst.1 nu) hgn
          (members_indepL s i j hi hj hij strs hst.1 nu
            (hst.2.1 nu)) hns)
        (elim.span_rows_append _ _ _ _
          (members_span_getL s i j hi hj hij strs hst.1 nu)
          (elim.spanRel_getAt (monomialsAt nu).length
            (groupAt (blockSpan s) nu) k hk
            (rowsLen_groupAt nu (blockSpan s)
              (lowerspan.spanReads s).1)))
      rw [ground.length_append] at hle
      rw [Nat.add_zero] at hb
      exact Nat.not_succ_le_self _ (Nat.le_trans hle hb)
  | fuel + 1, strs, hst, hb => by
    rw [collectAt_succL i j (blockSpan s) nu fuel strs]
    cases hf : (groupAt (blockSpan s) nu).find? (fun g =>
        ¬ poly.unitTail (elim.residV g.length
          (membersAt i j strs nu) g)) with
    | none =>
      refine ⟨hst, ?_⟩
      intro k hk
      have hgn : (ground.getAt ([] : List BPair)
          (groupAt (blockSpan s) nu) k).length
          = (monomialsAt nu).length :=
        elim.rowsLen_getAt (groupAt (blockSpan s) nu) k
          (rowsLen_groupAt nu (blockSpan s)
            (lowerspan.spanReads s).1) hk
      have hb3 : decide (¬ poly.unitTail (elim.residV
          (ground.getAt ([] : List BPair)
            (groupAt (blockSpan s) nu) k).length
          (membersAt i j strs nu)
          (ground.getAt [] (groupAt (blockSpan s) nu) k)))
          = false :=
        findB_noneL ([] : List BPair) _
          (groupAt (blockSpan s) nu) hf k hk
      rw [hgn] at hb3
      exact unitTail_of_decFalseL hb3
    | some g =>
      show StateL s i j (collectAt i j (blockSpan s) nu fuel
          (strs ++ [⟨⟨nu, elim.residV g.length
            (membersAt i j strs nu) g⟩, hAt i j nu⟩])) done
        ∧ (∀ k, k < (groupAt (blockSpan s) nu).length →
            poly.unitTail (elim.residV (monomialsAt nu).length
              (membersAt i j (collectAt i j (blockSpan s) nu fuel
                (strs ++ [⟨⟨nu, elim.residV g.length
                  (membersAt i j strs nu) g⟩, hAt i j nu⟩])) nu)
              (ground.getAt [] (groupAt (blockSpan s) nu) k)))
      match findB_someL ([] : List BPair) (fun g =>
          ¬ poly.unitTail (elim.residV g.length
            (membersAt i j strs nu) g))
          (groupAt (blockSpan s) nu) g hf with
      | ⟨hgt, k, hk, hgk⟩ =>
        have hgtrue : decide (¬ poly.unitTail (elim.residV g.length
            (membersAt i j strs nu) g)) = true := hgt
        have hrefuse0 : ¬ poly.unitTail (elim.residV g.length
            (membersAt i j strs nu) g) := of_decide_eq_true hgtrue
        have hglen : g.length = (monomialsAt nu).length := by
          rw [← hgk]
          exact elim.rowsLen_getAt (groupAt (blockSpan s) nu) k
            (rowsLen_groupAt nu (blockSpan s)
              (lowerspan.spanReads s).1) hk
        have hnu : nu.length = s.length := nu_lenL s nu k hk
        have hgsp : elim.spanRel (monomialsAt nu).length
            (groupAt (blockSpan s) nu) g := by
          rw [← hgk]
          exact elim.spanRel_getAt (monomialsAt nu).length
            (groupAt (blockSpan s) nu) k hk
            (rowsLen_groupAt nu (blockSpan s)
              (lowerspan.spanReads s).1)
        rw [hglen]
        rw [hglen] at hrefuse0
        have hcolln : elim.rowsLen (monomialsAt nu).length
            (membersAt i j strs nu) :=
          members_rowsLenL s i j strs hst.1 nu
        have hwperp : ∀ q, q < (membersAt i j strs nu).length →
            (elim.dotP (elim.residV (monomialsAt nu).length
                (membersAt i j strs nu) g)
              (ground.getAt [] (membersAt i j strs nu) q)).oneValue
              BPair.unit := by
          intro q hq
          rw [elim.dotP_comm]
          exact elim.resid_perp (monomialsAt nu).length
            (membersAt i j strs nu) g hcolln hglen q hq
        have hgnew := new_goodL s i j hi hj hij nu hnu strs hst.1
          hst.2.1
          (hup_ofL s i j hi hij nu hnu done rest strs hst hsorted
            hcov)
          g hglen hgsp hrefuse0
        have hnotdone : ¬ 0 < ground.countOf nu done := by
          intro hd
          have hp := hst.2.2 nu hd k hk
          rw [hgk] at hp
          exact hrefuse0 hp
        have hstep := step_invL s i j hi hj hij done strs hst.1
          hst.2.1 hst.2.2
          ⟨⟨nu, elim.residV (monomialsAt nu).length
            (membersAt i j strs nu) g⟩, hAt i j nu⟩
          hgnew hwperp hnotdone hdom
        refine collect_fuelL s i j hi hj hij nu done rest hsorted
          hdom hcov fuel _ hstep.1 ?_
        rw [hstep.2, Nat.add_assoc, Nat.add_comm 1 fuel]
        exact hb


/-! The walk over the sorted contents: each content's run joins its
strings and leaves every group row passing, the processed list
growing by the content at the head — the whole exhaustion's state
at the sorted list's end. -/

/-- A head's count in its own list is occupied. -/
private theorem countOf_self_consL (a : List Nat)
    (t : List (List Nat)) : 0 < ground.countOf a (a :: t) := by
  rw [ground.countOf_head a t]
  exact Nat.succ_pos _

private theorem walk_goL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j) :
    ∀ (rest done : List (List Nat)) (strs : List PairString),
      StateL s i j strs done → sortedKeyL i j rest →
      (∀ mu, 0 < ground.countOf mu done → ∀ x,
        0 < ground.countOf x rest → hKey i j x ≤ hKey i j mu) →
      (∀ mu, 0 < occupancyAt (blockSpan s) mu →
        0 < ground.countOf mu done ∨ 0 < ground.countOf mu rest) →
      StateL s i j (rest.foldl (fun strs nu =>
        collectAt i j (blockSpan s) nu
          (groupAt (blockSpan s) nu).length strs) strs)
        (done ++ rest)
  | [], done, strs, hst, _, _, _ => by
    rw [ground.append_nil]
    exact hst
  | nu :: rest, done, strs, hst, hsorted, hdom, hcov => by
    have hdom' : ∀ mu, 0 < ground.countOf mu done →
        hKey i j nu ≤ hKey i j mu :=
      fun mu hmu => hdom mu hmu nu (countOf_self_consL nu rest)
    have hres := collect_fuelL s i j hi hj hij nu done rest hsorted
      hdom' hcov (groupAt (blockSpan s) nu).length strs hst
      (Nat.le_add_left _ _)
    have hst2 : StateL s i j (collectAt i j (blockSpan s) nu
        (groupAt (blockSpan s) nu).length strs) (done ++ [nu]) := by
      refine ⟨hres.1.1, hres.1.2.1, ?_⟩
      intro mu hmu k hk
      by_cases hd : 0 < ground.countOf mu done
      · exact hres.1.2.2 mu hd k hk
      · have hz : ground.countOf mu done = 0 :=
          match Nat.eq_zero_or_pos (ground.countOf mu done) with
          | .inl h0 => h0
          | .inr hp => absurd hp hd
        rw [ground.countOf_append mu done [nu], hz, Nat.zero_add]
          at hmu
        have hmn : mu = nu := ground.countOf_single hmu
        rw [hmn]
        exact hres.2 k (by rw [← hmn]; exact hk)
    have hnext := walk_goL s i j hi hj hij rest (done ++ [nu])
      (collectAt i j (blockSpan s) nu
        (groupAt (blockSpan s) nu).length strs) hst2 hsorted.2
      (fun mu hmu x hx => by
        rw [ground.countOf_append mu done [nu]] at hmu
        by_cases hd : 0 < ground.countOf mu done
        · exact hdom mu hd x (ground.countOf_cons_pos hx)
        · have hz : ground.countOf mu done = 0 :=
            match Nat.eq_zero_or_pos (ground.countOf mu done) with
            | .inl h0 => h0
            | .inr hp => absurd hp hd
          rw [hz, Nat.zero_add] at hmu
          rw [ground.countOf_single hmu]
          exact hsorted.1 x hx)
      (fun mu hocc =>
        match hcov mu hocc with
        | .inl hd => Or.inl (ground.countOf_append_left mu [nu] hd)
        | .inr hr =>
          match countOf_cons_posL hr with
          | .inl he => Or.inl (ground.countOf_append_right mu done
              (by rw [he]; exact countOf_self_consL nu []))
          | .inr ht => Or.inr ht)
    rw [ground.append_assoc done [nu] rest] at hnext
    exact hnext

private theorem walk_stateL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j) :
    StateL s i j (walk i j (blockSpan s))
      ([] ++ contentsByKey i j (blockSpan s)) :=
  walk_goL s i j hi hj hij (contentsByKey i j (blockSpan s)) []
    []
    ⟨memAll_nil, fun _ p hp _ _ _ => absurd hp (Nat.not_lt_zero p),
      fun _ hd => absurd hd (Nat.lt_irrefl 0)⟩
    (contentsByKey_sortedL i j (blockSpan s))
    (fun _ hd => absurd hd (Nat.lt_irrefl 0))
    (fun mu hocc =>
      Or.inr (contentsByKey_coverL i j (blockSpan s) mu hocc))

/-- Every collected string is good. -/
theorem walk_good (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) :
    ∀ str ∈ walk i j (blockSpan s),
      goodString i j s.length (blockSpan s) str :=
  (walk_stateL s i j hi hj hij).1

/-- The members at a content are pairwise perpendicular. -/
theorem walk_perp (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (nu : List Nat) (p q : Nat)
    (hp : p < (membersAt i j (walk i j (blockSpan s)) nu).length)
    (hq : q < (membersAt i j (walk i j (blockSpan s)) nu).length)
    (hpq : ¬ p = q) :
    (elim.dotP
      (ground.getAt []
        (membersAt i j (walk i j (blockSpan s)) nu) p)
      (ground.getAt []
        (membersAt i j (walk i j (blockSpan s)) nu)
        q)).oneValue BPair.unit :=
  (walk_stateL s i j hi hj hij).2.1 nu p hp q hq hpq

/-- Every member at a content sits off the sum's unit. -/
theorem walk_off (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (nu : List Nat) (p : Nat)
    (hp : p < (membersAt i j (walk i j (blockSpan s)) nu).length) :
    ¬ poly.unitTail (ground.getAt []
      (membersAt i j (walk i j (blockSpan s)) nu) p) :=
  members_off_getL s i j hi hj hij (walk i j (blockSpan s))
    (walk_good s i j hi hj hij) nu p hp

/-- Every group row at a content sits in the collected members'
span, the walk's terminal read at the residual's certificate. -/
theorem walk_spanRowL (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) (k : Nat)
    (hk : k < (groupAt (blockSpan s) nu).length) :
    elim.spanRel (monomialsAt nu).length
      (membersAt i j (walk i j (blockSpan s)) nu)
      (ground.getAt [] (groupAt (blockSpan s) nu) k) := by
  have hgood := walk_good s i j hi hj hij
  have hrows := members_rowsLenL s i j (walk i j (blockSpan s))
    hgood nu
  have hgrows := rowsLen_groupAt nu (blockSpan s)
    (lowerspan.spanReads s).1
  have hind := members_indepL s i j hi hj hij
    (walk i j (blockSpan s)) hgood nu
    ((walk_stateL s i j hi hj hij).2.1 nu)
  have hocc : 0 < occupancyAt (blockSpan s) nu := by
    rw [← groupAt_occupancy]
    exact Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  refine elim.resid_sound (monomialsAt nu).length _ _ hrows
    (elim.rowsLen_getAt (groupAt (blockSpan s) nu) k hgrows hk)
    (elim.indep_det (monomialsAt nu).length _ hind) ?_
  exact (walk_stateL s i j hi hj hij).2.2 nu
    (contentsByKey_coverL i j (blockSpan s) nu hocc) k hk

/-- The string count reads the span occupancy at every content,
the exchange read closing the comparison of the two independent
spanning lists. -/
theorem walk_count (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (nu : List Nat) :
    stringCount i j (walk i j (blockSpan s)) nu
      = occupancyAt (blockSpan s) nu := by
  rw [← groupAt_occupancy]
  show (membersAt i j (walk i j (blockSpan s)) nu).length
    = (groupAt (blockSpan s) nu).length
  have hgood := walk_good s i j hi hj hij
  exact elim.span_count_eq (monomialsAt nu).length _ _
    (members_rowsLenL s i j (walk i j (blockSpan s)) hgood nu)
    (rowsLen_groupAt nu (blockSpan s) (lowerspan.spanReads s).1)
    (members_indepL s i j hi hj hij (walk i j (blockSpan s))
      hgood nu ((walk_stateL s i j hi hj hij).2.1 nu))
    (blockcount.indepAll_all (lowerspan.spanReads s).2.1 nu)
    (members_span_getL s i j hi hj hij (walk i j (blockSpan s))
      hgood nu)
    (walk_spanRowL s i j hi hj hij nu)

/-! The threaded evaluator: the walk with the member pool carried
through the fold, each string's run computed once and the current
content's collection extended at the new top alone — one value
with the stated walk, the batteries' evaluation route — and the
spanning reads' public export, the trace read's instantiating
list. -/

/-- The string's member run, one action per step. -/
def runGo (i j : Nat) : Nat → HVec → List HVec
  | 0, v => [v]
  | b + 1, v => v :: runGo i j b (act j i v)

/-- The collection step at a carried state: the strings, the
member pool, and the current content's collection, the new top
extending all three. -/
def collectAtT (i j : Nat) (grp : elim.Mat) (nu : List Nat) :
    Nat → List PairString × List HVec × elim.Mat →
      List PairString × List HVec × elim.Mat
  | 0, st => st
  | fuel + 1, (strs, mem, coll) =>
    match grp.find? (fun g =>
      ¬ poly.unitTail (elim.residV g.length coll g)) with
    | none => (strs, mem, coll)
    | some g =>
      let w := elim.residV g.length coll g
      collectAtT i j grp nu fuel
        (strs ++ [⟨⟨nu, w⟩, hAt i j nu⟩],
         mem ++ runGo i j (hAt i j nu) ⟨nu, w⟩,
         coll ++ [w])

/-- The threaded walk: the member pool carried, the group and the
collection read once per content. -/
def walkT (i j : Nat) (pool : List HVec) : List PairString :=
  ((contentsByKey i j pool).foldl
    (fun st nu =>
      let r := collectAtT i j (groupAt pool nu) nu
        (groupAt pool nu).length
        (st.1, st.2, groupAt st.2 nu)
      (r.1, r.2.1))
    ([], [])).1

/-! The threaded walk's correspondence: the run is the string's
depth map, the carried pool the strings' own, and the carried
collection the content's members — the new string contributing
one member at its own content, its deeper members at the strictly
descending first-letter count. -/

private theorem mapRangeConsL {α : Type} (g : Nat → α) :
    ∀ n : Nat, (List.range (n + 1)).map g
      = g 0 :: (List.range n).map (fun b => g (b + 1))
  | 0 => rfl
  | n + 1 => by
    rw [range_succ (n + 1), ground.map_append, mapRangeConsL g n,
      range_succ n, ground.map_append]
    rfl

private theorem runGo_eqL (i j : Nat) : ∀ (h : Nat) (v : HVec),
    runGo i j h v
      = (List.range (h + 1)).map (fun b => iterAct i j b v)
  | 0, _ => rfl
  | h + 1, v => by
    show v :: runGo i j h (act j i v)
      = (List.range (h + 1 + 1)).map (fun b => iterAct i j b v)
    rw [runGo_eqL i j h (act j i v),
      mapRangeConsL (fun b => iterAct i j b v) (h + 1)]
    rfl

private theorem memPool_appendL (i j : Nat) :
    ∀ a b : List PairString,
      memPool i j (a ++ b) = memPool i j a ++ memPool i j b :=
  fun a b => ground.flatMap_append _ a b

private theorem memPool_runGoL (i j : Nat) (str : PairString) :
    memPool i j [str] = runGo i j str.ht str.top := by
  rw [memPool_singleL, runGo_eqL]
  rfl

/-- The first letter's count descends one per step along the run,
the lowering's own read at the occupied entry. -/
private theorem iterAct_countL (i j : Nat) (hij : ¬ i = j)
    (v : HVec) (n : Nat) (hn : n ≤ ground.getAt 0 v.content i) :
    ∀ b : Nat, b ≤ n →
      ground.getAt 0 (iterAct i j b v).content i + b
        = ground.getAt 0 v.content i
  | 0, _ => rfl
  | b + 1, hb => by
    have ih := iterAct_countL i j hij v n hn b (Nat.le_of_succ_le hb)
    have hpos : 0 < ground.getAt 0 (iterAct i j b v).content i := by
      match Nat.eq_zero_or_pos
          (ground.getAt 0 (iterAct i j b v).content i) with
      | .inr hp => exact hp
      | .inl h0 =>
        rw [h0, Nat.zero_add] at ih
        exact absurd (Nat.le_trans hb
          (Nat.le_trans hn (Nat.le_of_eq ih.symm)))
          (Nat.not_succ_le_self b)
    rw [iterAct_succ' i j b v]
    show ground.getAt 0
        (bumpAt j (dipAt i (iterAct i j b v).content)) i + (b + 1)
      = ground.getAt 0 v.content i
    rw [getAt_bumpAt_ne j (dipAt i (iterAct i j b v).content) i hij,
      show b + 1 = 1 + b from Nat.add_comm b 1, ← Nat.add_assoc,
      getAt_dipAt_self i (iterAct i j b v).content hpos]
    exact ih

/-- A member below the top sits off the top's content: the first
letter's count has strictly descended inside the height run. -/
private theorem iterAct_content_neL (i j : Nat) (v : HVec)
    (b : Nat) (hb0 : 0 < b) (hb : b ≤ hAt i j v.content) :
    ¬ (iterAct i j b v).content = v.content := by
  by_cases hij : i = j
  · exfalso
    have hz : hAt i j v.content = 0 := by
      show ground.getAt 0 v.content i - ground.getAt 0 v.content j
        = 0
      rw [hij, Nat.sub_self]
    rw [hz] at hb
    exact absurd (Nat.lt_of_lt_of_le hb0 hb) (Nat.lt_irrefl 0)
  · intro hcon
    have hcount := iterAct_countL i j hij v (hAt i j v.content)
      (Nat.sub_le _ _) b hb
    rw [hcon] at hcount
    have hbz : b + ground.getAt 0 v.content i
        = 0 + ground.getAt 0 v.content i := by
      rw [Nat.zero_add, Nat.add_comm b _]
      exact hcount
    rw [ground.addCancelR _ hbz] at hb0
    exact absurd hb0 (Nat.lt_irrefl 0)

private theorem groupAt_cons_hitL (v : HVec) (t : List HVec)
    (nu : List Nat) (hc : v.content = nu) :
    groupAt (v :: t) nu = v.coords :: groupAt t nu := by
  rw [groupAt_cons v t nu, hc, ground.listEqBeq nu]

/-- A string at the truncated gap holds one member at its top's
content, the top itself. -/
private theorem members_newL (i j : Nat) (str : PairString)
    (hht : str.ht = hAt i j str.top.content) :
    membersAt i j [str] str.top.content = [str.top.coords] := by
  have hnil : groupAt ((List.range str.ht).map
      (fun b => memberAt i j str (b + 1))) str.top.content = [] := by
    refine groupAt_nilL _ _ (memAll_mapRangeL _ _ str.ht ?_)
    intro b hb
    refine iterAct_content_neL i j str.top (b + 1)
      (Nat.succ_pos b) ?_
    rw [← hht]
    exact hb
  rw [membersAt_eqL i j str.top.content [str], memPool_singleL,
    mapRangeConsL]
  rw [groupAt_cons_hitL (memberAt i j str 0) _ str.top.content rfl,
    hnil]
  rfl

private theorem membersAt_newL (i j : Nat) (nu : List Nat)
    (w : List BPair) (strs : List PairString) :
    membersAt i j (strs ++ [⟨⟨nu, w⟩, hAt i j nu⟩]) nu
      = membersAt i j strs nu ++ [w] := by
  rw [membersAt_appendL i j strs [⟨⟨nu, w⟩, hAt i j nu⟩] nu]
  exact congrArg (fun t => membersAt i j strs nu ++ t)
    (members_newL i j ⟨⟨nu, w⟩, hAt i j nu⟩ rfl)

private theorem memPool_newL (i j : Nat) (nu : List Nat)
    (w : List BPair) (strs : List PairString) :
    memPool i j (strs ++ [⟨⟨nu, w⟩, hAt i j nu⟩])
      = memPool i j strs ++ runGo i j (hAt i j nu) ⟨nu, w⟩ := by
  rw [memPool_appendL i j strs [⟨⟨nu, w⟩, hAt i j nu⟩]]
  exact congrArg (fun t => memPool i j strs ++ t)
    (memPool_runGoL i j ⟨⟨nu, w⟩, hAt i j nu⟩)

private theorem collectAtT_succL (i j : Nat) (grp : elim.Mat)
    (nu : List Nat) (fuel : Nat) (strs : List PairString)
    (mem : List HVec) (coll : elim.Mat) :
    collectAtT i j grp nu (fuel + 1) (strs, mem, coll)
      = match grp.find? (fun g =>
          ¬ poly.unitTail (elim.residV g.length coll g)) with
        | none => (strs, mem, coll)
        | some g =>
          collectAtT i j grp nu fuel
            (strs ++ [⟨⟨nu, elim.residV g.length coll g⟩,
                hAt i j nu⟩],
             mem ++ runGo i j (hAt i j nu)
               ⟨nu, elim.residV g.length coll g⟩,
             coll ++ [elim.residV g.length coll g]) := rfl

/-- The threaded collection run is the walk's, the carried pool
and collection the strings' own reads at every fuel. -/
private theorem collectT_eqL (i j : Nat) (pool : List HVec)
    (nu : List Nat) :
    ∀ (fuel : Nat) (strs : List PairString),
      collectAtT i j (groupAt pool nu) nu fuel
          (strs, memPool i j strs, membersAt i j strs nu)
        = (collectAt i j pool nu fuel strs,
           memPool i j (collectAt i j pool nu fuel strs),
           membersAt i j (collectAt i j pool nu fuel strs) nu)
  | 0, _ => rfl
  | fuel + 1, strs => by
    rw [collectAtT_succL i j (groupAt pool nu) nu fuel strs
        (memPool i j strs) (membersAt i j strs nu),
      collectAt_succL i j pool nu fuel strs]
    cases hf : (groupAt pool nu).find? (fun g =>
        ¬ poly.unitTail (elim.residV g.length
          (membersAt i j strs nu) g)) with
    | none => rfl
    | some g =>
      show collectAtT i j (groupAt pool nu) nu fuel
          (strs ++ [⟨⟨nu, elim.residV g.length
              (membersAt i j strs nu) g⟩, hAt i j nu⟩],
           memPool i j strs ++ runGo i j (hAt i j nu)
             ⟨nu, elim.residV g.length
               (membersAt i j strs nu) g⟩,
           membersAt i j strs nu
             ++ [elim.residV g.length (membersAt i j strs nu) g])
        = _
      rw [← memPool_newL i j nu
          (elim.residV g.length (membersAt i j strs nu) g) strs,
        ← membersAt_newL i j nu
          (elim.residV g.length (membersAt i j strs nu) g) strs]
      exact collectT_eqL i j pool nu fuel _

private theorem walkT_goL (i j : Nat) (pool : List HVec) :
    ∀ (l : List (List Nat)) (strs : List PairString),
      l.foldl
          (fun st nu =>
            let r := collectAtT i j (groupAt pool nu) nu
              (groupAt pool nu).length
              (st.1, st.2, groupAt st.2 nu)
            (r.1, r.2.1))
          (strs, memPool i j strs)
        = (l.foldl (fun strs nu =>
              collectAt i j pool nu (groupAt pool nu).length strs)
            strs,
           memPool i j (l.foldl (fun strs nu =>
              collectAt i j pool nu (groupAt pool nu).length strs)
            strs))
  | [], _ => rfl
  | nu :: l, strs => by
    show l.foldl _
        ((collectAtT i j (groupAt pool nu) nu
            (groupAt pool nu).length
            (strs, memPool i j strs,
              groupAt (memPool i j strs) nu)).1,
         (collectAtT i j (groupAt pool nu) nu
            (groupAt pool nu).length
            (strs, memPool i j strs,
              groupAt (memPool i j strs) nu)).2.1)
      = _
    rw [← membersAt_eqL i j nu strs,
      collectT_eqL i j pool nu (groupAt pool nu).length strs]
    exact walkT_goL i j pool l
      (collectAt i j pool nu (groupAt pool nu).length strs)

/-- The threaded walk is the walk: the carried pool reads the
strings' members and the carried collection the content's own. -/
theorem walkT_eq (i j : Nat) (pool : List HVec) :
    walkT i j pool = walk i j pool :=
  congrArg Prod.fst
    (walkT_goL i j pool (contentsByKey i j pool) [])

/-- Every collected member sits in its content group's span. -/
theorem walk_span (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (nu : List Nat) (p : Nat)
    (hp : p < (membersAt i j (walk i j (blockSpan s)) nu).length) :
    elim.spanRel (monomialsAt nu).length
      (groupAt (blockSpan s) nu)
      (ground.getAt []
        (membersAt i j (walk i j (blockSpan s)) nu) p) :=
  members_span_getL s i j hi hj hij (walk i j (blockSpan s))
    (walk_good s i j hi hj hij) nu p hp

/-! `thm:weylchar`'s string-by-string trace: the pair's two ordered
words at a collected member with the per-depth weights they read.
At the string's own data — top gap `h`, depth `b` — the
raising-after-lowering word `E_ij E_ji` reads the coefficient
`(b+1)(h-b)` and the lowering-after-raising word `E_ji E_ij` reads
`b(h-b+1)`, `lem:tops`(ii)'s fold at the words `F^{b+1}` and
`F^b`, their sum the display's own `(j+1)d + j(d+1)` at the pair
`⟨h:j⟩`.  The weights collect along `membersAt`'s own spine, one
entry per collected member, so the trace fold reads them term by
term. -/

/-- The raising-after-lowering word at a depth: the composite
`E_ij E_ji` at the member's own content scales the member by the
depth's coefficient `(b+1)(h-b)` — the further lowering the
string's next member, the raising back the coefficient's scale
(`iterAct_raise`), and the vacant first letter, which only the
height's own depth reaches, reading the sum's unit on both
members. -/
private theorem iterAct_traceUp (i j : Nat) (hij : ¬ i = j)
    (v : HVec) (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords)
    (b : Nat) (hb : b ≤ h) (nu : List Nat)
    (hnu : (iterAct i j b v).content = nu) :
    poly.oneValue
      (elim.matVec
        (elim.matMul (units.matUnitAt nu (moveAt j i nu) i j)
          (units.matUnitAt (moveAt j i nu) nu j i))
        (iterAct i j b v).coords)
      (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
        (iterAct i j b v).coords) := by
  rw [← hnu]
  refine poly.oneValue_trans
    (elim.matVec_matMul _ _
      (monomialsAt (iterAct i j b v).content).length
      (units.rowsLen_matUnitAt _ _ j i) _
      (iterAct_sized i j v hsz b)) ?_
  by_cases hocc : 0 < ground.getAt 0 (iterAct i j b v).content i
  · have hround : moveAt i j (moveAt j i (iterAct i j b v).content)
        = (iterAct i j b v).content :=
      moveAt_round_at i j (iterAct i j b v).content hocc
    have hstep : act j i (iterAct i j b v) = iterAct i j (b + 1) v :=
      (iterAct_succ' i j b v).symm
    have hc1 : (iterAct i j (b + 1) v).content
        = moveAt j i (iterAct i j b v).content :=
      congrArg HVec.content hstep.symm
    have hact : (act i j (iterAct i j (b + 1) v)).coords
        = elim.matVec (units.matUnitAt (iterAct i j b v).content
            (moveAt j i (iterAct i j b v).content) i j)
          (iterAct i j (b + 1) v).coords := by
      show elim.matVec (units.matUnitAt
          (moveAt i j (iterAct i j (b + 1) v).content)
          (iterAct i j (b + 1) v).content i j)
          (iterAct i j (b + 1) v).coords = _
      rw [hc1, hround]
    show poly.oneValue
      (elim.matVec (units.matUnitAt (iterAct i j b v).content
        (moveAt j i (iterAct i j b v).content) i j)
        (act j i (iterAct i j b v)).coords) _
    rw [hstep, ← hact]
    exact iterAct_raise i j hij v h hgap hi hj hsz htop b hb
  · have hz : ground.getAt 0 (iterAct i j b v).content i = 0 :=
      match Nat.eq_zero_or_pos
          (ground.getAt 0 (iterAct i j b v).content i) with
      | .inl h0 => h0
      | .inr hp => absurd hp hocc
    have cy := iterAct_content i j hij b v h hgap hb hi hj
    have h1 : b = ground.getAt 0 v.content j + h := by
      rw [← hgap, ← cy.2.1, hz, Nat.zero_add]
    have hbh : h = b :=
      Nat.le_antisymm
        (Nat.le_trans (Nat.le_add_left h (ground.getAt 0 v.content j))
          (Nat.le_of_eq h1.symm)) hb
    refine poly.unitTail_oneValue
      (elim.matVec_null _ _ (tops.act_null j i (iterAct i j b v) hz)) ?_
    refine elim.unitTail_vecScale_unit ?_ _
    rw [hbh, Nat.sub_self, Nat.mul_zero]
    exact BPair.oneValue_refl BPair.unit

/-- The lowering-after-raising word at a depth: the composite
`E_ji E_ij` at the member's own content scales the member by the
depth's coefficient `b(h-b+1)` — the raising the shallower member
at its own scale (`iterAct_raise` one depth up), the lowering back
the member itself, and the top's own depth reading the sum's unit
at the raising's image. -/
private theorem iterAct_traceDn (i j : Nat) (hij : ¬ i = j)
    (v : HVec) (h : Nat)
    (hgap : ground.getAt 0 v.content i
      = ground.getAt 0 v.content j + h)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hsz : sized v) (htop : poly.unitTail (act i j v).coords)
    (b : Nat) (hb : b ≤ h) (nu : List Nat)
    (hnu : (iterAct i j b v).content = nu) :
    poly.oneValue
      (elim.matVec
        (elim.matMul (units.matUnitAt nu (moveAt i j nu) j i)
          (units.matUnitAt (moveAt i j nu) nu i j))
        (iterAct i j b v).coords)
      (elim.vecScale (BPair.ofNat (b * (h - b + 1)))
        (iterAct i j b v).coords) := by
  match b, hb, hnu with
  | 0, _, hnu =>
    rw [← hnu]
    refine poly.oneValue_trans
      (elim.matVec_matMul _ _
        (monomialsAt (iterAct i j 0 v).content).length
        (units.rowsLen_matUnitAt _ _ i j) _
        (iterAct_sized i j v hsz 0)) ?_
    refine poly.unitTail_oneValue
      (elim.matVec_null _ _ htop) ?_
    refine elim.unitTail_vecScale_unit ?_ _
    rw [Nat.zero_mul]
    exact BPair.oneValue_refl BPair.unit
  | b + 1, hb, hnu =>
    rw [← hnu]
    have hmE : (iterAct i j b v).coords.length
        = (monomialsAt (iterAct i j b v).content).length :=
      iterAct_sized i j v hsz b
    have hstep : act j i (iterAct i j b v) = iterAct i j (b + 1) v :=
      (iterAct_succ' i j b v).symm
    have cy := iterAct_content i j hij b v h hgap
      (Nat.le_of_succ_le hb) hi hj
    have hocc : 0 < ground.getAt 0 (iterAct i j b v).content i :=
      match Nat.eq_zero_or_pos
          (ground.getAt 0 (iterAct i j b v).content i) with
      | .inr hp => hp
      | .inl h0 => by
        have hbi : b = ground.getAt 0 v.content j + h := by
          rw [← hgap, ← cy.2.1, h0, Nat.zero_add]
        exact absurd (Nat.le_trans hb
          (Nat.le_trans (Nat.le_add_left h _)
            (Nat.le_of_eq hbi.symm))) (Nat.not_succ_le_self b)
    have hround : moveAt i j (moveAt j i (iterAct i j b v).content)
        = (iterAct i j b v).content :=
      moveAt_round_at i j (iterAct i j b v).content hocc
    rw [← hstep]
    refine poly.oneValue_trans
      (elim.matVec_matMul _ _
        (monomialsAt (act j i (iterAct i j b v)).content).length
        (units.rowsLen_matUnitAt _ _ i j) _
        (act_sized j i (iterAct i j b v))) ?_
    have hraise := iterAct_raise i j hij v h hgap hi hj hsz htop b
      (Nat.le_of_succ_le hb)
    rw [← hstep] at hraise
    have hlenA : (act i j (act j i (iterAct i j b v))).coords.length
        = (elim.vecScale (BPair.ofNat ((b + 1) * (h - b)))
            (iterAct i j b v).coords).length := by
      rw [elim.length_vecScale]
      show (elim.matVec (units.matUnitAt
          (moveAt i j (act j i (iterAct i j b v)).content)
          (act j i (iterAct i j b v)).content i j)
          (act j i (iterAct i j b v)).coords).length
        = (iterAct i j b v).coords.length
      rw [units.matVec_matUnitAt_length]
      show (monomialsAt (moveAt i j
          (moveAt j i (iterAct i j b v).content))).length
        = (iterAct i j b v).coords.length
      rw [hround]
      exact hmE.symm
    have hmw : (iterAct i j b v).coords.length
        = (monomialsAt (moveAt i j
            (act j i (iterAct i j b v)).content)).length := by
      show (iterAct i j b v).coords.length
        = (monomialsAt (moveAt i j
            (moveAt j i (iterAct i j b v).content))).length
      rw [hround]
      exact hmE
    have hlast : elim.matVec (units.matUnitAt
        (act j i (iterAct i j b v)).content
        (moveAt i j (act j i (iterAct i j b v)).content) j i)
        (iterAct i j b v).coords
        = (act j i (iterAct i j b v)).coords := by
      show elim.matVec (units.matUnitAt
          (moveAt j i (iterAct i j b v).content)
          (moveAt i j (moveAt j i (iterAct i j b v).content)) j i)
          (iterAct i j b v).coords
        = elim.matVec (units.matUnitAt
            (moveAt j i (iterAct i j b v).content)
            (iterAct i j b v).content j i)
          (iterAct i j b v).coords
      rw [hround]
    refine poly.oneValue_trans
      (elim.matVec_congr _ _ _ hraise) ?_
    refine poly.oneValue_trans
      (elim.matVec_vecScale _ _
        (units.rowsLen_matUnitAt _ _ j i) _ _ hmw) ?_
    rw [hlast, ground.subSuccAdd hb]
    exact poly.oneValue_refl _

/-- The trace's per-depth weight list at a content: the stated
coefficient collected along `membersAt`'s own spine, one entry per
collected member. -/
def weightList (i j : Nat) (f : Nat → Nat → Nat)
    (strs : List PairString) (nu : List Nat) : List Nat :=
  strs.flatMap (fun s =>
    (List.range (s.ht + 1)).flatMap (fun b =>
      if (memberAt i j s b).content = nu then [f s.ht b] else []))

/-- The raising side's string weight at a content: the per-depth
coefficient `(j+1)d` of `thm:weylchar`'s display summed over the
collected members, the pair `⟨h:j⟩`'s own read of `lem:tops`(ii)'s
fold at the word `F^{j+1}`. -/
def stringWeightUp (i j : Nat) (strs : List PairString)
    (nu : List Nat) : Nat :=
  sumNat (strs.flatMap (fun s =>
    (List.range (s.ht + 1)).flatMap (fun b =>
      if (memberAt i j s b).content = nu
      then [(b + 1) * (s.ht - b)]
      else [])))

/-- The lowering side's string weight at a content: the per-depth
coefficient `j(d+1)` of `thm:weylchar`'s display summed over the
collected members, the pair `⟨h:j⟩`'s own read of `lem:tops`(ii)'s
fold at the word `F^j`. -/
def stringWeightDn (i j : Nat) (strs : List PairString)
    (nu : List Nat) : Nat :=
  sumNat (strs.flatMap (fun s =>
    (List.range (s.ht + 1)).flatMap (fun b =>
      if (memberAt i j s b).content = nu
      then [b * (s.ht - b + 1)]
      else [])))

/-- The two side weights are the weight list's own sums. -/
theorem stringWeight_reads (i j : Nat) (strs : List PairString)
    (nu : List Nat) :
    stringWeightUp i j strs nu
        = sumNat (weightList i j (fun ht b => (b + 1) * (ht - b))
          strs nu)
      ∧ stringWeightDn i j strs nu
        = sumNat (weightList i j (fun ht b => b * (ht - b + 1))
          strs nu) :=
  ⟨rfl, rfl⟩

/-- A flattened family's width at matched member widths. -/
private theorem flatLenL {α β γ : Type} (F : γ → List α)
    (G : γ → List β) (hFG : ∀ c, (F c).length = (G c).length) :
    ∀ l : List γ, (l.flatMap F).length = (l.flatMap G).length
  | [] => rfl
  | a :: t => by
    show ((F a) ++ t.flatMap F).length = ((G a) ++ t.flatMap G).length
    rw [ground.length_append, ground.length_append, hFG a,
      flatLenL F G hFG t]

/-- The weight list reads `membersAt`'s own width: the two spines
are the same, one entry per collected member. -/
theorem weightList_length (i j : Nat) (f : Nat → Nat → Nat)
    (strs : List PairString) (nu : List Nat) :
    (weightList i j f strs nu).length
      = (membersAt i j strs nu).length :=
  flatLenL
    (fun s => (List.range (s.ht + 1)).flatMap (fun b =>
      if (memberAt i j s b).content = nu then [f s.ht b] else []))
    (fun s => (List.range (s.ht + 1)).flatMap (fun b =>
      if (memberAt i j s b).content = nu
      then [(memberAt i j s b).coords] else []))
    (fun s => flatLenL
      (fun b => if (memberAt i j s b).content = nu
        then [f s.ht b] else [])
      (fun b => if (memberAt i j s b).content = nu
        then [(memberAt i j s b).coords] else [])
      (fun b => by
        by_cases hg : (memberAt i j s b).content = nu
        · rw [if_pos hg, if_pos hg]
          rfl
        · rw [if_neg hg, if_neg hg]
          rfl)
      (List.range (s.ht + 1)))
    strs

/-- The per-row weight read: every row's image under the operator
reads its own weight's clearing, the trace fold's per-term
datum. -/
private def traceWeights (T : elim.Mat) : elim.Mat → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | x :: L, c :: cs =>
      poly.oneValue (elim.matVec T x)
          (elim.vecScale (BPair.ofNat c) x)
        ∧ traceWeights T L cs

/-- The weight read joins over a joined pair of spines. -/
private theorem traceWeights_append (T : elim.Mat) :
    ∀ (A A' : elim.Mat) (C C' : List Nat),
      traceWeights T A C → traceWeights T A' C' →
      traceWeights T (A ++ A') (C ++ C')
  | [], _, [], _, _, h' => h'
  | [], _, _ :: _, _, h, _ => nomatch h
  | _ :: _, _, [], _, h, _ => nomatch h
  | _ :: A, A', _ :: C, C', h, h' =>
      ⟨h.1, traceWeights_append T A A' C C' h.2 h'⟩

/-- The weight read at a key: the row's image against its own
weight's entry. -/
private theorem traceWeights_getL :
    ∀ (T L : elim.Mat) (cs : List Nat), traceWeights T L cs →
      ∀ k, k < L.length →
        poly.oneValue (elim.matVec T (ground.getAt [] L k))
          (elim.vecScale (BPair.ofNat (ground.getAt 0 cs k))
            (ground.getAt [] L k))
  | _, [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _, _ :: _, [], h, _, _ => nomatch h
  | _, _ :: _, _ :: _, h, 0, _ => h.1
  | T, _ :: L, _ :: cs, h, k + 1, hk =>
      traceWeights_getL T L cs h.2 k (Nat.lt_of_succ_lt_succ hk)

/-- One string's depth run reads its weights, depth by depth. -/
private theorem depthWeightsL (i j : Nat) (f : Nat → Nat → Nat)
    (nu : List Nat) (T : elim.Mat) (str : PairString)
    (hread : ∀ b, b ≤ str.ht →
      (memberAt i j str b).content = nu →
      poly.oneValue (elim.matVec T (memberAt i j str b).coords)
        (elim.vecScale (BPair.ofNat (f str.ht b))
          (memberAt i j str b).coords)) :
    ∀ n, n ≤ str.ht + 1 →
      traceWeights T
        ((List.range n).flatMap (fun b =>
          if (memberAt i j str b).content = nu
          then [(memberAt i j str b).coords] else []))
        ((List.range n).flatMap (fun b =>
          if (memberAt i j str b).content = nu
          then [f str.ht b] else []))
  | 0, _ => trivial
  | n + 1, hn => by
    rw [ground.range_succ n, ground.flatMap_append,
      ground.flatMap_append]
    refine traceWeights_append T _ _ _ _
      (depthWeightsL i j f nu T str hread n (Nat.le_of_succ_le hn))
      ?_
    by_cases hg : (memberAt i j str n).content = nu
    · show traceWeights T
        ((if (memberAt i j str n).content = nu
          then [(memberAt i j str n).coords] else []) ++ [])
        ((if (memberAt i j str n).content = nu
          then [f str.ht n] else []) ++ [])
      rw [if_pos hg, if_pos hg]
      exact ⟨hread n (Nat.le_of_lt_succ hn) hg, trivial⟩
    · show traceWeights T
        ((if (memberAt i j str n).content = nu
          then [(memberAt i j str n).coords] else []) ++ [])
        ((if (memberAt i j str n).content = nu
          then [f str.ht n] else []) ++ [])
      rw [if_neg hg, if_neg hg]
      exact trivial

/-- The collected members read their weights, string by string. -/
private theorem membersWeightsL (i j : Nat) (f : Nat → Nat → Nat)
    (nu : List Nat) (T : elim.Mat) :
    ∀ strs : List PairString,
      (∀ str ∈ strs, ∀ b, b ≤ str.ht →
        (memberAt i j str b).content = nu →
        poly.oneValue (elim.matVec T (memberAt i j str b).coords)
          (elim.vecScale (BPair.ofNat (f str.ht b))
            (memberAt i j str b).coords)) →
      traceWeights T (membersAt i j strs nu)
        (weightList i j f strs nu)
  | [], _ => trivial
  | str :: t, hread => by
    show traceWeights T
      ((List.range (str.ht + 1)).flatMap (fun b =>
          if (memberAt i j str b).content = nu
          then [(memberAt i j str b).coords] else [])
        ++ membersAt i j t nu)
      ((List.range (str.ht + 1)).flatMap (fun b =>
          if (memberAt i j str b).content = nu
          then [f str.ht b] else [])
        ++ weightList i j f t nu)
    exact traceWeights_append T _ _ _ _
      (depthWeightsL i j f nu T str (hread str (List.Mem.head t))
        (str.ht + 1) (Nat.le_refl _))
      (membersWeightsL i j f nu T t
        (fun s hs => hread s (List.Mem.tail str hs)))

/-- `thm:weylchar`'s raising-side read at a collected member: the
composite `E_ij E_ji` at the pair's content scales the member by
its own depth's weight, the string's data the exhaustion's own. -/
theorem walk_traceUp (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (nu : List Nat) (k : Nat)
    (hk : k < (membersAt i j (walk i j (blockSpan s)) nu).length) :
    poly.oneValue
      (elim.matVec
        (elim.matMul (units.matUnitAt nu (moveAt j i nu) i j)
          (units.matUnitAt (moveAt j i nu) nu j i))
        (ground.getAt []
          (membersAt i j (walk i j (blockSpan s)) nu) k))
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0
          (weightList i j (fun ht b => (b + 1) * (ht - b))
            (walk i j (blockSpan s)) nu) k))
        (ground.getAt []
          (membersAt i j (walk i j (blockSpan s)) nu) k)) :=
  traceWeights_getL _ _ _
    (membersWeightsL i j (fun ht b => (b + 1) * (ht - b)) nu _
      (walk i j (blockSpan s))
      (fun str hstr b hbh hcon =>
        iterAct_traceUp i j hij str.top str.ht
          (walk_good s i j hi hj hij str hstr).2.2.1
          (by rw [(walk_good s i j hi hj hij str hstr).2.1]
              exact hi)
          (by rw [(walk_good s i j hi hj hij str hstr).2.1]
              exact hj)
          (walk_good s i j hi hj hij str hstr).1
          (walk_good s i j hi hj hij str hstr).2.2.2.1
          b hbh nu hcon)) k hk

/-- `thm:weylchar`'s lowering-side read at a collected member: the
composite `E_ji E_ij` at the pair's content scales the member by
its own depth's weight. -/
theorem walk_traceDn (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (nu : List Nat) (k : Nat)
    (hk : k < (membersAt i j (walk i j (blockSpan s)) nu).length) :
    poly.oneValue
      (elim.matVec
        (elim.matMul (units.matUnitAt nu (moveAt i j nu) j i)
          (units.matUnitAt (moveAt i j nu) nu i j))
        (ground.getAt []
          (membersAt i j (walk i j (blockSpan s)) nu) k))
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0
          (weightList i j (fun ht b => b * (ht - b + 1))
            (walk i j (blockSpan s)) nu) k))
        (ground.getAt []
          (membersAt i j (walk i j (blockSpan s)) nu) k)) :=
  traceWeights_getL _ _ _
    (membersWeightsL i j (fun ht b => b * (ht - b + 1)) nu _
      (walk i j (blockSpan s))
      (fun str hstr b hbh hcon =>
        iterAct_traceDn i j hij str.top str.ht
          (walk_good s i j hi hj hij str hstr).2.2.1
          (by rw [(walk_good s i j hi hj hij str hstr).2.1]
              exact hi)
          (by rw [(walk_good s i j hi hj hij str hstr).2.1]
              exact hj)
          (walk_good s i j hi hj hij str hstr).1
          (walk_good s i j hi hj hij str hstr).2.2.2.1
          b hbh nu hcon)) k hk

/-! `lem:strings`' content symmetry: the depth run reverses under
the letter transposition — at a string's own gap the depth-`(h-b)`
member's content is the depth-`b` member's transposed — so the
members at a content and at its transposition are equinumerous
string by string, and the span occupancy with them
(`walk_count`), the reflection read `thm:weylchar` consumes at
the block's contents. -/

/-- The run's collected count, the depth family's own fold. -/
private def sumToL (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c n + sumToL c n

/-- The flattened family's width is the run's collected count. -/
private theorem rangeLenL {α : Type} (F : Nat → List α) :
    ∀ n : Nat, ((List.range n).flatMap F).length
      = sumToL (fun b => (F b).length) n
  | 0 => rfl
  | n + 1 => by
    rw [ground.range_succ n, ground.flatMap_append,
      ground.length_append, rangeLenL F n]
    show sumToL (fun b => (F b).length) n
        + (F n ++ ([] : List α)).length
      = (F n).length + sumToL (fun b => (F b).length) n
    rw [ground.length_append]
    show sumToL (fun b => (F b).length) n + ((F n).length + 0)
      = (F n).length + sumToL (fun b => (F b).length) n
    rw [Nat.add_zero, Nat.add_comm]

/-- The run's count peels at its lowest depth. -/
private theorem sumTo_peelL (c : Nat → Nat) :
    ∀ n : Nat, sumToL c (n + 1)
      = c 0 + sumToL (fun b => c (b + 1)) n
  | 0 => rfl
  | n + 1 => by
    show c (n + 1) + sumToL c (n + 1)
      = c 0 + (c (n + 1) + sumToL (fun b => c (b + 1)) n)
    rw [sumTo_peelL c n, ← Nat.add_assoc,
      Nat.add_comm (c (n + 1)) (c 0), Nat.add_assoc]

/-- The run's count reads its family depth by depth. -/
private theorem sumTo_congrL (c d : Nat → Nat) :
    ∀ n : Nat, (∀ b, b < n → c b = d b) →
      sumToL c n = sumToL d n
  | 0, _ => rfl
  | n + 1, h => by
    show c n + sumToL c n = d n + sumToL d n
    rw [h n (Nat.le_refl (n + 1)),
      sumTo_congrL c d n
        (fun b hb => h b (Nat.lt_of_lt_of_le hb (Nat.le_succ n)))]

/-- The successor's gap at a depth inside the run. -/
private theorem succSubL : ∀ {n b : Nat}, b ≤ n →
    n + 1 - b = (n - b) + 1
  | _, 0, _ => rfl
  | 0, _ + 1, hb => absurd hb (Nat.not_succ_le_zero _)
  | n + 1, b + 1, hb => by
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    exact succSubL (Nat.le_of_succ_le_succ hb)

/-- The run's count is invariant under the depth reversal. -/
private theorem sumTo_revL (c : Nat → Nat) :
    ∀ n : Nat, sumToL (fun b => c (n - b)) (n + 1)
      = sumToL c (n + 1)
  | 0 => rfl
  | n + 1 => by
    have hcut : sumToL (fun b => c (n + 1 - b)) (n + 1)
        = sumToL (fun b => c (n - b + 1)) (n + 1) :=
      sumTo_congrL _ _ (n + 1)
        (fun b hb => congrArg c (succSubL (Nat.le_of_lt_succ hb)))
    show c (n + 1 - (n + 1))
        + sumToL (fun b => c (n + 1 - b)) (n + 1)
      = c (n + 1) + sumToL c (n + 1)
    rw [Nat.sub_self, hcut,
      sumTo_revL (fun x => c (x + 1)) n]
    exact (sumTo_peelL c (n + 1)).symm

/-- The depth's pick at a content: the member's coordinates when
its content is the key, the empty family otherwise —
`membersAt`'s own spine per depth. -/
private def depthPickL (i j : Nat) (str : PairString)
    (nu : List Nat) (b : Nat) : elim.Mat :=
  if (memberAt i j str b).content = nu
  then [(memberAt i j str b).coords] else []

/-- The depth run's reversal at a string's own gap: the deep
member's content is the shallow member's under the letter
transposition, the two identities the gap's own join. -/
private theorem member_mirrorL (i j : Nat) (hij : ¬ i = j)
    (str : PairString)
    (hgap : ground.getAt 0 str.top.content i
      = ground.getAt 0 str.top.content j + str.ht)
    (hi : i < str.top.content.length)
    (hj : j < str.top.content.length)
    (b : Nat) (hb : b ≤ str.ht) :
    (memberAt i j str (str.ht - b)).content
      = swapPair i j (memberAt i j str b).content := by
  have hB := iterAct_content i j hij b str.top str.ht hgap hb hi hj
  have hM := iterAct_content i j hij (str.ht - b) str.top str.ht
    hgap (Nat.sub_le str.ht b) hi hj
  have hiB : i < (memberAt i j str b).content.length := by
    show i < (iterAct i j b str.top).content.length
    rw [hB.1]
    exact hi
  have hjB : j < (memberAt i j str b).content.length := by
    show j < (iterAct i j b str.top).content.length
    rw [hB.1]
    exact hj
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · show (iterAct i j (str.ht - b) str.top).content.length
      = (swapPair i j (memberAt i j str b).content).length
    rw [length_swapPair, hM.1]
    show str.top.content.length
      = (iterAct i j b str.top).content.length
    rw [hB.1]
  · intro t ht
    show ground.getAt 0 (iterAct i j (str.ht - b) str.top).content t
      = ground.getAt 0
        (swapPair i j (memberAt i j str b).content) t
    by_cases hti : t = i
    · rw [hti, getAt_swapPair_fst _ hij hiB hjB]
      show ground.getAt 0
          (iterAct i j (str.ht - b) str.top).content i
        = ground.getAt 0 (iterAct i j b str.top).content j
      rw [hB.2.2.1]
      refine ground.addCancelR (str.ht - b) ?_
      rw [hM.2.1, hgap, Nat.add_assoc,
        ground.natAddSubCancel hb]
    · by_cases htj : t = j
      · rw [htj, getAt_swapPair_snd _ hij hiB hjB]
        show ground.getAt 0
            (iterAct i j (str.ht - b) str.top).content j
          = ground.getAt 0 (iterAct i j b str.top).content i
        rw [hM.2.2.1]
        refine ground.addCancelR b ?_
        rw [hB.2.1, hgap, Nat.add_assoc, Nat.add_comm (str.ht - b) b,
          ground.natAddSubCancel hb]
      · rw [getAt_swapPair_ne _ hiB hjB hti htj]
        show ground.getAt 0
            (iterAct i j (str.ht - b) str.top).content t
          = ground.getAt 0 (iterAct i j b str.top).content t
        rw [hM.2.2.2 t hti htj, hB.2.2.2 t hti htj]

/-- One string's picks at a content and at its transposition are
equinumerous, the depth run's own reversal. -/
private theorem string_mirrorL (i j : Nat) (hij : ¬ i = j)
    (str : PairString)
    (hgap : ground.getAt 0 str.top.content i
      = ground.getAt 0 str.top.content j + str.ht)
    (hi : i < str.top.content.length)
    (hj : j < str.top.content.length) (nu : List Nat) :
    ((List.range (str.ht + 1)).flatMap
        (depthPickL i j str (swapPair i j nu))).length
      = ((List.range (str.ht + 1)).flatMap
        (depthPickL i j str nu)).length := by
  rw [rangeLenL, rangeLenL]
  refine Eq.trans (sumTo_congrL _
    (fun b => (depthPickL i j str nu (str.ht - b)).length)
    (str.ht + 1) ?_)
    (sumTo_revL (fun x => (depthPickL i j str nu x).length) str.ht)
  intro b hb
  have hmir := member_mirrorL i j hij str hgap hi hj b
    (Nat.le_of_lt_succ hb)
  have hback : (memberAt i j str b).content
      = swapPair i j (memberAt i j str (str.ht - b)).content := by
    rw [hmir, swapPair_swapPair]
  show (depthPickL i j str (swapPair i j nu) b).length
    = (depthPickL i j str nu (str.ht - b)).length
  show (if (memberAt i j str b).content = swapPair i j nu
      then [(memberAt i j str b).coords] else []).length
    = (if (memberAt i j str (str.ht - b)).content = nu
      then [(memberAt i j str (str.ht - b)).coords] else []).length
  by_cases hg : (memberAt i j str b).content = swapPair i j nu
  · have hg2 : (memberAt i j str (str.ht - b)).content = nu := by
      rw [hmir, hg, swapPair_swapPair]
    rw [if_pos hg, if_pos hg2]
    rfl
  · have hg2 : ¬ (memberAt i j str (str.ht - b)).content = nu :=
      fun he => hg (by rw [hback, he])
    rw [if_neg hg, if_neg hg2]

/-- The collected members at a content and at its transposition
are equinumerous, string by string. -/
private theorem members_mirrorL (i j : Nat) (hij : ¬ i = j)
    (d : Nat) (hi : i < d) (hj : j < d) (nu : List Nat) :
    ∀ strs : List PairString,
      (∀ str ∈ strs, str.top.content.length = d
        ∧ ground.getAt 0 str.top.content i
            = ground.getAt 0 str.top.content j + str.ht) →
      (membersAt i j strs (swapPair i j nu)).length
        = (membersAt i j strs nu).length
  | [], _ => rfl
  | str :: t, hgood => by
    have hread := hgood str (List.Mem.head t)
    have hic : i < str.top.content.length := by
      rw [hread.1]
      exact hi
    have hjc : j < str.top.content.length := by
      rw [hread.1]
      exact hj
    show ((List.range (str.ht + 1)).flatMap
          (depthPickL i j str (swapPair i j nu))
        ++ membersAt i j t (swapPair i j nu)).length
      = ((List.range (str.ht + 1)).flatMap
          (depthPickL i j str nu)
        ++ membersAt i j t nu).length
    rw [ground.length_append, ground.length_append,
      string_mirrorL i j hij str hread.2 hic hjc nu,
      members_mirrorL i j hij d hi hj nu t
        (fun s hs => hgood s (List.Mem.tail str hs))]

/-- `lem:strings`' content symmetry at the block span: the
occupied contents' multiplicities are invariant under every
letter transposition — the string count reads the occupancy at
both keys (`walk_count`) and the depth run's reversal matches
the two collections member for member, so `thm:weylchar`'s
reflection hypothesis is the span's own read. -/
theorem symRead_def (lam : Shape) :
    weylchar.symRead lam.length
      ((blockSpan lam).map HVec.content) := by
  intro nu _ i hi j hj
  have hspan : ∀ x : List Nat,
      ground.countOf x ((blockSpan lam).map HVec.content)
        = occupancyAt (blockSpan lam) x := blockcount.span_countOf lam
  by_cases hij : i = j
  · rw [hij]
    show ground.countOf (swapPair j j nu)
        ((blockSpan lam).map HVec.content)
      = ground.countOf nu ((blockSpan lam).map HVec.content)
    rw [show swapPair j j nu = nu from by
      show (if j < j then _ else if j < j then _ else nu) = nu
      rw [if_neg (Nat.lt_irrefl j), if_neg (Nat.lt_irrefl j)]]
  · rw [hspan (swapPair i j nu), hspan nu,
      ← walk_count lam i j hi hj hij (swapPair i j nu),
      ← walk_count lam i j hi hj hij nu]
    exact members_mirrorL i j hij lam.length hi hj nu
      (walk i j (blockSpan lam))
      (fun str hstr =>
        ⟨(walk_good lam i j hi hj hij str hstr).2.1,
          (walk_good lam i j hi hj hij str hstr).2.2.1⟩)


/-! `lem:casimir`'s trace collection at the exhaustion: the trace
recursion's per-pair identity read string by string.  The tex's
clause — "per string one identity: an α-string through ν at depth
j from its top reads the trace coefficient (j+1)d + j(d+1) at the
tie d+q = p+j, its moved reads collect at 2Σ_{l≤j}(p+2l) =
2j(d+1)+2j·q, the two folds one gap identity, and a string above ν
sums its moved reads to equal members, the depth pairs at the join
swapping members" — lands as `stringCollect`.  The multiplicity is
the string count at every content (`blockcount.span_countOf` into
`walk_count`), so every member of the display is a fold over the
exhaustion: the side weights along `weightList`'s own spine, the
moved folds by the fold exchange (the scalar pass into
`famFold_swap`), and the two letters' counts by the scalar pass —
one identity per string closing them member by member.  Per string
the trichotomy is one hit read: a content either sits on the
string's ladder line at a stated depth (`onLineL`, its depth the
content's own by `line_keyL`) or no member of the string meets it
or its moves at all.  On the line the hit is the depth join
`b + l = k` (`hit_iffL`), so a through content (`k ≤ h`) picks its
own depth once, its moved reads run the shifts `1 ≤ l ≤ k` and the
gap identity closes at the join `ν_i + k = ν_j + (h-k)`; a content
below the ladder (`h < k`) picks nothing, its moved reads run the
whole ladder once, and the two folds are equal at the depth run's
reversal (`sumTo_revL`), the paired depths at the join summing to
equal members.  Off the line every read is the count's unit and
the identity is the unit's.  The run kit beneath them is the depth
fold's own — the family fold at a range, the run's vanishing,
truncation, shift, constant and one-depth reads, and the shift
run's triangle. -/

/-- A flattened family's box fold collects member by member. -/
private theorem sumNat_flatL {α : Type} (g : α → List Nat)
    (l : List α) :
    sumNat (l.flatMap g)
      = ground.famFold Nat.add 0 (fun x => sumNat (g x)) l :=
  ground.famFold_flatMap (fun x => x) g l

/-- The range's family fold is the run's collected count. -/
private theorem rangeFoldL (F : Nat → Nat) :
    ∀ n : Nat, ground.famFold Nat.add 0 F (List.range n) = sumToL F n
  | 0 => rfl
  | n + 1 => by
    rw [ground.range_succ n,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
        (List.range n) [n]]
    show ground.famFold Nat.add 0 F (List.range n) + (F n + 0)
      = F n + sumToL F n
    rw [Nat.add_zero, rangeFoldL F n, Nat.add_comm]

/-- The run's count is the unit at a vanishing family. -/
private theorem sumTo_zeroL (c : Nat → Nat) :
    ∀ n : Nat, (∀ b, b < n → c b = 0) → sumToL c n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show c n + sumToL c n = 0
    rw [h n (Nat.lt_succ_self n),
      sumTo_zeroL c n
        (fun b hb => h b (Nat.lt_trans hb (Nat.lt_succ_self n)))]

/-- A vanishing count vanishes at every depth of the run. -/
private theorem sumTo_memL (c : Nat → Nat) :
    ∀ n : Nat, sumToL c n = 0 → ∀ b, b < n → c b = 0
  | 0, _, _, hb => absurd hb (Nat.not_lt_zero _)
  | n + 1, h0, b, hb => by
    have hs : c n + sumToL c n = 0 := h0
    match Nat.lt_or_ge b n with
    | .inl hlt =>
      exact sumTo_memL c n ((ground.addZeroN hs).2) b hlt
    | .inr hge =>
      rw [Nat.le_antisymm (Nat.le_of_lt_succ hb) hge]
      exact (ground.addZeroN (a := sumToL c n)
        (by rw [Nat.add_comm]; exact hs)).2

/-- A positive count names a depth carrying it. -/
private theorem sumTo_posL (c : Nat → Nat) :
    ∀ n : Nat, 0 < sumToL c n → ∃ b, b < n ∧ 0 < c b
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, h => by
    match Nat.eq_zero_or_pos (c n) with
    | .inr hp => exact ⟨n, Nat.lt_succ_self n, hp⟩
    | .inl hz =>
      have he : sumToL c (n + 1) = sumToL c n := by
        show c n + sumToL c n = sumToL c n
        rw [hz, Nat.zero_add]
      have hs : 0 < sumToL c n := by
        rw [← he]
        exact h
      match sumTo_posL c n hs with
      | ⟨b, hb, hcb⟩ =>
        exact ⟨b, Nat.lt_trans hb (Nat.lt_succ_self n), hcb⟩

/-- The run's count truncates where its family vanishes. -/
private theorem sumTo_truncL (c : Nat → Nat) (m : Nat) :
    ∀ n : Nat, m ≤ n → (∀ l, m ≤ l → l < n → c l = 0) →
      sumToL c n = sumToL c m
  | 0, hm, _ => by rw [Nat.le_antisymm hm (Nat.zero_le m)]
  | n + 1, hm, h => by
    match Nat.lt_or_ge n m with
    | .inl hlt => rw [Nat.le_antisymm hm hlt]
    | .inr hge =>
      show c n + sumToL c n = sumToL c m
      rw [h n hge (Nat.lt_succ_self n), Nat.zero_add,
        sumTo_truncL c m n hge
          (fun l hl hln =>
            h l hl (Nat.lt_trans hln (Nat.lt_succ_self n)))]

/-- The run's count splits at a starting depth. -/
private theorem sumTo_shiftL (c : Nat → Nat) (A : Nat) :
    ∀ m : Nat, sumToL c (A + m)
      = sumToL (fun t => c (A + t)) m + sumToL c A
  | 0 => by
    show sumToL c (A + 0) = 0 + sumToL c A
    rw [Nat.add_zero, Nat.zero_add]
  | m + 1 => by
    show c (A + m) + sumToL c (A + m)
      = c (A + m) + sumToL (fun t => c (A + t)) m + sumToL c A
    rw [sumTo_shiftL c A m, Nat.add_assoc]

/-- The run's count at a constant family. -/
private theorem sumTo_constL (k : Nat) :
    ∀ n : Nat, sumToL (fun _ => k) n = n * k
  | 0 => (Nat.zero_mul k).symm
  | n + 1 => by
    show k + sumToL (fun _ => k) n = (n + 1) * k
    rw [sumTo_constL k n, ground.mulAddR n 1 k, Nat.one_mul,
      Nat.add_comm]

/-- The run's count splits over a pointwise sum. -/
private theorem sumTo_addL (c e : Nat → Nat) :
    ∀ n : Nat, sumToL (fun b => c b + e b) n
      = sumToL c n + sumToL e n
  | 0 => rfl
  | n + 1 => by
    show c n + e n + sumToL (fun b => c b + e b) n
      = c n + sumToL c n + (e n + sumToL e n)
    rw [sumTo_addL c e n, Nat.add_assoc (c n) (e n),
      Nat.add_assoc (c n) (sumToL c n),
      Nat.add_left_comm (e n) (sumToL c n) (sumToL e n)]

/-- The run's count at a one-depth family. -/
private theorem sumTo_pickL (c : Nat → Nat) (k : Nat) :
    ∀ n : Nat, k < n →
      sumToL (fun b => if b = k then c b else 0) n = c k
  | 0, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hk => by
    show (if n = k then c n else 0)
        + sumToL (fun b => if b = k then c b else 0) n = c k
    match Nat.lt_or_ge k n with
    | .inl hlt =>
      have hne : ¬ n = k := fun he => by
        rw [he] at hlt
        exact absurd hlt (Nat.lt_irrefl k)
      rw [if_neg hne, Nat.zero_add, sumTo_pickL c k n hlt]
    | .inr hge =>
      have hkn : k = n := Nat.le_antisymm (Nat.le_of_lt_succ hk) hge
      rw [sumTo_zeroL _ n (fun b hb => if_neg (fun he => by
          rw [he, hkn] at hb
          exact absurd hb (Nat.lt_irrefl n))),
        Nat.add_zero, if_pos hkn.symm, hkn]

/-- The shift fold's triangle: the run's doubled shifts. -/
private theorem triangleL :
    ∀ n : Nat, sumToL (fun l => 2 * (l + 1)) n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    show 2 * (n + 1) + sumToL (fun l => 2 * (l + 1)) n
      = (n + 1) * (n + 2)
    rw [triangleL n, Nat.mul_comm (n + 1) (n + 2),
      ground.mulAddR n 2 (n + 1), Nat.add_comm]

/-- The hit count at a shift: one depth of the run meets the moved
content when the join lands inside it. -/
private theorem hitOneL (m k : Nat) (hmk : m ≤ k) :
    ∀ n : Nat, k - m < n →
      sumToL (fun b => if b + m = k then 1 else 0) n = 1 := by
  intro n hn
  have hcong : ∀ b, b < n →
      (if b + m = k then 1 else 0) = (if b = k - m then 1 else 0) := by
    intro b _
    by_cases hb : b + m = k
    · rw [if_pos hb, if_pos (show b = k - m from by
        rw [← hb, Nat.add_comm b m, addSubSelfL m b])]
    · rw [if_neg hb, if_neg (fun he => hb (by
        rw [he, ground.subAdd hmk]))]
  rw [sumTo_congrL _ _ n hcong, sumTo_pickL (fun _ => 1) (k - m) n hn]

/-- The hit count is the unit where the join misses the run. -/
private theorem hitZeroL (m k : Nat) (n : Nat)
    (h : ∀ b, b < n → ¬ (b + m = k)) :
    sumToL (fun b => if b + m = k then 1 else 0) n = 0 :=
  sumTo_zeroL _ n (fun b hb => if_neg (h b hb))

/-- The through content's gap identity: at the string's own join the
depth's two trace coefficients with its moved reads' collection
close against the two letters' counts. -/
private theorem caseAArithL (b g p q : Nat) (hjoin : p + b = q + g) :
    (b + 1) * g + b * (g + 1) + 2 * (b * q) + 1 * q
      = 2 * (b * p + b * (b + 1)) + 1 * p := by
  have hbm : b * p + b * b = b * q + b * g := by
    have hc : b * (p + b) = b * (q + g) :=
      congrArg (fun z => b * z) hjoin
    rw [Nat.left_distrib b p b, Nat.left_distrib b q g] at hc
    exact hc
  have hsum : g + b + q = b + b + p := by
    rw [Nat.add_right_comm g b q, Nat.add_comm g q, ← hjoin,
      Nat.add_comm p b, Nat.add_right_comm b p b]
  have hL : (b + 1) * g + b * (g + 1) + 2 * (b * q) + 1 * q
      = b * g + b * g + (b * q + b * q) + (g + b + q) := by
    rw [ground.mulAddR b 1 g, Nat.one_mul, Nat.mul_succ b g,
      Nat.two_mul (b * q), Nat.one_mul,
      Nat.add_add_add_comm (b * g) g (b * g) b,
      Nat.add_assoc (b * g + b * g) (g + b) (b * q + b * q),
      Nat.add_comm (g + b) (b * q + b * q),
      ← Nat.add_assoc (b * g + b * g) (b * q + b * q) (g + b),
      Nat.add_assoc (b * g + b * g + (b * q + b * q)) (g + b) q]
  have hR : 2 * (b * p + b * (b + 1)) + 1 * p
      = b * g + b * g + (b * q + b * q) + (b + b + p) := by
    rw [Nat.mul_succ b b, ← Nat.add_assoc (b * p) (b * b) b, hbm,
      Nat.two_mul (b * q + b * g + b), Nat.one_mul,
      Nat.add_add_add_comm (b * q + b * g) b (b * q + b * g) b,
      Nat.add_add_add_comm (b * q) (b * g) (b * q) (b * g),
      Nat.add_comm (b * q + b * q) (b * g + b * g),
      Nat.add_assoc (b * g + b * g + (b * q + b * q)) (b + b) p]
  rw [hL, hR, hsum]

/-- The string above the content: the moved reads at two depths
joining to the run's own height sum to equal members. -/
private theorem caseBArithL (p q A t u K : Nat)
    (hA : A + (t + u) + 1 = K) (hjoin : p + (A + 1) + K = q) :
    (p + 2 * (A + t + 1)) + (p + 2 * (A + u + 1)) = 2 * q := by
  have hpair : (A + t + 1) + (A + u + 1) = A + 1 + K := by
    rw [← hA, Nat.add_assoc A t 1, Nat.add_assoc A u 1,
      Nat.add_add_add_comm A (t + 1) A (u + 1),
      Nat.add_assoc A A (t + 1 + (u + 1)), Nat.add_add_add_comm t 1 u 1,
      Nat.add_add_add_comm A 1 (A + (t + u)) 1,
      ← Nat.add_assoc A (t + u) (1 + 1),
      ← Nat.add_assoc A (A + (t + u)) (1 + 1)]
  rw [Nat.add_add_add_comm p (2 * (A + t + 1)) p (2 * (A + u + 1)),
    ← Nat.left_distrib 2 (A + t + 1) (A + u + 1), hpair,
    ← Nat.two_mul p, ← Nat.left_distrib 2 p (A + 1 + K),
    ← Nat.add_assoc p (A + 1) K, hjoin]

open strings blockcount

/-- The depth's pick at a content: the run's member test at the
depth, the count's unit off it. -/
private def pickAtL (i j : Nat) (str : PairString) (nu : List Nat)
    (b : Nat) : Nat :=
  if (memberAt i j str b).content = nu then 1 else 0

/-- The string's pick count at a content: the depth run's
collected member tests. -/
private def pickL (i j : Nat) (str : PairString)
    (nu : List Nat) : Nat :=
  sumToL (pickAtL i j str nu) (str.ht + 1)

/-- The depth's weight at a content: the stated coefficient at
the run's member test. -/
private def wtAtL (i j : Nat) (f : Nat → Nat → Nat) (str : PairString)
    (nu : List Nat) (b : Nat) : Nat :=
  if (memberAt i j str b).content = nu then f str.ht b else 0

/-- The string's weight at a content: the depth run's collected
coefficients. -/
private def wtL (i j : Nat) (f : Nat → Nat → Nat) (str : PairString)
    (nu : List Nat) : Nat :=
  sumToL (wtAtL i j f str nu) (str.ht + 1)

/-- The string's moved fold at the second letter's weight,
`weylchar.gSnd`'s own summand per string. -/
private def gSndL (i j : Nat) (str : PairString)
    (nu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun l => ground.getAt 0 nu j
      * pickL i j str (weylchar.moveBy i j l nu))
    ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1))

/-- The string's moved fold at the shifted first letter's weight,
`weylchar.gFst`'s own summand per string. -/
private def gFstL (i j : Nat) (str : PairString)
    (nu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun l => (ground.getAt 0 nu i + 2 * l)
      * pickL i j str (weylchar.moveBy i j l nu))
    ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1))

/-- The second letter's moved fold reads the shift run. -/
private theorem gSnd_sumL (i j : Nat) (str : PairString)
    (nu : List Nat) :
    gSndL i j str nu
      = sumToL (fun t => ground.getAt 0 nu j
          * pickL i j str (weylchar.moveBy i j (t + 1) nu))
        (ground.getAt 0 nu j) := by
  show ground.famFold Nat.add 0
    (fun l => ground.getAt 0 nu j
      * pickL i j str (weylchar.moveBy i j l nu))
    ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1)) = _
  rw [ground.famFold_map Nat.add 0
      (fun l => ground.getAt 0 nu j
        * pickL i j str (weylchar.moveBy i j l nu))
      (fun l => l + 1) (List.range (ground.getAt 0 nu j)),
    rangeFoldL]

/-- The first letter's moved fold reads the shift run. -/
private theorem gFst_sumL (i j : Nat) (str : PairString)
    (nu : List Nat) :
    gFstL i j str nu
      = sumToL (fun t => (ground.getAt 0 nu i + 2 * (t + 1))
          * pickL i j str (weylchar.moveBy i j (t + 1) nu))
        (ground.getAt 0 nu j) := by
  show ground.famFold Nat.add 0
    (fun l => (ground.getAt 0 nu i + 2 * l)
      * pickL i j str (weylchar.moveBy i j l nu))
    ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1)) = _
  rw [ground.famFold_map Nat.add 0
      (fun l => (ground.getAt 0 nu i + 2 * l)
        * pickL i j str (weylchar.moveBy i j l nu))
      (fun l => l + 1) (List.range (ground.getAt 0 nu j)),
    rangeFoldL]

/-- The string's line at a content: the content sits on the top's
own ladder at a stated depth — the first letter's count the
top's lowered by it, the second's the top's raised, every
further letter the top's. -/
private def onLineL (i j : Nat) (str : PairString) (nu : List Nat)
    (k : Nat) : Prop :=
  ground.getAt 0 nu i + k = ground.getAt 0 str.top.content i
    ∧ ground.getAt 0 nu j = ground.getAt 0 str.top.content j + k
    ∧ ∀ x, ¬ x = i → ¬ x = j →
        ground.getAt 0 nu x = ground.getAt 0 str.top.content x

/-- The line's depth is the content's own: two lines at one
content name one depth. -/
private theorem line_keyL (i j : Nat) (str : PairString) (nu : List Nat)
    {k k' : Nat} (hk : onLineL i j str nu k)
    (hk' : onLineL i j str nu k') : k = k' :=
  ground.addCancelL _ (hk.2.1.symm.trans hk'.2.1)

/-- The member's content at a depth reads a stated content exactly
at the depth's own three letter reads. -/
private theorem member_readsL (i j : Nat) (hij : ¬ i = j) (d : Nat)
    (hi : i < d) (hj : j < d) (str : PairString)
    (hlen : str.top.content.length = d)
    (hgap : ground.getAt 0 str.top.content i
      = ground.getAt 0 str.top.content j + str.ht)
    (b : Nat) (hb : b ≤ str.ht) (w : List Nat) (hw : w.length = d) :
    ((memberAt i j str b).content = w
      ↔ (ground.getAt 0 w i + b = ground.getAt 0 str.top.content i
        ∧ ground.getAt 0 w j = ground.getAt 0 str.top.content j + b
        ∧ ∀ x, ¬ x = i → ¬ x = j →
            ground.getAt 0 w x
              = ground.getAt 0 str.top.content x)) := by
  have hiT : i < str.top.content.length := by rw [hlen]; exact hi
  have hjT : j < str.top.content.length := by rw [hlen]; exact hj
  have cy := iterAct_content i j hij b str.top str.ht hgap hb hiT hjT
  constructor
  · intro he
    refine ⟨?_, ?_, ?_⟩
    · rw [← he]
      exact cy.2.1
    · rw [← he]
      exact cy.2.2.1
    · intro x hxi hxj
      rw [← he]
      exact cy.2.2.2 x hxi hxj
  · intro hr
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · show (iterAct i j b str.top).content.length = w.length
      rw [cy.1, hlen, hw]
    · intro t _
      by_cases hti : t = i
      · rw [hti]
        exact ground.addCancelR b (cy.2.1.trans hr.1.symm)
      · by_cases htj : t = j
        · rw [htj]
          show ground.getAt 0 (iterAct i j b str.top).content j
            = ground.getAt 0 w j
          rw [cy.2.2.1]
          exact hr.2.1.symm
        · show ground.getAt 0 (iterAct i j b str.top).content t
            = ground.getAt 0 w t
          rw [cy.2.2.2 t hti htj]
          exact (hr.2.2 t hti htj).symm

/-- The moved content's hit read: on the line the string's member
at a depth is the content's shift exactly at the depth join
`b + l = k`. -/
private theorem hit_iffL (i j : Nat) (hij : ¬ i = j) (d : Nat)
    (hi : i < d) (hj : j < d) (str : PairString)
    (hlen : str.top.content.length = d)
    (hgap : ground.getAt 0 str.top.content i
      = ground.getAt 0 str.top.content j + str.ht)
    (nu : List Nat) (hnulen : nu.length = d) (k : Nat)
    (hline : onLineL i j str nu k) (b l : Nat) (hb : b ≤ str.ht) :
    ((memberAt i j str b).content = weylchar.moveBy i j l nu
      ↔ b + l = k) := by
  have hnui : i < nu.length := by rw [hnulen]; exact hi
  have hnuj : j < nu.length := by rw [hnulen]; exact hj
  have hri : ground.getAt 0 (weylchar.moveBy i j l nu) i
      = ground.getAt 0 nu i + l :=
    weylchar.getAt_moveBy_fst hij l nu hnui
  have hrj : ground.getAt 0 (weylchar.moveBy i j l nu) j
      = ground.getAt 0 nu j - l :=
    weylchar.getAt_moveBy_snd i hij l nu hnuj
  have hmlen : (weylchar.moveBy i j l nu).length = d := by
    rw [weylchar.length_moveBy]
    exact hnulen
  have hiff := member_readsL i j hij d hi hj str hlen hgap b hb
    (weylchar.moveBy i j l nu) hmlen
  constructor
  · intro he
    have h1 := (hiff.mp he).1
    rw [hri] at h1
    refine ground.addCancelL (ground.getAt 0 nu i) ?_
    rw [Nat.add_comm b l, ← Nat.add_assoc, h1, ← hline.1]
  · intro hbl
    refine hiff.mpr ⟨?_, ?_, ?_⟩
    · rw [hri, Nat.add_assoc, Nat.add_comm l b, hbl]
      exact hline.1
    · rw [hrj, hline.2.1, ← hbl, ← Nat.add_assoc,
        Nat.add_comm (ground.getAt 0 str.top.content j + b) l,
        addSubSelfL l (ground.getAt 0 str.top.content j + b)]
    · intro x hxi hxj
      rw [weylchar.getAt_moveBy_ne i j l nu hxi hxj]
      exact hline.2.2 x hxi hxj

/-- A member meeting a moved content puts the content on the
string's own line at the depth join. -/
private theorem line_ofHitL (i j : Nat) (hij : ¬ i = j) (d : Nat)
    (hi : i < d) (hj : j < d) (str : PairString)
    (hlen : str.top.content.length = d)
    (hgap : ground.getAt 0 str.top.content i
      = ground.getAt 0 str.top.content j + str.ht)
    (nu : List Nat) (hnulen : nu.length = d) (b l : Nat)
    (hb : b ≤ str.ht) (hl : l ≤ ground.getAt 0 nu j)
    (hhit : (memberAt i j str b).content
      = weylchar.moveBy i j l nu) :
    onLineL i j str nu (b + l) := by
  have hnui : i < nu.length := by rw [hnulen]; exact hi
  have hnuj : j < nu.length := by rw [hnulen]; exact hj
  have hmlen : (weylchar.moveBy i j l nu).length = d := by
    rw [weylchar.length_moveBy]
    exact hnulen
  have hr := (member_readsL i j hij d hi hj str hlen hgap b hb
    (weylchar.moveBy i j l nu) hmlen).mp hhit
  have h1 := hr.1
  have h2 := hr.2.1
  rw [weylchar.getAt_moveBy_fst hij l nu hnui] at h1
  rw [weylchar.getAt_moveBy_snd i hij l nu hnuj] at h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm b l, ← Nat.add_assoc]
    exact h1
  · have h4 : ground.getAt 0 nu j
        = l + (ground.getAt 0 str.top.content j + b) := by
      rw [← h2]
      exact (ground.natAddSubCancel hl).symm
    rw [h4, Nat.add_comm l (ground.getAt 0 str.top.content j + b),
      Nat.add_assoc]
  · intro x hxi hxj
    rw [← weylchar.getAt_moveBy_ne i j l nu hxi hxj]
    exact hr.2.2 x hxi hxj

/-- A carried depth pick names the member's own content. -/
private theorem pick_hitL (i j : Nat) (str : PairString) (nu : List Nat)
    (b : Nat) (hb : 0 < pickAtL i j str nu b) :
    (memberAt i j str b).content = nu := by
  by_cases hg : (memberAt i j str b).content = nu
  · exact hg
  · have h0 : pickAtL i j str nu b = 0 :=
      show (if (memberAt i j str b).content = nu then (1 : Nat)
        else 0) = 0 from if_neg hg
    rw [h0] at hb
    exact absurd hb (Nat.lt_irrefl 0)

/-- A carried string pick names a depth meeting the content. -/
private theorem pickL_hitL (i j : Nat) (str : PairString)
    (nu : List Nat) (hb : 0 < pickL i j str nu) :
    ∃ b, b ≤ str.ht ∧ (memberAt i j str b).content = nu := by
  match sumTo_posL (pickAtL i j str nu) (str.ht + 1) hb with
  | ⟨b, hlt, hpos⟩ =>
    exact ⟨b, Nat.le_of_lt_succ hlt, pick_hitL i j str nu b hpos⟩

/-- The unit joins collapse: a value between the count's
units is its own. -/
private theorem zeroCollapseL (X : Nat) : 0 + 0 + X + 0 = X :=
  Nat.zero_add X

/-- The shift run's closed form: the weighted shifts collect at
the run's own triangle. -/
private theorem shiftSumL (p n : Nat) :
    sumToL (fun t => p + 2 * (t + 1)) n = n * p + n * (n + 1) := by
  have h := sumTo_addL (fun _ => p) (fun t => 2 * (t + 1)) n
  rw [sumTo_constL, triangleL] at h
  exact h

/-- `lem:casimir`'s per-string identity: at one good string the two
side weights with the moved folds close against the two
letters' counts at the string's own pick — a through content at
its depth's gap identity `ν_i + k = ν_j + (h-k)`, a content
below the ladder at the depth run's reversal with the paired
depths summing to equal members, and every further content at
the count's unit. -/
private theorem stringIdL (i j : Nat) (hij : ¬ i = j) (d : Nat)
    (hi : i < d) (hj : j < d) (str : PairString)
    (hlen : str.top.content.length = d)
    (hgap : ground.getAt 0 str.top.content i
      = ground.getAt 0 str.top.content j + str.ht)
    (nu : List Nat) (hnulen : nu.length = d) :
    wtL i j (fun ht b => (b + 1) * (ht - b)) str nu
        + wtL i j (fun ht b => b * (ht - b + 1)) str nu
        + 2 * gSndL i j str nu
        + pickL i j str nu * ground.getAt 0 nu j
      = 2 * gFstL i j str nu
        + pickL i j str nu * ground.getAt 0 nu i := by
  have hgS := gSnd_sumL i j str nu
  have hgF := gFst_sumL i j str nu
  match Nat.eq_zero_or_pos (pickL i j str nu
      + sumToL (fun t =>
          pickL i j str (weylchar.moveBy i j (t + 1) nu))
        (ground.getAt 0 nu j)) with
  | .inl hz =>
    have hz1 : pickL i j str nu = 0 := (ground.addZeroN hz).1
    have hz2 : sumToL (fun t =>
        pickL i j str (weylchar.moveBy i j (t + 1) nu))
        (ground.getAt 0 nu j) = 0 := (ground.addZeroN hz).2
    have hzt := sumTo_memL _ _ hz2
    have hnog : ∀ b, b < str.ht + 1 →
        ¬ (memberAt i j str b).content = nu := by
      intro b hb he
      have h0 : (if (memberAt i j str b).content = nu then (1 : Nat)
          else 0) = 0 :=
        sumTo_memL (pickAtL i j str nu) (str.ht + 1) hz1 b hb
      rw [if_pos he] at h0
      exact Nat.noConfusion h0
    have hwt : ∀ f : Nat → Nat → Nat, wtL i j f str nu = 0 := by
      intro f
      show sumToL (wtAtL i j f str nu) (str.ht + 1) = 0
      exact sumTo_zeroL _ (str.ht + 1) (fun b hb =>
        show (if (memberAt i j str b).content = nu then f str.ht b
          else 0) = 0 from if_neg (hnog b hb))
    have hgS0 : gSndL i j str nu = 0 := by
      rw [hgS]
      exact sumTo_zeroL _ _ (fun t ht => by
        show ground.getAt 0 nu j
            * pickL i j str (weylchar.moveBy i j (t + 1) nu) = 0
        rw [hzt t ht, Nat.mul_zero])
    have hgF0 : gFstL i j str nu = 0 := by
      rw [hgF]
      exact sumTo_zeroL _ _ (fun t ht => by
        show (ground.getAt 0 nu i + 2 * (t + 1))
            * pickL i j str (weylchar.moveBy i j (t + 1) nu) = 0
        rw [hzt t ht, Nat.mul_zero])
    rw [hwt, hwt, hz1, hgS0, hgF0,
      Nat.zero_mul (ground.getAt 0 nu j),
      Nat.zero_mul (ground.getAt 0 nu i), Nat.mul_zero 2]
  | .inr hp =>
    have hline : ∃ k, onLineL i j str nu k := by
      match Nat.eq_zero_or_pos (pickL i j str nu) with
      | .inr hpk =>
        match pickL_hitL i j str nu hpk with
        | ⟨b, hb, hhit⟩ =>
          exact ⟨b, (member_readsL i j hij d hi hj str hlen hgap b
            hb nu hnulen).mp hhit⟩
      | .inl hzk =>
        have h2 : 0 < sumToL (fun t =>
            pickL i j str (weylchar.moveBy i j (t + 1) nu))
            (ground.getAt 0 nu j) := by
          rw [hzk, Nat.zero_add] at hp
          exact hp
        match sumTo_posL _ _ h2 with
        | ⟨t, htlt, htpos⟩ =>
          match pickL_hitL i j str
              (weylchar.moveBy i j (t + 1) nu) htpos with
          | ⟨b, hb, hhit⟩ =>
            exact ⟨b + (t + 1), line_ofHitL i j hij d hi hj str hlen
              hgap nu hnulen b (t + 1) hb htlt hhit⟩
    match hline with
    | ⟨k, hk⟩ =>
      have hguard : ∀ b, b ≤ str.ht →
          ((memberAt i j str b).content = nu ↔ b = k) := by
        intro b hb
        constructor
        · intro he
          exact line_keyL i j str nu
            ((member_readsL i j hij d hi hj str hlen hgap b hb nu
              hnulen).mp he) hk
        · intro hbk
          refine (member_readsL i j hij d hi hj str hlen hgap b hb
            nu hnulen).mpr ?_
          rw [hbk]
          exact hk
      have hpickAt : ∀ b, b ≤ str.ht →
          pickAtL i j str nu b = if b = k then 1 else 0 := by
        intro b hb
        show (if (memberAt i j str b).content = nu then (1 : Nat)
          else 0) = if b = k then 1 else 0
        by_cases hbk : b = k
        · rw [if_pos ((hguard b hb).mpr hbk), if_pos hbk]
        · rw [if_neg (fun he => hbk ((hguard b hb).mp he)),
            if_neg hbk]
      have hwtAt : ∀ (f : Nat → Nat → Nat) b, b ≤ str.ht →
          wtAtL i j f str nu b
            = if b = k then f str.ht b else 0 := by
        intro f b hb
        show (if (memberAt i j str b).content = nu then f str.ht b
          else 0) = if b = k then f str.ht b else 0
        by_cases hbk : b = k
        · rw [if_pos ((hguard b hb).mpr hbk), if_pos hbk]
        · rw [if_neg (fun he => hbk ((hguard b hb).mp he)),
            if_neg hbk]
      have hpickMove : ∀ l,
          pickL i j str (weylchar.moveBy i j l nu)
            = sumToL (fun b => if b + l = k then 1 else 0)
              (str.ht + 1) := by
        intro l
        show sumToL (pickAtL i j str (weylchar.moveBy i j l nu))
          (str.ht + 1) = _
        refine sumTo_congrL _ _ (str.ht + 1) (fun b hb => ?_)
        show (if (memberAt i j str b).content
            = weylchar.moveBy i j l nu then (1 : Nat) else 0)
          = if b + l = k then 1 else 0
        by_cases hbl : b + l = k
        · rw [if_pos ((hit_iffL i j hij d hi hj str hlen hgap nu
              hnulen k hk b l (Nat.le_of_lt_succ hb)).mpr hbl),
            if_pos hbl]
        · rw [if_neg (fun he => hbl ((hit_iffL i j hij d hi hj str
              hlen hgap nu hnulen k hk b l
              (Nat.le_of_lt_succ hb)).mp he)), if_neg hbl]
      have hknu : k ≤ ground.getAt 0 nu j := by
        rw [hk.2.1]
        exact Nat.le_add_left k _
      match Nat.lt_or_ge str.ht k with
      | .inr hkh =>
        have hkS : k < str.ht + 1 := Nat.lt_succ_of_le hkh
        have hpick1 : pickL i j str nu = 1 := by
          show sumToL (pickAtL i j str nu) (str.ht + 1) = 1
          rw [sumTo_congrL _ (fun b => if b = k then 1 else 0)
              (str.ht + 1)
              (fun b hb => hpickAt b (Nat.le_of_lt_succ hb)),
            sumTo_pickL (fun _ => 1) k (str.ht + 1) hkS]
        have hwt1 : ∀ f : Nat → Nat → Nat,
            wtL i j f str nu = f str.ht k := by
          intro f
          show sumToL (wtAtL i j f str nu) (str.ht + 1) = f str.ht k
          rw [sumTo_congrL _ (fun b => if b = k then f str.ht b
                else 0) (str.ht + 1)
              (fun b hb => hwtAt f b (Nat.le_of_lt_succ hb)),
            sumTo_pickL (fun b => f str.ht b) k (str.ht + 1) hkS]
        have hmoveA : ∀ t, pickL i j str
            (weylchar.moveBy i j (t + 1) nu)
              = if t + 1 ≤ k then 1 else 0 := by
          intro t
          rw [hpickMove]
          by_cases hle : t + 1 ≤ k
          · rw [if_pos hle]
            exact hitOneL (t + 1) k hle (str.ht + 1)
              (Nat.lt_succ_of_le
                (Nat.le_trans (Nat.sub_le k (t + 1)) hkh))
          · rw [if_neg hle]
            exact hitZeroL (t + 1) k (str.ht + 1) (fun b _ hbe =>
              hle (by
                rw [← hbe]
                exact Nat.le_add_left (t + 1) b))
        have hgS1 : gSndL i j str nu = k * ground.getAt 0 nu j := by
          rw [hgS,
            sumTo_truncL _ k (ground.getAt 0 nu j) hknu
              (fun l hl _ => by
                show ground.getAt 0 nu j
                    * pickL i j str (weylchar.moveBy i j (l + 1) nu)
                  = 0
                rw [hmoveA l, if_neg (fun hc =>
                  absurd (Nat.le_trans hc hl)
                    (Nat.not_succ_le_self l)), Nat.mul_zero]),
            sumTo_congrL _ (fun _ => ground.getAt 0 nu j) k
              (fun t htk => by
                show ground.getAt 0 nu j
                    * pickL i j str (weylchar.moveBy i j (t + 1) nu)
                  = ground.getAt 0 nu j
                rw [hmoveA t, if_pos (show t + 1 ≤ k from htk),
                  Nat.mul_one]),
            sumTo_constL]
        have hgF1 : gFstL i j str nu
            = k * ground.getAt 0 nu i + k * (k + 1) := by
          rw [hgF,
            sumTo_truncL _ k (ground.getAt 0 nu j) hknu
              (fun l hl _ => by
                show (ground.getAt 0 nu i + 2 * (l + 1))
                    * pickL i j str (weylchar.moveBy i j (l + 1) nu)
                  = 0
                rw [hmoveA l, if_neg (fun hc =>
                  absurd (Nat.le_trans hc hl)
                    (Nat.not_succ_le_self l)), Nat.mul_zero]),
            sumTo_congrL _ (fun t => ground.getAt 0 nu i
                + 2 * (t + 1)) k
              (fun t htk => by
                show (ground.getAt 0 nu i + 2 * (t + 1))
                    * pickL i j str (weylchar.moveBy i j (t + 1) nu)
                  = ground.getAt 0 nu i + 2 * (t + 1)
                rw [hmoveA t, if_pos (show t + 1 ≤ k from htk),
                  Nat.mul_one]),
            shiftSumL]
        have hjoinA : ground.getAt 0 nu i + k
            = ground.getAt 0 nu j + (str.ht - k) := by
          rw [hk.1, hgap, hk.2.1, Nat.add_assoc,
            ground.natAddSubCancel hkh]
        rw [hwt1, hwt1, hpick1, hgS1, hgF1]
        exact caseAArithL k (str.ht - k) (ground.getAt 0 nu i)
          (ground.getAt 0 nu j) hjoinA
      | .inl hhk =>
        match Nat.le.dest hhk with
        | ⟨A, hA⟩ =>
          have hAk : A + (str.ht + 1) = k := by
            rw [Nat.add_comm]
            exact hA
          have hbne : ∀ b, b < str.ht + 1 → ¬ b = k := by
            intro b hb hbk
            rw [hbk] at hb
            exact absurd
              (Nat.lt_of_lt_of_le hhk (Nat.le_of_lt_succ hb))
              (Nat.lt_irrefl str.ht)
          have hpick0 : pickL i j str nu = 0 := by
            show sumToL (pickAtL i j str nu) (str.ht + 1) = 0
            exact sumTo_zeroL _ (str.ht + 1) (fun b hb => by
              rw [hpickAt b (Nat.le_of_lt_succ hb),
                if_neg (hbne b hb)])
          have hwt0 : ∀ f : Nat → Nat → Nat,
              wtL i j f str nu = 0 := by
            intro f
            show sumToL (wtAtL i j f str nu) (str.ht + 1) = 0
            exact sumTo_zeroL _ (str.ht + 1) (fun b hb => by
              rw [hwtAt f b (Nat.le_of_lt_succ hb),
                if_neg (hbne b hb)])
          have hmissHi : ∀ t, k ≤ t →
              pickL i j str (weylchar.moveBy i j (t + 1) nu) = 0 := by
            intro t htk
            rw [hpickMove]
            exact hitZeroL (t + 1) k (str.ht + 1) (fun b _ hbe =>
              absurd (Nat.le_trans (show t + 1 ≤ k from by
                  rw [← hbe]
                  exact Nat.le_add_left (t + 1) b) htk)
                (Nat.not_succ_le_self t))
          have hmissLo : ∀ t, t < A →
              pickL i j str (weylchar.moveBy i j (t + 1) nu) = 0 := by
            intro t hlo
            rw [hpickMove]
            refine hitZeroL (t + 1) k (str.ht + 1) (fun b hb hbe => ?_)
            have hbt : b + t = A + str.ht := by
              refine Nat.succ.inj ?_
              show b + t + 1 = A + str.ht + 1
              rw [Nat.add_assoc b t 1, hbe, ← hAk,
                Nat.add_assoc A str.ht 1]
            exact absurd (Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt
                (Nat.add_le_add_right (Nat.le_of_lt_succ hb) t)
                (Nat.add_lt_add_left hlo str.ht))
              (Nat.le_of_eq (Nat.add_comm str.ht A)))
              (by rw [hbt]; exact Nat.lt_irrefl (A + str.ht))
          have hhitW : ∀ s, s ≤ str.ht →
              pickL i j str
                (weylchar.moveBy i j (A + s + 1) nu) = 1 := by
            intro s hs
            have hsh : s + (str.ht - s) = str.ht :=
              ground.natAddSubCancel hs
            have hks : A + s + 1 + (str.ht - s) = k := by
              rw [← hAk, Nat.add_assoc A s 1,
                Nat.add_assoc A (s + 1) (str.ht - s),
                Nat.add_assoc s 1 (str.ht - s),
                Nat.add_comm 1 (str.ht - s),
                ← Nat.add_assoc s (str.ht - s) 1, hsh]
            rw [hpickMove]
            refine hitOneL (A + s + 1) k ?_ (str.ht + 1) ?_
            · rw [← hks]
              exact Nat.le_add_right (A + s + 1) (str.ht - s)
            · rw [← hks, addSubSelfL (A + s + 1) (str.ht - s)]
              exact Nat.lt_succ_of_le (Nat.sub_le str.ht s)
          have hgS1 : gSndL i j str nu
              = (str.ht + 1) * ground.getAt 0 nu j := by
            rw [hgS,
              sumTo_truncL _ (A + (str.ht + 1)) (ground.getAt 0 nu j)
                (by rw [hAk]; exact hknu)
                (fun l hl _ => by
                  show ground.getAt 0 nu j
                      * pickL i j str
                        (weylchar.moveBy i j (l + 1) nu) = 0
                  rw [hmissHi l (by rw [← hAk]; exact hl),
                    Nat.mul_zero]),
              sumTo_shiftL _ A (str.ht + 1),
              sumTo_zeroL _ A (fun t ht => by
                show ground.getAt 0 nu j
                    * pickL i j str
                      (weylchar.moveBy i j (t + 1) nu) = 0
                rw [hmissLo t ht, Nat.mul_zero]),
              Nat.add_zero,
              sumTo_congrL _ (fun _ => ground.getAt 0 nu j)
                (str.ht + 1) (fun s hs => by
                  show ground.getAt 0 nu j
                      * pickL i j str
                        (weylchar.moveBy i j (A + s + 1) nu)
                    = ground.getAt 0 nu j
                  rw [hhitW s (Nat.le_of_lt_succ hs), Nat.mul_one]),
              sumTo_constL]
          have hgF1 : gFstL i j str nu
              = sumToL (fun s => ground.getAt 0 nu i
                  + 2 * (A + s + 1)) (str.ht + 1) := by
            rw [hgF,
              sumTo_truncL _ (A + (str.ht + 1)) (ground.getAt 0 nu j)
                (by rw [hAk]; exact hknu)
                (fun l hl _ => by
                  show (ground.getAt 0 nu i + 2 * (l + 1))
                      * pickL i j str
                        (weylchar.moveBy i j (l + 1) nu) = 0
                  rw [hmissHi l (by rw [← hAk]; exact hl),
                    Nat.mul_zero]),
              sumTo_shiftL _ A (str.ht + 1),
              sumTo_zeroL _ A (fun t ht => by
                show (ground.getAt 0 nu i + 2 * (t + 1))
                    * pickL i j str
                      (weylchar.moveBy i j (t + 1) nu) = 0
                rw [hmissLo t ht, Nat.mul_zero]),
              Nat.add_zero,
              sumTo_congrL _ (fun s => ground.getAt 0 nu i
                  + 2 * (A + s + 1)) (str.ht + 1) (fun s hs => by
                show (ground.getAt 0 nu i + 2 * (A + s + 1))
                    * pickL i j str
                      (weylchar.moveBy i j (A + s + 1) nu)
                  = ground.getAt 0 nu i + 2 * (A + s + 1)
                rw [hhitW s (Nat.le_of_lt_succ hs), Nat.mul_one])]
          have hjoinB : ground.getAt 0 nu i + (A + 1) + k
              = ground.getAt 0 nu j := by
            rw [Nat.add_right_comm (ground.getAt 0 nu i) (A + 1) k,
              hk.1, hgap, hk.2.1, Nat.add_assoc,
              ← hAk, Nat.add_left_comm str.ht A 1]
          have hrev : sumToL (fun s => ground.getAt 0 nu i
                + 2 * (A + (str.ht - s) + 1)) (str.ht + 1)
              = sumToL (fun s => ground.getAt 0 nu i
                + 2 * (A + s + 1)) (str.ht + 1) :=
            sumTo_revL (fun s => ground.getAt 0 nu i
              + 2 * (A + s + 1)) str.ht
          have hsplit : sumToL (fun s =>
                (ground.getAt 0 nu i + 2 * (A + s + 1))
                + (ground.getAt 0 nu i
                  + 2 * (A + (str.ht - s) + 1))) (str.ht + 1)
              = sumToL (fun s => ground.getAt 0 nu i
                  + 2 * (A + s + 1)) (str.ht + 1)
                + sumToL (fun s => ground.getAt 0 nu i
                  + 2 * (A + (str.ht - s) + 1)) (str.ht + 1) :=
            sumTo_addL _ _ (str.ht + 1)
          have hconst : sumToL (fun s =>
                (ground.getAt 0 nu i + 2 * (A + s + 1))
                + (ground.getAt 0 nu i
                  + 2 * (A + (str.ht - s) + 1))) (str.ht + 1)
              = sumToL (fun _ => 2 * ground.getAt 0 nu j)
                (str.ht + 1) :=
            sumTo_congrL _ _ (str.ht + 1) (fun s hs =>
              caseBArithL (ground.getAt 0 nu i)
                (ground.getAt 0 nu j) A s (str.ht - s) k
                (by
                  rw [ground.natAddSubCancel (Nat.le_of_lt_succ hs)]
                  exact hAk)
                hjoinB)
          have hdouble : gFstL i j str nu + gFstL i j str nu
              = (str.ht + 1) * (2 * ground.getAt 0 nu j) := by
            have h1 : gFstL i j str nu + gFstL i j str nu
                = sumToL (fun s => ground.getAt 0 nu i
                    + 2 * (A + s + 1)) (str.ht + 1)
                  + sumToL (fun s => ground.getAt 0 nu i
                    + 2 * (A + (str.ht - s) + 1)) (str.ht + 1) := by
              rw [hgF1, hrev]
            rw [h1, ← hsplit, hconst, sumTo_constL]
          have hLHS : wtL i j (fun ht b => (b + 1) * (ht - b)) str nu
              + wtL i j (fun ht b => b * (ht - b + 1)) str nu
              + 2 * gSndL i j str nu
              + pickL i j str nu * ground.getAt 0 nu j
              = 2 * ((str.ht + 1) * ground.getAt 0 nu j) := by
            rw [hwt0, hwt0, hpick0, hgS1,
              Nat.zero_mul (ground.getAt 0 nu j)]
            exact zeroCollapseL _
          have hRHS : 2 * gFstL i j str nu
              + pickL i j str nu * ground.getAt 0 nu i
              = 2 * gFstL i j str nu := by
            rw [hpick0, Nat.zero_mul (ground.getAt 0 nu i),
              Nat.add_zero]
          rw [hLHS, hRHS,
            Nat.two_mul ((str.ht + 1) * ground.getAt 0 nu j),
            Nat.two_mul (gFstL i j str nu), hdouble,
            Nat.two_mul (ground.getAt 0 nu j),
            Nat.left_distrib (str.ht + 1) (ground.getAt 0 nu j)
              (ground.getAt 0 nu j)]

/-- The family fold's one value at one read per member. -/
private theorem famFold_memL {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) →
      ground.famFold Nat.add 0 f l = ground.famFold Nat.add 0 g l
  | [], _ => rfl
  | a :: t, h => by
    show f a + ground.famFold Nat.add 0 f t
      = g a + ground.famFold Nat.add 0 g t
    rw [h a (List.Mem.head t),
      famFold_memL f g t (fun x hx => h x (List.Mem.tail a hx))]

/-- The depth run's collected members are the string's pick count. -/
private theorem pick_lenL (i j : Nat) (str : PairString)
    (nu : List Nat) :
    ((List.range (str.ht + 1)).flatMap (fun b =>
        if (memberAt i j str b).content = nu
        then [(memberAt i j str b).coords] else [])).length
      = pickL i j str nu := by
  rw [ground.length_flatMap, rangeFoldL]
  refine sumTo_congrL _ _ (str.ht + 1) (fun b _ => ?_)
  show (if (memberAt i j str b).content = nu
      then [(memberAt i j str b).coords] else []).length
    = (if (memberAt i j str b).content = nu then 1 else 0)
  by_cases hg : (memberAt i j str b).content = nu
  · rw [if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg]
    rfl

/-- The collected members' width is the strings' collected picks. -/
private theorem members_foldL (i j : Nat) (strs : List PairString)
    (nu : List Nat) :
    (membersAt i j strs nu).length
      = ground.famFold Nat.add 0 (fun s => pickL i j s nu) strs := by
  show (strs.flatMap (fun s =>
      (List.range (s.ht + 1)).flatMap (fun b =>
        if (memberAt i j s b).content = nu
        then [(memberAt i j s b).coords] else []))).length = _
  rw [ground.length_flatMap]
  exact ground.famFold_congr_all Nat.add 0 _ _
    (fun s => pick_lenL i j s nu) strs

/-- The side weights collect string by string. -/
private theorem weight_foldL (i j : Nat) (f : Nat → Nat → Nat)
    (strs : List PairString) (nu : List Nat) :
    sumNat (weightList i j f strs nu)
      = ground.famFold Nat.add 0 (fun s => wtL i j f s nu) strs := by
  show sumNat (strs.flatMap (fun s =>
      (List.range (s.ht + 1)).flatMap (fun b =>
        if (memberAt i j s b).content = nu then [f s.ht b]
        else []))) = _
  rw [sumNat_flatL]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun s => ?_) strs
  show sumNat ((List.range (s.ht + 1)).flatMap (fun b =>
      if (memberAt i j s b).content = nu then [f s.ht b] else []))
    = wtL i j f s nu
  rw [sumNat_flatL, rangeFoldL]
  refine sumTo_congrL _ _ (s.ht + 1) (fun b _ => ?_)
  show sumNat (if (memberAt i j s b).content = nu then [f s.ht b]
      else [])
    = (if (memberAt i j s b).content = nu then f s.ht b else 0)
  by_cases hg : (memberAt i j s b).content = nu
  · rw [if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg]
    rfl

/-- The multiplicity at a content is the exhaustion's collected
picks: the string count reads the span occupancy
(`walk_count`). -/
private theorem mult_foldL (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (x : List Nat) :
    ground.countOf x ((blockSpan lam).map HVec.content)
      = ground.famFold Nat.add 0 (fun s => pickL i j s x)
        (walk i j (blockSpan lam)) := by
  rw [blockcount.span_countOf, ← walk_count lam i j hi hj hij x]
  exact members_foldL i j (walk i j (blockSpan lam)) x

/-- `lem:casimir`'s trace collection at a letter pair: the two side
weights with the moved folds `weylchar.gSnd`/`gFst` and the two
letters' counts at the span's multiplicity read one identity at
every content — `thm:weylchar`'s "Collecting string by string"
clause at the pair's own exhaustion, the recursion's per-pair
display.  The multiplicity is the string count
(`walk_count`), so every member of the display is a fold over
the exhaustion — the moved folds by the fold exchange — and one
identity per string (`stringIdL`) closes them member by member. -/
theorem stringCollect (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) (hlen : nu.length = lam.length) :
    stringWeightUp i j (walk i j (blockSpan lam)) nu
        + stringWeightDn i j (walk i j (blockSpan lam)) nu
        + 2 * weylchar.gSnd
            (fun chi => ground.countOf chi
              ((blockSpan lam).map HVec.content)) nu i j
        + ground.countOf nu ((blockSpan lam).map HVec.content)
            * getAt 0 nu j
      = 2 * weylchar.gFst
            (fun chi => ground.countOf chi
              ((blockSpan lam).map HVec.content)) nu i j
        + ground.countOf nu ((blockSpan lam).map HVec.content)
            * getAt 0 nu i := by
  have hmult := mult_foldL lam i j hi hj hij
  have hUp : stringWeightUp i j (walk i j (blockSpan lam)) nu
      = ground.famFold Nat.add 0
        (fun s => wtL i j (fun ht b => (b + 1) * (ht - b)) s nu)
        (walk i j (blockSpan lam)) :=
    weight_foldL i j (fun ht b => (b + 1) * (ht - b))
      (walk i j (blockSpan lam)) nu
  have hDn : stringWeightDn i j (walk i j (blockSpan lam)) nu
      = ground.famFold Nat.add 0
        (fun s => wtL i j (fun ht b => b * (ht - b + 1)) s nu)
        (walk i j (blockSpan lam)) :=
    weight_foldL i j (fun ht b => b * (ht - b + 1))
      (walk i j (blockSpan lam)) nu
  have hSnd : weylchar.gSnd
      (fun chi => ground.countOf chi
        ((blockSpan lam).map HVec.content)) nu i j
      = ground.famFold Nat.add 0 (fun s => gSndL i j s nu)
        (walk i j (blockSpan lam)) := by
    show ground.famFold Nat.add 0
      (fun l => ground.getAt 0 nu j
        * ground.countOf (weylchar.moveBy i j l nu)
          ((blockSpan lam).map HVec.content))
      ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1)) = _
    rw [ground.famFold_congr_all Nat.add 0 _
      (fun l => ground.famFold Nat.add 0
        (fun s => ground.getAt 0 nu j
          * pickL i j s (weylchar.moveBy i j l nu))
        (walk i j (blockSpan lam)))
      (fun l => by
        rw [hmult (weylchar.moveBy i j l nu)]
        exact ground.famFold_mul _ _ _)
      ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1))]
    exact ground.famFold_swap
      (fun l s => ground.getAt 0 nu j
        * pickL i j s (weylchar.moveBy i j l nu))
      ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1))
      (walk i j (blockSpan lam))
  have hFst : weylchar.gFst
      (fun chi => ground.countOf chi
        ((blockSpan lam).map HVec.content)) nu i j
      = ground.famFold Nat.add 0 (fun s => gFstL i j s nu)
        (walk i j (blockSpan lam)) := by
    show ground.famFold Nat.add 0
      (fun l => (ground.getAt 0 nu i + 2 * l)
        * ground.countOf (weylchar.moveBy i j l nu)
          ((blockSpan lam).map HVec.content))
      ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1)) = _
    rw [ground.famFold_congr_all Nat.add 0 _
      (fun l => ground.famFold Nat.add 0
        (fun s => (ground.getAt 0 nu i + 2 * l)
          * pickL i j s (weylchar.moveBy i j l nu))
        (walk i j (blockSpan lam)))
      (fun l => by
        rw [hmult (weylchar.moveBy i j l nu)]
        exact ground.famFold_mul _ _ _)
      ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1))]
    exact ground.famFold_swap
      (fun l s => (ground.getAt 0 nu i + 2 * l)
        * pickL i j s (weylchar.moveBy i j l nu))
      ((List.range (ground.getAt 0 nu j)).map (fun l => l + 1))
      (walk i j (blockSpan lam))
  rw [hUp, hDn, hSnd, hFst, hmult nu,
    ground.famFold_mul 2 _ _, ground.famFold_mul 2 _ _,
    ← ground.famFold_mulR (ground.getAt 0 nu j) _ _,
    ← ground.famFold_mulR (ground.getAt 0 nu i) _ _,
    ← ground.famFold_add_split, ← ground.famFold_add_split,
    ← ground.famFold_add_split, ← ground.famFold_add_split]
  exact famFold_memL _ _ (walk i j (blockSpan lam)) (fun s hs =>
    stringIdL i j hij lam.length hi hj s
      (walk_good lam i j hi hj hij s hs).2.1
      (walk_good lam i j hi hj hij s hs).2.2.1
      nu hlen)

/-! The reversal clause (`lem:strings`' close): the span's count
family is invariant under every transposition (`symRead_def`), so
a count read transports across any transposition unconditionally,
along any interior word, and between any two lists of one count
family through the shared adjacent-sorted representative; the row
list's reversal is therefore occupied at the top's own count, one,
and every occupied content sits at or above the reversal in the
dominance order, the reversal's prefix joining the complement's
prefix to the total at both lists. -/

private theorem countSwapL (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (nu : List Nat) :
    ground.countOf (swapPair i j nu)
        ((blockSpan lam).map HVec.content)
      = ground.countOf nu ((blockSpan lam).map HVec.content) := by
  match Nat.lt_or_ge 0
      (ground.countOf nu ((blockSpan lam).map HVec.content)) with
  | .inl hpos =>
    exact symRead_def lam nu
      (ground.mem_of_countOf_pos nu _ hpos) i hi j hj
  | .inr hz =>
    match Nat.lt_or_ge 0 (ground.countOf (swapPair i j nu)
        ((blockSpan lam).map HVec.content)) with
    | .inl hpos2 =>
      have h3 := symRead_def lam (swapPair i j nu)
        (ground.mem_of_countOf_pos _ _ hpos2) i hi j hj
      rw [swapPair_swapPair i j nu] at h3
      exact h3.symm
    | .inr hz2 =>
      rw [Nat.le_antisymm hz (Nat.zero_le _),
        Nat.le_antisymm hz2 (Nat.zero_le _)]

private theorem countSortL (lam : Shape) (m : List Nat)
    (hm : m.length = lam.length) :
    ground.countOf (applyWord (sortWord (inversions m) m) m)
        ((blockSpan lam).map HVec.content)
      = ground.countOf m ((blockSpan lam).map HVec.content) :=
  applyWord_inv
    (fun x => ground.countOf x ((blockSpan lam).map HVec.content))
    lam.length
    (fun nu' _ k hk => by
      rw [← swapPair_adjacent k nu']
      exact countSwapL lam k (k + 1) (Nat.lt_of_succ_lt hk) hk nu')
    (sortWord (inversions m) m) m hm
    (fun x hx => by
      rw [← hm]
      exact (sortWord_reads (inversions m) m
        (Nat.le_refl _)).2.2 x hx)

/-- The count family's exchange transport at the shared sorted
representative (`lem:strings`' close): two lists of the block's
width holding every value at one count read the span's occupancy
family at one count, each sorted to the one representative through
the transpositions' invariance. -/
theorem countCongr (lam : Shape) (x y : List Nat)
    (hx : x.length = lam.length) (hy : y.length = lam.length)
    (hcnt : ∀ v, ground.countOf v x = ground.countOf v y) :
    ground.countOf x ((blockSpan lam).map HVec.content)
      = ground.countOf y ((blockSpan lam).map HVec.content) := by
  have heq : applyWord (sortWord (inversions x) x) x
      = applyWord (sortWord (inversions y) y) y :=
    sorted_eq_of_counts _ _
      (sortWord_reads (inversions x) x (Nat.le_refl _)).1
      (sortWord_reads (inversions y) y (Nat.le_refl _)).1
      (fun v => by
        rw [countOf_applyWord v _ x, countOf_applyWord v _ y]
        exact hcnt v)
  rw [← countSortL lam x hx, ← countSortL lam y hy, heq]

/-- The reversal is occupied at the top's own count, one: the row
list's reversal reads the span's occupancy family at the shared
sorted representative (`lem:strings`' close). -/
theorem rev_occupied (lam : Shape) :
    ground.countOf ((rowList lam).reverse)
        ((blockSpan lam).map HVec.content) = 1 := by
  rw [countCongr lam ((rowList lam).reverse) (rowList lam)
    (by rw [ground.length_reverse, length_rowList])
    (length_rowList lam)
    (fun v => countOf_reverse v (rowList lam))]
  exact lowerspan.topRead_def lam

/-- Every occupied content sits at or above the row list's
reversal in the dominance order: the member's reversal is occupied
through the count family and dominated by the top, and the
dominance order flips at the two reversals (`lem:strings`'
close). -/
theorem rev_floor (lam : Shape) :
    ∀ nu ∈ (blockSpan lam).map HVec.content,
      weylchar.domBy ((rowList lam).reverse) nu := by
  intro nu hnu
  obtain ⟨v, hv, hvc⟩ := ground.mem_map_of HVec.content
    (blockSpan lam) nu hnu
  have hlen : nu.length = lam.length := by
    rw [← hvc]
    exact blockSpan_width lam v hv
  have hrevmem : nu.reverse ∈ (blockSpan lam).map HVec.content :=
    ground.mem_of_countOf_pos _ _ (by
      rw [countCongr lam nu.reverse nu
        (by rw [ground.length_reverse]; exact hlen) hlen
        (fun x => countOf_reverse x nu)]
      exact ground.countOf_pos_of_mem hnu)
  have hdom := lowerspan.supportRead_def lam nu.reverse hrevmem
  have hflip := weylchar.domBy_reverse nu.reverse (rowList lam) hdom
  rw [ground.reverse_reverse nu] at hflip
  exact hflip

end strings
