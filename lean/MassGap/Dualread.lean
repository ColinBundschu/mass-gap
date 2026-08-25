import MassGap.Blockcount
import MassGap.Lowerspan
import MassGap.Blockirr
import MassGap.Strings
import MassGap.Fusiondata
/-!
`lem:dualread` — clause (i)'s dual action with its laws through the
coevaluation's equivariance, and clause (ii)'s full-column line
with its transport reads.

Clause (i)'s tiers. The dual action `dact` is the balance partner
of the exchanged letters' action on the carrier, with its
definitional laws: the exchanged action joined to its dual reads
the unit tail, the dual image keeps the width, the double dual is
the original, the dual diagonal reads a content summand at its
coordinate's partner, and the transpose identity
`(E^∨_{ij})^T = E^∨_{ji}` walks the partner across the pairing
over the original's transpose (`dact_adjoint` at
`blockcount.unit_adjoint`).  Invariant subspaces agree
(`settled_neg` at `elim.spanRel_scale`'s partner scalar, the two
directions `dact_settled`/`act_settled_of_dact`), the block's span
is closed under the dual action (`dact_closed`), and duals of
blocks are irreducible, `lem:blockirr`(i) at the agreement
(`dual_irred`).  The evaluation is equivariant to the unit at the
coordinate form (`ev_equiv`) and at the graded pairing `dotG`
(`ev_equivG`, the mismatched-content guards closing at the moves'
round trips with the vacant source's image the unit tail).  The
Gram-dual coevaluation's datum is `coevData`, per occupied content
the group's adjugate entries at the further groups' determinants —
the graded Gram's own adjugate — and the moved coevaluation pairs
every member pair at the sum's unit (`coev_equiv`): the two
collapses run at the entrywise adjugate identity of the symmetric
group Gram (`elim.adjP_row_fold`, `elim.cofVec_col_fold`) and the
member reads join at `ev_equivG`.  The correspondence's reads:
the moved form is `movedAt` with `coev_equiv` its coevaluation
instance, the family's map `mapAt` folds the
argument's own content group, the map's invariant `mapInv`
is the coevaluation's second slot at the map's value, and the
composite at a map reads the graded determinant's scale: the
members' read at the adjugate identity (`mapInv_trip_mem`, the
filter's pick at the withdrawn key closing at `detAll`), and its
extension over the argument's content group's span
(`mapInv_trip`), both composites additive and scale-reading in
the argument with a span member's cleared combination read
through the members and the clearing withdrawn at the product's
injectivity, and the map's datum is the invariant's read — the
family at matched contents (`mapInv_matched`) with the moved read
at the sum's unit (`mapInv_equiv`): a letter pair's Leibniz image
at a member and any second vector collects at the adjugate
identity twice, the first slots walked across the transpose
identity to the member's letter image, the image's cleared
combination over the list's span (`elim.span_elim`) reading the
adjugate solve at the determinant against the combination's
coefficients with the equivariance transporting the letter across
the slot, the two reads joined at partners and the clearing
withdrawn at the product's injectivity.  The map's data are the
matrix family at `lem:blockirr`'s format (`mapMat`, one matrix per
content with row `r` the first slots' combination at the
coefficients against the second slots' `r`-th coordinates), its
action the family's own map at the format's frame (`mapMat_read`,
the members' sized coordinate families at matched contents); the
invariant reads as the equivariant map (`mapAt_equiv`: the
invariance read at the stated argument joins two crossed folds,
the first the map's value at the moved argument through the
evaluation's equivariance and the second the moved value's own
pairing, the invariance read over the carrier's stated list with
the family's slots its members, the moved map value's span read
the list's own settled images at the letter pair, and the moved
images one value at the pairing's definiteness); and the
composite at an
invariant reads its `det G`-multiple at every argument
(`mapMat_trip`): the identity at each first slot over the list's
span, the first slot's cleared combination reading the adjugate
solve at the determinant against the combination's coefficients
(`adjP_span_entry` at `elim.adjP_row_fold`) with the clearing
withdrawn at the product's injectivity.  The count clause reads the
invariants off one stacked system: an invariant enters at its
coefficient family over the two stated lists' matched member pairs
(`dualPairs`, one slot pair per member pair at one content), the
moved reads one linear system in the coefficients (`dualSys`), each
row the moved form's fold at a letter pair and a member pair
(`dualRow`), and the count is that system's kernel dimension over the
grid's coefficients (`invCount` at `elim.kernelDim`); the family at a
grid vector is `invFam`, the moved form at it the system's row
against the coefficients (`movedAt_invFam`), and a grid vector sits
in the kernel exactly where every moved read at the letter pairs and
the member pairs is the sum's unit (`dualKer_read`).

Clause (ii)'s tier. The shape at a power is `fulls d m`, the `m`
full columns over `d` letters (`def:places`' column display, every
shorter column unoccupied, the vacant letter count reading the
empty column list at `con:places`' positive column lengths), and
its row list is the constant list at that count, every row the
vacant tail's total joined to the top column's own occupancies
(`rowList_fulls`).  Its exhibit is the wedge tensored
onto the exhibit one power below (`blockcount.exhibit_addFull` at
the top column's addition), so the interior lowerings descend the
power: at a vacant letter the tensored image reads the sum's unit
outright, at an occupied one it is the wedge tensored onto the
inner image, and the wedge tensored on keeps the unit tail
(`blockcount.lowerH_tensorW_unit`).  The induction on the power
hands `blockcount.blockSpan_stationary` its hypothesis at every
`m`, and the span is the exhibit's own singleton — clause (ii)'s
line at clause (iii)'s tensor power (`lineSpan`), the base's
occupancy guard refusing every lowering.  The line's own singlet
read closes the clause (`fullTop_lower`): a top at the full-column
content generates the line, so its every interior lowering reads
the unit tail — the top's closure pool at the shape's own count
(`blockcount.seedBlock_dim`), the shape at the full-column content
the power's own column list (`shapeOf_fulls`, the consecutive
gaps vacant below the top column), the line's one member handed to
`blockcount.closeSpan_seed_line`; at a null seed the lowerings are
null through the action's own unit-tail read
(`elim.matVec_null`), so the seed's off-unit binder is derived,
not carried.  The transport reads
instantiate the walk correspondence at the height measure
(`blockcount.blockSpan_addFull` and `blockcount.occupancy_addFull`
at `lowerspan.ht`): the bumped shape's span is the span at the
wedge tensored on member for member with the dimension the mapped
span's (`spanAddFull`), and the occupancies read at the shifted
contents (`occupancyAddFull`).  The mapped span's own carriers
close the clause: the bumped shape's fused pool against a further
block is the pool's own with the wedge tensored on, member for
member at the arrangements' join (`countAt_fusedLine` at
`blockcount.tensorH_assoc`), so the two read one count at every
content; the mapped carrier's count at the shifted content is the
carrier's own (`countAt_lineShift`) — the group at the shifted
content is the content's own group mapped, the mapped collection
and the shifted content's own sit in one span at the mapped list's
linearity (`elim.kernelDim_congr`), and the stacked raisings read
across the map at every coefficient family
(`elim.kernelDim_kerIff` at `blockcount.act_tensorW_unit`): every
letter of the shifted content is occupied, so the stacked datum
carries a block at each of them, each block's read the further
factor's own, and at a letter the content leaves vacant the block's
read is the sum's unit outright.  The two compose at the target's
shifted row list (`blockcount.rowList_addFull`) to the fusion
count's descent at one full column (`fusionCount_addFull`,
`con:labels`' class-invariance clause,
`N^{c+(1^{d_f})}_{a+(1^{d_f}),b} = N^c_{ab}`), with the span length
the mapped span's (`spanAddFull`'s first read).  The dual block's top is the
reversal member (`dualTop`): at the span member carrying the row
list's reversal every dual raising's image reads the unit tail,
the moved content dropping the reversal's prefix at the lowered
key (`blockcount.prefixAt_moveAt`) against the floor
(`strings.rev_floor`), and an unoccupied lowered letter reading
the action null outright (`units.matVec_null_unocc`); the
reversal's group is one line (`strings.rev_occupied`), the dual
top's own occupancy.  The full columns are where clause (iii)'s
count is read: the fusion count at `fulls a.length m` is one at
the join of `b`'s row list with `a`'s reversal and vacant off it
(`fusionCount_fulls`), the two at-join arms `ker_le_one_join` and
`ker_ge_one_join` meeting at one and `ker_null_offJoin` the
vacant read.

The grid transport closes the count clause: `gridOf`, the
equivariant map's grid vector, enters the grid through the second
list's solve — one block per occupied content, the rows the second
list's cleared combinations at the coevaluation's coefficients
against the graded solves of the map's values (`gridBlock`,
`gridRow`, `zSolve`), each member's row read at the member's place
in its group — with
`gridOf_len` the grid's width, `gridOf_val` the map read at the two
graded determinants' scale by the round trip, `gridOf_ker` the
stacked system's kernel membership at the equivariance through the
moved form's two-reads split (`movedAt_two_reads`, the factored
crossed folds `moved_agree` consumes), `invFam_unitTail` the
unit-family map read, and `gridOf_off` the off-unit read at an
off-unit value.  The count closes at `invCount_span`: the kernel
list and a stated map list read one count, two independent lists
inside one span (`elim.span_count_eq` at the kernel kit).

Clause (iii)'s carrier tier closes clause (i)'s map at the tensor
grid: the family is the coefficients zipped onto the factor
enumeration (`pairFam`, `invFam`'s sibling), and its value is
equivariant at the raising direction (`pairVal_equiv`).  The kernel
read is the combination's annihilation by the stacked raising
(`ker_stack` at `elim.matVec_crossM`, `ker_adj` at
`units.stackedRaise_to` with an unoccupied lowered letter reading
the action null), carried to every raising below the width by the
descent on the gap (`raise_gap`, the commutator's crossed join at
`units.matVec_comm_read` with both composites null by the descent,
the vacant middle at the vacant content).  Contracting the
annihilated combination against the argument's tensor with an
output vector walks the raising across the transpose identity
(`blockcount.unit_adjoint`) and splits it over that tensor
(`blockcount.act_tensorH`), each place factorizing at the matched
first-factor degree (`blockcount.dotP_tensorH` at one first
content, `blockcount.dotP_tensorH_off` off it — `hdegA`'s frame,
the vacant argument letter withdrawing the first arm at the
enumeration's own growth `places.length_monomialsAt_le_bumpAt`):
the two arms are the value's two reads (`tens_entry`,
`grid_contract`), so the moved value pairs every output vector as
the value's moved read does (`pairVal_place` at `pairVal_pair`'s
filter collapse) and the two agree place for place at the place
indicators (`dotP_indAt` at `elim.dotP_oneIndex`).  Off the
argument's degree, at a vacant output letter, and at a vacant
argument letter the two reads are the unit family outright.

Clause (iii)'s off-join arm reads the value list (`valList`), one
value per stated first-block member at the complement of its own
content.  Every value is sized and settled inside the second
block's span (`valList_settled`): the value's rows are the second
block's members at the complement content, the pair guard's join
read back entrywise at matched widths (`compl_of_join`), so the
combination sits in that content's group's span
(`elim.spanRel_combo` at `blockcount.span_of_mem`).  The list is
closed at the letters (`valList_closed`): a letter's image of a
value is the value at the argument's dual move (`pairVal_equiv` at
the raising direction, `pairVal_equiv_lower` at the lowering),
the dual argument's cleared combination over its content group
(`dact_closed`, `elim.span_elim`) reads through the fold at the
value's linearity in its argument (`pairVal_argCombo` at
`pairVal_argAdd`/`pairVal_argScale`/`pairVal_argCongr`), and the
moved complement is the moved content's own join
(`join_move`, the two occupancies the moves' — an unoccupied
lowered letter reading the image null outright), so every row of
the combination is a value list member at the moved content and
the image sits in that group's span.  At a coefficient family off
the sum's unit the head's group holds a value off the unit tail
(`valOff_head`): the solve-back's contrapositive (`pairSolve`)
names a stated member whose value sits off the unit tail, so every
second-block member joins the value list's span
(`blockirr.irred`), the head among them; the head's own
coordinates sit off the unit family (`blockcount.exhibit_off_unit`)
and a combination of unit tails reads the unit tail, so the head's
group holds a value off the sum's unit, and that value's slot
reads the guard exact — `b`'s row list joins an occupied content
of `W_a` to the full columns.

The dual-table tier reads the dual action as a walk table over one
adjacent letter pair.  `exchTable` carries `con:units`' pair with
the step and its transpose exchanged and the two letters with them,
every law the original's at the exchanged role and the transpose
identity read backwards across the pairing; `negTable` carries
every image's coordinates at the memberwise swap with the contents
kept, the scaling law at the unit's partner moving the swap through
each image (`elim.vecScale_swap` at `poly.scale_one`) and
`elim.dotP_swap_left`/`elim.dotP_swapMap` reading it across both
pairings; and `dualTable` is their composite at the matrix units,
its step and transpose the dual lowering and raising at the
adjacent pair (`dact_step`, `dact_tr`).  Clause 10 of (iii) lands
on it: at the join, wherever a word's lowering image at the
target's top and its dual image at the reversal member are both off
the unit tail, the two contents join to the full columns
(`dualLive` — the lowering moves the pair down, the dual moves it
up, and the joined family rides the two moves
(`blockcount.moveAt_zipWith_left`/`_right`) through the step's
round trip, the join's own entry occupied at the live letter); so
the two tables' crossing scalars are tied cross-added and the dual
word family at the reversal member reads one Gram with the word
family at the target's top (`dualGram` at
`blockcount.wordGramT`, the two tops' self-pairings the scales).
-/

namespace dualread
open ground places blockcount

/-! `lem:dualread`(i)'s dual-action tier: the dual action is the
balance partner of the exchanged letters' action on the carrier —
the moved content the exchanged action's own, every coordinate the
memberwise swap — with its definitional laws: the exchanged action
joined to its dual reads the unit tail, the dual image keeps the
width, the double dual is the original at the exchange twice with
the partner twice, the dual diagonal reads a content summand at its
coordinate's partner, and the transpose identity
`(E^∨_{ij})^T = E^∨_{ji}` walks the partner across the pairing over
the original's transpose (`blockcount.unit_adjoint` at the
exchanged letters with `elim.dotP_swap_left`/`dotP_swapMap` moving
the swap through the two pairings). -/

/-- The dual action: the balance partner of the exchanged letters'
action, `lem:dualread`(i)'s operator at the carrier. -/
def dact (i j : Nat) (v : HVec) : HVec :=
  ⟨(act j i v).content, poly.neg (act j i v).coords⟩

/-- The sum's every entry of equal members: the exchanged action
joined to its dual reads the unit tail, `poly.add_neg`'s instance
at the action's coordinates. -/
theorem unitTail_act_dact (i j : Nat) (v : HVec) :
    poly.unitTail
      (poly.add (act j i v).coords (dact i j v).coords) :=
  poly.add_neg (act j i v).coords

/-- The dual image is sized: the memberwise swap keeps the width
and the action's own width read closes it. -/
theorem dact_sized (i j : Nat) (v : HVec) : sized (dact i j v) := by
  show (poly.neg (act j i v).coords).length
    = (places.monomialsAt (act j i v).content).length
  rw [poly.length_neg]
  exact act_sized j i v

/-- The double dual is the original: the exchange twice at the
partner twice, each letter's read the original's own. -/
theorem dact_dact (i j : Nat) (v : HVec) :
    (⟨(dact j i v).content, poly.neg (dact j i v).coords⟩ : HVec)
      = act i j v := by
  show (⟨(act i j v).content,
    poly.neg (poly.neg (act i j v).coords)⟩ : HVec) = act i j v
  rw [poly.neg_neg]

/-- Two dual factors compose to the exchanged originals' composite
at the double partner: the inner partner walks across the outer
action and the two partners compose to the original —
`lem:dualread`(i)'s composition sentence, the dual table's own
opening read. -/
theorem dact_comp (a b c d : Nat) (v : HVec) :
    dact a b (dact c d v) = act b a (act d c v) := by
  show (⟨(act b a (act d c v)).content,
    poly.neg (elim.matVec
      (units.matUnitAt (moveAt b a (act d c v).content)
        (act d c v).content b a)
      (poly.neg (act d c v).coords))⟩ : HVec)
    = act b a (act d c v)
  rw [elim.matVec_neg, poly.neg_neg]
  rfl

/-- An occupied letter sits inside the width: the read beyond the
width is the default. -/
private theorem occ_width {mu : List Nat} {p : Nat}
    (h : 0 < ground.getAt 0 mu p) : p < mu.length := by
  match Nat.lt_or_ge p mu.length with
  | .inl hlt => exact hlt
  | .inr hge =>
    rw [ground.getAt_over 0 mu p hge] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The dual diagonal reads a content summand at its coordinate's
partner: the content kept at the occupied letter's round trip, the
coordinates the diagonal's read at the partner scalar —
`lem:dualread`(i)'s `μ + μ^∨` of equal members coordinatewise. -/
theorem dact_diag (p : Nat) (v : HVec) (hs : sized v)
    (hocc : 0 < ground.getAt 0 v.content p) :
    (dact p p v).content = v.content
    ∧ poly.oneValue (dact p p v).coords
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 v.content p)).swap v.coords) := by
  have hp : p < v.content.length := occ_width hocc
  have hc : moveAt p p v.content = v.content := by
    show bumpAt p (dipAt p v.content) = v.content
    exact bumpAt_dipAt_self p v.content hocc
  constructor
  · show moveAt p p v.content = v.content
    exact hc
  · show poly.oneValue
      (poly.neg (elim.matVec
        (units.matUnitAt (moveAt p p v.content) v.content p p)
        v.coords))
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 v.content p)).swap v.coords)
    rw [hc, elim.vecScale_swap]
    exact poly.swapMap_oneValue
      (units.matVec_diag_read v.content p hp v.coords hs)

/-- The transpose identity at the dual, `(E^∨_{ij})^T = E^∨_{ji}`:
the moved dual image pairs a stated vector as the vector pairs the
exchanged dual image — the partner read across the pairing over the
original's transpose walk. -/
theorem dact_adjoint (i j : Nat) (mu : List Nat)
    (hj : j < mu.length) (hij : ¬ i = j)
    (hiocc : 0 < ground.getAt 0 mu i)
    (w r : List BPair)
    (hw : w.length = (places.monomialsAt mu).length)
    (hr : r.length = (places.monomialsAt (moveAt j i mu)).length) :
    (elim.dotP (dact i j ⟨mu, w⟩).coords r).oneValue
      (elim.dotP w (dact j i ⟨moveAt j i mu, r⟩).coords) := by
  have hi : i < mu.length := occ_width hiocc
  have hji : ¬ j = i := fun he => hij he.symm
  have hL : elim.dotP (dact i j ⟨mu, w⟩).coords r
      = (elim.dotP (elim.matVec
          (units.matUnitAt (moveAt j i mu) mu j i) w) r).swap :=
    elim.dotP_swap_left
      (elim.matVec (units.matUnitAt (moveAt j i mu) mu j i) w) r
  have hR : elim.dotP w (dact j i ⟨moveAt j i mu, r⟩).coords
      = (elim.dotP w (elim.matVec
          (units.matUnitAt mu (moveAt j i mu) i j) r)).swap := by
    show elim.dotP w (poly.neg (elim.matVec
        (units.matUnitAt (moveAt i j (moveAt j i mu))
          (moveAt j i mu) i j) r))
      = (elim.dotP w (elim.matVec
          (units.matUnitAt mu (moveAt j i mu) i j) r)).swap
    rw [moveAt_round_at i j mu hiocc]
    exact elim.dotP_swapMap w
      (elim.matVec (units.matUnitAt mu (moveAt j i mu) i j) r)
  rw [hL, hR]
  exact ground.swap_congr
    (unit_adjoint j i mu hj hi hji hiocc w r hw hr)

/-- The evaluation is equivariant to the unit: a letter pair's
Leibniz image reads `⟨E^∨_{ij}f, x⟩ + ⟨f, E_{ij}x⟩`, the first
summand the partner of `⟨E_{ji}f, x⟩` with the transpose identity
reading that pairing as the second, and a value joined to its
partner reads the sum's unit — `lem:dualread`(i)'s evaluation
sentence. -/
theorem ev_equiv (i j : Nat) (mu : List Nat)
    (hj : j < mu.length) (hij : ¬ i = j)
    (hiocc : 0 < ground.getAt 0 mu i)
    (w r : List BPair)
    (hw : w.length = (places.monomialsAt mu).length)
    (hr : r.length = (places.monomialsAt (moveAt j i mu)).length) :
    ((elim.dotP (dact i j ⟨mu, w⟩).coords r)
      + (elim.dotP w (act i j ⟨moveAt j i mu, r⟩).coords)).oneValue
      BPair.unit := by
  have hadj := dact_adjoint i j mu hj hij hiocc w r hw hr
  have hRe : elim.dotP w (dact j i ⟨moveAt j i mu, r⟩).coords
      = (elim.dotP w
          (act i j ⟨moveAt j i mu, r⟩).coords).swap := by
    show elim.dotP w
        (poly.neg (act i j ⟨moveAt j i mu, r⟩).coords)
      = (elim.dotP w (act i j ⟨moveAt j i mu, r⟩).coords).swap
    exact elim.dotP_swapMap w
      (act i j ⟨moveAt j i mu, r⟩).coords
  rw [hRe] at hadj
  refine BPair.oneValue_trans
    (BPair.add_congr hadj (BPair.oneValue_refl _)) ?_
  exact BPair.swap_add_null (BPair.oneValue_refl _)

/-! `lem:dualread`(i)'s agreement tier: invariant subspaces agree —
a dual image is the exchanged letters' image at the partner's
scale, a span member's scale inside the span, with the double
partner reading the original images back — so a pool's closure
converts between the two actions and duals of blocks are
irreducible, `lem:blockirr`(i) at the agreement. -/

/-- A settled vector's memberwise swap is settled: the unit tail's
swap keeps the unit read, and a span member's scale sits inside the
span at the unit's partner with the scaled read carried across. -/
theorem settled_neg (pool : List HVec) (c : List Nat)
    (x : List BPair) (h : settledAt pool ⟨c, x⟩) :
    settledAt pool ⟨c, poly.neg x⟩ := by
  match h with
  | .inl hU =>
    exact Or.inl (allU_of_unitTail (poly.neg x)
      (poly.unitTail_swapMap x (unitTail_of_allU x hU)))
  | .inr hsp =>
    refine Or.inr ?_
    show elim.spanRel (poly.neg x).length (groupAt pool c)
      (poly.neg x)
    rw [poly.length_neg]
    have hov : poly.oneValue
        (elim.vecScale (BPair.ofNat 1).swap x) (poly.neg x) := by
      rw [elim.vecScale_swap]
      exact poly.swapMap_oneValue (poly.scale_one x)
    exact elim.spanRel_congr x.length (groupAt pool c)
      (elim.vecScale (BPair.ofNat 1).swap x) (poly.neg x) hov
      (elim.spanRel_scale x.length (groupAt pool c) x
        (BPair.ofNat 1).swap hsp.1 hsp.2.1 hsp)
      (poly.length_neg x)

/-- The exchanged action's settled image reads the dual's settled:
the agreement's forward direction at a stated pool. -/
theorem dact_settled (pool : List HVec) (i j : Nat) (v : HVec)
    (h : settledAt pool (act j i v)) :
    settledAt pool (dact i j v) :=
  settled_neg pool (act j i v).content (act j i v).coords h

/-- The dual's settled image reads the exchanged action's: the
agreement's backward direction, the double partner reading the
original back. -/
theorem act_settled_of_dact (pool : List HVec) (i j : Nat)
    (v : HVec) (h : settledAt pool (dact i j v)) :
    settledAt pool (act j i v) := by
  have h2 := settled_neg pool (dact i j v).content
    (dact i j v).coords h
  rw [show (⟨(dact i j v).content, poly.neg (dact i j v).coords⟩
      : HVec) = act j i v from dact_dact j i v] at h2
  exact h2

/-- The block's span is closed under the dual action: every dual
image of a span member is settled, the exchanged letters' closure
at the partner's scale — `lem:dualread`(i)'s invariant subspaces
agreeing at the block. -/
theorem dact_closed (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length)
    (i j : Nat) (hi : i < s.length) (hj : j < s.length)
    (hij : ¬ i = j) :
    ∀ v ∈ blockSpan s, settledAt (blockSpan s) (dact i j v) :=
  fun v hv => dact_settled (blockSpan s) i j v
    (act_closed s hall hcl j i hj hi (fun he => hij he.symm) v hv)

/-- The reversal member is the dual top (`lem:dualread`(ii)'s dual
block): at a span member carrying the row list's reversal every
dual raising's image reads the unit tail — the moved content drops
the reversal's prefix at the lowered key so the floor reads its
group vacant, and an unoccupied lowered letter reads the action
null outright. -/
theorem dualTop (s : Shape) : ∀ v ∈ blockSpan s,
    v.content = (rowList s).reverse →
    ∀ i j, i < j → j < s.length →
    poly.unitTail (dact i j v).coords := by
  intro v hv hc i j hij hj
  show poly.unitTail (poly.neg (act j i v).coords)
  refine poly.unitTail_swapMap _ ?_
  match Nat.lt_or_ge 0 (ground.getAt 0 v.content i) with
  | .inr hz0 =>
    show poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt j i v.content) v.content j i)
      v.coords)
    exact units.matVec_null_unocc _ v.content j i
      (Nat.le_antisymm hz0 (Nat.zero_le _)) v.coords
  | .inl hocc =>
    refine tops.vacant_settled (blockSpan s) v j i
      (lowerspan.act_closed_def s j i hj
        (Nat.lt_trans hij hj) (Nat.ne_of_gt hij) v hv) ?_
    rw [occ_eq_countOf]
    match Nat.lt_or_ge 0 (ground.countOf (moveAt j i v.content)
        ((blockSpan s).map HVec.content)) with
    | .inr hz2 => exact Nat.le_antisymm hz2 (Nat.zero_le _)
    | .inl hpos =>
      have hpre := weylchar.domGo_prefix 0
        ((rowList s).reverse) (moveAt j i v.content)
        (strings.rev_floor s (moveAt j i v.content)
          (ground.mem_of_countOf_pos _ _ hpos)) (i + 1)
      rw [Nat.zero_add, ← hc,
        ← prefixAt_moveAt i j v.content hij hocc] at hpre
      exact absurd hpre (Nat.lt_irrefl _)

/-- Duals of blocks are irreducible: a stated list closed under the
dual action splits at `lem:blockirr`(i)'s two disjuncts, the
closure converted across the agreement. -/
theorem dual_irred (d : Nat) (v : HVec) (tail L : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (ground.getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (ground.getAt (⟨[], []⟩ : HVec) tail k))
    (hLsz : ∀ x ∈ L, sized x)
    (hLmem : ∀ x ∈ L, settledAt (v :: tail) x)
    (hLcl : ∀ x ∈ L, ∀ i < d, ∀ j < d, ¬ i = j →
        settledAt L (dact i j x)) :
    (∀ w ∈ v :: tail, settledAt L w)
      ∨ (∀ x ∈ L, poly.unitTail x.coords) :=
  blockirr.irred d v tail L hsz hwid hprov hLsz hLmem
    (fun x hx i hi j hj hij =>
      act_settled_of_dact L j i x
        (hLcl x hx j hj i hi (fun he => hij he.symm)))

/-! `lem:dualread`(i)'s dual-table tier: the dual action read as a
walk table over one adjacent letter pair.  The exchanged table
carries `con:units`' unit space with the step and its transpose
exchanged and the two letters with them, every law the original's
own at the exchanged role; the partner table carries every image's
coordinates at the memberwise swap with the contents kept, the
scaling law moving the swap through each image and the transpose
identity reading it across both pairings; and their composite at
the matrix units is the dual table, whose step and transpose are
`E^∨_{ij}` at the adjacent pair.  Clause 10 of `lem:dualread`(iii)
lands on it: at the join, wherever both word images are live the
two contents join to the full columns, so the two tables' crossing
scalars are tied cross-added and the dual word family at the
reversal member reads one Gram with the word family at the
target's top. -/

/-- The exchanged table: the step and its transpose exchanged, the
two letters with them — `con:units`' pair read from the raising
side, each law the original's at the exchanged role and the
transpose identity read backwards across the pairing. -/
private def exchTable (T : WalkTable) : WalkTable where
  dLet := T.uLet
  uLet := T.dLet
  step := T.tr
  tr := T.step
  letters := fun j => match T.letters j with
    | .inl h => .inr ⟨h.2, h.1⟩
    | .inr h => .inl ⟨h.2, h.1⟩
  step_content := T.tr_content
  tr_content := T.step_content
  step_sized := T.tr_sized
  tr_sized := T.step_sized
  step_congr := T.tr_congr
  step_vecAdd := T.tr_vecAdd
  step_vecScale := T.tr_vecScale
  tr_congr := T.step_congr
  tr_vecAdd := T.step_vecAdd
  tr_vecScale := T.step_vecScale
  step_unitTail := T.tr_unitTail
  tr_unitTail := T.step_unitTail
  step_vac := T.tr_vac
  tr_vac := T.step_vac
  adjoint := by
    intro j v z hsv hsz hj hU hZ
    have hdb : T.dLet j < v.content.length :=
      match T.letters j with
      | .inl h => by rw [h.1]; exact Nat.lt_of_succ_lt hj
      | .inr h => by rw [h.1]; exact hj
    have hbd : T.dLet j < (dipAt (T.uLet j) v.content).length := by
      rw [ground.length_dipAt]
      exact hdb
    have hzlen : j + 1 < z.content.length := by
      rw [hZ, length_moveAt]
      exact hj
    have hDz : 0 < ground.getAt 0 z.content (T.dLet j) := by
      rw [hZ]
      show 0 < ground.getAt 0
        (bumpAt (T.dLet j) (dipAt (T.uLet j) v.content)) (T.dLet j)
      rw [ground.getAt_bumpAt_self (T.dLet j)
        (dipAt (T.uLet j) v.content) hbd]
      exact Nat.succ_pos _
    have hVc : v.content = moveAt (T.uLet j) (T.dLet j) z.content := by
      rw [hZ, moveAt_round_at (T.uLet j) (T.dLet j) v.content hU]
    rw [elim.dotP_comm (T.tr j v).coords z.coords,
      elim.dotP_comm v.coords (T.step j z).coords]
    exact BPair.oneValue_symm (T.adjoint j z v hsz hsv hzlen hDz hVc)
  cross_occ := fun j v hs hj hD hU =>
    poly.oneValue_symm (T.cross_occ j v hs hj hU hD)
  cross_vacU := fun j v hs hj hD hU0 => T.cross_vacD j v hs hj hU0 hD
  cross_vacD := fun j v hs hj hD0 hU => T.cross_vacU j v hs hj hU hD0
  comm := by
    intro l j v hlj hs hl hj2
    match T.comm j l v (fun he => hlj he.symm) hs hj2 hl with
    | ⟨hc, hlen, hq⟩ => exact ⟨hc.symm, hlen.symm, poly.oneValue_symm hq⟩

/-- The memberwise swap is the unit's partner scale: the scaling at
the unit's swap reads the coordinates' own swap. -/
private theorem negScale (x : List BPair) :
    poly.oneValue (elim.vecScale (BPair.ofNat 1).swap x) (poly.neg x) := by
  rw [elim.vecScale_swap]
  exact poly.swapMap_oneValue (poly.scale_one x)

/-- The step at a swapped argument reads the step's own image
swapped, the table's scaling law at the unit's partner. -/
private theorem step_negArg (T : WalkTable) (j : Nat) (mu : List Nat)
    (x : List BPair) :
    poly.oneValue (T.step j ⟨mu, poly.neg x⟩).coords
      (poly.neg (T.step j ⟨mu, x⟩).coords) :=
  poly.oneValue_trans
    (T.step_congr j ⟨mu, poly.neg x⟩
      ⟨mu, elim.vecScale (BPair.ofNat 1).swap x⟩ rfl
      (poly.oneValue_symm (negScale x)))
    (poly.oneValue_trans (T.step_vecScale j mu (BPair.ofNat 1).swap x)
      (negScale (T.step j ⟨mu, x⟩).coords))

/-- The transpose at a swapped argument reads the transpose's own
image swapped. -/
private theorem tr_negArg (T : WalkTable) (j : Nat) (mu : List Nat)
    (x : List BPair) :
    poly.oneValue (T.tr j ⟨mu, poly.neg x⟩).coords
      (poly.neg (T.tr j ⟨mu, x⟩).coords) :=
  poly.oneValue_trans
    (T.tr_congr j ⟨mu, poly.neg x⟩
      ⟨mu, elim.vecScale (BPair.ofNat 1).swap x⟩ rfl
      (poly.oneValue_symm (negScale x)))
    (poly.oneValue_trans (T.tr_vecScale j mu (BPair.ofNat 1).swap x)
      (negScale (T.tr j ⟨mu, x⟩).coords))

/-- The partner step at a partner argument reads the table's own
image: the two swaps compose to the identity. -/
private theorem negStep_arg (T : WalkTable) (j : Nat) (mu : List Nat)
    (x : List BPair) :
    poly.oneValue (poly.neg (T.step j ⟨mu, poly.neg x⟩).coords)
      (T.step j ⟨mu, x⟩).coords := by
  have h : poly.oneValue (poly.neg (T.step j ⟨mu, poly.neg x⟩).coords)
      (poly.neg (poly.neg (T.step j ⟨mu, x⟩).coords)) :=
    poly.swapMap_oneValue (step_negArg T j mu x)
  rw [poly.neg_neg] at h
  exact h

/-- The partner transpose at a partner argument reads the table's
own image. -/
private theorem negTr_arg (T : WalkTable) (j : Nat) (mu : List Nat)
    (x : List BPair) :
    poly.oneValue (poly.neg (T.tr j ⟨mu, poly.neg x⟩).coords)
      (T.tr j ⟨mu, x⟩).coords := by
  have h : poly.oneValue (poly.neg (T.tr j ⟨mu, poly.neg x⟩).coords)
      (poly.neg (poly.neg (T.tr j ⟨mu, x⟩).coords)) :=
    poly.swapMap_oneValue (tr_negArg T j mu x)
  rw [poly.neg_neg] at h
  exact h

/-- The partner step's width at a partner argument is the table's
own: the two images share their content. -/
private theorem negStep_arg_len (T : WalkTable) (j : Nat) (mu : List Nat)
    (x : List BPair) :
    (poly.neg (T.step j ⟨mu, poly.neg x⟩).coords).length
      = (T.step j ⟨mu, x⟩).coords.length := by
  rw [poly.length_neg, T.step_sized j ⟨mu, poly.neg x⟩,
    T.step_sized j ⟨mu, x⟩, T.step_content j ⟨mu, poly.neg x⟩,
    T.step_content j ⟨mu, x⟩]

/-- The partner transpose's width at a partner argument is the
table's own. -/
private theorem negTr_arg_len (T : WalkTable) (j : Nat) (mu : List Nat)
    (x : List BPair) :
    (poly.neg (T.tr j ⟨mu, poly.neg x⟩).coords).length
      = (T.tr j ⟨mu, x⟩).coords.length := by
  rw [poly.length_neg, T.tr_sized j ⟨mu, poly.neg x⟩,
    T.tr_sized j ⟨mu, x⟩, T.tr_content j ⟨mu, poly.neg x⟩,
    T.tr_content j ⟨mu, x⟩]

/-- The partner table: every image's coordinates at the memberwise
swap, the contents kept — the balance partner of the table's
action, `lem:dualread`(i)'s `E^∨` at the table's own letter
pair. -/
private def negTable (T : WalkTable) : WalkTable where
  dLet := T.dLet
  uLet := T.uLet
  step := fun j v => ⟨(T.step j v).content, poly.neg (T.step j v).coords⟩
  tr := fun j v => ⟨(T.tr j v).content, poly.neg (T.tr j v).coords⟩
  letters := T.letters
  step_content := T.step_content
  tr_content := T.tr_content
  step_sized := by
    intro j v
    show (poly.neg (T.step j v).coords).length
      = (places.monomialsAt (T.step j v).content).length
    rw [poly.length_neg]
    exact T.step_sized j v
  tr_sized := by
    intro j v
    show (poly.neg (T.tr j v).coords).length
      = (places.monomialsAt (T.tr j v).content).length
    rw [poly.length_neg]
    exact T.tr_sized j v
  step_congr := fun j v w hc hq =>
    poly.swapMap_oneValue (T.step_congr j v w hc hq)
  step_vecAdd := by
    intro j mu x y hxy
    show poly.oneValue
      ((T.step j ⟨mu, elim.vecAdd x y⟩).coords.map BPair.swap)
      (elim.vecAdd ((T.step j ⟨mu, x⟩).coords.map BPair.swap)
        ((T.step j ⟨mu, y⟩).coords.map BPair.swap))
    rw [← elim.vecAdd_swapMap]
    exact poly.swapMap_oneValue (T.step_vecAdd j mu x y hxy)
  step_vecScale := by
    intro j mu c x
    show poly.oneValue
      ((T.step j ⟨mu, elim.vecScale c x⟩).coords.map BPair.swap)
      (elim.vecScale c ((T.step j ⟨mu, x⟩).coords.map BPair.swap))
    rw [elim.vecScale_swapMap]
    exact poly.swapMap_oneValue (T.step_vecScale j mu c x)
  tr_congr := fun j v w hc hq =>
    poly.swapMap_oneValue (T.tr_congr j v w hc hq)
  tr_vecAdd := by
    intro j mu x y hxy
    show poly.oneValue
      ((T.tr j ⟨mu, elim.vecAdd x y⟩).coords.map BPair.swap)
      (elim.vecAdd ((T.tr j ⟨mu, x⟩).coords.map BPair.swap)
        ((T.tr j ⟨mu, y⟩).coords.map BPair.swap))
    rw [← elim.vecAdd_swapMap]
    exact poly.swapMap_oneValue (T.tr_vecAdd j mu x y hxy)
  tr_vecScale := by
    intro j mu c x
    show poly.oneValue
      ((T.tr j ⟨mu, elim.vecScale c x⟩).coords.map BPair.swap)
      (elim.vecScale c ((T.tr j ⟨mu, x⟩).coords.map BPair.swap))
    rw [elim.vecScale_swapMap]
    exact poly.swapMap_oneValue (T.tr_vecScale j mu c x)
  step_unitTail := fun j v h =>
    poly.unitTail_swapMap _ (T.step_unitTail j v h)
  tr_unitTail := fun j v h =>
    poly.unitTail_swapMap _ (T.tr_unitTail j v h)
  step_vac := fun j v h => poly.unitTail_swapMap _ (T.step_vac j v h)
  tr_vac := fun j v h => poly.unitTail_swapMap _ (T.tr_vac j v h)
  adjoint := by
    intro j v z hsv hsz hj hD hZ
    show (elim.dotP (poly.neg (T.step j v).coords) z.coords).oneValue
      (elim.dotP v.coords ((T.tr j z).coords.map BPair.swap))
    rw [elim.dotP_swap_left, elim.dotP_swapMap]
    exact ground.swap_congr (T.adjoint j v z hsv hsz hj hD hZ)
  cross_occ := by
    intro j v hs hj hD hU
    refine poly.oneValue_trans
      (elim.polyOne_vecAdd _ _ _ _
        (negTr_arg T j (T.step j v).content (T.step j v).coords)
        (poly.oneValue_refl _)
        (negTr_arg_len T j (T.step j v).content (T.step j v).coords)
        rfl) ?_
    refine poly.oneValue_trans (T.cross_occ j v hs hj hD hU) ?_
    exact elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_symm
        (negStep_arg T j (T.tr j v).content (T.tr j v).coords))
      (poly.oneValue_refl _)
      (negStep_arg_len T j (T.tr j v).content (T.tr j v).coords).symm
      rfl
  cross_vacU := by
    intro j v hs hj hD hU0
    exact poly.oneValue_trans
      (negTr_arg T j (T.step j v).content (T.step j v).coords)
      (T.cross_vacU j v hs hj hD hU0)
  cross_vacD := by
    intro j v hs hj hD0 hU
    exact poly.oneValue_trans
      (negStep_arg T j (T.tr j v).content (T.tr j v).coords)
      (T.cross_vacD j v hs hj hD0 hU)
  comm := by
    intro l j v hlj hs hl hj2
    match T.comm l j v hlj hs hl hj2 with
    | ⟨hc, hlen, hq⟩ =>
      refine ⟨?_, ?_, ?_⟩
      · have h1 : (T.tr j ⟨(T.step l v).content,
            poly.neg (T.step l v).coords⟩).content
          = (T.tr j (T.step l v)).content := by
          rw [T.tr_content j ⟨(T.step l v).content,
              poly.neg (T.step l v).coords⟩,
            T.tr_content j (T.step l v)]
        have h2 : (T.step l ⟨(T.tr j v).content,
            poly.neg (T.tr j v).coords⟩).content
          = (T.step l (T.tr j v)).content := by
          rw [T.step_content l ⟨(T.tr j v).content,
              poly.neg (T.tr j v).coords⟩,
            T.step_content l (T.tr j v)]
        exact h1.trans (hc.trans h2.symm)
      · show (poly.neg (T.tr j ⟨(T.step l v).content,
            poly.neg (T.step l v).coords⟩).coords).length
          = (poly.neg (T.step l ⟨(T.tr j v).content,
            poly.neg (T.tr j v).coords⟩).coords).length
        rw [negTr_arg_len T j (T.step l v).content (T.step l v).coords,
          negStep_arg_len T l (T.tr j v).content (T.tr j v).coords]
        exact hlen
      · exact poly.oneValue_trans
          (negTr_arg T j (T.step l v).content (T.step l v).coords)
          (poly.oneValue_trans hq
            (poly.oneValue_symm
              (negStep_arg T l (T.tr j v).content (T.tr j v).coords)))

/-- The dual table: `lem:dualread`(i)'s construction — `E^∨_{ij}`
the balance partner of `E_{ji}` — the dual lowering at the adjacent
pair the partner of the matrix units' exchanged action, its words
the dual word family. -/
def dualTable : WalkTable := negTable (exchTable lowerTable)

/-- The dual lowering at the adjacent pair is the dual table's
step. -/
theorem dact_step (j : Nat) (v : HVec) :
    dact (j + 1) j v = dualTable.step j v := rfl

/-- The dual raising at the adjacent pair is the dual table's
transpose. -/
theorem dact_tr (j : Nat) (v : HVec) :
    dact j (j + 1) v = dualTable.tr j v := rfl

/-- The target's top: at an interior letter the exhibit's adjacent
raising reads the sum's unit. -/
private theorem top_e (b : Shape) : ∀ j, j + 1 < b.length →
    poly.unitTail (lowerTable.tr j (exhibit b)).coords := by
  intro j hj
  show poly.unitTail (elim.matVec
    (units.matUnitAt (moveAt j (j + 1) (exhibit b).content)
      (exhibit b).content j (j + 1)) (exhibit b).coords)
  rw [content_exhibit b]
  exact exhibit_top_all b j (j + 1) (Nat.lt_succ_self j) hj

/-- The reversal member is the dual top: at an interior letter its
dual raising reads the sum's unit. -/
private theorem top_g (a : Shape) (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse) :
    ∀ j, j + 1 < a.length →
      poly.unitTail (dualTable.tr j g).coords :=
  fun j hj => dualTop a g hg hgc j (j + 1) (Nat.lt_succ_self j) hj

/-- Every word image of the target's top keeps the first block's
letter width. -/
private theorem widthE (a b : Shape) (hba : b.length = a.length)
    (ws : List Nat) :
    (wactT lowerTable ws (exhibit b)).content.length = a.length := by
  rw [wactT_content lowerTable ws (exhibit b), wcontentT_len,
    content_exhibit b, places.length_rowList b]
  exact hba

/-- Every dual word image of a span member keeps the block's letter
width. -/
private theorem widthG (a : Shape) (g : HVec) (hg : g ∈ blockSpan a)
    (ws : List Nat) :
    (wactT dualTable ws g).content.length = a.length := by
  rw [wactT_content dualTable ws g, wcontentT_len]
  exact blockSpan_width a g hg

/-- The complement invariant at the join: wherever a word's
lowering image at the target's top and its dual image at the
reversal member are both off the unit tail, the two contents join
to the full columns — the lowering moves the letter pair down and
the dual moves it up, so the joined family is carried across the
step's round trip and the join's own entry is occupied. -/
theorem dualLive (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse) :
    ∀ ws : List Nat, (∀ l ∈ ws, l + 1 < a.length) →
      ¬ poly.unitTail (wact ws (exhibit b)).coords →
      ¬ poly.unitTail (wactT dualTable ws g).coords →
      List.zipWith (fun u w => u + w) (wact ws (exhibit b)).content
        (wactT dualTable ws g).content = List.replicate a.length m := by
  intro ws
  induction ws with
  | nil =>
    intro _ _ _
    show List.zipWith (fun u w => u + w) (exhibit b).content g.content
      = List.replicate a.length m
    rw [content_exhibit b, hgc]
    exact hjoin
  | cons l t ih =>
    intro hb hlive hlive'
    have hla : l + 1 < a.length := hb l (.head _)
    have hiv : ¬ poly.unitTail
        (wactT lowerTable t (exhibit b)).coords := by
      intro hu
      exact hlive (lowerTable.step_unitTail l
        (wactT lowerTable t (exhibit b)) hu)
    have hiv' : ¬ poly.unitTail (wactT dualTable t g).coords := by
      intro hu
      exact hlive' (dualTable.step_unitTail l
        (wactT dualTable t g) hu)
    have hIH : List.zipWith (fun u w => u + w)
        (wactT lowerTable t (exhibit b)).content
        (wactT dualTable t g).content = List.replicate a.length m :=
      ih (fun x hx => hb x (.tail _ hx)) hiv hiv'
    have hocc : 0 < ground.getAt 0
        (wactT lowerTable t (exhibit b)).content l := by
      match Nat.eq_zero_or_pos (ground.getAt 0
          (wactT lowerTable t (exhibit b)).content l) with
      | .inr hp => exact hp
      | .inl hz =>
        exact absurd (lowerTable.step_vac l
          (wactT lowerTable t (exhibit b)) hz) hlive
    have hocc' : 0 < ground.getAt 0
        (wactT dualTable t g).content (l + 1) := by
      match Nat.eq_zero_or_pos (ground.getAt 0
          (wactT dualTable t g).content (l + 1)) with
      | .inr hp => exact hp
      | .inl hz =>
        exact absurd (dualTable.step_vac l (wactT dualTable t g) hz)
          hlive'
    have hzip : ground.getAt 0 (List.zipWith (fun u w => u + w)
        (wactT lowerTable t (exhibit b)).content
        (wactT dualTable t g).content) l
      = ground.getAt 0 (wactT lowerTable t (exhibit b)).content l
        + ground.getAt 0 (wactT dualTable t g).content l :=
      ground.getAt_zipWith 0 0 0 (fun u w => u + w) _ _ l
        (by rw [widthE a b hba t]; exact Nat.lt_of_succ_lt hla)
        (by rw [widthG a g hg t]; exact Nat.lt_of_succ_lt hla)
    rw [hIH, ground.getAt_replicate 0 m a.length l
      (Nat.lt_of_succ_lt hla)] at hzip
    have hbnd : 0 < ground.getAt 0 (List.replicate a.length m) (l + 1) := by
      rw [ground.getAt_replicate 0 m a.length (l + 1) hla, hzip]
      exact Nat.lt_of_lt_of_le hocc (Nat.le_add_right _ _)
    show List.zipWith (fun u w => u + w)
      (lowerTable.step l (wactT lowerTable t (exhibit b))).content
      (dualTable.step l (wactT dualTable t g)).content
      = List.replicate a.length m
    rw [lowerTable.step_content l (wactT lowerTable t (exhibit b)),
      dualTable.step_content l (wactT dualTable t g)]
    show List.zipWith (fun u w => u + w)
      (moveAt (l + 1) l (wactT lowerTable t (exhibit b)).content)
      (moveAt l (l + 1) (wactT dualTable t g).content)
      = List.replicate a.length m
    rw [moveAt_zipWith_left (l + 1) l _ _ hocc,
      moveAt_zipWith_right l (l + 1) _ _ hocc', hIH,
      moveAt_round_at (l + 1) l (List.replicate a.length m) hbnd]

/-- Clause 10 of `lem:dualread`(iii): the dual word family at the
reversal member and the word family at the target's top read one
Gram at the two tops' self-pairings' scales — at the graded
pairing, every word pair's value at the first top against the
second's self-pairing is its value at the second top against the
first's, the crossing scalars tied cross-added by the join's
complement invariant. -/
theorem dualGram (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (ws ws' : List Nat)
    (hb : ∀ l ∈ ws, l + 1 < a.length) (hb' : ∀ l ∈ ws', l + 1 < a.length) :
    (dotG (wact ws (exhibit b)) (wact ws' (exhibit b))
        * elim.dotP g.coords g.coords).oneValue
      (dotG (wactT dualTable ws g) (wactT dualTable ws' g)
        * elim.dotP (exhibit b).coords (exhibit b).coords) := by
  refine wordGramT lowerTable dualTable a.length (exhibit b) g
    (exhibit_sized b) ((lowerspan.spanReads a).1 g hg)
    (by rw [content_exhibit b, places.length_rowList b]; exact hba)
    (blockSpan_width a g hg)
    (fun j hj => top_e b j (by rw [hba]; exact hj))
    (top_g a g hg hgc) ?_ ws ws' hb hb'
  intro ws0 j hjd hbb hlv hlv'
  have hlive : List.zipWith (fun u w => u + w)
      (wactT lowerTable ws0 (exhibit b)).content
      (wactT dualTable ws0 g).content = List.replicate a.length m :=
    dualLive a b m hba hjoin g hg hgc ws0 hbb hlv hlv'
  have hz1 : ground.getAt 0 (wactT lowerTable ws0 (exhibit b)).content (j + 1)
      + ground.getAt 0 (wactT dualTable ws0 g).content (j + 1) = m := by
    rw [← ground.getAt_zipWith 0 0 0 (fun u w => u + w)
      (wactT lowerTable ws0 (exhibit b)).content
      (wactT dualTable ws0 g).content (j + 1)
      (by rw [widthE a b hba ws0]; exact hjd)
      (by rw [widthG a g hg ws0]; exact hjd)]
    rw [hlive]
    exact ground.getAt_replicate 0 m a.length (j + 1) hjd
  have hz0 : ground.getAt 0 (wactT lowerTable ws0 (exhibit b)).content j
      + ground.getAt 0 (wactT dualTable ws0 g).content j = m := by
    rw [← ground.getAt_zipWith 0 0 0 (fun u w => u + w)
      (wactT lowerTable ws0 (exhibit b)).content
      (wactT dualTable ws0 g).content j
      (by rw [widthE a b hba ws0]; exact Nat.lt_of_succ_lt hjd)
      (by rw [widthG a g hg ws0]; exact Nat.lt_of_succ_lt hjd)]
    rw [hlive]
    exact ground.getAt_replicate 0 m a.length j (Nat.lt_of_succ_lt hjd)
  show ground.getAt 0 (wactT lowerTable ws0 (exhibit b)).content (j + 1)
      + ground.getAt 0 (wactT dualTable ws0 g).content (j + 1)
    = ground.getAt 0 (wactT dualTable ws0 g).content j
      + ground.getAt 0 (wactT lowerTable ws0 (exhibit b)).content j
  rw [hz1, Nat.add_comm (ground.getAt 0 (wactT dualTable ws0 g).content j)
    (ground.getAt 0 (wactT lowerTable ws0 (exhibit b)).content j), hz0]

/-! `lem:dualread`(i)'s evaluation tier at the graded pairing: the
coordinate fold within one content with distinct contents pairing
at the sum's unit, and the evaluation's equivariance read at every
letter pair and every member pair — the occupied case
`blockcount.unit_adjoint`'s walk through `ev_equiv`, the vacant
source's image the unit tail (`units.matVec_null_unocc`), and the
mismatched-content guards refusing together at the moves' round
trips. -/

/-- The evaluation's equivariance at the graded pairing: a letter
pair's Leibniz image at a member pair reads the sum's unit — the
two guards meet exactly at the moves' round trips, the occupied
case the transpose walk with the partner joined, and a vacant
source's image the unit tail. -/
theorem ev_equivG (p q : Nat) (a b : HVec)
    (hpb : p < b.content.length) (hqb : q < b.content.length)
    (hpq : ¬ p = q) (hsa : sized a) (hsb : sized b) :
    (dotG (dact p q b) a + dotG (act p q a) b).oneValue
      BPair.unit := by
  show ((if (dact p q b).content = a.content
      then elim.dotP (dact p q b).coords a.coords else BPair.unit)
    + (if (act p q a).content = b.content
      then elim.dotP (act p q a).coords b.coords
      else BPair.unit)).oneValue BPair.unit
  by_cases hg1 : (dact p q b).content = a.content
  · have hg1' : moveAt q p b.content = a.content := hg1
    by_cases hocc : 0 < ground.getAt 0 b.content p
    · have hg2 : (act p q a).content = b.content := by
        show moveAt p q a.content = b.content
        rw [← hg1']
        exact moveAt_round_at p q b.content hocc
      rw [if_pos hg1, if_pos hg2]
      have hev := ev_equiv p q b.content hqb hpq hocc
        b.coords a.coords hsb
        (by rw [hsa, hg1'])
      have hA : (⟨moveAt q p b.content, a.coords⟩ : HVec) = a := by
        rw [hg1']
      rw [hA] at hev
      rw [elim.dotP_comm (act p q a).coords b.coords]
      exact hev
    · have hz : ground.getAt 0 b.content p = 0 := by
        match he : ground.getAt 0 b.content p with
        | 0 => rfl
        | n + 1 =>
          exact absurd (by rw [he]; exact Nat.succ_pos n) hocc
      have hnull : poly.unitTail (dact p q b).coords := by
        show poly.unitTail (poly.neg (elim.matVec
          (units.matUnitAt (moveAt q p b.content) b.content q p)
          b.coords))
        exact poly.unitTail_swapMap _
          (units.matVec_null_unocc _ b.content q p hz b.coords)
      have hng2 : ¬ ((act p q a).content = b.content) := by
        intro hg2
        have hg2' : moveAt p q a.content = b.content := hg2
        rw [← hg1'] at hg2'
        have hcomp : moveAt p q (moveAt q p b.content)
            = bumpAt p b.content := by
          show bumpAt p (dipAt q (bumpAt q (dipAt p b.content)))
            = bumpAt p b.content
          rw [ground.dipAt_of_zero p b.content hz,
            ground.dipAt_bumpAt_self]
        rw [hcomp] at hg2'
        have hgc := congrArg (fun l => ground.getAt 0 l p) hg2'
        rw [ground.getAt_bumpAt_self p b.content hpb, hz] at hgc
        exact Nat.noConfusion hgc
      rw [if_pos hg1, if_neg hng2]
      refine BPair.oneValue_trans
        (BPair.add_congr (elim.dotP_null_tail_left _ _ hnull)
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_of_eqMem rfl
  · by_cases hg2 : (act p q a).content = b.content
    · have hnq : ground.getAt 0 a.content q = 0 := by
        match he : ground.getAt 0 a.content q with
        | 0 => rfl
        | n + 1 =>
          have hocc2 : 0 < ground.getAt 0 a.content q := by
            rw [he]
            exact Nat.succ_pos n
          have hrt := moveAt_round_at q p a.content hocc2
          have hg2' : moveAt p q a.content = b.content := hg2
          rw [hg2'] at hrt
          exact absurd
            (show (dact p q b).content = a.content from hrt) hg1
      have hnull2 : poly.unitTail (act p q a).coords := by
        show poly.unitTail (elim.matVec
          (units.matUnitAt (moveAt p q a.content) a.content p q)
          a.coords)
        exact units.matVec_null_unocc _ a.content p q hnq a.coords
      rw [if_neg hg1, if_pos hg2]
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (elim.dotP_null_tail_left _ _ hnull2)) ?_
      exact BPair.oneValue_of_eqMem rfl
    · rw [if_neg hg1, if_neg hg2]
      exact BPair.oneValue_of_eqMem rfl

/-! `lem:dualread`(i)'s coevaluation tier: the Gram-dual
coevaluation at a stated independent spanning list is the
determinant-scaled identity datum, `coev := Σ_{j,k} A_{jk}
y_j ⊗ y_k` with `A` the Gram's adjugate against its determinant —
the grading splitting the Gram at one block per occupied content,
so the adjugate collects each block's own at the further blocks'
determinants — and the coevaluation is equivariant to the unit:
a letter pair's Leibniz image paired against a member pair
collects at the adjugate identity to the determinant against one
crossed pairing per summand, the transpose identity with the
fold's exchange joining the two at partners. -/

/-- The block's determinant at a stated content: the content
group's own Gram determinant. -/
private def blockDet (Y : List HVec) (nu : List Nat) : BPair :=
  elim.detL (elim.gramM
    (groupAt Y nu))

/-- Every occupied content's determinant, the graded Gram's
own. -/
def detAll (Y : List HVec) : BPair :=
  (ground.dedupL (Y.map HVec.content)).foldl
    (fun acc nu => acc * blockDet Y nu) (BPair.ofNat 1)

/-- The further groups' determinants at a withdrawn content: the
skipping product over the occupied contents. -/
private def coScale (Y : List HVec) (mu : List Nat) : BPair :=
  (ground.dedupL (Y.map HVec.content)).foldl
    (fun acc nu => if nu = mu then acc else acc * blockDet Y nu)
    (BPair.ofNat 1)

/-- The Gram-dual coevaluation's data at a stated list: per
occupied content the group's adjugate entries at the further
groups' determinants, the graded Gram's own adjugate — the
determinant-scaled identity datum (`lem:dualread`(i)'s
display). -/
def coevData (Y : List HVec) : List (BPair × HVec × HVec) :=
  (ground.dedupL (Y.map HVec.content)).flatMap (fun mu =>
    let grp := Y.filter (fun w => w.content == mu)
    let G := elim.gramM (grp.map HVec.coords)
    let s := coScale Y mu
    (List.range grp.length).flatMap (fun j =>
      (List.range grp.length).map (fun k =>
        (s * ground.getAt BPair.unit (elim.cofVec G k) j,
          ground.getAt (⟨[], []⟩ : HVec) grp j,
          ground.getAt (⟨[], []⟩ : HVec) grp k))))

/-- A doubly indexed family at the sum's unit folds to the unit. -/
private theorem block_null (n : Nat) (T : Nat → Nat → BPair)
    (h : ∀ j k, j < n → k < n → (T j k).oneValue BPair.unit) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k => T j k)
        (List.range n)) (List.range n)).oneValue BPair.unit :=
  ground.foldB_nullRange _ n (fun j hj =>
    ground.foldB_nullRange _ n (fun k hk => h j k hj hk))

/-- The group's Gram entry at a member's key: the graded pairing
against that member reads the block's own entry, the group's
contents equal and the pairing's two orders one value. -/
private theorem grp_entry (grp : List HVec) (mu : List Nat)
    (hcont : ∀ w ∈ grp, w.content = mu)
    (v : HVec) (i : Nat) (hi : i < grp.length)
    (hv : ground.getAt (⟨[], []⟩ : HVec) grp i = v) :
    ∀ k, k < grp.length →
      dotG (ground.getAt (⟨[], []⟩ : HVec) grp k) v
        = ground.getAt BPair.unit
          (ground.getAt [] (elim.gramM (grp.map HVec.coords)) i)
          k := by
  subst hv
  intro k hk
  have hLl : (grp.map HVec.coords).length = grp.length :=
    ground.length_map _ grp
  have hck : (ground.getAt (⟨[], []⟩ : HVec) grp k).content = mu :=
    hcont _ (ground.mem_getAt _ grp k hk)
  have hci : (ground.getAt (⟨[], []⟩ : HVec) grp i).content = mu :=
    hcont _ (ground.mem_getAt _ grp i hi)
  rw [elim.gramM_entry (grp.map HVec.coords) i k
      (by rw [hLl]; exact hi) (by rw [hLl]; exact hk),
    ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
      HVec.coords grp i hi,
    ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
      HVec.coords grp k hk]
  show (if (ground.getAt (⟨[], []⟩ : HVec) grp k).content
        = (ground.getAt (⟨[], []⟩ : HVec) grp i).content
      then elim.dotP (ground.getAt (⟨[], []⟩ : HVec) grp k).coords
        (ground.getAt (⟨[], []⟩ : HVec) grp i).coords
      else BPair.unit)
    = elim.dotP (ground.getAt (⟨[], []⟩ : HVec) grp i).coords
      (ground.getAt (⟨[], []⟩ : HVec) grp k).coords
  rw [if_pos (show (ground.getAt (⟨[], []⟩ : HVec) grp k).content
      = (ground.getAt (⟨[], []⟩ : HVec) grp i).content from by
    rw [hck, hci]), elim.dotP_comm]

/-- The group's square order, the Gram at the group's own count. -/
private theorem grp_sqAt (grp : List HVec) :
    elim.sqAt (elim.gramM (grp.map HVec.coords)) grp.length := by
  rw [← show (grp.map HVec.coords).length = grp.length from
    ground.length_map _ grp]
  exact elim.gram_sqAt (grp.map HVec.coords)

/-- The group's Gram is symmetric at the group's own count. -/
private theorem grp_sym (grp : List HVec) :
    ∀ i < grp.length, ∀ j < grp.length,
      ground.getAt BPair.unit (ground.getAt []
          (elim.gramM (grp.map HVec.coords)) i) j
        = ground.getAt BPair.unit (ground.getAt []
          (elim.gramM (grp.map HVec.coords)) j) i :=
  fun i hi j hj => elim.gramM_symm (grp.map HVec.coords) i j
    (by rw [ground.length_map _ grp]; exact hi)
    (by rw [ground.length_map _ grp]; exact hj)

/-- The index fold of two families' entries is their pairing, the
two families read at their shared order. -/
private theorem fold_dotP (X V : List BPair) (m : Nat)
    (hX : X.length = m) (hV : V.length = m) :
    ground.famFold BPair.add BPair.unit
      (fun j => ground.getAt BPair.unit X j
        * ground.getAt BPair.unit V j)
      (List.range m) = elim.dotP X V := by
  rw [← elim.dotP_map_range
      (fun j => ground.getAt BPair.unit V j) m X hX,
    ground.range_map_getAt BPair.unit m V hV]

/-- The adjugate solve's entry as the key fold: the data against
the cofactor vectors' entries at the stated column key. -/
private theorem adjP_entry (G : elim.Mat) (P : List BPair)
    (hP : P.length = G.length) (j : Nat) (hj : j < G.length) :
    (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit P k
        * ground.getAt BPair.unit (elim.cofVec G k) j)
      (List.range G.length)).oneValue
      (ground.getAt BPair.unit (elim.adjP G P) j) := by
  have hCs : elim.rowsLen G.length
      ((List.range G.length).map (fun k => elim.cofVec G k)) :=
    elim.cofRows_rowsLen G
  have hCl : ((List.range G.length).map
      (fun k => elim.cofVec G k)).length = G.length :=
    elim.cofRows_len G
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => ground.getAt BPair.unit P k
        * ground.getAt BPair.unit
          (((List.range G.length).map
            (fun k => elim.cofVec G k)).map
            (fun r => ground.getAt BPair.unit r j)) k)
      (List.range G.length) (fun k hk => ?_)) ?_
  · rw [ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => ground.getAt BPair.unit r j) _ k
      (by rw [hCl]; exact ground.ltOfMem hk),
    ground.getAt_map 0 ([] : List BPair)
      (fun k => elim.cofVec G k) (List.range G.length) k
      (by rw [ground.length_range]; exact ground.ltOfMem hk),
    ground.getAt_range G.length k (ground.ltOfMem hk)]
    exact BPair.oneValue_refl _
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (fold_dotP P _ G.length hP
        (by rw [ground.length_map, hCl]))) ?_
    refine BPair.oneValue_symm ?_
    show (ground.getAt BPair.unit
        (elim.combo G.length P
          ((List.range G.length).map
            (fun k => elim.cofVec G k))) j).oneValue _
    exact elim.combo_getAt G.length P
      ((List.range G.length).map (fun k => elim.cofVec G k)) j
      hCs hj

/-- The block's first summand collects at the adjugate fold: the
fold over the second key against the cofactor vectors' entries is
the adjugate solve's own coordinate at the second slots' values,
and the first key's fold carries it against the walked family. -/
private theorem block_oneF (grp : List HVec) (s : BPair)
    (A Ψ : HVec → BPair) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (A (ground.getAt (⟨[], []⟩ : HVec) grp j)
            * Ψ (ground.getAt (⟨[], []⟩ : HVec) grp k)))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      (s * ground.famFold BPair.add BPair.unit (fun j =>
        A (ground.getAt (⟨[], []⟩ : HVec) grp j)
          * ground.getAt BPair.unit
            (elim.adjP (elim.gramM (grp.map HVec.coords))
              (grp.map Ψ)) j)
        (List.range grp.length)) := by
  have hGl : (elim.gramM (grp.map HVec.coords)).length
      = grp.length := by
    rw [elim.sqAt_len (elim.gram_sqAt (grp.map HVec.coords)),
      ground.length_map]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => (s * A (ground.getAt (⟨[], []⟩ : HVec) grp j))
        * ground.getAt BPair.unit
          (elim.adjP (elim.gramM (grp.map HVec.coords))
            (grp.map Ψ)) j)
      (List.range grp.length) (fun j hj0 => ?_)) ?_
  · have hj : j < grp.length := ground.ltOfMem hj0
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => (s * A (ground.getAt (⟨[], []⟩ : HVec) grp j))
          * (ground.getAt BPair.unit (grp.map Ψ) k
            * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j))
        (List.range grp.length) (fun k hk0 => ?_)) ?_
    · refine BPair.oneValue_of_eq ?_
      rw [ground.getAt_map (⟨[], []⟩ : HVec) BPair.unit Ψ grp k
          (ground.ltOfMem hk0),
        BPair.mul_mul_mul_comm s
          (ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          (A (ground.getAt (⟨[], []⟩ : HVec) grp j))
          (Ψ (ground.getAt (⟨[], []⟩ : HVec) grp k)),
        BPair.mul_comm
          (ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          (Ψ (ground.getAt (⟨[], []⟩ : HVec) grp k))]
    · refine BPair.oneValue_trans
        (ground.foldB_mul_left _ _ (List.range grp.length)) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      rw [← hGl]
      exact adjP_entry (elim.gramM (grp.map HVec.coords)) (grp.map Ψ)
        (by rw [ground.length_map, hGl]) j (by rw [hGl]; exact hj)
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (ground.famFold_congr_all BPair.add BPair.unit _ _
          (fun j => BPair.mul_assoc s _ _)
          (List.range grp.length))) ?_
    exact ground.foldB_mul_left _ _ (List.range grp.length)



/-- The block's first summand collapses at the adjugate identity:
the moved member's crossed pairing against the further member's
own, the fold over the second key the adjugate's entry and the
fold over the first the determinant at the member's key. -/
private theorem block_one (grp : List HVec) (mu : List Nat)
    (hcont : ∀ w ∈ grp, w.content = mu)
    (s : BPair) (p q : Nat) (a b : HVec) (hb : b ∈ grp) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (dotG (dact p q
                (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
            * dotG (ground.getAt (⟨[], []⟩ : HVec) grp k) b))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      (s * elim.detL (elim.gramM (grp.map HVec.coords))
        * dotG (dact p q b) a) := by
  have hGl : (elim.gramM (grp.map HVec.coords)).length
      = grp.length := by
    rw [elim.sqAt_len (elim.gram_sqAt (grp.map HVec.coords)),
      ground.length_map]
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) hb with
  | ⟨b', hb'l, hb'e⟩ =>
    have hB := grp_entry grp mu hcont b b' hb'l hb'e
    refine BPair.oneValue_trans
      (block_oneF grp s (fun w => dotG (dact p q w) a)
        (fun w => dotG w b)) ?_
    have hentry : ∀ j, j < grp.length →
        (ground.getAt BPair.unit
          (elim.adjP (elim.gramM (grp.map HVec.coords))
            (grp.map (fun w => dotG w b))) j).oneValue
          (if j = b'
            then elim.detL (elim.gramM (grp.map HVec.coords))
            else BPair.unit) := by
      intro j hj
      refine BPair.oneValue_trans
        (BPair.oneValue_symm
          (adjP_entry (elim.gramM (grp.map HVec.coords))
            (grp.map (fun w => dotG w b))
            (by rw [ground.length_map, hGl]) j
            (by rw [hGl]; exact hj))) ?_
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun k => dotG (ground.getAt (⟨[], []⟩ : HVec) grp k) b
            * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          (List.range (elim.gramM (grp.map HVec.coords)).length)
          (fun k hk => by
            rw [ground.getAt_map (⟨[], []⟩ : HVec) BPair.unit
              (fun w => dotG w b) grp k
              (by rw [← hGl]; exact ground.ltOfMem hk)]
            exact BPair.oneValue_refl _)) ?_
      rw [hGl]
      exact elim.adjP_row_fold (elim.gramM (grp.map HVec.coords))
        (grp_sqAt grp) (grp_sym grp) b' j hb'l hj
        (fun k => dotG (ground.getAt (⟨[], []⟩ : HVec) grp k) b) hB
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s)
        (ground.foldB_congr_members _
          (fun j => dotG (dact p q
              (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
            * (if j = b'
              then elim.detL (elim.gramM (grp.map HVec.coords))
              else BPair.unit))
          (List.range grp.length)
          (fun j hj => BPair.mul_congr (BPair.oneValue_refl _)
            (hentry j (ground.ltOfMem hj))))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s)
        (ground.foldB_pickRange _ b'
          (dotG (dact p q b) a
            * elim.detL (elim.gramM (grp.map HVec.coords)))
          grp.length hb'l
          (by rw [if_pos (show b' = b' from rfl), hb'e]
              exact BPair.oneValue_refl _)
          (fun t _ hti => by
            rw [if_neg hti]
            exact BPair.mul_unit _))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_comm (dotG (dact p q b) a)
        (elim.detL (elim.gramM (grp.map HVec.coords))),
      ← BPair.mul_assoc]

/-- The block's second summand collapses at the cofactor vector's
two reads with an opaque second slot: the exchanged fold over the
first key reads the determinant at the member's key with the sum's
unit at every further key, the slot's own value read at the
member. -/
private theorem block_twoF (grp : List HVec) (mu : List Nat)
    (hcont : ∀ w ∈ grp, w.content = mu)
    (s : BPair) (a : HVec) (ha : a ∈ grp) (Φ : HVec → BPair) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
            * Φ (ground.getAt (⟨[], []⟩ : HVec) grp k)))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      (s * elim.detL (elim.gramM (grp.map HVec.coords))
        * Φ a) := by
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) ha with
  | ⟨a', ha'l, ha'e⟩ =>
    have hA := grp_entry grp mu hcont a a' ha'l ha'e
    refine BPair.oneValue_trans
      (ground.foldB_swapL (fun j k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
            * Φ (ground.getAt (⟨[], []⟩ : HVec) grp k)))
        (List.range grp.length) (List.range grp.length)) ?_
    have hinner : ∀ k, k < grp.length →
        (ground.famFold BPair.add BPair.unit (fun j =>
          (s * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
            * (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
              * Φ (ground.getAt (⟨[], []⟩ : HVec) grp k)))
          (List.range grp.length)).oneValue
          ((s * Φ (ground.getAt (⟨[], []⟩ : HVec) grp k))
            * (if k = a'
              then elim.detL (elim.gramM (grp.map HVec.coords))
              else BPair.unit)) := by
      intro k hk
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (ground.famFold_congr_all BPair.add BPair.unit _
            (fun j => (s * Φ (ground.getAt (⟨[], []⟩ : HVec) grp k))
              * (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
                * ground.getAt BPair.unit
                  (elim.cofVec
                    (elim.gramM (grp.map HVec.coords)) k) j))
            (fun j => by
              rw [BPair.mul_comm
                  (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a)
                  (Φ (ground.getAt (⟨[], []⟩ : HVec) grp k)),
                BPair.mul_mul_mul_comm s
                  (ground.getAt BPair.unit
                    (elim.cofVec
                      (elim.gramM (grp.map HVec.coords)) k) j)
                  (Φ (ground.getAt (⟨[], []⟩ : HVec) grp k))
                  (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a),
                BPair.mul_comm
                  (ground.getAt BPair.unit
                    (elim.cofVec
                      (elim.gramM (grp.map HVec.coords)) k) j)
                  (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a)])
            (List.range grp.length))) ?_
      refine BPair.oneValue_trans
        (ground.foldB_mul_left _ _ (List.range grp.length)) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      exact elim.cofVec_col_fold (elim.gramM (grp.map HVec.coords))
        (grp_sqAt grp) a' k ha'l hk
        (fun j => dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a) hA
    refine ground.foldB_pickRange _ a' _ grp.length ha'l ?_ ?_
    · refine BPair.oneValue_trans (hinner a' ha'l) ?_
      rw [if_pos (show a' = a' from rfl), ha'e]
      refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_assoc, BPair.mul_comm (Φ a)
        (elim.detL (elim.gramM (grp.map HVec.coords))),
        ← BPair.mul_assoc]
    · intro t htn hti
      refine BPair.oneValue_trans (hinner t htn) ?_
      rw [if_neg hti]
      exact BPair.mul_unit _

/-- The block's scale against its own determinant reads every
group's determinant, the content occupied once in the distinct
index. -/
private theorem scale_detAll (Y : List HVec) (mu : List Nat)
    (h1 : ground.countOf mu
      (ground.dedupL (Y.map HVec.content)) = 1) :
    coScale Y mu * blockDet Y mu = detAll Y :=
  ground.foldl_skip BPair.mul BPair.mul_comm BPair.mul_assoc
    (blockDet Y) mu
    (ground.dedupL (Y.map HVec.content)) (BPair.ofNat 1) h1

/-- The block at one content over a stated second-slot map: the
distributive split hands the two summand folds their own collapses
— the first at the stated read `E`, the second at the opaque-slot
collapse read at the member — with every off-guard arm at the
sum's unit, the slot keeping each member's content. -/
private theorem group_readF (Sl : HVec → HVec) (grp : List HVec)
    (mu : List Nat)
    (hcont : ∀ w ∈ grp, w.content = mu)
    (hslot : ∀ w ∈ grp, (Sl w).content = w.content)
    (s D E : BPair)
    (hsd : s * elim.detL (elim.gramM (grp.map HVec.coords)) = D)
    (p q : Nat) (a b : HVec)
    (hag : mu = a.content → a ∈ grp)
    (hE : mu = b.content →
      (ground.famFold BPair.add BPair.unit (fun j =>
        ground.famFold BPair.add BPair.unit (fun k =>
          (s * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
            * (dotG (dact p q
                  (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
              * dotG (Sl (ground.getAt (⟨[], []⟩ : HVec) grp k)) b))
          (List.range grp.length))
        (List.range grp.length)).oneValue E) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (dotG (dact p q
                (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
              * dotG (Sl (ground.getAt (⟨[], []⟩ : HVec) grp k)) b
            + dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
              * dotG (act p q
                  (Sl (ground.getAt (⟨[], []⟩ : HVec) grp k))) b))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      ((if mu = b.content then E else BPair.unit)
        + (if mu = a.content
          then D * dotG (act p q (Sl a)) b
          else BPair.unit)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j =>
        ground.famFold BPair.add BPair.unit (fun k =>
          (s * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
            * (dotG (dact p q
                  (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
              * dotG (Sl
                (ground.getAt (⟨[], []⟩ : HVec) grp k)) b))
          (List.range grp.length)
        + ground.famFold BPair.add BPair.unit (fun k =>
          (s * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
            * (dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
              * dotG (act p q (Sl
                  (ground.getAt (⟨[], []⟩ : HVec) grp k))) b))
          (List.range grp.length))
      (List.range grp.length) (fun j _ => ?_)) ?_
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (ground.famFold_congr_all BPair.add BPair.unit _ _
          (fun k => BPair.left_distrib _ _ _)
          (List.range grp.length))) ?_
    exact ground.foldB_add _ _ (List.range grp.length)
  · refine BPair.oneValue_trans
      (ground.foldB_add _ _ (List.range grp.length)) ?_
    refine BPair.add_congr ?_ ?_
    · by_cases hbm : mu = b.content
      · rw [if_pos hbm]
        exact hE hbm
      · rw [if_neg hbm]
        refine block_null grp.length _ (fun j k _ hk => ?_)
        rw [show dotG (Sl
              (ground.getAt (⟨[], []⟩ : HVec) grp k)) b
            = BPair.unit from by
          show (if (Sl
                (ground.getAt (⟨[], []⟩ : HVec) grp k)).content
              = b.content then _ else BPair.unit) = BPair.unit
          rw [if_neg (show ¬ ((Sl
              (ground.getAt (⟨[], []⟩ : HVec) grp k)).content
                = b.content) from fun he => hbm
            ((hcont _ (ground.mem_getAt _ grp k hk)).symm.trans
              ((hslot _ (ground.mem_getAt _ grp k hk)).symm.trans
                he)))]]
        exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.mul_unit _))
          (BPair.mul_unit _)
    · by_cases ham : mu = a.content
      · rw [if_pos ham, ← hsd]
        exact block_twoF grp mu hcont s a (hag ham)
          (fun w => dotG (act p q (Sl w)) b)
      · rw [if_neg ham]
        refine block_null grp.length _ (fun j k hj _ => ?_)
        rw [show dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
            = BPair.unit from by
          show (if (ground.getAt (⟨[], []⟩ : HVec) grp j).content
              = a.content then _ else BPair.unit) = BPair.unit
          rw [if_neg (fun he => ham
            ((hcont _ (ground.mem_getAt _ grp j hj)).symm.trans
              he))]]
        exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.unit_mul _))
          (BPair.mul_unit _)

/-- The block at one content reads the determinant-scaled crossed
pairings: the moved member's own at the further member's content
and the moved further member's at the member's, every other
content's block at the sum's unit. -/
private theorem group_read (grp : List HVec) (mu : List Nat)
    (hcont : ∀ w ∈ grp, w.content = mu) (s D : BPair)
    (hsd : s * elim.detL (elim.gramM (grp.map HVec.coords)) = D)
    (p q : Nat) (a b : HVec)
    (hbg : mu = b.content → b ∈ grp)
    (hag : mu = a.content → a ∈ grp) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (dotG (dact p q
                (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
              * dotG (ground.getAt (⟨[], []⟩ : HVec) grp k) b
            + dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
              * dotG (act p q
                  (ground.getAt (⟨[], []⟩ : HVec) grp k)) b))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      ((if mu = b.content then D * dotG (dact p q b) a
        else BPair.unit)
        + (if mu = a.content then D * dotG (act p q a) b
          else BPair.unit)) :=
  group_readF (fun w => w) grp mu hcont (fun _ _ => rfl) s D
    (D * dotG (dact p q b) a) hsd p q a b hag
    (fun hbm => by
      rw [← hsd]
      exact block_one grp mu hcont s p q a b (hbg hbm))

/-- The coevaluation's datum at one content, the block's own
double index. -/
private def coevBody (Y : List HVec) (mu : List Nat) :
    List (BPair × HVec × HVec) :=
  (List.range (Y.filter (fun w => w.content == mu)).length).flatMap
    (fun j =>
      (List.range (Y.filter (fun w => w.content == mu)).length).map
        (fun k =>
          ((coScale Y mu) * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM
                ((Y.filter (fun w => w.content == mu)).map
                  HVec.coords)) k) j,
            ground.getAt (⟨[], []⟩ : HVec)
              (Y.filter (fun w => w.content == mu)) j,
            ground.getAt (⟨[], []⟩ : HVec)
              (Y.filter (fun w => w.content == mu)) k)))

private theorem coevData_flat (Y : List HVec) :
    coevData Y
      = (ground.dedupL (Y.map HVec.content)).flatMap
        (coevBody Y) := rfl

/-- The moved form read at a letter pair: the dual action at the
first slot with the action at the second, the Leibniz image's
fold against a member pair. -/
def movedAt (P : List (BPair × HVec × HVec)) (p q : Nat)
    (a b : HVec) : BPair :=
  elim.dotP (P.map (fun t => t.1))
    (P.map (fun t =>
      dotG (dact p q t.2.1) a * dotG t.2.2 b
        + dotG t.2.1 a * dotG (act p q t.2.2) b))

/-- The family's value at a member and a stated output content:
the first slots' pairings weighted into the second slots'
combination — the equivariant map's read at a grid family, the
output content the complementary grid's own datum
(`lem:dualread`(i)'s `x ↦ Σᵢ ⟨fᵢ,x⟩ wᵢ`). -/
def pairVal (P : List (BPair × HVec × HVec)) (x : HVec)
    (oc : List Nat) : HVec :=
  let Q := P.filter (fun t => t.2.1.content == x.content)
  ⟨oc,
    elim.combo (places.monomialsAt oc).length
      (Q.map (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
      (Q.map (fun t => t.2.2.coords))⟩

/-- The family's map at an argument: the second slots' combination
at the weighted pairings of the first slots against the argument —
`lem:dualread`(i)'s `x ↦ Σ_i ⟨f_i, x⟩ w_i` at the argument's own
content, `pairVal`'s instance there. -/
def mapAt (P : List (BPair × HVec × HVec)) (x : HVec) : HVec :=
  pairVal P x x.content

/-- The equivariant map's invariant: the coevaluation's second
slot at the map's value — `lem:dualread`(i)'s
`Σ_{j,k} A_{jk} y_j ⊗ φ(y_k)`. -/
def mapInv (T : List Nat → elim.Mat) (Y : List HVec) :
    List (BPair × HVec × HVec) :=
  (coevData Y).map (fun t =>
    (t.1, t.2.1, ⟨t.2.2.content,
      elim.matVec (T t.2.2.content) t.2.2.coords⟩))

/-- The moved form's fold at a stated family, the definition's own
reading. -/
private theorem movedAt_fold (P : List (BPair × HVec × HVec))
    (p q : Nat) (a b : HVec) :
    movedAt P p q a b
      = elim.dotP (P.map (fun t => t.1))
        (P.map (fun t =>
          dotG (dact p q t.2.1) a * dotG t.2.2 b
            + dotG t.2.1 a * dotG (act p q t.2.2) b)) := rfl

/-- The coevaluation is equivariant to the unit: a letter pair's
Leibniz image paired against a member pair collects at the
adjugate identity to the determinant against one crossed pairing
per summand, the transpose identity with the fold's exchange
joining the two at partners, so the moved coevaluation pairs every
member pair at the sum's unit — `lem:dualread`(i)'s coevaluation
sentence. -/
theorem coev_equiv (Y : List HVec) (p q : Nat) (a b : HVec)
    (hpb : p < b.content.length) (hqb : q < b.content.length)
    (hpq : ¬ p = q) (hsa : sized a) (hsb : sized b)
    (ha : a ∈ Y) (hb : b ∈ Y) :
    (movedAt (coevData Y) p q a b).oneValue BPair.unit := by
  rw [movedAt_fold (coevData Y) p q a b, elim.dotP_map_pair,
    coevData_flat Y]
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws
      _ (coevBody Y) (ground.dedupL (Y.map HVec.content))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun mu =>
        (if mu = b.content
          then detAll Y * dotG (dact p q b) a else BPair.unit)
        + (if mu = a.content
          then detAll Y * dotG (act p q a) b else BPair.unit))
      (ground.dedupL (Y.map HVec.content)) (fun mu hmu => ?_)) ?_
  · have h1 : ground.countOf mu
        (ground.dedupL (Y.map HVec.content)) = 1 :=
      Nat.le_antisymm
        (ground.countOf_dedupL_le mu (Y.map HVec.content)) hmu
    refine BPair.oneValue_trans
      (ground.famFold_flatMap_ov ground.bpairFoldLaws
        _ _ (List.range
          (Y.filter (fun w => w.content == mu)).length)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _ _
        (List.range (Y.filter (fun w => w.content == mu)).length)
        (fun j _ => BPair.oneValue_of_eq
          (ground.famFold_map BPair.add BPair.unit _ _
            (List.range
              (Y.filter (fun w => w.content == mu)).length)))) ?_
    exact group_read (Y.filter (fun w => w.content == mu)) mu
      (fun w hw => ground.listBeqEq
        ((ground.mem_filter_of _ Y w hw).2))
      (coScale Y mu) (detAll Y) (scale_detAll Y mu h1) p q a b
      (fun he => ground.mem_filter_to _ hb
        (by rw [he]; exact ground.listEqBeq b.content))
      (fun he => ground.mem_filter_to _ ha
        (by rw [he]; exact ground.listEqBeq a.content))
  · have hbD : ground.countOf b.content
        (ground.dedupL (Y.map HVec.content)) = 1 :=
      ground.countOf_dedupL_one (ground.mem_map_to HVec.content hb)
    have haD : ground.countOf a.content
        (ground.dedupL (Y.map HVec.content)) = 1 :=
      ground.countOf_dedupL_one (ground.mem_map_to HVec.content ha)
    refine BPair.oneValue_trans
      (ground.foldB_add _ _ (ground.dedupL (Y.map HVec.content)))
      ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (ground.foldB_indicator b.content
            (detAll Y * dotG (dact p q b) a)
            (ground.dedupL (Y.map HVec.content)))
          (by rw [hbD]; exact BPair.ofNat_one_mul _))
        (BPair.oneValue_trans
          (ground.foldB_indicator a.content
            (detAll Y * dotG (act p q a) b)
            (ground.dedupL (Y.map HVec.content)))
          (by rw [haD]; exact BPair.ofNat_one_mul _))) ?_
    rw [← BPair.left_distrib]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) ?_)
      (BPair.mul_unit _)
    exact ev_equivG p q a b hpb hqb hpq hsa hsb

/-! `lem:dualread`(iii)'s at-join arm, clause 11: the coevaluation
at the two collected word families.  Per occupied content of the
partner family the group's Gram carries its own adjugate entries
against the further groups' determinants, and each dual word is
weighted against its partner word; the weighted tensors' combination
at the full columns is the coevaluation's member of the fused
carrier.  Its coordinates sit in the stated pair list's span — every
dual word settles in the first block's span (the dual action's
closure walked along the word) and every partner word is a member of
the second block's, the two contents complementary at the join
(`dualLive`) — and the coevaluation sits off the unit family at the
determinant's diagonal: pairing it against one group's own tensor
collapses at the adjugate identity to that group's determinant
against the further groups' at the member's self-pairing, every
factor off the unit at the collected families' independence
(`lem:lowerspan`). -/

/-- The coevaluation's data at the two collected word families:
per occupied content of the partner family the group's adjugate
entries at the further groups' determinants, each dual word
weighted against its partner word. -/
def coevW (b : Shape) (g : HVec) (W : List (List Nat)) :
    List (BPair × HVec × HVec) :=
  let Y := W.map (fun ws => wact ws (exhibit b))
  (ground.dedupL (Y.map HVec.content)).flatMap (fun mu =>
    let idxs := W.filter
      (fun ws => (wact ws (exhibit b)).content == mu)
    let G := elim.gramM
      ((idxs.map (fun ws => wact ws (exhibit b))).map HVec.coords)
    let s := coScale Y mu
    (List.range idxs.length).flatMap (fun j =>
      (List.range idxs.length).map (fun k =>
        (s * ground.getAt BPair.unit (elim.cofVec G k) j,
          wactT dualTable
            (ground.getAt ([] : List Nat) idxs j) g,
          wact (ground.getAt ([] : List Nat) idxs k)
            (exhibit b)))))

/-- The coevaluation's member of the fused carrier at the full
columns: the weighted tensors' combination at the stated
content. -/
def coevVec (cc : List Nat) (b : Shape) (g : HVec)
    (W : List (List Nat)) : HVec :=
  ⟨cc, elim.combo (places.monomialsAt cc).length
    ((coevW b g W).map (fun t => t.1))
    ((coevW b g W).map (fun t => (tensorH t.2.1 t.2.2).coords))⟩

/-- A span member sits off the unit tail: its coordinate row is a
listed row of its own content group, independent there
(`lem:lowerspan`'s independence clause). -/
private theorem span_mem_off (s : Shape) (v : HVec)
    (hv : v ∈ blockSpan s) : ¬ poly.unitTail v.coords := by
  have hmem : v.coords ∈ groupAt (blockSpan s) v.content :=
    ground.mem_map_to HVec.coords
      (ground.mem_filter_to (fun w => w.content == v.content) hv
        (ground.listEqBeq v.content))
  match ground.getAt_of_mem ([] : List BPair) hmem with
  | ⟨k, hk, he⟩ =>
    rw [← he]
    exact elim.indep_row_off
      (blockcount.indepAll_all (lowerspan.spanReads s).2.1 v.content)
      k hk

/-- Every dual word image of a span member settles in the block's
span: the seed is the member's own group row and each letter's dual
lowering is the exchanged action's span transport at the balance
partner's scale. -/
private theorem dualWord_span (a : Shape) (g : HVec)
    (hg : g ∈ blockSpan a) :
    ∀ ws : List Nat, (∀ l ∈ ws, l + 1 < a.length) →
      elim.spanRel
        (places.monomialsAt (wactT dualTable ws g).content).length
        (groupAt (blockSpan a) (wactT dualTable ws g).content)
        (wactT dualTable ws g).coords
  | [], _ =>
    blockcount.spanRel_groupAt_mem (blockSpan a) g hg
      (lowerspan.spanReads a).1
  | l :: t, hb => by
    have hl1 : l + 1 < a.length := hb l (List.Mem.head t)
    have hIH := dualWord_span a g hg t
      (fun x hx => hb x (List.Mem.tail l hx))
    have hxs : (wactT dualTable t g).coords.length
        = (places.monomialsAt (wactT dualTable t g).content).length :=
      wactT_sized dualTable t g ((lowerspan.spanReads a).1 g hg)
    have hact := lowerspan.act_span_def a l (l + 1)
      (Nat.lt_of_succ_lt hl1) hl1 (Nat.ne_of_lt (Nat.lt_succ_self l))
      (wactT dualTable t g).content (wactT dualTable t g).coords hxs
      hIH
    have hov : poly.oneValue
        (elim.vecScale (BPair.ofNat 1).swap
          (elim.matVec (units.matUnitAt
            (moveAt l (l + 1) (wactT dualTable t g).content)
            (wactT dualTable t g).content l (l + 1))
            (wactT dualTable t g).coords))
        (poly.neg (elim.matVec (units.matUnitAt
            (moveAt l (l + 1) (wactT dualTable t g).content)
            (wactT dualTable t g).content l (l + 1))
            (wactT dualTable t g).coords)) := by
      rw [elim.vecScale_swap]
      exact poly.swapMap_oneValue (poly.scale_one _)
    show elim.spanRel
      (places.monomialsAt
        (dact (l + 1) l (wactT dualTable t g)).content).length
      (groupAt (blockSpan a)
        (dact (l + 1) l (wactT dualTable t g)).content)
      (dact (l + 1) l (wactT dualTable t g)).coords
    show elim.spanRel
      (places.monomialsAt
        (moveAt l (l + 1) (wactT dualTable t g).content)).length
      (groupAt (blockSpan a)
        (moveAt l (l + 1) (wactT dualTable t g).content))
      (poly.neg (elim.matVec (units.matUnitAt
        (moveAt l (l + 1) (wactT dualTable t g).content)
        (wactT dualTable t g).content l (l + 1))
        (wactT dualTable t g).coords))
    exact elim.spanRel_congr _ _ _ _ hov
      (elim.spanRel_scale _ _ _ (BPair.ofNat 1).swap hact.1 hact.2.1
        hact)
      ((poly.length_neg _).trans hact.2.1)

/-- A live dual word image keeps the member's degree: every letter's
dual lowering moves the content at an occupied source, and a vacant
one sends the image to the unit family outright. -/
private theorem dualWord_deg (a : Shape) (g : HVec)
    (hg : g ∈ blockSpan a) :
    ∀ ws : List Nat, (∀ l ∈ ws, l + 1 < a.length) →
      ¬ poly.unitTail (wactT dualTable ws g).coords →
      ground.sumNat (wactT dualTable ws g).content
        = ground.sumNat g.content
  | [], _, _ => rfl
  | l :: t, hb, hlive => by
    have hl1 : l + 1 < a.length := hb l (List.Mem.head t)
    have hlt : ¬ poly.unitTail (wactT dualTable t g).coords :=
      fun hu => hlive
        (dualTable.step_unitTail l (wactT dualTable t g) hu)
    have hocc : 0 < ground.getAt 0
        (wactT dualTable t g).content (l + 1) := by
      match Nat.eq_zero_or_pos (ground.getAt 0
          (wactT dualTable t g).content (l + 1)) with
      | .inr hp => exact hp
      | .inl hz =>
        exact absurd
          (dualTable.step_vac l (wactT dualTable t g) hz) hlive
    have hlen : l < (wactT dualTable t g).content.length := by
      rw [widthG a g hg t]
      exact Nat.lt_of_succ_lt hl1
    show ground.sumNat
      (moveAt l (l + 1) (wactT dualTable t g).content)
      = ground.sumNat g.content
    rw [blockcount.sumNat_moveAt l (l + 1)
      (wactT dualTable t g).content hlen hocc]
    exact dualWord_deg a g hg t
      (fun x hx => hb x (List.Mem.tail l hx)) hlt

/-- The dual word image at a live partner word is live and the two
contents join to the full columns: the Gram's two sides read one
value at the two tops' self-pairings, both off the unit tail at the
collected families' independence, so the dual image pairs itself off
the unit and the complement invariant closes at the join. -/
private theorem coevLive (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (ws : List Nat) (hws : ∀ l ∈ ws, l + 1 < a.length)
    (hmem : wact ws (exhibit b) ∈ blockSpan b) :
    ¬ poly.unitTail (wactT dualTable ws g).coords
      ∧ List.zipWith (fun u w => u + w)
        (wact ws (exhibit b)).content
        (wactT dualTable ws g).content
        = List.replicate a.length m := by
  have hYoff : ¬ poly.unitTail (wact ws (exhibit b)).coords :=
    span_mem_off b _ hmem
  have hP : ¬ (elim.dotP g.coords g.coords).oneValue BPair.unit :=
    fun h => span_mem_off a g hg (elim.dotP_self_null _ h)
  have hE : ¬ (elim.dotP (exhibit b).coords
      (exhibit b).coords).oneValue BPair.unit :=
    fun h => blockcount.exhibit_off_unit b (elim.dotP_self_null _ h)
  have hYY : ¬ (dotG (wact ws (exhibit b))
      (wact ws (exhibit b))).oneValue BPair.unit := by
    intro h
    refine hYoff (elim.dotP_self_null _ ?_)
    have h' : (if (wact ws (exhibit b)).content
          = (wact ws (exhibit b)).content
        then elim.dotP (wact ws (exhibit b)).coords
          (wact ws (exhibit b)).coords
        else BPair.unit).oneValue BPair.unit := h
    rw [if_pos (rfl : (wact ws (exhibit b)).content
      = (wact ws (exhibit b)).content)] at h'
    exact h'
  have hLHS : ¬ (dotG (wact ws (exhibit b)) (wact ws (exhibit b))
      * elim.dotP g.coords g.coords).oneValue BPair.unit := fun h =>
    hP (ground.mul_cancel_unit hYY h)
  have hRHS : ¬ (dotG (wactT dualTable ws g) (wactT dualTable ws g)
      * elim.dotP (exhibit b).coords
        (exhibit b).coords).oneValue BPair.unit := fun h =>
    hLHS (BPair.oneValue_trans
      (dualGram a b m hba hjoin g hg hgc ws ws hws hws) h)
  have hXX : ¬ (dotG (wactT dualTable ws g)
      (wactT dualTable ws g)).oneValue BPair.unit := fun h =>
    hRHS (elim.oneValue_unit_mul h)
  have hXoff : ¬ poly.unitTail (wactT dualTable ws g).coords := by
    intro hu
    refine hXX ?_
    show (if (wactT dualTable ws g).content
        = (wactT dualTable ws g).content
      then elim.dotP (wactT dualTable ws g).coords
        (wactT dualTable ws g).coords
      else BPair.unit).oneValue BPair.unit
    rw [if_pos (rfl : (wactT dualTable ws g).content
      = (wactT dualTable ws g).content)]
    exact elim.dotP_null_tail_right _ _ hu
  exact ⟨hXoff, dualLive a b m hba hjoin g hg hgc ws hws hYoff hXoff⟩

/-- The coevaluation's datum at one content, the group's own double
index over the words carrying that content. -/
private def coevWBody (b : Shape) (g : HVec) (W : List (List Nat))
    (mu : List Nat) : List (BPair × HVec × HVec) :=
  (List.range (W.filter
      (fun ws => (wact ws (exhibit b)).content == mu)).length).flatMap
    (fun j =>
      (List.range (W.filter
        (fun ws => (wact ws (exhibit b)).content == mu)).length).map
        (fun k =>
          (coScale (W.map (fun ws => wact ws (exhibit b))) mu
            * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM
                (((W.filter
                    (fun ws => (wact ws (exhibit b)).content == mu)).map
                  (fun ws => wact ws (exhibit b))).map HVec.coords)) k)
              j,
            wactT dualTable (ground.getAt ([] : List Nat)
              (W.filter
                (fun ws => (wact ws (exhibit b)).content == mu)) j) g,
            wact (ground.getAt ([] : List Nat)
              (W.filter
                (fun ws => (wact ws (exhibit b)).content == mu)) k)
              (exhibit b))))

private theorem coevW_flat (b : Shape) (g : HVec)
    (W : List (List Nat)) :
    coevW b g W
      = (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
          HVec.content)).flatMap (coevWBody b g W) := rfl

/-- The datum's entry slots at one content: the first slot is a
listed word's dual image at the reversal member and the second a
listed word's partner image at the target's top, both words carrying
that content. -/
private theorem coevWBody_slots (b : Shape) (g : HVec)
    (W : List (List Nat)) (mu : List Nat) (t : BPair × HVec × HVec)
    (ht : t ∈ coevWBody b g W mu) :
    ∃ wj, wj ∈ W.filter (fun z => (wact z (exhibit b)).content == mu)
      ∧ ∃ wk, wk ∈ W.filter (fun z => (wact z (exhibit b)).content == mu)
        ∧ t.2.1 = wactT dualTable wj g
        ∧ t.2.2 = wact wk (exhibit b) := by
  match ground.mem_flatMap_of _ _ t ht with
  | ⟨j, hj, htj⟩ =>
    match ground.mem_map_of _ _ t htj with
    | ⟨k, hk, hkt⟩ =>
      refine ⟨_, ground.mem_getAt ([] : List Nat) _ j
          (ground.ltOfMemRange hj),
        _, ground.mem_getAt ([] : List Nat) _ k
          (ground.ltOfMemRange hk), ?_, ?_⟩
      · rw [← hkt]
      · rw [← hkt]

/-- The coevaluation's entry slots: the first slot is a listed
word's dual image at the reversal member and the second that word's
partner image at the target's top, the two words carrying one
content. -/
private theorem coevW_slots (b : Shape) (g : HVec)
    (W : List (List Nat)) (t : BPair × HVec × HVec)
    (ht : t ∈ coevW b g W) :
    ∃ wj, wj ∈ W ∧ ∃ wk, wk ∈ W
      ∧ (wact wj (exhibit b)).content = (wact wk (exhibit b)).content
      ∧ t.2.1 = wactT dualTable wj g
      ∧ t.2.2 = wact wk (exhibit b) := by
  rw [coevW_flat b g W] at ht
  match ground.mem_flatMap_of _ _ t ht with
  | ⟨mu, _, htm⟩ =>
    match coevWBody_slots b g W mu t htm with
    | ⟨wj, hj, wk, hk, h1, h2⟩ =>
      have hjf := ground.mem_filter_of
        (fun z => (wact z (exhibit b)).content == mu) W wj hj
      have hkf := ground.mem_filter_of
        (fun z => (wact z (exhibit b)).content == mu) W wk hk
      exact ⟨wj, hjf.1, wk, hkf.1,
        by rw [ground.listBeqEq hjf.2, ground.listBeqEq hkf.2],
        h1, h2⟩

/-- Every weighted tensor of the coevaluation sits in the stated
pair list's span: the dual word settles in the first block's span
(`dualWord_span`) and the partner word is a member of the second
block's, the two contents complementary at the join (`coevLive`),
so the collecting read (`blockcount.tensor_span`) carries the tensor
into the fused pool's group at the full columns — the pair list's
own coordinate family (`blockcount.groupAt_fused`). -/
private theorem coevW_row (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (t : BPair × HVec × HVec) (ht : t ∈ coevW b g W) :
    elim.spanRel
      (places.monomialsAt (List.replicate a.length m)).length
      ((pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).map HVec.coords)
      (tensorH t.2.1 t.2.2).coords := by
  match coevW_slots b g W t ht with
  | ⟨wj, hwj, wk, hwk, hcjk, hs1, hs2⟩ =>
    have hwsj : ∀ l ∈ wj, l + 1 < a.length := fun l hl => by
      rw [← hba]
      exact hWb wj hwj l hl
    have hmemj : wact wj (exhibit b) ∈ blockSpan b := by
      rw [hW]
      exact ground.mem_map_to (fun ws => wact ws (exhibit b)) hwj
    have hmemk : wact wk (exhibit b) ∈ blockSpan b := by
      rw [hW]
      exact ground.mem_map_to (fun ws => wact ws (exhibit b)) hwk
    have hlive := coevLive a b m hba hjoin g hg hgc wj hwsj hmemj
    have hnu : (wactT dualTable wj g).content.length = a.length :=
      widthG a g hg wj
    have hnw : (wact wk (exhibit b)).content.length = a.length := by
      rw [blockcount.blockSpan_width b _ hmemk]
      exact hba
    have hjk : List.zipWith (fun p q => p + q)
        (wactT dualTable wj g).content
        (wact wk (exhibit b)).content
        = List.replicate a.length m := by
      rw [← hcjk, ground.zipWith_add_comm
        (wactT dualTable wj g).content (wact wj (exhibit b)).content]
      exact hlive.2
    have hspan := blockcount.tensor_span (blockSpan a) (blockSpan b)
      a.length (lowerspan.spanReads a).1 (lowerspan.spanReads b).1
      (blockcount.blockSpan_width a)
      (fun w hw => (blockcount.blockSpan_width b w hw).trans hba)
      (wactT dualTable wj g).content (wact wk (exhibit b)).content
      hnu hnw (wactT dualTable wj g).coords
      (wact wk (exhibit b)).coords (dualWord_span a g hg wj hwsj)
      (blockcount.spanRel_groupAt_mem (blockSpan b) _ hmemk
        (lowerspan.spanReads b).1)
    rw [hjk, groupAt_fused (blockSpan a) (blockSpan b)
      (List.replicate a.length m)] at hspan
    rw [hs1, hs2]
    exact hspan

/-- The coevaluation's coordinates sit in the span of the stated
pair list's rows: each weighted tensor is a member of that span
(`coevW_row`) and the span keeps the weighted combination
(`elim.spanRel_combo`). -/
theorem coevVec_span (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length) :
    elim.spanRel
      (places.monomialsAt (List.replicate a.length m)).length
      ((pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).map HVec.coords)
      (coevVec (List.replicate a.length m) b g W).coords := by
  have hrow := coevW_row a b m hba hjoin g hg hgc W hW hWb
  refine elim.spanRel_combo
    (places.monomialsAt (List.replicate a.length m)).length
    ((pairsAt (blockSpan a) (blockSpan b)
      (List.replicate a.length m)).map HVec.coords)
    (by
      rw [← groupAt_fused (blockSpan a) (blockSpan b)
        (List.replicate a.length m)]
      exact blockcount.rowsLen_groupAt (List.replicate a.length m)
        (fusedAt (blockSpan a) (blockSpan b))
        (blockcount.fusedAt_sized (blockSpan a) (blockSpan b)))
    ((coevW b g W).map (fun t => (tensorH t.2.1 t.2.2).coords))
    ((coevW b g W).map (fun t => t.1))
    (elim.rowsLen_map _ _ (coevW b g W)
      (fun t htm => (hrow t htm).2.1)) ?_
  intro k hk
  rw [ground.length_map] at hk
  rw [ground.getAt_map
    ((BPair.unit, (⟨[], []⟩ : HVec), (⟨[], []⟩ : HVec)))
    ([] : List BPair) (fun t => (tensorH t.2.1 t.2.2).coords)
    (coevW b g W) k hk]
  exact hrow _ (ground.mem_getAt _ (coevW b g W) k hk)

/-- The skipping product's accumulator stays off the sum's unit
where every further group's determinant does. -/
private theorem coScale_go (Y : List HVec) (mu : List Nat) :
    ∀ (l : List (List Nat)) (acc : BPair),
      ¬ acc.oneValue BPair.unit →
      (∀ nu, ¬ (blockDet Y nu).oneValue BPair.unit) →
      ¬ (l.foldl (fun acc nu =>
            if nu = mu then acc else acc * blockDet Y nu) acc).oneValue
        BPair.unit
  | [], _, hacc, _ => hacc
  | nu :: t, acc, hacc, hall => by
    refine coScale_go Y mu t _ ?_ hall
    show ¬ (if nu = mu then acc else acc * blockDet Y nu).oneValue
      BPair.unit
    by_cases he : nu = mu
    · rw [if_pos he]
      exact hacc
    · rw [if_neg he]
      intro hcon
      exact hall nu (ground.mul_cancel_unit hacc hcon)

/-- The further groups' determinants sit off the sum's unit where
every group's does, the natural one's seed off it. -/
private theorem coScale_off (Y : List HVec) (mu : List Nat)
    (hall : ∀ nu, ¬ (blockDet Y nu).oneValue BPair.unit) :
    ¬ (coScale Y mu).oneValue BPair.unit :=
  coScale_go Y mu (ground.dedupL (Y.map HVec.content))
    (BPair.ofNat 1) (by decide +kernel) hall

/-- An independent carrier's every group determinant sits off the
sum's unit. -/
private theorem blockDet_off (s : Shape) (nu : List Nat) :
    ¬ (blockDet (blockSpan s) nu).oneValue BPair.unit :=
  (blockcount.indepAll_all (lowerspan.spanReads s).2.1 nu).2

/-- The collected word family's group at a content is the carrier's
own: the filter reads the words' images. -/
private theorem coevGrp_group (b : Shape) (W : List (List Nat))
    (mu : List Nat) :
    ((W.filter (fun ws => (wact ws (exhibit b)).content == mu)).map
        (fun ws => wact ws (exhibit b))).map HVec.coords
      = groupAt (W.map (fun ws => wact ws (exhibit b))) mu := by
  show _ = (((W.map (fun ws => wact ws (exhibit b))).filter
    (fun w => w.content == mu)).map HVec.coords)
  rw [ground.filter_map (fun ws => wact ws (exhibit b))
    (fun w => w.content == mu) W]

/-- A listed word carrying one content: its partner image is a
member of the second block at that content, its dual image is sized,
keeps the first block's letter width and the reversal member's
degree, and the two contents join to the full columns in either
order. -/
private theorem coevSlot (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu : List Nat) (ws : List Nat)
    (hws : ws ∈ W.filter (fun z => (wact z (exhibit b)).content == mu)) :
    (wact ws (exhibit b)).content = mu
      ∧ wact ws (exhibit b) ∈ blockSpan b
      ∧ sized (wactT dualTable ws g)
      ∧ (wactT dualTable ws g).content.length = a.length
      ∧ ground.sumNat (wactT dualTable ws g).content
        = ground.sumNat g.content
      ∧ List.zipWith (fun u w => u + w) mu
          (wactT dualTable ws g).content = List.replicate a.length m
      ∧ List.zipWith (fun u w => u + w)
          (wactT dualTable ws g).content mu = List.replicate a.length m
      ∧ mu.length = a.length := by
  have hf := ground.mem_filter_of
    (fun z => (wact z (exhibit b)).content == mu) W ws hws
  have hmu : (wact ws (exhibit b)).content = mu :=
    ground.listBeqEq hf.2
  have hmem : wact ws (exhibit b) ∈ blockSpan b := by
    rw [hW]
    exact ground.mem_map_to (fun z => wact z (exhibit b)) hf.1
  have hwsa : ∀ l ∈ ws, l + 1 < a.length := fun l hl => by
    rw [← hba]
    exact hWb ws hf.1 l hl
  have hlive := coevLive a b m hba hjoin g hg hgc ws hwsa hmem
  have hmul : mu.length = a.length := by
    rw [← hmu, blockcount.blockSpan_width b _ hmem]
    exact hba
  have h6 : List.zipWith (fun u w => u + w) mu
      (wactT dualTable ws g).content = List.replicate a.length m := by
    rw [← hmu]
    exact hlive.2
  exact ⟨hmu, hmem,
    wactT_sized dualTable ws g ((lowerspan.spanReads a).1 g hg),
    widthG a g hg ws, dualWord_deg a g hg ws hwsa hlive.1, h6,
    (ground.zipWith_add_comm (wactT dualTable ws g).content mu).trans h6,
    hmul⟩


/-- The coevaluation's pairing against a stated vector at a scale is
the entries' own scaled fold: the combination's pairing is the
weights against the rows' pairings (`elim.dotP_combo`) and the scale
passes through the fold. -/
private theorem coevPair_fold (b : Shape) (g : HVec)
    (W : List (List Nat)) (cc : List Nat) (z : HVec) (E : BPair)
    (hK : elim.rowsLen (places.monomialsAt cc).length
      ((coevW b g W).map (fun t => (tensorH t.2.1 t.2.2).coords))) :
    (elim.dotP (coevVec cc b g W).coords z.coords * E).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun t => (t.1 * elim.dotP z.coords
            (tensorH t.2.1 t.2.2).coords) * E)
        (coevW b g W)) := by
  have hcombo := elim.dotP_combo ((coevW b g W).map (fun t => t.1))
    ((coevW b g W).map (fun t => (tensorH t.2.1 t.2.2).coords))
    z.coords (places.monomialsAt cc).length hK
  rw [ground.map_map (fun t => (tensorH t.2.1 t.2.2).coords)
      (fun row => elim.dotP z.coords row) (coevW b g W),
    elim.dotP_map_pair (fun t => t.1)
      (fun t => elim.dotP z.coords (tensorH t.2.1 t.2.2).coords)
      (coevW b g W)] at hcombo
  rw [elim.dotP_comm (coevVec cc b g W).coords z.coords]
  refine BPair.oneValue_trans
    (BPair.mul_congr hcombo (BPair.oneValue_refl E)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_comm _ E)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_mul_left E _ (coevW b g W))) ?_
  exact ground.foldB_congr_members _ _ (coevW b g W)
    (fun t _ => BPair.oneValue_of_eq (BPair.mul_comm _ _))

/-- A further group's block reads the sum's unit: the two tensors sit
at one fused content with distinct first factors at one degree, so
every entry's pairing splits at the unit
(`blockcount.dotP_tensorH_off`). -/
private theorem coevBody_off (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu0 nu : List Nat) (hne : ¬ nu = mu0) (ws0 : List Nat)
    (hws0 : ws0 ∈ W.filter
      (fun z => (wact z (exhibit b)).content == mu0))
    (E : BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun t => (t.1 * elim.dotP
          (tensorH (wactT dualTable ws0 g)
            (wact ws0 (exhibit b))).coords
          (tensorH t.2.1 t.2.2).coords) * E)
      (coevWBody b g W nu)).oneValue BPair.unit := by
  have hs0 := coevSlot a b m hba hjoin g hg hgc W hW hWb mu0 ws0 hws0
  refine ground.foldB_null _ (coevWBody b g W nu) (fun t htc => ?_)
  match coevWBody_slots b g W nu t
      (ground.mem_of_countOf_pos _ _ htc) with
  | ⟨wj, hj, wk, hk, h1, h2⟩ =>
    have hsj := coevSlot a b m hba hjoin g hg hgc W hW hWb nu wj hj
    have hsk := coevSlot a b m hba hjoin g hg hgc W hW hWb nu wk hk
    have hne' : ¬ (wactT dualTable ws0 g).content
        = (wactT dualTable wj g).content := by
      intro he
      have hA : List.zipWith (fun u w => u + w)
          (wactT dualTable ws0 g).content nu
          = List.replicate a.length m := by
        rw [he]
        exact hsj.2.2.2.2.2.2.1
      exact hne (blockcount.zipWith_add_cancelL
        (wactT dualTable ws0 g).content nu mu0 a.length
        hs0.2.2.2.1 hsj.2.2.2.2.2.2.2 hs0.2.2.2.2.2.2.2
        (hA.trans hs0.2.2.2.2.2.2.1.symm))
    have hoff := blockcount.dotP_tensorH_off (wactT dualTable ws0 g)
      (wact ws0 (exhibit b)) (wactT dualTable wj g)
      (wact wk (exhibit b))
      (by rw [hs0.2.2.2.1, hs0.1, hs0.2.2.2.2.2.2.2])
      (by rw [hsj.2.2.2.1, hsk.1, hsj.2.2.2.2.2.2.2])
      (hs0.2.2.2.2.1.trans hsj.2.2.2.2.1.symm)
      (by
        show List.zipWith (fun x y => x + y)
            (wactT dualTable ws0 g).content
            (wact ws0 (exhibit b)).content
          = List.zipWith (fun x y => x + y)
            (wactT dualTable wj g).content
            (wact wk (exhibit b)).content
        rw [hs0.1, hsk.1, hs0.2.2.2.2.2.2.1, hsj.2.2.2.2.2.2.1])
      hne'
    rw [h1, h2]
    refine elim.oneValue_unit_mul ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm t.1 _)) ?_
    exact elim.oneValue_unit_mul hoff


/-- The named group's block collapses at the adjugate identity: the
two tensors' pairing factorizes at the shared contents
(`blockcount.dotP_tensorH`), the dual words' pairing walks onto the
partner words' Gram at the two tops' self-pairings (`dualGram`), and
the double fold reads the group's determinant against the further
groups' at the member's own self-pairing (`block_twoF`). -/
private theorem coevBody_on (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu0 : List Nat) (ws0 : List Nat)
    (hws0 : ws0 ∈ W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) :
    (ground.famFold BPair.add BPair.unit
      (fun t => (t.1 * elim.dotP
          (tensorH (wactT dualTable ws0 g)
            (wact ws0 (exhibit b))).coords
          (tensorH t.2.1 t.2.2).coords)
        * elim.dotP (exhibit b).coords (exhibit b).coords)
      (coevWBody b g W mu0)).oneValue
      (coScale (W.map (fun ws => wact ws (exhibit b))) mu0
          * elim.detL (elim.gramM
            (((W.filter
              (fun z => (wact z (exhibit b)).content == mu0)).map
                (fun ws => wact ws (exhibit b))).map HVec.coords))
        * (elim.dotP g.coords g.coords
          * dotG (wact ws0 (exhibit b)) (wact ws0 (exhibit b)))) := by
  have hs0 := coevSlot a b m hba hjoin g hg hgc W hW hWb mu0 ws0 hws0
  have hszb := (lowerspan.spanReads b).1
  have hgl : ((W.filter
        (fun z => (wact z (exhibit b)).content == mu0)).map
        (fun ws => wact ws (exhibit b))).length
      = (W.filter
        (fun z => (wact z (exhibit b)).content == mu0)).length :=
    ground.length_map _ _
  have hb2 := block_twoF
    ((W.filter (fun z => (wact z (exhibit b)).content == mu0)).map
      (fun ws => wact ws (exhibit b))) mu0
    (fun w hw => by
      match ground.mem_map_of _ _ w hw with
      | ⟨z, hz, hzw⟩ =>
        rw [← hzw]
        exact (coevSlot a b m hba hjoin g hg hgc W hW hWb mu0 z hz).1)
    (coScale (W.map (fun ws => wact ws (exhibit b))) mu0)
    (wact ws0 (exhibit b))
    (ground.mem_map_to (fun z => wact z (exhibit b)) hws0)
    (fun w => elim.dotP g.coords g.coords
      * dotG w (wact ws0 (exhibit b)))
  rw [hgl] at hb2
  refine BPair.oneValue_trans ?_ hb2
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws _ _
      (List.range (W.filter
        (fun z => (wact z (exhibit b)).content == mu0)).length)) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ _
      (List.range (W.filter
        (fun z => (wact z (exhibit b)).content == mu0)).length)
      (fun j _ => BPair.oneValue_of_eq
        (ground.famFold_map BPair.add BPair.unit _ _
          (List.range (W.filter
            (fun z => (wact z (exhibit b)).content == mu0)).length))))
    ?_
  refine ground.foldB_congr_members _ _
    (List.range (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)).length)
    (fun j hj0 => ?_)
  have hj : j < (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)).length :=
    ground.ltOfMem hj0
  refine ground.foldB_congr_members _ _
    (List.range (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)).length)
    (fun k hk0 => ?_)
  have hk : k < (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)).length :=
    ground.ltOfMem hk0
  have hsj := coevSlot a b m hba hjoin g hg hgc W hW hWb mu0
    (ground.getAt ([] : List Nat) (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) j)
    (ground.mem_getAt ([] : List Nat) _ j hj)
  have hsk := coevSlot a b m hba hjoin g hg hgc W hW hWb mu0
    (ground.getAt ([] : List Nat) (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) k)
    (ground.mem_getAt ([] : List Nat) _ k hk)
  rw [ground.getAt_map ([] : List Nat) (⟨[], []⟩ : HVec)
      (fun ws => wact ws (exhibit b)) _ j hj,
    ground.getAt_map ([] : List Nat) (⟨[], []⟩ : HVec)
      (fun ws => wact ws (exhibit b)) _ k hk]
  have hXj : (wactT dualTable (ground.getAt ([] : List Nat)
      (W.filter (fun z => (wact z (exhibit b)).content == mu0)) j)
      g).content = (wactT dualTable ws0 g).content :=
    blockcount.zipWith_add_cancelL mu0 _ _ a.length
      hs0.2.2.2.2.2.2.2 hsj.2.2.2.1 hs0.2.2.2.1
      (hsj.2.2.2.2.2.1.trans hs0.2.2.2.2.2.1.symm)
  have hT := blockcount.dotP_tensorH (wactT dualTable ws0 g)
    (wact ws0 (exhibit b))
    (wactT dualTable (ground.getAt ([] : List Nat) (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) j) g)
    (wact (ground.getAt ([] : List Nat) (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) k)
      (exhibit b))
    hs0.2.2.1 (hszb _ hs0.2.1) hsj.2.2.1 (hszb _ hsk.2.1)
    (by rw [hs0.2.2.2.1, hs0.1, hs0.2.2.2.2.2.2.2])
    hXj.symm (by rw [hs0.1, hsk.1])
  have hG := dualGram a b m hba hjoin g hg hgc
    (ground.getAt ([] : List Nat) (W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) j) ws0
    (fun l hl => by
      rw [← hba]
      exact hWb _ (ground.mem_filter_of _ W _
        (ground.mem_getAt ([] : List Nat) _ j hj)).1 l hl)
    (fun l hl => by
      rw [← hba]
      exact hWb ws0 (ground.mem_filter_of _ W ws0 hws0).1 l hl)
  rw [dotG_read _ _ (hsj.1.trans hs0.1.symm), dotG_read _ _ hXj] at hG
  rw [dotG_read _ _ (hsj.1.trans hs0.1.symm),
    dotG_read _ _ (hsk.1.trans hs0.1.symm), BPair.mul_assoc]
  refine BPair.mul_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr hT (BPair.oneValue_refl _)) ?_
  rw [elim.dotP_comm (wactT dualTable ws0 g).coords,
    elim.dotP_comm (wact ws0 (exhibit b)).coords,
    ← BPair.mul_assoc (elim.dotP (wact (ground.getAt
      ([] : List Nat) (W.filter
        (fun z => (wact z (exhibit b)).content == mu0)) j)
      (exhibit b)).coords (wact ws0 (exhibit b)).coords)
      (elim.dotP g.coords g.coords)]
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr hG (BPair.oneValue_refl _)) ?_
  rw [BPair.mul_assoc, BPair.mul_comm
      (elim.dotP (exhibit b).coords (exhibit b).coords)
      (elim.dotP (wact (ground.getAt ([] : List Nat) (W.filter
        (fun z => (wact z (exhibit b)).content == mu0)) k)
        (exhibit b)).coords (wact ws0 (exhibit b)).coords),
    ← BPair.mul_assoc]
  exact BPair.oneValue_refl _


/-- The coevaluation pairs one group's own tensor at the
determinant's diagonal: the entries off that group read the sum's
unit and the group's own block collapses at the adjugate identity,
so the pairing at the two tops' self-pairings' scale reads the
group's determinant against the further groups' at the member's own
self-pairing. -/
private theorem coevOff_display (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu0 : List Nat)
    (hmu0 : mu0 ∈ (W.map (fun ws => wact ws (exhibit b))).map
      HVec.content)
    (ws0 : List Nat)
    (hws0 : ws0 ∈ W.filter
      (fun z => (wact z (exhibit b)).content == mu0)) :
    (elim.dotP (coevVec (List.replicate a.length m) b g W).coords
        (tensorH (wactT dualTable ws0 g)
          (wact ws0 (exhibit b))).coords
      * elim.dotP (exhibit b).coords (exhibit b).coords).oneValue
      (coScale (W.map (fun ws => wact ws (exhibit b))) mu0
          * elim.detL (elim.gramM
            (((W.filter
              (fun z => (wact z (exhibit b)).content == mu0)).map
                (fun ws => wact ws (exhibit b))).map HVec.coords))
        * (elim.dotP g.coords g.coords
          * dotG (wact ws0 (exhibit b)) (wact ws0 (exhibit b)))) := by
  refine BPair.oneValue_trans
    (coevPair_fold b g W (List.replicate a.length m)
      (tensorH (wactT dualTable ws0 g) (wact ws0 (exhibit b)))
      (elim.dotP (exhibit b).coords (exhibit b).coords)
      (elim.rowsLen_map _ _ (coevW b g W)
        (fun t htm => (coevW_row a b m hba hjoin g hg hgc W hW hWb t
          htm).2.1))) ?_
  rw [coevW_flat b g W]
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws _ (coevWBody b g W)
      (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
        HVec.content))) ?_
  exact ground.foldB_pick _ mu0 _
    (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
      HVec.content))
    (ground.countOf_dedupL_one hmu0)
    (coevBody_on a b m hba hjoin g hg hgc W hW hWb mu0 ws0 hws0)
    (fun nu _ hne => coevBody_off a b m hba hjoin g hg hgc W hW hWb
      mu0 nu hne ws0 hws0 _)

/-- The coevaluation sits off the unit family: paired against the
target's top's own group tensor it reads that group's determinant
against the further groups' at the top's self-pairing and the
reversal member's, every factor off the unit at the collected
families' independence (`lem:lowerspan`), so a unit-tailed
coordinate family is refused. -/
theorem coevVec_off (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length) :
    ¬ poly.unitTail
      (coevVec (List.replicate a.length m) b g W).coords := by
  have hex : exhibit b ∈ W.map (fun ws => wact ws (exhibit b)) := by
    rw [← hW]
    match blockcount.blockSpan_prov b with
    | ⟨tail, hsp, _⟩ =>
      rw [hsp]
      exact List.Mem.head tail
  match ground.mem_map_of (fun ws => wact ws (exhibit b)) W _ hex with
  | ⟨ws0, hws0W, hws0e⟩ =>
    have hws0 : ws0 ∈ W.filter
        (fun z => (wact z (exhibit b)).content == (exhibit b).content) :=
      ground.mem_filter_to _ hws0W
        (by rw [hws0e]; exact ground.listEqBeq (exhibit b).content)
    have hdisp := coevOff_display a b m hba hjoin g hg hgc W hW hWb
      (exhibit b).content
      (ground.mem_map_to HVec.content hex) ws0 hws0
    have hY0 : wact ws0 (exhibit b) ∈ blockSpan b := by
      rw [hW]
      exact ground.mem_map_to (fun ws => wact ws (exhibit b)) hws0W
    have hdet : ¬ (elim.detL (elim.gramM
        (((W.filter (fun z => (wact z (exhibit b)).content
            == (exhibit b).content)).map
          (fun ws => wact ws (exhibit b))).map
            HVec.coords))).oneValue BPair.unit := by
      rw [coevGrp_group b W (exhibit b).content, ← hW]
      exact blockDet_off b (exhibit b).content
    have hsc : ¬ (coScale (W.map (fun ws => wact ws (exhibit b)))
        (exhibit b).content).oneValue BPair.unit := by
      rw [← hW]
      exact coScale_off (blockSpan b) (exhibit b).content
        (blockDet_off b)
    have hP : ¬ (elim.dotP g.coords g.coords).oneValue BPair.unit :=
      fun h => span_mem_off a g hg (elim.dotP_self_null _ h)
    have hY : ¬ (dotG (wact ws0 (exhibit b))
        (wact ws0 (exhibit b))).oneValue BPair.unit := by
      rw [dotG_read _ _ rfl]
      exact fun h => span_mem_off b _ hY0 (elim.dotP_self_null _ h)
    intro hu
    refine hY (ground.mul_cancel_unit hP
      (ground.mul_cancel_unit
        (fun h => hdet (ground.mul_cancel_unit hsc h))
        (BPair.oneValue_trans (BPair.oneValue_symm hdisp)
          (elim.oneValue_unit_mul
            (elim.dotP_null_tail_left _ _ hu)))))


/-! `lem:dualread`(iii)'s at-join arm, clause 11's closing
sentence: the coevaluation pairs every stacked raising's image
against every pair at the sum's unit.  A moved pairing is the
walk's read at one further crossing (`blockcount.act_adjoint` at
the raised letter pair), the raised test splits over the tensor
into the two slots' moved reads (`blockcount.act_tensorH`), and
the two moved reads join at partners across the transpose identity
at the exchanged letters: the first slot's read is the extended
dual word's own at the balance partner and the second slot's is
the extended partner word's, the two words the one word extended
by the moved letter, so the two reads enter the sum swapped and
withdraw. -/

/-- The collected family's words carrying one content. -/
private def coevIdx (b : Shape) (W : List (List Nat))
    (mu : List Nat) : List (List Nat) :=
  W.filter (fun z => (wact z (exhibit b)).content == mu)

/-- The partner word image at a key of the content's word list. -/
private def coevY (b : Shape) (W : List (List Nat)) (mu : List Nat)
    (k : Nat) : HVec :=
  wact (ground.getAt ([] : List Nat) (coevIdx b W mu) k) (exhibit b)

/-- The dual word image at a key of the content's word list. -/
private def coevX (b : Shape) (g : HVec) (W : List (List Nat))
    (mu : List Nat) (k : Nat) : HVec :=
  wactT dualTable (ground.getAt ([] : List Nat) (coevIdx b W mu) k) g

/-- The content group's Gram over the partner word images. -/
private def coevG (b : Shape) (W : List (List Nat))
    (mu : List Nat) : elim.Mat :=
  elim.gramM (((coevIdx b W mu).map
    (fun ws => wact ws (exhibit b))).map HVec.coords)

/-- The group's row list reads the key's own partner image. -/
private theorem coevG_row (b : Shape) (W : List (List Nat))
    (mu : List Nat) (k : Nat) (hk : k < (coevIdx b W mu).length) :
    ground.getAt ([] : List BPair)
        (((coevIdx b W mu).map
          (fun ws => wact ws (exhibit b))).map HVec.coords) k
      = (coevY b W mu k).coords := by
  rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
      HVec.coords _ k (by rw [ground.length_map]; exact hk),
    ground.getAt_map ([] : List Nat) (⟨[], []⟩ : HVec)
      (fun ws => wact ws (exhibit b)) _ k hk]
  rfl

/-- The group's order: the Gram is square at the content's word
count. -/
private theorem coevG_sq (b : Shape) (W : List (List Nat))
    (mu : List Nat) :
    elim.sqAt (coevG b W mu) (coevIdx b W mu).length := by
  have h := grp_sqAt ((coevIdx b W mu).map
    (fun ws => wact ws (exhibit b)))
  rw [ground.length_map] at h
  exact h

/-- The group's Gram is symmetric at the content's word count. -/
private theorem coevG_sym (b : Shape) (W : List (List Nat))
    (mu : List Nat) :
    ∀ i < (coevIdx b W mu).length, ∀ j < (coevIdx b W mu).length,
      ground.getAt BPair.unit
          (ground.getAt [] (coevG b W mu) i) j
        = ground.getAt BPair.unit
          (ground.getAt [] (coevG b W mu) j) i := by
  intro i hi j hj
  exact grp_sym ((coevIdx b W mu).map (fun ws => wact ws (exhibit b)))
    i (by rw [ground.length_map]; exact hi)
    j (by rw [ground.length_map]; exact hj)

/-- The group's Gram entry at two keys: the two partner images'
own pairing. -/
private theorem coevG_entry (b : Shape) (W : List (List Nat))
    (mu : List Nat) (i j : Nat) (hi : i < (coevIdx b W mu).length)
    (hj : j < (coevIdx b W mu).length) :
    ground.getAt BPair.unit (ground.getAt [] (coevG b W mu) i) j
      = elim.dotP (coevY b W mu i).coords (coevY b W mu j).coords := by
  have hl : (((coevIdx b W mu).map
      (fun ws => wact ws (exhibit b))).map HVec.coords).length
      = (coevIdx b W mu).length := by
    rw [ground.length_map, ground.length_map]
  rw [show coevG b W mu = elim.gramM (((coevIdx b W mu).map
      (fun ws => wact ws (exhibit b))).map HVec.coords) from rfl,
    elim.gramM_entry _ i j (by rw [hl]; exact hi) (by rw [hl]; exact hj),
    coevG_row b W mu i hi, coevG_row b W mu j hj]

/-- The datum's fold at one content is the group's own double key
fold. -/
private theorem coevBody_fold (b : Shape) (g : HVec)
    (W : List (List Nat)) (mu : List Nat)
    (F : BPair × HVec × HVec → BPair) :
    (ground.famFold BPair.add BPair.unit F
      (coevWBody b g W mu)).oneValue
      (ground.famFold BPair.add BPair.unit (fun j =>
        ground.famFold BPair.add BPair.unit (fun k =>
          F (coScale (W.map (fun ws => wact ws (exhibit b))) mu
              * ground.getAt BPair.unit
                (elim.cofVec (coevG b W mu) k) j,
            coevX b g W mu j, coevY b W mu k))
          (List.range (coevIdx b W mu).length))
        (List.range (coevIdx b W mu).length)) := by
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws F _
      (List.range (coevIdx b W mu).length)) ?_
  exact BPair.oneValue_of_eq
    (ground.famFold_congr_all BPair.add BPair.unit _ _
      (fun j => ground.famFold_map BPair.add BPair.unit F _
        (List.range (coevIdx b W mu).length))
      (List.range (coevIdx b W mu).length))

/-- The group's double key fold at an opaque first slot and one
key's own pairing in the second collapses at the adjugate identity:
the fold over the second key reads the determinant at the stated
key and the sum's unit at every further key, so the first slot's
value at that key carries the block. -/
private theorem blockIdx_one (b : Shape) (W : List (List Nat))
    (mu : List Nat) (s : BPair) (A : Nat → BPair) (k0 : Nat)
    (hk0 : k0 < (coevIdx b W mu).length) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (coevG b W mu) k) j)
          * (A j * elim.dotP (coevY b W mu k0).coords
              (coevY b W mu k).coords))
        (List.range (coevIdx b W mu).length))
      (List.range (coevIdx b W mu).length)).oneValue
      (s * elim.detL (coevG b W mu) * A k0) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => (s * A j)
        * (if j = k0 then elim.detL (coevG b W mu) else BPair.unit))
      (List.range (coevIdx b W mu).length) (fun j hj0 => ?_)) ?_
  · have hj : j < (coevIdx b W mu).length := ground.ltOfMem hj0
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (ground.famFold_congr_all BPair.add BPair.unit _
          (fun k => (s * A j)
            * (elim.dotP (coevY b W mu k0).coords
                (coevY b W mu k).coords
              * ground.getAt BPair.unit
                (elim.cofVec (coevG b W mu) k) j))
          (fun k => by
            rw [BPair.mul_mul_mul_comm s
                (ground.getAt BPair.unit
                  (elim.cofVec (coevG b W mu) k) j) (A j)
                (elim.dotP (coevY b W mu k0).coords
                  (coevY b W mu k).coords),
              BPair.mul_comm
                (ground.getAt BPair.unit
                  (elim.cofVec (coevG b W mu) k) j)
                (elim.dotP (coevY b W mu k0).coords
                  (coevY b W mu k).coords)])
          (List.range (coevIdx b W mu).length))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_mul_left _ _
        (List.range (coevIdx b W mu).length)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    exact elim.adjP_row_fold (coevG b W mu) (coevG_sq b W mu)
      (coevG_sym b W mu) k0 j hk0 hj
      (fun k => elim.dotP (coevY b W mu k0).coords
        (coevY b W mu k).coords)
      (fun k hk => (coevG_entry b W mu k0 k hk0 hk).symm)
  · refine ground.foldB_pickRange _ k0 _ (coevIdx b W mu).length hk0 ?_ ?_
    · rw [if_pos (show k0 = k0 from rfl)]
      refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_assoc, BPair.mul_comm (A k0)
        (elim.detL (coevG b W mu)), ← BPair.mul_assoc]
    · intro t _ hti
      rw [if_neg hti]
      exact BPair.mul_unit _

/-- The Gram's column against the cofactor vectors at a stated
column key: the determinant at the column's own key and the sum's
unit at every further key. -/
private theorem blockIdx_col (b : Shape) (W : List (List Nat))
    (mu : List Nat) (l j : Nat) (hl : l < (coevIdx b W mu).length)
    (hj : j < (coevIdx b W mu).length) :
    (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit
          (ground.getAt [] (coevG b W mu) k) l
        * ground.getAt BPair.unit (elim.cofVec (coevG b W mu) k) j)
      (List.range (coevIdx b W mu).length)).oneValue
      (if j = l then elim.detL (coevG b W mu) else BPair.unit) :=
  elim.adjP_row_fold (coevG b W mu) (coevG_sq b W mu)
    (coevG_sym b W mu) l j hl hj
    (fun k => ground.getAt BPair.unit
      (ground.getAt [] (coevG b W mu) k) l)
    (fun k hk => coevG_sym b W mu k hk l hl)

/-- The group's adjugate solve at a scaled combination of the
group's own rows: the scale clears to the determinant against the
combination's own coefficient at that key. -/
private theorem blockIdx_solve (b : Shape) (W : List (List Nat))
    (mu : List Nat) (c1 : BPair) (gam : List BPair)
    (hgl : gam.length = (coevIdx b W mu).length)
    (Psi : Nat → BPair)
    (hPsi : ∀ k, k < (coevIdx b W mu).length →
      (c1 * Psi k).oneValue
        (elim.dotP gam (ground.getAt [] (coevG b W mu) k)))
    (j : Nat) (hj : j < (coevIdx b W mu).length) :
    (c1 * ground.famFold BPair.add BPair.unit
        (fun k => Psi k
          * ground.getAt BPair.unit (elim.cofVec (coevG b W mu) k) j)
        (List.range (coevIdx b W mu).length)).oneValue
      (elim.detL (coevG b W mu) * ground.getAt BPair.unit gam j) := by
  have hGl : (coevG b W mu).length = (coevIdx b W mu).length :=
    elim.sqAt_len (coevG_sq b W mu)
  have hrows : elim.rowsLen (coevIdx b W mu).length (coevG b W mu) :=
    elim.rowsLen_of_sqAt (coevG_sq b W mu)
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_mul_left c1 _
      (List.range (coevIdx b W mu).length))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => ground.famFold BPair.add BPair.unit
        (fun l => (ground.getAt BPair.unit gam l
            * ground.getAt BPair.unit
              (ground.getAt [] (coevG b W mu) k) l)
          * ground.getAt BPair.unit
            (elim.cofVec (coevG b W mu) k) j)
        (List.range (coevIdx b W mu).length))
      (List.range (coevIdx b W mu).length) (fun k hk0 => ?_)) ?_
  · have hk : k < (coevIdx b W mu).length := ground.ltOfMem hk0
    have hrowk : (ground.getAt [] (coevG b W mu) k).length
        = (coevIdx b W mu).length :=
      elim.rowsLen_getAt (coevG b W mu) k hrows (by rw [hGl]; exact hk)
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc c1 (Psi k) _).symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (hPsi k hk) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (congrArg
        (fun x => x * ground.getAt BPair.unit
          (elim.cofVec (coevG b W mu) k) j)
        (fold_dotP gam (ground.getAt [] (coevG b W mu) k)
          (coevIdx b W mu).length hgl hrowk).symm)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (ground.foldB_mul_left _ _
        (List.range (coevIdx b W mu).length))) ?_
    exact ground.foldB_congr_members _ _
      (List.range (coevIdx b W mu).length)
      (fun l _ => BPair.oneValue_of_eq (BPair.mul_comm _ _))
  · refine BPair.oneValue_trans
      (ground.foldB_swapL _ (List.range (coevIdx b W mu).length)
        (List.range (coevIdx b W mu).length)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun l => ground.getAt BPair.unit gam l
          * (if j = l then elim.detL (coevG b W mu) else BPair.unit))
        (List.range (coevIdx b W mu).length) (fun l hl0 => ?_)) ?_
    · have hl : l < (coevIdx b W mu).length := ground.ltOfMem hl0
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (ground.famFold_congr_all BPair.add BPair.unit _
            (fun k => ground.getAt BPair.unit gam l
              * (ground.getAt BPair.unit
                  (ground.getAt [] (coevG b W mu) k) l
                * ground.getAt BPair.unit
                  (elim.cofVec (coevG b W mu) k) j))
            (fun k => BPair.mul_assoc _ _ _)
            (List.range (coevIdx b W mu).length))) ?_
      refine BPair.oneValue_trans
        (ground.foldB_mul_left _ _
          (List.range (coevIdx b W mu).length)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl _)
        (blockIdx_col b W mu l j hl hj)
    · refine ground.foldB_pickRange _ j _ (coevIdx b W mu).length hj ?_ ?_
      · rw [if_pos (show j = j from rfl)]
        exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
      · intro t _ hti
        rw [if_neg (fun he : j = t => hti he.symm)]
        exact BPair.mul_unit _

/-- The group's double key fold at an opaque first slot and a
scaled combination of the group's own rows in the second: the
scale clears to the determinant against the combination's
coefficients paired with the first slot's values. -/
private theorem blockIdx_combo (b : Shape) (W : List (List Nat))
    (mu : List Nat) (s c1 : BPair) (A : Nat → BPair)
    (gam : List BPair) (hgl : gam.length = (coevIdx b W mu).length)
    (Psi : Nat → BPair)
    (hPsi : ∀ k, k < (coevIdx b W mu).length →
      (c1 * Psi k).oneValue
        (elim.dotP gam (ground.getAt [] (coevG b W mu) k))) :
    (c1 * ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (coevG b W mu) k) j)
          * (A j * Psi k))
        (List.range (coevIdx b W mu).length))
      (List.range (coevIdx b W mu).length)).oneValue
      (s * elim.detL (coevG b W mu)
        * elim.dotP gam
          ((List.range (coevIdx b W mu).length).map A)) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_mul_left c1 _
      (List.range (coevIdx b W mu).length))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => (s * elim.detL (coevG b W mu))
        * (ground.getAt BPair.unit gam j
          * ground.getAt BPair.unit
            ((List.range (coevIdx b W mu).length).map A) j))
      (List.range (coevIdx b W mu).length) (fun j hj0 => ?_)) ?_
  · have hj : j < (coevIdx b W mu).length := ground.ltOfMem hj0
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c1)
        (BPair.oneValue_of_eq
          (ground.famFold_congr_all BPair.add BPair.unit _
            (fun k => (s * A j)
              * (Psi k * ground.getAt BPair.unit
                  (elim.cofVec (coevG b W mu) k) j))
            (fun k => by
              rw [BPair.mul_mul_mul_comm s
                  (ground.getAt BPair.unit
                    (elim.cofVec (coevG b W mu) k) j) (A j) (Psi k),
                BPair.mul_comm
                  (ground.getAt BPair.unit
                    (elim.cofVec (coevG b W mu) k) j) (Psi k)])
            (List.range (coevIdx b W mu).length)))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c1)
        (ground.foldB_mul_left _ _
          (List.range (coevIdx b W mu).length))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm c1 (s * A j) _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (s * A j))
        (blockIdx_solve b W mu c1 gam hgl Psi hPsi j hj)) ?_
    rw [ground.getAt_map 0 BPair.unit A
        (List.range (coevIdx b W mu).length) j
        (by rw [ground.length_range]; exact hj),
      ground.getAt_range (coevIdx b W mu).length j hj]
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_mul_mul_comm s (A j) (elim.detL (coevG b W mu))
        (ground.getAt BPair.unit gam j),
      BPair.mul_comm (A j) (ground.getAt BPair.unit gam j)]
  · refine BPair.oneValue_trans
      (ground.foldB_mul_left _ _
        (List.range (coevIdx b W mu).length)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    exact BPair.oneValue_of_eq
      (fold_dotP gam ((List.range (coevIdx b W mu).length).map A)
        (coevIdx b W mu).length hgl
        (ground.length_mapRange _ _))

/-- A listed word at a key of one content's word list: the slot
reads at that key. -/
private theorem coevSlotAt (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu : List Nat) (k : Nat) (hk : k < (coevIdx b W mu).length) :
    (coevY b W mu k).content = mu
      ∧ coevY b W mu k ∈ blockSpan b
      ∧ sized (coevX b g W mu k)
      ∧ (coevX b g W mu k).content.length = a.length
      ∧ ground.sumNat (coevX b g W mu k).content
        = ground.sumNat g.content
      ∧ List.zipWith (fun u w => u + w) mu
          (coevX b g W mu k).content = List.replicate a.length m
      ∧ List.zipWith (fun u w => u + w)
          (coevX b g W mu k).content mu = List.replicate a.length m
      ∧ mu.length = a.length :=
  coevSlot a b m hba hjoin g hg hgc W hW hWb mu _
    (ground.mem_getAt ([] : List Nat) (coevIdx b W mu) k hk)

/-- The datum's fold against a stated test tensor at the group's
own content: the two tensors' pairing factorizes at the shared
contents (`blockcount.dotP_tensorH`), so the block is the group's
double key fold at the test's two factors' own pairings. -/
private theorem coevTest_fold (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu : List Nat) (hmul : mu.length = a.length)
    (x y : HVec) (hsx : sized x) (hsy : sized y)
    (hxw : x.content.length = a.length)
    (hyc : y.content = mu)
    (hxy : List.zipWith (fun p q => p + q) x.content mu
      = List.replicate a.length m)
    (E : BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun t => (t.1 * elim.dotP (tensorH x y).coords
          (tensorH t.2.1 t.2.2).coords) * E)
      (coevWBody b g W mu)).oneValue
      (ground.famFold BPair.add BPair.unit (fun j =>
        ground.famFold BPair.add BPair.unit (fun k =>
          (coScale (W.map (fun ws => wact ws (exhibit b))) mu
              * ground.getAt BPair.unit
                (elim.cofVec (coevG b W mu) k) j)
            * ((E * elim.dotP x.coords (coevX b g W mu j).coords)
              * elim.dotP y.coords (coevY b W mu k).coords))
          (List.range (coevIdx b W mu).length))
        (List.range (coevIdx b W mu).length)) := by
  refine BPair.oneValue_trans (coevBody_fold b g W mu _) ?_
  refine ground.foldB_congr_members _ _
    (List.range (coevIdx b W mu).length) (fun j hj0 => ?_)
  have hj : j < (coevIdx b W mu).length := ground.ltOfMem hj0
  have hsj := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu j hj
  refine ground.foldB_congr_members _ _
    (List.range (coevIdx b W mu).length) (fun k hk0 => ?_)
  have hk : k < (coevIdx b W mu).length := ground.ltOfMem hk0
  have hsk := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu k hk
  have hxj : x.content = (coevX b g W mu j).content :=
    blockcount.zipWith_add_cancelL mu x.content
      (coevX b g W mu j).content a.length hmul hxw hsj.2.2.2.1
      ((ground.zipWith_add_comm mu x.content).trans
        (hxy.trans hsj.2.2.2.2.2.1.symm))
  have hT := blockcount.dotP_tensorH x y (coevX b g W mu j)
    (coevY b W mu k) hsx hsy hsj.2.2.1
    ((lowerspan.spanReads b).1 _ hsk.2.1)
    (by rw [hxw, hyc, hmul]) hxj (by rw [hyc, hsk.1])
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.mul_congr (BPair.oneValue_refl _) hT)
      (BPair.oneValue_refl E)) ?_
  refine BPair.oneValue_of_eq ?_
  rw [BPair.mul_assoc, BPair.mul_comm
      (elim.dotP x.coords (coevX b g W mu j).coords
        * elim.dotP y.coords (coevY b W mu k).coords) E,
    ← BPair.mul_assoc E]

/-- The named group's block at a test tensor whose partner factor
is the group's own key: the double key fold collapses at the
adjugate identity to the group's determinant against the further
groups' at the test's first factor paired with that key's dual
word. -/
private theorem coevOn_x (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu : List Nat) (k0 : Nat) (hk0 : k0 < (coevIdx b W mu).length)
    (x : HVec) (hsx : sized x)
    (hxw : x.content.length = a.length)
    (hxy : List.zipWith (fun p q => p + q) x.content mu
      = List.replicate a.length m)
    (E : BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun t => (t.1 * elim.dotP
          (tensorH x (coevY b W mu k0)).coords
          (tensorH t.2.1 t.2.2).coords) * E)
      (coevWBody b g W mu)).oneValue
      (coScale (W.map (fun ws => wact ws (exhibit b))) mu
          * elim.detL (coevG b W mu)
        * (E * elim.dotP x.coords (coevX b g W mu k0).coords)) := by
  have hs0 := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu k0 hk0
  refine BPair.oneValue_trans
    (coevTest_fold a b m hba hjoin g hg hgc W hW hWb mu
      hs0.2.2.2.2.2.2.2 x (coevY b W mu k0) hsx
      ((lowerspan.spanReads b).1 _ hs0.2.1) hxw hs0.1 hxy E) ?_
  exact blockIdx_one b W mu
    (coScale (W.map (fun ws => wact ws (exhibit b))) mu)
    (fun j => E * elim.dotP x.coords (coevX b g W mu j).coords)
    k0 hk0

/-- A further group's block reads the sum's unit at a stated test
tensor: the test's first factor sits at the group's own complement
content only where the two contents agree, so every entry's pairing
splits at the unit (`blockcount.dotP_tensorH_off`). -/
private theorem coevOff_x (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu nu : List Nat) (hne : ¬ nu = mu) (hmul : mu.length = a.length)
    (x y : HVec)
    (hxw : x.content.length = a.length)
    (hxd : ground.sumNat x.content = ground.sumNat g.content)
    (hyc : y.content = mu)
    (hxy : List.zipWith (fun p q => p + q) x.content mu
      = List.replicate a.length m)
    (E : BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun t => (t.1 * elim.dotP (tensorH x y).coords
          (tensorH t.2.1 t.2.2).coords) * E)
      (coevWBody b g W nu)).oneValue BPair.unit := by
  refine ground.foldB_null _ (coevWBody b g W nu) (fun t htc => ?_)
  match coevWBody_slots b g W nu t
      (ground.mem_of_countOf_pos _ _ htc) with
  | ⟨wj, hj, wk, hk, h1, h2⟩ =>
    have hsj := coevSlot a b m hba hjoin g hg hgc W hW hWb nu wj hj
    have hsk := coevSlot a b m hba hjoin g hg hgc W hW hWb nu wk hk
    have hne' : ¬ x.content = (wactT dualTable wj g).content := by
      intro he
      refine hne (blockcount.zipWith_add_cancelL x.content nu mu
        a.length hxw hsj.2.2.2.2.2.2.2 hmul ?_)
      rw [he]
      exact hsj.2.2.2.2.2.2.1.trans
        (by rw [← he]; exact hxy.symm)
    have hoff := blockcount.dotP_tensorH_off x y
      (wactT dualTable wj g) (wact wk (exhibit b))
      (by rw [hxw, hyc, hmul])
      (by rw [hsj.2.2.2.1, hsk.1, hsj.2.2.2.2.2.2.2])
      (hxd.trans hsj.2.2.2.2.1.symm)
      (by
        show List.zipWith (fun p q => p + q) x.content y.content
          = List.zipWith (fun p q => p + q)
            (wactT dualTable wj g).content
            (wact wk (exhibit b)).content
        rw [hyc, hsk.1, hsj.2.2.2.2.2.2.1]
        exact hxy)
      hne'
    rw [h1, h2]
    refine elim.oneValue_unit_mul ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm t.1 _)) ?_
    exact elim.oneValue_unit_mul hoff

/-- The content group's Gram determinant is the family's own block
determinant at that content. -/
private theorem coevG_det (b : Shape) (W : List (List Nat))
    (mu : List Nat) :
    elim.detL (coevG b W mu)
      = blockDet (W.map (fun ws => wact ws (exhibit b))) mu := by
  show elim.detL (elim.gramM (((W.filter
        (fun ws => (wact ws (exhibit b)).content == mu)).map
      (fun ws => wact ws (exhibit b))).map HVec.coords))
    = blockDet (W.map (fun ws => wact ws (exhibit b))) mu
  rw [coevGrp_group b W mu]
  rfl

/-- The coevaluation's pairing against a test tensor whose partner
factor is one group's own key: the entries off that group read the
sum's unit and the group's own block collapses at the adjugate
identity, so the pairing reads every group's determinant against
the test's first factor paired with that key's dual word. -/
private theorem coevPair_key (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu : List Nat)
    (hmu : mu ∈ (W.map (fun ws => wact ws (exhibit b))).map
      HVec.content)
    (k0 : Nat) (hk0 : k0 < (coevIdx b W mu).length)
    (x : HVec) (hsx : sized x)
    (hxw : x.content.length = a.length)
    (hxd : ground.sumNat x.content = ground.sumNat g.content)
    (hxy : List.zipWith (fun p q => p + q) x.content mu
      = List.replicate a.length m)
    (E : BPair) :
    (elim.dotP (coevVec (List.replicate a.length m) b g W).coords
        (tensorH x (coevY b W mu k0)).coords * E).oneValue
      (detAll (W.map (fun ws => wact ws (exhibit b)))
        * (E * elim.dotP x.coords (coevX b g W mu k0).coords)) := by
  have hs0 := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu k0 hk0
  have hcount : ground.countOf mu
      (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
        HVec.content)) = 1 :=
    ground.countOf_dedupL_one hmu
  refine BPair.oneValue_trans
    (coevPair_fold b g W (List.replicate a.length m)
      (tensorH x (coevY b W mu k0)) E
      (elim.rowsLen_map _ _ (coevW b g W)
        (fun t htm => (coevW_row a b m hba hjoin g hg hgc W hW hWb t
          htm).2.1))) ?_
  rw [coevW_flat b g W]
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws _
      (coevWBody b g W)
      (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
        HVec.content))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_pick _ mu _
      (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
        HVec.content)) hcount
      (coevOn_x a b m hba hjoin g hg hgc W hW hWb mu k0 hk0 x hsx
        hxw hxy E)
      (fun nu _ hne => coevOff_x a b m hba hjoin g hg hgc W hW hWb
        mu nu hne hs0.2.2.2.2.2.2.2 x (coevY b W mu k0) hxw hxd
        hs0.1 hxy E)) ?_
  rw [coevG_det b W mu, scale_detAll
    (W.map (fun ws => wact ws (exhibit b))) mu hcount]
  exact BPair.oneValue_refl _

/-- The coevaluation's pairing against a test tensor whose partner
factor is a scaled combination of one group's own rows: the scale
clears to every group's determinant against the combination's
coefficients paired with the group's dual words. -/
private theorem coevPair_gam (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (mu : List Nat)
    (hmu : mu ∈ (W.map (fun ws => wact ws (exhibit b))).map
      HVec.content)
    (hmul : mu.length = a.length)
    (x y : HVec) (hsx : sized x) (hsy : sized y)
    (hxw : x.content.length = a.length)
    (hxd : ground.sumNat x.content = ground.sumNat g.content)
    (hyc : y.content = mu)
    (hxy : List.zipWith (fun p q => p + q) x.content mu
      = List.replicate a.length m)
    (c1 : BPair) (gam : List BPair)
    (hgl : gam.length = (coevIdx b W mu).length)
    (hcom : ∀ k, k < (coevIdx b W mu).length →
      (c1 * elim.dotP y.coords (coevY b W mu k).coords).oneValue
        (elim.dotP gam (ground.getAt [] (coevG b W mu) k)))
    (E : BPair) :
    (c1 * (elim.dotP (coevVec (List.replicate a.length m) b g W).coords
        (tensorH x y).coords * E)).oneValue
      (detAll (W.map (fun ws => wact ws (exhibit b)))
        * elim.dotP gam
          ((List.range (coevIdx b W mu).length).map
            (fun j => E * elim.dotP x.coords
              (coevX b g W mu j).coords))) := by
  have hcount : ground.countOf mu
      (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
        HVec.content)) = 1 :=
    ground.countOf_dedupL_one hmu
  have hchain : (elim.dotP
        (coevVec (List.replicate a.length m) b g W).coords
        (tensorH x y).coords * E).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun t => (t.1 * elim.dotP (tensorH x y).coords
            (tensorH t.2.1 t.2.2).coords) * E)
        (coevWBody b g W mu)) := by
    refine BPair.oneValue_trans
      (coevPair_fold b g W (List.replicate a.length m)
        (tensorH x y) E
        (elim.rowsLen_map _ _ (coevW b g W)
          (fun t htm => (coevW_row a b m hba hjoin g hg hgc W hW hWb
            t htm).2.1))) ?_
    rw [coevW_flat b g W]
    refine BPair.oneValue_trans
      (ground.famFold_flatMap_ov ground.bpairFoldLaws _
        (coevWBody b g W)
        (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
          HVec.content))) ?_
    exact ground.foldB_pick _ mu _
      (ground.dedupL ((W.map (fun ws => wact ws (exhibit b))).map
        HVec.content)) hcount (BPair.oneValue_refl _)
      (fun nu _ hne => coevOff_x a b m hba hjoin g hg hgc W hW hWb
        mu nu hne hmul x y hxw hxd hyc hxy E)
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl c1) hchain) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl c1)
      (coevTest_fold a b m hba hjoin g hg hgc W hW hWb mu hmul
        x y hsx hsy hxw hyc hxy E)) ?_
  refine BPair.oneValue_trans
    (blockIdx_combo b W mu
      (coScale (W.map (fun ws => wact ws (exhibit b))) mu) c1
      (fun j => E * elim.dotP x.coords (coevX b g W mu j).coords)
      gam hgl
      (fun k => elim.dotP y.coords (coevY b W mu k).coords)
      hcom) ?_
  rw [coevG_det b W mu, scale_detAll
    (W.map (fun ws => wact ws (exhibit b))) mu hcount]
  exact BPair.oneValue_refl _

/-- Two families whose pairwise pairings agree at the
cross-multiplied scales carry every relation across: a combination
reading the sum's unit on the second family reads it on the first,
the self-pairings transported through the two families' pairings
and the off-unit scale cleared (`lem:blockcount`(iii)'s transport
read at the two blocks' own widths). -/
private theorem dualGram_null (mX mY : Nat) (s s' : BPair)
    (hs : ¬ s.oneValue BPair.unit) (X Y : elim.Mat)
    (hX : elim.rowsLen mX X) (hY : elim.rowsLen mY Y)
    (hlen : Y.length = X.length)
    (hgram : ∀ k, k < X.length → ∀ l, l < X.length →
      (s' * elim.dotP (ground.getAt [] Y k)
          (ground.getAt [] Y l)).oneValue
        (s * elim.dotP (ground.getAt [] X k)
          (ground.getAt [] X l)))
    (cs : List BPair)
    (hnull : poly.unitTail (elim.combo mY cs Y)) :
    poly.unitTail (elim.combo mX cs X) := by
  have hrow : ∀ k, k < X.length →
      (s' * elim.dotP (ground.getAt [] Y k)
          (elim.combo mY cs Y)).oneValue
        (s * elim.dotP (ground.getAt [] X k)
          (elim.combo mX cs X)) := by
    intro k hk
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s')
        (elim.dotP_combo cs Y (ground.getAt [] Y k) mY hY)) ?_
    refine BPair.oneValue_trans ?_
      (BPair.mul_congr (BPair.oneValue_refl s)
        (BPair.oneValue_symm
          (elim.dotP_combo cs X (ground.getAt [] X k) mX hX)))
    refine elim.dotP_scaleTransport s s' cs
      (X.map (fun row => elim.dotP (ground.getAt [] X k) row))
      (Y.map (fun row => elim.dotP (ground.getAt [] Y k) row))
      (by rw [ground.length_map, ground.length_map]; exact hlen) ?_
    intro l hl
    rw [ground.length_map] at hl
    have hl' : l < Y.length := by rw [hlen]; exact hl
    rw [ground.getAt_map ([] : List BPair) BPair.unit
        (fun row => elim.dotP (ground.getAt [] Y k) row) Y l hl',
      ground.getAt_map ([] : List BPair) BPair.unit
        (fun row => elim.dotP (ground.getAt [] X k) row) X l hl]
    exact hgram k hk l hl
  have hfull : (s' * elim.dotP (elim.combo mY cs Y)
        (elim.combo mY cs Y)).oneValue
      (s * elim.dotP (elim.combo mX cs X)
        (elim.combo mX cs X)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s')
        (elim.dotP_combo cs Y (elim.combo mY cs Y) mY hY)) ?_
    refine BPair.oneValue_trans ?_
      (BPair.mul_congr (BPair.oneValue_refl s)
        (BPair.oneValue_symm
          (elim.dotP_combo cs X (elim.combo mX cs X) mX hX)))
    refine elim.dotP_scaleTransport s s' cs
      (X.map (fun row => elim.dotP (elim.combo mX cs X) row))
      (Y.map (fun row => elim.dotP (elim.combo mY cs Y) row))
      (by rw [ground.length_map, ground.length_map]; exact hlen) ?_
    intro l hl
    rw [ground.length_map] at hl
    have hl' : l < Y.length := by rw [hlen]; exact hl
    rw [ground.getAt_map ([] : List BPair) BPair.unit
        (fun row => elim.dotP (elim.combo mY cs Y) row) Y l hl',
      ground.getAt_map ([] : List BPair) BPair.unit
        (fun row => elim.dotP (elim.combo mX cs X) row) X l hl,
      elim.dotP_comm (elim.combo mY cs Y) (ground.getAt [] Y l),
      elim.dotP_comm (elim.combo mX cs X) (ground.getAt [] X l)]
    exact hrow l hl
  refine elim.dotP_self_null _ (ground.mul_cancel_unit hs ?_)
  refine BPair.oneValue_trans (BPair.oneValue_symm hfull) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl s')
      (elim.dotP_null_tail_left _ _ hnull)) ?_
  exact BPair.mul_unit s'

private theorem unitTail_swapAdd (c : BPair) (u w : List BPair)
    (h : poly.oneValue (elim.vecScale c u) w) :
    poly.unitTail (elim.vecAdd (elim.vecScale c.swap u) w) := by
  rw [elim.vecScale_swap]
  exact elim.null_swap_add (elim.vecScale c u) w h

private theorem coevVec_sized (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length) :
    sized (coevVec (List.replicate a.length m) b g W) :=
  elim.length_combo _ _ _
    (elim.rowsLen_map _ _ (coevW b g W)
      (fun t htm => (coevW_row a b m hba hjoin g hg hgc W hW hWb t
        htm).2.1))

/-- The dual word pair's Gram read at matched contents: the two
tops' self-pairings scale the two families' own pairings across. -/
private theorem dualPairRead (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (ws ws' : List Nat)
    (hb : ∀ l ∈ ws, l + 1 < a.length)
    (hb' : ∀ l ∈ ws', l + 1 < a.length)
    (hcy : (wact ws (exhibit b)).content
      = (wact ws' (exhibit b)).content)
    (hcx : (wactT dualTable ws g).content
      = (wactT dualTable ws' g).content) :
    (elim.dotP g.coords g.coords
        * elim.dotP (wact ws (exhibit b)).coords
          (wact ws' (exhibit b)).coords).oneValue
      (elim.dotP (exhibit b).coords (exhibit b).coords
        * elim.dotP (wactT dualTable ws g).coords
          (wactT dualTable ws' g).coords) := by
  have h := dualGram a b m hba hjoin g hg hgc ws ws' hb hb'
  rw [dotG_read _ _ hcy, dotG_read _ _ hcx] at h
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
  exact BPair.oneValue_trans h (BPair.oneValue_of_eq
    (BPair.mul_comm _ _))

/-- A word's two images are live together: the partner image sits
off the unit tail exactly where the dual image does, the two tops'
self-pairings off the unit at the collected families'
independence. -/
private theorem dualWord_nullX (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (ws : List Nat) (hb : ∀ l ∈ ws, l + 1 < a.length)
    (hY : poly.unitTail (wact ws (exhibit b)).coords) :
    poly.unitTail (wactT dualTable ws g).coords := by
  have hE : ¬ (elim.dotP (exhibit b).coords
      (exhibit b).coords).oneValue BPair.unit :=
    fun h => blockcount.exhibit_off_unit b (elim.dotP_self_null _ h)
  have h := dualPairRead a b m hba hjoin g hg hgc ws ws hb hb rfl rfl
  refine elim.dotP_self_null _ (ground.mul_cancel_unit hE ?_)
  refine BPair.oneValue_trans (BPair.oneValue_symm h) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (elim.dotP_null_tail_left _ _ hY)) ?_
  exact BPair.mul_unit _

/-- The dual image is live where the partner image is. -/
private theorem dualWord_nullY (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (ws : List Nat) (hb : ∀ l ∈ ws, l + 1 < a.length)
    (hX : poly.unitTail (wactT dualTable ws g).coords) :
    poly.unitTail (wact ws (exhibit b)).coords := by
  have hP : ¬ (elim.dotP g.coords g.coords).oneValue BPair.unit :=
    fun h => span_mem_off a g hg (elim.dotP_self_null _ h)
  have h := dualPairRead a b m hba hjoin g hg hgc ws ws hb hb rfl rfl
  refine elim.dotP_self_null _ (ground.mul_cancel_unit hP ?_)
  refine BPair.oneValue_trans h ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (elim.dotP_null_tail_left _ _ hX)) ?_
  exact BPair.mul_unit _

/-- The dual word's entry at the raised letter's partner: at the
join's moved columns the dual content carries one box more than
the partner's at the letter above the raise. -/
private theorem coevKer_occX (a m i : Nat) (mu0 nuX vc : List Nat)
    (hm : 0 < m) (hi : i + 1 < a)
    (hvc : vc.length = a) (hnu : nuX.length = a) (hmu : mu0.length = a)
    (h1 : List.zipWith (fun p q => p + q) mu0 nuX
      = List.replicate a m)
    (h2 : List.zipWith (fun p q => p + q) mu0 vc
      = moveAt i (i + 1) (List.replicate a m)) :
    ground.getAt 0 nuX (i + 1) = ground.getAt 0 vc (i + 1) + 1 := by
  have hcl : (List.replicate a m).length = a := ground.length_replicate m a
  have hmi : i + 1 < mu0.length := by rw [hmu]; exact hi
  have hni : i + 1 < nuX.length := by rw [hnu]; exact hi
  have hvi : i + 1 < vc.length := by rw [hvc]; exact hi
  have e1 : ground.getAt 0 mu0 (i + 1) + ground.getAt 0 nuX (i + 1)
      = m := by
    rw [← ground.getAt_zipWith 0 0 0 (fun p q => p + q) mu0 nuX
      (i + 1) hmi hni, h1,
      ground.getAt_replicate 0 m a (i + 1) hi]
  have e2 : ground.getAt 0 mu0 (i + 1) + ground.getAt 0 vc (i + 1) + 1
      = m := by
    rw [← ground.getAt_zipWith 0 0 0 (fun p q => p + q) mu0 vc
      (i + 1) hmi hvi, h2]
    show ground.getAt 0 (ground.bumpAt i
      (ground.dipAt (i + 1) (List.replicate a m))) (i + 1) + 1 = m
    rw [ground.getAt_bumpAt_ne i _ (i + 1) (Nat.succ_ne_self i)]
    refine (ground.getAt_dipAt_self (i + 1) (List.replicate a m)
      ?_).trans (ground.getAt_replicate 0 m a (i + 1) hi)
    rw [ground.getAt_replicate 0 m a (i + 1) hi]
    exact hm
  refine ground.addCancelL (ground.getAt 0 mu0 (i + 1)) ?_
  rw [e1, ← e2, Nat.add_assoc]

private theorem coevKer_vacT (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (i : Nat) (hi : i + 1 < a.length) (hm : 0 < m)
    (v : HVec) (hsv : sized v) (hvl : v.content.length = a.length)
    (mu0 : List Nat) (k0 : Nat) (hk0 : k0 < (coevIdx b W mu0).length)
    (hjv : List.zipWith (fun p q => p + q) v.content mu0
      = moveAt i (i + 1) (List.replicate a.length m))
    (hz : ground.getAt 0 v.content i = 0) :
    (elim.dotP v.coords (wactT dualTable
      (i :: ground.getAt ([] : List Nat)
        (coevIdx b W mu0) k0) g).coords).oneValue BPair.unit := by
  have hs0 := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu0 k0 hk0
  have hocc : 0 < ground.getAt 0
      (coevX b g W mu0 k0).content (i + 1) := by
    rw [coevKer_occX a.length m i mu0 (coevX b g W mu0 k0).content
      v.content hm hi hvl hs0.2.2.2.1 hs0.2.2.2.2.2.2.2
      hs0.2.2.2.2.2.1
      ((ground.zipWith_add_comm mu0 v.content).trans hjv)]
    exact Nat.succ_pos _
  have hvX : v.content
      = moveAt i (i + 1) (coevX b g W mu0 k0).content := by
    refine blockcount.zipWith_add_cancelL mu0 v.content _ a.length
      hs0.2.2.2.2.2.2.2 hvl
      (by rw [length_moveAt]; exact hs0.2.2.2.1) ?_
    rw [(ground.zipWith_add_comm mu0 v.content).trans hjv,
      blockcount.moveAt_zipWith_right i (i + 1) mu0
        (coevX b g W mu0 k0).content hocc, hs0.2.2.2.2.2.1]
  have hXl : (coevX b g W mu0 k0).content.length = a.length :=
    hs0.2.2.2.1
  have hadj := blockcount.act_adjoint (coevX b g W mu0 k0) v i (i + 1)
    hs0.2.2.1 hsv (by rw [hXl]; exact Nat.lt_of_succ_lt hi)
    (by rw [hXl]; exact hi) (fun he => Nat.succ_ne_self i he.symm)
    hocc hvX
  have hnull : (elim.dotP
      (act i (i + 1) (coevX b g W mu0 k0)).coords
      v.coords).oneValue BPair.unit :=
    BPair.oneValue_trans hadj
      (elim.dotP_null_tail_right _ _ (tops.act_null (i + 1) i v hz))
  show (elim.dotP v.coords (poly.neg
    (act i (i + 1) (coevX b g W mu0 k0)).coords)).oneValue BPair.unit
  rw [show poly.neg (act i (i + 1) (coevX b g W mu0 k0)).coords
      = (act i (i + 1) (coevX b g W mu0 k0)).coords.map BPair.swap
    from rfl, elim.dotP_swapMap,
    elim.dotP_comm v.coords
      (act i (i + 1) (coevX b g W mu0 k0)).coords]
  exact ground.swap_congr hnull

/-- The first slot's moved read at an occupied raise letter: the
lowered member's pairing against the group's key walks across the
transpose identity to the member's own pairing against the dual
word extended by the letter, entering swapped at the balance
partner. -/
private theorem coevKer_termL (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (i : Nat) (hi : i + 1 < a.length) (hm : 0 < m)
    (v : HVec) (hsv : sized v) (hvl : v.content.length = a.length)
    (mu0 : List Nat) (k0 : Nat) (hk0 : k0 < (coevIdx b W mu0).length)
    (hjv : List.zipWith (fun p q => p + q) v.content mu0
      = moveAt i (i + 1) (List.replicate a.length m))
    (hocc : 0 < ground.getAt 0 v.content i)
    (E : BPair) :
    (elim.dotP (coevVec (List.replicate a.length m) b g W).coords
        (tensorH (act (i + 1) i v)
          (coevY b W mu0 k0)).coords * E).oneValue
      (detAll (W.map (fun ws => wact ws (exhibit b)))
        * (E * (elim.dotP v.coords (wactT dualTable
            (i :: ground.getAt ([] : List Nat)
              (coevIdx b W mu0) k0) g).coords).swap)) := by
  have hs0 := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu0 k0 hk0
  have hccocc : 0 < ground.getAt 0
      (List.replicate a.length m) (i + 1) := by
    rw [ground.getAt_replicate 0 m a.length (i + 1) hi]
    exact hm
  have hxl : (act (i + 1) i v).content.length = a.length := by
    show (moveAt (i + 1) i v.content).length = a.length
    rw [length_moveAt]
    exact hvl
  have hxc : List.zipWith (fun p q => p + q)
      (act (i + 1) i v).content mu0
      = List.replicate a.length m := by
    show List.zipWith (fun p q => p + q)
      (moveAt (i + 1) i v.content) mu0 = _
    rw [blockcount.moveAt_zipWith_left (i + 1) i v.content mu0 hocc,
      hjv, blockcount.moveAt_round_at (i + 1) i
        (List.replicate a.length m) hccocc]
  have hxX : (act (i + 1) i v).content
      = (coevX b g W mu0 k0).content :=
    blockcount.zipWith_add_cancelL mu0 _ _ a.length
      hs0.2.2.2.2.2.2.2 hxl hs0.2.2.2.1
      (((ground.zipWith_add_comm mu0 (act (i + 1) i v).content).trans
        hxc).trans hs0.2.2.2.2.2.1.symm)
  have hmu : mu0 ∈ (W.map (fun ws => wact ws (exhibit b))).map
      HVec.content := by
    have h1 : coevY b W mu0 k0 ∈ W.map (fun ws => wact ws (exhibit b)) := by
      rw [← hW]
      exact hs0.2.1
    have h2 := ground.mem_map_to HVec.content h1
    rw [hs0.1] at h2
    exact h2
  have hkey := coevPair_key a b m hba hjoin g hg hgc W hW hWb mu0 hmu
    k0 hk0 (act (i + 1) i v) (blockcount.act_sized (i + 1) i v) hxl
    (by rw [hxX]; exact hs0.2.2.2.2.1) hxc E
  have hadj := blockcount.act_adjoint v (coevX b g W mu0 k0) (i + 1) i
    hsv hs0.2.2.1 (by rw [hvl]; exact hi)
    (by rw [hvl]; exact Nat.lt_of_succ_lt hi) (Nat.succ_ne_self i)
    hocc hxX.symm
  refine BPair.oneValue_trans hkey ?_
  refine BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.mul_congr (BPair.oneValue_refl E) ?_)
  refine BPair.oneValue_trans hadj (BPair.oneValue_of_eq ?_)
  rw [show (act i (i + 1) (coevX b g W mu0 k0)).coords
      = poly.neg (wactT dualTable
        (i :: ground.getAt ([] : List Nat)
          (coevIdx b W mu0) k0) g).coords from
    (poly.neg_neg (act i (i + 1) (coevX b g W mu0 k0)).coords).symm,
    show poly.neg (wactT dualTable
        (i :: ground.getAt ([] : List Nat)
          (coevIdx b W mu0) k0) g).coords
      = (wactT dualTable (i :: ground.getAt ([] : List Nat)
        (coevIdx b W mu0) k0) g).coords.map BPair.swap from rfl,
    elim.dotP_swapMap]

/-- A combination over the empty family is the width's unit
family. -/
private theorem combo_nil (n : Nat) : ∀ cs : List BPair,
    elim.combo n cs [] = List.replicate n BPair.unit
  | [] => rfl
  | _ :: _ => rfl

private theorem coevX_row (b : Shape) (g : HVec)
    (W : List (List Nat)) (mu : List Nat) (k : Nat)
    (hk : k < (coevIdx b W mu).length) :
    ground.getAt ([] : List BPair)
        ((List.range (coevIdx b W mu).length).map
          (fun j => (coevX b g W mu j).coords)) k
      = (coevX b g W mu k).coords := by
  rw [ground.getAt_map 0 ([] : List BPair)
      (fun j => (coevX b g W mu j).coords)
      (List.range (coevIdx b W mu).length) k
      (by rw [ground.length_range]; exact hk),
    ground.getAt_range (coevIdx b W mu).length k hk]

/-- The relation among a content group's partner words carries to
their dual words: the two families' pairings agree at the two tops'
self-pairings (`dualGram`), so the scaled member's combination read
transports across and the dual word's own pairing reads the scaled
combination's (`lem:dualread`(iii)'s solve-back at the group). -/
private theorem coevKer_relX (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (ws1 : List Nat) (hb1 : ∀ l ∈ ws1, l + 1 < a.length)
    (mu1 : List Nat)
    (hmu1 : (wact ws1 (exhibit b)).content = mu1)
    (hX1 : ∀ k, k < (coevIdx b W mu1).length →
      (coevX b g W mu1 k).content = (wactT dualTable ws1 g).content)
    (c1 : BPair) (gam : List BPair)
    (hrel : poly.oneValue
      (elim.vecScale c1 (wact ws1 (exhibit b)).coords)
      (elim.combo (places.monomialsAt mu1).length gam
        (groupAt (blockSpan b) mu1)))
    (v : HVec) :
    (elim.dotP v.coords (elim.combo
        (places.monomialsAt (wactT dualTable ws1 g).content).length
        gam ((List.range (coevIdx b W mu1).length).map
          (fun j => (coevX b g W mu1 j).coords)))).oneValue
      (c1 * elim.dotP v.coords (wactT dualTable ws1 g).coords) := by
  have hYeq : groupAt (blockSpan b) mu1
      = ((coevIdx b W mu1).map
        (fun ws => wact ws (exhibit b))).map HVec.coords := by
    show groupAt (blockSpan b) mu1
      = ((W.filter (fun ws => (wact ws (exhibit b)).content == mu1)).map
        (fun ws => wact ws (exhibit b))).map HVec.coords
    rw [hW, coevGrp_group b W mu1]
  have hYlen : (groupAt (blockSpan b) mu1).length
      = (coevIdx b W mu1).length := by
    rw [hYeq, ground.length_map, ground.length_map]
  have hXlen : ((List.range (coevIdx b W mu1).length).map
      (fun j => (coevX b g W mu1 j).coords)).length
      = (coevIdx b W mu1).length :=
    ground.length_mapRange _ _
  have hbk : ∀ k, k < (coevIdx b W mu1).length →
      ∀ l ∈ ground.getAt ([] : List Nat) (coevIdx b W mu1) k,
        l + 1 < a.length := by
    intro k hk l hl
    rw [← hba]
    exact hWb _ (ground.mem_filter_of _ W _
      (ground.mem_getAt ([] : List Nat) (coevIdx b W mu1) k hk)).1 l hl
  have hslot : ∀ k, k < (coevIdx b W mu1).length →
      (coevY b W mu1 k).content = mu1
        ∧ sized (coevX b g W mu1 k)
        ∧ sized (coevY b W mu1 k) := by
    intro k hk
    have hs := coevSlotAt a b m hba hjoin g hg hgc W hW hWb mu1 k hk
    exact ⟨hs.1, hs.2.2.1, (lowerspan.spanReads b).1 _ hs.2.1⟩
  have hsX1 : sized (wactT dualTable ws1 g) :=
    wactT_sized dualTable ws1 g ((lowerspan.spanReads a).1 g hg)
  have hsY1 : sized (wact ws1 (exhibit b)) :=
    blockcount.wact_sized ws1 (exhibit b) (blockcount.exhibit_sized b)
  have hrowsX : elim.rowsLen
      (places.monomialsAt (wactT dualTable ws1 g).content).length
      ((wactT dualTable ws1 g).coords
        :: (List.range (coevIdx b W mu1).length).map
          (fun j => (coevX b g W mu1 j).coords)) := by
    refine ⟨hsX1, elim.rowsLen_map _ _
      (List.range (coevIdx b W mu1).length) (fun j hj => ?_)⟩
    have hj' : j < (coevIdx b W mu1).length :=
      ground.ltOfMemRange hj
    rw [(hslot j hj').2.1, hX1 j hj']
  have hrowsY : elim.rowsLen (places.monomialsAt mu1).length
      ((wact ws1 (exhibit b)).coords :: groupAt (blockSpan b) mu1) := by
    refine ⟨by rw [hsY1, hmu1], ?_⟩
    exact blockcount.rowsLen_groupAt mu1 (blockSpan b)
      (lowerspan.spanReads b).1
  have hlen : ((wact ws1 (exhibit b)).coords
        :: groupAt (blockSpan b) mu1).length
      = ((wactT dualTable ws1 g).coords
        :: (List.range (coevIdx b W mu1).length).map
          (fun j => (coevX b g W mu1 j).coords)).length := by
    show (groupAt (blockSpan b) mu1).length + 1 = _ + 1
    rw [hYlen, hXlen]
  have hread : ∀ k, k < (coevIdx b W mu1).length + 1 →
      ∃ ws, (∀ l ∈ ws, l + 1 < a.length)
        ∧ ground.getAt ([] : List BPair)
            ((wactT dualTable ws1 g).coords
              :: (List.range (coevIdx b W mu1).length).map
                (fun j => (coevX b g W mu1 j).coords)) k
          = (wactT dualTable ws g).coords
        ∧ ground.getAt ([] : List BPair)
            ((wact ws1 (exhibit b)).coords
              :: groupAt (blockSpan b) mu1) k
          = (wact ws (exhibit b)).coords
        ∧ (wact ws (exhibit b)).content = mu1
        ∧ (wactT dualTable ws g).content
          = (wactT dualTable ws1 g).content := by
    intro k hk
    match k with
    | 0 => exact ⟨ws1, hb1, rfl, rfl, hmu1, rfl⟩
    | k + 1 =>
      have hkn : k < (coevIdx b W mu1).length :=
        Nat.lt_of_succ_lt_succ hk
      refine ⟨ground.getAt ([] : List Nat) (coevIdx b W mu1) k,
        hbk k hkn, coevX_row b g W mu1 k hkn, ?_,
        (hslot k hkn).1, hX1 k hkn⟩
      show ground.getAt ([] : List BPair)
        (groupAt (blockSpan b) mu1) k = _
      rw [hYeq]
      exact coevG_row b W mu1 k hkn
  have hXl1 : ((wactT dualTable ws1 g).coords
      :: (List.range (coevIdx b W mu1).length).map
        (fun j => (coevX b g W mu1 j).coords)).length
      = (coevIdx b W mu1).length + 1 := by
    show ((List.range (coevIdx b W mu1).length).map
      (fun j => (coevX b g W mu1 j).coords)).length + 1 = _
    rw [hXlen]
  have hE : ¬ (elim.dotP (exhibit b).coords
      (exhibit b).coords).oneValue BPair.unit :=
    fun h => blockcount.exhibit_off_unit b (elim.dotP_self_null _ h)
  have hnullY : poly.unitTail (elim.combo
      (places.monomialsAt mu1).length (c1.swap :: gam)
      ((wact ws1 (exhibit b)).coords
        :: groupAt (blockSpan b) mu1)) :=
    unitTail_swapAdd c1 (wact ws1 (exhibit b)).coords _ hrel
  have hnullX := dualGram_null
    (places.monomialsAt (wactT dualTable ws1 g).content).length
    (places.monomialsAt mu1).length
    (elim.dotP (exhibit b).coords (exhibit b).coords)
    (elim.dotP g.coords g.coords) hE _ _ hrowsX hrowsY hlen
    (by
      intro k hk l hl
      rw [hXl1] at hk hl
      match hread k hk, hread l hl with
      | ⟨wsk, hbk', hxk, hyk, hck, hdk⟩,
        ⟨wsl, hbl', hxl, hyl, hcl, hdl⟩ =>
        rw [hxk, hxl, hyk, hyl]
        exact dualPairRead a b m hba hjoin g hg hgc wsk wsl hbk' hbl'
          (hck.trans hcl.symm) (hdk.trans hdl.symm))
    (c1.swap :: gam) hnullY
  have hsplit := elim.dotP_null_tail_right v.coords _ hnullX
  have hlenA : (elim.vecScale c1.swap
        (wactT dualTable ws1 g).coords).length
      = (elim.combo
        (places.monomialsAt (wactT dualTable ws1 g).content).length
        gam ((List.range (coevIdx b W mu1).length).map
          (fun j => (coevX b g W mu1 j).coords))).length := by
    rw [elim.length_vecScale, hsX1,
      elim.length_combo _ gam _ hrowsX.2]
  have hAB := elim.dotP_vecAdd_right v.coords
    (elim.vecScale c1.swap (wactT dualTable ws1 g).coords)
    (elim.combo
      (places.monomialsAt (wactT dualTable ws1 g).content).length
      gam ((List.range (coevIdx b W mu1).length).map
        (fun j => (coevX b g W mu1 j).coords))) hlenA
  have hkey : (c1.swap
        * elim.dotP v.coords (wactT dualTable ws1 g).coords
      + elim.dotP v.coords (elim.combo
        (places.monomialsAt (wactT dualTable ws1 g).content).length
        gam ((List.range (coevIdx b W mu1).length).map
          (fun j => (coevX b g W mu1 j).coords)))).oneValue
      BPair.unit := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_symm
        (elim.dotP_vecScale_right v.coords _ c1.swap))
        (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_trans (BPair.oneValue_symm hAB) hsplit
  refine BPair.oneValue_trans (BPair.add_cancel
    (b := (c1.swap * elim.dotP v.coords
      (wactT dualTable ws1 g).coords).swap)
    (c := c1.swap * elim.dotP v.coords
      (wactT dualTable ws1 g).coords) ?_) ?_
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    exact BPair.oneValue_trans hkey
      (BPair.oneValue_symm (BPair.swap_add_null
        (BPair.oneValue_refl (c1.swap * elim.dotP v.coords
          (wactT dualTable ws1 g).coords))))
  · rw [BPair.swap_mul, BPair.swap_swap]
    exact BPair.oneValue_refl _

/-- The second slot's moved read at a live lowered partner: the
lowered partner word is the word extended by the raise letter, its
image settles in the extended content's group, and the group's
solve-back carries the collection to the extended dual word's own
pairing at the clearing scale. -/
private theorem coevKer_termR (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (i : Nat) (hi : i + 1 < a.length) (hm : 0 < m)
    (v : HVec) (hsv : sized v) (hvl : v.content.length = a.length)
    (ws0 : List Nat) (hws0 : ws0 ∈ W)
    (hjv : List.zipWith (fun p q => p + q) v.content
        (wact ws0 (exhibit b)).content
      = moveAt i (i + 1) (List.replicate a.length m))
    (hlive : ¬ poly.unitTail (wact (i :: ws0) (exhibit b)).coords)
    (E : BPair) :
    ∃ c1 : BPair, ¬ c1.oneValue BPair.unit ∧
      (c1 * (elim.dotP
          (coevVec (List.replicate a.length m) b g W).coords
          (tensorH v (act (i + 1) i
            (wact ws0 (exhibit b)))).coords * E)).oneValue
        (detAll (W.map (fun ws => wact ws (exhibit b)))
          * (E * (c1 * elim.dotP v.coords
              (wactT dualTable (i :: ws0) g).coords))) := by
  have hws0a : ∀ l ∈ ws0, l + 1 < a.length := fun l hl => by
    rw [← hba]
    exact hWb ws0 hws0 l hl
  have hb1 : ∀ l ∈ (i :: ws0), l + 1 < a.length := by
    intro l hl
    match hl with
    | List.Mem.head _ => exact hi
    | List.Mem.tail _ h => exact hws0a l h
  have hXlive : ¬ poly.unitTail
      (wactT dualTable (i :: ws0) g).coords := fun h =>
    hlive (dualWord_nullY a b m hba hjoin g hg hgc (i :: ws0) hb1 h)
  have hjoin1 := dualLive a b m hba hjoin g hg hgc (i :: ws0) hb1
    hlive hXlive
  have hwocc : 0 < ground.getAt 0
      (wact ws0 (exhibit b)).content i := by
    match Nat.eq_zero_or_pos (ground.getAt 0
        (wact ws0 (exhibit b)).content i) with
    | .inr h => exact h
    | .inl h =>
      exact absurd (tops.act_null (i + 1) i (wact ws0 (exhibit b)) h) hlive
  have hccocc : 0 < ground.getAt 0
      (List.replicate a.length m) (i + 1) := by
    rw [ground.getAt_replicate 0 m a.length (i + 1) hi]
    exact hm
  have hwmem : wact ws0 (exhibit b) ∈ blockSpan b := by
    rw [hW]
    exact ground.mem_map_to (fun ws => wact ws (exhibit b)) hws0
  have hwl : (wact ws0 (exhibit b)).content.length = a.length := by
    rw [blockcount.blockSpan_width b _ hwmem]
    exact hba
  have hsy : sized (wact (i :: ws0) (exhibit b)) :=
    blockcount.wact_sized (i :: ws0) (exhibit b)
      (blockcount.exhibit_sized b)
  have hjv1 : List.zipWith (fun p q => p + q) v.content
      (wact (i :: ws0) (exhibit b)).content
      = List.replicate a.length m := by
    show List.zipWith (fun p q => p + q) v.content
      (moveAt (i + 1) i (wact ws0 (exhibit b)).content) = _
    rw [blockcount.moveAt_zipWith_right (i + 1) i v.content
        (wact ws0 (exhibit b)).content hwocc, hjv,
      blockcount.moveAt_round_at (i + 1) i
        (List.replicate a.length m) hccocc]
  have hmu1l : (wact (i :: ws0) (exhibit b)).content.length
      = a.length := by
    show (moveAt (i + 1) i (wact ws0 (exhibit b)).content).length
      = a.length
    rw [length_moveAt]
    exact hwl
  have hX1l : (wactT dualTable (i :: ws0) g).content.length
      = a.length := widthG a g hg (i :: ws0)
  have hvX1 : v.content = (wactT dualTable (i :: ws0) g).content :=
    blockcount.zipWith_add_cancelL
      (wact (i :: ws0) (exhibit b)).content v.content _ a.length
      hmu1l hvl hX1l
      (((ground.zipWith_add_comm
          (wact (i :: ws0) (exhibit b)).content v.content).trans
        hjv1).trans hjoin1.symm)
  have hspan0 : elim.spanRel
      (places.monomialsAt (wact ws0 (exhibit b)).content).length
      (groupAt (blockSpan b) (wact ws0 (exhibit b)).content)
      (wact ws0 (exhibit b)).coords :=
    blockcount.spanRel_groupAt_mem (blockSpan b) _ hwmem
      (lowerspan.spanReads b).1
  have hspan1 : elim.spanRel
      (places.monomialsAt
        (wact (i :: ws0) (exhibit b)).content).length
      (groupAt (blockSpan b) (wact (i :: ws0) (exhibit b)).content)
      (wact (i :: ws0) (exhibit b)).coords :=
    lowerspan.act_span_def b (i + 1) i (by rw [hba]; exact hi)
      (by rw [hba]; exact Nat.lt_of_succ_lt hi) (Nat.succ_ne_self i)
      (wact ws0 (exhibit b)).content (wact ws0 (exhibit b)).coords
      (blockcount.wact_sized ws0 (exhibit b)
        (blockcount.exhibit_sized b)) hspan0
  have hYeq : groupAt (blockSpan b)
        (wact (i :: ws0) (exhibit b)).content
      = ((coevIdx b W (wact (i :: ws0) (exhibit b)).content).map
        (fun ws => wact ws (exhibit b))).map HVec.coords := by
    show groupAt (blockSpan b) _
      = ((W.filter (fun ws => (wact ws (exhibit b)).content
          == (wact (i :: ws0) (exhibit b)).content)).map
        (fun ws => wact ws (exhibit b))).map HVec.coords
    rw [hW, coevGrp_group b W (wact (i :: ws0) (exhibit b)).content]
  match elim.span_elim hspan1 with
  | ⟨c1, gam, hc1, hgl0, hrel⟩ =>
    have hgl : gam.length
        = (coevIdx b W (wact (i :: ws0) (exhibit b)).content).length := by
      rw [hgl0, hYeq, ground.length_map, ground.length_map]
    have hn : 0 < (coevIdx b W
        (wact (i :: ws0) (exhibit b)).content).length := by
      match hc : coevIdx b W (wact (i :: ws0) (exhibit b)).content with
      | _ :: _ => exact Nat.succ_pos _
      | [] =>
        refine absurd (elim.unitTail_unscale c1 hc1 _
          (poly.oneValue_unitTail hrel ?_)) hlive
        rw [hYeq, hc]
        show poly.unitTail (elim.combo
          (places.monomialsAt
            (wact (i :: ws0) (exhibit b)).content).length gam [])
        rw [combo_nil]
        exact poly.unitTail_replicate _
    have hs0 := coevSlotAt a b m hba hjoin g hg hgc W hW hWb
      (wact (i :: ws0) (exhibit b)).content 0 hn
    have hmu1mem : (wact (i :: ws0) (exhibit b)).content
        ∈ (W.map (fun ws => wact ws (exhibit b))).map HVec.content := by
      have h1 : coevY b W (wact (i :: ws0) (exhibit b)).content 0
          ∈ W.map (fun ws => wact ws (exhibit b)) := by
        rw [← hW]
        exact hs0.2.1
      have h2 := ground.mem_map_to HVec.content h1
      rw [hs0.1] at h2
      exact h2
    have hX1 : ∀ k, k < (coevIdx b W
        (wact (i :: ws0) (exhibit b)).content).length →
        (coevX b g W (wact (i :: ws0) (exhibit b)).content k).content
          = (wactT dualTable (i :: ws0) g).content := by
      intro k hk
      have hsk := coevSlotAt a b m hba hjoin g hg hgc W hW hWb
        (wact (i :: ws0) (exhibit b)).content k hk
      exact blockcount.zipWith_add_cancelL
        (wact (i :: ws0) (exhibit b)).content _ _ a.length
        hmu1l hsk.2.2.2.1 hX1l (hsk.2.2.2.2.2.1.trans hjoin1.symm)
    have hrowsX : elim.rowsLen
        (places.monomialsAt
          (wactT dualTable (i :: ws0) g).content).length
        ((List.range (coevIdx b W
            (wact (i :: ws0) (exhibit b)).content).length).map
          (fun j => (coevX b g W
            (wact (i :: ws0) (exhibit b)).content j).coords)) := by
      refine elim.rowsLen_map _ _ _ (fun j hj => ?_)
      have hj' : j < (coevIdx b W
          (wact (i :: ws0) (exhibit b)).content).length :=
        ground.ltOfMemRange hj
      have hsk := coevSlotAt a b m hba hjoin g hg hgc W hW hWb
        (wact (i :: ws0) (exhibit b)).content j hj'
      rw [hsk.2.2.1, hX1 j hj']
    have hcom : ∀ k, k < (coevIdx b W
        (wact (i :: ws0) (exhibit b)).content).length →
        (c1 * elim.dotP (wact (i :: ws0) (exhibit b)).coords
            (coevY b W
              (wact (i :: ws0) (exhibit b)).content k).coords).oneValue
          (elim.dotP gam (ground.getAt []
            (coevG b W
              (wact (i :: ws0) (exhibit b)).content) k)) := by
      intro k hk
      have hrow : ground.getAt ([] : List BPair)
          (coevG b W (wact (i :: ws0) (exhibit b)).content) k
          = (groupAt (blockSpan b)
              (wact (i :: ws0) (exhibit b)).content).map
            (fun c => elim.dotP (coevY b W
              (wact (i :: ws0) (exhibit b)).content k).coords c) := by
        rw [hYeq]
        show ground.getAt ([] : List BPair) (elim.gramM
          (((coevIdx b W (wact (i :: ws0) (exhibit b)).content).map
            (fun ws => wact ws (exhibit b))).map HVec.coords)) k = _
        rw [elim.gramM_row _ k
            (by rw [ground.length_map, ground.length_map]; exact hk),
          coevG_row b W (wact (i :: ws0) (exhibit b)).content k hk]
      rw [hrow]
      refine BPair.oneValue_trans ?_
        (elim.dotP_combo gam (groupAt (blockSpan b)
            (wact (i :: ws0) (exhibit b)).content)
          (coevY b W (wact (i :: ws0) (exhibit b)).content k).coords
          (places.monomialsAt
            (wact (i :: ws0) (exhibit b)).content).length
          (blockcount.rowsLen_groupAt _ (blockSpan b)
            (lowerspan.spanReads b).1))
      rw [elim.dotP_comm (wact (i :: ws0) (exhibit b)).coords
        (coevY b W (wact (i :: ws0) (exhibit b)).content k).coords]
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (elim.dotP_vecScale_right
          (coevY b W (wact (i :: ws0) (exhibit b)).content k).coords
          _ c1)) ?_
      exact elim.dotP_oneValue_right _ _ _ hrel
    have hgam := coevPair_gam a b m hba hjoin g hg hgc W hW hWb
      (wact (i :: ws0) (exhibit b)).content hmu1mem hmu1l
      v (wact (i :: ws0) (exhibit b)) hsv hsy hvl
      (by rw [hvX1]
          exact dualWord_deg a g hg (i :: ws0) hb1 hXlive)
      rfl hjv1 c1 gam hgl hcom E
    have hrelX := coevKer_relX a b m hba hjoin g hg hgc W hW hWb
      (i :: ws0) hb1 (wact (i :: ws0) (exhibit b)).content rfl hX1
      c1 gam hrel v
    refine ⟨c1, hc1, BPair.oneValue_trans hgam ?_⟩
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (congrArg (elim.dotP gam)
        (ground.map_map
          (fun j => elim.dotP v.coords (coevX b g W
            (wact (i :: ws0) (exhibit b)).content j).coords)
          (fun x => E * x)
          (List.range (coevIdx b W
            (wact (i :: ws0) (exhibit b)).content).length)).symm)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_vecScale_right gam _ E) ?_
    refine BPair.mul_congr (BPair.oneValue_refl E) ?_
    refine BPair.oneValue_trans ?_ hrelX
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (elim.dotP_combo gam _ v.coords _ hrowsX) ?_
    rw [ground.map_map
      (fun j => (coevX b g W
        (wact (i :: ws0) (exhibit b)).content j).coords)
      (fun row => elim.dotP v.coords row)
      (List.range (coevIdx b W
        (wact (i :: ws0) (exhibit b)).content).length)]
    exact BPair.oneValue_refl _

/-- A factor at the sum's unit kills the scaled product. -/
private theorem coevKer_kill (D E T : BPair)
    (hT : T.oneValue BPair.unit) :
    (D * (E * T)).oneValue BPair.unit :=
  BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl D)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl E) hT)
        (BPair.mul_unit E)))
    (BPair.mul_unit D)

/-- The two slots' moved reads join at partners: the first slot's
read enters the sum swapped against the second's, so the two
withdraw at the sum's unit. -/
private theorem coevKer_join (D E c1 N1 N2 T : BPair)
    (h1 : (N1 * E).oneValue (D * (E * T.swap)))
    (h2 : (c1 * (N2 * E)).oneValue (D * (E * (c1 * T)))) :
    (c1 * ((N1 + N2) * E)).oneValue BPair.unit := by
  have hd : (N1 + N2) * E = N1 * E + N2 * E := by
    rw [BPair.mul_comm (N1 + N2) E, BPair.left_distrib E N1 N2,
      BPair.mul_comm E N1, BPair.mul_comm E N2]
  rw [hd, BPair.left_distrib c1 (N1 * E) (N2 * E)]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl c1) h1) h2) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_of_eq (show c1 * (D * (E * T.swap))
        = D * (E * (c1 * T.swap)) from by
          rw [BPair.mul_left_comm c1 D (E * T.swap),
            BPair.mul_left_comm c1 E T.swap]))
      (BPair.oneValue_refl (D * (E * (c1 * T))))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (show D * (E * (c1 * T.swap))
        + D * (E * (c1 * T))
      = D * (E * (c1 * T.swap + c1 * T)) from by
        rw [BPair.left_distrib E (c1 * T.swap) (c1 * T),
          BPair.left_distrib D (E * (c1 * T.swap))
            (E * (c1 * T))])) ?_
  refine coevKer_kill D E _ ?_
  rw [BPair.mul_swap c1 T]
  exact BPair.swap_add_null (BPair.oneValue_refl (c1 * T))

/-- The coevaluation's raised image pairs every pair at the sum's
unit: the moved pairing is the walk's read at one further crossing
(`blockcount.act_adjoint`), the lowered test splits over the tensor
(`blockcount.act_tensorH`), and the two slots' moved reads join at
partners across the transpose identity at the exchanged letters. -/
private theorem coevKer_pair (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (i : Nat) (hi : i + 1 < a.length) (hm : 0 < m)
    (v w : HVec) (hv : v ∈ blockSpan a) (hw : w ∈ blockSpan b)
    (hvw : List.zipWith (fun p q => p + q) v.content w.content
      = moveAt i (i + 1) (List.replicate a.length m)) :
    (elim.dotP (act i (i + 1)
        (coevVec (List.replicate a.length m) b g W)).coords
      (tensorH v w).coords).oneValue BPair.unit := by
  have hccl : (List.replicate a.length m).length = a.length :=
    ground.length_replicate m a.length
  have hccocc : 0 < ground.getAt 0
      (List.replicate a.length m) (i + 1) := by
    rw [ground.getAt_replicate 0 m a.length (i + 1) hi]
    exact hm
  have hib : i < (List.replicate a.length m).length := by
    rw [hccl]
    exact Nat.lt_of_succ_lt hi
  have hsv : sized v := (lowerspan.spanReads a).1 v hv
  have hsw : sized w := (lowerspan.spanReads b).1 w hw
  have hvl : v.content.length = a.length :=
    blockcount.blockSpan_width a v hv
  have hwl : w.content.length = a.length := by
    rw [blockcount.blockSpan_width b w hw]
    exact hba
  have hsPhi := coevVec_sized a b m hba hjoin g hg hgc W hW hWb
  have hEoff : ¬ (elim.dotP (exhibit b).coords
      (exhibit b).coords).oneValue BPair.unit :=
    fun h => blockcount.exhibit_off_unit b (elim.dotP_self_null _ h)
  have hadj := blockcount.act_adjoint
    (coevVec (List.replicate a.length m) b g W) (tensorH v w) i (i + 1)
    hsPhi (blockcount.tensorH_sized v w)
    (show i < (List.replicate a.length m).length from hib)
    (show i + 1 < (List.replicate a.length m).length from by
      rw [hccl]; exact hi)
    (fun he => Nat.succ_ne_self i he.symm) hccocc hvw
  have hT := blockcount.act_tensorH (i + 1) i v w hsv hsw
    (hvl.trans hwl.symm) (by rw [hvl]; exact hi)
    (by rw [hvl]; exact Nat.lt_of_succ_lt hi) (Nat.succ_ne_self i)
  have hsplit0 := elim.dotP_oneValue_right
    (coevVec (List.replicate a.length m) b g W).coords _ _ hT
  refine BPair.oneValue_trans hadj
    (BPair.oneValue_trans hsplit0 ?_)
  have hwmap : w ∈ W.map (fun ws => wact ws (exhibit b)) := by
    rw [← hW]
    exact hw
  match ground.mem_map_of (fun ws => wact ws (exhibit b)) W w hwmap with
  | ⟨ws0, hws0, hws0e⟩ =>
    subst hws0e
    have hws0f : ws0 ∈ coevIdx b W (wact ws0 (exhibit b)).content :=
      ground.mem_filter_to _ hws0
        (ground.listEqBeq (wact ws0 (exhibit b)).content)
    match ground.getAt_of_mem ([] : List Nat) hws0f with
    | ⟨k0, hk0, hk0e⟩ =>
      have hY0 : coevY b W (wact ws0 (exhibit b)).content k0
          = wact ws0 (exhibit b) := by
        show wact (ground.getAt ([] : List Nat)
          (coevIdx b W (wact ws0 (exhibit b)).content) k0)
          (exhibit b) = _
        rw [hk0e]
      by_cases hlive : poly.unitTail (wact (i :: ws0) (exhibit b)).coords
      · have hBnull : poly.unitTail
            (tensorH v (act (i + 1) i (wact ws0 (exhibit b)))).coords :=
          (blockcount.tensorH_unitTail v
            (act (i + 1) i (wact ws0 (exhibit b))) hsv
            (blockcount.act_sized (i + 1) i (wact ws0 (exhibit b)))
            (by
              show v.content.length
                = (moveAt (i + 1) i
                  (wact ws0 (exhibit b)).content).length
              rw [length_moveAt, hvl, hwl])).mpr (Or.inr hlive)
        have hTnull : (elim.dotP v.coords
            (wactT dualTable (i :: ws0) g).coords).oneValue
            BPair.unit :=
          elim.dotP_null_tail_right _ _
            (dualWord_nullX a b m hba hjoin g hg hgc (i :: ws0)
              (by
                intro l hl
                match hl with
                | List.Mem.head _ => exact hi
                | List.Mem.tail _ h =>
                  rw [← hba]
                  exact hWb ws0 hws0 l h) hlive)
        by_cases hvocc : 0 < ground.getAt 0 v.content i
        · have hAc : (tensorH (act (i + 1) i v)
              (wact ws0 (exhibit b))).content
              = List.replicate a.length m := by
            show List.zipWith (fun x y => x + y)
              (moveAt (i + 1) i v.content)
              (wact ws0 (exhibit b)).content = _
            rw [blockcount.moveAt_zipWith_left (i + 1) i v.content
                (wact ws0 (exhibit b)).content hvocc, hvw,
              blockcount.moveAt_round_at (i + 1) i
                (List.replicate a.length m) hccocc]
          have hle : (tensorH (act (i + 1) i v)
                (wact ws0 (exhibit b))).coords.length
              ≤ (tensorH v (act (i + 1) i
                (wact ws0 (exhibit b)))).coords.length := by
            rw [blockcount.tensorH_sized, blockcount.tensorH_sized,
              hAc]
            by_cases hwocc : 0 < ground.getAt 0
                (wact ws0 (exhibit b)).content i
            · rw [show (tensorH v (act (i + 1) i
                    (wact ws0 (exhibit b)))).content
                  = List.replicate a.length m from by
                show List.zipWith (fun x y => x + y) v.content
                  (moveAt (i + 1) i
                    (wact ws0 (exhibit b)).content) = _
                rw [blockcount.moveAt_zipWith_right (i + 1) i
                    v.content (wact ws0 (exhibit b)).content hwocc,
                  hvw, blockcount.moveAt_round_at (i + 1) i
                    (List.replicate a.length m) hccocc]]
              exact Nat.le_refl _
            · rw [show (tensorH v (act (i + 1) i
                    (wact ws0 (exhibit b)))).content
                  = ground.bumpAt i (List.replicate a.length m) from
                (moveAt_vacR (i + 1) i v.content
                  (wact ws0 (exhibit b)).content
                  (moveAt i (i + 1) (List.replicate a.length m)) hvw
                  (Nat.eq_zero_of_not_pos hwocc)).trans
                  (bumpAt_moveAt i (i + 1) (List.replicate a.length m) hccocc)]
              exact places.length_monomialsAt_le_bumpAt i
                (List.replicate a.length m) hib
          have hL := coevKer_termL a b m hba hjoin g hg hgc W hW hWb
            i hi hm v hsv hvl (wact ws0 (exhibit b)).content k0 hk0
            hvw hvocc (elim.dotP (exhibit b).coords (exhibit b).coords)
          rw [hY0, hk0e] at hL
          refine ground.mul_cancel_unit hEoff
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_)
          refine BPair.oneValue_trans
            (BPair.mul_congr (elim.dotP_oneValue_right _ _ _
              (elim.vecAdd_null_right_le _ _ hle hBnull)) (BPair.oneValue_refl _)) ?_
          refine BPair.oneValue_trans hL ?_
          exact coevKer_kill _ _ _ (ground.swap_congr hTnull)
        · have hAnull : poly.unitTail
              (tensorH (act (i + 1) i v)
                (wact ws0 (exhibit b))).coords :=
            (blockcount.tensorH_unitTail (act (i + 1) i v)
              (wact ws0 (exhibit b))
              (blockcount.act_sized (i + 1) i v) hsw
              (by
                show (moveAt (i + 1) i v.content).length
                  = (wact ws0 (exhibit b)).content.length
                rw [length_moveAt, hvl, hwl])).mpr
              (Or.inl (tops.act_null (i + 1) i v
                (Nat.eq_zero_of_not_pos hvocc)))
          exact elim.dotP_null_tail_right _ _
            (elim.unitTail_vecAdd_of hAnull hBnull)
      · have hwocc : 0 < ground.getAt 0
            (wact ws0 (exhibit b)).content i := by
          match Nat.eq_zero_or_pos (ground.getAt 0
              (wact ws0 (exhibit b)).content i) with
          | .inr h => exact h
          | .inl h =>
            exact absurd
              (tops.act_null (i + 1) i (wact ws0 (exhibit b)) h) hlive
        have hBc : (tensorH v (act (i + 1) i
            (wact ws0 (exhibit b)))).content
            = List.replicate a.length m := by
          show List.zipWith (fun x y => x + y) v.content
            (moveAt (i + 1) i (wact ws0 (exhibit b)).content) = _
          rw [blockcount.moveAt_zipWith_right (i + 1) i v.content
              (wact ws0 (exhibit b)).content hwocc, hvw,
            blockcount.moveAt_round_at (i + 1) i
              (List.replicate a.length m) hccocc]
        match coevKer_termR a b m hba hjoin g hg hgc W hW hWb i hi hm
            v hsv hvl ws0 hws0 hvw hlive
            (elim.dotP (exhibit b).coords (exhibit b).coords) with
        | ⟨c1, hc1, hR⟩ =>
          by_cases hvocc : 0 < ground.getAt 0 v.content i
          · have hAc : (tensorH (act (i + 1) i v)
                (wact ws0 (exhibit b))).content
                = List.replicate a.length m := by
              show List.zipWith (fun x y => x + y)
                (moveAt (i + 1) i v.content)
                (wact ws0 (exhibit b)).content = _
              rw [blockcount.moveAt_zipWith_left (i + 1) i v.content
                  (wact ws0 (exhibit b)).content hvocc, hvw,
                blockcount.moveAt_round_at (i + 1) i
                  (List.replicate a.length m) hccocc]
            have hlenAB : (tensorH (act (i + 1) i v)
                  (wact ws0 (exhibit b))).coords.length
                = (tensorH v (act (i + 1) i
                  (wact ws0 (exhibit b)))).coords.length := by
              rw [blockcount.tensorH_sized, blockcount.tensorH_sized,
                hAc, hBc]
            have hL := coevKer_termL a b m hba hjoin g hg hgc W hW hWb
              i hi hm v hsv hvl (wact ws0 (exhibit b)).content k0 hk0
              hvw hvocc
              (elim.dotP (exhibit b).coords (exhibit b).coords)
            rw [hY0, hk0e] at hL
            refine ground.mul_cancel_unit hEoff
              (ground.mul_cancel_unit hc1
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl c1)
                    (BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_))
            refine BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl c1)
                (BPair.mul_congr (elim.dotP_vecAdd_right _ _ _ hlenAB)
                  (BPair.oneValue_refl _))) ?_
            exact coevKer_join _ _ c1 _ _ _ hL hR
          · have hAnull : poly.unitTail
                (tensorH (act (i + 1) i v)
                  (wact ws0 (exhibit b))).coords :=
              (blockcount.tensorH_unitTail (act (i + 1) i v)
                (wact ws0 (exhibit b))
                (blockcount.act_sized (i + 1) i v) hsw
                (by
                  show (moveAt (i + 1) i v.content).length
                    = (wact ws0 (exhibit b)).content.length
                  rw [length_moveAt, hvl, hwl])).mpr
                (Or.inl (tops.act_null (i + 1) i v
                  (Nat.eq_zero_of_not_pos hvocc)))
            have hle : (tensorH v (act (i + 1) i
                  (wact ws0 (exhibit b)))).coords.length
                ≤ (tensorH (act (i + 1) i v)
                  (wact ws0 (exhibit b))).coords.length := by
              rw [blockcount.tensorH_sized, blockcount.tensorH_sized,
                hBc, show (tensorH (act (i + 1) i v)
                    (wact ws0 (exhibit b))).content
                  = ground.bumpAt i (List.replicate a.length m) from
                (moveAt_vacL (i + 1) i v.content
                  (wact ws0 (exhibit b)).content
                  (moveAt i (i + 1) (List.replicate a.length m)) hvw
                  (Nat.eq_zero_of_not_pos hvocc)).trans
                  (bumpAt_moveAt i (i + 1) (List.replicate a.length m) hccocc)]
              exact places.length_monomialsAt_le_bumpAt i
                (List.replicate a.length m) hib
            have hTnull := coevKer_vacT a b m hba hjoin g hg hgc W hW
              hWb i hi hm v hsv hvl
              (wact ws0 (exhibit b)).content k0 hk0 hvw
              (Nat.eq_zero_of_not_pos hvocc)
            rw [hk0e] at hTnull
            refine ground.mul_cancel_unit hEoff
              (ground.mul_cancel_unit hc1
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl c1)
                    (BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_))
            refine BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl c1)
                (BPair.mul_congr (elim.dotP_oneValue_right _ _ _
                  (elim.vecAdd_null_left_le _ _ hle hAnull))
                  (BPair.oneValue_refl _))) ?_
            refine BPair.oneValue_trans hR ?_
            exact coevKer_kill _ _ _
              (BPair.oneValue_trans
                (BPair.mul_congr (BPair.oneValue_refl c1) hTnull)
                (BPair.mul_unit c1))

/-- A fused row's raised image sits in the fused pool's own group
at the moved content: the raise splits over the tensor
(`blockcount.act_tensorH`) and each occupied arm's moved factor
stays in its block's content span (`lowerspan.act_span_def`), so
the collecting read carries the arm into the moved content's group
(`blockcount.tensor_span`); a vacant arm's image is null and no
longer than its partner, so it drops from the sum. -/
private theorem coevKer_rowSpan (a b : Shape) (i : Nat)
    (hba : b.length = a.length) (hi : i + 1 < a.length)
    (cc : List Nat) (hccocc : 0 < ground.getAt 0 cc (i + 1))
    (u : HVec) (hu : u ∈ fusedAt (blockSpan a) (blockSpan b))
    (huc : u.content = cc) :
    elim.spanRel (places.monomialsAt (moveAt i (i + 1) cc)).length
      (groupAt (fusedAt (blockSpan a) (blockSpan b))
        (moveAt i (i + 1) cc))
      (elim.matVec
        (units.matUnitAt (moveAt i (i + 1) cc) cc i (i + 1))
        u.coords) := by
  subst huc
  match ground.mem_flatMap_of (fun v => (blockSpan b).map (tensorH v))
      (blockSpan a) u hu with
  | ⟨p, hp, hpu⟩ =>
    match ground.mem_map_of (tensorH p) (blockSpan b) u hpu with
    | ⟨q, hq, hqu⟩ =>
      subst hqu
      have hsp : sized p := (lowerspan.spanReads a).1 p hp
      have hsq : sized q := (lowerspan.spanReads b).1 q hq
      have hpl : p.content.length = a.length :=
        blockcount.blockSpan_width a p hp
      have hql : q.content.length = a.length :=
        (blockcount.blockSpan_width b q hq).trans hba
      have hia : i < a.length := Nat.lt_of_succ_lt hi
      have hij : ¬ i = i + 1 := fun he => Nat.succ_ne_self i he.symm
      have hgetT : ground.getAt 0 (tensorH p q).content (i + 1)
          = ground.getAt 0 p.content (i + 1)
            + ground.getAt 0 q.content (i + 1) :=
        ground.getAt_zipWith 0 0 0 (fun x y => x + y) p.content
          q.content (i + 1) (by rw [hpl]; exact hi)
          (by rw [hql]; exact hi)
      have hTsp := blockcount.act_tensorH i (i + 1) p q hsp hsq
        (hpl.trans hql.symm) (by rw [hpl]; exact hia)
        (by rw [hpl]; exact hi) hij
      have hspp : elim.spanRel
          (places.monomialsAt (moveAt i (i + 1) p.content)).length
          (groupAt (blockSpan a) (moveAt i (i + 1) p.content))
          (act i (i + 1) p).coords :=
        lowerspan.act_span_def a i (i + 1) hia hi hij
          p.content p.coords hsp
          (blockcount.spanRel_groupAt_mem (blockSpan a) p hp
            (lowerspan.spanReads a).1)
      have hspq : elim.spanRel
          (places.monomialsAt (moveAt i (i + 1) q.content)).length
          (groupAt (blockSpan b) (moveAt i (i + 1) q.content))
          (act i (i + 1) q).coords :=
        lowerspan.act_span_def b i (i + 1) (by rw [hba]; exact hia)
          (by rw [hba]; exact hi) hij q.content q.coords hsq
          (blockcount.spanRel_groupAt_mem (blockSpan b) q hq
            (lowerspan.spanReads b).1)
      have hqmem : elim.spanRel
          (places.monomialsAt q.content).length
          (groupAt (blockSpan b) q.content) q.coords :=
        blockcount.spanRel_groupAt_mem (blockSpan b) q hq
          (lowerspan.spanReads b).1
      have hpmem : elim.spanRel
          (places.monomialsAt p.content).length
          (groupAt (blockSpan a) p.content) p.coords :=
        blockcount.spanRel_groupAt_mem (blockSpan a) p hp
          (lowerspan.spanReads a).1
      have hAlen : (moveAt i (i + 1) p.content).length = a.length := by
        rw [length_moveAt]
        exact hpl
      have hBlen : (moveAt i (i + 1) q.content).length = a.length := by
        rw [length_moveAt]
        exact hql
      have hactl : (act i (i + 1) (tensorH p q)).coords.length
          = (places.monomialsAt
            (moveAt i (i + 1) (tensorH p q).content)).length :=
        blockcount.act_sized i (i + 1) (tensorH p q)
      show elim.spanRel
        (places.monomialsAt
          (moveAt i (i + 1) (tensorH p q).content)).length
        (groupAt (fusedAt (blockSpan a) (blockSpan b))
          (moveAt i (i + 1) (tensorH p q).content))
        (act i (i + 1) (tensorH p q)).coords
      by_cases hpo : 0 < ground.getAt 0 p.content (i + 1)
      · have hAc : List.zipWith (fun x y => x + y)
            (act i (i + 1) p).content q.content
            = moveAt i (i + 1) (tensorH p q).content := by
          show List.zipWith (fun x y => x + y)
            (moveAt i (i + 1) p.content) q.content = _
          rw [blockcount.moveAt_zipWith_left i (i + 1) p.content
            q.content hpo]
          rfl
        have hAspan : elim.spanRel
            (places.monomialsAt
              (moveAt i (i + 1) (tensorH p q).content)).length
            (groupAt (fusedAt (blockSpan a) (blockSpan b))
              (moveAt i (i + 1) (tensorH p q).content))
            (tensorH (act i (i + 1) p) q).coords := by
          have hz := blockcount.tensor_span (blockSpan a) (blockSpan b)
            a.length (lowerspan.spanReads a).1 (lowerspan.spanReads b).1
            (blockcount.blockSpan_width a)
            (fun w hw => (blockcount.blockSpan_width b w hw).trans hba)
            (moveAt i (i + 1) p.content) q.content hAlen hql
            (act i (i + 1) p).coords q.coords hspp hqmem
          rw [show List.zipWith (fun x y => x + y)
              (moveAt i (i + 1) p.content) q.content
            = moveAt i (i + 1) (tensorH p q).content from hAc] at hz
          exact hz
        by_cases hqo : 0 < ground.getAt 0 q.content (i + 1)
        · have hBc : List.zipWith (fun x y => x + y) p.content
              (act i (i + 1) q).content
              = moveAt i (i + 1) (tensorH p q).content := by
            show List.zipWith (fun x y => x + y) p.content
              (moveAt i (i + 1) q.content) = _
            rw [blockcount.moveAt_zipWith_right i (i + 1) p.content
              q.content hqo]
            rfl
          have hBspan : elim.spanRel
              (places.monomialsAt
                (moveAt i (i + 1) (tensorH p q).content)).length
              (groupAt (fusedAt (blockSpan a) (blockSpan b))
                (moveAt i (i + 1) (tensorH p q).content))
              (tensorH p (act i (i + 1) q)).coords := by
            have hz := blockcount.tensor_span (blockSpan a)
              (blockSpan b) a.length (lowerspan.spanReads a).1
              (lowerspan.spanReads b).1
              (blockcount.blockSpan_width a)
              (fun w hw => (blockcount.blockSpan_width b w hw).trans hba)
              p.content (moveAt i (i + 1) q.content) hpl hBlen
              p.coords (act i (i + 1) q).coords hpmem hspq
            rw [show List.zipWith (fun x y => x + y) p.content
                (moveAt i (i + 1) q.content)
              = moveAt i (i + 1) (tensorH p q).content from hBc] at hz
            exact hz
          refine elim.spanRel_congr _ _ _ _
            (poly.oneValue_symm hTsp) ?_ hactl
          exact elim.spanRel_add _ _ _ _
            (blockcount.rowsLen_groupAt _ _
              (blockcount.fusedAt_sized _ _))
            (by
              rw [blockcount.tensorH_sized]
              show (places.monomialsAt (List.zipWith (fun x y => x + y)
                  (act i (i + 1) p).content q.content)).length = _
              rw [hAc])
            (by
              rw [blockcount.tensorH_sized]
              show (places.monomialsAt (List.zipWith (fun x y => x + y)
                  p.content (act i (i + 1) q).content)).length = _
              rw [hBc])
            hAspan hBspan
        · have hBnull : poly.unitTail
              (tensorH p (act i (i + 1) q)).coords :=
            (blockcount.tensorH_unitTail p (act i (i + 1) q) hsp
              (blockcount.act_sized i (i + 1) q)
              (by
                show p.content.length
                  = (moveAt i (i + 1) q.content).length
                rw [hBlen, hpl])).mpr
              (Or.inr (tops.act_null i (i + 1) q
                (Nat.eq_zero_of_not_pos hqo)))
          have hle : (tensorH (act i (i + 1) p) q).coords.length
              ≤ (tensorH p (act i (i + 1) q)).coords.length := by
            rw [blockcount.tensorH_sized, blockcount.tensorH_sized]
            show (places.monomialsAt (List.zipWith (fun x y => x + y)
                (act i (i + 1) p).content q.content)).length
              ≤ (places.monomialsAt (List.zipWith (fun x y => x + y)
                p.content (act i (i + 1) q).content)).length
            rw [hAc, show List.zipWith (fun x y => x + y) p.content
                  (act i (i + 1) q).content
                = ground.bumpAt i (tensorH p q).content from
              moveAt_vacR i (i + 1) p.content q.content
                (tensorH p q).content rfl
                (Nat.eq_zero_of_not_pos hqo)]
            rw [show ground.bumpAt i (tensorH p q).content
                = ground.bumpAt (i + 1)
                  (moveAt i (i + 1) (tensorH p q).content) from
              (bumpAt_moveAt i (i + 1) (tensorH p q).content hccocc).symm]
            refine places.length_monomialsAt_le_bumpAt (i + 1) _ ?_
            rw [length_moveAt, show (tensorH p q).content.length
                = a.length from by
              rw [show (tensorH p q).content
                = List.zipWith (fun x y => x + y) p.content q.content
                from rfl]
              exact ground.length_zipWith (fun x y => x + y) p.content
                q.content a.length hpl hql]
            exact hi
          refine elim.spanRel_congr _ _ _ _
            (poly.oneValue_symm (poly.oneValue_trans hTsp
              (elim.vecAdd_null_right_le _ _ hle hBnull))) hAspan hactl
      · have hAnull : poly.unitTail
            (tensorH (act i (i + 1) p) q).coords :=
          (blockcount.tensorH_unitTail (act i (i + 1) p) q
            (blockcount.act_sized i (i + 1) p) hsq
            (by
              show (moveAt i (i + 1) p.content).length
                = q.content.length
              rw [hAlen, hql])).mpr
            (Or.inl (tops.act_null i (i + 1) p
              (Nat.eq_zero_of_not_pos hpo)))
        have hqo : 0 < ground.getAt 0 q.content (i + 1) := by
          rw [hgetT, Nat.eq_zero_of_not_pos hpo, Nat.zero_add] at hccocc
          exact hccocc
        have hBc : List.zipWith (fun x y => x + y) p.content
            (act i (i + 1) q).content
            = moveAt i (i + 1) (tensorH p q).content := by
          show List.zipWith (fun x y => x + y) p.content
            (moveAt i (i + 1) q.content) = _
          rw [blockcount.moveAt_zipWith_right i (i + 1) p.content
            q.content hqo]
          rfl
        have hBspan : elim.spanRel
            (places.monomialsAt
              (moveAt i (i + 1) (tensorH p q).content)).length
            (groupAt (fusedAt (blockSpan a) (blockSpan b))
              (moveAt i (i + 1) (tensorH p q).content))
            (tensorH p (act i (i + 1) q)).coords := by
          have hz := blockcount.tensor_span (blockSpan a)
            (blockSpan b) a.length (lowerspan.spanReads a).1
            (lowerspan.spanReads b).1
            (blockcount.blockSpan_width a)
            (fun w hw => (blockcount.blockSpan_width b w hw).trans hba)
            p.content (moveAt i (i + 1) q.content) hpl hBlen
            p.coords (act i (i + 1) q).coords hpmem hspq
          rw [show List.zipWith (fun x y => x + y) p.content
              (moveAt i (i + 1) q.content)
            = moveAt i (i + 1) (tensorH p q).content from hBc] at hz
          exact hz
        have hle : (tensorH p (act i (i + 1) q)).coords.length
            ≤ (tensorH (act i (i + 1) p) q).coords.length := by
          rw [blockcount.tensorH_sized, blockcount.tensorH_sized]
          show (places.monomialsAt (List.zipWith (fun x y => x + y)
              p.content (act i (i + 1) q).content)).length
            ≤ (places.monomialsAt (List.zipWith (fun x y => x + y)
              (act i (i + 1) p).content q.content)).length
          rw [hBc, show List.zipWith (fun x y => x + y)
                (act i (i + 1) p).content q.content
              = ground.bumpAt i (tensorH p q).content from
            moveAt_vacL i (i + 1) p.content q.content
              (tensorH p q).content rfl
              (Nat.eq_zero_of_not_pos hpo)]
          rw [show ground.bumpAt i (tensorH p q).content
              = ground.bumpAt (i + 1)
                (moveAt i (i + 1) (tensorH p q).content) from
            (bumpAt_moveAt i (i + 1) (tensorH p q).content hccocc).symm]
          refine places.length_monomialsAt_le_bumpAt (i + 1) _ ?_
          rw [length_moveAt, show (tensorH p q).content.length
              = a.length from by
            rw [show (tensorH p q).content
              = List.zipWith (fun x y => x + y) p.content q.content
              from rfl]
            exact ground.length_zipWith (fun x y => x + y) p.content
              q.content a.length hpl hql]
          exact hi
        refine elim.spanRel_congr _ _ _ _
          (poly.oneValue_symm (poly.oneValue_trans hTsp
            (elim.vecAdd_null_left_le _ _ hle hAnull))) hBspan hactl

/-- The coevaluation's raised image sits in the moved content's
own pair span: the coevaluation sits in the stated pair list's span
(`coevVec_span`) and every row of that list maps into the moved
content's group under the raise (`coevKer_rowSpan`), so the span
transports across the action (`elim.span_map`). -/
private theorem coevKer_span (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (i : Nat) (hi : i + 1 < a.length) (hm : 0 < m) :
    elim.spanRel
      (places.monomialsAt
        (moveAt i (i + 1) (List.replicate a.length m))).length
      (groupAt (fusedAt (blockSpan a) (blockSpan b))
        (moveAt i (i + 1) (List.replicate a.length m)))
      (elim.matVec (units.matUnitAt
        (moveAt i (i + 1) (List.replicate a.length m))
        (List.replicate a.length m) i (i + 1))
        (coevVec (List.replicate a.length m) b g W).coords) := by
  have hccocc : 0 < ground.getAt 0
      (List.replicate a.length m) (i + 1) := by
    rw [ground.getAt_replicate 0 m a.length (i + 1) hi]
    exact hm
  have hspan := coevVec_span a b m hba hjoin g hg hgc W hW hWb
  rw [← groupAt_fused (blockSpan a) (blockSpan b)
    (List.replicate a.length m)] at hspan
  have hres := elim.span_map
    (units.matUnitAt (moveAt i (i + 1) (List.replicate a.length m))
      (List.replicate a.length m) i (i + 1))
    (places.monomialsAt (List.replicate a.length m)).length
    (units.rowsLen_matUnitAt _ _ i (i + 1))
    (groupAt (fusedAt (blockSpan a) (blockSpan b))
      (List.replicate a.length m))
    (groupAt (fusedAt (blockSpan a) (blockSpan b))
      (moveAt i (i + 1) (List.replicate a.length m)))
    (blockcount.rowsLen_groupAt _ _ (blockcount.fusedAt_sized _ _))
    (by
      rw [units.length_matUnitAt]
      exact blockcount.rowsLen_groupAt _ _
        (blockcount.fusedAt_sized _ _))
    (by
      intro k hk
      match blockcount.groupAt_rows
          (fun v => v ∈ fusedAt (blockSpan a) (blockSpan b))
          (fusedAt (blockSpan a) (blockSpan b)) (fun _ hv => hv)
          (List.replicate a.length m) k hk with
      | ⟨u, hu, huc, hue⟩ =>
        rw [hue, units.length_matUnitAt]
        exact coevKer_rowSpan a b i hba hi
          (List.replicate a.length m) hccocc u hu huc)
    (coevVec (List.replicate a.length m) b g W).coords
    (coevVec_sized a b m hba hjoin g hg hgc W hW hWb) hspan
  rw [units.length_matUnitAt] at hres
  exact hres

/-- The coevaluation's image under one adjacent raising reads the
unit tail: the image sits in the moved content's pair span
(`coevKer_span`) and pairs every pair of that span at the sum's
unit (`coevKer_pair`), so its own self-pairing reads the unit and
the coordinate family is at the unit tail
(`elim.dotP_self_null`). -/
private theorem coevKer_step (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length)
    (i : Nat) (hi : i + 1 < a.length) (hm : 0 < m) :
    poly.unitTail (elim.matVec (units.matUnitAt
      (moveAt i (i + 1) (List.replicate a.length m))
      (List.replicate a.length m) i (i + 1))
      (coevVec (List.replicate a.length m) b g W).coords) := by
  have hyl : (elim.matVec (units.matUnitAt
        (moveAt i (i + 1) (List.replicate a.length m))
        (List.replicate a.length m) i (i + 1))
        (coevVec (List.replicate a.length m) b g W).coords).length
      = (places.monomialsAt
        (moveAt i (i + 1) (List.replicate a.length m))).length := by
    rw [elim.matVec_length, units.length_matUnitAt]
  have hperp : ∀ k, k < (groupAt (fusedAt (blockSpan a) (blockSpan b))
        (moveAt i (i + 1) (List.replicate a.length m))).length →
      (elim.dotP (elim.matVec (units.matUnitAt
          (moveAt i (i + 1) (List.replicate a.length m))
          (List.replicate a.length m) i (i + 1))
          (coevVec (List.replicate a.length m) b g W).coords)
        (ground.getAt [] (groupAt
          (fusedAt (blockSpan a) (blockSpan b))
          (moveAt i (i + 1)
            (List.replicate a.length m))) k)).oneValue BPair.unit := by
    intro k hk
    match blockcount.groupAt_rows
        (fun v => v ∈ fusedAt (blockSpan a) (blockSpan b))
        (fusedAt (blockSpan a) (blockSpan b)) (fun _ hv => hv)
        (moveAt i (i + 1) (List.replicate a.length m)) k hk with
    | ⟨u, hu, huc, hue⟩ =>
      rw [hue]
      match ground.mem_flatMap_of
          (fun v => (blockSpan b).map (tensorH v))
          (blockSpan a) u hu with
      | ⟨p, hp, hpu⟩ =>
        match ground.mem_map_of (tensorH p) (blockSpan b) u hpu with
        | ⟨q, hq, hqu⟩ =>
          subst hqu
          exact coevKer_pair a b m hba hjoin g hg hgc W hW hWb i hi hm
            p q hp hq huc
  match elim.span_elim (coevKer_span a b m hba hjoin g hg hgc W hW
      hWb i hi hm) with
  | ⟨c0, cs, hc0, _, hone⟩ =>
    refine elim.dotP_self_null _ (ground.mul_cancel_unit hc0 ?_)
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (elim.dotP_vecScale_right _ _ c0)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right _ _ _ hone) ?_
    exact elim.dotP_comboNull _ _ hyl cs _
      (blockcount.rowsLen_groupAt _ _ (blockcount.fusedAt_sized _ _))
      hperp

/-- The coevaluation lies in the stacked raisings' kernel
(`lem:dualread`(iii)'s at-join arm, clause 11's closing sentence):
each adjacent raising's image sits in the moved content's pair span
and pairs every such pair at the sum's unit — the moved pairing is
the walk's read at one further crossing and the two slots' moved
reads join at partners across the transpose identity at the
exchanged letters — so every raising sends the coevaluation to the
unit family and the stacked system does too. -/
theorem coevVec_ker (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (W : List (List Nat))
    (hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)))
    (hWb : ∀ ws ∈ W, ∀ l ∈ ws, l + 1 < b.length) :
    poly.unitTail (elim.matVec
      (units.stackedRaise (List.replicate a.length m))
      (coevVec (List.replicate a.length m) b g W).coords) := by
  refine units.stackedRaise_of _ _ (fun i hi hocc => ?_)
  have hi' : i + 1 < a.length := by
    rw [← ground.length_replicate m a.length]
    exact hi
  have hm : 0 < m := by
    rw [ground.getAt_replicate 0 m a.length (i + 1) hi'] at hocc
    exact hocc
  rw [← blockcount.moveAt_moveUp i (List.replicate a.length m)]
  exact coevKer_step a b m hba hjoin g hg hgc W hW hWb i hi' hm


/-! `lem:dualread`(i)'s correspondence tier: the family's map read
back through the coevaluation's second slot collapses at the
adjugate identity to the graded determinant's scale. -/


/-- A grid entry's first slot carries its content. -/
private theorem coevBody_slot1 (Y : List HVec) (nu : List Nat) :
    ∀ t ∈ coevBody Y nu, t.2.1.content = nu := by
  intro t ht
  match ground.mem_flatMap_of _ _ t ht with
  | ⟨j, hj, hjt⟩ =>
    match ground.mem_map_of _ _ t hjt with
    | ⟨k, _, hkt⟩ =>
      rw [← hkt]
      show (ground.getAt (⟨[], []⟩ : HVec)
        (Y.filter (fun w => w.content == nu)) j).content = nu
      have hjl : j
          < (Y.filter (fun w => w.content == nu)).length :=
        ground.ltOfMemRange hj
      exact ground.listBeqEq
        (ground.mem_filter_of _ _ _
          (ground.mem_getAt _ _ j hjl)).2

/-- A grid entry's second slot carries its content. -/
private theorem coevBody_slot2 (Y : List HVec) (nu : List Nat) :
    ∀ t ∈ coevBody Y nu, t.2.2.content = nu := by
  intro t ht
  match ground.mem_flatMap_of _ _ t ht with
  | ⟨j, _, hjt⟩ =>
    match ground.mem_map_of _ _ t hjt with
    | ⟨k, hk, hkt⟩ =>
      rw [← hkt]
      show (ground.getAt (⟨[], []⟩ : HVec)
        (Y.filter (fun w => w.content == nu)) k).content = nu
      have hkl : k
          < (Y.filter (fun w => w.content == nu)).length :=
        ground.ltOfMemRange hk
      exact ground.listBeqEq
        (ground.mem_filter_of _ _ _
          (ground.mem_getAt _ _ k hkl)).2

/-- At a withdrawn content the grids filter to the vacant
family. -/
private theorem coevFilter_none (Y : List HVec) (mu : List Nat) :
    ∀ l : List (List Nat), ground.countOf mu l = 0 →
      (l.flatMap (coevBody Y)).filter
        (fun t => t.2.1.content == mu) = []
  | [], _ => rfl
  | nu :: t, h => by
    have hsum : (if mu = nu then 1 else 0)
        + ground.countOf mu t = 0 :=
      (ground.countOf_cons mu nu t).symm.trans h
    have hne : ¬ mu = nu := by
      intro he
      rw [if_pos he, Nat.add_comm] at hsum
      exact Nat.noConfusion hsum
    have ht : ground.countOf mu t = 0 := by
      rw [if_neg hne, Nat.zero_add] at hsum
      exact hsum
    show ((coevBody Y nu ++ t.flatMap (coevBody Y)).filter
      (fun t' => t'.2.1.content == mu)) = []
    rw [ground.filter_append,
      ground.filter_false _ (coevBody Y nu) (fun a ha => by
        match hb : a.2.1.content == mu with
        | true =>
          exact absurd
            ((ground.listBeqEq hb).symm.trans
              (coevBody_slot1 Y nu a ha)) hne
        | false => rfl),
      coevFilter_none Y mu t ht]
    rfl

/-- The coevaluation's grids filter at a once-occupied content to
that content's own grid. -/
private theorem coevFilter_pick (Y : List HVec) (mu : List Nat) :
    ∀ l : List (List Nat), ground.countOf mu l = 1 →
      (l.flatMap (coevBody Y)).filter
        (fun t => t.2.1.content == mu) = coevBody Y mu
  | [], h => Nat.noConfusion h
  | nu :: t, h => by
    have hsum : (if mu = nu then 1 else 0)
        + ground.countOf mu t = 1 :=
      (ground.countOf_cons mu nu t).symm.trans h
    show ((coevBody Y nu ++ t.flatMap (coevBody Y)).filter
      (fun t' => t'.2.1.content == mu)) = coevBody Y mu
    rw [ground.filter_append]
    by_cases hmn : mu = nu
    · have ht : ground.countOf mu t = 0 := by
        rw [if_pos hmn] at hsum
        exact ground.addCancelL 1
          (by rw [Nat.add_zero]; exact hsum)
      rw [coevFilter_none Y mu t ht, ground.append_nil, ← hmn]
      exact ground.filter_all _ (coevBody Y mu) (fun a ha => by
        rw [show a.2.1.content = mu
          from coevBody_slot1 Y mu a ha]
        exact ground.listEqBeq mu)
    · have ht : ground.countOf mu t = 1 := by
        rw [if_neg hmn, Nat.zero_add] at hsum
        exact hsum
      rw [ground.filter_false _ (coevBody Y nu) (fun a ha => by
        match hb : a.2.1.content == mu with
        | true =>
          exact absurd ((coevBody_slot1 Y nu a ha).symm.trans
            (ground.listBeqEq hb)) (fun he => hmn he.symm)
        | false => rfl)]
      show ([] : List (BPair × HVec × HVec))
          ++ (t.flatMap (coevBody Y)).filter
            (fun t' => t'.2.1.content == mu) = coevBody Y mu
      exact coevFilter_pick Y mu t ht

/-- The map's coordinates at the filtered combination. -/
private theorem mapAt_coords (P : List (BPair × HVec × HVec))
    (x : HVec) :
    (mapAt P x).coords
      = elim.combo (places.monomialsAt x.content).length
          ((P.filter (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
          ((P.filter (fun t => t.2.1.content == x.content)).map
            (fun t => t.2.2.coords)) := rfl

/-- The grid at a content, the definition's own display. -/
private theorem coevBody_grid (Y : List HVec) (mu : List Nat) :
    coevBody Y mu
      = (List.range (Y.filter (fun w =>
          w.content == mu)).length).flatMap (fun j =>
        (List.range (Y.filter (fun w =>
            w.content == mu)).length).map (fun k =>
          ((coScale Y mu) * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM
                ((Y.filter (fun w => w.content == mu)).map
                  HVec.coords)) k) j,
            ground.getAt (⟨[], []⟩ : HVec)
              (Y.filter (fun w => w.content == mu)) j,
            ground.getAt (⟨[], []⟩ : HVec)
              (Y.filter (fun w => w.content == mu)) k))) := rfl

/-- The product's rearrangement at the collapse: the argument's
pairing crosses to the cofactor's own factor. -/
private theorem mul_arrange (s a d c : BPair) :
    ((s * a) * d) * c = (c * s) * (d * a) := by
  rw [BPair.mul_assoc (s * a) d c, BPair.mul_comm d c,
    BPair.mul_mul_mul_comm s a c d, BPair.mul_comm s c,
    BPair.mul_comm a d]

/-- The map's filter at a once-occupied content picks the
content's own grid, the coevaluation's members at the moved second
slots. -/
private theorem tripFilter (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (h1 : ground.countOf xc
      (ground.dedupL (Y.map HVec.content)) = 1) :
    (mapInv T Y).filter (fun t => t.2.1.content == xc)
      = (coevBody Y xc).map (fun t =>
          (t.1, t.2.1, (⟨t.2.2.content,
            elim.matVec (T t.2.2.content) t.2.2.coords⟩
              : HVec))) := by
  show ((coevData Y).map (fun t =>
      (t.1, t.2.1, (⟨t.2.2.content,
        elim.matVec (T t.2.2.content) t.2.2.coords⟩
          : HVec)))).filter
      (fun t => t.2.1.content == xc) = _
  rw [ground.filter_map
      (fun t : BPair × HVec × HVec =>
        (t.1, t.2.1, (⟨t.2.2.content,
          elim.matVec (T t.2.2.content) t.2.2.coords⟩
            : HVec)))
      (fun t => t.2.1.content == xc) (coevData Y)]
  show ((coevData Y).filter
      (fun t : BPair × HVec × HVec =>
        t.2.1.content == xc)).map
      (fun t => (t.1, t.2.1, (⟨t.2.2.content,
        elim.matVec (T t.2.2.content) t.2.2.coords⟩
          : HVec))) = _
  rw [coevData_flat Y, coevFilter_pick Y xc _ h1]

/-- The filtered map's second slots sit at the content's own
width, the moved members' action rows at the matrix's count. -/
private theorem tripRows (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (h1 : ground.countOf xc
      (ground.dedupL (Y.map HVec.content)) = 1)
    (hT : (T xc).length = (places.monomialsAt xc).length) :
    elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)) := by
  refine elim.rowsLen_map _ _ _ (fun t' ht' => ?_)
  rw [tripFilter T Y xc h1] at ht'
  match ground.mem_map_of _ _ t' ht' with
  | ⟨t, htm, hte⟩ =>
    rw [← hte]
    show (elim.matVec (T t.2.2.content)
      t.2.2.coords).length = _
    rw [coevBody_slot2 Y xc t htm, elim.matVec_length, hT]

/-- The composite's entry beyond the content's width: both sides
read the unit past their shared length. -/
private theorem trip_tail_entry (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    (hrows : elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)))
    (z : List BPair) (r : Nat)
    (hr : ¬ r < (places.monomialsAt xc).length) :
    (ground.getAt BPair.unit
        (mapAt (mapInv T Y) ⟨xc, z⟩).coords r).oneValue
      (ground.getAt BPair.unit
        (elim.vecScale (detAll Y) (elim.matVec (T xc) z)) r) := by
  rw [mapAt_coords,
    ground.getAt_over BPair.unit _ r (by
      rw [elim.length_combo _ _ _ hrows]
      exact Nat.le_of_not_lt hr),
    ground.getAt_over BPair.unit _ r (by
      rw [elim.length_vecScale, elim.matVec_length, hT]
      exact Nat.le_of_not_lt hr)]
  exact BPair.oneValue_refl _

/-- The composite's entry at a once-occupied content opens at the
content's own grid: the double index fold of the coevaluation's
weights against the argument's pairings and the moved second
slots' entries. -/
private theorem trip_grid (T : List Nat → elim.Mat)
    (Y : List HVec) (x : HVec)
    (h1 : ground.countOf x.content
      (ground.dedupL (Y.map HVec.content)) = 1)
    (hrows : elim.rowsLen (places.monomialsAt x.content).length
      (((mapInv T Y).filter (fun t => t.2.1.content == x.content)).map
        (fun t => t.2.2.coords)))
    (r : Nat) (hr : r < (places.monomialsAt x.content).length) :
    (ground.getAt BPair.unit
        (mapAt (mapInv T Y) x).coords r).oneValue
      (ground.famFold BPair.add BPair.unit (fun j =>
        ground.famFold BPair.add BPair.unit (fun k =>
          ((coScale Y x.content
              * ground.getAt BPair.unit
                (elim.cofVec (elim.gramM
                  ((Y.filter (fun w =>
                    w.content == x.content)).map
                    HVec.coords)) k) j)
            * elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                j).coords x.coords)
          * ground.getAt BPair.unit
            (elim.matVec (T (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).content)
              (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).coords) r)
          (List.range (Y.filter (fun w =>
            w.content == x.content)).length))
        (List.range (Y.filter (fun w =>
          w.content == x.content)).length)) := by
  rw [mapAt_coords]
  refine BPair.oneValue_trans
    (elim.combo_getAt _ _ _ r hrows hr) ?_
  rw [tripFilter T Y x.content h1, ground.map_map, ground.map_map,
    ground.map_map, elim.dotP_map_pair, coevBody_grid]
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws
      _ _ (List.range (Y.filter (fun w =>
        w.content == x.content)).length)) ?_
  exact ground.foldB_congr_members _ _
    (List.range (Y.filter (fun w =>
      w.content == x.content)).length)
    (fun j _ => BPair.oneValue_of_eq
      (ground.famFold_map BPair.add BPair.unit _ _
        (List.range (Y.filter (fun w =>
          w.content == x.content)).length)))

/-- The members' read: the composite's value at a listed member is
the member's own at `detAll`'s scale — `lem:dualread`(i)'s round
trip at the adjugate identity, the filter's pick at the member's
withdrawn key closing at the graded determinant, the matrix at the
content's own coordinates. -/
theorem mapInv_trip_mem (T : List Nat → elim.Mat)
    (Y : List HVec)
    (x : HVec) (hx : x ∈ Y)
    (hT : (T x.content).length
      = (places.monomialsAt x.content).length) :
    poly.oneValue (mapAt (mapInv T Y) x).coords
      (elim.vecScale (detAll Y)
        (elim.matVec (T x.content) x.coords)) := by
  have h1 : ground.countOf x.content
      (ground.dedupL (Y.map HVec.content)) = 1 :=
    ground.countOf_dedupL_one (ground.mem_map_to HVec.content hx)
  have hrows := tripRows T Y x.content h1 hT
  have hgrp : ∀ w ∈ Y.filter (fun w' =>
      w'.content == x.content), w.content = x.content :=
    fun w hw =>
      ground.listBeqEq (ground.mem_filter_of _ _ _ hw).2
  refine poly.ov_of_getAt (fun r => ?_)
  by_cases hr : r < (places.monomialsAt x.content).length
  · rw [elim.getAt_vecScale (detAll Y) _ r (by
      rw [elim.matVec_length, hT]
      exact hr)]
    refine BPair.oneValue_trans (trip_grid T Y x h1 hrows r hr) ?_
    refine BPair.oneValue_trans
      (ground.foldB_swapL
        (fun j k => ((coScale Y x.content
              * ground.getAt BPair.unit
                (elim.cofVec (elim.gramM
                  ((Y.filter (fun w =>
                    w.content == x.content)).map
                    HVec.coords)) k) j)
            * elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                j).coords x.coords)
          * ground.getAt BPair.unit
            (elim.matVec (T (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).content)
              (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).coords) r)
        (List.range (Y.filter (fun w =>
          w.content == x.content)).length)
        (List.range (Y.filter (fun w =>
          w.content == x.content)).length)) ?_
    match ground.getAt_of_mem (⟨[], []⟩ : HVec)
      (ground.mem_filter_to (fun w => w.content == x.content) hx
        (ground.listEqBeq x.content)) with
    | ⟨m, hm, hme⟩ =>
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun k => (ground.getAt BPair.unit
              (elim.matVec (T x.content)
                (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == x.content))
                  k).coords) r
            * coScale Y x.content)
            * (if k = m
              then elim.detL (elim.gramM
                ((Y.filter (fun w =>
                  w.content == x.content)).map HVec.coords))
              else BPair.unit))
          (List.range (Y.filter (fun w =>
            w.content == x.content)).length)
          (fun k hk0 => ?_)) ?_
      · have hk : k < (Y.filter (fun w =>
            w.content == x.content)).length :=
          ground.ltOfMem hk0
        have hkc : (ground.getAt (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == x.content))
            k).content = x.content :=
          hgrp _ (ground.mem_getAt _ _ k hk)
        refine BPair.oneValue_trans
          (ground.foldB_congr_members _
            (fun j => (ground.getAt BPair.unit
                (elim.matVec (T x.content)
                  (ground.getAt (⟨[], []⟩ : HVec)
                    (Y.filter (fun w =>
                      w.content == x.content)) k).coords) r
              * coScale Y x.content)
              * (dotG (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == x.content))
                  j) x
                * ground.getAt BPair.unit
                  (elim.cofVec (elim.gramM
                    ((Y.filter (fun w =>
                      w.content == x.content)).map
                      HVec.coords)) k) j))
            (List.range (Y.filter (fun w =>
              w.content == x.content)).length)
            (fun j hj0 => ?_)) ?_
        · have hj : j < (Y.filter (fun w =>
              w.content == x.content)).length :=
            ground.ltOfMem hj0
          refine BPair.oneValue_of_eq ?_
          rw [hkc,
            show dotG (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content)) j) x
              = elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w =>
                    w.content == x.content)) j).coords
                  x.coords from by
              show (if (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w =>
                    w.content == x.content)) j).content
                  = x.content then _ else _) = _
              rw [if_pos (hgrp _
                (ground.mem_getAt _ _ j hj))],
            mul_arrange]
        · refine BPair.oneValue_trans
            (ground.foldB_mul_left _ _
              (List.range (Y.filter (fun w =>
                w.content == x.content)).length)) ?_
          refine BPair.mul_congr (BPair.oneValue_refl _) ?_
          apply elim.cofVec_col_fold
            (elim.gramM ((Y.filter (fun w =>
              w.content == x.content)).map HVec.coords))
            (grp_sqAt (Y.filter (fun w =>
              w.content == x.content))) m k hm hk
            (fun j => dotG (ground.getAt (⟨[], []⟩ : HVec)
              (Y.filter (fun w => w.content == x.content)) j) x)
            (grp_entry (Y.filter (fun w =>
              w.content == x.content)) x.content hgrp x m hm hme)
      · refine ground.foldB_pickRange _ m _ (Y.filter (fun w =>
          w.content == x.content)).length hm ?_ ?_
        · rw [if_pos (show m = m from rfl), hme]
          refine BPair.oneValue_of_eq ?_
          rw [BPair.mul_assoc,
            show elim.detL (elim.gramM
                ((Y.filter (fun w =>
                  w.content == x.content)).map HVec.coords))
              = blockDet Y x.content from rfl,
            scale_detAll Y x.content h1,
            BPair.mul_comm]
        · intro t' _ hti
          rw [if_neg hti]
          exact BPair.mul_unit _
  · exact trip_tail_entry T Y x.content hT hrows x.coords r hr

/-- The combination's peel at a leading coefficient and row. -/
private theorem combo_cons (n : Nat) (c : BPair) (cs : List BPair)
    (r : List BPair) (L : elim.Mat) :
    elim.combo n (c :: cs) (r :: L)
      = elim.vecAdd (elim.vecScale c r) (elim.combo n cs L) := rfl

/-- The composite's read at a unit-tailed argument: both sides read
the unit tail, the weights at the vanished pairings and the moved
member at the cleared action. -/
private theorem trip_null (T : List Nat → elim.Mat)
    (Y : List HVec) (x : HVec) (hu : poly.unitTail x.coords) :
    poly.oneValue (mapAt (mapInv T Y) x).coords
      (elim.vecScale (detAll Y)
        (elim.matVec (T x.content) x.coords)) := by
  refine poly.unitTail_oneValue ?_ ?_
  · rw [mapAt_coords]
    refine elim.unitTail_combo_of _ _ _ ?_
    exact poly.unitTail_map _ _ (fun t _ =>
      elim.oneValue_mul_unit t.1 _
        (elim.dotP_null_tail_right t.2.1.coords x.coords hu))
  · exact elim.unitTail_vecScale (detAll Y) _
      (elim.matVec_null (T x.content) x.coords hu)

/-- The scaled action's entry at the frame: the graded determinant
against the row's pairing, the width the matrix's own. -/
private theorem rhs_entry (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    (z : List BPair) (r : Nat)
    (hr : r < (places.monomialsAt xc).length) :
    ground.getAt BPair.unit
        (elim.vecScale (detAll Y) (elim.matVec (T xc) z)) r
      = detAll Y
        * elim.dotN (ground.getAt ([] : List BPair) (T xc) r) z := by
  rw [elim.getAt_vecScale (detAll Y) _ r (by
    rw [elim.matVec_length, hT]
    exact hr)]
  rw [show elim.matVec (T xc) z
      = (T xc).map (fun row => elim.dotN row z) from rfl]
  rw [ground.getAt_map ([] : List BPair) BPair.unit
    (fun row => elim.dotN row z) (T xc) r (by
      rw [hT]
      exact hr)]

/-- The composite's entry congruence in the argument, the weights
reading the moved pairing per member. -/
private theorem lhs_congr_entry (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hrows : elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)))
    {u v : List BPair} (huv : poly.oneValue u v) (r : Nat)
    (hr : r < (places.monomialsAt xc).length) :
    (ground.getAt BPair.unit
        (mapAt (mapInv T Y) ⟨xc, u⟩).coords r).oneValue
      (ground.getAt BPair.unit
        (mapAt (mapInv T Y) ⟨xc, v⟩).coords r) := by
  rw [mapAt_coords, mapAt_coords]
  refine BPair.oneValue_trans
    (elim.combo_getAt _ _ _ r hrows hr) ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _ _ _
      (poly.oneValue_map _ _ _ (fun t _ =>
        BPair.mul_congr (BPair.oneValue_refl t.1)
          (elim.dotP_oneValue_right t.2.1.coords u v huv)))) ?_
  exact BPair.oneValue_symm (elim.combo_getAt _ _ _ r hrows hr)

/-- The scaled action's entry congruence in the argument. -/
private theorem rhs_congr_entry (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    {u v : List BPair} (huv : poly.oneValue u v) (r : Nat)
    (hr : r < (places.monomialsAt xc).length) :
    (ground.getAt BPair.unit
        (elim.vecScale (detAll Y) (elim.matVec (T xc) u)) r).oneValue
      (ground.getAt BPair.unit
        (elim.vecScale (detAll Y) (elim.matVec (T xc) v)) r) := by
  rw [rhs_entry T Y xc hT u r hr, rhs_entry T Y xc hT v r hr]
  exact BPair.mul_congr (BPair.oneValue_refl (detAll Y))
    (elim.dotN_congrR _ u v huv)

/-- A clearing crosses a map to the pointwise product's map. -/
private theorem vecScale_map {α : Type} (c : BPair)
    (f : α → BPair) (l : List α) :
    elim.vecScale c (l.map f) = l.map (fun t => c * f t) :=
  ground.map_map f (fun d => c * d) l

/-- The composite's entry at a cleared argument reads the clearing
against the entry, the scalar crossing the weights and the fold. -/
private theorem lhs_scale_entry (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hrows : elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)))
    (c : BPair) (z : List BPair) (r : Nat)
    (hr : r < (places.monomialsAt xc).length) :
    (ground.getAt BPair.unit
        (mapAt (mapInv T Y) ⟨xc, elim.vecScale c z⟩).coords
        r).oneValue
      (c * ground.getAt BPair.unit
        (mapAt (mapInv T Y) ⟨xc, z⟩).coords r) := by
  rw [mapAt_coords, mapAt_coords]
  refine BPair.oneValue_trans
    (elim.combo_getAt _ _ _ r hrows hr) ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _ _ _
      (poly.oneValue_map _ _ _ (fun t _ =>
        BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl t.1)
            (elim.dotP_vecScale_right t.2.1.coords z c))
          (BPair.oneValue_of_eq (BPair.mul_left_comm t.1 c _))))) ?_
  rw [← vecScale_map c
    (fun t => t.1 * elim.dotP t.2.1.coords z)
    ((mapInv T Y).filter (fun t => t.2.1.content == xc))]
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (elim.dotP_comm _ _)) ?_
  refine BPair.oneValue_trans (elim.dotP_vecScale_right _ _ c) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl c)
      (BPair.oneValue_of_eq (elim.dotP_comm _ _))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl c)
    (BPair.oneValue_symm (elim.combo_getAt _ _ _ r hrows hr))

/-- The scaled action's entry at a cleared argument reads the
clearing against the entry. -/
private theorem rhs_scale_entry (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    (c : BPair) (z : List BPair) (r : Nat)
    (hr : r < (places.monomialsAt xc).length) :
    (ground.getAt BPair.unit
        (elim.vecScale (detAll Y)
          (elim.matVec (T xc) (elim.vecScale c z))) r).oneValue
      (c * ground.getAt BPair.unit
        (elim.vecScale (detAll Y) (elim.matVec (T xc) z)) r) := by
  rw [rhs_entry T Y xc hT (elim.vecScale c z) r hr,
    rhs_entry T Y xc hT z r hr]
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (detAll Y))
      (BPair.oneValue_trans (elim.dotN_read _ _)
        (BPair.oneValue_trans (elim.dotP_vecScale_right _ z c)
          (BPair.mul_congr (BPair.oneValue_refl c)
            (BPair.oneValue_symm (elim.dotN_read _ z)))))) ?_
  exact BPair.oneValue_of_eq (BPair.mul_left_comm (detAll Y) c _)

/-- The composite's read is additive in the argument at the
members' shared order, both sides splitting entry by entry. -/
private theorem trip_add (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    (hrows : elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)))
    (u v : List BPair) (huv : u.length = v.length)
    (hu : poly.oneValue (mapAt (mapInv T Y) ⟨xc, u⟩).coords
      (elim.vecScale (detAll Y) (elim.matVec (T xc) u)))
    (hv : poly.oneValue (mapAt (mapInv T Y) ⟨xc, v⟩).coords
      (elim.vecScale (detAll Y) (elim.matVec (T xc) v))) :
    poly.oneValue
      (mapAt (mapInv T Y) ⟨xc, elim.vecAdd u v⟩).coords
      (elim.vecScale (detAll Y)
        (elim.matVec (T xc) (elim.vecAdd u v))) := by
  refine poly.ov_of_getAt (fun r => ?_)
  by_cases hr : r < (places.monomialsAt xc).length
  · rw [mapAt_coords, rhs_entry T Y xc hT (elim.vecAdd u v) r hr]
    refine BPair.oneValue_trans
      (elim.combo_getAt _ _ _ r hrows hr) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _
        (poly.oneValue_map _ _ _ (fun t _ =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (elim.dotP_vecAdd_right t.2.1.coords u v huv))
            (BPair.oneValue_of_eq (BPair.left_distrib t.1 _ _))))) ?_
    rw [show ((mapInv T Y).filter
          (fun t => t.2.1.content == xc)).map
          (fun t => t.1 * elim.dotP t.2.1.coords u
            + t.1 * elim.dotP t.2.1.coords v)
        = elim.vecAdd
          (((mapInv T Y).filter
            (fun t => t.2.1.content == xc)).map
            (fun t => t.1 * elim.dotP t.2.1.coords u))
          (((mapInv T Y).filter
            (fun t => t.2.1.content == xc)).map
            (fun t => t.1 * elim.dotP t.2.1.coords v)) from
      (elim.mapAdd _ _ _).symm]
    refine BPair.oneValue_trans
      (elim.dotP_vecAdd_left _ _ _
        (Nat.le_of_eq (by
          rw [ground.length_map, ground.length_map,
            ground.length_map]))
        (Nat.le_of_eq (by
          rw [ground.length_map, ground.length_map,
            ground.length_map]))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.oneValue_symm
            (elim.combo_getAt _ _ _ r hrows hr))
          (BPair.oneValue_trans (poly.oneValue_getAt r hu)
            (BPair.oneValue_of_eq (rhs_entry T Y xc hT u r hr))))
        (BPair.oneValue_trans
          (BPair.oneValue_symm
            (elim.combo_getAt _ _ _ r hrows hr))
          (BPair.oneValue_trans (poly.oneValue_getAt r hv)
            (BPair.oneValue_of_eq
              (rhs_entry T Y xc hT v r hr))))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.left_distrib (detAll Y) _ _).symm) ?_
    refine BPair.mul_congr (BPair.oneValue_refl (detAll Y)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
    refine BPair.oneValue_trans
      (elim.dotP_vecAdd_right _ u v huv) ?_
    exact BPair.add_congr
      (BPair.oneValue_symm (elim.dotN_read _ u))
      (BPair.oneValue_symm (elim.dotN_read _ v))
  · exact trip_tail_entry T Y xc hT hrows (elim.vecAdd u v) r hr

/-- The composite's read scales in the argument, the clearing
crossing both sides entry by entry. -/
private theorem trip_scale (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    (hrows : elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)))
    (c : BPair) (z : List BPair)
    (hz : poly.oneValue (mapAt (mapInv T Y) ⟨xc, z⟩).coords
      (elim.vecScale (detAll Y) (elim.matVec (T xc) z))) :
    poly.oneValue
      (mapAt (mapInv T Y) ⟨xc, elim.vecScale c z⟩).coords
      (elim.vecScale (detAll Y)
        (elim.matVec (T xc) (elim.vecScale c z))) := by
  refine poly.ov_of_getAt (fun r => ?_)
  by_cases hr : r < (places.monomialsAt xc).length
  · refine BPair.oneValue_trans
      (lhs_scale_entry T Y xc hrows c z r hr) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c)
        (poly.oneValue_getAt r hz)) ?_
    exact BPair.oneValue_symm
      (rhs_scale_entry T Y xc hT c z r hr)
  · exact trip_tail_entry T Y xc hT hrows (elim.vecScale c z) r hr

/-- The composite's read at a combination of listed members, the
peel one member at a time: the head at the member collapse scaled,
the tail at the recursion, the join at the additivity. -/
private theorem tripCombo (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (hT : (T xc).length = (places.monomialsAt xc).length)
    (hrows : elim.rowsLen (places.monomialsAt xc).length
      (((mapInv T Y).filter (fun t => t.2.1.content == xc)).map
        (fun t => t.2.2.coords)))
    (n : Nat) :
    ∀ (cs : List BPair) (G : List HVec),
      (∀ g ∈ G, g ∈ Y ∧ g.content = xc ∧ g.coords.length = n) →
      poly.oneValue
        (mapAt (mapInv T Y)
          ⟨xc, elim.combo n cs (G.map HVec.coords)⟩).coords
        (elim.vecScale (detAll Y)
          (elim.matVec (T xc)
            (elim.combo n cs (G.map HVec.coords))))
  | [], G, _ =>
    trip_null T Y ⟨xc, elim.combo n [] (G.map HVec.coords)⟩
      (poly.unitTail_replicate n)
  | _ :: _, [], _ =>
    trip_null T Y
      ⟨xc, elim.combo n _ (([] : List HVec).map HVec.coords)⟩
      (poly.unitTail_replicate n)
  | c :: cs, g :: G', hG => by
    have hg := hG g (List.Mem.head G')
    rw [show ((g :: G').map HVec.coords)
        = g.coords :: G'.map HVec.coords from rfl,
      combo_cons n c cs g.coords (G'.map HVec.coords)]
    refine trip_add T Y xc hT hrows _ _ ?_ ?_ ?_
    · have hrowsG : elim.rowsLen n (G'.map HVec.coords) :=
        elim.rowsLen_map _ _ _
          (fun g' hg' => (hG g' (List.Mem.tail _ hg')).2.2)
      rw [elim.length_vecScale,
        elim.length_combo _ _ _ hrowsG]
      exact hg.2.2
    · refine trip_scale T Y xc hT hrows c g.coords ?_
      have hgT : (T g.content).length
          = (places.monomialsAt g.content).length := by
        rw [hg.2.1]
        exact hT
      have hbase := mapInv_trip_mem T Y g hg.1 hgT
      rw [← hg.2.1]
      exact hbase
    · exact tripCombo T Y xc hT hrows n cs G'
        (fun g' hg' => hG g' (List.Mem.tail _ hg'))

/-- The members' reads extend over the list's span: the composite
at a map reads the graded determinant's scale at every member of
the argument's content group's span — `lem:dualread`(i)'s round
trip, both composites additive and scale-reading in the argument,
a span member's cleared combination reading them through the
members with the clearing withdrawn at the product's injectivity,
the matrix at the content's own coordinates. -/
theorem mapInv_trip (T : List Nat → elim.Mat) (Y : List HVec)
    (x : HVec)
    (hsp : elim.spanRel x.coords.length
      (blockcount.groupAt Y x.content) x.coords)
    (hT : (T x.content).length
      = (places.monomialsAt x.content).length) :
    poly.oneValue (mapAt (mapInv T Y) x).coords
      (elim.vecScale (detAll Y)
        (elim.matVec (T x.content) x.coords)) := by
    have hgrp : blockcount.groupAt Y x.content
        = (Y.filter (fun w => w.content == x.content)).map
          HVec.coords := rfl
    match hYf : Y.filter (fun w => w.content == x.content) with
    | [] =>
      rw [hgrp, hYf] at hsp
      match elim.span_elim hsp with
      | ⟨c₀, cs, hc₀, _, hone⟩ =>
        refine trip_null T Y x (elim.unitTail_unscale _ hc₀ x.coords ?_)
        refine poly.oneValue_unitTail hone ?_
        exact elim.unitTail_combo_rows _ cs _
          (fun k hk => absurd hk (Nat.not_lt_zero k))
    | g :: rest =>
      have hgmem : g ∈ Y.filter
          (fun w => w.content == x.content) := by
        rw [hYf]
        exact List.Mem.head rest
      have hgY : g ∈ Y := (ground.mem_filter_of _ _ _ hgmem).1
      have hgc : g.content = x.content :=
        ground.listBeqEq (ground.mem_filter_of _ _ _ hgmem).2
      have hxm : x.content ∈ Y.map HVec.content := by
        rw [← hgc]
        exact ground.mem_map_to HVec.content hgY
      have h1 : ground.countOf x.content
          (ground.dedupL (Y.map HVec.content)) = 1 :=
        ground.countOf_dedupL_one hxm
      have hrows := tripRows T Y x.content h1 hT
      have hGf : ∀ g' ∈ Y.filter
          (fun w => w.content == x.content),
          g' ∈ Y ∧ g'.content = x.content
            ∧ g'.coords.length = x.coords.length := by
        intro g' hg'
        refine ⟨(ground.mem_filter_of _ _ _ hg').1,
          ground.listBeqEq (ground.mem_filter_of _ _ _ hg').2,
          ?_⟩
        match ground.getAt_of_mem ([] : List BPair)
          (ground.mem_map_to HVec.coords hg') with
        | ⟨k, hk, hke⟩ =>
          rw [← hke]
          exact elim.rowsLen_getAt _ k hsp.1 hk
      match elim.span_elim hsp with
      | ⟨c₀, cs, hc₀, _, hone⟩ =>
        have htrip := tripCombo T Y x.content hT hrows
          x.coords.length cs
          (Y.filter (fun w => w.content == x.content)) hGf
        refine poly.ov_of_getAt (fun r => ?_)
        by_cases hr : r < (places.monomialsAt x.content).length
        · refine ground.mulCancel hc₀ ?_
          refine BPair.oneValue_trans
            (BPair.oneValue_symm
              (lhs_scale_entry T Y x.content hrows c₀
                x.coords r hr)) ?_
          refine BPair.oneValue_trans
            (lhs_congr_entry T Y x.content hrows hone r hr) ?_
          refine BPair.oneValue_trans
            (poly.oneValue_getAt r htrip) ?_
          refine BPair.oneValue_trans
            (rhs_congr_entry T Y x.content hT
              (poly.oneValue_symm hone) r hr) ?_
          exact rhs_scale_entry T Y x.content hT c₀
            x.coords r hr
        · exact trip_tail_entry T Y x.content hT hrows x.coords r hr

/-! `lem:dualread`(i)'s invariant tier: the map's datum read at a
letter pair against a member and any second vector — the first
slots walked across the transpose identity to the member's letter
image, the two adjugate folds collected at the map's read of that
image, and the residual reading the sum's unit over the list's
span at the pairing's definiteness. -/

/-- The map's second slot at a member: the matrix at the member's
own content against the member's coordinates. -/
private def slotT (T : List Nat → elim.Mat) (w : HVec) : HVec :=
  ⟨w.content, elim.matVec (T w.content) w.coords⟩

/-- The Gram's column reads its row at the stated key, the
pairing's two orders one value. -/
private theorem gram_col_row (L : elim.Mat) (i : Nat)
    (hi : i < L.length) :
    poly.oneValue
      ((elim.gramM L).map (fun r => ground.getAt BPair.unit r i))
      (ground.getAt ([] : List BPair) (elim.gramM L) i) := by
  have hGl : (elim.gramM L).length = L.length :=
    elim.sqAt_len (elim.gram_sqAt L)
  have hGr : elim.rowsLen L.length (elim.gramM L) :=
    elim.rowsLen_of_sqAt (elim.gram_sqAt L)
  refine poly.ov_of_getAt (fun j => ?_)
  by_cases hj : j < L.length
  · rw [ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => ground.getAt BPair.unit r i) (elim.gramM L) j
      (by rw [hGl]; exact hj),
    elim.gramM_symm L j i hj hi]
    exact BPair.oneValue_refl _
  · rw [ground.getAt_over BPair.unit _ j (by
      rw [ground.length_map, hGl]
      exact Nat.le_of_not_lt hj),
    ground.getAt_over BPair.unit _ j (by
      rw [elim.rowsLen_getAt (elim.gramM L) i hGr
        (by rw [hGl]; exact hi)]
      exact Nat.le_of_not_lt hj)]
    exact BPair.oneValue_refl _

/-- The Gram against the adjugate solve reads the determinant's
scale entry for entry, `G·(adj(G)·p) ~ det(G)·p` at the symmetric
square's own columns. -/
private theorem adjP_solve (L : elim.Mat) (P : List BPair) (m : Nat)
    (hm : L.length = m) (hP : P.length = m) :
    poly.oneValue
      (elim.combo m (elim.adjP (elim.gramM L) P) (elim.gramM L))
      (elim.vecScale (elim.detL (elim.gramM L)) P) := by
  subst hm
  have hGr : elim.rowsLen L.length (elim.gramM L) :=
    elim.rowsLen_of_sqAt (elim.gram_sqAt L)
  refine poly.ov_of_getAt (fun i => ?_)
  by_cases hi : i < L.length
  · rw [elim.getAt_vecScale (elim.detL (elim.gramM L)) P i
      (by rw [hP]; exact hi)]
    refine BPair.oneValue_trans
      (elim.combo_getAt L.length (elim.adjP (elim.gramM L) P)
        (elim.gramM L) i hGr hi) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right (elim.adjP (elim.gramM L) P) _ _
        (gram_col_row L i hi)) ?_
    rw [elim.dotP_comm]
    refine BPair.oneValue_trans
      (elim.adjP_read (elim.gramM L) (elim.gram_sqAt L) P hP i hi) ?_
    exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
  · rw [ground.getAt_over BPair.unit _ i (by
      rw [elim.length_combo L.length _ (elim.gramM L) hGr]
      exact Nat.le_of_not_lt hi),
    ground.getAt_over BPair.unit _ i (by
      rw [elim.length_vecScale, hP]
      exact Nat.le_of_not_lt hi)]
    exact BPair.oneValue_refl _

/-- The mapped pairing reads a clearing's scale. -/
private theorem mapPair_scale (M : elim.Mat) (r : List BPair)
    (c : BPair) (u : List BPair) :
    (elim.dotP (elim.matVec M (elim.vecScale c u)) r).oneValue
      (c * elim.dotP (elim.matVec M u) r) := by
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _ _ r (elim.matVec_vecScale_free M c u)) ?_
  rw [elim.dotP_comm, elim.dotP_comm (elim.matVec M u) r]
  exact elim.dotP_vecScale_right r _ c

/-- The mapped pairing's congruence in its vector. -/
private theorem mapPair_congr (M : elim.Mat) (r u u' : List BPair)
    (h : poly.oneValue u u') :
    (elim.dotP (elim.matVec M u) r).oneValue
      (elim.dotP (elim.matVec M u') r) :=
  elim.dotP_oneValue_left _ _ r (elim.matVec_congr M u u' h)

/-- The mapped pairing at a combination reads the coefficients
against the rows' own mapped pairings, the two frameless
combination reads composed at the exchanged pairing orders. -/
private theorem mapPair_combo (M : elim.Mat) (r : List BPair)
    (n : Nat) (cs : List BPair) (L : elim.Mat)
    (hL : elim.rowsLen n L) :
    (elim.dotP (elim.matVec M (elim.combo n cs L)) r).oneValue
      (elim.dotP cs
        (L.map (fun row => elim.dotP (elim.matVec M row) r))) := by
  have hK : elim.rowsLen M.length (L.map (elim.matVec M)) :=
    elim.rowsLen_map (elim.matVec M) M.length L
      (fun x _ => elim.matVec_length M x)
  rw [elim.dotP_comm (elim.matVec M (elim.combo n cs L)) r,
    show L.map (fun row => elim.dotP (elim.matVec M row) r)
        = (L.map (elim.matVec M)).map
          (fun row => elim.dotP r row) from by
      rw [ground.map_map]
      exact ground.map_congr_members _ _ L
        (fun w _ => elim.dotP_comm (elim.matVec M w) r)]
  exact BPair.oneValue_trans
    (elim.dotP_oneValue_right r _ _ (elim.matVec_combo M n cs L hL))
    (elim.dotP_combo cs (L.map (elim.matVec M)) r M.length hK)

/-- The group's second slots read the content's own matrix against
the members' coordinates, the graded guard firing at the group's
shared content. -/
private theorem slot_map (T : List Nat → elim.Mat)
    (grp : List HVec) (b : HVec)
    (hcont : ∀ w ∈ grp, w.content = b.content) :
    grp.map (fun w => dotG (slotT T w) b)
      = (grp.map HVec.coords).map (fun row =>
        elim.dotP (elim.matVec (T b.content) row) b.coords) := by
  rw [ground.map_map]
  refine ground.map_congr_members _ _ grp (fun w hw => ?_)
  have hwc : w.content = b.content :=
    hcont w (ground.mem_of_countOf_pos _ grp hw)
  show (if (slotT T w).content = b.content
      then elim.dotP (slotT T w).coords b.coords
      else BPair.unit)
    = elim.dotP (elim.matVec (T b.content) w.coords) b.coords
  rw [if_pos (show (slotT T w).content = b.content from hwc)]
  show elim.dotP (elim.matVec (T w.content) w.coords) b.coords
    = elim.dotP (elim.matVec (T b.content) w.coords) b.coords
  rw [hwc]

/-- The block at one content with the map's second slots: the
first summand collects at the adjugate fold when the content is
the second vector's, the second at the determinant-scaled crossed
pairing when it is the argument's, every further content's block
at the sum's unit. -/
private theorem group_readT (T : List Nat → elim.Mat)
    (grp : List HVec) (mu : List Nat)
    (hcont : ∀ w ∈ grp, w.content = mu) (s D E : BPair)
    (hsd : s * elim.detL (elim.gramM (grp.map HVec.coords)) = D)
    (p q : Nat) (a b : HVec)
    (hag : mu = a.content → a ∈ grp)
    (hE : mu = b.content →
      s * ground.famFold BPair.add BPair.unit (fun j =>
        dotG (dact p q (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
          * ground.getAt BPair.unit
            (elim.adjP (elim.gramM (grp.map HVec.coords))
              (grp.map (fun w => dotG (slotT T w) b))) j)
        (List.range grp.length) = E) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (dotG (dact p q
                (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
              * dotG (slotT T
                (ground.getAt (⟨[], []⟩ : HVec) grp k)) b
            + dotG (ground.getAt (⟨[], []⟩ : HVec) grp j) a
              * dotG (act p q (slotT T
                  (ground.getAt (⟨[], []⟩ : HVec) grp k))) b))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      ((if mu = b.content then E else BPair.unit)
        + (if mu = a.content
          then D * dotG (act p q (slotT T a)) b
          else BPair.unit)) :=
  group_readF (slotT T) grp mu hcont (fun _ _ => rfl) s D E hsd
    p q a b hag
    (fun hbm => by
      rw [← hE hbm]
      exact block_oneF grp s (fun w => dotG (dact p q w) a)
        (fun w => dotG (slotT T w) b))

/-- The cleared pairing at a group member reads the Gram's row
against the combination's coefficients: the clearing crosses the
pairing to the cleared vector, the combination expands over the
group's rows, and the row of pairings is the Gram's own. -/
private theorem span_pair_row (grp : List HVec) (v : List BPair)
    (c₀ : BPair) (cs : List BPair) (n : Nat)
    (hrows : elim.rowsLen n (grp.map HVec.coords))
    (hone : poly.oneValue (elim.vecScale c₀ v)
      (elim.combo n cs (grp.map HVec.coords)))
    (j : Nat) (hj : j < grp.length) :
    (c₀ * elim.dotP
        (ground.getAt (⟨[], []⟩ : HVec) grp j).coords v).oneValue
      (ground.getAt BPair.unit
        (elim.matVec (elim.gramM (grp.map HVec.coords)) cs) j) := by
  have hLl : (grp.map HVec.coords).length = grp.length :=
    ground.length_map _ grp
  have hGl : (elim.gramM (grp.map HVec.coords)).length
      = grp.length := by
    rw [elim.sqAt_len (elim.gram_sqAt (grp.map HVec.coords)), hLl]
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (elim.dotP_vecScale_right
      (ground.getAt (⟨[], []⟩ : HVec) grp j).coords v c₀)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right _ _ _ hone) ?_
  refine BPair.oneValue_trans
    (elim.dotP_combo cs (grp.map HVec.coords)
      (ground.getAt (⟨[], []⟩ : HVec) grp j).coords n
      hrows) ?_
  rw [show elim.matVec (elim.gramM (grp.map HVec.coords)) cs
      = (elim.gramM (grp.map HVec.coords)).map
        (fun r => elim.dotN r cs) from rfl,
    ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => elim.dotN r cs)
      (elim.gramM (grp.map HVec.coords)) j
      (by rw [hGl]; exact hj)]
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (elim.dotN_read (ground.getAt ([] : List BPair)
      (elim.gramM (grp.map HVec.coords)) j) cs) ?_)
  rw [elim.dotP_comm (ground.getAt ([] : List BPair)
      (elim.gramM (grp.map HVec.coords)) j) cs,
    show ground.getAt ([] : List BPair)
        (elim.gramM (grp.map HVec.coords)) j
      = (grp.map HVec.coords).map (fun c => elim.dotP
          (ground.getAt (⟨[], []⟩ : HVec) grp j).coords c)
      from by
      show ground.getAt ([] : List BPair)
          ((grp.map HVec.coords).map (fun r =>
            (grp.map HVec.coords).map (fun c => elim.dotP r c)))
          j = _
      rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
          (fun r => (grp.map HVec.coords).map
            (fun c => elim.dotP r c))
          (grp.map HVec.coords) j (by rw [hLl]; exact hj),
        ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
          HVec.coords grp j hj]]
  exact BPair.oneValue_refl _

/-- The block's term-one fold cleared at the span's own scalar:
the first slots walk across the transpose identity to the member's
letter image, the walked family reads the Gram against the
combination's coefficients, and the adjugate solve collects the
determinant against the second slots' pairings. -/
private theorem blk_clear (T : List Nat → elim.Mat)
    (grp : List HVec) (p q : Nat) (a b : HVec) (c₀ : BPair)
    (cs : List BPair) (n : Nat)
    (hcont : ∀ w ∈ grp, w.content = b.content)
    (hrows : elim.rowsLen n (grp.map HVec.coords))
    (hcsl : cs.length = grp.length)
    (hone : poly.oneValue (elim.vecScale c₀ (act p q a).coords)
      (elim.combo n cs (grp.map HVec.coords)))
    (hqb : q < b.content.length) (hpq : ¬ p = q)
    (hocc : 0 < ground.getAt 0 b.content p)
    (hg1 : moveAt q p b.content = a.content) (hsa : sized a)
    (hnm : n = (places.monomialsAt b.content).length) :
    (c₀ * ground.famFold BPair.add BPair.unit (fun j =>
      dotG (dact p q (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
        * ground.getAt BPair.unit
          (elim.adjP (elim.gramM (grp.map HVec.coords))
            (grp.map (fun w => dotG (slotT T w) b))) j)
      (List.range grp.length)).oneValue
      ((elim.detL (elim.gramM (grp.map HVec.coords))
        * elim.dotP cs
          (grp.map (fun w => dotG (slotT T w) b))).swap) := by
  have hLl : (grp.map HVec.coords).length = grp.length :=
    ground.length_map _ grp
  have hGl : (elim.gramM (grp.map HVec.coords)).length
      = grp.length := by
    rw [elim.sqAt_len (elim.gram_sqAt (grp.map HVec.coords)), hLl]
  have hGr : elim.rowsLen grp.length
      (elim.gramM (grp.map HVec.coords)) := by
    have h := elim.rowsLen_of_sqAt
      (elim.gram_sqAt (grp.map HVec.coords))
    rw [hLl] at h
    exact h
  have hstep : ∀ j, j < grp.length →
      (c₀ * dotG (dact p q
          (ground.getAt (⟨[], []⟩ : HVec) grp j)) a).oneValue
        (ground.getAt BPair.unit
          (poly.neg (elim.matVec
            (elim.gramM (grp.map HVec.coords)) cs)) j) := by
    intro j hj
    have hyc : (ground.getAt (⟨[], []⟩ : HVec) grp j).content
        = b.content := hcont _ (ground.mem_getAt _ grp j hj)
    have hyl : (ground.getAt (⟨[], []⟩ : HVec) grp j).coords.length
        = n := by
      have h := elim.rowsLen_getAt (grp.map HVec.coords) j hrows
        (by rw [hLl]; exact hj)
      rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
        HVec.coords grp j hj] at h
      exact h
    have hbeta : (c₀ * elim.dotP
        (ground.getAt (⟨[], []⟩ : HVec) grp j).coords
        (act p q a).coords).oneValue
        (ground.getAt BPair.unit
          (elim.matVec (elim.gramM (grp.map HVec.coords)) cs) j) :=
      span_pair_row grp (act p q a).coords c₀ cs n hrows hone j hj
    have hev := ev_equiv p q b.content hqb hpq hocc
      (ground.getAt (⟨[], []⟩ : HVec) grp j).coords a.coords
      (by rw [hyl, hnm]) (by rw [hg1]; exact hsa)
    rw [show (⟨b.content,
        (ground.getAt (⟨[], []⟩ : HVec) grp j).coords⟩ : HVec)
        = ground.getAt (⟨[], []⟩ : HVec) grp j from by rw [← hyc],
      show (⟨moveAt q p b.content, a.coords⟩ : HVec) = a
        from by rw [hg1]] at hev
    rw [show dotG (dact p q
          (ground.getAt (⟨[], []⟩ : HVec) grp j)) a
        = elim.dotP (dact p q
          (ground.getAt (⟨[], []⟩ : HVec) grp j)).coords a.coords
        from by
      show (if (dact p q
            (ground.getAt (⟨[], []⟩ : HVec) grp j)).content
          = a.content then _ else BPair.unit) = _
      rw [if_pos (show (dact p q
          (ground.getAt (⟨[], []⟩ : HVec) grp j)).content
            = a.content from by
        show moveAt q p
          (ground.getAt (⟨[], []⟩ : HVec) grp j).content = a.content
        rw [hyc]
        exact hg1)]]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c₀)
        (ground.oneOfUnit (show (elim.dotP (dact p q
              (ground.getAt (⟨[], []⟩ : HVec) grp j)).coords a.coords
            + (elim.dotP
              (ground.getAt (⟨[], []⟩ : HVec) grp j).coords
              (act p q a).coords).swap.swap).oneValue BPair.unit
          from hev))) ?_
    rw [BPair.mul_swap,
      show poly.neg (elim.matVec
          (elim.gramM (grp.map HVec.coords)) cs)
        = (elim.matVec (elim.gramM (grp.map HVec.coords)) cs).map
          BPair.swap from rfl,
      ground.getAt_map BPair.unit BPair.unit BPair.swap _ j
        (by rw [elim.matVec_length, hGl]; exact hj)]
    exact ground.swap_congr hbeta
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (ground.foldB_mul_left c₀ _ (List.range grp.length))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => ground.getAt BPair.unit
          (poly.neg (elim.matVec
            (elim.gramM (grp.map HVec.coords)) cs)) j
        * ground.getAt BPair.unit
          (elim.adjP (elim.gramM (grp.map HVec.coords))
            (grp.map (fun w => dotG (slotT T w) b))) j)
      (List.range grp.length) (fun j hj0 => ?_)) ?_
  · rw [← BPair.mul_assoc]
    exact BPair.mul_congr (hstep j (ground.ltOfMem hj0))
      (BPair.oneValue_refl _)
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (fold_dotP _ _ grp.length
        (by rw [poly.length_neg, elim.matVec_length, hGl])
        (by rw [elim.length_adjP, hGl]))) ?_
    rw [elim.dotP_swap_left]
    refine ground.swap_congr ?_
    rw [elim.dotP_comm
      (elim.matVec (elim.gramM (grp.map HVec.coords)) cs)
      (elim.adjP (elim.gramM (grp.map HVec.coords))
        (grp.map (fun w => dotG (slotT T w) b)))]
    refine BPair.oneValue_trans
      (elim.dotP_matVec grp.length _
        (elim.gramM (grp.map HVec.coords)) cs hGr hcsl
        (by rw [elim.length_adjP, hGl])) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ cs
        (adjP_solve (grp.map HVec.coords) _ grp.length hLl
          (by rw [ground.length_map]))) ?_
    rw [elim.dotP_comm
      (elim.vecScale (elim.detL (elim.gramM (grp.map HVec.coords)))
        (grp.map (fun w => dotG (slotT T w) b))) cs]
    exact elim.dotP_vecScale_right cs _ _

/-- The block's term-two factor cleared at the span's own scalar:
the equivariance transports the letter across the slot and the
transported image reads the coefficients against the second slots'
pairings. -/
private theorem term2_clear (T : List Nat → elim.Mat)
    (grp : List HVec) (p q : Nat) (a b : HVec) (c₀ : BPair)
    (cs : List BPair) (n : Nat)
    (hcont : ∀ w ∈ grp, w.content = b.content)
    (hrows : elim.rowsLen n (grp.map HVec.coords))
    (hone : poly.oneValue (elim.vecScale c₀ (act p q a).coords)
      (elim.combo n cs (grp.map HVec.coords)))
    (hg2 : moveAt p q a.content = b.content)
    (hmv : poly.oneValue (act p q (slotT T a)).coords
      (elim.matVec (T (moveAt p q a.content))
        (act p q a).coords)) :
    (c₀ * dotG (act p q (slotT T a)) b).oneValue
      (elim.dotP cs (grp.map (fun w => dotG (slotT T w) b))) := by
  rw [slot_map T grp b hcont,
    show dotG (act p q (slotT T a)) b
      = elim.dotP (act p q (slotT T a)).coords b.coords from by
    show (if (act p q (slotT T a)).content = b.content
        then _ else BPair.unit) = _
    rw [if_pos (show (act p q (slotT T a)).content = b.content
      from hg2)]]
  rw [hg2] at hmv
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl c₀)
      (elim.dotP_oneValue_left _ _ b.coords hmv)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (mapPair_scale (T b.content) b.coords c₀
      (act p q a).coords)) ?_
  refine BPair.oneValue_trans
    (mapPair_congr (T b.content) b.coords _ _ hone) ?_
  exact mapPair_combo (T b.content) b.coords n cs
    (grp.map HVec.coords) hrows

/-- The equivariant map's invariant read: a letter pair's Leibniz
image at the coevaluation's second slot under the map pairs the
member against every second vector at the sum's unit — the read
collects at the adjugate identity twice, the member's own column
reading the determinant against the map's moved value with the
equivariance transporting the letter across the slot, the first
slots walked across the transpose identity to the members'
pairings against the member's letter image, and the image's
cleared combination over the list's span (`elim.span_elim`)
reading the adjugate solve at the determinant against the
combination's coefficients, the map's value additive and
scale-reading across the members, the two reads joined at partners
and the clearing withdrawn at the product's injectivity
(`lem:dualread`(i)'s backward sentence at `lem:lowerspan`'s solve
and span reads). -/
theorem mapInv_equiv (T : List Nat → elim.Mat) (Y : List HVec)
    (p q : Nat) (a b : HVec)
    (hpb : p < b.content.length) (hqb : q < b.content.length)
    (hpq : ¬ p = q) (hsa : sized a) (ha : a ∈ Y)
    (hmv : poly.oneValue
      (act p q (⟨a.content,
        elim.matVec (T a.content) a.coords⟩ : HVec)).coords
      (elim.matVec (T (moveAt p q a.content)) (act p q a).coords))
    (hcl : elim.spanRel (act p q a).coords.length
      (blockcount.groupAt Y (act p q a).content)
      (act p q a).coords) :
    (movedAt (mapInv T Y) p q a b).oneValue BPair.unit := by
  have haD : ground.countOf a.content
      (ground.dedupL (Y.map HVec.content)) = 1 :=
    ground.countOf_dedupL_one (ground.mem_map_to HVec.content ha)
  have hcb : ∀ w ∈ Y.filter (fun w => w.content == b.content),
      w.content = b.content := fun w hw =>
    ground.listBeqEq (ground.mem_filter_of _ _ _ hw).2
  have hgc : ∀ j,
      j < (Y.filter (fun w => w.content == b.content)).length →
      (ground.getAt (⟨[], []⟩ : HVec)
        (Y.filter (fun w => w.content == b.content)) j).content
        = b.content := fun j hj =>
    hcb _ (ground.mem_getAt _ _ j hj)
  rw [movedAt_fold (mapInv T Y) p q a b,
    show mapInv T Y = (coevData Y).map (fun t =>
      (t.1, t.2.1, slotT T t.2.2)) from rfl,
    ground.map_map, ground.map_map, elim.dotP_map_pair,
    coevData_flat Y]
  refine BPair.oneValue_trans
    (ground.famFold_flatMap_ov ground.bpairFoldLaws
      _ (coevBody Y) (ground.dedupL (Y.map HVec.content))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun mu =>
        (if mu = b.content
          then coScale Y b.content
            * ground.famFold BPair.add BPair.unit (fun j =>
              dotG (dact p q (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == b.content)) j)) a
                * ground.getAt BPair.unit
                  (elim.adjP (elim.gramM
                    ((Y.filter (fun w => w.content == b.content)).map
                      HVec.coords))
                    ((Y.filter (fun w => w.content == b.content)).map
                      (fun w => dotG (slotT T w) b))) j)
              (List.range
                (Y.filter (fun w => w.content == b.content)).length)
          else BPair.unit)
        + (if mu = a.content
          then detAll Y * dotG (act p q (slotT T a)) b
          else BPair.unit))
      (ground.dedupL (Y.map HVec.content)) (fun mu hmu => ?_)) ?_
  · have h1 : ground.countOf mu
        (ground.dedupL (Y.map HVec.content)) = 1 :=
      Nat.le_antisymm
        (ground.countOf_dedupL_le mu (Y.map HVec.content)) hmu
    refine BPair.oneValue_trans
      (ground.famFold_flatMap_ov ground.bpairFoldLaws
        _ _ (List.range
          (Y.filter (fun w => w.content == mu)).length)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _ _
        (List.range (Y.filter (fun w => w.content == mu)).length)
        (fun j _ => BPair.oneValue_of_eq
          (ground.famFold_map BPair.add BPair.unit _ _
            (List.range
              (Y.filter (fun w => w.content == mu)).length)))) ?_
    exact group_readT T (Y.filter (fun w => w.content == mu)) mu
      (fun w hw => ground.listBeqEq
        ((ground.mem_filter_of _ Y w hw).2))
      (coScale Y mu) (detAll Y) _ (scale_detAll Y mu h1) p q a b
      (fun he => ground.mem_filter_to _ ha
        (by rw [he]; exact ground.listEqBeq a.content))
      (fun he => by rw [he])
  · refine BPair.oneValue_trans
      (ground.foldB_add _ _ (ground.dedupL (Y.map HVec.content))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (ground.foldB_indicator b.content _
          (ground.dedupL (Y.map HVec.content)))
        (BPair.oneValue_trans
          (ground.foldB_indicator a.content
            (detAll Y * dotG (act p q (slotT T a)) b)
            (ground.dedupL (Y.map HVec.content)))
          (by rw [haD]; exact BPair.ofNat_one_mul _))) ?_
    have hnull : ∀ (h : ∀ j,
        j < (Y.filter (fun w => w.content == b.content)).length →
        (dotG (dact p q (ground.getAt (⟨[], []⟩ : HVec)
          (Y.filter (fun w => w.content == b.content)) j)) a).oneValue
          BPair.unit),
        (BPair.ofNat (ground.countOf b.content
              (ground.dedupL (Y.map HVec.content)))
            * (coScale Y b.content
              * ground.famFold BPair.add BPair.unit (fun j =>
                dotG (dact p q (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == b.content)) j)) a
                  * ground.getAt BPair.unit
                    (elim.adjP (elim.gramM
                      ((Y.filter (fun w => w.content == b.content)).map
                        HVec.coords))
                      ((Y.filter (fun w => w.content == b.content)).map
                        (fun w => dotG (slotT T w) b))) j)
                (List.range
                  (Y.filter
                    (fun w => w.content == b.content)).length))).oneValue
          BPair.unit := by
      intro h
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (ground.foldB_nullRange _ _ (fun j hj =>
                BPair.oneValue_trans
                  (BPair.mul_congr (h j hj)
                    (BPair.oneValue_refl _))
                  (BPair.unit_mul _))))
            (BPair.mul_unit _))) ?_
      exact BPair.mul_unit _
    by_cases hg1 : (dact p q b).content = a.content
    · have hg1' : moveAt q p b.content = a.content := hg1
      by_cases hocc : 0 < ground.getAt 0 b.content p
      · have hg2 : moveAt p q a.content = b.content := by
          rw [← hg1']
          exact moveAt_round_at p q b.content hocc
        have hzc : (act p q a).content = b.content := hg2
        have hcl2 : elim.spanRel (act p q a).coords.length
            ((Y.filter (fun w => w.content == b.content)).map
              HVec.coords) (act p q a).coords := by
          have hgrp : blockcount.groupAt Y (act p q a).content
              = (Y.filter (fun w => w.content == b.content)).map
                HVec.coords := by
            show ((Y.filter
                (fun w => w.content == (act p q a).content)).map
              HVec.coords) = _
            rw [hzc]
          rw [hgrp] at hcl
          exact hcl
        have hnm : (act p q a).coords.length
            = (places.monomialsAt b.content).length := by
          have h := blockcount.act_sized p q a
          rw [show (act p q a).coords.length
              = (places.monomialsAt (act p q a).content).length
            from h, hzc]
        match elim.span_elim hcl2 with
        | ⟨c₀, cs, hc₀, hcsl, hone⟩ =>
          have hcsl' : cs.length
              = (Y.filter (fun w => w.content == b.content)).length := by
            rw [hcsl, ground.length_map]
          by_cases hbY : 0 < ground.countOf b.content
            (ground.dedupL (Y.map HVec.content))
          · have hbD : ground.countOf b.content
                (ground.dedupL (Y.map HVec.content)) = 1 :=
              Nat.le_antisymm
                (ground.countOf_dedupL_le b.content
                  (Y.map HVec.content)) hbY
            have hscale : coScale Y b.content
                * elim.detL (elim.gramM
                  ((Y.filter (fun w => w.content == b.content)).map
                    HVec.coords)) = detAll Y :=
              scale_detAll Y b.content hbD
            rw [hbD]
            refine BPair.oneValue_trans
              (BPair.add_congr (BPair.ofNat_one_mul _)
                (BPair.oneValue_refl _)) ?_
            refine ground.mulCancel hc₀ ?_
            refine BPair.oneValue_trans ?_
              (BPair.oneValue_symm (BPair.mul_unit c₀))
            rw [BPair.left_distrib]
            refine BPair.oneValue_trans
              (BPair.add_congr ?_ ?_)
              (BPair.swap_add_null (BPair.oneValue_refl
                (detAll Y * elim.dotP cs
                  ((Y.filter (fun w => w.content == b.content)).map
                    (fun w => dotG (slotT T w) b)))))
            · rw [← BPair.mul_assoc,
                BPair.mul_comm c₀ (coScale Y b.content),
                BPair.mul_assoc]
              refine BPair.oneValue_trans
                (BPair.mul_congr (BPair.oneValue_refl _)
                  (blk_clear T
                    (Y.filter (fun w => w.content == b.content))
                    p q a b c₀ cs (act p q a).coords.length hcb
                    hcl2.1 hcsl' hone hqb hpq hocc hg1' hsa hnm)) ?_
              rw [BPair.mul_swap, ← BPair.mul_assoc, hscale]
              exact BPair.oneValue_refl _
            · rw [← BPair.mul_assoc, BPair.mul_comm c₀ (detAll Y),
                BPair.mul_assoc]
              refine BPair.mul_congr (BPair.oneValue_refl _) ?_
              exact term2_clear T
                (Y.filter (fun w => w.content == b.content))
                p q a b c₀ cs (act p q a).coords.length hcb hcl2.1
                hone hg2 hmv
          · have hbD : ground.countOf b.content
                (ground.dedupL (Y.map HVec.content)) = 0 := by
              match hcnt : ground.countOf b.content
                  (ground.dedupL (Y.map HVec.content)) with
              | 0 => rfl
              | n + 1 =>
                exact absurd (by rw [hcnt]; exact Nat.succ_pos n) hbY
            have hfil : Y.filter (fun w => w.content == b.content)
                = [] := by
              refine ground.filter_false _ Y (fun w hw => ?_)
              match hb2 : (w.content == b.content) with
              | false => rfl
              | true =>
                exact absurd (ground.countOf_pos_of_mem
                  (ground.mem_dedupL (by
                    rw [← ground.listBeqEq hb2]
                    exact ground.mem_map_to HVec.content hw))) hbY
            refine BPair.oneValue_trans
              (BPair.add_congr
                (by rw [hbD]; exact BPair.unit_mul _)
                ?_)
              (BPair.unit_add BPair.unit)
            refine ground.mulCancel hc₀ ?_
            refine BPair.oneValue_trans ?_
              (BPair.oneValue_symm (BPair.mul_unit c₀))
            rw [← BPair.mul_assoc, BPair.mul_comm c₀ (detAll Y),
              BPair.mul_assoc]
            refine BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl _)
                (term2_clear T
                  (Y.filter (fun w => w.content == b.content))
                  p q a b c₀ cs (act p q a).coords.length hcb
                  hcl2.1 hone hg2 hmv)) ?_
            rw [hfil]
            show (detAll Y * elim.dotP cs
              (([] : List HVec).map
                (fun w => dotG (slotT T w) b))).oneValue BPair.unit
            rw [show (([] : List HVec).map
                (fun w => dotG (slotT T w) b))
              = ([] : List BPair) from rfl, elim.dotP_nil_right]
            exact BPair.mul_unit _
      · have hz : ground.getAt 0 b.content p = 0 := by
          match he : ground.getAt 0 b.content p with
          | 0 => rfl
          | n + 1 =>
            exact absurd (by rw [he]; exact Nat.succ_pos n) hocc
        have hng2 : ¬ (moveAt p q a.content = b.content) := by
          intro hg2
          have hg2' : moveAt p q a.content = b.content := hg2
          rw [← hg1'] at hg2'
          have hcomp : moveAt p q (moveAt q p b.content)
              = bumpAt p b.content := by
            show bumpAt p (dipAt q (bumpAt q (dipAt p b.content)))
              = bumpAt p b.content
            rw [ground.dipAt_of_zero p b.content hz,
              ground.dipAt_bumpAt_self]
          rw [hcomp] at hg2'
          have hgc2 := congrArg (fun l => ground.getAt 0 l p) hg2'
          rw [ground.getAt_bumpAt_self p b.content hpb, hz] at hgc2
          exact Nat.noConfusion hgc2
        refine BPair.oneValue_trans
          (BPair.add_congr (hnull (fun j hj => ?_)) ?_)
          (BPair.unit_add BPair.unit)
        · by_cases hg : (dact p q (ground.getAt (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == b.content)) j)).content
              = a.content
          · rw [show dotG (dact p q (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == b.content)) j)) a
                = elim.dotP (dact p q (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter
                    (fun w => w.content == b.content)) j)).coords
                  a.coords from by
              show (if (dact p q (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter
                    (fun w => w.content == b.content)) j)).content
                = a.content then _ else BPair.unit) = _
              rw [if_pos hg]]
            refine elim.dotP_null_tail_left _ _ ?_
            show poly.unitTail (poly.neg (elim.matVec
              (units.matUnitAt (moveAt q p (ground.getAt
                  (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == b.content))
                  j).content)
                (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == b.content))
                  j).content q p)
              (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == b.content))
                j).coords))
            refine poly.unitTail_swapMap _ ?_
            exact units.matVec_null_unocc _ _ q p
              (by rw [hgc j hj]; exact hz) _
          · refine BPair.oneValue_of_eq ?_
            show (if (dact p q (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter
                  (fun w => w.content == b.content)) j)).content
              = a.content then _ else BPair.unit) = BPair.unit
            rw [if_neg hg]
        · refine BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_of_eq ?_)) (BPair.mul_unit _)
          show (if (act p q (slotT T a)).content = b.content
            then _ else BPair.unit) = BPair.unit
          rw [if_neg (show ¬ ((act p q (slotT T a)).content
            = b.content) from hng2)]
    · refine BPair.oneValue_trans
        (BPair.add_congr (hnull (fun j hj => ?_)) ?_)
        (BPair.unit_add BPair.unit)
      · refine BPair.oneValue_of_eq ?_
        show (if (dact p q (ground.getAt (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == b.content)) j)).content
          = a.content then _ else BPair.unit) = BPair.unit
        rw [if_neg (show ¬ ((dact p q (ground.getAt
            (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == b.content)) j)).content
              = a.content) from by
          show ¬ (moveAt q p (ground.getAt (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == b.content)) j).content
              = a.content)
          rw [hgc j hj]
          exact hg1)]
      · by_cases hg2 : moveAt p q a.content = b.content
        · have hnq : ground.getAt 0 a.content q = 0 := by
            match he : ground.getAt 0 a.content q with
            | 0 => rfl
            | n + 1 =>
              have hocc2 : 0 < ground.getAt 0 a.content q := by
                rw [he]
                exact Nat.succ_pos n
              have hrt := moveAt_round_at q p a.content hocc2
              rw [hg2] at hrt
              exact absurd
                (show (dact p q b).content = a.content from hrt) hg1
          refine BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) ?_)
            (BPair.mul_unit _)
          rw [show dotG (act p q (slotT T a)) b
              = elim.dotP (act p q (slotT T a)).coords b.coords
              from by
            show (if (act p q (slotT T a)).content = b.content
              then _ else BPair.unit) = _
            rw [if_pos (show (act p q (slotT T a)).content
              = b.content from hg2)]]
          refine elim.dotP_null_tail_left _ _ ?_
          show poly.unitTail (elim.matVec
            (units.matUnitAt (moveAt p q (slotT T a).content)
              (slotT T a).content p q) (slotT T a).coords)
          exact units.matVec_null_unocc _ _ p q hnq _
        · refine BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_of_eq ?_)) (BPair.mul_unit _)
          show (if (act p q (slotT T a)).content = b.content
            then _ else BPair.unit) = BPair.unit
          rw [if_neg (show ¬ ((act p q (slotT T a)).content
            = b.content) from hg2)]

/-- The map's datum sits at matched contents, each entry's two
slots at one content — the invariant's family clause, the
coevaluation's per-content grid with the map's value at its
member's own content (`lem:dualread`(i)'s backward sentence, the
family at matched contents). -/
theorem mapInv_matched (T : List Nat → elim.Mat) (Y : List HVec) :
    ∀ t ∈ mapInv T Y, (t.2.2).content = (t.2.1).content := by
  intro t ht
  match ground.mem_map_of _ _ t ht with
  | ⟨u, hu, hut⟩ =>
    rw [← hut]
    show u.2.2.content = u.2.1.content
    rw [coevData_flat] at hu
    match ground.mem_flatMap_of _ _ u hu with
    | ⟨mu, _, hmu⟩ =>
      rw [coevBody_slot2 Y mu u hmu, coevBody_slot1 Y mu u hmu]

/-! `lem:dualread`(i)'s map data: the matrix family at
`lem:blockirr`'s format, its action the family's own map. -/

/-- The map's matrix family: one matrix per content, row `r` the
first slots' combination at the coefficients against the second
slots' `r`-th coordinates — `lem:dualread`(i)'s map data at
`lem:blockirr`'s matrix families. -/
def mapMat (P : List (BPair × HVec × HVec)) (mu : List Nat) :
    elim.Mat :=
  (List.range (places.monomialsAt mu).length).map (fun r =>
    elim.combo (places.monomialsAt mu).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.1 * ground.getAt BPair.unit t.2.2.coords r))
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.1.coords)))

/-- The filtered first slots' width read at the format's frame. -/
private theorem filterRowsF (P : List (BPair × HVec × HVec))
    (mu : List Nat)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec)) :
    elim.rowsLen (places.monomialsAt mu).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.1.coords)) := by
  refine elim.rowsLen_map _ _ _ (fun t ht => ?_)
  match ground.mem_filter_of _ P t ht with
  | ⟨htP, htc⟩ =>
    rw [(hsz t htP).1, ground.listBeqEq htc]

/-- The filtered second slots' width read at the matched
contents. -/
private theorem filterRowsW (P : List (BPair × HVec × HVec))
    (mu : List Nat)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content) :
    elim.rowsLen (places.monomialsAt mu).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords)) := by
  refine elim.rowsLen_map _ _ _ (fun t ht => ?_)
  match ground.mem_filter_of _ P t ht with
  | ⟨htP, htc⟩ =>
    rw [(hsz t htP).2, ← hm t htP, ground.listBeqEq htc]

/-- The matrix family's action is the map's own value at the
format's frame: entry by entry, the row's pairing and the
combination's coordinate collect to one index fold of the members'
products, the two orders exchanged at the entries. -/
theorem mapMat_read (P : List (BPair × HVec × HVec)) (mu : List Nat)
    (v : List BPair)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content) :
    poly.oneValue (elim.matVec (mapMat P mu) v)
      (mapAt P (⟨mu, v⟩ : HVec)).coords := by
  have hF := filterRowsF P mu hsz
  have hW := filterRowsW P mu hsz hm
  have hMl : (mapMat P mu).length = (places.monomialsAt mu).length :=
    ground.length_mapRange _ _
  refine poly.ov_of_getAt (fun r => ?_)
  by_cases hr : r < (places.monomialsAt mu).length
  · rw [show elim.matVec (mapMat P mu) v
        = (mapMat P mu).map (fun row => elim.dotN row v) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit
        (fun row => elim.dotN row v) (mapMat P mu) r
        (by rw [hMl]; exact hr),
      show mapMat P mu
        = (List.range (places.monomialsAt mu).length).map (fun j =>
          elim.combo (places.monomialsAt mu).length
            ((P.filter (fun t => t.2.1.content == mu)).map
              (fun t => t.1 * ground.getAt BPair.unit t.2.2.coords j))
            ((P.filter (fun t => t.2.1.content == mu)).map
              (fun t => t.2.1.coords))) from rfl,
      ground.getAt_map (0 : Nat) ([] : List BPair) _
        (List.range (places.monomialsAt mu).length) r
        (by rw [ground.length_range]; exact hr),
      ground.getAt_range _ r hr]
    refine BPair.oneValue_trans (elim.dotN_dotP _ v) ?_
    rw [elim.dotP_comm]
    refine BPair.oneValue_trans
      (elim.dotP_combo _ _ v _ hF) ?_
    rw [ground.map_map, elim.dotP_map_pair]
    refine BPair.oneValue_symm ?_
    rw [mapAt_coords,
      show (⟨mu, v⟩ : HVec).content = mu from rfl,
      show (⟨mu, v⟩ : HVec).coords = v from rfl]
    refine BPair.oneValue_trans
      (elim.combo_getAt _ _ _ r hW hr) ?_
    rw [ground.map_map, elim.dotP_map_pair]
    refine BPair.oneValue_of_eq
      (ground.famFold_congr_all _ _ _ _ (fun t => ?_) _)
    rw [elim.dotP_comm _ v, BPair.mul_right_comm]
  · rw [ground.getAt_over BPair.unit _ r (by
      rw [elim.matVec_length, hMl]
      exact Nat.le_of_not_lt hr),
    ground.getAt_over BPair.unit _ r (by
      rw [mapAt_coords, elim.length_combo _ _ _ hW]
      exact Nat.le_of_not_lt hr)]
    exact BPair.oneValue_refl _

/-! `lem:dualread`(i)'s forward tier: the invariance read at the
stated argument against the carrier's stated list joins two
crossed folds, the first the map's value at the moved argument
through the evaluation's equivariance and the second the moved
value's own pairing, and the moved images read one value at the
pairing's definiteness, the moved map value inside the carrier's
moved group at the list's settled images. -/

/-- The dual image's pairing against the argument is the balance
partner of the member's pairing against the moved argument: the
evaluation's equivariance at matched widths, the two guards
refusing together at a width gap. -/
private theorem dact_walk (p q : Nat) (a f : HVec)
    (hpa : p < a.content.length) (hqa : q < a.content.length)
    (hpq : ¬ p = q) (hsa : sized a) (hsf : sized f) :
    (dotG (dact p q f) a).oneValue ((dotG f (act p q a)).swap) := by
  by_cases hlen : f.content.length = a.content.length
  · refine ground.oneOfUnit ?_
    rw [BPair.swap_swap, dotG_comm f (act p q a)]
    exact ev_equivG p q a f (by rw [hlen]; exact hpa)
      (by rw [hlen]; exact hqa) hpq hsa hsf
  · rw [show dotG (dact p q f) a = BPair.unit from by
      show (if (dact p q f).content = a.content then _ else _) = _
      refine if_neg (fun hc => hlen ?_)
      have hc' : moveAt q p f.content = a.content := hc
      rw [← hc', length_moveAt],
    show dotG f (act p q a) = BPair.unit from by
      show (if f.content = (act p q a).content then _ else _) = _
      refine if_neg (fun hc => hlen ?_)
      have hc' : f.content = moveAt p q a.content := hc
      rw [hc', length_moveAt]]
    exact BPair.oneValue_refl _

/-- A family fold whose off-filter members read the sum's unit
collapses to the filtered fold, the vacant terms withdrawing. -/
private theorem dotP_filter_collapse
    (pred : (BPair × HVec × HVec) → Bool)
    (g : (BPair × HVec × HVec) → BPair) :
    ∀ P : List (BPair × HVec × HVec),
      (∀ t ∈ P, pred t = false → (g t).oneValue BPair.unit) →
      (elim.dotP (P.map (fun t => t.1)) (P.map g)).oneValue
        (elim.dotP ((P.filter pred).map (fun t => t.1))
          ((P.filter pred).map g))
  | [], _ => BPair.oneValue_refl _
  | t :: rest, h => by
    cases hp : pred t with
    | true =>
      rw [ground.filter_cons_true hp]
      show (t.1 * g t + elim.dotP (rest.map _) (rest.map g)).oneValue
        (t.1 * g t + elim.dotP ((rest.filter pred).map _)
          ((rest.filter pred).map g))
      exact BPair.add_congr (BPair.oneValue_refl _)
        (dotP_filter_collapse pred g rest
          (fun x hx hxf => h x (List.Mem.tail t hx) hxf))
    | false =>
      rw [ground.filter_cons_false hp]
      show (t.1 * g t + elim.dotP (rest.map _) (rest.map g)).oneValue
        (elim.dotP ((rest.filter pred).map _)
          ((rest.filter pred).map g))
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (h t (List.Mem.head rest) hp))
            (BPair.mul_unit t.1))
          (dotP_filter_collapse pred g rest
            (fun x hx hxf => h x (List.Mem.tail t hx) hxf))) ?_
      exact BPair.unit_add _

/-- The map's pairing fold: the family's own fold at the argument's
pairings against the further vector, the cross-content members
entering at the grading's unit — the fold the argument's own
content group with every cross-content pairing the sum's unit. -/
private theorem mapAt_pair (P : List (BPair × HVec × HVec))
    (z w : HVec)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content)
    (hw : w.content = z.content) :
    (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t => dotG t.2.1 z * dotG t.2.2 w))).oneValue
      (dotG (mapAt P z) w) := by
  refine BPair.oneValue_trans
    (dotP_filter_collapse (fun t => t.2.1.content == z.content) _ P
      (fun t _ htf => ?_)) ?_
  · rw [show dotG t.2.1 z = BPair.unit from by
      show (if t.2.1.content = z.content then _ else _) = _
      refine if_neg (fun hc => ?_)
      rw [hc, ground.listEqBeq] at htf
      exact Bool.noConfusion htf,
      BPair.mul_comm]
    exact BPair.mul_unit _
  · rw [show dotG (mapAt P z) w = elim.dotP (mapAt P z).coords w.coords
      from by
      show (if (mapAt P z).content = w.content then _ else _) = _
      exact if_pos (show z.content = w.content from hw.symm),
      mapAt_coords]
    refine BPair.oneValue_symm ?_
    rw [elim.dotP_comm]
    refine BPair.oneValue_trans
      (elim.dotP_combo _ _ w.coords _ (filterRowsW P z.content hsz hm))
        ?_
    rw [ground.map_map, elim.dotP_map_pair, elim.dotP_map_pair]
    refine BPair.oneValue_of_eq
      (ground.famFold_congr_members _ _ _ _ _ (fun t ht => ?_))
    match ground.mem_filter_of _ P t
      (ground.mem_of_countOf_pos t _ ht) with
    | ⟨htP, htc⟩ =>
      have hce : t.2.1.content = z.content := ground.listBeqEq htc
      rw [show dotG t.2.1 z = elim.dotP t.2.1.coords z.coords from by
          show (if t.2.1.content = z.content then _ else _) = _
          exact if_pos hce,
        show dotG t.2.2 w = elim.dotP t.2.2.coords w.coords from by
          show (if t.2.2.content = w.content then _ else _) = _
          exact if_pos (by rw [← hm t htP, hce, hw]),
        elim.dotP_comm w.coords t.2.2.coords, ← BPair.mul_assoc]

/-- The moved form splits into the map's two moved reads: the dual
arm collects across the transpose walk to the moved argument's map
value paired against the member, the action arm to the moved value's
own pairing — the two crossed folds, invariance-free. -/
private theorem movedAt_two_reads (P : List (BPair × HVec × HVec))
    (p q : Nat) (a b : HVec)
    (hpa : p < a.content.length) (hqa : q < a.content.length)
    (hpq : ¬ p = q) (hsa : sized a)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content)
    (hbc : b.content = moveAt p q a.content) :
    (movedAt P p q a b).oneValue
      ((elim.dotP b.coords (mapAt P (act p q a)).coords).swap
        + elim.dotP b.coords (act p q (mapAt P a)).coords) := by
  have hsplit : (movedAt P p q a b).oneValue
      (elim.dotP (P.map (fun t => t.1))
        (P.map (fun t => dotG (dact p q t.2.1) a * dotG t.2.2 b))
      + elim.dotP (P.map (fun t => t.1))
        (P.map (fun t => dotG t.2.1 a * dotG (act p q t.2.2) b))) :=
    BPair.oneValue_trans
      (BPair.oneValue_of_eq
        ((movedAt_fold P p q a b).trans
          (congrArg (elim.dotP (P.map (fun t => t.1)))
            (elim.mapAdd _ _ P).symm)))
      (elim.dotP_vecAdd_right _ _ _
        (by rw [ground.length_map, ground.length_map]))
  have hA1 : (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t =>
        dotG (dact p q t.2.1) a * dotG t.2.2 b))).oneValue
      (elim.dotP (P.map (fun t => t.1))
        (P.map (fun t =>
          ((dotG t.2.1 (act p q a)) * dotG t.2.2 b).swap))) :=
    elim.dotP_oneValue_right _ _ _
      (poly.oneValue_map _ _ P (fun t ht =>
        BPair.oneValue_trans
          (BPair.mul_congr
            (dact_walk p q a t.2.1 hpa hqa hpq hsa (hsz t ht).1)
            (BPair.oneValue_refl (dotG t.2.2 b)))
          (BPair.oneValue_of_eq (BPair.swap_mul _ _))))
  have hA2 : elim.dotP (P.map (fun t => t.1))
      (P.map (fun t =>
        ((dotG t.2.1 (act p q a)) * dotG t.2.2 b).swap))
      = (elim.dotP (P.map (fun t => t.1))
        (P.map (fun t =>
          dotG t.2.1 (act p q a) * dotG t.2.2 b))).swap :=
    (congrArg (elim.dotP (P.map (fun t => t.1)))
      (ground.map_map _ BPair.swap P).symm).trans
      (elim.dotP_swapMap _ _)
  have hA3 : (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t =>
        dotG t.2.1 (act p q a) * dotG t.2.2 b))).oneValue
      (dotG (mapAt P (act p q a)) b) :=
    mapAt_pair P (act p q a) b hsz hm hbc
  have hA4 : dotG (mapAt P (act p q a)) b
      = elim.dotP b.coords (mapAt P (act p q a)).coords := by
    rw [show dotG (mapAt P (act p q a)) b
        = elim.dotP (mapAt P (act p q a)).coords b.coords from by
      show (if _ = b.content then _ else _) = _
      exact if_pos hbc.symm]
    exact elim.dotP_comm _ _
  have hA : (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t =>
        dotG (dact p q t.2.1) a * dotG t.2.2 b))).oneValue
      ((elim.dotP b.coords (mapAt P (act p q a)).coords).swap) :=
    BPair.oneValue_trans hA1
      (BPair.oneValue_trans (BPair.oneValue_of_eq hA2)
        (ground.swap_congr
          (BPair.oneValue_trans hA3 (BPair.oneValue_of_eq hA4))))
  have hB1 : (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t =>
        dotG t.2.1 a * dotG (act p q t.2.2) b))).oneValue
      (elim.dotP
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.1))
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => dotG t.2.1 a * dotG (act p q t.2.2) b))) :=
    dotP_filter_collapse _ _ P (fun t _ htf => by
      rw [show dotG t.2.1 a = BPair.unit from by
        show (if t.2.1.content = a.content then _ else _) = _
        refine if_neg (fun hc => ?_)
        rw [hc, ground.listEqBeq] at htf
        exact Bool.noConfusion htf,
        BPair.mul_comm]
      exact BPair.mul_unit _)
  have hB2 : (elim.dotP b.coords
      (act p q (mapAt P a)).coords).oneValue
      (elim.dotP b.coords
        (elim.combo (units.matUnitAt (moveAt p q a.content)
            a.content p q).length
          ((P.filter (fun t => t.2.1.content == a.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords a.coords))
          (((P.filter (fun t => t.2.1.content == a.content)).map
            (fun t => t.2.2.coords)).map
            (elim.matVec (units.matUnitAt (moveAt p q a.content)
              a.content p q))))) :=
    elim.dotP_oneValue_right _ _ _
      (elim.matVec_combo _ _ _ _ (filterRowsW P a.content hsz hm))
  have hB3 : (elim.dotP b.coords
      (elim.combo (units.matUnitAt (moveAt p q a.content)
          a.content p q).length
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords a.coords))
        (((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.2.2.coords)).map
          (elim.matVec (units.matUnitAt (moveAt p q a.content)
            a.content p q))))).oneValue
      (elim.dotP
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords a.coords))
        ((((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.2.2.coords)).map
          (elim.matVec (units.matUnitAt (moveAt p q a.content)
            a.content p q))).map
          (fun row => elim.dotP b.coords row))) :=
    elim.dotP_combo _ _ b.coords _
      (elim.rowsLen_map _ _ _ (fun r _ => elim.matVec_length _ r))
  have hB4 : (elim.dotP
      ((P.filter (fun t => t.2.1.content == a.content)).map
        (fun t => t.1 * elim.dotP t.2.1.coords a.coords))
      ((((P.filter (fun t => t.2.1.content == a.content)).map
        (fun t => t.2.2.coords)).map
        (elim.matVec (units.matUnitAt (moveAt p q a.content)
          a.content p q))).map
        (fun row => elim.dotP b.coords row)))
      = elim.dotP
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.1))
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => dotG t.2.1 a * dotG (act p q t.2.2) b)) := by
    rw [ground.map_map, ground.map_map, elim.dotP_map_pair,
      elim.dotP_map_pair]
    refine ground.famFold_congr_members _ _ _ _ _ (fun t ht => ?_)
    match ground.mem_filter_of _ P t
      (ground.mem_of_countOf_pos t _ ht) with
    | ⟨htP, htc⟩ =>
      have hce : t.2.1.content = a.content := ground.listBeqEq htc
      have hce2 : t.2.2.content = a.content :=
        (hm t htP).symm.trans hce
      rw [show dotG t.2.1 a = elim.dotP t.2.1.coords a.coords from by
          show (if t.2.1.content = a.content then _ else _) = _
          exact if_pos hce,
        show dotG (act p q t.2.2) b
            = elim.dotP (act p q t.2.2).coords b.coords from by
          show (if (act p q t.2.2).content = b.content then _ else _)
            = _
          refine if_pos ?_
          show moveAt p q t.2.2.content = b.content
          rw [hce2, hbc],
        show (act p q t.2.2).coords
            = elim.matVec (units.matUnitAt
                (moveAt p q t.2.2.content) t.2.2.content p q)
              t.2.2.coords from rfl,
        hce2, elim.dotP_comm _ b.coords, ← BPair.mul_assoc]
  have hB : (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t =>
        dotG t.2.1 a * dotG (act p q t.2.2) b))).oneValue
      (elim.dotP b.coords (act p q (mapAt P a)).coords) :=
    BPair.oneValue_trans hB1
      (BPair.oneValue_symm
        (BPair.oneValue_trans hB2
          (BPair.oneValue_trans hB3 (BPair.oneValue_of_eq hB4))))
  exact BPair.oneValue_trans hsplit
    (BPair.add_congr hA hB)

/-- The invariance read at the stated argument against a group
member joins the two crossed folds — the first the map's value at
the moved argument through the evaluation's equivariance, the
second the moved value's own pairing — so the map's two moved
reads agree against the member. -/
private theorem moved_agree (P : List (BPair × HVec × HVec))
    (p q : Nat) (a b : HVec)
    (hpa : p < a.content.length) (hqa : q < a.content.length)
    (hpq : ¬ p = q) (hsa : sized a)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content)
    (hbc : b.content = moveAt p q a.content)
    (hinvb : (movedAt P p q a b).oneValue BPair.unit) :
    (elim.dotP b.coords (act p q (mapAt P a)).coords).oneValue
      (elim.dotP b.coords (mapAt P (act p q a)).coords) := by
  have h2r := movedAt_two_reads P p q a b hpa hqa hpq hsa hsz hm hbc
  refine ground.oneOfUnit ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
  exact BPair.oneValue_trans (BPair.oneValue_symm h2r) hinvb

/-- The invariant reads as the equivariant map: the invariance
read at the pair of the stated argument with a further member of
the carrier's stated list joins two crossed folds, the first the
map's value at the moved argument through the evaluation's
equivariance and the second the moved value's own pairing, so the
map's two moved reads agree against every member and the moved
images are one value at the pairing's definiteness — the moved
map value's span read the carrier's own, the family's slots
members of the stated list with the list's images settled at the
letter pair — `lem:dualread`(i)'s forward sentence at the two
carriers' stated lists. -/
theorem mapAt_equiv (P : List (BPair × HVec × HVec))
    (L : List HVec) (p q : Nat) (a : HVec)
    (hpa : p < a.content.length) (hqa : q < a.content.length)
    (hpq : ¬ p = q) (hsa : sized a)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content)
    (hszL : ∀ w ∈ L, sized w)
    (hPL : ∀ t ∈ P, (t.2.2 : HVec) ∈ L)
    (hinv : ∀ b ∈ L, (movedAt P p q a b).oneValue BPair.unit)
    (hclL : ∀ b ∈ L, settledAt L (act p q b)) :
    poly.oneValue (mapAt P (act p q a)).coords
      (act p q (mapAt P a)).coords := by
  have hWa := filterRowsW P a.content hsz hm
  have hGa : elim.rowsLen (places.monomialsAt a.content).length
      (blockcount.groupAt L a.content) :=
    rowsLen_groupAt a.content L hszL
  -- the map's value sits in the argument's content group's span,
  -- the slots' rows the group's own members
  have hsp0 : elim.spanRel (places.monomialsAt a.content).length
      (blockcount.groupAt L a.content) (mapAt P a).coords := by
    rw [mapAt_coords]
    refine elim.spanRel_combo _ _ hGa _ _ hWa (fun k hk => ?_)
    have hkf : k < (P.filter (fun t =>
        t.2.1.content == a.content)).length := by
      rw [ground.length_map] at hk
      exact hk
    have hrowEq : ground.getAt []
        ((P.filter (fun t => t.2.1.content == a.content)).map
          (fun t => t.2.2.coords)) k
        = (ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
            (⟨[], []⟩ : HVec))
          (P.filter (fun t => t.2.1.content == a.content))
          k).2.2.coords :=
      ground.getAt_map (BPair.unit, (⟨[], []⟩ : HVec),
        (⟨[], []⟩ : HVec)) ([] : List BPair) _ _ k hkf
    match ground.mem_filter_of _ _ _
      (ground.mem_getAt (BPair.unit, (⟨[], []⟩ : HVec),
        (⟨[], []⟩ : HVec))
        (P.filter (fun t => t.2.1.content == a.content)) k hkf) with
    | ⟨htP, htc⟩ =>
      have hbL : (ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
          (⟨[], []⟩ : HVec))
          (P.filter (fun t => t.2.1.content == a.content))
          k).2.2 ∈ L.filter (fun w => w.content == a.content) := by
        refine ground.mem_filter_to _ (hPL _ htP) ?_
        rw [← hm _ htP, ground.listBeqEq htc]
        exact ground.listEqBeq a.content
      match ground.getAt_of_mem ([] : List BPair)
        (ground.mem_map_to HVec.coords hbL) with
      | ⟨m, hml, hme⟩ =>
        rw [hrowEq, ← hme]
        exact elim.spanRel_getAt _ _ m hml hGa
  have hx0 : (mapAt P a).coords.length
      = (places.monomialsAt a.content).length := by
    rw [mapAt_coords]
    exact elim.length_combo _ _ _ hWa
  -- the carrier's closure transports the span read across the
  -- letter pair
  have hclA : elim.spanRel
      (places.monomialsAt (moveAt p q a.content)).length
      (blockcount.groupAt L (moveAt p q a.content))
      (act p q (mapAt P a)).coords := by
    have h := blockcount.act_transport L p q hszL hclL a.content
      (mapAt P a).coords hx0 hsp0
    exact h
  match elim.span_elim hclA with
  | ⟨c₀, cs, hc₀, _, hone⟩ =>
    have hW := filterRowsW P (moveAt p q a.content) hsz hm
    have hn : (act p q (mapAt P a)).coords.length
        = (places.monomialsAt (moveAt p q a.content)).length :=
      act_sized p q (mapAt P a)
    have hv_len : (mapAt P (act p q a)).coords.length
        = (places.monomialsAt (moveAt p q a.content)).length := by
      rw [mapAt_coords]
      exact elim.length_combo _ _ _ hW
    -- the agreement at every row of the carrier's moved group
    have hag : ∀ j, j < (blockcount.groupAt L
        (moveAt p q a.content)).length →
        (elim.dotP (ground.getAt [] (blockcount.groupAt L
            (moveAt p q a.content)) j)
          (act p q (mapAt P a)).coords).oneValue
        (elim.dotP (ground.getAt [] (blockcount.groupAt L
            (moveAt p q a.content)) j)
          (mapAt P (act p q a)).coords) := by
      intro j hj
      have hjf : j < (L.filter
          (fun w => w.content == moveAt p q a.content)).length := by
        have := hj
        rw [show blockcount.groupAt L (moveAt p q a.content)
            = (L.filter
              (fun w => w.content == moveAt p q a.content)).map
              HVec.coords from rfl,
          ground.length_map] at this
        exact this
      have hrowEq : ground.getAt [] (blockcount.groupAt L
          (moveAt p q a.content)) j
          = (ground.getAt (⟨[], []⟩ : HVec)
            (L.filter
              (fun w => w.content == moveAt p q a.content))
            j).coords :=
        ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
          HVec.coords _ j hjf
      match ground.mem_filter_of _ _ _
        (ground.mem_getAt (⟨[], []⟩ : HVec)
          (L.filter (fun w => w.content == moveAt p q a.content))
          j hjf) with
      | ⟨hbL, hbB⟩ =>
        rw [hrowEq]
        exact moved_agree P p q a _ hpa hqa hpq hsa hsz hm
          (ground.listBeqEq hbB) (hinv _ hbL)
    -- the gap's row reads
    have hrow : ∀ j, j < (blockcount.groupAt L
        (moveAt p q a.content)).length →
        (elim.dotP (ground.getAt [] (blockcount.groupAt L
            (moveAt p q a.content)) j)
          (elim.vecAdd
            (elim.vecScale c₀ (act p q (mapAt P a)).coords)
            (poly.neg (elim.vecScale c₀
              (mapAt P (act p q a)).coords)))).oneValue
        BPair.unit := by
      intro j hj
      refine BPair.oneValue_trans
        (elim.dotP_vecAdd_right _ _ _ (by
          rw [poly.length_neg, elim.length_vecScale,
            elim.length_vecScale, hn, hv_len])) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (elim.dotP_vecScale_right _ _ c₀)
            (BPair.mul_congr (BPair.oneValue_refl c₀) (hag j hj)))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (elim.dotP_swapMap _ _))
            (ground.swap_congr (elim.dotP_vecScale_right _ _ c₀))))
        ?_
      exact ground.unitOfOne (BPair.oneValue_refl _)
    -- the moved value's coordinates are the family's own moved
    -- combination
    have hgv : (mapAt P (act p q a)).coords
        = elim.combo
          (places.monomialsAt (moveAt p q a.content)).length
          ((P.filter (fun t =>
            t.2.1.content == moveAt p q a.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords (act p q a).coords))
          ((P.filter (fun t =>
            t.2.1.content == moveAt p q a.content)).map
            (fun t => t.2.2.coords)) := by
      rw [mapAt_coords]
      exact rfl
    -- the gap's pairings at the carrier's moved group read the
    -- unit tail
    have hut : poly.unitTail ((blockcount.groupAt L
        (moveAt p q a.content)).map
        (fun row => elim.dotP
          (elim.vecAdd
            (elim.vecScale c₀ (act p q (mapAt P a)).coords)
            (poly.neg (elim.vecScale c₀
              (mapAt P (act p q a)).coords))) row)) := by
      refine poly.unitTail_map _ _ (fun row hrowm => ?_)
      match ground.getAt_of_mem ([] : List BPair) hrowm with
      | ⟨j, hjl, hje⟩ =>
        rw [← hje, elim.dotP_comm]
        exact hrow j hjl
    -- and at the family's own moved rows, each a row of the
    -- carrier's group
    have hutF : poly.unitTail (((P.filter (fun t =>
        t.2.1.content == moveAt p q a.content)).map
          (fun t => t.2.2.coords)).map
        (fun row => elim.dotP
          (elim.vecAdd
            (elim.vecScale c₀ (act p q (mapAt P a)).coords)
            (poly.neg (elim.vecScale c₀
              (mapAt P (act p q a)).coords))) row)) := by
      refine poly.unitTail_map _ _ (fun row hrowm => ?_)
      match ground.mem_map_of _ _ row hrowm with
      | ⟨t, htf, hte⟩ =>
        match ground.mem_filter_of _ _ _ htf with
        | ⟨htP, htc⟩ =>
          have hbL : (t.2.2 : HVec) ∈ L.filter
              (fun w => w.content == moveAt p q a.content) := by
            refine ground.mem_filter_to _ (hPL _ htP) ?_
            rw [← hm _ htP, ground.listBeqEq htc]
            exact ground.listEqBeq (moveAt p q a.content)
          match ground.getAt_of_mem ([] : List BPair)
            (ground.mem_map_to HVec.coords hbL) with
          | ⟨m, hml, hme⟩ =>
            rw [← hte,
              show (t.2.2 : HVec).coords
                = ground.getAt [] (blockcount.groupAt L
                  (moveAt p q a.content)) m from hme.symm,
              elim.dotP_comm]
            exact hrow m hml
    have hb1 : (elim.dotP
        (elim.vecAdd
          (elim.vecScale c₀ (act p q (mapAt P a)).coords)
          (poly.neg (elim.vecScale c₀ (mapAt P (act p q a)).coords)))
        (elim.vecScale c₀ (act p q (mapAt P a)).coords)).oneValue
        BPair.unit :=
      BPair.oneValue_trans
        (elim.dotP_oneValue_right _ _ _ hone)
        (BPair.oneValue_trans
          (elim.dotP_combo _ _ _ _ hclA.1)
          (elim.dotP_null_tail_right _ _ hut))
    have hb2 : (elim.dotP
        (elim.vecAdd
          (elim.vecScale c₀ (act p q (mapAt P a)).coords)
          (poly.neg (elim.vecScale c₀ (mapAt P (act p q a)).coords)))
        (elim.vecScale c₀ (mapAt P (act p q a)).coords)).oneValue
        BPair.unit :=
      BPair.oneValue_trans (elim.dotP_vecScale_right _ _ c₀)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl c₀)
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (congrArg (elim.dotP _) hgv))
              (BPair.oneValue_trans
                (elim.dotP_combo _ _ _ _ hW)
                (elim.dotP_null_tail_right _ _ hutF))))
          (BPair.mul_unit c₀))
    have hself : (elim.dotP
        (elim.vecAdd
          (elim.vecScale c₀ (act p q (mapAt P a)).coords)
          (poly.neg (elim.vecScale c₀ (mapAt P (act p q a)).coords)))
        (elim.vecAdd
          (elim.vecScale c₀ (act p q (mapAt P a)).coords)
          (poly.neg (elim.vecScale c₀
            (mapAt P (act p q a)).coords)))).oneValue
        BPair.unit :=
      BPair.oneValue_trans
        (elim.dotP_vecAdd_right _ _ _ (by
          rw [poly.length_neg, elim.length_vecScale,
            elim.length_vecScale, hn, hv_len]))
        (BPair.oneValue_trans
          (BPair.add_congr hb1
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (elim.dotP_swapMap _ _))
              (ground.swap_congr hb2)))
          (BPair.unit_add BPair.unit))
    exact poly.oneValue_symm
      (elim.oneValue_unscale c₀ hc₀ _ _
        (elim.oneValue_of_null_swap _ _ (by
          rw [elim.length_vecScale, elim.length_vecScale, hn, hv_len])
          (elim.dotP_self_null _ hself)))

/-! `lem:dualread`(i)'s count clause: an invariant enters at its
coefficient family over the two stated lists' matched member pairs
(`dualPairs`, one slot pair per member pair at one content), the
moved reads one stacked linear system in the coefficients
(`dualSys`), each row the moved form's fold at a letter pair and a
member pair (`dualRow`), with its count and kernel list the
elimination's (`def:elim`, `invCount` at `elim.kernelDim` over the
grid's own width).  The coefficient family at a grid vector is
`invFam`, the moved form at it the system's row against the
coefficients (`movedAt_invFam`, the grid's two projections read off
the matched-width pairing), and a grid vector sits in the system's
kernel exactly where every moved read at the letter pairs and the
member pairs is the sum's unit (`dualKer_read`: the rows' membership
walked over the range families with the equal-letter rows absent,
and the skipping fold read against the plain pairing at
`elim.dotN_read`). -/

/-- The matched pair grid at the two stated lists: one slot pair per
member pair at one content — `lem:dualread`(i)'s coefficient
carrier. -/
def dualPairs (Y Z : List HVec) : List (HVec × HVec) :=
  Y.flatMap (fun y => Z.flatMap (fun z =>
    if y.content = z.content then [(y, z)] else []))

/-- The invariance system's row at a letter pair and a member pair:
the moved form's fold read at each grid slot. -/
def dualRow (Y Z : List HVec) (p q : Nat) (a b : HVec) :
    List BPair :=
  (dualPairs Y Z).map (fun t =>
    dotG (dact p q t.1) a * dotG t.2 b
      + dotG t.1 a * dotG (act p q t.2) b)

/-- The stacked invariance system: one row per letter pair and member
pair of the two stated lists. -/
def dualSys (Y Z : List HVec) (d : Nat) : elim.Mat :=
  (List.range d).flatMap (fun p =>
    (List.range d).flatMap (fun q =>
      if p = q then [] else
        Y.flatMap (fun a => Z.map (fun b => dualRow Y Z p q a b))))

/-- The invariant count: the stacked system's kernel dimension over
the grid's coefficients (`def:elim`'s kernel calculus). -/
def invCount (Y Z : List HVec) (d : Nat) : Nat :=
  elim.kernelDim (dualPairs Y Z).length (dualSys Y Z d)

/-- The coefficient family at a grid vector: one member per grid slot
at its coefficient. -/
def invFam (Y Z : List HVec) (c : List BPair) :
    List (BPair × HVec × HVec) :=
  List.zipWith (fun cv t => (cv, t.1, t.2)) c (dualPairs Y Z)

/-- The grid family's first projection at matched widths: the
coefficients themselves. -/
private theorem zipTrip_fst :
    ∀ (c : List BPair) (g : List (HVec × HVec)),
      c.length = g.length →
      (List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c g).map
          (fun t => t.1) = c
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: s, _ :: g, h =>
    congrArg (List.cons x) (zipTrip_fst s g (Nat.succ.inj h))

/-- The grid family's slot pair read at matched widths: the moved
form's fold at a letter pair and a member pair is the grid's own. -/
private theorem zipTrip_row (p q : Nat) (a b : HVec) :
    ∀ (c : List BPair) (g : List (HVec × HVec)),
      c.length = g.length →
      (List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c g).map
          (fun t => dotG (dact p q t.2.1) a * dotG t.2.2 b
            + dotG t.2.1 a * dotG (act p q t.2.2) b)
        = g.map (fun t => dotG (dact p q t.1) a * dotG t.2 b
            + dotG t.1 a * dotG (act p q t.2) b)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: s, z :: g, h =>
    congrArg (List.cons (dotG (dact p q z.1) a * dotG z.2 b
        + dotG z.1 a * dotG (act p q z.2) b))
      (zipTrip_row p q a b s g (Nat.succ.inj h))

/-- The moved form at a coefficient family is the system's row
against the coefficients, the fold linear in them. -/
theorem movedAt_invFam (Y Z : List HVec) (c : List BPair)
    (hc : c.length = (dualPairs Y Z).length) (p q : Nat) (a b : HVec) :
    movedAt (invFam Y Z c) p q a b
      = elim.dotP c (dualRow Y Z p q a b) := by
  show elim.dotP
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c
        (dualPairs Y Z)).map (fun t => t.1))
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c
        (dualPairs Y Z)).map (fun t =>
          dotG (dact p q t.2.1) a * dotG t.2.2 b
            + dotG t.2.1 a * dotG (act p q t.2.2) b))
    = elim.dotP c (dualRow Y Z p q a b)
  rw [zipTrip_fst c (dualPairs Y Z) hc,
    zipTrip_row p q a b c (dualPairs Y Z) hc]
  exact rfl

/-- The system's row at a letter pair below the width with distinct
letters and a member pair of the two lists joins the stack. -/
private theorem dualSys_mem (Y Z : List HVec) (d p q : Nat)
    (hp : p < d) (hq : q < d) (hpq : ¬ p = q) {a b : HVec}
    (ha : a ∈ Y) (hb : b ∈ Z) :
    dualRow Y Z p q a b ∈ dualSys Y Z d := by
  refine ground.mem_flatMap_to _ (ground.memRange hp) ?_
  refine ground.mem_flatMap_to _ (ground.memRange hq) ?_
  show dualRow Y Z p q a b ∈
    (if p = q then [] else
      Y.flatMap (fun a => Z.map (fun b => dualRow Y Z p q a b)))
  rw [if_neg hpq]
  exact ground.mem_flatMap_to _ ha
    (ground.mem_map_to (fun b => dualRow Y Z p q a b) hb)

/-- A read holding at every generator row holds at every member of
the stack: the walk over the two range families with the
equal-letter arms vacant. -/
private theorem dualSys_all (Y Z : List HVec) (d : Nat)
    (P : List BPair → Prop)
    (h : ∀ p, p < d → ∀ q, q < d → ¬ p = q → ∀ a ∈ Y, ∀ b ∈ Z,
      P (dualRow Y Z p q a b)) :
    ∀ r ∈ dualSys Y Z d, P r := by
  intro r hr
  match ground.mem_flatMap_of _ (List.range d) r hr with
  | ⟨p, hpm, hp⟩ =>
    match ground.mem_flatMap_of _ (List.range d) r hp with
    | ⟨q, hqm, hq⟩ =>
      by_cases hpq : p = q
      · have hq' : r ∈ ([] : elim.Mat) := by
          have hq0 : r ∈
            (if p = q then [] else
              Y.flatMap (fun a => Z.map (fun b => dualRow Y Z p q a b))) := hq
          rw [if_pos hpq] at hq0
          exact hq0
        exact nomatch hq'
      · have hq0 : r ∈
          (if p = q then [] else
            Y.flatMap (fun a => Z.map (fun b => dualRow Y Z p q a b))) := hq
        rw [if_neg hpq] at hq0
        match ground.mem_flatMap_of _ Y r hq0 with
        | ⟨a, ham, hra⟩ =>
          match ground.mem_map_of _ Z r hra with
          | ⟨b, hbm, hrb⟩ =>
            rw [← hrb]
            exact h p (ground.ltOfMemRange hpm)
              q (ground.ltOfMemRange hqm) hpq
              a ham b hbm

/-- A grid vector sits in the system's kernel exactly where every
moved read at the letter pairs and the member pairs is the sum's
unit. -/
theorem dualKer_read (Y Z : List HVec) (d : Nat) (c : List BPair)
    (hc : c.length = (dualPairs Y Z).length) :
    poly.unitTail (elim.matVec (dualSys Y Z d) c) ↔
      (∀ p, p < d → ∀ q, q < d → ¬ p = q → ∀ a ∈ Y, ∀ b ∈ Z,
        (movedAt (invFam Y Z c) p q a b).oneValue BPair.unit) := by
  constructor
  · intro h p hp q hq hpq a ha b hb
    have hu : (elim.dotN (dualRow Y Z p q a b) c).oneValue BPair.unit :=
      poly.unitTail_member h _
        (ground.mem_map_to (fun r => elim.dotN r c)
          (dualSys_mem Y Z d p q hp hq hpq ha hb))
    rw [movedAt_invFam Y Z c hc p q a b,
      elim.dotP_comm c (dualRow Y Z p q a b)]
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (elim.dotN_read (dualRow Y Z p q a b) c)) hu
  · intro h
    refine poly.unitTail_map (fun r => elim.dotN r c) (dualSys Y Z d) ?_
    refine dualSys_all Y Z d
      (fun r => (elim.dotN r c).oneValue BPair.unit) ?_
    intro p hp q hq hpq a ha b hb
    have h0 := h p hp q hq hpq a ha b hb
    rw [movedAt_invFam Y Z c hc p q a b,
      elim.dotP_comm c (dualRow Y Z p q a b)] at h0
    exact BPair.oneValue_trans
      (elim.dotN_read (dualRow Y Z p q a b) c) h0

/-- The complementary grid's family: the coefficients zipped onto
the factor enumeration at the stated content
(`lem:dualread`(i)'s family format at the tensor grid, clause
(iii)'s carrier, `invFam`'s sibling). -/
def pairFam (A B : List HVec) (cc : List Nat) (c : List BPair) :
    List (BPair × HVec × HVec) :=
  List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c
    (blockcount.pairIdx A (fun v => v) B cc)

/-! `lem:dualread`(i)'s count clause solve-back: a grid vector whose
map reads every listed member at the sum's unit is the unit family.
Per content the grid filters to the two lists' groups' product
(`dualPairs_filter`), the value there is the second group's
combination at the first group's weighted pairings (`regroup`, the
blocks' collection per second member at `chunkGrid`'s split of the
grid vector into one block per first member), the second group's
independence reads those weights back (`solveHom` at
`elim.indep_elim`), and per second member the weights pair the
first group's combination against its every member at the sum's
unit, so the perpendicular combination is the unit family at the
first group's independence (`elim.indep_perp_null`).  The contents
collect entrywise: each grid slot sits in its own content's filter
(`solve_at`), and the coefficients are the family's first
projection (`dualSolve`). -/

/-- A coefficient family is its own two projections' componentwise
walk: the coefficients against the slot pairs. -/
private theorem zipTrip_rebuild :
    ∀ L : List (BPair × HVec × HVec),
      List.zipWith (fun cv (t : HVec × HVec) => (cv, t))
        (L.map (fun t => t.1)) (L.map (fun t => t.2)) = L
  | [] => rfl
  | a :: t => congrArg (List.cons a) (zipTrip_rebuild t)

/-- The family's filter at a slot-pair test reads the grid's own
filter through the second projection, at matched counts. -/
private theorem zipTrip_filter (Q : HVec × HVec → Bool) :
    ∀ (c : List BPair) (g : List (HVec × HVec)), c.length = g.length →
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t)) c g).filter
          (fun t => Q t.2)).map (fun t => t.2) = g.filter Q
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: s, z :: g, h => by
    show (((x, z) :: List.zipWith
        (fun cv (t : HVec × HVec) => (cv, t)) s g).filter
        (fun t => Q t.2)).map (fun t => t.2) = (z :: g).filter Q
    cases hq : Q z with
    | true =>
      rw [ground.filter_cons_true
          (a := ((x, z) : BPair × HVec × HVec)) hq,
        ground.filter_cons_true hq]
      exact congrArg (List.cons z) (zipTrip_filter Q s g (Nat.succ.inj h))
    | false =>
      rw [ground.filter_cons_false
          (a := ((x, z) : BPair × HVec × HVec)) hq,
        ground.filter_cons_false hq]
      exact zipTrip_filter Q s g (Nat.succ.inj h)

/-- The family's weighted pairings at matched counts: each
coefficient against its slot pair's first member paired with the
argument. -/
private theorem zipTrip_mapMul (y : HVec) :
    ∀ (c : List BPair) (g : List (HVec × HVec)), c.length = g.length →
      (List.zipWith (fun cv (t : HVec × HVec) => (cv, t)) c g).map
          (fun t => t.1 * elim.dotP t.2.1.coords y.coords)
        = List.zipWith (fun cv (t : HVec × HVec) =>
            cv * elim.dotP t.1.coords y.coords) c g
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: s, z :: g, h =>
    congrArg (List.cons (x * elim.dotP z.1.coords y.coords))
      (zipTrip_mapMul y s g (Nat.succ.inj h))

/-- The family's second slots' coordinates at matched counts: the
grid's own. -/
private theorem zipTrip_mapRow :
    ∀ (c : List BPair) (g : List (HVec × HVec)), c.length = g.length →
      (List.zipWith (fun cv (t : HVec × HVec) => (cv, t)) c g).map
          (fun t => t.2.2.coords) = g.map (fun t => t.2.coords)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: s, z :: g, h =>
    congrArg (List.cons z.2.coords) (zipTrip_mapRow s g (Nat.succ.inj h))

/-- One first member's row of weights: against the grid row at a
fixed first slot the weights are the block's coefficients each
against that slot's pairing with the argument. -/
private theorem zipRow_map (a y : HVec) :
    ∀ (u : List BPair) (v : List HVec), u.length = v.length →
      List.zipWith (fun cv (t : HVec × HVec) =>
          cv * elim.dotP t.1.coords y.coords) u
          (v.map (fun b => ((a, b) : HVec × HVec)))
        = u.map (fun cv => cv * elim.dotP a.coords y.coords)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: u, _b :: v, h =>
    congrArg (List.cons (x * elim.dotP a.coords y.coords))
      (zipRow_map a y u v (Nat.succ.inj h))

/-- A grid row's second slots carry the second list's own
coordinates. -/
private theorem gridRow_rows (a : HVec) :
    ∀ B : List HVec,
      (B.map (fun b => ((a, b) : HVec × HVec))).map (fun t => t.2.coords)
        = B.map HVec.coords
  | [] => rfl
  | b :: B => congrArg (List.cons b.coords) (gridRow_rows a B)

/-- The product grid's second-slot rows carry the second list's
width, one grid row per first member. -/
private theorem rowsLen_gridRows (n : Nat) (B : List HVec)
    (hB : elim.rowsLen n (B.map HVec.coords)) :
    ∀ A : List HVec, elim.rowsLen n
      ((A.flatMap (fun a => B.map (fun b => (a, b)))).map
        (fun t => t.2.coords))
  | [] => trivial
  | a :: A => by
    show elim.rowsLen n
      ((B.map (fun b => ((a, b) : HVec × HVec))
        ++ A.flatMap (fun a => B.map (fun b => (a, b)))).map
        (fun t => t.2.coords))
    rw [ground.map_append, gridRow_rows a B]
    exact elim.rowsLen_append n hB (rowsLen_gridRows n B hB A)

/-- A vector at the product grid's count splits into one block per
first member, each block at the second list's count. -/
private theorem chunkGrid (B : List HVec) :
    ∀ (A : List HVec) (cc : List BPair),
      cc.length = (A.flatMap (fun a => B.map (fun b => (a, b)))).length →
      ∃ bs : List (List BPair), A.length = bs.length
        ∧ (∀ blk ∈ bs, blk.length = B.length)
        ∧ cc = bs.flatMap (fun b => b)
  | [], cc, h =>
    ⟨[], rfl, (fun _ hb => nomatch hb),
     ground.nil_of_length_zero cc h⟩
  | a :: A, cc, h => by
    have hlen : cc.length
        = B.length
          + (A.flatMap (fun a => B.map (fun b => (a, b)))).length := by
      rw [h]
      show ((B.map (fun b => ((a, b) : HVec × HVec))
        ++ A.flatMap (fun a => B.map (fun b => (a, b)))).length) = _
      rw [ground.length_append, ground.length_map]
    obtain ⟨u, v, hcc, hu⟩ := ground.listSplit cc B.length
      (by rw [hlen]; exact Nat.le_add_right _ _)
    have hsum : cc.length = u.length + v.length := by
      rw [hcc]; exact ground.length_append u v
    rw [hu] at hsum
    have hv : v.length
        = (A.flatMap (fun a => B.map (fun b => (a, b)))).length :=
      (ground.addCancelL B.length (hlen.symm.trans hsum)).symm
    obtain ⟨bs, hbl, hbm, hbf⟩ := chunkGrid B A v hv
    refine ⟨u :: bs, ?_, ?_, ?_⟩
    · show A.length + 1 = bs.length + 1
      rw [hbl]
    · intro blk hb
      cases hb with
      | head => exact hu
      | tail _ hm => exact hbm blk hm
    · show cc = u ++ bs.flatMap (fun b => b)
      rw [hcc, hbf]

/-- The product grid's combination collects per second member: the
blocks' weighted coefficients against the grid's second slots read
the second list's own combination at the collected weights, the
weights the blocks' combination at the first members' pairings with
the argument — the grid walked one first member at a time, each
step splitting the join and adding its scaled block. -/
private theorem regroup (y : HVec) (n : Nat) (B : List HVec)
    (hB : elim.rowsLen n (B.map HVec.coords)) :
    ∀ (A : List HVec) (bs : List (List BPair)),
      A.length = bs.length → (∀ blk ∈ bs, blk.length = B.length) →
      poly.oneValue
        (elim.combo n
          (List.zipWith (fun cv (t : HVec × HVec) =>
              cv * elim.dotP t.1.coords y.coords)
            (bs.flatMap (fun b => b))
            (A.flatMap (fun a => B.map (fun b => (a, b)))))
          ((A.flatMap (fun a => B.map (fun b => (a, b)))).map
            (fun t => t.2.coords)))
        (elim.combo n
          (elim.combo B.length
            (A.map (fun a => elim.dotP y.coords a.coords)) bs)
          (B.map HVec.coords))
  | [], [], _, _ =>
    poly.unitTail_oneValue (poly.unitTail_replicate n)
      (elim.unitTail_combo_of n _ (B.map HVec.coords)
        (poly.unitTail_replicate B.length))
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a0 :: A, blk :: bs, hl, hlen => by
    have hblk : blk.length = B.length := hlen blk (List.Mem.head bs)
    have hbs : ∀ b ∈ bs, b.length = B.length :=
      fun b hb => hlen b (List.Mem.tail blk hb)
    have hrest : elim.rowsLen n
        ((A.flatMap (fun a => B.map (fun b => (a, b)))).map
          (fun t => t.2.coords)) := rowsLen_gridRows n B hB A
    have hzip :
        List.zipWith (fun cv (t : HVec × HVec) =>
            cv * elim.dotP t.1.coords y.coords)
          ((blk :: bs).flatMap (fun b => b))
          ((a0 :: A).flatMap (fun a => B.map (fun b => (a, b))))
          = blk.map (fun cv => cv * elim.dotP a0.coords y.coords)
            ++ List.zipWith (fun cv (t : HVec × HVec) =>
                cv * elim.dotP t.1.coords y.coords)
              (bs.flatMap (fun b => b))
              (A.flatMap (fun a => B.map (fun b => (a, b)))) := by
      show List.zipWith (fun cv (t : HVec × HVec) =>
            cv * elim.dotP t.1.coords y.coords)
          (blk ++ bs.flatMap (fun b => b))
          (B.map (fun b => ((a0, b) : HVec × HVec))
            ++ A.flatMap (fun a => B.map (fun b => (a, b)))) = _
      rw [ground.zipWith_append _ blk (bs.flatMap (fun b => b))
          (B.map (fun b => ((a0, b) : HVec × HVec)))
          (A.flatMap (fun a => B.map (fun b => (a, b))))
          (by rw [ground.length_map]; exact hblk),
        zipRow_map a0 y blk B hblk]
    have hrows :
        ((a0 :: A).flatMap (fun a => B.map (fun b => (a, b)))).map
            (fun t => t.2.coords)
          = B.map HVec.coords
            ++ (A.flatMap (fun a => B.map (fun b => (a, b)))).map
              (fun t => t.2.coords) := by
      show ((B.map (fun b => ((a0, b) : HVec × HVec))
          ++ A.flatMap (fun a => B.map (fun b => (a, b)))).map
          (fun t => t.2.coords)) = _
      rw [ground.map_append, gridRow_rows a0 B]
    have hscale : blk.map (fun cv => cv * elim.dotP a0.coords y.coords)
        = elim.vecScale (elim.dotP y.coords a0.coords) blk :=
      ground.map_congr_all _ _ (fun x => by
        rw [BPair.mul_comm, elim.dotP_comm a0.coords y.coords]
        exact rfl) blk
    have hw : (elim.combo B.length
        (A.map (fun a => elim.dotP y.coords a.coords)) bs).length
        = B.length :=
      elim.length_combo B.length _ bs (elim.rowsLen_intro bs (fun i hi => hbs _
        (ground.mem_getAt [] bs i hi)))
    have hsc : (elim.vecScale (elim.dotP y.coords a0.coords) blk).length
        = B.length := by rw [elim.length_vecScale]; exact hblk
    refine poly.oneValue_trans
      (q := elim.vecAdd
        (elim.combo n (elim.vecScale (elim.dotP y.coords a0.coords) blk)
          (B.map HVec.coords))
        (elim.combo n
          (elim.combo B.length
            (A.map (fun a => elim.dotP y.coords a.coords)) bs)
          (B.map HVec.coords))) ?_ ?_
    · rw [hzip, hrows]
      refine poly.oneValue_trans
        (elim.combo_append n _ (B.map HVec.coords) _ _
          (by rw [ground.length_map, ground.length_map]; exact hblk)
          hB hrest) ?_
      refine elim.polyOne_vecAdd _ _ _ _ ?_
        (regroup y n B hB A bs (Nat.succ.inj hl) hbs) ?_ ?_
      · rw [hscale]
        exact poly.oneValue_refl _
      · rw [elim.length_combo n _ (B.map HVec.coords) hB,
          elim.length_combo n _ (B.map HVec.coords) hB]
      · rw [elim.length_combo n _ _ hrest,
          elim.length_combo n _ (B.map HVec.coords) hB]
    · exact poly.oneValue_symm
        (elim.combo_vecAdd n
          (elim.vecScale (elim.dotP y.coords a0.coords) blk)
          (elim.combo B.length
            (A.map (fun a : HVec => elim.dotP y.coords a.coords)) bs)
          (B.map HVec.coords)
          ((by rw [hsc, ground.length_map] :
              (elim.vecScale (elim.dotP y.coords a0.coords) blk).length
                = (B.map HVec.coords).length).trans
            (by rw [hw, ground.length_map] :
              (elim.combo B.length
                (A.map (fun a : HVec => elim.dotP y.coords a.coords))
                bs).length = (B.map HVec.coords).length).symm))

/-- One member's slot chunk: the second list's matched members at
the pair. -/
private theorem chunk_map (y : HVec) : ∀ Z : List HVec,
    Z.flatMap (fun z => if y.content = z.content
        then [(y, z)] else [])
      = (Z.filter (fun w => w.content == y.content)).map
          (fun z => (y, z))
  | [] => rfl
  | z :: Z => by
    show (if y.content = z.content then [(y, z)] else [])
        ++ Z.flatMap (fun z => if y.content = z.content
          then [(y, z)] else [])
      = ((z :: Z).filter (fun w => w.content == y.content)).map
          (fun z => (y, z))
    rw [ground.filter_cons]
    by_cases h : y.content = z.content
    · rw [if_pos h, show (z.content == y.content) = true from
        h ▸ ground.listEqBeq y.content]
      show (y, z) :: Z.flatMap _ = (z :: Z.filter _).map _
      rw [chunk_map y Z]
      exact rfl
    · have hb : (z.content == y.content) = false := by
        cases hzy : (z.content == y.content) with
        | false => rfl
        | true => exact absurd (ground.listBeqEq hzy).symm h
      rw [if_neg h, hb]
      show Z.flatMap _ = (Z.filter _).map _
      exact chunk_map y Z

/-- At a first member of the stated content the matched pairs
filter to that content's second-list group, each paired with the
member. -/
private theorem rowFilter_keep (y : HVec) (mu : List Nat)
    (hy : y.content = mu) (Z : List HVec) :
    (Z.flatMap (fun z =>
        if y.content = z.content then [(y, z)] else [])).filter
        (fun t => t.1.content == mu)
      = (Z.filter (fun w => w.content == mu)).map (fun b => (y, b)) := by
  rw [chunk_map y Z, ground.filter_map (fun z => (y, z))
      (fun t => t.1.content == mu),
    ground.filter_all _ _ (fun _ _ => hy ▸ ground.listEqBeq mu), hy]

/-- At a first member off the stated content the matched pairs
filter to the vacant family. -/
private theorem rowFilter_drop (y : HVec) (mu : List Nat)
    (hy : ¬ y.content = mu) (Z : List HVec) :
    (Z.flatMap (fun z =>
        if y.content = z.content then [(y, z)] else [])).filter
        (fun t => t.1.content == mu) = [] := by
  rw [chunk_map y Z, ground.filter_map (fun z => (y, z))
      (fun t => t.1.content == mu),
    ground.filter_false _ _ (fun _ _ => by
      cases hb : (y.content == mu) with
      | true => exact absurd (ground.listBeqEq hb) hy
      | false => rfl)]
  rfl

/-- The matched pair grid filters at a content to the two lists'
groups there, one slot pair per member pair of the product. -/
private theorem dualPairs_filter (Z : List HVec) (mu : List Nat) :
    ∀ Y : List HVec,
      (dualPairs Y Z).filter (fun t => t.1.content == mu)
        = (Y.filter (fun w => w.content == mu)).flatMap (fun a =>
            (Z.filter (fun w => w.content == mu)).map (fun b => (a, b)))
  | [] => rfl
  | y :: Y => by
    show ((Z.flatMap (fun z =>
          if y.content = z.content then [(y, z)] else [])
        ++ dualPairs Y Z).filter (fun t => t.1.content == mu))
      = ((y :: Y).filter (fun w => w.content == mu)).flatMap (fun a =>
          (Z.filter (fun w => w.content == mu)).map (fun b => (a, b)))
    rw [ground.filter_append, dualPairs_filter Z mu Y]
    by_cases hy : y.content = mu
    · rw [rowFilter_keep y mu hy Z,
        ground.filter_cons_true (p := fun w : HVec => w.content == mu)
          (a := y) (l := Y)
          (show (y.content == mu) = true from by
            rw [hy]; exact ground.listEqBeq mu)]
      rfl
    · have hym : (y.content == mu) = false := by
        cases hb : (y.content == mu) with
        | true => exact absurd (ground.listBeqEq hb) hy
        | false => rfl
      rw [rowFilter_drop y mu hy Z,
        ground.filter_cons_false (p := fun w : HVec => w.content == mu)
          (a := y) (l := Y) hym]
      rfl

/-- A family of unit tails joins to a unit tail. -/
private theorem unitTail_flat :
    ∀ bs : List (List BPair), (∀ b ∈ bs, poly.unitTail b) →
      poly.unitTail (bs.flatMap (fun b => b))
  | [], _ => trivial
  | b :: bs, h => by
    show poly.unitTail (b ++ bs.flatMap (fun x => x))
    exact elim.unitTail_append (h b (List.Mem.head bs))
      (unitTail_flat bs (fun x hx => h x (List.Mem.tail b hx)))

/-- The solve-back at one content: a vector over the two
independent lists' product grid whose weighted combination reads
the unit family at every member of the first list is the unit
family.  The vector splits into one block per first member; the
value collects per second member, so the second list's
independence reads the collected weights back; each collected
weight at a second member is the block column's combination over
the first list paired with the member, so that combination is
perpendicular to the whole first list and the first list's
independence reads the column at the unit family; and the columns'
reads assemble the blocks.  The two lists carry their own widths:
the first list's enters through the perpendicular read at its own
rows, the second list's through the collected combination, and the
pairings crossing the two are folds over the coefficient lists, so
no read ties the two widths together. -/
private theorem solveHom (nA nB : Nat) (A B : List HVec)
    (hA : elim.indepRows nA (A.map HVec.coords))
    (hB : elim.indepRows nB (B.map HVec.coords))
    (cc : List BPair)
    (hcc : cc.length
      = (A.flatMap (fun a => B.map (fun b => (a, b)))).length)
    (hval : ∀ y ∈ A, poly.unitTail
      (elim.combo nB
        (List.zipWith (fun cv (t : HVec × HVec) =>
            cv * elim.dotP t.1.coords y.coords) cc
          (A.flatMap (fun a => B.map (fun b => (a, b)))))
        ((A.flatMap (fun a => B.map (fun b => (a, b)))).map
          (fun t => t.2.coords)))) :
    poly.unitTail cc := by
  obtain ⟨bs, hbl, hbm, hbf⟩ := chunkGrid B A cc hcc
  subst hbf
  have hbsr : elim.rowsLen B.length bs :=
    elim.rowsLen_intro bs (fun i hi => hbm _
      (ground.mem_getAt [] bs i hi))
  have hkey : ∀ y ∈ A, poly.unitTail
      (elim.combo B.length
        (A.map (fun a : HVec => elim.dotP y.coords a.coords)) bs) := by
    intro y hy
    refine elim.indep_elim hB _ ?_ ?_
    · rw [elim.length_combo B.length _ bs hbsr, ground.length_map]
    · exact poly.unitTail_oneValue_right (hval y hy)
        (regroup y nB B hB.1 A bs hbl hbm)
  have hcol : ∀ k, k < B.length →
      poly.unitTail (bs.map (fun r => ground.getAt BPair.unit r k)) := by
    intro k hk
    refine elim.indep_perp_null nA (A.map HVec.coords) hA _ ?_ ?_
    · rw [ground.length_map, ground.length_map]
      exact hbl.symm
    · intro l hl
      rw [ground.length_map] at hl
      have hy : ground.getAt (⟨[], []⟩ : HVec) A l ∈ A :=
        ground.mem_getAt _ A l hl
      have hrow : ground.getAt ([] : List BPair) (A.map HVec.coords) l
          = (ground.getAt (⟨[], []⟩ : HVec) A l).coords :=
        ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
          HVec.coords A l hl
      have hmm : (A.map HVec.coords).map
            (fun row => elim.dotP
              (ground.getAt (⟨[], []⟩ : HVec) A l).coords row)
          = A.map (fun a : HVec => elim.dotP
              (ground.getAt (⟨[], []⟩ : HVec) A l).coords a.coords) :=
        ground.map_map HVec.coords _ A
      rw [hrow, elim.dotP_comm]
      refine BPair.oneValue_trans
        (elim.dotP_combo (bs.map (fun r => ground.getAt BPair.unit r k))
          (A.map HVec.coords)
          (ground.getAt (⟨[], []⟩ : HVec) A l).coords nA hA.1) ?_
      rw [hmm, elim.dotP_comm]
      refine BPair.oneValue_trans
        (BPair.oneValue_symm
          (elim.combo_getAt B.length _ bs k hbsr hk)) ?_
      exact poly.getAt_unitTail (hkey _ hy) k
  refine unitTail_flat bs ?_
  intro blk hblkm
  obtain ⟨j, hj, hje⟩ := ground.getAt_of_mem ([] : List BPair) hblkm
  refine elim.unitTail_of_getAt blk (fun k hk => ?_)
  have hkB : k < B.length := by
    rw [hbm blk hblkm] at hk; exact hk
  have hentry : ground.getAt BPair.unit
      (bs.map (fun r => ground.getAt BPair.unit r k)) j
      = ground.getAt BPair.unit blk k := by
    rw [ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => ground.getAt BPair.unit r k) bs j hj, hje]
  rw [← hentry]
  exact poly.getAt_unitTail (hcol k hkB) j

/-- The solve-back read at one content: the grid family's slots at
that content carry the unit coefficient, the grid there the two
lists' groups' product and the map's value at each member of the
first group the product's own combination. -/
private theorem solve_at (Y Z : List HVec) (c : List BPair)
    (hiY : indepAll Y) (hiZ : indepAll Z)
    (hc : c.length = (dualPairs Y Z).length)
    (hval : ∀ y ∈ Y, poly.unitTail (mapAt (invFam Y Z c) y).coords)
    (mu : List Nat) :
    poly.unitTail
      (((invFam Y Z c).filter (fun t => t.2.1.content == mu)).map
        (fun t => t.1)) := by
  have hgrid : ((invFam Y Z c).filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2)
      = (Y.filter (fun w => w.content == mu)).flatMap (fun a =>
          (Z.filter (fun w => w.content == mu)).map (fun b => (a, b))) :=
    (zipTrip_filter (fun p : HVec × HVec => p.1.content == mu) c
      (dualPairs Y Z) hc).trans (dualPairs_filter Z mu Y)
  have hlen : (((invFam Y Z c).filter (fun t => t.2.1.content == mu)).map
        (fun t => t.1)).length
      = ((Y.filter (fun w => w.content == mu)).flatMap (fun a =>
          (Z.filter (fun w => w.content == mu)).map
            (fun b => (a, b)))).length := by
    rw [ground.length_map, ← hgrid, ground.length_map]
  have hQ : (invFam Y Z c).filter (fun t => t.2.1.content == mu)
      = List.zipWith (fun cv (t : HVec × HVec) => (cv, t))
          (((invFam Y Z c).filter (fun t => t.2.1.content == mu)).map
            (fun t => t.1))
          ((Y.filter (fun w => w.content == mu)).flatMap (fun a =>
            (Z.filter (fun w => w.content == mu)).map
              (fun b => (a, b)))) := by
    rw [← hgrid]
    exact (zipTrip_rebuild _).symm
  refine solveHom (places.monomialsAt mu).length
    (places.monomialsAt mu).length
    (Y.filter (fun w => w.content == mu))
    (Z.filter (fun w => w.content == mu))
    (blockcount.indepAll_all hiY mu) (blockcount.indepAll_all hiZ mu)
    _ hlen ?_
  intro y hy
  have hyc : y.content = mu :=
    ground.listBeqEq (ground.mem_filter_of _ Y y hy).2
  have h0 := hval y (ground.mem_filter_of _ Y y hy).1
  rw [mapAt_coords (invFam Y Z c) y, hyc, hQ,
    zipTrip_mapMul y _ _ hlen, zipTrip_mapRow _ _ hlen] at h0
  exact h0

/-- A grid vector whose map reads every listed member at the sum's
unit is the unit family: per content the value is the second list's
combination at the first list's weighted pairings, the second list's
independence reads those weights back, and per second member the
weights pair the first list's group against its every member at the
sum's unit, the perpendicular combination the unit family at the
group's independence — `lem:dualread`(i)'s solve-back. -/
theorem dualSolve (Y Z : List HVec) (c : List BPair)
    (hiY : blockcount.indepAll Y) (hiZ : blockcount.indepAll Z)
    (hc : c.length = (dualPairs Y Z).length)
    (hval : ∀ y ∈ Y, poly.unitTail (mapAt (invFam Y Z c) y).coords) :
    poly.unitTail c := by
  have he : (invFam Y Z c).map (fun t => t.1) = c :=
    zipTrip_fst c (dualPairs Y Z) hc
  refine he ▸ poly.unitTail_map (fun t => t.1) (invFam Y Z c) ?_
  intro t ht
  refine poly.unitTail_member
    (solve_at Y Z c hiY hiZ hc hval t.2.1.content) t.1
    (ground.mem_map_to (fun (s : BPair × HVec × HVec) => s.1) ?_)
  exact ground.mem_filter_to _ ht (ground.listEqBeq t.2.1.content)


/-! `lem:dualread`(iii)'s solve-back at the complementary grid: per
content a value is the second group's combination at the first
group's weighted pairings, and a family whose every value reads the
unit tail is the unit family, the two groups' independence reading
the weights and the perpendicular combination back — (i)'s count
clause at the complementary groups (`lem:lowerspan`).  The front end
is the pair grid's own: the enumeration's guard is the entrywise
join, so at a stated first content the second content is determined
(`ground.addCancelL` entry by entry at matched widths) and the grid
there is the two groups' product at the complementary contents, one
slot pair per member pair.  The engine is (i)'s `solveHom` at the
two contents' widths. -/

/-- A zipped slot's coefficient is a member of the vector and its
pair a member of the grid. -/
private theorem zipTrip_mem :
    ∀ (c : List BPair) (g : List (HVec × HVec))
      (t : BPair × HVec × HVec),
      t ∈ List.zipWith (fun cv (s : HVec × HVec) =>
        (cv, s.1, s.2)) c g → t.1 ∈ c ∧ (t.2.1, t.2.2) ∈ g
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | cv :: c, s :: g, t, h => by
    have h' : t ∈ (cv, s.1, s.2)
        :: List.zipWith (fun cv (s : HVec × HVec) =>
          (cv, s.1, s.2)) c g := h
    cases h' with
    | head => exact ⟨List.Mem.head c, List.Mem.head g⟩
    | tail _ hm =>
      exact ⟨List.Mem.tail cv (zipTrip_mem c g t hm).1,
        List.Mem.tail s (zipTrip_mem c g t hm).2⟩

/-- The display's width is the factor enumeration's. -/
private theorem pairsAt_len (A B : List HVec) (cc : List Nat) :
    (pairsAt A B cc).length
      = (blockcount.pairIdx A (fun v => v) B cc).length := by
  rw [blockcount.pairsAt_pairIdx A B cc, ground.length_map]

/-- The family's slots sit in the two lists at the guard. -/
private theorem pairFam_slots (A B : List HVec) (cc : List Nat)
    (c : List BPair) (t : BPair × HVec × HVec)
    (ht : t ∈ pairFam A B cc c) :
    t.2.1 ∈ A ∧ t.2.2 ∈ B
      ∧ List.zipWith (fun x y => x + y) t.2.1.content t.2.2.content
        = cc :=
  blockcount.pairIdx_mem (zipTrip_mem c _ t ht).2

/-- The value's coordinates, the definition's own display. -/
private theorem pairVal_coords (P : List (BPair × HVec × HVec))
    (x : HVec) (oc : List Nat) :
    (pairVal P x oc).coords
      = elim.combo (places.monomialsAt oc).length
          ((P.filter (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
          ((P.filter (fun t => t.2.1.content == x.content)).map
            (fun t => t.2.2.coords)) := rfl

/-- At a first factor the enumeration's block is the complementary
group, each member paired with the factor: the guard reads the
second factor's content back off the join. -/
private theorem pairRow_keep (v : HVec) (oc cc : List Nat)
    (hjoin : List.zipWith (fun x y => x + y) v.content oc = cc)
    (hoc : oc.length = v.content.length) :
    ∀ B : List HVec, (∀ w ∈ B, w.content.length = v.content.length) →
      B.flatMap (fun w =>
          if List.zipWith (fun x y => x + y) v.content w.content = cc
            then [(v, w)] else [])
        = (B.filter (fun w => w.content == oc)).map
            (fun b => ((v, b) : HVec × HVec))
  | [], _ => rfl
  | w :: B, hw => by
    show (if List.zipWith (fun x y => x + y) v.content w.content = cc
        then [(v, w)] else [])
        ++ B.flatMap (fun z =>
          if List.zipWith (fun x y => x + y) v.content z.content = cc
            then [(v, z)] else [])
      = ((w :: B).filter (fun z => z.content == oc)).map
          (fun b => ((v, b) : HVec × HVec))
    have hrec := pairRow_keep v oc cc hjoin hoc B
      (fun x hx => hw x (List.Mem.tail w hx))
    rw [ground.filter_cons]
    by_cases h : List.zipWith (fun x y => x + y) v.content w.content
        = cc
    · have hwo : w.content = oc :=
        blockcount.zipWith_add_cancelL v.content w.content oc
          v.content.length rfl (hw w (List.Mem.head B)) hoc
          (h.trans hjoin.symm)
      rw [if_pos h, show (w.content == oc) = true from by
        rw [hwo]; exact ground.listEqBeq oc]
      show (v, w) :: B.flatMap _ = (w :: B.filter _).map _
      rw [hrec]
      exact rfl
    · have hwb : (w.content == oc) = false := by
        cases hb : (w.content == oc) with
        | false => rfl
        | true =>
          refine absurd ?_ h
          rw [ground.listBeqEq hb]
          exact hjoin
      rw [if_neg h, hwb]
      show B.flatMap _ = (B.filter _).map _
      exact hrec

/-- At a first factor off the stated content the enumeration's
block refuses the content test outright. -/
private theorem pairRow_drop (v : HVec) (mu cc : List Nat)
    (hvm : (v.content == mu) = false) :
    ∀ B : List HVec,
      (B.flatMap (fun w =>
          if List.zipWith (fun x y => x + y) v.content w.content = cc
            then [(v, w)] else [])).filter
        (fun t => (t.1 : HVec).content == mu) = []
  | [] => rfl
  | w :: B => by
    show ((if List.zipWith (fun x y => x + y) v.content w.content = cc
        then [(v, w)] else [])
        ++ B.flatMap (fun z =>
          if List.zipWith (fun x y => x + y) v.content z.content = cc
            then [(v, z)] else [])).filter
        (fun t => (t.1 : HVec).content == mu) = []
    rw [ground.filter_append, pairRow_drop v mu cc hvm B]
    by_cases h : List.zipWith (fun x y => x + y) v.content w.content
        = cc
    · rw [if_pos h, ground.filter_cons_false
        (p := fun t : HVec × HVec => t.1.content == mu)
        (a := ((v, w) : HVec × HVec)) (l := []) hvm]
      rfl
    · rw [if_neg h]
      rfl

/-- The factor enumeration filters at a first content to the two
lists' groups' product at the complementary contents, one slot pair
per member pair — the pair grid's own front end, `dualPairs_filter`
at the complementary contents. -/
private theorem pairIdx_filter (B : List HVec) (mu oc cc : List Nat)
    (hjoin : List.zipWith (fun x y => x + y) mu oc = cc)
    (hoc : oc.length = mu.length)
    (hwB : ∀ w ∈ B, w.content.length = mu.length) :
    ∀ A : List HVec,
      (blockcount.pairIdx A (fun v => v) B cc).filter
          (fun t => (t.1 : HVec).content == mu)
        = (A.filter (fun w => w.content == mu)).flatMap (fun a =>
            (B.filter (fun w => w.content == oc)).map
              (fun b => (a, b)))
  | [] => rfl
  | v :: A => by
    show ((B.flatMap (fun w =>
          if List.zipWith (fun x y => x + y) v.content w.content = cc
            then [(v, w)] else [])
        ++ blockcount.pairIdx A (fun z => z) B cc).filter
        (fun t => (t.1 : HVec).content == mu))
      = ((v :: A).filter (fun w => w.content == mu)).flatMap (fun a =>
          (B.filter (fun w => w.content == oc)).map (fun b => (a, b)))
    rw [ground.filter_append,
      pairIdx_filter B mu oc cc hjoin hoc hwB A]
    by_cases hv : v.content = mu
    · have hvb : (v.content == mu) = true := by
        rw [hv]; exact ground.listEqBeq mu
      rw [pairRow_keep v oc cc (by rw [hv]; exact hjoin)
          (by rw [hv]; exact hoc) B
          (fun x hx => by rw [hv]; exact hwB x hx),
        ground.filter_map (fun b => ((v, b) : HVec × HVec))
          (fun t => (t.1 : HVec).content == mu),
        ground.filter_all _ _ (fun _ _ => hvb),
        ground.filter_cons_true (p := fun w : HVec => w.content == mu)
          (a := v) (l := A) hvb]
      rfl
    · have hvb : (v.content == mu) = false := by
        cases hb : (v.content == mu) with
        | true => exact absurd (ground.listBeqEq hb) hv
        | false => rfl
      rw [pairRow_drop v mu cc hvb B,
        ground.filter_cons_false (p := fun w : HVec => w.content == mu)
          (a := v) (l := A) hvb]
      rfl

/-- The solve-back read at one content of the complementary grid:
the family's slots at that content carry the unit coefficient, the
grid there the two lists' groups' product at the complementary
contents and the value at each member of the first group the
product's own combination, the two groups entering at their own
contents' widths. -/
private theorem pairSolve_at (A B : List HVec) (cc : List Nat)
    (c : List BPair) (d : Nat)
    (hwB : ∀ w ∈ B, w.content.length = d)
    (hiA : indepAll A) (hiB : indepAll B)
    (hc : c.length = (blockcount.pairIdx A (fun v => v) B cc).length)
    (hval : ∀ y ∈ A, ∀ oc : List Nat, oc.length = d →
      List.zipWith (fun u w => u + w) y.content oc = cc →
      poly.unitTail (pairVal (pairFam A B cc c) y oc).coords)
    (mu oc : List Nat) (hmu : mu.length = d) (hoc : oc.length = d)
    (hjoin : List.zipWith (fun x y => x + y) mu oc = cc) :
    poly.unitTail
      (((pairFam A B cc c).filter
        (fun t => t.2.1.content == mu)).map (fun t => t.1)) := by
  have hgrid : ((pairFam A B cc c).filter
        (fun t => t.2.1.content == mu)).map (fun t => t.2)
      = (A.filter (fun w => w.content == mu)).flatMap (fun a =>
          (B.filter (fun w => w.content == oc)).map
            (fun b => (a, b))) :=
    (zipTrip_filter (fun p : HVec × HVec => p.1.content == mu) c
      (blockcount.pairIdx A (fun v => v) B cc) hc).trans
      (pairIdx_filter B mu oc cc hjoin (by rw [hoc, hmu])
        (fun w hw => by rw [hwB w hw, hmu]) A)
  have hlen : (((pairFam A B cc c).filter
        (fun t => t.2.1.content == mu)).map (fun t => t.1)).length
      = ((A.filter (fun w => w.content == mu)).flatMap (fun a =>
          (B.filter (fun w => w.content == oc)).map
            (fun b => (a, b)))).length := by
    rw [ground.length_map, ← hgrid, ground.length_map]
  have hQ : (pairFam A B cc c).filter (fun t => t.2.1.content == mu)
      = List.zipWith (fun cv (t : HVec × HVec) => (cv, t))
          (((pairFam A B cc c).filter
            (fun t => t.2.1.content == mu)).map (fun t => t.1))
          ((A.filter (fun w => w.content == mu)).flatMap (fun a =>
            (B.filter (fun w => w.content == oc)).map
              (fun b => (a, b)))) := by
    rw [← hgrid]
    exact (zipTrip_rebuild _).symm
  refine solveHom (places.monomialsAt mu).length
    (places.monomialsAt oc).length
    (A.filter (fun w => w.content == mu))
    (B.filter (fun w => w.content == oc))
    (blockcount.indepAll_all hiA mu) (blockcount.indepAll_all hiB oc)
    _ hlen ?_
  intro y hy
  have hyc : y.content = mu :=
    ground.listBeqEq (ground.mem_filter_of _ A y hy).2
  have h0 := hval y (ground.mem_filter_of _ A y hy).1 oc hoc
    (by rw [hyc]; exact hjoin)
  rw [pairVal_coords (pairFam A B cc c) y oc, hyc, hQ,
    zipTrip_mapMul y _ _ hlen, zipTrip_mapRow _ _ hlen] at h0
  exact h0

/-- A grid vector over the complementary pair grid whose value
reads every listed first factor at every joined output content at
the sum's unit is the unit family: per first content the value is
the second group's combination at the first group's weighted
pairings, the second group's independence reads those weights back,
and per second member the weights pair the first group against its
every member at the sum's unit, the perpendicular combination the
unit family at the first group's independence —
`lem:dualread`(iii)'s off-join arm at the pair grid.  The width
tier `d`, `hwA`, `hwB` is `con:places`' one-letter-width frame: at
bare-list `zipWith` guards the widths pin the join exact, the second
content determined entrywise from the first
(`ground.addCancelL`); `hiA` and `hiB` are the two groups'
independence, the weights and the perpendicular combination read
back; `hc` is the family's shape at the display's own width; and
`hval`'s output content runs at the join with the width, so a value
is read exactly at the contents the grid carries. -/
theorem pairSolve (A B : List HVec) (cc : List Nat) (c : List BPair)
    (d : Nat)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ w ∈ B, w.content.length = d)
    (hiA : blockcount.indepAll A) (hiB : blockcount.indepAll B)
    (hc : c.length = (pairsAt A B cc).length)
    (hval : ∀ y ∈ A, ∀ oc : List Nat, oc.length = d →
      List.zipWith (fun u w => u + w) y.content oc = cc →
      poly.unitTail (pairVal (pairFam A B cc c) y oc).coords) :
    poly.unitTail c := by
  have hcg : c.length
      = (blockcount.pairIdx A (fun v => v) B cc).length := by
    rw [hc, pairsAt_len A B cc]
  have he : (pairFam A B cc c).map (fun t => t.1) = c :=
    zipTrip_fst c (blockcount.pairIdx A (fun v => v) B cc) hcg
  refine he ▸ poly.unitTail_map (fun t => t.1) (pairFam A B cc c) ?_
  intro t ht
  match pairFam_slots A B cc c t ht with
  | ⟨htA, htB, htj⟩ =>
    refine poly.unitTail_member
      (pairSolve_at A B cc c d hwB hiA hiB hcg hval
        t.2.1.content t.2.2.content (hwA _ htA) (hwB _ htB) htj) t.1
      (ground.mem_map_to (fun (s : BPair × HVec × HVec) => s.1) ?_)
    exact ground.mem_filter_to _ ht (ground.listEqBeq t.2.1.content)


/-! `lem:dualread`(i)'s grid transport: an equivariant map enters the
grid through the second list's solve — per member of the first list
the row over the shared content's slots is the second list's cleared
combination at the coevaluation's coefficients against the graded
solves of the map's values — with the map the determinants' scale of
its own by the round trip, the moved reads at the sum's unit by the
equivariance, and a coefficient family at the unit family mapping
every argument to the unit tail. -/

/-- The solve at the second list's group: the adjugate against the
group's Gram at a value's pairing data, `lem:lowerspan`'s membership
solve at the stated content. -/
private def zSolve (Z : List HVec) (mu : List Nat) (v : List BPair) :
    List BPair :=
  elim.adjP (elim.gramM (groupAt Z mu))
    ((groupAt Z mu).map (fun r => elim.dotP v r))

/-- One first-list member's row over its content's grid slots: the
second list's combination at the coevaluation's coefficients against
the graded solves of the map's values at the group, the member's row
at the member's place in its group. -/
private def gridRow (T : List Nat → elim.Mat) (Y Z : List HVec)
    (mu : List Nat) (j : Nat) : List BPair :=
  elim.combo (groupAt Z mu).length
    ((List.range (groupAt Y mu).length).map (fun k =>
      coScale Y mu * ground.getAt BPair.unit
        (elim.cofVec (elim.gramM (groupAt Y mu)) k) j))
    ((List.range (groupAt Y mu).length).map (fun k =>
      elim.vecScale (coScale Z mu)
        (zSolve Z mu
          (elim.matVec (T mu) (ground.getAt [] (groupAt Y mu) k)))))

/-- A content's block: the content group's rows, one block per
occupied content — the grid's datum (`lem:dualread`(i)). -/
private def gridBlock (T : List Nat → elim.Mat) (Y Z : List HVec)
    (mu : List Nat) : List (List BPair) :=
  (List.range (groupAt Y mu).length).map (gridRow T Y Z mu)

/-- The block's row at a group position is the member's row. -/
private theorem gridBlock_row (T : List Nat → elim.Mat)
    (Y Z : List HVec) (mu : List Nat) (j : Nat)
    (hj : j < (groupAt Y mu).length) :
    ground.getAt [] (gridBlock T Y Z mu) j = gridRow T Y Z mu j := by
  rw [show gridBlock T Y Z mu
      = (List.range (groupAt Y mu).length).map (gridRow T Y Z mu)
    from rfl,
    ground.getAt_map_range ([] : List BPair) _
      (groupAt Y mu).length j,
    if_pos hj]

/-- The block family's read at a member key is its content's
block. -/
private theorem keyAt_tab (T : List Nat → elim.Mat)
    (Y Z : List HVec) :
    ∀ (L : List (List Nat)) (mu : List Nat), mu ∈ L →
    ground.keyAt (fun a b => a == b) [] mu
        (L.map (fun c => (c, gridBlock T Y Z c)))
      = gridBlock T Y Z mu
  | [], _, h => nomatch h
  | c :: L, mu, h => by
    show cond (c == mu) (gridBlock T Y Z c)
        (ground.keyAt (fun a b => a == b) [] mu
          (L.map (fun c => (c, gridBlock T Y Z c))))
      = gridBlock T Y Z mu
    cases hb : (c == mu) with
    | true =>
      rw [ground.listBeqEq hb]
      exact rfl
    | false =>
      refine keyAt_tab T Y Z L mu ?_
      cases h with
      | head =>
        rw [ground.listEqBeq c] at hb
        exact Bool.noConfusion hb
      | tail _ h' => exact h'

/-- The member's position sits inside its content group. -/
private theorem posLt_group (Y : List HVec) (y : HVec)
    (pre suf : List HVec) (hps : pre ++ y :: suf = Y) :
    (pre.filter (fun w => w.content == y.content)).length
      < (groupAt Y y.content).length := by
  show _ < ((Y.filter (fun w => w.content == y.content)).map
    HVec.coords).length
  rw [ground.length_map, ← hps, ground.filter_append,
    ground.length_append,
    ground.filter_cons_true (p := fun w => w.content == y.content)
      (a := y) (ground.listEqBeq y.content)]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _)

/-- The walk emitting one row per first-list member: the member's
row read off its content's block at the member's place in its
group. -/
private def gridGo (tab : List (List Nat × List (List BPair))) :
    List HVec → List HVec → List BPair
  | _, [] => []
  | pre, y :: suf =>
      ground.getAt [] (ground.keyAt (fun a b => a == b) []
          y.content tab)
        ((pre.filter (fun w => w.content == y.content)).length)
        ++ gridGo tab (pre ++ [y]) suf

/-- The equivariant map's grid vector: the map enters the grid
through the second list's solve, one block per occupied content
with each member's row at its place in its group —
`lem:dualread`(i)'s grid transport. -/
def gridOf (T : List Nat → elim.Mat) (Y Z : List HVec) :
    List BPair :=
  gridGo ((ground.dedupL (Y.map HVec.content)).map (fun mu =>
    (mu, gridBlock T Y Z mu))) [] Y

/-- The chunk's width is the group's. -/
private theorem length_chunk (y : HVec) (Z : List HVec) :
    (Z.flatMap (fun z => if y.content = z.content
        then [(y, z)] else [])).length
      = (groupAt Z y.content).length := by
  rw [chunk_map y Z,
    ground.length_map (fun z => (y, z))
      (Z.filter (fun w => w.content == y.content))]
  exact (ground.length_map HVec.coords
    (Z.filter (fun w => w.content == y.content))).symm

/-- The row sits at the group's width. -/
private theorem length_gridRow (T : List Nat → elim.Mat)
    (Y Z : List HVec) (mu : List Nat) (j : Nat) :
    (gridRow T Y Z mu j).length = (groupAt Z mu).length := by
  refine elim.length_combo (groupAt Z mu).length _ _
    (elim.rowsLen_map _ _ _ (fun k _ => ?_))
  rw [elim.length_vecScale]
  show (elim.adjP (elim.gramM (groupAt Z mu))
    ((groupAt Z mu).map (fun r => elim.dotP
      (elim.matVec (T mu) (ground.getAt [] (groupAt Y mu) k))
      r))).length = _
  rw [elim.length_adjP]
  exact ground.length_map _ (groupAt Z mu)

/-- The walk's width is the grid's, at every faithful counter. -/
private theorem gridGo_len (T : List Nat → elim.Mat)
    (Y Z : List HVec) :
    ∀ (suf pre : List HVec), pre ++ suf = Y →
      (gridGo ((ground.dedupL (Y.map HVec.content)).map (fun mu =>
          (mu, gridBlock T Y Z mu))) pre suf).length
        = (suf.flatMap (fun y => Z.flatMap (fun z =>
            if y.content = z.content then [(y, z)] else []))).length
  | [], _, _ => rfl
  | y :: suf, pre, hps => by
    show (ground.getAt [] (ground.keyAt (fun a b => a == b) []
          y.content ((ground.dedupL (Y.map HVec.content)).map
            (fun mu => (mu, gridBlock T Y Z mu))))
        ((pre.filter (fun w => w.content == y.content)).length)
      ++ gridGo ((ground.dedupL (Y.map HVec.content)).map (fun mu =>
          (mu, gridBlock T Y Z mu))) (pre ++ [y]) suf).length
      = ((Z.flatMap fun z => if y.content = z.content
          then [(y, z)] else [])
        ++ suf.flatMap (fun y => Z.flatMap (fun z =>
          if y.content = z.content then [(y, z)] else []))).length
    have hyY : y ∈ Y := hps ▸ ground.mem_append_right pre
      (List.Mem.head suf)
    have hrow : ground.getAt [] (ground.keyAt (fun a b => a == b) []
          y.content ((ground.dedupL (Y.map HVec.content)).map
            (fun mu => (mu, gridBlock T Y Z mu))))
        ((pre.filter (fun w => w.content == y.content)).length)
        = gridRow T Y Z y.content
          ((pre.filter (fun w =>
            w.content == y.content)).length) := by
      rw [keyAt_tab T Y Z (ground.dedupL (Y.map HVec.content))
          y.content
          (ground.mem_dedupL (ground.mem_map_to HVec.content hyY)),
        gridBlock_row T Y Z y.content _ (posLt_group Y y pre suf hps)]
    rw [ground.length_append, ground.length_append, hrow,
      length_gridRow, length_chunk,
      gridGo_len T Y Z suf (pre ++ [y])
        (by rw [ground.append_assoc]; exact hps)]

/-- The grid vector sits at the grid's own width. -/
theorem gridOf_len (T : List Nat → elim.Mat) (Y Z : List HVec) :
    (gridOf T Y Z).length = (dualPairs Y Z).length :=
  gridGo_len T Y Z Y [] rfl

/-- A coefficient family at the unit family maps every argument to
the unit tail: each filtered coefficient reads the unit and the
combination reads the unit tail with them. -/
theorem invFam_unitTail (Y Z : List HVec) (c : List BPair) (x : HVec)
    (hc : poly.unitTail c) :
    poly.unitTail (mapAt (invFam Y Z c) x).coords := by
  rw [mapAt_coords]
  refine elim.unitTail_combo_of _ _ _ (poly.unitTail_map _ _ ?_)
  intro t ht
  have h2 : t.1 ∈ c := (zipTrip_mem c (dualPairs Y Z) t
    (ground.mem_filter_of _ _ _ ht).1).1
  exact BPair.oneValue_trans
    (BPair.mul_congr_left (poly.unitTail_member hc t.1 h2))
    (BPair.unit_mul (elim.dotP t.2.1.coords x.coords))


/-! `lem:dualread`(i)'s second round trip: the composite at an
invariant reads its `det G`-multiple, the identity at each first
slot over the list's span — the first slot's cleared combination
reading the adjugate solve at the determinant against the
combination's coefficients, the clearing withdrawn at the product's
injectivity. -/

/-- The product's rotation at three factors. -/
private theorem mul_rot3 (a b c : BPair) : a * (b * c) = b * (c * a) := by
  rw [BPair.mul_left_comm, BPair.mul_comm a c]

/-- The adjugate solve's entry at a first slot cleared into the
group's span: the cleared pairings read the Gram against the
combination's coefficients, and the symmetric Gram's row fold
against the cofactor vectors collapses at the determinant on the
entry's own key. -/
private theorem adjP_span_entry (grp : List HVec) (f : HVec)
    (c₀ : BPair) (cs : List BPair) (n : Nat)
    (hrows : elim.rowsLen n (grp.map HVec.coords))
    (hcsl : cs.length = grp.length)
    (hone : poly.oneValue (elim.vecScale c₀ f.coords)
      (elim.combo n cs (grp.map HVec.coords)))
    (j : Nat) (hj : j < grp.length) :
    (c₀ * ground.getAt BPair.unit
        (elim.adjP (elim.gramM (grp.map HVec.coords))
          (grp.map (fun w => elim.dotP f.coords w.coords))) j).oneValue
      (ground.getAt BPair.unit cs j
        * elim.detL (elim.gramM (grp.map HVec.coords))) := by
  have hLl : (grp.map HVec.coords).length = grp.length :=
    ground.length_map _ grp
  have hGl : (elim.gramM (grp.map HVec.coords)).length
      = grp.length := by
    rw [elim.sqAt_len (elim.gram_sqAt (grp.map HVec.coords)), hLl]
  have hGr : elim.rowsLen grp.length
      (elim.gramM (grp.map HVec.coords)) := by
    have h := elim.rowsLen_of_sqAt
      (elim.gram_sqAt (grp.map HVec.coords))
    rw [hLl] at h
    exact h
  -- the cleared pairing at a member reads the Gram's row against
  -- the coefficients, one index fold
  have hrowk : ∀ k, k < grp.length →
      (c₀ * elim.dotP f.coords
        (ground.getAt (⟨[], []⟩ : HVec) grp k).coords).oneValue
        (ground.famFold BPair.add BPair.unit (fun b =>
          ground.getAt BPair.unit cs b
            * ground.getAt BPair.unit
              (ground.getAt ([] : List BPair)
                (elim.gramM (grp.map HVec.coords)) k) b)
          (List.range grp.length)) := by
    intro k hk
    rw [← elim.dotP_map_range
        (fun b => ground.getAt BPair.unit
          (ground.getAt ([] : List BPair)
            (elim.gramM (grp.map HVec.coords)) k) b)
        grp.length cs hcsl,
      ground.range_map_getAt BPair.unit grp.length _
        (elim.rowsLen_getAt _ k hGr (by rw [hGl]; exact hk)),
      elim.dotP_comm f.coords]
    refine BPair.oneValue_trans
      (span_pair_row grp f.coords c₀ cs n hrows hone k hk) ?_
    rw [show elim.matVec (elim.gramM (grp.map HVec.coords)) cs
        = (elim.gramM (grp.map HVec.coords)).map
          (fun r => elim.dotN r cs) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit
        (fun r => elim.dotN r cs) _ k (by rw [hGl]; exact hk),
      elim.dotP_comm cs]
    exact elim.dotN_read _ cs
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl c₀)
      (BPair.oneValue_symm
        (adjP_entry (elim.gramM (grp.map HVec.coords))
          (grp.map (fun w => elim.dotP f.coords w.coords))
          (by rw [ground.length_map, hGl]) j
          (by rw [hGl]; exact hj)))) ?_
  rw [hGl]
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (ground.foldB_mul_left c₀ _ (List.range grp.length))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => ground.famFold BPair.add BPair.unit (fun b =>
        ground.getAt BPair.unit cs b
          * (ground.getAt BPair.unit
              (ground.getAt ([] : List BPair)
                (elim.gramM (grp.map HVec.coords)) k) b
            * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j))
        (List.range grp.length))
      (List.range grp.length) (fun k hk0 => ?_)) ?_
  · have hk : k < grp.length := ground.ltOfMem hk0
    rw [ground.getAt_map (⟨[], []⟩ : HVec) BPair.unit
        (fun w => elim.dotP f.coords w.coords) grp k hk,
      ← BPair.mul_assoc]
    refine BPair.oneValue_trans
      (BPair.mul_congr (hrowk k hk) (BPair.oneValue_refl _)) ?_
    rw [BPair.mul_comm
      (ground.famFold BPair.add BPair.unit _ (List.range grp.length))
      (ground.getAt BPair.unit
        (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)]
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (ground.foldB_mul_left _ _ (List.range grp.length))) ?_
    exact BPair.oneValue_of_eq
      (ground.famFold_congr_all BPair.add BPair.unit _ _
        (fun b => mul_rot3 _ _ _) (List.range grp.length))
  refine BPair.oneValue_trans
    (ground.foldB_swapL _ (List.range grp.length)
      (List.range grp.length)) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun b => ground.getAt BPair.unit cs b
        * (if j = b
          then elim.detL (elim.gramM (grp.map HVec.coords))
          else BPair.unit))
      (List.range grp.length) (fun b hb0 => ?_)) ?_
  · have hb : b < grp.length := ground.ltOfMem hb0
    refine BPair.oneValue_trans
      (ground.foldB_mul_left _ _ (List.range grp.length)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => ground.getAt BPair.unit
            (ground.getAt ([] : List BPair)
              (elim.gramM (grp.map HVec.coords)) b) k
          * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
        (List.range grp.length) (fun k hk0 =>
          BPair.oneValue_of_eq (by
            rw [grp_sym grp k (ground.ltOfMem hk0) b hb]))) ?_
    exact elim.adjP_row_fold (elim.gramM (grp.map HVec.coords))
      (grp_sqAt grp) (grp_sym grp) b j hb hj
      (fun k => ground.getAt BPair.unit
        (ground.getAt ([] : List BPair)
          (elim.gramM (grp.map HVec.coords)) b) k)
      (fun _ _ => rfl)
  refine ground.foldB_pickRange _ j _ grp.length hj ?_ ?_
  · rw [if_pos (show j = j from rfl)]
    exact BPair.oneValue_refl _
  · intro t _ htj
    rw [if_neg (fun he => htj he.symm)]
    exact BPair.mul_unit _

/-- The block's double fold at an argument's pairings against a
first slot's collapses at the first slot's span read: the fold
over the second key collects at the adjugate solve, the solve's
entries read the combination's coefficients against the
determinant, and the coefficients' fold against the argument's
pairings is the cleared first slot's own pairing against the
argument, the clearing withdrawn at the product's injectivity. -/
private theorem trip_collapse (grp : List HVec) (s : BPair)
    (x f : HVec)
    (hsp : elim.spanRel f.coords.length (grp.map HVec.coords)
      f.coords) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun k =>
        (s * ground.getAt BPair.unit
            (elim.cofVec (elim.gramM (grp.map HVec.coords)) k) j)
          * (elim.dotP (ground.getAt (⟨[], []⟩ : HVec) grp j).coords
              x.coords
            * elim.dotP f.coords
              (ground.getAt (⟨[], []⟩ : HVec) grp k).coords))
        (List.range grp.length))
      (List.range grp.length)).oneValue
      ((s * elim.detL (elim.gramM (grp.map HVec.coords)))
        * elim.dotP f.coords x.coords) := by
  have hLl : (grp.map HVec.coords).length = grp.length :=
    ground.length_map _ grp
  refine BPair.oneValue_trans
    (block_oneF grp s (fun w => elim.dotP w.coords x.coords)
      (fun w => elim.dotP f.coords w.coords)) ?_
  rw [BPair.mul_assoc]
  refine BPair.mul_congr (BPair.oneValue_refl s) ?_
  match elim.span_elim hsp with
  | ⟨c₀, cs, hc₀, hcsl, hone⟩ =>
    have hcsl' : cs.length = grp.length := hcsl.trans hLl
    refine ground.mulCancel hc₀ ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (ground.foldB_mul_left c₀ _ (List.range grp.length))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun j => elim.detL (elim.gramM (grp.map HVec.coords))
          * (ground.getAt BPair.unit cs j
            * elim.dotP (ground.getAt (⟨[], []⟩ : HVec) grp j).coords
              x.coords))
        (List.range grp.length) (fun j hj0 => ?_)) ?_
    · rw [BPair.mul_left_comm c₀]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (adjP_span_entry grp f c₀ cs f.coords.length hsp.1 hcsl'
            hone j (ground.ltOfMem hj0))) ?_
      exact BPair.oneValue_of_eq (BPair.mul_rot3r _ _ _)
    refine BPair.oneValue_trans
      (ground.foldB_mul_left _ _ (List.range grp.length)) ?_
    rw [← elim.dotP_map_range
        (fun j => elim.dotP (ground.getAt (⟨[], []⟩ : HVec) grp j).coords
          x.coords)
        grp.length cs hcsl',
      show (List.range grp.length).map
          (fun j => elim.dotP (ground.getAt (⟨[], []⟩ : HVec) grp j).coords
            x.coords)
        = (grp.map HVec.coords).map (fun row => elim.dotP x.coords row)
        from by
        rw [ground.map_map,
          ← ground.map_map (ground.getAt (⟨[], []⟩ : HVec) grp)
            (fun w => elim.dotP w.coords x.coords),
          ground.range_map_getAt (⟨[], []⟩ : HVec) grp.length grp rfl]
        exact ground.map_congr_members _ _ grp
          (fun w _ => elim.dotP_comm w.coords x.coords)]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm
          (elim.dotP_combo cs (grp.map HVec.coords) x.coords
            f.coords.length hsp.1))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (elim.dotP_oneValue_right _ _ _ (poly.oneValue_symm hone))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (elim.dotP_vecScale_right x.coords f.coords c₀)) ?_
    rw [BPair.mul_left_comm, elim.dotP_comm x.coords f.coords]
    exact BPair.oneValue_refl _

/-- The map's filter at a withdrawn content is the vacant family. -/
private theorem tripFilter_none (T : List Nat → elim.Mat)
    (Y : List HVec) (xc : List Nat)
    (h0 : ground.countOf xc
      (ground.dedupL (Y.map HVec.content)) = 0) :
    (mapInv T Y).filter (fun t => t.2.1.content == xc) = [] := by
  show ((coevData Y).map (fun t =>
      (t.1, t.2.1, (⟨t.2.2.content,
        elim.matVec (T t.2.2.content) t.2.2.coords⟩
          : HVec)))).filter
      (fun t => t.2.1.content == xc) = _
  rw [ground.filter_map
      (fun t : BPair × HVec × HVec =>
        (t.1, t.2.1, (⟨t.2.2.content,
          elim.matVec (T t.2.2.content) t.2.2.coords⟩
            : HVec)))
      (fun t => t.2.1.content == xc) (coevData Y)]
  show ((coevData Y).filter
      (fun t : BPair × HVec × HVec =>
        t.2.1.content == xc)).map
      (fun t => (t.1, t.2.1, (⟨t.2.2.content,
        elim.matVec (T t.2.2.content) t.2.2.coords⟩
          : HVec))) = _
  rw [coevData_flat Y, coevFilter_none Y xc _ h0]
  rfl

/-- The entries' rearrangement at the opened second slot: the
member's coefficient and coordinate cross to the outside, the
block's weight and the two pairings collecting inside. -/
private theorem trip_arrange (s c A c' F w : BPair) :
    ((s * c) * A) * ((c' * F) * w)
      = (c' * w) * ((s * c) * (A * F)) := by
  rw [BPair.mul_comm (c' * F) w,
    ← BPair.mul_assoc ((s * c) * A) w (c' * F),
    BPair.mul_comm ((s * c) * A) w,
    BPair.mul_assoc w ((s * c) * A) (c' * F),
    BPair.mul_assoc (s * c) A (c' * F),
    BPair.mul_left_comm A c' F,
    BPair.mul_left_comm (s * c) c' (A * F),
    ← BPair.mul_assoc w c' ((s * c) * (A * F)),
    BPair.mul_comm w c']

/-- The entries' collection at the scale: the determinant crosses
to the outside of the member's weighted coordinate. -/
private theorem entry_collect (c w D F : BPair) :
    (c * w) * (D * F) = D * ((c * F) * w) := by
  rw [BPair.mul_left_comm (c * w) D F, BPair.mul_right_comm c w F]

/-- The composite at an invariant reads its `det G`-multiple at
every argument: the map's matrix family at the coevaluation's second
slot, read back through the map, is the determinant's scale of the
map's own value — `lem:dualread`(i)'s second round trip, the identity
at each first slot over the list's span, the first slot's cleared
combination reading the adjugate solve at the determinant against
the combination's coefficients with the clearing withdrawn at the
product's injectivity, the members' sized coordinate families at
matched contents the format's frame. -/
theorem mapMat_trip (P : List (BPair × HVec × HVec)) (Y : List HVec)
    (x : HVec)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content)
    (hfi : ∀ t ∈ P, elim.spanRel (t.2.1 : HVec).coords.length
      (blockcount.groupAt Y (t.2.1 : HVec).content)
      (t.2.1 : HVec).coords) :
    poly.oneValue (mapAt (mapInv (mapMat P) Y) x).coords
      (elim.vecScale (detAll Y) (mapAt P x).coords) := by
  have hW := filterRowsW P x.content hsz hm
  have hT : (mapMat P x.content).length
      = (places.monomialsAt x.content).length :=
    ground.length_mapRange _ _
  have hgc : ∀ w ∈ Y.filter (fun w' =>
      w'.content == x.content), w.content = x.content :=
    fun w hw =>
      ground.listBeqEq (ground.mem_filter_of _ _ _ hw).2
  have hfx : ∀ t ∈ P.filter (fun t => t.2.1.content == x.content),
      elim.spanRel (t.2.1 : HVec).coords.length
        ((Y.filter (fun w => w.content == x.content)).map HVec.coords)
        (t.2.1 : HVec).coords := by
    intro t ht
    match ground.mem_filter_of _ P t ht with
    | ⟨htP, htc⟩ =>
      have h := hfi t htP
      rw [ground.listBeqEq htc] at h
      exact h
  match hYf : Y.filter (fun w => w.content == x.content) with
  | [] =>
    have h0 : ground.countOf x.content
        (ground.dedupL (Y.map HVec.content)) = 0 := by
      match Nat.eq_zero_or_pos (ground.countOf x.content
          (ground.dedupL (Y.map HVec.content))) with
      | .inl h => exact h
      | .inr hp =>
        match ground.mem_map_of HVec.content Y _
          (ground.mem_of_dedupL (ground.mem_of_countOf_pos _ _ hp)) with
        | ⟨w, hwY, hwc⟩ =>
          have hwf : w ∈ Y.filter (fun w' => w'.content == x.content) :=
            ground.mem_filter_to _ hwY
              (by rw [hwc]; exact ground.listEqBeq x.content)
          rw [hYf] at hwf
          exact nomatch hwf
    refine poly.unitTail_oneValue ?_ ?_
    · rw [mapAt_coords, tripFilter_none (mapMat P) Y x.content h0]
      exact poly.unitTail_replicate (places.monomialsAt x.content).length
    · refine elim.unitTail_vecScale _ _ ?_
      rw [mapAt_coords]
      refine elim.unitTail_combo_of _ _ _ ?_
      refine poly.unitTail_map _ _ (fun t ht => ?_)
      have hs := hfx t ht
      rw [hYf] at hs
      match elim.span_elim hs with
      | ⟨c₀, _, hc₀, _, hone⟩ =>
        exact elim.oneValue_mul_unit t.1 _
          (elim.dotP_null_tail_left _ _
            (elim.unitTail_unscale c₀ hc₀ _
              (poly.oneValue_unitTail hone
                (elim.unitTail_combo_rows _ _ _
                  (fun k hk => absurd hk (Nat.not_lt_zero k))))))
  | g :: rest =>
    have hgmem : g ∈ Y.filter
        (fun w => w.content == x.content) := by
      rw [hYf]
      exact List.Mem.head rest
    have hgY : g ∈ Y := (ground.mem_filter_of _ _ _ hgmem).1
    have hgc' : g.content = x.content :=
      ground.listBeqEq (ground.mem_filter_of _ _ _ hgmem).2
    have hxm : x.content ∈ Y.map HVec.content := by
      rw [← hgc']
      exact ground.mem_map_to HVec.content hgY
    have h1 : ground.countOf x.content
        (ground.dedupL (Y.map HVec.content)) = 1 :=
      ground.countOf_dedupL_one hxm
    have hrows := tripRows (mapMat P) Y x.content h1 hT
    refine poly.ov_of_getAt (fun r => ?_)
    by_cases hr : r < (places.monomialsAt x.content).length
    · rw [elim.getAt_vecScale (detAll Y) _ r (by
        rw [mapAt_coords, elim.length_combo _ _ _ hW]
        exact hr)]
      refine BPair.oneValue_trans
        (trip_grid (mapMat P) Y x h1 hrows r hr) ?_
      -- the moved second slot's entry opens at the map's own fold
      -- over the family, the member's coefficient and coordinate
      -- crossing to the outside
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun j => ground.famFold BPair.add BPair.unit (fun k =>
            ground.famFold BPair.add BPair.unit
              (fun t : BPair × HVec × HVec =>
                (t.1 * ground.getAt BPair.unit t.2.2.coords r)
                  * ((coScale Y x.content
                      * ground.getAt BPair.unit
                        (elim.cofVec (elim.gramM
                          ((Y.filter (fun w =>
                            w.content == x.content)).map
                            HVec.coords)) k) j)
                    * (elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                          (Y.filter (fun w =>
                            w.content == x.content)) j).coords
                          x.coords
                      * elim.dotP t.2.1.coords
                        (ground.getAt (⟨[], []⟩ : HVec)
                          (Y.filter (fun w =>
                            w.content == x.content)) k).coords)))
              (P.filter (fun t => t.2.1.content == x.content)))
            (List.range (Y.filter (fun w =>
              w.content == x.content)).length))
          (List.range (Y.filter (fun w =>
            w.content == x.content)).length)
          (fun j _ => ground.foldB_congr_members _ _
            (List.range (Y.filter (fun w =>
              w.content == x.content)).length)
            (fun k hk0 => ?_))) ?_
      · have hk : k < (Y.filter (fun w =>
            w.content == x.content)).length :=
          ground.ltOfMem hk0
        have hkc : (ground.getAt (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == x.content))
            k).content = x.content :=
          hgc _ (ground.mem_getAt _ _ k hk)
        have hEk : (ground.getAt BPair.unit
            (elim.matVec (mapMat P (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).content)
              (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).coords) r).oneValue
            (ground.famFold BPair.add BPair.unit
              (fun t : BPair × HVec × HVec =>
                (t.1 * elim.dotP t.2.1.coords
                    (ground.getAt (⟨[], []⟩ : HVec)
                      (Y.filter (fun w =>
                        w.content == x.content)) k).coords)
                  * ground.getAt BPair.unit t.2.2.coords r)
              (P.filter (fun t => t.2.1.content == x.content))) := by
          rw [hkc]
          refine BPair.oneValue_trans
            (poly.oneValue_getAt r
              (mapMat_read P x.content _ hsz hm)) ?_
          rw [mapAt_coords,
            show (⟨x.content, (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).coords⟩ : HVec).content = x.content from rfl,
            show (⟨x.content, (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).coords⟩ : HVec).coords
              = (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                k).coords from rfl]
          refine BPair.oneValue_trans
            (elim.combo_getAt _ _ _ r hW hr) ?_
          rw [ground.map_map, elim.dotP_map_pair]
          exact BPair.oneValue_refl _
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hEk) ?_
        refine BPair.oneValue_trans
          (BPair.oneValue_symm (ground.foldB_mul_left _ _ _)) ?_
        refine BPair.oneValue_of_eq
          (ground.famFold_congr_all BPair.add BPair.unit _ _
            (fun t => ?_) _)
        exact trip_arrange _ _ _ _ _ _
      -- the family's fold crosses to the outside
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun j => ground.famFold BPair.add BPair.unit
            (fun t : BPair × HVec × HVec =>
              ground.famFold BPair.add BPair.unit (fun k =>
                (t.1 * ground.getAt BPair.unit t.2.2.coords r)
                  * ((coScale Y x.content
                      * ground.getAt BPair.unit
                        (elim.cofVec (elim.gramM
                          ((Y.filter (fun w =>
                            w.content == x.content)).map
                            HVec.coords)) k) j)
                    * (elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                          (Y.filter (fun w =>
                            w.content == x.content)) j).coords
                          x.coords
                      * elim.dotP t.2.1.coords
                        (ground.getAt (⟨[], []⟩ : HVec)
                          (Y.filter (fun w =>
                            w.content == x.content)) k).coords)))
                (List.range (Y.filter (fun w =>
                  w.content == x.content)).length))
            (P.filter (fun t => t.2.1.content == x.content)))
          (List.range (Y.filter (fun w =>
            w.content == x.content)).length)
          (fun j _ => ground.foldB_swapL _ _ _)) ?_
      refine BPair.oneValue_trans (ground.foldB_swapL _ _ _) ?_
      -- per member the block's double fold collapses at the first
      -- slot's span read
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun t : BPair × HVec × HVec =>
            detAll Y * ((t.1 * elim.dotP t.2.1.coords x.coords)
              * ground.getAt BPair.unit t.2.2.coords r))
          (P.filter (fun t => t.2.1.content == x.content))
          (fun t ht0 => ?_)) ?_
      · refine BPair.oneValue_trans
          (ground.foldB_congr_members _
            (fun j => (t.1 * ground.getAt BPair.unit t.2.2.coords r)
              * ground.famFold BPair.add BPair.unit (fun k =>
                (coScale Y x.content
                    * ground.getAt BPair.unit
                      (elim.cofVec (elim.gramM
                        ((Y.filter (fun w =>
                          w.content == x.content)).map
                          HVec.coords)) k) j)
                  * (elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                        (Y.filter (fun w =>
                          w.content == x.content)) j).coords
                        x.coords
                    * elim.dotP t.2.1.coords
                      (ground.getAt (⟨[], []⟩ : HVec)
                        (Y.filter (fun w =>
                          w.content == x.content)) k).coords))
                (List.range (Y.filter (fun w =>
                  w.content == x.content)).length))
            (List.range (Y.filter (fun w =>
              w.content == x.content)).length)
            (fun j _ => ground.foldB_mul_left _ _
              (List.range (Y.filter (fun w =>
                w.content == x.content)).length))) ?_
        refine BPair.oneValue_trans
          (ground.foldB_mul_left _ _
            (List.range (Y.filter (fun w =>
              w.content == x.content)).length)) ?_
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (trip_collapse (Y.filter (fun w => w.content == x.content))
              (coScale Y x.content) x t.2.1
              (hfx t (ground.mem_of_countOf_pos _ _ ht0)))) ?_
        rw [show elim.detL (elim.gramM
              ((Y.filter (fun w =>
                w.content == x.content)).map HVec.coords))
            = blockDet Y x.content from rfl,
          scale_detAll Y x.content h1]
        exact BPair.oneValue_of_eq (entry_collect _ _ _ _)
      refine BPair.oneValue_trans (ground.foldB_mul_left _ _ _) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      refine BPair.oneValue_symm ?_
      rw [mapAt_coords]
      refine BPair.oneValue_trans
        (elim.combo_getAt _ _ _ r hW hr) ?_
      rw [ground.map_map, elim.dotP_map_pair]
      exact BPair.oneValue_refl _
    · rw [ground.getAt_over BPair.unit _ r (by
        rw [mapAt_coords, elim.length_combo _ _ _ hrows]
        exact Nat.le_of_not_lt hr),
      ground.getAt_over BPair.unit _ r (by
        rw [elim.length_vecScale, mapAt_coords,
          elim.length_combo _ _ _ hW]
        exact Nat.le_of_not_lt hr)]
      exact BPair.oneValue_refl _

/-! `lem:dualread`(i)'s grid transport, the solve reads: the graded
solve clears over the second list's span, the two determinants'
product collects to the graded determinant at every content, and the
block folds collect per first member. -/

/-- The two factors collect to the graded determinant at every
content: the skipping product against the block's own determinant,
the unoccupied content's block at the vacant group's determinant. -/
private theorem detZ_split (Z : List HVec) (mu : List Nat) :
    (coScale Z mu * blockDet Z mu).oneValue (detAll Z) := by
  cases hocc : ground.countOf mu
      (ground.dedupL (Z.map HVec.content)) with
  | zero =>
    have hsk : coScale Z mu = detAll Z :=
      ground.foldl_skip_absent BPair.mul (blockDet Z) mu
        (ground.dedupL (Z.map HVec.content)) (BPair.ofNat 1) hocc
    have hnm : ∀ z ∈ Z, (z.content == mu) = false := by
      intro z hz
      cases hb : (z.content == mu) with
      | false => rfl
      | true =>
        have hzc : z.content = mu := ground.listBeqEq hb
        have hmem : mu ∈ ground.dedupL (Z.map HVec.content) :=
          ground.mem_dedupL (hzc ▸ ground.mem_map_to HVec.content hz)
        have hpos := ground.countOf_pos_of_mem hmem
        rw [hocc] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)
    have hgz : Z.filter (fun w => w.content == mu) = [] :=
      ground.filter_false _ Z hnm
    have hbd : (blockDet Z mu).oneValue (BPair.ofNat 1) := by
      show (elim.detL (elim.gramM
        ((Z.filter (fun w => w.content == mu)).map
          HVec.coords))).oneValue (BPair.ofNat 1)
      rw [hgz]
      exact BPair.add_unit (BPair.ofPos .one)
    rw [hsk]
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (detAll Z)) hbd)
      (BPair.mul_ofNat_one (detAll Z))
  | succ k =>
    have h1 : ground.countOf mu
        (ground.dedupL (Z.map HVec.content)) = 1 :=
      Nat.le_antisymm
        (ground.countOf_dedupL_le mu (Z.map HVec.content))
        (hocc ▸ Nat.succ_pos k)
    exact BPair.oneValue_of_eq (scale_detAll Z mu h1)

/-- The block filter's read: a constant-first-slot block is kept
whole at its content and dropped whole off it. -/
private theorem filter_chunkTrip (mu : List Nat) (y : HVec) :
    ∀ (cs : List BPair) (L : List HVec),
      (List.zipWith (fun cv (s : HVec × HVec) => (cv, s.1, s.2)) cs
        (L.map (fun z => (y, z)))).filter
          (fun t => t.2.1.content == mu)
        = (if (y.content == mu) = true
          then List.zipWith (fun cv (s : HVec × HVec) =>
            (cv, s.1, s.2)) cs (L.map (fun z => (y, z)))
          else [])
  | [], L => by
    cases hb : (y.content == mu) with
    | true => rw [if_pos rfl]; exact rfl
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]; exact rfl
  | _ :: _, [] => by
    cases hb : (y.content == mu) with
    | true => rw [if_pos rfl]; exact rfl
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]; exact rfl
  | c :: cs, z :: L => by
    cases hb : (y.content == mu) with
    | true =>
      rw [if_pos rfl]
      show List.filter (fun t => t.2.1.content == mu)
          ((c, y, z) :: List.zipWith (fun cv (s : HVec × HVec) =>
            (cv, s.1, s.2)) cs (L.map (fun z => (y, z)))) = _
      rw [ground.filter_cons_true
          (p := fun t => t.2.1.content == mu)
          (a := ((c, y, z) : BPair × HVec × HVec)) hb,
        filter_chunkTrip mu y cs L, hb, if_pos rfl]
      exact rfl
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]
      show List.filter (fun t => t.2.1.content == mu)
          ((c, y, z) :: List.zipWith (fun cv (s : HVec × HVec) =>
            (cv, s.1, s.2)) cs (L.map (fun z => (y, z)))) = _
      rw [ground.filter_cons_false
          (p := fun t => t.2.1.content == mu)
          (a := ((c, y, z) : BPair × HVec × HVec)) hb,
        filter_chunkTrip mu y cs L, hb,
        if_neg (fun h => Bool.noConfusion h)]

/-- The graded solve clears over the second list's span: the
combination of the solve against the group reads the block
determinant's scale of the value. -/
private theorem solve_clear (Z : List HVec) (mu : List Nat)
    (w : List BPair) (n : Nat)
    (hsp : elim.spanRel n (groupAt Z mu) w) :
    poly.oneValue (elim.combo n (zSolve Z mu w) (groupAt Z mu))
      (elim.vecScale (blockDet Z mu) w) := by
  match elim.span_elim hsp with
  | ⟨c₀, cs, hc₀, hcs, hone⟩ =>
    have hwn : w.length = n := hsp.2.1
    have hrows : elim.rowsLen n (groupAt Z mu) := hsp.1
    have hgl : (groupAt Z mu).length
        = (Z.filter (fun v => v.content == mu)).length :=
      ground.length_map HVec.coords _
    have hzl : (zSolve Z mu w).length = (groupAt Z mu).length := by
      show (elim.adjP _ _).length = _
      rw [elim.length_adjP]
      exact (ground.length_map _ (groupAt Z mu)).symm ▸ rfl
    have hzsp : zSolve Z mu w
        = elim.adjP (elim.gramM
            ((Z.filter (fun v => v.content == mu)).map HVec.coords))
          ((Z.filter (fun v => v.content == mu)).map
            (fun v => elim.dotP w v.coords)) := by
      show elim.adjP (elim.gramM (groupAt Z mu))
          ((groupAt Z mu).map (fun r => elim.dotP w r)) = _
      rw [show groupAt Z mu = (Z.filter (fun v =>
          v.content == mu)).map HVec.coords from rfl,
        ground.map_map]
    have e4 : poly.oneValue (elim.vecScale c₀ (zSolve Z mu w))
        (elim.vecScale (blockDet Z mu) cs) := by
      refine poly.ov_of_getAt (fun j => ?_)
      by_cases hj : j < (Z.filter (fun v => v.content == mu)).length
      · rw [elim.getAt_vecScale c₀ _ j (by
          rw [hzl, hgl]; exact hj),
          elim.getAt_vecScale (blockDet Z mu) _ j (by
          rw [hcs, hgl]; exact hj), hzsp]
        refine BPair.oneValue_trans
          (adjP_span_entry (Z.filter (fun v => v.content == mu))
            (⟨mu, w⟩ : HVec) c₀ cs n hrows (by rw [hcs]; exact hgl)
            hone j hj) ?_
        exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
      · rw [ground.getAt_over BPair.unit _ j (by
          rw [elim.length_vecScale, hzl, hgl]
          exact Nat.le_of_not_lt hj),
          ground.getAt_over BPair.unit _ j (by
          rw [elim.length_vecScale, hcs, hgl]
          exact Nat.le_of_not_lt hj)]
        exact BPair.oneValue_refl _
    refine poly.ov_of_getAt (fun i => ?_)
    by_cases hi : i < n
    · refine ground.mulCancel hc₀ ?_
      rw [elim.getAt_vecScale (blockDet Z mu) w i (by
        rw [hwn]; exact hi)]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c₀)
          (elim.combo_getAt n (zSolve Z mu w) (groupAt Z mu) i
            hrows hi)) ?_
      rw [elim.dotP_comm (zSolve Z mu w)
        ((groupAt Z mu).map (fun r => ground.getAt BPair.unit r i))]
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (elim.dotP_vecScale_right
          ((groupAt Z mu).map (fun r => ground.getAt BPair.unit r i))
          (zSolve Z mu w) c₀)) ?_
      refine BPair.oneValue_trans
        (elim.dotP_oneValue_right _ _ _ e4) ?_
      refine BPair.oneValue_trans
        (elim.dotP_vecScale_right _ cs (blockDet Z mu)) ?_
      rw [elim.dotP_comm
        ((groupAt Z mu).map (fun r => ground.getAt BPair.unit r i))
        cs]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (blockDet Z mu))
          (BPair.oneValue_symm (elim.combo_getAt n cs
            (groupAt Z mu) i hrows hi))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (blockDet Z mu))
          (poly.oneValue_getAt i (poly.oneValue_symm hone))) ?_
      rw [elim.getAt_vecScale c₀ w i (by rw [hwn]; exact hi),
        ← BPair.mul_assoc, BPair.mul_comm (blockDet Z mu) c₀,
        BPair.mul_assoc]
      exact BPair.oneValue_refl _
    · rw [ground.getAt_over BPair.unit _ i (by
        rw [elim.length_combo n _ _ hrows]
        exact Nat.le_of_not_lt hi),
        ground.getAt_over BPair.unit _ i (by
        rw [elim.length_vecScale, hwn]
        exact Nat.le_of_not_lt hi)]
      exact BPair.oneValue_refl _


/-- The block's fold at a tagged chunk: the coefficients against the
first slot's pairing and the second slots' entry reads collect to
the pairing's scale of the coefficients' fold. -/
private theorem zipTrip_foldW (x : HVec) (r : Nat) (y : HVec) :
    ∀ (cs : List BPair) (L : List HVec), cs.length = L.length →
      (ground.famFold BPair.add BPair.unit
        (fun t => (t.1 * elim.dotP t.2.1.coords x.coords)
          * ground.getAt BPair.unit t.2.2.coords r)
        (List.zipWith (fun cv (s : HVec × HVec) => (cv, s.1, s.2)) cs
          (L.map (fun z => (y, z))))).oneValue
      (elim.dotP y.coords x.coords
        * elim.dotP cs (L.map (fun z =>
            ground.getAt BPair.unit z.coords r)))
  | [], [], _ =>
    BPair.oneValue_symm (BPair.mul_unit (elim.dotP y.coords x.coords))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | c :: cs, z :: L, h => by
    show ((c * elim.dotP y.coords x.coords)
        * ground.getAt BPair.unit z.coords r
      + ground.famFold BPair.add BPair.unit _ _).oneValue
      (elim.dotP y.coords x.coords
        * (c * ground.getAt BPair.unit z.coords r
          + elim.dotP cs (L.map (fun z =>
              ground.getAt BPair.unit z.coords r))))
    rw [BPair.left_distrib, BPair.mul_comm c (elim.dotP y.coords x.coords),
      BPair.mul_assoc]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (zipTrip_foldW x r y cs L (Nat.succ.inj h))

/-- One block's collection: the tagged chunk's fold reads the graded
determinant's scale of the coevaluation coefficients' fold at the
map values' entry reads, the graded solve clearing per group
member. -/
private theorem block_val (T : List Nat → elim.Mat) (Y Z : List HVec)
    (x : HVec) (r : Nat)
    (hr : r < (places.monomialsAt x.content).length)
    (hT : (T x.content).length = (places.monomialsAt x.content).length)
    (hZrows : elim.rowsLen (places.monomialsAt x.content).length
      (groupAt Z x.content))
    (hYrows : elim.rowsLen (places.monomialsAt x.content).length
      (groupAt Y x.content))
    (hfZ : ∀ v ∈ groupAt Y x.content,
      elim.spanRel v.length (groupAt Z x.content)
        (elim.matVec (T x.content) v))
    (y : HVec) (j : Nat) :
    (ground.famFold BPair.add BPair.unit
      (fun t => (t.1 * elim.dotP t.2.1.coords x.coords)
        * ground.getAt BPair.unit t.2.2.coords r)
      (List.zipWith (fun cv (s : HVec × HVec) => (cv, s.1, s.2))
        (gridRow T Y Z x.content j)
        ((Z.filter (fun v => v.content == x.content)).map
          (fun z => (y, z))))).oneValue
    (detAll Z * ground.famFold BPair.add BPair.unit (fun k =>
      ((coScale Y x.content * ground.getAt BPair.unit
          (elim.cofVec (elim.gramM (groupAt Y x.content)) k) j)
        * elim.dotP y.coords x.coords)
        * ground.getAt BPair.unit
          (elim.matVec (T x.content)
            (ground.getAt [] (groupAt Y x.content) k)) r)
      (List.range (groupAt Y x.content).length)) := by
  have hgl : (groupAt Z x.content).length
      = (Z.filter (fun v => v.content == x.content)).length :=
    ground.length_map HVec.coords _
  have hlen : (gridRow T Y Z x.content j).length
      = (Z.filter (fun v => v.content == x.content)).length := by
    rw [length_gridRow]; exact hgl
  refine BPair.oneValue_trans
    (zipTrip_foldW x r y (gridRow T Y Z x.content j)
      (Z.filter (fun v => v.content == x.content)) hlen) ?_
  have hBrows : elim.rowsLen (groupAt Z x.content).length
      ((List.range (groupAt Y x.content).length).map (fun k =>
        elim.vecScale (coScale Z x.content)
          (zSolve Z x.content
            (elim.matVec (T x.content)
              (ground.getAt [] (groupAt Y x.content) k))))) := by
    refine elim.rowsLen_map _ _ _ (fun k _ => ?_)
    rw [elim.length_vecScale]
    show (elim.adjP (elim.gramM (groupAt Z x.content)) _).length = _
    rw [elim.length_adjP]
    exact ground.length_map _ (groupAt Z x.content)
  have hproj : (Z.filter (fun v => v.content == x.content)).map
      (fun z => ground.getAt BPair.unit z.coords r)
      = (groupAt Z x.content).map (fun row =>
          ground.getAt BPair.unit row r) := by
    show _ = ((Z.filter (fun v => v.content == x.content)).map
      HVec.coords).map (fun row => ground.getAt BPair.unit row r)
    rw [ground.map_map]
  have hinner : (elim.dotP (gridRow T Y Z x.content j)
      ((Z.filter (fun v => v.content == x.content)).map
        (fun z => ground.getAt BPair.unit z.coords r))).oneValue
      (detAll Z * ground.famFold BPair.add BPair.unit (fun k =>
        (coScale Y x.content * ground.getAt BPair.unit
          (elim.cofVec (elim.gramM (groupAt Y x.content)) k) j)
        * ground.getAt BPair.unit
          (elim.matVec (T x.content)
            (ground.getAt [] (groupAt Y x.content) k)) r)
        (List.range (groupAt Y x.content).length)) := by
    rw [elim.dotP_comm, hproj]
    refine BPair.oneValue_trans
      (elim.dotP_combo _ _ _ (groupAt Z x.content).length hBrows) ?_
    rw [ground.map_map, elim.dotP_map_pair]
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => detAll Z
          * ((coScale Y x.content * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (groupAt Y x.content)) k) j)
            * ground.getAt BPair.unit
              (elim.matVec (T x.content)
                (ground.getAt [] (groupAt Y x.content) k)) r))
        (List.range (groupAt Y x.content).length)
        (fun k hk0 => ?_)) ?_
    · have hk : k < (groupAt Y x.content).length := ground.ltOfMem hk0
      have hvmem : ground.getAt [] (groupAt Y x.content) k
          ∈ groupAt Y x.content :=
        ground.mem_getAt [] (groupAt Y x.content) k hk
      have hvlen : (ground.getAt [] (groupAt Y x.content) k).length
          = (places.monomialsAt x.content).length :=
        elim.rowsLen_getAt _ k hYrows hk
      have hspv := hfZ (ground.getAt [] (groupAt Y x.content) k) hvmem
      rw [hvlen] at hspv
      have hclear := solve_clear Z x.content
        (elim.matVec (T x.content)
          (ground.getAt [] (groupAt Y x.content) k))
        (places.monomialsAt x.content).length hspv
      have hentry := poly.oneValue_getAt r hclear
      rw [elim.getAt_vecScale (blockDet Z x.content) _ r (by
        rw [elim.matVec_length, hT]; exact hr)] at hentry
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (elim.dotP_vecScale_right _ _ (coScale Z x.content))) ?_
      rw [elim.dotP_comm]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr (BPair.oneValue_refl (coScale Z x.content))
            (BPair.oneValue_trans
              (BPair.oneValue_symm
                (elim.combo_getAt (places.monomialsAt x.content).length
                  _ (groupAt Z x.content) r hZrows hr))
              hentry))) ?_
      rw [← BPair.mul_assoc (coScale Z x.content) (blockDet Z x.content) _,
        ← BPair.mul_assoc _
          (coScale Z x.content * blockDet Z x.content) _,
        BPair.mul_comm _ (coScale Z x.content * blockDet Z x.content),
        BPair.mul_assoc (coScale Z x.content * blockDet Z x.content) _ _]
      exact BPair.mul_congr (detZ_split Z x.content)
        (BPair.oneValue_refl _)
    · exact ground.foldB_mul_left (detAll Z) _ _
  refine BPair.oneValue_trans
    (BPair.mul_congr
      (BPair.oneValue_refl (elim.dotP y.coords x.coords)) hinner) ?_
  · rw [← BPair.mul_assoc _ (detAll Z) _,
      BPair.mul_comm (elim.dotP y.coords x.coords) (detAll Z),
      BPair.mul_assoc (detAll Z) _ _]
    refine BPair.mul_congr (BPair.oneValue_refl (detAll Z)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (ground.foldB_mul_left
        (elim.dotP y.coords x.coords) _ _)) ?_
    refine BPair.oneValue_of_eq
      (ground.famFold_congr_all BPair.add BPair.unit _ _ (fun k => ?_)
        (List.range (groupAt Y x.content).length))
    rw [← BPair.mul_assoc, BPair.mul_comm (elim.dotP y.coords x.coords) _,
      BPair.mul_assoc]


/-- A grid pair's second slot sits in the second list at the first
slot's content. -/
private theorem dualPairs_mem (Y Z : List HVec) (y z : HVec)
    (h : (y, z) ∈ dualPairs Y Z) :
    z ∈ Z ∧ z.content = y.content := by
  match ground.mem_flatMap_of _ Y (y, z) h with
  | ⟨y', _, hyz⟩ =>
    rw [chunk_map y' Z] at hyz
    match ground.mem_map_of _ _ _ hyz with
    | ⟨z', hz', hze⟩ =>
      have hy : y' = y := congrArg Prod.fst hze
      have hz : z' = z := congrArg Prod.snd hze
      have hmem := ground.mem_filter_of _ Z z' hz'
      rw [hz] at hmem
      refine ⟨hmem.1, ?_⟩
      rw [← hy]
      exact ground.listBeqEq hmem.2

/-- The walk's blocks collect: the filtered fold over the grid at
the coefficient family reads the graded determinant's scale of the
coevaluation's double fold at the group offsets. -/
private theorem go_val (T : List Nat → elim.Mat) (Y Z : List HVec)
    (x : HVec) (r : Nat)
    (hr : r < (places.monomialsAt x.content).length)
    (hT : (T x.content).length = (places.monomialsAt x.content).length)
    (hZrows : elim.rowsLen (places.monomialsAt x.content).length
      (groupAt Z x.content))
    (hYrows : elim.rowsLen (places.monomialsAt x.content).length
      (groupAt Y x.content))
    (hfZ : ∀ v ∈ groupAt Y x.content,
      elim.spanRel v.length (groupAt Z x.content)
        (elim.matVec (T x.content) v)) :
    ∀ (suf pre : List HVec), pre ++ suf = Y →
      (ground.famFold BPair.add BPair.unit
        (fun t => (t.1 * elim.dotP t.2.1.coords x.coords)
          * ground.getAt BPair.unit t.2.2.coords r)
        (List.filter (fun t => t.2.1.content == x.content)
          (List.zipWith (fun cv (s : HVec × HVec) => (cv, s.1, s.2))
            (gridGo ((ground.dedupL (Y.map HVec.content)).map
              (fun mu => (mu, gridBlock T Y Z mu))) pre suf)
            (suf.flatMap (fun y => Z.flatMap (fun z =>
              if y.content = z.content
              then [(y, z)] else [])))))).oneValue
      (detAll Z * ground.famFold BPair.add BPair.unit (fun i =>
        ground.famFold BPair.add BPair.unit (fun k =>
          ((coScale Y x.content * ground.getAt BPair.unit
              (elim.cofVec (elim.gramM (groupAt Y x.content)) k)
              ((pre.filter (fun w =>
                w.content == x.content)).length + i))
            * elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                (Y.filter (fun w => w.content == x.content))
                ((pre.filter (fun w =>
                  w.content == x.content)).length + i)).coords
                x.coords)
          * ground.getAt BPair.unit
            (elim.matVec (T x.content)
              (ground.getAt [] (groupAt Y x.content) k)) r)
          (List.range (groupAt Y x.content).length))
        (List.range ((suf.filter (fun w =>
          w.content == x.content)).length)))
  | [], pre, _ =>
    BPair.oneValue_symm (BPair.mul_unit (detAll Z))
  | y :: suf, pre, hps => by
    have hyY : y ∈ Y := hps ▸ ground.mem_append_right pre
      (List.Mem.head suf)
    have hrow : ground.getAt [] (ground.keyAt (fun a b => a == b) []
          y.content ((ground.dedupL (Y.map HVec.content)).map
            (fun mu => (mu, gridBlock T Y Z mu))))
        ((pre.filter (fun w => w.content == y.content)).length)
        = gridRow T Y Z y.content
          ((pre.filter (fun w =>
            w.content == y.content)).length) := by
      rw [keyAt_tab T Y Z (ground.dedupL (Y.map HVec.content))
          y.content
          (ground.mem_dedupL (ground.mem_map_to HVec.content hyY)),
        gridBlock_row T Y Z y.content _ (posLt_group Y y pre suf hps)]
    have hlen : (gridRow T Y Z y.content
        ((pre.filter (fun w => w.content == y.content)).length)).length
        = (Z.flatMap (fun z => if y.content = z.content
            then [(y, z)] else [])).length := by
      rw [length_gridRow, length_chunk]
    show (ground.famFold BPair.add BPair.unit _
      (List.filter (fun t => t.2.1.content == x.content)
        (List.zipWith (fun cv (s : HVec × HVec) => (cv, s.1, s.2))
          (ground.getAt [] (ground.keyAt (fun a b => a == b) []
              y.content ((ground.dedupL (Y.map HVec.content)).map
                (fun mu => (mu, gridBlock T Y Z mu))))
              ((pre.filter (fun w =>
                w.content == y.content)).length)
            ++ gridGo ((ground.dedupL (Y.map HVec.content)).map
              (fun mu => (mu, gridBlock T Y Z mu)))
              (pre ++ [y]) suf)
          ((Z.flatMap (fun z => if y.content = z.content
              then [(y, z)] else []))
            ++ suf.flatMap (fun y => Z.flatMap (fun z =>
              if y.content = z.content
              then [(y, z)] else [])))))).oneValue _
    rw [hrow, ground.zipWith_append _ _ _ _ _ hlen,
      ground.filter_append, chunk_map y Z,
      filter_chunkTrip x.content y]
    refine BPair.oneValue_trans
      (ground.famFold_append_ov ground.bpairFoldLaws _ _ _) ?_
    cases hb : (y.content == x.content) with
    | true =>
      rw [if_pos rfl]
      have hyc : y.content = x.content := ground.listBeqEq hb
      have hcoh : ground.getAt (⟨[], []⟩ : HVec)
          (Y.filter (fun w => w.content == x.content))
          ((pre.filter (fun w => w.content == x.content)).length)
          = y := by
        rw [← hps, ground.filter_append,
          ground.filter_cons_true
            (p := fun w => w.content == x.content) (a := y) hb]
        exact ground.getAt_append_add (⟨[], []⟩ : HVec)
          (pre.filter (fun w => w.content == x.content))
          (y :: suf.filter (fun w => w.content == x.content)) 0
      have hoff : ((pre ++ [y]).filter (fun w =>
          w.content == x.content)).length
          = (pre.filter (fun w => w.content == x.content)).length
            + 1 := by
        rw [ground.filter_append, ground.length_append,
          ground.filter_cons_true
            (p := fun w => w.content == x.content) (a := y) hb]
        exact rfl
      rw [hyc]
      have hhead := block_val T Y Z x r hr hT hZrows hYrows hfZ y
        ((pre.filter (fun w => w.content == x.content)).length)
      have htail := go_val T Y Z x r hr hT hZrows hYrows hfZ suf
        (pre ++ [y]) (by rw [ground.append_assoc]; exact hps)
      refine BPair.oneValue_trans (BPair.add_congr hhead htail) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.left_distrib (detAll Z) _ _).symm) ?_
      refine BPair.mul_congr (BPair.oneValue_refl (detAll Z)) ?_
      rw [show ((y :: suf).filter (fun w =>
          w.content == x.content)).length
          = (suf.filter (fun w => w.content == x.content)).length + 1
        from by
          rw [ground.filter_cons_true
            (p := fun w => w.content == x.content) (a := y) hb]
          exact rfl,
        ground.range_cons]
      show BPair.oneValue (_ + _) (_ + _)
      refine BPair.add_congr ?_ ?_
      · show (ground.famFold BPair.add BPair.unit (fun k =>
            ((coScale Y x.content * ground.getAt BPair.unit
                (elim.cofVec (elim.gramM (groupAt Y x.content)) k)
                ((pre.filter (fun w =>
                  w.content == x.content)).length))
              * elim.dotP y.coords x.coords)
            * ground.getAt BPair.unit
              (elim.matVec (T x.content)
                (ground.getAt [] (groupAt Y x.content) k)) r)
            (List.range (groupAt Y x.content).length)).oneValue
          (ground.famFold BPair.add BPair.unit (fun k =>
            ((coScale Y x.content * ground.getAt BPair.unit
                (elim.cofVec (elim.gramM (groupAt Y x.content)) k)
                ((pre.filter (fun w =>
                  w.content == x.content)).length))
              * elim.dotP (ground.getAt (⟨[], []⟩ : HVec)
                  (Y.filter (fun w => w.content == x.content))
                  ((pre.filter (fun w =>
                    w.content == x.content)).length)).coords
                x.coords)
            * ground.getAt BPair.unit
              (elim.matVec (T x.content)
                (ground.getAt [] (groupAt Y x.content) k)) r)
            (List.range (groupAt Y x.content).length))
        rw [hcoh]
        exact BPair.oneValue_refl _
      · rw [ground.famFold_map BPair.add BPair.unit]
        refine BPair.oneValue_of_eq
          (ground.famFold_congr_all BPair.add BPair.unit _ _
            (fun i => ?_) (List.range ((suf.filter (fun w =>
              w.content == x.content)).length)))
        rw [hoff, Nat.add_right_comm]
        exact rfl
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]
      have hoff : ((pre ++ [y]).filter (fun w =>
          w.content == x.content)).length
          = (pre.filter (fun w => w.content == x.content)).length := by
        rw [ground.filter_append, ground.length_append,
          ground.filter_cons_false
            (p := fun w => w.content == x.content) (a := y) hb]
        exact rfl
      have htl : ((y :: suf).filter (fun w =>
          w.content == x.content)).length
          = (suf.filter (fun w => w.content == x.content)).length := by
        rw [ground.filter_cons_false
          (p := fun w => w.content == x.content) (a := y) hb]
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl BPair.unit)
          (go_val T Y Z x r hr hT hZrows hYrows hfZ suf (pre ++ [y])
            (by rw [ground.append_assoc]; exact hps))) ?_
      refine BPair.oneValue_trans (BPair.unit_add _) ?_
      rw [htl]
      refine BPair.mul_congr (BPair.oneValue_refl (detAll Z)) ?_
      refine BPair.oneValue_of_eq
        (ground.famFold_congr_all BPair.add BPair.unit _ _
          (fun i => ?_) (List.range ((suf.filter (fun w =>
            w.content == x.content)).length)))
      rw [hoff]


/-- A grid pair's first slot sits in the first list. -/
private theorem dualPairs_mem_fst (Y Z : List HVec) (y z : HVec)
    (h : (y, z) ∈ dualPairs Y Z) : y ∈ Y := by
  match ground.mem_flatMap_of _ Y (y, z) h with
  | ⟨y', hy', hyz⟩ =>
    rw [chunk_map y' Z] at hyz
    match ground.mem_map_of _ _ _ hyz with
    | ⟨z', _, hze⟩ =>
      have hy : y' = y := congrArg Prod.fst hze
      rw [← hy]
      exact hy'

/-- The grid vector's map is the determinants' scale of the map's
own by the round trip: the second list's graded determinant against
the first list's — `lem:dualread`(i)'s grid-transport sentence, the
argument's span read at the content's width and each value's
cleared combination over the second list's span. -/
theorem gridOf_val (T : List Nat → elim.Mat) (Y Z : List HVec)
    (x : HVec)
    (hsp : elim.spanRel (places.monomialsAt x.content).length
      (blockcount.groupAt Y x.content) x.coords)
    (hfZ : ∀ v ∈ blockcount.groupAt Y x.content,
      elim.spanRel v.length (blockcount.groupAt Z x.content)
        (elim.matVec (T x.content) v)) :
    poly.oneValue (mapAt (invFam Y Z (gridOf T Y Z)) x).coords
      (elim.vecScale (detAll Z * detAll Y)
        (elim.matVec (T x.content) x.coords)) := by
  have hxl : x.coords.length
      = (places.monomialsAt x.content).length := hsp.2.1
  have hYrows : elim.rowsLen (places.monomialsAt x.content).length
      (groupAt Y x.content) := hsp.1
  match hYf : Y.filter (fun w => w.content == x.content) with
  | [] =>
    have hQ : (invFam Y Z (gridOf T Y Z)).filter
        (fun t => t.2.1.content == x.content) = [] := by
      refine ground.filter_false _ _ (fun t ht => ?_)
      cases hbt : (t.2.1.content == x.content) with
      | false => rfl
      | true =>
        have hyY : t.2.1 ∈ Y := dualPairs_mem_fst Y Z t.2.1 t.2.2
          (zipTrip_mem (gridOf T Y Z) (dualPairs Y Z) t ht).2
        have hyf : t.2.1 ∈ Y.filter (fun w =>
            w.content == x.content) :=
          ground.mem_filter_to _ hyY hbt
        rw [hYf] at hyf
        exact absurd hyf (fun hc => nomatch hc)
    have hLu : poly.unitTail
        (mapAt (invFam Y Z (gridOf T Y Z)) x).coords := by
      rw [mapAt_coords, hQ]
      exact elim.unitTail_combo_of _ _ _ trivial
    have hxu : poly.unitTail x.coords := by
      rw [show groupAt Y x.content = (Y.filter (fun w =>
        w.content == x.content)).map HVec.coords from rfl, hYf] at hsp
      match elim.span_elim hsp with
      | ⟨c₀, cs, hc₀, _, hone⟩ =>
        refine elim.unitTail_unscale c₀ hc₀ x.coords ?_
        refine poly.oneValue_unitTail hone ?_
        exact elim.unitTail_combo_rows _ cs _
          (fun k hk => absurd hk (Nat.not_lt_zero k))
    refine poly.unitTail_oneValue hLu ?_
    exact elim.unitTail_vecScale _ _ (elim.matVec_null _ _ hxu)
  | w0 :: rest =>
    have hw0 : w0 ∈ Y.filter (fun w => w.content == x.content) := by
      rw [hYf]
      exact List.Mem.head rest
    have hxm : x.content ∈ Y.map HVec.content := by
      rw [← ground.listBeqEq (ground.mem_filter_of _ _ _ hw0).2]
      exact ground.mem_map_to HVec.content
        (ground.mem_filter_of _ _ _ hw0).1
    have h1 : ground.countOf x.content
        (ground.dedupL (Y.map HVec.content)) = 1 :=
      ground.countOf_dedupL_one hxm
    have hgl : (groupAt Y x.content).length
        = (Y.filter (fun w => w.content == x.content)).length :=
      ground.length_map HVec.coords _
    have hocc : 0 < (groupAt Y x.content).length := by
      rw [hgl, hYf]
      exact Nat.succ_pos rest.length
    have hZrows : elim.rowsLen (places.monomialsAt x.content).length
        (groupAt Z x.content) := by
      have hm0 : ground.getAt [] (groupAt Y x.content) 0
          ∈ groupAt Y x.content :=
        ground.mem_getAt [] _ 0 hocc
      have hl0 : (ground.getAt [] (groupAt Y x.content) 0).length
          = (places.monomialsAt x.content).length :=
        elim.rowsLen_getAt _ 0 hYrows hocc
      have hs0 := (hfZ (ground.getAt [] (groupAt Y x.content) 0)
        hm0).1
      rw [hl0] at hs0
      exact hs0
    have hT : (T x.content).length
        = (places.monomialsAt x.content).length := by
      have hm0 : ground.getAt [] (groupAt Y x.content) 0
          ∈ groupAt Y x.content :=
        ground.mem_getAt [] _ 0 hocc
      have hw0 := (hfZ (ground.getAt [] (groupAt Y x.content) 0)
        hm0).2.1
      rw [elim.matVec_length] at hw0
      rw [hw0]
      exact elim.rowsLen_getAt _ 0 hYrows hocc
    have hgcont : ∀ w ∈ Y.filter (fun w' =>
        w'.content == x.content), w.content = x.content :=
      fun w hw => ground.listBeqEq (ground.mem_filter_of _ _ _ hw).2
    have hW : elim.rowsLen (places.monomialsAt x.content).length
        (((invFam Y Z (gridOf T Y Z)).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.2.2.coords)) := by
      refine elim.rowsLen_map _ _ _ (fun t ht => ?_)
      have hin := ground.mem_filter_of _ _ t ht
      have hpair := (zipTrip_mem (gridOf T Y Z) (dualPairs Y Z)
        t hin.1).2
      have hz := dualPairs_mem Y Z t.2.1 t.2.2 hpair
      have hzc : t.2.2.content = x.content := by
        rw [hz.2]
        exact ground.listBeqEq hin.2
      have hzg : t.2.2.coords ∈ groupAt Z x.content := by
        refine ground.mem_map_to HVec.coords ?_
        exact ground.mem_filter_to _ hz.1
          (hzc ▸ ground.listEqBeq t.2.2.content)
      match ground.getAt_of_mem [] hzg with
      | ⟨k, hk, hke⟩ =>
        rw [← hke]
        exact elim.rowsLen_getAt _ k hZrows hk
    refine poly.ov_of_getAt (fun r => ?_)
    by_cases hr : r < (places.monomialsAt x.content).length
    · rw [mapAt_coords, elim.getAt_vecScale _ _ r (by
        rw [elim.matVec_length, hT]; exact hr)]
      refine BPair.oneValue_trans
        (elim.combo_getAt _ _ _ r hW hr) ?_
      rw [ground.map_map, elim.dotP_map_pair]
      have hgo := go_val T Y Z x r hr hT hZrows hYrows hfZ Y [] rfl
      refine BPair.oneValue_trans hgo ?_
      have htg := trip_grid T Y x h1
        (tripRows T Y x.content h1 hT) r hr
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (detAll Z))
          (BPair.oneValue_trans ?_
            (BPair.oneValue_symm htg))) ?_
      · rw [show groupAt Y x.content = (Y.filter (fun w =>
          w.content == x.content)).map HVec.coords from rfl,
          ground.length_map HVec.coords]
        refine ground.foldB_congr_members _ _ _ (fun i hi0 => ?_)
        rw [show (List.filter (fun w => w.content == x.content)
            ([] : List HVec)).length + i = i from Nat.zero_add i]
        refine ground.foldB_congr_members _ _ _ (fun k hk0 => ?_)
        have hk : k < (Y.filter (fun w =>
            w.content == x.content)).length := ground.ltOfMem hk0
        rw [ground.getAt_map (⟨[], []⟩ : HVec) []
          HVec.coords _ k hk,
          hgcont (ground.getAt (⟨[], []⟩ : HVec)
            (Y.filter (fun w => w.content == x.content)) k)
            (ground.mem_getAt _ _ k hk)]
        exact BPair.oneValue_refl _
      · have htrip := mapInv_trip T Y x (by
          rw [hxl]; exact hsp) hT
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (detAll Z))
            (poly.oneValue_getAt r htrip)) ?_
        rw [elim.getAt_vecScale (detAll Y) _ r (by
          rw [elim.matVec_length, hT]; exact hr),
          ← BPair.mul_assoc]
        exact BPair.oneValue_refl _
    · rw [mapAt_coords, ground.getAt_over BPair.unit _ r (by
        rw [elim.length_combo _ _ _ hW]
        exact Nat.le_of_not_lt hr),
        ground.getAt_over BPair.unit _ r (by
        rw [elim.length_vecScale, elim.matVec_length, hT]
        exact Nat.le_of_not_lt hr)]
      exact BPair.oneValue_refl _


/-- At a map value off the determinants' unit tail the grid vector
sits off the unit family: a unit-family grid vector maps every
argument to the unit tail against the value's own read. -/
theorem gridOf_off (T : List Nat → elim.Mat) (Y Z : List HVec)
    (x : HVec)
    (hsp : elim.spanRel (places.monomialsAt x.content).length
      (blockcount.groupAt Y x.content) x.coords)
    (hfZ : ∀ v ∈ blockcount.groupAt Y x.content,
      elim.spanRel v.length (blockcount.groupAt Z x.content)
        (elim.matVec (T x.content) v))
    (hoff : ¬ poly.unitTail
      (elim.vecScale (detAll Z * detAll Y)
        (elim.matVec (T x.content) x.coords))) :
    ¬ poly.unitTail (gridOf T Y Z) := by
  intro hu
  refine hoff ?_
  refine poly.oneValue_unitTail
    (poly.oneValue_symm (gridOf_val T Y Z x hsp hfZ)) ?_
  exact invFam_unitTail Y Z (gridOf T Y Z) x hu


/-- Off the letter pair's move the moved form reads the sum's unit:
each arm's two guards meet only at the moved content, and the walk
across the transpose carries the dual arm's guard to the same
meeting. -/
private theorem movedAt_off_move (P : List (BPair × HVec × HVec))
    (p q : Nat) (a b : HVec)
    (hpa : p < a.content.length) (hqa : q < a.content.length)
    (hpq : ¬ p = q) (hsa : sized a)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = (t.2.2 : HVec).content)
    (hbc : ¬ b.content = moveAt p q a.content) :
    (movedAt P p q a b).oneValue BPair.unit := by
  rw [movedAt_fold, elim.dotP_map_pair]
  refine ground.foldB_null _ P (fun t ht => ?_)
  have htm : t ∈ P := ground.mem_of_countOf_pos t P ht
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl t.1) ?_)
    (BPair.mul_unit t.1)
  refine BPair.oneValue_trans (BPair.add_congr ?_ ?_)
    (BPair.unit_add BPair.unit)
  · refine BPair.oneValue_trans
      (BPair.mul_congr
        (dact_walk p q a t.2.1 hpa hqa hpq hsa (hsz t htm).1)
        (BPair.oneValue_refl (dotG t.2.2 b))) ?_
    by_cases hg : t.2.1.content = moveAt p q a.content
    · rw [show dotG t.2.2 b = BPair.unit from by
        show (if t.2.2.content = b.content then _ else _) = _
        refine if_neg (fun hc => hbc ?_)
        rw [← hc, ← hm t htm]
        exact hg]
      exact BPair.mul_unit _
    · rw [show dotG t.2.1 (act p q a) = BPair.unit from by
        show (if t.2.1.content = (act p q a).content
          then _ else _) = _
        exact if_neg hg]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_of_eq
          (show (BPair.unit : BPair).swap = BPair.unit from rfl))
          (BPair.oneValue_refl (dotG t.2.2 b))) ?_
      exact BPair.unit_mul _
  · by_cases hg : t.2.1.content = a.content
    · rw [show dotG (act p q t.2.2) b = BPair.unit from by
        show (if (act p q t.2.2).content = b.content
          then _ else _) = _
        refine if_neg (fun hc => hbc ?_)
        have hc' : moveAt p q t.2.2.content = b.content := hc
        rw [← hc', ← hm t htm, hg]]
      exact BPair.mul_unit _
    · rw [show dotG t.2.1 a = BPair.unit from by
        show (if t.2.1.content = a.content then _ else _) = _
        exact if_neg hg]
      exact BPair.unit_mul _

/-- The grid vector sits in the stacked system's kernel: the moved
reads at the sum's unit by the equivariance — each read the map's
two moved reads joined at partners, the values the determinants'
scale of the map's own by the round trip.  The sized binder and the
letter width are the carriers' frame, `def:blockcount`'s members at
sized coordinate families over `con:places`' monomials with the
system's letters at the carriers' width; the moved argument's span
read is the closure the transport consumes, its refusal committed
at a second list holding the moved content. -/
theorem gridOf_ker (T : List Nat → elim.Mat) (Y Z : List HVec)
    (d : Nat)
    (hszY : ∀ w ∈ Y, sized w)
    (hwY : ∀ w ∈ Y, d ≤ w.content.length)
    (hmv : ∀ p, p < d → ∀ q, q < d → ¬ p = q → ∀ a ∈ Y,
      poly.oneValue (act p q (⟨a.content,
        elim.matVec (T a.content) a.coords⟩ : HVec)).coords
        (elim.matVec (T (blockcount.moveAt p q a.content))
          (act p q a).coords))
    (hcl : ∀ p, p < d → ∀ q, q < d → ¬ p = q → ∀ a ∈ Y,
      elim.spanRel (act p q a).coords.length
        (blockcount.groupAt Y (act p q a).content)
        (act p q a).coords)
    (hfZ : ∀ mu ∈ Y.map HVec.content,
      ∀ v ∈ blockcount.groupAt Y mu,
      elim.spanRel v.length (blockcount.groupAt Z mu)
        (elim.matVec (T mu) v)) :
    poly.unitTail (elim.matVec (dualSys Y Z d) (gridOf T Y Z)) := by
  have hszfam : ∀ t ∈ invFam Y Z (gridOf T Y Z),
      sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec) := by
    intro t ht
    have hpair := (zipTrip_mem (gridOf T Y Z) (dualPairs Y Z) t ht).2
    have hyY := dualPairs_mem_fst Y Z t.2.1 t.2.2 hpair
    have hz := dualPairs_mem Y Z t.2.1 t.2.2 hpair
    refine ⟨hszY t.2.1 hyY, ?_⟩
    have hyg : t.2.1.coords ∈ groupAt Y t.2.1.content :=
      ground.mem_map_to HVec.coords
        (ground.mem_filter_to _ hyY (ground.listEqBeq t.2.1.content))
    have hsp := hfZ t.2.1.content
      (ground.mem_map_to HVec.content hyY) t.2.1.coords hyg
    have hzg : t.2.2.coords ∈ groupAt Z t.2.1.content := by
      refine ground.mem_map_to HVec.coords ?_
      exact ground.mem_filter_to _ hz.1
        (hz.2 ▸ ground.listEqBeq t.2.2.content)
    match ground.getAt_of_mem [] hzg with
    | ⟨k, hk, hke⟩ =>
      show t.2.2.coords.length
        = (places.monomialsAt t.2.2.content).length
      rw [← hke, elim.rowsLen_getAt _ k hsp.1 hk,
        hszY t.2.1 hyY, hz.2]
  have hmfam : ∀ t ∈ invFam Y Z (gridOf T Y Z),
      (t.2.1 : HVec).content = (t.2.2 : HVec).content :=
    fun t ht => (dualPairs_mem Y Z t.2.1 t.2.2
      (zipTrip_mem (gridOf T Y Z) (dualPairs Y Z) t ht).2).2.symm
  refine (dualKer_read Y Z d (gridOf T Y Z)
    (gridOf_len T Y Z)).mpr ?_
  intro p hp q hq hpq a ha b _
  have hpa : p < a.content.length :=
    Nat.lt_of_lt_of_le hp (hwY a ha)
  have hqa : q < a.content.length :=
    Nat.lt_of_lt_of_le hq (hwY a ha)
  by_cases hbc : b.content = moveAt p q a.content
  · have h2r := movedAt_two_reads (invFam Y Z (gridOf T Y Z))
      p q a b hpa hqa hpq (hszY a ha) hszfam hmfam hbc
    have hYra : elim.rowsLen (places.monomialsAt a.content).length
        (groupAt Y a.content) := rowsLen_groupAt a.content Y hszY
    have hspa : elim.spanRel (places.monomialsAt a.content).length
        (blockcount.groupAt Y a.content) a.coords := by
      have hag : a.coords ∈ groupAt Y a.content :=
        ground.mem_map_to HVec.coords
          (ground.mem_filter_to _ ha (ground.listEqBeq a.content))
      match ground.getAt_of_mem [] hag with
      | ⟨k, hk, hke⟩ =>
        rw [← hke]
        exact elim.spanRel_getAt _ _ k hk hYra
    have hva := gridOf_val T Y Z a hspa
      (fun v hv => hfZ a.content
        (ground.mem_map_to HVec.content ha) v hv)
    have hclA := hcl p hp q hq hpq a ha
    have hsact : (act p q a).coords.length
        = (places.monomialsAt (act p q a).content).length :=
      act_sized p q a
    rw [hsact] at hclA
    have hfZ' : ∀ v ∈ blockcount.groupAt Y (act p q a).content,
        elim.spanRel v.length
          (blockcount.groupAt Z (act p q a).content)
          (elim.matVec (T (act p q a).content) v) := by
      intro v hv
      match ground.mem_map_of _ _ v hv with
      | ⟨w, hwf, hwe⟩ =>
        have hwY' : w ∈ Y := (ground.mem_filter_of _ Y w hwf).1
        have hwc : w.content = (act p q a).content :=
          ground.listBeqEq (ground.mem_filter_of _ Y w hwf).2
        refine hfZ (act p q a).content ?_ v hv
        rw [← hwc]
        exact ground.mem_map_to HVec.content hwY'
    have hvm := gridOf_val T Y Z (act p q a) hclA hfZ'
    have hR2 : poly.oneValue
        (act p q (mapAt (invFam Y Z (gridOf T Y Z)) a)).coords
        (mapAt (invFam Y Z (gridOf T Y Z)) (act p q a)).coords := by
      show poly.oneValue
        (elim.matVec (units.matUnitAt (moveAt p q a.content)
            a.content p q)
          (mapAt (invFam Y Z (gridOf T Y Z)) a).coords)
        (mapAt (invFam Y Z (gridOf T Y Z)) (act p q a)).coords
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _ hva) ?_
      refine poly.oneValue_trans
        (elim.matVec_vecScale_free _ _ _) ?_
      refine poly.oneValue_trans
        (elim.vecScale_oneValue _ _ _ (hmv p hp q hq hpq a ha)) ?_
      exact poly.oneValue_symm hvm
    refine BPair.oneValue_trans h2r ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_refl
          (elim.dotP b.coords
            (mapAt (invFam Y Z (gridOf T Y Z))
              (act p q a)).coords).swap)
        (elim.dotP_oneValue_right b.coords _ _ hR2)) ?_
    exact BPair.oneValue_of_eqMem (ground.add_comm _ _)
  · exact movedAt_off_move (invFam Y Z (gridOf T Y Z)) p q a b
      hpa hqa hpq (hszY a ha) hszfam hmfam hbc


/-- The stacked system's rows sit at the grid's width. -/
private theorem dualSys_rowsLen (Y Z : List HVec) (d : Nat) :
    elim.rowsLen (dualPairs Y Z).length (dualSys Y Z d) := by
  refine elim.rowsLen_intro _ (fun i hi => ?_)
  have hr : ground.getAt [] (dualSys Y Z d) i ∈ dualSys Y Z d :=
    ground.mem_getAt [] _ i hi
  match ground.mem_flatMap_of _ _ _ hr with
  | ⟨p, _, hp⟩ =>
    match ground.mem_flatMap_of _ _ _ hp with
    | ⟨q, _, hq⟩ =>
      by_cases hpq : p = q
      · rw [if_pos hpq] at hq
        exact absurd hq (fun hc => nomatch hc)
      · rw [if_neg hpq] at hq
        match ground.mem_flatMap_of _ _ _ hq with
        | ⟨a, _, ha⟩ =>
          match ground.mem_map_of _ _ _ ha with
          | ⟨b, _, hb⟩ =>
            rw [← hb]
            exact ground.length_map _ (dualPairs Y Z)

/-- The kernel list and a stated map list read one count: at a
stated list of grid vectors inside the stacked system's kernel,
independent and carrying the kernel list in its span, the invariant
count is the stated list's own — `lem:dualread`(i)'s count close,
two independent lists inside one span (`elim.span_count_eq`). -/
theorem invCount_span (Y Z : List HVec) (d : Nat) (G : elim.Mat)
    (hGw : elim.rowsLen (dualPairs Y Z).length G)
    (hGi : elim.indepRows (dualPairs Y Z).length G)
    (hGk : ∀ g ∈ G,
      poly.unitTail (elim.matVec (dualSys Y Z d) g))
    (hsp : ∀ v ∈ elim.kernelList (dualPairs Y Z).length
        (dualSys Y Z d),
      elim.spanRel (dualPairs Y Z).length G v) :
    invCount Y Z d = G.length := by
  show elim.kernelDim (dualPairs Y Z).length (dualSys Y Z d)
    = G.length
  rw [← elim.kernelList_dim]
  exact elim.span_count_eq (dualPairs Y Z).length _ G
    (elim.kernelList_rowsLen _ _) hGw
    (elim.kernelList_indep _ _ (dualSys_rowsLen Y Z d)) hGi
    (fun k hk => hsp _ (ground.mem_getAt [] _ k hk))
    (fun k hk => elim.kernelList_span _ _ (dualSys_rowsLen Y Z d)
      (ground.getAt [] G k) (elim.rowsLen_getAt _ k hGw hk)
      (hGk _ (ground.mem_getAt [] G k hk)))

/-! Clause (iii)'s carrier tier at `lem:dualread`(i)'s moved
reads: the complementary grid's value map is equivariant at the
raising direction.  The grid's
coefficients build one combination at the fused content
(`elim.matVec_crossM` at `hker`), and the kernel read says every
adjacent raising annihilates it (`units.stackedRaise_to`, an
unoccupied lowered letter reading the action null outright); the
descent on the gap carries that to every raising below the width
(`ker_raise`, the commutator's crossed join at
`units.matVec_comm_read` with both composites null by the descent,
the vacant middle taken at the vacant content).  Contracting the
annihilated combination against a tensor of the argument with an
output vector splits the raising over the tensor
(`blockcount.act_tensorH`) and factorizes each place at the
matched first-factor degree (`blockcount.dotP_tensorH` matched,
`blockcount.dotP_tensorH_off` mismatched at one degree — the
`hdegA` frame): the first slots' arm walks across the transpose
identity to the dual argument (`dact_walk`) and the second slots'
arm to the moved output vector, so the two arms are the value's two
reads and the moved value pairs the output vector as the value's
moved read does, at every place (`elim.dotP_oneIndex` at the
identity's rows). -/

/-- The family's slot-pair map at matched counts is the grid's
own. -/
private theorem zipTrip_mapG {γ : Type} (F : HVec → HVec → γ) :
    ∀ (c : List BPair) (g : List (HVec × HVec)), c.length = g.length →
      (List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c g).map
          (fun t => F t.2.1 t.2.2) = g.map (fun s => F s.1 s.2)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: s, z :: g, h =>
    congrArg (List.cons (F z.1 z.2))
      (zipTrip_mapG F s g (Nat.succ.inj h))

/-- The display's coordinate rows are the enumeration's tensors'
own. -/
private theorem pairsAt_rows (A B : List HVec) (cc : List Nat) :
    (pairsAt A B cc).map HVec.coords
      = (blockcount.pairIdx A (fun v => v) B cc).map
        (fun t => (tensorH t.1 t.2).coords) := by
  rw [blockcount.pairsAt_pairIdx A B cc, ground.map_map]

/-- The display's rows sit at the fused content's width. -/
private theorem pairsAt_rowsLen (A B : List HVec) (cc : List Nat) :
    elim.rowsLen (places.monomialsAt cc).length
      ((pairsAt A B cc).map HVec.coords) := by
  rw [pairsAt_rows A B cc]
  refine elim.rowsLen_map _ _ _ (fun t ht => ?_)
  match blockcount.pairIdx_mem ht with
  | ⟨_, _, hg⟩ =>
    show (tensorH t.1 t.2).coords.length
      = (places.monomialsAt cc).length
    rw [tensorH_sized t.1 t.2,
      show (tensorH t.1 t.2).content
        = List.zipWith (fun a b => a + b) t.1.content t.2.content
        from rfl, hg]


/-- The stacked read at the grid's combination: `hker` is the
combination's own annihilation by the stacked raising. -/
private theorem ker_stack (A B : List HVec) (cc : List Nat)
    (c : List BPair)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise cc)
        ((pairsAt A B cc).map HVec.coords)) c)) :
    poly.unitTail (elim.matVec (units.stackedRaise cc)
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))) :=
  poly.unitTail_oneValue_right hker
    (elim.matVec_crossM (places.monomialsAt cc).length
      (units.stackedRaise cc) ((pairsAt A B cc).map HVec.coords) c
      (units.rowsLen_stackedRaise cc)
      (pairsAt_rowsLen A B cc))

/-- Every adjacent raising annihilates the grid's combination: the
occupied moves are the stacked read's own and an unoccupied lowered
letter reads the action null outright. -/
private theorem ker_adj (A B : List HVec) (cc : List Nat)
    (c : List BPair)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise cc)
        ((pairsAt A B cc).map HVec.coords)) c))
    (i : Nat) (hi : i + 1 < cc.length) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i (i + 1) cc) cc i (i + 1))
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))) := by
  by_cases hocc : 0 < ground.getAt 0 cc (i + 1)
  · rw [moveAt_moveUp i cc]
    exact units.stackedRaise_to cc _
      (ker_stack A B cc c hker) i hi hocc
  · exact units.matVec_null_unocc _ cc i (i + 1)
      (Nat.le_antisymm (Nat.ge_of_not_lt hocc) (Nat.zero_le _)) _

/-- The commutator's crossed join at one middle letter: at three
distinct letters with the two inner composites' reads at the unit
tail, the crossed composite reads the letter pair's action at the
unit tail — the occupied middle at the chain reads with the
commutator's exchange, the vacant middle at the degenerate
enumeration. -/
private theorem comm_step (cc : List Nat) (Ph : List BPair)
    (hsz : Ph.length = (places.monomialsAt cc).length)
    (I K J : Nat) (hI : I < cc.length) (hK : K < cc.length)
    (hIJn : ¬ I = J) (hKJn : ¬ K = J) (hIKn : ¬ I = K)
    (hInner1 : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt K J cc) cc K J) Ph))
    (hInner2 : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt I K cc) cc I K) Ph)) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt I J cc) cc I J) Ph) := by
  have hIJ := out_gen cc I J hI hIJn
  have hKJ := out_gen cc K J hK hKJn
  have hIA : I < (moveAt K J cc).length := by
    rw [length_moveAt]
    exact hI
  have hIK := out_gen (moveAt K J cc) I K hIA hIKn
  rw [moveAt_chain I K J cc] at hIK
  have htermA : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt I J cc)
        (moveAt K J cc) I K)
      (elim.matVec (units.matUnitAt (moveAt K J cc) cc
        K J) Ph)) :=
    elim.matVec_null _ _ hInner1
  by_cases hkocc : 0 < ground.getAt 0 cc K
  · have hIK' := out_gen cc I K hI hIKn
    have hkB : K < (moveAt I K cc).length := by
      rw [length_moveAt]
      exact hK
    have hKJ' := out_gen (moveAt I K cc) K J hkB hKJn
    rw [moveAt_chain' I K J cc hIJn hKJn hkocc] at hKJ'
    refine poly.oneValue_unitTail
      (units.matVec_comm_read (moveAt I J cc)
        (moveAt K J cc) (moveAt I K cc) cc
        I K J hIJn hKJ hIK hIK' hKJ' hIJ Ph hsz) ?_
    exact elim.unitTail_vecAdd_of htermA
      (poly.unitTail_swapMap _
        (elim.matVec_null _ _ hInner2))
  · have hz : ground.getAt 0 cc K = 0 :=
      Nat.le_antisymm (Nat.ge_of_not_lt hkocc) (Nat.zero_le _)
    have hIK' : ∀ s m : List Nat,
        0 < ground.countOf s (places.monomialsAt cc) →
        0 < ground.countOf m (units.unitAct I K s) →
        m.length = sumNat (List.replicate cc.length 0)
          ∧ content (List.replicate cc.length 0).length m
            = List.replicate cc.length 0 := by
      intro s m hs hm
      rw [units.unitAct_nil_of_zero I K s
        (places.letter_zero cc K hz s hs)] at hm
      exact absurd hm (Nat.lt_irrefl 0)
    have hKJ' : ∀ s m : List Nat,
        0 < ground.countOf s
          (places.monomialsAt (List.replicate cc.length 0)) →
        0 < ground.countOf m (units.unitAct K J s) →
        m.length = sumNat (moveAt I J cc)
          ∧ content (moveAt I J cc).length m = moveAt I J cc :=
      fun s m hs hm =>
        (units.no_out_zero cc.length K J s m hs hm).elim
    refine poly.oneValue_unitTail
      (units.matVec_comm_read (moveAt I J cc)
        (moveAt K J cc) (List.replicate cc.length 0) cc
        I K J hIJn hKJ hIK hIK' hKJ' hIJ Ph hsz) ?_
    exact elim.unitTail_vecAdd_of htermA
      (poly.unitTail_swapMap _
        (elim.matVec_null _ _
          (units.matVec_null_unocc _ cc I K hz Ph)))


/-- The descent on the gap at a stated vector: with every adjacent
raising's action null every raising below the width is null, the
commutator's crossed join carrying both composites at a null inner
read — the descent's own recursion at `units.matVec_comm_read`,
the vacant middle taken at the vacant content. -/
private theorem raise_gap (cc : List Nat) (Ph : List BPair)
    (hsz : Ph.length = (places.monomialsAt cc).length)
    (hbase : ∀ i, i + 1 < cc.length →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i (i + 1) cc) cc i (i + 1)) Ph)) :
    ∀ (g pp qq : Nat), pp < cc.length → qq < cc.length →
      qq = pp + (g + 1) →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt pp qq cc) cc pp qq) Ph)
  | 0, pp, qq, _, hqq, he => by
    rw [he]
    exact hbase pp (by rw [← he]; exact hqq)
  | g + 1, pp, qq, hpp, hqq, he => by
    have hlt : pp + 1 < qq := by
      rw [he]
      exact Nat.succ_lt_succ (Nat.lt_succ_of_le (Nat.le_add_right pp g))
    have hk : pp + 1 < cc.length := Nat.lt_trans hlt hqq
    have hgap : qq = pp + 1 + (g + 1) := by
      rw [he, Nat.add_assoc pp 1 (g + 1), Nat.add_comm 1 (g + 1)]
    exact comm_step cc Ph hsz pp (pp + 1) qq hpp hk
      (Nat.ne_of_lt (Nat.lt_of_succ_lt hlt))
      (Nat.ne_of_lt hlt)
      (fun hc => Nat.ne_of_lt (Nat.lt_succ_self pp) hc)
      (raise_gap cc Ph hsz hbase g (pp + 1) qq hk hqq hgap)
      (hbase pp hk)

/-- The descent on the gap at the lowering direction: with every
adjacent lowering's action null every lowering below the width is
null, the commutator's crossed join carrying both composites at a
null inner read, the vacant middle taken at the vacant content. -/
private theorem lower_gap (cc : List Nat) (Ph : List BPair)
    (hsz : Ph.length = (places.monomialsAt cc).length)
    (hbase : ∀ i, i + 1 < cc.length →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt (i + 1) i cc) cc (i + 1) i) Ph)) :
    ∀ (g pp qq : Nat), pp < cc.length → qq < cc.length →
      qq = pp + (g + 1) →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt qq pp cc) cc qq pp) Ph)
  | 0, pp, qq, _, hqq, he => by
    rw [he]
    exact hbase pp (by rw [← he]; exact hqq)
  | g + 1, pp, qq, _, hqq, he => by
    have hlt : pp + 1 < qq := by
      rw [he]
      exact Nat.succ_lt_succ (Nat.lt_succ_of_le (Nat.le_add_right pp g))
    have hk : pp + 1 < cc.length := Nat.lt_trans hlt hqq
    have hgap : qq = pp + 1 + (g + 1) := by
      rw [he, Nat.add_assoc pp 1 (g + 1), Nat.add_comm 1 (g + 1)]
    exact comm_step cc Ph hsz qq (pp + 1) pp hqq hk
      (fun hc => Nat.ne_of_lt (Nat.lt_of_succ_lt hlt) hc.symm)
      (fun hc => Nat.ne_of_lt (Nat.lt_succ_self pp) hc.symm)
      (fun hc => Nat.ne_of_lt hlt hc.symm)
      (hbase pp hk)
      (lower_gap cc Ph hsz hbase g (pp + 1) qq hk hqq hgap)

/-- The pairing against a joined datum whose first summand is the
unit family reads the second summand alone, the join truncating no
place the row reads. -/
private theorem dotP_addNullL : ∀ (r u w : List BPair),
    poly.unitTail u → r.length ≤ u.length →
    (elim.dotP r (elim.vecAdd u w)).oneValue (elim.dotP r w)
  | [], _, _, _, _ => BPair.oneValue_refl _
  | _ :: _, [], _, _, hl => absurd hl (Nat.not_succ_le_zero _)
  | _ :: _, _ :: _, [], _, _ => BPair.oneValue_refl _
  | a :: r, e :: u, z :: w, hu, hl => by
    show (a * (e + z) + elim.dotP r (elim.vecAdd u w)).oneValue
      (a * z + elim.dotP r w)
    exact BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl a)
        (BPair.oneValue_trans
          (BPair.add_congr hu.1 (BPair.oneValue_refl z))
          (BPair.unit_add z)))
      (dotP_addNullL r u w hu.2 (Nat.le_of_succ_le_succ hl))

/-- The graded pairing at a memberwise-swapped family is the
pairing's own partner. -/
private theorem dotG_neg (mu : List Nat) (u : List BPair) (b : HVec) :
    dotG ⟨mu, poly.neg u⟩ b = (dotG ⟨mu, u⟩ b).swap := by
  show (if mu = b.content then elim.dotP (poly.neg u) b.coords
      else BPair.unit)
    = (if mu = b.content then elim.dotP u b.coords
        else BPair.unit).swap
  by_cases h : mu = b.content
  · rw [if_pos h, if_pos h]
    exact elim.dotP_swap_left u b.coords
  · rw [if_neg h, if_neg h]
    rfl

/-- The value's second slots at a stated output content sit at that
content's width. -/
private theorem pairRowsW (P : List (BPair × HVec × HVec))
    (mu oc : List Nat)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = mu →
      (t.2.2 : HVec).content = oc) :
    elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords)) := by
  refine elim.rowsLen_map _ _ _ (fun t ht => ?_)
  match ground.mem_filter_of _ P t ht with
  | ⟨htP, htc⟩ =>
    rw [(hsz t htP).2, hm t htP (ground.listBeqEq htc)]

/-- The value's pairing fold: the family's own fold at the
argument's pairings against a further vector at the output content,
the cross-content members entering at the grading's unit. -/
private theorem pairVal_pair (P : List (BPair × HVec × HVec))
    (z b : HVec) (oc : List Nat)
    (hsz : ∀ t ∈ P, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (hm : ∀ t ∈ P, (t.2.1 : HVec).content = z.content →
      (t.2.2 : HVec).content = oc)
    (hb : b.content = oc) :
    (elim.dotP (P.map (fun t => t.1))
      (P.map (fun t => dotG t.2.1 z * dotG t.2.2 b))).oneValue
      (dotG (pairVal P z oc) b) := by
  refine BPair.oneValue_trans
    (dotP_filter_collapse (fun t => t.2.1.content == z.content) _ P
      (fun t _ htf => ?_)) ?_
  · rw [show dotG t.2.1 z = BPair.unit from by
      show (if t.2.1.content = z.content then _ else _) = _
      refine if_neg (fun hc => ?_)
      rw [hc, ground.listEqBeq] at htf
      exact Bool.noConfusion htf,
      BPair.mul_comm]
    exact BPair.mul_unit _
  · rw [show dotG (pairVal P z oc) b
        = elim.dotP (pairVal P z oc).coords b.coords from by
      show (if (pairVal P z oc).content = b.content then _ else _) = _
      exact if_pos (show oc = b.content from hb.symm),
      pairVal_coords]
    refine BPair.oneValue_symm ?_
    rw [elim.dotP_comm]
    refine BPair.oneValue_trans
      (elim.dotP_combo _ _ b.coords _
        (pairRowsW P z.content oc hsz hm)) ?_
    rw [ground.map_map, elim.dotP_map_pair, elim.dotP_map_pair]
    refine BPair.oneValue_of_eq
      (ground.famFold_congr_members _ _ _ _ _ (fun t ht => ?_))
    match ground.mem_filter_of _ P t
      (ground.mem_of_countOf_pos t _ ht) with
    | ⟨htP, htc⟩ =>
      have hce : t.2.1.content = z.content := ground.listBeqEq htc
      rw [show dotG t.2.1 z = elim.dotP t.2.1.coords z.coords from by
          show (if t.2.1.content = z.content then _ else _) = _
          exact if_pos hce,
        show dotG t.2.2 b = elim.dotP t.2.2.coords b.coords from by
          show (if t.2.2.content = b.content then _ else _) = _
          exact if_pos (by rw [hm t htP hce, hb]),
        elim.dotP_comm b.coords t.2.2.coords, ← BPair.mul_assoc]

/-- The moved contraction's read at a grid tensor: the raising's
Leibniz split over the argument's tensor with the output vector,
each arm factorizing at the matched first-factor degree
(`blockcount.dotP_tensorH` at one first content,
`blockcount.dotP_tensorH_off` off it), the vacant argument letter
withdrawing the first arm outright. -/
private theorem tens_entry (v w z b : HVec) (p q d kA : Nat)
    (cc : List Nat)
    (hsv : sized v) (hsw : sized w) (hsz : sized z) (hsb : sized b)
    (hwv : v.content.length = d) (hww : w.content.length = d)
    (hwz : z.content.length = d) (hwb : b.content.length = d)
    (hdv : ground.sumNat v.content = kA)
    (hdz : ground.sumNat z.content = kA)
    (hccl : cc.length = d)
    (hp : p < d) (hq : q < d) (hqp : ¬ q = p)
    (hbp : 0 < ground.getAt 0 b.content p)
    (hccq : 0 < ground.getAt 0 cc q)
    (hg : List.zipWith (fun a e => a + e) v.content w.content = cc)
    (hzb : List.zipWith (fun a e => a + e) z.content b.content
      = moveAt p q cc) :
    (elim.dotP (act q p (tensorH z b)).coords
        (tensorH v w).coords).oneValue
      (dotG v (act q p z) * dotG w b
        + dotG v z * dotG w (act q p b)) := by
  have hlenvw : v.content.length = w.content.length := by
    rw [hwv, hww]
  have hlenzb : z.content.length = b.content.length := by
    rw [hwz, hwb]
  have hqz : q < z.content.length := by rw [hwz]; exact hq
  have hpz : p < z.content.length := by rw [hwz]; exact hp
  have hpcc : p < cc.length := by rw [hccl]; exact hp
  have hqcc : q < cc.length := by rw [hccl]; exact hq
  have hround : moveAt q p (moveAt p q cc) = cc :=
    moveAt_round_at q p cc hccq
  have hU2c : (tensorH z (act q p b)).content = cc := by
    show List.zipWith (fun a e => a + e) z.content
      (moveAt q p b.content) = cc
    rw [moveAt_zipWith_right q p z.content b.content hbp, hzb, hround]
  have hXc : (tensorH v w).content = cc := hg
  have hXlen : (tensorH v w).coords.length
      = (places.monomialsAt cc).length := by
    rw [tensorH_sized v w, hXc]
  have hU2len : (tensorH z (act q p b)).coords.length
      = (places.monomialsAt cc).length := by
    rw [tensorH_sized z (act q p b), hU2c]
  have hsplit := act_tensorH q p z b hsz hsb hlenzb hqz hpz hqp
  rw [elim.dotP_comm]
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right (tensorH v w).coords _ _ hsplit) ?_
  -- the second arm reads the value's moved output vector
  have harm2 : (elim.dotP (tensorH v w).coords
      (tensorH z (act q p b)).coords).oneValue
      (dotG v z * dotG w (act q p b)) := by
    by_cases hcv : v.content = z.content
    · have hcw : w.content = (act q p b).content := by
        refine blockcount.zipWith_add_cancelL v.content w.content
          (act q p b).content w.content.length ?_ rfl ?_ ?_
        · rw [hwv, hww]
        · show (moveAt q p b.content).length = w.content.length
          rw [length_moveAt, hww, hwb]
        · rw [hg, hcv]
          exact hU2c.symm
      refine BPair.oneValue_trans
        (dotP_tensorH v w z (act q p b) hsv hsw hsz
          (act_sized q p b) hlenvw hcv hcw) ?_
      rw [show dotG v z = elim.dotP v.coords z.coords from
          if_pos hcv,
        show dotG w (act q p b) = elim.dotP w.coords
            (act q p b).coords from if_pos hcw]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans
        (dotP_tensorH_off v w z (act q p b) hlenvw
          (by show z.content.length = (moveAt q p b.content).length
              rw [length_moveAt, hwz, hwb])
          (by rw [hdv, hdz])
          (by rw [hXc, hU2c]) hcv) ?_
      rw [show dotG v z = BPair.unit from if_neg hcv]
      exact BPair.oneValue_symm
        (BPair.unit_mul (dotG w (act q p b)))
  by_cases hzp : 0 < ground.getAt 0 z.content p
  · -- both arms sit at the fused content
    have hU1c : (tensorH (act q p z) b).content = cc := by
      show List.zipWith (fun a e => a + e) (moveAt q p z.content)
        b.content = cc
      rw [moveAt_zipWith_left q p z.content b.content hzp, hzb, hround]
    have hU1len : (tensorH (act q p z) b).coords.length
        = (places.monomialsAt cc).length := by
      rw [tensorH_sized (act q p z) b, hU1c]
    have harm1 : (elim.dotP (tensorH v w).coords
        (tensorH (act q p z) b).coords).oneValue
        (dotG v (act q p z) * dotG w b) := by
      by_cases hcv : v.content = (act q p z).content
      · have hcw : w.content = b.content := by
          refine blockcount.zipWith_add_cancelL v.content w.content
            b.content w.content.length ?_ rfl ?_ ?_
          · rw [hwv, hww]
          · rw [hwb, hww]
          · rw [hg, hcv]
            exact hU1c.symm
        refine BPair.oneValue_trans
          (dotP_tensorH v w (act q p z) b hsv hsw
            (act_sized q p z) hsb hlenvw hcv hcw) ?_
        rw [show dotG v (act q p z) = elim.dotP v.coords
              (act q p z).coords from if_pos hcv,
          show dotG w b = elim.dotP w.coords b.coords from
            if_pos hcw]
        exact BPair.oneValue_refl _
      · refine BPair.oneValue_trans
          (dotP_tensorH_off v w (act q p z) b hlenvw
            (by show (moveAt q p z.content).length = b.content.length
                rw [length_moveAt, hwz, hwb])
            (by rw [hdv,
                show ground.sumNat (act q p z).content
                    = ground.sumNat z.content from
                  sumNat_moveAt q p z.content hqz hzp, hdz])
            (by rw [hXc, hU1c]) hcv) ?_
        rw [show dotG v (act q p z) = BPair.unit from if_neg hcv]
        exact BPair.oneValue_symm
          (BPair.unit_mul (dotG w b))
    refine BPair.oneValue_trans
      (elim.dotP_vecAdd_right (tensorH v w).coords _ _
        (by rw [hU1len, hU2len])) ?_
    exact BPair.add_congr harm1 harm2
  · -- the vacant argument letter withdraws the first arm
    have hzp0 : ground.getAt 0 z.content p = 0 :=
      Nat.le_antisymm (Nat.ge_of_not_lt hzp) (Nat.zero_le _)
    have hnullz : poly.unitTail (act q p z).coords :=
      units.matVec_null_unocc _ z.content q p hzp0 z.coords
    have hU1null : poly.unitTail (tensorH (act q p z) b).coords :=
      (tensorH_unitTail (act q p z) b (act_sized q p z) hsb
        (by show (moveAt q p z.content).length = b.content.length
            rw [length_moveAt, hwz, hwb])).mpr (Or.inl hnullz)
    have hU1c : (tensorH (act q p z) b).content
        = ground.bumpAt p cc := by
      show List.zipWith (fun a e => a + e)
        (ground.bumpAt q (dipAt p z.content)) b.content
        = ground.bumpAt p cc
      rw [ground.dipAt_of_zero p z.content hzp0,
        ground.bumpAt_zipWith_left q z.content b.content, hzb,
        show moveAt p q cc = ground.bumpAt p (dipAt q cc) from rfl,
        ground.bumpAt_comm q p (dipAt q cc),
        ground.bumpAt_dipAt_self q cc hccq]
    have hle : (tensorH v w).coords.length
        ≤ (tensorH (act q p z) b).coords.length := by
      rw [hXlen, tensorH_sized (act q p z) b, hU1c]
      exact places.length_monomialsAt_le_bumpAt p cc hpcc
    have h1unit : (dotG v (act q p z)).oneValue BPair.unit := by
      show (if v.content = (act q p z).content
          then elim.dotP v.coords (act q p z).coords
          else BPair.unit).oneValue BPair.unit
      by_cases hcv : v.content = (act q p z).content
      · rw [if_pos hcv]
        exact elim.dotP_null_tail_right v.coords _ hnullz
      · rw [if_neg hcv]
        exact BPair.oneValue_refl BPair.unit
    refine BPair.oneValue_trans
      (dotP_addNullL (tensorH v w).coords _ _ hU1null hle) ?_
    refine BPair.oneValue_trans harm2 ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.mul_congr h1unit (BPair.oneValue_refl (dotG w b)))
          (BPair.unit_mul (dotG w b)))
        (BPair.oneValue_refl _)) ?_)
    exact BPair.unit_add _

/-- The moved contraction's fold: the annihilated combination read
against the argument's tensor with an output vector collects the
grid's two arms at the sum's unit — `lem:dualread`(i)'s moved
read at the tensor grid, the kernel read's whole content. -/
private theorem grid_contract_gen (A B : List HVec) (cc : List Nat)
    (d kA : Nat) (c : List BPair)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ v ∈ B, sized v)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ v ∈ B, v.content.length = d)
    (hdegA : ∀ v ∈ A, ground.sumNat v.content = kA)
    (hccl : cc.length = d)
    (i j : Nat) (hi : i < d) (hj : j < d) (hijn : ¬ i = j)
    (hnull : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt j i cc) cc j i)
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))))
    (z b : HVec) (hsz : sized z) (hsb : sized b)
    (hwz : z.content.length = d) (hwb : b.content.length = d)
    (hdz : ground.sumNat z.content = kA)
    (hbj : 0 < ground.getAt 0 b.content j)
    (hcci : 0 < ground.getAt 0 cc i)
    (hzb : List.zipWith (fun a e => a + e) z.content b.content
      = moveAt j i cc) :
    (elim.dotP c ((blockcount.pairIdx A (fun v => v) B cc).map
      (fun t => dotG t.1 (act i j z) * dotG t.2 b
        + dotG t.1 z * dotG t.2 (act i j b)))).oneValue
      BPair.unit := by
  have hicc : i < cc.length := by rw [hccl]; exact hi
  have hjcc : j < cc.length := by rw [hccl]; exact hj
  have hjin : ¬ j = i := fun hc => hijn hc.symm
  have hrows := pairsAt_rowsLen A B cc
  have hPhiLen : (elim.combo (places.monomialsAt cc).length c
      ((pairsAt A B cc).map HVec.coords)).length
      = (places.monomialsAt cc).length :=
    elim.length_combo _ c _ hrows
  have hround : moveAt i j (moveAt j i cc) = cc :=
    moveAt_round_at i j cc hcci
  have hzbc : (tensorH z b).content = moveAt j i cc := hzb
  have hzbl : (tensorH z b).coords.length
      = (places.monomialsAt (moveAt j i cc)).length := by
    rw [tensorH_sized z b, hzbc]
  have hact : (act i j (tensorH z b)).coords
      = elim.matVec (units.matUnitAt cc (moveAt j i cc) i j)
        (tensorH z b).coords := by
    show elim.matVec (units.matUnitAt
      (moveAt i j (tensorH z b).content) (tensorH z b).content i j)
      (tensorH z b).coords = _
    rw [hzbc, hround]
  have hfused : (elim.dotP
      (act i j (tensorH z b)).coords
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))).oneValue BPair.unit := by
    rw [hact, ← elim.dotP_comm]
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (unit_adjoint j i cc hjcc hicc hjin hcci _
          (tensorH z b).coords hPhiLen hzbl)) ?_
    exact elim.dotP_null_tail_left _ _ hnull
  refine BPair.oneValue_trans ?_ hfused
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (elim.dotP_combo c ((pairsAt A B cc).map HVec.coords)
      (act i j (tensorH z b)).coords _ hrows) ?_)
  rw [pairsAt_rows A B cc, ground.map_map]
  refine elim.dotP_oneValue_right c _ _
    (poly.oneValue_map _ _ _ (fun t ht => ?_))
  match blockcount.pairIdx_mem ht with
  | ⟨hta, htb, htg⟩ =>
    exact tens_entry t.1 t.2 z b j i d kA cc (hszA t.1 hta)
      (hszB t.2 htb) hsz hsb (hwA t.1 hta) (hwB t.2 htb) hwz hwb
      (hdegA t.1 hta) hdz hccl hj hi hijn hbj hcci htg hzb


/-- The family's fold is the grid's own at matched counts. -/
private theorem pairFam_fold (A B : List HVec) (cc : List Nat)
    (c : List BPair) (F : HVec → HVec → BPair)
    (hcG : c.length
      = (blockcount.pairIdx A (fun v => v) B cc).length) :
    elim.dotP ((pairFam A B cc c).map (fun t => t.1))
        ((pairFam A B cc c).map (fun t => F t.2.1 t.2.2))
      = elim.dotP c ((blockcount.pairIdx A (fun v => v) B cc).map
        (fun t => F t.1 t.2)) := by
  show elim.dotP
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c
        (blockcount.pairIdx A (fun v => v) B cc)).map
        (fun t => t.1))
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c
        (blockcount.pairIdx A (fun v => v) B cc)).map
        (fun t => F t.2.1 t.2.2))
    = elim.dotP c ((blockcount.pairIdx A (fun v => v) B cc).map
      (fun t => F t.1 t.2))
  rw [zipTrip_fst c _ hcG, zipTrip_mapG F c _ hcG]

/-- The value is the unit family at unit-class coefficients. -/
private theorem pairVal_null (P : List (BPair × HVec × HVec))
    (z : HVec) (oc : List Nat)
    (h : ∀ t ∈ P, t.2.1.content = z.content →
      (t.1 * elim.dotP t.2.1.coords z.coords).oneValue BPair.unit) :
    poly.unitTail (pairVal P z oc).coords := by
  rw [pairVal_coords]
  refine elim.unitTail_combo_of _ _ _ (poly.unitTail_map _ _ (fun t ht => ?_))
  match ground.mem_filter_of _ P t ht with
  | ⟨htP, htc⟩ => exact h t htP (ground.listBeqEq htc)

/-- The graded pairing against the exchanged action is the pairing
against the dual action's partner. -/
private theorem dotG_dact (v z : HVec) (p q : Nat) :
    dotG v (act q p z) = (dotG v (dact p q z)).swap := by
  have h : dotG (dact p q z) v = (dotG (act q p z) v).swap :=
    dotG_neg (act q p z).content (act q p z).coords v
  rw [dotG_comm v (dact p q z), h, BPair.swap_swap, dotG_comm]

/-- A family's place read at the indicator: the pairing against the
place indicator is the place's own entry. -/
private theorem dotP_indAt (u : List BPair) (n k : Nat)
    (hu : u.length = n) (hk : k < n) :
    (elim.dotP u (elim.idRow n k)).oneValue
      (ground.getAt BPair.unit u k) := by
  refine BPair.oneValue_trans
    (elim.dotP_oneIndex u (elim.idRow n k) k
      (by rw [hu, elim.length_idRow])
      (by rw [elim.length_idRow]; exact hk)
      (fun j hj hjk => by
        rw [elim.length_idRow] at hj
        rw [elim.getAt_idRow n k j hj, if_neg hjk]
        exact BPair.oneValue_refl BPair.unit)) ?_
  rw [elim.getAt_idRow n k k hk, if_pos rfl]
  exact BPair.mul_ofNat_one _

/-- The moved value's place read: at an output vector over the
moved output content the moved value pairs it as the value's own
moved read does — the contraction's two arms read the two
values. -/
private theorem pairVal_place_gen (A B : List HVec) (cc : List Nat)
    (d kA : Nat) (c : List BPair)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ v ∈ B, sized v)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ v ∈ B, v.content.length = d)
    (hdegA : ∀ v ∈ A, ground.sumNat v.content = kA)
    (hccl : cc.length = d)
    (hcG : c.length
      = (blockcount.pairIdx A (fun v => v) B cc).length)
    (hszP : ∀ t ∈ pairFam A B cc c,
      sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec))
    (i j : Nat) (hi : i < d) (hj : j < d) (hijn : ¬ i = j)
    (hnull : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt j i cc) cc j i)
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))))
    (x : HVec) (hsx : sized x) (hwx : x.content.length = d)
    (hdx : ground.sumNat x.content = kA)
    (oc : List Nat) (hocw : oc.length = d)
    (hoc : List.zipWith (fun u w => u + w) x.content oc = cc)
    (hoci : 0 < ground.getAt 0 oc i)
    (hmP : ∀ t ∈ pairFam A B cc c,
      (t.2.1 : HVec).content = (dact j i x).content →
      (t.2.2 : HVec).content = moveAt j i oc)
    (hmP2 : ∀ t ∈ pairFam A B cc c,
      (t.2.1 : HVec).content = x.content →
      (t.2.2 : HVec).content = oc)
    (b : HVec) (hsb : sized b) (hbc : b.content = moveAt j i oc) :
    (elim.dotP (pairVal (pairFam A B cc c) (dact j i x)
        (moveAt j i oc)).coords b.coords).oneValue
      (elim.dotP (act j i (pairVal (pairFam A B cc c) x oc)).coords
        b.coords) := by
  have hJIN : ¬ j = i := fun hc => hijn hc.symm
  have hix : i < x.content.length := by rw [hwx]; exact hi
  have hjoc : j < oc.length := by rw [hocw]; exact hj
  have hioc : i < oc.length := by rw [hocw]; exact hi
  have hcci : 0 < ground.getAt 0 cc i := by
    have h := ground.getAt_zipWith 0 0 0 (fun u w => u + w)
      x.content oc i hix hioc
    rw [hoc] at h
    rw [h]
    exact Nat.lt_of_lt_of_le hoci (Nat.le_add_left _ _)
  have hroundoc : moveAt i j (moveAt j i oc) = oc :=
    moveAt_round_at i j oc hoci
  have hzbc : List.zipWith (fun u w => u + w) x.content b.content
      = moveAt j i cc := by
    rw [hbc, moveAt_zipWith_right j i x.content oc hoci, hoc]
  have hwb : b.content.length = d := by
    rw [hbc, length_moveAt, hocw]
  have hbj : 0 < ground.getAt 0 b.content j := by
    rw [hbc]
    show 0 < ground.getAt 0 (ground.bumpAt j (dipAt i oc)) j
    rw [ground.getAt_bumpAt_self j (dipAt i oc)
      (by rw [ground.length_dipAt]; exact hjoc)]
    exact Nat.succ_pos _
  have hbcoords : (act i j b).coords
      = elim.matVec (units.matUnitAt oc (moveAt j i oc) i j)
        b.coords := by
    show elim.matVec (units.matUnitAt (moveAt i j b.content)
      b.content i j) b.coords = _
    rw [hbc, hroundoc]
  have hUlen : (pairVal (pairFam A B cc c) x oc).coords.length
      = (places.monomialsAt oc).length := by
    rw [pairVal_coords]
    exact elim.length_combo _ _ _
      (pairRowsW (pairFam A B cc c) x.content oc hszP hmP2)
  have hcon := grid_contract_gen A B cc d kA c hszA hszB hwA hwB
    hdegA hccl i j hi hj hijn hnull x b hsx hsb hwx hwb hdx hbj
    hcci hzbc
  have hsp : (elim.dotP c
      ((blockcount.pairIdx A (fun v => v) B cc).map
        (fun t => dotG t.1 (act i j x) * dotG t.2 b
          + dotG t.1 x * dotG t.2 (act i j b)))).oneValue
      (elim.dotP c ((blockcount.pairIdx A (fun v => v) B cc).map
          (fun t => dotG t.1 (act i j x) * dotG t.2 b))
        + elim.dotP c ((blockcount.pairIdx A (fun v => v) B cc).map
          (fun t => dotG t.1 x * dotG t.2 (act i j b)))) :=
    BPair.oneValue_trans
      (BPair.oneValue_of_eq (congrArg (elim.dotP c)
        (elim.mapAdd _ _ _).symm))
      (elim.dotP_vecAdd_right c _ _
        (by rw [ground.length_map, ground.length_map]))
  have harm1 : (elim.dotP c
      ((blockcount.pairIdx A (fun v => v) B cc).map
        (fun t => dotG t.1 (act i j x) * dotG t.2 b))).oneValue
      ((elim.dotP (pairVal (pairFam A B cc c) (dact j i x)
        (moveAt j i oc)).coords b.coords).swap) := by
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right c _ _
        (poly.oneValue_map _ (fun (t : HVec × HVec) =>
            (dotG t.1 (dact j i x) * dotG t.2 b).swap) _
          (fun t _ => BPair.oneValue_of_eq (by
            rw [dotG_dact t.1 x j i, BPair.swap_mul])))) ?_
    rw [← ground.map_map (fun (t : HVec × HVec) =>
        dotG t.1 (dact j i x) * dotG t.2 b) BPair.swap,
      elim.dotP_swapMap]
    refine ground.swap_congr ?_
    rw [← pairFam_fold A B cc c
      (fun a w => dotG a (dact j i x) * dotG w b) hcG]
    refine BPair.oneValue_trans
      (pairVal_pair (pairFam A B cc c) (dact j i x) b
        (moveAt j i oc) hszP hmP hbc) ?_
    rw [show dotG (pairVal (pairFam A B cc c) (dact j i x)
          (moveAt j i oc)) b
        = elim.dotP (pairVal (pairFam A B cc c) (dact j i x)
            (moveAt j i oc)).coords b.coords from
      if_pos (show moveAt j i oc = b.content from hbc.symm)]
    exact BPair.oneValue_refl _
  have harm2 : (elim.dotP c
      ((blockcount.pairIdx A (fun v => v) B cc).map
        (fun t => dotG t.1 x * dotG t.2 (act i j b)))).oneValue
      (elim.dotP (act j i (pairVal (pairFam A B cc c) x oc)).coords
        b.coords) := by
    rw [← pairFam_fold A B cc c
      (fun a w => dotG a x * dotG w (act i j b)) hcG]
    have hbc2 : (act i j b).content = oc := by
      show moveAt i j b.content = oc
      rw [hbc]
      exact hroundoc
    refine BPair.oneValue_trans
      (pairVal_pair (pairFam A B cc c) x (act i j b) oc hszP hmP2
        hbc2) ?_
    rw [show dotG (pairVal (pairFam A B cc c) x oc) (act i j b)
        = elim.dotP (pairVal (pairFam A B cc c) x oc).coords
          (act i j b).coords from
      if_pos (show oc = (act i j b).content from hbc2.symm),
      hbcoords]
    refine BPair.oneValue_symm ?_
    show (elim.dotP (elim.matVec
        (units.matUnitAt (moveAt j i oc) oc j i)
        (pairVal (pairFam A B cc c) x oc).coords) b.coords).oneValue _
    exact unit_adjoint j i oc hjoc hioc hJIN hoci
      (pairVal (pairFam A B cc c) x oc).coords b.coords hUlen
      (show b.coords.length
          = (places.monomialsAt (moveAt j i oc)).length by
        rw [← hbc]; exact hsb)
  exact BPair.oneValue_symm (ground.oneOfUnit
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.add_congr harm1 harm2))
        (BPair.oneValue_trans (BPair.oneValue_symm hsp) hcon))))

/-- The complementary grid's value map is equivariant at the
raising direction: at a one-degree first list inside the width,
a kernel datum of the stacked raising at the fused content, and
an output content of that width joining the argument's at it, the
value at the dual argument reads the value's own moved read,
place for place — `lem:dualread`(i)'s moved-reads sentence at the
tensor grid, clause (iii)'s carrier. -/
private theorem pairVal_equiv_gen (A B : List HVec) (cc : List Nat)
    (d kA : Nat) (c : List BPair)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ v ∈ B, sized v)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ v ∈ B, v.content.length = d)
    (hdegA : ∀ v ∈ A, ground.sumNat v.content = kA)
    (hcw : cc.length = d)
    (hc : c.length = (pairsAt A B cc).length)
    (i j : Nat) (hi : i < d) (hj : j < d) (hijn : ¬ i = j)
    (hnull : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i j cc) cc i j)
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))))
    (x : HVec) (hsx : sized x) (hwx : x.content.length = d)
    (oc : List Nat) (hocw : oc.length = d)
    (hoc : List.zipWith (fun u w => u + w) x.content oc = cc) :
    poly.oneValue
      (pairVal (pairFam A B cc c) (dact i j x)
        (moveAt i j oc)).coords
      (act i j (pairVal (pairFam A B cc c) x oc)).coords := by
  have hIJN0 : ¬ i = j := hijn
  have hJIN0 : ¬ j = i := fun hh => hIJN0 hh.symm
  have hjx : j < x.content.length := by rw [hwx]; exact hj
  have hjoc : j < oc.length := by rw [hocw]; exact hj
  have hcG : c.length
      = (blockcount.pairIdx A (fun v => v) B cc).length := by
    rw [hc, pairsAt_len A B cc]
  have hszP : ∀ t ∈ pairFam A B cc c,
      sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec) := fun t ht =>
    match pairFam_slots A B cc c t ht with
    | ⟨ha, hb, _⟩ => ⟨hszA _ ha, hszB _ hb⟩
  have hmP2 : ∀ t ∈ pairFam A B cc c,
      (t.2.1 : HVec).content = x.content →
      (t.2.2 : HVec).content = oc := by
    intro t ht hcv
    match pairFam_slots A B cc c t ht with
    | ⟨hta, htb, htg⟩ =>
      refine blockcount.zipWith_add_cancelL t.2.1.content
        t.2.2.content oc t.2.2.content.length ?_ rfl ?_ ?_
      · rw [hwA _ hta, hwB _ htb]
      · rw [hwB _ htb, hocw]
      · rw [htg, hcv, hoc]
  by_cases hdx : ground.sumNat x.content = kA
  · by_cases hocj : 0 < ground.getAt 0 oc j
    · have hround : moveAt j i (moveAt i j cc) = cc := by
        refine moveAt_round_at j i cc ?_
        have h := ground.getAt_zipWith 0 0 0 (fun u w => u + w)
          x.content oc j hjx hjoc
        rw [hoc] at h
        rw [h]
        exact Nat.lt_of_lt_of_le hocj (Nat.le_add_left _ _)
      have hzbc : List.zipWith (fun u w => u + w) x.content
          (moveAt i j oc) = moveAt i j cc := by
        rw [moveAt_zipWith_right i j x.content oc hocj, hoc]
      have hmP : ∀ t ∈ pairFam A B cc c,
          (t.2.1 : HVec).content = (dact i j x).content →
          (t.2.2 : HVec).content = moveAt i j oc := by
        intro t ht hcv
        match pairFam_slots A B cc c t ht with
        | ⟨hta, htb, htg⟩ =>
          by_cases hxi : 0 < ground.getAt 0 x.content i
          · refine blockcount.zipWith_add_cancelL t.2.1.content
              t.2.2.content (moveAt i j oc)
              t.2.2.content.length ?_ rfl ?_ ?_
            · rw [hwA _ hta, hwB _ htb]
            · rw [length_moveAt, hocw, hwB _ htb]
            · rw [htg, hcv]
              show cc = List.zipWith (fun u w => u + w)
                (moveAt j i x.content) (moveAt i j oc)
              rw [moveAt_zipWith_left j i x.content (moveAt i j oc) hxi,
                hzbc, hround]
          · exfalso
            have hxp0 : ground.getAt 0 x.content i = 0 :=
              Nat.le_antisymm (Nat.ge_of_not_lt hxi) (Nat.zero_le _)
            have hsum : ground.sumNat t.2.1.content
                = ground.sumNat x.content + 1 := by
              rw [hcv]
              show ground.sumNat
                  (ground.bumpAt j (dipAt i x.content))
                = ground.sumNat x.content + 1
              rw [ground.dipAt_of_zero i x.content hxp0,
                ground.sumNat_bumpAt j x.content hjx]
            rw [hdegA _ hta, hdx] at hsum
            exact absurd hsum (Nat.ne_of_lt (Nat.lt_succ_self kA))
      have hLlen : (pairVal (pairFam A B cc c) (dact i j x)
          (moveAt i j oc)).coords.length
          = (places.monomialsAt (moveAt i j oc)).length := by
        rw [pairVal_coords]
        exact elim.length_combo _ _ _
          (pairRowsW (pairFam A B cc c) (dact i j x).content
            (moveAt i j oc) hszP hmP)
      have hRlen : (act i j
          (pairVal (pairFam A B cc c) x oc)).coords.length
          = (places.monomialsAt (moveAt i j oc)).length := by
        show (elim.matVec (units.matUnitAt (moveAt i j oc) oc i j)
          (pairVal (pairFam A B cc c) x oc).coords).length = _
        rw [units.matVec_matUnitAt_length]
      refine poly.ov_of_getAt (fun k => ?_)
      by_cases hk : k < (places.monomialsAt (moveAt i j oc)).length
      · exact BPair.oneValue_trans
          (BPair.oneValue_symm (dotP_indAt _ _ k hLlen hk))
          (BPair.oneValue_trans
            (pairVal_place_gen A B cc d kA c hszA hszB hwA hwB
              hdegA hcw hcG hszP j i hj hi
              (fun hh => hijn hh.symm) hnull x hsx hwx hdx oc hocw
              hoc hocj hmP hmP2
              ⟨moveAt i j oc, elim.idRow
                (places.monomialsAt (moveAt i j oc)).length k⟩
              (show (elim.idRow (places.monomialsAt
                    (moveAt i j oc)).length k).length
                  = (places.monomialsAt (moveAt i j oc)).length from
                elim.length_idRow _ k)
              rfl)
            (dotP_indAt _ _ k hRlen hk))
      · rw [ground.getAt_over BPair.unit _ k
            (by rw [hLlen]; exact Nat.ge_of_not_lt hk),
          ground.getAt_over BPair.unit _ k
            (by rw [hRlen]; exact Nat.ge_of_not_lt hk)]
        exact BPair.oneValue_refl BPair.unit
    · -- the vacant output letter: both reads are the unit family
      have hz : ground.getAt 0 oc j = 0 :=
        Nat.le_antisymm (Nat.ge_of_not_lt hocj) (Nat.zero_le _)
      refine poly.unitTail_oneValue ?_ ?_
      · refine pairVal_null _ _ _ (fun t ht hcv => ?_)
        exfalso
        match pairFam_slots A B cc c t ht with
        | ⟨hta, htb, htg⟩ =>
          have hccj : ground.getAt 0 cc j
              = ground.getAt 0 t.2.1.content j
                + ground.getAt 0 t.2.2.content j := by
            rw [← htg]
            exact ground.getAt_zipWith 0 0 0 (fun u w => u + w)
              t.2.1.content t.2.2.content j
              (by rw [hwA _ hta]; exact hj)
              (by rw [hwB _ htb]; exact hj)
          have hccj' : ground.getAt 0 cc j
              = ground.getAt 0 x.content j
                + ground.getAt 0 oc j := by
            rw [← hoc]
            exact ground.getAt_zipWith 0 0 0 (fun u w => u + w)
              x.content oc j hjx hjoc
          have ht1q : ground.getAt 0 t.2.1.content j
              = ground.getAt 0 x.content j + 1 := by
            rw [hcv]
            show ground.getAt 0
                (ground.bumpAt j (dipAt i x.content)) j
              = ground.getAt 0 x.content j + 1
            rw [ground.getAt_bumpAt_self j (dipAt i x.content)
                (by rw [ground.length_dipAt]; exact hjx),
              ground.getAt_dipAt_ne i x.content j hJIN0]
          have e1 : ground.getAt 0 x.content j
              = ground.getAt 0 x.content j + 1
                + ground.getAt 0 t.2.2.content j := by
            rw [← ht1q, ← hccj, hccj', hz]
            exact (Nat.add_zero _).symm
          exact Nat.noConfusion (ground.addCancelL
            (ground.getAt 0 x.content j)
            ((Nat.add_zero _).trans (e1.trans (by
              rw [Nat.add_assoc, Nat.add_comm 1
                (ground.getAt 0 t.2.2.content j)]))))
      · show poly.unitTail (elim.matVec
          (units.matUnitAt (moveAt i j oc) oc i j)
          (pairVal (pairFam A B cc c) x oc).coords)
        exact units.matVec_null_unocc _ oc i j hz _
  · -- the argument off the first list's degree
    refine poly.unitTail_oneValue ?_ ?_
    · refine pairVal_null _ _ _ (fun t ht hcv => ?_)
      by_cases hxi : 0 < ground.getAt 0 x.content i
      · exfalso
        match pairFam_slots A B cc c t ht with
        | ⟨hta, _, _⟩ =>
          refine hdx ?_
          rw [← hdegA _ hta, hcv]
          show ground.sumNat x.content
            = ground.sumNat (moveAt j i x.content)
          rw [sumNat_moveAt j i x.content hjx hxi]
      · have hxp0 : ground.getAt 0 x.content i = 0 :=
          Nat.le_antisymm (Nat.ge_of_not_lt hxi) (Nat.zero_le _)
        have hnull : poly.unitTail (dact i j x).coords :=
          poly.unitTail_swapMap _
            (units.matVec_null_unocc _ x.content j i hxp0 x.coords)
        exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl t.1)
            (elim.dotP_null_tail_right t.2.1.coords _ hnull))
          (BPair.mul_unit t.1)
    · show poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j oc) oc i j)
        (pairVal (pairFam A B cc c) x oc).coords)
      refine elim.matVec_null _ _ ?_
      refine pairVal_null _ _ _ (fun t ht hcv => ?_)
      exfalso
      match pairFam_slots A B cc c t ht with
      | ⟨hta, _, _⟩ =>
        refine hdx ?_
        rw [← hcv]
        exact hdegA _ hta

theorem pairVal_equiv (A B : List HVec) (cc : List Nat)
    (d kA : Nat) (c : List BPair)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ v ∈ B, sized v)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ v ∈ B, v.content.length = d)
    (hdegA : ∀ v ∈ A, ground.sumNat v.content = kA)
    (hcw : cc.length = d)
    (hc : c.length = (pairsAt A B cc).length)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise cc)
        ((pairsAt A B cc).map HVec.coords)) c))
    (p q : Nat) (hq : q < d) (hpq : p < q)
    (x : HVec) (hsx : sized x) (hwx : x.content.length = d)
    (oc : List Nat) (hocw : oc.length = d)
    (hoc : List.zipWith (fun u w => u + w) x.content oc = cc) :
    poly.oneValue
      (pairVal (pairFam A B cc c) (dact p q x)
        (moveAt p q oc)).coords
      (act p q (pairVal (pairFam A B cc c) x oc)).coords := by
  have hp : p < d := Nat.lt_trans hpq hq
  have hpcc : p < cc.length := by rw [hcw]; exact hp
  have hqcc : q < cc.length := by rw [hcw]; exact hq
  refine pairVal_equiv_gen A B cc d kA c hszA hszB hwA hwB hdegA
    hcw hc p q hp hq (Nat.ne_of_lt hpq) ?_ x hsx hwx oc hocw hoc
  match ground.gap_of_lt q p hpq with
  | ⟨g, hg⟩ =>
    exact raise_gap cc _
      (elim.length_combo _ c _ (pairsAt_rowsLen A B cc))
      (fun i hi => ker_adj A B cc c hker i hi) g p q hpcc hqcc hg

/-- The full-column shape at a power: the top column occupied `m`
times, every shorter column unoccupied — the shape whose exhibit is
the wedge's `m`-fold tensor.  At the vacant letter count the shape
is the empty column list, `con:places`' columns carrying positive
length. -/
def fulls (d m : Nat) : Shape :=
  match d with
  | 0 => []
  | Nat.succ e => List.replicate e 0 ++ [m]

/-- The full-column shape keeps the stated width. -/
theorem length_fulls (d m : Nat) :
    (fulls d m).length = d :=
  match d with
  | 0 => rfl
  | Nat.succ e => by
    show (List.replicate e 0 ++ [m]).length = e + 1
    rw [ground.length_append, ground.length_replicate]
    rfl

/-- The vacant occupancies below a top column total that column's
own count. -/
private theorem sumNat_zeros_top (e m : Nat) :
    ground.sumNat (List.replicate e 0 ++ [m]) = m := by
  rw [ground.sumNat_append (List.replicate e 0) [m],
    ground.sumNat_replicate_zero e, Nat.zero_add]
  rfl

/-- Every row of the full-column shape counts the top column's own
occupancies: each row reads its own entry joined to the vacant
tail's total, which is the top column's count. -/
private theorem rowList_zeros_top : ∀ e m : Nat,
    rowList (List.replicate e 0 ++ [m]) = List.replicate (e + 1) m
  | 0, _ => rfl
  | e + 1, m => by
    show (0 + ground.sumNat (List.replicate e 0 ++ [m]))
        :: rowList (List.replicate e 0 ++ [m])
      = m :: List.replicate (e + 1) m
    rw [sumNat_zeros_top e m, Nat.zero_add, rowList_zeros_top e m]

/-- The full-columns shape's row list is the constant list. -/
theorem rowList_fulls (d m : Nat) :
    rowList (fulls d m) = List.replicate d m :=
  match d with
  | 0 => rfl
  | Nat.succ e => rowList_zeros_top e m

private theorem shapeOf_fulls (d m : Nat) :
    shapeOf (List.replicate d m) = fulls d m :=
  match d with
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    show (m - m) :: shapeOf (List.replicate (k + 1) m)
      = fulls (k + 2) m
    rw [Nat.sub_self m, shapeOf_fulls (k + 1) m]
    rfl

private theorem bumpAt_fulls : ∀ n m : Nat,
    ground.bumpAt n (List.replicate n 0 ++ [m])
      = List.replicate n 0 ++ [m + 1]
  | 0, _ => rfl
  | n + 1, m => by
    show (0 : Nat) :: ground.bumpAt n (List.replicate n 0 ++ [m])
      = 0 :: (List.replicate n 0 ++ [m + 1])
    rw [bumpAt_fulls n m]

private theorem fulls_succ (d m : Nat) :
    fulls d (m + 1)
      = ground.bumpAt ((fulls d m).length - 1) (fulls d m) :=
  match d with
  | 0 => rfl
  | Nat.succ e => by
    rw [length_fulls (e + 1) m]
    exact (bumpAt_fulls e m).symm

private theorem fulls_zero_vacant (d j : Nat) :
    ground.getAt 0 (exhibit (fulls d 0)).content j = 0 := by
  rw [content_exhibit (fulls d 0)]
  match d with
  | 0 => rfl
  | Nat.succ e =>
    show ground.getAt 0
      (rowList (List.replicate e 0 ++ [0])) j = 0
    rw [ground.replicate_snoc 0 e,
      places.rowList_replicate_zero (e + 1)]
    exact ground.getAt_replicate_zero (e + 1) j

private theorem fulls_lower_unit (d : Nat) :
    ∀ (m j : Nat) (u : HVec), j + 1 < (fulls d m).length →
      lowerH j (exhibit (fulls d m)) = some u →
      poly.unitTail u.coords
  | 0, j, _, _, h => by
    have hg := (lowerH_reads h).1
    rw [fulls_zero_vacant d j] at hg
    exact absurd hg (Nat.lt_irrefl 0)
  | m + 1, j, _, hj, h => by
    have hjm : j + 1 < (fulls d m).length := by
      rw [length_fulls d m, ← length_fulls d (m + 1)]
      exact hj
    have hE : (exhibit (fulls d m)).content.length
        = (fulls d m).length := by
      rw [content_exhibit (fulls d m), places.length_rowList]
    have hadd := exhibit_addFull (fulls d m)
    rw [fulls_succ d m] at h
    have hcl : (exhibit (ground.bumpAt ((fulls d m).length - 1)
          (fulls d m))).coords.length
        = (tensorH (wedge (fulls d m).length (fulls d m).length)
          (exhibit (fulls d m))).coords.length := by
      rw [exhibit_sized (ground.bumpAt ((fulls d m).length - 1)
          (fulls d m)), hadd.1,
        tensorH_sized (wedge (fulls d m).length (fulls d m).length)
          (exhibit (fulls d m))]
    match lowerH_move hadd.1 hadd.2 h with
    | ⟨u2, hu2, _, hq2⟩ =>
      match lowerH_tensorW_unit (fulls d m).length j
          (exhibit (fulls d m)) (exhibit_sized (fulls d m)) hE hjm
          (fun w hw => fulls_lower_unit d m j w hjm hw) with
      | ⟨u3, hu3, hq3⟩ =>
        refine poly.oneValue_unitTail hq2 ?_
        rw [show u2 = u3 from Option.some.inj (hu2.symm.trans hu3)]
        exact hq3

/-- The full-column line at every power: the wedge's `m`-fold
tensor spans a line, its block's span the column exhibit's own
singleton — clause (ii)'s line read at clause (iii)'s power, the
interior lowerings descending the power to the unoccupied base. -/
theorem lineSpan : ∀ d m : Nat,
    blockSpan (fulls d m) = [exhibit (fulls d m)] := by
  intro d m
  exact blockSpan_stationary (fulls d m)
    (fun j u hj hl => fulls_lower_unit d m j u hj hl)

/-- The full-column line's occupancy at every power: the power's
unit-monomial content once, every further content vacant. -/
theorem occ_line (d n : Nat) (mu : List Nat) :
    blockcount.occ mu (blockSpan (fulls d n))
      = if mu = List.replicate d n then 1 else 0 := by
  rw [lineSpan d n]
  show (if (exhibit (fulls d n)).content = mu then 1 else 0) + 0 = _
  rw [content_exhibit, rowList_fulls d n, Nat.add_zero]
  by_cases h : mu = List.replicate d n
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

/-- The full column at one is the unit occupancy at the last key. -/
theorem fulls_one_unitAt (d : Nat) (hd : 0 < d) :
    fulls d 1 = ground.unitAt d (d - 1) := by
  match d, hd with
  | e + 1, _ =>
    rw [ground.addSubSelfR e 1,
      ground.unitAt_replicate (e + 1) e (Nat.lt_succ_self e),
      ground.addSubSelfL e 1, Nat.sub_self]
    rfl

/-- The singlet read: a top at the full-column content generates
the line, so its every interior lowering reads the unit tail —
clause (ii)'s line at clause (iii)'s power (`lem:blockirr`(iv)'s
one dimension at the shape), the adjacent raisings the whole top
read (`lem:lowerspan`: the raising kernel is the adjacent
stack's, the gap's descent at the commutator's crossed join). -/
theorem fullTop_lower (d m : Nat) (w : HVec) (hsz : sized w)
    (hwd : w.content = List.replicate d m)
    (hadj : ∀ i, i + 1 < d →
      poly.unitTail (act i (i + 1) w).coords) :
    ∀ j v, j + 1 < d → lowerH j w = some v →
      poly.unitTail v.coords := by
  intro j v hj hl
  by_cases hoff : poly.unitTail w.coords
  · rw [lowerH_eq hl]
    exact elim.matVec_null _ w.coords hoff
  · have hwl : w.content.length = d := by
      rw [hwd, ground.length_replicate]
    have htop : ∀ j, j < d → ∀ i, i < j →
        poly.unitTail (act i j w).coords := by
      intro j' hj' i hij
      match ground.gap_of_lt j' i hij with
      | ⟨g, hg⟩ =>
        show poly.unitTail (elim.matVec
          (units.matUnitAt (moveAt i j' w.content) w.content i j')
          w.coords)
        exact raise_gap w.content w.coords hsz
          (fun k hk => hadj k (by rw [← hwl]; exact hk))
          g i j' (by rw [hwl]; exact Nat.lt_trans hij hj')
          (by rw [hwl]; exact hj') hg
    have hlen := seedBlock_dim d w hsz hwl hoff htop
      (lowerspan.ht w.content + 1) (Nat.le_succ _)
    have hline : (blockSpan (shapeOf w.content)).length = 1 := by
      rw [hwd, shapeOf_fulls d m, lineSpan d m]
      rfl
    rw [hline] at hlen
    exact closeSpan_seed_line d (lowerspan.ht w.content) w hlen
      j v hj hl

/-! The lowering direction's mirror tier at the singlet frame: at
the full-column fused content the grid's combination is a top, so
the singlet read nulls its adjacent lowerings, the gap's descent
carries them to every lowering below the width, and the moved
contraction, the place read and the equivariance run the raising
tier's spine at the exchanged letters. -/

/-- Every adjacent lowering annihilates the singlet grid's
combination: the fused vector is a top at the full-column content,
so the singlet read nulls its lowerings, and an unoccupied letter
reads the action null outright. -/
private theorem ker_lower_adj (A B : List HVec) (d m : Nat)
    (cc : List Nat) (c : List BPair)
    (hcc : cc = List.replicate d m)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise cc)
        ((pairsAt A B cc).map HVec.coords)) c))
    (j : Nat) (hj : j + 1 < cc.length) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt (j + 1) j cc) cc (j + 1) j)
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))) := by
  by_cases hocc : 0 < ground.getAt 0 cc j
  · have hszF : sized (⟨cc,
        elim.combo (places.monomialsAt cc).length c
          ((pairsAt A B cc).map HVec.coords)⟩ : HVec) :=
      elim.length_combo _ c _ (pairsAt_rowsLen A B cc)
    have hj' : j + 1 < d := by
      rw [← ground.length_replicate m d, ← hcc]
      exact hj
    have hadjF : ∀ i, i + 1 < d →
        poly.unitTail (act i (i + 1) (⟨cc,
          elim.combo (places.monomialsAt cc).length c
            ((pairsAt A B cc).map HVec.coords)⟩ : HVec)).coords := by
      intro i hi
      exact ker_adj A B cc c hker i
        (by rw [hcc, ground.length_replicate]; exact hi)
    rw [moveAt_moveDn j cc]
    exact fullTop_lower d m _ hszF hcc hadjF j
      ⟨units.moveDn j cc,
        elim.matVec (units.matUnitAt (units.moveDn j cc) cc
          (j + 1) j) (elim.combo (places.monomialsAt cc).length c
            ((pairsAt A B cc).map HVec.coords))⟩ hj' (if_pos hocc)
  · exact units.matVec_null_unocc _ cc (j + 1) j
      (Nat.le_antisymm (Nat.ge_of_not_lt hocc) (Nat.zero_le _)) _

/-- Every lowering below the width annihilates the singlet grid's
combination, the adjacent reads at the singlet's own null lowerings
and the descent on the gap. -/
private theorem ker_lower (A B : List HVec) (d m : Nat)
    (cc : List Nat) (c : List BPair)
    (hcc : cc = List.replicate d m)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise cc)
        ((pairsAt A B cc).map HVec.coords)) c))
    (i j : Nat) (hi : i < cc.length) (hij : j < i) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i j cc) cc i j)
      (elim.combo (places.monomialsAt cc).length c
        ((pairsAt A B cc).map HVec.coords))) := by
  match ground.gap_of_lt i j hij with
  | ⟨g, hg⟩ =>
    exact lower_gap cc _
      (elim.length_combo _ c _ (pairsAt_rowsLen A B cc))
      (fun k hk => ker_lower_adj A B d m cc c hcc hker k hk)
      g j i (Nat.lt_trans hij hi) hi hg

/-- The complementary grid's value map is equivariant at the
lowering direction on the singlet system: at the full-column fused
content the combination's lowerings are null — the singlet read —
so the value at the dual argument reads the value's own moved read
at the lowering as well, `lem:dualread`(i)'s moved-reads sentence
completed at the letter pair's other side, clause (iii)'s
carrier. -/
theorem pairVal_equiv_lower (A B : List HVec) (cc : List Nat)
    (d kA m : Nat) (c : List BPair)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ v ∈ B, sized v)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ v ∈ B, v.content.length = d)
    (hdegA : ∀ v ∈ A, ground.sumNat v.content = kA)
    (hcw : cc.length = d)
    (hcc : cc = List.replicate d m)
    (hc : c.length = (pairsAt A B cc).length)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise cc)
        ((pairsAt A B cc).map HVec.coords)) c))
    (p q : Nat) (hq : q < d) (hpq : p < q)
    (x : HVec) (hsx : sized x) (hwx : x.content.length = d)
    (oc : List Nat) (hocw : oc.length = d)
    (hoc : List.zipWith (fun u w => u + w) x.content oc = cc) :
    poly.oneValue
      (pairVal (pairFam A B cc c) (dact q p x)
        (moveAt q p oc)).coords
      (act q p (pairVal (pairFam A B cc c) x oc)).coords := by
  have hp : p < d := Nat.lt_trans hpq hq
  have hqcc : q < cc.length := by rw [hcw]; exact hq
  exact pairVal_equiv_gen A B cc d kA c hszA hszB hwA hwB hdegA
    hcw hc q p hq hp (fun hh => Nat.ne_of_lt hpq hh.symm)
    (ker_lower A B d m cc c hcc hker q p hqcc hpq) x hsx hwx
    oc hocw hoc

/-- The bumped shape's span is the span at the wedge tensored on,
member for member, with the dimension the mapped span's — clause
(ii)'s transport read at the height measure's own discharge
(`blockcount.blockSpan_addFull` at `lowerspan.ht`). -/
theorem spanAddFull (lam : Shape) :
    (blockSpan (ground.bumpAt (lam.length - 1) lam)).length
      = (blockSpan lam).length
    ∧ ∀ k, k < (blockSpan lam).length →
      (ground.getAt (⟨[], []⟩ : HVec)
          (blockSpan (ground.bumpAt (lam.length - 1) lam))
          k).content
        = (tensorH (wedge lam.length lam.length)
            (ground.getAt (⟨[], []⟩ : HVec)
              (blockSpan lam) k)).content
      ∧ poly.oneValue
          (ground.getAt (⟨[], []⟩ : HVec)
            (blockSpan (ground.bumpAt (lam.length - 1) lam))
            k).coords
          (tensorH (wedge lam.length lam.length)
            (ground.getAt (⟨[], []⟩ : HVec)
              (blockSpan lam) k)).coords :=
  blockcount.blockSpan_addFull lam lowerspan.ht
    (lowerspan.ht_nomove lam.length) (lowerspan.ht_drop lam.length)
    (lowerspan.ht_exh lam)

/-- The bumped shape's occupancies read at the shifted contents —
clause (ii)'s occupancy read at the height measure's discharge,
the width binder load-bearing at the shift's truncation. -/
theorem occupancyAddFull (lam : Shape) (mu : List Nat)
    (hmu : mu.length = lam.length) :
    occupancyAt (blockSpan (ground.bumpAt (lam.length - 1) lam))
      (tensorH (wedge lam.length lam.length)
        (⟨mu, []⟩ : HVec)).content
    = occupancyAt (blockSpan lam) mu :=
  blockcount.occupancy_addFull lam lowerspan.ht
    (lowerspan.ht_nomove lam.length) (lowerspan.ht_drop lam.length)
    (lowerspan.ht_exh lam) mu hmu

/-! `lem:dualread`(ii)'s mapped-span engine: the block at one more
full column reads its span at the full wedge tensored on, so the
fused pool, the counts and the span length read the mapped span's
— the fused pool against a further block pairs the mapped members
at the arrangements' join, the pair list at a shifted content is
the content's own list mapped, and the stacked raisings annihilate
a coefficient family's combination at the mapped list exactly
where they annihilate it at the list.  The fusion count's descent
at one full column (`con:labels`' class-invariance clause) is the
two carrier exchanges composed at the shifted row list. -/

/-- The bumped shape's every span member reads the wedge tensored
onto a member of the shape's own span, the transport at its own
key. -/
private theorem addFull_mem_fwd (a : Shape) :
    ∀ v ∈ blockSpan (ground.bumpAt (a.length - 1) a),
      ∃ v₀, v₀ ∈ blockSpan a
        ∧ v.content = (tensorH (wedge a.length a.length) v₀).content
        ∧ poly.oneValue v.coords
          (tensorH (wedge a.length a.length) v₀).coords := by
  intro v hv
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) hv with
  | ⟨k, hk, hkv⟩ =>
    have hkA : k < (blockSpan a).length := by
      rw [← (spanAddFull a).1]
      exact hk
    refine ⟨ground.getAt (⟨[], []⟩ : HVec) (blockSpan a) k,
      ground.mem_getAt _ _ k hkA, ?_, ?_⟩
    · rw [← hkv]
      exact ((spanAddFull a).2 k hkA).1
    · rw [← hkv]
      exact ((spanAddFull a).2 k hkA).2

/-- Every member of the shape's own span is read by a member of the
bumped shape's, the transport's converse half at its own key. -/
private theorem addFull_mem_bwd (a : Shape) :
    ∀ v₀ ∈ blockSpan a,
      ∃ v, v ∈ blockSpan (ground.bumpAt (a.length - 1) a)
        ∧ v.content = (tensorH (wedge a.length a.length) v₀).content
        ∧ poly.oneValue v.coords
          (tensorH (wedge a.length a.length) v₀).coords := by
  intro v₀ hv₀
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) hv₀ with
  | ⟨k, hk, hkv⟩ =>
    have hk' : k < (blockSpan
        (ground.bumpAt (a.length - 1) a)).length := by
      rw [(spanAddFull a).1]
      exact hk
    refine ⟨ground.getAt (⟨[], []⟩ : HVec)
      (blockSpan (ground.bumpAt (a.length - 1) a)) k,
      ground.mem_getAt _ _ k hk', ?_, ?_⟩
    · rw [← hkv]
      exact ((spanAddFull a).2 k hk).1
    · rw [← hkv]
      exact ((spanAddFull a).2 k hk).2

/-- The fused pair at one member pair: the wedge tensored onto the
pair's own tensor reads the bumped member's tensor against the same
second member, the arrangements' join regrouping the three factors
(`blockcount.tensorH_assoc`) with the first factors' one-value read
carried across the tensor. -/
private theorem line_pair (a b : Shape) (hba : b.length = a.length)
    (v v₀ w : HVec) (hv₀ : v₀ ∈ blockSpan a) (hw : w ∈ blockSpan b)
    (hsv : sized v)
    (hcv : v.content
      = (tensorH (wedge a.length a.length) v₀).content)
    (hqv : poly.oneValue v.coords
      (tensorH (wedge a.length a.length) v₀).coords) :
    (tensorH (wedge a.length a.length) (tensorH v₀ w)).content
        = (tensorH v w).content
      ∧ poly.oneValue
        (tensorH (wedge a.length a.length) (tensorH v₀ w)).coords
        (tensorH v w).coords := by
  have hsv₀ : sized v₀ := (lowerspan.spanReads a).1 v₀ hv₀
  have hsw : sized w := (lowerspan.spanReads b).1 w hw
  have hwd : (wedge a.length a.length).content.length = a.length :=
    wedge_clen a.length a.length
  have hv₀d : v₀.content.length = a.length :=
    blockSpan_width a v₀ hv₀
  have hwwd : w.content.length = a.length :=
    (blockSpan_width b w hw).trans hba
  have hass := tensorH_assoc (wedge a.length a.length) v₀ w
    (wedge_sized a.length a.length) hsv₀ hsw
    (hwd.trans hv₀d.symm) (hv₀d.trans hwwd.symm)
  have hpo := tensorH_polyOne
    (tensorH (wedge a.length a.length) v₀) v w w
    (tensorH_sized _ _) hsv hsw hsw hcv.symm rfl
    (poly.oneValue_symm hqv) (poly.oneValue_refl _)
  refine ⟨?_, poly.oneValue_trans (poly.oneValue_symm hass.2) hpo⟩
  rw [← hass.1, content_tensorH
      (tensorH (wedge a.length a.length) v₀) w,
    content_tensorH v w, hcv]

/-- Two carriers whose members read one another's contents and
coordinates read one count at every content: each member sits in
the partner carrier's content group's span at the one-value read
(`blockcount.countAt_congr` at `elim.spanRel_congr`). -/
private theorem countAt_pool_corr (P Q : List HVec) (mu : List Nat)
    (hszP : ∀ x ∈ P, sized x) (hszQ : ∀ x ∈ Q, sized x)
    (hPQ : ∀ x ∈ P, ∃ y, y ∈ Q ∧ y.content = x.content
      ∧ poly.oneValue y.coords x.coords)
    (hQP : ∀ y ∈ Q, ∃ x, x ∈ P ∧ x.content = y.content
      ∧ poly.oneValue x.coords y.coords) :
    countAt P mu = countAt Q mu := by
  refine countAt_congr mu P Q hszP hszQ ?_ ?_
  · refine group_span_rows P Q mu hszP ?_
    intro x hx
    match hPQ x hx with
    | ⟨y, hy, hyc, hyq⟩ =>
      have hsx : x.coords.length
          = (monomialsAt x.content).length := hszP x hx
      have h := spanRel_groupAt_mem Q y hy hszQ
      rw [hyc] at h
      rw [hsx]
      exact elim.spanRel_congr _ _ y.coords x.coords hyq h hsx
  · refine group_span_rows Q P mu hszQ ?_
    intro y hy
    match hQP y hy with
    | ⟨x, hx, hxc, hxq⟩ =>
      have hsy : y.coords.length
          = (monomialsAt y.content).length := hszQ y hy
      have h := spanRel_groupAt_mem P x hx hszP
      rw [hxc] at h
      rw [hsy]
      exact elim.spanRel_congr _ _ x.coords y.coords hxq h hsy

/-- The carrier exchange at the mapped fused pool, every content at
once: the bumped shape's fused pool against a further block is the
pool's own with the wedge tensored on, member for member — the
mapped member's tensor regrouped at the arrangements' join — so the
two carriers read one count at every content.  The one letter width
`hba` is load-bearing with its committed refusal; the letter count's
positivity is derivable and is not carried. -/
theorem countAt_fusedLine (a b : Shape) (hba : b.length = a.length)
    (mm : List Nat) :
    countAt (fusedAt (blockSpan (ground.bumpAt (a.length - 1) a))
        (blockSpan b)) mm
      = countAt ((fusedAt (blockSpan a) (blockSpan b)).map
          (fun v => tensorH (wedge a.length a.length) v)) mm := by
  refine countAt_pool_corr _ _ mm ?_ ?_ ?_ ?_
  · intro x hx
    match ground.mem_flatMap_of _ _ x hx with
    | ⟨v, _, hxv⟩ =>
      match ground.mem_map_of (tensorH v) _ x hxv with
      | ⟨w, _, hwx⟩ =>
        rw [← hwx]
        exact tensorH_sized v w
  · intro y hy
    match ground.mem_map_of _ _ y hy with
    | ⟨z, _, hzy⟩ =>
      rw [← hzy]
      exact tensorH_sized _ z
  · intro x hx
    match ground.mem_flatMap_of _ _ x hx with
    | ⟨v, hv, hxv⟩ =>
      match ground.mem_map_of (tensorH v) _ x hxv with
      | ⟨w, hw, hwx⟩ =>
        match addFull_mem_fwd a v hv with
        | ⟨v₀, hv₀, hcv, hqv⟩ =>
          have hpair := line_pair a b hba v v₀ w hv₀ hw
            ((lowerspan.spanReads _).1 v hv) hcv hqv
          refine ⟨tensorH (wedge a.length a.length) (tensorH v₀ w),
            ground.mem_map_to _ (ground.mem_flatMap_to _ hv₀
              (ground.mem_map_to (tensorH v₀) hw)), ?_, ?_⟩
          · rw [← hwx]
            exact hpair.1
          · rw [← hwx]
            exact hpair.2
  · intro y hy
    match ground.mem_map_of _ _ y hy with
    | ⟨z, hz, hzy⟩ =>
      match ground.mem_flatMap_of _ _ z hz with
      | ⟨v₀, hv₀, hzv⟩ =>
        match ground.mem_map_of (tensorH v₀) _ z hzv with
        | ⟨w, hw, hwz⟩ =>
          match addFull_mem_bwd a v₀ hv₀ with
          | ⟨v, hv, hcv, hqv⟩ =>
            have hpair := line_pair a b hba v v₀ w hv₀ hw
              ((lowerspan.spanReads _).1 v hv) hcv hqv
            refine ⟨tensorH v w, ground.mem_flatMap_to _ hv
              (ground.mem_map_to (tensorH v) hw), ?_, ?_⟩
            · rw [← hzy, ← hwz]
              exact hpair.1.symm
            · rw [← hzy, ← hwz]
              exact poly.oneValue_symm hpair.2

/-- The wedge tensored onto a coordinate family at a stated
content, the mapped list's own row. -/
private def rowW (d : Nat) (cc : List Nat) (r : List BPair) :
    List BPair :=
  (tensorH (wedge d d) ⟨cc, r⟩).coords

/-- The mapped row's width is the shifted content's enumeration. -/
private theorem rowW_len (d : Nat) (cc : List Nat)
    (r : List BPair) :
    (rowW d cc r).length
      = (monomialsAt (List.zipWith (fun a b => a + b)
          (wedge d d).content cc)).length :=
  tensorH_sized (wedge d d) ⟨cc, r⟩

/-- The mapped row sits at the unit tail exactly where its own row
does, the wedge's family off it. -/
private theorem rowW_unit (d : Nat) (cc : List Nat)
    (hcl : cc.length = d) (a : List BPair)
    (ha : a.length = (monomialsAt cc).length) :
    (poly.unitTail (rowW d cc a) ↔ poly.unitTail a) := by
  have hw : (wedge d d).content.length = cc.length := by
    rw [wedge_clen d d, hcl]
  constructor
  · intro h
    match (tensorH_unitTail (wedge d d) ⟨cc, a⟩
        (wedge_sized d d) ha hw).mp h with
    | Or.inl hwu => exact absurd hwu (wedge_off_unit d)
    | Or.inr hx => exact hx
  · intro h
    exact (tensorH_unitTail (wedge d d) ⟨cc, a⟩
      (wedge_sized d d) ha hw).mpr (Or.inr h)

/-- The mapped row reads one value at a one-value row. -/
private theorem rowW_congr (d : Nat) (cc : List Nat)
    (a b : List BPair) (ha : a.length = (monomialsAt cc).length)
    (hb : b.length = (monomialsAt cc).length)
    (h : poly.oneValue a b) :
    poly.oneValue (rowW d cc a) (rowW d cc b) :=
  tensorH_polyOne (wedge d d) (wedge d d) ⟨cc, a⟩ ⟨cc, b⟩
    (wedge_sized d d) (wedge_sized d d) ha hb rfl rfl
    (poly.oneValue_refl _) h

/-- A combination over the mapped list is the mapped combination,
the tensor's additivity and scale-equivariance in the second
factor folded along the coefficients. -/
private theorem rowW_combo (d : Nat) (cc : List Nat)
    (hcl : cc.length = d) :
    ∀ (cs : List BPair) (M : elim.Mat),
    elim.rowsLen (monomialsAt cc).length M →
    poly.oneValue
      (elim.combo (monomialsAt (List.zipWith (fun a b => a + b)
        (wedge d d).content cc)).length cs (M.map (rowW d cc)))
      (rowW d cc (elim.combo (monomialsAt cc).length cs M))
  | [], M, _ =>
    poly.unitTail_oneValue (poly.unitTail_replicate _)
      ((rowW_unit d cc hcl _
        (ground.length_replicate BPair.unit _)).mpr
        (poly.unitTail_replicate _))
  | _ :: _, [], _ =>
    poly.unitTail_oneValue (poly.unitTail_replicate _)
      ((rowW_unit d cc hcl _
        (ground.length_replicate BPair.unit _)).mpr
        (poly.unitTail_replicate _))
  | c :: cs, r :: M, hM => by
    have hr : r.length = (monomialsAt cc).length := hM.1
    have hcb : (elim.combo (monomialsAt cc).length cs M).length
        = (monomialsAt cc).length := elim.length_combo _ cs M hM.2
    have hsc : (elim.vecScale c r).length
        = (monomialsAt cc).length := by
      rw [elim.length_vecScale c r, hr]
    show poly.oneValue
      (elim.vecAdd (elim.vecScale c (rowW d cc r))
        (elim.combo _ cs (M.map (rowW d cc))))
      (rowW d cc (elim.vecAdd (elim.vecScale c r)
        (elim.combo (monomialsAt cc).length cs M)))
    refine poly.oneValue_trans
      (elim.polyOne_vecAdd _ (rowW d cc (elim.vecScale c r)) _
        (rowW d cc (elim.combo (monomialsAt cc).length cs M))
        (poly.oneValue_symm (tensorW_vecScale d cc c r hcl hr))
        (rowW_combo d cc hcl cs M hM.2)
        (by rw [elim.length_vecScale c (rowW d cc r),
            rowW_len d cc r, rowW_len d cc (elim.vecScale c r)])
        (by rw [elim.length_combo _ cs (M.map (rowW d cc))
            (elim.rowsLen_map _ _ _ (fun x _ => rowW_len d cc x)),
          rowW_len d cc _])) ?_
    exact poly.oneValue_symm
      (tensorW_vecAdd d cc (elim.vecScale c r)
        (elim.combo (monomialsAt cc).length cs M) hcl hsc hcb)

/-- A span member's mapped row sits in the mapped list's span, the
clearing scalar kept and the combination mapped. -/
private theorem rowW_span (d : Nat) (cc : List Nat)
    (hcl : cc.length = d) (M : elim.Mat)
    (hM : elim.rowsLen (monomialsAt cc).length M)
    (v : List BPair) (hv : v.length = (monomialsAt cc).length)
    (h : elim.spanRel (monomialsAt cc).length M v) :
    elim.spanRel (monomialsAt (List.zipWith (fun a b => a + b)
        (wedge d d).content cc)).length (M.map (rowW d cc))
      (rowW d cc v) :=
  elim.spanRel_mapBy (monomialsAt cc).length
    (monomialsAt (List.zipWith (fun a b => a + b)
      (wedge d d).content cc)).length (rowW d cc)
    (fun x => rowW_len d cc x)
    (fun a b ha hb hone => rowW_congr d cc a b ha hb hone)
    (fun c x hx => tensorW_vecScale d cc c x hcl hx)
    (fun cs M' hM' =>
      poly.oneValue_symm (rowW_combo d cc hcl cs M' hM'))
    M hM v hv h

/-- The mapped list keeps the independence: a null combination of
mapped rows is the mapped null combination, the wedge tensored on
withdrawn at the coefficients. -/
private theorem rowW_indep (d : Nat) (cc : List Nat)
    (hcl : cc.length = d) (M : elim.Mat)
    (hM : elim.rowsLen (monomialsAt cc).length M)
    (hi : elim.indepRows (monomialsAt cc).length M) :
    elim.indepRows (monomialsAt (List.zipWith (fun a b => a + b)
      (wedge d d).content cc)).length (M.map (rowW d cc)) :=
  elim.indep_mapBy (monomialsAt cc).length
    (monomialsAt (List.zipWith (fun a b => a + b)
      (wedge d d).content cc)).length (rowW d cc)
    (fun x => rowW_len d cc x)
    (fun x hx h => (rowW_unit d cc hcl x hx).mp h)
    (fun cs M' hM' =>
      poly.oneValue_symm (rowW_combo d cc hcl cs M' hM'))
    M hM hi

/-- The stacked raisings annihilate a mapped row exactly where they
annihilate the row: at the shifted content every letter is
occupied, so the stacked datum carries a block at each of them, and
each block's read is the further factor's own
(`blockcount.act_tensorW_unit`) — at a letter vacant in the
content the block's read is the sum's unit outright, the action's
vacant-source read. -/
private theorem stackW_unit (d : Nat) (cc : List Nat)
    (hcl : cc.length = d) (u : List BPair)
    (hu : u.length = (monomialsAt cc).length) :
    (poly.unitTail (elim.matVec (units.stackedRaise
        (List.zipWith (fun a b => a + b) (wedge d d).content cc))
        (rowW d cc u))
      ↔ poly.unitTail (elim.matVec (units.stackedRaise cc) u)) := by
  have hmul : (List.zipWith (fun a b => a + b)
      (wedge d d).content cc).length = d :=
    ground.length_zipWith (fun a b => a + b) (wedge d d).content cc
      d (wedge_clen d d) hcl
  have hstep : ∀ i, i + 1 < d →
      (poly.unitTail (elim.matVec (units.matUnitAt
          (units.moveUp i (List.zipWith (fun a b => a + b)
            (wedge d d).content cc))
          (List.zipWith (fun a b => a + b) (wedge d d).content cc)
          i (i + 1)) (rowW d cc u))
        ↔ poly.unitTail (elim.matVec (units.matUnitAt
          (units.moveUp i cc) cc i (i + 1)) u)) := by
    intro i hi
    have h := act_tensorW_unit d i hi ⟨cc, u⟩ hu hcl
    rw [show (act i (i + 1)
          (tensorH (wedge d d) (⟨cc, u⟩ : HVec))).coords
        = elim.matVec (units.matUnitAt
            (moveAt i (i + 1) (List.zipWith (fun a b => a + b)
              (wedge d d).content cc))
            (List.zipWith (fun a b => a + b) (wedge d d).content cc)
            i (i + 1)) (rowW d cc u) from rfl,
      show (act i (i + 1) (⟨cc, u⟩ : HVec)).coords
        = elim.matVec (units.matUnitAt (moveAt i (i + 1) cc) cc
            i (i + 1)) u from rfl,
      moveAt_moveUp i (List.zipWith (fun a b => a + b)
        (wedge d d).content cc),
      moveAt_moveUp i cc] at h
    exact h
  constructor
  · intro hL
    refine units.stackedRaise_of cc u ?_
    intro i hi _
    have hid : i + 1 < d := by
      rw [← hcl]
      exact hi
    refine (hstep i hid).mp (units.stackedRaise_to _ (rowW d cc u)
      hL i (by rw [hmul]; exact hid) ?_)
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b)
        (wedge d d).content cc (i + 1)
        (by rw [wedge_clen d d]; exact hid)
        (by rw [hcl]; exact hid),
      wedge_full_get d (i + 1) hid]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
  · intro hR
    refine units.stackedRaise_of _ (rowW d cc u) ?_
    intro i hi _
    have hid : i + 1 < d := by
      rw [hmul] at hi
      exact hi
    refine (hstep i hid).mpr ?_
    by_cases hocc : 0 < ground.getAt 0 cc (i + 1)
    · exact units.stackedRaise_to cc u hR i
        (by rw [hcl]; exact hid) hocc
    · exact units.matVec_null_unocc _ cc i (i + 1)
        (Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hocc)) u

/-- The mapped carrier's group at the shifted content is the
content's own group mapped: the shifted contents cancel the wedge's
own, so the two filters keep the same members. -/
private theorem groupAt_mapW (d : Nat) (cc : List Nat)
    (hcl : cc.length = d) :
    ∀ P : List HVec, (∀ x ∈ P, x.content.length = d) →
      groupAt (P.map (fun v => tensorH (wedge d d) v))
          (List.zipWith (fun a b => a + b) (wedge d d).content cc)
        = (groupAt P cc).map (rowW d cc)
  | [], _ => rfl
  | v :: t, hw => by
    have hvd : v.content.length = d := hw v (List.Mem.head t)
    have htl := groupAt_mapW d cc hcl t
      (fun x hx => hw x (List.Mem.tail v hx))
    show groupAt (tensorH (wedge d d) v
        :: t.map (fun v => tensorH (wedge d d) v))
        (List.zipWith (fun a b => a + b) (wedge d d).content cc)
      = (groupAt (v :: t) cc).map (rowW d cc)
    rw [groupAt_cons (tensorH (wedge d d) v)
        (t.map (fun v => tensorH (wedge d d) v))
        (List.zipWith (fun a b => a + b) (wedge d d).content cc),
      groupAt_cons v t cc]
    cases hb : (v.content == cc) with
    | true =>
      have hvc : v.content = cc := ground.listBeqEq hb
      have hct : (tensorH (wedge d d) v).content
          = List.zipWith (fun a b => a + b)
            (wedge d d).content cc := by
        rw [content_tensorH, hvc]
      rw [hct, ground.listEqBeq _]
      show (tensorH (wedge d d) v).coords
          :: groupAt (t.map (fun v => tensorH (wedge d d) v))
            (List.zipWith (fun a b => a + b) (wedge d d).content cc)
        = (v.coords :: groupAt t cc).map (rowW d cc)
      rw [htl]
      show (tensorH (wedge d d) v).coords :: _
        = (tensorH (wedge d d) (⟨cc, v.coords⟩ : HVec)).coords :: _
      rw [← hvc]
    | false =>
      have hne : ¬ v.content = cc := by
        intro he
        rw [he, ground.listEqBeq cc] at hb
        exact Bool.noConfusion hb
      have hbf : ((tensorH (wedge d d) v).content
          == List.zipWith (fun a b => a + b)
            (wedge d d).content cc) = false := by
        cases hb2 : ((tensorH (wedge d d) v).content
            == List.zipWith (fun a b => a + b)
              (wedge d d).content cc) with
        | false => rfl
        | true =>
          exact absurd (zipWith_add_cancelL (wedge d d).content
            v.content cc d (wedge_clen d d) hvd hcl
            (by rw [← content_tensorH]
                exact ground.listBeqEq hb2)) hne
      rw [hbf]
      exact htl

/-- The mapped carrier's count at the shifted content is the
carrier's own: the group at the shifted content is the content's
own group mapped, the mapped collection and the shifted content's
own sit in one span at the mapped list's linearity
(`elim.kernelDim_congr`), and the stacked raisings read across the
map at every coefficient family (`elim.kernelDim_kerIff` at the
stacked bridge).  The members' widths and the content's own are
load-bearing with their committed refusals; the letter count's
positivity is derivable and is not carried. -/
theorem countAt_lineShift (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (cc : List Nat) (hcl : cc.length = d) :
    countAt (P.map (fun v => tensorH (wedge d d) v))
        (List.zipWith (fun a b => a + b) (wedge d d).content cc)
      = countAt P cc := by
  have hG : elim.rowsLen (monomialsAt cc).length (groupAt P cc) :=
    rowsLen_groupAt cc P hsz
  have hC : elim.rowsLen (monomialsAt cc).length
      (elim.collectOf (monomialsAt cc).length (groupAt P cc)) :=
    elim.collect_rowsLen _ _ hG
  have hGW : elim.rowsLen (monomialsAt (List.zipWith
      (fun a b => a + b) (wedge d d).content cc)).length
      ((groupAt P cc).map (rowW d cc)) :=
    elim.rowsLen_map _ _ _ (fun x _ => rowW_len d cc x)
  have hCW : elim.rowsLen (monomialsAt (List.zipWith
      (fun a b => a + b) (wedge d d).content cc)).length
      ((elim.collectOf (monomialsAt cc).length
        (groupAt P cc)).map (rowW d cc)) :=
    elim.rowsLen_map _ _ _ (fun x _ => rowW_len d cc x)
  have hA : elim.rowsLen (monomialsAt (List.zipWith
      (fun a b => a + b) (wedge d d).content cc)).length
      (elim.collectOf (monomialsAt (List.zipWith
        (fun a b => a + b) (wedge d d).content cc)).length
        ((groupAt P cc).map (rowW d cc))) :=
    elim.collect_rowsLen _ _ hGW
  have hstep1 := elim.kernelDim_congr
    (monomialsAt (List.zipWith (fun a b => a + b)
      (wedge d d).content cc)).length
    (units.stackedRaise (List.zipWith (fun a b => a + b)
      (wedge d d).content cc))
    ((elim.collectOf (monomialsAt cc).length
      (groupAt P cc)).map (rowW d cc))
    (elim.collectOf (monomialsAt (List.zipWith
      (fun a b => a + b) (wedge d d).content cc)).length
      ((groupAt P cc).map (rowW d cc)))
    (units.rowsLen_stackedRaise _) hCW hA
    (rowW_indep d cc hcl _ hC (elim.collect_indep _ _ hG))
    (elim.collect_indep _ _ hGW)
    (fun k hk => by
      rw [ground.length_map (rowW d cc) _] at hk
      rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
        (rowW d cc) _ k hk]
      exact elim.spanRel_trans _ ((groupAt P cc).map (rowW d cc)) _
        _ hGW hA
        (fun j hj => elim.collect_span_row _ _ hGW j hj)
        (rowW_span d cc hcl (groupAt P cc) hG _
          (elim.rowsLen_getAt _ k hC hk)
          (elim.collect_row_span _ _ hG k hk)))
    (fun k hk => by
      refine elim.spanRel_trans _
        ((groupAt P cc).map (rowW d cc)) _ _ hGW hCW ?_
        (elim.collect_row_span _ _ hGW k hk)
      intro j hj
      rw [ground.length_map (rowW d cc) _] at hj
      rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
        (rowW d cc) _ j hj]
      exact rowW_span d cc hcl _ hC _
        (elim.rowsLen_getAt _ j hG hj)
        (elim.collect_span_row _ _ hG j hj))
  have hstep2 := elim.kernelDim_kerIff
    (units.stackedRaise (List.zipWith (fun a b => a + b)
      (wedge d d).content cc))
    ((elim.collectOf (monomialsAt cc).length
      (groupAt P cc)).map (rowW d cc))
    (units.stackedRaise cc)
    (elim.collectOf (monomialsAt cc).length (groupAt P cc))
    (ground.length_map (rowW d cc) _)
    (fun x _ => by
      constructor
      · intro h1
        refine poly.oneValue_unitTail
          (elim.matVec_crossM (monomialsAt cc).length
            (units.stackedRaise cc) _ x
            (units.rowsLen_stackedRaise cc) hC) ?_
        refine (stackW_unit d cc hcl _
          (elim.length_combo _ x _ hC)).mp ?_
        refine poly.unitTail_oneValue_right
          (poly.unitTail_oneValue_right h1
            (elim.matVec_crossM _ _ _ x
              (units.rowsLen_stackedRaise _) hCW)) ?_
        exact elim.matVec_congr _ _ _
          (rowW_combo d cc hcl x _ hC)
      · intro h1
        refine poly.oneValue_unitTail
          (elim.matVec_crossM _ _ _ x
            (units.rowsLen_stackedRaise _) hCW) ?_
        refine poly.oneValue_unitTail
          (elim.matVec_congr _ _ _ (rowW_combo d cc hcl x _ hC)) ?_
        refine (stackW_unit d cc hcl _
          (elim.length_combo _ x _ hC)).mpr ?_
        exact poly.unitTail_oneValue_right h1
          (elim.matVec_crossM (monomialsAt cc).length
            (units.stackedRaise cc) _ x
            (units.rowsLen_stackedRaise cc) hC))
  show elim.kernelDim
      (elim.collectOf (monomialsAt (List.zipWith
        (fun a b => a + b) (wedge d d).content cc)).length
        (groupAt (P.map (fun v => tensorH (wedge d d) v))
          (List.zipWith (fun a b => a + b)
            (wedge d d).content cc))).length
      (elim.crossM (units.stackedRaise (List.zipWith
          (fun a b => a + b) (wedge d d).content cc))
        (elim.collectOf (monomialsAt (List.zipWith
          (fun a b => a + b) (wedge d d).content cc)).length
          (groupAt (P.map (fun v => tensorH (wedge d d) v))
            (List.zipWith (fun a b => a + b)
              (wedge d d).content cc))))
    = elim.kernelDim
      (elim.collectOf (monomialsAt cc).length
        (groupAt P cc)).length
      (elim.crossM (units.stackedRaise cc)
        (elim.collectOf (monomialsAt cc).length (groupAt P cc)))
  rw [groupAt_mapW d cc hcl P hwid]
  exact hstep1.symm.trans hstep2

/-- The fusion count's descent at one full column
(`con:labels`' class-invariance clause,
`N^{c+(1^{d_f})}_{a+(1^{d_f}),b} = N^c_{ab}`): the count is the
fused pool's own at the target's row list
(`blockcount.fusionCount_countAt`), the bumped target's row list is
the wedge's content joined to the target's, the bumped first
shape's fused pool is the pool's own at the wedge tensored on
(`countAt_fusedLine`), and the mapped pool's count at the shifted
content is the pool's own (`countAt_lineShift`).  The second
shape's width is load-bearing with its committed refusal; the
target's width is the frame, `con:labels`' one letter count — at a
target off the width both counts read the vacant group's kernel,
the shifted and unshifted contents alike off every fused content's
width — and the letter count's positivity is derivable and is not
carried. -/
theorem fusionCount_addFull (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length) :
    fusionCount (ground.bumpAt (a.length - 1) a) b
        (ground.bumpAt (a.length - 1) c)
      = fusionCount a b c := by
  have hbl : (ground.bumpAt (a.length - 1) a).length = a.length :=
    ground.length_bumpAt _ a
  have hrc : places.rowList (ground.bumpAt (a.length - 1) c)
      = List.zipWith (fun x y => x + y)
        (wedge a.length a.length).content (places.rowList c) := by
    rw [← hca]
    exact rowList_addFull c
  have hszP : ∀ x ∈ fusedAt (blockSpan a) (blockSpan b),
      sized x := by
    intro x hx
    match ground.mem_flatMap_of _ _ x hx with
    | ⟨v, _, hxv⟩ =>
      match ground.mem_map_of (tensorH v) _ x hxv with
      | ⟨w, _, hwx⟩ =>
        rw [← hwx]
        exact tensorH_sized v w
  have hwidP : ∀ x ∈ fusedAt (blockSpan a) (blockSpan b),
      x.content.length = a.length := by
    intro x hx
    match ground.mem_flatMap_of _ _ x hx with
    | ⟨v, hv, hxv⟩ =>
      match ground.mem_map_of (tensorH v) _ x hxv with
      | ⟨w, hw, hwx⟩ =>
        rw [← hwx]
        exact ground.length_zipWith (fun x y => x + y) v.content
          w.content a.length (blockSpan_width a v hv)
          ((blockSpan_width b w hw).trans hba)
  rw [fusionCount_countAt (ground.bumpAt (a.length - 1) a) b
      (ground.bumpAt (a.length - 1) c) (hba.trans hbl.symm),
    fusionCount_countAt a b c hba, hrc,
    countAt_fusedLine a b hba _,
    countAt_lineShift a.length _ hszP hwidP (places.rowList c)
      ((places.length_rowList c).trans hca)]


/-! `lem:dualread`(iii)'s off-join arm at the value list: the first
block's stated members read one value each at the complement of
their own content, every value sized and settled inside the second
block's span, the list closed at every letter pair at distinct
letters, and at a coefficient family off the sum's unit a member's
value sits off the unit tail at the second block's row list, the
pair guard's join exact there — `b`'s row list joins an occupied
content of `W_a` to the full columns. -/

/-- The complement read of an exact join: at matched widths the
second summand is the fused content's memberwise difference against
the first. -/
private theorem compl_of_join (mu nu cc : List Nat) (d : Nat)
    (hmu : mu.length = d) (hnu : nu.length = d)
    (h : List.zipWith (fun x y => x + y) mu nu = cc) :
    List.zipWith (fun u w => u - w) cc mu = nu := by
  have hcc : cc.length = d := by
    rw [← h]
    exact ground.length_zipWith (fun x y => x + y) mu nu d hmu hnu
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_zipWith (fun u w => u - w) cc mu d hcc hmu, hnu]
  · intro i hi
    rw [ground.length_zipWith (fun u w => u - w) cc mu d hcc hmu] at hi
    rw [ground.getAt_zipWith 0 0 0 (fun u w => u - w) cc mu i
        (by rw [hcc]; exact hi) (by rw [hmu]; exact hi),
      ← h,
      ground.getAt_zipWith 0 0 0 (fun x y => x + y) mu nu i
        (by rw [hmu]; exact hi) (by rw [hnu]; exact hi)]
    exact ground.addSubSelfL _ _

/-- An exact join transports across a letter pair's moves: the
first content moved at the exchanged letters against the second
moved at the letters themselves joins the fused content back, the
two occupancies the moves' own. -/
private theorem join_move (mu nu cc : List Nat) (d i j : Nat)
    (hmu : mu.length = d) (hnu : nu.length = d)
    (hi : i < d) (hj : j < d) (hij : ¬ i = j)
    (hmi : 0 < ground.getAt 0 mu i)
    (hnj : 0 < ground.getAt 0 nu j)
    (h : List.zipWith (fun x y => x + y) mu nu = cc) :
    List.zipWith (fun x y => x + y) (moveAt j i mu) (moveAt i j nu)
      = cc := by
  have hcci : 0 < ground.getAt 0 cc i := by
    rw [← h, ground.getAt_zipWith 0 0 0 (fun x y => x + y) mu nu i
      (by rw [hmu]; exact hi) (by rw [hnu]; exact hi)]
    exact Nat.lt_of_lt_of_le hmi (Nat.le_add_right _ _)
  have hccj : 0 < ground.getAt 0 cc j := by
    rw [← h, ground.getAt_zipWith 0 0 0 (fun x y => x + y) mu nu j
      (by rw [hmu]; exact hj) (by rw [hnu]; exact hj)]
    exact Nat.lt_of_lt_of_le hnj (Nat.le_add_left _ _)
  show List.zipWith (fun x y => x + y)
      (ground.bumpAt j (ground.dipAt i mu))
      (ground.bumpAt i (ground.dipAt j nu)) = cc
  rw [ground.bumpAt_zipWith_left j (ground.dipAt i mu)
      (ground.bumpAt i (ground.dipAt j nu)),
    ground.bumpAt_zipWith_right i (ground.dipAt i mu)
      (ground.dipAt j nu),
    ground.dipAt_zipWith_left i mu (ground.dipAt j nu) hmi,
    ground.dipAt_zipWith_right j mu nu hnj, h,
    ground.bumpAt_dipAt_self i (ground.dipAt j cc)
      (by rw [ground.getAt_dipAt_ne j cc i hij]; exact hcci),
    ground.bumpAt_dipAt_self j cc hccj]

/-- The value list at the first block's stated members, one value
per member at the complement of its content
(`lem:dualread`(iii)). -/
def valList (A B : List HVec) (cc : List Nat) (c : List BPair) :
    List HVec :=
  A.map (fun y => pairVal (pairFam A B cc c) y
    (List.zipWith (fun u w => u - w) cc y.content))

/-- The value's content is the stated output content. -/
private theorem pairVal_content (P : List (BPair × HVec × HVec))
    (x : HVec) (oc : List Nat) : (pairVal P x oc).content = oc := rfl

/-- The family's slots at a stated first content: the second slot
sits in the second list at the content's complement, the guard's
join read back. -/
private theorem pairFam_slot_at (A B : List HVec) (cc : List Nat)
    (c : List BPair) (d : Nat)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ w ∈ B, w.content.length = d)
    (y : HVec) (t : BPair × HVec × HVec)
    (ht : t ∈ (pairFam A B cc c).filter
      (fun s => s.2.1.content == y.content)) :
    t.2.2 ∈ B
      ∧ t.2.2.content = List.zipWith (fun u w => u - w) cc y.content := by
  match ground.mem_filter_of _ (pairFam A B cc c) t ht with
  | ⟨htF, htb⟩ =>
    match pairFam_slots A B cc c t htF with
    | ⟨htA, htB, htj⟩ =>
      have hyc : t.2.1.content = y.content := ground.listBeqEq htb
      refine ⟨htB, ?_⟩
      rw [← hyc]
      exact (compl_of_join t.2.1.content t.2.2.content cc d
        (hwA _ htA) (hwB _ htB) htj).symm

/-- The value's rows at a stated member: the second slots' families
at the complement content's own width. -/
private theorem valRows (A B : List HVec) (cc : List Nat)
    (c : List BPair) (d : Nat)
    (hwA : ∀ v ∈ A, v.content.length = d)
    (hwB : ∀ w ∈ B, w.content.length = d)
    (hszB : ∀ w ∈ B, sized w) (y : HVec) :
    elim.rowsLen (places.monomialsAt
        (List.zipWith (fun u w => u - w) cc y.content)).length
      (((pairFam A B cc c).filter
        (fun s => s.2.1.content == y.content)).map
        (fun t => t.2.2.coords)) := by
  refine elim.rowsLen_map _ _ _ (fun t ht => ?_)
  match pairFam_slot_at A B cc c d hwA hwB y t ht with
  | ⟨htB, htc⟩ =>
    rw [← htc]
    exact hszB _ htB

/-- Every value is sized and settled inside the second block's
span: the value's rows are the second block's members at the
complement content, so the combination sits in that content's
group's span — `lem:dualread`(iii)'s value list at the first
block's stated members. -/
theorem valList_settled (a b : Shape) (m : Nat) (c : List BPair)
    (hba : b.length = a.length) :
    ∀ x ∈ valList (blockSpan a) (blockSpan b)
        (List.replicate a.length m) c,
      sized x ∧ settledAt (blockSpan b) x := by
  have hwA : ∀ v ∈ blockSpan a, v.content.length = a.length :=
    blockSpan_width a
  have hwB : ∀ w ∈ blockSpan b, w.content.length = a.length :=
    fun w hw => (blockSpan_width b w hw).trans hba
  intro x hx
  match ground.mem_map_of _ (blockSpan a) x hx with
  | ⟨y, hyA, hxy⟩ =>
    have hrows := valRows (blockSpan a) (blockSpan b)
      (List.replicate a.length m) c a.length hwA hwB
      (lowerspan.spanReads b).1 y
    have hgrows : elim.rowsLen (places.monomialsAt
          (List.zipWith (fun u w => u - w)
            (List.replicate a.length m) y.content)).length
        (groupAt (blockSpan b)
          (List.zipWith (fun u w => u - w)
            (List.replicate a.length m) y.content)) :=
      rowsLen_groupAt _ (blockSpan b) (lowerspan.spanReads b).1
    rw [← hxy]
    refine ⟨?_, Or.inr ?_⟩
    · show (pairVal (pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c) y
          (List.zipWith (fun u w => u - w)
            (List.replicate a.length m) y.content)).coords.length
        = (places.monomialsAt
            (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content)).length
      rw [pairVal_coords]
      exact elim.length_combo _ _ _ hrows
    · rw [pairVal_content, pairVal_coords,
        elim.length_combo _ _ _ hrows]
      refine elim.spanRel_combo _ _ hgrows _ _ hrows (fun k hk => ?_)
      rw [ground.length_map] at hk
      have hmem := ground.mem_getAt
        ((BPair.unit, (⟨[], []⟩ : HVec), (⟨[], []⟩ : HVec)))
        ((pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c).filter
          (fun s => s.2.1.content == y.content)) k hk
      match pairFam_slot_at (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c a.length hwA hwB y _ hmem with
      | ⟨htB, htc⟩ =>
        rw [ground.getAt_map
          ((BPair.unit, (⟨[], []⟩ : HVec), (⟨[], []⟩ : HVec)))
          ([] : List BPair) (fun t => t.2.2.coords)
          ((pairFam (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c).filter
            (fun s => s.2.1.content == y.content)) k hk]
        refine span_of_mem _ _ _ ?_ hgrows
        refine ground.mem_filter_to _ htB ?_
        rw [htc]
        exact ground.listEqBeq _

/-- The value's width at a member of the stated content: the
combination's own at the output content's enumeration. -/
private theorem pairVal_len (P : List (BPair × HVec × HVec))
    (oc mu : List Nat) (x : HVec) (hx : x.content = mu)
    (hrows : elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords))) :
    (pairVal P x oc).coords.length = (places.monomialsAt oc).length := by
  rw [pairVal_coords P x oc, hx]
  exact elim.length_combo _ _ _ hrows

/-- The value's entry at a place: the weighted pairings against the
second slots' column reads. -/
private theorem pairVal_entry (P : List (BPair × HVec × HVec))
    (oc mu : List Nat) (x : HVec) (hx : x.content = mu)
    (hrows : elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords)))
    (r : Nat) (hr : r < (places.monomialsAt oc).length) :
    (ground.getAt BPair.unit (pairVal P x oc).coords r).oneValue
      (elim.dotP
        ((P.filter (fun t => t.2.1.content == mu)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
        (((P.filter (fun t => t.2.1.content == mu)).map
          (fun t => t.2.2.coords)).map
          (fun row => ground.getAt BPair.unit row r))) := by
  rw [pairVal_coords P x oc, hx]
  exact elim.combo_getAt _ _ _ r hrows hr

/-- The value reads one value in its argument at the shared
content, the weights reading the moved pairing per slot. -/
private theorem pairVal_argCongr (P : List (BPair × HVec × HVec))
    (oc mu : List Nat) (x z : HVec) (hx : x.content = mu)
    (hz : z.content = mu) (h : poly.oneValue x.coords z.coords)
    (hrows : elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords))) :
    poly.oneValue (pairVal P x oc).coords (pairVal P z oc).coords := by
  refine poly.oneValue_of_entries _ _ ?_ (fun r hr => ?_)
  · rw [pairVal_len P oc mu x hx hrows, pairVal_len P oc mu z hz hrows]
  · rw [pairVal_len P oc mu x hx hrows] at hr
    refine BPair.oneValue_trans
      (pairVal_entry P oc mu x hx hrows r hr) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _
        (poly.oneValue_map _ _ _ (fun t _ =>
          BPair.mul_congr (BPair.oneValue_refl t.1)
            (elim.dotP_oneValue_right t.2.1.coords x.coords
              z.coords h)))) ?_
    exact BPair.oneValue_symm (pairVal_entry P oc mu z hz hrows r hr)

/-- The value scales in its argument, the clearing crossing the
weights and the fold. -/
private theorem pairVal_argScale (P : List (BPair × HVec × HVec))
    (oc mu : List Nat) (c : BPair) (u : List BPair)
    (hrows : elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords))) :
    poly.oneValue
      (pairVal P ⟨mu, elim.vecScale c u⟩ oc).coords
      (elim.vecScale c (pairVal P ⟨mu, u⟩ oc).coords) := by
  have hlu : (pairVal P (⟨mu, u⟩ : HVec) oc).coords.length
      = (places.monomialsAt oc).length :=
    pairVal_len P oc mu ⟨mu, u⟩ rfl hrows
  have hls : (pairVal P (⟨mu, elim.vecScale c u⟩ : HVec) oc).coords.length
      = (places.monomialsAt oc).length :=
    pairVal_len P oc mu ⟨mu, elim.vecScale c u⟩ rfl hrows
  refine poly.oneValue_of_entries _ _ ?_ (fun r hr => ?_)
  · rw [hls, elim.length_vecScale, hlu]
  · rw [hls] at hr
    rw [elim.getAt_vecScale c _ r (by rw [hlu]; exact hr)]
    refine BPair.oneValue_trans
      (pairVal_entry P oc mu ⟨mu, elim.vecScale c u⟩ rfl hrows r hr) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _
        (poly.oneValue_map _ _ _ (fun t _ =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (elim.dotP_vecScale_right t.2.1.coords u c))
            (BPair.oneValue_of_eq (BPair.mul_left_comm t.1 c _))))) ?_
    rw [← vecScale_map c
      (fun t => t.1 * elim.dotP t.2.1.coords u)
      (P.filter (fun t => t.2.1.content == mu))]
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (elim.dotP_comm _ _)) ?_
    refine BPair.oneValue_trans (elim.dotP_vecScale_right _ _ c) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c)
        (BPair.oneValue_of_eq (elim.dotP_comm _ _))) ?_
    exact BPair.mul_congr (BPair.oneValue_refl c)
      (BPair.oneValue_symm
        (pairVal_entry P oc mu ⟨mu, u⟩ rfl hrows r hr))

/-- The value is additive in its argument at the arguments' shared
order, both sides splitting entry by entry. -/
private theorem pairVal_argAdd (P : List (BPair × HVec × HVec))
    (oc mu : List Nat) (u w : List BPair) (huw : u.length = w.length)
    (hrows : elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords))) :
    poly.oneValue
      (pairVal P ⟨mu, elim.vecAdd u w⟩ oc).coords
      (elim.vecAdd (pairVal P ⟨mu, u⟩ oc).coords
        (pairVal P ⟨mu, w⟩ oc).coords) := by
  have hlu : (pairVal P (⟨mu, u⟩ : HVec) oc).coords.length
      = (places.monomialsAt oc).length :=
    pairVal_len P oc mu ⟨mu, u⟩ rfl hrows
  have hlw : (pairVal P (⟨mu, w⟩ : HVec) oc).coords.length
      = (places.monomialsAt oc).length :=
    pairVal_len P oc mu ⟨mu, w⟩ rfl hrows
  have hla : (pairVal P (⟨mu, elim.vecAdd u w⟩ : HVec) oc).coords.length
      = (places.monomialsAt oc).length :=
    pairVal_len P oc mu ⟨mu, elim.vecAdd u w⟩ rfl hrows
  refine poly.oneValue_of_entries _ _ ?_ (fun r hr => ?_)
  · rw [hla, elim.length_vecAdd _ _ (places.monomialsAt oc).length
      hlu hlw]
  · rw [hla] at hr
    rw [elim.getAt_vecAdd _ _ r (by rw [hlu]; exact hr)
      (by rw [hlw]; exact hr)]
    refine BPair.oneValue_trans
      (pairVal_entry P oc mu ⟨mu, elim.vecAdd u w⟩ rfl hrows r hr) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _
        (poly.oneValue_map _ _ _ (fun t _ =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (elim.dotP_vecAdd_right t.2.1.coords u w huw))
            (BPair.oneValue_of_eq (BPair.left_distrib t.1 _ _))))) ?_
    rw [show (P.filter (fun t => t.2.1.content == mu)).map
          (fun t => t.1 * elim.dotP t.2.1.coords u
            + t.1 * elim.dotP t.2.1.coords w)
        = elim.vecAdd
          ((P.filter (fun t => t.2.1.content == mu)).map
            (fun t => t.1 * elim.dotP t.2.1.coords u))
          ((P.filter (fun t => t.2.1.content == mu)).map
            (fun t => t.1 * elim.dotP t.2.1.coords w)) from
      (elim.mapAdd _ _ _).symm]
    refine BPair.oneValue_trans
      (elim.dotP_vecAdd_left _ _ _
        (Nat.le_of_eq (by
          rw [ground.length_map, ground.length_map,
            ground.length_map]))
        (Nat.le_of_eq (by
          rw [ground.length_map, ground.length_map,
            ground.length_map]))) ?_
    exact BPair.add_congr
      (BPair.oneValue_symm
        (pairVal_entry P oc mu ⟨mu, u⟩ rfl hrows r hr))
      (BPair.oneValue_symm
        (pairVal_entry P oc mu ⟨mu, w⟩ rfl hrows r hr))

/-- The value at a combination of listed members, the peel one
member at a time: the head at the member's own value scaled, the
tail at the recursion, the join at the additivity — the moved
argument's combination reading through the fold. -/
private theorem pairVal_argCombo (P : List (BPair × HVec × HVec))
    (oc mu : List Nat) (n : Nat)
    (hrows : elim.rowsLen (places.monomialsAt oc).length
      ((P.filter (fun t => t.2.1.content == mu)).map
        (fun t => t.2.2.coords))) :
    ∀ (cs : List BPair) (G : List HVec),
      (∀ g ∈ G, g.content = mu ∧ g.coords.length = n) →
      poly.oneValue
        (pairVal P ⟨mu, elim.combo n cs (G.map HVec.coords)⟩ oc).coords
        (elim.combo (places.monomialsAt oc).length cs
          (G.map (fun g => (pairVal P g oc).coords)))
  | [], G, _ =>
    poly.unitTail_oneValue
      (pairVal_null P ⟨mu, elim.combo n [] (G.map HVec.coords)⟩ oc
        (fun t _ _ =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (elim.dotP_null_tail_right t.2.1.coords _
                (poly.unitTail_replicate n)))
            (BPair.mul_unit t.1)))
      (poly.unitTail_replicate (places.monomialsAt oc).length)
  | _ :: _, [], _ =>
    poly.unitTail_oneValue
      (pairVal_null P ⟨mu, elim.combo n _
        (([] : List HVec).map HVec.coords)⟩ oc
        (fun t _ _ =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (elim.dotP_null_tail_right t.2.1.coords _
                (poly.unitTail_replicate n)))
            (BPair.mul_unit t.1)))
      (poly.unitTail_replicate (places.monomialsAt oc).length)
  | c :: cs, g :: G', hG => by
    have hgc : g.content = mu := (hG g (List.Mem.head G')).1
    have hgn : g.coords.length = n := (hG g (List.Mem.head G')).2
    have hgv : (⟨mu, g.coords⟩ : HVec) = g := by rw [← hgc]
    have hrowsG : elim.rowsLen n (G'.map HVec.coords) :=
      elim.rowsLen_map _ _ _
        (fun g' hg' => (hG g' (List.Mem.tail _ hg')).2)
    have hlg : (pairVal P g oc).coords.length
        = (places.monomialsAt oc).length :=
      pairVal_len P oc mu g hgc hrows
    have hrowsV : elim.rowsLen (places.monomialsAt oc).length
        (G'.map (fun g => (pairVal P g oc).coords)) :=
      elim.rowsLen_map _ _ _ (fun g' hg' =>
        pairVal_len P oc mu g' (hG g' (List.Mem.tail _ hg')).1 hrows)
    show poly.oneValue
      (pairVal P ⟨mu, elim.combo n (c :: cs)
        (g.coords :: G'.map HVec.coords)⟩ oc).coords
      (elim.combo (places.monomialsAt oc).length (c :: cs)
        ((pairVal P g oc).coords
          :: G'.map (fun g => (pairVal P g oc).coords)))
    rw [combo_cons n c cs g.coords (G'.map HVec.coords),
      combo_cons (places.monomialsAt oc).length c cs
        (pairVal P g oc).coords
        (G'.map (fun g => (pairVal P g oc).coords))]
    refine poly.oneValue_trans
      (pairVal_argAdd P oc mu (elim.vecScale c g.coords)
        (elim.combo n cs (G'.map HVec.coords))
        (by rw [elim.length_vecScale, hgn,
          elim.length_combo _ _ _ hrowsG]) hrows) ?_
    refine elim.polyOne_vecAdd _ _ _ _ ?_ ?_ ?_ ?_
    · refine poly.oneValue_trans
        (pairVal_argScale P oc mu c g.coords hrows) ?_
      rw [hgv]
      exact poly.oneValue_refl _
    · exact pairVal_argCombo P oc mu n hrows cs G'
        (fun g' hg' => hG g' (List.Mem.tail _ hg'))
    · rw [pairVal_len P oc mu ⟨mu, elim.vecScale c g.coords⟩ rfl hrows,
        elim.length_vecScale, hlg]
    · rw [pairVal_len P oc mu ⟨mu, elim.combo n cs (G'.map HVec.coords)⟩
        rfl hrows,
        elim.length_combo _ _ _ hrowsV]

/-- The action's content is the letter pair's move on the
argument's. -/
private theorem act_content (i j : Nat) (v : HVec) :
    (act i j v).content = moveAt i j v.content := rfl

/-- The action's coordinates are the move's matrix against the
argument's. -/
private theorem act_coords (i j : Nat) (v : HVec) :
    (act i j v).coords
      = elim.matVec (units.matUnitAt (moveAt i j v.content)
        v.content i j) v.coords := rfl

/-- The dual action's content is the exchanged letters' move. -/
private theorem dact_content (i j : Nat) (v : HVec) :
    (dact i j v).content = moveAt j i v.content := rfl

/-- A value off the unit tail names a slot at the argument's
content: at a vacant filter the combination is the unit family. -/
private theorem pairVal_slot (P : List (BPair × HVec × HVec))
    (z : HVec) (oc : List Nat)
    (h : ¬ poly.unitTail (pairVal P z oc).coords) :
    ∃ t ∈ P, t.2.1.content = z.content := by
  match hf : P.filter (fun t => t.2.1.content == z.content) with
  | [] =>
    refine absurd ?_ h
    rw [pairVal_coords P z oc, hf]
    exact poly.unitTail_replicate _
  | t :: rest =>
    have ht : t ∈ P.filter (fun s => s.2.1.content == z.content) := by
      rw [hf]
      exact List.Mem.head rest
    match ground.mem_filter_of _ P t ht with
    | ⟨htP, htb⟩ => exact ⟨t, htP, ground.listBeqEq htb⟩

/-- The acted value's width: the moved output content's own
enumeration. -/
private theorem act_pairVal_len (P : List (BPair × HVec × HVec))
    (i j : Nat) (z : HVec) (oc : List Nat) :
    (act i j (pairVal P z oc)).coords.length
      = (places.monomialsAt (moveAt i j oc)).length := by
  have hs : (act i j (pairVal P z oc)).coords.length
      = (places.monomialsAt
        (act i j (pairVal P z oc)).content).length :=
    act_sized i j (pairVal P z oc)
  rw [act_content, pairVal_content] at hs
  exact hs

/-- The value at a stated member of the first list joins the value
list at the complement content, the member's own image there. -/
private theorem valList_row (A B : List HVec) (cc : List Nat)
    (c : List BPair) (oc : List Nat) (g : HVec) (hgA : g ∈ A)
    (hgc : List.zipWith (fun u w => u - w) cc g.content = oc) :
    pairVal (pairFam A B cc c) g oc ∈ valList A B cc c := by
  rw [← hgc]
  exact ground.mem_map_to _ hgA

/-- A first-list member at the moved content contributes a value
list row at the moved complement: the member's value sits in the
value list's group there. -/
private theorem valList_group_row (A B : List HVec) (cc : List Nat)
    (c : List BPair) (mu oc : List Nat)
    (hcompl : List.zipWith (fun u w => u - w) cc mu = oc)
    (hMrows : elim.rowsLen (places.monomialsAt oc).length
      (groupAt (valList A B cc c) oc))
    (g : HVec) (hg : g ∈ A.filter (fun w => w.content == mu)) :
    elim.spanRel (places.monomialsAt oc).length
      (groupAt (valList A B cc c) oc)
      (pairVal (pairFam A B cc c) g oc).coords := by
  match ground.mem_filter_of _ A g hg with
  | ⟨hgA, hgb⟩ =>
    have hgc : List.zipWith (fun u w => u - w) cc g.content = oc := by
      rw [ground.listBeqEq hgb]
      exact hcompl
    refine span_of_mem _ oc _ (ground.mem_filter_to _ ?_ ?_) hMrows
    · exact valList_row A B cc c oc g hgA hgc
    · rw [pairVal_content]
      exact ground.listEqBeq _

/-- The value list is closed at the letters inside the second
block's span: a letter's image of a value is the value at the
argument's dual move, the moved argument's combination reading
through the fold, so the image sits in the value list's own span at
the moved content — `lem:dualread`(iii)'s closure sentence. -/
theorem valList_closed (a b : Shape) (m : Nat) (c : List BPair)
    (hba : b.length = a.length)
    (hc : c.length
      = (pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).length)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) c)) :
    ∀ x ∈ valList (blockSpan a) (blockSpan b)
        (List.replicate a.length m) c,
      ∀ i < a.length, ∀ j < a.length, ¬ i = j →
        settledAt (valList (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c) (act i j x) := by
  have hwA : ∀ v ∈ blockSpan a, v.content.length = a.length :=
    blockSpan_width a
  have hwB : ∀ w ∈ blockSpan b, w.content.length = a.length :=
    fun w hw => (blockSpan_width b w hw).trans hba
  have hszA := (lowerspan.spanReads a).1
  have hszB := (lowerspan.spanReads b).1
  have hccl : (List.replicate a.length m).length = a.length :=
    ground.length_replicate m a.length
  intro x hx i hi j hj hij
  match ground.mem_map_of _ (blockSpan a) x hx with
  | ⟨y, hyA, hxy⟩ =>
    rw [← hxy]
    have hwy : y.content.length = a.length := hwA y hyA
    have hocl : (List.zipWith (fun u w => u - w)
        (List.replicate a.length m) y.content).length = a.length :=
      ground.length_zipWith (fun u w => u - w) _ _ a.length hccl hwy
    have hrows := valRows (blockSpan a) (blockSpan b)
      (List.replicate a.length m) c a.length hwA hwB hszB y
    by_cases hV : poly.unitTail
        (act i j (pairVal (pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c) y
          (List.zipWith (fun u w => u - w)
            (List.replicate a.length m) y.content))).coords
    · exact Or.inl (allU_of_unitTail _ hV)
    · have hxoff : ¬ poly.unitTail
          (pairVal (pairFam (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c) y
            (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content)).coords := by
        intro hu
        refine hV ?_
        rw [act_coords]
        exact elim.matVec_null _ _ hu
      have hjoin : List.zipWith (fun x y => x + y) y.content
          (List.zipWith (fun u w => u - w)
            (List.replicate a.length m) y.content)
          = List.replicate a.length m := by
        match pairVal_slot _ y _ hxoff with
        | ⟨t, htF, htc⟩ =>
          have htf : t ∈ (pairFam (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c).filter
              (fun s => s.2.1.content == y.content) :=
            ground.mem_filter_to _ htF (by
              rw [htc]
              exact ground.listEqBeq _)
          match pairFam_slot_at (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c a.length hwA hwB y t htf,
            pairFam_slots (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c t htF with
          | ⟨_, htcc⟩, ⟨_, _, htj⟩ =>
            rw [← htcc, ← htc]
            exact htj
      have hequiv : poly.oneValue
          (pairVal (pairFam (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c) (dact i j y)
            (moveAt i j (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content))).coords
          (act i j (pairVal (pairFam (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c) y
            (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content))).coords := by
        match Nat.lt_or_ge i j with
        | .inl hlt =>
          exact pairVal_equiv (blockSpan a) (blockSpan b)
            (List.replicate a.length m) a.length (degree a) c
            hszA hszB hwA hwB (blockSpan_degree a) hccl hc hker
            i j hj hlt y (hszA y hyA) hwy _ hocl hjoin
        | .inr hge =>
          exact pairVal_equiv_lower (blockSpan a) (blockSpan b)
            (List.replicate a.length m) a.length (degree a) m c
            hszA hszB hwA hwB (blockSpan_degree a) hccl rfl hc hker
            j i hi (Nat.lt_of_le_of_ne hge (fun he => hij he.symm))
            y (hszA y hyA) hwy _ hocl hjoin
      by_cases hW : poly.unitTail
          (pairVal (pairFam (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c) (dact i j y)
            (moveAt i j (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content))).coords
      · exact Or.inl (allU_of_unitTail _
          (poly.unitTail_oneValue_right hW hequiv))
      · have hzoff : ¬ poly.unitTail (dact i j y).coords := by
          intro hu
          refine hW (pairVal_null _ (dact i j y) _ (fun t _ _ => ?_))
          exact BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl t.1)
              (elim.dotP_null_tail_right t.2.1.coords _ hu))
            (BPair.mul_unit t.1)
        have hyi : 0 < ground.getAt 0 y.content i := by
          by_cases h0 : 0 < ground.getAt 0 y.content i
          · exact h0
          · refine absurd ?_ hzoff
            exact poly.unitTail_swapMap _
              (units.matVec_null_unocc _ y.content j i
                (Nat.le_antisymm (Nat.ge_of_not_lt h0)
                  (Nat.zero_le _)) y.coords)
        have hocj : 0 < ground.getAt 0
            (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content) j := by
          by_cases h0 : 0 < ground.getAt 0
              (List.zipWith (fun u w => u - w)
                (List.replicate a.length m) y.content) j
          · exact h0
          · refine absurd ?_ hV
            rw [act_coords, pairVal_content]
            exact units.matVec_null_unocc _ _ i j
              (Nat.le_antisymm (Nat.ge_of_not_lt h0)
                (Nat.zero_le _)) _
        have hcompl : List.zipWith (fun u w => u - w)
            (List.replicate a.length m) (dact i j y).content
            = moveAt i j (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content) := by
          rw [dact_content]
          exact compl_of_join (moveAt j i y.content)
            (moveAt i j (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content))
            (List.replicate a.length m) a.length
            (by rw [length_moveAt]; exact hwy)
            (by rw [length_moveAt]; exact hocl)
            (join_move y.content (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content)
              (List.replicate a.length m) a.length i j hwy hocl
              hi hj hij hyi hocj hjoin)
        have hrows' := valRows (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c a.length hwA hwB hszB
          (dact i j y)
        rw [hcompl] at hrows'
        have hG : ∀ g ∈ (blockSpan a).filter
            (fun w => w.content == (dact i j y).content),
            g.content = (dact i j y).content
              ∧ g.coords.length = (dact i j y).coords.length := by
          intro g hg
          match ground.mem_filter_of _ (blockSpan a) g hg with
          | ⟨hgA, hgb⟩ =>
            have hgc : g.content = (dact i j y).content :=
              ground.listBeqEq hgb
            refine ⟨hgc, ?_⟩
            rw [hszA g hgA, hgc]
            exact (dact_sized i j y).symm
        have hspan : elim.spanRel (dact i j y).coords.length
            (groupAt (blockSpan a) (dact i j y).content)
            (dact i j y).coords :=
          match dact_closed a hszA (lowerspan.spanReads a).2.2
              i j hi hj hij y hyA with
          | .inl hall => absurd (unitTail_of_allU _ hall) hzoff
          | .inr hsp => hsp
        match elim.span_elim hspan with
        | ⟨c₀, cs, hc₀, _, hone⟩ =>
          have hstep : poly.oneValue
              (elim.vecScale c₀
                (pairVal (pairFam (blockSpan a) (blockSpan b)
                  (List.replicate a.length m) c) (dact i j y)
                  (moveAt i j (List.zipWith (fun u w => u - w)
                    (List.replicate a.length m) y.content))).coords)
              (elim.combo (places.monomialsAt
                  (moveAt i j (List.zipWith (fun u w => u - w)
                    (List.replicate a.length m) y.content))).length cs
                (((blockSpan a).filter
                  (fun w => w.content == (dact i j y).content)).map
                  (fun g => (pairVal (pairFam (blockSpan a)
                    (blockSpan b) (List.replicate a.length m) c) g
                    (moveAt i j (List.zipWith (fun u w => u - w)
                      (List.replicate a.length m)
                      y.content))).coords))) := by
            refine poly.oneValue_trans (poly.oneValue_symm
              (pairVal_argScale _ _ (dact i j y).content c₀
                (dact i j y).coords hrows')) ?_
            refine poly.oneValue_trans
              (pairVal_argCongr _ _ (dact i j y).content
                ⟨(dact i j y).content,
                  elim.vecScale c₀ (dact i j y).coords⟩
                ⟨(dact i j y).content,
                  elim.combo (dact i j y).coords.length cs
                    (groupAt (blockSpan a)
                      (dact i j y).content)⟩ rfl rfl hone hrows') ?_
            exact pairVal_argCombo _ _ (dact i j y).content
              (dact i j y).coords.length hrows' cs _ hG
          have hMrows : elim.rowsLen (places.monomialsAt
                (moveAt i j (List.zipWith (fun u w => u - w)
                  (List.replicate a.length m) y.content))).length
              (groupAt (valList (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c)
                (moveAt i j (List.zipWith (fun u w => u - w)
                  (List.replicate a.length m) y.content))) :=
            rowsLen_groupAt _ _ (fun z hz =>
              (valList_settled a b m c hba z hz).1)
          have hKrows : elim.rowsLen (places.monomialsAt
                (moveAt i j (List.zipWith (fun u w => u - w)
                  (List.replicate a.length m) y.content))).length
              ((((blockSpan a).filter
                (fun w => w.content == (dact i j y).content)).map
                (fun g => (pairVal (pairFam (blockSpan a)
                  (blockSpan b) (List.replicate a.length m) c) g
                  (moveAt i j (List.zipWith (fun u w => u - w)
                    (List.replicate a.length m)
                    y.content))).coords))) :=
            elim.rowsLen_map _ _ _ (fun g hg =>
              pairVal_len _ _ (dact i j y).content g (hG g hg).1 hrows')
          have hcombospan := elim.spanRel_combo _ _ hMrows _ cs hKrows
            (fun k hk => by
              rw [ground.length_map] at hk
              rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
                (fun g => (pairVal (pairFam (blockSpan a) (blockSpan b)
                  (List.replicate a.length m) c) g
                  (moveAt i j (List.zipWith (fun u w => u - w)
                    (List.replicate a.length m) y.content))).coords)
                _ k hk]
              exact valList_group_row (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c (dact i j y).content
                (moveAt i j (List.zipWith (fun u w => u - w)
                  (List.replicate a.length m) y.content))
                hcompl hMrows _
                (ground.mem_getAt (⟨[], []⟩ : HVec) _ k hk))
          have hVlen := act_pairVal_len (pairFam (blockSpan a)
            (blockSpan b) (List.replicate a.length m) c) i j y
            (List.zipWith (fun u w => u - w)
              (List.replicate a.length m) y.content)
          refine Or.inr ?_
          rw [act_content, pairVal_content, hVlen]
          refine elim.spanRel_unscale _ _ c₀ _ hc₀ ?_
          refine elim.spanRel_congr _ _ _ _ ?_ hcombospan ?_
          · exact poly.oneValue_trans (poly.oneValue_symm hstep)
              (elim.vecScale_oneValue c₀ _ _ hequiv)
          · rw [elim.length_vecScale]
            exact hVlen

/-- At a coefficient family off the sum's unit the value list holds
a value off the unit tail at the second block's row list, and the
member carrying it joins that row list to the full columns: the
solve-back names a member whose value sits off the unit tail, so
every second-block member joins the value list's span
(`lem:blockirr`(i)), the head among them, and the head's group in
the value list holds a value off the sum's unit — a combination of
unit tails reads the unit tail — with the pair guard's join exact
at the slot the value names — `lem:dualread`(iii)'s off-join
arm. -/
theorem valOff_head (a b : Shape) (m : Nat) (c : List BPair)
    (hba : b.length = a.length)
    (hc : c.length
      = (pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).length)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) c))
    (hoff : ¬ poly.unitTail c) :
    ∃ y ∈ blockSpan a,
      List.zipWith (fun u w => u + w) y.content (rowList b)
          = List.replicate a.length m
        ∧ ¬ poly.unitTail
          (pairVal (pairFam (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c) y (rowList b)).coords := by
  have hwA : ∀ v ∈ blockSpan a, v.content.length = a.length :=
    blockSpan_width a
  have hwB : ∀ w ∈ blockSpan b, w.content.length = a.length :=
    fun w hw => (blockSpan_width b w hw).trans hba
  have hszB := (lowerspan.spanReads b).1
  have hccl : (List.replicate a.length m).length = a.length :=
    ground.length_replicate m a.length
  by_cases hEx : ∃ y ∈ blockSpan a, ¬ poly.unitTail
      (pairVal (pairFam (blockSpan a) (blockSpan b)
        (List.replicate a.length m) c) y
        (List.zipWith (fun u w => u - w)
          (List.replicate a.length m) y.content)).coords
  · match hEx with
    | ⟨y0, hy0A, hy0off⟩ =>
      match blockSpan_prov b with
      | ⟨tail, hBeq, hprov⟩ =>
        have hmemB : ∀ w, w ∈ exhibit b :: tail → w ∈ blockSpan b :=
          fun w hw => by rw [hBeq]; exact hw
        have hirr := blockirr.irred a.length (exhibit b) tail
          (valList (blockSpan a) (blockSpan b)
            (List.replicate a.length m) c)
          (fun w hw => hszB w (hmemB w hw))
          (fun w hw => hwB w (hmemB w hw))
          (fun k hk =>
            match hprov k hk with
            | ⟨p, hpk, q, hqb, hl⟩ =>
              ⟨p, hpk, q, by rw [← hba]; exact hqb, hl⟩)
          (fun z hz => (valList_settled a b m c hba z hz).1)
          (fun z hz => by
            have hs := (valList_settled a b m c hba z hz).2
            rw [hBeq] at hs
            exact hs)
          (valList_closed a b m c hba hc hker)
        have hleft : ∀ w ∈ exhibit b :: tail,
            settledAt (valList (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c) w :=
          match hirr with
          | .inl hl => hl
          | .inr hr =>
            absurd (hr _ (ground.mem_map_to _ hy0A)) hy0off
        have hsp : elim.spanRel (exhibit b).coords.length
            (groupAt (valList (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c) (rowList b))
            (exhibit b).coords := by
          have h0 : allU (exhibit b).coords = true
              ∨ elim.spanRel (exhibit b).coords.length
                (groupAt (valList (blockSpan a) (blockSpan b)
                  (List.replicate a.length m) c) (exhibit b).content)
                (exhibit b).coords :=
            hleft (exhibit b) (List.Mem.head tail)
          rw [content_exhibit b] at h0
          match h0 with
          | .inl hall =>
            exact absurd (unitTail_of_allU _ hall)
              (exhibit_off_unit b)
          | .inr hsp0 => exact hsp0
        match elim.span_elim hsp with
        | ⟨c₀, cs, hc₀, _, hone⟩ =>
        by_cases hEx2 : ∃ w ∈ List.filter
            (fun z : HVec => z.content == rowList b)
            (valList (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c),
            ¬ poly.unitTail w.coords
        · match hEx2 with
          | ⟨w0, hw0f, hw0off⟩ =>
            match ground.mem_filter_of _ _ w0 hw0f with
            | ⟨hw0V, hw0b⟩ =>
              match ground.mem_map_of _ (blockSpan a) w0 hw0V with
              | ⟨y1, hy1A, hy1⟩ =>
                have hy1c : List.zipWith (fun u w => u - w)
                    (List.replicate a.length m) y1.content
                    = rowList b := by
                  rw [← pairVal_content (pairFam (blockSpan a)
                      (blockSpan b) (List.replicate a.length m) c) y1
                      (List.zipWith (fun u w => u - w)
                        (List.replicate a.length m) y1.content),
                    hy1]
                  exact ground.listBeqEq hw0b
                have hvoff : ¬ poly.unitTail
                    (pairVal (pairFam (blockSpan a) (blockSpan b)
                      (List.replicate a.length m) c) y1
                      (rowList b)).coords := by
                  rw [← hy1c, hy1]
                  exact hw0off
                refine ⟨y1, hy1A, ?_, hvoff⟩
                match pairVal_slot _ y1 _ hvoff with
                | ⟨t, htF, htc⟩ =>
                  have htf : t ∈ (pairFam (blockSpan a) (blockSpan b)
                      (List.replicate a.length m) c).filter
                      (fun s => s.2.1.content == y1.content) :=
                    ground.mem_filter_to _ htF (by
                      rw [htc]
                      exact ground.listEqBeq _)
                  match pairFam_slot_at (blockSpan a) (blockSpan b)
                      (List.replicate a.length m) c a.length hwA hwB
                      y1 t htf,
                    pairFam_slots (blockSpan a) (blockSpan b)
                      (List.replicate a.length m) c t htF with
                  | ⟨_, htcc⟩, ⟨_, _, htj⟩ =>
                    rw [← hy1c, ← htcc, ← htc]
                    exact htj
        · refine absurd ?_ (exhibit_off_unit b)
          refine elim.unitTail_unscale _ hc₀ (exhibit b).coords ?_
          refine poly.oneValue_unitTail hone ?_
          refine elim.unitTail_combo_rows _ cs _ (fun k hk => ?_)
          have hk' : k < (((valList (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c).filter
              (fun w => w.content == rowList b)).map
              HVec.coords).length := hk
          rw [ground.length_map] at hk'
          show poly.unitTail (ground.getAt ([] : List BPair)
            (((valList (blockSpan a) (blockSpan b)
              (List.replicate a.length m) c).filter
              (fun w => w.content == rowList b)).map HVec.coords) k)
          rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
            HVec.coords _ k hk']
          exact Decidable.byContradiction (fun hn => hEx2
            ⟨_, ground.mem_getAt (⟨[], []⟩ : HVec) _ k hk', hn⟩)
  · refine absurd (pairSolve (blockSpan a) (blockSpan b)
      (List.replicate a.length m) c a.length hwA hwB
      (lowerspan.spanReads a).2.1 (lowerspan.spanReads b).2.1 hc
      ?_) hoff
    intro y hy oc hocl hjoin
    by_cases hu : poly.unitTail
        (pairVal (pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) c) y
          (List.zipWith (fun u w => u - w)
            (List.replicate a.length m) y.content)).coords
    · rw [← compl_of_join y.content oc (List.replicate a.length m)
        a.length (hwA y hy) hocl hjoin]
      exact hu
    · exact absurd ⟨y, hy, hu⟩ hEx

/-! `lem:dualread`(iii)'s meet and the off-join arm's conclusion:
the occupied contents sit at or above the reversals
(`lem:strings`), and the two joins exchange the reads — at the
full-column content a prefix of the complement joins the content's
own prefix to the full columns' count, and at one degree a prefix
of a reversal joins its list's complementary prefix to the degree —
so the first factor's floor reads the occupied content at or above
`a`'s reversal while the second factor's floor, read through the
two exchanges, sits at or below it, and the two dominance
witnesses join to the unit fold: `b`'s row list is the complement's
read, `b` and `a^*` differing by full columns.  Off the join the
kernel is the unit family, and its dimension is nought. -/

/-- The dominance witness exchanges at the complements: at two
exact joins onto one fused content, every prefix of a summand joins
its complement's prefix to the fused content's own, so a comparison
of the two first summands at every prefix reads back reversed at
the two second summands, the totals tying at the whole length. -/
private theorem domBy_complFlip (X X' Y Y' cc : List Nat)
    (hX : X.length = cc.length) (hX' : X'.length = cc.length)
    (hY : Y.length = cc.length) (hY' : Y'.length = cc.length)
    (hj1 : List.zipWith (fun u w => u + w) X X' = cc)
    (hj2 : List.zipWith (fun u w => u + w) Y Y' = cc)
    (h : weylchar.domBy X Y) : weylchar.domBy Y' X' := by
  have e1 : ∀ k, ground.prefixAt k X + ground.prefixAt k X'
      = ground.prefixAt k cc := fun k =>
    (ground.prefixAt_zipAdd X X' (hX.trans hX'.symm) k).symm.trans
      (congrArg (ground.prefixAt k) hj1)
  have e2 : ∀ k, ground.prefixAt k Y + ground.prefixAt k Y'
      = ground.prefixAt k cc := fun k =>
    (ground.prefixAt_zipAdd Y Y' (hY.trans hY'.symm) k).symm.trans
      (congrArg (ground.prefixAt k) hj2)
  refine weylchar.domGo_ofPrefix 0 Y' X' (hY'.trans hX'.symm)
    (fun k => ?_) ?_
  · rw [Nat.zero_add]
    have hk := weylchar.domGo_prefix 0 X Y h k
    rw [Nat.zero_add] at hk
    exact ground.leCancelL (ground.prefixAt k X)
      (Nat.le_trans
        (Nat.add_le_add_right hk (ground.prefixAt k Y'))
        (Nat.le_of_eq ((e2 k).trans (e1 k).symm)))
  · rw [Nat.zero_add, hY', hX']
    have htot := weylchar.domGo_sum 0 X Y h
    rw [Nat.zero_add, hX, hY] at htot
    refine ground.addCancelL (ground.prefixAt cc.length Y) ?_
    rw [e2 cc.length, ← e1 cc.length, htot]

/-- The meet of the two joins: at two contents each joining a row
list to the full columns, each at or above its own list's reversal,
the second row list is the first's reversal's complement — the
reversed join carries the second witness to the complements, the
complementary exchange reads the first witness back at the
exchanged pair, and the two comparisons meet at one content. -/
private theorem join_meet (d m : Nat) (al be mu nu : List Nat)
    (hal : al.length = d) (hbe : be.length = d)
    (hj1 : List.zipWith (fun u w => u + w) mu be = List.replicate d m)
    (hj2 : List.zipWith (fun u w => u + w) nu al = List.replicate d m)
    (hd1 : weylchar.domBy al.reverse mu)
    (hd2 : weylchar.domBy be.reverse nu) :
    List.zipWith (fun u w => u + w) be al.reverse
      = List.replicate d m := by
  have hcc : (List.replicate d m).length = d :=
    ground.length_replicate m d
  have halr : al.reverse.length = d := by
    rw [ground.length_reverse]
    exact hal
  have hber : be.reverse.length = d := by
    rw [ground.length_reverse]
    exact hbe
  have hmu : mu.length = d := by
    rw [← weylchar.domGo_len 0 al.reverse mu hd1]
    exact halr
  have hnu : nu.length = d := by
    rw [← weylchar.domGo_len 0 be.reverse nu hd2]
    exact hber
  have hnur : nu.reverse.length = d := by
    rw [ground.length_reverse]
    exact hnu
  have hj2r : List.zipWith (fun u w => u + w) nu.reverse al.reverse
      = List.replicate d m := by
    rw [← ground.reverse_zipWith (fun u w => u + w) nu al
        (hnu.trans hal.symm), hj2, ground.reverse_replicate]
  have hfl : weylchar.domBy nu.reverse be := by
    have hr := weylchar.domBy_reverse be.reverse nu hd2
    rw [ground.reverse_reverse be] at hr
    exact hr
  have hbn : weylchar.domBy be nu.reverse :=
    domBy_complFlip al.reverse nu.reverse mu be (List.replicate d m)
      (halr.trans hcc.symm) (hnur.trans hcc.symm)
      (hmu.trans hcc.symm) (hbe.trans hcc.symm)
      ((ground.zipWith_add_comm al.reverse nu.reverse).trans hj2r)
      hj1 hd1
  rw [weylchar.domBy_antisymm be nu.reverse hbn hfl]
  exact hj2r

/-- Off the join the kernel of the stacked raisings at the stated
pair list is the unit family: a positive dimension names a kernel
member off the unit family, whose off-join read gives a first-block
content joining the second block's row list to the full columns,
and the exchanged pair list reads one dimension
(`lem:blockcount`(iii)), so the exchanged arm gives a second-block
content joining the first block's row list as well; both contents
sit at or above their own list's reversals (`lem:strings`), and the
meet reads the second row list as the first's reversal's
complement, against the off-join hypothesis — `lem:dualread`(iii)'s
off-join arm. -/
theorem ker_null_offJoin (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : ¬ List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m) :
    elim.kernelDim
      (pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).length
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) = 0 := by
  have hwit : ∀ s t : Shape, t.length = s.length →
      0 < elim.kernelDim
          (pairsAt (blockSpan s) (blockSpan t)
            (List.replicate s.length m)).length
          (elim.crossM (units.stackedRaise (List.replicate s.length m))
            ((pairsAt (blockSpan s) (blockSpan t)
              (List.replicate s.length m)).map HVec.coords)) →
      ∃ y ∈ blockSpan s,
        List.zipWith (fun u w => u + w) y.content (rowList t)
          = List.replicate s.length m := by
    intro s t hts hpos
    have hM := elim.rowsLen_crossM
      (units.stackedRaise (List.replicate s.length m))
      ((pairsAt (blockSpan s) (blockSpan t)
        (List.replicate s.length m)).map HVec.coords)
    rw [ground.length_map] at hM
    have hKlen : 0 < (elim.kernelList
        (pairsAt (blockSpan s) (blockSpan t)
          (List.replicate s.length m)).length
        (elim.crossM (units.stackedRaise (List.replicate s.length m))
          ((pairsAt (blockSpan s) (blockSpan t)
            (List.replicate s.length m)).map HVec.coords))).length := by
      rw [elim.kernelList_dim]
      exact hpos
    have hcw := elim.rowsLen_getAt _ 0
      (elim.kernelList_rowsLen _ _) hKlen
    have hoff := elim.indep_row_off
      (elim.kernelList_indep _ _ hM) 0 hKlen
    have hker := elim.kernelList_members _ _ hM 0 hKlen
    match valOff_head s t m _ hts hcw hker hoff with
    | ⟨y, hy, hjy, _⟩ => exact ⟨y, hy, hjy⟩
  match Nat.eq_zero_or_pos (elim.kernelDim
      (pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).length
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords))) with
  | .inl hz => exact hz
  | .inr hpos =>
    have hcomm := blockcount.kernelDim_pairs_comm (blockSpan a)
      (blockSpan b) (List.replicate a.length m) a.length
      (degree a) (degree b) (blockSpan_width a)
      (fun w hw => (blockSpan_width b w hw).trans hba)
      (blockSpan_degree a) (blockSpan_degree b)
      (lowerspan.spanReads a).2.1 (lowerspan.spanReads b).2.1
    have hpos2 : 0 < elim.kernelDim
        (pairsAt (blockSpan b) (blockSpan a)
          (List.replicate b.length m)).length
        (elim.crossM (units.stackedRaise (List.replicate b.length m))
          ((pairsAt (blockSpan b) (blockSpan a)
            (List.replicate b.length m)).map HVec.coords)) := by
      rw [hba, ← hcomm]
      exact hpos
    match hwit a b hba hpos, hwit b a hba.symm hpos2 with
    | ⟨y, hyA, hyj⟩, ⟨w, hwB, hwj⟩ =>
      refine absurd (join_meet a.length m (rowList a) (rowList b)
        y.content w.content (places.length_rowList a)
        ((places.length_rowList b).trans hba) hyj ?_ ?_ ?_) hjoin
      · rw [← hba]
        exact hwj
      · exact strings.rev_floor a y.content
          (ground.mem_map_to HVec.content hyA)
      · exact strings.rev_floor b w.content
          (ground.mem_map_to HVec.content hwB)

/-! `lem:dualread`(iii)'s at-join arm: at the join the kernel is at
most one line.  The value map is linear in its coefficient family —
the filtered slots' weights read the family's own sum, scale and
balance partner while the second slots' rows stand one list
throughout — and the first block's reversal member is occupied once
(`lem:strings`), its value a scale of the second block's head
(`lem:lowerspan`), so a kernel family whose value there reads the
sum's unit is the unit family, and two kernel families' cleared
combination reads one line. -/

/-- The family's weights at a filtered content read through an
entry map that crosses the pairing, the grid slots free. -/
private theorem pairFam_filter_mapC (x : HVec) (f : BPair → BPair)
    (hf : ∀ a p : BPair, f a * p = f (a * p)) :
    ∀ (c : List BPair) (g : List (HVec × HVec)), c.length = g.length →
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2))
            (c.map f) g).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
        = (((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2))
              c g).filter
            (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords)).map f
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: c, z :: g, h => by
    show ((((f a, z.1, z.2) : BPair × HVec × HVec) :: List.zipWith
            (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) (c.map f) g).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
        = (((((a, z.1, z.2) : BPair × HVec × HVec) :: List.zipWith
              (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c g).filter
            (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords)).map f
    cases hq : (z.1.content == x.content) with
    | true =>
      rw [ground.filter_cons_true
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((f a, z.1, z.2) : BPair × HVec × HVec)) hq,
        ground.filter_cons_true
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a, z.1, z.2) : BPair × HVec × HVec)) hq]
      show (f a * elim.dotP z.1.coords x.coords) :: _
        = f (a * elim.dotP z.1.coords x.coords) :: _
      rw [hf a (elim.dotP z.1.coords x.coords),
        pairFam_filter_mapC x f hf c g (Nat.succ.inj h)]
    | false =>
      rw [ground.filter_cons_false
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((f a, z.1, z.2) : BPair × HVec × HVec)) hq,
        ground.filter_cons_false
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a, z.1, z.2) : BPair × HVec × HVec)) hq]
      exact pairFam_filter_mapC x f hf c g (Nat.succ.inj h)

/-- The family's weights at a filtered content split at a summed
coefficient family, the grid slots free. -/
private theorem pairFam_filter_addC (x : HVec) :
    ∀ (c c' : List BPair) (g : List (HVec × HVec)),
      c.length = g.length → c'.length = g.length →
      ((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2))
            (elim.vecAdd c c') g).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
        = elim.vecAdd
          (((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2))
              c g).filter
            (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
          (((List.zipWith (fun cv (t : HVec × HVec) => (cv, t.1, t.2))
              c' g).filter
            (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, h, _ => nomatch h
  | [], _ :: _, _, h, h' => nomatch (h'.trans h.symm)
  | _ :: _, [], _, h, h' => nomatch (h.trans h'.symm)
  | _ :: _, _ :: _, [], h, _ => nomatch h
  | a :: c, a' :: c', z :: g, h, h' => by
    show ((((a + a', z.1, z.2) : BPair × HVec × HVec) :: List.zipWith
            (fun cv (t : HVec × HVec) => (cv, t.1, t.2))
            (elim.vecAdd c c') g).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
        = elim.vecAdd
          (((((a, z.1, z.2) : BPair × HVec × HVec) :: List.zipWith
              (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c g).filter
            (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
          (((((a', z.1, z.2) : BPair × HVec × HVec) :: List.zipWith
              (fun cv (t : HVec × HVec) => (cv, t.1, t.2)) c' g).filter
            (fun t => t.2.1.content == x.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
    cases hq : (z.1.content == x.content) with
    | true =>
      rw [ground.filter_cons_true
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a + a', z.1, z.2) : BPair × HVec × HVec)) hq,
        ground.filter_cons_true
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a, z.1, z.2) : BPair × HVec × HVec)) hq,
        ground.filter_cons_true
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a', z.1, z.2) : BPair × HVec × HVec)) hq]
      show ((a + a') * elim.dotP z.1.coords x.coords) :: _
        = (a * elim.dotP z.1.coords x.coords
            + a' * elim.dotP z.1.coords x.coords) :: _
      rw [BPair.right_distrib a a' (elim.dotP z.1.coords x.coords),
        pairFam_filter_addC x c c' g (Nat.succ.inj h) (Nat.succ.inj h')]
      rfl
    | false =>
      rw [ground.filter_cons_false
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a + a', z.1, z.2) : BPair × HVec × HVec)) hq,
        ground.filter_cons_false
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a, z.1, z.2) : BPair × HVec × HVec)) hq,
        ground.filter_cons_false
          (p := fun t : BPair × HVec × HVec => t.2.1.content == x.content)
          (a := ((a', z.1, z.2) : BPair × HVec × HVec)) hq]
      exact pairFam_filter_addC x c c' g (Nat.succ.inj h) (Nat.succ.inj h')

/-- The family's weights at a summed coefficient family split at
the two summands, the enumeration's slots the same throughout. -/
private theorem pairFam_filter_add (A B : List HVec) (cc : List Nat)
    (x : HVec) (c c' : List BPair)
    (hc : c.length = (pairsAt A B cc).length)
    (hc' : c'.length = (pairsAt A B cc).length) :
    ((pairFam A B cc (elim.vecAdd c c')).filter
        (fun t => t.2.1.content == x.content)).map
        (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
      = elim.vecAdd
        (((pairFam A B cc c).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords))
        (((pairFam A B cc c').filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)) :=
  pairFam_filter_addC x c c' (blockcount.pairIdx A (fun v => v) B cc)
    (hc.trans (pairsAt_len A B cc)) (hc'.trans (pairsAt_len A B cc))

/-- The family's weights at a scaled coefficient family read the
weights' own scale. -/
private theorem pairFam_filter_scale (A B : List HVec) (cc : List Nat)
    (x : HVec) (s : BPair) (c : List BPair)
    (hc : c.length = (pairsAt A B cc).length) :
    ((pairFam A B cc (elim.vecScale s c)).filter
        (fun t => t.2.1.content == x.content)).map
        (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
      = elim.vecScale s
        (((pairFam A B cc c).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)) :=
  pairFam_filter_mapC x (fun y => s * y)
    (fun a p => BPair.mul_assoc s a p) c
    (blockcount.pairIdx A (fun v => v) B cc)
    (hc.trans (pairsAt_len A B cc))

/-- The family's weights at a coefficient family's balance partner
read the weights' own partner. -/
private theorem pairFam_filter_neg (A B : List HVec) (cc : List Nat)
    (x : HVec) (c : List BPair)
    (hc : c.length = (pairsAt A B cc).length) :
    ((pairFam A B cc (poly.neg c)).filter
        (fun t => t.2.1.content == x.content)).map
        (fun t => t.1 * elim.dotP t.2.1.coords x.coords)
      = poly.neg
        (((pairFam A B cc c).filter
          (fun t => t.2.1.content == x.content)).map
          (fun t => t.1 * elim.dotP t.2.1.coords x.coords)) :=
  pairFam_filter_mapC x BPair.swap (fun a p => BPair.swap_mul a p) c
    (blockcount.pairIdx A (fun v => v) B cc)
    (hc.trans (pairsAt_len A B cc))

/-- The family's second slots at a filtered content read the
factor enumeration's own, the coefficients free. -/
private theorem pairFam_filter_rows (A B : List HVec) (cc : List Nat)
    (c : List BPair) (x : HVec)
    (hc : c.length = (pairsAt A B cc).length) :
    ((pairFam A B cc c).filter
        (fun t => t.2.1.content == x.content)).map
        (fun t => t.2.2.coords)
      = ((blockcount.pairIdx A (fun v => v) B cc).filter
          (fun p => p.1.content == x.content)).map
          (fun p => p.2.coords) := by
  rw [← zipTrip_filter (fun p : HVec × HVec => p.1.content == x.content)
      c (blockcount.pairIdx A (fun v => v) B cc)
      (hc.trans (pairsAt_len A B cc)),
    ground.map_map]
  rfl

/-- The family's filtered count at a stated content is the factor
enumeration's own. -/
private theorem pairFam_filter_len (A B : List HVec) (cc : List Nat)
    (c : List BPair) (x : HVec)
    (hc : c.length = (pairsAt A B cc).length) :
    ((pairFam A B cc c).filter
        (fun t => t.2.1.content == x.content)).length
      = ((blockcount.pairIdx A (fun v => v) B cc).filter
          (fun p => p.1.content == x.content)).length := by
  have h := congrArg List.length (pairFam_filter_rows A B cc c x hc)
  rw [ground.length_map, ground.length_map] at h
  exact h

/-- The value is additive in its coefficient family at the
families' shared order, the weights splitting slot by slot and the
second slots' rows standing. -/
private theorem pairVal_coefAdd (A B : List HVec) (cc : List Nat)
    (c c' : List BPair) (x : HVec) (oc : List Nat)
    (hc : c.length = (pairsAt A B cc).length)
    (hc' : c'.length = (pairsAt A B cc).length) :
    poly.oneValue
      (pairVal (pairFam A B cc (elim.vecAdd c c')) x oc).coords
      (elim.vecAdd (pairVal (pairFam A B cc c) x oc).coords
        (pairVal (pairFam A B cc c') x oc).coords) := by
  rw [pairVal_coords (pairFam A B cc (elim.vecAdd c c')) x oc,
    pairVal_coords (pairFam A B cc c) x oc,
    pairVal_coords (pairFam A B cc c') x oc,
    pairFam_filter_add A B cc x c c' hc hc',
    pairFam_filter_rows A B cc (elim.vecAdd c c') x
      (((ground.length_zipWith BPair.add c c'
        (pairsAt A B cc).length hc hc')).trans rfl),
    pairFam_filter_rows A B cc c x hc,
    pairFam_filter_rows A B cc c' x hc']
  refine elim.combo_vecAdd (places.monomialsAt oc).length _ _ _ ?_
  rw [ground.length_map, ground.length_map,
    pairFam_filter_len A B cc c x hc, pairFam_filter_len A B cc c' x hc']

/-- The value scales in its coefficient family, the clearing
crossing the weights. -/
private theorem pairVal_coefScale (A B : List HVec) (cc : List Nat)
    (s : BPair) (c : List BPair) (x : HVec) (oc : List Nat)
    (hc : c.length = (pairsAt A B cc).length) :
    poly.oneValue
      (pairVal (pairFam A B cc (elim.vecScale s c)) x oc).coords
      (elim.vecScale s (pairVal (pairFam A B cc c) x oc).coords) := by
  rw [pairVal_coords (pairFam A B cc (elim.vecScale s c)) x oc,
    pairVal_coords (pairFam A B cc c) x oc,
    pairFam_filter_scale A B cc x s c hc,
    pairFam_filter_rows A B cc (elim.vecScale s c) x
      ((elim.length_vecScale s c).trans hc),
    pairFam_filter_rows A B cc c x hc]
  exact poly.oneValue_symm
    (elim.vecScale_combo s (places.monomialsAt oc).length _ _)

/-- The value reads its coefficient family's balance partner at its
own partner, the swap crossing the weights and the combination. -/
private theorem pairVal_coefNeg (A B : List HVec) (cc : List Nat)
    (c : List BPair) (x : HVec) (oc : List Nat)
    (hc : c.length = (pairsAt A B cc).length) :
    (pairVal (pairFam A B cc (poly.neg c)) x oc).coords
      = poly.neg (pairVal (pairFam A B cc c) x oc).coords := by
  rw [pairVal_coords (pairFam A B cc (poly.neg c)) x oc,
    pairVal_coords (pairFam A B cc c) x oc,
    pairFam_filter_neg A B cc x c hc,
    pairFam_filter_rows A B cc (poly.neg c) x
      ((ground.length_map BPair.swap c).trans hc),
    pairFam_filter_rows A B cc c x hc]
  exact elim.combo_swapMap (places.monomialsAt oc).length _ _

/-- At the join the first block's reversal member reads the
coefficient family back: a family whose value there sits at the
sum's unit is the unit family — an off-unit family's own off-join
member joins the second block's row list to the full columns as
the reversal does, the sum's injectivity reads the two contents
one, and the reversal member is occupied once (`lem:strings`), so
the two members are one and the value's off-unit read is
refused; the reversal content is the clause's own site. -/
private theorem valRev_unit (a b : Shape) (m : Nat) (c : List BPair)
    (hba : b.length = a.length)
    (hc : c.length
      = (pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).length)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) c))
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (hval : poly.unitTail
      (pairVal (pairFam (blockSpan a) (blockSpan b)
        (List.replicate a.length m) c) g (rowList b)).coords) :
    poly.unitTail c := by
  by_cases hu : poly.unitTail c
  · exact hu
  · match valOff_head a b m c hba hc hker hu with
    | ⟨y, hyA, hyj, hyoff⟩ =>
      have hyc : y.content = g.content := by
        refine blockcount.zipWith_add_cancelL (rowList b) y.content
          g.content a.length ((places.length_rowList b).trans hba)
          (blockSpan_width a y hyA) (blockSpan_width a g hg) ?_
        rw [ground.zipWith_add_comm (rowList b) y.content, hyj,
          ground.zipWith_add_comm (rowList b) g.content, hgc,
          ground.zipWith_add_comm (rowList a).reverse (rowList b),
          hjoin]
      match ground.getAt_of_mem (⟨[], []⟩ : HVec) hyA,
        ground.getAt_of_mem (⟨[], []⟩ : HVec) hg with
      | ⟨p, hp, hpy⟩, ⟨q, hq, hqg⟩ =>
        by_cases hpq : p = q
        · rw [hpq] at hpy
          have hyg : y = g := hpy.symm.trans hqg
          rw [hyg] at hyoff
          exact absurd hval hyoff
        · have hml : ((blockSpan a).map HVec.content).length
              = (blockSpan a).length :=
            ground.length_map HVec.content (blockSpan a)
          have hp' : p < ((blockSpan a).map HVec.content).length := by
            rw [hml]
            exact hp
          have hq' : q < ((blockSpan a).map HVec.content).length := by
            rw [hml]
            exact hq
          have hgp : ground.getAt ([] : List Nat)
              ((blockSpan a).map HVec.content) p = (rowList a).reverse := by
            rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List Nat)
              HVec.content (blockSpan a) p hp, hpy, hyc, hgc]
          have hgq : ground.getAt ([] : List Nat)
              ((blockSpan a).map HVec.content) q = (rowList a).reverse := by
            rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List Nat)
              HVec.content (blockSpan a) q hq, hqg, hgc]
          have h2 := ground.countOf_two_pos ([] : List Nat)
            ((blockSpan a).map HVec.content) p q hp' hq' hpq
            (hgp.trans hgq.symm)
          rw [hgp, strings.rev_occupied a] at h2
          exact absurd h2 (by decide +kernel)

/-- The second block's group at its own row list is the head's
line (`lem:lowerspan`). -/
private theorem group_rowList (b : Shape) :
    groupAt (blockSpan b) (rowList b) = [(exhibit b).coords] := by
  match blockSpan_prov b with
  | ⟨tail, hBeq, hprov⟩ =>
    have h := blockirr.group_head b.length (exhibit b) tail
      (fun w hw => blockSpan_width b w (by rw [hBeq]; exact hw)) hprov
    rw [content_exhibit b] at h
    rw [hBeq]
    exact h

/-- The combination at a one-row list is that row's scale at the
leading coefficient, the vacant family reading the unit tail. -/
private theorem combo_oneRow (n : Nat) (r : List BPair) (hr : r.length = n) :
    ∀ cs : List BPair,
      poly.oneValue (elim.combo n cs [r])
        (elim.vecScale (ground.getAt BPair.unit cs 0) r)
  | [] =>
    poly.unitTail_oneValue (poly.unitTail_replicate n)
      (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) r)
  | [c] =>
    elim.vecAdd_null_right (elim.vecScale c r)
      (List.replicate n BPair.unit)
      (by rw [elim.length_vecScale, hr, ground.length_replicate])
      (poly.unitTail_replicate n)
  | c :: _ :: _ =>
    elim.vecAdd_null_right (elim.vecScale c r)
      (List.replicate n BPair.unit)
      (by rw [elim.length_vecScale, hr, ground.length_replicate])
      (poly.unitTail_replicate n)

/-- The value at the first block's reversal member: its width is
the second block's row list's own enumeration, and off the sum's
unit it is a cleared scale of the second block's head — the value's
content is the complement of the reversal, the join's read of the
target's own top, and the group there is the head's line
(`lem:lowerspan`). -/
private theorem valTop_read (a b : Shape) (m : Nat) (u : List BPair)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse) :
    (pairVal (pairFam (blockSpan a) (blockSpan b)
        (List.replicate a.length m) u) g (rowList b)).coords.length
        = (places.monomialsAt (rowList b)).length
      ∧ (¬ poly.unitTail (pairVal (pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) u) g (rowList b)).coords →
        ∃ c₀ lam, ¬ c₀.oneValue BPair.unit
          ∧ poly.oneValue
            (elim.vecScale c₀ (pairVal (pairFam (blockSpan a)
              (blockSpan b) (List.replicate a.length m) u) g
              (rowList b)).coords)
            (elim.vecScale lam (exhibit b).coords)) := by
  have hcompl : List.zipWith (fun x w => x - w)
      (List.replicate a.length m) g.content = rowList b := by
    rw [hgc]
    exact compl_of_join (rowList a).reverse (rowList b)
      (List.replicate a.length m) a.length
      (by rw [ground.length_reverse]; exact places.length_rowList a)
      ((places.length_rowList b).trans hba)
      ((ground.zipWith_add_comm (rowList a).reverse (rowList b)).trans
        hjoin)
  have hE : (exhibit b).coords.length
      = (places.monomialsAt (rowList b)).length := by
    have h : (exhibit b).coords.length
        = (places.monomialsAt (exhibit b).content).length :=
      (lowerspan.spanReads b).1 (exhibit b) (exhibit_mem b)
    rw [content_exhibit b] at h
    exact h
  match valList_settled a b m u hba _
      (valList_row (blockSpan a) (blockSpan b)
        (List.replicate a.length m) u (rowList b) g hg hcompl) with
  | ⟨hsz, hst⟩ =>
    refine ⟨hsz, fun hoff => ?_⟩
    match hst with
    | .inl hall => exact absurd (unitTail_of_allU _ hall) hoff
    | .inr hsp =>
      rw [show (pairVal (pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) u) g (rowList b)).content
          = rowList b from rfl, group_rowList b] at hsp
      match elim.span_elim hsp with
      | ⟨c₀, cs, hc₀, _, hone⟩ =>
        exact ⟨c₀, ground.getAt BPair.unit cs 0, hc₀,
          poly.oneValue_trans hone
            (combo_oneRow _ (exhibit b).coords (hE.trans hsz.symm) cs)⟩

/-- Two kernel families read one line at the reversal member: the
first family's value there is a cleared scale of the second block's
head and so is the second family's, the cleared combination's value
reads the sum's unit, and the reversal member reads that
combination back as the unit family — so the second family sits in
the first's span. -/
private theorem ker_span_step (a b : Shape) (m : Nat) (c c' : List BPair)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m)
    (g : HVec) (hg : g ∈ blockSpan a)
    (hgc : g.content = (rowList a).reverse)
    (hc : c.length = (pairsAt (blockSpan a) (blockSpan b)
      (List.replicate a.length m)).length)
    (hc' : c'.length = (pairsAt (blockSpan a) (blockSpan b)
      (List.replicate a.length m)).length)
    (hker : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) c))
    (hker' : poly.unitTail (elim.matVec
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) c'))
    (hoff : ¬ poly.unitTail c) :
    elim.spanRel (pairsAt (blockSpan a) (blockSpan b)
      (List.replicate a.length m)).length [c] c' := by
  have hN : ∀ u : List BPair,
      (pairVal (pairFam (blockSpan a) (blockSpan b)
          (List.replicate a.length m) u) g (rowList b)).coords.length
        = (places.monomialsAt (rowList b)).length :=
    fun u => (valTop_read a b m u hba hjoin g hg hgc).1
  have hrows : elim.rowsLen (pairsAt (blockSpan a) (blockSpan b)
      (List.replicate a.length m)).length [c] := ⟨hc, trivial⟩
  have hVc : ¬ poly.unitTail (pairVal (pairFam (blockSpan a)
      (blockSpan b) (List.replicate a.length m) c) g
      (rowList b)).coords := fun hv =>
    hoff (valRev_unit a b m c hba hc hker hjoin g hg hgc hv)
  match (valTop_read a b m c hba hjoin g hg hgc).2 hVc with
  | ⟨c₀, lam, hc₀, hcv⟩ =>
    have hlam : ¬ lam.oneValue BPair.unit := fun hl =>
      hVc (elim.unitTail_unscale c₀ hc₀ _
        (poly.oneValue_unitTail hcv
          (elim.unitTail_vecScale_unit hl (exhibit b).coords)))
    by_cases hV' : poly.unitTail (pairVal (pairFam (blockSpan a)
        (blockSpan b) (List.replicate a.length m) c') g (rowList b)).coords
    · refine elim.span_intro _ [c] c' hrows hc'
        ⟨c₀, [BPair.unit], hc₀, rfl, ?_⟩
      exact poly.unitTail_oneValue
        (elim.unitTail_vecScale c₀ c'
          (valRev_unit a b m c' hba hc' hker' hjoin g hg hgc hV'))
        (elim.unitTail_vecAdd_of
          (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) c)
          (poly.unitTail_replicate _))
    · match (valTop_read a b m c' hba hjoin g hg hgc).2 hV' with
      | ⟨c₀', lam', hc₀', hcv'⟩ =>
        have hs' : ¬ (lam * c₀').oneValue BPair.unit := fun hs =>
          hc₀' (ground.mul_cancel_unit hlam hs)
        have hEq : poly.oneValue
            (elim.vecScale (lam * c₀')
              (pairVal (pairFam (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c') g (rowList b)).coords)
            (elim.vecScale (lam' * c₀)
              (pairVal (pairFam (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c) g (rowList b)).coords) := by
          rw [← elim.vecScale_vecScale lam c₀'
              (pairVal (pairFam (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c') g (rowList b)).coords,
            ← elim.vecScale_vecScale lam' c₀
              (pairVal (pairFam (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c) g (rowList b)).coords]
          refine poly.oneValue_trans
            (elim.vecScale_oneValue lam _ _ hcv') ?_
          rw [elim.vecScale_vecScale lam lam' (exhibit b).coords,
            BPair.mul_comm lam lam',
            ← elim.vecScale_vecScale lam' lam (exhibit b).coords]
          exact elim.vecScale_oneValue lam' _ _ (poly.oneValue_symm hcv)
        have hXlen : (poly.neg (elim.vecScale (lam * c₀') c')).length
            = (pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).length :=
          (ground.length_map BPair.swap (elim.vecScale (lam * c₀') c')).trans
            ((elim.length_vecScale (lam * c₀') c').trans hc')
        have hYlen : (elim.vecScale (lam' * c₀) c).length
            = (pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).length :=
          (elim.length_vecScale (lam' * c₀) c).trans hc
        have hwlen : (elim.vecAdd (poly.neg (elim.vecScale (lam * c₀') c'))
              (elim.vecScale (lam' * c₀) c)).length
            = (pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).length :=
          ground.length_zipWith BPair.add _ _ _ hXlen hYlen
        have hwker : poly.unitTail (elim.matVec
            (elim.crossM (units.stackedRaise (List.replicate a.length m))
              ((pairsAt (blockSpan a) (blockSpan b)
                (List.replicate a.length m)).map HVec.coords))
            (elim.vecAdd (poly.neg (elim.vecScale (lam * c₀') c'))
              (elim.vecScale (lam' * c₀) c))) := by
          refine poly.oneValue_unitTail
            (elim.matVec_vecAdd_free _ _ _ (hXlen.trans hYlen.symm))
            (elim.unitTail_vecAdd_of ?_ ?_)
          · rw [elim.matVec_neg]
            exact poly.unitTail_swapMap _
              (poly.oneValue_unitTail (elim.matVec_vecScale_free _ _ c')
                (elim.unitTail_vecScale (lam * c₀') _ hker'))
          · exact poly.oneValue_unitTail
              (elim.matVec_vecScale_free _ _ c)
              (elim.unitTail_vecScale (lam' * c₀) _ hker)
        have hA : poly.oneValue
            (pairVal (pairFam (blockSpan a) (blockSpan b)
              (List.replicate a.length m)
              (poly.neg (elim.vecScale (lam * c₀') c'))) g
              (rowList b)).coords
            (poly.neg (elim.vecScale (lam * c₀')
              (pairVal (pairFam (blockSpan a) (blockSpan b)
                (List.replicate a.length m) c') g (rowList b)).coords)) := by
          rw [pairVal_coefNeg (blockSpan a) (blockSpan b)
            (List.replicate a.length m) (elim.vecScale (lam * c₀') c') g
            (rowList b) ((elim.length_vecScale (lam * c₀') c').trans hc')]
          exact poly.swapMap_oneValue
            (pairVal_coefScale (blockSpan a) (blockSpan b)
              (List.replicate a.length m) (lam * c₀') c' g (rowList b) hc')
        have hwval : poly.unitTail
            (pairVal (pairFam (blockSpan a) (blockSpan b)
              (List.replicate a.length m)
              (elim.vecAdd (poly.neg (elim.vecScale (lam * c₀') c'))
                (elim.vecScale (lam' * c₀) c))) g (rowList b)).coords := by
          refine poly.oneValue_unitTail
            (pairVal_coefAdd (blockSpan a) (blockSpan b)
              (List.replicate a.length m)
              (poly.neg (elim.vecScale (lam * c₀') c'))
              (elim.vecScale (lam' * c₀) c) g (rowList b) hXlen hYlen) ?_
          refine poly.oneValue_unitTail
            (elim.polyOne_vecAdd _ _ _ _ hA
              (pairVal_coefScale (blockSpan a) (blockSpan b)
                (List.replicate a.length m) (lam' * c₀) c g (rowList b) hc)
              ?_ ?_) ?_
          · exact (hN (poly.neg (elim.vecScale (lam * c₀') c'))).trans
              ((ground.length_map BPair.swap
                  (elim.vecScale (lam * c₀')
                    (pairVal (pairFam (blockSpan a) (blockSpan b)
                      (List.replicate a.length m) c') g
                      (rowList b)).coords)).trans
                ((elim.length_vecScale (lam * c₀') _).trans (hN c'))).symm
          · exact (hN (elim.vecScale (lam' * c₀) c)).trans
              ((elim.length_vecScale (lam' * c₀)
                (pairVal (pairFam (blockSpan a) (blockSpan b)
                  (List.replicate a.length m) c) g
                  (rowList b)).coords).trans (hN c)).symm
          · exact elim.null_swap_add _ _ hEq
        have hsw := elim.swap_of_null_add
          (poly.neg (elim.vecScale (lam * c₀') c'))
          (elim.vecScale (lam' * c₀) c) (hXlen.trans hYlen.symm)
          (valRev_unit a b m _ hba hwlen hwker hjoin g hg hgc hwval)
        have hnn : (poly.neg (elim.vecScale (lam * c₀') c')).map BPair.swap
            = elim.vecScale (lam * c₀') c' :=
          poly.neg_neg (elim.vecScale (lam * c₀') c')
        rw [hnn] at hsw
        refine elim.span_intro _ [c] c' hrows hc'
          ⟨lam * c₀', [lam' * c₀], hs', rfl, ?_⟩
        refine poly.oneValue_trans (poly.oneValue_symm hsw)
          (poly.oneValue_symm (elim.vecAdd_null_right
            (elim.vecScale (lam' * c₀) c)
            (List.replicate (pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).length BPair.unit)
            (by rw [elim.length_vecScale, hc, ground.length_replicate])
            (poly.unitTail_replicate _)))

/-- At the join the kernel of the stacked raisings at the stated
pair list is at most one line: the first block's reversal member is
occupied once (`lem:strings`) and its value sits in the second
block's head's group, the top line (`lem:lowerspan`), so every
kernel family reads a scale of the head there and two kernel
families' cleared combination is the unit family — the kernel
list's every member sits in the first member's span and the count
is at most one — `lem:dualread`(iii)'s at-join arm. -/
theorem ker_le_one_join (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m) :
    elim.kernelDim
      (pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).length
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) ≤ 1 := by
  have hM : elim.rowsLen
      (pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).length
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) := by
    have h := elim.rowsLen_crossM
      (units.stackedRaise (List.replicate a.length m))
      ((pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).map HVec.coords)
    rw [ground.length_map] at h
    exact h
  rw [← elim.kernelList_dim]
  match Nat.eq_zero_or_pos (elim.kernelList
      (pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).length
      (elim.crossM (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords))).length with
  | .inl hz =>
    rw [hz]
    exact Nat.zero_le 1
  | .inr hpos =>
    match ground.mem_map_of HVec.content (blockSpan a)
        ((rowList a).reverse)
        (ground.mem_of_countOf_pos ((rowList a).reverse)
          ((blockSpan a).map HVec.content)
          (by rw [strings.rev_occupied a]; exact Nat.succ_pos 0)) with
    | ⟨g, hgA, hgc⟩ =>
      exact elim.span_count_le
        (pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).length _
        [ground.getAt ([] : List BPair) (elim.kernelList
          (pairsAt (blockSpan a) (blockSpan b)
            (List.replicate a.length m)).length
          (elim.crossM (units.stackedRaise (List.replicate a.length m))
            ((pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).map HVec.coords))) 0]
        (elim.kernelList_rowsLen _ _)
        ⟨elim.rowsLen_getAt _ 0 (elim.kernelList_rowsLen _ _) hpos,
          trivial⟩
        (elim.kernelList_indep _ _ hM)
        (fun k hk => ker_span_step a b m _ _ hba hjoin g hgA hgc
          (elim.rowsLen_getAt _ 0 (elim.kernelList_rowsLen _ _) hpos)
          (elim.rowsLen_getAt _ k (elim.kernelList_rowsLen _ _) hk)
          (elim.kernelList_members _ _ hM 0 hpos)
          (elim.kernelList_members _ _ hM k hk)
          (elim.indep_row_off (elim.kernelList_indep _ _ hM) 0 hpos))

/-! `lem:dualread`(iii)'s at-join occupancy and the clause's own
count: the coevaluation is a member of the stated pair list's span
whose scale reads a kernel family off the unit family, so the
kernel list is occupied and the dimension is at least one; against
the at-most-one read the count at the full columns is exactly one
at the join and vacant off it. -/

/-- At the join the kernel is occupied: the reversal member is the
first block's one member at the row list's reversal
(`lem:strings`), the second block's span is its head's word family
(`lem:blockirr`(iv)), and the coevaluation at that data sits in the
stated pair list's span, in the stacked raisings' kernel, and off
the unit family.  The span's elimination clears the coevaluation by
an off-unit scale into a coefficient family: that family is a
kernel member of the cross datum (the cross action reads the
stacked action at the combination) and sits off the unit family (a
unit-tailed family combines to the unit family, which would
withdraw the cleared coevaluation), so the kernel list carries it
and cannot be vacant — `lem:dualread`(iii)'s at-join occupancy. -/
theorem ker_ge_one_join (a b : Shape) (m : Nat)
    (hba : b.length = a.length)
    (hjoin : List.zipWith (fun u w => u + w) (rowList b)
      (rowList a).reverse = List.replicate a.length m) :
    1 ≤ elim.kernelDim
      (pairsAt (blockSpan a) (blockSpan b)
        (List.replicate a.length m)).length
      (elim.crossM
        (units.stackedRaise (List.replicate a.length m))
        ((pairsAt (blockSpan a) (blockSpan b)
          (List.replicate a.length m)).map HVec.coords)) := by
  match ground.mem_map_of HVec.content (blockSpan a) ((rowList a).reverse)
      (ground.mem_of_countOf_pos ((rowList a).reverse)
        ((blockSpan a).map HVec.content)
        (by rw [strings.rev_occupied a]; exact Nat.succ_pos 0)) with
  | ⟨g, hgA, hgc⟩ =>
    match blockSpan_prov b with
    | ⟨tail, hBeq, hprov⟩ =>
      match blockirr.pool_words b.length (exhibit b) tail hprov with
      | ⟨W, hWeq, hWb⟩ =>
        have hW : blockSpan b = W.map (fun ws => wact ws (exhibit b)) :=
          hBeq.trans hWeq
        match elim.span_elim
            (coevVec_span a b m hba hjoin g hgA hgc W hW hWb) with
        | ⟨c₀, cs, hc0, hcsl, hs⟩ =>
          have hker : poly.unitTail (elim.matVec
              (elim.crossM (units.stackedRaise (List.replicate a.length m))
                ((pairsAt (blockSpan a) (blockSpan b)
                  (List.replicate a.length m)).map HVec.coords)) cs) := by
            refine poly.oneValue_unitTail
              (elim.matVec_crossM
                (places.monomialsAt (List.replicate a.length m)).length
                (units.stackedRaise (List.replicate a.length m))
                ((pairsAt (blockSpan a) (blockSpan b)
                  (List.replicate a.length m)).map HVec.coords) cs
                (units.rowsLen_stackedRaise _)
                (pairsAt_rowsLen (blockSpan a) (blockSpan b)
                  (List.replicate a.length m))) ?_
            refine poly.oneValue_unitTail
              (elim.matVec_congr
                (units.stackedRaise (List.replicate a.length m))
                (elim.combo
                  (places.monomialsAt (List.replicate a.length m)).length cs
                  ((pairsAt (blockSpan a) (blockSpan b)
                    (List.replicate a.length m)).map HVec.coords))
                (elim.vecScale c₀
                  (coevVec (List.replicate a.length m) b g W).coords)
                (poly.oneValue_symm hs)) ?_
            refine poly.oneValue_unitTail
              (elim.matVec_vecScale_free
                (units.stackedRaise (List.replicate a.length m)) c₀
                (coevVec (List.replicate a.length m) b g W).coords) ?_
            exact elim.unitTail_vecScale c₀ _
              (coevVec_ker a b m hba hjoin g hgA hgc W hW hWb)
          have hoff : ¬ poly.unitTail cs := by
            intro hu
            refine coevVec_off a b m hba hjoin g hgA hgc W hW hWb ?_
            refine elim.unitTail_unscale c₀ hc0 _ ?_
            exact poly.oneValue_unitTail hs
              (elim.unitTail_combo_of _ cs _ hu)
          have hM : elim.rowsLen
              (pairsAt (blockSpan a) (blockSpan b)
                (List.replicate a.length m)).length
              (elim.crossM (units.stackedRaise (List.replicate a.length m))
                ((pairsAt (blockSpan a) (blockSpan b)
                  (List.replicate a.length m)).map HVec.coords)) := by
            have h := elim.rowsLen_crossM
              (units.stackedRaise (List.replicate a.length m))
              ((pairsAt (blockSpan a) (blockSpan b)
                (List.replicate a.length m)).map HVec.coords)
            rw [ground.length_map] at h
            exact h
          have hcs : cs.length
              = (pairsAt (blockSpan a) (blockSpan b)
                (List.replicate a.length m)).length := by
            rw [hcsl, ground.length_map]
          have hsp := elim.kernelList_span
            (pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).length
            (elim.crossM (units.stackedRaise (List.replicate a.length m))
              ((pairsAt (blockSpan a) (blockSpan b)
                (List.replicate a.length m)).map HVec.coords)) hM cs hcs hker
          rw [← elim.kernelList_dim]
          refine Nat.pos_of_ne_zero (fun hz => hoff ?_)
          refine elim.spanRel_nil_unit
            (pairsAt (blockSpan a) (blockSpan b)
              (List.replicate a.length m)).length cs ?_
          rw [ground.nil_of_length_zero _ hz] at hsp
          exact hsp

/-- The fusion count at the full columns: one at the join of the
second block's row list with the first's reversal, vacant off it —
`lem:dualread`(iii) whole.  The stated content is the full-column
shape's row list, the constant list at the first block's letter
count (`rowList_fulls`), so the count is the kernel dimension at
that content: at the join the two arms meet at one
(`ker_le_one_join`, `ker_ge_one_join`) and off it the kernel is the
unit family (`ker_null_offJoin`). -/
theorem fusionCount_fulls (a b : Shape) (m : Nat)
    (hba : b.length = a.length) :
    fusionCount a b (dualread.fulls a.length m)
      = if List.zipWith (fun x y => x + y) (rowList b)
            ((rowList a).reverse)
          = List.replicate a.length m
        then 1 else 0 := by
  show elim.kernelDim
      (pairsAt (blockSpan a) (blockSpan b)
        (rowList (fulls a.length m))).length
      (elim.crossM (units.stackedRaise (rowList (fulls a.length m)))
        ((pairsAt (blockSpan a) (blockSpan b)
          (rowList (fulls a.length m))).map HVec.coords))
    = if List.zipWith (fun x y => x + y) (rowList b)
          ((rowList a).reverse)
        = List.replicate a.length m
      then 1 else 0
  rw [rowList_fulls a.length m]
  by_cases hj : List.zipWith (fun x y => x + y) (rowList b)
      ((rowList a).reverse) = List.replicate a.length m
  · rw [if_pos hj]
    exact Nat.le_antisymm (ker_le_one_join a b m hba hj)
      (ker_ge_one_join a b m hba hj)
  · rw [if_neg hj]
    exact ker_null_offJoin a b m hba hj

end dualread
