import MassGap.Dualread
import MassGapChecks.Blockcount
/-!
The check module for `lem:dualread`: the dual-action tier's decided
reads with the theorem routes beside them and the load-bearing
binders' isolating refusals — the unoccupied-letter refusals at the
diagonal's content and at the transpose walk — and the batteries
deciding the full-column line at the powers the tex displays: the
shape's own column list, the span's singleton at every power the
kernel reaches, and the theorem's instances beside the decided
reads, with the unoccupied power the base of the descent.  The
singlet read sits beside them: the gap read at the full-column
content, its letter count carrying no frame — at the vacant count
both sides read the empty column list — the row list at the
constant list, and the top's interior lowering at the unit tail
decided and
routed, the top binder isolated at a one-monomial vector of the
same content whose interior lowering refuses the tail.

The coevaluation tier's batteries sit beside them: the Gram-dual
coevaluation's datum at the tex's carriers, the moved coevaluation
decided at every member pair and both letter orders with the
theorem's route applied whole, and the flat-coefficient forgery's
refusal at a content carrying two members — the identity the
adjugate's, not the fold's shape.

The map tier's batteries follow them: the matrix family's
action decided as the map's value at both occupied contents with
the format's frame isolated at ragged slots on either side; the
forward equivariance at the occupied move with the invariance read
and the moved value's span read each isolated by its refusal and the
letter frame's survivals; and the second round trip decided at a
member, at an off-span argument, at the non-invariant and mismatched
families and through the theorem at the member and at the off-span
argument, with the first slots' span read isolated and the
off-content ragged member's survival recorded.

The count clause's batteries close the module: the matched pair
grid's width with the invariant count at the block's span and at the
mismatched-content lists' vacant grids, the moved form decided and
routed as the system's row against the coefficients, and the kernel
read's two directions — the stacked system's unit tail at a grid
vector the system reads carried through to a moved read at a letter
pair and a member pair, and at a grid vector the system refuses the
tail's refusal, the moved read's own refusal, and the second
direction carrying the refusal to the whole family of moved reads.
The solve-back closes them: the theorem's route at the block's own
span, the two independence binders isolated at a repeated member on
either side with every co-binder held and the coefficients refused,
and the map's unit read refused at the grid vector the stacked
system refuses.

The carrier tier's batteries close the module: the complementary
grid's shape at the block span's own fixture with the kernel datum
off the unit family, the value's equivariance decided at both
letter orders and read through the theorem at the raising pairs,
the non-adjacent raising at three letters decided and routed, and
the three refuted binder classes committed — the raising direction
`hpq` (the lowering refusing past both occupancy reads at the fused
content `[4,2]`, the raising surviving at the same data), the
one-degree frame `hdegA` (the minimal two-degree grid refusing with
its one-degree twin surviving), and the output content's width
`hocw` (the occupied padding refusing where `hoc`'s `zipWith`
truncates, the vacant padding surviving at the fixed
enumeration).

The complementary grid's solve-back closes them: the theorem's
route at two independent singletons of complementary content
joining the fused content, the unit family read back with the value
binder discharged at the coefficient read's own combination, and
five isolating refusals — the two groups' independence at a
repeated member on either side, the value read itself at
independent data with one value off the unit tail, the second
list's width at a member of content length `d + 1` whose truncated
join passes the grid's guard, and the family's shape at
coefficients past the pair list — the last four taken at the vacant
width, where the output content is the vacant list and every read
decides.

The value list's batteries close the module: the two blocks' spans
at the two-letter full column with the stated pair list's kernel
datum off the unit family, the list's length and its members'
contents and one member's value decided, the sized-and-settled read
and the closure read decided at both letter orders and read through
their theorems, and the off-join arm's existential decided and
routed with its witness member's join and off-unit value beside it.
The off-join read's binders refuse at their own instances: the
family's off-unit read at the unit family, which carries the shape
and the kernel read; the kernel read at an off-unit family of the
stated shape off the kernel, for the head's-group read and for the
letter closure alike; and the two blocks' matched width at a second
block one letter wider, where a value sits off the second block's
span and the off-join conclusion fails at an occupied pair list.
At a family longer than the pair list the tail past the list is
never read and the conclusion holds.  The mismatched second block
sits beside them, the stated pair list vacant and the conclusion
refused at the vacant family; the off-join conclusion is read at
occupied pair lists as well, the kernel vacant there.  The three-letter fixture
closes them at the full column `[1,1,1]` with the second block
`[0,1,0]`, the kernel one line there.

The dual-table tier's batteries close the module at the two-letter
join `a = b = [1,0]`, `m = 1`: the two bridges between the dual
action and the dual table's step and transpose decided and routed,
the complement invariant at the one-letter word with both liveness
binders decided and routed, and the Gram at the reversal member
decided and routed at two word pairs.  The liveness binders are
load-bearing (at the two-letter word both images read the unit tail
and the joined contents refuse the full columns) and so is the
reversal content (the span's other member carries the row list, and
the Gram's display refuses there).

The mapped-span engine's batteries close the module.  The fusion
count's descent at one full column is decided at four instances
beside the theorem's route, the last at the vacant count on both
sides, with the span length at the added column decided and routed
at three shapes, the carrier exchange at the mapped fused pool
decided and routed at an occupied content, and the mapped
carrier's count at the shifted content decided and routed both at
an interior content and at a content with a vacant letter — the
shifted content occupies every letter while the carrier's own
leaves one vacant, so the stacked datum carries a block the
carrier's own has none of.  Four binders are isolated by their
refusals: the second shape's letter width (one letter wider,
parting both the descent's counts and the carrier exchange's), the
stated content's own width (a content wider than the letter count
truncating onto the carrier while its group there is vacant), the
members' letter width (a member three letters wide, sized,
truncated onto the stated content), and the members' coordinate
width (a family one key short of its content's enumeration, read
whole once the wedge is tensored on); the descent read at an
unshifted target is refused beside them, the added column's two
counts parting at nought against one.  The lowering word past the
full wedge reads its own stratum: at a word whose
letters stay occupied the image's content is the shifted content
and its coordinates the tensored image's, and at a letter the
further factor leaves vacant the two contents part — the wedge
carrying the move its partner has no source for — while the two
coordinate families still read the sum's unit together.
-/
set_option maxHeartbeats 4000000

open ground places blockcount dualread

/-! `lem:dualread`(i)'s dual-action tier: the wedge at two letters
with its dual images, the decided reads beside the theorem
routes. -/

private def vDW : HVec := exhibit ([0, 1] : Shape)

/-! The sum's every entry of equal members, decided and at the
theorem's route. -/

example : poly.unitTail
    (poly.add (act 1 0 vDW).coords (dact 0 1 vDW).coords) := by decide +kernel
example : poly.unitTail
    (poly.add (act 1 0 vDW).coords (dact 0 1 vDW).coords) :=
  unitTail_act_dact 0 1 vDW

/-! The dual image's width, and the double dual. -/

example : sized (dact 0 1 vDW) := dact_sized 0 1 vDW
example : (⟨(dact 1 0 vDW).content, poly.neg (dact 1 0 vDW).coords⟩
    : HVec) = act 0 1 vDW := by decide +kernel
example : (⟨(dact 1 0 vDW).content, poly.neg (dact 1 0 vDW).coords⟩
    : HVec) = act 0 1 vDW := dact_dact 0 1 vDW

/-! The composition at the double partner, decided and at the
theorem's route. -/

example : dact 0 1 (dact 1 0 vDW) = act 1 0 (act 0 1 vDW) := by
  decide +kernel
example : dact 0 1 (dact 1 0 vDW) = act 1 0 (act 0 1 vDW) :=
  dact_comp 0 1 1 0 vDW

/-! The dual diagonal at the partner scalar, applied whole beside
the decided conjuncts. -/

example : (dact 0 0 vDW).content = vDW.content := by decide +kernel
example : poly.oneValue (dact 0 0 vDW).coords
    (elim.vecScale
      (BPair.ofNat (ground.getAt 0 vDW.content 0)).swap
      vDW.coords) := by decide +kernel
example : (dact 0 0 vDW).content = vDW.content
    ∧ poly.oneValue (dact 0 0 vDW).coords
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 vDW.content 0)).swap
        vDW.coords) :=
  dact_diag 0 vDW (by decide +kernel) (by decide +kernel)

/-- The diagonal content read's isolating refusal at the unoccupied
letter: the moved content differs while the carrier is sized at an
occupied width, so the occupancy binder is load-bearing. -/
private def vDU : HVec := ⟨[0, 2], [BPair.ofNat 1]⟩

example : sized vDU := by decide +kernel
example : 0 < vDU.content.length := by decide +kernel
example : ¬ ((dact 0 0 vDU).content = vDU.content) := by decide +kernel

/-- The sizedness binder's isolating refusal at the diagonal: a
carrier ragged beyond its basis at an occupied letter parts the
partner-scalar read while the occupancy and the content conjunct
survive, so the binder is load-bearing — the coordinate family over
the content's own monomials (`con:places`) is what the scalar read
prices. -/
private def vDL : HVec :=
  ⟨[1, 1], [BPair.ofNat 1, BPair.unit, BPair.ofNat 4]⟩

example : ¬ sized vDL := by decide +kernel
example : 0 < ground.getAt 0 vDL.content 0 := by decide +kernel
example : (dact 0 0 vDL).content = vDL.content := by decide +kernel
example : ¬ ((dact 0 0 vDL).content = vDL.content
    ∧ poly.oneValue (dact 0 0 vDL).coords
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 vDL.content 0)).swap
        vDL.coords)) := by decide +kernel

/-- The refusal at the occupied second letter, the width's other
axis. -/
private def vDL2 : HVec := ⟨[1, 1],
  [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 5]⟩

example : ¬ sized vDL2 ∧ 0 < ground.getAt 0 vDL2.content 1 := by
  decide +kernel
example : ¬ ((dact 1 1 vDL2).content = vDL2.content
    ∧ poly.oneValue (dact 1 1 vDL2).coords
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 vDL2.content 1)).swap
        vDL2.coords)) := by decide +kernel

/-- The content conjunct alone is hypothesis-free past the
occupancy: it survives at the short-ragged carrier. -/
private def vDR : HVec := ⟨[1, 1], [BPair.ofNat 1]⟩

example : ¬ sized vDR := by decide +kernel
example : (dact 0 0 vDR).content = vDR.content := by decide +kernel

/-! The transpose identity at the dual: decided at the wedge and at
a wider shape with a second occupied letter, the theorem route
beside them. -/

example : (elim.dotP (dact 0 1 ⟨[1, 1], vDW.coords⟩).coords
      [BPair.ofNat 2]).oneValue
    (elim.dotP vDW.coords
      (dact 1 0 ⟨moveAt 1 0 [1, 1], [BPair.ofNat 2]⟩).coords) := by
  decide +kernel
example : (elim.dotP (dact 0 1 ⟨[1, 1], vDW.coords⟩).coords
      [BPair.ofNat 2]).oneValue
    (elim.dotP vDW.coords
      (dact 1 0 ⟨moveAt 1 0 [1, 1], [BPair.ofNat 2]⟩).coords) :=
  dact_adjoint 0 1 [1, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    vDW.coords [BPair.ofNat 2] (by decide +kernel) (by decide +kernel)

private def wD3 : List BPair :=
  (monomialsAt [2, 1, 0]).map (fun _ => BPair.ofNat 1)
private def rD3 : List BPair :=
  (monomialsAt (moveAt 1 0 [2, 1, 0])).map (fun _ => BPair.ofNat 3)

example : (elim.dotP (dact 0 1 ⟨[2, 1, 0], wD3⟩).coords
      rD3).oneValue
    (elim.dotP wD3
      (dact 1 0 ⟨moveAt 1 0 [2, 1, 0], rD3⟩).coords) := by decide +kernel

/-- The transpose walk's isolating refusal at the unoccupied source
letter: every co-binder reads true and the two pairings part, so the
occupancy binder is load-bearing. -/
private def wDU : List BPair :=
  (monomialsAt [0, 1]).map (fun _ => BPair.ofNat 1)
private def rDU : List BPair :=
  (monomialsAt (moveAt 1 0 [0, 1])).map (fun _ => BPair.ofNat 2)

example : ¬ ((elim.dotP (dact 0 1 ⟨[0, 1], wDU⟩).coords
      rDU).oneValue
    (elim.dotP wDU
      (dact 1 0 ⟨moveAt 1 0 [0, 1], rDU⟩).coords)) := by decide +kernel

/-- The distinct-letters binder's frame record: the move pair's
vocabulary is `con:units`' raising and lowering at distinct letters,
the diagonal's transpose read the partner scalar's own
(`dact_diag`), and the two dual pairings meet at the diagonal
instance, the record's read. -/
example : (elim.dotP (dact 0 0 ⟨[1, 1], vDW.coords⟩).coords
      [BPair.ofNat 2, BPair.ofNat 3]).oneValue
    (elim.dotP vDW.coords
      (dact 0 0 ⟨moveAt 0 0 [1, 1],
        [BPair.ofNat 2, BPair.ofNat 3]⟩).coords) := by decide +kernel

/-! `lem:dualread`(i)'s agreement tier: the dual images settled at
the block's span, the settled swap, and the dual irreducibility
applied whole. -/

example : settledAt (blockSpan ([0, 1] : Shape)) (dact 0 1 vDW) := by
  decide +kernel
example : ∀ v ∈ blockSpan ([0, 1] : Shape),
    settledAt (blockSpan ([0, 1] : Shape)) (dact 0 1 v) :=
  dact_closed [0, 1] (by decide +kernel) (by decide +kernel) 0 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : settledAt [vDW] ⟨vDW.content, poly.neg vDW.coords⟩ := by
  decide +kernel
example : settledAt [vDW] ⟨vDW.content, poly.neg vDW.coords⟩ :=
  settled_neg [vDW] vDW.content vDW.coords (by decide +kernel)

example : (∀ w ∈ [vDW], settledAt [vDW] w)
    ∨ (∀ x ∈ [vDW], poly.unitTail x.coords) :=
  dual_irred 2 vDW [] [vDW] (by decide +kernel) (by decide +kernel)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : ∀ w ∈ [vDW], settledAt [vDW] w := by decide +kernel

/-! `lem:dualread`(i)'s evaluation tier: the coordinate form and the
graded form decided beside the theorem routes, the graded read at
every member pair of the block's span. -/

example : ((elim.dotP (dact 0 1 ⟨[1, 1], vDW.coords⟩).coords
      [BPair.ofNat 2])
    + (elim.dotP vDW.coords
      (act 0 1 ⟨moveAt 1 0 [1, 1], [BPair.ofNat 2]⟩).coords)
    ).oneValue BPair.unit := by decide +kernel
example : ((elim.dotP (dact 0 1 ⟨[1, 1], vDW.coords⟩).coords
      [BPair.ofNat 2])
    + (elim.dotP vDW.coords
      (act 0 1 ⟨moveAt 1 0 [1, 1], [BPair.ofNat 2]⟩).coords)
    ).oneValue BPair.unit :=
  ev_equiv 0 1 [1, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    vDW.coords [BPair.ofNat 2] (by decide +kernel) (by decide +kernel)

example : ∀ a ∈ blockSpan ([0, 1] : Shape),
    ∀ b ∈ blockSpan ([0, 1] : Shape),
    (dotG (dact 0 1 b) a + dotG (act 0 1 a) b).oneValue
      BPair.unit := by decide +kernel
example : ∀ a ∈ blockSpan ([1, 1] : Shape),
    ∀ b ∈ blockSpan ([1, 1] : Shape),
    (dotG (dact 1 0 b) a + dotG (act 1 0 a) b).oneValue
      BPair.unit := by decide +kernel
example : (dotG (dact 0 1 (exhibit [0, 1])) (exhibit [0, 1])
    + dotG (act 0 1 (exhibit [0, 1])) (exhibit [0, 1])).oneValue
      BPair.unit :=
  ev_equivG 0 1 (exhibit [0, 1]) (exhibit [0, 1]) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The promoted scale-partner and width laws at the tier's data. -/

example : elim.vecScale (BPair.swap (BPair.ofNat 2)) vDW.coords
    = (elim.vecScale (BPair.ofNat 2) vDW.coords).map BPair.swap :=
  elim.vecScale_swap (BPair.ofNat 2) vDW.coords
example : (poly.neg vDW.coords).length = vDW.coords.length :=
  poly.length_neg vDW.coords

/-! `lem:dualread`(i)'s coevaluation tier: the Gram-dual
coevaluation's datum at the tex's carriers, the moved coevaluation
decided at every member pair and both letter orders with the
theorem's route applied whole, and the flat-coefficient forgery's
refusal the datum's discrimination. -/

private def Ys : List HVec := blockSpan ([0, 1] : Shape)
private def Yr : List HVec := blockSpan ([1, 1] : Shape)
private def Yt : List HVec := blockSpan ([1, 0, 0] : Shape)

/-- A ragged pool at one occupied content twice, the block whose
adjugate is not the singleton's. -/
private def xF : HVec := ⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 5]⟩
private def x2F : HVec := ⟨[1, 1], [BPair.ofNat 4, BPair.ofNat 10]⟩
private def zF : HVec := ⟨[2, 0], [BPair.ofNat 3]⟩
private def Yh : List HVec := [xF, x2F, zF]

/-- The moved coevaluation against a member pair: a letter pair's
Leibniz image paired at the coevaluation's datum. -/
private def coevMoved (Y : List HVec) (p q : Nat)
    (a b : HVec) : BPair :=
  movedAt (coevData Y) p q a b

private def coevFlat (Y : List HVec) (p q : Nat) (a b : HVec) :
    BPair :=
  elim.dotP ((coevData Y).map (fun _ => BPair.ofNat 1))
    ((coevData Y).map (fun t =>
      dotG (dact p q t.2.1) a * dotG t.2.2 b
        + dotG t.2.1 a * dotG (act p q t.2.2) b))

/-! The datum is occupied, one entry per key pair per occupied
content, with the member pairs the group's own. -/

example : 0 < (coevData Ys).length := by decide +kernel
example : (coevData Ys).length = 1 := by decide +kernel
example : (coevData Yr).length = 2 := by decide +kernel
example : (coevData Yt).length = 3 := by decide +kernel
example : (coevData Yh).length = 5 := by decide +kernel
example : (coevData Yr).map (fun t => (t.2.1.content, t.2.2.content))
    = [([2, 1], [2, 1]), ([1, 2], [1, 2])] := by decide +kernel

/-! The datum's coefficients sit off the sum's unit: the adjugate
entries against the further blocks' determinants contribute. -/

example : ¬ (ground.getAt BPair.unit
    ((coevData Yr).map (fun t => t.1)) 0).oneValue BPair.unit := by
  decide +kernel
example : ¬ (ground.getAt BPair.unit
    ((coevData Yh).map (fun t => t.1)) 0).oneValue BPair.unit := by
  decide +kernel

/-! The moved coevaluation reads the sum's unit at every member
pair and both letter orders, at the tex's two carriers and at the
ragged pool. -/

example : ∀ a ∈ Ys, ∀ b ∈ Ys,
    (coevMoved Ys 0 1 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Ys, ∀ b ∈ Ys,
    (coevMoved Ys 1 0 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yr, ∀ b ∈ Yr,
    (coevMoved Yr 0 1 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yr, ∀ b ∈ Yr,
    (coevMoved Yr 1 0 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yh, ∀ b ∈ Yh,
    (coevMoved Yh 0 1 a b).oneValue BPair.unit := by decide +kernel

/-! The theorem's route applied whole at stated member pairs. -/

example : (coevMoved Ys 0 1 (exhibit [0, 1])
    (exhibit [0, 1])).oneValue BPair.unit :=
  coev_equiv Ys 0 1 (exhibit [0, 1]) (exhibit [0, 1]) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ys (by decide +kernel))
    (ground.mem_of_countOf_pos _ Ys (by decide +kernel))
example : (coevMoved Yr 1 0 (exhibit [1, 1])
    (ground.getAt (⟨[], []⟩ : HVec) Yr 1)).oneValue BPair.unit :=
  coev_equiv Yr 1 0 (exhibit [1, 1])
    (ground.getAt (⟨[], []⟩ : HVec) Yr 1) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Yr (by decide +kernel))
    (ground.mem_of_countOf_pos _ Yr (by decide +kernel))

/-! The independent multi-member groups: a two-member group and a
three-member group at off-unit block determinants, the adjugate
tier's own exercise — the moved coevaluation reads the sum's unit
with the theorem route beside it. -/

private def Yi : List HVec :=
  [⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩,
   ⟨[2, 1], [BPair.unit, BPair.ofNat 1, BPair.unit]⟩,
   ⟨[1, 2], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩]
private def Yg : List HVec :=
  [⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 1, BPair.unit]⟩,
   ⟨[2, 1], [BPair.unit, BPair.ofNat 1, BPair.ofNat 1]⟩,
   ⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.ofNat 1]⟩,
   ⟨[1, 2], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩]

example : (∀ w ∈ Yi, sized w) ∧ (∀ w ∈ Yg, sized w) := by decide +kernel
example : ¬ (elim.detL (elim.gramM
    ((Yi.filter (fun w => w.content == [2, 1])).map
      HVec.coords))).oneValue BPair.unit := by decide +kernel
example : ¬ (elim.detL (elim.gramM
    ((Yg.filter (fun w => w.content == [2, 1])).map
      HVec.coords))).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yi, ∀ b ∈ Yi,
    (coevMoved Yi 0 1 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yg, ∀ b ∈ Yg,
    (coevMoved Yg 0 1 a b).oneValue BPair.unit := by decide +kernel
example : (coevMoved Yi 0 1 (ground.getAt (⟨[], []⟩ : HVec) Yi 0)
    (ground.getAt (⟨[], []⟩ : HVec) Yi 2)).oneValue BPair.unit :=
  coev_equiv Yi 0 1 (ground.getAt (⟨[], []⟩ : HVec) Yi 0)
    (ground.getAt (⟨[], []⟩ : HVec) Yi 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Yi (by decide +kernel))
    (ground.mem_of_countOf_pos _ Yi (by decide +kernel))
example : (coevMoved Yg 0 1 (ground.getAt (⟨[], []⟩ : HVec) Yg 1)
    (ground.getAt (⟨[], []⟩ : HVec) Yg 3)).oneValue BPair.unit :=
  coev_equiv Yg 0 1 (ground.getAt (⟨[], []⟩ : HVec) Yg 1)
    (ground.getAt (⟨[], []⟩ : HVec) Yg 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Yg (by decide +kernel))
    (ground.mem_of_countOf_pos _ Yg (by decide +kernel))

/-! The datum's discrimination: at a content carrying two members
the flat-coefficient pairing refuses, so the identity is the
adjugate's and not the fold's shape. -/

example : ¬ (∀ a ∈ Yh, ∀ b ∈ Yh,
    (coevFlat Yh 0 1 a b).oneValue BPair.unit) := by decide +kernel

/-! The letter binders' frame records at `hpb`, `hqb` and `hpq`
(`con:places`' letter range at the carrier's width): at the equal
letter pair the diagonal's dual is the action's own balance
partner, so the two crossed pairings join outright, and at a letter
beyond the stated width the moved contents miss the pair's and the
graded pairings refuse together — the reads the instances below
decide. -/

example : ∀ a ∈ Ys, ∀ b ∈ Ys,
    (coevMoved Ys 0 0 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yr, ∀ b ∈ Yr,
    (coevMoved Yr 1 1 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yh, ∀ b ∈ Yh,
    (coevMoved Yh 1 1 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yr, ∀ b ∈ Yr,
    (coevMoved Yr 2 0 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yr, ∀ b ∈ Yr,
    (coevMoved Yr 0 2 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yt, ∀ b ∈ Yt,
    (coevMoved Yt 3 0 a b).oneValue BPair.unit := by decide +kernel
example : ∀ a ∈ Yt, ∀ b ∈ Yt,
    (coevMoved Yt 1 2 a b).oneValue BPair.unit := by decide +kernel

/-! The shape at a power: the top column occupied, every shorter
column unoccupied, the vacant letter count reading the empty column
list; its row list is the constant list at that count, decided and
routed. -/

example : fulls 2 0 = [0, 0] := by decide +kernel
example : fulls 2 1 = [0, 1] := by decide +kernel
example : fulls 2 2 = [0, 2] := by decide +kernel
example : fulls 3 1 = [0, 0, 1] := by decide +kernel
example : fulls 3 2 = [0, 0, 2] := by decide +kernel
example : fulls 0 3 = [] := by decide +kernel
example : rowList (fulls 0 3) = List.replicate 0 3 := by decide +kernel
example : rowList (fulls 1 2) = List.replicate 1 2 := by decide +kernel
example : rowList (fulls 2 1) = List.replicate 2 1 := by decide +kernel
example : rowList (fulls 3 0) = List.replicate 3 0 := by decide +kernel
example : rowList (fulls 2 1) = List.replicate 2 1 := rowList_fulls 2 1
example : rowList (fulls 3 0) = List.replicate 3 0 := rowList_fulls 3 0
example : rowList (fulls 0 3) = List.replicate 0 3 := rowList_fulls 0 3

/-! Clause (ii)'s line at clause (iii)'s powers: the span is the
column exhibit's own singleton. -/

example : blockSpan (fulls 2 0) = [exhibit (fulls 2 0)] := by decide +kernel
example : blockSpan (fulls 2 1) = [exhibit (fulls 2 1)] := by decide +kernel
example : blockSpan (fulls 2 2) = [exhibit (fulls 2 2)] := by decide +kernel
example : blockSpan (fulls 3 1) = [exhibit (fulls 3 1)] := by decide +kernel
example : blockSpan (fulls 3 2) = [exhibit (fulls 3 2)] := by decide +kernel

/-! The theorem's own instances beside the decided reads. -/

example : blockSpan (fulls 2 1) = [exhibit (fulls 2 1)] := lineSpan 2 1
example : blockSpan (fulls 2 2) = [exhibit (fulls 2 2)] := lineSpan 2 2
example : blockSpan (fulls 3 1) = [exhibit (fulls 3 1)] := lineSpan 3 1
example : blockSpan (fulls 3 2) = [exhibit (fulls 3 2)] := lineSpan 3 2
example : blockSpan (fulls 2 0) = [exhibit (fulls 2 0)] := lineSpan 2 0

/-- The line's occupancy read: one member at the power's own
content, the block dimension of the full-column line. -/
example : (blockSpan (fulls 3 2)).length = 1 := by
  rw [lineSpan 3 2]; rfl

/-! Clause (iii)'s singlet read (`fullTop_lower`): a top at the
full-column content generates the line, so its every interior
lowering reads the unit tail, the theorem applied whole at the
full-column top.  The shape at the full-column content is the
power's own column list at every letter count: at the vacant count
the consecutive gaps and the column list are both the empty list,
so the read carries no letter-count frame.  The top binder is
load-bearing: at the same content a vector supported on one
monomial is no top, and its interior lowering's coordinates refuse
the unit tail. -/

example : shapeOf (List.replicate 2 1) = fulls 2 1 := by decide +kernel
example : shapeOf (List.replicate 3 2) = fulls 3 2 := by decide +kernel
example : shapeOf (List.replicate 2 0) = fulls 2 0 := by decide +kernel
example : shapeOf (List.replicate 0 1) = fulls 0 1 := by decide +kernel

example : (exhibit (fulls 2 1)).content = List.replicate 2 1 := by
  decide +kernel
example : sized (exhibit (fulls 2 1)) := by decide +kernel
example : ∀ j, j < 2 → ∀ i, i < j →
    poly.unitTail (act i j (exhibit (fulls 2 1))).coords := by decide +kernel
example : ∀ v, lowerH 0 (exhibit (fulls 2 1)) = some v →
    poly.unitTail v.coords :=
  fun v hv => fullTop_lower 2 1 (exhibit (fulls 2 1)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 v (by decide +kernel) hv

example : sized (exhibit [1, 1]) := by decide +kernel
example : ∀ i, i + 1 < 2 →
    poly.unitTail (act i (i + 1) (exhibit [1, 1])).coords := by decide +kernel
example : ∀ m : Nat, ¬ (exhibit [1, 1]).content = List.replicate 2 m := by
  intro m h
  have h0 : ground.getAt 0 (exhibit [1, 1]).content 0 = m := by
    rw [h]; rfl
  have h1 : ground.getAt 0 (exhibit [1, 1]).content 1 = m := by
    rw [h]; rfl
  exact absurd ((show (2 : Nat) = m from h0).trans
    (show (1 : Nat) = m from h1).symm) (by decide +kernel)
example : ¬ poly.unitTail (match lowerH 0 (exhibit [1, 1]) with
    | some v => v.coords
    | none => []) := by decide +kernel

private def cNT : HVec := ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩

example : sized cNT := by decide +kernel
example : cNT.content = List.replicate 2 1 := by decide +kernel
example : ¬ (∀ i, i + 1 < 2 →
    poly.unitTail (act i (i + 1) cNT).coords) := by decide +kernel
example : ¬ poly.unitTail (match lowerH 0 cNT with
    | some v => v.coords
    | none => []) := by decide +kernel

/-! `lem:dualread`(i)'s round trip at the map: the composite reads
the graded determinant's scale at the members and at every member
of the argument's content group's span; the frame sits at the
content's own width and the argument at its member or span read,
each with its committed refusal. -/

private def Tid2 (mu : List Nat) : elim.Mat :=
  (elim.idList (places.monomialsAt mu).length).map
    (elim.vecScale (BPair.ofNat 2))

private def Yp : List HVec :=
  [⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 1, BPair.unit]⟩,
   ⟨[2, 1], [BPair.unit, BPair.ofNat 1, BPair.ofNat 1]⟩]

private def vP0 : HVec := ground.getAt (⟨[], []⟩ : HVec) Yp 0

private def vP1 : HVec := ground.getAt (⟨[], []⟩ : HVec) Yp 1

private def xNonP : HVec :=
  ⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩

private def T4bad (_mu : List Nat) : elim.Mat :=
  [[BPair.ofNat 2, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 2, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 2],
   [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]]

private def YRag : List HVec :=
  [⟨[1, 1], [BPair.ofNat 2]⟩, ⟨[2, 0], [BPair.ofNat 3]⟩]

-- the trip at both members, decided and through the theorem
example : poly.oneValue (mapAt (mapInv Tid2 Yp) vP0).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 vP0.content) vP0.coords)) := by decide +kernel

example : poly.oneValue (mapAt (mapInv Tid2 Yp) vP1).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 vP1.content) vP1.coords)) := by decide +kernel

example : poly.oneValue (mapAt (mapInv Tid2 Yp) vP0).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 vP0.content) vP0.coords)) :=
  mapInv_trip_mem Tid2 Yp vP0
    (ground.mem_of_countOf_pos _ Yp (by decide +kernel)) (by decide +kernel)

example : poly.oneValue (mapAt (mapInv Tid2 Yp) vP1).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 vP1.content) vP1.coords)) :=
  mapInv_trip_mem Tid2 Yp vP1
    (ground.mem_of_countOf_pos _ Yp (by decide +kernel)) (by decide +kernel)

-- the span binder's refusal: an argument off the partial group's
-- span, the span read refusing beside the conclusion
example : ¬ elim.spanRel xNonP.coords.length
    (blockcount.groupAt Yp xNonP.content) xNonP.coords := by decide +kernel
example : ¬ poly.oneValue (mapAt (mapInv Tid2 Yp) xNonP).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 xNonP.content) xNonP.coords)) := by
  decide +kernel

-- the width frame's refusal: a row past the content's coordinates
example : ¬ poly.oneValue (mapAt (mapInv T4bad Yp) vP0).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (T4bad vP0.content) vP0.coords)) := by decide +kernel

-- the trip at a ragged member, the sized frame not consumed
example : ∀ x ∈ YRag,
    poly.oneValue (mapAt (mapInv Tid2 YRag) x).coords
      (elim.vecScale (detAll YRag)
        (elim.matVec (Tid2 x.content) x.coords)) := by decide +kernel

private def xSp : HVec :=
  ⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 1]⟩

private def xNull : HVec :=
  ⟨[2, 1], [BPair.unit, BPair.unit, BPair.unit]⟩

-- the trip at a span member off the list: the span read through
-- the members, decided and through the theorem
example : ground.countOf xSp Yp = 0 := by decide +kernel
example : elim.spanRel xSp.coords.length
    (blockcount.groupAt Yp xSp.content) xSp.coords := by decide +kernel
example : poly.oneValue (mapAt (mapInv Tid2 Yp) xSp).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 xSp.content) xSp.coords)) := by decide +kernel
example : poly.oneValue (mapAt (mapInv Tid2 Yp) xSp).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 xSp.content) xSp.coords)) :=
  mapInv_trip Tid2 Yp xSp (by decide +kernel) (by decide +kernel)

-- the trip at a unit-tailed span member, the cleared
-- combination's degenerate read
example : poly.oneValue (mapAt (mapInv Tid2 Yp) xNull).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 xNull.content) xNull.coords)) :=
  mapInv_trip Tid2 Yp xNull (by decide +kernel) (by decide +kernel)

-- the width frame is load-bearing on the span arm as well: the
-- four-row map refuses at the off-list span member
example : ¬ poly.oneValue (mapAt (mapInv T4bad Yp) xSp).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (T4bad xSp.content) xSp.coords)) := by decide +kernel

/-- The ragged content group: two members at one content of
distinct widths, the group off the span relation's row frame. -/
private def YRagGrp : List HVec :=
  [⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 1, BPair.unit]⟩,
   ⟨[2, 1], [BPair.ofNat 1]⟩]

private def vRg0 : HVec := ground.getAt (⟨[], []⟩ : HVec) YRagGrp 0

-- the two reads are independent: a listed member of a ragged
-- group refuses the span read while the members' read holds,
-- decided and through the theorem
example : ¬ elim.spanRel vRg0.coords.length
    (blockcount.groupAt YRagGrp vRg0.content) vRg0.coords := by
  decide +kernel
example : poly.oneValue (mapAt (mapInv Tid2 YRagGrp) vRg0).coords
    (elim.vecScale (detAll YRagGrp)
      (elim.matVec (Tid2 vRg0.content) vRg0.coords)) := by decide +kernel
example : poly.oneValue (mapAt (mapInv Tid2 YRagGrp) vRg0).coords
    (elim.vecScale (detAll YRagGrp)
      (elim.matVec (Tid2 vRg0.content) vRg0.coords)) :=
  mapInv_trip_mem Tid2 YRagGrp vRg0
    (ground.mem_of_countOf_pos _ YRagGrp (by decide +kernel)) (by decide +kernel)

/-- The two-block carrier: the adjugate and the further block's
determinant both off their units. -/
private def Y2c : List HVec :=
  [⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 1, BPair.unit]⟩,
   ⟨[2, 1], [BPair.unit, BPair.ofNat 1, BPair.ofNat 1]⟩,
   ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
   ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩]

private def T4unit (_mu : List Nat) : elim.Mat :=
  [[BPair.ofNat 2, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 2, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 2],
   [BPair.unit, BPair.unit, BPair.unit]]

private def xUnocc : HVec :=
  ⟨[1, 2], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩

-- the trip where the adjugate collapse and the skipping product
-- are both occupied, every member
example : ∀ x ∈ Y2c,
    poly.oneValue (mapAt (mapInv Tid2 Y2c) x).coords
      (elim.vecScale (detAll Y2c)
        (elim.matVec (Tid2 x.content) x.coords)) := by decide +kernel

-- the scale and the read off their units at the two-block carrier
example : ¬ (detAll Y2c).oneValue BPair.unit := by decide +kernel
example : ¬ (detAll Yp).oneValue BPair.unit := by decide +kernel
example : ¬ poly.unitTail
    (mapAt (mapInv Tid2 Y2c)
      (ground.getAt (⟨[], []⟩ : HVec) Y2c 0)).coords := by decide +kernel

-- the argument at an unoccupied content refuses, the span read's
-- second axis
example : ¬ elim.spanRel xUnocc.coords.length
    (blockcount.groupAt Yp xUnocc.content) xUnocc.coords := by
  decide +kernel
example : ¬ poly.oneValue (mapAt (mapInv Tid2 Yp) xUnocc).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (Tid2 xUnocc.content) xUnocc.coords)) := by
  decide +kernel

-- the width frame's discrimination control: a unit-class excess
-- row does not refute, the padded read's own forgiveness
example : poly.oneValue (mapAt (mapInv T4unit Yp) vP0).coords
    (elim.vecScale (detAll Yp)
      (elim.matVec (T4unit vP0.content) vP0.coords)) := by decide +kernel

/-! `lem:dualread`(i)'s invariant read at the map: the moved
datum's pairing against a member and a second vector, decided at
the scalar and the non-scalar map with the theorem routes beside
them, and the load-bearing binders' isolating refusals — the
transport read, the span read and the argument's membership — with
the frame records beside them. -/

private def mvA : HVec :=
  ⟨[1, 2], [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]⟩
private def mvE1 : HVec :=
  ⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩
private def mvE2 : HVec :=
  ⟨[2, 1], [BPair.unit, BPair.ofNat 1, BPair.unit]⟩
private def mvE3 : HVec :=
  ⟨[2, 1], [BPair.unit, BPair.unit, BPair.ofNat 1]⟩
private def Ymv : List HVec := [mvE1, mvE2, mvE3, mvA]

/-- The non-scalar map at the moved content, the argument's image
an eigenvector at the doubling. -/
private def Tns (mu : List Nat) : elim.Mat :=
  if mu = [2, 1] then
    [[BPair.ofNat 3, (BPair.ofNat 1).swap, BPair.unit],
     [BPair.unit, BPair.ofNat 2, BPair.unit],
     [BPair.unit, BPair.unit, BPair.ofNat 2]]
  else Tid2 mu

/-- The map parting the two contents' scales, the transport's own
refusal. -/
private def Tmv3 (mu : List Nat) : elim.Mat :=
  if mu = [2, 1] then
    (elim.idList (places.monomialsAt mu).length).map
      (elim.vecScale (BPair.ofNat 3))
  else Tid2 mu

/-- The map at a scale of its own on the further letter pair's
contents. -/
private def Tnb (mu : List Nat) : elim.Mat :=
  if mu = [3, 0] then [[BPair.ofNat 3]]
  else if mu = [0, 3] then [[BPair.ofNat 3]]
  else Tid2 mu

/-- The map with a row past the content's coordinates. -/
private def Tpd (mu : List Nat) : elim.Mat :=
  if mu = [2, 1] then
    Tid2 mu ++ [[BPair.unit, BPair.unit, BPair.unit]]
  else Tid2 mu

/-- The map fixing a further argument's image at the doubling. -/
private def T2x (mu : List Nat) : elim.Mat :=
  if mu = [2, 1] then
    [[BPair.ofNat 9, (BPair.ofNat 5).swap, BPair.unit],
     [BPair.unit, BPair.ofNat 2, BPair.unit],
     [BPair.unit, BPair.unit, BPair.ofNat 2]]
  else Tid2 mu

private def aXv : HVec :=
  ⟨[1, 2], [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 5]⟩
private def a3v : HVec :=
  ⟨[1, 2], [BPair.ofNat 3, BPair.ofNat 3, BPair.ofNat 3]⟩
private def Ypoor : List HVec := [mvE1, mvA]
private def mvE1d : HVec :=
  ⟨[2, 1], [BPair.ofNat 2, BPair.unit, BPair.unit]⟩
private def Ydep : List HVec := [mvE1, mvE1d, mvE2, mvE3, mvA]

/-! The scalar map: the invariant read decided at two second
vectors with the theorem's route applied whole. -/

example : (movedAt (mapInv Tid2 Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tid2 Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit :=
  mapInv_equiv Tid2 Ymv 0 1 mvA mvE1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
example : (movedAt (mapInv Tid2 Ymv) 0 1 mvA mvE2).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tid2 Ymv) 0 1 mvA mvE2).oneValue
    BPair.unit :=
  mapInv_equiv Tid2 Ymv 0 1 mvA mvE2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)

/-! The non-scalar map at the moved content, decided and through
the theorem. -/

example : (movedAt (mapInv Tns Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tns Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit :=
  mapInv_equiv Tns Ymv 0 1 mvA mvE1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
example : (movedAt (mapInv Tns Ymv) 0 1 mvA mvE2).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tns Ymv) 0 1 mvA mvE2).oneValue
    BPair.unit :=
  mapInv_equiv Tns Ymv 0 1 mvA mvE2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)

/-! The dependent group: the moved content's determinant at the
sum's unit with the read standing, the independence binder's own
absence from the statement. -/

example : (elim.detL (elim.gramM
    (blockcount.groupAt Ydep [2, 1]))).oneValue BPair.unit := by
  decide +kernel
example : (movedAt (mapInv Tns Ydep) 0 1 mvA mvE1d).oneValue
    BPair.unit :=
  mapInv_equiv Tns Ydep 0 1 mvA mvE1d (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ydep (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)

/-! The second vector is general: off the list, unsized past the
content's coordinates, and short of them — the statement binds
neither its membership nor its width. -/

example : (movedAt (mapInv Tns Ymv) 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 5, BPair.ofNat 7, BPair.ofNat 11]⟩).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tns Ymv) 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 5, BPair.ofNat 7, BPair.ofNat 11]⟩).oneValue
    BPair.unit :=
  mapInv_equiv Tns Ymv 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 5, BPair.ofNat 7, BPair.ofNat 11]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
example : (movedAt (mapInv Tns Ymv) 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.unit,
      BPair.ofNat 3]⟩).oneValue BPair.unit := by decide +kernel
example : (movedAt (mapInv Tns Ymv) 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩).oneValue
    BPair.unit := by decide +kernel

/-! The transport read's isolating refusal: the two contents'
scales parted, the read refusing beside the conclusion. -/

example : ¬ poly.oneValue
    (act 0 1 (⟨mvA.content,
      elim.matVec (Tmv3 mvA.content) mvA.coords⟩ : HVec)).coords
    (elim.matVec (Tmv3 (moveAt 0 1 mvA.content))
      (act 0 1 mvA).coords) := by decide +kernel
example : ¬ (movedAt (mapInv Tmv3 Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit := by decide +kernel

/-! The span read's isolating refusal: the moved content's group
short of the argument's image, the read refusing beside the
conclusion. -/

example : ¬ elim.spanRel (act 0 1 mvA).coords.length
    (blockcount.groupAt Ypoor (act 0 1 mvA).content)
    (act 0 1 mvA).coords := by decide +kernel
example : ¬ (movedAt (mapInv Tns Ypoor) 0 1 mvA mvE1).oneValue
    BPair.unit := by decide +kernel

/-! The argument's membership binder's isolating refusal: at an
argument off the list every further read holds — the transport at
its own map and the image's span read — while the argument sits
off its own content group's span and the conclusion refuses; and
beside it the independence record at an off-list argument inside
that span, the conclusion standing. -/

example : poly.oneValue
    (act 0 1 (⟨aXv.content,
      elim.matVec (T2x aXv.content) aXv.coords⟩ : HVec)).coords
    (elim.matVec (T2x (moveAt 0 1 aXv.content))
      (act 0 1 aXv).coords) := by decide +kernel
example : elim.spanRel (act 0 1 aXv).coords.length
    (blockcount.groupAt Ymv (act 0 1 aXv).content)
    (act 0 1 aXv).coords := by decide +kernel
example : ¬ elim.spanRel aXv.coords.length
    (blockcount.groupAt Ymv aXv.content) aXv.coords := by decide +kernel
example : ¬ (movedAt (mapInv T2x Ymv) 0 1 aXv mvE1).oneValue
    BPair.unit := by decide +kernel
example : ground.countOf a3v Ymv = 0 := by decide +kernel
example : elim.spanRel a3v.coords.length
    (blockcount.groupAt Ymv a3v.content) a3v.coords := by decide +kernel
example : (movedAt (mapInv Tns Ymv) 0 1 a3v mvE1).oneValue
    BPair.unit := by decide +kernel

/-! The wide-transport record: the letter pair's transport refuses
at the second vector's own content while it holds at the argument,
and the conclusion stands — the read the statement prices is the
argument's. -/

example : ¬ poly.oneValue
    (act 0 1 (⟨mvE1.content,
      elim.matVec (Tnb mvE1.content) mvE1.coords⟩ : HVec)).coords
    (elim.matVec (Tnb (moveAt 0 1 mvE1.content))
      (act 0 1 mvE1).coords) := by decide +kernel
example : poly.oneValue
    (act 0 1 (⟨mvA.content,
      elim.matVec (Tnb mvA.content) mvA.coords⟩ : HVec)).coords
    (elim.matVec (Tnb (moveAt 0 1 mvA.content))
      (act 0 1 mvA).coords) := by decide +kernel
example : (movedAt (mapInv Tnb Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit := by decide +kernel

/-! The width-frame record: a row past the content's coordinates
keeps the transport read and the conclusion, the map's shape
entering through the transport alone. -/

example : poly.oneValue
    (act 0 1 (⟨mvA.content,
      elim.matVec (Tpd mvA.content) mvA.coords⟩ : HVec)).coords
    (elim.matVec (Tpd (moveAt 0 1 mvA.content))
      (act 0 1 mvA).coords) := by decide +kernel
example : (movedAt (mapInv Tpd Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit := by decide +kernel

/-! The letter frame's records: the diagonal letter pair, the
letters beyond the stated width, and the mirrored pair. -/

example : (movedAt (mapInv Tns Ymv) 0 0 mvE1 mvE2).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tid2 Ymv) 5 0 mvA mvE1).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tid2 Ymv) 0 5 mvA mvE1).oneValue
    BPair.unit := by decide +kernel
example : (movedAt (mapInv Tid2 Ymv) 1 0 mvE1 mvA).oneValue
    BPair.unit := by decide +kernel

/-! The argument's sized frame: the unsized argument as a list
member with the transport re-held — the padded coordinates at the
non-scalar map, and the short coordinates at the map fixing the
truncated image — the conclusion standing at both; the statement's
route reads the sized frame, so the records decide the reads
beyond it. -/

private def mvAp : HVec :=
  ⟨[1, 2], [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
    BPair.ofNat 5]⟩
private def Ymp : List HVec := [mvE1, mvE2, mvE3, mvAp]
private def mvAs : HVec := ⟨[1, 2], [BPair.ofNat 1, BPair.ofNat 1]⟩
private def Yms : List HVec := [mvE1, mvE2, mvE3, mvAs]
private def T3f (mu : List Nat) : elim.Mat :=
  if mu = [2, 1] then
    [[BPair.ofNat 3, (BPair.ofNat 2).swap, BPair.unit],
     [BPair.unit, BPair.ofNat 2, BPair.unit],
     [BPair.unit, BPair.unit, BPair.ofNat 2]]
  else Tid2 mu

example : poly.oneValue
    (act 0 1 (⟨mvAp.content,
      elim.matVec (Tns mvAp.content) mvAp.coords⟩ : HVec)).coords
    (elim.matVec (Tns (moveAt 0 1 mvAp.content))
      (act 0 1 mvAp).coords) := by decide +kernel
example : (movedAt (mapInv Tns Ymp) 0 1 mvAp mvE1).oneValue
    BPair.unit := by decide +kernel
example : poly.oneValue
    (act 0 1 (⟨mvAs.content,
      elim.matVec (T3f mvAs.content) mvAs.coords⟩ : HVec)).coords
    (elim.matVec (T3f (moveAt 0 1 mvAs.content))
      (act 0 1 mvAs).coords) := by decide +kernel
example : (movedAt (mapInv T3f Yms) 0 1 mvAs mvE1).oneValue
    BPair.unit := by decide +kernel

/-! The membership refusal's own pin beside its records: the
refused argument sits off the list. -/

example : ground.countOf aXv Ymv = 0 := by decide +kernel

/-! The theorem's route at the frame records: the landed binder
set accepts the general second vector, the shaped map and the
argument-side transport alone. -/

example : (movedAt (mapInv Tns Ymv) 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.unit,
      BPair.ofNat 3]⟩).oneValue BPair.unit :=
  mapInv_equiv Tns Ymv 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 1, BPair.unit, BPair.unit,
      BPair.ofNat 3]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
example : (movedAt (mapInv Tns Ymv) 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩).oneValue
    BPair.unit :=
  mapInv_equiv Tns Ymv 0 1 mvA
    ⟨[2, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
example : (movedAt (mapInv Tpd Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit :=
  mapInv_equiv Tpd Ymv 0 1 mvA mvE1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
example : (movedAt (mapInv Tnb Ymv) 0 1 mvA mvE1).oneValue
    BPair.unit :=
  mapInv_equiv Tnb Ymv 0 1 mvA mvE1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (ground.mem_of_countOf_pos _ Ymv (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)

/-! The matched-contents read: the invariant's family clause
decided and through the theorem. -/

example : ∀ t ∈ mapInv Tns Ymv,
    (t.2.2).content = (t.2.1).content := by decide +kernel
example : ∀ t ∈ mapInv Tns Ymv,
    (t.2.2).content = (t.2.1).content := mapInv_matched Tns Ymv

/-! `lem:dualread`(i)'s map data and its two round trips: the matrix
family at the identity family over the two-row block, the forward
equivariance at the occupied move with its two isolating refusals,
and the composite at an invariant reading the graded determinant's
scale at every argument with the first slots' span read isolated. -/

private def uC : HVec := ground.getAt (⟨[], []⟩ : HVec) Yr 1
private def yC : HVec := ground.getAt (⟨[], []⟩ : HVec) Yr 0
private def PC : List (BPair × HVec × HVec) := coevData Yr
private def PC1 : List (BPair × HVec × HVec) := [(BPair.ofNat 1, uC, uC)]
private def WC1 : List HVec := PC1.map (fun t => t.2.2)
private def PCs : List (BPair × HVec × HVec) :=
  PC.map (fun t =>
    if t.2.1.content == yC.content
    then (t.1, t.2.1, (⟨t.2.2.content,
      elim.vecScale (BPair.ofNat 2) t.2.2.coords⟩ : HVec))
    else t)
private def WCs : List HVec := PCs.map (fun t => t.2.2)
private def xOffC : HVec :=
  ⟨uC.content, [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 5]⟩
private def PCf : List (BPair × HVec × HVec) := [(BPair.ofNat 1, xOffC, xOffC)]
private def PCm : List (BPair × HVec × HVec) := [(BPair.ofNat 1, yC, uC)]

/-! The family format's frame at the identity family: the sized
slots at matched contents, decided. -/
example : ∀ t ∈ PC, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec) := by decide +kernel
example : ∀ t ∈ PC, (t.2.1 : HVec).content = (t.2.2 : HVec).content := by decide +kernel

/-! The matrix family's action is the map's value: decided at both
occupied contents and through the theorem. -/
example : poly.oneValue (elim.matVec (mapMat PC uC.content) uC.coords)
    (mapAt PC (⟨uC.content, uC.coords⟩ : HVec)).coords := by decide +kernel
example : poly.oneValue (elim.matVec (mapMat PC yC.content) yC.coords)
    (mapAt PC (⟨yC.content, yC.coords⟩ : HVec)).coords := by decide +kernel
example : poly.oneValue (elim.matVec (mapMat PC uC.content) uC.coords)
    (mapAt PC (⟨uC.content, uC.coords⟩ : HVec)).coords :=
  mapMat_read PC uC.content uC.coords (by decide +kernel) (by decide +kernel)

/-! The format's frame isolated at the matrix read: ragged second
slots truncate the map's accumulator along the second slots while
the matrix's row truncates along the first, so the read refuses;
widened to the format it passes. Ragged first slots refuse the read
as well. -/
private def wFullC : HVec := ⟨uC.content, [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]⟩
private def wShortC : HVec := ⟨uC.content, [BPair.ofNat 1, BPair.ofNat 1]⟩
private def PRag : List (BPair × HVec × HVec) :=
  [(BPair.ofNat 1, uC, wFullC), (BPair.ofNat 1, uC, wShortC)]
private def PWide : List (BPair × HVec × HVec) :=
  [(BPair.ofNat 1, uC, wFullC), (BPair.ofNat 1, uC, wFullC)]
private def PRagF : List (BPair × HVec × HVec) :=
  [(BPair.ofNat 1, wFullC, wFullC), (BPair.ofNat 1, wShortC, wFullC)]
example : ¬ (∀ t ∈ PRag, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec)) := by decide +kernel
example : ∀ t ∈ PRag, (t.2.1 : HVec).content = (t.2.2 : HVec).content := by decide +kernel
example : ¬ poly.oneValue (elim.matVec (mapMat PRag uC.content) uC.coords)
    (mapAt PRag (⟨uC.content, uC.coords⟩ : HVec)).coords := by decide +kernel
example : poly.oneValue (elim.matVec (mapMat PWide uC.content) uC.coords)
    (mapAt PWide (⟨uC.content, uC.coords⟩ : HVec)).coords := by decide +kernel
example : ¬ (∀ t ∈ PRagF, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec)) := by decide +kernel
example : ¬ poly.oneValue (elim.matVec (mapMat PRagF uC.content) wFullC.coords)
    (mapAt PRagF (⟨uC.content, wFullC.coords⟩ : HVec)).coords := by decide +kernel

/-! The matched-contents frame isolated at the matrix read: sized
slots at mismatched contents, the read refused. -/
private def PMm : List (BPair × HVec × HVec) :=
  [(BPair.ofNat 1,
    ⟨[2, 1], [(BPair.ofNat 1).swap, BPair.unit, BPair.unit]⟩,
    ⟨[1, 1], [(BPair.ofNat 1).swap, BPair.ofNat 1]⟩),
   (BPair.ofNat 1,
    ⟨[2, 1], [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap,
      (BPair.ofNat 1).swap]⟩,
    ⟨[2, 1], [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap,
      (BPair.ofNat 1).swap]⟩)]
example : ∀ t ∈ PMm, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec) := by decide +kernel
example : ¬ (∀ t ∈ PMm, (t.2.1 : HVec).content = (t.2.2 : HVec).content) := by
  decide +kernel
example : ¬ poly.oneValue
    (elim.matVec (mapMat PMm [2, 1])
      [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap, (BPair.ofNat 1).swap])
    (mapAt PMm (⟨[2, 1], [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap,
      (BPair.ofNat 1).swap]⟩ : HVec)).coords := by decide +kernel

/-! The forward equivariance at the occupied move, the carrier's
stated list the block span: the family's slots members of the
list, the invariance read and the list's settled images decided,
the moved image occupied, the conclusion decided and through the
theorem. -/
example : ∀ t ∈ PC, 0 < ground.countOf (t.2.2 : HVec) Yr := by decide +kernel
example : ∀ b ∈ Yr, (movedAt PC 0 1 uC b).oneValue BPair.unit := by decide +kernel
example : ∀ b ∈ Yr, settledAt Yr (act 0 1 b) := by decide +kernel
example : ¬ poly.unitTail (act 0 1 (mapAt PC uC)).coords := by decide +kernel
example : poly.oneValue (mapAt PC (act 0 1 uC)).coords
    (act 0 1 (mapAt PC uC)).coords := by decide +kernel
example : poly.oneValue (mapAt PC (act 0 1 uC)).coords
    (act 0 1 (mapAt PC uC)).coords :=
  mapAt_equiv PC Yr 0 1 uC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun t ht => ground.mem_of_countOf_pos _ Yr
      ((by decide +kernel : ∀ t ∈ PC,
        0 < ground.countOf (t.2.2 : HVec) Yr) t ht))
    (by decide +kernel) (by decide +kernel)

/-! The invariance read's isolating refusal: one content's second
slots scaled with the scaled slots the stated list, the family at
matched contents with the list's images settled, the invariance
refused and the conclusion with it. -/
example : ∀ t ∈ PCs, (t.2.1 : HVec).content = (t.2.2 : HVec).content := by decide +kernel
example : ∀ t ∈ PCs, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec) := by decide +kernel
example : ∀ w ∈ WCs, sized w := by decide +kernel
example : ∀ t ∈ PCs, 0 < ground.countOf (t.2.2 : HVec) WCs := by decide +kernel
example : ∀ b ∈ WCs, settledAt WCs (act 0 1 b) := by decide +kernel
example : ¬ (∀ b ∈ WCs, (movedAt PCs 0 1 uC b).oneValue BPair.unit) := by decide +kernel
example : ¬ poly.oneValue (mapAt PCs (act 0 1 uC)).coords
    (act 0 1 (mapAt PCs uC)).coords := by decide +kernel

/-! The settled-images read's isolating refusal: the one-member
family at the lower member with the one-member list, the
invariance held, the member's moved image occupied off the vacant
moved group, the conclusion refused. -/
example : ∀ b ∈ WC1, (movedAt PC1 0 1 uC b).oneValue BPair.unit := by decide +kernel
example : ¬ (∀ b ∈ WC1, settledAt WC1 (act 0 1 b)) := by decide +kernel
example : ¬ poly.oneValue (mapAt PC1 (act 0 1 uC)).coords
    (act 0 1 (mapAt PC1 uC)).coords := by decide +kernel

/-! The matched-contents frame's isolating refusal: a one-member
family at mismatched slot contents over the one-member list, every
further read held, the conclusion refused. -/
private def bm1C : BPair := (BPair.ofNat 1).swap
private def fMC : HVec := ⟨[2, 1], [bm1C, bm1C, bm1C]⟩
private def wMC : HVec := ⟨[1, 2], [bm1C, BPair.unit, BPair.ofNat 1]⟩
private def PMC : List (BPair × HVec × HVec) := [(bm1C, fMC, wMC)]
example : ∀ t ∈ PMC, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec) := by decide +kernel
example : ¬ (∀ t ∈ PMC, (t.2.1 : HVec).content = (t.2.2 : HVec).content) := by
  decide +kernel
example : ∀ w ∈ [wMC], sized w := by decide +kernel
example : ∀ t ∈ PMC, 0 < ground.countOf (t.2.2 : HVec) [wMC] := by decide +kernel
example : ∀ b ∈ [wMC], (movedAt PMC 1 0 fMC b).oneValue BPair.unit := by decide +kernel
example : ∀ b ∈ [wMC], settledAt [wMC] (act 1 0 b) := by decide +kernel
example : ¬ poly.oneValue (mapAt PMC (act 1 0 fMC)).coords
    (act 1 0 (mapAt PMC fMC)).coords := by decide +kernel

/-! The letter frame's records: the diagonal pair and the pair
beyond the width, the conclusion surviving at both with the
list's reads held. -/
example : ∀ b ∈ Yr, settledAt Yr (act 0 0 b) := by decide +kernel
example : ∀ b ∈ Yr, (movedAt PC 0 0 uC b).oneValue BPair.unit := by decide +kernel
example : poly.oneValue (mapAt PC (act 0 0 uC)).coords
    (act 0 0 (mapAt PC uC)).coords := by decide +kernel
example : ∀ b ∈ Yr, settledAt Yr (act 4 5 b) := by decide +kernel
example : ∀ b ∈ Yr, (movedAt PC 4 5 uC b).oneValue BPair.unit := by decide +kernel
example : poly.oneValue (mapAt PC (act 4 5 uC)).coords
    (act 4 5 (mapAt PC uC)).coords := by decide +kernel

/-! The second round trip: the composite at the identity family
reads the graded determinant's scale, decided at a member and at an
off-span argument, at the non-invariant family and at the
mismatched family, and through the theorem at the member and at
the off-span argument. -/
example : ∀ t ∈ PC, elim.spanRel (t.2.1 : HVec).coords.length
    (blockcount.groupAt Yr (t.2.1 : HVec).content)
    (t.2.1 : HVec).coords := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat PC) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt PC uC).coords) := by decide +kernel
example : ¬ elim.spanRel xOffC.coords.length
    (blockcount.groupAt Yr xOffC.content) xOffC.coords := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat PC) Yr) xOffC).coords
    (elim.vecScale (detAll Yr) (mapAt PC xOffC).coords) := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat PCs) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt PCs uC).coords) := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat PCm) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt PCm uC).coords) := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat PC) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt PC uC).coords) :=
  mapMat_trip PC Yr uC (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : poly.oneValue (mapAt (mapInv (mapMat PC) Yr) xOffC).coords
    (elim.vecScale (detAll Yr) (mapAt PC xOffC).coords) :=
  mapMat_trip PC Yr xOffC (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The first slots' span read isolated: the off-span first slot at
the off-span argument, the conclusion refused. -/
example : ¬ (∀ t ∈ PCf, elim.spanRel (t.2.1 : HVec).coords.length
    (blockcount.groupAt Yr (t.2.1 : HVec).content)
    (t.2.1 : HVec).coords) := by decide +kernel
example : ¬ poly.oneValue (mapAt (mapInv (mapMat PCf) Yr) xOffC).coords
    (elim.vecScale (detAll Yr) (mapAt PCf xOffC).coords) := by decide +kernel

/-! The format's frame isolated at the round trip: the ragged family
holds the first slots' span read and the conclusion refuses. -/
example : ∀ t ∈ PRag, elim.spanRel (t.2.1 : HVec).coords.length
    (blockcount.groupAt Yr (t.2.1 : HVec).content)
    (t.2.1 : HVec).coords := by decide +kernel
example : ¬ poly.oneValue (mapAt (mapInv (mapMat PRag) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt PRag uC).coords) := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat PWide) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt PWide uC).coords) := by decide +kernel

/-! The survival record at an off-content ragged member: the
appended member refuses the sized frame and the first slots' span
read at once, and the matrix read with the round trip pass, both
reads filtering at the read's own content past the member. -/
private def POff : List (BPair × HVec × HVec) :=
  PC ++ [(BPair.ofNat 2, ⟨[5, 5], [BPair.ofNat 1]⟩, ⟨[5, 5], []⟩)]
example : ¬ (∀ t ∈ POff, sized (t.2.1 : HVec) ∧ sized (t.2.2 : HVec)) := by decide +kernel
example : ¬ (∀ t ∈ POff, elim.spanRel (t.2.1 : HVec).coords.length
    (blockcount.groupAt Yr (t.2.1 : HVec).content)
    (t.2.1 : HVec).coords) := by decide +kernel
example : poly.oneValue (elim.matVec (mapMat POff uC.content) uC.coords)
    (mapAt POff (⟨uC.content, uC.coords⟩ : HVec)).coords := by decide +kernel
example : poly.oneValue (mapAt (mapInv (mapMat POff) Yr) uC).coords
    (elim.vecScale (detAll Yr) (mapAt POff uC).coords) := by decide +kernel

/-! `lem:dualread`(i)'s count clause: the matched pair grid at the
stated lists with the stacked system's kernel dimension, the moved
form read as the system's row against the coefficients, and the
kernel read's two directions at a grid vector the system reads and
at one it refuses. -/

private def Y1 : List HVec := blockSpan ([1] : Shape)
private def cKer : List BPair := (List.range 2).map (fun _ => BPair.unit)
private def cNK : List BPair := [BPair.ofNat 1, BPair.unit]

/-! The grid's width and the invariant count at the block's span,
with the mismatched-content lists' vacant grids. -/

example : (dualPairs Yr Yr).length = 2 := by decide +kernel
example : invCount Yr Yr 2 = 1 := by decide +kernel
example : invCount Y1 Yr 2 = 0 := by decide +kernel
example : invCount Yr Y1 2 = 0 := by decide +kernel

/-! The moved form at a coefficient family reads the system's row
against the coefficients, decided and at the theorem's route. -/

example : movedAt (invFam Yr Yr cNK) 0 1
      (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
      (ground.getAt (⟨[], []⟩ : HVec) Yr 0)
    = elim.dotP cNK (dualRow Yr Yr 0 1
      (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
      (ground.getAt (⟨[], []⟩ : HVec) Yr 0)) := by decide +kernel
example : movedAt (invFam Yr Yr cNK) 0 1
      (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
      (ground.getAt (⟨[], []⟩ : HVec) Yr 0)
    = elim.dotP cNK (dualRow Yr Yr 0 1
      (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
      (ground.getAt (⟨[], []⟩ : HVec) Yr 0)) :=
  movedAt_invFam Yr Yr cNK (by decide +kernel) 0 1
    (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
    (ground.getAt (⟨[], []⟩ : HVec) Yr 0)

/-! The kernel read at a grid vector the system reads: the stacked
system's unit tail decided, with the theorem carrying it to the
moved read at a letter pair and a member pair. -/

example : poly.unitTail (elim.matVec (dualSys Yr Yr 2) cKer) := by decide +kernel
example : (movedAt (invFam Yr Yr cKer) 0 1
    (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
    (ground.getAt (⟨[], []⟩ : HVec) Yr 0)).oneValue BPair.unit :=
  (dualKer_read Yr Yr 2 cKer (by decide +kernel)).mp (by decide +kernel)
    0 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
    _ (ground.mem_of_countOf_pos _ Yr (by decide +kernel))
    _ (ground.mem_of_countOf_pos _ Yr (by decide +kernel))

/-! The refusals at a grid vector the system does not read: the
stacked system's tail refused, the moved read refused at a letter
pair and a member pair, and the theorem's second direction carrying
the refusal to the family of moved reads. -/

example : ¬ poly.unitTail (elim.matVec (dualSys Yr Yr 2) cNK) := by decide +kernel
example : ¬ (movedAt (invFam Yr Yr cNK) 0 1
    (ground.getAt (⟨[], []⟩ : HVec) Yr 1)
    (ground.getAt (⟨[], []⟩ : HVec) Yr 0)).oneValue BPair.unit := by decide +kernel
example : ¬ (∀ p, p < 2 → ∀ q, q < 2 → ¬ p = q → ∀ a ∈ Yr, ∀ b ∈ Yr,
      (movedAt (invFam Yr Yr cNK) p q a b).oneValue BPair.unit) :=
  fun h =>
    (by decide +kernel : ¬ poly.unitTail (elim.matVec (dualSys Yr Yr 2) cNK))
      ((dualKer_read Yr Yr 2 cNK (by decide +kernel)).mpr h)

/-! `lem:dualread`(i)'s solve-back: a grid vector whose map reads
every listed member at the sum's unit is the unit family, the
theorem's route at the block's own span, with the two independence
binders isolated at a repeated member on either side and the value
read's own discrimination at a grid vector the map refuses. -/

private def Yone : List HVec := [uC]
private def Zdep : List HVec := [uC, uC]
private def cDep : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]

example : poly.unitTail cKer :=
  dualSolve Yr Yr cKer (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The second list's independence isolated: at a repeated second
member every other binder holds and the map reads the sum's unit at
the listed member, while the coefficients refuse the unit family. -/

example : ∀ w ∈ Yone, sized w := by decide +kernel
example : ∀ w ∈ Zdep, sized w := by decide +kernel
example : blockcount.indepAll Yone := by decide +kernel
example : ¬ blockcount.indepAll Zdep := by decide +kernel
example : cDep.length = (dualPairs Yone Zdep).length := by decide +kernel
example : ∀ y ∈ Yone,
    poly.unitTail (mapAt (invFam Yone Zdep cDep) y).coords := by decide +kernel
example : ¬ poly.unitTail cDep := by decide +kernel

/-! The first list's independence isolated: the repeated member
moved to the first list, the same coefficients refused. -/

example : cDep.length = (dualPairs Zdep Yone).length := by decide +kernel
example : ∀ y ∈ Zdep,
    poly.unitTail (mapAt (invFam Zdep Yone cDep) y).coords := by decide +kernel

/-! The value read's own discrimination: at the block's span the
grid vector the stacked system refuses also refuses the map's unit
read, so the hypothesis is occupied at the fixture. -/

example : ¬ (∀ y ∈ Yr,
    poly.unitTail (mapAt (invFam Yr Yr cNK) y).coords) := by decide +kernel

/-! `lem:dualread`(i)'s grid transport: the equivariant map's grid
vector at the graded solves, its width the grid's own, the kernel
membership at the equivariance, the map read at the two graded
determinants' scale with the wrong scale refused at the
discriminating second list, the unit-family map read, and every
load-bearing binder isolated at its committed refusal with the
letter and format frames' survivals beside them. -/

private def xrG : HVec := ground.getAt (⟨[], []⟩ : HVec) Yr 0
private def xr1G : HVec := ground.getAt (⟨[], []⟩ : HVec) Yr 1
private def TidG (mu : List Nat) : elim.Mat :=
  (elim.idList (places.monomialsAt mu).length).map
    (elim.vecScale (BPair.ofNat 2))
private def TscG (mu : List Nat) : elim.Mat :=
  (elim.idList (places.monomialsAt mu).length).map
    (elim.vecScale (if mu = [2, 1] then BPair.ofNat 2
      else BPair.ofNat 3))
private def TnullG (mu : List Nat) : elim.Mat :=
  (elim.idList (places.monomialsAt mu).length).map
    (elim.vecScale BPair.unit)
private def ZwG : List HVec :=
  [xrG, ⟨xr1G.content, elim.vecScale (BPair.ofNat 2) xr1G.coords⟩]
private def Z1G : List HVec := [vP0]
private def Z1rG : List HVec := [xrG]
private def v12xG : HVec :=
  ⟨[1, 2], [BPair.ofNat 1, BPair.unit, BPair.unit]⟩
private def YclG : List HVec := [xrG, v12xG]
private def cUG : List BPair :=
  (List.range (dualPairs Yp Yp).length).map (fun _ =>
    BPair.add (BPair.ofNat 3) (BPair.ofNat 3).swap)
/-! The grid vector's width is the grid's, decided at the block's
span, at the one-content family and at a mismatched pair, and
through the theorem. -/

example : (gridOf TidG Yr Yr).length = (dualPairs Yr Yr).length := by
  decide +kernel
example : (gridOf TidG Yp Yp).length = (dualPairs Yp Yp).length := by
  decide +kernel
example : (gridOf TidG Ys Yr).length = (dualPairs Ys Yr).length := by
  decide +kernel
example : (gridOf TidG Yr Yr).length = (dualPairs Yr Yr).length :=
  gridOf_len TidG Yr Yr

/-! A unit-family grid vector maps every argument to the unit tail,
decided and through the theorem. -/

example : poly.unitTail cUG := by decide +kernel
example : poly.unitTail (mapAt (invFam Yp Yp cUG) vP0).coords := by
  decide +kernel
example : poly.unitTail (mapAt (invFam Yp Yp cUG) vP0).coords :=
  invFam_unitTail Yp Yp cUG vP0 (by decide +kernel)

/-! The map is the determinants' scale of its own: decided and
through the theorem at the block's span and at the one-content
family, the wrong scale refused at the discriminating second list
whose block determinants differ. -/

example : poly.oneValue
    (mapAt (invFam Yr Yr (gridOf TidG Yr Yr)) xrG).coords
    (elim.vecScale (detAll Yr * detAll Yr)
      (elim.matVec (TidG xrG.content) xrG.coords)) := by decide +kernel
example : poly.oneValue
    (mapAt (invFam Yr Yr (gridOf TidG Yr Yr)) xrG).coords
    (elim.vecScale (detAll Yr * detAll Yr)
      (elim.matVec (TidG xrG.content) xrG.coords)) :=
  gridOf_val TidG Yr Yr xrG (by decide +kernel) (by decide +kernel)
example : poly.oneValue
    (mapAt (invFam Yp Yp (gridOf TidG Yp Yp)) vP0).coords
    (elim.vecScale (detAll Yp * detAll Yp)
      (elim.matVec (TidG vP0.content) vP0.coords)) :=
  gridOf_val TidG Yp Yp vP0 (by decide +kernel) (by decide +kernel)
example : ¬ (elim.detL (elim.gramM
    (blockcount.groupAt ZwG [2, 1]))).oneValue
    (elim.detL (elim.gramM (blockcount.groupAt ZwG [1, 2]))) := by
  decide +kernel
example : poly.oneValue
    (mapAt (invFam Yr ZwG (gridOf TidG Yr ZwG)) xrG).coords
    (elim.vecScale (detAll ZwG * detAll Yr)
      (elim.matVec (TidG xrG.content) xrG.coords)) :=
  gridOf_val TidG Yr ZwG xrG (by decide +kernel) (by decide +kernel)
example : ¬ poly.oneValue
    (mapAt (invFam Yr ZwG (gridOf TidG Yr ZwG)) xrG).coords
    (elim.vecScale (elim.detL (elim.gramM
        (blockcount.groupAt ZwG xrG.content)) * detAll Yr)
      (elim.matVec (TidG xrG.content) xrG.coords)) := by decide +kernel

/-! The argument's span read isolated: the off-span argument refuses
the read with the further binders held. -/

example : ¬ elim.spanRel (places.monomialsAt xNonP.content).length
    (blockcount.groupAt Yp xNonP.content) xNonP.coords := by decide +kernel
example : ∀ v ∈ blockcount.groupAt Yp xNonP.content,
    elim.spanRel v.length (blockcount.groupAt Yp xNonP.content)
      (elim.matVec (TidG xNonP.content) v) := by decide +kernel
example : ¬ poly.oneValue
    (mapAt (invFam Yp Yp (gridOf TidG Yp Yp)) xNonP).coords
    (elim.vecScale (detAll Yp * detAll Yp)
      (elim.matVec (TidG xNonP.content) xNonP.coords)) := by decide +kernel

/-! The values' span reads isolated at the delta's reach: the
second list missing a value refuses the read at the argument whose
solve touches the missing slot and survives at the argument whose
adjugate delta withdraws it. -/

example : elim.spanRel (places.monomialsAt vP1.content).length
    (blockcount.groupAt Yp vP1.content) vP1.coords := by decide +kernel
example : ¬ (∀ v ∈ blockcount.groupAt Yp vP1.content,
    elim.spanRel v.length (blockcount.groupAt Z1G vP1.content)
      (elim.matVec (TidG vP1.content) v)) := by decide +kernel
example : ¬ poly.oneValue
    (mapAt (invFam Yp Z1G (gridOf TidG Yp Z1G)) vP1).coords
    (elim.vecScale (detAll Z1G * detAll Yp)
      (elim.matVec (TidG vP1.content) vP1.coords)) := by decide +kernel
example : poly.oneValue
    (mapAt (invFam Yp Z1G (gridOf TidG Yp Z1G)) vP0).coords
    (elim.vecScale (detAll Z1G * detAll Yp)
      (elim.matVec (TidG vP0.content) vP0.coords)) := by decide +kernel

/-! The kernel membership: decided and through the theorem, the
format frame's clause a term read at the family's own width. -/

example : poly.unitTail
    (elim.matVec (dualSys Yr Yr 2) (gridOf TidG Yr Yr)) := by decide +kernel
example : poly.unitTail
    (elim.matVec (dualSys Yr Yr 2) (gridOf TidG Yr Yr)) :=
  gridOf_ker TidG Yr Yr 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : poly.unitTail
    (elim.matVec (dualSys Yr ZwG 2) (gridOf TidG Yr ZwG)) := by decide +kernel

/-! The equivariance isolated: the per-content scalar map keeps
every co-binder and refuses the stack, the span-preserving reads
decided beside the refusal. -/

example : ∀ mu ∈ Yr.map HVec.content,
    ∀ v ∈ blockcount.groupAt Yr mu,
    elim.spanRel v.length (blockcount.groupAt Yr mu)
      (elim.matVec (TscG mu) v) := by decide +kernel
example : ∀ p, p < 2 → ∀ q, q < 2 → ¬ p = q → ∀ a ∈ Yr,
    elim.spanRel (act p q a).coords.length
      (blockcount.groupAt Yr (act p q a).content)
      (act p q a).coords := by decide +kernel
example : ¬ (∀ p, p < 2 → ∀ q, q < 2 → ¬ p = q → ∀ a ∈ Yr,
    poly.oneValue (act p q (⟨a.content,
      elim.matVec (TscG a.content) a.coords⟩ : HVec)).coords
      (elim.matVec (TscG (blockcount.moveAt p q a.content))
        (act p q a).coords)) := by decide +kernel
example : ¬ poly.unitTail
    (elim.matVec (dualSys Yr Yr 2) (gridOf TscG Yr Yr)) := by decide +kernel

/-! The values' span read isolated at the kernel: the second list
missing the moved value refuses the stack with every co-binder
held. -/

example : ¬ (∀ mu ∈ Yr.map HVec.content,
    ∀ v ∈ blockcount.groupAt Yr mu,
    elim.spanRel v.length (blockcount.groupAt Z1rG mu)
      (elim.matVec (TidG mu) v)) := by decide +kernel
example : ¬ poly.unitTail
    (elim.matVec (dualSys Yr Z1rG 2) (gridOf TidG Yr Z1rG)) := by
  decide +kernel

/-! The moved span read isolated: with the second list holding the
moved content the closure's refusal refuses the stack at every
co-binder held, and at a second list off the moved contents the
branch stays closed, the scalar map's failed closure decided
beside its surviving stack. -/

private def Y1G : List HVec := [xrG]

example : ∀ w ∈ Y1G, sized w := by decide +kernel
example : ∀ w ∈ Y1G, 2 ≤ w.content.length := by decide +kernel
example : ∀ p, p < 2 → ∀ q, q < 2 → ¬ p = q → ∀ a ∈ Y1G,
    poly.oneValue (act p q (⟨a.content,
      elim.matVec (TidG a.content) a.coords⟩ : HVec)).coords
      (elim.matVec (TidG (blockcount.moveAt p q a.content))
        (act p q a).coords) := by decide +kernel
example : ∀ mu ∈ Y1G.map HVec.content,
    ∀ v ∈ blockcount.groupAt Y1G mu,
    elim.spanRel v.length (blockcount.groupAt Yr mu)
      (elim.matVec (TidG mu) v) := by decide +kernel
example : ¬ (∀ p, p < 2 → ∀ q, q < 2 → ¬ p = q → ∀ a ∈ Y1G,
    elim.spanRel (act p q a).coords.length
      (blockcount.groupAt Y1G (act p q a).content)
      (act p q a).coords) := by decide +kernel
example : ¬ poly.unitTail
    (elim.matVec (dualSys Y1G Yr 2) (gridOf TidG Y1G Yr)) := by
  decide +kernel

example : ¬ (∀ p, p < 2 → ∀ q, q < 2 → ¬ p = q → ∀ a ∈ YclG,
    elim.spanRel (act p q a).coords.length
      (blockcount.groupAt YclG (act p q a).content)
      (act p q a).coords) := by decide +kernel
example : poly.unitTail
    (elim.matVec (dualSys YclG YclG 2) (gridOf TidG YclG YclG)) := by
  decide +kernel

/-! The letter frame's survivals: the stack at letters beyond the
width stays at the unit read, and the out-of-range rows read the
unit against the non-kernel vector at every member pair. -/

example : poly.unitTail
    (elim.matVec (dualSys Yr Yr 4) (gridOf TidG Yr Yr)) := by decide +kernel
example : ∀ a ∈ Yr, ∀ b ∈ Yr,
    poly.unitTail (elim.matVec [dualRow Yr Yr 2 3 a b] cNK) := by
  decide +kernel

/-! The off-unit read: at the map value off the determinants' unit
tail the grid vector refuses the unit family, through the theorem,
with the vacant map's grid vector at the unit family beside it. -/

example : ¬ poly.unitTail
    (elim.vecScale (detAll Yr * detAll Yr)
      (elim.matVec (TidG xrG.content) xrG.coords)) := by decide +kernel
example : ¬ poly.unitTail (gridOf TidG Yr Yr) :=
  gridOf_off TidG Yr Yr xrG (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : poly.unitTail (gridOf TnullG Yr Yr) := by decide +kernel

/-! The count at the sum's unit with the grid occupied: a second
list twisted off the block's closure shares both contents, the two
slots' stack at full rank. -/

example : 0 < (dualPairs Yr [xrG, v12xG]).length := by decide +kernel
example : invCount Yr [xrG, v12xG] 2 = 0 := by decide +kernel
example : invCount [xrG, v12xG] Yr 2 = 0 := by decide +kernel

/-! The count close at the block's grid: the kernel list and the
stated one-map list read one count — the theorem route beside the
kernel's own decide, the independence, kernel and spanning binders
at their isolating refusals, and the width binder the grid's own
stated frame (`def:elim`'s row convention): the padded row refuses
the independence and kernel co-binders and the short row the
spanning one. -/

example : invCount Yr Yr 2 = 1 :=
  invCount_span Yr Yr 2 [gridOf TidG Yr Yr]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : elim.rowsLen (dualPairs Yr Yr).length
    [gridOf TidG Yr Yr,
     elim.vecScale (BPair.ofNat 2) (gridOf TidG Yr Yr)] := by
  decide +kernel
example : ∀ g ∈ [gridOf TidG Yr Yr,
      elim.vecScale (BPair.ofNat 2) (gridOf TidG Yr Yr)],
    poly.unitTail (elim.matVec (dualSys Yr Yr 2) g) := by decide +kernel
example : ∀ v ∈ elim.kernelList (dualPairs Yr Yr).length
      (dualSys Yr Yr 2),
    elim.spanRel (dualPairs Yr Yr).length
      [gridOf TidG Yr Yr,
       elim.vecScale (BPair.ofNat 2) (gridOf TidG Yr Yr)] v := by
  decide +kernel
example : ¬ elim.indepRows (dualPairs Yr Yr).length
    [gridOf TidG Yr Yr,
     elim.vecScale (BPair.ofNat 2) (gridOf TidG Yr Yr)] := by
  decide +kernel
example : ¬ (invCount Yr Yr 2 = 2) := by decide +kernel

example : elim.rowsLen (dualPairs Yr Yr).length
    [gridOf TidG Yr Yr, cNK] := by decide +kernel
example : elim.indepRows (dualPairs Yr Yr).length
    [gridOf TidG Yr Yr, cNK] := by decide +kernel
example : ∀ v ∈ elim.kernelList (dualPairs Yr Yr).length
      (dualSys Yr Yr 2),
    elim.spanRel (dualPairs Yr Yr).length
      [gridOf TidG Yr Yr, cNK] v := by decide +kernel
example : ¬ poly.unitTail
    (elim.matVec (dualSys Yr Yr 2) cNK) := by decide +kernel

example : ¬ (∀ v ∈ elim.kernelList (dualPairs Yr Yr).length
      (dualSys Yr Yr 2),
    elim.spanRel (dualPairs Yr Yr).length
      ([] : elim.Mat) v) := by decide +kernel
example : ¬ (invCount Yr Yr 2 = 0) := by decide +kernel

/-! The dual top (`lem:dualread`(ii)'s dual block): at the span
member carrying the row list's reversal every dual raising's image
reads the unit tail, decided at both committed spans and read
through the theorem with the membership at the indexed read.  The
binder record: the reversal content is load-bearing (the top
member's raising image occupied at both spans), the raising
direction is load-bearing (the dual lowering's image occupied at
the reversal member), the membership is load-bearing (a fabricated
non-member at the reversal content refuses), and the letter frame
survives beyond the width (`con:units`' letters, the frame's
survival at two out-of-range pairs). -/

example : (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1])
    1).content = (rowList [1, 1]).reverse := by decide +kernel
example : poly.unitTail (dact 0 1
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 1)).coords
    := by decide +kernel
example : poly.unitTail (dact 0 1
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 1)).coords :=
  dualTop [1, 1] _
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 1
      (by decide +kernel))
    (by decide +kernel) 0 1 (by decide +kernel) (by decide +kernel)
example : poly.unitTail (dact 1 2
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1, 0])
      7)).coords :=
  dualTop [1, 1, 0] _
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1, 0]) 7
      (by decide +kernel))
    (by decide +kernel) 1 2 (by decide +kernel) (by decide +kernel)
example : poly.unitTail (dact 0 1
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1, 0])
      7)).coords := by
  rw [blockcount.span110_pin]; decide +kernel
example : poly.unitTail (dact 0 2
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1, 0])
      7)).coords := by
  rw [blockcount.span110_pin]; decide +kernel

example : ¬ poly.unitTail (dact 0 1
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 0)).coords
    := by decide +kernel
example : ¬ poly.unitTail (dact 1 2
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1, 0])
      3)).coords := by
  rw [blockcount.span110_pin]; decide +kernel
example : ¬ poly.unitTail (dact 1 0
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 1)).coords
    := by decide +kernel
example : ¬ poly.unitTail (dact 0 1
    (⟨[1, 2], [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]⟩
      : HVec)).coords := by decide +kernel
example : poly.unitTail (dact 0 5
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 1)).coords
    := by decide +kernel
example : poly.unitTail (dact 2 3
    (ground.getAt (⟨[], []⟩ : HVec) (blockSpan [1, 1]) 1)).coords
    := by decide +kernel

/-! `lem:dualread`(iii)'s carrier tier: the complementary grid's
family and its value's equivariance at the raising direction,
decided at the block span's own grid and read through the theorem,
with the three refuted binder classes committed beside it. -/

private def cA0 : List HVec := blockSpan [2, 0]
private def cCC0 : List Nat := [2, 2]
private def cK0 : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt cA0 cA0 cCC0).length
    (elim.crossM (units.stackedRaise cCC0)
      ((pairsAt cA0 cA0 cCC0).map HVec.coords))) 0
private def cP0 : List (BPair × HVec × HVec) :=
  pairFam cA0 cA0 cCC0 cK0
private def cX0 : HVec := ground.getAt (⟨[], []⟩ : HVec) cA0 0
private def cX1 : HVec := ground.getAt (⟨[], []⟩ : HVec) cA0 1

/-! The grid's shape at the fixture: three pairs, the display the
factor enumeration's own map, and the kernel datum off the unit
family — `hker` a live read. -/

example : (pairsAt cA0 cA0 cCC0).length = 3 := by decide +kernel
example : pairsAt cA0 cA0 cCC0
    = (blockcount.pairIdx cA0 (fun v => v) cA0 cCC0).map
      (fun t => tensorH t.1 t.2) := by decide +kernel
example : cX0.content = [2, 0] := by decide +kernel
example : cX1.content = [1, 1] := by decide +kernel
example : ¬ poly.unitTail cK0 := by decide +kernel
example : ¬ (units.stackedRaise cCC0) = [] := by decide +kernel

/-! The value's equivariance at the fixture's members, decided at
both letter orders, with the raising instance read through the
theorem — the membership-free binders discharged by decision. -/

/-- The fixture discriminates: neither read is the unit family. -/
example : ¬ poly.unitTail (act 0 1 (pairVal cP0 cX0 [0, 2])).coords
    := by decide +kernel
example : ¬ poly.unitTail
    (pairVal cP0 (dact 0 1 cX0) [1, 1]).coords := by decide +kernel
example : ¬ poly.unitTail (act 0 1 (pairVal cP0 cX1 [1, 1])).coords
    := by decide +kernel

example : poly.oneValue (pairVal cP0 (dact 0 1 cX0) [1, 1]).coords
    (act 0 1 (pairVal cP0 cX0 [0, 2])).coords := by decide +kernel
example : poly.oneValue (pairVal cP0 (dact 1 0 cX1) [0, 2]).coords
    (act 1 0 (pairVal cP0 cX1 [1, 1])).coords := by decide +kernel
example : poly.oneValue (pairVal cP0 (dact 0 1 cX1) [2, 0]).coords
    (act 0 1 (pairVal cP0 cX1 [1, 1])).coords := by decide +kernel

example : poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 0 1 cX0)
      (moveAt 0 1 [0, 2])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX0 [0, 2])).coords :=
  pairVal_equiv cA0 cA0 cCC0 2 2 cK0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 1 (by decide +kernel) (by decide +kernel) cX0
    (by decide +kernel) (by decide +kernel) [0, 2] (by decide +kernel) (by decide +kernel)

example : poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 0 1 cX1)
      (moveAt 0 1 [1, 1])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX1 [1, 1])).coords :=
  pairVal_equiv cA0 cA0 cCC0 2 2 cK0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 1 (by decide +kernel) (by decide +kernel) cX1
    (by decide +kernel) (by decide +kernel) [1, 1] (by decide +kernel) (by decide +kernel)

/-! The non-adjacent raising: three letters at the fused content
`[1,1,1]`, the first list the three degree-one members and the
second the six degree-two ones, the letter pair `(0,2)` — the gap
case's own instance, decided and routed, with both reads pinned off
the unit family so the instance discriminates. -/

private def cN1 : BPair := BPair.ofNat 1
private def cM1 : BPair := (BPair.ofNat 1).swap
private def cAC : List HVec :=
  [⟨[0, 0, 1], [cN1]⟩, ⟨[0, 1, 0], [cN1]⟩, ⟨[1, 0, 0], [cN1]⟩]
private def cBC : List HVec :=
  [⟨[0, 0, 2], [cN1]⟩, ⟨[0, 1, 1], [cN1, cM1]⟩, ⟨[0, 2, 0], [cM1]⟩,
   ⟨[1, 0, 1], [cN1, cM1]⟩, ⟨[1, 1, 0], [cM1, cN1]⟩,
   ⟨[2, 0, 0], [cN1]⟩]
private def cCCC : List Nat := [1, 1, 1]
private def cKC : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt cAC cBC cCCC).length
    (elim.crossM (units.stackedRaise cCCC)
      ((pairsAt cAC cBC cCCC).map HVec.coords))) 0
private def cXC : HVec := ground.getAt (⟨[], []⟩ : HVec) cAC 2

example : (pairsAt cAC cBC cCCC).length = 3 := by decide +kernel
example : ¬ cKC = [] := by decide +kernel
example : ¬ poly.unitTail cKC := by decide +kernel
example : cXC.content = [1, 0, 0] := by decide +kernel
example : ∀ v ∈ cAC, ground.sumNat v.content = 1 := by decide +kernel
example : ∀ v ∈ cBC, ground.sumNat v.content = 2 := by decide +kernel
example : ¬ poly.unitTail
    (act 0 2 (pairVal (pairFam cAC cBC cCCC cKC) cXC
      [0, 1, 1])).coords := by decide +kernel
example : ¬ poly.unitTail
    (pairVal (pairFam cAC cBC cCCC cKC) (dact 0 2 cXC)
      (moveAt 0 2 [0, 1, 1])).coords := by decide +kernel

example : poly.oneValue
    (pairVal (pairFam cAC cBC cCCC cKC) (dact 0 2 cXC)
      (moveAt 0 2 [0, 1, 1])).coords
    (act 0 2
      (pairVal (pairFam cAC cBC cCCC cKC) cXC [0, 1, 1])).coords :=
  by decide +kernel
example : poly.oneValue
    (pairVal (pairFam cAC cBC cCCC cKC) (dact 0 2 cXC)
      (moveAt 0 2 [0, 1, 1])).coords
    (act 0 2
      (pairVal (pairFam cAC cBC cCCC cKC) cXC [0, 1, 1])).coords :=
  pairVal_equiv cAC cBC cCCC 3 1 cKC (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 2 (by decide +kernel) (by decide +kernel) cXC
    (by decide +kernel) (by decide +kernel) [0, 1, 1] (by decide +kernel) (by decide +kernel)

/-! The raising direction's binder `hpq` is load-bearing: at the
block span `[1,1]` and the fused content `[4,2]` the lowering pair
`(1,0)` refuses past every occupancy read, with every co-binder of
the theorem held there and the raising direction surviving at the
same data.  The same refusal isolates the lowering theorem's
singlet frame `hcc`: no power makes `[4,2]` a full column, every
other binder of `pairVal_equiv_lower` holds at this data, and the
moved read refuses — the frame's own pin. -/

private def cA1 : List HVec := blockSpan [1, 1]
private def cCC1 : List Nat := [4, 2]
private def cK1 : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt cA1 cA1 cCC1).length
    (elim.crossM (units.stackedRaise cCC1)
      ((pairsAt cA1 cA1 cCC1).map HVec.coords))) 0
private def cZ0 : HVec := ground.getAt (⟨[], []⟩ : HVec) cA1 0

example : ¬ (units.stackedRaise cCC1) = [] := by decide +kernel
example : ¬ cK1 = [] := by decide +kernel
example : ∀ v ∈ cA1, sized v := by decide +kernel
example : ∀ v ∈ cA1, v.content.length = 2 := by decide +kernel
example : ∀ v ∈ cA1, ground.sumNat v.content = 3 := by decide +kernel
example : cK1.length = (pairsAt cA1 cA1 cCC1).length := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise cCC1)
      ((pairsAt cA1 cA1 cCC1).map HVec.coords)) cK1) := by decide +kernel
example : sized cZ0 := by decide +kernel
example : cZ0.content = [2, 1] := by decide +kernel
example : List.zipWith (fun u w => u + w) cZ0.content [2, 1]
    = cCC1 := by decide +kernel
example : ([2, 1] : List Nat).length = 2 := by decide +kernel

/-- Both occupancy reads hold at the lowering pair, so no occupancy
binder recovers it. -/
example : 0 < ground.getAt 0 cZ0.content 1 := by decide +kernel
example : 0 < ground.getAt 0 ([2, 1] : List Nat) 0 := by decide +kernel

/-- The fused content is a full column at no power. -/
example : ∀ m : Nat, ¬ cCC1 = List.replicate 2 m := by
  intro m h
  have h0 : ground.getAt 0 cCC1 0 = m := by rw [h]; rfl
  have h1 : ground.getAt 0 cCC1 1 = m := by rw [h]; rfl
  exact absurd ((show (4 : Nat) = m from h0).trans
    (show (2 : Nat) = m from h1).symm) (by decide +kernel)

example : ¬ poly.oneValue
    (pairVal (pairFam cA1 cA1 cCC1 cK1) (dact 1 0 cZ0)
      (moveAt 1 0 [2, 1])).coords
    (act 1 0
      (pairVal (pairFam cA1 cA1 cCC1 cK1) cZ0 [2, 1])).coords :=
  by decide +kernel

example : poly.oneValue
    (pairVal (pairFam cA1 cA1 cCC1 cK1) (dact 0 1 cZ0)
      (moveAt 0 1 [2, 1])).coords
    (act 0 1
      (pairVal (pairFam cA1 cA1 cCC1 cK1) cZ0 [2, 1])).coords :=
  by decide +kernel

/-! The one-degree frame `hdegA` is load-bearing: at a grid whose
first factors realize two degrees the pin refuses in the raising
direction, every co-binder held — the minimal such grid, two
letters at the fused content `[1,1]` with one first factor of
degree zero beside one of degree one, and the one-degree twin at
the same content surviving. -/

private def cY0 : HVec := ⟨[0, 0], [BPair.ofNat 1]⟩
private def cY1 : HVec := ⟨[1, 0], [BPair.ofNat 1]⟩
private def cW0 : HVec := ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩
private def cW1 : HVec := ⟨[0, 1], [BPair.ofNat 1]⟩
private def cAD : List HVec := [cY0, cY1]
private def cBD : List HVec := [cW0, cW1]
private def cCCD : List Nat := [1, 1]
private def cCD : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]

example : (blockcount.pairIdx cAD (fun v => v) cBD cCCD).map
    (fun t => ground.sumNat t.1.content) = [0, 1] := by decide +kernel
example : ¬ ground.sumNat cY0.content = ground.sumNat cY1.content :=
  by decide +kernel
example : ¬ poly.unitTail cCD := by decide +kernel
example : ∀ v ∈ cAD, sized v := by decide +kernel
example : ∀ v ∈ cBD, sized v := by decide +kernel
example : ∀ v ∈ cAD, v.content.length = 2 := by decide +kernel
example : ∀ v ∈ cBD, v.content.length = 2 := by decide +kernel
example : cCD.length = (pairsAt cAD cBD cCCD).length := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise cCCD)
      ((pairsAt cAD cBD cCCD).map HVec.coords)) cCD) := by decide +kernel
example : cY1 ∈ cAD :=
  ground.mem_getAt (⟨[], []⟩ : HVec) cAD 1 (by decide +kernel)

example : ¬ poly.oneValue
    (pairVal (pairFam cAD cBD cCCD cCD) (dact 0 1 cY1)
      (moveAt 0 1 [0, 1])).coords
    (act 0 1
      (pairVal (pairFam cAD cBD cCCD cCD) cY1 [0, 1])).coords :=
  by decide +kernel

private def cU1 : HVec := ⟨[0, 1], [BPair.ofNat 1]⟩
private def cAE : List HVec := [cY1, cU1]
private def cKE : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt cAE cAE cCCD).length
    (elim.crossM (units.stackedRaise cCCD)
      ((pairsAt cAE cAE cCCD).map HVec.coords))) 0

example : (blockcount.pairIdx cAE (fun v => v) cAE cCCD).map
    (fun t => ground.sumNat t.1.content) = [1, 1] := by decide +kernel
example : poly.oneValue
    (pairVal (pairFam cAE cAE cCCD cKE) (dact 0 1 cY1)
      (moveAt 0 1 [0, 1])).coords
    (act 0 1
      (pairVal (pairFam cAE cAE cCCD cKE) cY1 [0, 1])).coords :=
  by decide +kernel

/-! The lowering direction's own isolating refusals at the standing
fixtures: the one-degree binder at the mixed-degree family, the
kernel read at the forged coefficients, the output width at the
long content, and the second list's width at the wide member —
each the moved read's refusal at the exchanged letters. -/

example : ¬ poly.oneValue
    (pairVal (pairFam cAD cBD cCCD cCD) (dact 1 0 cY0)
      (moveAt 1 0 [1, 1])).coords
    (act 1 0
      (pairVal (pairFam cAD cBD cCCD cCD) cY0 [1, 1])).coords :=
  by decide +kernel

example : ¬ poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 1 0 cX1)
      (moveAt 1 0 [1, 1, 1])).coords
    (act 1 0
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX1 [1, 1, 1])).coords :=
  by decide +kernel

/-! The output content's width binder `hocw` is load-bearing: `hoc`
is a `zipWith`, truncating at the fused content's width, so it pins
only the first `d` entries of the output content.  At the fixture's
own data with the output content padded by an occupied letter every
other binder holds and the pin refuses; padding by a vacant letter
leaves the enumeration fixed and the read survives, so the refusal
is the occupied padding's — the width read's own. -/

example : List.zipWith (fun u w => u + w) cX0.content [0, 2, 1]
    = cCC0 := by decide +kernel
example : ¬ ([0, 2, 1] : List Nat).length = 2 := by decide +kernel
example : ¬ ground.sumNat cX0.content + ground.sumNat [0, 2, 1]
    = ground.sumNat cCC0 := by decide +kernel

example : ¬ poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 0 1 cX0)
      (moveAt 0 1 [0, 2, 1])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX0 [0, 2, 1])).coords :=
  by decide +kernel
example : ¬ poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 0 1 cX1)
      (moveAt 0 1 [1, 1, 1])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX1 [1, 1, 1])).coords :=
  by decide +kernel

example : List.zipWith (fun u w => u + w) cX0.content [0, 2, 0]
    = cCC0 := by decide +kernel
example : poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 0 1 cX0)
      (moveAt 0 1 [0, 2, 0])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX0 [0, 2, 0])).coords :=
  by decide +kernel
example : poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cK0) (dact 0 1 cX1)
      (moveAt 0 1 [1, 1, 0])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cK0) cX1 [1, 1, 0])).coords :=
  by decide +kernel

/-! The kernel binder is load-bearing: two independent off-kernel
coefficient families at the committed span each satisfy the width
read, each refuse the stacked raising's kernel read, and each
refuses the moved-value identity. -/

private def cBadC : List BPair := [BPair.ofNat 1, BPair.unit, BPair.unit]
private def cBadC2 : List BPair := [BPair.unit, BPair.ofNat 1, BPair.unit]

example : ¬ poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cBadC) (dact 1 0 cX1)
      (moveAt 1 0 [1, 1])).coords
    (act 1 0
      (pairVal (pairFam cA0 cA0 cCC0 cBadC) cX1 [1, 1])).coords :=
  by decide +kernel

example : cBadC.length = (pairsAt cA0 cA0 cCC0).length := by decide +kernel
example : ¬ poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise cCC0)
      ((pairsAt cA0 cA0 cCC0).map HVec.coords)) cBadC) := by decide +kernel
example : ¬ poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cBadC) (dact 0 1 cX0)
      (moveAt 0 1 [0, 2])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cBadC) cX0 [0, 2])).coords
    := by decide +kernel
example : ¬ poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise cCC0)
      ((pairsAt cA0 cA0 cCC0).map HVec.coords)) cBadC2) := by decide +kernel
example : ¬ poly.oneValue
    (pairVal (pairFam cA0 cA0 cCC0 cBadC2) (dact 0 1 cX0)
      (moveAt 0 1 [0, 2])).coords
    (act 0 1
      (pairVal (pairFam cA0 cA0 cCC0 cBadC2) cX0 [0, 2])).coords
    := by decide +kernel

/-! The second list's width binder is load-bearing: a member past
the width passes the grid's truncating guard while its coordinates
enumerate a longer family, and the identity refuses at the member
argument whose slots reach it — with the first member's instance
surviving at the same lists, the isolation the width's own. -/

private def cAW : List HVec :=
  [⟨[1, 0], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩]
private def cBW : List HVec :=
  [⟨[0, 1, 7], [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
      BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
      BPair.ofNat 1]⟩,
   ⟨[1, 0], [BPair.ofNat 1]⟩]
private def cCCW : List Nat := [1, 1]
private def cKW : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt cAW cBW cCCW).length
    (elim.crossM (units.stackedRaise cCCW)
      ((pairsAt cAW cBW cCCW).map HVec.coords))) 0

example : ¬ (∀ v ∈ cBW, v.content.length = 2) := by decide +kernel
example : ¬ poly.unitTail cKW := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise cCCW)
      ((pairsAt cAW cBW cCCW).map HVec.coords)) cKW) := by decide +kernel
example : ¬ poly.oneValue
    (pairVal (pairFam cAW cBW cCCW cKW)
      (dact 0 1 (ground.getAt (⟨[], []⟩ : HVec) cAW 0))
      (moveAt 0 1 [0, 1])).coords
    (act 0 1 (pairVal (pairFam cAW cBW cCCW cKW)
      (ground.getAt (⟨[], []⟩ : HVec) cAW 0) [0, 1])).coords
    := by decide +kernel
example : poly.oneValue
    (pairVal (pairFam cAW cBW cCCW cKW)
      (dact 0 1 (ground.getAt (⟨[], []⟩ : HVec) cAW 1))
      (moveAt 0 1 [1, 0])).coords
    (act 0 1 (pairVal (pairFam cAW cBW cCCW cKW)
      (ground.getAt (⟨[], []⟩ : HVec) cAW 1) [1, 0])).coords
    := by decide +kernel
example : ¬ poly.oneValue
    (pairVal (pairFam cAW cBW cCCW cKW)
      (dact 1 0 (ground.getAt (⟨[], []⟩ : HVec) cAW 1))
      (moveAt 1 0 [1, 0])).coords
    (act 1 0 (pairVal (pairFam cAW cBW cCCW cKW)
      (ground.getAt (⟨[], []⟩ : HVec) cAW 1) [1, 0])).coords
    := by decide +kernel

/-! `lem:dualread`(iii)'s lowering mirror at the singlet frame: at
the fused content `[1,1]`, the two-letter full column at power one,
the complementary grid's value map is equivariant at the lowering
direction as well, read through `pairVal_equiv_lower` at the grid's
own kernel datum — the letter pair `(0,1)` taken at the lowering,
with both reads pinned off the unit family so the instance
discriminates. -/

example : cCCD = List.replicate 2 1 := by decide +kernel
example : (pairsAt cAE cAE cCCD).length = 2 := by decide +kernel
example : ¬ poly.unitTail cKE := by decide +kernel
example : cU1.content = [0, 1] := by decide +kernel
example : List.zipWith (fun u w => u + w) cU1.content [1, 0]
    = cCCD := by decide +kernel
example : 0 < ground.getAt 0 ([1, 0] : List Nat) 0 := by decide +kernel

/-- The fixture discriminates: neither read is the unit family. -/
example : ¬ poly.unitTail
    (act 1 0 (pairVal (pairFam cAE cAE cCCD cKE) cU1 [1, 0])).coords
    := by decide +kernel
example : ¬ poly.unitTail
    (pairVal (pairFam cAE cAE cCCD cKE) (dact 1 0 cU1)
      (moveAt 1 0 [1, 0])).coords := by decide +kernel

example : poly.oneValue
    (pairVal (pairFam cAE cAE cCCD cKE) (dact 1 0 cU1)
      (moveAt 1 0 [1, 0])).coords
    (act 1 0
      (pairVal (pairFam cAE cAE cCCD cKE) cU1 [1, 0])).coords :=
  pairVal_equiv_lower cAE cAE cCCD 2 1 1 cKE (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 1 (by decide +kernel) (by decide +kernel) cU1
    (by decide +kernel) (by decide +kernel) [1, 0] (by decide +kernel) (by decide +kernel)

/-! `lem:dualread`(iii)'s solve-back at the complementary grid: the
theorem's route at two independent singletons of complementary
content joining the fused content, with the unit family read back,
and every load-bearing binder isolated at its committed refusal.
The value binder quantifies the output content at the join, so a
fixture discharges it in one of the two ways the statement allows:
at the unit family every coefficient reads the sum's unit and the
combination does at every output content, and at the vacant width
`d = 0` the output content is the vacant list outright and the read
decides.  The refusals are the two groups' independence (a repeated
first member and its mirror at the second, the coefficients the
balance pair and its partner), the value read itself (independent
data with one value off the unit tail), the second list's width (a
member at content length `d + 1` whose truncated join passes the
grid's guard), and the family's shape (coefficients past the pair
list at a junk tail). -/

private def cASo : List HVec := [cY1]
private def cBSo : List HVec := [cU1]
private def cUSo : List BPair := [BPair.unit]
private def cHSo : List BPair := [BPair.ofNat 1]

example : (pairsAt cASo cBSo cCCD).length = 1 := by decide +kernel
example : ∀ w ∈ cASo, sized w := by decide +kernel
example : ∀ w ∈ cBSo, sized w := by decide +kernel
example : ∀ v ∈ cASo, v.content.length = 2 := by decide +kernel
example : ∀ w ∈ cBSo, w.content.length = 2 := by decide +kernel
example : cCCD.length = 2 := by decide +kernel
example : blockcount.indepAll cASo := by decide +kernel
example : blockcount.indepAll cBSo := by decide +kernel
example : cUSo.length = (pairsAt cASo cBSo cCCD).length := by decide +kernel
example : List.zipWith (fun u w => u + w) cY1.content cU1.content
    = cCCD := by decide +kernel
example : poly.unitTail cUSo := by decide +kernel

example : poly.unitTail cUSo :=
  pairSolve cASo cBSo cCCD cUSo 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      have hco : ∀ y ∈ cASo, poly.unitTail
          (((pairFam cASo cBSo cCCD cUSo).filter
            (fun t => t.2.1.content == y.content)).map
            (fun t => t.1 * elim.dotP t.2.1.coords y.coords)) := by
        decide +kernel
      exact fun y hy oc _ _ =>
        elim.unitTail_combo_of (places.monomialsAt oc).length _ _
          (hco y hy))

/-! The value read is load-bearing, not vacuous: at the same
independent singletons the coefficient off the sum's unit refuses
the unit family, the join at the complementary content is occupied,
and the value there reads off the unit tail — the hypothesis
refused with every co-binder held. -/

example : cHSo.length = (pairsAt cASo cBSo cCCD).length := by decide +kernel
example : ¬ poly.unitTail cHSo := by decide +kernel
example : cY1 ∈ cASo :=
  ground.mem_getAt (⟨[], []⟩ : HVec) cASo 0 (by decide +kernel)
example : ([0, 1] : List Nat).length = 2 := by decide +kernel
example : List.zipWith (fun u w => u + w) cY1.content [0, 1]
    = cCCD := by decide +kernel
example : ¬ poly.unitTail
    (pairVal (pairFam cASo cBSo cCCD cHSo) cY1 [0, 1]).coords :=
  by decide +kernel
example : ¬ (∀ y ∈ cASo, ∀ oc : List Nat, oc.length = 2 →
    List.zipWith (fun u w => u + w) y.content oc = cCCD →
    poly.unitTail (pairVal (pairFam cASo cBSo cCCD cHSo) y oc).coords) :=
  fun h =>
    (by decide +kernel : ¬ poly.unitTail
        (pairVal (pairFam cASo cBSo cCCD cHSo) cY1 [0, 1]).coords)
      (h cY1 (ground.mem_getAt (⟨[], []⟩ : HVec) cASo 0 (by decide +kernel))
        [0, 1] (by decide +kernel) (by decide +kernel))

/-! The remaining binders are isolated at the vacant width, where
the output content is the vacant list and every read decides: one
letter-free member of coordinate one, its repetition, and the
member at content length one whose join with a letter-free content
truncates to the vacant fused content. -/

private def vSo : HVec := ⟨[], [BPair.ofNat 1]⟩
private def wSo : HVec := ⟨[3], [BPair.ofNat 1]⟩
private def cCSo : List Nat := []
private def cPSo : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]
private def cLSo : List BPair := [BPair.unit, BPair.ofNat 1]
private def cRSo : List HVec := [vSo, vSo]
private def cOSo : List HVec := [vSo]
private def cWSo : List HVec := [vSo, wSo]

example : sized vSo := by decide +kernel
example : sized wSo := by decide +kernel
example : vSo.content.length = 0 := by decide +kernel
example : cCSo.length = 0 := by decide +kernel
example : ¬ poly.unitTail cPSo := by decide +kernel
example : ¬ poly.unitTail cLSo := by decide +kernel
example : blockcount.indepAll cOSo := by decide +kernel

/-! The first list's independence: at a repeated first member the
value reads the unit tail at every listed member — the two
coefficients the balance pair and its partner against one row —
while the coefficients refuse the unit family and every co-binder
holds. -/

example : ¬ blockcount.indepAll cRSo := by decide +kernel
example : ∀ w ∈ cRSo, sized w := by decide +kernel
example : ∀ v ∈ cRSo, v.content.length = 0 := by decide +kernel
example : cPSo.length = (pairsAt cRSo cOSo cCSo).length := by decide +kernel
example : ∀ y ∈ cRSo, ∀ oc : List Nat, oc.length = 0 →
    List.zipWith (fun u w => u + w) y.content oc = cCSo →
    poly.unitTail (pairVal (pairFam cRSo cOSo cCSo cPSo) y oc).coords := by
  have hv : ∀ y ∈ cRSo, poly.unitTail
      (pairVal (pairFam cRSo cOSo cCSo cPSo) y []).coords := by decide +kernel
  intro y hy oc hoc _
  rw [ground.nil_of_length_zero oc hoc]
  exact hv y hy

/-! The second list's independence: the same forge mirrored at the
second list, the same coefficients refused. -/

example : cPSo.length = (pairsAt cOSo cRSo cCSo).length := by decide +kernel
example : ∀ y ∈ cOSo, ∀ oc : List Nat, oc.length = 0 →
    List.zipWith (fun u w => u + w) y.content oc = cCSo →
    poly.unitTail (pairVal (pairFam cOSo cRSo cCSo cPSo) y oc).coords := by
  have hv : ∀ y ∈ cOSo, poly.unitTail
      (pairVal (pairFam cOSo cRSo cCSo cPSo) y []).coords := by decide +kernel
  intro y hy oc hoc _
  rw [ground.nil_of_length_zero oc hoc]
  exact hv y hy

/-! The second list's width: a member at content length `d + 1`
joins a letter-free first content at the truncated vacant read, so
it passes the grid's guard and enters the value beside the member
at the stated width, its own content group independent and its
coordinates the same row — every co-binder held, the width read
alone refused, and the coefficients off the unit family. -/

example : blockcount.indepAll cWSo := by decide +kernel
example : ∀ w ∈ cWSo, sized w := by decide +kernel
example : ¬ (∀ w ∈ cWSo, w.content.length = 0) := by decide +kernel
example : wSo.content.length = 1 := by decide +kernel
example : List.zipWith (fun u w => u + w) vSo.content wSo.content
    = cCSo := by decide +kernel
example : cPSo.length = (pairsAt cOSo cWSo cCSo).length := by decide +kernel
example : ∀ y ∈ cOSo, ∀ oc : List Nat, oc.length = 0 →
    List.zipWith (fun u w => u + w) y.content oc = cCSo →
    poly.unitTail (pairVal (pairFam cOSo cWSo cCSo cPSo) y oc).coords := by
  have hv : ∀ y ∈ cOSo, poly.unitTail
      (pairVal (pairFam cOSo cWSo cCSo cPSo) y []).coords := by decide +kernel
  intro y hy oc hoc _
  rw [ground.nil_of_length_zero oc hoc]
  exact hv y hy

/-! The family's shape: coefficients past the pair list carry a
junk tail the grid never reads, so the value stays at the unit tail
while the family refuses the unit family. -/

example : ¬ cLSo.length = (pairsAt cOSo cOSo cCSo).length := by decide +kernel
example : (pairsAt cOSo cOSo cCSo).length = 1 := by decide +kernel
example : ∀ y ∈ cOSo, ∀ oc : List Nat, oc.length = 0 →
    List.zipWith (fun u w => u + w) y.content oc = cCSo →
    poly.unitTail (pairVal (pairFam cOSo cOSo cCSo cLSo) y oc).coords := by
  have hv : ∀ y ∈ cOSo, poly.unitTail
      (pairVal (pairFam cOSo cOSo cCSo cLSo) y []).coords := by decide +kernel
  intro y hy oc hoc _
  rw [ground.nil_of_length_zero oc hoc]
  exact hv y hy

/-! The two independence binders at an occupied width: the repeated
member at width two, the output content determined by the join's
left cancellation, and the value the balance pair's cancellation —
the front end's content split exercised off the vacant width. -/

private def dA2 : List HVec :=
  [⟨[1, 0], [BPair.ofNat 1]⟩, ⟨[1, 0], [BPair.ofNat 1]⟩]
private def dB2 : List HVec := [⟨[0, 1], [BPair.ofNat 1]⟩]
private def dB2r : List HVec :=
  [⟨[0, 1], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩]
private def dA2s : List HVec := [⟨[1, 0], [BPair.ofNat 1]⟩]
private def dC2 : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]

example : ¬ blockcount.indepAll dA2 := by decide +kernel
example : blockcount.indepAll dB2 := by decide +kernel
example : ∀ v ∈ dA2, v.content.length = 2 := by decide +kernel
example : ∀ w ∈ dB2, w.content.length = 2 := by decide +kernel
example : dC2.length = (pairsAt dA2 dB2 [1, 1]).length := by decide +kernel
example : ¬ poly.unitTail dC2 := by decide +kernel
example : ∀ y ∈ dA2, ∀ oc : List Nat, oc.length = 2 →
    List.zipWith (fun u w => u + w) y.content oc = [1, 1] →
    poly.unitTail (pairVal (pairFam dA2 dB2 [1, 1] dC2) y oc).coords := by
  intro y hy oc hlen hjoin
  have hyc : y.content = [1, 0] :=
    (show ∀ z ∈ dA2, z.content = [1, 0] by decide +kernel) y hy
  rw [hyc] at hjoin
  have hoc : oc = [0, 1] :=
    blockcount.zipWith_add_cancelL [1, 0] oc [0, 1] 2 rfl hlen rfl
      (hjoin.trans (show ([1, 1] : List Nat)
        = List.zipWith (fun u w => u + w) [1, 0] [0, 1] from rfl))
  rw [hoc]
  exact (show ∀ z ∈ dA2, poly.unitTail
    (pairVal (pairFam dA2 dB2 [1, 1] dC2) z [0, 1]).coords
    by decide +kernel) y hy

example : ¬ blockcount.indepAll dB2r := by decide +kernel
example : blockcount.indepAll dA2s := by decide +kernel
example : ∀ v ∈ dA2s, v.content.length = 2 := by decide +kernel
example : ∀ w ∈ dB2r, w.content.length = 2 := by decide +kernel
example : dC2.length = (pairsAt dA2s dB2r [1, 1]).length := by decide +kernel
example : ∀ y ∈ dA2s, ∀ oc : List Nat, oc.length = 2 →
    List.zipWith (fun u w => u + w) y.content oc = [1, 1] →
    poly.unitTail (pairVal (pairFam dA2s dB2r [1, 1] dC2) y oc).coords := by
  intro y hy oc hlen hjoin
  have hyc : y.content = [1, 0] :=
    (show ∀ z ∈ dA2s, z.content = [1, 0] by decide +kernel) y hy
  rw [hyc] at hjoin
  have hoc : oc = [0, 1] :=
    blockcount.zipWith_add_cancelL [1, 0] oc [0, 1] 2 rfl hlen rfl
      (hjoin.trans (show ([1, 1] : List Nat)
        = List.zipWith (fun u w => u + w) [1, 0] [0, 1] from rfl))
  rw [hoc]
  exact (show ∀ z ∈ dA2s, poly.unitTail
    (pairVal (pairFam dA2s dB2r [1, 1] dC2) z [0, 1]).coords
    by decide +kernel) y hy

/-! `lem:dualread`(iii)'s off-join arm at the value list: the two
blocks' spans at the two-letter full column `[1,1]`, the stated
pair list's kernel datum off the unit family, and the value list's
three reads decided beside their theorem routes — every member
sized and settled inside the second block's span, the list closed
at both letter orders, and the head's group holding a value off the
unit tail with the pair guard's join exact at the member the value
names.  The off-join read's binders refuse at their own committed
instances: the family's own off-unit read (`hoff`) at the unit
family, which satisfies the shape and the kernel read; the kernel
read (`hker`) at an off-unit family of the stated shape sitting off
the kernel, for the head's-group read and for the letter closure;
and the matched width (`hba`) at a second block one letter wider,
where a value sits off the second block's span.  At a family longer
than the pair list (`hc` refused) the tail past the list is never
read and the conclusion holds.  The
mismatched second block sits beside them: at `b = [0,0]` the stated
pair list is vacant, the guard's join refuses at every first-block
member, and the whole existential is refused, `hoff` the binder
that fails.  The three-letter fixture closes the block at the
column `[1,1,1]` with the second block `[0,1,0]`, the kernel one
line there. -/

private def vA2 : List HVec := blockSpan ([1, 0] : Shape)
private def vB2 : List HVec := blockSpan ([1, 0] : Shape)
private def vCC2 : List Nat := List.replicate ([1, 0] : Shape).length 1
private def vK2 : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt vA2 vB2 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords))) 0
private def vL2 : List HVec := valList vA2 vB2 vCC2 vK2

example : vCC2 = [1, 1] := by decide +kernel
example : vA2.map HVec.content = [[1, 0], [0, 1]] := by decide +kernel
example : rowList ([1, 0] : Shape) = [1, 0] := by decide +kernel
example : (pairsAt vA2 vB2 vCC2).length = 2 := by decide +kernel
example : vK2.length = (pairsAt vA2 vB2 vCC2).length := by decide +kernel
example : ¬ poly.unitTail vK2 := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) vK2) := by decide +kernel

/-! The value list's own read: one value per stated member at the
complement of its content. -/

example : vL2.length = 2 := by decide +kernel
example : vL2.map HVec.content = [[0, 1], [1, 0]] := by decide +kernel
example : ground.getAt (⟨[], []⟩ : HVec) vL2 0
    = pairVal (pairFam vA2 vB2 vCC2 vK2)
      (ground.getAt (⟨[], []⟩ : HVec) vA2 0) [0, 1] := by decide +kernel
example : ¬ poly.unitTail (ground.getAt (⟨[], []⟩ : HVec) vL2 0).coords :=
  by decide +kernel
example : ¬ poly.unitTail (ground.getAt (⟨[], []⟩ : HVec) vL2 1).coords :=
  by decide +kernel

/-! Every value sized and settled inside the second block's span,
decided at a member and read through the theorem. -/

example : sized (ground.getAt (⟨[], []⟩ : HVec) vL2 0)
    ∧ settledAt vB2 (ground.getAt (⟨[], []⟩ : HVec) vL2 0) := by decide +kernel
example : settledAt vB2 (ground.getAt (⟨[], []⟩ : HVec) vL2 1) := by decide +kernel
example : ∀ x ∈ vL2, sized x ∧ settledAt vB2 x := by decide +kernel

example : sized (ground.getAt (⟨[], []⟩ : HVec) vL2 0)
    ∧ settledAt (blockSpan ([1, 0] : Shape))
      (ground.getAt (⟨[], []⟩ : HVec) vL2 0) :=
  valList_settled [1, 0] [1, 0] 1 vK2 rfl _
    (ground.mem_getAt (⟨[], []⟩ : HVec) vL2 0 (by decide +kernel))

/-! The list closed at the letters, decided at both orders and read
through the theorem at one member and one pair. -/

example : settledAt vL2 (act 0 1 (ground.getAt (⟨[], []⟩ : HVec) vL2 0)) :=
  by decide +kernel
example : settledAt vL2 (act 1 0 (ground.getAt (⟨[], []⟩ : HVec) vL2 0)) :=
  by decide +kernel
example : settledAt vL2 (act 0 1 (ground.getAt (⟨[], []⟩ : HVec) vL2 1)) :=
  by decide +kernel

example : settledAt (valList (blockSpan ([1, 0] : Shape))
      (blockSpan ([1, 0] : Shape))
      (List.replicate ([1, 0] : Shape).length 1) vK2)
    (act 0 1 (ground.getAt (⟨[], []⟩ : HVec) vL2 0)) :=
  valList_closed [1, 0] [1, 0] 1 vK2 rfl (by decide +kernel) (by decide +kernel) _
    (ground.mem_getAt (⟨[], []⟩ : HVec) vL2 0 (by decide +kernel))
    0 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)

/-! The head's group holds a value off the unit tail: the witness
member's join at the second block's row list and its value's
off-unit read decided, and the existential read through the
theorem. -/

example : (ground.getAt (⟨[], []⟩ : HVec) vA2 1).content = [0, 1] :=
  by decide +kernel
example : List.zipWith (fun u w => u + w)
    (ground.getAt (⟨[], []⟩ : HVec) vA2 1).content
    (rowList ([1, 0] : Shape)) = vCC2 := by decide +kernel
example : ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vK2)
    (ground.getAt (⟨[], []⟩ : HVec) vA2 1)
    (rowList ([1, 0] : Shape))).coords := by decide +kernel

example : ∃ y ∈ vA2, List.zipWith (fun u w => u + w) y.content
      (rowList ([1, 0] : Shape)) = vCC2
    ∧ ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vK2) y
      (rowList ([1, 0] : Shape))).coords := by decide +kernel

example : ∃ y ∈ blockSpan ([1, 0] : Shape),
    List.zipWith (fun u w => u + w) y.content (rowList ([1, 0] : Shape))
        = List.replicate ([1, 0] : Shape).length 1
      ∧ ¬ poly.unitTail
        (pairVal (pairFam (blockSpan ([1, 0] : Shape))
          (blockSpan ([1, 0] : Shape))
          (List.replicate ([1, 0] : Shape).length 1) vK2) y
          (rowList ([1, 0] : Shape))).coords :=
  valOff_head [1, 0] [1, 0] 1 vK2 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The family's off-unit read is load-bearing: the unit family
carries the stated shape and sits in the kernel, and the off-join
conclusion is refused there. -/

private def vU2 : List BPair := [BPair.unit, BPair.unit]

example : poly.unitTail vU2 := by decide +kernel
example : vU2.length = (pairsAt vA2 vB2 vCC2).length := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) vU2) := by decide +kernel
example : ¬ ∃ y ∈ vA2, List.zipWith (fun u w => u + w) y.content
      (rowList ([1, 0] : Shape)) = vCC2
    ∧ ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vU2) y
      (rowList ([1, 0] : Shape))).coords := by decide +kernel

/-! The kernel read is load-bearing: an off-unit family of the
stated shape sitting off the stacked raisings' kernel refuses the
off-join conclusion. -/

private def vOff2 : List BPair := [BPair.ofNat 1, BPair.unit]

example : ¬ poly.unitTail vOff2 := by decide +kernel
example : vOff2.length = (pairsAt vA2 vB2 vCC2).length := by decide +kernel
example : ¬ poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) vOff2) := by decide +kernel
example : ¬ ∃ y ∈ vA2, List.zipWith (fun u w => u + w) y.content
      (rowList ([1, 0] : Shape)) = vCC2
    ∧ ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vOff2) y
      (rowList ([1, 0] : Shape))).coords := by decide +kernel

/-! A family longer than the stated pair list: the tail past the
list is never read, so the kernel read and the off-unit read hold
with the shape read refused, and the conclusion holds. -/

private def vLong2 : List BPair := vK2 ++ [BPair.ofNat 1]

example : ¬ vLong2.length = (pairsAt vA2 vB2 vCC2).length := by decide +kernel
example : ¬ poly.unitTail vLong2 := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) vLong2) := by decide +kernel
example : ∃ y ∈ vA2, List.zipWith (fun u w => u + w) y.content
      (rowList ([1, 0] : Shape)) = vCC2
    ∧ ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vLong2) y
      (rowList ([1, 0] : Shape))).coords := by decide +kernel

/-! The mismatched second block: at `b = [0,0]` no first-block
content joins the row list to the full columns, the stated pair
list is vacant, and the off-join conclusion is refused outright —
the family there is the vacant one and the off-unit read is the
binder that fails. -/

private def vB0 : List HVec := blockSpan ([0, 0] : Shape)

example : rowList ([0, 0] : Shape) = [0, 0] := by decide +kernel
example : (pairsAt vA2 vB0 vCC2).length = 0 := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w)
    (ground.getAt (⟨[], []⟩ : HVec) vA2 1).content
    (rowList ([0, 0] : Shape)) = vCC2 := by decide +kernel
example : poly.unitTail ([] : List BPair) := by decide +kernel
example : ¬ ∃ y ∈ vA2, List.zipWith (fun u w => u + w) y.content
      (rowList ([0, 0] : Shape)) = vCC2
    ∧ ¬ poly.unitTail (pairVal (pairFam vA2 vB0 vCC2 []) y
      (rowList ([0, 0] : Shape))).coords := by decide +kernel

/-! The three-letter fixture at the full column `[1,1,1]`: the
first block `[1,0,0]` against the second `[0,1,0]`, the stated pair
list of three tensors with the kernel one line, the value list's
three complements, and the three reads decided with the off-join
arm read through the theorem. -/

private def vA3 : List HVec := blockSpan ([1, 0, 0] : Shape)
private def vB3 : List HVec := blockSpan ([0, 1, 0] : Shape)
private def vCC3 : List Nat := List.replicate ([1, 0, 0] : Shape).length 1
private def vK3 : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt vA3 vB3 vCC3).length
    (elim.crossM (units.stackedRaise vCC3)
      ((pairsAt vA3 vB3 vCC3).map HVec.coords))) 0
private def vL3 : List HVec := valList vA3 vB3 vCC3 vK3

example : (pairsAt vA3 vB3 vCC3).length = 3 := by decide +kernel
example : vK3.length = (pairsAt vA3 vB3 vCC3).length := by decide +kernel
example : ¬ poly.unitTail vK3 := by decide +kernel
example : poly.unitTail (elim.matVec
    (elim.crossM (units.stackedRaise vCC3)
      ((pairsAt vA3 vB3 vCC3).map HVec.coords)) vK3) := by decide +kernel
example : rowList ([0, 1, 0] : Shape) = [1, 1, 0] := by decide +kernel
example : vL3.map HVec.content = [[0, 1, 1], [1, 0, 1], [1, 1, 0]] :=
  by decide +kernel
example : ∀ x ∈ vL3, sized x ∧ settledAt vB3 x := by decide +kernel
example : settledAt vL3 (act 0 1 (ground.getAt (⟨[], []⟩ : HVec) vL3 0)) :=
  by decide +kernel
example : settledAt vL3 (act 2 1 (ground.getAt (⟨[], []⟩ : HVec) vL3 2)) :=
  by decide +kernel

example : settledAt (valList (blockSpan ([1, 0, 0] : Shape))
      (blockSpan ([0, 1, 0] : Shape))
      (List.replicate ([1, 0, 0] : Shape).length 1) vK3)
    (act 0 1 (ground.getAt (⟨[], []⟩ : HVec) vL3 0)) :=
  valList_closed [1, 0, 0] [0, 1, 0] 1 vK3 rfl (by decide +kernel) (by decide +kernel) _
    (ground.mem_getAt (⟨[], []⟩ : HVec) vL3 0 (by decide +kernel))
    0 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)

example : ∃ y ∈ blockSpan ([1, 0, 0] : Shape),
    List.zipWith (fun u w => u + w) y.content
        (rowList ([0, 1, 0] : Shape))
        = List.replicate ([1, 0, 0] : Shape).length 1
      ∧ ¬ poly.unitTail
        (pairVal (pairFam (blockSpan ([1, 0, 0] : Shape))
          (blockSpan ([0, 1, 0] : Shape))
          (List.replicate ([1, 0, 0] : Shape).length 1) vK3) y
          (rowList ([0, 1, 0] : Shape))).coords :=
  valOff_head [1, 0, 0] [0, 1, 0] 1 vK3 rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)


/-! `lem:dualread`(iii)'s meet and the off-join arm's conclusion.
The complementary exchange runs at a quadruple over the two-letter
full column `[2,2]`: two exact joins onto it with the first
summands compared, and the comparison read back at the two second
summands.  The three load-bearing binders are isolated at their
own committed refusals — each join in turn, at a quadruple where
that join fails and the exchanged comparison fails with it, and
the comparison itself, at a quadruple where both joins hold, the
comparison fails and the exchanged comparison fails.  The meet
runs at the three-letter full column `[3,3,3]`: the two row lists
`[3,0,0]` and `[3,3,0]` with the two contents at their own lists'
reversals, and the conclusion the second row list against the
first's reversal.  Its two dominance binders are isolated at the
two-letter column `[2,2]`, each at a fixture where that binder
alone fails and the conclusion fails with it.  The off-join arm
closes at the spans: at `a = [1,0]`, `b = [0,0]` and the column
`[1,1]` the guard's join refuses and the kernel dimension decides
to nought, read through the theorem; and at `b = [1,0]` the join
holds, the dimension decides to one, and the conclusion is
refused. -/

example : List.zipWith (fun u w => u + w) [1, 1] [1, 1] = [2, 2] := by decide +kernel
example : List.zipWith (fun u w => u + w) [2, 0] [0, 2] = [2, 2] := by decide +kernel
example : weylchar.domBy [1, 1] [2, 0] := by decide +kernel
example : weylchar.domBy [0, 2] [1, 1] := by decide +kernel

/-! The first join is load-bearing: at `X' = [2,2]` the first join
fails while the second join and the comparison hold, and the
exchanged comparison fails. -/

example : ¬ List.zipWith (fun u w => u + w) [1, 1] [2, 2] = [2, 2] := by decide +kernel
example : ¬ weylchar.domBy [0, 2] [2, 2] := by decide +kernel

/-! The second join is load-bearing: at `Y' = [2,2]` the second
join fails while the first join and the comparison hold, and the
exchanged comparison fails. -/

example : ¬ List.zipWith (fun u w => u + w) [2, 0] [2, 2] = [2, 2] := by decide +kernel
example : ¬ weylchar.domBy [2, 2] [1, 1] := by decide +kernel

/-! The comparison is load-bearing: at the exchanged quadruple both
joins hold, the comparison fails, and the exchanged comparison
fails with it. -/

example : List.zipWith (fun u w => u + w) [2, 0] [0, 2] = [2, 2] := by decide +kernel
example : List.zipWith (fun u w => u + w) [1, 1] [1, 1] = [2, 2] := by decide +kernel
example : ¬ weylchar.domBy [2, 0] [1, 1] := by decide +kernel
example : ¬ weylchar.domBy [1, 1] [0, 2] := by decide +kernel

/-! The meet at the three-letter full column: the two joins, the
two contents at their own lists' reversals, and the second row
list against the first's reversal. -/

example : List.zipWith (fun u w => u + w) [0, 0, 3] [3, 3, 0]
    = List.replicate 3 3 := by decide +kernel
example : List.zipWith (fun u w => u + w) [0, 3, 3] [3, 0, 0]
    = List.replicate 3 3 := by decide +kernel
example : weylchar.domBy ([3, 0, 0] : List Nat).reverse [0, 0, 3] := by decide +kernel
example : weylchar.domBy ([3, 3, 0] : List Nat).reverse [0, 3, 3] := by decide +kernel
example : List.zipWith (fun u w => u + w) [3, 3, 0]
    ([3, 0, 0] : List Nat).reverse = List.replicate 3 3 := by decide +kernel

/-! The first list's floor is load-bearing: at `al = [0,2]`,
`be = [2,0]` both joins hold and the second floor holds, the first
floor fails, and the meet fails with it. -/

example : List.zipWith (fun u w => u + w) [0, 2] [2, 0]
    = List.replicate 2 2 := by decide +kernel
example : List.zipWith (fun u w => u + w) [2, 0] [0, 2]
    = List.replicate 2 2 := by decide +kernel
example : ¬ weylchar.domBy ([0, 2] : List Nat).reverse [0, 2] := by decide +kernel
example : weylchar.domBy ([2, 0] : List Nat).reverse [2, 0] := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w) [2, 0]
    ([0, 2] : List Nat).reverse = List.replicate 2 2 := by decide +kernel

/-! The second list's floor is load-bearing: at the exchanged
fixture both joins hold and the first floor holds, the second floor
fails, and the meet fails with it. -/

example : weylchar.domBy ([2, 0] : List Nat).reverse [2, 0] := by decide +kernel
example : ¬ weylchar.domBy ([0, 2] : List Nat).reverse [0, 2] := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w) [0, 2]
    ([2, 0] : List Nat).reverse = List.replicate 2 2 := by decide +kernel

/-! The off-join arm at the spans: the mismatched second block
`[0,0]` refuses the guard's join and the kernel dimension decides
to nought, read through the theorem. -/

example : ¬ List.zipWith (fun u w => u + w) (rowList ([0, 0] : Shape))
    (rowList ([1, 0] : Shape)).reverse
    = List.replicate ([1, 0] : Shape).length 1 := by decide +kernel

example : elim.kernelDim
    (pairsAt vA2 vB0 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB0 vCC2).map HVec.coords)) = 0 := by decide +kernel

example : elim.kernelDim
    (pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([0, 0] : Shape))
      (List.replicate ([1, 0] : Shape).length 1)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([1, 0] : Shape).length 1))
      ((pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([0, 0] : Shape))
        (List.replicate ([1, 0] : Shape).length 1)).map HVec.coords)) = 0 :=
  ker_null_offJoin [1, 0] [0, 0] 1 rfl (by decide +kernel)

/-! The off-join hypothesis is load-bearing: at `b = [1,0]` the
guard's join holds and the kernel dimension decides to one, the
conclusion refused. -/

example : List.zipWith (fun u w => u + w) (rowList ([1, 0] : Shape))
    (rowList ([1, 0] : Shape)).reverse
    = List.replicate ([1, 0] : Shape).length 1 := by decide +kernel

example : elim.kernelDim (pairsAt vA2 vB2 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) = 1 := by decide +kernel

example : ¬ elim.kernelDim (pairsAt vA2 vB2 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) = 0 := by decide +kernel

/-! `lem:dualread`(iii)'s at-join arm.  The value map's linearity in
its coefficient family runs at the join fixture `a = b = [1,0]`,
`m = 1`: the sum, the scale and the balance partner of the kernel
family read the value's own sum, scale and partner at the first
block's reversal member.  The reversal member's read follows: a
family off the unit tail carries a value off the unit tail there,
the value binder refused at its own instance; the reversal content
is the clause's own site, every member's value off the unit tail at
the join (the complement of each first-block content a second-block
content); and off the join the stated pair list is vacant, the
family the unit one and the conclusion holding with it.  The count
closes at the two join fixtures `a = b = [1,0]`,
`m = 1` and `a = b = [2,0]`, `m = 2`, the dimension deciding to one
at each and the theorem read beside it. -/

private def vG2 : HVec := ground.getAt (⟨[], []⟩ : HVec) vA2 1
private def vK2s : List BPair := elim.vecScale (BPair.ofNat 2) vK2

example : vG2.content = (rowList ([1, 0] : Shape)).reverse := by decide +kernel
example : 1 < vA2.length := by decide +kernel
example : vK2s.length = (pairsAt vA2 vB2 vCC2).length := by decide +kernel
example : (elim.vecAdd vK2 vK2s).length = (pairsAt vA2 vB2 vCC2).length :=
  by decide +kernel
example : (poly.neg vK2).length = (pairsAt vA2 vB2 vCC2).length := by decide +kernel

example : poly.oneValue
    (pairVal (pairFam vA2 vB2 vCC2 (elim.vecAdd vK2 vK2s)) vG2
      (rowList ([1, 0] : Shape))).coords
    (elim.vecAdd
      (pairVal (pairFam vA2 vB2 vCC2 vK2) vG2
        (rowList ([1, 0] : Shape))).coords
      (pairVal (pairFam vA2 vB2 vCC2 vK2s) vG2
        (rowList ([1, 0] : Shape))).coords) := by decide +kernel

example : poly.oneValue
    (pairVal (pairFam vA2 vB2 vCC2 (elim.vecScale (BPair.ofNat 2) vK2)) vG2
      (rowList ([1, 0] : Shape))).coords
    (elim.vecScale (BPair.ofNat 2)
      (pairVal (pairFam vA2 vB2 vCC2 vK2) vG2
        (rowList ([1, 0] : Shape))).coords) := by decide +kernel

example : (pairVal (pairFam vA2 vB2 vCC2 (poly.neg vK2)) vG2
      (rowList ([1, 0] : Shape))).coords
    = poly.neg (pairVal (pairFam vA2 vB2 vCC2 vK2) vG2
      (rowList ([1, 0] : Shape))).coords := by decide +kernel

/-! The value binder is load-bearing at the reversal member: the
kernel family off the unit tail carries a value off the unit tail
there, and the conclusion fails with it. -/

example : ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vK2) vG2
    (rowList ([1, 0] : Shape))).coords := by decide +kernel

example : poly.unitTail vU2
    ∧ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vU2) vG2
      (rowList ([1, 0] : Shape))).coords := by decide +kernel

/-! The content binder's reads at a member off the reversal
content: at both the two-letter and the three-letter join fixtures
the value there is off the unit tail as well. -/

example : ¬ (ground.getAt (⟨[], []⟩ : HVec) vA2 0).content
    = (rowList ([1, 0] : Shape)).reverse := by decide +kernel
example : ¬ poly.unitTail (pairVal (pairFam vA2 vB2 vCC2 vK2)
    (ground.getAt (⟨[], []⟩ : HVec) vA2 0)
    (rowList ([1, 0] : Shape))).coords := by decide +kernel

example : List.zipWith (fun u w => u + w) (rowList ([0, 1, 0] : Shape))
    (rowList ([1, 0, 0] : Shape)).reverse
    = List.replicate ([1, 0, 0] : Shape).length 1 := by decide +kernel
example : (ground.getAt (⟨[], []⟩ : HVec) vA3 2).content
    = (rowList ([1, 0, 0] : Shape)).reverse := by decide +kernel
example : ¬ poly.unitTail (pairVal (pairFam vA3 vB3 vCC3 vK3)
    (ground.getAt (⟨[], []⟩ : HVec) vA3 2)
    (rowList ([0, 1, 0] : Shape))).coords := by decide +kernel
example : ¬ (ground.getAt (⟨[], []⟩ : HVec) vA3 0).content
    = (rowList ([1, 0, 0] : Shape)).reverse := by decide +kernel
example : ¬ poly.unitTail (pairVal (pairFam vA3 vB3 vCC3 vK3)
    (ground.getAt (⟨[], []⟩ : HVec) vA3 0)
    (rowList ([0, 1, 0] : Shape))).coords := by decide +kernel
example : ¬ poly.unitTail (pairVal (pairFam vA3 vB3 vCC3 vK3)
    (ground.getAt (⟨[], []⟩ : HVec) vA3 1)
    (rowList ([0, 1, 0] : Shape))).coords := by decide +kernel

/-! The join's reads off the join: the stated pair list is vacant
there, the family is the unit one and its value at the reversal
member reads the unit tail with it. -/

example : poly.unitTail (pairVal (pairFam vA2 vB0 vCC2 []) vG2
    (rowList ([0, 0] : Shape))).coords := by decide +kernel

/-! The count at the two join fixtures: the dimension decides to
one at each and the theorem reads it back. -/

example : elim.kernelDim (pairsAt vA2 vB2 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB2 vCC2).map HVec.coords)) ≤ 1 := by decide +kernel

example : elim.kernelDim
    (pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([1, 0] : Shape))
      (List.replicate ([1, 0] : Shape).length 1)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([1, 0] : Shape).length 1))
      ((pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([1, 0] : Shape))
        (List.replicate ([1, 0] : Shape).length 1)).map HVec.coords))
      ≤ 1 :=
  ker_le_one_join [1, 0] [1, 0] 1 rfl (by decide +kernel)

example : List.zipWith (fun u w => u + w) (rowList ([2, 0] : Shape))
    (rowList ([2, 0] : Shape)).reverse
    = List.replicate ([2, 0] : Shape).length 2 := by decide +kernel

example : elim.kernelDim
    (pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([2, 0] : Shape))
      (List.replicate ([2, 0] : Shape).length 2)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([2, 0] : Shape).length 2))
      ((pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([2, 0] : Shape))
        (List.replicate ([2, 0] : Shape).length 2)).map HVec.coords))
      = 1 := by decide +kernel

example : elim.kernelDim
    (pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([2, 0] : Shape))
      (List.replicate ([2, 0] : Shape).length 2)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([2, 0] : Shape).length 2))
      ((pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([2, 0] : Shape))
        (List.replicate ([2, 0] : Shape).length 2)).map HVec.coords))
      ≤ 1 :=
  ker_le_one_join [2, 0] [2, 0] 2 rfl (by decide +kernel)

/-! The off-join conclusion at occupied pair lists: at `a = [2,0]`
the stated pair list against `b = [0,0]` at `m = 1` and against
`b = [0,1]` at `m = 2` holds one member, the join refuses, and the
kernel is vacant, the theorem read at both.  The matched-width
binder refuses at a second block one letter wider: at `a = [1,0]`
against `b = [1,0,0]` at `m = 1` a value sits off the second
block's span, and against `b = [0,1,0]` the join refuses while the
kernel holds one line.  The letter closure's kernel read refuses at
the off-kernel family `vOff2` at the letters `(0, 1)`. -/

private def vA20 : List HVec := blockSpan ([2, 0] : Shape)
private def vB01 : List HVec := blockSpan ([0, 1] : Shape)
private def vCC22 : List Nat := List.replicate ([2, 0] : Shape).length 2

example : (pairsAt vA20 vB0 vCC2).length = 1 := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w) (rowList ([0, 0] : Shape))
    (rowList ([2, 0] : Shape)).reverse
    = List.replicate ([2, 0] : Shape).length 1 := by decide +kernel
example : elim.kernelDim (pairsAt vA20 vB0 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA20 vB0 vCC2).map HVec.coords)) = 0 := by decide +kernel
example : elim.kernelDim
    (pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([0, 0] : Shape))
      (List.replicate ([2, 0] : Shape).length 1)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([2, 0] : Shape).length 1))
      ((pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([0, 0] : Shape))
        (List.replicate ([2, 0] : Shape).length 1)).map HVec.coords)) = 0 :=
  ker_null_offJoin [2, 0] [0, 0] 1 rfl (by decide +kernel)

example : (pairsAt vA20 vB01 vCC22).length = 1 := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w) (rowList ([0, 1] : Shape))
    (rowList ([2, 0] : Shape)).reverse
    = List.replicate ([2, 0] : Shape).length 2 := by decide +kernel
example : elim.kernelDim
    (pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([0, 1] : Shape))
      (List.replicate ([2, 0] : Shape).length 2)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([2, 0] : Shape).length 2))
      ((pairsAt (blockSpan ([2, 0] : Shape)) (blockSpan ([0, 1] : Shape))
        (List.replicate ([2, 0] : Shape).length 2)).map HVec.coords)) = 0 :=
  ker_null_offJoin [2, 0] [0, 1] 2 rfl (by decide +kernel)

private def vB100 : List HVec := blockSpan ([1, 0, 0] : Shape)
private def vKw : List BPair := ground.getAt ([] : List BPair)
  (elim.kernelList (pairsAt vA2 vB100 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB100 vCC2).map HVec.coords))) 0

example : (pairsAt vA2 vB100 vCC2).length = 2 := by decide +kernel
example : ¬ poly.unitTail vKw := by decide +kernel
example : ¬ ∀ x ∈ valList vA2 vB100 vCC2 vKw,
    sized x ∧ settledAt vB100 x := by decide +kernel
example : ∀ x ∈ valList vA2 vB100 vCC2 vKw, sized x := by decide +kernel

private def vB010 : List HVec := blockSpan ([0, 1, 0] : Shape)

example : (pairsAt vA2 vB010 vCC2).length = 2 := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w) (rowList ([0, 1, 0] : Shape))
    (rowList ([1, 0] : Shape)).reverse
    = List.replicate ([1, 0] : Shape).length 1 := by decide +kernel
example : ¬ elim.kernelDim (pairsAt vA2 vB010 vCC2).length
    (elim.crossM (units.stackedRaise vCC2)
      ((pairsAt vA2 vB010 vCC2).map HVec.coords)) = 0 := by decide +kernel

example : ¬ ∀ x ∈ valList vA2 vB2 vCC2 vOff2,
    settledAt (valList vA2 vB2 vCC2 vOff2) (act 0 1 x) := by decide +kernel

/-! `lem:dualread`(i)'s dual-table tier and clause 10 of (iii) at
the two-letter join `a = b = [1,0]`, `m = 1`: the two bridges
between the dual action and the dual table's step and transpose
decided and routed; the complement invariant at the one-letter word
with both liveness binders decided; and the Gram at the reversal
member decided and routed at two word pairs.  The liveness binders
are load-bearing: at the two-letter word both images read the unit
tail and the joined contents refuse the full columns.  The reversal
content is load-bearing: the exhibit's own member of the span
carries the row list rather than its reversal and the Gram's
display refuses there. -/

private def wDA : Shape := [1, 0]
private def wDG : HVec := ground.getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1
private def wDE : HVec := ground.getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 0

example : wDG.content = (rowList wDA).reverse := by decide +kernel
example : ¬ wDE.content = (rowList wDA).reverse := by decide +kernel
example : List.zipWith (fun u w => u + w) (rowList wDA)
    (rowList wDA).reverse = List.replicate wDA.length 1 := by decide +kernel

example : dact 1 0 (exhibit wDA) = dualTable.step 0 (exhibit wDA) := by
  decide +kernel
example : dact 0 1 (exhibit wDA) = dualTable.tr 0 (exhibit wDA) := by
  decide +kernel
example : dact 1 0 (exhibit wDA) = dualTable.step 0 (exhibit wDA) :=
  dact_step 0 (exhibit wDA)
example : dact 0 1 (exhibit wDA) = dualTable.tr 0 (exhibit wDA) :=
  dact_tr 0 (exhibit wDA)
example : dact 1 0 wDG = dualTable.step 0 wDG := dact_step 0 wDG
example : dact 0 1 wDG = dualTable.tr 0 wDG := dact_tr 0 wDG

example : ¬ poly.unitTail (wact [0] (exhibit wDA)).coords := by decide +kernel
example : ¬ poly.unitTail (wactT dualTable [0] wDG).coords := by decide +kernel
example : List.zipWith (fun u w => u + w)
    (wact [0] (exhibit wDA)).content
    (wactT dualTable [0] wDG).content
    = List.replicate wDA.length 1 := by decide +kernel
example : List.zipWith (fun u w => u + w)
    (wact [0] (exhibit wDA)).content
    (wactT dualTable [0] wDG).content
    = List.replicate wDA.length 1 :=
  dualLive wDA wDA 1 rfl (by decide +kernel) wDG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1 (by decide +kernel))
    (by decide +kernel) [0]
    (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel) memAll_nil)
    (by decide +kernel) (by decide +kernel)

example : poly.unitTail (wact [0, 0] (exhibit wDA)).coords := by decide +kernel
example : poly.unitTail (wactT dualTable [0, 0] wDG).coords := by decide +kernel
example : ¬ List.zipWith (fun u w => u + w)
    (wact [0, 0] (exhibit wDA)).content
    (wactT dualTable [0, 0] wDG).content
    = List.replicate wDA.length 1 := by decide +kernel

example : (dotG (wact [0] (exhibit wDA)) (wact [0] (exhibit wDA))
      * elim.dotP wDG.coords wDG.coords).oneValue
    (dotG (wactT dualTable [0] wDG) (wactT dualTable [0] wDG)
      * elim.dotP (exhibit wDA).coords (exhibit wDA).coords) := by decide +kernel
example : (dotG (wact [0] (exhibit wDA)) (wact [0] (exhibit wDA))
      * elim.dotP wDG.coords wDG.coords).oneValue
    (dotG (wactT dualTable [0] wDG) (wactT dualTable [0] wDG)
      * elim.dotP (exhibit wDA).coords (exhibit wDA).coords) :=
  dualGram wDA wDA 1 rfl (by decide +kernel) wDG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1 (by decide +kernel))
    (by decide +kernel) [0] [0]
    (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel) memAll_nil)
    (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel) memAll_nil)

example : (dotG (wact [] (exhibit wDA)) (wact [0] (exhibit wDA))
      * elim.dotP wDG.coords wDG.coords).oneValue
    (dotG (wactT dualTable [] wDG) (wactT dualTable [0] wDG)
      * elim.dotP (exhibit wDA).coords (exhibit wDA).coords) := by decide +kernel
example : (dotG (wact [] (exhibit wDA)) (wact [0] (exhibit wDA))
      * elim.dotP wDG.coords wDG.coords).oneValue
    (dotG (wactT dualTable [] wDG) (wactT dualTable [0] wDG)
      * elim.dotP (exhibit wDA).coords (exhibit wDA).coords) :=
  dualGram wDA wDA 1 rfl (by decide +kernel) wDG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1 (by decide +kernel))
    (by decide +kernel) [] [0] memAll_nil
    (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel) memAll_nil)

example : wDE ∈ blockSpan wDA :=
  ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 0 (by decide +kernel)
example : ¬ (dotG (wact [0] (exhibit wDA)) (wact [0] (exhibit wDA))
      * elim.dotP wDE.coords wDE.coords).oneValue
    (dotG (wactT dualTable [0] wDE) (wactT dualTable [0] wDE)
      * elim.dotP (exhibit wDA).coords (exhibit wDA).coords) := by decide +kernel

/-! Clause 11 of `lem:dualread`(iii) at the same two-letter join
`a = b = [1,0]`, `m = 1` with the collected family `W = [[], [0]]`,
and at the vacant join `a = b = [0,0]`, `m = 0` with `W = [[]]`: the
coevaluation's datum read entry by entry — the two content groups
singletons, each weight reading the natural one and each entry's two
slots the word's dual image at the reversal member and its partner
image at the target's top — the member's content and coordinate
width at the full columns, and the two clauses decided and applied
whole at both joins.

The span display's two binders are load-bearing.  At the exhibit in
place of the reversal member the first slots leave the reversal's own
group and the display refuses; at the second block `[0,0]` against
`a = [1,0]`, whose collected family still reads `W = [[]]`, the two
row lists do not join to the full columns and the display refuses
there too.  The off-unit clause splits its two binders: the
reversal content is the clause's frame — the determinant's diagonal
is a read of the group's own Gram against the further groups', and
the two decided reads below record the display holding at the moved
member — while the join is load-bearing through the entries' width
tie: off the join the tensors' contents miss the stated width, the
combination reads the unit family, and the display refuses, the
committed refusal beside the reads. -/

private def cW : List (List Nat) := [[], [0]]
private def cCC : List Nat := List.replicate wDA.length 1
private def cU : Shape := [0, 0]
private def cVG : HVec := ground.getAt (⟨[], []⟩ : HVec) (blockSpan cU) 0
private def cWU : List (List Nat) := [[]]
private def cCU : List Nat := List.replicate cU.length 0

example : blockSpan wDA = cW.map (fun ws => wact ws (exhibit wDA)) := by
  decide +kernel
example : (coevW wDA wDG cW).length = 2 := by decide +kernel
example : ((ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
    (⟨[], []⟩ : HVec)) (coevW wDA wDG cW) 0).1).oneValue
  (BPair.ofNat 1) := by decide +kernel
example : ((ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
    (⟨[], []⟩ : HVec)) (coevW wDA wDG cW) 1).1).oneValue
  (BPair.ofNat 1) := by decide +kernel
example : (ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
    (⟨[], []⟩ : HVec)) (coevW wDA wDG cW) 0).2.1
  = wactT dualTable [] wDG := by decide +kernel
example : (ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
    (⟨[], []⟩ : HVec)) (coevW wDA wDG cW) 0).2.2
  = wact [] (exhibit wDA) := by decide +kernel
example : (ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
    (⟨[], []⟩ : HVec)) (coevW wDA wDG cW) 1).2.1
  = wactT dualTable [0] wDG := by decide +kernel
example : (ground.getAt (BPair.unit, (⟨[], []⟩ : HVec),
    (⟨[], []⟩ : HVec)) (coevW wDA wDG cW) 1).2.2
  = wact [0] (exhibit wDA) := by decide +kernel
example : (coevVec cCC wDA wDG cW).content = cCC := rfl
example : (coevVec cCC wDA wDG cW).coords.length
  = (places.monomialsAt cCC).length := by decide +kernel

example : elim.spanRel (places.monomialsAt cCC).length
    ((pairsAt (blockSpan wDA) (blockSpan wDA) cCC).map HVec.coords)
    (coevVec cCC wDA wDG cW).coords := by decide +kernel
example : elim.spanRel (places.monomialsAt cCC).length
    ((pairsAt (blockSpan wDA) (blockSpan wDA) cCC).map HVec.coords)
    (coevVec cCC wDA wDG cW).coords :=
  coevVec_span wDA wDA 1 rfl (by decide +kernel) wDG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1 (by decide +kernel))
    (by decide +kernel) cW (by decide +kernel)
    (memAll_cons memAll_nil (memAll_cons
      (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel)
        memAll_nil) memAll_nil))
example : ¬ poly.unitTail (coevVec cCC wDA wDG cW).coords := by decide +kernel
example : ¬ poly.unitTail (coevVec cCC wDA wDG cW).coords :=
  coevVec_off wDA wDA 1 rfl (by decide +kernel) wDG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1 (by decide +kernel))
    (by decide +kernel) cW (by decide +kernel)
    (memAll_cons memAll_nil (memAll_cons
      (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel)
        memAll_nil) memAll_nil))

example : cVG.content = (rowList cU).reverse := by decide +kernel
example : blockSpan cU = cWU.map (fun ws => wact ws (exhibit cU)) := by
  decide +kernel
example : (coevW cU cVG cWU).length = 1 := by decide +kernel
example : elim.spanRel (places.monomialsAt cCU).length
    ((pairsAt (blockSpan cU) (blockSpan cU) cCU).map HVec.coords)
    (coevVec cCU cU cVG cWU).coords := by decide +kernel
example : elim.spanRel (places.monomialsAt cCU).length
    ((pairsAt (blockSpan cU) (blockSpan cU) cCU).map HVec.coords)
    (coevVec cCU cU cVG cWU).coords :=
  coevVec_span cU cU 0 rfl (by decide +kernel) cVG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan cU) 0 (by decide +kernel))
    (by decide +kernel) cWU (by decide +kernel) (memAll_cons memAll_nil memAll_nil)
example : ¬ poly.unitTail (coevVec cCU cU cVG cWU).coords := by decide +kernel
example : ¬ poly.unitTail (coevVec cCU cU cVG cWU).coords :=
  coevVec_off cU cU 0 rfl (by decide +kernel) cVG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan cU) 0 (by decide +kernel))
    (by decide +kernel) cWU (by decide +kernel) (memAll_cons memAll_nil memAll_nil)

example : ¬ elim.spanRel (places.monomialsAt cCC).length
    ((pairsAt (blockSpan wDA) (blockSpan wDA) cCC).map HVec.coords)
    (coevVec cCC wDA wDE cW).coords := by decide +kernel
example : ¬ poly.unitTail (coevVec cCC wDA wDE cW).coords := by decide +kernel

example : ¬ List.zipWith (fun u w => u + w) (rowList cU)
    (rowList wDA).reverse = List.replicate wDA.length 1 := by decide +kernel
example : ¬ elim.spanRel (places.monomialsAt cCC).length
    ((pairsAt (blockSpan wDA) (blockSpan cU) cCC).map HVec.coords)
    (coevVec cCC cU wDG cWU).coords := by decide +kernel
example : ¬ poly.unitTail (coevVec cCC cU wDG cWU).coords := by decide +kernel

private def cB1 : Shape := [0, 1]

example : ¬ (List.zipWith (fun u w => u + w) (rowList cB1)
    (rowList wDA).reverse = List.replicate wDA.length 0) := by decide +kernel
example : blockSpan cB1 = ([[]] : List (List Nat)).map
    (fun ws => wact ws (exhibit cB1)) := by decide +kernel
example : poly.unitTail
    (coevVec (List.replicate wDA.length 0) cB1 wDG [[]]).coords := by
  decide +kernel

/-! Clause 11's closing sentence at the same two joins: the
coevaluation lies in the stacked raisings' kernel.  The stacked
system's whole read is decided and routed at both joins — at the
vacant join `a = b = [0,0]`, `m = 0`, the stacked matrix is the
empty row list outright, every adjacent move unoccupied — and the
one adjacent raising's own read at the two-letter join sits beside
them, with the moved image decided inside the moved content's pair
span.

The kernel display's two binders are load-bearing at the same two
violating fixtures the span clause records: at the exhibit in place
of the reversal member the first slots leave the reversal's own
group, and at the second block `[0,0]` against `a = [1,0]` the two
row lists do not join to the full columns; the kernel display
refuses at both, the single raising's own read refusing at the
first. -/

example : poly.unitTail (elim.matVec (units.stackedRaise cCC)
    (coevVec cCC wDA wDG cW).coords) := by decide +kernel
example : poly.unitTail (elim.matVec (units.stackedRaise cCC)
    (coevVec cCC wDA wDG cW).coords) :=
  coevVec_ker wDA wDA 1 rfl (by decide +kernel) wDG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan wDA) 1 (by decide +kernel))
    (by decide +kernel) cW (by decide +kernel)
    (memAll_cons memAll_nil (memAll_cons
      (memAll_cons (show (0 : Nat) + 1 < wDA.length by decide +kernel)
        memAll_nil) memAll_nil))

example : units.stackedRaise cCU = ([] : elim.Mat) := by decide +kernel
example : poly.unitTail (elim.matVec (units.stackedRaise cCU)
    (coevVec cCU cU cVG cWU).coords) := by decide +kernel
example : poly.unitTail (elim.matVec (units.stackedRaise cCU)
    (coevVec cCU cU cVG cWU).coords) :=
  coevVec_ker cU cU 0 rfl (by decide +kernel) cVG
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan cU) 0 (by decide +kernel))
    (by decide +kernel) cWU (by decide +kernel) (memAll_cons memAll_nil memAll_nil)

example : poly.unitTail (elim.matVec
    (units.matUnitAt (moveAt 0 1 cCC) cCC 0 1)
    (coevVec cCC wDA wDG cW).coords) := by decide +kernel
example : elim.spanRel (places.monomialsAt (moveAt 0 1 cCC)).length
    ((pairsAt (blockSpan wDA) (blockSpan wDA) (moveAt 0 1 cCC)).map
      HVec.coords)
    (elim.matVec (units.matUnitAt (moveAt 0 1 cCC) cCC 0 1)
      (coevVec cCC wDA wDG cW).coords) := by decide +kernel

example : ¬ poly.unitTail (elim.matVec (units.stackedRaise cCC)
    (coevVec cCC wDA wDE cW).coords) := by decide +kernel
example : ¬ poly.unitTail (elim.matVec
    (units.matUnitAt (moveAt 0 1 cCC) cCC 0 1)
    (coevVec cCC wDA wDE cW).coords) := by decide +kernel
example : ¬ poly.unitTail (elim.matVec (units.stackedRaise cCC)
    (coevVec cCC cU wDG cWU).coords) := by decide +kernel

/-! `lem:dualread`(iii)'s coevaluation at a multiplicity-two content
group: the adjoint-type shape `[1, 1, 0]` at width three holds the
content `(1, 1, 1)` twice, so the group's adjugate collection and the
word relation transfer run at a group of order two, and the self-join
holds at the full columns `(2, 2, 2)` — the committed instances
exercising the solve-back off the singleton groups, the kernel read
decided at the eight-member block's Gram solves and the span read
routed through its theorem. -/

private def fA3 : Shape := [1, 1, 0]
private def fW3 : List (List Nat) :=
  [[], [0], [1], [1, 0], [0, 1], [0, 1, 0], [1, 1, 0], [0, 1, 0, 1]]
private def fG3 : HVec :=
  ground.getAt (⟨[], []⟩ : HVec) (blockSpan fA3) 7

example : fG3.content = (rowList fA3).reverse := by decide +kernel
example : ground.countOf ([1, 1, 1] : List Nat)
    ((blockSpan fA3).map HVec.content) = 2 := by decide +kernel
example : blockSpan fA3
    = fW3.map (fun ws => wact ws (exhibit fA3)) := by decide +kernel
example : List.zipWith (fun u w => u + w) (rowList fA3)
    (rowList fA3).reverse = List.replicate 3 2 := by decide +kernel
example : ¬ poly.unitTail
    (coevVec (List.replicate 3 2) fA3 fG3 fW3).coords := by decide +kernel
example : poly.unitTail (elim.matVec
    (units.stackedRaise (List.replicate 3 2))
    (coevVec (List.replicate 3 2) fA3 fG3 fW3).coords) := by decide +kernel
example : poly.unitTail (elim.matVec
    (units.stackedRaise (List.replicate 3 2))
    (coevVec (List.replicate 3 2) fA3 fG3 fW3).coords) :=
  coevVec_ker fA3 fA3 2 rfl (by decide +kernel) fG3
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan fA3) 7 (by decide +kernel))
    (by decide +kernel) fW3 (by decide +kernel) (by decide +kernel)

example : elim.spanRel
    (places.monomialsAt (List.replicate 3 2)).length
    ((pairsAt (blockSpan fA3) (blockSpan fA3)
      (List.replicate 3 2)).map HVec.coords)
    (coevVec (List.replicate 3 2) fA3 fG3 fW3).coords :=
  coevVec_span fA3 fA3 2 rfl (by decide +kernel) fG3
    (ground.mem_getAt (⟨[], []⟩ : HVec) (blockSpan fA3) 7 (by decide +kernel))
    (by decide +kernel) fW3 (by decide +kernel) (by decide +kernel)

/-! `lem:dualread`(iii)'s at-join occupancy and the clause's own
count at the full columns.  The occupancy is applied whole at the
two-letter join `a = b = [1,0]`, `m = 1`, whose collected family
is `[[], [0]]`, and at the vacant join `a = b = [0,0]`, `m = 0`,
whose stacked matrix is the empty row list, with each dimension
decided beside its application.  The count reads both arms of the
condition: at the join it is one and off the join — the second
block `[0,0]` against `a = [1,0]` — it is nought, the theorem's
own if-form applied whole at each and the condition decided beside
it.  At the vacant letter count the shape is the empty column
list, both row lists are empty, the condition holds outright and
the count reads one: the width-0 fusion of the trivial block with
itself. -/

example : 1 ≤ elim.kernelDim
    (pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([1, 0] : Shape))
      (List.replicate ([1, 0] : Shape).length 1)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([1, 0] : Shape).length 1))
      ((pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([1, 0] : Shape))
        (List.replicate ([1, 0] : Shape).length 1)).map HVec.coords)) := by
  decide +kernel
example : 1 ≤ elim.kernelDim
    (pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([1, 0] : Shape))
      (List.replicate ([1, 0] : Shape).length 1)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([1, 0] : Shape).length 1))
      ((pairsAt (blockSpan ([1, 0] : Shape)) (blockSpan ([1, 0] : Shape))
        (List.replicate ([1, 0] : Shape).length 1)).map HVec.coords)) :=
  ker_ge_one_join [1, 0] [1, 0] 1 rfl (by decide +kernel)

example : 1 ≤ elim.kernelDim
    (pairsAt (blockSpan ([0, 0] : Shape)) (blockSpan ([0, 0] : Shape))
      (List.replicate ([0, 0] : Shape).length 0)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([0, 0] : Shape).length 0))
      ((pairsAt (blockSpan ([0, 0] : Shape)) (blockSpan ([0, 0] : Shape))
        (List.replicate ([0, 0] : Shape).length 0)).map HVec.coords)) := by
  decide +kernel
example : 1 ≤ elim.kernelDim
    (pairsAt (blockSpan ([0, 0] : Shape)) (blockSpan ([0, 0] : Shape))
      (List.replicate ([0, 0] : Shape).length 0)).length
    (elim.crossM
      (units.stackedRaise (List.replicate ([0, 0] : Shape).length 0))
      ((pairsAt (blockSpan ([0, 0] : Shape)) (blockSpan ([0, 0] : Shape))
        (List.replicate ([0, 0] : Shape).length 0)).map HVec.coords)) :=
  ker_ge_one_join [0, 0] [0, 0] 0 rfl (by decide +kernel)

example : List.zipWith (fun x y => x + y) (rowList ([1, 0] : Shape))
    ((rowList ([1, 0] : Shape)).reverse)
    = List.replicate ([1, 0] : Shape).length 1 := by decide +kernel
example : fusionCount [1, 0] [1, 0] (fulls 2 1) = 1 := by decide +kernel
example : fusionCount [1, 0] [1, 0]
      (dualread.fulls ([1, 0] : Shape).length 1)
    = if List.zipWith (fun x y => x + y) (rowList ([1, 0] : Shape))
          ((rowList ([1, 0] : Shape)).reverse)
        = List.replicate ([1, 0] : Shape).length 1
      then 1 else 0 :=
  fusionCount_fulls [1, 0] [1, 0] 1 rfl

example : ¬ List.zipWith (fun x y => x + y) (rowList ([0, 0] : Shape))
    ((rowList ([1, 0] : Shape)).reverse)
    = List.replicate ([1, 0] : Shape).length 1 := by decide +kernel
example : fusionCount [1, 0] [0, 0] (fulls 2 1) = 0 := by decide +kernel
example : fusionCount [1, 0] [0, 0]
      (dualread.fulls ([1, 0] : Shape).length 1)
    = if List.zipWith (fun x y => x + y) (rowList ([0, 0] : Shape))
          ((rowList ([1, 0] : Shape)).reverse)
        = List.replicate ([1, 0] : Shape).length 1
      then 1 else 0 :=
  fusionCount_fulls [1, 0] [0, 0] 1 rfl

example : fulls 0 1 = ([] : Shape) := by decide +kernel
example : List.zipWith (fun x y => x + y) (rowList ([] : Shape))
    ((rowList ([] : Shape)).reverse)
    = List.replicate ([] : Shape).length 1 := by decide +kernel
example : fusionCount [] [] (fulls 0 1) = 1 := by decide +kernel
example : fusionCount [] [] (dualread.fulls ([] : Shape).length 1)
    = if List.zipWith (fun x y => x + y) (rowList ([] : Shape))
          ((rowList ([] : Shape)).reverse)
        = List.replicate ([] : Shape).length 1
      then 1 else 0 :=
  fusionCount_fulls [] [] 1 rfl

/-! The width tie is load-bearing in both arms: at mismatched
letter counts the delta's condition and the count part in either
direction — a wider second shape reading count one at the
condition's refusal, and a wider second shape reading count naught
at the condition's own hold. -/

example : ¬ (([0, 1, 0] : Shape).length = ([1, 0] : Shape).length) := by
  decide +kernel
example : ¬ (List.zipWith (fun x y => x + y) (rowList ([0, 1, 0] : Shape))
    ((rowList ([1, 0] : Shape)).reverse)
    = List.replicate ([1, 0] : Shape).length 1) := by decide +kernel
example : fusionCount [1, 0] [0, 1, 0]
    (fulls ([1, 0] : Shape).length 1) = 1 := by decide +kernel
example : ¬ (([0, 0, 1] : Shape).length = ([0, 1] : Shape).length) := by
  decide +kernel
example : List.zipWith (fun x y => x + y) (rowList ([0, 0, 1] : Shape))
    ((rowList ([0, 1] : Shape)).reverse)
    = List.replicate ([0, 1] : Shape).length 2 := by decide +kernel
example : fusionCount [0, 1] [0, 0, 1]
    (fulls ([0, 1] : Shape).length 2) = 0 := by decide +kernel

/-! The mapped-span engine's batteries: the descent at one full
column decided at the tex's instances and read through the theorem,
the span length at the added column, the carrier exchange at the
mapped fused pool and the mapped carrier's count at the shifted
content, with the load-bearing binders' isolating refusals — the
two letter widths, the target's own shift, the members' widths and
sizes, and the content's own width. -/

/-! The fusion count's descent at one full column: the four
instances decided beside the theorem's route, the last at the
vacant count on both sides. -/

example : fusionCount (ground.bumpAt 1 [1, 0]) [1, 0]
    (ground.bumpAt 1 [0, 1]) = fusionCount [1, 0] [1, 0] [0, 1] := by
  decide +kernel
example : fusionCount (ground.bumpAt 1 [1, 0]) [1, 0]
    (ground.bumpAt 1 [0, 1]) = fusionCount [1, 0] [1, 0] [0, 1] :=
  fusionCount_addFull [1, 0] [1, 0] [0, 1] rfl rfl

example : fusionCount (ground.bumpAt 1 [1, 0]) [1, 0]
    (ground.bumpAt 1 [2, 0]) = fusionCount [1, 0] [1, 0] [2, 0] := by
  decide +kernel
example : fusionCount (ground.bumpAt 1 [1, 0]) [1, 0]
    (ground.bumpAt 1 [2, 0]) = fusionCount [1, 0] [1, 0] [2, 0] :=
  fusionCount_addFull [1, 0] [1, 0] [2, 0] rfl rfl

example : fusionCount (ground.bumpAt 2 [1, 0, 0]) [1, 0, 0]
    (ground.bumpAt 2 [0, 1, 0])
    = fusionCount [1, 0, 0] [1, 0, 0] [0, 1, 0] := by decide +kernel
example : fusionCount (ground.bumpAt 2 [1, 0, 0]) [1, 0, 0]
    (ground.bumpAt 2 [0, 1, 0])
    = fusionCount [1, 0, 0] [1, 0, 0] [0, 1, 0] :=
  fusionCount_addFull [1, 0, 0] [1, 0, 0] [0, 1, 0] rfl rfl

example : fusionCount [1, 0, 0] [2, 0, 0] [0, 0, 1] = 0 := by decide +kernel
example : fusionCount (ground.bumpAt 2 [1, 0, 0]) [2, 0, 0]
    (ground.bumpAt 2 [0, 0, 1])
    = fusionCount [1, 0, 0] [2, 0, 0] [0, 0, 1] := by decide +kernel
example : fusionCount (ground.bumpAt 2 [1, 0, 0]) [2, 0, 0]
    (ground.bumpAt 2 [0, 0, 1])
    = fusionCount [1, 0, 0] [2, 0, 0] [0, 0, 1] :=
  fusionCount_addFull [1, 0, 0] [2, 0, 0] [0, 0, 1] rfl rfl

/-! The descent read refused at an unshifted target: the added
column moves the fused contents off the target's own, and the two
counts part at nought against one (the target's width itself is
the frame, both counts vacant off it). -/

example : fusionCount (ground.bumpAt 1 [1, 0]) [1, 0] [0, 1] = 0 := by
  decide +kernel
example : fusionCount [1, 0] [1, 0] [0, 1] = 1 := by decide +kernel
example : ¬ (fusionCount (ground.bumpAt 1 [1, 0]) [1, 0] [0, 1]
    = fusionCount [1, 0] [1, 0] [0, 1]) := by decide +kernel

/-! Refusal isolating the descent's letter-width binder: at a
second shape one letter wider the added column reaches past the
first shape's letters and the two counts part at nought against
one, the target's own shift held. -/

example : ¬ (([2, 0, 0] : Shape).length = ([1, 0] : Shape).length) := by
  decide +kernel
example : ¬ (fusionCount (ground.bumpAt 1 [1, 0]) [2, 0, 0]
    (ground.bumpAt 1 [0, 1])
    = fusionCount [1, 0] [2, 0, 0] [0, 1]) := by decide +kernel

/-! The span length at the added full column, the theorem's route
at three shapes with the decided twins at two: the derivation
holds one arm at every shape (`blockcount.blockSpan_addFull` at
the height measure), the twins exercising the multi-member spans
at both letter widths, the third shape's read the route's own. -/

example : (blockSpan (ground.bumpAt 1 [1, 0])).length
    = (blockSpan [1, 0]).length := by decide +kernel
example : (blockSpan (ground.bumpAt 1 [1, 0])).length
    = (blockSpan [1, 0]).length := (spanAddFull [1, 0]).1
example : (blockSpan (ground.bumpAt 2 [1, 1, 0])).length
    = (blockSpan [1, 1, 0]).length := (spanAddFull [1, 1, 0]).1
example : (blockSpan (ground.bumpAt 2 [2, 0, 0])).length
    = (blockSpan [2, 0, 0]).length := by decide +kernel
example : (blockSpan (ground.bumpAt 2 [2, 0, 0])).length
    = (blockSpan [2, 0, 0]).length := (spanAddFull [2, 0, 0]).1

/-! The carrier exchange at the mapped fused pool, decided at a
content the count occupies and read through the theorem, with the
letter-width refusal beside it. -/

example : countAt (fusedAt (blockSpan (ground.bumpAt 1 [1, 0]))
      (blockSpan [1, 0])) [2, 2]
    = countAt ((fusedAt (blockSpan [1, 0]) (blockSpan [1, 0])).map
        (fun v => tensorH (wedge 2 2) v)) [2, 2] := by decide +kernel
example : countAt (fusedAt (blockSpan (ground.bumpAt 1 [1, 0]))
      (blockSpan [1, 0])) [2, 2]
    = countAt ((fusedAt (blockSpan [1, 0]) (blockSpan [1, 0])).map
        (fun v => tensorH (wedge 2 2) v)) [2, 2] :=
  countAt_fusedLine [1, 0] [1, 0] rfl [2, 2]

example : ¬ (countAt (fusedAt (blockSpan (ground.bumpAt 1 [1, 0]))
      (blockSpan [2, 0, 0])) [3, 1]
    = countAt ((fusedAt (blockSpan [1, 0])
        (blockSpan [2, 0, 0])).map
        (fun v => tensorH (wedge 2 2) v)) [3, 1]) := by decide +kernel

/-! The mapped carrier's count at the shifted content: the fused
pool at two copies of one block read at an interior content and at
a content with a vacant letter — the shifted content occupies every
letter while the carrier's own leaves one vacant, so the stacked
datum carries a block the carrier's own has none of. -/

example : countAt ((fusedAt (blockSpan [1, 0]) (blockSpan [1, 0])).map
      (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [1, 1])
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [1, 1] := by decide +kernel
example : countAt ((fusedAt (blockSpan [1, 0]) (blockSpan [1, 0])).map
      (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [1, 1])
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [1, 1] :=
  countAt_lineShift 2 (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
    (by decide +kernel) (by decide +kernel) [1, 1] rfl

example : ground.getAt 0 [2, 0] 1 = 0 := by decide +kernel
example : countAt ((fusedAt (blockSpan [1, 0]) (blockSpan [1, 0])).map
      (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [2, 0])
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [2, 0] := by decide +kernel
example : countAt ((fusedAt (blockSpan [1, 0]) (blockSpan [1, 0])).map
      (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [2, 0])
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [2, 0] :=
  countAt_lineShift 2 (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
    (by decide +kernel) (by decide +kernel) [2, 0] rfl

/-! Refusal isolating the content's own width: at a content wider
than the letter count the shift truncates to the carrier's own
letters while the carrier's group at that content is vacant, and
the two counts part at one against nought. -/

example : ¬ (([1, 1, 0] : List Nat).length = 2) := by decide +kernel
example : ¬ (countAt ((fusedAt (blockSpan [1, 0])
      (blockSpan [1, 0])).map (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [1, 1, 0])
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [1, 1, 0]) := by decide +kernel

/-! Refusal isolating the members' letter width: a member three
letters wide is truncated by the shift onto the stated content
while its own group at that content is vacant, and the two counts
part at one against nought. -/

private def wideP : List HVec := [exhibit [1, 0, 0]]

example : ¬ (∀ x ∈ wideP, x.content.length = 2) := by decide +kernel
example : ∀ x ∈ wideP, sized x := by decide +kernel
example : ¬ (countAt (wideP.map (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [1, 0])
    = countAt wideP [1, 0]) := by decide +kernel

/-! Refusal isolating the members' coordinate width: a member whose
family stops one key short of its content's enumeration is read
whole once the wedge is tensored on, and the two counts part at one
against nought. -/

private def raggedP : List HVec :=
  [⟨[1, 1], [BPair.ofNat 1]⟩,
   ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩]

example : ¬ (∀ x ∈ raggedP, sized x) := by decide +kernel
example : ∀ x ∈ raggedP, x.content.length = 2 := by decide +kernel
example : ¬ (countAt (raggedP.map (fun v => tensorH (wedge 2 2) v))
      (List.zipWith (fun a b => a + b) (wedge 2 2).content [1, 1])
    = countAt raggedP [1, 1]) := by decide +kernel

/-! The lowering word past the full wedge: the wedge's own letter is
occupied at every interior key, so a word's image at the tensor
reads the wedge tensored onto the image while every letter the word
consumes stays occupied in the further factor — and at a letter the
further factor leaves vacant the two contents part, the wedge
carrying the move its partner has no source for, while the two
coordinate families still read the sum's unit together. -/

example : (wact [0, 1] (tensorH (wedge 3 3) (exhibit [1, 1, 0]))).content
    = List.zipWith (fun a b => a + b) (wedge 3 3).content
      (wact [0, 1] (exhibit [1, 1, 0])).content := by decide +kernel
example : poly.oneValue
    (wact [0, 1] (tensorH (wedge 3 3) (exhibit [1, 1, 0]))).coords
    (tensorH (wedge 3 3) (wact [0, 1] (exhibit [1, 1, 0]))).coords := by
  decide +kernel

example : ground.getAt 0 (exhibit ([0, 0] : Shape)).content 0 = 0 := by
  decide +kernel
example : ¬ (wact [0] (tensorH (wedge 2 2) (exhibit [0, 0]))).content
    = List.zipWith (fun a b => a + b) (wedge 2 2).content
      (wact [0] (exhibit [0, 0])).content := by decide +kernel
example : poly.oneValue
    (wact [0] (tensorH (wedge 2 2) (exhibit [0, 0]))).coords
    (tensorH (wedge 2 2) (wact [0] (exhibit [0, 0]))).coords := by
  decide +kernel
