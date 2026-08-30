import MassGap.Units
/-!
`def:blockcount` — the block count `N_λ(M)` is the dimension of the
content-`λ` vectors of `M` whose every raising image is the sum's
unit, a kernel dimension of the stacked raisings on the content
summand (`def:elim`'s descent); the fusion count at shapes is
`N^c_{ab} = N_c(W_a ⊗ W_b)` at the blocks `W_λ`, the lowering spans
of the column exhibits (`lem:lowerspan`'s carrier: the span closes
under the adjacent lowerings, the words stabilizing at length
`k d_f`, the tex's own bound and the closure's fuel).  A block's
span is content-graded, one homogeneous vector per generator, so
the fused content summand's stated pair list is the tensor pairs
at complementary contents, and the count is the kernel dimension
of the stacked raisings against that pair list (`elim.crossM`).  A stated carrier's count at a content is `countAt`,
the kernel dimension of the stacked raisings against the
summand's collected list (`lem:lowerspan`'s joined-collection),
its additivity over an orthogonal split landing at the exhaustion
tier (`countAt_append`, Fusiondata).  `lem:blockcount`'s own
reads land across the two tiers: the exhaustion, the dimension sum
`dim M = Σ N_λ d_λ`, and the fusion-data identities — the Cartan
floor here (`fusionCount_cartan`), the bridge to the fused count,
the flip, the unit read and the fused carrier's dimension display
at the exhaustion tier (Fusiondata's `fusionCount_countAt`,
`fusionCount_comm`, `fusionCount_unit`, `fusionCount_assoc`,
`fusionCount_dim`), each applied whole in its check module.  The
exhaustion expansion (`countAt_fused_exhaust`) runs at a
one-degree carrier, `con:places`' one-degree blocks the frame:
the degree binder is load-bearing with its isolating refusal at a
two-degree carrier pinned in ChecksFusiondata, the additivity's
cross pairing running through two first factors of distinct
degrees there.

`lem:blockcount`(iii)'s carrier-and-independence tier is landed
here.  The stated pair list at a content is `pairsAt`, the two
blocks' spanning lists' tensors at complementary contents; two
tensors at one fused content but distinct first contents pair at
the sum's unit (`dotP_tensorH_off`: each enumeration place's split
at the first factor's degree misses one of the two contents'
splits), beside the matched-content factorization at the factors'
own pairings (`dotP_tensorH`).  So the pair list is independent
(`tensor_indep`): a combination reading the unit family pairs
every pair at the sum's unit and its coefficients read back
through the two factors in turn — per first-factor content the
contraction is a combination of the second factor's group pairing
every group member at that unit, its self-pairing reading that
unit through the pairings' fold, the positive pairing withdrawing
it and the group's independence reading its coefficients at the
unit family, the first factor's groups then reading the
coefficients themselves (`elim.indep_perp_null` once per factor).
The fused pool is `fusedAt`, every tensor of a member of the first
list with a member of the second; its content group at the target
is the pair list's own coordinate family, so an independent pair
list stands as its own collection and the pool's count is the
display's own kernel dimension (`countAt_pairs` at
`elim.collect_keep`), with the fusion count that pool's count at
the target content (`fusionCount_countAt`, landed at the
exhaustion tier in Fusiondata: the two shapes' one letter width is
its one frame, the members' widths and one degree the span's own
reads, and the two independence binders derive from
`lowerspan.spanReads`).  A member of each block's
content span tensors into the fused pool's own span at the summed
content (`tensor_span`, `con:places`' collecting sentence — a
tensor of two combinations collecting to the pairs at the
coefficients' products): the two clearings multiply and the double
combination walks out one factor at a time through the tensor's
additivity and scale-equivariance in that factor
(`tensorH_vecAddL/R`, `tensorH_vecScaleL/R` at the general first
or second factor, the wedge-tensored pair `tensorW_vecAdd`,
`tensorW_vecScale` their instances), each pair of rows a member of
the fused pool's content group.  At the shapes' own column
union the count is occupied outright (`fusionCount_cartan`,
`lem:blockcount`(iii)'s closing sentence): the two column
exhibits' tensor is a top off the sum's unit at content `a + b`,
it heads the display's pair list, and the coefficient family
carrying the natural one at that head lies in the kernel list's
span, so the kernel list cannot be empty.

The letter pair's action splits over the tensor
(`act_tensorH`, `con:units`' composite clause — a composite
power's fold splitting at the arrangements' join): the moved
composite's coordinates read the two one-sided images' sum, the
entry proof running the reversed action's Leibniz sum over the
source enumeration against the pair list's own concatenation
split, with the unoccupied second letter's one-sided images the
sum's unit at the truncating memberwise sum.

`lem:blockirr`(iv)'s word tier runs over a walk table
(`WalkTable`), `con:units`' unit space read at one adjacent letter
pair: the lowering is the step, the raising its transpose, the two
content moves the grading, and the pair's commutator `[E, F] = H`
(both vacant arms included), the transpose identity and distinct
letters' commutation are its laws.  A word acts as the fold of the
table's steps (`wactT`) with the content chain its own
(`wcontentT`), and the pairings are graded (`dotG`, `con:places`'
orthogonality: the coordinate fold inside one content summand,
distinct contents at the sum's unit).  The walk carries a table
per side with the two crossings' scalars tied cross-added
(`wordGramWalkT`, `wordGramT`, `wordGramStepT`), so no content
match is read: the reversed word walks across the transposes, each
crossing folding into a content read with a shorter word's
pairing, and a raising's read at a top is the sum's unit.
`lowerTable` is the matrix units' own table at the adjacent
letters, and the lowering words' reads (`wact`, `wcontent`,
`wordGram`, `wordGramRaise`, `wordGramRaise2`) are its instances.

The span's semantic tier: the pool's growth is an append with
every appended member an occupied lowering image, read through the
parametric bridge `blockSpan_reads`/`blockSpan_all` — a predicate
at the exhibit kept by the lowerings holds over the whole span,
the members beyond the head marked as images — with the image's
own data `lowerH_reads` and the head's content `content_exhibit`
(the exhibit's content is the row list, the fold's indicator
counts collecting to the rows); `lem:lowerspan`'s discharge
instantiates the bridge at the dominance and height invariants.
`lem:blockirr`'s own two span data ride the same growth: the
letter width (`blockSpan_width`, the exhibit's row list at the
base and the moves' length preservation at the step) and the
indexed provenance (`blockSpan_prov`, the head equation with every
later member an occupied interior lowering of a member listed at
or before its predecessor — a round's joins are the frontier's
images and the frontier is a suffix of the pool, so the preimage's
key precedes the joined member's).
The membership guard is `lem:lowerspan`'s span-membership read at
`def:elim`'s residual — a candidate joins its content group
exactly where the residual sits off the unit tail, the test's
two-way certificates (`elim.resid_sound`, `elim.resid_complete`,
`elim.indep_extend`, `elim.indep_det`) the guard's semantics.  The
guard's soundness rides the pool groups' independence, maintained
by the certificates from the independent seed — the seed proven at
every shape (`exhibit_off_unit`: the distinguished arrangement's
coefficient survives every tensor step, the factors' distinguished
pair unique at the concatenation's rank) — and the closure's
fixpoint read is proven with it (`blockSpan_sem` at a stated
measure: the fuel covers the measure's fold, a rejected candidate a
span member of its group, the groups independent throughout, one
member joined per refusal).  The stationary read runs both ways: a
seed whose every interior lowering reads the sum's unit stands
alone in its span (`blockSpan_stationary`), and a seed closure
standing at one member reads every interior lowering back at the
unit tail (`closeSpan_seed_line`) — the round's candidates each
refused the collection, the refusal the null read or the vacant
group's residual, the residual at the vacant group the
coordinates' own.  The span's linearity reads and the
width bound are landed at their owner (`elim.spanRel_null`,
`spanRel_scale`, `spanRel_add`, `indep_bound` — the tex's stated
cap at `lem:lowerspan`), and the unit-family test's Bool reads
(`allU_of_unitTail`, `unitTail_of_allU`) join `settledAt`'s first
disjunct to the unit tail for the consumers.  The exhibit's top
read is landed (`exhibit_top`, `lem:tops`(iii)), the wedge's own
factor beside it (`wedge_top`), with the wedge-tensored raising
reading the sum's unit exactly where the further factor's own
raising does (`act_tensorW_unit`, the lowering's mirror at
`lowerH_tensorW_unit`: the letter pair's action splits over the
tensor, the wedge arm reads the unit at the repeat, and at a
letter vacant in the further factor both reads are the unit
outright): an adjacent
raising's image of the column exhibit reads the sum's unit at
every coordinate — the wedge's repeat transposition joins the
arrangements in opposite-parity pairs, the tensor's raising splits
over the concatenation, and the whole proof rides the reversed
action's own output list (`units.countOf_unitAct_swap`).  The
span's closure is landed (`lem:lowerspan`'s word induction): the
letter-pair move and the unit's action at the general pair
(`moveAt`, `act`, `con:units`' objects at the carrier), with every
distinct pair's action sending members to settled vectors
(`act_closed`) and transporting a group's span into the moved
group's (`act_span`) — parametric in the span's semantic reads
(`lowerspan.spanReads` the instantiation), the adjacent raisings by
the induction along the pool's growth seeded at the top read and
stepped through the table's matrix tier (`units.matVec_pair_read`,
`units.matVec_swap_read`), the further pairs by the gap descent at
the crossed composites (`units.matVec_comm_read`).  The remaining
arrivals sit with the string decomposition (`lem:strings`): the
pairs' orthogonal string exhaustion with the trace tier beneath
`lem:casimir`'s recursion, and the dimension identification
closing the span occupancy onto the block dimension through the
landed exchange read (`elim.span_count_eq`: two independent lists
inside one span read one count).  The bumped shape's walk
correspondence is landed (`lem:dualread`(ii)'s transport at the
stated measure): the two walks pair member for member through the
closure's own induction — the wedge-tensored candidate the
partner's class at an occupied letter and a refused unit tail at
a vacant one, the membership decisions synchronized through the
span transport at the wedge withdrawn — with the dimension and
the shifted-content occupancies the mapped span's
(`blockSpan_addFull`, `occupancy_addFull`, the lowering's class
congruence `lowerH_move` beside them), the bumped shape's row list
the wedge's content joined to the row list (`rowList_addFull`).

The pool group's own kit is public for the consumers above it: the
head split and the join (`groupAt_cons`, `groupAt_append`), the
width at a sized family (`rowsLen_groupAt`), the rows' provenance
(`groupAt_rows`), the membership read's split (`memAll_split`
beside `ground.all_of_append _ _ _`), the content occupancy read structurally
(`occ`, `occupancyAt_eq_occ`) with the group's row count at it
(`length_groupAt`, `groupAt_occupancy`), the letter-pair action's
width (`act_sized`) with its round trip at every pair
(`moveAt_round_at`), and the width predicate's decidable read
(`sized`).
-/

namespace blockcount
open ground places

set_option genInjectivity false in
/-- A content-homogeneous vector: its content with its coordinates
over the content's own monomials, the coordinate family's keys. -/
structure HVec where
  content : List Nat
  coords : List BPair

/-- Decidable equality on the carrier, the content and the
coordinate family's own (hand-written: the generated `injEq` route
is disabled with the injectivity lemmas). -/
def HVec.decEq : (a b : HVec) → Decidable (a = b)
  | ⟨c1, x1⟩, ⟨c2, x2⟩ =>
    if h1 : c1 = c2 then
      if h2 : x1 = x2 then isTrue (by rw [h1, h2])
      else isFalse (fun hh => h2 (congrArg HVec.coords hh))
    else isFalse (fun hh => h1 (congrArg HVec.content hh))

instance : DecidableEq HVec := HVec.decEq

/-- The wedge tensor at a column length: the swap-graded sum over
the arrangements, each monomial on its permutation's side. -/
def wedge (d l : Nat) : HVec :=
  let mu := (List.range d).map (fun i => if i < l then 1 else 0)
  ⟨mu, (monomialsAt mu).map (fun m =>
    if parity m then (BPair.ofNat 1).swap else BPair.ofNat 1)⟩

/-- The tensor of two homogeneous vectors: contents add, each
coordinate pair's product entering at the concatenated monomial. -/
def tensorH (v w : HVec) : HVec :=
  let mu := List.zipWith (fun a b => a + b) v.content w.content
  let monos := monomialsAt mu
  ⟨mu,
    ((List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
              w.coords).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt (rankOf (p.1 ++ q.1) mu) (p.2 * q.2) acc2)
            acc)
      (monos.map (fun _ => BPair.unit))).map BPair.norm⟩

/-- The graded pairing: the coordinate fold within one content
summand, two distinct contents pairing at the sum's unit —
`con:places`' grading orthogonality read on the carrier. -/
def dotG (v w : HVec) : BPair :=
  if v.content = w.content then elim.dotP v.coords w.coords
  else BPair.unit

/-- At one content the graded pairing is the coordinate fold. -/
theorem dotG_read (v w : HVec) (h : v.content = w.content) :
    dotG v w = elim.dotP v.coords w.coords := by
  show (if v.content = w.content then elim.dotP v.coords w.coords
    else BPair.unit) = _
  exact if_pos h

/-- At distinct contents the graded pairing is the sum's unit. -/
private theorem dotG_off (v w : HVec) (h : ¬ v.content = w.content) :
    dotG v w = BPair.unit := by
  show (if v.content = w.content then elim.dotP v.coords w.coords
    else BPair.unit) = _
  exact if_neg h

/-- The graded pairing's exchange, the coordinate fold's own. -/
theorem dotG_comm (v w : HVec) : dotG v w = dotG w v := by
  by_cases h : v.content = w.content
  · rw [dotG_read v w h, dotG_read w v h.symm, elim.dotP_comm]
  · rw [dotG_off v w h, dotG_off w v (fun hh => h hh.symm)]

/-- A unit-tailed right member pairs at the sum's unit, at either
guard: the fold's own null read inside the content summand and the
grading's unit outside it. -/
private theorem dotG_null_right (v w : HVec) (h : poly.unitTail w.coords) :
    (dotG v w).oneValue BPair.unit := by
  by_cases hg : v.content = w.content
  · rw [dotG_read v w hg]
    exact elim.dotP_null_tail_right _ _ h
  · rw [dotG_off v w hg]
    exact BPair.oneValue_refl _

/-- A unit-tailed left member pairs at the sum's unit, at either
guard. -/
private theorem dotG_null_left (v w : HVec) (h : poly.unitTail v.coords) :
    (dotG v w).oneValue BPair.unit := by
  by_cases hg : v.content = w.content
  · rw [dotG_read v w hg]
    exact elim.dotP_null_tail_left _ _ h
  · rw [dotG_off v w hg]
    exact BPair.oneValue_refl _

private def columnLengths (s : Shape) : List Nat :=
  (List.range s.length).reverse.flatMap (fun i =>
    List.replicate (ground.getAt 0 s i) (i + 1))

/-- The column exhibit: the wedge tensors over the sorted column
lengths, one factor per column, the unit shape's the scalar one. -/
def exhibit (s : Shape) : HVec :=
  (columnLengths s).foldl (fun acc l => tensorH acc (wedge s.length l))
    ⟨List.replicate s.length 0, [BPair.ofNat 1]⟩

/-- The adjacent lowering on a homogeneous vector, an occupancy
read: absent where the moved letter is unoccupied. -/
def lowerH (j : Nat) (v : HVec) : Option HVec :=
  if 0 < ground.getAt 0 v.content j then
    let mu := units.moveDn j v.content
    some ⟨mu, elim.matVec (units.matUnitAt mu v.content (j + 1) j)
      v.coords⟩
  else none

/-- The unit-family test, the coordinates' Bool fold at the unit
read — `settledAt`'s first disjunct and the producer's null
filter. -/
def allU : List BPair → Bool
  | [] => true
  | a :: t => (if a.oneValue BPair.unit then true else false) && allU t

private def tryAdd (pool : List HVec) (v : HVec) : List HVec :=
  if allU v.coords then pool
  else
    let group := pool.filter (fun w => w.content == v.content)
    if poly.unitTail (elim.residV v.coords.length
        (group.map HVec.coords) v.coords) then pool
    else pool ++ [v]

/-- The lowering closure at stated seeds: each round joins the
frontier's occupied interior lowerings at the membership guard,
the fuel the stabilization bound — `blockSpan`'s engine at the
exhibit seeds, the exhaustion tier's at a stated top's. -/
def closeSpan (d : Nat) : Nat → List HVec → List HVec →
    List HVec
  | 0, pool, _ => pool
  | fuel + 1, pool, frontier =>
    match frontier with
    | [] => pool
    | _ :: _ =>
      let pool' :=
        (frontier.flatMap (fun v => (List.range (d - 1)).flatMap
          (fun j =>
            match lowerH j v with
            | some w => [w]
            | none => []))).foldl tryAdd pool
      closeSpan d fuel pool' (pool'.drop pool.length)

/-- The block's span: the lowering closure of the column exhibit, a
content-graded independent list, the words' stabilization bound the
closure's fuel. -/
def blockSpan (s : Shape) : List HVec :=
  closeSpan s.length (degree s * s.length) [exhibit s] [exhibit s]

/-- The span's occupancy at a content, the content grading's own
read. -/
def occupancyAt (span : List HVec) (mu : List Nat) : Nat :=
  span.foldl (fun acc v => if v.content = mu then acc + 1 else acc) 0

/-- The block count in the power: the kernel dimension of the
stacked raisings on the content summand. -/
def countPower (lam : Shape) : Nat :=
  elim.kernelDim (monomialsAt (rowList lam)).length
    (units.stackedRaise (rowList lam))

/-- The stated pair list at a content: the two blocks' spanning
lists' tensors at complementary contents, contents adding over the
factors (`lem:blockcount`(iii)). -/
def pairsAt (A B : List HVec) (cc : List Nat) : List HVec :=
  A.flatMap (fun v =>
    B.flatMap (fun w =>
      if List.zipWith (fun x y => x + y) v.content w.content = cc
          then
        [tensorH v w]
      else []))

/-- The fused pool at two spanning lists: every tensor of a member
of the first with a member of the second, the fused carrier
(`lem:blockcount`(iii)). -/
def fusedAt (A B : List HVec) : List HVec :=
  A.flatMap (fun v => B.map (tensorH v))

/-- The fusion count `N^c_{ab} = N_c(W_a ⊗ W_b)`: the kernel
dimension of the stacked raisings against the fused content
summand's stated pair list, the tensor pairs at complementary
contents. -/
def fusionCount (a b c : Shape) : Nat :=
  let cc := rowList c
  let pairs := pairsAt (blockSpan a) (blockSpan b) cc
  elim.kernelDim pairs.length
    (elim.crossM (units.stackedRaise cc) (pairs.map HVec.coords))

/-! The span's structural reads (`lem:lowerspan`'s carrier tier):
every predicate holding at the exhibit and kept by the occupied
lowerings holds at every span member, and the members beyond the
head are lowering images outright — the bridge `blockSpan_reads`,
quantified over the predicate so the consumers instantiate their
own invariants, with `content_exhibit` tying the head's content to
the row list. -/

/-- The nil family reads every predicate. -/
theorem memAll_nil {α : Type} {P : α → Prop} :
    ∀ v ∈ ([] : List α), P v := fun _ h => nomatch h

/-- The head's read joined to the tail's. -/
theorem memAll_cons {α : Type} {P : α → Prop} {a : α}
    {t : List α} (ha : P a) (ht : ∀ v ∈ t, P v) :
    ∀ v ∈ a :: t, P v
  | _, .head _ => ha
  | _, .tail _ h => ht _ h

/-- The head's own read. -/
theorem memAll_head {α : Type} {P : α → Prop} {a : α}
    {t : List α} (h : ∀ v ∈ a :: t, P v) : P a :=
  h a (List.Mem.head t)

/-- The tail's read. -/
theorem memAll_tail {α : Type} {P : α → Prop} {a : α}
    {t : List α} (h : ∀ v ∈ a :: t, P v) : ∀ v ∈ t, P v :=
  fun v hv => h v (List.Mem.tail a hv)

/-- The read splits back off a join of families. -/
theorem memAll_split {α : Type} {P : α → Prop} {a b : List α}
    (h : ∀ v ∈ a ++ b, P v) :
    (∀ v ∈ a, P v) ∧ (∀ v ∈ b, P v) :=
  ⟨fun v hv => h v (ground.mem_append_left b hv),
   fun v hv => h v (ground.mem_append_right a hv)⟩

private theorem revRange_succ : ∀ k : Nat,
    (List.range (k + 1)).reverse
      = ((List.range k).reverse.map (fun x => x + 1)) ++ [0]
  | 0 => rfl
  | k + 1 => by
    have h1 : (List.range (k + 1)).reverse
        = k :: (List.range k).reverse := by
      rw [range_succ k, ground.reverse_snoc]
    have h2 : (k : Nat) :: (List.range k).reverse
        = (List.range k).reverse.map (fun x => x + 1) ++ [0] := by
      rw [← h1]
      exact revRange_succ k
    rw [range_succ (k + 1), ground.reverse_snoc, h1]
    show (k + 1) :: (k :: (List.range k).reverse)
      = ((k + 1) :: (List.range k).reverse.map (fun x => x + 1))
        ++ [0]
    exact congrArg (List.cons (k + 1)) h2

/-! The exhibit's content is the row list: the fold's content adds
one indicator per column, and the counts collect to the rows. -/

private theorem countAbove_append (i : Nat) : ∀ a b : List Nat,
    ground.countAbove i (a ++ b)
      = ground.countAbove i a + ground.countAbove i b
  | [], b => (Nat.zero_add (ground.countAbove i b)).symm
  | l :: t, b => by
    show ground.countAbove i (l :: (t ++ b))
      = ground.countAbove i (l :: t) + ground.countAbove i b
    rw [ground.countAbove_cons, ground.countAbove_cons,
      countAbove_append i t b, Nat.add_assoc]

private theorem countAbove_zero_succ : ∀ l : List Nat,
    ground.countAbove 0 (l.map (fun x => x + 1)) = l.length
  | [] => rfl
  | x :: t => by
    show (if 0 < x + 1 then 1 else 0)
        + ground.countAbove 0 (t.map (fun x => x + 1))
      = t.length + 1
    rw [if_pos (Nat.succ_pos x), countAbove_zero_succ t, Nat.add_comm]

private theorem countAbove_succ_succ (i : Nat) : ∀ l : List Nat,
    ground.countAbove (i + 1) (l.map (fun x => x + 1))
      = ground.countAbove i l
  | [] => rfl
  | x :: t => by
    show ground.countAbove (i + 1) ((x + 1) :: t.map (fun x => x + 1))
      = ground.countAbove i (x :: t)
    rw [ground.countAbove_cons, ground.countAbove_cons,
      countAbove_succ_succ i t]
    by_cases h : i < x
    · rw [if_pos h, if_pos (Nat.succ_lt_succ h)]
    · rw [if_neg h,
        if_neg (fun hs => h (Nat.lt_of_succ_lt_succ hs))]

private theorem countAbove_replicate_one (n : Nat) :
    ground.countAbove 0 (List.replicate n 1) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show (if 0 < 1 then 1 else 0) + ground.countAbove 0 (List.replicate m 1)
      = m + 1
    rw [if_pos (Nat.succ_pos 0), ih, Nat.add_comm]

private theorem countAbove_replicate_succ (i n : Nat) :
    ground.countAbove (i + 1) (List.replicate n 1) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show (if i + 1 < 1 then 1 else 0)
        + ground.countAbove (i + 1) (List.replicate m 1) = 0
    rw [ih, if_neg (fun h =>
      Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ h))]

private theorem flatMap_shift (n : Nat) (t : Shape) : ∀ l : List Nat,
    l.flatMap (fun x =>
      List.replicate (ground.getAt 0 (n :: t) (x + 1)) (x + 1 + 1))
      = (l.flatMap (fun x =>
          List.replicate (ground.getAt 0 t x) (x + 1))).map
        (fun y => y + 1)
  | [] => rfl
  | x :: r => by
    show List.replicate (ground.getAt 0 (n :: t) (x + 1)) (x + 1 + 1)
        ++ r.flatMap (fun x =>
          List.replicate (ground.getAt 0 (n :: t) (x + 1))
            (x + 1 + 1))
      = (List.replicate (ground.getAt 0 t x) (x + 1)
        ++ r.flatMap (fun x =>
          List.replicate (ground.getAt 0 t x) (x + 1))).map
        (fun y => y + 1)
    rw [flatMap_shift n t r, ground.map_append, ground.map_replicate]
    rfl

private theorem columnLengths_cons (n : Nat) (t : Shape) :
    columnLengths (n :: t)
      = (columnLengths t).map (fun x => x + 1)
        ++ List.replicate n 1 := by
  have h0 : ([0] : List Nat).flatMap
      (fun i => List.replicate (ground.getAt 0 (n :: t) i) (i + 1))
      = List.replicate n 1 := by
    show List.replicate (ground.getAt 0 (n :: t) 0) (0 + 1) ++ []
      = List.replicate n 1
    exact ground.append_nil _
  show (List.range (t.length + 1)).reverse.flatMap
      (fun i => List.replicate (ground.getAt 0 (n :: t) i) (i + 1))
    = _
  rw [revRange_succ t.length, ground.flatMap_append, flatMap_map,
    flatMap_shift n t, h0]
  rfl

private theorem columnLengths_length : ∀ s : Shape,
    (columnLengths s).length = sumNat s
  | [] => rfl
  | n :: t => by
    rw [columnLengths_cons n t, ground.length_append,
      ground.length_map, columnLengths_length t,
      ground.length_replicate 1 n]
    show sumNat t + n = n + sumNat t
    exact Nat.add_comm _ _

private theorem countAbove_columnLengths : ∀ (s : Shape) (i : Nat),
    ground.countAbove i (columnLengths s) = ground.getAt 0 (rowList s) i
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | n :: t, 0 => by
    rw [columnLengths_cons n t, countAbove_append,
      countAbove_zero_succ, columnLengths_length t,
      countAbove_replicate_one n]
    show sumNat t + n = ground.getAt 0 ((n + sumNat t) :: rowList t) 0
    show sumNat t + n = n + sumNat t
    exact Nat.add_comm _ _
  | n :: t, i + 1 => by
    rw [columnLengths_cons n t, countAbove_append,
      countAbove_succ_succ, countAbove_replicate_succ,
      countAbove_columnLengths t i]
    exact Nat.add_zero _


/-- The tensor's content is the componentwise sum, the carrier's
own field. -/
theorem content_tensorH (v w : HVec) :
    (tensorH v w).content
      = List.zipWith (fun a b => a + b) v.content w.content := rfl

/-- The wedge's content: the indicator family at the column
length. -/
theorem content_wedge (d l : Nat) :
    (wedge d l).content
      = (List.range d).map (fun i => if i < l then 1 else 0) := rfl

private theorem content_fold (d : Nat) :
    ∀ (cl : List Nat) (acc : HVec), acc.content.length = d →
      ((cl.foldl (fun a l => tensorH a (wedge d l)) acc)).content
        = (List.range d).map (fun i =>
            ground.getAt 0 acc.content i + ground.countAbove i cl)
  | [], acc, hl => by
    show acc.content = (List.range d).map (fun i =>
      ground.getAt 0 acc.content i + ground.countAbove i [])
    exact (ground.range_map_getAt 0 d acc.content hl).symm
  | l :: cl, acc, hl => by
    show ((cl.foldl (fun a l => tensorH a (wedge d l))
        (tensorH acc (wedge d l)))).content = _
    rw [content_fold d cl (tensorH acc (wedge d l))
      (by
        rw [content_tensorH]
        exact ground.length_zipWith (fun x y => x + y) acc.content (wedge d l).content d hl
          (by rw [content_wedge, ground.length_mapRange]))]
    refine ground.map_congr_members _ _ (List.range d)
      (fun i hi => ?_)
    have hid : i < d := by
      rw [ground.countOf_range i d] at hi
      by_cases h : i < d
      · exact h
      · rw [if_neg h] at hi
        exact absurd hi (Nat.lt_irrefl 0)
    rw [content_tensorH,
      ground.getAt_zipWith 0 0 0 (fun x y => x + y) acc.content (wedge d l).content i
        (by rw [hl]; exact hid)
        (by rw [content_wedge, ground.length_mapRange]; exact hid),
      content_wedge,
      ground.getAt_map 0 0 (fun i => if i < l then 1 else 0)
        (List.range d) i (by rw [ground.length_range]; exact hid),
      ground.getAt_range d i hid, Nat.add_assoc,
      ← ground.countAbove_cons]

/-- The exhibit's content is the row list, the head's content
read. -/
theorem content_exhibit (s : Shape) :
    (exhibit s).content = rowList s := by
  show ((columnLengths s).foldl
      (fun acc l => tensorH acc (wedge s.length l))
      ⟨List.replicate s.length 0, [BPair.ofNat 1]⟩).content = _
  rw [content_fold s.length (columnLengths s)
    ⟨List.replicate s.length 0, [BPair.ofNat 1]⟩
    (ground.length_replicate 0 s.length)]
  rw [ground.map_congr_all _
    (fun i => ground.getAt 0 (rowList s) i)
    (fun i => by
      show ground.getAt 0 (List.replicate s.length 0) i
          + ground.countAbove i (columnLengths s)
        = ground.getAt 0 (rowList s) i
      rw [getAt_replicate_zero s.length i, Nat.zero_add,
        countAbove_columnLengths s i]) (List.range s.length)]
  exact ground.range_map_getAt 0 s.length (rowList s)
    (places.length_rowList s)

/-- A present lowering image is its data outright: the moved
content with the letter pair's matrix action on the
coordinates. -/
theorem lowerH_eq {j : Nat} {v w : HVec} (h : lowerH j v = some w) :
    w = ⟨units.moveDn j v.content,
      elim.matVec (units.matUnitAt (units.moveDn j v.content)
        v.content (j + 1) j) v.coords⟩ := by
  by_cases hg : 0 < ground.getAt 0 v.content j
  · have h' : (some (⟨units.moveDn j v.content,
        elim.matVec (units.matUnitAt (units.moveDn j v.content)
          v.content (j + 1) j) v.coords⟩ : HVec)) = some w := by
      rw [← h]
      exact (if_pos hg).symm
    exact (Option.some.inj h').symm
  · have h' : (none : Option HVec) = some w := by
      rw [← h]
      exact (if_neg hg).symm
    exact nomatch h'

/-- A lowering image's reads: the occupied guard with the moved
content, the image's own data. -/
theorem lowerH_reads {j : Nat} {v w : HVec}
    (h : lowerH j v = some w) :
    0 < ground.getAt 0 v.content j
      ∧ w.content = units.moveDn j v.content := by
  by_cases hg : 0 < ground.getAt 0 v.content j
  · exact ⟨hg, congrArg HVec.content (lowerH_eq h)⟩
  · rw [lowerH, if_neg hg] at h
    exact nomatch h

/-! The pool's growth: an addition is an append, the appended
member a lowering image, and every predicate held at the pool and
kept by the images holds at the closure. -/

private theorem tryAdd_split (pool : List HVec) (v : HVec) :
    tryAdd pool v = pool ∨ tryAdd pool v = pool ++ [v] := by
  by_cases h1 : allU v.coords = true
  · exact Or.inl (if_pos h1)
  · have he : tryAdd pool v
        = (let group := pool.filter (fun w => w.content == v.content)
           if poly.unitTail (elim.residV v.coords.length
               (group.map HVec.coords) v.coords)
           then pool else pool ++ [v]) := if_neg h1
    rw [he]
    by_cases h2 : poly.unitTail (elim.residV v.coords.length
      (((pool.filter (fun w => w.content == v.content)).map
        HVec.coords)) v.coords)
    · exact Or.inl (if_pos h2)
    · exact Or.inr (if_neg h2)

private theorem foldl_tryAdd_reads (P : HVec → Prop) :
    ∀ (cands pool : List HVec), (∀ v ∈ cands, P v) →
      ∃ tail, cands.foldl tryAdd pool = pool ++ tail
        ∧ ∀ v ∈ tail, P v
  | [], pool, _ => ⟨[], (ground.append_nil pool).symm, memAll_nil⟩
  | c :: cs, pool, h => by
    show ∃ tail, cs.foldl tryAdd (tryAdd pool c) = pool ++ tail
      ∧ ∀ v ∈ tail, P v
    cases tryAdd_split pool c with
    | inl he =>
      rw [he]
      exact foldl_tryAdd_reads P cs pool (memAll_tail h)
    | inr he =>
      rw [he]
      obtain ⟨t2, ht2, hp2⟩ := foldl_tryAdd_reads P cs (pool ++ [c])
        (memAll_tail h)
      exact ⟨c :: t2, by rw [ht2, ground.append_assoc]; rfl,
        memAll_cons (memAll_head h) hp2⟩

private theorem cand_one (Q R : HVec → Prop) (d : Nat)
    (hstep : ∀ v w (j : Nat), j + 1 < d → Q v →
      lowerH j v = some w → Q w ∧ R w)
    (v : HVec) (hv : Q v) :
    ∀ k : Nat, (∀ j, j < k → j + 1 < d) →
      ∀ w ∈ (List.range k).flatMap (fun j =>
          match lowerH j v with
          | some w => [w]
          | none => []), Q w ∧ R w
  | 0, _ => memAll_nil
  | k + 1, hk => by
    rw [range_succ k, ground.flatMap_append]
    refine ground.all_of_append _ _ _
      (cand_one Q R d hstep v hv k
        (fun j hj => hk j (Nat.lt_succ_of_lt hj))) ?_
    show ∀ w ∈ ((match lowerH k v with
        | some w => [w]
        | none => []) ++ []), Q w ∧ R w
    rw [ground.append_nil]
    cases hlw : lowerH k v with
    | some w =>
      exact memAll_cons
        (hstep v w k (hk k (Nat.lt_succ_self k)) hv hlw) memAll_nil
    | none => exact memAll_nil

private theorem cand_all (Q R : HVec → Prop) (d : Nat)
    (hstep : ∀ v w (j : Nat), j + 1 < d → Q v →
      lowerH j v = some w → Q w ∧ R w) :
    ∀ fr : List HVec, (∀ v ∈ fr, Q v) →
      ∀ w ∈ fr.flatMap (fun v => (List.range (d - 1)).flatMap
          (fun j =>
            match lowerH j v with
            | some w => [w]
            | none => [])), Q w ∧ R w
  | [], _ => memAll_nil
  | v :: fs, h =>
    ground.all_of_append _ _ _
      (cand_one Q R d hstep v (memAll_head h) (d - 1)
        (fun _ hj => ground.succ_lt_of_lt_pred hj))
      (cand_all Q R d hstep fs (memAll_tail h))

private theorem closeSpan_reads (d : Nat) (Q R : HVec → Prop)
    (hstep : ∀ v w (j : Nat), j + 1 < d → Q v →
      lowerH j v = some w → Q w ∧ R w) :
    ∀ (fuel : Nat) (pool frontier : List HVec),
      (∀ v ∈ pool, Q v) → (∀ v ∈ frontier, Q v) →
      ∃ tail, closeSpan d fuel pool frontier = pool ++ tail
        ∧ ∀ v ∈ tail, Q v ∧ R v
  | 0, pool, _, _, _ =>
    ⟨[], (ground.append_nil pool).symm, memAll_nil⟩
  | _ + 1, pool, [], _, _ =>
    ⟨[], (ground.append_nil pool).symm, memAll_nil⟩
  | fuel + 1, pool, v :: fs, hp, hf => by
    show ∃ tail,
      (let pool' :=
        ((v :: fs).flatMap (fun v => (List.range (d - 1)).flatMap
          (fun j =>
            match lowerH j v with
            | some w => [w]
            | none => []))).foldl tryAdd pool
       closeSpan d fuel pool' (pool'.drop pool.length))
        = pool ++ tail ∧ ∀ v ∈ tail, Q v ∧ R v
    obtain ⟨t1, ht1, hqr1⟩ := foldl_tryAdd_reads
      (fun v => Q v ∧ R v)
      ((v :: fs).flatMap (fun v => (List.range (d - 1)).flatMap
        (fun j =>
          match lowerH j v with
          | some w => [w]
          | none => [])))
      pool (cand_all Q R d hstep (v :: fs) hf)
    show ∃ tail,
      closeSpan d fuel
        (((v :: fs).flatMap (fun v =>
          (List.range (d - 1)).flatMap (fun j =>
            match lowerH j v with
            | some w => [w]
            | none => []))).foldl tryAdd pool)
        ((((v :: fs).flatMap (fun v =>
          (List.range (d - 1)).flatMap (fun j =>
            match lowerH j v with
            | some w => [w]
            | none => []))).foldl tryAdd pool).drop pool.length)
        = pool ++ tail ∧ ∀ v ∈ tail, Q v ∧ R v
    rw [ht1, ground.drop_append_self pool t1]
    obtain ⟨t2, ht2, hqr2⟩ := closeSpan_reads d Q R hstep fuel
      (pool ++ t1) t1
      (ground.all_of_append _ _ _ hp (fun v hv => (hqr1 v hv).1))
      (fun v hv => (hqr1 v hv).1)
    exact ⟨t1 ++ t2, by rw [ht2, ground.append_assoc],
      ground.all_of_append _ _ _ hqr1 hqr2⟩

/-- The span's parametric read: a predicate at the exhibit kept by
the occupied lowerings holds over the whole span, the members
beyond the head lowering images with their own mark — the
consumers instantiate the invariant (`lem:lowerspan`'s bridge). -/
theorem blockSpan_reads (s : Shape) (Q R : HVec → Prop)
    (hbase : Q (exhibit s))
    (hstep : ∀ v w (j : Nat), j + 1 < s.length → Q v →
      lowerH j v = some w → Q w ∧ R w) :
    ∃ tail, blockSpan s = exhibit s :: tail
      ∧ ∀ v ∈ tail, Q v ∧ R v := by
  obtain ⟨tail, ht, hqr⟩ := closeSpan_reads s.length Q R hstep
    (degree s * s.length) [exhibit s] [exhibit s]
    (memAll_cons hbase memAll_nil) (memAll_cons hbase memAll_nil)
  exact ⟨tail, ht, hqr⟩

/-- The span's whole-family read, the bridge's weakening. -/
theorem blockSpan_all (s : Shape) (Q : HVec → Prop)
    (hbase : Q (exhibit s))
    (hstep : ∀ v w (j : Nat), j + 1 < s.length → Q v →
      lowerH j v = some w → Q w) :
    ∀ v ∈ blockSpan s, Q v := by
  obtain ⟨tail, ht, hqr⟩ := blockSpan_reads s Q (fun _ => True)
    hbase (fun v w j hj hv hw => ⟨hstep v w j hj hv hw, trivial⟩)
  rw [ht]
  exact memAll_cons hbase (fun v hv => (hqr v hv).1)

/-- The span's letter width: every member carries the shape's own
letter count, the exhibit's row list at the base and the moves'
length preservation at the step (`lem:blockirr`'s width datum). -/
theorem blockSpan_width (s : Shape) : ∀ v ∈ blockSpan s,
    v.content.length = s.length := by
  refine blockSpan_all s (fun v => v.content.length = s.length)
    ?_ ?_
  · rw [content_exhibit s]
    exact places.length_rowList s
  · intro v w j _ hv hlw
    rw [(lowerH_reads hlw).2, units.length_moveDn j v.content]
    exact hv

/-- The span's degree: every member's content reads the shape's box
total, the exhibit's row list at the base and the moves' box
preservation at the step, the width riding beside it
(`lem:blockcount`(iii)'s one-degree read of a block's contents). -/
theorem blockSpan_degree (s : Shape) : ∀ v ∈ blockSpan s,
    sumNat v.content = degree s := by
  have h : ∀ v ∈ blockSpan s,
      v.content.length = s.length ∧ sumNat v.content = degree s := by
    refine blockSpan_all s
      (fun v => v.content.length = s.length
        ∧ sumNat v.content = degree s) ?_ ?_
    · rw [content_exhibit s]
      exact ⟨places.length_rowList s, rfl⟩
    · intro v w j hj hv hlw
      obtain ⟨hocc, hct⟩ := lowerH_reads hlw
      refine ⟨?_, ?_⟩
      · rw [hct, units.length_moveDn j v.content]
        exact hv.1
      · rw [hct, units.sumNat_moveDn j v.content
          (by rw [hv.1]; exact hj) hocc]
        exact hv.2
  exact fun v hv => (h v hv).2

/-! The fundamental block's span (`lem:pieri`'s one-box factor at
`lem:adjchar`'s block, `V` itself): at one box in the first column
the span is the unit contents, one member per letter carrying the
one-coordinate unit read — the exhibit the first letter's, each
adjacent lowering the next letter's, and every further lowering
vacant, so the closure walks the letters once. -/

/-- The fundamental block's member at a letter: the unit content
with the one-coordinate unit read. -/
private def stdV (d i : Nat) : HVec := ⟨unitAt d i, [BPair.ofNat 1]⟩

private theorem moveDn_unitAt : ∀ (d i : Nat), i + 1 < d →
    units.moveDn i (unitAt d i) = unitAt d (i + 1)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | 1, _, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | m + 2, 0, _ => by
    rw [unitAt_zero (m + 1)]
    show (0 : Nat) :: (0 + 1) :: List.replicate m 0 = unitAt (m + 2) 1
    rw [unitAt_succ (m + 1) 0, unitAt_zero m]
  | n + 1, i + 1, h => by
    rw [unitAt_succ n i]
    show (0 : Nat) :: units.moveDn i (unitAt n i) = unitAt (n + 1) (i + 2)
    rw [moveDn_unitAt n i (Nat.lt_of_succ_lt_succ h), unitAt_succ n (i + 1)]

/-- A guard vacant at every key of the range keeps the fold's
seed. -/
private theorem rankFold_off (mu : List Nat) :
    ∀ (n a : Nat), (∀ b, b < n → ground.getAt 0 mu b = 0) →
      (List.range n).foldl (fun acc b =>
        if 0 < ground.getAt 0 mu b then acc + countMon (dipAt b mu)
        else acc) a = a
  | 0, _, _ => rfl
  | n + 1, a, h => by
    rw [ground.range_succ n, ground.foldl_append,
      rankFold_off mu n a (fun b hb => h b (Nat.lt_succ_of_lt hb))]
    show (if 0 < ground.getAt 0 mu n then a + countMon (dipAt n mu)
      else a) = a
    rw [h n (Nat.lt_succ_self n), if_neg (Nat.lt_irrefl 0)]

private theorem matUnitAt_std (d i : Nat) (hi : i + 1 < d) :
    units.matUnitAt (unitAt d (i + 1)) (unitAt d i) (i + 1) i
      = [[BPair.unit + BPair.ofNat 1]] := by
  have hrank : rankOf [i + 1] (unitAt d (i + 1)) = 0 := by
    show (List.range (i + 1)).foldl (fun acc b =>
        if 0 < ground.getAt 0 (unitAt d (i + 1)) b then
          acc + countMon (dipAt b (unitAt d (i + 1))) else acc) 0
      + rankOf [] (dipAt (i + 1) (unitAt d (i + 1))) = 0
    rw [rankFold_off (unitAt d (i + 1)) (i + 1) 0 (fun b hb => by
      rw [getAt_unitAt d (i + 1) b,
        if_pos (Nat.lt_trans hb hi),
        if_neg (Nat.ne_of_lt hb)])]
    rfl
  have hact : units.unitAct (i + 1) i [i] = [[i + 1]] := by
    show ((if i == i then [[i + 1]] else [])
      ++ (units.unitAct (i + 1) i []).map (fun m => i :: m))
      = [[i + 1]]
    rw [show (i == i) = true from ground.eqBeqOf rfl]
    rfl
  show elim.transposeM ((monomialsAt (unitAt d i)).map (fun s =>
      (units.unitAct (i + 1) i s).foldl
        (fun col m => if m.length = sumNat (unitAt d (i + 1))
            ∧ content (unitAt d (i + 1)).length m = unitAt d (i + 1) then
          units.scatterAt (rankOf m (unitAt d (i + 1))) (BPair.ofNat 1) col
          else col)
        ((monomialsAt (unitAt d (i + 1))).map (fun _ => BPair.unit))))
    = [[BPair.unit + BPair.ofNat 1]]
  rw [monomialsAt_unitAt d i (Nat.lt_of_succ_lt hi),
    monomialsAt_unitAt d (i + 1) hi, length_unitAt d (i + 1),
    sumNat_unitAt d (i + 1) hi]
  show elim.transposeM [(units.unitAct (i + 1) i [i]).foldl
      (fun col m => if m.length = 1 ∧ content d m = unitAt d (i + 1) then
        units.scatterAt (rankOf m (unitAt d (i + 1))) (BPair.ofNat 1) col
        else col) [BPair.unit]]
    = [[BPair.unit + BPair.ofNat 1]]
  rw [hact]
  show elim.transposeM [if ([i + 1] : List Nat).length = 1
      ∧ content d [i + 1] = unitAt d (i + 1) then
      units.scatterAt (rankOf [i + 1] (unitAt d (i + 1)))
        (BPair.ofNat 1) [BPair.unit]
      else [BPair.unit]]
    = [[BPair.unit + BPair.ofNat 1]]
  rw [if_pos (show ([i + 1] : List Nat).length = 1
      ∧ content d [i + 1] = unitAt d (i + 1)
    from ⟨rfl, content_unitAt d (i + 1)⟩), hrank]
  rfl

private theorem lowerH_std (d i : Nat) (hi : i + 1 < d) :
    lowerH i (stdV d i) = some (stdV d (i + 1)) := by
  have hocc : ground.getAt 0 (unitAt d i) i = 1 := by
    rw [getAt_unitAt d i i, if_pos (Nat.lt_of_succ_lt hi), if_pos rfl]
  show (if 0 < ground.getAt 0 (unitAt d i) i then
      some (⟨units.moveDn i (unitAt d i),
        elim.matVec (units.matUnitAt (units.moveDn i (unitAt d i))
          (unitAt d i) (i + 1) i) [BPair.ofNat 1]⟩ : HVec)
    else none) = some (stdV d (i + 1))
  rw [hocc, if_pos (Nat.succ_pos 0), moveDn_unitAt d i hi,
    matUnitAt_std d i hi]
  rfl

private theorem lowerH_std_off (d i j : Nat) (hj : ¬ j = i) :
    lowerH j (stdV d i) = none := by
  have hoff : ground.getAt 0 (unitAt d i) j = 0 := by
    rw [getAt_unitAt d i j]
    by_cases hjd : j < d
    · rw [if_pos hjd, if_neg hj]
    · rw [if_neg hjd]
  show (if 0 < ground.getAt 0 (unitAt d i) j then
      some (⟨units.moveDn j (unitAt d i),
        elim.matVec (units.matUnitAt (units.moveDn j (unitAt d i))
          (unitAt d i) (j + 1) j) [BPair.ofNat 1]⟩ : HVec)
    else none) = none
  rw [hoff, if_neg (Nat.lt_irrefl 0)]

private theorem columnLengths_unitShape (n : Nat) :
    columnLengths (List.replicate n 0) = [] :=
  ground.nil_of_length_zero _
    ((columnLengths_length (List.replicate n 0)).trans
      (sumNat_replicate_zero n))

private theorem columnLengths_unitAt_zero (n : Nat) :
    columnLengths (unitAt (n + 1) 0) = [1] := by
  rw [unitAt_zero n, columnLengths_cons 1 (List.replicate n 0),
    columnLengths_unitShape n]
  rfl

private theorem wedge_one_std (d : Nat) (hd : 0 < d) :
    wedge d 1 = ⟨unitAt d 0, [BPair.ofNat 1]⟩ := by
  have hmu : (List.range d).map (fun i => if i < 1 then 1 else 0)
      = unitAt d 0 := by
    show (List.range d).map (fun i => if i < 1 then 1 else 0)
      = (List.range d).map (fun j => if j = 0 then 1 else 0)
    exact ground.map_congr_all _ _
      (fun i => by
        by_cases hi : i = 0
        · rw [if_pos hi, if_pos (by rw [hi]; exact Nat.succ_pos 0)]
        · rw [if_neg hi, if_neg (fun hlt =>
            hi (Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.zero_le i)))])
      (List.range d)
  show (⟨(List.range d).map (fun i => if i < 1 then 1 else 0),
      (monomialsAt ((List.range d).map (fun i => if i < 1 then 1 else 0))).map
        (fun m => if parity m then (BPair.ofNat 1).swap
          else BPair.ofNat 1)⟩ : HVec)
    = ⟨unitAt d 0, [BPair.ofNat 1]⟩
  rw [hmu, monomialsAt_unitAt d 0 hd]
  rfl

private theorem tensorH_seed (n : Nat) :
    tensorH ⟨List.replicate (n + 1) 0, [BPair.ofNat 1]⟩
        ⟨unitAt (n + 1) 0, [BPair.ofNat 1]⟩
      = stdV (n + 1) 0 := by
  have hz : List.zipWith (fun a b => a + b) (List.replicate (n + 1) 0)
      (unitAt (n + 1) 0) = unitAt (n + 1) 0 :=
    ground.zipWith_zero_left (n + 1) (unitAt (n + 1) 0)
      (length_unitAt (n + 1) 0)
  have hv : monomialsAt (List.replicate (n + 1) 0) = [[]] :=
    monomialsAt_sum_zero _ (sumNat_replicate_zero (n + 1))
  have hw : monomialsAt (unitAt (n + 1) 0) = [[0]] :=
    monomialsAt_unitAt (n + 1) 0 (Nat.succ_pos n)
  show (⟨List.zipWith (fun a b => a + b) (List.replicate (n + 1) 0)
        (unitAt (n + 1) 0),
      ((List.zipWith (fun m x => (m, x))
          (monomialsAt (List.replicate (n + 1) 0))
          [BPair.ofNat 1]).foldl
        (fun acc p =>
          if p.2.isUnitRep then acc
          else (List.zipWith (fun m x => (m, x))
              (monomialsAt (unitAt (n + 1) 0)) [BPair.ofNat 1]).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt
                (rankOf (p.1 ++ q.1)
                  (List.zipWith (fun a b => a + b)
                    (List.replicate (n + 1) 0) (unitAt (n + 1) 0)))
                (p.2 * q.2) acc2)
            acc)
        ((monomialsAt (List.zipWith (fun a b => a + b)
            (List.replicate (n + 1) 0) (unitAt (n + 1) 0))).map
          (fun _ => BPair.unit))).map BPair.norm⟩ : HVec)
    = stdV (n + 1) 0
  rw [hz, hv, hw]
  rfl

private theorem exhibit_std (n : Nat) :
    exhibit (unitAt (n + 1) 0) = stdV (n + 1) 0 := by
  show (columnLengths (unitAt (n + 1) 0)).foldl
      (fun acc l => tensorH acc (wedge (unitAt (n + 1) 0).length l))
      ⟨List.replicate (unitAt (n + 1) 0).length 0, [BPair.ofNat 1]⟩
    = stdV (n + 1) 0
  rw [columnLengths_unitAt_zero n, length_unitAt (n + 1) 0]
  show tensorH ⟨List.replicate (n + 1) 0, [BPair.ofNat 1]⟩
      (wedge (n + 1) 1) = stdV (n + 1) 0
  rw [wedge_one_std (n + 1) (Nat.succ_pos n)]
  exact tensorH_seed n

private theorem flatMap_range_pick {α : Type} (f : Nat → List α)
    (i : Nat) (hoff : ∀ k, ¬ k = i → f k = []) :
    ∀ n : Nat, i < n → (List.range n).flatMap f = f i
  | 0, h => absurd h (Nat.not_lt_zero i)
  | n + 1, h => by
    rw [ground.range_succ n, ground.flatMap_append]
    cases Nat.lt_or_ge i n with
    | inl hin =>
      rw [flatMap_range_pick f i hoff n hin]
      show f i ++ (f n ++ []) = f i
      rw [hoff n (fun he =>
        absurd hin (by rw [he]; exact Nat.lt_irrefl i))]
      exact ground.append_nil (f i)
    | inr hge =>
      have hie : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
      rw [ground.flatMap_nil f (List.range n) (fun k hkm =>
          hoff k (fun he =>
            absurd (ground.ltOfMemRange hkm)
              (by rw [he, hie]; exact Nat.lt_irrefl n)))]
      show [] ++ (f n ++ []) = f i
      rw [hie]
      exact ground.append_nil (f n)

private theorem imgs_std_step (d k : Nat) (hk : k + 1 < d) :
    ([stdV d k].flatMap (fun v => (List.range (d - 1)).flatMap
        (fun j => match lowerH j v with
          | some w => [w]
          | none => []))) = [stdV d (k + 1)] := by
  have hkd : k < d - 1 := by
    match d, hk with
    | m + 1, hk => exact Nat.lt_of_succ_lt_succ hk
  show (List.range (d - 1)).flatMap
      (fun j => match lowerH j (stdV d k) with
        | some w => [w]
        | none => []) ++ [] = [stdV d (k + 1)]
  rw [flatMap_range_pick
      (fun j => match lowerH j (stdV d k) with
        | some w => [w]
        | none => [])
      k
      (fun j hj => by
        show (match lowerH j (stdV d k) with
          | some w => [w]
          | none => []) = []
        rw [lowerH_std_off d k j hj])
      (d - 1) hkd]
  show (match lowerH k (stdV d k) with
    | some w => [w]
    | none => []) ++ [] = [stdV d (k + 1)]
  rw [lowerH_std d k hk]
  rfl

private theorem imgs_std_top (d k : Nat) (hk : k + 1 = d) :
    ([stdV d k].flatMap (fun v => (List.range (d - 1)).flatMap
        (fun j => match lowerH j v with
          | some w => [w]
          | none => []))) = [] := by
  have hoff : ∀ j, j < d - 1 → ¬ j = k := by
    intro j hj he
    rw [he, ← hk] at hj
    exact Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le hj (Nat.le_of_eq (Nat.succ_sub_one k)))
  show (List.range (d - 1)).flatMap
      (fun j => match lowerH j (stdV d k) with
        | some w => [w]
        | none => []) ++ [] = []
  rw [ground.flatMap_nil
      (fun j => match lowerH j (stdV d k) with
        | some w => [w]
        | none => [])
      (List.range (d - 1))
      (fun j hj => by
        have _hlt : j < d - 1 :=
          ground.ltOfMemRange hj
        show (match lowerH j (stdV d k) with
          | some w => [w]
          | none => []) = []
        rw [lowerH_std_off d k j (hoff j _hlt)])]
  rfl

/-- The unit contents off a stated letter miss that letter's own
group: the filter at the letter's content is vacant. -/
private theorem filter_nil_std (d m : Nat) :
    ∀ (l : List Nat),
      (∀ i, 0 < ground.countOf i l → i < d ∧ ¬ i = m) →
      (l.map (stdV d)).filter (fun w => w.content == unitAt d m) = []
  | [], _ => rfl
  | a :: t, h => by
    have ha : a < d ∧ ¬ a = m :=
      h a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    have hfalse : ((stdV d a).content == unitAt d m) = false := by
      cases hb : ((stdV d a).content == unitAt d m) with
      | true =>
        exact absurd (ground.listBeqEq hb) (unitAt_ne d a m ha.1 ha.2)
      | false => rfl
    show ((stdV d a :: t.map (stdV d)).filter
      (fun w => w.content == unitAt d m)) = []
    rw [ground.filter_cons_false
      (p := fun w => w.content == unitAt d m) (a := stdV d a)
      (l := t.map (stdV d)) hfalse]
    exact filter_nil_std d m t
      (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)))

private theorem tryAdd_std (d k : Nat) (hk : k + 1 < d) :
    tryAdd ((List.range (k + 1)).map (stdV d)) (stdV d (k + 1))
      = (List.range (k + 1)).map (stdV d) ++ [stdV d (k + 1)] := by
  have hfilter : ((List.range (k + 1)).map (stdV d)).filter
      (fun w => w.content == unitAt d (k + 1)) = [] := by
    refine filter_nil_std d (k + 1) (List.range (k + 1)) (fun i hi => ?_)
    have hik : i < k + 1 := by
      rw [countOf_range i (k + 1)] at hi
      by_cases hc : i < k + 1
      · exact hc
      · rw [if_neg hc] at hi
        exact absurd hi (Nat.lt_irrefl 0)
    exact ⟨Nat.lt_trans hik hk, Nat.ne_of_lt hik⟩
  show (if allU [BPair.ofNat 1] then (List.range (k + 1)).map (stdV d)
    else
      if poly.unitTail (elim.residV ([BPair.ofNat 1] : List BPair).length
          ((((List.range (k + 1)).map (stdV d)).filter
            (fun w => w.content == unitAt d (k + 1))).map HVec.coords)
          [BPair.ofNat 1]) then (List.range (k + 1)).map (stdV d)
      else (List.range (k + 1)).map (stdV d) ++ [stdV d (k + 1)])
    = (List.range (k + 1)).map (stdV d) ++ [stdV d (k + 1)]
  rw [show allU [BPair.ofNat 1] = false from rfl,
    if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
    hfilter]
  show (if poly.unitTail (elim.residV 1 [] [BPair.ofNat 1]) then
      (List.range (k + 1)).map (stdV d)
    else (List.range (k + 1)).map (stdV d) ++ [stdV d (k + 1)])
    = (List.range (k + 1)).map (stdV d) ++ [stdV d (k + 1)]
  rw [if_neg (show ¬ poly.unitTail
    (elim.residV 1 [] [BPair.ofNat 1]) from by decide +kernel)]

private theorem closeSpan_nil (d fuel : Nat) (pool : List HVec) :
    closeSpan d fuel pool [] = pool := by
  cases fuel with
  | zero => rfl
  | succ _ => rfl

private theorem closeSpan_std (d : Nat) : ∀ (fuel k : Nat),
    k + 1 ≤ d → d ≤ k + fuel + 1 →
    closeSpan d fuel ((List.range (k + 1)).map (stdV d)) [stdV d k]
      = (List.range d).map (stdV d)
  | 0, k, h1, h2 => by
    show (List.range (k + 1)).map (stdV d) = (List.range d).map (stdV d)
    rw [Nat.le_antisymm h1 h2]
  | fuel + 1, k, h1, h2 => by
    cases Nat.lt_or_ge (k + 1) d with
    | inl hlt =>
      have hstep : ((List.range (k + 1)).map (stdV d)
          ++ [stdV d (k + 1)]) = (List.range (k + 2)).map (stdV d) := by
        rw [ground.range_succ (k + 1), ground.map_append]
        rfl
      show closeSpan d fuel
          (([stdV d k].flatMap (fun v => (List.range (d - 1)).flatMap
              (fun j => match lowerH j v with
                | some w => [w]
                | none => []))).foldl tryAdd
            ((List.range (k + 1)).map (stdV d)))
          ((([stdV d k].flatMap (fun v => (List.range (d - 1)).flatMap
              (fun j => match lowerH j v with
                | some w => [w]
                | none => []))).foldl tryAdd
            ((List.range (k + 1)).map (stdV d))).drop
              ((List.range (k + 1)).map (stdV d)).length)
        = (List.range d).map (stdV d)
      rw [imgs_std_step d k hlt]
      show closeSpan d fuel
          (tryAdd ((List.range (k + 1)).map (stdV d)) (stdV d (k + 1)))
          ((tryAdd ((List.range (k + 1)).map (stdV d))
            (stdV d (k + 1))).drop
              ((List.range (k + 1)).map (stdV d)).length)
        = (List.range d).map (stdV d)
      rw [tryAdd_std d k hlt, ground.drop_append_self
        ((List.range (k + 1)).map (stdV d)) [stdV d (k + 1)], hstep]
      exact closeSpan_std d fuel (k + 1) hlt
        (by
          rw [Nat.add_right_comm k 1 fuel]
          exact h2)
    | inr hge =>
      have hkd : k + 1 = d := Nat.le_antisymm h1 hge
      show closeSpan d fuel
          (([stdV d k].flatMap (fun v => (List.range (d - 1)).flatMap
              (fun j => match lowerH j v with
                | some w => [w]
                | none => []))).foldl tryAdd
            ((List.range (k + 1)).map (stdV d)))
          ((([stdV d k].flatMap (fun v => (List.range (d - 1)).flatMap
              (fun j => match lowerH j v with
                | some w => [w]
                | none => []))).foldl tryAdd
            ((List.range (k + 1)).map (stdV d))).drop
              ((List.range (k + 1)).map (stdV d)).length)
        = (List.range d).map (stdV d)
      rw [imgs_std_top d k hkd]
      show closeSpan d fuel ((List.range (k + 1)).map (stdV d))
          (((List.range (k + 1)).map (stdV d)).drop
            ((List.range (k + 1)).map (stdV d)).length)
        = (List.range d).map (stdV d)
      rw [ground.dropLength ((List.range (k + 1)).map (stdV d)),
        closeSpan_nil d fuel ((List.range (k + 1)).map (stdV d)), hkd]

/-- The fundamental block's span: at one box the closure lists the
unit contents, one member per letter with the one-coordinate unit
read. -/
theorem blockSpan_fund (d : Nat) (hd : 0 < d) :
    blockSpan (unitAt d 0)
      = (List.range d).map (fun i =>
          ⟨unitAt d i, [BPair.ofNat 1]⟩) := by
  match d, hd with
  | n + 1, _ =>
    show closeSpan (unitAt (n + 1) 0).length
        (degree (unitAt (n + 1) 0) * (unitAt (n + 1) 0).length)
        [exhibit (unitAt (n + 1) 0)] [exhibit (unitAt (n + 1) 0)]
      = (List.range (n + 1)).map (stdV (n + 1))
    rw [length_unitAt (n + 1) 0, degree_unitAt n, Nat.one_mul, exhibit_std n]
    exact closeSpan_std (n + 1) (n + 1) 0
      (Nat.succ_le_succ (Nat.zero_le n))
      (by rw [Nat.zero_add]; exact Nat.le_succ (n + 1))

/-! The unit-family test's Prop reads: the Bool guard against the
unit tail, `settledAt`'s first disjunct joined for the
consumers. -/

/-- The unit-family test's forward read: a unit tail passes. -/
theorem allU_of_unitTail : ∀ v : List BPair,
    poly.unitTail v → allU v = true
  | [], _ => rfl
  | a :: t, h => by
    show ((if a.oneValue BPair.unit then true else false)
      && allU t) = true
    rw [if_pos (show a.oneValue BPair.unit from h.1)]
    exact allU_of_unitTail t h.2

/-- The unit-family test's backward read: a pass is a unit
tail. -/
theorem unitTail_of_allU : ∀ v : List BPair,
    allU v = true → poly.unitTail v
  | [], _ => trivial
  | a :: t, h => by
    have h' : ((if a.oneValue BPair.unit then true else false)
      && allU t) = true := h
    by_cases hu : a.oneValue BPair.unit
    · rw [if_pos hu] at h'
      exact ⟨hu, unitTail_of_allU t h'⟩
    · rw [if_neg hu] at h'
      exact Bool.noConfusion h'

/-! The span's fixpoint semantics (`lem:lowerspan`'s
joined-collection clause): the pool's content groups are
independent — one member joined per refusal — and at the returned
pool every member's
occupied adjacent lowering image sits in its content group's span,
the guard's certificates the reads (`def:elim`'s residual tier). -/

/-- The pool's group at a content: the members' coordinate rows. -/
def groupAt (pool : List HVec) (mu : List Nat) : elim.Mat :=
  (pool.filter (fun w => w.content == mu)).map HVec.coords

/-- A content's dimension over a stated carrier: the group's
collection count, `lem:lowerspan`'s joined-collection read at the
content summand. -/
def dimAt (pool : List HVec) (mu : List Nat) : Nat :=
  (elim.collectOf (places.monomialsAt mu).length
    (groupAt pool mu)).length

/-- The block count at a stated carrier: the kernel dimension of
the stacked raisings against the content summand's collected
list, `def:blockcount`'s read at `lem:lowerspan`'s
joined-collection. -/
def countAt (pool : List HVec) (mu : List Nat) : Nat :=
  elim.kernelDim
    (elim.collectOf (places.monomialsAt mu).length
      (groupAt pool mu)).length
    (elim.crossM (units.stackedRaise mu)
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt pool mu)))

/-- The coordinate width at the content's enumeration. -/
def sized (w : HVec) : Prop :=
  w.coords.length = (places.monomialsAt w.content).length

instance (w : HVec) : Decidable (sized w) :=
  inferInstanceAs (Decidable (_ = _))

/-- The group independence at every content the pool carries, the
refusal joins' read. -/
def indepAll (pool : List HVec) : Prop :=
  ∀ mu ∈ pool.map HVec.content,
    elim.indepRows (places.monomialsAt mu).length (groupAt pool mu)

instance (pool : List HVec) : Decidable (indepAll pool) :=
  inferInstanceAs (Decidable (∀ mu ∈ pool.map HVec.content,
    elim.indepRows (places.monomialsAt mu).length (groupAt pool mu)))

/-- A settled vector: the coordinates at the sum's unit, or the
vector inside its content group's span. -/
def settledAt (pool : List HVec) (w : HVec) : Prop :=
  allU w.coords = true
    ∨ elim.spanRel w.coords.length (groupAt pool w.content) w.coords

instance (pool : List HVec) (w : HVec) : Decidable (settledAt pool w) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The read at an option: the stated predicate at a present
vector, vacuous at the absent one. -/
def optRead (P : HVec → Prop) [DecidablePred P] :
    Option HVec → Prop
  | some w => P w
  | none => True

instance (P : HVec → Prop) [DecidablePred P] (o : Option HVec) :
    Decidable (optRead P o) :=
  match o with
  | some w => inferInstanceAs (Decidable (P w))
  | none => .isTrue trivial

/-- The closure read at a letter count: every member's occupied
adjacent lowering image is settled. -/
def closedAt (pool : List HVec) (d : Nat) : Prop :=
  ∀ v ∈ pool, ∀ j < d - 1, optRead (settledAt pool) (lowerH j v)

instance (pool : List HVec) (d : Nat) : Decidable (closedAt pool d) :=
  inferInstanceAs (Decidable (∀ v ∈ pool, ∀ j < d - 1,
    optRead (settledAt pool) (lowerH j v)))

/-- The closure read's equation form: at a pool member and an
interior letter a present lowering image is settled. -/
theorem closedAt_elim {pool : List HVec} {d : Nat}
    (h : closedAt pool d) :
    ∀ v ∈ pool, ∀ j w, j < d - 1 →
      lowerH j v = some w → settledAt pool w := by
  intro v hv j w hj he
  have h' := h v hv j hj
  rw [he] at h'
  exact h'

/-- The closure read off the equation form. -/
theorem closedAt_intro {pool : List HVec} {d : Nat}
    (h : ∀ v ∈ pool, ∀ j w, j < d - 1 →
      lowerH j v = some w → settledAt pool w) :
    closedAt pool d := by
  intro v hv j hj
  cases he : lowerH j v with
  | none => exact trivial
  | some w => exact h v hv j w hj he

/-- The group's head split: a member joins its own content's group
and passes every other. -/
theorem groupAt_cons (v : HVec) (t : List HVec)
    (mu : List Nat) :
    groupAt (v :: t) mu
      = match v.content == mu with
        | true => v.coords :: groupAt t mu
        | false => groupAt t mu := by
  show ((v :: t).filter (fun w => w.content == mu)).map HVec.coords
    = _
  rw [ground.filter_cons (fun w => w.content == mu) v t]
  cases hb : v.content == mu with
  | true => rfl
  | false => rfl

/-- Two realizations of one index list agreeing at their members'
contents carry one content group index by index: the group's head
test reads the content alone, so both pools' groups are the same
selected sublist's rows (`lem:blockirr`(iv)'s per-group word
list). -/
theorem groupAt_map_congr {α : Type} (F G : α → HVec)
    (hc : ∀ a, (F a).content = (G a).content) (mu : List Nat) :
    ∀ l : List α, ∃ sub : List α,
      groupAt (l.map F) mu = sub.map (fun a => (F a).coords)
        ∧ groupAt (l.map G) mu = sub.map (fun a => (G a).coords)
        ∧ (∀ a ∈ sub, a ∈ l)
        ∧ ∀ a ∈ sub, (F a).content = mu
  | [] => ⟨[], rfl, rfl, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | a :: t => by
    match groupAt_map_congr F G hc mu t with
    | ⟨sub, hF, hG, hmem, hcon⟩ =>
      cases hb : (F a).content == mu with
      | true =>
        refine ⟨a :: sub, ?_, ?_, ?_, ?_⟩
        · show groupAt (F a :: t.map F) mu
            = (F a).coords :: sub.map (fun a => (F a).coords)
          rw [groupAt_cons, hb, hF]
        · show groupAt (G a :: t.map G) mu
            = (G a).coords :: sub.map (fun a => (G a).coords)
          rw [groupAt_cons, ← hc a, hb, hG]
        · intro x hx
          match hx with
          | .head _ => exact List.Mem.head t
          | .tail _ hxt => exact List.Mem.tail a (hmem x hxt)
        · intro x hx
          match hx with
          | .head _ => exact ground.listBeqEq hb
          | .tail _ hxt => exact hcon x hxt
      | false =>
        refine ⟨sub, ?_, ?_, ?_, hcon⟩
        · show groupAt (F a :: t.map F) mu
            = sub.map (fun a => (F a).coords)
          rw [groupAt_cons, hb, hF]
        · show groupAt (G a :: t.map G) mu
            = sub.map (fun a => (G a).coords)
          rw [groupAt_cons, ← hc a, hb, hG]
        · exact fun x hx => List.Mem.tail a (hmem x hx)

/-- The group splits over a join of pools. -/
theorem groupAt_append (u w : List HVec) (mu : List Nat) :
    groupAt (u ++ w) mu = groupAt u mu ++ groupAt w mu := by
  show ((u ++ w).filter (fun x => x.content == mu)).map HVec.coords
    = _
  rw [ground.filter_append (fun x => x.content == mu) u w,
    ground.map_append]
  rfl

/-- A content the pool does not carry reads the vacant group. -/
theorem groupAt_nil_of_countOf :
    ∀ (pool : List HVec) (mu : List Nat),
      ground.countOf mu (pool.map HVec.content) = 0 →
      groupAt pool mu = []
  | [], _, _ => rfl
  | v :: t, mu, h => by
    have h' : (if mu = v.content then 1 else 0)
        + ground.countOf mu (t.map HVec.content) = 0 :=
      (ground.countOf_cons mu v.content (t.map HVec.content)).symm.trans h
    by_cases he : mu = v.content
    · rw [if_pos he, Nat.add_comm] at h'
      exact Nat.noConfusion h'
    · rw [if_neg he, Nat.zero_add] at h'
      rw [groupAt_cons v t mu]
      cases hb : v.content == mu with
      | true => exact absurd (ground.listBeqEq hb).symm he
      | false => exact groupAt_nil_of_countOf t mu h'

/-- A content off the pool's own contents filters to the vacant
group: the membership-bounded read's off-pool arm. -/
theorem groupAt_nil_of_not_mem (pool : List HVec) (mu : List Nat)
    (h : ¬ mu ∈ pool.map HVec.content) : groupAt pool mu = [] :=
  groupAt_nil_of_countOf pool mu
    (match Nat.eq_zero_or_pos
        (ground.countOf mu (pool.map HVec.content)) with
     | .inl hz => hz
     | .inr hp => absurd (ground.mem_of_countOf_pos mu _ hp) h)

/-- The independence at every content whatever, the bounded read's
own extension: off the pool's contents the group is vacant. -/
theorem indepAll_all {pool : List HVec} (h : indepAll pool)
    (mu : List Nat) :
    elim.indepRows (places.monomialsAt mu).length
      (groupAt pool mu) :=
  match Nat.eq_zero_or_pos
      (ground.countOf mu (pool.map HVec.content)) with
  | .inr hp => h mu (ground.mem_of_countOf_pos mu _ hp)
  | .inl hz => by
    rw [groupAt_nil_of_not_mem pool mu (fun hm =>
      absurd (ground.countOf_pos_of_mem hm)
        (by rw [hz]; exact Nat.lt_irrefl 0))]
    exact elim.indep_nil _

/-- A sized pool's group at a content has the content
enumeration's width at every row. -/
theorem rowsLen_groupAt (mu : List Nat) :
    ∀ pool : List HVec, (∀ v ∈ pool, sized v) →
      elim.rowsLen (places.monomialsAt mu).length (groupAt pool mu)
  | [], _ => True.intro
  | v :: t, hs => by
    rw [groupAt_cons v t mu]
    cases hb : v.content == mu with
    | true =>
      refine ⟨?_, rowsLen_groupAt mu t (memAll_tail hs)⟩
      rw [memAll_head hs, ground.listBeqEq hb]
    | false => exact rowsLen_groupAt mu t (memAll_tail hs)

/-- A stated list's member sits in its own rows' span
(`lem:lowerspan`'s membership at the collection's own read). -/
theorem span_of_mem (L : List HVec) (cc : List Nat)
    (u : HVec) (hu : u ∈ L)
    (hrows : elim.rowsLen (monomialsAt cc).length
      (L.map HVec.coords)) :
    elim.spanRel (monomialsAt cc).length (L.map HVec.coords)
      u.coords := by
  obtain ⟨j, hj, hju⟩ := ground.getAt_of_mem (⟨[], []⟩ : HVec) hu
  have hj' : j < (L.map HVec.coords).length := by
    rw [ground.length_map]; exact hj
  have h := elim.spanRel_getAt (monomialsAt cc).length
    (L.map HVec.coords) j hj' hrows
  rw [ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair)
    HVec.coords L j hj, hju] at h
  exact h

/-- A pool member's coordinate row sits in its own content group's
span, the row the group's own listed one. -/
theorem spanRel_groupAt_mem (P : List HVec) (x : HVec) (hx : x ∈ P)
    (hsz : ∀ w ∈ P, sized w) :
    elim.spanRel (places.monomialsAt x.content).length
      (groupAt P x.content) x.coords := by
  have hmem : x.coords ∈ groupAt P x.content :=
    ground.mem_map_to HVec.coords
      (ground.mem_filter_to (fun w => w.content == x.content) hx
        (ground.listEqBeq x.content))
  match ground.getAt_of_mem ([] : List BPair) hmem with
  | ⟨k, hk, he⟩ =>
    rw [← he]
    exact elim.spanRel_getAt _ _ k hk
      (rowsLen_groupAt x.content P hsz)

/-- The count reads the pool through its group's span alone,
`def:blockcount`'s own well-definedness: two stated carriers whose
content groups sit in one span read one count, the collections two
independent lists of the summand with the kernel dimensions one at
the stacked family (`elim.kernelDim_congr`, `lem:lowerspan`'s
two-list clause). -/
theorem countAt_congr (mu : List Nat) (P P' : List HVec)
    (hszP : ∀ x ∈ P, sized x) (hszP' : ∀ x ∈ P', sized x)
    (h1 : ∀ k, k < (groupAt P mu).length →
      elim.spanRel (places.monomialsAt mu).length (groupAt P' mu)
        (ground.getAt [] (groupAt P mu) k))
    (h2 : ∀ k, k < (groupAt P' mu).length →
      elim.spanRel (places.monomialsAt mu).length (groupAt P mu)
        (ground.getAt [] (groupAt P' mu) k)) :
    countAt P mu = countAt P' mu := by
  have hG : elim.rowsLen (places.monomialsAt mu).length
      (groupAt P mu) := rowsLen_groupAt mu P hszP
  have hG' : elim.rowsLen (places.monomialsAt mu).length
      (groupAt P' mu) := rowsLen_groupAt mu P' hszP'
  have hC := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt P mu) hG
  have hC' := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt P' mu) hG'
  refine elim.kernelDim_congr (places.monomialsAt mu).length
    (units.stackedRaise mu) _ _
    (units.rowsLen_stackedRaise mu) hC hC'
    (elim.collect_indep _ _ hG) (elim.collect_indep _ _ hG')
    ?_ ?_
  · intro k hk
    refine elim.spanRel_trans (places.monomialsAt mu).length
      (groupAt P' mu) _ _ hG' hC'
      (fun k2 hk2 => elim.collect_span_row _ _ hG' k2 hk2) ?_
    exact elim.spanRel_trans (places.monomialsAt mu).length
      (groupAt P mu) _ _ hG hG' h1
      (elim.collect_row_span _ _ hG k hk)
  · intro k hk
    refine elim.spanRel_trans (places.monomialsAt mu).length
      (groupAt P mu) _ _ hG hC
      (fun k2 hk2 => elim.collect_span_row _ _ hG k2 hk2) ?_
    exact elim.spanRel_trans (places.monomialsAt mu).length
      (groupAt P' mu) _ _ hG' hG h2
      (elim.collect_row_span _ _ hG' k hk)

/-! The content occupancy read structurally: the fold's own
recursion, the fold's accumulator, and the group's length. -/

/-- The content occupancy by structural recursion, the fold's own
read. -/
def occ (mu : List Nat) : List HVec → Nat
  | [] => 0
  | v :: t => (if v.content = mu then 1 else 0) + occ mu t

/-- The occupancy step at its additive spelling. -/
private theorem occStep_add (mu : List Nat) :
    ∀ (acc : Nat) (v : HVec),
      (if v.content = mu then acc + 1 else acc)
        = acc + (if v.content = mu then 1 else 0) := by
  intro acc v
  cases hv : decide (v.content = mu) with
  | true => rw [if_pos (of_decide_eq_true hv),
      if_pos (of_decide_eq_true hv)]
  | false =>
    have hne : ¬ v.content = mu := fun h => by
      rw [decide_eq_true h] at hv
      exact Bool.noConfusion hv
    rw [if_neg hne, if_neg hne]
    exact (Nat.add_zero acc).symm

/-- The seed hoists out of the occupancy fold (`ground.foldlSeed`
at the step's additive spelling). -/
private theorem occFold_acc (mu : List Nat) (l : List HVec)
    (acc : Nat) :
    l.foldl (fun acc v => if v.content = mu then acc + 1 else acc)
      acc
      = acc + l.foldl
        (fun acc v => if v.content = mu then acc + 1 else acc) 0 := by
  rw [ground.foldl_congr _ _ (occStep_add mu) l acc,
    ground.foldl_congr _ _ (occStep_add mu) l 0,
    ground.foldlSeed (fun v => if HVec.content v = mu then 1 else 0) l acc,
    ground.foldlSeed (fun v => if HVec.content v = mu then 1 else 0) l 0,
    Nat.zero_add]


/-- A family off a content reads its occupancy at the sum's
unit. -/
theorem occ_off {mu : List Nat} : ∀ l : List HVec,
    (∀ v ∈ l, ¬ v.content = mu) → occ mu l = 0
  | [], _ => rfl
  | v :: t, h => by
    show (if v.content = mu then 1 else 0) + occ mu t = 0
    rw [if_neg (h v (List.Mem.head t)),
      occ_off t (fun x hx => h x (List.Mem.tail v hx))]

/-- The span occupancy is the structural count. -/

theorem occupancyAt_eq_occ (mu : List Nat) :
    ∀ l : List HVec, occupancyAt l mu = occ mu l
  | [] => rfl
  | v :: t => by
    show t.foldl _ (if v.content = mu then 0 + 1 else 0)
      = (if v.content = mu then 1 else 0) + occ mu t
    rw [occFold_acc mu t _]
    show (if v.content = mu then 0 + 1 else 0) + occupancyAt t mu
      = _
    rw [occupancyAt_eq_occ mu t]


/-- The structural count is the content list's own, the map's
read: the occupancy family enters as the pool's contents. -/
theorem occ_eq_countOf (mu : List Nat) : ∀ span : List HVec,
    occ mu span = countOf mu (span.map HVec.content)
  | [] => rfl
  | v :: t => by
    show (if v.content = mu then 1 else 0) + occ mu t
      = countOf mu (v.content :: t.map HVec.content)
    rw [ground.countOf_cons, occ_eq_countOf mu t]
    by_cases h : v.content = mu
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun he => h he.symm)]
/-- The span's content count is the occupancy read at the content,
the two count spellings identified. -/
theorem span_countOf (lam : places.Shape) (x : List Nat) :
    ground.countOf x ((blockSpan lam).map HVec.content)
      = occupancyAt (blockSpan lam) x :=
  (occ_eq_countOf x (blockSpan lam)).symm.trans
    (occupancyAt_eq_occ x (blockSpan lam)).symm



/-- The group's row count is the content's structural count. -/
theorem length_groupAt (mu : List Nat) :
    ∀ pool : List HVec, (groupAt pool mu).length = occ mu pool
  | [] => rfl
  | v :: t => by
    rw [groupAt_cons v t mu]
    cases hb : v.content == mu with
    | true =>
      show (groupAt t mu).length + 1
        = (if v.content = mu then 1 else 0) + occ mu t
      rw [if_pos (ground.listBeqEq hb), length_groupAt mu t,
        Nat.add_comm]
    | false =>
      show (groupAt t mu).length
        = (if v.content = mu then 1 else 0) + occ mu t
      rw [if_neg (fun he : v.content = mu => by
          rw [he, ground.listEqBeq mu] at hb
          exact Bool.noConfusion hb),
        Nat.zero_add, length_groupAt mu t]

/-- The group's row count is the content's span occupancy. -/
theorem groupAt_occupancy (pool : List HVec) (mu : List Nat) :
    (groupAt pool mu).length = occupancyAt pool mu := by
  rw [occupancyAt_eq_occ mu pool, length_groupAt mu pool]

/-- A content's dimension over an independent carrier is its
occupancy: the collection keeps the whole group
(`lem:lowerspan`'s joined-collection at an independent list). -/
theorem dimAt_occ (P : List HVec) (hiP : indepAll P)
    (mu : List Nat) : dimAt P mu = occ mu P := by
  show (elim.collectOf (places.monomialsAt mu).length
    (groupAt P mu)).length = occ mu P
  rw [elim.collect_keep (places.monomialsAt mu).length
      (groupAt P mu) (indepAll_all hiP mu),
    length_groupAt mu P]

private theorem settled_mono (pool ext : List HVec) (w : HVec)
    (hs : ∀ v ∈ pool, sized v) (hx : ∀ v ∈ ext, sized v)
    (hw : sized w)
    (h : settledAt pool w) : settledAt (pool ++ ext) w := by
  cases h with
  | inl hu => exact Or.inl hu
  | inr hsp =>
    refine Or.inr ?_
    rw [groupAt_append pool ext w.content]
    refine elim.spanRel_mono w.coords.length _ _ w.coords ?_ ?_ hsp
    · have hL := rowsLen_groupAt w.content pool hs
      rw [← hw] at hL
      exact hL
    · have hL := rowsLen_groupAt w.content ext hx
      rw [← hw] at hL
      exact hL

private theorem settled_member (pool : List HVec) (v : HVec)
    (hs : ∀ x ∈ pool, sized x) (hv : sized v) :
    settledAt (pool ++ [v]) v := by
  refine Or.inr ?_
  have hgrp : groupAt (pool ++ [v]) v.content
      = groupAt pool v.content ++ [v.coords] := by
    rw [groupAt_append pool [v] v.content,
      groupAt_cons v [] v.content, ground.listEqBeq v.content]
    rfl
  have hLall : elim.rowsLen v.coords.length
      (groupAt (pool ++ [v]) v.content) := by
    have hL := rowsLen_groupAt v.content (pool ++ [v])
      (ground.all_of_append _ _ _ hs (memAll_cons hv memAll_nil))
    rw [← hv] at hL
    exact hL
  have hk : (groupAt pool v.content).length
      < (groupAt (pool ++ [v]) v.content).length := by
    rw [hgrp, ground.length_append]
    exact Nat.lt_succ_self _
  have hget : ground.getAt [] (groupAt (pool ++ [v]) v.content)
      (groupAt pool v.content).length = v.coords := by
    rw [hgrp, ground.getAt_append,
      if_neg (Nat.not_lt.mpr (Nat.le_refl _)), Nat.sub_self]
    rfl
  have := elim.spanRel_getAt v.coords.length
    (groupAt (pool ++ [v]) v.content)
    (groupAt pool v.content).length hk hLall
  rw [hget] at this
  exact this

private theorem tryAdd_sem (pool : List HVec) (v : HVec)
    (hs : ∀ x ∈ pool, sized x) (hv : sized v)
    (hind : indepAll pool) :
    (tryAdd pool v = pool ∧ settledAt pool v)
      ∨ (tryAdd pool v = pool ++ [v]
          ∧ indepAll (pool ++ [v])) := by
  have hL : elim.rowsLen v.coords.length
      (groupAt pool v.content) := by
    have h := rowsLen_groupAt v.content pool hs
    rw [← hv] at h
    exact h
  have hind' : elim.indepRows v.coords.length
      (groupAt pool v.content) := by
    have h := indepAll_all hind v.content
    rw [← hv] at h
    exact h
  by_cases h1 : allU v.coords = true
  · exact Or.inl ⟨if_pos h1, Or.inl h1⟩
  · have he : tryAdd pool v
        = (let group := pool.filter (fun w => w.content == v.content)
           if poly.unitTail (elim.residV v.coords.length
               (group.map HVec.coords) v.coords)
           then pool else pool ++ [v]) := if_neg h1
    by_cases h2 : poly.unitTail (elim.residV v.coords.length
      (groupAt pool v.content) v.coords)
    · refine Or.inl ⟨he.trans (if_pos h2), Or.inr ?_⟩
      exact elim.resid_sound v.coords.length _ v.coords hL rfl
        (elim.indep_det v.coords.length _ hind') h2
    · refine Or.inr ⟨he.trans (if_neg h2), ?_⟩
      intro mu _
      by_cases hmu : v.content = mu
      · cases hmu
        have hext := elim.indep_extend v.coords.length
          (groupAt pool v.content) v.coords hL rfl hind'
          (fun hsp => h2 (elim.resid_complete v.coords.length _
            v.coords hL rfl hsp))
        have hgrp : groupAt (pool ++ [v]) v.content
            = groupAt pool v.content ++ [v.coords] := by
          rw [groupAt_append pool [v] v.content,
            groupAt_cons v [] v.content,
            ground.listEqBeq v.content]
          rfl
        rw [hgrp, ← hv]
        exact hext
      · have hgrp : groupAt (pool ++ [v]) mu = groupAt pool mu := by
          rw [groupAt_append pool [v] mu, groupAt_cons v [] mu]
          cases hb : v.content == mu with
          | true => exact absurd (ground.listBeqEq hb) hmu
          | false =>
            show groupAt pool mu ++ groupAt ([] : List HVec) mu = _
            exact ground.append_nil _
        rw [hgrp]
        exact indepAll_all hind mu

private theorem foldl_tryAdd_sem :
    ∀ (imgs pool : List HVec), (∀ v ∈ pool, sized v) →
      (∀ v ∈ imgs, sized v) → indepAll pool →
      ∃ ext, imgs.foldl tryAdd pool = pool ++ ext
        ∧ indepAll (pool ++ ext)
        ∧ (∀ w ∈ imgs, settledAt (pool ++ ext) w)
        ∧ (∀ Q : HVec → Prop, (∀ v ∈ imgs, Q v) → ∀ v ∈ ext, Q v)
  | [], pool, _, _, hind =>
    ⟨[], (ground.append_nil pool).symm,
      by rw [ground.append_nil pool]; exact hind,
      memAll_nil, fun _ _ => memAll_nil⟩
  | w :: imgs', pool, hs, hi, hind => by
    show ∃ ext, imgs'.foldl tryAdd (tryAdd pool w) = pool ++ ext
      ∧ indepAll (pool ++ ext)
      ∧ (∀ x ∈ w :: imgs', settledAt (pool ++ ext) x)
      ∧ (∀ Q : HVec → Prop, (∀ v ∈ w :: imgs', Q v) →
          ∀ v ∈ ext, Q v)
    cases tryAdd_sem pool w hs (memAll_head hi) hind with
    | inl hcase =>
      rw [hcase.1]
      match foldl_tryAdd_sem imgs' pool hs (memAll_tail hi)
          hind with
      | ⟨ext, heq, hind2, hsetts, htrans⟩ =>
        refine ⟨ext, heq, hind2, memAll_cons ?_ hsetts,
          fun Q hQ => htrans Q (memAll_tail hQ)⟩
        exact settled_mono pool ext w hs
          (htrans sized (memAll_tail hi)) (memAll_head hi) hcase.2
    | inr hcase =>
      rw [hcase.1]
      match foldl_tryAdd_sem imgs' (pool ++ [w])
          (ground.all_of_append _ _ _ hs
            (memAll_cons (memAll_head hi) memAll_nil))
          (memAll_tail hi) hcase.2 with
      | ⟨ext', heq, hind2, hsetts, htrans⟩ =>
        have hassoc : pool ++ [w] ++ ext' = pool ++ (w :: ext') := by
          rw [ground.append_assoc]
          rfl
        refine ⟨w :: ext', by rw [heq, hassoc],
          by rw [← hassoc]; exact hind2, memAll_cons ?_ ?_,
          fun Q hQ => memAll_cons (memAll_head hQ)
            (htrans Q (memAll_tail hQ))⟩
        · rw [← hassoc]
          exact settled_mono (pool ++ [w]) ext' w
            (ground.all_of_append _ _ _ hs
              (memAll_cons (memAll_head hi) memAll_nil))
            (htrans sized (memAll_tail hi)) (memAll_head hi)
            (settled_member pool w hs (memAll_head hi))
        · rw [← hassoc]
          exact hsetts

/-- A per-member read over a joined image family: every member's
image list at the read puts the joined list at it whole. -/
theorem memAll_flatMap_of (P A : HVec → Prop)
    (f : HVec → List HVec) (h : ∀ v, A v → ∀ w ∈ f v, P w) :
    ∀ l : List HVec, (∀ v ∈ l, A v) → ∀ w ∈ l.flatMap f, P w
  | [], _ => memAll_nil
  | v :: t, ha => by
    show ∀ w ∈ f v ++ t.flatMap f, P w
    exact ground.all_of_append _ _ _ (h v (memAll_head ha))
      (memAll_flatMap_of P A f h t (memAll_tail ha))

private theorem memAll_flatMap_to (P : HVec → Prop)
    (f : HVec → List HVec) :
    ∀ l : List HVec, (∀ w ∈ l.flatMap f, P w) →
      ∀ v ∈ l, ∀ w ∈ f v, P w
  | [], _ => memAll_nil
  | v :: t, h => by
    have hsp := memAll_split (P := P)
      (a := f v) (b := t.flatMap f) h
    exact memAll_cons hsp.1 (memAll_flatMap_to P f t hsp.2)

private theorem memAll_range_to (P : HVec → Prop)
    (g : Nat → List HVec) :
    ∀ n : Nat, (∀ w ∈ (List.range n).flatMap g, P w) →
      ∀ j, j < n → ∀ w ∈ g j, P w
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, h, j, hj => by
    rw [range_succ n, ground.flatMap_append] at h
    have hsp := memAll_split (P := P)
      (a := (List.range n).flatMap g) (b := [n].flatMap g) h
    by_cases hjn : j = n
    · have h2 : ∀ w ∈ g n ++ [], P w := hsp.2
      rw [ground.append_nil (g n)] at h2
      rw [hjn]
      exact h2
    · exact memAll_range_to P g n hsp.1 j
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjn)

private theorem memAll_range_of (P : HVec → Prop)
    (g : Nat → List HVec) :
    ∀ n : Nat, (∀ j, j < n → ∀ w ∈ g j, P w) →
      ∀ w ∈ (List.range n).flatMap g, P w
  | 0, _ => memAll_nil
  | n + 1, h => by
    rw [range_succ n, ground.flatMap_append]
    refine ground.all_of_append _ _ _
      (memAll_range_of P g n
        (fun j hj => h j (Nat.lt_of_lt_of_le hj
          (Nat.le_succ n)))) ?_
    show ∀ w ∈ g n ++ [], P w
    rw [ground.append_nil (g n)]
    exact h n (Nat.lt_succ_self n)

/-- The image family of a frontier at a letter count: the occupied
adjacent lowerings, the closure round's own enumeration. -/
private def imgsOf (d : Nat) (frontier : List HVec) : List HVec :=
  frontier.flatMap (fun v => (List.range (d - 1)).flatMap
    (fun j =>
      match lowerH j v with
      | some w => [w]
      | none => []))

private theorem imgs_closed (d : Nat) (R : List HVec)
    (frontier : List HVec)
    (h : ∀ w ∈ imgsOf d frontier, settledAt R w) :
    ∀ v ∈ frontier, ∀ j w, j < d - 1 → lowerH j v = some w →
      settledAt R w := by
  intro v hvm j w hj heq
  have hv := memAll_flatMap_to _ _ frontier h v hvm
  have hj' := memAll_range_to _ _ (d - 1) hv j hj
  rw [heq] at hj'
  exact hj' w (List.Mem.head [])

private theorem imgs_of_build (P : HVec → Prop) (A : HVec → Prop)
    (d : Nat) (frontier : List HVec) (ha : ∀ v ∈ frontier, A v)
    (h : ∀ v j w, A v → j < d - 1 → lowerH j v = some w → P w) :
    ∀ w ∈ imgsOf d frontier, P w := by
  refine memAll_flatMap_of P A _ ?_ frontier ha
  intro v hav
  refine memAll_range_of P _ (d - 1) ?_
  intro j hj
  match heq : lowerH j v with
  | none => exact memAll_nil
  | some w => exact memAll_cons (h v j w hav hj heq) memAll_nil

/-! The pool's indexed provenance (`lem:blockirr`'s `hprov`
datum): a closure round appends only the frontier's own lowering
images, and the frontier is a suffix of the pool, so every joined
member names an occupied interior lowering of a member listed
strictly before it. -/

/-- The indexed provenance at a pool: every member beyond the
first is an occupied interior lowering of a strictly earlier
one. -/
private def provAt (d : Nat) (pool : List HVec) : Prop :=
  ∀ m, 0 < m → m < pool.length →
    ∃ i, i < m ∧ ∃ j, j + 1 < d ∧
      lowerH j (getAt (⟨[], []⟩ : HVec) pool i)
        = some (getAt (⟨[], []⟩ : HVec) pool m)

/-- The read is kept by a join of listed members' lowering images:
the joined member's preimage sits inside the first family, hence
strictly before it. -/
private theorem prov_append (d : Nat) (pool ext : List HVec)
    (hp : provAt d pool)
    (hext : ∀ w ∈ ext, ∃ j, j + 1 < d ∧ ∃ u, u ∈ pool
      ∧ lowerH j u = some w) :
    provAt d (pool ++ ext) := by
  intro m hm0 hml
  match Nat.lt_or_ge m pool.length with
  | Or.inl hlt =>
    match hp m hm0 hlt with
    | ⟨i, him, j, hj, hlow⟩ =>
      refine ⟨i, him, j, hj, ?_⟩
      rw [ground.getAt_append (⟨[], []⟩ : HVec) pool ext i,
        if_pos (Nat.lt_trans him hlt),
        ground.getAt_append (⟨[], []⟩ : HVec) pool ext m,
        if_pos hlt]
      exact hlow
  | Or.inr hge =>
    match Nat.le.dest hge with
    | ⟨r, hr⟩ =>
      have hrl : r < ext.length := by
        rw [ground.length_append pool ext, ← hr] at hml
        exact Nat.lt_of_add_lt_add_left hml
      have hget : getAt (⟨[], []⟩ : HVec) (pool ++ ext) m
          = getAt (⟨[], []⟩ : HVec) ext r := by
        rw [← hr]
        exact ground.getAt_append_add (⟨[], []⟩ : HVec) pool ext r
      rw [hget]
      match hext _ (ground.mem_getAt (⟨[], []⟩ : HVec) ext r hrl) with
      | ⟨j, hj, u, hu, hlow⟩ =>
        match ground.getAt_of_mem (⟨[], []⟩ : HVec) hu with
        | ⟨i, hil, hie⟩ =>
          refine ⟨i, Nat.lt_of_lt_of_le hil hge, j, hj, ?_⟩
          rw [ground.getAt_append (⟨[], []⟩ : HVec) pool ext i,
            if_pos hil, hie]
          exact hlow

/-- The closure keeps the indexed provenance: the round's joins
are the frontier's images, the frontier itself listed. -/
private theorem closeSpan_prov (d : Nat) :
    ∀ (fuel : Nat) (pool frontier : List HVec),
      (∀ v ∈ frontier, v ∈ pool) → provAt d pool →
      ∃ tail, closeSpan d fuel pool frontier = pool ++ tail
        ∧ provAt d (pool ++ tail)
  | 0, pool, _, _, hp =>
    ⟨[], (ground.append_nil pool).symm, by
      rw [ground.append_nil]
      exact hp⟩
  | _ + 1, pool, [], _, hp =>
    ⟨[], (ground.append_nil pool).symm, by
      rw [ground.append_nil]
      exact hp⟩
  | fuel + 1, pool, v :: fs, hf, hp => by
    have hstep : closeSpan d (fuel + 1) pool (v :: fs)
        = closeSpan d fuel ((imgsOf d (v :: fs)).foldl tryAdd pool)
            (((imgsOf d (v :: fs)).foldl tryAdd pool).drop
              pool.length) := rfl
    match foldl_tryAdd_reads
        (fun w => ∃ j, j + 1 < d ∧ ∃ u, u ∈ pool
          ∧ lowerH j u = some w)
        (imgsOf d (v :: fs)) pool
        (imgs_of_build _ (fun u => u ∈ pool) d (v :: fs) hf
          (fun u j w hu hj heq =>
            ⟨j, ground.succ_lt_of_lt_pred hj, u, hu, heq⟩)) with
    | ⟨t1, ht1, hc1⟩ =>
      match closeSpan_prov d fuel (pool ++ t1) t1
          (fun w hw => ground.mem_append_right pool hw)
          (prov_append d pool t1 hp hc1) with
      | ⟨t2, ht2, hp2⟩ =>
        refine ⟨t1 ++ t2, ?_, ?_⟩
        · rw [hstep, ht1, ground.drop_append_self pool t1, ht2,
            ground.append_assoc]
        · rw [← ground.append_assoc]
          exact hp2

/-- `lem:blockirr`'s provenance datum: the span lists the exhibit
first, and every later member is an occupied interior lowering of
a member listed at or before its own predecessor — the closure
appending frontier images alone. -/
theorem blockSpan_prov (s : Shape) : ∃ tail,
    blockSpan s = exhibit s :: tail
      ∧ ∀ k, k < tail.length →
        ∃ i, i ≤ k ∧ ∃ j, j + 1 < s.length ∧
          lowerH j (getAt (⟨[], []⟩ : HVec) (exhibit s :: tail) i)
            = some (getAt (⟨[], []⟩ : HVec) tail k) := by
  have hseed : provAt s.length [exhibit s] := by
    intro m hm0 hm1
    exact absurd (Nat.lt_of_lt_of_le hm0 (Nat.le_of_lt_succ hm1))
      (Nat.lt_irrefl 0)
  match closeSpan_prov s.length (degree s * s.length)
      [exhibit s] [exhibit s] (fun _ hv => hv) hseed with
  | ⟨t, ht, hpt⟩ =>
    refine ⟨t, ht, ?_⟩
    intro k hk
    have hkl : k + 1 < ([exhibit s] ++ t).length :=
      Nat.succ_lt_succ hk
    match hpt (k + 1) (Nat.succ_pos k) hkl with
    | ⟨i, him, j, hj, hlow⟩ =>
      exact ⟨i, Nat.le_of_lt_succ him, j, hj, hlow⟩

private theorem lowerH_fields {j : Nat} {v w : HVec}
    (h : lowerH j v = some w) :
    w.content = units.moveDn j v.content
      ∧ w.coords = elim.matVec
          (units.matUnitAt (units.moveDn j v.content) v.content
            (j + 1) j) v.coords :=
  ⟨congrArg HVec.content (lowerH_eq h),
   congrArg HVec.coords (lowerH_eq h)⟩

private theorem lowerH_sized {j : Nat} {v w : HVec}
    (h : lowerH j v = some w) : sized w := by
  match lowerH_fields h with
  | ⟨hc, hx⟩ =>
    show w.coords.length = (places.monomialsAt w.content).length
    rw [hc, hx,
      show (elim.matVec (units.matUnitAt (units.moveDn j v.content)
          v.content (j + 1) j) v.coords).length
        = (units.matUnitAt (units.moveDn j v.content) v.content
            (j + 1) j).length from ground.length_map _ _,
      units.length_matUnitAt]

/-- The exhibit is a member of its own span, the closure's head. -/
theorem exhibit_mem (s : Shape) : exhibit s ∈ blockSpan s := by
  match blockSpan_prov s with
  | ⟨tail, hEq, _⟩ =>
    rw [hEq]
    exact List.Mem.head tail

/-- The lowering moves along the coordinate class: at one content
and one-value coordinates the images share their content and read
one value, the action's congruence at the moved matrix. -/
theorem lowerH_move {j : Nat} {v v' u : HVec}
    (hc : v.content = v'.content)
    (hq : poly.oneValue v.coords v'.coords)
    (h : lowerH j v = some u) :
    ∃ u', lowerH j v' = some u'
      ∧ u.content = u'.content
      ∧ poly.oneValue u.coords u'.coords := by
  have hg : 0 < ground.getAt 0 v'.content j := by
    rw [← hc]
    exact (lowerH_reads h).1
  refine ⟨⟨units.moveDn j v'.content,
    elim.matVec (units.matUnitAt (units.moveDn j v'.content)
      v'.content (j + 1) j) v'.coords⟩, if_pos hg, ?_, ?_⟩
  · rw [(lowerH_fields h).1, hc]
  · rw [lowerH_eq h]
    show poly.oneValue
      (elim.matVec (units.matUnitAt (units.moveDn j v.content)
        v.content (j + 1) j) v.coords)
      (elim.matVec (units.matUnitAt (units.moveDn j v'.content)
        v'.content (j + 1) j) v'.coords)
    rw [hc]
    exact elim.matVec_congr _ _ _ hq

private theorem closeSpan_sem (d : Nat) (meas : List Nat → Nat)
    (K : HVec → Prop)
    (hK : ∀ (j : Nat) (v w : HVec), lowerH j v = some w → K v → K w)
    (hnomove : ∀ v : HVec, K v → meas v.content = 0 →
      ∀ j : Nat, j < d - 1 → lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v w : HVec), j < d - 1 →
      lowerH j v = some w → K v →
      meas w.content + 1 = meas v.content) :
    ∀ (fuel : Nat) (done frontier : List HVec),
      (∀ v ∈ done ++ frontier, sized v) →
      (∀ v ∈ done ++ frontier, K v) →
      indepAll (done ++ frontier) →
      (∀ v ∈ done, ∀ j w, j < d - 1 → lowerH j v = some w →
        settledAt (done ++ frontier) w) →
      (∀ w ∈ frontier, meas w.content ≤ fuel) →
      ∃ ext, closeSpan d fuel (done ++ frontier) frontier
          = (done ++ frontier) ++ ext
        ∧ (∀ v ∈ (done ++ frontier) ++ ext, sized v)
        ∧ (∀ v ∈ (done ++ frontier) ++ ext, K v)
        ∧ indepAll ((done ++ frontier) ++ ext)
        ∧ closedAt (closeSpan d fuel (done ++ frontier) frontier) d
  | 0, done, frontier, hs, hk, hind, hdone, hht => by
    refine ⟨[], (ground.append_nil _).symm, ?_, ?_, ?_, ?_⟩
    · rw [ground.append_nil]
      exact hs
    · rw [ground.append_nil]
      exact hk
    · rw [ground.append_nil]
      exact hind
    · refine closedAt_intro (ground.all_of_append _ _ _ hdone ?_)
      intro v hv j w hj heq
      have h0 : meas v.content = 0 := Nat.le_zero.mp (hht v hv)
      rw [hnomove v ((memAll_split hk).2 v hv) h0 j hj] at heq
      exact nomatch heq
  | fuel + 1, done, [], hs, hk, hind, hdone, _ => by
    refine ⟨[], (ground.append_nil _).symm, ?_, ?_, ?_, ?_⟩
    · rw [ground.append_nil]
      exact hs
    · rw [ground.append_nil]
      exact hk
    · rw [ground.append_nil]
      exact hind
    · exact closedAt_intro (ground.all_of_append _ _ _ hdone memAll_nil)
  | fuel + 1, done, f :: fr, hs, hk, hind, hdone, hht => by
    have hkf : ∀ v ∈ f :: fr, K v := (memAll_split hk).2
    have himgsS : ∀ w ∈ imgsOf d (f :: fr), sized w :=
      imgs_of_build sized K d (f :: fr) hkf
        (fun v j w _ _ heq => lowerH_sized heq)
    have himgsK : ∀ w ∈ imgsOf d (f :: fr), K w :=
      imgs_of_build K K d (f :: fr) hkf
        (fun v j w hav _ heq => hK j v w heq hav)
    have himgsM : ∀ w ∈ imgsOf d (f :: fr),
        meas w.content ≤ fuel := by
      refine imgs_of_build _
        (fun v => K v ∧ meas v.content ≤ fuel + 1)
        d (f :: fr) (fun v hv => ⟨hkf v hv, hht v hv⟩) ?_
      intro v j w hav hj heq
      have hd := hdrop j v w hj heq hav.1
      have h2 : meas w.content + 1 ≤ fuel + 1 := by
        rw [hd]
        exact hav.2
      exact Nat.le_of_succ_le_succ h2
    match foldl_tryAdd_sem (imgsOf d (f :: fr)) (done ++ (f :: fr))
        hs himgsS hind with
    | ⟨ext₁, heq₁, hind₁, hsetts, htrans⟩ =>
      have hs₁ : ∀ v ∈ (done ++ (f :: fr)) ++ ext₁, sized v :=
        ground.all_of_append _ _ _ hs (htrans sized himgsS)
      have hk₁ : ∀ v ∈ (done ++ (f :: fr)) ++ ext₁, K v :=
        ground.all_of_append _ _ _ hk (htrans K himgsK)
      have hdone' : ∀ v ∈ done ++ (f :: fr), ∀ j w, j < d - 1 →
          lowerH j v = some w →
          settledAt ((done ++ (f :: fr)) ++ ext₁) w := by
        refine ground.all_of_append _ _ _ ?_ ?_
        · intro v hv j w hj heq
          exact settled_mono (done ++ (f :: fr)) ext₁ w hs
            (htrans sized himgsS) (lowerH_sized heq)
            (hdone v hv j w hj heq)
        · exact imgs_closed d ((done ++ (f :: fr)) ++ ext₁)
            (f :: fr) hsetts
      match closeSpan_sem d meas K hK hnomove hdrop fuel
          (done ++ (f :: fr)) ext₁ hs₁ hk₁ hind₁
          hdone' (htrans _ himgsM) with
      | ⟨ext₂, heq₂, hs₂, hk₂, hind₂, hclosed⟩ =>
        have hstep : closeSpan d (fuel + 1) (done ++ (f :: fr))
            (f :: fr)
            = closeSpan d fuel
                ((imgsOf d (f :: fr)).foldl tryAdd
                  (done ++ (f :: fr)))
                (((imgsOf d (f :: fr)).foldl tryAdd
                  (done ++ (f :: fr))).drop
                  (done ++ (f :: fr)).length) := rfl
        refine ⟨ext₁ ++ ext₂, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hstep, heq₁, ground.drop_append_self (done ++ (f :: fr)) ext₁,
            heq₂, ground.append_assoc]
        · rw [← ground.append_assoc]
          exact hs₂
        · rw [← ground.append_assoc]
          exact hk₂
        · rw [← ground.append_assoc]
          intro mu hmu
          exact hind₂ mu hmu
        · rw [hstep, heq₁, ground.drop_append_self (done ++ (f :: fr)) ext₁]
          exact hclosed

private theorem foldl_len_inv {α : Type}
    (g : List BPair → α → List BPair)
    (h : ∀ acc x, (g acc x).length = acc.length) :
    ∀ (l : List α) (acc : List BPair),
      (l.foldl g acc).length = acc.length
  | [], _ => rfl
  | x :: t, acc => (foldl_len_inv g h t (g acc x)).trans (h acc x)

/-- The tensor is sized outright: its coordinate width is the
joined content's enumeration, the scatters keeping the seed's. -/
theorem tensorH_sized (v w : HVec) : sized (tensorH v w) := by
  show (((List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
              w.coords).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt
                (rankOf (p.1 ++ q.1)
                  (List.zipWith (fun a b => a + b) v.content
                    w.content))
                (p.2 * q.2) acc2)
            acc)
      ((monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit))).map
      BPair.norm).length
    = (monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).length
  rw [ground.length_map,
    foldl_len_inv _ (fun acc p => by
      by_cases hp : p.2.isUnitRep = true
      · rw [if_pos hp]
      · rw [if_neg hp]
        exact foldl_len_inv _ (fun acc2 q => by
          by_cases hq : q.2.isUnitRep = true
          · rw [if_pos hq]
          · rw [if_neg hq]
            exact units.length_scatterAt _ _ acc2) _ acc)
      (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords) _,
    ground.length_map]

private theorem exhibit_go_sized (d : Nat) :
    ∀ (ls : List Nat) (acc : HVec), sized acc →
      sized (ls.foldl (fun acc l => tensorH acc (wedge d l)) acc)
  | [], _, h => h
  | l :: ls, acc, _ =>
    exhibit_go_sized d ls (tensorH acc (wedge d l))
      (tensorH_sized acc (wedge d l))

/-- The exhibit is sized: one coordinate per member of its
content's enumeration. -/
theorem exhibit_sized (s : Shape) : sized (exhibit s) := by
  refine exhibit_go_sized s.length (columnLengths s) _ ?_
  show (1 : Nat)
    = (monomialsAt (List.replicate s.length 0)).length
  rw [places.monomialsAt_sum_zero _
    (sumNat_replicate_zero s.length)]
  rfl

/-! The seed's occupancy (`lem:lowerspan`'s seed clause): the
exhibit's coordinate family sits off the unit tail — the
distinguished arrangement's coefficient survives every tensor
step, the factors' distinguished pair unique at the
concatenation's rank. -/

private theorem zip_member {q : List Nat × BPair} :
    ∀ (bs : List (List Nat)) (cs : List BPair),
      0 < ground.countOf q
        (List.zipWith (fun m x => (m, x)) bs cs) →
      ∃ i, i < bs.length ∧ i < cs.length
        ∧ q = (ground.getAt [] bs i, ground.getAt BPair.unit cs i)
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, [], h => absurd h (Nat.lt_irrefl 0)
  | b :: bs, c :: cs, h => by
    by_cases hq : q = (b, c)
    · exact ⟨0, Nat.succ_pos _, Nat.succ_pos _, hq⟩
    · have h' : 0 < ground.countOf q
          (List.zipWith (fun m x => (m, x)) bs cs) := by
        have h2 : 0 < (if q = (b, c) then 1 else 0)
            + ground.countOf q
              (List.zipWith (fun m x => (m, x)) bs cs) := by
          rw [← ground.countOf_cons]
          exact h
        rw [if_neg hq, Nat.zero_add] at h2
        exact h2
      match zip_member bs cs h' with
      | ⟨i, hb, hc, he⟩ =>
        exact ⟨i + 1, Nat.succ_lt_succ hb, Nat.succ_lt_succ hc, he⟩

/-- The contribution fold at one target key: the inner scatter
pass's reads at the key, seeded at the sum's unit. -/
private def hitI (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) :
    List (List Nat × BPair) → BPair
  | [] => BPair.unit
  | q :: t =>
    if q.2.isUnitRep then hitI mu' k' p t
    else if k' = rankOf (p.1 ++ q.1) mu' then
      p.2 * q.2 + hitI mu' k' p t
    else hitI mu' k' p t

private theorem innerFold_len (mu' : List Nat)
    (p : List Nat × BPair) (ql : List (List Nat × BPair))
    (acc : List BPair) :
    (ql.foldl (fun acc2 q =>
      if q.2.isUnitRep then acc2
      else units.scatterAt (rankOf (p.1 ++ q.1) mu')
        (p.2 * q.2) acc2) acc).length = acc.length :=
  foldl_len_inv _ (fun acc2 q => by
    by_cases hq : q.2.isUnitRep = true
    · rw [if_pos hq]
    · rw [if_neg hq]
      exact units.length_scatterAt _ _ acc2) ql acc

private theorem getAt_innerFold (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) :
    ∀ (ql : List (List Nat × BPair)) (acc : List BPair),
      k' < acc.length →
      (ground.getAt BPair.unit (ql.foldl (fun acc2 q =>
        if q.2.isUnitRep then acc2
        else units.scatterAt (rankOf (p.1 ++ q.1) mu')
          (p.2 * q.2) acc2) acc) k').oneValue
      (ground.getAt BPair.unit acc k' + hitI mu' k' p ql)
  | [], acc, _ => BPair.oneValue_symm (BPair.add_unit _)
  | q :: t, acc, hk => by
    show (ground.getAt BPair.unit (t.foldl _
        (if q.2.isUnitRep then acc
         else units.scatterAt (rankOf (p.1 ++ q.1) mu')
           (p.2 * q.2) acc)) k').oneValue
      (ground.getAt BPair.unit acc k'
        + (if q.2.isUnitRep then hitI mu' k' p t
           else if k' = rankOf (p.1 ++ q.1) mu' then
             p.2 * q.2 + hitI mu' k' p t
           else hitI mu' k' p t))
    by_cases hq : q.2.isUnitRep = true
    · rw [if_pos hq, if_pos hq]
      exact getAt_innerFold mu' k' p t acc hk
    · rw [if_neg hq, if_neg hq]
      have hk2 : k' < (units.scatterAt (rankOf (p.1 ++ q.1) mu')
          (p.2 * q.2) acc).length := by
        rw [units.length_scatterAt]
        exact hk
      refine BPair.oneValue_trans
        (getAt_innerFold mu' k' p t _ hk2) ?_
      rw [units.getAt_scatterAt BPair.unit _ _ acc k' hk]
      by_cases hr : k' = rankOf (p.1 ++ q.1) mu'
      · rw [if_pos hr, if_pos hr, BPair.add_assoc]
        exact BPair.oneValue_refl _
      · rw [if_neg hr, if_neg hr]
        exact BPair.oneValue_refl _

/-- The contribution fold over the first factor's passes. -/
private def hitO (mu' : List Nat) (k' : Nat)
    (ql : List (List Nat × BPair)) :
    List (List Nat × BPair) → BPair
  | [] => BPair.unit
  | p :: t =>
    if p.2.isUnitRep then hitO mu' k' ql t
    else hitI mu' k' p ql + hitO mu' k' ql t

private theorem getAt_outerFold (mu' : List Nat) (k' : Nat)
    (ql : List (List Nat × BPair)) :
    ∀ (pl : List (List Nat × BPair)) (acc : List BPair),
      k' < acc.length →
      (ground.getAt BPair.unit (pl.foldl (fun acc p =>
        if p.2.isUnitRep then acc
        else ql.foldl (fun acc2 q =>
          if q.2.isUnitRep then acc2
          else units.scatterAt (rankOf (p.1 ++ q.1) mu')
            (p.2 * q.2) acc2) acc) acc) k').oneValue
      (ground.getAt BPair.unit acc k' + hitO mu' k' ql pl)
  | [], acc, _ => BPair.oneValue_symm (BPair.add_unit _)
  | p :: t, acc, hk => by
    show (ground.getAt BPair.unit (t.foldl _
        (if p.2.isUnitRep then acc
         else ql.foldl _ acc)) k').oneValue
      (ground.getAt BPair.unit acc k'
        + (if p.2.isUnitRep then hitO mu' k' ql t
           else hitI mu' k' p ql + hitO mu' k' ql t))
    by_cases hp : p.2.isUnitRep = true
    · rw [if_pos hp, if_pos hp]
      exact getAt_outerFold mu' k' ql t acc hk
    · rw [if_neg hp, if_neg hp]
      have hk2 : k' < (ql.foldl (fun acc2 q =>
          if q.2.isUnitRep then acc2
          else units.scatterAt (rankOf (p.1 ++ q.1) mu')
            (p.2 * q.2) acc2) acc).length := by
        rw [innerFold_len mu' p ql acc]
        exact hk
      refine BPair.oneValue_trans
        (getAt_outerFold mu' k' ql t _ hk2)
        (BPair.oneValue_trans
          (BPair.add_congr (getAt_innerFold mu' k' p ql acc hk)
            (BPair.oneValue_refl (hitO mu' k' ql t))) ?_)
      rw [BPair.add_assoc]
      exact BPair.oneValue_refl _

private theorem hitI_null (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) :
    ∀ ql : List (List Nat × BPair),
      (∀ q, 0 < ground.countOf q ql → q.2.isUnitRep = false →
        ¬ k' = rankOf (p.1 ++ q.1) mu') →
      hitI mu' k' p ql = BPair.unit
  | [], _ => rfl
  | q :: t, h => by
    have htail : ∀ q', 0 < ground.countOf q' t →
        q'.2.isUnitRep = false →
        ¬ k' = rankOf (p.1 ++ q'.1) mu' := by
      intro q' hq' hu
      refine h q' (Nat.lt_of_lt_of_le hq' ?_) hu
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show (if q.2.isUnitRep then hitI mu' k' p t
        else if k' = rankOf (p.1 ++ q.1) mu' then
          p.2 * q.2 + hitI mu' k' p t
        else hitI mu' k' p t) = BPair.unit
    by_cases hq : q.2.isUnitRep = true
    · rw [if_pos hq]
      exact hitI_null mu' k' p t htail
    · rw [if_neg hq,
        if_neg (h q (by
          rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
          exact Nat.succ_pos _) (Bool.eq_false_iff.mpr hq))]
      exact hitI_null mu' k' p t htail

private theorem hitO_null (mu' : List Nat) (k' : Nat)
    (ql : List (List Nat × BPair)) :
    ∀ pl : List (List Nat × BPair),
      (∀ p, 0 < ground.countOf p pl → p.2.isUnitRep = false →
        ∀ q, 0 < ground.countOf q ql → q.2.isUnitRep = false →
        ¬ k' = rankOf (p.1 ++ q.1) mu') →
      (hitO mu' k' ql pl).oneValue BPair.unit
  | [], _ => BPair.oneValue_refl _
  | p :: t, h => by
    have htail : ∀ p', 0 < ground.countOf p' t →
        p'.2.isUnitRep = false → ∀ q, 0 < ground.countOf q ql →
        q.2.isUnitRep = false →
        ¬ k' = rankOf (p'.1 ++ q.1) mu' := by
      intro p' hp' hu
      refine h p' (Nat.lt_of_lt_of_le hp' ?_) hu
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show (if p.2.isUnitRep then hitO mu' k' ql t
        else hitI mu' k' p ql + hitO mu' k' ql t).oneValue
      BPair.unit
    by_cases hp : p.2.isUnitRep = true
    · rw [if_pos hp]
      exact hitO_null mu' k' ql t htail
    · rw [if_neg hp,
        hitI_null mu' k' p ql
          (h p (by
            rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
            exact Nat.succ_pos _) (Bool.eq_false_iff.mpr hp))]
      exact BPair.oneValue_trans (BPair.unit_add _)
        (hitO_null mu' k' ql t htail)

private theorem head_ne_of_count_one {b : List Nat}
    {bs : List (List Nat)} {i₀ : Nat} (hi : i₀ < bs.length)
    (hcnt : ground.countOf (ground.getAt [] bs i₀) (b :: bs) = 1) :
    ¬ ground.getAt [] bs i₀ = b
      ∧ ground.countOf (ground.getAt [] bs i₀) bs = 1 := by
  have hsplit : (if ground.getAt [] bs i₀ = b then 1 else 0)
      + ground.countOf (ground.getAt [] bs i₀) bs = 1 := by
    rw [← ground.countOf_cons]
    exact hcnt
  have hpos := ground.countOf_getAt_pos [] bs i₀ hi
  by_cases hb : ground.getAt [] bs i₀ = b
  · rw [if_pos hb] at hsplit
    have h1 : ground.countOf (ground.getAt [] bs i₀) bs = 0 := by
      rw [Nat.add_comm] at hsplit
      exact Nat.succ.inj hsplit
    rw [h1] at hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  · rw [if_neg hb, Nat.zero_add] at hsplit
    exact ⟨hb, hsplit⟩

private theorem hitO_at (mu' : List Nat) (k' : Nat)
    (ql : List (List Nat × BPair)) :
    ∀ (i₀ : Nat) (bs : List (List Nat)) (cs : List BPair),
      i₀ < bs.length → i₀ < cs.length →
      (∀ x, 0 < ground.countOf x bs →
        ¬ x = ground.getAt [] bs i₀ →
        ∀ q, 0 < ground.countOf q ql → q.2.isUnitRep = false →
        ¬ k' = rankOf (x ++ q.1) mu') →
      ground.countOf (ground.getAt [] bs i₀) bs = 1 →
      (ground.getAt BPair.unit cs i₀).isUnitRep = false →
      (hitO mu' k' ql
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (hitI mu' k' (ground.getAt [] bs i₀,
        ground.getAt BPair.unit cs i₀) ql)
  | _, [], _, hb, _, _, _, _ => absurd hb (Nat.not_lt_zero _)
  | _, _ :: _, [], _, hc, _, _, _ => absurd hc (Nat.not_lt_zero _)
  | 0, b :: bs, c :: cs, _, _, hmiss, hcnt, hoff => by
    show (if (c : BPair).isUnitRep then _
        else hitI mu' k' (b, c) ql
          + hitO mu' k' ql
            (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (hitI mu' k' (b, c) ql)
    have hoff' : (c : BPair).isUnitRep = false := hoff
    rw [hoff']
    rw [if_neg (fun hc' : (false : Bool) = true =>
      Bool.noConfusion hc')]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (hitI mu' k' (b, c) ql))
        (hitO_null mu' k' ql _ ?_))
      (BPair.add_unit _)
    intro p hp hpu q hq hqu
    match zip_member bs cs hp with
    | ⟨i, hib, hic, he⟩ =>
      have hcnt0 : ground.countOf b bs = 0 := by
        have hsplit : (if (b : List Nat) = b then 1 else 0)
            + ground.countOf b bs = 1 := by
          rw [← ground.countOf_cons]
          exact hcnt
        rw [if_pos rfl, Nat.add_comm] at hsplit
        exact Nat.succ.inj hsplit
      refine hmiss p.1 ?_ ?_ q hq hqu
      · rw [ground.countOf_cons]
        refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
        rw [he]
        exact ground.countOf_getAt_pos [] bs i hib
      · intro hpb
        have hb : ground.getAt [] bs i = b := by
          rw [he] at hpb
          exact hpb
        have := ground.countOf_getAt_pos [] bs i hib
        rw [hb, hcnt0] at this
        exact absurd this (Nat.lt_irrefl 0)
  | i₀ + 1, b :: bs, c :: cs, hb, hc, hmiss, hcnt, hoff => by
    have hb' : i₀ < bs.length := Nat.lt_of_succ_lt_succ hb
    have hc' : i₀ < cs.length := Nat.lt_of_succ_lt_succ hc
    match head_ne_of_count_one hb' hcnt with
    | ⟨hne, hcnt'⟩ =>
      have hmiss' : ∀ x, 0 < ground.countOf x bs →
          ¬ x = ground.getAt [] bs i₀ →
          ∀ q, 0 < ground.countOf q ql → q.2.isUnitRep = false →
          ¬ k' = rankOf (x ++ q.1) mu' := by
        intro x hx hxne
        refine hmiss x (Nat.lt_of_lt_of_le hx ?_) hxne
        rw [ground.countOf_cons]
        exact Nat.le_add_left _ _
      have hrec := hitO_at mu' k' ql i₀ bs cs hb' hc' hmiss'
        hcnt' hoff
      show (if (c : BPair).isUnitRep then
          hitO mu' k' ql (List.zipWith (fun m x => (m, x)) bs cs)
        else hitI mu' k' (b, c) ql
          + hitO mu' k' ql
            (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        (hitI mu' k' (ground.getAt [] bs i₀,
          ground.getAt BPair.unit cs i₀) ql)
      cases hcu : (c : BPair).isUnitRep with
      | true =>
        rw [if_pos rfl]
        exact hrec
      | false =>
        rw [if_neg (fun hc' : (false : Bool) = true =>
          Bool.noConfusion hc')]
        rw [hitI_null mu' k' (b, c) ql (fun q hq hqu =>
          hmiss b (by
            rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
            exact Nat.succ_pos _)
          (fun hc2 => hne hc2.symm) q hq hqu)]
        exact BPair.oneValue_trans (BPair.unit_add _) hrec

private theorem hitI_at (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) :
    ∀ (bs : List (List Nat)) (cs : List BPair),
      0 < bs.length → 0 < cs.length →
      k' = rankOf (p.1 ++ ground.getAt [] bs 0) mu' →
      (∀ x, 0 < ground.countOf x bs →
        ¬ x = ground.getAt [] bs 0 →
        ¬ k' = rankOf (p.1 ++ x) mu') →
      ground.countOf (ground.getAt [] bs 0) bs = 1 →
      (∀ i, i < cs.length →
        (ground.getAt BPair.unit cs i).isUnitRep = false) →
      (hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (p.2 * ground.getAt BPair.unit cs 0)
  | [], _, hb, _, _, _, _, _ => absurd hb (Nat.lt_irrefl 0)
  | _ :: _, [], _, hc, _, _, _, _ => absurd hc (Nat.lt_irrefl 0)
  | b :: bs, c :: cs, _, _, hk, hmiss, hcnt, hallOff => by
    show (if (c : BPair).isUnitRep then
        hitI mu' k' p (List.zipWith (fun m x => (m, x)) bs cs)
      else if k' = rankOf (p.1 ++ b) mu' then
        p.2 * c + hitI mu' k' p
          (List.zipWith (fun m x => (m, x)) bs cs)
      else hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (p.2 * c)
    have hoff' : (c : BPair).isUnitRep = false :=
      hallOff 0 (Nat.succ_pos _)
    have hk' : k' = rankOf (p.1 ++ b) mu' := hk
    rw [hoff']
    rw [if_neg (fun hc' : (false : Bool) = true =>
      Bool.noConfusion hc'), if_pos hk']
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (p.2 * c))
        ?_) (BPair.add_unit _)
    show (hitI mu' k' p
      (List.zipWith (fun m x => (m, x)) bs cs)).oneValue BPair.unit
    rw [hitI_null mu' k' p _ ?_]
    · exact BPair.oneValue_refl _
    · intro q hq _
      match zip_member bs cs hq with
      | ⟨i, hib, _, he⟩ =>
        have hcnt0 : ground.countOf b bs = 0 := by
          have hsplit : (if (b : List Nat) = b then 1 else 0)
              + ground.countOf b bs = 1 := by
            rw [← ground.countOf_cons]
            exact hcnt
          rw [if_pos rfl, Nat.add_comm] at hsplit
          exact Nat.succ.inj hsplit
        refine hmiss q.1 ?_ ?_
        · rw [ground.countOf_cons]
          refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
          rw [he]
          exact ground.countOf_getAt_pos [] bs i hib
        · intro hqb
          have hb2 : ground.getAt [] bs i = b := by
            rw [he] at hqb
            exact hqb
          have := ground.countOf_getAt_pos [] bs i hib
          rw [hb2, hcnt0] at this
          exact absurd this (Nat.lt_irrefl 0)

private theorem concat_member (mu1 mu2 m1 m2 : List Nat)
    (hlen : mu1.length = mu2.length)
    (h1l : m1.length = sumNat mu1)
    (h1c : content mu1.length m1 = mu1)
    (h2l : m2.length = sumNat mu2)
    (h2c : content mu2.length m2 = mu2) :
    (m1 ++ m2).length
        = sumNat (List.zipWith (fun a b => a + b) mu1 mu2)
      ∧ content
          (List.zipWith (fun a b => a + b) mu1 mu2).length
          (m1 ++ m2)
        = List.zipWith (fun a b => a + b) mu1 mu2 := by
  constructor
  · rw [ground.length_append, sumNat_zipWith_add mu1 mu2 hlen,
      h1l, h2l]
  · rw [ground.length_zipWith (fun x y => x + y) mu1 mu2 mu1.length rfl hlen.symm,
      content_append mu1.length m1 m2, h1c, hlen, h2c]

private theorem count_one_of_member {m mu : List Nat}
    (h1 : m.length = sumNat mu) (h2 : content mu.length m = mu) :
    ground.countOf m (monomialsAt mu) = 1 := by
  rw [countOf_monomialsAt mu m, if_pos ⟨h1, h2⟩]

private theorem tensor_dist (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (hsv : sized v) (hsw : sized w)
    (m : List Nat)
    (hm1 : m.length = sumNat v.content)
    (hm2 : content v.content.length m = v.content)
    (hoff : ¬ (ground.getAt BPair.unit v.coords
        (rankOf m v.content)).oneValue BPair.unit)
    (hwAll : ∀ i, i < w.coords.length →
      ¬ (ground.getAt BPair.unit w.coords i).oneValue
        BPair.unit) :
    ∃ m', m'.length = sumNat (tensorH v w).content
      ∧ content (tensorH v w).content.length m'
          = (tensorH v w).content
      ∧ ¬ (ground.getAt BPair.unit (tensorH v w).coords
          (rankOf m' (tensorH v w).content)).oneValue
          BPair.unit := by
  have hwB : 0 < (monomialsAt w.content).length :=
    monomialsAt_occupied w.content
  have hmw := member_conditions
    (ground.countOf_getAt_pos [] (monomialsAt w.content) 0 hwB)
  have hm' := concat_member v.content w.content m
    (ground.getAt [] (monomialsAt w.content) 0) hlen hm1 hm2
    hmw.1 hmw.2
  refine ⟨m ++ ground.getAt [] (monomialsAt w.content) 0,
    hm'.1, hm'.2, ?_⟩
  have hkB := rankOf_read
    (m ++ ground.getAt [] (monomialsAt w.content) 0)
    (List.zipWith (fun a b => a + b) v.content w.content)
    hm'.1 hm'.2
  have hvB := rankOf_read m v.content hm1 hm2
  have hi₀c : rankOf m v.content < v.coords.length := by
    rw [hsv]
    exact hvB.1
  have hw0 : 0 < w.coords.length := by
    rw [hsw]
    exact hwB
  -- the misses at the concatenation's rank, one reason per side
  have hrinj : ∀ x q1 : List Nat,
      x.length = sumNat v.content →
      content v.content.length x = v.content →
      q1.length = sumNat w.content →
      content w.content.length q1 = w.content →
      rankOf (m ++ ground.getAt [] (monomialsAt w.content) 0)
          (List.zipWith (fun a b => a + b) v.content w.content)
        = rankOf (x ++ q1)
          (List.zipWith (fun a b => a + b) v.content w.content) →
      x = m ∧ q1 = ground.getAt [] (monomialsAt w.content) 0 := by
    intro x q1 hx1 hx2 hq1 hq2 heq
    have hxq := concat_member v.content w.content x q1 hlen
      hx1 hx2 hq1 hq2
    have hxB := rankOf_read (x ++ q1)
      (List.zipWith (fun a b => a + b) v.content w.content)
      hxq.1 hxq.2
    have hgets : m ++ ground.getAt [] (monomialsAt w.content) 0
        = x ++ q1 := by
      rw [← hkB.2, ← hxB.2, heq]
    match append_inj_len m x
        (ground.getAt [] (monomialsAt w.content) 0) q1
        (by rw [hx1, hm1]) hgets with
    | ⟨hmx, hq⟩ => exact ⟨hmx.symm, hq.symm⟩
  -- the coordinate list is the fold's read through the norm
  show ¬ (ground.getAt BPair.unit
    (((List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x))
              (monomialsAt w.content) w.coords).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt
                (rankOf (p.1 ++ q.1)
                  (List.zipWith (fun a b => a + b) v.content
                    w.content))
                (p.2 * q.2) acc2)
            acc)
      ((monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit))).map BPair.norm)
    (rankOf (m ++ ground.getAt [] (monomialsAt w.content) 0)
      (List.zipWith (fun a b => a + b) v.content
        w.content))).oneValue BPair.unit
  have hseedlen : (rankOf
      (m ++ ground.getAt [] (monomialsAt w.content) 0)
      (List.zipWith (fun a b => a + b) v.content w.content))
      < ((monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit)).length := by
    rw [ground.length_map]
    exact hkB.1
  have hfoldlen : (rankOf
      (m ++ ground.getAt [] (monomialsAt w.content) 0)
      (List.zipWith (fun a b => a + b) v.content w.content))
      < ((List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x))
              (monomialsAt w.content) w.coords).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt
                (rankOf (p.1 ++ q.1)
                  (List.zipWith (fun a b => a + b) v.content
                    w.content))
                (p.2 * q.2) acc2)
            acc)
      ((monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit))).length := by
    rw [foldl_len_inv _ (fun acc p => by
      by_cases hp : p.2.isUnitRep = true
      · rw [if_pos hp]
      · rw [if_neg hp]
        exact innerFold_len _ p _ acc) _ _]
    exact hseedlen
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ _
    hfoldlen]
  -- the entry collapses to the distinguished pair's product
  have hout := getAt_outerFold
    (List.zipWith (fun a b => a + b) v.content w.content)
    (rankOf (m ++ ground.getAt [] (monomialsAt w.content) 0)
      (List.zipWith (fun a b => a + b) v.content w.content))
    (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
      w.coords)
    (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
      v.coords)
    ((monomialsAt (List.zipWith (fun a b => a + b) v.content
      w.content)).map (fun _ => BPair.unit))
    hseedlen
  rw [ground.getAt_map ([] : List Nat) BPair.unit
    (fun _ => BPair.unit) _ _ hkB.1] at hout
  have hO := hitO_at
    (List.zipWith (fun a b => a + b) v.content w.content)
    (rankOf (m ++ ground.getAt [] (monomialsAt w.content) 0)
      (List.zipWith (fun a b => a + b) v.content w.content))
    (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
      w.coords)
    (rankOf m v.content) (monomialsAt v.content) v.coords
    hvB.1 hi₀c
    (by
      intro x hx hxne q hq _
      intro hkr
      match zip_member (monomialsAt w.content) w.coords hq with
      | ⟨i, hib, _, he⟩ =>
        have hxm := member_conditions hx
        have hqm := member_conditions
          (ground.countOf_getAt_pos [] (monomialsAt w.content)
            i hib)
        have hq1 : q.1 = ground.getAt [] (monomialsAt w.content)
            i := by rw [he]
        refine hxne ?_
        rw [hvB.2]
        exact (hrinj x q.1 hxm.1 hxm.2
          (by rw [hq1]; exact hqm.1)
          (by rw [hq1]; exact hqm.2) hkr).1)
    (by
      rw [hvB.2]
      exact count_one_of_member hm1 hm2)
    (Bool.eq_false_iff.mpr (fun hu =>
      hoff (BPair.oneValue_of_eq (BPair.unit_of_isUnitRep hu))))
  rw [hvB.2] at hO
  have hI := hitI_at
    (List.zipWith (fun a b => a + b) v.content w.content)
    (rankOf (m ++ ground.getAt [] (monomialsAt w.content) 0)
      (List.zipWith (fun a b => a + b) v.content w.content))
    (m, ground.getAt BPair.unit v.coords (rankOf m v.content))
    (monomialsAt w.content) w.coords hwB hw0 rfl
    (by
      intro x hx hxne
      intro hkr
      have hxm := member_conditions hx
      refine hxne ?_
      exact (hrinj m x hm1 hm2 hxm.1 hxm.2 hkr).2)
    (count_one_of_member hmw.1 hmw.2)
    (fun i hi => Bool.eq_false_iff.mpr (fun hu =>
      hwAll i hi (BPair.oneValue_of_eq (BPair.unit_of_isUnitRep hu))))
  -- the product sits off the unit
  have hprod : ¬ ((ground.getAt BPair.unit v.coords
      (rankOf m v.content))
      * ground.getAt BPair.unit w.coords 0).oneValue
      BPair.unit := by
    intro hc
    exact hwAll 0 hw0 (ground.mul_cancel_unit hoff hc)
  -- assemble the chain
  intro hu
  refine hprod ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm hI) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm hO) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.unit_add _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm hout) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.norm_oneValue _)) hu

/-- The wedge's coordinate family is sized: one coordinate per
arrangement of its own content. -/
theorem wedge_sized (d l : Nat) : sized (wedge d l) := by
  show ((monomialsAt ((List.range d).map
      (fun i => if i < l then 1 else 0))).map _).length
    = (monomialsAt ((List.range d).map
      (fun i => if i < l then 1 else 0))).length
  rw [ground.length_map]

/-- The wedge's content is the letter count wide, the indicator
family over the letters' own enumeration. -/
theorem wedge_clen (d l : Nat) :
    (wedge d l).content.length = d :=
  ground.length_mapRange _ d

private theorem wedge_off (d l : Nat) :
    ∀ i, i < (wedge d l).coords.length →
      ¬ (ground.getAt BPair.unit (wedge d l).coords i).oneValue
        BPair.unit := by
  intro i hi
  have hi' : i < (monomialsAt ((List.range d).map
      (fun i => if i < l then 1 else 0))).length := by
    have h2 : ((monomialsAt ((List.range d).map
        (fun i => if i < l then 1 else 0))).map
        (fun m => if parity m then (BPair.ofNat 1).swap
          else BPair.ofNat 1)).length
        = (monomialsAt ((List.range d).map
          (fun i => if i < l then 1 else 0))).length :=
      ground.length_map _ _
    rw [show (wedge d l).coords.length
        = ((monomialsAt ((List.range d).map
          (fun i => if i < l then 1 else 0))).map
          (fun m => if parity m then (BPair.ofNat 1).swap
            else BPair.ofNat 1)).length from rfl, h2] at hi
    exact hi
  show ¬ (ground.getAt BPair.unit
    ((monomialsAt ((List.range d).map
      (fun i => if i < l then 1 else 0))).map
      (fun m => if parity m then (BPair.ofNat 1).swap
        else BPair.ofNat 1)) i).oneValue BPair.unit
  rw [ground.getAt_map [] BPair.unit _ _ i hi']
  by_cases hp : parity (ground.getAt [] (monomialsAt
      ((List.range d).map (fun i => if i < l then 1 else 0))) i)
      = true
  · rw [if_pos hp]
    exact BPair.ofNat_one_swap_off
  · rw [if_neg hp]
    exact BPair.ofNat_one_off

private theorem map_zero_range : ∀ d : Nat,
    (List.range d).map (fun _ => (0 : Nat))
      = List.replicate d 0
  | 0 => rfl
  | d + 1 => by
    rw [range_succ d, ground.map_append, map_zero_range d]
    exact ground.replicate_snoc 0 d

private theorem exhibit_dist (d : Nat) :
    ∀ (ls : List Nat) (acc : HVec),
      acc.content.length = d → sized acc →
      (∃ m, m.length = sumNat acc.content
        ∧ content acc.content.length m = acc.content
        ∧ ¬ (ground.getAt BPair.unit acc.coords
            (rankOf m acc.content)).oneValue BPair.unit) →
      ∃ m, m.length = sumNat
          (ls.foldl (fun acc l => tensorH acc (wedge d l))
            acc).content
        ∧ content (ls.foldl (fun acc l => tensorH acc (wedge d l))
              acc).content.length m
          = (ls.foldl (fun acc l => tensorH acc (wedge d l))
              acc).content
        ∧ ¬ (ground.getAt BPair.unit
            (ls.foldl (fun acc l => tensorH acc (wedge d l))
              acc).coords
            (rankOf m (ls.foldl
              (fun acc l => tensorH acc (wedge d l))
              acc).content)).oneValue BPair.unit
  | [], _, _, _, hd => hd
  | l :: ls, acc, hcl, hsz, hd => by
    match hd with
    | ⟨m, hm1, hm2, hoff⟩ =>
      refine exhibit_dist d ls (tensorH acc (wedge d l)) ?_
        (tensorH_sized acc (wedge d l)) ?_
      · show (List.zipWith (fun a b => a + b) acc.content
          (wedge d l).content).length = d
        exact ground.length_zipWith (fun x y => x + y) acc.content (wedge d l).content
          d hcl (wedge_clen d l)
      · exact tensor_dist acc (wedge d l)
          (by rw [hcl, wedge_clen d l]) hsz (wedge_sized d l)
          m hm1 hm2 hoff (wedge_off d l)

/-- The exhibit's coordinate family sits off the unit tail: the
distinguished arrangement's coefficient survives every tensor
step, the factors' distinguished pair unique at the
concatenation's rank (`lem:lowerspan`'s seed clause). -/
theorem exhibit_off_unit (s : Shape) :
    ¬ poly.unitTail (exhibit s).coords := by
  have hseed : ∃ m, m.length
        = sumNat (⟨List.replicate s.length 0,
            [BPair.ofNat 1]⟩ : HVec).content
      ∧ content (⟨List.replicate s.length 0,
            [BPair.ofNat 1]⟩ : HVec).content.length m
          = (⟨List.replicate s.length 0,
            [BPair.ofNat 1]⟩ : HVec).content
      ∧ ¬ (ground.getAt BPair.unit
          (⟨List.replicate s.length 0,
            [BPair.ofNat 1]⟩ : HVec).coords
          (rankOf m (⟨List.replicate s.length 0,
            [BPair.ofNat 1]⟩ : HVec).content)).oneValue
          BPair.unit := by
    refine ⟨[], (sumNat_replicate_zero s.length).symm, ?_, ?_⟩
    · show content (List.replicate s.length 0).length []
        = List.replicate s.length 0
      rw [ground.length_replicate]
      show (List.range s.length).map
        (fun i => ground.countOf i ([] : List Nat))
        = List.replicate s.length 0
      rw [ground.map_congr_all
        (fun i => ground.countOf i ([] : List Nat))
        (fun _ => (0 : Nat)) (fun i => rfl)
        (List.range s.length)]
      exact map_zero_range s.length
    · exact BPair.ofNat_one_off
  have hs0 : sized (⟨List.replicate s.length 0,
      [BPair.ofNat 1]⟩ : HVec) := by
    show (1 : Nat)
      = (monomialsAt (List.replicate s.length 0)).length
    rw [places.monomialsAt_sum_zero _
      (sumNat_replicate_zero s.length)]
    rfl
  match exhibit_dist s.length (columnLengths s)
      ⟨List.replicate s.length 0, [BPair.ofNat 1]⟩
      (ground.length_replicate 0 s.length) hs0 hseed with
  | ⟨m, hm1, hm2, hoff⟩ =>
    intro hu
    refine hoff ?_
    exact poly.getAt_unitTail hu _

private theorem indep_seed (v : HVec) (hs : sized v)
    (hoff : ¬ poly.unitTail v.coords) : indepAll [v] := by
  intro mu _
  rw [groupAt_cons v [] mu]
  cases hb : v.content == mu with
  | true =>
    have hcmu : v.content = mu := ground.listBeqEq hb
    show elim.indepRows (places.monomialsAt mu).length
      (v.coords :: groupAt [] mu)
    refine elim.indep_single _ _ ?_ hoff
    rw [hs, hcmu]
  | false => exact elim.indep_nil _

/-- The span's semantic reads at a stated measure (`lem:lowerspan`'s
joined-collection clause): with the measure dropping per occupied lowering,
move-free at its floor, and the exhibit's coordinates off the unit
tail, the span is sized, its content groups are independent, and
every member's occupied adjacent lowering image sits in its group's
span. -/
theorem blockSpan_sem (s : Shape) (meas : List Nat → Nat)
    (hnomove : ∀ v : HVec, v.content.length = s.length →
      meas v.content = 0 → ∀ j : Nat, j < s.length - 1 →
      lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v w : HVec), j < s.length - 1 →
      lowerH j v = some w → v.content.length = s.length →
      meas w.content + 1 = meas v.content)
    (hexh : meas (rowList s) ≤ degree s * s.length)
    (hsized : sized (exhibit s))
    (hseed : ¬ poly.unitTail (exhibit s).coords) :
    (∀ v ∈ blockSpan s, sized v) ∧ indepAll (blockSpan s)
      ∧ closedAt (blockSpan s) s.length := by
  have hclen : (exhibit s).content.length = s.length := by
    rw [content_exhibit s, places.length_rowList s]
  have hKkeep : ∀ (j : Nat) (v w : HVec), lowerH j v = some w →
      v.content.length = s.length → w.content.length = s.length := by
    intro j v w heq hv
    rw [(lowerH_fields heq).1, units.length_moveDn j v.content]
    exact hv
  have hindseed : indepAll [exhibit s] :=
    indep_seed (exhibit s) hsized hseed
  match closeSpan_sem s.length meas
      (fun v => v.content.length = s.length) hKkeep hnomove hdrop
      (degree s * s.length) [] [exhibit s]
      (memAll_cons hsized memAll_nil)
      (memAll_cons hclen memAll_nil) hindseed memAll_nil
      (memAll_cons (by
        show meas (exhibit s).content ≤ degree s * s.length
        rw [content_exhibit s]
        exact hexh) memAll_nil) with
  | ⟨ext, heq, hs, _, hind, hclosed⟩ =>
    rw [show (([] : List HVec) ++ [exhibit s]) = [exhibit s]
      from rfl] at heq hs hind hclosed
    refine ⟨?_, ?_, ?_⟩
    · show ∀ v ∈ blockSpan s, sized v
      rw [show blockSpan s = closeSpan s.length
          (degree s * s.length) [exhibit s] [exhibit s] from rfl,
        heq]
      exact hs
    · show indepAll (blockSpan s)
      rw [show blockSpan s = closeSpan s.length
          (degree s * s.length) [exhibit s] [exhibit s] from rfl,
        heq]
      exact hind
    · exact hclosed

/-! The exhibit's top read (`lem:tops`(iii)): an adjacent raising's
image of the column exhibit reads the sum's unit at every
coordinate — a raised wedge repeats a letter and the repeat's
transposition joins the arrangements in opposite-parity pairs, the
tensor's raising splitting over the concatenation by the Leibniz
fold. -/

private theorem content_eq_of_entries (d : Nat) (m mu : List Nat)
    (hl : mu.length = d)
    (h : ∀ x, x < d → ground.countOf x m = ground.getAt 0 mu x) :
    content d m = mu := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · show ((List.range d).map
      (fun i => ground.countOf i m)).length = mu.length
    rw [ground.length_mapRange, hl]
  · intro x hx
    have hxd : x < d := by
      have h2 : ((List.range d).map
          (fun i => ground.countOf i m)).length = d :=
        ground.length_mapRange _ d
      show x < d
      rw [← h2]
      exact hx
    rw [getAt_contentAt d m x hxd]
    exact h x hxd

/-! The Leibniz sum over an action's outputs, the raising image's
own read at a target monomial. -/

private def coordAt (v : HVec) (m : List Nat) : BPair :=
  ground.getAt BPair.unit v.coords (rankOf m v.content)

private theorem bsum_mulR (f : List Nat → BPair) (c : BPair) :
    ∀ l : List (List Nat),
      (ground.bsum (fun m => f m * c) l).oneValue (ground.bsum f l * c)
  | [] => BPair.oneValue_symm (BPair.unit_mul c)
  | m :: t => by
    show (f m * c + ground.bsum (fun m => f m * c) t).oneValue
      ((f m + ground.bsum f t) * c)
    rw [BPair.right_distrib]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (bsum_mulR f c t)

/-! The coefficient fold against a source enumeration, the
combination's positional read. -/

/-- The weighted fold over paired lists: the pairing at the mapped
member list, `wSum f bs cs` and `elim.dotP cs (bs.map f)` one
value at every input by the shared recursion.  The definition
keeps the zip recursion's own spelling, the per-member pattern
its family's proofs and consumers read — a collapse onto the
pairing would rewrite the family for no consumer's gain. -/
private def wSum (f : List Nat → BPair) :
    List (List Nat) → List BPair → BPair
  | [], _ => BPair.unit
  | _ :: _, [] => BPair.unit
  | s :: bs, c :: cs => c * f s + wSum f bs cs

private theorem wSum_null (f : List Nat → BPair) :
    ∀ (bs : List (List Nat)) (cs : List BPair),
      (∀ s, 0 < ground.countOf s bs →
        (f s).oneValue BPair.unit) →
      (wSum f bs cs).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | b :: bs, c :: cs, h => by
    have htail : ∀ s, 0 < ground.countOf s bs →
        (f s).oneValue BPair.unit := by
      intro s hs
      refine h s (Nat.lt_of_lt_of_le hs ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show (c * f b + wSum f bs cs).oneValue BPair.unit
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl c)
            (h b (by
              rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
              exact Nat.succ_pos _)))
          (BPair.mul_unit c))
        (wSum_null f bs cs htail)) ?_
    exact BPair.unit_add BPair.unit

private theorem wSum_congr (f g : List Nat → BPair) :
    ∀ (bs : List (List Nat)) (cs : List BPair),
      (∀ s, 0 < ground.countOf s bs → (f s).oneValue (g s)) →
      (wSum f bs cs).oneValue (wSum g bs cs)
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | b :: bs, c :: cs, h => by
    have htail : ∀ s, 0 < ground.countOf s bs →
        (f s).oneValue (g s) := by
      intro s hs
      refine h s (Nat.lt_of_lt_of_le hs ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show (c * f b + wSum f bs cs).oneValue
      (c * g b + wSum g bs cs)
    exact BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl c)
        (h b (by
          rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
          exact Nat.succ_pos _)))
      (wSum_congr f g bs cs htail)

private theorem wSum_add (f g : List Nat → BPair) :
    ∀ (bs : List (List Nat)) (cs : List BPair),
      (wSum (fun s => f s + g s) bs cs).oneValue
        (wSum f bs cs + wSum g bs cs)
  | [], _ => BPair.oneValue_symm (BPair.unit_add _)
  | _ :: _, [] => BPair.oneValue_symm (BPair.unit_add _)
  | b :: bs, c :: cs => by
    show (c * (f b + g b) + wSum (fun s => f s + g s) bs cs).oneValue
      (c * f b + wSum f bs cs + (c * g b + wSum g bs cs))
    rw [BPair.left_distrib, BPair.add_assoc, BPair.add_assoc,
      BPair.add_left_comm (wSum f bs cs) (c * g b)]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.oneValue_refl _)
        (wSum_add f g bs cs))

private theorem wSum_delta :
    ∀ (bs : List (List Nat)) (cs : List BPair) (k : Nat),
      k < bs.length → k < cs.length →
      ground.countOf (ground.getAt [] bs k) bs = 1 →
      (wSum (fun s => BPair.ofNat
        (if s = ground.getAt [] bs k then 1 else 0)) bs cs).oneValue
        (ground.getAt BPair.unit cs k)
  | [], _, k, hb, _, _ => absurd hb (Nat.not_lt_zero k)
  | _ :: _, [], k, _, hc, _ => absurd hc (Nat.not_lt_zero k)
  | b :: bs, c :: cs, 0, _, _, hcnt => by
    have hcnt0 : ground.countOf b bs = 0 := by
      have hsplit : (if (b : List Nat) = b then 1 else 0)
          + ground.countOf b bs = 1 := by
        rw [← ground.countOf_cons]
        exact hcnt
      rw [if_pos rfl, Nat.add_comm] at hsplit
      exact Nat.succ.inj hsplit
    show (c * BPair.ofNat (if (b : List Nat) = b then 1 else 0)
      + wSum (fun s => BPair.ofNat (if s = b then 1 else 0))
        bs cs).oneValue c
    rw [if_pos rfl]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_ofNat_one c)
        (wSum_null _ bs cs ?_)) (BPair.add_unit c)
    intro s hs
    have hsb : ¬ s = b := by
      intro he
      rw [he, hcnt0] at hs
      exact absurd hs (Nat.lt_irrefl 0)
    rw [if_neg hsb]
    exact BPair.oneValue_refl _
  | b :: bs, c :: cs, k + 1, hb, hc, hcnt => by
    have hb' : k < bs.length := Nat.lt_of_succ_lt_succ hb
    have hc' : k < cs.length := Nat.lt_of_succ_lt_succ hc
    match head_ne_of_count_one hb' hcnt with
    | ⟨hne, hcnt'⟩ =>
      show (c * BPair.ofNat
          (if (b : List Nat) = ground.getAt [] bs k then 1 else 0)
        + wSum (fun s => BPair.ofNat
            (if s = ground.getAt [] bs k then 1 else 0))
          bs cs).oneValue (ground.getAt BPair.unit cs k)
      rw [if_neg (fun he => hne he.symm)]
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_unit c)
          (wSum_delta bs cs k hb' hc' hcnt'))
        (BPair.unit_add _)

/-! The raising image's entry: the unit matrix's action reads the
combination over the source enumeration, and the counts collect to
the Leibniz sum over the reversed action's outputs. -/

private def colOf (muTo : List Nat) (i j : Nat) (s : List Nat) :
    List BPair :=
  (units.unitAct i j s).foldl
    (fun col m =>
      if m.length = sumNat muTo ∧ content muTo.length m = muTo then
        units.scatterAt (rankOf m muTo) (BPair.ofNat 1) col
      else col)
    ((monomialsAt muTo).map (fun _ => BPair.unit))

private theorem colOf_len (muTo : List Nat) (i j : Nat)
    (s : List Nat) :
    (colOf muTo i j s).length = (monomialsAt muTo).length := by
  rw [show colOf muTo i j s = (units.unitAct i j s).foldl
        (fun col m =>
          if m.length = sumNat muTo
              ∧ content muTo.length m = muTo then
            units.scatterAt (rankOf m muTo) (BPair.ofNat 1) col
          else col)
        ((monomialsAt muTo).map (fun _ => BPair.unit)) from rfl,
    foldl_len_inv _
      (fun acc m => by
        by_cases hm : m.length = sumNat muTo
            ∧ content muTo.length m = muTo
        · rw [if_pos hm]
          exact units.length_scatterAt _ _ acc
        · rw [if_neg hm])
      (units.unitAct i j s) _,
    ground.length_map]

private theorem matUnitAt_cols (muTo muFrom : List Nat)
    (i j : Nat) :
    units.matUnitAt muTo muFrom i j
      = elim.transposeM
        ((monomialsAt muFrom).map (colOf muTo i j)) := rfl

private theorem colOf_entry (muTo muFrom : List Nat) (i j : Nat)
    (hout : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (units.unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (p q : Nat) (hp : p < (monomialsAt muTo).length)
    (hq : q < (monomialsAt muFrom).length) :
    (ground.getAt BPair.unit
      (colOf muTo i j
        (ground.getAt [] (monomialsAt muFrom) q)) p).oneValue
      (BPair.ofNat (ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (units.unitAct i j
          (ground.getAt [] (monomialsAt muFrom) q)))) := by
  have hX : ground.getAt ([] : List BPair)
      ((monomialsAt muFrom).map (colOf muTo i j)) q
      = colOf muTo i j (ground.getAt [] (monomialsAt muFrom) q) :=
    ground.getAt_map ([] : List Nat) ([] : List BPair)
      (colOf muTo i j) (monomialsAt muFrom) q hq
  have hT := elim.getAt_transposeM BPair.unit
    ((monomialsAt muFrom).map (colOf muTo i j))
    (elim.rowsLen_map (colOf muTo i j) (monomialsAt muTo).length
      (monomialsAt muFrom) (fun x _ => colOf_len muTo i j x))
    p q hp (by rw [ground.length_map]; exact hq)
  rw [← hX, ← hT, ← matUnitAt_cols muTo muFrom i j]
  exact units.matUnitAt_read muTo muFrom i j hout p q hp hq

private theorem wSum_dotP (g : List Nat → BPair) :
    ∀ (bs : List (List Nat)) (cs : List BPair),
      wSum g bs cs = elim.dotP cs (bs.map g)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, c :: cs => by
    show c * g b + wSum g bs cs
      = c * g b + elim.dotP cs (bs.map g)
    rw [wSum_dotP g bs cs]

/-- The combination's entry at a key: the coefficients' weighted
fold over the members' own reads, the general read's instance at
the mapped family. -/
private theorem getAt_combo (n : Nat) (f : List Nat → List BPair)
    (hf : ∀ s, (f s).length = n) (p : Nat) (hp : p < n)
    (bs : List (List Nat)) (cs : List BPair) :
    (ground.getAt BPair.unit
      (elim.combo n cs (bs.map f)) p).oneValue
      (wSum (fun s => ground.getAt BPair.unit (f s) p) bs cs) := by
  rw [wSum_dotP (fun s => ground.getAt BPair.unit (f s) p) bs cs]
  have h := elim.combo_getAt n cs (bs.map f) p
    (elim.rowsLen_map f n bs (fun x _ => hf x)) hp
  rw [ground.map_map f
    (fun r => ground.getAt BPair.unit r p) bs] at h
  exact h

private theorem matVec_entry (muTo muFrom : List Nat) (i j : Nat)
    (hout : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (units.unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (x : List BPair) (hx : x.length = (monomialsAt muFrom).length)
    (p : Nat) (hp : p < (monomialsAt muTo).length) :
    (ground.getAt BPair.unit
      (elim.matVec (units.matUnitAt muTo muFrom i j) x) p).oneValue
      (wSum (fun s => BPair.ofNat (ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (units.unitAct i j s))) (monomialsAt muFrom) x) := by
  have hrows := elim.rowsLen_map (colOf muTo i j)
    (monomialsAt muTo).length (monomialsAt muFrom)
    (fun x _ => colOf_len muTo i j x)
  have hcombo := elim.matVec_transpose_combo
    (monomialsAt muTo).length
    ((monomialsAt muFrom).map (colOf muTo i j)) x hrows
    (by rw [hx, ground.length_map])
  rw [matUnitAt_cols muTo muFrom i j]
  refine BPair.oneValue_trans (poly.oneValue_getAt p hcombo) ?_
  refine BPair.oneValue_trans
    (getAt_combo (monomialsAt muTo).length (colOf muTo i j)
      (colOf_len muTo i j) p hp (monomialsAt muFrom) x) ?_
  refine wSum_congr _ _ (monomialsAt muFrom) x ?_
  intro s hs
  match member_conditions hs with
  | ⟨hl, hc⟩ =>
    have hr := rankOf_read s muFrom hl hc
    have he := colOf_entry muTo muFrom i j hout p
      (rankOf s muFrom) hp hr.1
    rw [hr.2] at he
    exact he

private theorem wSum_collect (mu : List Nat) (x : List BPair)
    (hx : x.length = (monomialsAt mu).length) :
    ∀ outs : List (List Nat),
      (∀ m, 0 < ground.countOf m outs →
        m.length = sumNat mu ∧ content mu.length m = mu) →
      (wSum (fun s => BPair.ofNat (ground.countOf s outs))
        (monomialsAt mu) x).oneValue
        (ground.bsum (fun m =>
          ground.getAt BPair.unit x (rankOf m mu)) outs)
  | [], _ => wSum_null _ _ _ (fun _ _ => BPair.oneValue_refl _)
  | m :: rest, h => by
    have hm := h m (by
      rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
      exact Nat.succ_pos _)
    have hrest : ∀ m', 0 < ground.countOf m' rest →
        m'.length = sumNat mu ∧ content mu.length m' = mu := by
      intro m' hm'
      refine h m' (Nat.lt_of_lt_of_le hm' ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show (wSum (fun s => BPair.ofNat (ground.countOf s (m :: rest)))
        (monomialsAt mu) x).oneValue
      (ground.getAt BPair.unit x (rankOf m mu)
        + ground.bsum (fun m' =>
            ground.getAt BPair.unit x (rankOf m' mu)) rest)
    refine BPair.oneValue_trans
      (wSum_congr _ (fun s => BPair.ofNat (if s = m then 1 else 0)
          + BPair.ofNat (ground.countOf s rest))
        (monomialsAt mu) x
        (fun s _ => by
          rw [ground.countOf_cons]
          exact BPair.ofNat_add _ _)) ?_
    refine BPair.oneValue_trans
      (wSum_add _ _ (monomialsAt mu) x) ?_
    have hr := rankOf_read m mu hm.1 hm.2
    refine BPair.add_congr ?_ (wSum_collect mu x hx rest hrest)
    have hd := wSum_delta (monomialsAt mu) x (rankOf m mu) hr.1
      (by rw [hx]; exact hr.1)
      (by rw [hr.2]; exact count_one_of_member hm.1 hm.2)
    rw [hr.2] at hd
    exact hd

/-! The raised content's reads and the two output transports: a
raising's outputs sit at the raised content, the reversed action's
outputs back at the source's. -/

private theorem getAt_moveUp_next (j : Nat) (nu : List Nat)
    (hb : 0 < ground.getAt 0 nu (j + 1)) :
    ground.getAt 0 (units.moveUp j nu) (j + 1) + 1
      = ground.getAt 0 nu (j + 1) := by
  rw [units.getAt_moveUp_next j nu]
  exact ground.subAdd hb

private theorem sumNat_moveUp : ∀ (j : Nat) (nu : List Nat),
    j + 1 < nu.length → 0 < ground.getAt 0 nu (j + 1) →
    sumNat (units.moveUp j nu) = sumNat nu
  | 0, [], h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], h, _ => absurd h (Nat.not_lt_zero _)
  | 0, [_], h, _ => absurd h (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, hb => by
    match b, hb with
    | 0, hb => exact absurd hb (Nat.lt_irrefl 0)
    | c + 1, _ =>
      show a + 1 + (c + sumNat t) = a + (c + 1 + sumNat t)
      rw [Nat.add_assoc, ← Nat.add_assoc 1 c (sumNat t),
        Nat.add_comm 1 c]
  | j + 1, a :: t, h, hb => by
    show a + sumNat (units.moveUp j t) = a + sumNat t
    rw [sumNat_moveUp j t (Nat.lt_of_succ_lt_succ h) hb]

private theorem raise_out_fwd (mu : List Nat) (j : Nat)
    (hj : j + 1 < mu.length)
    (hocc : 0 < ground.getAt 0 mu (j + 1)) :
    ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (units.unitAct j (j + 1) s) →
      m.length = sumNat (units.moveUp j mu)
        ∧ content (units.moveUp j mu).length m
          = units.moveUp j mu := by
  intro s m hs hm
  have hd : (units.moveUp j mu).length = mu.length :=
    units.length_moveUp j mu
  match member_conditions hs with
  | ⟨hsl, hsc⟩ =>
    refine ⟨?_, ?_⟩
    · rw [units.length_unitAct_out j (j + 1) s m hm, hsl,
        sumNat_moveUp j mu hj hocc]
    · rw [hd]
      refine content_eq_of_entries mu.length m
        (units.moveUp j mu) hd ?_
      intro x hx
      have hcnt := units.countOf_unitAct_out j (j + 1) x s m hm
      have hsx : ground.countOf x s = ground.getAt 0 mu x := by
        rw [← getAt_contentAt mu.length s x hx, hsc]
      rw [hsx] at hcnt
      by_cases hxj : x = j
      · rw [hxj] at hcnt ⊢
        rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_self j)), if_pos rfl,
          Nat.add_zero] at hcnt
        rw [hcnt, units.getAt_moveUp_self j mu
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
            (Nat.le_of_lt hj))]
      · by_cases hxj1 : x = j + 1
        · rw [hxj1] at hcnt ⊢
          rw [if_pos rfl, if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm),
            Nat.add_zero] at hcnt
          refine ground.addCancelR 1 ?_
          rw [hcnt, getAt_moveUp_next j mu hocc]
          exact Nat.add_zero _
        · rw [if_neg hxj1, if_neg hxj, Nat.add_zero,
            Nat.add_zero] at hcnt
          rw [hcnt, units.getAt_moveUp_ne j mu x hxj hxj1]

private theorem raise_out_rev (mu : List Nat) (j : Nat)
    (hj : j + 1 < mu.length)
    (hocc : 0 < ground.getAt 0 mu (j + 1)) :
    ∀ t m : List Nat,
      0 < ground.countOf t (monomialsAt (units.moveUp j mu)) →
      0 < ground.countOf m (units.unitAct (j + 1) j t) →
      m.length = sumNat mu ∧ content mu.length m = mu := by
  intro t m ht hm
  have hd : (units.moveUp j mu).length = mu.length :=
    units.length_moveUp j mu
  match member_conditions ht with
  | ⟨htl, htc⟩ =>
    have htc' : content mu.length t = units.moveUp j mu := by
      rw [← hd]
      exact htc
    refine ⟨?_, ?_⟩
    · rw [units.length_unitAct_out (j + 1) j t m hm, htl,
        sumNat_moveUp j mu hj hocc]
    · refine content_eq_of_entries mu.length m mu rfl ?_
      intro x hx
      have hcnt := units.countOf_unitAct_out (j + 1) j x t m hm
      have htx : ground.countOf x t
          = ground.getAt 0 (units.moveUp j mu) x := by
        rw [← getAt_contentAt mu.length t x hx, htc']
      rw [htx] at hcnt
      by_cases hxj : x = j
      · rw [hxj] at hcnt ⊢
        rw [if_pos rfl, if_neg (Nat.ne_of_lt (Nat.lt_succ_self j)),
          Nat.add_zero] at hcnt
        refine ground.addCancelR 1 ?_
        rw [hcnt, units.getAt_moveUp_self j mu
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
            (Nat.le_of_lt hj))]
      · by_cases hxj1 : x = j + 1
        · rw [hxj1] at hcnt ⊢
          rw [if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm),
            if_pos rfl, Nat.add_zero] at hcnt
          rw [hcnt, getAt_moveUp_next j mu hocc]
        · rw [if_neg hxj, if_neg hxj1, Nat.add_zero,
            Nat.add_zero] at hcnt
          rw [hcnt, units.getAt_moveUp_ne j mu x hxj hxj1]

/-! The occupancy sum over a concatenation and a member's
distinctness at a unit-occupancy content — the distinctness the
wedge's pairing consumes, the letters' bound itself read from its
owner (`places.mem_lt_of_content`). -/

private theorem member_distinct (mu m : List Nat)
    (hle : ∀ i, ground.getAt 0 mu i ≤ 1)
    (hl : m.length = sumNat mu) (hc : content mu.length m = mu) :
    ∀ y, ground.countOf y m ≤ 1 := by
  have hsum : sumNat (content mu.length m) = m.length := by
    rw [hc, hl]
  intro y
  match Nat.eq_zero_or_pos (ground.countOf y m) with
  | .inl hz =>
    rw [hz]
    exact Nat.le_succ 0
  | .inr hpos =>
    have hyd := mem_lt_of_content mu.length m hsum y hpos
    have h2 : ground.countOf y m = ground.getAt 0 mu y := by
      rw [← getAt_contentAt mu.length m y hyd, hc]
    rw [h2]
    exact hle y

/-! The Leibniz action's output list at a letter's occupancy: one
output at a single place, the two replacements at a repeated one,
and the split over a concatenation. -/

private def repl1 (i x : Nat) : List Nat → List Nat
  | [] => []
  | a :: t => if x = a then i :: t else a :: repl1 i x t

private def repl2 (i x : Nat) : List Nat → List Nat
  | [] => []
  | a :: t => if x = a then a :: repl1 i x t else a :: repl2 i x t

private def pos2 (x : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => if x = a then posOf x t + 1 else pos2 x t + 1

private theorem repl1_hit (i x a : Nat) (t : List Nat)
    (h : x = a) : repl1 i x (a :: t) = i :: t := by
  show (if x = a then i :: t else a :: repl1 i x t) = i :: t
  rw [if_pos h]

private theorem repl1_miss (i x a : Nat) (t : List Nat)
    (h : ¬ x = a) : repl1 i x (a :: t) = a :: repl1 i x t := by
  show (if x = a then i :: t else a :: repl1 i x t) = _
  rw [if_neg h]

private theorem repl2_hit (i x a : Nat) (t : List Nat)
    (h : x = a) : repl2 i x (a :: t) = a :: repl1 i x t := by
  show (if x = a then a :: repl1 i x t
    else a :: repl2 i x t) = _
  rw [if_pos h]

private theorem repl2_miss (i x a : Nat) (t : List Nat)
    (h : ¬ x = a) : repl2 i x (a :: t) = a :: repl2 i x t := by
  show (if x = a then a :: repl1 i x t
    else a :: repl2 i x t) = _
  rw [if_neg h]

private theorem posOf_hit (x a : Nat) (t : List Nat) (h : x = a) :
    posOf x (a :: t) = 0 := by
  show (if x = a then 0 else posOf x t + 1) = 0
  rw [if_pos h]

private theorem posOf_miss (x a : Nat) (t : List Nat)
    (h : ¬ x = a) : posOf x (a :: t) = posOf x t + 1 := by
  show (if x = a then 0 else posOf x t + 1) = _
  rw [if_neg h]

private theorem pos2_hit (x a : Nat) (t : List Nat) (h : x = a) :
    pos2 x (a :: t) = posOf x t + 1 := by
  show (if x = a then posOf x t + 1 else pos2 x t + 1) = _
  rw [if_pos h]

private theorem pos2_miss (x a : Nat) (t : List Nat)
    (h : ¬ x = a) : pos2 x (a :: t) = pos2 x t + 1 := by
  show (if x = a then posOf x t + 1 else pos2 x t + 1) = _
  rw [if_neg h]

private theorem length_repl1 (i x : Nat) : ∀ t : List Nat,
    (repl1 i x t).length = t.length
  | [] => rfl
  | a :: t => by
    by_cases h : x = a
    · rw [repl1_hit i x a t h]
      rfl
    · rw [repl1_miss i x a t h]
      exact congrArg Nat.succ (length_repl1 i x t)

private theorem length_repl2 (i x : Nat) : ∀ t : List Nat,
    (repl2 i x t).length = t.length
  | [] => rfl
  | a :: t => by
    by_cases h : x = a
    · rw [repl2_hit i x a t h]
      exact congrArg Nat.succ (length_repl1 i x t)
    · rw [repl2_miss i x a t h]
      exact congrArg Nat.succ (length_repl2 i x t)

private theorem getAt_repl1_self (i x : Nat) : ∀ t : List Nat,
    0 < ground.countOf x t →
    ground.getAt 0 (repl1 i x t) (posOf x t) = i
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: t, h => by
    by_cases hxa : x = a
    · rw [repl1_hit i x a t hxa, posOf_hit x a t hxa]
      rfl
    · rw [repl1_miss i x a t hxa, posOf_miss x a t hxa]
      show ground.getAt 0 (repl1 i x t) (posOf x t) = i
      refine getAt_repl1_self i x t ?_
      rw [← ground.countOf_head_ne hxa t]
      exact h

private theorem getAt_repl1_ne (i x : Nat) :
    ∀ (t : List Nat) (k : Nat), ¬ k = posOf x t →
      ground.getAt 0 (repl1 i x t) k = ground.getAt 0 t k
  | [], _, _ => rfl
  | a :: t, k, hk => by
    by_cases hxa : x = a
    · match k with
      | 0 => exact absurd (posOf_hit x a t hxa).symm hk
      | _ + 1 =>
        rw [repl1_hit i x a t hxa]
        rfl
    · rw [repl1_miss i x a t hxa]
      match k with
      | 0 => rfl
      | k + 1 =>
        show ground.getAt 0 (repl1 i x t) k = ground.getAt 0 t k
        refine getAt_repl1_ne i x t k ?_
        intro he
        exact hk (by rw [posOf_miss x a t hxa, he])

private theorem getAt_repl2_self (i x : Nat) : ∀ t : List Nat,
    2 ≤ ground.countOf x t →
    ground.getAt 0 (repl2 i x t) (pos2 x t) = i
  | [], h => absurd h (Nat.not_succ_le_zero 1)
  | a :: t, h => by
    by_cases hxa : x = a
    · rw [repl2_hit i x a t hxa, pos2_hit x a t hxa]
      show ground.getAt 0 (repl1 i x t) (posOf x t) = i
      refine getAt_repl1_self i x t ?_
      have h2 : ground.countOf x t + 1
          = ground.countOf x (a :: t) := by
        rw [hxa, ground.countOf_head]
      have h3 : 2 ≤ ground.countOf x t + 1 := by
        rw [h2]
        exact h
      exact Nat.le_of_succ_le_succ h3
    · rw [repl2_miss i x a t hxa, pos2_miss x a t hxa]
      show ground.getAt 0 (repl2 i x t) (pos2 x t) = i
      refine getAt_repl2_self i x t ?_
      rw [← ground.countOf_head_ne hxa t]
      exact h

private theorem getAt_repl2_ne (i x : Nat) :
    ∀ (t : List Nat) (k : Nat), ¬ k = pos2 x t →
      ground.getAt 0 (repl2 i x t) k = ground.getAt 0 t k
  | [], _, _ => rfl
  | a :: t, k, hk => by
    by_cases hxa : x = a
    · rw [repl2_hit i x a t hxa]
      match k with
      | 0 => rfl
      | k + 1 =>
        show ground.getAt 0 (repl1 i x t) k = ground.getAt 0 t k
        refine getAt_repl1_ne i x t k ?_
        intro he
        exact hk (by rw [pos2_hit x a t hxa, he])
    · rw [repl2_miss i x a t hxa]
      match k with
      | 0 => rfl
      | k + 1 =>
        show ground.getAt 0 (repl2 i x t) k = ground.getAt 0 t k
        refine getAt_repl2_ne i x t k ?_
        intro he
        exact hk (by rw [pos2_miss x a t hxa, he])

private theorem posOf_lt_pos2 (x : Nat) : ∀ t : List Nat,
    2 ≤ ground.countOf x t → posOf x t < pos2 x t
  | [], h => absurd h (Nat.not_succ_le_zero 1)
  | a :: t, h => by
    by_cases hxa : x = a
    · rw [posOf_hit x a t hxa, pos2_hit x a t hxa]
      exact Nat.succ_pos _
    · rw [posOf_miss x a t hxa, pos2_miss x a t hxa]
      refine Nat.succ_lt_succ (posOf_lt_pos2 x t ?_)
      rw [← ground.countOf_head_ne hxa t]
      exact h

private theorem pos2_lt (x : Nat) : ∀ t : List Nat,
    2 ≤ ground.countOf x t → pos2 x t < t.length
  | [], h => absurd h (Nat.not_succ_le_zero 1)
  | a :: t, h => by
    by_cases hxa : x = a
    · rw [pos2_hit x a t hxa]
      refine Nat.succ_lt_succ (posOf_lt x t ?_)
      have h2 : ground.countOf x t + 1
          = ground.countOf x (a :: t) := by
        rw [hxa, ground.countOf_head]
      have h3 : 2 ≤ ground.countOf x t + 1 := by
        rw [h2]
        exact h
      exact Nat.le_of_succ_le_succ h3
    · rw [pos2_miss x a t hxa]
      refine Nat.succ_lt_succ (pos2_lt x t ?_)
      rw [← ground.countOf_head_ne hxa t]
      exact h

private theorem getAt_pos2 (x : Nat) : ∀ t : List Nat,
    2 ≤ ground.countOf x t → ground.getAt 0 t (pos2 x t) = x
  | [], h => absurd h (Nat.not_succ_le_zero 1)
  | a :: t, h => by
    by_cases hxa : x = a
    · rw [pos2_hit x a t hxa]
      show ground.getAt 0 t (posOf x t) = x
      refine getAt_posOf x t ?_
      have h2 : ground.countOf x t + 1
          = ground.countOf x (a :: t) := by
        rw [hxa, ground.countOf_head]
      have h3 : 2 ≤ ground.countOf x t + 1 := by
        rw [h2]
        exact h
      exact Nat.le_of_succ_le_succ h3
    · rw [pos2_miss x a t hxa]
      show ground.getAt 0 t (pos2 x t) = x
      refine getAt_pos2 x t ?_
      rw [← ground.countOf_head_ne hxa t]
      exact h

private theorem unitAct_pos (i x : Nat) : ∀ t : List Nat,
    0 < ground.countOf x t →
    0 < ground.countOf (repl1 i x t) (units.unitAct i x t)
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: t, h => by
    by_cases hxa : x = a
    · rw [units.unitAct_cons_hit i x a t hxa, repl1_hit i x a t hxa,
        ground.countOf_head]
      exact Nat.succ_pos _
    · rw [units.unitAct_cons_miss i x a t hxa, repl1_miss i x a t hxa,
        ground.countOf_consMap a a (units.unitAct i x t)
          (repl1 i x t), if_pos rfl]
      refine unitAct_pos i x t ?_
      rw [← ground.countOf_head_ne hxa t]
      exact h

private theorem unitAct_one (i x : Nat) : ∀ t : List Nat,
    ground.countOf x t = 1 → units.unitAct i x t = [repl1 i x t]
  | [], h => Nat.noConfusion h
  | a :: t, h => by
    by_cases hxa : x = a
    · have hz : ground.countOf x t = 0 := by
        have h2 : ground.countOf x t + 1
            = ground.countOf x (a :: t) := by
          rw [hxa, ground.countOf_head]
        have h' : ground.countOf x t + 1 = 1 := by
          rw [h2]
          exact h
        exact Nat.succ.inj h'
      rw [units.unitAct_cons_hit i x a t hxa,
        units.unitAct_nil_of_zero i x t hz,
        repl1_hit i x a t hxa]
      rfl
    · have h1 : ground.countOf x t = 1 := by
        rw [← ground.countOf_head_ne hxa t]
        exact h
      rw [units.unitAct_cons_miss i x a t hxa, unitAct_one i x t h1,
        repl1_miss i x a t hxa]
      rfl

private theorem unitAct_two (i x : Nat) : ∀ t : List Nat,
    ground.countOf x t = 2 →
    units.unitAct i x t = [repl1 i x t, repl2 i x t]
  | [], h => Nat.noConfusion h
  | a :: t, h => by
    by_cases hxa : x = a
    · have h1 : ground.countOf x t = 1 := by
        have h2 : ground.countOf x t + 1
            = ground.countOf x (a :: t) := by
          rw [hxa, ground.countOf_head]
        have h' : ground.countOf x t + 1 = 2 := by
          rw [h2]
          exact h
        exact Nat.succ.inj h'
      rw [units.unitAct_cons_hit i x a t hxa, unitAct_one i x t h1,
        repl1_hit i x a t hxa, repl2_hit i x a t hxa]
      rfl
    · have h2 : ground.countOf x t = 2 := by
        rw [← ground.countOf_head_ne hxa t]
        exact h
      rw [units.unitAct_cons_miss i x a t hxa, unitAct_two i x t h2,
        repl1_miss i x a t hxa, repl2_miss i x a t hxa]
      rfl

private theorem repl2_swapPair (i x : Nat) (t : List Nat)
    (h : 2 ≤ ground.countOf x t) :
    places.swapPair (posOf x t) (pos2 x t) (repl1 i x t)
      = repl2 i x t := by
  have hlt := posOf_lt_pos2 x t h
  have hne : ¬ posOf x t = pos2 x t := fun he =>
    Nat.lt_irrefl (posOf x t) (by
      rw [he] at hlt ⊢
      exact hlt)
  have h1 : 0 < ground.countOf x t :=
    Nat.lt_of_lt_of_le (Nat.succ_pos 1) h
  have hp : posOf x t < (repl1 i x t).length := by
    rw [length_repl1]
    exact posOf_lt x t h1
  have hq : pos2 x t < (repl1 i x t).length := by
    rw [length_repl1]
    exact pos2_lt x t h
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [places.length_swapPair, length_repl1, length_repl2]
  · intro k _
    by_cases hkp : k = posOf x t
    · rw [hkp, places.getAt_swapPair_fst _ hne hp hq,
        getAt_repl1_ne i x t (pos2 x t) (fun he => hne he.symm),
        getAt_pos2 x t h, getAt_repl2_ne i x t (posOf x t) hne,
        getAt_posOf x t h1]
    · by_cases hkq : k = pos2 x t
      · rw [hkq, places.getAt_swapPair_snd _ hne hp hq,
          getAt_repl1_self i x t h1, getAt_repl2_self i x t h]
      · rw [places.getAt_swapPair_ne _ hp hq hkp hkq,
          getAt_repl1_ne i x t k hkp, getAt_repl2_ne i x t k hkq]

private theorem parity_repl2 (i x : Nat) (t : List Nat)
    (h : 2 ≤ ground.countOf x t)
    (hdist : ∀ y, ground.countOf y (repl1 i x t) ≤ 1) :
    parity (repl2 i x t) = !(parity (repl1 i x t)) := by
  have hlt := posOf_lt_pos2 x t h
  have hne : ¬ posOf x t = pos2 x t := fun he =>
    Nat.lt_irrefl (posOf x t) (by
      rw [he] at hlt ⊢
      exact hlt)
  have h1 : 0 < ground.countOf x t :=
    Nat.lt_of_lt_of_le (Nat.succ_pos 1) h
  have hp : posOf x t < (repl1 i x t).length := by
    rw [length_repl1]
    exact posOf_lt x t h1
  have hq : pos2 x t < (repl1 i x t).length := by
    rw [length_repl1]
    exact pos2_lt x t h
  rw [← repl2_swapPair i x t h]
  exact places.parity_swapPair (repl1 i x t) hne hp hq hdist

/-! The tensor's coordinate at a concatenated monomial: the
factors' coordinates multiply, and an off-content split reads the
sum's unit. -/

private theorem hitI_unitL (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) (hp : p.2 = BPair.unit) :
    ∀ ql : List (List Nat × BPair),
      (hitI mu' k' p ql).oneValue BPair.unit
  | [] => BPair.oneValue_refl _
  | q :: t => by
    show (if q.2.isUnitRep then hitI mu' k' p t
        else if k' = rankOf (p.1 ++ q.1) mu' then
          p.2 * q.2 + hitI mu' k' p t
        else hitI mu' k' p t).oneValue BPair.unit
    by_cases hq : q.2.isUnitRep = true
    · rw [if_pos hq]
      exact hitI_unitL mu' k' p hp t
    · rw [if_neg hq]
      by_cases hr : k' = rankOf (p.1 ++ q.1) mu'
      · rw [if_pos hr]
        refine BPair.oneValue_trans
          (BPair.add_congr ?_ (hitI_unitL mu' k' p hp t))
          (BPair.unit_add BPair.unit)
        rw [hp]
        exact BPair.unit_mul q.2
      · rw [if_neg hr]
        exact hitI_unitL mu' k' p hp t

private theorem hitI_gen (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) :
    ∀ (bs : List (List Nat)) (cs : List BPair) (i₀ : Nat),
      i₀ < bs.length → i₀ < cs.length →
      k' = rankOf (p.1 ++ ground.getAt [] bs i₀) mu' →
      (∀ y, 0 < ground.countOf y bs →
        ¬ y = ground.getAt [] bs i₀ →
        ¬ k' = rankOf (p.1 ++ y) mu') →
      ground.countOf (ground.getAt [] bs i₀) bs = 1 →
      (hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        (p.2 * ground.getAt BPair.unit cs i₀)
  | [], _, i₀, hb, _, _, _, _ => absurd hb (Nat.not_lt_zero i₀)
  | _ :: _, [], i₀, _, hc, _, _, _ =>
    absurd hc (Nat.not_lt_zero i₀)
  | b :: bs, c :: cs, 0, _, _, hk, hmiss, hcnt => by
    have hcnt0 : ground.countOf b bs = 0 := by
      have hsplit : (if (b : List Nat) = b then 1 else 0)
          + ground.countOf b bs = 1 := by
        rw [← ground.countOf_cons]
        exact hcnt
      rw [if_pos rfl, Nat.add_comm] at hsplit
      exact Nat.succ.inj hsplit
    have hk' : k' = rankOf (p.1 ++ b) mu' := hk
    have hnull : (hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        BPair.unit := by
      refine ground.BPair.oneValue_of_eq (hitI_null mu' k' p _ ?_)
      intro q hq _
      match zip_member bs cs hq with
      | ⟨idx, hib, _, he⟩ =>
        refine hmiss q.1 ?_ ?_
        · rw [ground.countOf_cons]
          refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
          rw [he]
          exact ground.countOf_getAt_pos [] bs idx hib
        · intro hqb
          have hbb : ground.getAt [] bs idx = b := by
            rw [he] at hqb
            exact hqb
          have hpos := ground.countOf_getAt_pos [] bs idx hib
          rw [hbb, hcnt0] at hpos
          exact absurd hpos (Nat.lt_irrefl 0)
    show (if (c : BPair).isUnitRep then
        hitI mu' k' p (List.zipWith (fun m x => (m, x)) bs cs)
      else if k' = rankOf (p.1 ++ b) mu' then
        p.2 * c + hitI mu' k' p
          (List.zipWith (fun m x => (m, x)) bs cs)
      else hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (p.2 * c)
    by_cases hcu : (c : BPair).isUnitRep = true
    · rw [if_pos hcu]
      refine BPair.oneValue_trans hnull ?_
      rw [BPair.unit_of_isUnitRep hcu]
      exact BPair.oneValue_symm (BPair.mul_unit p.2)
    · rw [if_neg hcu, if_pos hk']
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) hnull)
        (BPair.add_unit _)
  | b :: bs, c :: cs, i₀ + 1, hb, hc, hk, hmiss, hcnt => by
    have hb' : i₀ < bs.length := Nat.lt_of_succ_lt_succ hb
    have hc' : i₀ < cs.length := Nat.lt_of_succ_lt_succ hc
    match head_ne_of_count_one hb' hcnt with
    | ⟨hne, hcnt'⟩ =>
      have hmiss' : ∀ y, 0 < ground.countOf y bs →
          ¬ y = ground.getAt [] bs i₀ →
          ¬ k' = rankOf (p.1 ++ y) mu' := by
        intro y hy hyne
        refine hmiss y (Nat.lt_of_lt_of_le hy ?_) hyne
        rw [ground.countOf_cons]
        exact Nat.le_add_left _ _
      have hrec := hitI_gen mu' k' p bs cs i₀ hb' hc' hk hmiss'
        hcnt'
      have hbmiss : ¬ k' = rankOf (p.1 ++ b) mu' :=
        hmiss b (by
          rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
          exact Nat.succ_pos _) (fun he => hne he.symm)
      show (if (c : BPair).isUnitRep then
          hitI mu' k' p (List.zipWith (fun m x => (m, x)) bs cs)
        else if k' = rankOf (p.1 ++ b) mu' then
          p.2 * c + hitI mu' k' p
            (List.zipWith (fun m x => (m, x)) bs cs)
        else hitI mu' k' p
          (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        (p.2 * ground.getAt BPair.unit cs i₀)
      by_cases hcu : (c : BPair).isUnitRep = true
      · rw [if_pos hcu]
        exact hrec
      · rw [if_neg hcu, if_neg hbmiss]
        exact hrec

private theorem hitO_gen (mu' : List Nat) (k' : Nat)
    (ql : List (List Nat × BPair)) :
    ∀ (bs : List (List Nat)) (cs : List BPair) (i₀ : Nat),
      i₀ < bs.length → i₀ < cs.length →
      (∀ y, 0 < ground.countOf y bs →
        ¬ y = ground.getAt [] bs i₀ →
        ∀ q, 0 < ground.countOf q ql → q.2.isUnitRep = false →
        ¬ k' = rankOf (y ++ q.1) mu') →
      ground.countOf (ground.getAt [] bs i₀) bs = 1 →
      (hitO mu' k' ql
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        (hitI mu' k' (ground.getAt [] bs i₀,
          ground.getAt BPair.unit cs i₀) ql)
  | [], _, i₀, hb, _, _, _ => absurd hb (Nat.not_lt_zero i₀)
  | _ :: _, [], i₀, _, hc, _, _ => absurd hc (Nat.not_lt_zero i₀)
  | b :: bs, c :: cs, 0, _, _, hmiss, hcnt => by
    have hcnt0 : ground.countOf b bs = 0 := by
      have hsplit : (if (b : List Nat) = b then 1 else 0)
          + ground.countOf b bs = 1 := by
        rw [← ground.countOf_cons]
        exact hcnt
      rw [if_pos rfl, Nat.add_comm] at hsplit
      exact Nat.succ.inj hsplit
    have hnull : (hitO mu' k' ql
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        BPair.unit := by
      refine hitO_null mu' k' ql _ ?_
      intro pp hpp _ q hq hqu
      match zip_member bs cs hpp with
      | ⟨idx, hib, _, he⟩ =>
        refine hmiss pp.1 ?_ ?_ q hq hqu
        · rw [ground.countOf_cons]
          refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
          rw [he]
          exact ground.countOf_getAt_pos [] bs idx hib
        · intro hpb
          have hbb : ground.getAt [] bs idx = b := by
            rw [he] at hpb
            exact hpb
          have hpos := ground.countOf_getAt_pos [] bs idx hib
          rw [hbb, hcnt0] at hpos
          exact absurd hpos (Nat.lt_irrefl 0)
    show (if (c : BPair).isUnitRep then
        hitO mu' k' ql (List.zipWith (fun m x => (m, x)) bs cs)
      else hitI mu' k' (b, c) ql
        + hitO mu' k' ql
          (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (hitI mu' k' (b, c) ql)
    by_cases hcu : (c : BPair).isUnitRep = true
    · rw [if_pos hcu]
      exact BPair.oneValue_trans hnull
        (BPair.oneValue_symm (hitI_unitL mu' k' (b, c)
          (BPair.unit_of_isUnitRep hcu) ql))
    · rw [if_neg hcu]
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) hnull)
        (BPair.add_unit _)
  | b :: bs, c :: cs, i₀ + 1, hb, hc, hmiss, hcnt => by
    have hb' : i₀ < bs.length := Nat.lt_of_succ_lt_succ hb
    have hc' : i₀ < cs.length := Nat.lt_of_succ_lt_succ hc
    match head_ne_of_count_one hb' hcnt with
    | ⟨hne, hcnt'⟩ =>
      have hmiss' : ∀ y, 0 < ground.countOf y bs →
          ¬ y = ground.getAt [] bs i₀ →
          ∀ q, 0 < ground.countOf q ql → q.2.isUnitRep = false →
          ¬ k' = rankOf (y ++ q.1) mu' := by
        intro y hy hyne
        refine hmiss y (Nat.lt_of_lt_of_le hy ?_) hyne
        rw [ground.countOf_cons]
        exact Nat.le_add_left _ _
      have hrec := hitO_gen mu' k' ql bs cs i₀ hb' hc' hmiss' hcnt'
      show (if (c : BPair).isUnitRep then
          hitO mu' k' ql (List.zipWith (fun m x => (m, x)) bs cs)
        else hitI mu' k' (b, c) ql
          + hitO mu' k' ql
            (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
        (hitI mu' k' (ground.getAt [] bs i₀,
          ground.getAt BPair.unit cs i₀) ql)
      by_cases hcu : (c : BPair).isUnitRep = true
      · rw [if_pos hcu]
        exact hrec
      · rw [if_neg hcu,
          hitI_null mu' k' (b, c) ql (fun q hq hqu =>
            hmiss b (by
              rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
              exact Nat.succ_pos _)
              (fun he => hne he.symm) q hq hqu)]
        exact BPair.oneValue_trans (BPair.unit_add _) hrec

private theorem tensor_getAt (v w : HVec) (k : Nat)
    (hk : k < (monomialsAt (List.zipWith (fun a b => a + b)
      v.content w.content)).length) :
    (ground.getAt BPair.unit (tensorH v w).coords k).oneValue
      (hitO (List.zipWith (fun a b => a + b) v.content w.content) k
        (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
          w.coords)
        (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
          v.coords)) := by
  have hseedlen : k < ((monomialsAt
      (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit)).length := by
    rw [ground.length_map]
    exact hk
  show (ground.getAt BPair.unit
    (((List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x))
              (monomialsAt w.content) w.coords).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt
                (rankOf (p.1 ++ q.1)
                  (List.zipWith (fun a b => a + b) v.content
                    w.content))
                (p.2 * q.2) acc2)
            acc)
      ((monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit))).map
      BPair.norm) k).oneValue _
  have hfoldlen : k < ((List.zipWith (fun m x => (m, x))
      (monomialsAt v.content) v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x))
              (monomialsAt w.content) w.coords).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt
                (rankOf (p.1 ++ q.1)
                  (List.zipWith (fun a b => a + b) v.content
                    w.content))
                (p.2 * q.2) acc2)
            acc)
      ((monomialsAt (List.zipWith (fun a b => a + b) v.content
        w.content)).map (fun _ => BPair.unit))).length := by
    rw [foldl_len_inv _ (fun acc p => by
      by_cases hp : p.2.isUnitRep = true
      · rw [if_pos hp]
      · rw [if_neg hp]
        exact innerFold_len _ p _ acc) _ _]
    exact hseedlen
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ _
    hfoldlen]
  have hout := getAt_outerFold
    (List.zipWith (fun a b => a + b) v.content w.content) k
    (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
      w.coords)
    (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
      v.coords)
    ((monomialsAt (List.zipWith (fun a b => a + b) v.content
      w.content)).map (fun _ => BPair.unit)) hseedlen
  rw [ground.getAt_map ([] : List Nat) BPair.unit
    (fun _ => BPair.unit) _ _ hk] at hout
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans hout (BPair.unit_add _))

private theorem tensor_coord (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (hsv : sized v) (hsw : sized w) (m1 m2 : List Nat)
    (h1l : m1.length = sumNat v.content)
    (h1c : content v.content.length m1 = v.content)
    (h2l : m2.length = sumNat w.content)
    (h2c : content w.content.length m2 = w.content) :
    (ground.getAt BPair.unit (tensorH v w).coords
      (rankOf (m1 ++ m2)
        (List.zipWith (fun a b => a + b) v.content
          w.content))).oneValue
      (coordAt v m1 * coordAt w m2) := by
  have hm' := concat_member v.content w.content m1 m2 hlen h1l h1c
    h2l h2c
  have hkB := rankOf_read (m1 ++ m2)
    (List.zipWith (fun a b => a + b) v.content w.content)
    hm'.1 hm'.2
  have hvB := rankOf_read m1 v.content h1l h1c
  have hwB := rankOf_read m2 w.content h2l h2c
  have hi₀c : rankOf m1 v.content < v.coords.length := by
    rw [hsv]
    exact hvB.1
  have hj₀c : rankOf m2 w.content < w.coords.length := by
    rw [hsw]
    exact hwB.1
  have hrinj : ∀ y q1 : List Nat,
      y.length = sumNat v.content →
      content v.content.length y = v.content →
      q1.length = sumNat w.content →
      content w.content.length q1 = w.content →
      rankOf (m1 ++ m2)
          (List.zipWith (fun a b => a + b) v.content w.content)
        = rankOf (y ++ q1)
          (List.zipWith (fun a b => a + b) v.content w.content) →
      y = m1 ∧ q1 = m2 := by
    intro y q1 hy1 hy2 hq1 hq2 heq
    have hyq := concat_member v.content w.content y q1 hlen
      hy1 hy2 hq1 hq2
    have hyB := rankOf_read (y ++ q1)
      (List.zipWith (fun a b => a + b) v.content w.content)
      hyq.1 hyq.2
    have hgets : m1 ++ m2 = y ++ q1 := by
      rw [← hkB.2, ← hyB.2, heq]
    match append_inj_len m1 y m2 q1 (by rw [hy1, h1l]) hgets with
    | ⟨hmy, hq⟩ => exact ⟨hmy.symm, hq.symm⟩
  have hO := hitO_gen
    (List.zipWith (fun a b => a + b) v.content w.content)
    (rankOf (m1 ++ m2)
      (List.zipWith (fun a b => a + b) v.content w.content))
    (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
      w.coords)
    (monomialsAt v.content) v.coords (rankOf m1 v.content)
    hvB.1 hi₀c
    (by
      intro y hy hyne q hq _ hkr
      match zip_member (monomialsAt w.content) w.coords hq with
      | ⟨idx, hib, _, he⟩ =>
        have hym := member_conditions hy
        have hqm := member_conditions
          (ground.countOf_getAt_pos [] (monomialsAt w.content)
            idx hib)
        have hq1 : q.1
            = ground.getAt [] (monomialsAt w.content) idx := by
          rw [he]
        refine hyne ?_
        rw [hvB.2]
        exact (hrinj y q.1 hym.1 hym.2
          (by rw [hq1]; exact hqm.1)
          (by rw [hq1]; exact hqm.2) hkr).1)
    (by
      rw [hvB.2]
      exact count_one_of_member h1l h1c)
  rw [hvB.2] at hO
  have hI := hitI_gen
    (List.zipWith (fun a b => a + b) v.content w.content)
    (rankOf (m1 ++ m2)
      (List.zipWith (fun a b => a + b) v.content w.content))
    (m1, ground.getAt BPair.unit v.coords (rankOf m1 v.content))
    (monomialsAt w.content) w.coords (rankOf m2 w.content)
    hwB.1 hj₀c
    (by rw [hwB.2])
    (by
      intro y hy hyne hkr
      have hym := member_conditions hy
      refine hyne ?_
      rw [hwB.2]
      exact (hrinj m1 y h1l h1c hym.1 hym.2 hkr).2)
    (by
      rw [hwB.2]
      exact count_one_of_member h2l h2c)
  exact BPair.oneValue_trans
    (tensor_getAt v w _ hkB.1)
    (BPair.oneValue_trans hO hI)

private theorem tensor_coord_null (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (M1 M2 : List Nat)
    (hMl : (M1 ++ M2).length
      = sumNat (List.zipWith (fun a b => a + b) v.content
        w.content))
    (hMc : content (List.zipWith (fun a b => a + b) v.content
        w.content).length (M1 ++ M2)
      = List.zipWith (fun a b => a + b) v.content w.content)
    (h1l : M1.length = sumNat v.content)
    (hbad : (M1.length = sumNat v.content
        ∧ content v.content.length M1 = v.content) →
      (M2.length = sumNat w.content
        ∧ content w.content.length M2 = w.content) → False) :
    (ground.getAt BPair.unit (tensorH v w).coords
      (rankOf (M1 ++ M2)
        (List.zipWith (fun a b => a + b) v.content
          w.content))).oneValue BPair.unit := by
  have hkB := rankOf_read (M1 ++ M2)
    (List.zipWith (fun a b => a + b) v.content w.content) hMl hMc
  have hnull := hitO_null
    (List.zipWith (fun a b => a + b) v.content w.content)
    (rankOf (M1 ++ M2)
      (List.zipWith (fun a b => a + b) v.content w.content))
    (List.zipWith (fun m x => (m, x)) (monomialsAt w.content)
      w.coords)
    (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
      v.coords)
    (by
      intro pp hpp _ q hq _ hkr
      match zip_member (monomialsAt v.content) v.coords hpp with
      | ⟨i1, hi1, _, he1⟩ =>
        match zip_member (monomialsAt w.content) w.coords hq with
        | ⟨i2, hi2, _, he2⟩ =>
          have hpm := member_conditions
            (ground.countOf_getAt_pos [] (monomialsAt v.content)
              i1 hi1)
          have hqm := member_conditions
            (ground.countOf_getAt_pos [] (monomialsAt w.content)
              i2 hi2)
          have hp1 : pp.1
              = ground.getAt [] (monomialsAt v.content) i1 := by
            rw [he1]
          have hq1 : q.1
              = ground.getAt [] (monomialsAt w.content) i2 := by
            rw [he2]
          have hpc : pp.1.length = sumNat v.content
              ∧ content v.content.length pp.1 = v.content := by
            rw [hp1]
            exact hpm
          have hqc : q.1.length = sumNat w.content
              ∧ content w.content.length q.1 = w.content := by
            rw [hq1]
            exact hqm
          have hcm := concat_member v.content w.content pp.1 q.1
            hlen hpc.1 hpc.2 hqc.1 hqc.2
          have hB := rankOf_read (pp.1 ++ q.1)
            (List.zipWith (fun a b => a + b) v.content w.content)
            hcm.1 hcm.2
          have heq : M1 ++ M2 = pp.1 ++ q.1 := by
            rw [← hkB.2, ← hB.2, hkr]
          match append_inj_len M1 pp.1 M2 q.1
              (by rw [hpc.1, h1l]) heq with
          | ⟨hm2, hq2⟩ =>
            refine hbad ?_ ?_
            · rw [hm2]
              exact hpc
            · rw [hq2]
              exact hqc)
  exact BPair.oneValue_trans (tensor_getAt v w _ hkB.1) hnull

/-! The raising's vanishing invariant, and the wedge's own read: a
raised wedge repeats a letter, the repeat's transposition joining
the two outputs at opposite gradings. -/

private def actNull (i x : Nat) (v : HVec) : Prop :=
  ∀ t : List Nat,
    (∀ m, 0 < ground.countOf m (units.unitAct i x t) →
      m.length = sumNat v.content
        ∧ content v.content.length m = v.content) →
    (ground.bsum (coordAt v) (units.unitAct i x t)).oneValue
      BPair.unit

private def raiseNull (j : Nat) (v : HVec) : Prop :=
  actNull (j + 1) j v

private theorem swapPairSum (x : BPair) :
    (x + (x.swap + BPair.unit)).oneValue BPair.unit := by
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl x)
      (BPair.add_unit x.swap)) ?_
  rw [BPair.add_comm]
  exact BPair.swap_add_null (BPair.oneValue_refl x)

private theorem swapPairSum' (x : BPair) :
    (x.swap + (x + BPair.unit)).oneValue BPair.unit :=
  swapPairSum x.swap

private theorem wedge_raiseNull (d l j : Nat) (hj : j + 1 < d) :
    raiseNull j (wedge d l) := by
  intro t hmem
  have hwl : (wedge d l).content.length = d := wedge_clen d l
  have hwcget : ∀ x, x < d →
      ground.getAt 0 (wedge d l).content x
        = if x < l then 1 else 0 := by
    intro x hx
    show ground.getAt 0 ((List.range d).map
      (fun i => if i < l then 1 else 0)) x = _
    rw [ground.getAt_map 0 0 (fun i => if i < l then 1 else 0)
        (List.range d) x
        (by rw [ground.length_range]; exact hx),
      ground.getAt_range d x hx]
  have hcntmem : ∀ m x, 0 < ground.countOf m
        (units.unitAct (j + 1) j t) → x < d →
      ground.countOf x m
        = ground.getAt 0 (wedge d l).content x := by
    intro m x hm hx
    match hmem m hm with
    | ⟨_, hmc⟩ =>
      rw [hwl] at hmc
      rw [← getAt_contentAt d m x hx, hmc]
  have hcoord : ∀ m : List Nat,
      m.length = sumNat (wedge d l).content →
      content (wedge d l).content.length m = (wedge d l).content →
      coordAt (wedge d l) m
        = if parity m then (BPair.ofNat 1).swap
          else BPair.ofNat 1 := by
    intro m hml hmc
    have hr := rankOf_read m (wedge d l).content hml hmc
    show ground.getAt BPair.unit
      ((monomialsAt (wedge d l).content).map (fun m =>
        if parity m then (BPair.ofNat 1).swap else BPair.ofNat 1))
      (rankOf m (wedge d l).content) = _
    rw [ground.getAt_map ([] : List Nat) BPair.unit _
      (monomialsAt (wedge d l).content) _ hr.1, hr.2]
  have hjd : j < d :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  by_cases hjl : j + 1 < l
  · match Nat.eq_zero_or_pos (ground.countOf j t) with
    | .inl hz =>
      rw [units.unitAct_nil_of_zero (j + 1) j t hz]
      exact BPair.oneValue_refl _
    | .inr hpos =>
      have hr1 := unitAct_pos (j + 1) j t hpos
      have hwj : ground.getAt 0 (wedge d l).content j = 1 := by
        rw [hwcget j hjd,
          if_pos (Nat.lt_trans (Nat.lt_succ_self j) hjl)]
      have hcnt2 : ground.countOf j t = 2 := by
        have ho := units.countOf_unitAct_out (j + 1) j j t
          (repl1 (j + 1) j t) hr1
        rw [if_pos rfl, if_neg (Nat.ne_of_lt (Nat.lt_succ_self j)),
          hcntmem (repl1 (j + 1) j t) j hr1 hjd, hwj] at ho
        exact (Nat.add_zero _).symm.trans ho.symm
      have hle : ∀ i,
          ground.getAt 0 (wedge d l).content i ≤ 1 := by
        intro i
        by_cases hid : i < d
        · rw [hwcget i hid]
          by_cases hil : i < l
          · rw [if_pos hil]
            exact Nat.le_refl 1
          · rw [if_neg hil]
            exact Nat.le_succ 0
        · rw [ground.getAt_over 0 (wedge d l).content i
            (by rw [hwl]; exact Nat.le_of_not_lt hid)]
          exact Nat.le_succ 0
      have hlist := unitAct_two (j + 1) j t hcnt2
      have hm2 : 0 < ground.countOf (repl2 (j + 1) j t)
          (units.unitAct (j + 1) j t) := by
        rw [hlist]
        refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
        show 0 < ground.countOf (repl2 (j + 1) j t)
          [repl2 (j + 1) j t]
        rw [ground.countOf_cons, if_pos rfl]
        exact Nat.succ_pos 0
      have hdist : ∀ y,
          ground.countOf y (repl1 (j + 1) j t) ≤ 1 :=
        member_distinct (wedge d l).content (repl1 (j + 1) j t)
          hle (hmem _ hr1).1 (hmem _ hr1).2
      have hpar := parity_repl2 (j + 1) j t
        (Nat.le_of_eq hcnt2.symm) hdist
      rw [hlist]
      show (coordAt (wedge d l) (repl1 (j + 1) j t)
        + (coordAt (wedge d l) (repl2 (j + 1) j t)
          + BPair.unit)).oneValue BPair.unit
      rw [hcoord (repl1 (j + 1) j t) (hmem _ hr1).1 (hmem _ hr1).2,
        hcoord (repl2 (j + 1) j t) (hmem _ hm2).1 (hmem _ hm2).2,
        hpar]
      cases hp : parity (repl1 (j + 1) j t) with
      | true =>
        rw [if_pos rfl, if_neg (fun hc : (!true) = true =>
          Bool.noConfusion hc)]
        exact swapPairSum' (BPair.ofNat 1)
      | false =>
        rw [if_neg (fun hc : (false : Bool) = true =>
            Bool.noConfusion hc),
          if_pos (show (!false) = true from rfl)]
        exact swapPairSum (BPair.ofNat 1)
  · refine ground.foldB_null _ _ ?_
    intro m hm
    have hw1 : ground.countOf (j + 1) m = 0 := by
      rw [hcntmem m (j + 1) hm hj, hwcget (j + 1) hj, if_neg hjl]
    have ho := units.countOf_unitAct_out (j + 1) j (j + 1) t m hm
    rw [hw1, if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm),
      if_pos rfl] at ho
    have hbad : ground.countOf (j + 1) t + 1 = 0 := ho.symm
    exact Nat.noConfusion hbad

/-! The tensor's raising: the Leibniz fold splits over the
concatenation, each half a factor's own raising against the other
factor's coordinate. -/

private theorem countOf_map_pos {α β : Type} [DecidableEq α]
    [DecidableEq β] (g : α → β) (a : α) :
    ∀ l : List α, 0 < ground.countOf a l →
      0 < ground.countOf (g a) (l.map g)
  | [], h => absurd h (Nat.lt_irrefl 0)
  | b :: t, h => by
    show 0 < ground.countOf (g a) (g b :: t.map g)
    rw [ground.countOf_cons]
    by_cases hab : a = b
    · rw [if_pos (congrArg g hab), Nat.add_comm]
      exact Nat.succ_pos _
    · refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
      refine countOf_map_pos g a t ?_
      rw [← ground.countOf_head_ne hab t]
      exact h

private theorem zipWith_add_cancelR (a b c : List Nat) (n : Nat)
    (ha : a.length = n) (hb : b.length = n) (hc : c.length = n)
    (h : List.zipWith (fun x y => x + y) a c
      = List.zipWith (fun x y => x + y) b c) : a = b := by
  refine ground.getAt_ext 0 _ _ (ha.trans hb.symm) ?_
  intro i hi
  rw [ha] at hi
  have e1 := ground.getAt_zipWith 0 0 0 (fun x y => x + y) a c i (by rw [ha]; exact hi)
    (by rw [hc]; exact hi)
  have e2 := ground.getAt_zipWith 0 0 0 (fun x y => x + y) b c i (by rw [hb]; exact hi)
    (by rw [hc]; exact hi)
  rw [h, e2] at e1
  exact (ground.addCancelR _ e1).symm

theorem zipWith_add_cancelL (c a b : List Nat) (n : Nat)
    (hc : c.length = n) (ha : a.length = n) (hb : b.length = n)
    (h : List.zipWith (fun x y => x + y) c a
      = List.zipWith (fun x y => x + y) c b) : a = b := by
  refine ground.getAt_ext 0 _ _ (ha.trans hb.symm) ?_
  intro i hi
  rw [ha] at hi
  have e1 := ground.getAt_zipWith 0 0 0 (fun x y => x + y) c a i (by rw [hc]; exact hi)
    (by rw [ha]; exact hi)
  have e2 := ground.getAt_zipWith 0 0 0 (fun x y => x + y) c b i (by rw [hc]; exact hi)
    (by rw [hb]; exact hi)
  rw [h, e2] at e1
  have e3 : ground.getAt 0 b i + ground.getAt 0 c i
      = ground.getAt 0 a i + ground.getAt 0 c i := by
    rw [Nat.add_comm (ground.getAt 0 b i),
      Nat.add_comm (ground.getAt 0 a i)]
    exact e1
  exact (ground.addCancelR _ e3).symm

private theorem tensor_raise_split (j : Nat) (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (hsv : sized v) (hsw : sized w)
    (hv : raiseNull j v) (hw : raiseNull j w)
    (t1 t2 : List Nat)
    (h1 : t1.length = sumNat v.content)
    (h2 : t2.length = sumNat w.content)
    (hmem : ∀ m, 0 < ground.countOf m
        (units.unitAct (j + 1) j (t1 ++ t2)) →
      m.length = sumNat (tensorH v w).content
        ∧ content (tensorH v w).content.length m
          = (tensorH v w).content) :
    (ground.bsum (coordAt (tensorH v w))
      (units.unitAct (j + 1) j (t1 ++ t2))).oneValue
      BPair.unit := by
  have hd : (List.zipWith (fun a b => a + b) v.content
      w.content).length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hlen.symm
  have hmemA : ∀ m1, 0 < ground.countOf m1
      (units.unitAct (j + 1) j t1) →
      (m1 ++ t2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (m1 ++ t2)
          = List.zipWith (fun a b => a + b) v.content w.content := by
    intro m1 hm1
    refine hmem (m1 ++ t2) ?_
    rw [units.unitAct_append (j + 1) j t1 t2, ground.countOf_append]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
    exact countOf_map_pos (fun m => m ++ t2) m1
      (units.unitAct (j + 1) j t1) hm1
  have hmemB : ∀ m2, 0 < ground.countOf m2
      (units.unitAct (j + 1) j t2) →
      (t1 ++ m2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (t1 ++ m2)
          = List.zipWith (fun a b => a + b) v.content w.content := by
    intro m2 hm2
    refine hmem (t1 ++ m2) ?_
    rw [units.unitAct_append (j + 1) j t1 t2, ground.countOf_append]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
    exact countOf_map_pos (fun m => t1 ++ m) m2
      (units.unitAct (j + 1) j t2) hm2
  have hA : (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct (j + 1) j t1).map
        (fun m => m ++ t2))).oneValue BPair.unit := by
    rw [ground.bsum_map]
    by_cases h2m : content w.content.length t2 = w.content
    · have hm1c : ∀ m1, 0 < ground.countOf m1
          (units.unitAct (j + 1) j t1) →
          m1.length = sumNat v.content
            ∧ content v.content.length m1 = v.content := by
        intro m1 hm1
        refine ⟨(units.length_unitAct_out (j + 1) j t1 m1 hm1).trans
          h1, ?_⟩
        have hc := (hmemA m1 hm1).2
        have ht2c : content v.content.length t2 = w.content := by
          rw [hlen]
          exact h2m
        rw [hd, content_append v.content.length m1 t2, ht2c] at hc
        refine zipWith_add_cancelR (content v.content.length m1)
          v.content w.content v.content.length ?_ rfl hlen.symm hc
        exact ground.length_mapRange _ v.content.length
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _ (fun m1 => coordAt v m1 * coordAt w t2)
          (units.unitAct (j + 1) j t1)
          (fun m1 hm1 => tensor_coord v w hlen hsv hsw m1 t2
            (hm1c m1 hm1).1 (hm1c m1 hm1).2 h2 h2m)) ?_
      exact BPair.oneValue_trans
        (bsum_mulR (coordAt v) (coordAt w t2) _)
        (BPair.oneValue_trans
          (BPair.mul_congr (hv t1 hm1c) (BPair.oneValue_refl _))
          (BPair.unit_mul _))
    · refine ground.foldB_null _ _ ?_
      intro m1 hm1
      refine tensor_coord_null v w hlen m1 t2 (hmemA m1 hm1).1
        (hmemA m1 hm1).2
        ((units.length_unitAct_out (j + 1) j t1 m1 hm1).trans h1)
        ?_
      intro _ hq
      exact h2m hq.2
  have hB : (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct (j + 1) j t2).map
        (fun m => t1 ++ m))).oneValue BPair.unit := by
    rw [ground.bsum_map]
    by_cases h1m : content v.content.length t1 = v.content
    · have hm2c : ∀ m2, 0 < ground.countOf m2
          (units.unitAct (j + 1) j t2) →
          m2.length = sumNat w.content
            ∧ content w.content.length m2 = w.content := by
        intro m2 hm2
        refine ⟨(units.length_unitAct_out (j + 1) j t2 m2 hm2).trans
          h2, ?_⟩
        have hc := (hmemB m2 hm2).2
        rw [hd, content_append v.content.length t1 m2, h1m] at hc
        have hcm : content v.content.length m2 = w.content := by
          refine zipWith_add_cancelL v.content
            (content v.content.length m2) w.content
            v.content.length rfl ?_ hlen.symm hc
          exact ground.length_mapRange _ v.content.length
        rw [← hlen]
        exact hcm
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _ (fun m2 => coordAt v t1 * coordAt w m2)
          (units.unitAct (j + 1) j t2)
          (fun m2 hm2 => tensor_coord v w hlen hsv hsw t1 m2 h1 h1m
            (hm2c m2 hm2).1 (hm2c m2 hm2).2)) ?_
      exact BPair.oneValue_trans
        (ground.foldB_mul_left (coordAt v t1) (coordAt w) _)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) (hw t2 hm2c))
          (BPair.mul_unit _))
    · refine ground.foldB_null _ _ ?_
      intro m2 hm2
      refine tensor_coord_null v w hlen t1 m2 (hmemB m2 hm2).1
        (hmemB m2 hm2).2 h1 ?_
      intro hp _
      exact h1m hp.2
  rw [units.unitAct_append (j + 1) j t1 t2]
  exact BPair.oneValue_trans
    (ground.famFold_append_ov ground.bpairFoldLaws _ _ _)
    (BPair.oneValue_trans (BPair.add_congr hA hB)
      (BPair.unit_add BPair.unit))

private theorem tensor_raiseNull (j : Nat) (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (hsv : sized v) (hsw : sized w)
    (hv : raiseNull j v) (hw : raiseNull j w) :
    raiseNull j (tensorH v w) := by
  intro t hmem
  by_cases htl : t.length
      = sumNat (List.zipWith (fun a b => a + b) v.content
        w.content)
  · have hsum : sumNat (List.zipWith (fun a b => a + b) v.content
        w.content) = sumNat v.content + sumNat w.content :=
      sumNat_zipWith_add v.content w.content hlen
    have hle : sumNat v.content ≤ t.length := by
      rw [htl, hsum]
      exact Nat.le_add_right _ _
    have h1 : (List.take (sumNat v.content) t).length
        = sumNat v.content := ground.length_take _ t hle
    have h2 : (List.drop (sumNat v.content) t).length
        = sumNat w.content := by
      have hsplit : (List.take (sumNat v.content) t).length
          + (List.drop (sumNat v.content) t).length = t.length := by
        rw [← ground.length_append,
          List.take_append_drop (sumNat v.content) t]
      rw [h1, htl, hsum] at hsplit
      refine ground.addCancelR (sumNat v.content) ?_
      rw [Nat.add_comm (List.drop (sumNat v.content) t).length,
        Nat.add_comm (sumNat w.content)]
      exact hsplit
    have hres := tensor_raise_split j v w hlen hsv hsw hv hw
      (List.take (sumNat v.content) t) (List.drop (sumNat v.content) t)
      h1 h2 (by rw [List.take_append_drop]; exact hmem)
    rw [List.take_append_drop] at hres
    exact hres
  · refine ground.foldB_null _ _ ?_
    intro m hm
    exact absurd
      ((units.length_unitAct_out (j + 1) j t m hm).symm.trans
        (hmem m hm).1) htl

private theorem seed_raiseNull (d j : Nat) :
    raiseNull j
      (⟨List.replicate d 0, [BPair.ofNat 1]⟩ : HVec) := by
  intro t hmem
  refine ground.foldB_null _ _ ?_
  intro m hm
  match hmem m hm with
  | ⟨hml, _⟩ =>
    have h0 : m.length = 0 := by
      rw [hml]
      show sumNat (List.replicate d 0) = 0
      exact sumNat_replicate_zero d
    have hlt : m.length = t.length :=
      units.length_unitAct_out (j + 1) j t m hm
    have ht0 : t = [] := by
      match t, hlt with
      | [], _ => rfl
      | _ :: _, hlt =>
        rw [h0] at hlt
        exact Nat.noConfusion hlt
    rw [ht0] at hm
    exact absurd hm (Nat.lt_irrefl 0)

private theorem exhibit_raiseNull_go (d j : Nat) (hj : j + 1 < d) :
    ∀ (ls : List Nat) (acc : HVec), acc.content.length = d →
      sized acc → raiseNull j acc →
      sized (ls.foldl (fun a l => tensorH a (wedge d l)) acc)
        ∧ (ls.foldl (fun a l => tensorH a (wedge d l))
            acc).content.length = d
        ∧ raiseNull j
            (ls.foldl (fun a l => tensorH a (wedge d l)) acc)
  | [], acc, hl, hs, hr => ⟨hs, hl, hr⟩
  | l :: ls, acc, hl, hs, hr => by
    refine exhibit_raiseNull_go d j hj ls (tensorH acc (wedge d l))
      ?_ (tensorH_sized acc (wedge d l)) ?_
    · show (List.zipWith (fun a b => a + b) acc.content
        (wedge d l).content).length = d
      exact ground.length_zipWith (fun x y => x + y) acc.content (wedge d l).content d hl
        (wedge_clen d l)
    · exact tensor_raiseNull j acc (wedge d l)
        (by rw [hl, wedge_clen d l]) hs (wedge_sized d l) hr
        (wedge_raiseNull d l j hj)

private theorem exhibit_raiseNull (s : Shape) (j : Nat)
    (hj : j + 1 < s.length) : raiseNull j (exhibit s) :=
  (exhibit_raiseNull_go s.length j hj (columnLengths s)
    ⟨List.replicate s.length 0, [BPair.ofNat 1]⟩
    (ground.length_replicate 0 s.length)
    (by
      show (1 : Nat)
        = (monomialsAt (List.replicate s.length 0)).length
      rw [places.monomialsAt_sum_zero _
        (sumNat_replicate_zero s.length)]
      rfl)
    (seed_raiseNull s.length j)).2.2

private theorem raiseNull_top (z : HVec) (j : Nat) (hsz : sized z)
    (hjr : j + 1 < z.content.length) (hr : raiseNull j z) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (units.moveUp j z.content) z.content j
        (j + 1)) z.coords) := by
  refine elim.unitTail_of_getAt _ ?_
  intro p hp
  rw [show (elim.matVec (units.matUnitAt
        (units.moveUp j z.content) z.content j (j + 1))
        z.coords).length
      = (monomialsAt (units.moveUp j z.content)).length from by
    rw [units.matVec_matUnitAt_length]] at hp
  by_cases hocc : 0 < ground.getAt 0 z.content (j + 1)
  · refine BPair.oneValue_trans
      (matVec_entry (units.moveUp j z.content) z.content j (j + 1)
        (raise_out_fwd z.content j hjr hocc) z.coords hsz p hp) ?_
    refine BPair.oneValue_trans
      (wSum_congr _ (fun s' => BPair.ofNat (ground.countOf s'
          (units.unitAct (j + 1) j
            (ground.getAt [] (monomialsAt
              (units.moveUp j z.content)) p))))
        (monomialsAt z.content) z.coords
        (fun s' _ => ground.BPair.oneValue_of_eq (congrArg BPair.ofNat
          (units.countOf_unitAct_swap j (j + 1) s' _)))) ?_
    have houts : ∀ m, 0 < ground.countOf m
        (units.unitAct (j + 1) j
          (ground.getAt [] (monomialsAt
            (units.moveUp j z.content)) p)) →
        m.length = sumNat z.content
          ∧ content z.content.length m = z.content :=
      fun m hm => raise_out_rev z.content j hjr hocc _ m
        (ground.countOf_getAt_pos []
          (monomialsAt (units.moveUp j z.content)) p hp) hm
    exact BPair.oneValue_trans
      (wSum_collect z.content z.coords hsz _ houts) (hr _ houts)
  · have hg0 : ground.getAt 0 z.content (j + 1) = 0 :=
      match Nat.eq_zero_or_pos
          (ground.getAt 0 z.content (j + 1)) with
      | .inl h => h
      | .inr h => absurd h hocc
    have hzero : ∀ s', 0 < ground.countOf s'
        (monomialsAt z.content) →
        ground.countOf (j + 1) s' = 0 := by
      intro s' hs'
      match member_conditions hs' with
      | ⟨_, hc⟩ =>
        rw [← getAt_contentAt z.content.length s' (j + 1) hjr,
          hc, hg0]
    have hout : ∀ s' m : List Nat,
        0 < ground.countOf s' (monomialsAt z.content) →
        0 < ground.countOf m (units.unitAct j (j + 1) s') →
        m.length = sumNat (units.moveUp j z.content)
          ∧ content (units.moveUp j z.content).length m
            = units.moveUp j z.content := by
      intro s' m hs' hm
      rw [units.unitAct_nil_of_zero j (j + 1) s'
        (hzero s' hs')] at hm
      exact absurd hm (Nat.lt_irrefl 0)
    refine BPair.oneValue_trans
      (matVec_entry (units.moveUp j z.content) z.content j (j + 1)
        hout z.coords hsz p hp) ?_
    refine wSum_null _ _ _ ?_
    intro s' hs'
    rw [units.unitAct_nil_of_zero j (j + 1) s' (hzero s' hs')]
    exact BPair.oneValue_refl _

/-- The exhibit is a top at the adjacent raisings: the raised
image's every coordinate reads the sum's unit, the wedge's repeat
read (`lem:tops`(iii) at `def:blockcount`'s carrier). -/
theorem exhibit_top (s : Shape) (j : Nat) (hj : j + 1 < s.length) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (units.moveUp j (rowList s)) (rowList s)
        j (j + 1)) (exhibit s).coords) := by
  have hc : (exhibit s).content = rowList s := content_exhibit s
  have h := raiseNull_top (exhibit s) j (exhibit_sized s)
    (by rw [hc, places.length_rowList]; exact hj)
    (exhibit_raiseNull s j hj)
  rw [hc] at h
  exact h

/-! The span's closure (`lem:lowerspan`'s word induction): the
unit's action at every distinct letter pair keeps the span — the
adjacent raisings by the induction along the pool's growth, seeded
at the exhibit's top read and stepped through the commutator
table's matrix tier, the further pairs by the gap descent at the
crossed composites — stated at the span's semantic reads and
instantiated by their proof at the measure. -/

/-- The letter-pair move at a stated ordered pair: the count at
the first letter raised by one, at the second lowered by one
(`con:units`' content move at the general pair). -/
def moveAt (i j : Nat) (mu : List Nat) : List Nat :=
  bumpAt i (dipAt j mu)

/-- The unit's action on a homogeneous vector: the letter-pair
move on the content with the matrix action on the coordinates
(`con:units` at `def:blockcount`'s carrier). -/
def act (i j : Nat) (v : HVec) : HVec :=
  let mu := moveAt i j v.content
  ⟨mu, elim.matVec (units.matUnitAt mu v.content i j) v.coords⟩

/-! The move's positional kit: the entry reads at the two moved
letters and beyond them, the total kept at an occupied second
letter, the adjacent instances against `con:units`' own moves, and
the round trips. -/

/-- The move's length read at the letter pair. -/
theorem length_moveAt (i j : Nat) (mu : List Nat) :
    (moveAt i j mu).length = mu.length := by
  show (bumpAt i (dipAt j mu)).length = mu.length
  rw [length_bumpAt, length_dipAt]

/-- The move's entry at the raised letter. -/
theorem getAt_moveAt_fst (i j : Nat) (mu : List Nat)
    (hij : ¬ i = j) (hi : i < mu.length) :
    ground.getAt 0 (moveAt i j mu) i
      = ground.getAt 0 mu i + 1 := by
  show ground.getAt 0 (bumpAt i (dipAt j mu)) i = _
  rw [getAt_bumpAt_self i (dipAt j mu)
      (by rw [length_dipAt]; exact hi),
    getAt_dipAt_ne j mu i hij]

/-- The move's entry at the lowered letter, occupied before the
move. -/
theorem getAt_moveAt_snd (i j : Nat) (mu : List Nat)
    (hij : ¬ i = j) (hocc : 0 < ground.getAt 0 mu j) :
    ground.getAt 0 (moveAt i j mu) j + 1
      = ground.getAt 0 mu j := by
  show ground.getAt 0 (bumpAt i (dipAt j mu)) j + 1 = _
  rw [getAt_bumpAt_ne i (dipAt j mu) j (fun he => hij he.symm),
    getAt_dipAt_self j mu hocc]

/-- The move's entry off both letters, the content's own. -/
theorem getAt_moveAt_ne (i j : Nat) (mu : List Nat)
    (x : Nat) (hxi : ¬ x = i) (hxj : ¬ x = j) :
    ground.getAt 0 (moveAt i j mu) x = ground.getAt 0 mu x := by
  show ground.getAt 0 (bumpAt i (dipAt j mu)) x = _
  rw [getAt_bumpAt_ne i (dipAt j mu) x hxi,
    getAt_dipAt_ne j mu x hxj]

theorem sumNat_moveAt (i j : Nat) (mu : List Nat)
    (hi : i < mu.length) (hocc : 0 < ground.getAt 0 mu j) :
    sumNat (moveAt i j mu) = sumNat mu :=
  ground.sumNat_move j i mu hocc hi

/-- The move at a lowered key below the raised one drops the
prefix through the lowered key by the one box, the raise sitting
beyond the read. -/
theorem prefixAt_moveAt (i j : Nat) (mu : List Nat) (hij : i < j)
    (hocc : 0 < ground.getAt 0 mu i) :
    ground.prefixAt (i + 1) (moveAt j i mu) + 1
      = ground.prefixAt (i + 1) mu := by
  show ground.prefixAt (i + 1)
      (ground.bumpAt j (ground.dipAt i mu)) + 1 = _
  rw [ground.prefixAt_bumpAt j (ground.dipAt i mu) (i + 1) hij,
    ground.prefixAt_dipAt i mu hocc]

/-- Two letter-pair moves commute off both crossed letters. -/
theorem moveAt_comm (i j a b : Nat) (mu : List Nat)
    (h1 : ¬ i = b) (h2 : ¬ a = j) :
    moveAt i j (moveAt a b mu) = moveAt a b (moveAt i j mu) := by
  show bumpAt i (dipAt j (bumpAt a (dipAt b mu)))
    = bumpAt a (dipAt b (bumpAt i (dipAt j mu)))
  rw [← bumpAt_dipAt_ne a j (dipAt b mu) (fun he => h2 he),
    bumpAt_comm i a (dipAt j (dipAt b mu)), dipAt_comm j b mu,
    bumpAt_dipAt_ne i b (dipAt j mu) h1]

/-- The positional bridge: the adjacent lowering is the letter
pair's own move at the successor against the letter. -/
theorem moveAt_moveDn : ∀ (j : Nat) (mu : List Nat),
    moveAt (j + 1) j mu = units.moveDn j mu
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | j + 1, a :: t => by
    show a :: bumpAt (j + 1) (dipAt j t) = a :: units.moveDn j t
    rw [show bumpAt (j + 1) (dipAt j t)
        = moveAt (j + 1) j t from rfl, moveAt_moveDn j t]

/-- The adjacent letter-pair move is the raising's own: `moveAt` at
a consecutive pair reads `moveUp`. -/
theorem moveAt_moveUp : ∀ (j : Nat) (mu : List Nat),
    moveAt j (j + 1) mu = units.moveUp j mu
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | j + 1, a :: t => by
    show a :: bumpAt j (dipAt (j + 1) t) = a :: units.moveUp j t
    rw [show bumpAt j (dipAt (j + 1) t)
        = moveAt j (j + 1) t from rfl, moveAt_moveUp j t]

/-- The wedge is a top at the adjacent raisings: the raised
image's every coordinate reads the sum's unit, the repeat's
transposition joining the two outputs at opposite gradings
(`lem:tops`(iii) at the column's own factor). -/
theorem wedge_top (d l j : Nat) (hj : j + 1 < d) :
    poly.unitTail (act j (j + 1) (wedge d l)).coords := by
  show poly.unitTail (elim.matVec (units.matUnitAt
    (moveAt j (j + 1) (wedge d l).content) (wedge d l).content
    j (j + 1)) (wedge d l).coords)
  rw [moveAt_moveUp j (wedge d l).content]
  exact raiseNull_top (wedge d l) j (wedge_sized d l)
    (by rw [wedge_clen d l]; exact hj) (wedge_raiseNull d l j hj)

/-- The letter-pair move's round trip at an occupied letter: the
moved content moves back to itself, at every pair. -/
theorem moveAt_round_at (i j : Nat) (mu : List Nat)
    (h : 0 < ground.getAt 0 mu i) :
    moveAt i j (moveAt j i mu) = mu := by
  show bumpAt i (dipAt j (bumpAt j (dipAt i mu))) = mu
  rw [ground.dipAt_bumpAt_self j (dipAt i mu), bumpAt_dipAt_self i mu h]

/-! The memberwise swap as the natural one's swapped scaling, and
the balance pair's cancellation — the crossed composites' reads,
the span transport itself landed at its owner
(`elim.span_map`, `elim.spanRel_congr`). -/

private theorem negMul (x : BPair) :
    ((BPair.ofNat 1).swap * x).oneValue x.swap := by
  rw [BPair.mul_comm, BPair.mul_swap]
  exact ground.swap_congr (BPair.mul_ofNat_one x)

private theorem polyOne_scaleSwap : ∀ y : List BPair,
    poly.oneValue (elim.vecScale ((BPair.ofNat 1).swap) y)
      (y.map BPair.swap)
  | [] => trivial
  | a :: t => ⟨negMul a, polyOne_scaleSwap t⟩

private theorem addSwapCancel (a b : BPair) :
    (a + b + b.swap).oneValue a := by
  rw [BPair.add_assoc]
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl a) ?_) (BPair.add_unit a)
  rw [BPair.add_comm b b.swap]
  exact BPair.swap_add_null (BPair.oneValue_refl b)

private theorem vecAddCancel : ∀ a b : List BPair,
    a.length = b.length →
    poly.oneValue
      (elim.vecAdd (elim.vecAdd a b)
        (elim.vecScale ((BPair.ofNat 1).swap) b)) a
  | [], [], _ => trivial
  | [], _ :: t, h => nomatch (show 0 = Nat.succ t.length from h)
  | _ :: t, [], h => nomatch (show Nat.succ t.length = 0 from h)
  | a :: u, b :: w, h => by
    refine ⟨?_, vecAddCancel u w (Nat.succ.inj h)⟩
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (a + b)) (negMul b))
      (addSwapCancel a b)


/-! The action's reads at the pool: the vector's fields determine
it, a settled vector sits in its group's span, a group row is a
member's own, and the unoccupied source letter's image is the sum's
unit at every target content. -/

private theorem hvec_eq {a b : HVec} (hc : a.content = b.content)
    (hx : a.coords = b.coords) : a = b := by
  match a, b with
  | ⟨c1, x1⟩, ⟨c2, x2⟩ =>
    show HVec.mk c1 x1 = HVec.mk c2 x2
    rw [show c1 = c2 from hc, show x1 = x2 from hx]

/-- The settled read is the span's: a settled vector sits in its
content group's span, the unit-tail disjunct through the vacant
combination (`elim.spanRel_null`). -/
theorem settled_to_span (pool : List HVec) (w : HVec)
    (hall : ∀ v ∈ pool, sized v) (hsz : sized w)
    (h : settledAt pool w) :
    elim.spanRel w.coords.length (groupAt pool w.content)
      w.coords :=
  match h with
  | Or.inl hu =>
    elim.spanRel_null _ _ _ (unitTail_of_allU w.coords hu)
      (by rw [hsz]; exact rowsLen_groupAt w.content pool hall) rfl
  | Or.inr hs => hs

/-- Every listed row of a group is some pool member's coordinate
family at that content, the family predicate along. -/
theorem groupAt_rows (P : HVec → Prop) :
    ∀ (pool : List HVec), (∀ v ∈ pool, P v) →
      ∀ (mu : List Nat) (k : Nat),
        k < (groupAt pool mu).length →
        ∃ v : HVec, P v ∧ v.content = mu
          ∧ ground.getAt ([] : List BPair) (groupAt pool mu) k
            = v.coords
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | v :: t, hp, mu, k, hk => by
    have hg : groupAt (v :: t) mu
        = match v.content == mu with
          | true => v.coords :: groupAt t mu
          | false => groupAt t mu := groupAt_cons v t mu
    cases hb : v.content == mu with
    | true =>
      rw [hb] at hg
      match k with
      | 0 =>
        refine ⟨v, memAll_head hp, ground.listBeqEq hb, ?_⟩
        rw [hg]
        rfl
      | k' + 1 =>
        rw [hg] at hk ⊢
        exact groupAt_rows P t (memAll_tail hp) mu k'
          (Nat.lt_of_succ_lt_succ hk)
    | false =>
      rw [hb] at hg
      rw [hg] at hk ⊢
      exact groupAt_rows P t (memAll_tail hp) mu k hk

/-- A pool member is settled at its own pool: its content group
lists its coordinates, the one-member combination's read
(`lem:lowerspan`'s listed row inside its list's span). -/
theorem member_settled :
    ∀ (pool : List HVec), (∀ x ∈ pool, sized x) →
    ∀ v ∈ pool, settledAt pool v
  | [], _, _, hv => nomatch hv
  | v :: t, hall, q, hq => by
    match q, hq with
    | _, List.Mem.head _ =>
      refine Or.inr ?_
      have hg : groupAt (v :: t) v.content
          = v.coords :: groupAt t v.content := by
        rw [groupAt_cons v t v.content,
          ground.listEqBeq v.content]
      have hL : elim.rowsLen v.coords.length
          (groupAt (v :: t) v.content) := by
        have h := rowsLen_groupAt v.content (v :: t) hall
        rw [← hall v (List.Mem.head t)] at h
        exact h
      have hk : 0 < (groupAt (v :: t) v.content).length := by
        rw [hg]
        exact Nat.succ_pos _
      have h2 := elim.spanRel_getAt v.coords.length
        (groupAt (v :: t) v.content) 0 hk hL
      rw [show ground.getAt ([] : List BPair)
          (groupAt (v :: t) v.content) 0 = v.coords from by
        rw [hg]
        rfl] at h2
      exact h2
    | q', List.Mem.tail _ hqt =>
      match member_settled t (memAll_tail hall) q' hqt with
      | Or.inl hu => exact Or.inl hu
      | Or.inr hs =>
        refine Or.inr ?_
        rw [groupAt_cons v t q'.content]
        cases hb : v.content == q'.content with
        | true =>
          have hvlen : v.coords.length = q'.coords.length := by
            rw [hall v (List.Mem.head t),
              hall q' (List.Mem.tail v hqt), ground.listBeqEq hb]
          show elim.spanRel q'.coords.length
            ([v.coords] ++ groupAt t q'.content) q'.coords
          refine elim.spanRel_mono_left q'.coords.length
            [v.coords] (groupAt t q'.content) q'.coords
            ⟨hvlen, True.intro⟩ ?_ hs
          rw [hall q' (List.Mem.tail v hqt)]
          exact rowsLen_groupAt q'.content t (memAll_tail hall)
        | false => exact hs

/-- The action's outputs at a distinct letter pair sit at the moved
content, the output kit's per-letter reads assembled positionwise —
the matrix tier's content hypotheses at the letter-pair move. -/
theorem out_gen (mu : List Nat) (i j : Nat)
    (hi : i < mu.length) (hij : ¬ i = j) :
    ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (units.unitAct i j s) →
      m.length = sumNat (moveAt i j mu)
        ∧ content (moveAt i j mu).length m = moveAt i j mu := by
  intro s m hs hm
  have hd : (moveAt i j mu).length = mu.length :=
    length_moveAt i j mu
  match member_conditions hs with
  | ⟨hsl, hsc⟩ =>
    have hjs : 0 < ground.countOf j s := by
      match Nat.eq_zero_or_pos (ground.countOf j s) with
      | .inl hzz =>
        rw [units.unitAct_nil_of_zero i j s hzz] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      | .inr hpp => exact hpp
    have hjd : j < mu.length := by
      by_cases hj : j < mu.length
      · exact hj
      · exact absurd
          (mem_lt_of_content mu.length s (by rw [hsc, hsl]) j hjs)
          hj
    have hocc : 0 < ground.getAt 0 mu j := by
      rw [← getAt_contentAt mu.length s j hjd, hsc] at hjs
      exact hjs
    refine ⟨?_, ?_⟩
    · rw [units.length_unitAct_out i j s m hm, hsl,
        sumNat_moveAt i j mu hi hocc]
    · rw [hd]
      refine content_eq_of_entries mu.length m
        (moveAt i j mu) hd ?_
      intro x hx
      have hcnt := units.countOf_unitAct_out i j x s m hm
      have hsx : ground.countOf x s = ground.getAt 0 mu x := by
        rw [← getAt_contentAt mu.length s x hx, hsc]
      rw [hsx] at hcnt
      by_cases hxi : x = i
      · rw [hxi] at hcnt ⊢
        rw [if_neg hij, if_pos rfl, Nat.add_zero] at hcnt
        rw [hcnt, getAt_moveAt_fst i j mu hij hi]
      · by_cases hxj : x = j
        · rw [hxj] at hcnt ⊢
          rw [if_pos rfl, if_neg (fun he => hij he.symm)] at hcnt
          refine ground.addCancelR 1 ?_
          rw [hcnt, getAt_moveAt_snd i j mu hij hocc, Nat.add_zero]
        · rw [if_neg hxj, if_neg hxi, Nat.add_zero,
            Nat.add_zero] at hcnt
          rw [hcnt, getAt_moveAt_ne i j mu x hxi hxj]

/-- The letter-pair action's image is sized: the width is the
moved content's enumeration. -/
theorem act_sized (i j : Nat) (v : HVec) :
    sized (act i j v) := by
  show (elim.matVec (units.matUnitAt (moveAt i j v.content)
      v.content i j) v.coords).length
    = (monomialsAt (moveAt i j v.content)).length
  rw [units.matVec_matUnitAt_length]

/-- The pairing walks across the transpose partner at the letter
pair: the moved image pairs a stated vector as the vector pairs
the transposed image, `con:units`' transpose read at the unit
matrices. -/
theorem unit_adjoint (i j : Nat) (mu : List Nat)
    (hi : i < mu.length) (hj : j < mu.length) (hij : ¬ i = j)
    (hjocc : 0 < ground.getAt 0 mu j)
    (w r : List BPair)
    (hw : w.length = (places.monomialsAt mu).length)
    (hr : r.length
      = (places.monomialsAt (moveAt i j mu)).length) :
    (elim.dotP
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) w)
      r).oneValue
    (elim.dotP w
      (elim.matVec (units.matUnitAt mu (moveAt i j mu) j i)
        r)) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hjm : j < (moveAt i j mu).length := by
    rw [length_moveAt]
    exact hj
  have hout2 : ∀ s m : List Nat,
      0 < ground.countOf s
        (places.monomialsAt (moveAt i j mu)) →
      0 < ground.countOf m (units.unitAct j i s) →
      m.length = sumNat mu ∧ content mu.length m = mu := by
    have h := out_gen (moveAt i j mu) j i hjm hji
    rw [moveAt_round_at j i mu hjocc] at h
    exact h
  refine BPair.oneValue_trans
    (elim.dotP_matVec_transpose (places.monomialsAt mu).length
      (units.matUnitAt (moveAt i j mu) mu i j) w r
      (units.rowsLen_matUnitAt _ _ i j) hw
      (by rw [hr, units.length_matUnitAt])) ?_
  exact elim.dotP_oneValue_right w _ _
    (elim.matVec_matOne _ _ _
      (units.matUnit_transpose_read (moveAt i j mu) mu i j
        (out_gen mu i j hi hij) hout2))

/-- The action's span transport: at a pool whose members' images
are settled, a group's span member maps into the moved group's
span. -/
theorem act_transport (pool : List HVec) (i j : Nat)
    (hall : ∀ v ∈ pool, sized v)
    (himg : ∀ v ∈ pool, settledAt pool (act i j v))
    (mu : List Nat) (x : List BPair)
    (hx : x.length = (monomialsAt mu).length)
    (hsp : elim.spanRel (monomialsAt mu).length
      (groupAt pool mu) x) :
    elim.spanRel (monomialsAt (moveAt i j mu)).length
      (groupAt pool (moveAt i j mu))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        x) := by
  have hTlen : (units.matUnitAt (moveAt i j mu) mu i j).length
      = (monomialsAt (moveAt i j mu)).length :=
    units.length_matUnitAt _ _ i j
  have hM : elim.rowsLen
      (units.matUnitAt (moveAt i j mu) mu i j).length
      (groupAt pool (moveAt i j mu)) := by
    rw [hTlen]
    exact rowsLen_groupAt (moveAt i j mu) pool hall
  have himg' : ∀ k, k < (groupAt pool mu).length →
      elim.spanRel (units.matUnitAt (moveAt i j mu) mu i j).length
        (groupAt pool (moveAt i j mu))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (ground.getAt [] (groupAt pool mu) k)) := by
    intro k hk
    match groupAt_rows
        (fun v => settledAt pool (act i j v) ∧ sized v) pool
        (fun v hv => ⟨himg v hv, hall v hv⟩) mu k hk with
    | ⟨v, ⟨hset, _⟩, hc, hrow⟩ =>
      have h2 := settled_to_span pool (act i j v) hall
        (act_sized i j v) hset
      have hcc : (act i j v).content = moveAt i j mu := by
        show moveAt i j v.content = moveAt i j mu
        rw [hc]
      have hxx : (act i j v).coords
          = elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
            (ground.getAt [] (groupAt pool mu) k) := by
        show elim.matVec (units.matUnitAt
          (moveAt i j v.content) v.content i j) v.coords = _
        rw [hc, hrow]
      rw [hcc, hxx, elim.matVec_length] at h2
      exact h2
  have hres := elim.span_map (units.matUnitAt (moveAt i j mu) mu i j)
    (monomialsAt mu).length
    (groupAt pool mu) (groupAt pool (moveAt i j mu))
    (rowsLen_groupAt mu pool hall) hM himg' x hx hsp
  rw [hTlen] at hres
  exact hres

/-- The pool's adjacent lowerings as the general action: the
closure read at a letter pair, the unoccupied source letter's
image the sum's unit. -/
private theorem lower_imgs (pool : List HVec) (d j : Nat)
    (hcl : closedAt pool d) (hall : ∀ v ∈ pool, sized v)
    (hj : j + 1 < d) :
    ∀ v ∈ pool, settledAt pool (act (j + 1) j v) := by
  intro v hvm
  have hv : (∀ j w, j < d - 1 → lowerH j v = some w →
      settledAt pool w) ∧ sized v :=
    ⟨closedAt_elim hcl v hvm, hall v hvm⟩
  by_cases hg : 0 < ground.getAt 0 v.content j
  · have hlw : lowerH j v
        = some ⟨units.moveDn j v.content,
            elim.matVec (units.matUnitAt (units.moveDn j v.content)
              v.content (j + 1) j) v.coords⟩ := if_pos hg
    have hset := hv.1 j _ (Nat.le_pred_of_lt hj) hlw
    have hact : act (j + 1) j v
        = ⟨units.moveDn j v.content,
            elim.matVec (units.matUnitAt (units.moveDn j v.content)
              v.content (j + 1) j) v.coords⟩ := by
      refine hvec_eq ?_ ?_
      · show moveAt (j + 1) j v.content = units.moveDn j v.content
        exact moveAt_moveDn j v.content
      · show elim.matVec (units.matUnitAt
          (moveAt (j + 1) j v.content) v.content (j + 1) j)
            v.coords
          = elim.matVec (units.matUnitAt
            (units.moveDn j v.content) v.content (j + 1) j)
            v.coords
        rw [moveAt_moveDn j v.content]
    rw [hact]
    exact hset
  · have hz : ground.getAt 0 v.content j = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 v.content j) with
      | .inl h => h
      | .inr h => absurd h hg
    refine Or.inl (allU_of_unitTail _ ?_)
    show poly.unitTail (elim.matVec (units.matUnitAt
      (moveAt (j + 1) j v.content) v.content (j + 1) j) v.coords)
    exact units.matVec_null_unocc _ v.content (j + 1) j hz v.coords


/-! The adjacent raisings' closure (`lem:lowerspan`'s word
induction along the pool's growth): the exhibit's top read seeds
the invariant, and at each occupied lowering the commutator
table's matrix tier steps it — the letter's own pair through the
crossed diagonal scalars, the further pairs through the disjoint
units' exchange. -/

private theorem settled_of_span (pool : List HVec) (w : HVec)
    (hsz : sized w)
    (h : elim.spanRel (monomialsAt w.content).length
      (groupAt pool w.content) w.coords) : settledAt pool w := by
  refine Or.inr ?_
  rw [hsz]
  exact h

theorem span_of_settled (pool : List HVec) (w : HVec)
    (hall : ∀ v ∈ pool, sized v) (hsz : sized w)
    (h : settledAt pool w) :
    elim.spanRel (monomialsAt w.content).length
      (groupAt pool w.content) w.coords := by
  have h2 := settled_to_span pool w hall hsz h
  rw [hsz] at h2
  exact h2

/-- The crossed composite's span read: at the pin's exchange the
raised lowering sits in the source group's span, the diagonal
scalars entering at the scaled member and the swapped clearing. -/
private theorem raise_pair_gen (pool : List HVec)
    (mu muB : List Nat) (j : Nat) (x : List BPair)
    (hx : x.length = (monomialsAt mu).length)
    (hG : elim.rowsLen (monomialsAt mu).length (groupAt pool mu))
    (hsp : elim.spanRel (monomialsAt mu).length
      (groupAt pool mu) x)
    (hB : elim.spanRel (monomialsAt mu).length (groupAt pool mu)
      (elim.matVec (units.matUnitAt mu muB (j + 1) j)
        (elim.matVec (units.matUnitAt muB mu j (j + 1)) x)))
    (hpin : poly.oneValue
      (elim.vecAdd
        (elim.matVec
          (units.matUnitAt mu (moveAt (j + 1) j mu) j (j + 1))
          (elim.matVec
            (units.matUnitAt (moveAt (j + 1) j mu) mu (j + 1) j) x))
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 mu (j + 1))) x))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt mu muB (j + 1) j)
          (elim.matVec (units.matUnitAt muB mu j (j + 1)) x))
        (elim.vecScale (BPair.ofNat (ground.getAt 0 mu j)) x))) :
    elim.spanRel (monomialsAt mu).length (groupAt pool mu)
      (elim.matVec
        (units.matUnitAt mu (moveAt (j + 1) j mu) j (j + 1))
        (elim.matVec
          (units.matUnitAt (moveAt (j + 1) j mu) mu (j + 1) j)
          x)) := by
  have hlenA : (elim.matVec
      (units.matUnitAt mu (moveAt (j + 1) j mu) j (j + 1))
      (elim.matVec
        (units.matUnitAt (moveAt (j + 1) j mu) mu (j + 1) j) x)).length
      = (monomialsAt mu).length := by
    rw [units.matVec_matUnitAt_length]
  have hlenB : (elim.matVec (units.matUnitAt mu muB (j + 1) j)
      (elim.matVec (units.matUnitAt muB mu j (j + 1)) x)).length
      = (monomialsAt mu).length := by
    rw [units.matVec_matUnitAt_length]
  have hlenS : ∀ c : BPair, (elim.vecScale c x).length
      = (monomialsAt mu).length :=
    fun c => (elim.length_vecScale c x).trans hx
  have hRHS := elim.spanRel_add (monomialsAt mu).length
    (groupAt pool mu) _ _ hG hlenB
    (hlenS (BPair.ofNat (ground.getAt 0 mu j))) hB
    (elim.spanRel_scale (monomialsAt mu).length (groupAt pool mu)
      x (BPair.ofNat (ground.getAt 0 mu j)) hG hx hsp)
  have hLHS := elim.spanRel_congr (monomialsAt mu).length
    (groupAt pool mu) _ _ (poly.oneValue_symm hpin) hRHS
    (elim.length_vecAdd _ _ _ hlenA
      (hlenS (BPair.ofNat (ground.getAt 0 mu (j + 1)))))
  have hD : elim.spanRel (monomialsAt mu).length (groupAt pool mu)
      (elim.vecScale ((BPair.ofNat 1).swap)
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 mu (j + 1))) x)) := by
    rw [elim.vecScale_vecScale]
    exact elim.spanRel_scale (monomialsAt mu).length
      (groupAt pool mu) x _ hG hx hsp
  have hsum := elim.spanRel_add (monomialsAt mu).length
    (groupAt pool mu) _ _ hG
    (elim.length_vecAdd _ _ _ hlenA
      (hlenS (BPair.ofNat (ground.getAt 0 mu (j + 1)))))
    ((elim.length_vecScale _ _).trans
      (hlenS (BPair.ofNat (ground.getAt 0 mu (j + 1)))))
    hLHS hD
  exact elim.spanRel_congr (monomialsAt mu).length (groupAt pool mu)
    _ _
    (vecAddCancel _ _
      (hlenA.trans
        (hlenS (BPair.ofNat (ground.getAt 0 mu (j + 1)))).symm))
    hsum hlenA

/-- The letter's own pair after its lowering: the raised image of
an occupied lowering is settled, the exchange's second composite
the vector's own raising (its target content unoccupied at the
raised letter, the composite the sum's unit). -/
private theorem raise_pair (pool : List HVec) (d j : Nat)
    (hall : ∀ x ∈ pool, sized x) (hcl : closedAt pool d)
    (hj : j + 1 < d) (v : HVec)
    (hlen : v.content.length = d) (hsz : sized v)
    (hset : settledAt pool v)
    (hrai : settledAt pool (act j (j + 1) v))
    (hocc : 0 < ground.getAt 0 v.content j) :
    settledAt pool (act j (j + 1) (act (j + 1) j v)) := by
  have hj1d : j + 1 < v.content.length := by
    rw [hlen]
    exact hj
  have hjd : j < v.content.length :=
    Nat.lt_trans (Nat.lt_succ_self j) hj1d
  have hjA : j < (moveAt (j + 1) j v.content).length := by
    rw [length_moveAt]
    exact hjd
  have hG : elim.rowsLen (monomialsAt v.content).length
      (groupAt pool v.content) := rowsLen_groupAt _ pool hall
  have hsp : elim.spanRel (monomialsAt v.content).length
      (groupAt pool v.content) v.coords :=
    span_of_settled pool v hall hsz hset
  have hDn := out_gen v.content (j + 1) j hj1d
    (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm)
  have hUp := out_gen (moveAt (j + 1) j v.content) j (j + 1) hjA
    (Nat.ne_of_lt (Nat.lt_succ_self j))
  rw [moveAt_round_at j (j + 1) v.content hocc] at hUp
  have hkey : elim.spanRel (monomialsAt v.content).length
      (groupAt pool v.content)
      (elim.matVec (units.matUnitAt v.content
          (moveAt (j + 1) j v.content) j (j + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (j + 1) j v.content) v.content (j + 1) j)
          v.coords)) := by
    by_cases hocc2 : 0 < ground.getAt 0 v.content (j + 1)
    · have hUp' := out_gen v.content j (j + 1) hjd
        (Nat.ne_of_lt (Nat.lt_succ_self j))
      have hjB : j + 1 < (moveAt j (j + 1) v.content).length := by
        rw [length_moveAt]
        exact hj1d
      have hDn' := out_gen (moveAt j (j + 1) v.content) (j + 1) j
        hjB (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm)
      rw [moveAt_round_at (j + 1) j v.content hocc2] at hDn'
      have hinner : elim.spanRel
          (monomialsAt (moveAt j (j + 1) v.content)).length
          (groupAt pool (moveAt j (j + 1) v.content))
          (elim.matVec (units.matUnitAt
            (moveAt j (j + 1) v.content) v.content j (j + 1))
            v.coords) :=
        span_of_settled pool (act j (j + 1) v) hall
          (act_sized j (j + 1) v) hrai
      have hB := act_transport pool (j + 1) j hall
        (lower_imgs pool d j hcl hall hj)
        (moveAt j (j + 1) v.content) _
        (act_sized j (j + 1) v) hinner
      rw [moveAt_round_at (j + 1) j v.content hocc2] at hB
      exact raise_pair_gen pool v.content
        (moveAt j (j + 1) v.content) j v.coords hsz hG hsp hB
        (units.matVec_pair_read v.content
          (moveAt (j + 1) j v.content)
          (moveAt j (j + 1) v.content) j hDn hUp hUp' hDn'
          v.coords hsz)
    · have hz1 : ground.getAt 0 v.content (j + 1) = 0 :=
        match Nat.eq_zero_or_pos
            (ground.getAt 0 v.content (j + 1)) with
        | .inl h => h
        | .inr h => absurd h hocc2
      have hUp' : ∀ s m : List Nat,
          0 < ground.countOf s (monomialsAt v.content) →
          0 < ground.countOf m (units.unitAct j (j + 1) s) →
          m.length = sumNat (List.replicate v.content.length 0)
            ∧ content
              (List.replicate v.content.length 0).length m
              = List.replicate v.content.length 0 := by
        intro s m hs hm
        rw [units.unitAct_nil_of_zero j (j + 1) s
          (letter_zero v.content (j + 1) hz1 s hs)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      have hDn' : ∀ s m : List Nat,
          0 < ground.countOf s
            (monomialsAt (List.replicate v.content.length 0)) →
          0 < ground.countOf m (units.unitAct (j + 1) j s) →
          m.length = sumNat v.content
            ∧ content v.content.length m = v.content :=
        fun s m hs hm =>
          (units.no_out_zero v.content.length (j + 1) j s m hs hm).elim
      have hB : elim.spanRel (monomialsAt v.content).length
          (groupAt pool v.content)
          (elim.matVec (units.matUnitAt v.content
              (List.replicate v.content.length 0) (j + 1) j)
            (elim.matVec (units.matUnitAt
              (List.replicate v.content.length 0) v.content
              j (j + 1)) v.coords)) :=
        elim.spanRel_null _ _ _
          (elim.matVec_null _ _
            (units.matVec_null_unocc
              (List.replicate v.content.length 0) v.content
              j (j + 1) hz1 v.coords))
          hG
          (by rw [units.matVec_matUnitAt_length])
      exact raise_pair_gen pool v.content
        (List.replicate v.content.length 0) j v.coords hsz hG hsp
        hB
        (units.matVec_pair_read v.content
          (moveAt (j + 1) j v.content)
          (List.replicate v.content.length 0) j hDn hUp hUp' hDn'
          v.coords hsz)
  refine settled_of_span pool _
    (act_sized j (j + 1) (act (j + 1) j v)) ?_
  have hcontent : (act j (j + 1) (act (j + 1) j v)).content
      = v.content := by
    show moveAt j (j + 1) (moveAt (j + 1) j v.content) = v.content
    exact moveAt_round_at j (j + 1) v.content hocc
  have hcoords : (act j (j + 1) (act (j + 1) j v)).coords
      = elim.matVec (units.matUnitAt v.content
          (moveAt (j + 1) j v.content) j (j + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (j + 1) j v.content) v.content (j + 1) j)
          v.coords) := by
    show elim.matVec (units.matUnitAt
        (moveAt j (j + 1) (moveAt (j + 1) j v.content))
        (moveAt (j + 1) j v.content) j (j + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (j + 1) j v.content) v.content (j + 1) j)
          v.coords) = _
    rw [moveAt_round_at j (j + 1) v.content hocc]
  rw [hcontent, hcoords]
  exact hkey

/-- A further pair after a lowering: the disjoint units commute,
the exchange reading the vector's own further raising through the
lowering transport. -/
private theorem raise_cross (pool : List HVec) (d jr j : Nat)
    (hall : ∀ x ∈ pool, sized x) (hcl : closedAt pool d)
    (hj : j + 1 < d) (hjr : jr + 1 < d) (hne : ¬ jr = j)
    (v : HVec) (hlen : v.content.length = d) (hsz : sized v)
    (hrai : settledAt pool (act jr (jr + 1) v)) :
    settledAt pool (act jr (jr + 1) (act (j + 1) j v)) := by
  have hj1d : j + 1 < v.content.length := by
    rw [hlen]
    exact hj
  have hjr1d : jr + 1 < v.content.length := by
    rw [hlen]
    exact hjr
  have hjrd : jr < v.content.length :=
    Nat.lt_trans (Nat.lt_succ_self jr) hjr1d
  have hjrA : jr < (moveAt (j + 1) j v.content).length := by
    rw [length_moveAt]
    exact hjrd
  have hjB : j + 1 < (moveAt jr (jr + 1) v.content).length := by
    rw [length_moveAt]
    exact hj1d
  have hcomm : moveAt (j + 1) j (moveAt jr (jr + 1) v.content)
      = moveAt jr (jr + 1) (moveAt (j + 1) j v.content) :=
    moveAt_comm (j + 1) j jr (jr + 1) v.content
      (fun he => hne (Nat.succ.inj he).symm) hne
  have hCD := out_gen v.content (j + 1) j hj1d
    (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm)
  have hAB := out_gen (moveAt (j + 1) j v.content) jr (jr + 1)
    hjrA (Nat.ne_of_lt (Nat.lt_succ_self jr))
  have hAB' := out_gen v.content jr (jr + 1) hjrd
    (Nat.ne_of_lt (Nat.lt_succ_self jr))
  have hCD' := out_gen (moveAt jr (jr + 1) v.content) (j + 1) j
    hjB (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm)
  rw [hcomm] at hCD'
  have hpin := units.matVec_swap_read (moveAt (j + 1) j v.content)
    (moveAt jr (jr + 1) v.content)
    (moveAt jr (jr + 1) (moveAt (j + 1) j v.content))
    v.content jr (jr + 1) (j + 1) j hne
    (fun he => hne (Nat.succ.inj he).symm) hCD hAB hAB' hCD'
    v.coords hsz
  have hinner : elim.spanRel
      (monomialsAt (moveAt jr (jr + 1) v.content)).length
      (groupAt pool (moveAt jr (jr + 1) v.content))
      (elim.matVec (units.matUnitAt
        (moveAt jr (jr + 1) v.content) v.content jr (jr + 1))
        v.coords) :=
    span_of_settled pool (act jr (jr + 1) v) hall
      (act_sized jr (jr + 1) v) hrai
  have hB := act_transport pool (j + 1) j hall
    (lower_imgs pool d j hcl hall hj)
    (moveAt jr (jr + 1) v.content) _
    (act_sized jr (jr + 1) v) hinner
  rw [hcomm] at hB
  refine settled_of_span pool _
    (act_sized jr (jr + 1) (act (j + 1) j v)) ?_
  show elim.spanRel
    (monomialsAt (moveAt jr (jr + 1)
      (moveAt (j + 1) j v.content))).length
    (groupAt pool (moveAt jr (jr + 1)
      (moveAt (j + 1) j v.content)))
    (elim.matVec (units.matUnitAt
      (moveAt jr (jr + 1) (moveAt (j + 1) j v.content))
      (moveAt (j + 1) j v.content) jr (jr + 1))
      (elim.matVec (units.matUnitAt
        (moveAt (j + 1) j v.content) v.content (j + 1) j)
        v.coords))
  exact elim.spanRel_congr _ _ _ _ (poly.oneValue_symm hpin) hB
    (by rw [units.matVec_matUnitAt_length])

private def raiseQ (s : Shape) (v : HVec) : Prop :=
  v.content.length = s.length ∧ sized v
    ∧ settledAt (blockSpan s) v
    ∧ ∀ jr, jr + 1 < s.length →
        settledAt (blockSpan s) (act jr (jr + 1) v)

private theorem raise_seed (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v) :
    raiseQ s (exhibit s) := by
  refine ⟨?_, exhibit_sized s, ?_, ?_⟩
  · rw [content_exhibit s]
    exact places.length_rowList s
  · match blockSpan_prov s with
    | ⟨t, ht, _⟩ =>
      exact member_settled (blockSpan s) hall (exhibit s)
        (by rw [ht]; exact List.Mem.head t)
  · intro jr hjr
    refine Or.inl (allU_of_unitTail _ ?_)
    show poly.unitTail (elim.matVec (units.matUnitAt
      (moveAt jr (jr + 1) (exhibit s).content) (exhibit s).content
      jr (jr + 1)) (exhibit s).coords)
    rw [content_exhibit s, moveAt_moveUp jr (rowList s)]
    exact exhibit_top s jr hjr

private theorem raise_step (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length) :
    ∀ (v w : HVec) (j : Nat), j + 1 < s.length → raiseQ s v →
      lowerH j v = some w → raiseQ s w := by
  intro v w j hj hq hlw
  have hocc : 0 < ground.getAt 0 v.content j := by
    by_cases hg : 0 < ground.getAt 0 v.content j
    · exact hg
    · rw [show lowerH j v = none from if_neg hg] at hlw
      exact nomatch hlw
  have hfields := lowerH_fields hlw
  have hw : w = act (j + 1) j v := by
    refine hvec_eq ?_ ?_
    · show w.content = moveAt (j + 1) j v.content
      rw [moveAt_moveDn j v.content]
      exact hfields.1
    · show w.coords = elim.matVec (units.matUnitAt
        (moveAt (j + 1) j v.content) v.content (j + 1) j) v.coords
      rw [hfields.2]
      show elim.matVec (units.matUnitAt (units.moveDn j v.content)
          v.content (j + 1) j) v.coords
        = elim.matVec (units.matUnitAt (moveAt (j + 1) j v.content)
          v.content (j + 1) j) v.coords
      rw [moveAt_moveDn j v.content]
  rw [hw]
  refine ⟨?_, act_sized (j + 1) j v, ?_, ?_⟩
  · show (moveAt (j + 1) j v.content).length = s.length
    rw [length_moveAt]
    exact hq.1
  · refine settled_of_span (blockSpan s) _
      (act_sized (j + 1) j v) ?_
    exact act_transport (blockSpan s) (j + 1) j hall
      (lower_imgs (blockSpan s) s.length j hcl hall hj) v.content
      v.coords hq.2.1
      (span_of_settled (blockSpan s) v hall hq.2.1 hq.2.2.1)
  · intro jr hjr
    by_cases hje : jr = j
    · rw [hje]
      exact raise_pair (blockSpan s) s.length j hall hcl hj v
        hq.1 hq.2.1 hq.2.2.1 (by rw [← hje]; exact hq.2.2.2 jr hjr)
        hocc
    · exact raise_cross (blockSpan s) s.length jr j hall hcl hj
        hjr hje v hq.1 hq.2.1 (hq.2.2.2 jr hjr)

private theorem raise_all (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length) :
    ∀ v ∈ blockSpan s, raiseQ s v :=
  blockSpan_all s (raiseQ s) (raise_seed s hall)
    (raise_step s hall hcl)

/-- The adjacent raisings' closure: at the span's semantic reads
every member's adjacent raising is settled. -/
private theorem act_adj_raise (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length)
    (jr : Nat) (hjr : jr + 1 < s.length) :
    ∀ v ∈ blockSpan s, settledAt (blockSpan s) (act jr (jr + 1) v) :=
  fun v hv => (raise_all s hall hcl v hv).2.2.2 jr hjr


/-! The further pairs' closure (the gap descent): the single unit
is the crossed composites' join at an interior letter
(`units.matVec_comm_read`), each composite's inner action settled
at the shorter gap and its outer action transported by the same
read — the descent stepping one letter per round from the adjacent
pairs. -/

/-- The moves chain at a shared middle letter, the raise
cancelling the lowering there. -/
theorem moveAt_chain (i k j : Nat) (mu : List Nat) :
    moveAt i k (moveAt k j mu) = moveAt i j mu := by
  show bumpAt i (dipAt k (bumpAt k (dipAt j mu)))
    = bumpAt i (dipAt j mu)
  rw [ground.dipAt_bumpAt_self k (dipAt j mu)]

/-- The moves chain in the second order at an occupied middle
letter. -/
theorem moveAt_chain' (i k j : Nat) (mu : List Nat)
    (hij : ¬ i = j) (hkj : ¬ k = j)
    (hk : 0 < ground.getAt 0 mu k) :
    moveAt k j (moveAt i k mu) = moveAt i j mu := by
  have hk' : 0 < ground.getAt 0 (dipAt j mu) k := by
    rw [getAt_dipAt_ne j mu k hkj]
    exact hk
  show bumpAt k (dipAt j (bumpAt i (dipAt k mu)))
    = bumpAt i (dipAt j mu)
  rw [← bumpAt_dipAt_ne i j (dipAt k mu) hij,
    bumpAt_comm k i (dipAt j (dipAt k mu)), dipAt_comm j k mu,
    bumpAt_dipAt_self k (dipAt j mu) hk']

private theorem spanRel_swapMap (n : Nat) (L : elim.Mat)
    (y : List BPair) (hL : elim.rowsLen n L) (hy : y.length = n)
    (h : elim.spanRel n L y) :
    elim.spanRel n L (y.map BPair.swap) :=
  elim.spanRel_congr n L _ _ (polyOne_scaleSwap y)
    (elim.spanRel_scale n L y ((BPair.ofNat 1).swap) hL hy h)
    ((ground.length_map _ y).trans hy)

private theorem act_split_gen (pool : List HVec)
    (mu muMidB : List Nat) (i k j : Nat) (x : List BPair)
    (hG : elim.rowsLen (monomialsAt (moveAt i j mu)).length
      (groupAt pool (moveAt i j mu)))
    (hT1 : elim.spanRel (monomialsAt (moveAt i j mu)).length
      (groupAt pool (moveAt i j mu))
      (elim.matVec
        (units.matUnitAt (moveAt i j mu) (moveAt k j mu) i k)
        (elim.matVec (units.matUnitAt (moveAt k j mu) mu k j) x)))
    (hT2 : elim.spanRel (monomialsAt (moveAt i j mu)).length
      (groupAt pool (moveAt i j mu))
      (elim.matVec (units.matUnitAt (moveAt i j mu) muMidB k j)
        (elim.matVec (units.matUnitAt muMidB mu i k) x)))
    (hpin : poly.oneValue
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x)
      (elim.vecAdd
        (elim.matVec
          (units.matUnitAt (moveAt i j mu) (moveAt k j mu) i k)
          (elim.matVec (units.matUnitAt (moveAt k j mu) mu k j) x))
        ((elim.matVec (units.matUnitAt (moveAt i j mu) muMidB k j)
          (elim.matVec (units.matUnitAt muMidB mu i k) x)).map
          BPair.swap))) :
    elim.spanRel (monomialsAt (moveAt i j mu)).length
      (groupAt pool (moveAt i j mu))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x) := by
  have hl1 : (elim.matVec
      (units.matUnitAt (moveAt i j mu) (moveAt k j mu) i k)
      (elim.matVec (units.matUnitAt (moveAt k j mu) mu k j)
        x)).length = (monomialsAt (moveAt i j mu)).length := by
    rw [units.matVec_matUnitAt_length]
  have hl2 : (elim.matVec
      (units.matUnitAt (moveAt i j mu) muMidB k j)
      (elim.matVec (units.matUnitAt muMidB mu i k) x)).length
      = (monomialsAt (moveAt i j mu)).length := by
    rw [units.matVec_matUnitAt_length]
  refine elim.spanRel_congr _ _ _ _ (poly.oneValue_symm hpin) ?_
    (by rw [units.matVec_matUnitAt_length])
  exact elim.spanRel_add _ _ _ _ hG hl1
    ((ground.length_map _ _).trans hl2) hT1
    (spanRel_swapMap _ _ _ hG hl2 hT2)

/-- The gap's descent step (`lem:lowerspan`'s descent clause: a
pair at a gap beyond one is the crossed composite at an interior
letter): at an interior letter distinct from both ends the pair's
action is settled once the two shorter pairs' are. -/
private theorem act_split (pool : List HVec) (d i k j : Nat)
    (hall : ∀ v ∈ pool, sized v)
    (hlens : ∀ v ∈ pool, v.content.length = d)
    (hi : i < d) (hk : k < d) (hij : ¬ i = j) (hik : ¬ i = k)
    (hkj : ¬ k = j)
    (h1 : ∀ v ∈ pool, settledAt pool (act i k v))
    (h2 : ∀ v ∈ pool, settledAt pool (act k j v)) :
    ∀ v ∈ pool, settledAt pool (act i j v) := by
  intro v hvm
  have hv : ((sized v ∧ v.content.length = d)
      ∧ (settledAt pool (act i k v) ∧ settledAt pool (act k j v))) :=
    ⟨⟨hall v hvm, hlens v hvm⟩, ⟨h1 v hvm, h2 v hvm⟩⟩
  have hsz : sized v := hv.1.1
  have hid : i < v.content.length := by
    rw [hv.1.2]
    exact hi
  have hkd : k < v.content.length := by
    rw [hv.1.2]
    exact hk
  have hidA : i < (moveAt k j v.content).length := by
    rw [length_moveAt]
    exact hid
  have hG : elim.rowsLen
      (monomialsAt (moveAt i j v.content)).length
      (groupAt pool (moveAt i j v.content)) :=
    rowsLen_groupAt _ pool hall
  have hIJ := out_gen v.content i j hid hij
  have hKJ := out_gen v.content k j hkd hkj
  have hIK := out_gen (moveAt k j v.content) i k hidA hik
  rw [moveAt_chain i k j v.content] at hIK
  have hT1 : elim.spanRel
      (monomialsAt (moveAt i j v.content)).length
      (groupAt pool (moveAt i j v.content))
      (elim.matVec (units.matUnitAt (moveAt i j v.content)
          (moveAt k j v.content) i k)
        (elim.matVec (units.matUnitAt (moveAt k j v.content)
          v.content k j) v.coords)) := by
    have hinner : elim.spanRel
        (monomialsAt (moveAt k j v.content)).length
        (groupAt pool (moveAt k j v.content))
        (elim.matVec (units.matUnitAt (moveAt k j v.content)
          v.content k j) v.coords) :=
      span_of_settled pool (act k j v) hall (act_sized k j v) hv.2.2
    have h := act_transport pool i k hall h1
      (moveAt k j v.content) _ (act_sized k j v) hinner
    rw [moveAt_chain i k j v.content] at h
    exact h
  refine settled_of_span pool _ (act_sized i j v) ?_
  show elim.spanRel (monomialsAt (moveAt i j v.content)).length
    (groupAt pool (moveAt i j v.content))
    (elim.matVec (units.matUnitAt (moveAt i j v.content)
      v.content i j) v.coords)
  by_cases hkocc : 0 < ground.getAt 0 v.content k
  · have hIK' := out_gen v.content i k hid hik
    have hkB : k < (moveAt i k v.content).length := by
      rw [length_moveAt]
      exact hkd
    have hKJ' := out_gen (moveAt i k v.content) k j hkB hkj
    rw [moveAt_chain' i k j v.content hij hkj hkocc] at hKJ'
    have hT2 : elim.spanRel
        (monomialsAt (moveAt i j v.content)).length
        (groupAt pool (moveAt i j v.content))
        (elim.matVec (units.matUnitAt (moveAt i j v.content)
            (moveAt i k v.content) k j)
          (elim.matVec (units.matUnitAt (moveAt i k v.content)
            v.content i k) v.coords)) := by
      have hinner : elim.spanRel
          (monomialsAt (moveAt i k v.content)).length
          (groupAt pool (moveAt i k v.content))
          (elim.matVec (units.matUnitAt (moveAt i k v.content)
            v.content i k) v.coords) :=
        span_of_settled pool (act i k v) hall (act_sized i k v) hv.2.1
      have h := act_transport pool k j hall h2
        (moveAt i k v.content) _ (act_sized i k v) hinner
      rw [moveAt_chain' i k j v.content hij hkj hkocc] at h
      exact h
    exact act_split_gen pool v.content (moveAt i k v.content)
      i k j v.coords hG hT1 hT2
      (units.matVec_comm_read (moveAt i j v.content)
        (moveAt k j v.content) (moveAt i k v.content) v.content
        i k j hij hKJ hIK hIK' hKJ' hIJ v.coords hsz)
  · have hz : ground.getAt 0 v.content k = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 v.content k) with
      | .inl h => h
      | .inr h => absurd h hkocc
    have hIK' : ∀ s m : List Nat,
        0 < ground.countOf s (monomialsAt v.content) →
        0 < ground.countOf m (units.unitAct i k s) →
        m.length = sumNat (List.replicate v.content.length 0)
          ∧ content (List.replicate v.content.length 0).length m
            = List.replicate v.content.length 0 := by
      intro s m hs hm
      rw [units.unitAct_nil_of_zero i k s
        (letter_zero v.content k hz s hs)] at hm
      exact absurd hm (Nat.lt_irrefl 0)
    have hKJ' : ∀ s m : List Nat,
        0 < ground.countOf s
          (monomialsAt (List.replicate v.content.length 0)) →
        0 < ground.countOf m (units.unitAct k j s) →
        m.length = sumNat (moveAt i j v.content)
          ∧ content (moveAt i j v.content).length m
            = moveAt i j v.content :=
      fun s m hs hm =>
        (units.no_out_zero v.content.length k j s m hs hm).elim
    have hT2 : elim.spanRel
        (monomialsAt (moveAt i j v.content)).length
        (groupAt pool (moveAt i j v.content))
        (elim.matVec (units.matUnitAt (moveAt i j v.content)
            (List.replicate v.content.length 0) k j)
          (elim.matVec (units.matUnitAt
            (List.replicate v.content.length 0) v.content i k)
            v.coords)) :=
      elim.spanRel_null _ _ _
        (elim.matVec_null _ _
          (units.matVec_null_unocc
            (List.replicate v.content.length 0) v.content i k hz
            v.coords))
        hG
        (by rw [units.matVec_matUnitAt_length])
    exact act_split_gen pool v.content
      (List.replicate v.content.length 0) i k j v.coords hG hT1
      hT2
      (units.matVec_comm_read (moveAt i j v.content)
        (moveAt k j v.content)
        (List.replicate v.content.length 0) v.content i k j hij
        hKJ hIK hIK' hKJ' hIJ v.coords hsz)

/-- The descent on the gap (`lem:lowerspan`'s descent clause: the
descent closes every pair from the adjacent ones, raisings and
lowerings both): at both adjacent directions settled, every pair
at a stated gap is settled. -/
private theorem act_gap (pool : List HVec) (d : Nat)
    (hall : ∀ v ∈ pool, sized v)
    (hlens : ∀ v ∈ pool, v.content.length = d)
    (hbase : ∀ jr, jr + 1 < d →
      ∀ v ∈ pool, settledAt pool (act jr (jr + 1) v))
    (hbaseD : ∀ jr, jr + 1 < d →
      ∀ v ∈ pool, settledAt pool (act (jr + 1) jr v)) :
    ∀ (g i j : Nat), i < d → j < d →
      (j = i + (g + 1) ∨ i = j + (g + 1)) →
      ∀ v ∈ pool, settledAt pool (act i j v)
  | 0, i, j, hi, hj, hcase => by
    match hcase with
    | .inl he =>
      rw [he]
      refine hbase i ?_
      rw [← he]
      exact hj
    | .inr he =>
      rw [he]
      refine hbaseD j ?_
      rw [← he]
      exact hi
  | g + 1, i, j, hi, hj, hcase => by
    match hcase with
    | .inl he =>
      have hlt : i + 1 < j := by
        rw [he]
        exact Nat.lt_succ_of_le
          (Nat.succ_le_succ (Nat.le_add_right i g))
      have hgap : j = i + 1 + (g + 1) := by
        rw [he, Nat.add_assoc i 1 (g + 1), Nat.add_comm 1 (g + 1)]
      exact act_split pool d i (i + 1) j hall hlens hi
        (Nat.lt_trans hlt hj)
        (Nat.ne_of_lt (Nat.lt_of_succ_lt hlt))
        (Nat.ne_of_lt (Nat.lt_succ_self i)) (Nat.ne_of_lt hlt)
        (hbase i (Nat.lt_trans hlt hj))
        (act_gap pool d hall hlens hbase hbaseD g (i + 1) j
          (Nat.lt_trans hlt hj) hj (Or.inl hgap))
    | .inr he =>
      have hlt : j + 1 < i := by
        rw [he]
        exact Nat.lt_succ_of_le
          (Nat.succ_le_succ (Nat.le_add_right j g))
      have hgap : i = j + 1 + (g + 1) := by
        rw [he, Nat.add_assoc j 1 (g + 1), Nat.add_comm 1 (g + 1)]
      exact act_split pool d i (j + 1) j hall hlens hi
        (Nat.lt_trans hlt hi)
        (fun hc => Nat.ne_of_lt (Nat.lt_of_succ_lt hlt) hc.symm)
        (fun hc => Nat.ne_of_lt hlt hc.symm)
        (fun hc => Nat.ne_of_lt (Nat.lt_succ_self j) hc.symm)
        (act_gap pool d hall hlens hbase hbaseD g i (j + 1) hi
          (Nat.lt_trans hlt hi) (Or.inr hgap))
        (hbaseD j (Nat.lt_trans hlt hi))

/-- The closure: at the span's semantic reads every distinct
letter pair's action sends every member to a settled vector, the
word induction's read. -/
theorem act_closed (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length)
    (i j : Nat) (hi : i < s.length) (hj : j < s.length)
    (hij : ¬ i = j) :
    ∀ v ∈ blockSpan s, settledAt (blockSpan s) (act i j v) := by
  have hlens : ∀ v ∈ blockSpan s, v.content.length = s.length :=
    fun v hv => (raise_all s hall hcl v hv).1
  match Nat.lt_or_ge i j with
  | .inl hlt =>
    match gap_of_lt j i hlt with
    | ⟨g, hg⟩ =>
      exact act_gap (blockSpan s) s.length hall hlens
        (fun jr hjr => act_adj_raise s hall hcl jr hjr)
        (fun jr hjr =>
          lower_imgs (blockSpan s) s.length jr hcl hall hjr)
        g i j hi hj (Or.inl hg)
  | .inr hge =>
    match gap_of_lt i j
        (Nat.lt_of_le_of_ne hge (fun he => hij he.symm)) with
    | ⟨g, hg⟩ =>
      exact act_gap (blockSpan s) s.length hall hlens
        (fun jr hjr => act_adj_raise s hall hcl jr hjr)
        (fun jr hjr =>
          lower_imgs (blockSpan s) s.length jr hcl hall hjr)
        g i j hi hj (Or.inr hg)

/-- The closure at the span level: the action transports a group's
span member into the moved group's span. -/
theorem act_span (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length)
    (i j : Nat) (hi : i < s.length) (hj : j < s.length)
    (hij : ¬ i = j) (mu : List Nat)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length)
    (hsp : elim.spanRel (monomialsAt mu).length
      (groupAt (blockSpan s) mu) x) :
    elim.spanRel (monomialsAt (moveAt i j mu)).length
      (groupAt (blockSpan s) (moveAt i j mu))
      (elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j) x) :=
  act_transport (blockSpan s) i j hall
    (act_closed s hall hcl i j hi hj hij) mu x hx hsp

/-- The H-read's closure (`lem:lowerspan`'s diagonal clause): the
equal-lettered unit acts as the letter's occupancy scalar on every
member, the scaled member settled in its own group. -/
theorem diag_closed (s : Shape)
    (hall : ∀ v ∈ blockSpan s, sized v)
    (hcl : closedAt (blockSpan s) s.length) (p : Nat)
    (hp : p < s.length) :
    ∀ v ∈ blockSpan s, settledAt (blockSpan s)
      (⟨v.content,
        elim.matVec (units.matUnitAt v.content v.content p p)
          v.coords⟩ : HVec) := by
  intro v hvm
  have hv := raise_all s hall hcl v hvm
  have hlen : v.content.length = s.length := hv.1
  have hx : v.coords.length
      = (monomialsAt v.content).length := hv.2.1
  have hone := units.matVec_diag_read v.content p
    (by rw [hlen]; exact hp) v.coords hx
  have hsp : elim.spanRel (monomialsAt v.content).length
      (groupAt (blockSpan s) v.content)
      (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content p))
        v.coords) := by
    refine elim.spanRel_scale _ _ _ _ ?_ hx ?_
    · exact rowsLen_groupAt v.content (blockSpan s) hall
    · rw [← hx]
      exact settled_to_span (blockSpan s) v hall hx hv.2.2.1
  refine Or.inr ?_
  show elim.spanRel
    (elim.matVec (units.matUnitAt v.content v.content p p)
      v.coords).length
    (groupAt (blockSpan s) v.content) _
  rw [units.matVec_matUnitAt_length]
  exact elim.spanRel_congr _ _ _ _ (poly.oneValue_symm hone) hsp
    (by rw [units.matVec_matUnitAt_length])

/-! The exhibit's general top read (`lem:lowerspan`'s descent
clause at the raisings): a pair at a gap beyond one is the crossed
composite at an interior letter, each composite's inner image an
adjacent-or-shorter one, so the descent on the gap carries
`lem:tops`(iii) from the adjacent raisings to every pair. -/

private theorem exhibit_top_go (s : Shape) :
    ∀ (g i j : Nat), j < s.length → j = i + (g + 1) →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j (rowList s)) (rowList s) i j)
        (exhibit s).coords)
  | 0, i, j, hj, he => by
    have he' : j = i + 1 := he
    rw [he', moveAt_moveUp i (rowList s)]
    exact exhibit_top s i (he' ▸ hj)
  | g + 1, i, j, hj, he => by
    have hmu : (rowList s).length = s.length :=
      places.length_rowList s
    have hsz : (exhibit s).coords.length
        = (monomialsAt (rowList s)).length := by
      have h : (exhibit s).coords.length
          = (monomialsAt (exhibit s).content).length :=
        exhibit_sized s
      rw [content_exhibit s] at h
      exact h
    have hlt : i + 1 < j := by
      rw [he]
      exact Nat.lt_succ_of_le
        (Nat.succ_le_succ (Nat.le_add_right i g))
    have hgap : j = i + 1 + (g + 1) := by
      rw [he, Nat.add_assoc i 1 (g + 1), Nat.add_comm 1 (g + 1)]
    have hij : ¬ i = j := Nat.ne_of_lt (Nat.lt_of_succ_lt hlt)
    have hik : ¬ i = i + 1 := Nat.ne_of_lt (Nat.lt_succ_self i)
    have hkj : ¬ i + 1 = j := Nat.ne_of_lt hlt
    have hjd : j < (rowList s).length := by
      rw [hmu]
      exact hj
    have hid : i < (rowList s).length :=
      Nat.lt_trans (Nat.lt_of_succ_lt hlt) hjd
    have hkd : i + 1 < (rowList s).length := Nat.lt_trans hlt hjd
    have hidA : i < (moveAt (i + 1) j (rowList s)).length := by
      rw [length_moveAt]
      exact hid
    have hKJ := out_gen (rowList s) (i + 1) j hkd hkj
    have hIK := out_gen (moveAt (i + 1) j (rowList s)) i (i + 1)
      hidA hik
    rw [moveAt_chain i (i + 1) j (rowList s)] at hIK
    have hIJ := out_gen (rowList s) i j hid hij
    have hA : poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j (rowList s))
          (moveAt (i + 1) j (rowList s)) i (i + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (i + 1) j (rowList s)) (rowList s) (i + 1) j)
          (exhibit s).coords)) :=
      elim.matVec_null _ _
        (exhibit_top_go s g (i + 1) j hj hgap)
    by_cases hkocc : 0 < ground.getAt 0 (rowList s) (i + 1)
    · have hkB : i + 1 < (moveAt i (i + 1) (rowList s)).length := by
        rw [length_moveAt]
        exact hkd
      have hIK' := out_gen (rowList s) i (i + 1) hid hik
      have hKJ' := out_gen (moveAt i (i + 1) (rowList s)) (i + 1) j
        hkB hkj
      rw [moveAt_chain' i (i + 1) j (rowList s) hij hkj hkocc]
        at hKJ'
      have hB : poly.unitTail (elim.matVec
          (units.matUnitAt (moveAt i j (rowList s))
            (moveAt i (i + 1) (rowList s)) (i + 1) j)
          (elim.matVec (units.matUnitAt
            (moveAt i (i + 1) (rowList s)) (rowList s) i (i + 1))
            (exhibit s).coords)) :=
        elim.matVec_null _ _ (by
          rw [moveAt_moveUp i (rowList s)]
          exact exhibit_top s i (Nat.lt_trans hlt hj))
      exact poly.oneValue_unitTail
        (units.matVec_comm_read (moveAt i j (rowList s))
          (moveAt (i + 1) j (rowList s))
          (moveAt i (i + 1) (rowList s)) (rowList s) i (i + 1) j
          hij hKJ hIK hIK' hKJ' hIJ (exhibit s).coords hsz)
        (elim.unitTail_vecAdd_of hA (poly.unitTail_swapMap _ hB))
    · have hz : ground.getAt 0 (rowList s) (i + 1) = 0 :=
        match Nat.eq_zero_or_pos
            (ground.getAt 0 (rowList s) (i + 1)) with
        | .inl h => h
        | .inr h => absurd h hkocc
      have hIK' : ∀ w m : List Nat,
          0 < ground.countOf w (monomialsAt (rowList s)) →
          0 < ground.countOf m (units.unitAct i (i + 1) w) →
          m.length = sumNat (List.replicate (rowList s).length 0)
            ∧ content
                (List.replicate (rowList s).length 0).length m
              = List.replicate (rowList s).length 0 := by
        intro w m hw hm
        rw [units.unitAct_nil_of_zero i (i + 1) w
          (letter_zero (rowList s) (i + 1) hz w hw)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      have hKJ' : ∀ w m : List Nat,
          0 < ground.countOf w
            (monomialsAt (List.replicate (rowList s).length 0)) →
          0 < ground.countOf m (units.unitAct (i + 1) j w) →
          m.length = sumNat (moveAt i j (rowList s))
            ∧ content (moveAt i j (rowList s)).length m
              = moveAt i j (rowList s) :=
        fun w m hw hm =>
          (units.no_out_zero (rowList s).length (i + 1) j w m hw hm).elim
      have hB : poly.unitTail (elim.matVec
          (units.matUnitAt (moveAt i j (rowList s))
            (List.replicate (rowList s).length 0) (i + 1) j)
          (elim.matVec (units.matUnitAt
            (List.replicate (rowList s).length 0) (rowList s)
            i (i + 1)) (exhibit s).coords)) :=
        elim.matVec_null _ _
          (units.matVec_null_unocc
            (List.replicate (rowList s).length 0)
            (rowList s) i (i + 1) hz (exhibit s).coords)
      exact poly.oneValue_unitTail
        (units.matVec_comm_read (moveAt i j (rowList s))
          (moveAt (i + 1) j (rowList s))
          (List.replicate (rowList s).length 0) (rowList s)
          i (i + 1) j hij hKJ hIK hIK' hKJ' hIJ
          (exhibit s).coords hsz)
        (elim.unitTail_vecAdd_of hA (poly.unitTail_swapMap _ hB))

/-- The exhibit's top read at every raising pair: the general
pair's image is the crossed composite of adjacent images
(`lem:lowerspan`'s descent clause), each adjacent image the sum's
unit (`lem:tops`(iii)). -/
theorem exhibit_top_all (s : Shape) (i j : Nat) (hij : i < j)
    (hj : j < s.length) :
    poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i j (rowList s)) (rowList s) i j)
      (exhibit s).coords) :=
  match gap_of_lt j i hij with
  | ⟨g, hg⟩ => exhibit_top_go s g i j hj hg

/-! `lem:dualread`(ii)'s engine tier: the full wedge's letter reads
with its lowering image, the tensor's coordinate at a split
position, and the pairing's factorization over the
concatenation. -/

/-- The full wedge's content is occupied at every letter: the
indicator reads the natural one below the letter count. -/
theorem wedge_full_get (d x : Nat) (hx : x < d) :
    ground.getAt 0 (wedge d d).content x = 1 := by
  show ground.getAt 0 ((List.range d).map
    (fun i => if i < d then 1 else 0)) x = 1
  rw [ground.getAt_map 0 0 (fun i => if i < d then 1 else 0)
      (List.range d) x (by rw [ground.length_range]; exact hx),
    ground.getAt_range d x hx, if_pos hx]

private theorem wedge_full_le (d i : Nat) :
    ground.getAt 0 (wedge d d).content i ≤ 1 := by
  by_cases hid : i < d
  · exact Nat.le_of_eq (wedge_full_get d i hid)
  · rw [ground.getAt_over 0 (wedge d d).content i
      (by rw [wedge_clen d d]; exact Nat.le_of_not_lt hid)]
    exact Nat.le_succ 0

/-- The full wedge sits off the unit tail: its head coordinate is
the scalar one at an occupied enumeration. -/
theorem wedge_off_unit : ∀ d : Nat,
    ¬ poly.unitTail (wedge d d).coords := by
  intro d hu
  have hb : 0 < (wedge d d).coords.length := by
    rw [wedge_sized d d]
    exact monomialsAt_occupied (wedge d d).content
  exact wedge_off d d 0 hb
    (poly.getAt_unitTail hu 0)

private theorem getAt_moveDn_self (j : Nat) (mu : List Nat)
    (hocc : 0 < ground.getAt 0 mu j) :
    ground.getAt 0 (units.moveDn j mu) j + 1
      = ground.getAt 0 mu j := by
  rw [units.getAt_moveDn_self j mu]
  exact ground.subAdd hocc

private theorem lower_out_fwd (mu : List Nat) (j : Nat)
    (hj : j + 1 < mu.length)
    (hocc : 0 < ground.getAt 0 mu j) :
    ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (units.unitAct (j + 1) j s) →
      m.length = sumNat (units.moveDn j mu)
        ∧ content (units.moveDn j mu).length m
          = units.moveDn j mu := by
  intro s m hs hm
  have hd : (units.moveDn j mu).length = mu.length :=
    units.length_moveDn j mu
  match member_conditions hs with
  | ⟨hsl, hsc⟩ =>
    refine ⟨?_, ?_⟩
    · rw [units.length_unitAct_out (j + 1) j s m hm, hsl,
        units.sumNat_moveDn j mu hj hocc]
    · rw [hd]
      refine content_eq_of_entries mu.length m
        (units.moveDn j mu) hd ?_
      intro x hx
      have hcnt := units.countOf_unitAct_out (j + 1) j x s m hm
      have hsx : ground.countOf x s = ground.getAt 0 mu x := by
        rw [← getAt_contentAt mu.length s x hx, hsc]
      rw [hsx] at hcnt
      by_cases hxj : x = j
      · rw [hxj] at hcnt ⊢
        rw [if_pos rfl, if_neg (Nat.ne_of_lt (Nat.lt_succ_self j))] at hcnt
        refine ground.addCancelR 1 ?_
        rw [getAt_moveDn_self j mu hocc, hcnt]
        exact Nat.add_zero _
      · by_cases hxj1 : x = j + 1
        · rw [hxj1] at hcnt ⊢
          rw [if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm), if_pos rfl,
            Nat.add_zero] at hcnt
          rw [hcnt, units.getAt_moveDn_next j mu hj]
        · rw [if_neg hxj, if_neg hxj1, Nat.add_zero,
            Nat.add_zero] at hcnt
          rw [hcnt, units.getAt_moveDn_ne j mu x hxj hxj1]

private theorem lower_out_rev (mu : List Nat) (j : Nat)
    (hj : j + 1 < mu.length)
    (hocc : 0 < ground.getAt 0 mu j) :
    ∀ t m : List Nat,
      0 < ground.countOf t (monomialsAt (units.moveDn j mu)) →
      0 < ground.countOf m (units.unitAct j (j + 1) t) →
      m.length = sumNat mu ∧ content mu.length m = mu := by
  intro t m ht hm
  have hd : (units.moveDn j mu).length = mu.length :=
    units.length_moveDn j mu
  match member_conditions ht with
  | ⟨htl, htc⟩ =>
    have htc' : content mu.length t = units.moveDn j mu := by
      rw [← hd]
      exact htc
    refine ⟨?_, ?_⟩
    · rw [units.length_unitAct_out j (j + 1) t m hm, htl,
        units.sumNat_moveDn j mu hj hocc]
    · refine content_eq_of_entries mu.length m mu rfl ?_
      intro x hx
      have hcnt := units.countOf_unitAct_out j (j + 1) x t m hm
      have htx : ground.countOf x t
          = ground.getAt 0 (units.moveDn j mu) x := by
        rw [← getAt_contentAt mu.length t x hx, htc']
      rw [htx] at hcnt
      by_cases hxj : x = j
      · rw [hxj] at hcnt ⊢
        rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_self j)), if_pos rfl, Nat.add_zero]
          at hcnt
        rw [hcnt, getAt_moveDn_self j mu hocc]
      · by_cases hxj1 : x = j + 1
        · rw [hxj1] at hcnt ⊢
          rw [if_pos rfl, if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm),
            Nat.add_zero] at hcnt
          refine ground.addCancelR 1 ?_
          rw [hcnt, units.getAt_moveDn_next j mu hj]
        · rw [if_neg hxj1, if_neg hxj, Nat.add_zero,
            Nat.add_zero] at hcnt
          rw [hcnt, units.getAt_moveDn_ne j mu x hxj hxj1]

/-- The reversed lowering's Leibniz sum at a target word reads the
sum's unit. -/
private def lowerNull (j : Nat) (v : HVec) : Prop :=
  actNull j (j + 1) v

private theorem wedge_lowerNull (d j : Nat) (hj : j + 1 < d) :
    lowerNull j (wedge d d) := by
  intro t hmem
  have hcntmem : ∀ m x, 0 < ground.countOf m
        (units.unitAct j (j + 1) t) → x < d →
      ground.countOf x m
        = ground.getAt 0 (wedge d d).content x := by
    intro m x hm hx
    match hmem m hm with
    | ⟨_, hmc⟩ =>
      rw [wedge_clen d d] at hmc
      rw [← getAt_contentAt d m x hx, hmc]
  have hcoord : ∀ m : List Nat,
      m.length = sumNat (wedge d d).content →
      content (wedge d d).content.length m = (wedge d d).content →
      coordAt (wedge d d) m
        = if parity m then (BPair.ofNat 1).swap
          else BPair.ofNat 1 := by
    intro m hml hmc
    have hr := rankOf_read m (wedge d d).content hml hmc
    show ground.getAt BPair.unit
      ((monomialsAt (wedge d d).content).map (fun m =>
        if parity m then (BPair.ofNat 1).swap else BPair.ofNat 1))
      (rankOf m (wedge d d).content) = _
    rw [ground.getAt_map ([] : List Nat) BPair.unit _
      (monomialsAt (wedge d d).content) _ hr.1, hr.2]
  match Nat.eq_zero_or_pos (ground.countOf (j + 1) t) with
  | .inl hz =>
    rw [units.unitAct_nil_of_zero j (j + 1) t hz]
    exact BPair.oneValue_refl _
  | .inr hpos =>
    have hr1 := unitAct_pos j (j + 1) t hpos
    have hcnt2 : ground.countOf (j + 1) t = 2 := by
      have ho := units.countOf_unitAct_out j (j + 1) (j + 1) t
        (repl1 j (j + 1) t) hr1
      rw [if_pos rfl, if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm),
        hcntmem (repl1 j (j + 1) t) (j + 1) hr1 hj,
        wedge_full_get d (j + 1) hj] at ho
      exact (Nat.add_zero _).symm.trans ho.symm
    have hlist := unitAct_two j (j + 1) t hcnt2
    have hm2 : 0 < ground.countOf (repl2 j (j + 1) t)
        (units.unitAct j (j + 1) t) := by
      rw [hlist]
      refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
      show 0 < ground.countOf (repl2 j (j + 1) t) [repl2 j (j + 1) t]
      rw [ground.countOf_cons, if_pos rfl]
      exact Nat.succ_pos 0
    have hdist : ∀ y, ground.countOf y (repl1 j (j + 1) t) ≤ 1 :=
      member_distinct (wedge d d).content (repl1 j (j + 1) t)
        (wedge_full_le d) (hmem _ hr1).1 (hmem _ hr1).2
    have hpar := parity_repl2 j (j + 1) t
      (Nat.le_of_eq hcnt2.symm) hdist
    rw [hlist]
    show (coordAt (wedge d d) (repl1 j (j + 1) t)
      + (coordAt (wedge d d) (repl2 j (j + 1) t)
        + BPair.unit)).oneValue BPair.unit
    rw [hcoord (repl1 j (j + 1) t) (hmem _ hr1).1 (hmem _ hr1).2,
      hcoord (repl2 j (j + 1) t) (hmem _ hm2).1 (hmem _ hm2).2,
      hpar]
    cases hp : parity (repl1 j (j + 1) t) with
    | true =>
      rw [if_pos rfl, if_neg (fun hc : (!true) = true =>
        Bool.noConfusion hc)]
      exact swapPairSum' (BPair.ofNat 1)
    | false =>
      rw [if_neg (fun hc : (false : Bool) = true =>
          Bool.noConfusion hc),
        if_pos (show (!false) = true from rfl)]
      exact swapPairSum (BPair.ofNat 1)

/-- The lowering image's entry at a target place: the reversed
action's Leibniz sum over the target's own word. -/
private theorem lowerH_entry (z : HVec) (j p : Nat)
    (hsz : sized z)
    (hjlen : j + 1 < z.content.length)
    (hocc : 0 < ground.getAt 0 z.content j)
    (hp : p < (monomialsAt (units.moveDn j z.content)).length) :
    (ground.getAt BPair.unit
      (elim.matVec (units.matUnitAt (units.moveDn j z.content)
        z.content (j + 1) j) z.coords) p).oneValue
      (ground.bsum (coordAt z) (units.unitAct j (j + 1)
        (ground.getAt []
          (monomialsAt (units.moveDn j z.content)) p))) := by
  refine BPair.oneValue_trans
    (matVec_entry (units.moveDn j z.content) z.content (j + 1) j
      (lower_out_fwd z.content j hjlen hocc) z.coords hsz p hp) ?_
  refine BPair.oneValue_trans
    (wSum_congr _ (fun s' => BPair.ofNat (ground.countOf s'
        (units.unitAct j (j + 1)
          (ground.getAt []
            (monomialsAt (units.moveDn j z.content)) p))))
      (monomialsAt z.content) z.coords
      (fun s' _ => ground.BPair.oneValue_of_eq (congrArg BPair.ofNat
        (units.countOf_unitAct_swap (j + 1) j s' _)))) ?_
  exact wSum_collect z.content z.coords hsz _
    (fun m hm => lower_out_rev z.content j hjlen hocc _ m
      (ground.countOf_getAt_pos []
        (monomialsAt (units.moveDn j z.content)) p hp) hm)

private theorem lowerH_length (z : HVec) (j : Nat) :
    (elim.matVec (units.matUnitAt (units.moveDn j z.content)
      z.content (j + 1) j) z.coords).length
      = (monomialsAt (units.moveDn j z.content)).length := by
  rw [units.matVec_matUnitAt_length]

/-- The full wedge's adjacent lowering image reads the sum's unit
at every coordinate: the target's repeated letter joins its two
sources at opposite gradings.  The range `j + 1 < d` is the
adjacent generators' own index frame (`con:units`), the interior
letter pairs. -/
theorem wedge_lowerH_unit : ∀ (d j : Nat), j + 1 < d →
    ∃ u, lowerH j (wedge d d) = some u
      ∧ poly.unitTail u.coords := by
  intro d j hj
  have hjd : j < d :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  have hocc : 0 < ground.getAt 0 (wedge d d).content j := by
    rw [wedge_full_get d j hjd]
    exact Nat.succ_pos 0
  have hjlen : j + 1 < (wedge d d).content.length := by
    rw [wedge_clen d d]
    exact hj
  have hsome : lowerH j (wedge d d)
      = some ⟨units.moveDn j (wedge d d).content,
        elim.matVec (units.matUnitAt
          (units.moveDn j (wedge d d).content)
          (wedge d d).content (j + 1) j) (wedge d d).coords⟩ :=
    if_pos hocc
  refine ⟨_, hsome, ?_⟩
  show poly.unitTail (elim.matVec (units.matUnitAt
    (units.moveDn j (wedge d d).content) (wedge d d).content
    (j + 1) j) (wedge d d).coords)
  refine elim.unitTail_of_getAt _ ?_
  intro p hp
  rw [lowerH_length (wedge d d) j] at hp
  exact BPair.oneValue_trans
    (lowerH_entry (wedge d d) j p (wedge_sized d d) hjlen hocc hp)
    (wedge_lowerNull d j hj _
      (fun m hm => lower_out_rev (wedge d d).content j hjlen hocc
        _ m (ground.countOf_getAt_pos []
          (monomialsAt (units.moveDn j (wedge d d).content)) p hp)
        hm))

/-! The tensor's coordinate at an enumeration place: the place's
monomial splits at the first factor's degree, the split-matching
places reading the factors' product and every other the sum's
unit. -/

private theorem split_lengths (M : List Nat) (a b : Nat)
    (hM : M.length = a + b) :
    M = List.take a M ++ List.drop a M
      ∧ (List.take a M).length = a ∧ (List.drop a M).length = b := by
  have hle : a ≤ M.length := by
    rw [hM]
    exact Nat.le_add_right _ _
  have h1 : (List.take a M).length = a := ground.length_take a M hle
  refine ⟨(List.take_append_drop a M).symm, h1, ?_⟩
  have hsplit : (List.take a M).length + (List.drop a M).length = M.length := by
    rw [← ground.length_append, List.take_append_drop a M]
  rw [h1, hM] at hsplit
  refine ground.addCancelR a ?_
  rw [Nat.add_comm (List.drop a M).length, Nat.add_comm b]
  exact hsplit

private theorem member_split (v w : HVec)
    (hlen : v.content.length = w.content.length) (M : List Nat)
    (hM : M.length = sumNat (tensorH v w).content) :
    M = List.take (sumNat v.content) M ++ List.drop (sumNat v.content) M
      ∧ (List.take (sumNat v.content) M).length = sumNat v.content
      ∧ (List.drop (sumNat v.content) M).length = sumNat w.content :=
  split_lengths M (sumNat v.content) (sumNat w.content)
    (hM.trans (sumNat_zipWith_add v.content w.content hlen))

private theorem tensor_coord_at (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (hsv : sized v) (hsw : sized w) (k : Nat) (m1 m2 : List Nat)
    (hk : k < (monomialsAt (tensorH v w).content).length)
    (hsplit : ground.getAt [] (monomialsAt (tensorH v w).content) k
      = m1 ++ m2)
    (h1l : m1.length = sumNat v.content)
    (h1c : content v.content.length m1 = v.content)
    (h2l : m2.length = sumNat w.content)
    (h2c : content w.content.length m2 = w.content) :
    (ground.getAt BPair.unit (tensorH v w).coords k).oneValue
      (coordAt v m1 * coordAt w m2) := by
  have hr : rankOf (m1 ++ m2) (tensorH v w).content = k := by
    rw [← hsplit]
    exact rankOf_getAt (tensorH v w).content k hk
  rw [← hr]
  exact tensor_coord v w hlen hsv hsw m1 m2 h1l h1c h2l h2c

private theorem tensor_coord_at_null (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (k : Nat) (m1 m2 : List Nat)
    (hk : k < (monomialsAt (tensorH v w).content).length)
    (hsplit : ground.getAt [] (monomialsAt (tensorH v w).content) k
      = m1 ++ m2)
    (h1l : m1.length = sumNat v.content)
    (hbad : (m1.length = sumNat v.content
        ∧ content v.content.length m1 = v.content) →
      (m2.length = sumNat w.content
        ∧ content w.content.length m2 = w.content) → False) :
    (ground.getAt BPair.unit (tensorH v w).coords k).oneValue
      BPair.unit := by
  have hm := member_conditions
    (ground.countOf_getAt_pos []
      (monomialsAt (tensorH v w).content) k hk)
  rw [hsplit] at hm
  have hr : rankOf (m1 ++ m2) (tensorH v w).content = k := by
    rw [← hsplit]
    exact rankOf_getAt (tensorH v w).content k hk
  rw [← hr]
  exact tensor_coord_null v w hlen m1 m2 hm.1 hm.2 h1l hbad


private theorem length_vecAdd_le : ∀ (u w : List BPair),
    u.length ≤ w.length → (elim.vecAdd u w).length = u.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | _ :: u, _ :: w, h =>
    congrArg Nat.succ (length_vecAdd_le u w
      (Nat.le_of_succ_le_succ h))

private theorem length_vecAdd_ge : ∀ (u w : List BPair),
    w.length ≤ u.length → (elim.vecAdd u w).length = w.length
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: u, _ :: w, h =>
    congrArg Nat.succ (length_vecAdd_ge u w
      (Nat.le_of_succ_le_succ h))

theorem moveAt_zipWith_left (i j : Nat) (a b : List Nat)
    (hocc : 0 < ground.getAt 0 a j) :
    List.zipWith (fun x y => x + y) (moveAt i j a) b
      = moveAt i j (List.zipWith (fun x y => x + y) a b) := by
  show List.zipWith (fun x y => x + y) (bumpAt i (dipAt j a)) b
    = bumpAt i (dipAt j (List.zipWith (fun x y => x + y) a b))
  rw [bumpAt_zipWith_left i (dipAt j a) b,
    dipAt_zipWith_left j a b hocc]

theorem moveAt_zipWith_right (i j : Nat) (a b : List Nat)
    (hocc : 0 < ground.getAt 0 b j) :
    List.zipWith (fun x y => x + y) a (moveAt i j b)
      = moveAt i j (List.zipWith (fun x y => x + y) a b) := by
  show List.zipWith (fun x y => x + y) a (bumpAt i (dipAt j b))
    = bumpAt i (dipAt j (List.zipWith (fun x y => x + y) a b))
  rw [bumpAt_zipWith_right i a (dipAt j b),
    dipAt_zipWith_right j a b hocc]

/-- The tensor sits at the unit tail exactly where a factor does:
a factor's unit coefficients absorb every scattered product, and
two off-unit coefficients give an off-unit product at their
concatenation's place. -/
theorem tensorH_unitTail : ∀ (v w : HVec), sized v → sized w →
    v.content.length = w.content.length →
    (poly.unitTail (tensorH v w).coords ↔
      (poly.unitTail v.coords ∨ poly.unitTail w.coords)) := by
  intro v w hsv hsw hlen
  constructor
  · intro ht
    by_cases hv : poly.unitTail v.coords
    · exact Or.inl hv
    · refine Or.inr ?_
      by_cases hw : poly.unitTail w.coords
      · exact hw
      · exfalso
        match poly.offUnit_witness v.coords hv,
            poly.offUnit_witness w.coords hw with
        | ⟨p, hp, hpo⟩, ⟨q, hq, hqo⟩ =>
          have hpm : p < (monomialsAt v.content).length := by
            rw [← hsv]
            exact hp
          have hqm : q < (monomialsAt w.content).length := by
            rw [← hsw]
            exact hq
          have hm1 := member_conditions
            (ground.countOf_getAt_pos []
              (monomialsAt v.content) p hpm)
          have hm2 := member_conditions
            (ground.countOf_getAt_pos []
              (monomialsAt w.content) q hqm)
          have hc1 : coordAt v
              (ground.getAt [] (monomialsAt v.content) p)
              = ground.getAt BPair.unit v.coords p := by
            show ground.getAt BPair.unit v.coords
              (rankOf (ground.getAt [] (monomialsAt v.content) p)
                v.content) = _
            rw [rankOf_getAt v.content p hpm]
          have hc2 : coordAt w
              (ground.getAt [] (monomialsAt w.content) q)
              = ground.getAt BPair.unit w.coords q := by
            show ground.getAt BPair.unit w.coords
              (rankOf (ground.getAt [] (monomialsAt w.content) q)
                w.content) = _
            rw [rankOf_getAt w.content q hqm]
          have hprod : ¬ (coordAt v
              (ground.getAt [] (monomialsAt v.content) p)
              * coordAt w
                (ground.getAt [] (monomialsAt w.content) q)).oneValue
              BPair.unit := by
            rw [hc1, hc2]
            intro hcon
            exact hqo (ground.mul_cancel_unit hpo hcon)
          have hcm := concat_member v.content w.content
            (ground.getAt [] (monomialsAt v.content) p)
            (ground.getAt [] (monomialsAt w.content) q) hlen
            hm1.1 hm1.2 hm2.1 hm2.2
          have hrk := rankOf_read
            (ground.getAt [] (monomialsAt v.content) p
              ++ ground.getAt [] (monomialsAt w.content) q)
            (List.zipWith (fun a b => a + b) v.content w.content)
            hcm.1 hcm.2
          have hidx : rankOf
              (ground.getAt [] (monomialsAt v.content) p
                ++ ground.getAt [] (monomialsAt w.content) q)
              (List.zipWith (fun a b => a + b) v.content w.content)
              < (tensorH v w).coords.length := by
            rw [tensorH_sized v w]
            exact hrk.1
          exact hprod (BPair.oneValue_trans
            (BPair.oneValue_symm (tensor_coord v w hlen hsv hsw _ _
              hm1.1 hm1.2 hm2.1 hm2.2))
            (poly.getAt_unitTail ht _))
  · intro hu
    refine elim.unitTail_of_getAt _ ?_
    intro k hk
    rw [tensorH_sized v w] at hk
    match member_split v w hlen
        (ground.getAt [] (monomialsAt (tensorH v w).content) k)
        (member_conditions (ground.countOf_getAt_pos []
          (monomialsAt (tensorH v w).content) k hk)).1 with
    | ⟨hcat, hl1, hl2⟩ =>
      by_cases hg1 : content v.content.length
          (List.take (sumNat v.content)
            (ground.getAt [] (monomialsAt (tensorH v w).content) k))
          = v.content
      · by_cases hg2 : content w.content.length
            (List.drop (sumNat v.content)
              (ground.getAt []
                (monomialsAt (tensorH v w).content) k))
            = w.content
        · refine BPair.oneValue_trans
            (tensor_coord_at v w hlen hsv hsw k _ _ hk hcat
              hl1 hg1 hl2 hg2) ?_
          match hu with
          | .inl h =>
            exact BPair.oneValue_trans
              (BPair.mul_congr (poly.getAt_unitTail h _)
                (BPair.oneValue_refl _)) (BPair.unit_mul _)
          | .inr h =>
            exact BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl _)
                (poly.getAt_unitTail h _)) (BPair.mul_unit _)
        · exact tensor_coord_at_null v w hlen k _ _ hk hcat hl1
            (fun _ h2 => hg2 h2.2)
      · exact tensor_coord_at_null v w hlen k _ _ hk hcat hl1
          (fun h1 _ => hg1 h1.2)

private theorem act_entry (z : HVec) (i j p : Nat)
    (hsz : sized z) (hi : i < z.content.length) (hij : ¬ i = j)
    (hj : j < z.content.length)
    (hocc : 0 < ground.getAt 0 z.content j)
    (hp : p < (monomialsAt (moveAt i j z.content)).length) :
    (ground.getAt BPair.unit (act i j z).coords p).oneValue
      (ground.bsum (coordAt z) (units.unitAct j i
        (ground.getAt []
          (monomialsAt (moveAt i j z.content)) p))) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hjm : j < (moveAt i j z.content).length := by
    rw [length_moveAt]
    exact hj
  have houts : ∀ m, 0 < ground.countOf m
      (units.unitAct j i (ground.getAt []
        (monomialsAt (moveAt i j z.content)) p)) →
      m.length = sumNat z.content
        ∧ content z.content.length m = z.content := by
    have h := out_gen (moveAt i j z.content) j i hjm hji
    rw [moveAt_round_at j i z.content hocc] at h
    exact fun m hm => h _ m (ground.countOf_getAt_pos []
      (monomialsAt (moveAt i j z.content)) p hp) hm
  show (ground.getAt BPair.unit (elim.matVec (units.matUnitAt
    (moveAt i j z.content) z.content i j) z.coords) p).oneValue _
  refine BPair.oneValue_trans
    (matVec_entry (moveAt i j z.content) z.content i j
      (out_gen z.content i j hi hij) z.coords hsz p hp) ?_
  refine BPair.oneValue_trans
    (wSum_congr _ (fun s' => BPair.ofNat (ground.countOf s'
        (units.unitAct j i (ground.getAt []
          (monomialsAt (moveAt i j z.content)) p))))
      (monomialsAt z.content) z.coords
      (fun s' _ => ground.BPair.oneValue_of_eq (congrArg BPair.ofNat
        (units.countOf_unitAct_swap i j s' _)))) ?_
  exact wSum_collect z.content z.coords hsz _ houts

private theorem act_unitTail (z : HVec) (i j : Nat)
    (hsz : sized z) (hi : i < z.content.length) (hij : ¬ i = j)
    (hj : j < z.content.length)
    (hzero : ground.getAt 0 z.content j = 0) :
    poly.unitTail (act i j z).coords := by
  have hnil : ∀ s, 0 < ground.countOf s (monomialsAt z.content) →
      units.unitAct i j s = [] := by
    intro s hs
    match member_conditions hs with
    | ⟨_, hsc⟩ =>
      refine units.unitAct_nil_of_zero i j s ?_
      rw [← getAt_contentAt z.content.length s j hj, hsc, hzero]
  show poly.unitTail (elim.matVec (units.matUnitAt
    (moveAt i j z.content) z.content i j) z.coords)
  refine elim.unitTail_of_getAt _ ?_
  intro p hp
  rw [units.matVec_matUnitAt_length] at hp
  refine BPair.oneValue_trans
    (matVec_entry (moveAt i j z.content) z.content i j
      (out_gen z.content i j hi hij) z.coords hsz p hp) ?_
  refine wSum_null _ _ _ ?_
  intro s' hs'
  rw [hnil s' hs']
  exact BPair.oneValue_refl _

private theorem act_memA {P : List Nat → Prop} (a b : Nat)
    (M1 M2 : List Nat)
    (houts : ∀ m, 0 < ground.countOf m
      (units.unitAct a b (M1 ++ M2)) → P m) :
    ∀ m1, 0 < ground.countOf m1 (units.unitAct a b M1) →
      P (m1 ++ M2) := by
  intro m1 hm1
  refine houts (m1 ++ M2) ?_
  rw [units.unitAct_append a b M1 M2, ground.countOf_append]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
  exact countOf_map_pos (fun m => m ++ M2) m1
    (units.unitAct a b M1) hm1

private theorem act_memB {P : List Nat → Prop} (a b : Nat)
    (M1 M2 : List Nat)
    (houts : ∀ m, 0 < ground.countOf m
      (units.unitAct a b (M1 ++ M2)) → P m) :
    ∀ m2, 0 < ground.countOf m2 (units.unitAct a b M2) →
      P (M1 ++ m2) := by
  intro m2 hm2
  refine houts (M1 ++ m2) ?_
  rw [units.unitAct_append a b M1 M2, ground.countOf_append]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
  exact countOf_map_pos (fun m => M1 ++ m) m2
    (units.unitAct a b M2) hm2

private theorem act_tensor_outs (i j : Nat) (z : HVec)
    (hj : j < z.content.length)
    (hij : ¬ i = j) (hocc : 0 < ground.getAt 0 z.content j)
    (p : Nat)
    (hp : p < (monomialsAt (moveAt i j z.content)).length) :
    ∀ m, 0 < ground.countOf m (units.unitAct j i
      (ground.getAt []
        (monomialsAt (moveAt i j z.content)) p)) →
      m.length = sumNat z.content
        ∧ content z.content.length m = z.content := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hjm : j < (moveAt i j z.content).length := by
    rw [length_moveAt]
    exact hj
  have h := out_gen (moveAt i j z.content) j i hjm hji
  rw [moveAt_round_at j i z.content hocc] at h
  exact fun m hm => h _ m (ground.countOf_getAt_pos []
    (monomialsAt (moveAt i j z.content)) p hp) hm

private theorem act_tensor_leibniz (i j : Nat) (v w : HVec)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hlen : v.content.length = w.content.length)
    (hij : ¬ i = j)
    (hocc : 0 < ground.getAt 0 (tensorH v w).content j)
    (p : Nat) (M1 M2 : List Nat)
    (hp : p < (monomialsAt
      (moveAt i j (tensorH v w).content)).length)
    (hcat : ground.getAt []
        (monomialsAt (moveAt i j (tensorH v w).content)) p
      = M1 ++ M2) :
    (ground.getAt BPair.unit
        (act i j (tensorH v w)).coords p).oneValue
      (ground.bsum (coordAt (tensorH v w))
          ((units.unitAct j i M1).map (fun m => m ++ M2))
        + ground.bsum (coordAt (tensorH v w))
          ((units.unitAct j i M2).map (fun m => M1 ++ m))) := by
  have hTd : (tensorH v w).content.length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hlen.symm
  have hiT : i < (tensorH v w).content.length := by
    rw [hTd]
    exact hi
  have hjT : j < (tensorH v w).content.length := by
    rw [hTd]
    exact hj
  refine BPair.oneValue_trans
    (act_entry (tensorH v w) i j p (tensorH_sized v w) hiT hij hjT
      hocc hp) ?_
  rw [hcat, units.unitAct_append j i M1 M2]
  exact ground.famFold_append_ov ground.bpairFoldLaws _ _ _

private theorem split_contentL (a b : HVec)
    (hlen : a.content.length = b.content.length)
    (M1 M2 : List Nat)
    (hMc : content (tensorH a b).content.length (M1 ++ M2)
      = (tensorH a b).content)
    (hg2 : content b.content.length M2 = b.content) :
    content a.content.length M1 = a.content := by
  have hd : (tensorH a b).content.length = a.content.length :=
    ground.length_zipWith (fun x y => x + y) a.content b.content a.content.length rfl
      hlen.symm
  have ht2c : content a.content.length M2 = b.content := by
    rw [hlen]
    exact hg2
  rw [hd, content_append a.content.length M1 M2, ht2c] at hMc
  refine zipWith_add_cancelR (content a.content.length M1)
    a.content b.content a.content.length ?_ rfl hlen.symm hMc
  exact ground.length_mapRange _ a.content.length

private theorem split_contentR (a b : HVec)
    (hlen : a.content.length = b.content.length)
    (M1 M2 : List Nat)
    (hMc : content (tensorH a b).content.length (M1 ++ M2)
      = (tensorH a b).content)
    (hg1 : content a.content.length M1 = a.content) :
    content b.content.length M2 = b.content := by
  have hd : (tensorH a b).content.length = a.content.length :=
    ground.length_zipWith (fun x y => x + y) a.content b.content a.content.length rfl
      hlen.symm
  rw [hd, content_append a.content.length M1 M2, hg1] at hMc
  have hcm : content a.content.length M2 = b.content := by
    refine zipWith_add_cancelL a.content
      (content a.content.length M2) b.content
      a.content.length rfl ?_ hlen.symm hMc
    exact ground.length_mapRange _ a.content.length
  rw [← hlen]
  exact hcm

private theorem act_tensor_halfA (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (M1 M2 : List Nat)
    (hl1 : M1.length = sumNat v.content)
    (hl2 : M2.length = sumNat w.content)
    (hg2 : content w.content.length M2 = w.content)
    (hmemA : ∀ m1, 0 < ground.countOf m1 (units.unitAct j i M1) →
      (m1 ++ M2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (m1 ++ M2)
          = List.zipWith (fun a b => a + b) v.content w.content) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M1).map (fun m => m ++ M2))).oneValue
      (ground.bsum (coordAt v) (units.unitAct j i M1)
        * coordAt w M2) := by
  have hm1c : ∀ m1, 0 < ground.countOf m1 (units.unitAct j i M1) →
      m1.length = sumNat v.content
        ∧ content v.content.length m1 = v.content := fun m1 hm1 =>
    ⟨(units.length_unitAct_out j i M1 m1 hm1).trans hl1,
     split_contentL v w hlen m1 M2 (hmemA m1 hm1).2 hg2⟩
  rw [ground.bsum_map]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun m1 => coordAt v m1 * coordAt w M2)
      (units.unitAct j i M1)
      (fun m1 hm1 => tensor_coord v w hlen hsv hsw m1 M2
        (hm1c m1 hm1).1 (hm1c m1 hm1).2 hl2 hg2)) ?_
  exact bsum_mulR (coordAt v) (coordAt w M2) _

private theorem act_tensor_halfB (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (M1 M2 : List Nat)
    (hl1 : M1.length = sumNat v.content)
    (hl2 : M2.length = sumNat w.content)
    (hg1 : content v.content.length M1 = v.content)
    (hmemB : ∀ m2, 0 < ground.countOf m2 (units.unitAct j i M2) →
      (M1 ++ m2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (M1 ++ m2)
          = List.zipWith (fun a b => a + b) v.content w.content) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M2).map (fun m => M1 ++ m))).oneValue
      (coordAt v M1
        * ground.bsum (coordAt w) (units.unitAct j i M2)) := by
  have hm2c : ∀ m2, 0 < ground.countOf m2 (units.unitAct j i M2) →
      m2.length = sumNat w.content
        ∧ content w.content.length m2 = w.content := fun m2 hm2 =>
    ⟨(units.length_unitAct_out j i M2 m2 hm2).trans hl2,
     split_contentR v w hlen M1 m2 (hmemB m2 hm2).2 hg1⟩
  rw [ground.bsum_map]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun m2 => coordAt v M1 * coordAt w m2)
      (units.unitAct j i M2)
      (fun m2 hm2 => tensor_coord v w hlen hsv hsw M1 m2 hl1 hg1
        (hm2c m2 hm2).1 (hm2c m2 hm2).2)) ?_
  exact ground.foldB_mul_left (coordAt v M1) (coordAt w) _

private theorem act_tensor_halfA_null (i j : Nat) (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (M1 M2 : List Nat)
    (hl1 : M1.length = sumNat v.content)
    (hmemA : ∀ m1, 0 < ground.countOf m1 (units.unitAct j i M1) →
      (m1 ++ M2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (m1 ++ M2)
          = List.zipWith (fun a b => a + b) v.content w.content)
    (hbad : ∀ m1, 0 < ground.countOf m1 (units.unitAct j i M1) →
      (m1.length = sumNat v.content
          ∧ content v.content.length m1 = v.content) →
        (M2.length = sumNat w.content
          ∧ content w.content.length M2 = w.content) → False) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M1).map
        (fun m => m ++ M2))).oneValue BPair.unit := by
  rw [ground.bsum_map]
  refine ground.foldB_null _ _ ?_
  intro m1 hm1
  exact tensor_coord_null v w hlen m1 M2 (hmemA m1 hm1).1
    (hmemA m1 hm1).2
    ((units.length_unitAct_out j i M1 m1 hm1).trans hl1)
    (hbad m1 hm1)

private theorem act_tensor_halfB_null (i j : Nat) (v w : HVec)
    (hlen : v.content.length = w.content.length)
    (M1 M2 : List Nat)
    (hl1 : M1.length = sumNat v.content)
    (hmemB : ∀ m2, 0 < ground.countOf m2 (units.unitAct j i M2) →
      (M1 ++ m2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (M1 ++ m2)
          = List.zipWith (fun a b => a + b) v.content w.content)
    (hbad : ∀ m2, 0 < ground.countOf m2 (units.unitAct j i M2) →
      (M1.length = sumNat v.content
          ∧ content v.content.length M1 = v.content) →
        (m2.length = sumNat w.content
          ∧ content w.content.length m2 = w.content) → False) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M2).map
        (fun m => M1 ++ m))).oneValue BPair.unit := by
  rw [ground.bsum_map]
  refine ground.foldB_null _ _ ?_
  intro m2 hm2
  exact tensor_coord_null v w hlen M1 m2 (hmemB m2 hm2).1
    (hmemB m2 hm2).2 hl1 (hbad m2 hm2)

private theorem act_out_occupied (a b : Nat) (hab : ¬ a = b)
    (M m : List Nat)
    (hm : 0 < ground.countOf m (units.unitAct a b M)) :
    0 < ground.countOf a m := by
  have h := units.countOf_unitAct_out a b a M m hm
  rw [if_neg hab, if_pos rfl, Nat.add_zero] at h
  rw [h]
  exact Nat.succ_pos _

private theorem act_tensor_sideA (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hij : ¬ i = j) (hpv : 0 < ground.getAt 0 v.content j)
    (hlenA : (act i j v).content.length = w.content.length)
    (hcA : (tensorH (act i j v) w).content
      = moveAt i j (tensorH v w).content)
    (p : Nat) (M1 M2 : List Nat)
    (hp : p < (monomialsAt
      (moveAt i j (tensorH v w).content)).length)
    (hcat : ground.getAt []
        (monomialsAt (moveAt i j (tensorH v w).content)) p
      = M1 ++ M2)
    (hl1 : M1.length = sumNat v.content)
    (hl2 : M2.length = sumNat w.content)
    (hmemA : ∀ m1, 0 < ground.countOf m1 (units.unitAct j i M1) →
      (m1 ++ M2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (m1 ++ M2)
          = List.zipWith (fun a b => a + b) v.content w.content) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M1).map (fun m => m ++ M2))).oneValue
      (ground.getAt BPair.unit
        (tensorH (act i j v) w).coords p) := by
  have hk : p < (monomialsAt (tensorH (act i j v) w).content).length := by
    rw [hcA]
    exact hp
  have hsplitA : ground.getAt []
      (monomialsAt (tensorH (act i j v) w).content) p = M1 ++ M2 := by
    rw [hcA]
    exact hcat
  have hsum : sumNat (moveAt i j v.content) = sumNat v.content :=
    sumNat_moveAt i j v.content hi hpv
  have hl1' : M1.length = sumNat (act i j v).content := by
    show M1.length = sumNat (moveAt i j v.content)
    rw [hsum]
    exact hl1
  have hMc : content (tensorH (act i j v) w).content.length
      (M1 ++ M2) = (tensorH (act i j v) w).content := by
    rw [← hsplitA]
    exact (member_conditions (ground.countOf_getAt_pos []
      (monomialsAt (tensorH (act i j v) w).content) p hk)).2
  by_cases hg2 : content w.content.length M2 = w.content
  · have hg1' : content (act i j v).content.length M1
        = (act i j v).content :=
      split_contentL (act i j v) w hlenA M1 M2 hMc hg2
    have hcoord : (coordAt (act i j v) M1).oneValue
        (ground.bsum (coordAt v) (units.unitAct j i M1)) := by
      have hr := rankOf_read M1 (moveAt i j v.content)
        (by rw [hsum]; exact hl1) hg1'
      have h := act_entry v i j (rankOf M1 (moveAt i j v.content))
        hsv hi hij hj hpv hr.1
      rw [hr.2] at h
      exact h
    refine BPair.oneValue_trans
      (act_tensor_halfA i j v w hsv hsw hlen M1 M2 hl1 hl2 hg2
        hmemA) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (tensor_coord_at (act i j v) w hlenA (act_sized i j v) hsw p
        M1 M2 hk hsplitA hl1' hg1' hl2 hg2) ?_)
    exact BPair.mul_congr hcoord (BPair.oneValue_refl _)
  · refine BPair.oneValue_trans
      (act_tensor_halfA_null i j v w hlen M1 M2 hl1 hmemA
        (fun _ _ _ hq => hg2 hq.2)) ?_
    exact BPair.oneValue_symm
      (tensor_coord_at_null (act i j v) w hlenA p M1 M2 hk hsplitA
        hl1' (fun _ hq => hg2 hq.2))

private theorem act_tensor_sideB (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hiW : i < w.content.length) (hjW : j < w.content.length)
    (hij : ¬ i = j) (hpw : 0 < ground.getAt 0 w.content j)
    (hlenB : v.content.length = (act i j w).content.length)
    (hcB : (tensorH v (act i j w)).content
      = moveAt i j (tensorH v w).content)
    (p : Nat) (M1 M2 : List Nat)
    (hp : p < (monomialsAt
      (moveAt i j (tensorH v w).content)).length)
    (hcat : ground.getAt []
        (monomialsAt (moveAt i j (tensorH v w).content)) p
      = M1 ++ M2)
    (hl1 : M1.length = sumNat v.content)
    (hl2 : M2.length = sumNat w.content)
    (hmemB : ∀ m2, 0 < ground.countOf m2 (units.unitAct j i M2) →
      (M1 ++ m2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (M1 ++ m2)
          = List.zipWith (fun a b => a + b) v.content w.content) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M2).map (fun m => M1 ++ m))).oneValue
      (ground.getAt BPair.unit
        (tensorH v (act i j w)).coords p) := by
  have hk : p < (monomialsAt (tensorH v (act i j w)).content).length := by
    rw [hcB]
    exact hp
  have hsplitB : ground.getAt []
      (monomialsAt (tensorH v (act i j w)).content) p = M1 ++ M2 := by
    rw [hcB]
    exact hcat
  have hsum : sumNat (moveAt i j w.content) = sumNat w.content :=
    sumNat_moveAt i j w.content hiW hpw
  have hl2' : M2.length = sumNat (act i j w).content := by
    show M2.length = sumNat (moveAt i j w.content)
    rw [hsum]
    exact hl2
  have hMc : content (tensorH v (act i j w)).content.length
      (M1 ++ M2) = (tensorH v (act i j w)).content := by
    rw [← hsplitB]
    exact (member_conditions (ground.countOf_getAt_pos []
      (monomialsAt (tensorH v (act i j w)).content) p hk)).2
  by_cases hg1 : content v.content.length M1 = v.content
  · have hg2' : content (act i j w).content.length M2
        = (act i j w).content :=
      split_contentR v (act i j w) hlenB M1 M2 hMc hg1
    have hcoord : (coordAt (act i j w) M2).oneValue
        (ground.bsum (coordAt w) (units.unitAct j i M2)) := by
      have hr := rankOf_read M2 (moveAt i j w.content)
        (by rw [hsum]; exact hl2) hg2'
      have h := act_entry w i j (rankOf M2 (moveAt i j w.content))
        hsw hiW hij hjW hpw hr.1
      rw [hr.2] at h
      exact h
    refine BPair.oneValue_trans
      (act_tensor_halfB i j v w hsv hsw hlen M1 M2 hl1 hl2 hg1
        hmemB) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (tensor_coord_at v (act i j w) hlenB hsv (act_sized i j w) p
        M1 M2 hk hsplitB hl1 hg1 hl2' hg2') ?_)
    exact BPair.mul_congr (BPair.oneValue_refl _) hcoord
  · refine BPair.oneValue_trans
      (act_tensor_halfB_null i j v w hlen M1 M2 hl1 hmemB
        (fun _ _ hq _ => hg1 hq.2)) ?_
    exact BPair.oneValue_symm
      (tensor_coord_at_null v (act i j w) hlenB p M1 M2 hk hsplitB
        hl1 (fun hq _ => hg1 hq.2))

private theorem act_tensor_sideA_zero (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hij : ¬ i = j) (hvz : ground.getAt 0 v.content j = 0)
    (hlenA : (act i j v).content.length = w.content.length)
    (p : Nat) (M1 M2 : List Nat)
    (hl1 : M1.length = sumNat v.content)
    (hmemA : ∀ m1, 0 < ground.countOf m1 (units.unitAct j i M1) →
      (m1 ++ M2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (m1 ++ M2)
          = List.zipWith (fun a b => a + b) v.content w.content) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M1).map (fun m => m ++ M2))).oneValue
      (ground.getAt BPair.unit
        (tensorH (act i j v) w).coords p) := by
  have hAu : poly.unitTail (tensorH (act i j v) w).coords :=
    (tensorH_unitTail (act i j v) w (act_sized i j v) hsw
      hlenA).mpr
      (Or.inl (act_unitTail v i j hsv hi hij hj hvz))
  refine BPair.oneValue_trans
    (act_tensor_halfA_null i j v w hlen M1 M2 hl1 hmemA ?_)
    (BPair.oneValue_symm (poly.getAt_unitTail hAu p))
  intro m1 hm1 hq _
  have hcj : ground.countOf j m1 = 0 := by
    rw [← getAt_contentAt v.content.length m1 j hj, hq.2, hvz]
  have hpos := act_out_occupied j i (fun he => hij he.symm) M1 m1 hm1
  rw [hcj] at hpos
  exact absurd hpos (Nat.lt_irrefl 0)

private theorem act_tensor_sideB_zero (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hiW : i < w.content.length) (hjW : j < w.content.length)
    (hij : ¬ i = j) (hwz : ground.getAt 0 w.content j = 0)
    (hlenB : v.content.length = (act i j w).content.length)
    (p : Nat) (M1 M2 : List Nat)
    (hl1 : M1.length = sumNat v.content)
    (hmemB : ∀ m2, 0 < ground.countOf m2 (units.unitAct j i M2) →
      (M1 ++ m2).length = sumNat
          (List.zipWith (fun a b => a + b) v.content w.content)
        ∧ content (List.zipWith (fun a b => a + b) v.content
            w.content).length (M1 ++ m2)
          = List.zipWith (fun a b => a + b) v.content w.content) :
    (ground.bsum (coordAt (tensorH v w))
      ((units.unitAct j i M2).map (fun m => M1 ++ m))).oneValue
      (ground.getAt BPair.unit
        (tensorH v (act i j w)).coords p) := by
  have hBu : poly.unitTail (tensorH v (act i j w)).coords :=
    (tensorH_unitTail v (act i j w) hsv (act_sized i j w)
      hlenB).mpr
      (Or.inr (act_unitTail w i j hsw hiW hij hjW hwz))
  refine BPair.oneValue_trans
    (act_tensor_halfB_null i j v w hlen M1 M2 hl1 hmemB ?_)
    (BPair.oneValue_symm (poly.getAt_unitTail hBu p))
  intro m2 hm2 _ hq
  have hcj : ground.countOf j m2 = 0 := by
    rw [← getAt_contentAt w.content.length m2 j hjW, hq.2, hwz]
  have hpos := act_out_occupied j i (fun he => hij he.symm) M2 m2 hm2
  rw [hcj] at hpos
  exact absurd hpos (Nat.lt_irrefl 0)

private theorem act_tensorH_both (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hij : ¬ i = j)
    (hpv : 0 < ground.getAt 0 v.content j)
    (hpw : 0 < ground.getAt 0 w.content j) :
    poly.oneValue (act i j (tensorH v w)).coords
      (elim.vecAdd (tensorH (act i j v) w).coords
        (tensorH v (act i j w)).coords) := by
  have hTd : (tensorH v w).content.length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hlen.symm
  have hiT : i < (tensorH v w).content.length := by
    rw [hTd]
    exact hi
  have hjT : j < (tensorH v w).content.length := by
    rw [hTd]
    exact hj
  have hiW : i < w.content.length := by
    rw [← hlen]
    exact hi
  have hjW : j < w.content.length := by
    rw [← hlen]
    exact hj
  have hocc : 0 < ground.getAt 0 (tensorH v w).content j := by
    show 0 < ground.getAt 0 (List.zipWith (fun a b => a + b)
      v.content w.content) j
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) v.content w.content j hj hjW]
    exact Nat.lt_of_lt_of_le hpv (Nat.le_add_right _ _)
  have hlenA : (act i j v).content.length = w.content.length := by
    show (moveAt i j v.content).length = w.content.length
    rw [length_moveAt]
    exact hlen
  have hlenB : v.content.length = (act i j w).content.length := by
    show v.content.length = (moveAt i j w.content).length
    rw [length_moveAt]
    exact hlen
  have hcA : (tensorH (act i j v) w).content
      = moveAt i j (tensorH v w).content :=
    moveAt_zipWith_left i j v.content w.content hpv
  have hcB : (tensorH v (act i j w)).content
      = moveAt i j (tensorH v w).content :=
    moveAt_zipWith_right i j v.content w.content hpw
  have hLA : (tensorH (act i j v) w).coords.length
      = (monomialsAt
        (moveAt i j (tensorH v w).content)).length := by
    rw [tensorH_sized (act i j v) w, hcA]
  have hLB : (tensorH v (act i j w)).coords.length
      = (monomialsAt
        (moveAt i j (tensorH v w).content)).length := by
    rw [tensorH_sized v (act i j w), hcB]
  have hLL : (act i j (tensorH v w)).coords.length
      = (monomialsAt (moveAt i j (tensorH v w).content)).length :=
    act_sized i j (tensorH v w)
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [hLL, elim.length_vecAdd _ _
      (monomialsAt (moveAt i j (tensorH v w).content)).length hLA
      hLB]
  · intro p hp
    rw [hLL] at hp
    rw [elim.getAt_vecAdd _ _ p (by rw [hLA]; exact hp)
      (by rw [hLB]; exact hp)]
    have hMl : (ground.getAt []
          (monomialsAt (moveAt i j (tensorH v w).content)) p).length
        = sumNat (tensorH v w).content := by
      rw [(member_conditions (ground.countOf_getAt_pos []
        (monomialsAt (moveAt i j (tensorH v w).content)) p hp)).1]
      exact sumNat_moveAt i j (tensorH v w).content hiT hocc
    match member_split v w hlen _ hMl with
    | ⟨hcat, hl1, hl2⟩ =>
      have houts := act_tensor_outs i j (tensorH v w) hjT hij
        hocc p hp
      rw [hcat] at houts
      refine BPair.oneValue_trans
        (act_tensor_leibniz i j v w hi hj hlen hij hocc p _ _ hp
          hcat) ?_
      exact BPair.add_congr
        (act_tensor_sideA i j v w hsv hsw hlen hi hj hij hpv hlenA
          hcA p _ _ hp hcat hl1 hl2 (act_memA j i _ _ houts))
        (act_tensor_sideB i j v w hsv hsw hlen hiW hjW hij hpw
          hlenB hcB p _ _ hp hcat hl1 hl2 (act_memB j i _ _ houts))

private theorem act_tensorH_leftOnly (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hij : ¬ i = j)
    (hpv : 0 < ground.getAt 0 v.content j)
    (hwz : ground.getAt 0 w.content j = 0) :
    poly.oneValue (act i j (tensorH v w)).coords
      (elim.vecAdd (tensorH (act i j v) w).coords
        (tensorH v (act i j w)).coords) := by
  have hTd : (tensorH v w).content.length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hlen.symm
  have hiT : i < (tensorH v w).content.length := by
    rw [hTd]
    exact hi
  have hjT : j < (tensorH v w).content.length := by
    rw [hTd]
    exact hj
  have hiW : i < w.content.length := by
    rw [← hlen]
    exact hi
  have hjW : j < w.content.length := by
    rw [← hlen]
    exact hj
  have hocc : 0 < ground.getAt 0 (tensorH v w).content j := by
    show 0 < ground.getAt 0 (List.zipWith (fun a b => a + b)
      v.content w.content) j
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) v.content w.content j hj hjW]
    exact Nat.lt_of_lt_of_le hpv (Nat.le_add_right _ _)
  have hlenA : (act i j v).content.length = w.content.length := by
    show (moveAt i j v.content).length = w.content.length
    rw [length_moveAt]
    exact hlen
  have hlenB : v.content.length = (act i j w).content.length := by
    show v.content.length = (moveAt i j w.content).length
    rw [length_moveAt]
    exact hlen
  have hcA : (tensorH (act i j v) w).content
      = moveAt i j (tensorH v w).content :=
    moveAt_zipWith_left i j v.content w.content hpv
  have hcB : (tensorH v (act i j w)).content
      = bumpAt j (moveAt i j (tensorH v w).content) := by
    show List.zipWith (fun a b => a + b) v.content
        (bumpAt i (dipAt j w.content))
      = bumpAt j (bumpAt i (dipAt j (List.zipWith
        (fun a b => a + b) v.content w.content)))
    rw [ground.dipAt_of_zero j w.content hwz,
      bumpAt_zipWith_right i v.content w.content,
      bumpAt_comm j i (dipAt j (List.zipWith (fun a b => a + b)
        v.content w.content)),
      bumpAt_dipAt_self j (List.zipWith (fun a b => a + b)
        v.content w.content) hocc]
  have hLA : (tensorH (act i j v) w).coords.length
      = (monomialsAt
        (moveAt i j (tensorH v w).content)).length := by
    rw [tensorH_sized (act i j v) w, hcA]
  have hLB : (tensorH v (act i j w)).coords.length
      = (monomialsAt (bumpAt j
        (moveAt i j (tensorH v w).content))).length := by
    rw [tensorH_sized v (act i j w), hcB]
  have hLL : (act i j (tensorH v w)).coords.length
      = (monomialsAt (moveAt i j (tensorH v w).content)).length :=
    act_sized i j (tensorH v w)
  have hle : (monomialsAt (moveAt i j (tensorH v w).content)).length
      ≤ (monomialsAt (bumpAt j
        (moveAt i j (tensorH v w).content))).length :=
    places.length_monomialsAt_le_bumpAt j
      (moveAt i j (tensorH v w).content)
      (by rw [length_moveAt]; exact hjT)
  have hAB : (tensorH (act i j v) w).coords.length
      ≤ (tensorH v (act i j w)).coords.length := by
    rw [hLA, hLB]
    exact hle
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [hLL, length_vecAdd_le _ _ hAB, hLA]
  · intro p hp
    rw [hLL] at hp
    rw [elim.getAt_vecAdd _ _ p (by rw [hLA]; exact hp)
      (by rw [hLB]; exact Nat.lt_of_lt_of_le hp hle)]
    have hMl : (ground.getAt []
          (monomialsAt (moveAt i j (tensorH v w).content)) p).length
        = sumNat (tensorH v w).content := by
      rw [(member_conditions (ground.countOf_getAt_pos []
        (monomialsAt (moveAt i j (tensorH v w).content)) p hp)).1]
      exact sumNat_moveAt i j (tensorH v w).content hiT hocc
    match member_split v w hlen _ hMl with
    | ⟨hcat, hl1, hl2⟩ =>
      have houts := act_tensor_outs i j (tensorH v w) hjT hij
        hocc p hp
      rw [hcat] at houts
      refine BPair.oneValue_trans
        (act_tensor_leibniz i j v w hi hj hlen hij hocc p _ _ hp
          hcat) ?_
      exact BPair.add_congr
        (act_tensor_sideA i j v w hsv hsw hlen hi hj hij hpv hlenA
          hcA p _ _ hp hcat hl1 hl2 (act_memA j i _ _ houts))
        (act_tensor_sideB_zero i j v w hsv hsw hlen hiW hjW hij
          hwz hlenB p _ _ hl1 (act_memB j i _ _ houts))

private theorem act_tensorH_rightOnly (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hij : ¬ i = j)
    (hvz : ground.getAt 0 v.content j = 0)
    (hpw : 0 < ground.getAt 0 w.content j) :
    poly.oneValue (act i j (tensorH v w)).coords
      (elim.vecAdd (tensorH (act i j v) w).coords
        (tensorH v (act i j w)).coords) := by
  have hTd : (tensorH v w).content.length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hlen.symm
  have hiT : i < (tensorH v w).content.length := by
    rw [hTd]
    exact hi
  have hjT : j < (tensorH v w).content.length := by
    rw [hTd]
    exact hj
  have hiW : i < w.content.length := by
    rw [← hlen]
    exact hi
  have hjW : j < w.content.length := by
    rw [← hlen]
    exact hj
  have hocc : 0 < ground.getAt 0 (tensorH v w).content j := by
    show 0 < ground.getAt 0 (List.zipWith (fun a b => a + b)
      v.content w.content) j
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) v.content w.content j hj hjW]
    exact Nat.lt_of_lt_of_le hpw (Nat.le_add_left _ _)
  have hlenA : (act i j v).content.length = w.content.length := by
    show (moveAt i j v.content).length = w.content.length
    rw [length_moveAt]
    exact hlen
  have hlenB : v.content.length = (act i j w).content.length := by
    show v.content.length = (moveAt i j w.content).length
    rw [length_moveAt]
    exact hlen
  have hcB : (tensorH v (act i j w)).content
      = moveAt i j (tensorH v w).content :=
    moveAt_zipWith_right i j v.content w.content hpw
  have hcA : (tensorH (act i j v) w).content
      = bumpAt j (moveAt i j (tensorH v w).content) := by
    show List.zipWith (fun a b => a + b)
        (bumpAt i (dipAt j v.content)) w.content
      = bumpAt j (bumpAt i (dipAt j (List.zipWith
        (fun a b => a + b) v.content w.content)))
    rw [ground.dipAt_of_zero j v.content hvz,
      bumpAt_zipWith_left i v.content w.content,
      bumpAt_comm j i (dipAt j (List.zipWith (fun a b => a + b)
        v.content w.content)),
      bumpAt_dipAt_self j (List.zipWith (fun a b => a + b)
        v.content w.content) hocc]
  have hLB : (tensorH v (act i j w)).coords.length
      = (monomialsAt
        (moveAt i j (tensorH v w).content)).length := by
    rw [tensorH_sized v (act i j w), hcB]
  have hLA : (tensorH (act i j v) w).coords.length
      = (monomialsAt (bumpAt j
        (moveAt i j (tensorH v w).content))).length := by
    rw [tensorH_sized (act i j v) w, hcA]
  have hLL : (act i j (tensorH v w)).coords.length
      = (monomialsAt (moveAt i j (tensorH v w).content)).length :=
    act_sized i j (tensorH v w)
  have hle : (monomialsAt (moveAt i j (tensorH v w).content)).length
      ≤ (monomialsAt (bumpAt j
        (moveAt i j (tensorH v w).content))).length :=
    places.length_monomialsAt_le_bumpAt j
      (moveAt i j (tensorH v w).content)
      (by rw [length_moveAt]; exact hjT)
  have hBA : (tensorH v (act i j w)).coords.length
      ≤ (tensorH (act i j v) w).coords.length := by
    rw [hLA, hLB]
    exact hle
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [hLL, length_vecAdd_ge _ _ hBA, hLB]
  · intro p hp
    rw [hLL] at hp
    rw [elim.getAt_vecAdd _ _ p
      (by rw [hLA]; exact Nat.lt_of_lt_of_le hp hle)
      (by rw [hLB]; exact hp)]
    have hMl : (ground.getAt []
          (monomialsAt (moveAt i j (tensorH v w).content)) p).length
        = sumNat (tensorH v w).content := by
      rw [(member_conditions (ground.countOf_getAt_pos []
        (monomialsAt (moveAt i j (tensorH v w).content)) p hp)).1]
      exact sumNat_moveAt i j (tensorH v w).content hiT hocc
    match member_split v w hlen _ hMl with
    | ⟨hcat, hl1, hl2⟩ =>
      have houts := act_tensor_outs i j (tensorH v w) hjT hij
        hocc p hp
      rw [hcat] at houts
      refine BPair.oneValue_trans
        (act_tensor_leibniz i j v w hi hj hlen hij hocc p _ _ hp
          hcat) ?_
      exact BPair.add_congr
        (act_tensor_sideA_zero i j v w hsv hsw hlen hi hj hij hvz
          hlenA p _ _ hl1 (act_memA j i _ _ houts))
        (act_tensor_sideB i j v w hsv hsw hlen hiW hjW hij hpw
          hlenB hcB p _ _ hp hcat hl1 hl2 (act_memB j i _ _ houts))

/-! The Leibniz split at the letter-pair action (`con:units`'
clause, a composite power's fold splitting at the arrangements'
join): the action on a tensor reads the two one-sided actions'
sum. -/

/-- The letter pair's action splits over the tensor
(`con:units`' composite clause): the moved composite's coordinates
read the sum of the two one-sided images, the first factor moved
against the second and the first against the second moved.  The
width binder `hlen` is load-bearing — the ragged pair refuses; the
index binders `hi`, `hj` and the distinctness `hij` are the letter
frame (`con:units`' index frame, the `wordGram` precedent), the
truncating folds off that frame carrying no content. -/
theorem act_tensorH (i j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i < v.content.length) (hj : j < v.content.length)
    (hij : ¬ i = j) :
    poly.oneValue (act i j (tensorH v w)).coords
      (elim.vecAdd (tensorH (act i j v) w).coords
        (tensorH v (act i j w)).coords) := by
  have hTd : (tensorH v w).content.length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hlen.symm
  have hiT : i < (tensorH v w).content.length := by
    rw [hTd]
    exact hi
  have hjT : j < (tensorH v w).content.length := by
    rw [hTd]
    exact hj
  have hiW : i < w.content.length := by
    rw [← hlen]
    exact hi
  have hjW : j < w.content.length := by
    rw [← hlen]
    exact hj
  have hccget : ground.getAt 0 (tensorH v w).content j
      = ground.getAt 0 v.content j + ground.getAt 0 w.content j := by
    show ground.getAt 0 (List.zipWith (fun a b => a + b) v.content
      w.content) j = _
    exact ground.getAt_zipWith 0 0 0 (fun x y => x + y) v.content w.content j hj hjW
  have hlenA : (act i j v).content.length = w.content.length := by
    show (moveAt i j v.content).length = w.content.length
    rw [length_moveAt]
    exact hlen
  have hlenB : v.content.length = (act i j w).content.length := by
    show v.content.length = (moveAt i j w.content).length
    rw [length_moveAt]
    exact hlen
  by_cases hpv : 0 < ground.getAt 0 v.content j
  · by_cases hpw : 0 < ground.getAt 0 w.content j
    · exact act_tensorH_both i j v w hsv hsw hlen hi hj hij hpv hpw
    · exact act_tensorH_leftOnly i j v w hsv hsw hlen hi hj hij hpv
        (Nat.eq_zero_of_not_pos hpw)
  · by_cases hpw : 0 < ground.getAt 0 w.content j
    · exact act_tensorH_rightOnly i j v w hsv hsw hlen hi hj hij
        (Nat.eq_zero_of_not_pos hpv) hpw
    · have hccz : ground.getAt 0 (tensorH v w).content j = 0 := by
        rw [hccget, Nat.eq_zero_of_not_pos hpv, Nat.eq_zero_of_not_pos hpw]
      refine poly.unitTail_oneValue
        (act_unitTail (tensorH v w) i j (tensorH_sized v w) hiT hij
          hjT hccz) ?_
      refine elim.unitTail_vecAdd_of ?_ ?_
      · exact (tensorH_unitTail (act i j v) w (act_sized i j v) hsw
          hlenA).mpr
          (Or.inl (act_unitTail v i j hsv hi hij hj
            (Nat.eq_zero_of_not_pos hpv)))
      · exact (tensorH_unitTail v (act i j w) hsv (act_sized i j w)
          hlenB).mpr
          (Or.inr (act_unitTail w i j hsw hiW hij hjW
            (Nat.eq_zero_of_not_pos hpw)))

/-! The scatter fold's congruence: at one pair of contents the
two coordinate families' one-value reads pass through the guarded
passes, a guard's skip against its partner's summand the unit's
absorption. -/

private theorem hitI_unitP (mu' : List Nat) (k' : Nat)
    (p : List Nat × BPair) (hp : p.2.oneValue BPair.unit) :
    ∀ ql : List (List Nat × BPair),
      (hitI mu' k' p ql).oneValue BPair.unit
  | [] => BPair.oneValue_refl _
  | q :: t => by
    show (if q.2.isUnitRep then hitI mu' k' p t
        else if k' = rankOf (p.1 ++ q.1) mu' then
          p.2 * q.2 + hitI mu' k' p t
        else hitI mu' k' p t).oneValue BPair.unit
    by_cases hq : q.2.isUnitRep = true
    · rw [if_pos hq]
      exact hitI_unitP mu' k' p hp t
    · rw [if_neg hq]
      by_cases hr : k' = rankOf (p.1 ++ q.1) mu'
      · rw [if_pos hr]
        exact BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_trans
              (BPair.mul_congr hp (BPair.oneValue_refl q.2))
              (BPair.unit_mul q.2))
            (hitI_unitP mu' k' p hp t))
          (BPair.unit_add BPair.unit)
      · rw [if_neg hr]
        exact hitI_unitP mu' k' p hp t

private theorem hitI_congr (mu' : List Nat) (k' : Nat)
    (p p' : List Nat × BPair) (hp1 : p.1 = p'.1)
    (hp2 : p.2.oneValue p'.2) :
    ∀ (bs : List (List Nat)) (cs cs' : List BPair),
      cs.length = cs'.length → poly.oneValue cs cs' →
      (hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (hitI mu' k' p'
        (List.zipWith (fun m x => (m, x)) bs cs'))
  | [], _, _, _, _ => BPair.oneValue_refl _
  | _ :: _, [], [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ :: _, hl, _ => nomatch hl
  | _ :: _, _ :: _, [], hl, _ => nomatch hl
  | b :: bs, c :: cs, c' :: cs', hl, h => by
    have hrec := hitI_congr mu' k' p p' hp1 hp2 bs cs cs'
      (Nat.succ.inj hl) h.2
    show (if c.isUnitRep then
        hitI mu' k' p (List.zipWith (fun m x => (m, x)) bs cs)
      else if k' = rankOf (p.1 ++ b) mu' then
        p.2 * c
          + hitI mu' k' p (List.zipWith (fun m x => (m, x)) bs cs)
      else hitI mu' k' p
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (if c'.isUnitRep then
        hitI mu' k' p' (List.zipWith (fun m x => (m, x)) bs cs')
      else if k' = rankOf (p'.1 ++ b) mu' then
        p'.2 * c'
          + hitI mu' k' p'
            (List.zipWith (fun m x => (m, x)) bs cs')
      else hitI mu' k' p'
        (List.zipWith (fun m x => (m, x)) bs cs'))
    rw [← hp1]
    by_cases hc : c.isUnitRep = true
    · rw [if_pos hc]
      by_cases hc' : c'.isUnitRep = true
      · rw [if_pos hc']
        exact hrec
      · rw [if_neg hc']
        have hcu : c'.oneValue BPair.unit := by
          rw [BPair.unit_of_isUnitRep hc] at h
          exact BPair.oneValue_symm h.1
        by_cases hr : k' = rankOf (p.1 ++ b) mu'
        · rw [if_pos hr]
          exact BPair.oneValue_trans hrec
            (BPair.oneValue_symm (BPair.oneValue_trans
              (BPair.add_congr
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl p'.2) hcu)
                  (BPair.mul_unit p'.2))
                (BPair.oneValue_refl _))
              (BPair.unit_add _)))
        · rw [if_neg hr]
          exact hrec
    · rw [if_neg hc]
      by_cases hc' : c'.isUnitRep = true
      · rw [if_pos hc']
        have hcu : c.oneValue BPair.unit := by
          rw [BPair.unit_of_isUnitRep hc'] at h
          exact h.1
        by_cases hr : k' = rankOf (p.1 ++ b) mu'
        · rw [if_pos hr]
          exact BPair.oneValue_trans
            (BPair.oneValue_trans
              (BPair.add_congr
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl p.2) hcu)
                  (BPair.mul_unit p.2))
                (BPair.oneValue_refl _))
              (BPair.unit_add _)) hrec
        · rw [if_neg hr]
          exact hrec
      · rw [if_neg hc']
        by_cases hr : k' = rankOf (p.1 ++ b) mu'
        · rw [if_pos hr, if_pos hr]
          exact BPair.add_congr (BPair.mul_congr hp2 h.1) hrec
        · rw [if_neg hr, if_neg hr]
          exact hrec

private theorem hitO_congr (mu' : List Nat) (k' : Nat)
    (ql ql' : List (List Nat × BPair))
    (hq : ∀ p p' : List Nat × BPair, p.1 = p'.1 →
      p.2.oneValue p'.2 →
      (hitI mu' k' p ql).oneValue (hitI mu' k' p' ql')) :
    ∀ (bs : List (List Nat)) (cs cs' : List BPair),
      cs.length = cs'.length → poly.oneValue cs cs' →
      (hitO mu' k' ql
        (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (hitO mu' k' ql'
        (List.zipWith (fun m x => (m, x)) bs cs'))
  | [], _, _, _, _ => BPair.oneValue_refl _
  | _ :: _, [], [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ :: _, hl, _ => nomatch hl
  | _ :: _, _ :: _, [], hl, _ => nomatch hl
  | b :: bs, c :: cs, c' :: cs', hl, h => by
    have hrec := hitO_congr mu' k' ql ql' hq bs cs cs'
      (Nat.succ.inj hl) h.2
    show (if c.isUnitRep then
        hitO mu' k' ql (List.zipWith (fun m x => (m, x)) bs cs)
      else hitI mu' k' (b, c) ql
        + hitO mu' k' ql
          (List.zipWith (fun m x => (m, x)) bs cs)).oneValue
      (if c'.isUnitRep then
        hitO mu' k' ql' (List.zipWith (fun m x => (m, x)) bs cs')
      else hitI mu' k' (b, c') ql'
        + hitO mu' k' ql'
          (List.zipWith (fun m x => (m, x)) bs cs'))
    by_cases hc : c.isUnitRep = true
    · rw [if_pos hc]
      by_cases hc' : c'.isUnitRep = true
      · rw [if_pos hc']
        exact hrec
      · rw [if_neg hc']
        have hcu : c'.oneValue BPair.unit := by
          rw [BPair.unit_of_isUnitRep hc] at h
          exact BPair.oneValue_symm h.1
        exact BPair.oneValue_trans hrec
          (BPair.oneValue_symm (BPair.oneValue_trans
            (BPair.add_congr (hitI_unitP mu' k' (b, c') hcu ql')
              (BPair.oneValue_refl _))
            (BPair.unit_add _)))
    · rw [if_neg hc]
      by_cases hc' : c'.isUnitRep = true
      · rw [if_pos hc']
        have hcu : c.oneValue BPair.unit := by
          rw [BPair.unit_of_isUnitRep hc'] at h
          exact h.1
        exact BPair.oneValue_trans
          (BPair.oneValue_trans
            (BPair.add_congr (hitI_unitP mu' k' (b, c) hcu ql)
              (BPair.oneValue_refl _))
            (BPair.unit_add _)) hrec
      · rw [if_neg hc']
        exact BPair.add_congr (hq (b, c) (b, c') rfl h.1) hrec

/-- The tensor reads one value in both factors: at one pair of
contents the scattered products read the factors' own, place by
place. -/
theorem tensorH_polyOne : ∀ (v v' w w' : HVec),
    sized v → sized v' → sized w → sized w' →
    v.content = v'.content → w.content = w'.content →
    poly.oneValue v.coords v'.coords →
    poly.oneValue w.coords w'.coords →
    poly.oneValue (tensorH v w).coords (tensorH v' w').coords := by
  intro v v' w w' hsv hsv' hsw hsw' hcv hcw hov how
  have hlv : v.coords.length = v'.coords.length := by
    rw [hsv, hsv', hcv]
  have hlw : w.coords.length = w'.coords.length := by
    rw [hsw, hsw', hcw]
  have hct : (tensorH v w).content = (tensorH v' w').content := by
    show List.zipWith (fun a b => a + b) v.content w.content
      = List.zipWith (fun a b => a + b) v'.content w'.content
    rw [hcv, hcw]
  refine poly.oneValue_of_entries _ _
    (by rw [tensorH_sized v w, tensorH_sized v' w', hct]) ?_
  intro k hk
  rw [tensorH_sized v w] at hk
  have hk2 : k < (monomialsAt (List.zipWith (fun a b => a + b)
      v.content w.content)).length := hk
  have hk3 : k < (monomialsAt (List.zipWith (fun a b => a + b)
      v'.content w'.content)).length := by
    rw [← hcv, ← hcw]
    exact hk2
  refine BPair.oneValue_trans (tensor_getAt v w k hk2)
    (BPair.oneValue_trans ?_
      (BPair.oneValue_symm (tensor_getAt v' w' k hk3)))
  rw [hcv, hcw]
  exact hitO_congr _ k _ _
    (fun p p' hp1 hp2 => hitI_congr _ k p p' hp1 hp2
      (monomialsAt w'.content) w.coords w'.coords hlw how)
    (monomialsAt v'.content) v.coords v'.coords hlv hov

/-! The tensor's regrouping: the three factors' contents add
componentwise in either grouping and the concatenation's own
regrouping aligns the coordinate places. -/

private theorem zipWith_add_assoc : ∀ (a b c : List Nat),
    a.length = b.length → b.length = c.length →
    List.zipWith (fun x y => x + y)
        (List.zipWith (fun x y => x + y) a b) c
      = List.zipWith (fun x y => x + y) a
        (List.zipWith (fun x y => x + y) b c)
  | [], [], [], _, _ => rfl
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h
  | x :: a, y :: b, z :: c, h1, h2 => by
    show (x + y + z) :: List.zipWith (fun x y => x + y)
        (List.zipWith (fun x y => x + y) a b) c
      = (x + (y + z)) :: List.zipWith (fun x y => x + y) a
        (List.zipWith (fun x y => x + y) b c)
    rw [zipWith_add_assoc a b c (Nat.succ.inj h1) (Nat.succ.inj h2),
      Nat.add_assoc]

private theorem tensor_assoc_at (u v w : HVec)
    (hsu : sized u) (hsv : sized v) (hsw : sized w)
    (huv : u.content.length = v.content.length)
    (hvw : v.content.length = w.content.length)
    (k : Nat) (m1 m2 m3 : List Nat)
    (hkL : k
      < (monomialsAt (tensorH (tensorH u v) w).content).length)
    (hkR : k
      < (monomialsAt (tensorH u (tensorH v w)).content).length)
    (hsL : ground.getAt []
        (monomialsAt (tensorH (tensorH u v) w).content) k
      = (m1 ++ m2) ++ m3)
    (hsR : ground.getAt []
        (monomialsAt (tensorH u (tensorH v w)).content) k
      = m1 ++ (m2 ++ m3))
    (h1l : m1.length = sumNat u.content)
    (h2l : m2.length = sumNat v.content)
    (h3l : m3.length = sumNat w.content) :
    (ground.getAt BPair.unit
        (tensorH (tensorH u v) w).coords k).oneValue
      (ground.getAt BPair.unit
        (tensorH u (tensorH v w)).coords k) := by
  have hAl : (tensorH u v).content.length = u.content.length :=
    ground.length_zipWith (fun x y => x + y) u.content v.content u.content.length rfl
      huv.symm
  have hBl : (tensorH v w).content.length = v.content.length :=
    ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length rfl
      hvw.symm
  have hAw : (tensorH u v).content.length = w.content.length := by
    rw [hAl, huv, hvw]
  have huB : u.content.length = (tensorH v w).content.length := by
    rw [hBl, huv]
  have h12l : (m1 ++ m2).length = sumNat (tensorH u v).content := by
    rw [ground.length_append, h1l, h2l]
    exact (sumNat_zipWith_add u.content v.content huv).symm
  have h23l : (m2 ++ m3).length = sumNat (tensorH v w).content := by
    rw [ground.length_append, h2l, h3l]
    exact (sumNat_zipWith_add v.content w.content hvw).symm
  have hLunit : ¬ (content u.content.length m1 = u.content
        ∧ content v.content.length m2 = v.content
        ∧ content w.content.length m3 = w.content) →
      (ground.getAt BPair.unit
        (tensorH (tensorH u v) w).coords k).oneValue BPair.unit := by
    intro hbad
    by_cases h3 : content w.content.length m3 = w.content
    · by_cases h12 : content (tensorH u v).content.length (m1 ++ m2)
          = (tensorH u v).content
      · refine BPair.oneValue_trans
          (tensor_coord_at (tensorH u v) w hAw (tensorH_sized u v)
            hsw k (m1 ++ m2) m3 hkL hsL h12l h12 h3l h3) ?_
        refine BPair.oneValue_trans
          (BPair.mul_congr
            (tensor_coord_null u v huv m1 m2 h12l h12 h1l ?_)
            (BPair.oneValue_refl _))
          (BPair.unit_mul _)
        intro hq1 hq2
        exact hbad ⟨hq1.2, hq2.2, h3⟩
      · exact tensor_coord_at_null (tensorH u v) w hAw k
          (m1 ++ m2) m3 hkL hsL h12l (fun hq1 _ => h12 hq1.2)
    · exact tensor_coord_at_null (tensorH u v) w hAw k
        (m1 ++ m2) m3 hkL hsL h12l (fun _ hq2 => h3 hq2.2)
  have hRunit : ¬ (content u.content.length m1 = u.content
        ∧ content v.content.length m2 = v.content
        ∧ content w.content.length m3 = w.content) →
      (ground.getAt BPair.unit
        (tensorH u (tensorH v w)).coords k).oneValue BPair.unit := by
    intro hbad
    by_cases h1 : content u.content.length m1 = u.content
    · by_cases h23 : content (tensorH v w).content.length (m2 ++ m3)
          = (tensorH v w).content
      · refine BPair.oneValue_trans
          (tensor_coord_at u (tensorH v w) huB hsu
            (tensorH_sized v w) k m1 (m2 ++ m3) hkR hsR h1l h1
            h23l h23) ?_
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (tensor_coord_null v w hvw m2 m3 h23l h23 h2l ?_))
          (BPair.mul_unit _)
        intro hq2 hq3
        exact hbad ⟨h1, hq2.2, hq3.2⟩
      · exact tensor_coord_at_null u (tensorH v w) huB k m1
          (m2 ++ m3) hkR hsR h1l (fun _ hq2 => h23 hq2.2)
    · exact tensor_coord_at_null u (tensorH v w) huB k m1
        (m2 ++ m3) hkR hsR h1l (fun hq1 _ => h1 hq1.2)
  by_cases hall : content u.content.length m1 = u.content
      ∧ content v.content.length m2 = v.content
      ∧ content w.content.length m3 = w.content
  · match hall with
    | ⟨hg1, hg2, hg3⟩ =>
      have h12c : content (tensorH u v).content.length (m1 ++ m2)
          = (tensorH u v).content :=
        (concat_member u.content v.content m1 m2 huv h1l hg1 h2l
          hg2).2
      have h23c : content (tensorH v w).content.length (m2 ++ m3)
          = (tensorH v w).content :=
        (concat_member v.content w.content m2 m3 hvw h2l hg2 h3l
          hg3).2
      have hL : (ground.getAt BPair.unit
          (tensorH (tensorH u v) w).coords k).oneValue
          (coordAt u m1 * coordAt v m2 * coordAt w m3) :=
        BPair.oneValue_trans
          (tensor_coord_at (tensorH u v) w hAw (tensorH_sized u v)
            hsw k (m1 ++ m2) m3 hkL hsL h12l h12c h3l hg3)
          (BPair.mul_congr
            (tensor_coord u v huv hsu hsv m1 m2 h1l hg1 h2l hg2)
            (BPair.oneValue_refl _))
      have hR : (ground.getAt BPair.unit
          (tensorH u (tensorH v w)).coords k).oneValue
          (coordAt u m1 * (coordAt v m2 * coordAt w m3)) :=
        BPair.oneValue_trans
          (tensor_coord_at u (tensorH v w) huB hsu
            (tensorH_sized v w) k m1 (m2 ++ m3) hkR hsR h1l hg1
            h23l h23c)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (tensor_coord v w hvw hsv hsw m2 m3 h2l hg2 h3l hg3))
      rw [← BPair.mul_assoc] at hR
      exact BPair.oneValue_trans hL (BPair.oneValue_symm hR)
  · exact BPair.oneValue_trans (hLunit hall)
      (BPair.oneValue_symm (hRunit hall))

/-- The tensor regroups: three factors at one width give one
content in either grouping, and the coordinates read one value
place by place. -/
theorem tensorH_assoc : ∀ (u v w : HVec),
    sized u → sized v → sized w →
    u.content.length = v.content.length →
    v.content.length = w.content.length →
    (tensorH (tensorH u v) w).content
        = (tensorH u (tensorH v w)).content
      ∧ poly.oneValue (tensorH (tensorH u v) w).coords
          (tensorH u (tensorH v w)).coords := by
  intro u v w hsu hsv hsw huv hvw
  have hAl : (tensorH u v).content.length = u.content.length :=
    ground.length_zipWith (fun x y => x + y) u.content v.content u.content.length rfl
      huv.symm
  have hAw : (tensorH u v).content.length = w.content.length := by
    rw [hAl, huv, hvw]
  have hct : (tensorH (tensorH u v) w).content
      = (tensorH u (tensorH v w)).content :=
    zipWith_add_assoc u.content v.content w.content huv hvw
  refine ⟨hct, ?_⟩
  refine poly.oneValue_of_entries _ _
    (by rw [tensorH_sized (tensorH u v) w,
      tensorH_sized u (tensorH v w), hct]) ?_
  intro k hk
  rw [tensorH_sized (tensorH u v) w] at hk
  have hkR : k
      < (monomialsAt (tensorH u (tensorH v w)).content).length := by
    rw [← hct]
    exact hk
  have hMsum : (ground.getAt []
      (monomialsAt (tensorH (tensorH u v) w).content) k).length
      = sumNat u.content
        + (sumNat v.content + sumNat w.content) := by
    rw [(member_conditions (ground.countOf_getAt_pos []
      (monomialsAt (tensorH (tensorH u v) w).content) k hk)).1]
    show sumNat (List.zipWith (fun a b => a + b)
        (tensorH u v).content w.content) = _
    rw [sumNat_zipWith_add (tensorH u v).content w.content hAw,
      show sumNat (tensorH u v).content
          = sumNat u.content + sumNat v.content from
        sumNat_zipWith_add u.content v.content huv,
      Nat.add_assoc]
  match split_lengths _ _ _ hMsum with
  | ⟨hcat1, hp1l, hrestl⟩ =>
    match split_lengths _ _ _ hrestl with
    | ⟨hcat2, hp2l, hp3l⟩ =>
      refine tensor_assoc_at u v w hsu hsv hsw huv hvw k _ _ _
        hk hkR ?_ ?_ hp1l hp2l hp3l
      · rw [ground.append_assoc, ← hcat2]
        exact hcat1
      · rw [← hct, ← hcat2]
        exact hcat1

/-! The wedge-tensored lowering: the Leibniz sum splits over the
concatenation, the wedge half joining at the unit and the second
half rebuilding the second factor's own lowering. -/

private theorem tensorW_out_v (d : Nat) (v : HVec)
    (hvd : v.content.length = d)
    (t1 : List Nat)
    (h1 : t1.length = sumNat (wedge d d).content)
    (hg1 : content (wedge d d).content.length t1
      = (wedge d d).content)
    (m2 : List Nat)
    (hlm : (t1 ++ m2).length
        = sumNat (tensorH (wedge d d) v).content
      ∧ content (tensorH (wedge d d) v).content.length (t1 ++ m2)
        = (tensorH (wedge d d) v).content) :
    m2.length = sumNat v.content
      ∧ content v.content.length m2 = v.content := by
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  have hd : (tensorH (wedge d d) v).content.length
      = (wedge d d).content.length :=
    ground.length_zipWith (fun x y => x + y) (wedge d d).content v.content
      (wedge d d).content.length rfl hlen.symm
  refine ⟨?_, ?_⟩
  · have hl := hlm.1
    rw [ground.length_append, h1,
      show sumNat (tensorH (wedge d d) v).content
          = sumNat (wedge d d).content + sumNat v.content from
        sumNat_zipWith_add (wedge d d).content v.content hlen] at hl
    refine ground.addCancelR (sumNat (wedge d d).content) ?_
    rw [Nat.add_comm m2.length, Nat.add_comm (sumNat v.content)]
    exact hl
  · have hc := hlm.2
    rw [hd, content_append (wedge d d).content.length t1 m2,
      hg1] at hc
    have hcm : content (wedge d d).content.length m2
        = v.content := by
      refine zipWith_add_cancelL (wedge d d).content
        (content (wedge d d).content.length m2) v.content
        (wedge d d).content.length rfl ?_ hlen.symm hc
      exact ground.length_mapRange _ (wedge d d).content.length
    rw [← hlen]
    exact hcm

private theorem tensorW_lower_first (d j : Nat) (hj : j + 1 < d)
    (v : HVec) (hsv : sized v) (hvd : v.content.length = d)
    (t1 t2 : List Nat)
    (h1 : t1.length = sumNat (wedge d d).content)
    (h2 : t2.length = sumNat v.content)
    (hmemA : ∀ m1, 0 < ground.countOf m1
        (units.unitAct j (j + 1) t1) →
      (m1 ++ t2).length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length (m1 ++ t2)
          = (tensorH (wedge d d) v).content) :
    (ground.bsum (coordAt (tensorH (wedge d d) v))
      ((units.unitAct j (j + 1) t1).map
        (fun m => m ++ t2))).oneValue BPair.unit := by
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  have hd : (tensorH (wedge d d) v).content.length
      = (wedge d d).content.length :=
    ground.length_zipWith (fun x y => x + y) (wedge d d).content v.content
      (wedge d d).content.length rfl hlen.symm
  rw [ground.bsum_map]
  by_cases h2m : content v.content.length t2 = v.content
  · have hm1c : ∀ m1, 0 < ground.countOf m1
        (units.unitAct j (j + 1) t1) →
        m1.length = sumNat (wedge d d).content
          ∧ content (wedge d d).content.length m1
            = (wedge d d).content := by
      intro m1 hm1
      refine ⟨(units.length_unitAct_out j (j + 1) t1 m1 hm1).trans
        h1, ?_⟩
      have hc := (hmemA m1 hm1).2
      have ht2c : content (wedge d d).content.length t2
          = v.content := by
        rw [hlen]
        exact h2m
      rw [hd, content_append (wedge d d).content.length m1 t2,
        ht2c] at hc
      refine zipWith_add_cancelR
        (content (wedge d d).content.length m1)
        (wedge d d).content v.content
        (wedge d d).content.length ?_ rfl hlen.symm hc
      exact ground.length_mapRange _ (wedge d d).content.length
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun m1 => coordAt (wedge d d) m1 * coordAt v t2)
        (units.unitAct j (j + 1) t1)
        (fun m1 hm1 => tensor_coord (wedge d d) v hlen
          (wedge_sized d d) hsv m1 t2 (hm1c m1 hm1).1
          (hm1c m1 hm1).2 h2 h2m)) ?_
    exact BPair.oneValue_trans
      (bsum_mulR (coordAt (wedge d d)) (coordAt v t2) _)
      (BPair.oneValue_trans
        (BPair.mul_congr (wedge_lowerNull d j hj t1 hm1c)
          (BPair.oneValue_refl _))
        (BPair.unit_mul _))
  · refine ground.foldB_null _ _ ?_
    intro m1 hm1
    refine tensor_coord_null (wedge d d) v hlen m1 t2
      (hmemA m1 hm1).1 (hmemA m1 hm1).2
      ((units.length_unitAct_out j (j + 1) t1 m1 hm1).trans h1) ?_
    intro _ hq
    exact h2m hq.2

private theorem tensorW_second_null (d j : Nat) (v : HVec)
    (hvd : v.content.length = d)
    (t1 t2 : List Nat)
    (h1 : t1.length = sumNat (wedge d d).content)
    (hg1 : ¬ content (wedge d d).content.length t1
      = (wedge d d).content)
    (hmemB : ∀ m2, 0 < ground.countOf m2
        (units.unitAct j (j + 1) t2) →
      (t1 ++ m2).length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length (t1 ++ m2)
          = (tensorH (wedge d d) v).content) :
    (ground.bsum (coordAt (tensorH (wedge d d) v))
      ((units.unitAct j (j + 1) t2).map
        (fun m => t1 ++ m))).oneValue BPair.unit := by
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  rw [ground.bsum_map]
  refine ground.foldB_null _ _ ?_
  intro m2 hm2
  refine tensor_coord_null (wedge d d) v hlen t1 m2
    (hmemB m2 hm2).1 (hmemB m2 hm2).2 h1 ?_
  intro hp _
  exact hg1 hp.2

private theorem tensorW_memA (d j : Nat) (v : HVec)
    (t1 t2 : List Nat)
    (hmem : ∀ m, 0 < ground.countOf m
        (units.unitAct j (j + 1) (t1 ++ t2)) →
      m.length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length m
          = (tensorH (wedge d d) v).content) :
    ∀ m1, 0 < ground.countOf m1 (units.unitAct j (j + 1) t1) →
      (m1 ++ t2).length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length (m1 ++ t2)
          = (tensorH (wedge d d) v).content := by
  intro m1 hm1
  refine hmem (m1 ++ t2) ?_
  rw [units.unitAct_append j (j + 1) t1 t2, ground.countOf_append]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
  exact countOf_map_pos (fun m => m ++ t2) m1
    (units.unitAct j (j + 1) t1) hm1

private theorem tensorW_memB (d j : Nat) (v : HVec)
    (t1 t2 : List Nat)
    (hmem : ∀ m, 0 < ground.countOf m
        (units.unitAct j (j + 1) (t1 ++ t2)) →
      m.length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length m
          = (tensorH (wedge d d) v).content) :
    ∀ m2, 0 < ground.countOf m2 (units.unitAct j (j + 1) t2) →
      (t1 ++ m2).length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length (t1 ++ m2)
          = (tensorH (wedge d d) v).content := by
  intro m2 hm2
  refine hmem (t1 ++ m2) ?_
  rw [units.unitAct_append j (j + 1) t1 t2, ground.countOf_append]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
  exact countOf_map_pos (fun m => t1 ++ m) m2
    (units.unitAct j (j + 1) t2) hm2

private theorem tensorW_lower_unit (d j : Nat) (hj : j + 1 < d)
    (v : HVec) (hsv : sized v) (hvd : v.content.length = d)
    (hvac : ground.getAt 0 v.content j = 0)
    (t1 t2 : List Nat)
    (h1 : t1.length = sumNat (wedge d d).content)
    (h2 : t2.length = sumNat v.content)
    (hmem : ∀ m, 0 < ground.countOf m
        (units.unitAct j (j + 1) (t1 ++ t2)) →
      m.length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length m
          = (tensorH (wedge d d) v).content) :
    (ground.bsum (coordAt (tensorH (wedge d d) v))
      (units.unitAct j (j + 1) (t1 ++ t2))).oneValue
      BPair.unit := by
  have hjd : j < d :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  have hB : (ground.bsum (coordAt (tensorH (wedge d d) v))
      ((units.unitAct j (j + 1) t2).map
        (fun m => t1 ++ m))).oneValue BPair.unit := by
    by_cases hg1 : content (wedge d d).content.length t1
        = (wedge d d).content
    · rw [ground.bsum_map]
      refine ground.foldB_null _ _ ?_
      intro m2 hm2
      exfalso
      have hmv := tensorW_out_v d v hvd t1 h1 hg1 m2
        (tensorW_memB d j v t1 t2 hmem m2 hm2)
      have hcj : ground.countOf j m2 = 0 := by
        rw [← getAt_contentAt v.content.length m2 j
          (by rw [hvd]; exact hjd), hmv.2, hvac]
      have ho := units.countOf_unitAct_out j (j + 1) j t2 m2 hm2
      rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_self j)), if_pos rfl, Nat.add_zero, hcj]
        at ho
      exact Nat.noConfusion ho
    · exact tensorW_second_null d j v hvd t1 t2 h1 hg1
        (tensorW_memB d j v t1 t2 hmem)
  rw [units.unitAct_append j (j + 1) t1 t2]
  exact BPair.oneValue_trans
    (ground.famFold_append_ov ground.bpairFoldLaws _ _ _)
    (BPair.oneValue_trans
      (BPair.add_congr (tensorW_lower_first d j hj v hsv hvd t1 t2
        h1 h2 (tensorW_memA d j v t1 t2 hmem)) hB)
      (BPair.unit_add BPair.unit))

/-- The wedge-tensored lowering at a vacant letter reads the sum's
unit: the wedge half joins at the unit and the second factor has no
source for the moved letter. -/
theorem lowerH_tensorW_vacant : ∀ (d j : Nat) (v : HVec),
    sized v → v.content.length = d → j + 1 < d →
    ground.getAt 0 v.content j = 0 →
    ∃ u, lowerH j (tensorH (wedge d d) v) = some u
      ∧ poly.unitTail u.coords := by
  intro d j v hsv hvd hj hvac
  have hjd : j < d :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  have hTl : (tensorH (wedge d d) v).content.length = d :=
    ground.length_zipWith (fun x y => x + y) (wedge d d).content v.content d
      (wedge_clen d d) hvd
  have hocc : 0 < ground.getAt 0
      (tensorH (wedge d d) v).content j := by
    show 0 < ground.getAt 0 (List.zipWith (fun a b => a + b)
      (wedge d d).content v.content) j
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) (wedge d d).content v.content j
        (by rw [wedge_clen d d]; exact hjd)
        (by rw [hvd]; exact hjd),
      wedge_full_get d j hjd, hvac]
    exact Nat.succ_pos 0
  have hjlen : j + 1 < (tensorH (wedge d d) v).content.length := by
    rw [hTl]
    exact hj
  have hsome : lowerH j (tensorH (wedge d d) v)
      = some ⟨units.moveDn j (tensorH (wedge d d) v).content,
        elim.matVec (units.matUnitAt
          (units.moveDn j (tensorH (wedge d d) v).content)
          (tensorH (wedge d d) v).content (j + 1) j)
          (tensorH (wedge d d) v).coords⟩ :=
    if_pos hocc
  refine ⟨_, hsome, ?_⟩
  show poly.unitTail (elim.matVec (units.matUnitAt
    (units.moveDn j (tensorH (wedge d d) v).content)
    (tensorH (wedge d d) v).content (j + 1) j)
    (tensorH (wedge d d) v).coords)
  refine elim.unitTail_of_getAt _ ?_
  intro p hp
  rw [lowerH_length (tensorH (wedge d d) v) j] at hp
  have houts : ∀ m, 0 < ground.countOf m
      (units.unitAct j (j + 1)
        (ground.getAt [] (monomialsAt (units.moveDn j
          (tensorH (wedge d d) v).content)) p)) →
      m.length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length m
          = (tensorH (wedge d d) v).content :=
    fun m hm => lower_out_rev (tensorH (wedge d d) v).content j
      hjlen hocc _ m (ground.countOf_getAt_pos []
        (monomialsAt (units.moveDn j
          (tensorH (wedge d d) v).content)) p hp) hm
  have hTp : (ground.getAt [] (monomialsAt (units.moveDn j
        (tensorH (wedge d d) v).content)) p).length
      = sumNat (tensorH (wedge d d) v).content := by
    rw [(member_conditions (ground.countOf_getAt_pos []
      (monomialsAt (units.moveDn j
        (tensorH (wedge d d) v).content)) p hp)).1]
    exact units.sumNat_moveDn j (tensorH (wedge d d) v).content hjlen hocc
  refine BPair.oneValue_trans
    (lowerH_entry (tensorH (wedge d d) v) j p
      (tensorH_sized (wedge d d) v) hjlen hocc hp) ?_
  match member_split (wedge d d) v hlen _ hTp with
  | ⟨hcat, hl1, hl2⟩ =>
    rw [hcat] at houts ⊢
    exact tensorW_lower_unit d j hj v hsv hvd hvac _ _ hl1 hl2 houts

/-! The occupied letter's read: the moved content splits off the
wedge's own, and the second half rebuilds the second factor's
lowering image. -/

private theorem moveDn_zipWith (j : Nat) (a b : List Nat)
    (hab : a.length = b.length) (hj : j + 1 < b.length)
    (hocc : 0 < ground.getAt 0 b j) :
    units.moveDn j (List.zipWith (fun x y => x + y) a b)
      = List.zipWith (fun x y => x + y) a (units.moveDn j b) := by
  have hjb : j < b.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  have hja : j < a.length := by
    rw [hab]
    exact hjb
  have hj1a : j + 1 < a.length := by
    rw [hab]
    exact hj
  have hjm : j < (units.moveDn j b).length := by
    rw [units.length_moveDn]
    exact hjb
  have hj1m : j + 1 < (units.moveDn j b).length := by
    rw [units.length_moveDn]
    exact hj
  have hz : (List.zipWith (fun x y => x + y) a b).length
      = b.length := ground.length_zipWith (fun x y => x + y) a b b.length hab rfl
  have hz2 : (List.zipWith (fun x y => x + y) a
      (units.moveDn j b)).length = b.length :=
    ground.length_zipWith (fun x y => x + y) a (units.moveDn j b) b.length hab
      (units.length_moveDn j b)
  have hoccz : 0 < ground.getAt 0
      (List.zipWith (fun x y => x + y) a b) j := by
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) a b j hja hjb]
    exact Nat.lt_of_lt_of_le hocc (Nat.le_add_left _ _)
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [units.length_moveDn, hz, hz2]
  · intro x hx
    rw [units.length_moveDn, hz] at hx
    have hxa : x < a.length := by
      rw [hab]
      exact hx
    have hxm : x < (units.moveDn j b).length := by
      rw [units.length_moveDn]
      exact hx
    by_cases hxj : x = j
    · rw [hxj]
      refine ground.addCancelR 1 ?_
      rw [getAt_moveDn_self j
          (List.zipWith (fun x y => x + y) a b) hoccz,
        ground.getAt_zipWith 0 0 0 (fun x y => x + y) a b j hja hjb,
        ground.getAt_zipWith 0 0 0 (fun x y => x + y) a (units.moveDn j b) j hja hjm,
        Nat.add_assoc, getAt_moveDn_self j b hocc]
    · by_cases hxj1 : x = j + 1
      · rw [hxj1,
          units.getAt_moveDn_next j (List.zipWith (fun x y => x + y) a b)
            (by rw [hz]; exact hj),
          ground.getAt_zipWith 0 0 0 (fun x y => x + y) a b (j + 1) hj1a hj,
          ground.getAt_zipWith 0 0 0 (fun x y => x + y) a (units.moveDn j b) (j + 1) hj1a hj1m,
          units.getAt_moveDn_next j b hj, Nat.add_assoc]
      · rw [units.getAt_moveDn_ne j (List.zipWith (fun x y => x + y) a b)
            x hxj hxj1,
          ground.getAt_zipWith 0 0 0 (fun x y => x + y) a b x hxa hx,
          ground.getAt_zipWith 0 0 0 (fun x y => x + y) a (units.moveDn j b) x hxa hxm,
          units.getAt_moveDn_ne j b x hxj hxj1]

private theorem lower_src_content (mu : List Nat) (j : Nat)
    (hj : j + 1 < mu.length) (hocc : 0 < ground.getAt 0 mu j)
    (t m : List Nat) (hml : m.length = sumNat mu)
    (hmc : content mu.length m = mu)
    (hm : 0 < ground.countOf m (units.unitAct j (j + 1) t)) :
    t.length = sumNat (units.moveDn j mu)
      ∧ content (units.moveDn j mu).length t
        = units.moveDn j mu := by
  have hd : (units.moveDn j mu).length = mu.length :=
    units.length_moveDn j mu
  refine ⟨?_, ?_⟩
  · rw [← units.length_unitAct_out j (j + 1) t m hm, hml,
      units.sumNat_moveDn j mu hj hocc]
  · rw [hd]
    refine content_eq_of_entries mu.length t (units.moveDn j mu)
      hd ?_
    intro x hx
    have hcnt := units.countOf_unitAct_out j (j + 1) x t m hm
    have hmx : ground.countOf x m = ground.getAt 0 mu x := by
      rw [← getAt_contentAt mu.length m x hx, hmc]
    rw [hmx] at hcnt
    by_cases hxj : x = j
    · rw [hxj] at hcnt ⊢
      rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_self j)), if_pos rfl, Nat.add_zero] at hcnt
      refine ground.addCancelR 1 ?_
      rw [← hcnt, getAt_moveDn_self j mu hocc]
    · by_cases hxj1 : x = j + 1
      · rw [hxj1] at hcnt ⊢
        rw [if_pos rfl, if_neg (fun he => Nat.ne_of_lt (Nat.lt_succ_self j) he.symm)]
          at hcnt
        rw [units.getAt_moveDn_next j mu hj, hcnt]
        exact (Nat.add_zero _).symm
      · rw [if_neg hxj1, if_neg hxj, Nat.add_zero, Nat.add_zero]
          at hcnt
        rw [units.getAt_moveDn_ne j mu x hxj hxj1, hcnt]

private theorem tensorW_second_good (d j : Nat) (v : HVec)
    (hsv : sized v) (hvd : v.content.length = d)
    (t1 t2 : List Nat)
    (h1 : t1.length = sumNat (wedge d d).content)
    (hg1 : content (wedge d d).content.length t1
      = (wedge d d).content)
    (hmemB : ∀ m2, 0 < ground.countOf m2
        (units.unitAct j (j + 1) t2) →
      (t1 ++ m2).length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length (t1 ++ m2)
          = (tensorH (wedge d d) v).content) :
    (ground.bsum (coordAt (tensorH (wedge d d) v))
      ((units.unitAct j (j + 1) t2).map
        (fun m => t1 ++ m))).oneValue
      (coordAt (wedge d d) t1
        * ground.bsum (coordAt v) (units.unitAct j (j + 1) t2)) := by
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  rw [ground.bsum_map]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun m2 => coordAt (wedge d d) t1 * coordAt v m2)
      (units.unitAct j (j + 1) t2)
      (fun m2 hm2 => tensor_coord (wedge d d) v hlen
        (wedge_sized d d) hsv t1 m2 h1 hg1
        (tensorW_out_v d v hvd t1 h1 hg1 m2 (hmemB m2 hm2)).1
        (tensorW_out_v d v hvd t1 h1 hg1 m2 (hmemB m2 hm2)).2)) ?_
  exact ground.foldB_mul_left (coordAt (wedge d d) t1) (coordAt v) _

private theorem tensorW_lower_coords (d j : Nat) (hj : j + 1 < d)
    (v u' : HVec) (hsv : sized v) (hvd : v.content.length = d)
    (hoccv : 0 < ground.getAt 0 v.content j)
    (hu'c : u'.content = units.moveDn j v.content)
    (hu'x : u'.coords = elim.matVec (units.matUnitAt
      (units.moveDn j v.content) v.content (j + 1) j) v.coords) :
    poly.oneValue
      (elim.matVec (units.matUnitAt
        (units.moveDn j (tensorH (wedge d d) v).content)
        (tensorH (wedge d d) v).content (j + 1) j)
        (tensorH (wedge d d) v).coords)
      (tensorH (wedge d d) u').coords := by
  have hjd : j < d :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  have hjv : j + 1 < v.content.length := by
    rw [hvd]
    exact hj
  have hTl : (tensorH (wedge d d) v).content.length = d :=
    ground.length_zipWith (fun x y => x + y) (wedge d d).content v.content d
      (wedge_clen d d) hvd
  have hjlen : j + 1 < (tensorH (wedge d d) v).content.length := by
    rw [hTl]
    exact hj
  have hoccT : 0 < ground.getAt 0
      (tensorH (wedge d d) v).content j := by
    show 0 < ground.getAt 0 (List.zipWith (fun a b => a + b)
      (wedge d d).content v.content) j
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) (wedge d d).content v.content j
      (by rw [wedge_clen d d]; exact hjd) (by rw [hvd]; exact hjd)]
    exact Nat.lt_of_lt_of_le hoccv (Nat.le_add_left _ _)
  have hmv : units.moveDn j (tensorH (wedge d d) v).content
      = (tensorH (wedge d d) u').content := by
    show units.moveDn j (List.zipWith (fun a b => a + b)
        (wedge d d).content v.content)
      = List.zipWith (fun a b => a + b) (wedge d d).content
        u'.content
    rw [hu'c]
    exact moveDn_zipWith j (wedge d d).content v.content hlen hjv
      hoccv
  have hsu' : sized u' := by
    show u'.coords.length = (monomialsAt u'.content).length
    rw [hu'x, hu'c]
    exact lowerH_length v j
  have hlenWu' : (wedge d d).content.length = u'.content.length := by
    rw [hu'c, units.length_moveDn]
    exact hlen
  have hsumu : sumNat u'.content = sumNat v.content := by
    rw [hu'c]
    exact units.sumNat_moveDn j v.content hjv hoccv
  refine poly.oneValue_of_entries _ _
    (by rw [lowerH_length (tensorH (wedge d d) v) j,
      tensorH_sized (wedge d d) u', hmv]) ?_
  intro p hp
  rw [lowerH_length (tensorH (wedge d d) v) j] at hp
  have hkR : p
      < (monomialsAt (tensorH (wedge d d) u').content).length := by
    rw [← hmv]
    exact hp
  have houts : ∀ m, 0 < ground.countOf m
      (units.unitAct j (j + 1)
        (ground.getAt [] (monomialsAt (units.moveDn j
          (tensorH (wedge d d) v).content)) p)) →
      m.length = sumNat (tensorH (wedge d d) v).content
        ∧ content (tensorH (wedge d d) v).content.length m
          = (tensorH (wedge d d) v).content :=
    fun m hm => lower_out_rev (tensorH (wedge d d) v).content j
      hjlen hoccT _ m (ground.countOf_getAt_pos []
        (monomialsAt (units.moveDn j
          (tensorH (wedge d d) v).content)) p hp) hm
  have hTp : (ground.getAt [] (monomialsAt (units.moveDn j
        (tensorH (wedge d d) v).content)) p).length
      = sumNat (tensorH (wedge d d) v).content := by
    rw [(member_conditions (ground.countOf_getAt_pos []
      (monomialsAt (units.moveDn j
        (tensorH (wedge d d) v).content)) p hp)).1]
    exact units.sumNat_moveDn j (tensorH (wedge d d) v).content hjlen
      hoccT
  refine BPair.oneValue_trans
    (lowerH_entry (tensorH (wedge d d) v) j p
      (tensorH_sized (wedge d d) v) hjlen hoccT hp) ?_
  match member_split (wedge d d) v hlen _ hTp with
  | ⟨hcat, hl1, hl2⟩ =>
    have hsplitR : ground.getAt []
        (monomialsAt (tensorH (wedge d d) u').content) p
        = List.take (sumNat (wedge d d).content)
            (ground.getAt [] (monomialsAt (units.moveDn j
              (tensorH (wedge d d) v).content)) p)
          ++ List.drop (sumNat (wedge d d).content)
            (ground.getAt [] (monomialsAt (units.moveDn j
              (tensorH (wedge d d) v).content)) p) := by
      rw [← hmv]
      exact hcat
    have hl2' : (List.drop (sumNat (wedge d d).content)
        (ground.getAt [] (monomialsAt (units.moveDn j
          (tensorH (wedge d d) v).content)) p)).length
        = sumNat u'.content := by
      rw [hsumu]
      exact hl2
    rw [hcat] at houts
    rw [hcat, units.unitAct_append j (j + 1) _ _]
    refine BPair.oneValue_trans
      (ground.famFold_append_ov ground.bpairFoldLaws _ _ _) ?_
    have hA := tensorW_lower_first d j hj v hsv hvd _ _ hl1 hl2
      (tensorW_memA d j v _ _ houts)
    by_cases hg1 : content (wedge d d).content.length
        (List.take (sumNat (wedge d d).content)
          (ground.getAt [] (monomialsAt (units.moveDn j
            (tensorH (wedge d d) v).content)) p))
        = (wedge d d).content
    · by_cases hg2 : content u'.content.length
          (List.drop (sumNat (wedge d d).content)
            (ground.getAt [] (monomialsAt (units.moveDn j
              (tensorH (wedge d d) v).content)) p))
          = u'.content
      · have hg2' : content (units.moveDn j v.content).length
            (List.drop (sumNat (wedge d d).content)
              (ground.getAt [] (monomialsAt (units.moveDn j
                (tensorH (wedge d d) v).content)) p))
            = units.moveDn j v.content := by
          rw [← hu'c]
          exact hg2
        have hl2'' : (List.drop (sumNat (wedge d d).content)
            (ground.getAt [] (monomialsAt (units.moveDn j
              (tensorH (wedge d d) v).content)) p)).length
            = sumNat (units.moveDn j v.content) := by
          rw [units.sumNat_moveDn j v.content hjv hoccv]
          exact hl2
        have hrr := rankOf_read _ (units.moveDn j v.content) hl2''
          hg2'
        have hcu : (coordAt u' (List.drop (sumNat (wedge d d).content)
            (ground.getAt [] (monomialsAt (units.moveDn j
              (tensorH (wedge d d) v).content)) p))).oneValue
            (ground.bsum (coordAt v) (units.unitAct j (j + 1)
              (List.drop (sumNat (wedge d d).content)
                (ground.getAt [] (monomialsAt (units.moveDn j
                  (tensorH (wedge d d) v).content)) p)))) := by
          show (ground.getAt BPair.unit u'.coords
            (rankOf _ u'.content)).oneValue _
          rw [hu'x, hu'c]
          have hh := lowerH_entry v j (rankOf _
            (units.moveDn j v.content)) hsv hjv hoccv hrr.1
          rw [hrr.2] at hh
          exact hh
        have hB := tensorW_second_good d j v hsv hvd _ _ hl1 hg1
          (tensorW_memB d j v _ _ houts)
        have hR := tensor_coord_at (wedge d d) u' hlenWu'
          (wedge_sized d d) hsu' p _ _ hkR hsplitR hl1 hg1 hl2' hg2
        exact BPair.oneValue_trans
          (BPair.oneValue_trans (BPair.add_congr hA hB)
            (BPair.unit_add _))
          (BPair.oneValue_symm (BPair.oneValue_trans hR
            (BPair.mul_congr (BPair.oneValue_refl _) hcu)))
      · have hB : (ground.bsum (coordAt (tensorH (wedge d d) v))
            ((units.unitAct j (j + 1)
              (List.drop (sumNat (wedge d d).content)
                (ground.getAt [] (monomialsAt (units.moveDn j
                  (tensorH (wedge d d) v).content)) p))).map
              (fun m => List.take (sumNat (wedge d d).content)
                (ground.getAt [] (monomialsAt (units.moveDn j
                  (tensorH (wedge d d) v).content)) p)
                ++ m))).oneValue BPair.unit := by
          rw [ground.bsum_map]
          refine ground.foldB_null _ _ ?_
          intro m2 hm2
          exfalso
          have hmv2 := tensorW_out_v d v hvd _ hl1 hg1 m2
            (tensorW_memB d j v _ _ houts m2 hm2)
          have hsrc := lower_src_content v.content j hjv hoccv _ m2
            hmv2.1 hmv2.2 hm2
          refine hg2 ?_
          rw [hu'c]
          exact hsrc.2
        exact BPair.oneValue_trans
          (BPair.oneValue_trans (BPair.add_congr hA hB)
            (BPair.unit_add _))
          (BPair.oneValue_symm
            (tensor_coord_at_null (wedge d d) u' hlenWu' p _ _ hkR
              hsplitR hl1 (fun _ hq => hg2 hq.2)))
    · have hB := tensorW_second_null d j v hvd _ _ hl1 hg1
        (tensorW_memB d j v _ _ houts)
      exact BPair.oneValue_trans
        (BPair.oneValue_trans (BPair.add_congr hA hB)
          (BPair.unit_add _))
        (BPair.oneValue_symm
          (tensor_coord_at_null (wedge d d) u' hlenWu' p _ _ hkR
            hsplitR hl1 (fun hq _ => hg1 hq.2)))

/-- The wedge-tensored lowering at an occupied letter: the moved
content is the wedge tensored with the second factor's moved
content, and the coordinates read the tensored lowering image. -/
theorem lowerH_tensorW : ∀ (d j : Nat) (v : HVec),
    sized v → v.content.length = d → j + 1 < d →
    0 < ground.getAt 0 v.content j →
    ∃ u u', lowerH j (tensorH (wedge d d) v) = some u
      ∧ lowerH j v = some u'
      ∧ u.content = (tensorH (wedge d d) u').content
      ∧ poly.oneValue u.coords (tensorH (wedge d d) u').coords := by
  intro d j v hsv hvd hj hoccv
  have hjd : j < d :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_of_lt hj)
  have hlen : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hvd]
  have hjv : j + 1 < v.content.length := by
    rw [hvd]
    exact hj
  have hoccT : 0 < ground.getAt 0
      (tensorH (wedge d d) v).content j := by
    show 0 < ground.getAt 0 (List.zipWith (fun a b => a + b)
      (wedge d d).content v.content) j
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) (wedge d d).content v.content j
      (by rw [wedge_clen d d]; exact hjd) (by rw [hvd]; exact hjd)]
    exact Nat.lt_of_lt_of_le hoccv (Nat.le_add_left _ _)
  refine ⟨_, _, if_pos hoccT, if_pos hoccv, ?_,
    tensorW_lower_coords d j hj v _ hsv hvd hoccv rfl rfl⟩
  exact moveDn_zipWith j (wedge d d).content v.content hlen hjv
    hoccv

/-! The full column's addition: the scalar seed is unital at either
side, the fold transports one-value data, and the wedge pulls out
of the exhibit's fold by the regrouping. -/

private theorem hvec_trans {a b c : HVec}
    (h1 : a.content = b.content ∧ poly.oneValue a.coords b.coords)
    (h2 : b.content = c.content ∧ poly.oneValue b.coords c.coords) :
    a.content = c.content ∧ poly.oneValue a.coords c.coords :=
  ⟨h1.1.trans h2.1, poly.oneValue_trans h1.2 h2.2⟩

private theorem zipWith_zero_right : ∀ (n : Nat) (b : List Nat),
    b.length = n →
    List.zipWith (fun x y => x + y) b (List.replicate n 0) = b
  | 0, [], _ => rfl
  | 0, _ :: _, h => nomatch h
  | _ + 1, [], h => nomatch h
  | n + 1, c :: t, h => by
    show (c + 0) :: List.zipWith (fun x y => x + y) t
      (List.replicate n 0) = c :: t
    rw [zipWith_zero_right n t (Nat.succ.inj h), Nat.add_zero]

private theorem content_nil_replicate (d : Nat) :
    content d ([] : List Nat) = List.replicate d 0 := by
  show (List.range d).map
    (fun i => ground.countOf i ([] : List Nat))
    = List.replicate d 0
  rw [ground.map_congr_all
    (fun i => ground.countOf i ([] : List Nat))
    (fun _ => (0 : Nat)) (fun _ => rfl) (List.range d)]
  exact map_zero_range d

private theorem seed_sized (d : Nat) :
    sized (⟨List.replicate d 0, [BPair.ofNat 1]⟩ : HVec) := by
  show (1 : Nat) = (monomialsAt (List.replicate d 0)).length
  rw [places.monomialsAt_sum_zero _ (sumNat_replicate_zero d)]
  rfl

private theorem seed_nil_reads (d : Nat) :
    ([] : List Nat).length
        = sumNat (⟨List.replicate d 0,
          [BPair.ofNat 1]⟩ : HVec).content
      ∧ content (⟨List.replicate d 0,
          [BPair.ofNat 1]⟩ : HVec).content.length ([] : List Nat)
        = (⟨List.replicate d 0,
          [BPair.ofNat 1]⟩ : HVec).content := by
  refine ⟨(sumNat_replicate_zero d).symm, ?_⟩
  show content (List.replicate d 0).length ([] : List Nat)
    = List.replicate d 0
  rw [ground.length_replicate]
  exact content_nil_replicate d

private theorem coordAt_seed (d : Nat) :
    coordAt (⟨List.replicate d 0, [BPair.ofNat 1]⟩ : HVec)
        ([] : List Nat)
      = BPair.ofNat 1 := by
  have hr := rankOf_read ([] : List Nat) (List.replicate d 0)
    (seed_nil_reads d).1 (seed_nil_reads d).2
  have hm1 : (monomialsAt (List.replicate d 0)).length = 1 := by
    rw [places.monomialsAt_sum_zero _ (sumNat_replicate_zero d)]
    rfl
  have hz : rankOf ([] : List Nat) (List.replicate d 0) = 0 := by
    rw [hm1] at hr
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hr.1)
  show ground.getAt BPair.unit [BPair.ofNat 1]
    (rankOf ([] : List Nat) (List.replicate d 0)) = BPair.ofNat 1
  rw [hz]
  rfl

private theorem tensorH_seed_left (d : Nat) (x : HVec)
    (hsx : sized x) (hxd : x.content.length = d) :
    (tensorH ⟨List.replicate d 0, [BPair.ofNat 1]⟩ x).content
        = x.content
      ∧ poly.oneValue
          (tensorH ⟨List.replicate d 0, [BPair.ofNat 1]⟩ x).coords
          x.coords := by
  have hlen : (⟨List.replicate d 0,
        [BPair.ofNat 1]⟩ : HVec).content.length
      = x.content.length := by
    show (List.replicate d 0).length = x.content.length
    rw [ground.length_replicate, hxd]
  have hct : (tensorH ⟨List.replicate d 0, [BPair.ofNat 1]⟩
      x).content = x.content := by
    show List.zipWith (fun a b => a + b) (List.replicate d 0)
      x.content = x.content
    exact ground.zipWith_zero_left d x.content hxd
  refine ⟨hct, ?_⟩
  refine poly.oneValue_of_entries _ _
    (by rw [tensorH_sized _ x, hct, hsx]) ?_
  intro k hk
  rw [tensorH_sized _ x] at hk
  have hkc : k < (monomialsAt x.content).length := by
    rw [← hct]
    exact hk
  have hMc := member_conditions (ground.countOf_getAt_pos []
    (monomialsAt (tensorH ⟨List.replicate d 0, [BPair.ofNat 1]⟩
      x).content) k hk)
  have hrk : rankOf (ground.getAt []
      (monomialsAt (tensorH ⟨List.replicate d 0,
        [BPair.ofNat 1]⟩ x).content) k) x.content = k := by
    rw [hct]
    exact rankOf_getAt x.content k hkc
  refine BPair.oneValue_trans
    (tensor_coord_at ⟨List.replicate d 0, [BPair.ofNat 1]⟩ x hlen
      (seed_sized d) hsx k [] _ hk rfl (seed_nil_reads d).1
      (seed_nil_reads d).2 (by rw [hMc.1, hct])
      (by rw [← hct]; exact hMc.2)) ?_
  rw [coordAt_seed d,
    show coordAt x (ground.getAt []
        (monomialsAt (tensorH ⟨List.replicate d 0,
          [BPair.ofNat 1]⟩ x).content) k)
      = ground.getAt BPair.unit x.coords k from by
      show ground.getAt BPair.unit x.coords (rankOf _ x.content) = _
      rw [hrk],
    BPair.mul_comm]
  exact BPair.mul_ofNat_one _

private theorem seed_right_entry (d : Nat) (x : HVec)
    (hsx : sized x) (hxd : x.content.length = d)
    (k : Nat) (M m1 m2 : List Nat)
    (hk : k < (monomialsAt x.content).length)
    (hk2 : k < (monomialsAt (tensorH x ⟨List.replicate d 0,
      [BPair.ofNat 1]⟩).content).length)
    (hM : ground.getAt [] (monomialsAt (tensorH x
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩).content) k = M)
    (hcat : M = m1 ++ m2)
    (hl1 : m1.length = sumNat x.content)
    (hl2 : m2.length = 0)
    (hct : (tensorH x ⟨List.replicate d 0,
      [BPair.ofNat 1]⟩).content = x.content)
    (hMc : content (tensorH x ⟨List.replicate d 0,
        [BPair.ofNat 1]⟩).content.length M
      = (tensorH x ⟨List.replicate d 0,
        [BPair.ofNat 1]⟩).content) :
    (ground.getAt BPair.unit x.coords k).oneValue
      (ground.getAt BPair.unit (tensorH x
        ⟨List.replicate d 0, [BPair.ofNat 1]⟩).coords k) := by
  have hlen : x.content.length
      = (⟨List.replicate d 0,
        [BPair.ofNat 1]⟩ : HVec).content.length := by
    show x.content.length = (List.replicate d 0).length
    rw [ground.length_replicate, hxd]
  have hnil : m2 = [] := ground.nil_of_length_zero m2 hl2
  have hm1 : M = m1 := by
    rw [hcat, hnil, ground.append_nil]
  have hrk : rankOf m1 x.content = k := by
    rw [← hm1, ← hM, hct]
    exact rankOf_getAt x.content k hk
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (tensor_coord_at x ⟨List.replicate d 0, [BPair.ofNat 1]⟩ hlen
      hsx (seed_sized d) k m1 m2 hk2 (hM.trans hcat) hl1
      (by rw [← hm1, ← hct]; exact hMc)
      (by rw [hnil]; exact (seed_nil_reads d).1)
      (by rw [hnil]; exact (seed_nil_reads d).2)) ?_)
  rw [hnil, coordAt_seed d,
    show coordAt x m1 = ground.getAt BPair.unit x.coords k from by
      show ground.getAt BPair.unit x.coords (rankOf m1 x.content)
        = _
      rw [hrk]]
  exact BPair.mul_ofNat_one _

private theorem tensorH_seed_right (d : Nat) (x : HVec)
    (hsx : sized x) (hxd : x.content.length = d) :
    x.content
        = (tensorH x ⟨List.replicate d 0,
            [BPair.ofNat 1]⟩).content
      ∧ poly.oneValue x.coords
          (tensorH x ⟨List.replicate d 0,
            [BPair.ofNat 1]⟩).coords := by
  have hct : (tensorH x ⟨List.replicate d 0,
      [BPair.ofNat 1]⟩).content = x.content := by
    show List.zipWith (fun a b => a + b) x.content
      (List.replicate d 0) = x.content
    exact zipWith_zero_right d x.content hxd
  refine ⟨hct.symm, ?_⟩
  refine poly.oneValue_of_entries _ _
    (by rw [tensorH_sized x _, hct, hsx]) ?_
  intro k hk
  rw [hsx] at hk
  have hk2 : k < (monomialsAt (tensorH x ⟨List.replicate d 0,
      [BPair.ofNat 1]⟩).content).length := by
    rw [hct]
    exact hk
  have hMc := member_conditions (ground.countOf_getAt_pos []
    (monomialsAt (tensorH x ⟨List.replicate d 0,
      [BPair.ofNat 1]⟩).content) k hk2)
  have hMl : (ground.getAt [] (monomialsAt
      (tensorH x ⟨List.replicate d 0,
        [BPair.ofNat 1]⟩).content) k).length
      = sumNat x.content + 0 := by
    rw [Nat.add_zero, hMc.1, hct]
  match split_lengths _ _ _ hMl with
  | ⟨hcat, hl1, hl2⟩ =>
    exact seed_right_entry d x hsx hxd k _ _ _ hk hk2 rfl hcat hl1
      hl2 hct hMc.2

private theorem fold_congr (d : Nat) :
    ∀ (ls : List Nat) (x y : HVec), sized x → sized y →
      x.content.length = d → y.content.length = d →
      x.content = y.content → poly.oneValue x.coords y.coords →
      (ls.foldl (fun a l => tensorH a (wedge d l)) x).content
          = (ls.foldl (fun a l => tensorH a (wedge d l)) y).content
        ∧ poly.oneValue
            (ls.foldl (fun a l => tensorH a (wedge d l)) x).coords
            (ls.foldl (fun a l => tensorH a (wedge d l)) y).coords
  | [], _, _, _, _, _, _, hc, hx => ⟨hc, hx⟩
  | l :: ls, x, y, hsx, hsy, hxd, hyd, hc, hx => by
    refine fold_congr d ls (tensorH x (wedge d l))
      (tensorH y (wedge d l)) (tensorH_sized x _)
      (tensorH_sized y _) ?_ ?_ ?_ ?_
    · show (List.zipWith (fun a b => a + b) x.content
        (wedge d l).content).length = d
      exact ground.length_zipWith (fun x y => x + y) x.content (wedge d l).content d hxd
        (wedge_clen d l)
    · show (List.zipWith (fun a b => a + b) y.content
        (wedge d l).content).length = d
      exact ground.length_zipWith (fun x y => x + y) y.content (wedge d l).content d hyd
        (wedge_clen d l)
    · show List.zipWith (fun a b => a + b) x.content
          (wedge d l).content
        = List.zipWith (fun a b => a + b) y.content
          (wedge d l).content
      rw [hc]
    · exact tensorH_polyOne x y (wedge d l) (wedge d l) hsx hsy
        (wedge_sized d l) (wedge_sized d l) hc rfl hx
        (poly.oneValue_refl _)

private theorem exhibit_pull (d : Nat) :
    ∀ (ls : List Nat) (acc : HVec), sized acc →
      acc.content.length = d →
      (ls.foldl (fun a l => tensorH a (wedge d l))
            (tensorH (wedge d d) acc)).content
          = (tensorH (wedge d d)
              (ls.foldl (fun a l => tensorH a (wedge d l))
                acc)).content
        ∧ poly.oneValue
            (ls.foldl (fun a l => tensorH a (wedge d l))
              (tensorH (wedge d d) acc)).coords
            (tensorH (wedge d d)
              (ls.foldl (fun a l => tensorH a (wedge d l))
                acc)).coords
  | [], _, _, _ => ⟨rfl, poly.oneValue_refl _⟩
  | l :: ls, acc, hsa, hda => by
    have hdl : (tensorH acc (wedge d l)).content.length = d := by
      show (List.zipWith (fun a b => a + b) acc.content
        (wedge d l).content).length = d
      exact ground.length_zipWith (fun x y => x + y) acc.content (wedge d l).content d hda
        (wedge_clen d l)
    have hdw : (tensorH (wedge d d) acc).content.length = d := by
      show (List.zipWith (fun a b => a + b) (wedge d d).content
        acc.content).length = d
      exact ground.length_zipWith (fun x y => x + y) (wedge d d).content acc.content d
        (wedge_clen d d) hda
    have hd1 : (tensorH (tensorH (wedge d d) acc)
        (wedge d l)).content.length = d := by
      show (List.zipWith (fun a b => a + b)
        (tensorH (wedge d d) acc).content
        (wedge d l).content).length = d
      exact ground.length_zipWith (fun x y => x + y) _ _ d hdw (wedge_clen d l)
    have hd2 : (tensorH (wedge d d)
        (tensorH acc (wedge d l))).content.length = d := by
      show (List.zipWith (fun a b => a + b) (wedge d d).content
        (tensorH acc (wedge d l)).content).length = d
      exact ground.length_zipWith (fun x y => x + y) _ _ d (wedge_clen d d) hdl
    have hassoc := tensorH_assoc (wedge d d) acc (wedge d l)
      (wedge_sized d d) hsa (wedge_sized d l)
      (by rw [wedge_clen d d, hda]) (by rw [hda, wedge_clen d l])
    exact hvec_trans
      (fold_congr d ls (tensorH (tensorH (wedge d d) acc)
          (wedge d l))
        (tensorH (wedge d d) (tensorH acc (wedge d l)))
        (tensorH_sized _ _) (tensorH_sized _ _) hd1 hd2
        hassoc.1 hassoc.2)
      (exhibit_pull d ls (tensorH acc (wedge d l))
        (tensorH_sized acc _) hdl)

private theorem columnLengths_bumpTop : ∀ s : Shape, 0 < s.length →
    columnLengths (ground.bumpAt (s.length - 1) s)
      = s.length :: columnLengths s
  | [], h => absurd h (Nat.lt_irrefl 0)
  | [n], _ => by
    show columnLengths (ground.bumpAt 0 [n])
      = 1 :: columnLengths [n]
    rw [show ground.bumpAt 0 [n] = [n + 1] from rfl,
      columnLengths_cons (n + 1) [], columnLengths_cons n []]
    rfl
  | n :: m :: t, _ => by
    rw [show ground.bumpAt ((n :: m :: t).length - 1) (n :: m :: t)
        = n :: ground.bumpAt ((m :: t).length - 1) (m :: t)
        from rfl,
      columnLengths_cons n (ground.bumpAt ((m :: t).length - 1)
        (m :: t)),
      columnLengths_bumpTop (m :: t) (Nat.succ_pos _),
      columnLengths_cons n (m :: t)]
    rfl

/-- The exhibit at the shape with one more full column: the added
column's wedge tensors onto the exhibit, contents and coordinates
alike. -/
theorem exhibit_addFull : ∀ lam : Shape,
    (exhibit (ground.bumpAt (lam.length - 1) lam)).content
        = (tensorH (wedge lam.length lam.length)
            (exhibit lam)).content
      ∧ poly.oneValue
          (exhibit (ground.bumpAt (lam.length - 1) lam)).coords
          (tensorH (wedge lam.length lam.length)
            (exhibit lam)).coords := by
  intro lam
  match lam with
  | [] => exact ⟨rfl, poly.oneValue_refl _⟩
  | a :: t =>
  have hlam : 0 < (a :: t : Shape).length := Nat.succ_pos _
  generalize (a :: t : Shape) = lam at hlam ⊢
  have hbl : (ground.bumpAt (lam.length - 1) lam).length
      = lam.length := ground.length_bumpAt _ lam
  have hsd : (⟨List.replicate lam.length 0,
      [BPair.ofNat 1]⟩ : HVec).content.length = lam.length :=
    ground.length_replicate 0 lam.length
  have hAd : (tensorH ⟨List.replicate lam.length 0,
      [BPair.ofNat 1]⟩ (wedge lam.length lam.length)).content.length
      = lam.length := by
    show (List.zipWith (fun a b => a + b)
      (List.replicate lam.length 0)
      (wedge lam.length lam.length).content).length = lam.length
    exact ground.length_zipWith (fun x y => x + y) _ _ lam.length hsd
      (wedge_clen lam.length lam.length)
  have hBd : (tensorH (wedge lam.length lam.length)
      ⟨List.replicate lam.length 0,
        [BPair.ofNat 1]⟩).content.length = lam.length := by
    show (List.zipWith (fun a b => a + b)
      (wedge lam.length lam.length).content
      (List.replicate lam.length 0)).length = lam.length
    exact ground.length_zipWith (fun x y => x + y) _ _ lam.length
      (wedge_clen lam.length lam.length) hsd
  have hex : exhibit (ground.bumpAt (lam.length - 1) lam)
      = (columnLengths lam).foldl
        (fun a l => tensorH a (wedge lam.length l))
        (tensorH ⟨List.replicate lam.length 0, [BPair.ofNat 1]⟩
          (wedge lam.length lam.length)) := by
    show ((columnLengths (ground.bumpAt (lam.length - 1) lam)).foldl
      (fun acc l => tensorH acc
        (wedge (ground.bumpAt (lam.length - 1) lam).length l))
      ⟨List.replicate (ground.bumpAt (lam.length - 1) lam).length 0,
        [BPair.ofNat 1]⟩) = _
    rw [hbl, columnLengths_bumpTop lam hlam]
    rfl
  rw [hex]
  have hs1 := tensorH_seed_left lam.length
    (wedge lam.length lam.length) (wedge_sized _ _)
    (wedge_clen _ _)
  have hs2 := tensorH_seed_right lam.length
    (wedge lam.length lam.length) (wedge_sized _ _)
    (wedge_clen _ _)
  refine hvec_trans
    (hvec_trans
      (fold_congr lam.length (columnLengths lam) _ _
        (tensorH_sized _ _) (wedge_sized _ _) hAd
        (wedge_clen _ _) hs1.1 hs1.2)
      (fold_congr lam.length (columnLengths lam) _ _
        (wedge_sized _ _) (tensorH_sized _ _) (wedge_clen _ _)
        hBd hs2.1 hs2.2))
    (exhibit_pull lam.length (columnLengths lam)
      ⟨List.replicate lam.length 0, [BPair.ofNat 1]⟩
      (seed_sized lam.length) hsd)

/-! `lem:dualread`(ii)'s pairing: the joint enumeration re-lists as
the factors' pairs beside the places whose split misses the
factors' contents, and the pairing folds factor by factor. -/

private theorem bsum_relist (f : List Nat → BPair)
    (l l' : List (List Nat))
    (h : ∀ x, ground.countOf x l = ground.countOf x l') :
    ground.bsum f l = ground.bsum f l' :=
  ground.famFold_relist BPair.add BPair.unit BPair.add_comm
    BPair.add_assoc f l l' h

private theorem bsum_flatMap (f : List Nat → BPair)
    (g : List Nat → List (List Nat)) :
    ∀ l : List (List Nat),
      (ground.bsum f (l.flatMap g)).oneValue
        (ground.bsum (fun y => ground.bsum f (g y)) l) :=
  ground.famFold_flatMap_ov ground.bpairFoldLaws f g

private theorem dotP_bsum (F G : List Nat → BPair) :
    ∀ (bs : List (List Nat)) (x y : List BPair),
      x.length = bs.length → y.length = bs.length →
      (∀ i, i < bs.length →
        F (ground.getAt [] bs i) = ground.getAt BPair.unit x i) →
      (∀ i, i < bs.length →
        G (ground.getAt [] bs i) = ground.getAt BPair.unit y i) →
      elim.dotP x y = ground.bsum (fun M => F M * G M) bs
  | [], [], [], _, _, _, _ => rfl
  | [], [], _ :: _, _, hy, _, _ => nomatch hy
  | [], _ :: _, _, hx, _, _, _ => nomatch hx
  | _ :: _, [], _, hx, _, _, _ => nomatch hx
  | _ :: _, _ :: _, [], _, hy, _, _ => nomatch hy
  | b :: bt, c :: xt, e :: yt, hx, hy, hF, hG => by
    show c * e + elim.dotP xt yt
      = F b * G b + ground.bsum (fun M => F M * G M) bt
    rw [show F b = c from hF 0 (Nat.succ_pos _),
      show G b = e from hG 0 (Nat.succ_pos _),
      dotP_bsum F G bt xt yt (Nat.succ.inj hx) (Nat.succ.inj hy)
        (fun i hi => hF (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi => hG (i + 1) (Nat.succ_lt_succ hi))]

private theorem countOf_map_append (n : Nat) (M1 x : List Nat)
    (hM1 : M1.length = n) :
    ∀ l : List (List Nat),
      ground.countOf x (l.map (fun M2 => M1 ++ M2))
        = if M1 = List.take n x then
            ground.countOf (List.drop n x) l else 0
  | [] => by
    by_cases h : M1 = List.take n x
    · rw [if_pos h]
      rfl
    · rw [if_neg h]
      rfl
  | b :: t => by
    have hrec := countOf_map_append n M1 x hM1 t
    show ground.countOf x ((M1 ++ b) :: t.map (fun M2 => M1 ++ M2))
      = if M1 = List.take n x then
          ground.countOf (List.drop n x) (b :: t)
        else 0
    rw [ground.countOf_cons, ground.countOf_cons, hrec]
    by_cases h : M1 = List.take n x
    · rw [if_pos h, if_pos h]
      by_cases hb : x = M1 ++ b
      · rw [if_pos hb, if_pos (show List.drop n x = b from by
          rw [hb, ← hM1, ground.drop_append_self])]
      · rw [if_neg hb, if_neg (show ¬ List.drop n x = b from fun he =>
          hb (by rw [h, ← he, List.take_append_drop]))]
    · rw [if_neg h, if_neg h,
        if_neg (show ¬ x = M1 ++ b from fun he =>
          h (by rw [he, ← hM1, ground.take_append_self]))]

private theorem countOf_pairList (n : Nat) (x : List Nat)
    (bs2 : List (List Nat)) :
    ∀ bs1 : List (List Nat),
      (∀ M1, 0 < ground.countOf M1 bs1 → M1.length = n) →
      ground.countOf x
          (bs1.flatMap (fun M1 => bs2.map (fun M2 => M1 ++ M2)))
        = ground.famFold Nat.add 0
            (fun M1 => if M1 = List.take n x
              then ground.countOf (List.drop n x) bs2 else 0) bs1
  | [], _ => rfl
  | b :: t, h => by
    have hb : b.length = n := h b (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _)
    have ht : ∀ M1, 0 < ground.countOf M1 t → M1.length = n :=
      fun M1 hM1 => h M1 (Nat.lt_of_lt_of_le hM1
        (Nat.le_add_left _ _))
    show ground.countOf x (bs2.map (fun M2 => b ++ M2)
        ++ t.flatMap (fun M1 => bs2.map (fun M2 => M1 ++ M2)))
      = (if b = List.take n x then
          ground.countOf (List.drop n x) bs2 else 0)
        + ground.famFold Nat.add 0
          (fun M1 => if M1 = List.take n x
            then ground.countOf (List.drop n x) bs2 else 0) t
    rw [ground.countOf_append, countOf_map_append n b x hb bs2,
      countOf_pairList n x bs2 t ht]

private theorem countOf_reject (p : List Nat → Bool)
    (x : List Nat) :
    ∀ l : List (List Nat),
      ground.countOf x
          (l.flatMap (fun M => if p M then [] else [M]))
        = if p x then 0 else ground.countOf x l
  | [] => by
    by_cases hpx : p x = true
    · rw [if_pos hpx]
      rfl
    · rw [if_neg hpx]
      rfl
  | b :: t => by
    have hrec := countOf_reject p x t
    show ground.countOf x ((if p b then [] else [b])
        ++ t.flatMap (fun M => if p M then [] else [M]))
      = if p x then 0 else ground.countOf x (b :: t)
    rw [ground.countOf_cons, ground.countOf_append, hrec]
    by_cases hpx : p x = true
    · rw [if_pos hpx, if_pos hpx, Nat.add_zero]
      by_cases hpb : p b = true
      · rw [if_pos hpb]
        rfl
      · rw [if_neg hpb, ground.countOf_cons]
        show (if x = b then 1 else 0) + 0 = 0
        rw [if_neg (show ¬ x = b from fun he =>
          hpb (by rw [← he]; exact hpx))]
    · rw [if_neg hpx, if_neg hpx]
      by_cases hpb : p b = true
      · rw [if_pos hpb,
          if_neg (show ¬ x = b from fun he =>
            hpx (by rw [he]; exact hpb))]
        rfl
      · rw [if_neg hpb, ground.countOf_cons]
        show (if x = b then 1 else 0) + 0 + ground.countOf x t
          = (if x = b then 1 else 0) + ground.countOf x t
        rw [Nat.add_zero]

private def splitGood (mu nu M : List Nat) : Bool :=
  if (List.take (sumNat mu) M).length = sumNat mu
      ∧ content mu.length (List.take (sumNat mu) M) = mu
      ∧ (List.drop (sumNat mu) M).length = sumNat nu
      ∧ content nu.length (List.drop (sumNat mu) M) = nu
    then true else false

private theorem splitGood_of (mu nu M : List Nat)
    (h : (List.take (sumNat mu) M).length = sumNat mu
      ∧ content mu.length (List.take (sumNat mu) M) = mu
      ∧ (List.drop (sumNat mu) M).length = sumNat nu
      ∧ content nu.length (List.drop (sumNat mu) M) = nu) :
    splitGood mu nu M = true := if_pos h

private theorem splitGood_elim (mu nu M : List Nat)
    (h : splitGood mu nu M = true) :
    (List.take (sumNat mu) M).length = sumNat mu
      ∧ content mu.length (List.take (sumNat mu) M) = mu
      ∧ (List.drop (sumNat mu) M).length = sumNat nu
      ∧ content nu.length (List.drop (sumNat mu) M) = nu := by
  by_cases hc : (List.take (sumNat mu) M).length = sumNat mu
      ∧ content mu.length (List.take (sumNat mu) M) = mu
      ∧ (List.drop (sumNat mu) M).length = sumNat nu
      ∧ content nu.length (List.drop (sumNat mu) M) = nu
  · exact hc
  · rw [show splitGood mu nu M = false from if_neg hc] at h
    exact Bool.noConfusion h

private theorem pairList_count (mu nu : List Nat)
    (hlen : mu.length = nu.length) (x : List Nat) :
    ground.countOf x (monomialsAt
        (List.zipWith (fun a b => a + b) mu nu))
      = ground.countOf x
          ((monomialsAt mu).flatMap (fun M1 =>
              (monomialsAt nu).map (fun M2 => M1 ++ M2))
            ++ (monomialsAt
              (List.zipWith (fun a b => a + b) mu nu)).flatMap
              (fun M => if splitGood mu nu M then [] else [M])) := by
  rw [ground.countOf_append]
  have hL2 : ground.countOf x
      ((monomialsAt mu).flatMap (fun M1 =>
        (monomialsAt nu).map (fun M2 => M1 ++ M2)))
      = if splitGood mu nu x then 1 else 0 := by
    rw [countOf_pairList (sumNat mu) x (monomialsAt nu)
      (monomialsAt mu) (fun M1 hM1 => (member_conditions hM1).1)]
    by_cases hg : splitGood mu nu x = true
    · match splitGood_elim mu nu x hg with
      | ⟨h1, h2, h3, h4⟩ =>
        rw [if_pos hg,
          ground.famFold_pick _ (List.take (sumNat mu) x)
            (monomialsAt mu) (count_one_of_member h1 h2),
          countOf_monomialsAt nu (List.drop (sumNat mu) x),
          if_pos ⟨h3, h4⟩]
    · rw [if_neg hg]
      by_cases ht : (List.take (sumNat mu) x).length = sumNat mu
          ∧ content mu.length (List.take (sumNat mu) x) = mu
      · have hd : ¬ ((List.drop (sumNat mu) x).length = sumNat nu
            ∧ content nu.length (List.drop (sumNat mu) x) = nu) :=
          fun hdd => hg (splitGood_of mu nu x
            ⟨ht.1, ht.2, hdd.1, hdd.2⟩)
        rw [ground.famFold_pick _ (List.take (sumNat mu) x)
            (monomialsAt mu) (count_one_of_member ht.1 ht.2),
          countOf_monomialsAt nu (List.drop (sumNat mu) x), if_neg hd]
      · refine ground.famFold_pickZero _ (List.take (sumNat mu) x)
          (monomialsAt mu) ?_
        rw [countOf_monomialsAt mu (List.take (sumNat mu) x), if_neg ht]
  rw [hL2, countOf_reject (splitGood mu nu) x]
  by_cases hg : splitGood mu nu x = true
  · match splitGood_elim mu nu x hg with
    | ⟨h1, h2, h3, h4⟩ =>
      have hcm := concat_member mu nu (List.take (sumNat mu) x)
        (List.drop (sumNat mu) x) hlen h1 h2 h3 h4
      rw [if_pos hg, if_pos hg, Nat.add_zero,
        countOf_monomialsAt
          (List.zipWith (fun a b => a + b) mu nu) x]
      refine if_pos ?_
      rw [← List.take_append_drop (sumNat mu) x]
      exact hcm
  · rw [if_neg hg, if_neg hg, Nat.zero_add]

/-- The tensor's pairing factorizes: at one pair of contents and
matched factor widths the joint pairing is the factors' own
pairings multiplied. -/
theorem dotP_tensorH : ∀ (v w v' w' : HVec),
    sized v → sized w → sized v' → sized w' →
    v.content.length = w.content.length →
    v.content = v'.content → w.content = w'.content →
    (elim.dotP (tensorH v w).coords (tensorH v' w').coords).oneValue
      (elim.dotP v.coords v'.coords
        * elim.dotP w.coords w'.coords) := by
  intro v w v' w' hsv hsw hsv' hsw' hlen hcv hcw
  have hlen' : v'.content.length = w'.content.length := by
    rw [← hcv, ← hcw]
    exact hlen
  have hTc : (tensorH v w).content = (tensorH v' w').content := by
    show List.zipWith (fun a b => a + b) v.content w.content
      = List.zipWith (fun a b => a + b) v'.content w'.content
    rw [hcv, hcw]
  have hTd : elim.dotP (tensorH v w).coords (tensorH v' w').coords
      = ground.bsum (fun M => coordAt (tensorH v w) M
        * coordAt (tensorH v' w') M)
        (monomialsAt (tensorH v w).content) := by
    refine dotP_bsum _ _ _ _ _ (tensorH_sized v w)
      (by rw [tensorH_sized v' w', hTc]) (fun i hi => ?_)
      (fun i hi => ?_)
    · show ground.getAt BPair.unit (tensorH v w).coords
        (rankOf _ (tensorH v w).content) = _
      rw [rankOf_getAt (tensorH v w).content i hi]
    · show ground.getAt BPair.unit (tensorH v' w').coords
        (rankOf _ (tensorH v' w').content) = _
      rw [← hTc, rankOf_getAt (tensorH v w).content i hi]
  have hvd : elim.dotP v.coords v'.coords
      = ground.bsum (fun M => coordAt v M * coordAt v' M)
        (monomialsAt v.content) := by
    refine dotP_bsum _ _ _ _ _ hsv (by rw [hsv', hcv])
      (fun i hi => ?_) (fun i hi => ?_)
    · show ground.getAt BPair.unit v.coords
        (rankOf _ v.content) = _
      rw [rankOf_getAt v.content i hi]
    · show ground.getAt BPair.unit v'.coords
        (rankOf _ v'.content) = _
      rw [← hcv, rankOf_getAt v.content i hi]
  have hwd : elim.dotP w.coords w'.coords
      = ground.bsum (fun M => coordAt w M * coordAt w' M)
        (monomialsAt w.content) := by
    refine dotP_bsum _ _ _ _ _ hsw (by rw [hsw', hcw])
      (fun i hi => ?_) (fun i hi => ?_)
    · show ground.getAt BPair.unit w.coords
        (rankOf _ w.content) = _
      rw [rankOf_getAt w.content i hi]
    · show ground.getAt BPair.unit w'.coords
        (rankOf _ w'.content) = _
      rw [← hcw, rankOf_getAt w.content i hi]
  rw [hTd, hvd, hwd,
    bsum_relist (fun M => coordAt (tensorH v w) M
        * coordAt (tensorH v' w') M)
      (monomialsAt (tensorH v w).content)
      ((monomialsAt v.content).flatMap (fun M1 =>
          (monomialsAt w.content).map (fun M2 => M1 ++ M2))
        ++ (monomialsAt (tensorH v w).content).flatMap
          (fun M => if splitGood v.content w.content M
            then [] else [M]))
      (pairList_count v.content w.content hlen)]
  refine BPair.oneValue_trans
    (ground.famFold_append_ov ground.bpairFoldLaws _ _ _) ?_
  have hRnull : (ground.bsum (fun M => coordAt (tensorH v w) M
      * coordAt (tensorH v' w') M)
      ((monomialsAt (tensorH v w).content).flatMap
        (fun M => if splitGood v.content w.content M
          then [] else [M]))).oneValue BPair.unit := by
    refine ground.foldB_null _ _ ?_
    intro M hM
    rw [countOf_reject (splitGood v.content w.content) M] at hM
    by_cases hg : splitGood v.content w.content M = true
    · rw [if_pos hg] at hM
      exact absurd hM (Nat.lt_irrefl 0)
    · rw [if_neg hg] at hM
      match member_conditions hM with
      | ⟨hMl, hMc⟩ =>
        match member_split v w hlen M hMl with
        | ⟨hcat, hl1, hl2⟩ =>
          rw [hcat]
          refine BPair.oneValue_trans
            (BPair.mul_congr
              (tensor_coord_null v w hlen _ _
                (by rw [← hcat]; exact hMl)
                (by rw [← hcat]; exact hMc) hl1 ?_)
              (BPair.oneValue_refl _))
            (BPair.unit_mul _)
          intro hq1 hq2
          exact hg (splitGood_of v.content w.content M
            ⟨hl1, hq1.2, hl2, hq2.2⟩)
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) hRnull) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.oneValue_trans (bsum_flatMap _ _ _) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ (fun M1 => (coordAt v M1 * coordAt v' M1)
        * ground.bsum (fun M2 => coordAt w M2 * coordAt w' M2)
          (monomialsAt w.content))
      (monomialsAt v.content) (fun M1 hM1 => ?_)) ?_
  · match member_conditions hM1 with
    | ⟨h1l, h1c⟩ =>
      rw [ground.bsum_map]
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _ (fun M2 => (coordAt v M1 * coordAt v' M1)
            * (coordAt w M2 * coordAt w' M2))
          (monomialsAt w.content) (fun M2 hM2 => ?_)) ?_
      · match member_conditions hM2 with
        | ⟨h2l, h2c⟩ =>
          refine BPair.oneValue_trans
            (BPair.mul_congr
              (tensor_coord v w hlen hsv hsw M1 M2 h1l h1c h2l h2c)
              (tensor_coord v' w' hlen' hsv' hsw' M1 M2
                (by rw [← hcv]; exact h1l)
                (by rw [← hcv]; exact h1c)
                (by rw [← hcw]; exact h2l)
                (by rw [← hcw]; exact h2c))) ?_
          exact ground.BPair.oneValue_of_eq (BPair.mul_mul_mul_comm (coordAt v M1) (coordAt w M2)
            (coordAt v' M1) (coordAt w' M2))
      · exact ground.foldB_mul_left
          (coordAt v M1 * coordAt v' M1)
          (fun M2 => coordAt w M2 * coordAt w' M2) _
  · exact bsum_mulR (fun M1 => coordAt v M1 * coordAt v' M1)
      (ground.bsum (fun M2 => coordAt w M2 * coordAt w' M2)
        (monomialsAt w.content)) _

private theorem tensor_place_off (v w v' w' : HVec)
    (hlen : v.content.length = w.content.length)
    (hlen' : v'.content.length = w'.content.length)
    (hvv' : v.content.length = v'.content.length)
    (hdeg : sumNat v.content = sumNat v'.content)
    (hcc : (tensorH v w).content = (tensorH v' w').content)
    (hne : ¬ v.content = v'.content)
    (k : Nat) (m1 m2 : List Nat)
    (hk : k < (monomialsAt (tensorH v w).content).length)
    (hcat : ground.getAt [] (monomialsAt (tensorH v w).content) k
      = m1 ++ m2)
    (h1l : m1.length = sumNat v.content) :
    (ground.getAt BPair.unit (tensorH v w).coords k).oneValue
        BPair.unit
      ∨ (ground.getAt BPair.unit (tensorH v' w').coords k).oneValue
        BPair.unit := by
  by_cases hg1 : content v.content.length m1 = v.content
  · by_cases hg2 : content w.content.length m2 = w.content
    · refine Or.inr (tensor_coord_at_null v' w' hlen' k m1 m2
        (by rw [← hcc]; exact hk) (by rw [← hcc]; exact hcat)
        (by rw [← hdeg]; exact h1l) ?_)
      intro h1 _
      exact hne (hg1.symm.trans (by rw [hvv']; exact h1.2))
    · exact Or.inl (tensor_coord_at_null v w hlen k m1 m2 hk hcat
        h1l (fun _ h2 => hg2 h2.2))
  · exact Or.inl (tensor_coord_at_null v w hlen k m1 m2 hk hcat
      h1l (fun h1 _ => hg1 h1.2))

/-- Two tensors at one fused content but distinct first contents
pair at the sum's unit: each enumeration place splits at the first
factor's degree, and at every place one of the two coordinates
reads the sum's unit off its own contents' split
(`lem:blockcount`(iii)). -/
theorem dotP_tensorH_off : ∀ (v w v' w' : HVec),
    v.content.length = w.content.length →
    v'.content.length = w'.content.length →
    sumNat v.content = sumNat v'.content →
    (tensorH v w).content = (tensorH v' w').content →
    ¬ v.content = v'.content →
    (elim.dotP (tensorH v w).coords
      (tensorH v' w').coords).oneValue BPair.unit := by
  intro v w v' w' hlen hlen' hdeg hcc hne
  have hvv' : v.content.length = v'.content.length := by
    rw [← ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length
        rfl hlen.symm,
      ← ground.length_zipWith (fun x y => x + y) v'.content w'.content v'.content.length
        rfl hlen'.symm]
    exact congrArg List.length hcc
  refine elim.dotP_null_or _ _
    (by rw [tensorH_sized v w, tensorH_sized v' w', hcc])
    (fun k hk => ?_)
  rw [tensorH_sized v w] at hk
  match member_split v w hlen
      (ground.getAt [] (monomialsAt (tensorH v w).content) k)
      (member_conditions (ground.countOf_getAt_pos []
        (monomialsAt (tensorH v w).content) k hk)).1 with
  | ⟨hcat, hl1, _⟩ =>
    exact tensor_place_off v w v' w' hlen hlen' hvv' hdeg hcc hne k
      _ _ hk hcat hl1

/-! `lem:blockcount`(iii)'s independence and the fused carrier: the
stated pair list at a content carries each first-factor member's
tensors against its partners at the complementary content, so a
combination reading the unit family pairs every pair at the sum's
unit and its coefficients read back through the two factors in
turn — per first-factor content the second factor's group pairs
every group member at that unit and reads its own coefficients
there, the first factor's groups then reading the coefficients
themselves.  The fused pool carries every tensor whatever, its
content group at the target the pair list's own coordinate family,
so the fusion count is that pool's own count. -/

private def pairsOne (v : HVec) (B : List HVec) (cc : List Nat) :
    List HVec :=
  B.flatMap (fun w =>
    if List.zipWith (fun x y => x + y) v.content w.content = cc then
      [tensorH v w]
    else [])

private theorem pairsAt_cons (v : HVec) (A B : List HVec)
    (cc : List Nat) :
    pairsAt (v :: A) B cc = pairsOne v B cc ++ pairsAt A B cc := rfl

private def partnersAt (α : List Nat) (B : List HVec) (cc : List Nat) :
    List HVec :=
  B.filter (fun w =>
    decide (List.zipWith (fun x y => x + y) α w.content = cc))

private theorem pairsOne_eq (v : HVec) (cc : List Nat) :
    ∀ B : List HVec,
      pairsOne v B cc = (partnersAt v.content B cc).map (tensorH v)
  | [] => rfl
  | w :: t => by
    show (if List.zipWith (fun x y => x + y) v.content w.content
          = cc then [tensorH v w] else []) ++ pairsOne v t cc
      = ((w :: t).filter (fun w =>
          decide (List.zipWith (fun x y => x + y) v.content w.content
            = cc))).map (tensorH v)
    rw [ground.filter_cons]
    by_cases hg :
        List.zipWith (fun x y => x + y) v.content w.content = cc
    · rw [if_pos hg]
      show tensorH v w :: pairsOne v t cc
        = (match (decide (List.zipWith (fun x y => x + y) v.content
            w.content = cc)) with
          | true => w :: t.filter _
          | false => t.filter _).map (tensorH v)
      rw [decide_eq_true hg]
      show tensorH v w :: pairsOne v t cc
        = tensorH v w :: (t.filter _).map (tensorH v)
      rw [pairsOne_eq v cc t]
      rfl
    · rw [if_neg hg]
      show pairsOne v t cc
        = (match (decide (List.zipWith (fun x y => x + y) v.content
            w.content = cc)) with
          | true => w :: t.filter _
          | false => t.filter _).map (tensorH v)
      rw [decide_eq_false hg]
      exact pairsOne_eq v cc t


private theorem filter_congr_all {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = q x) →
      l.filter p = l.filter q
  | [], _ => rfl
  | a :: t, h => by
    rw [ground.filter_cons p a t, ground.filter_cons q a t,
      h a (List.Mem.head t),
      filter_congr_all p q t (fun x hx => h x (List.Mem.tail a hx))]


private theorem partners_mem {α cc : List Nat} {B : List HVec}
    {w : HVec}
    (h : w ∈ partnersAt α B cc) :
    w ∈ B ∧ List.zipWith (fun x y => x + y) α w.content = cc :=
  match ground.mem_filter_of _ B w h with
  | ⟨hb, hp⟩ => ⟨hb, of_decide_eq_true hp⟩

private theorem partners_group (α cc : List Nat) (d : Nat)
    (B : List HVec) (hwidB : ∀ w ∈ B, w.content.length = d)
    (hαd : α.length = d) (w0 : HVec) (hw0 : w0 ∈ partnersAt α B cc) :
    partnersAt α B cc = B.filter (fun w => w.content == w0.content) := by
  obtain ⟨hb0, hg0⟩ := partners_mem hw0
  refine filter_congr_all _ _ B (fun w hw => ?_)
  cases hbe : (w.content == w0.content) with
  | true =>
    refine decide_eq_true ?_
    rw [ground.listBeqEq hbe]
    exact hg0
  | false =>
    cases hde : decide (List.zipWith (fun x y => x + y) α w.content
        = cc) with
    | false => rfl
    | true =>
      have hgw := of_decide_eq_true hde
      have : w.content = w0.content :=
        zipWith_add_cancelL α w.content w0.content d hαd
          (hwidB w hw) (hwidB w0 hb0) (hgw.trans hg0.symm)
      rw [this, ground.listEqBeq w0.content] at hbe
      exact Bool.noConfusion hbe

private theorem groupAt_partners (α cc : List Nat) (d : Nat)
    (B : List HVec) (hwidB : ∀ w ∈ B, w.content.length = d)
    (hαd : α.length = d) (w0 : HVec) (hw0 : w0 ∈ partnersAt α B cc) :
    groupAt B w0.content = (partnersAt α B cc).map HVec.coords := by
  rw [partners_group α cc d B hwidB hαd w0 hw0]
  rfl


private theorem pairs_mem {A B : List HVec} {cc : List Nat} {p : HVec}
    (h : p ∈ pairsAt A B cc) :
    ∃ v w, v ∈ A ∧ w ∈ B
      ∧ List.zipWith (fun x y => x + y) v.content w.content = cc
      ∧ tensorH v w = p := by
  obtain ⟨v, hv, hp⟩ :=
    ground.mem_flatMap_of (fun v => pairsOne v B cc) A p h
  rw [pairsOne_eq v cc B] at hp
  obtain ⟨w, hw, hwp⟩ :=
    ground.mem_map_of (tensorH v) (partnersAt v.content B cc) p hp
  obtain ⟨hwB, hg⟩ := partners_mem hw
  exact ⟨v, w, hv, hwB, hg, hwp⟩

private theorem pairs_coordLen (A B : List HVec) (cc : List Nat) :
    ∀ p ∈ pairsAt A B cc,
      p.coords.length = (monomialsAt cc).length := by
  intro p hp
  obtain ⟨v, w, _, _, hg, hvw⟩ := pairs_mem hp
  rw [← hvw]
  have hs := tensorH_sized v w
  show (tensorH v w).coords.length = (monomialsAt cc).length
  rw [hs, content_tensorH v w, hg]

private def chunkFit (B : List HVec) (cc : List Nat) :
    List HVec → List (List BPair) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | v :: A, c :: C =>
    c.length = (pairsOne v B cc).length ∧ chunkFit B cc A C

private theorem chunks_exists (B : List HVec) (cc : List Nat) :
    ∀ (A : List HVec) (cs : List BPair),
      cs.length = (pairsAt A B cc).length →
      ∃ C : List (List BPair), C.flatten = cs ∧ chunkFit B cc A C
  | [], cs, h =>
    ⟨[], (ground.nil_of_length_zero cs h).symm, trivial⟩
  | v :: A, cs, h => by
    have hsum : cs.length
        = (pairsOne v B cc).length + (pairsAt A B cc).length := by
      rw [h]
      exact ground.length_append (pairsOne v B cc) (pairsAt A B cc)
    obtain ⟨a, b, hab, hal⟩ := ground.listSplit cs
      (pairsOne v B cc).length
      (by rw [hsum]; exact Nat.le_add_right _ _)
    have hbl : b.length = (pairsAt A B cc).length := by
      have h1 : a.length + b.length
          = (pairsOne v B cc).length + (pairsAt A B cc).length := by
        rw [← ground.length_append a b, ← hab, hsum]
      rw [hal] at h1
      exact ground.addCancelL _ h1
    obtain ⟨C, hC, hfit⟩ := chunks_exists B cc A b hbl
    refine ⟨a :: C, ?_, ⟨hal, hfit⟩⟩
    show a ++ C.flatten = cs
    rw [hC, hab]


private def dotRow (r : List BPair) (p : HVec) : BPair :=
  elim.dotP r p.coords

private def gvec (α : List Nat) (B : List HVec) (cc : List Nat)
    (wl : HVec) : List BPair :=
  (partnersAt α B cc).map (dotRow wl.coords)

private def chunksAt (α : List Nat) :
    List HVec → List (List BPair) → List (List BPair)
  | [], _ => []
  | _ :: _, [] => []
  | v :: A, c :: C =>
    match v.content == α with
    | true => c :: chunksAt α A C
    | false => chunksAt α A C

private def chunkCol (j : Nat) (C : List (List BPair)) : List BPair :=
  C.map (fun ch => ground.getAt BPair.unit ch j)

private def fvecOf (α : List Nat) (r : List BPair) (len : Nat) :
    List HVec → List (List BPair) → List BPair
  | [], _ => List.replicate len BPair.unit
  | _ :: _, [] => List.replicate len BPair.unit
  | v :: A, c :: C =>
    match v.content == α with
    | true =>
      elim.vecAdd (elim.vecScale (elim.dotP r v.coords) c)
        (fvecOf α r len A C)
    | false => fvecOf α r len A C

private theorem partners_content {α cc : List Nat} {B : List HVec}
    (d : Nat) (hwidB : ∀ w ∈ B, w.content.length = d)
    (hαd : α.length = d) {w w' : HVec}
    (hw : w ∈ partnersAt α B cc) (hw' : w' ∈ partnersAt α B cc) :
    w.content = w'.content := by
  obtain ⟨hwB, hgw⟩ := partners_mem hw
  obtain ⟨hwB', hgw'⟩ := partners_mem hw'
  exact zipWith_add_cancelL α w.content w'.content d hαd
    (hwidB w hwB) (hwidB w' hwB') (hgw.trans hgw'.symm)

private theorem chunksAt_cons_pos (α : List Nat) (v : HVec)
    (A : List HVec) (c : List BPair) (C : List (List BPair))
    (hb : (v.content == α) = true) :
    chunksAt α (v :: A) (c :: C) = c :: chunksAt α A C := by
  show (match v.content == α with
      | true => c :: chunksAt α A C
      | false => chunksAt α A C) = c :: chunksAt α A C
  rw [hb]

private theorem chunksAt_cons_neg (α : List Nat) (v : HVec)
    (A : List HVec) (c : List BPair) (C : List (List BPair))
    (hb : (v.content == α) = false) :
    chunksAt α (v :: A) (c :: C) = chunksAt α A C := by
  show (match v.content == α with
      | true => c :: chunksAt α A C
      | false => chunksAt α A C) = chunksAt α A C
  rw [hb]

private theorem fvecOf_cons_pos (α : List Nat) (r : List BPair)
    (len : Nat) (v : HVec) (A : List HVec) (c : List BPair)
    (C : List (List BPair)) (hb : (v.content == α) = true) :
    fvecOf α r len (v :: A) (c :: C)
      = elim.vecAdd (elim.vecScale (elim.dotP r v.coords) c)
        (fvecOf α r len A C) := by
  show (match v.content == α with
      | true =>
        elim.vecAdd (elim.vecScale (elim.dotP r v.coords) c)
          (fvecOf α r len A C)
      | false => fvecOf α r len A C)
    = elim.vecAdd (elim.vecScale (elim.dotP r v.coords) c)
      (fvecOf α r len A C)
  rw [hb]

private theorem fvecOf_cons_neg (α : List Nat) (r : List BPair)
    (len : Nat) (v : HVec) (A : List HVec) (c : List BPair)
    (C : List (List BPair)) (hb : (v.content == α) = false) :
    fvecOf α r len (v :: A) (c :: C) = fvecOf α r len A C := by
  show (match v.content == α with
      | true =>
        elim.vecAdd (elim.vecScale (elim.dotP r v.coords) c)
          (fvecOf α r len A C)
      | false => fvecOf α r len A C)
    = fvecOf α r len A C
  rw [hb]

private theorem unitTail_at : ∀ (u : List BPair) (j : Nat),
    poly.unitTail u →
    (ground.getAt BPair.unit u j).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl BPair.unit
  | _ :: _, 0, h => h.1
  | _ :: t, j + 1, h => unitTail_at t j h.2

private theorem length_chunksAt (α : List Nat) :
    ∀ (A : List HVec) (C : List (List BPair)), A.length = C.length →
      (chunksAt α A C).length
        = (A.filter (fun v => v.content == α)).length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | v :: A, c :: C, h => by
    cases hb : (v.content == α) with
    | true =>
      rw [chunksAt_cons_pos α v A c C hb,
        List.filter_cons_of_pos (p := fun x => x.content == α)
          (a := v) (l := A) hb]
      show (chunksAt α A C).length + 1
        = (A.filter (fun v => v.content == α)).length + 1
      rw [length_chunksAt α A C (Nat.succ.inj h)]
    | false =>
      rw [chunksAt_cons_neg α v A c C hb,
        List.filter_cons_of_neg (p := fun x => x.content == α)
          (a := v) (l := A) (ground.boolNe hb)]
      exact length_chunksAt α A C (Nat.succ.inj h)

private theorem length_fvecOf (B : List HVec) (cc α : List Nat)
    (r : List BPair) :
    ∀ (A : List HVec) (C : List (List BPair)), chunkFit B cc A C →
      (fvecOf α r ((partnersAt α B cc).length) A C).length
        = (partnersAt α B cc).length
  | [], [], _ => ground.length_replicate BPair.unit _
  | [], _ :: _, hfit => nomatch hfit
  | _ :: _, [], hfit => nomatch hfit
  | v :: A, c :: C, hfit => by
    cases hb : (v.content == α) with
    | true =>
      rw [fvecOf_cons_pos α r ((partnersAt α B cc).length) v A c C
        hb]
      refine elim.length_vecAdd _ _ _ ?_ ?_
      · rw [elim.length_vecScale, hfit.1, pairsOne_eq v cc B,
          ground.length_map, ground.listBeqEq hb]
      · exact length_fvecOf B cc α r A C hfit.2
    | false =>
      rw [fvecOf_cons_neg α r ((partnersAt α B cc).length) v A c C
        hb]
      exact length_fvecOf B cc α r A C hfit.2

private theorem getAt_fvecOf (B : List HVec) (cc α : List Nat)
    (r : List BPair) (j : Nat)
    (hj : j < (partnersAt α B cc).length) :
    ∀ (A : List HVec) (C : List (List BPair)), chunkFit B cc A C →
      (ground.getAt BPair.unit
          (fvecOf α r ((partnersAt α B cc).length) A C) j).oneValue
        (elim.dotP (chunkCol j (chunksAt α A C))
          ((A.filter (fun v => v.content == α)).map (dotRow r)))
  | [], [], _ => by
    show (ground.getAt BPair.unit
        (List.replicate ((partnersAt α B cc).length) BPair.unit)
        j).oneValue
      (elim.dotP (chunkCol j (chunksAt α [] []))
        ((([] : List HVec).filter (fun v => v.content == α)).map
          (dotRow r)))
    rw [ground.getAt_replicate_self BPair.unit
      ((partnersAt α B cc).length) j]
    exact BPair.oneValue_refl BPair.unit
  | [], _ :: _, hfit => nomatch hfit
  | _ :: _, [], hfit => nomatch hfit
  | v :: A, c :: C, hfit => by
    cases hb : (v.content == α) with
    | true =>
      rw [fvecOf_cons_pos α r ((partnersAt α B cc).length) v A c C
          hb,
        chunksAt_cons_pos α v A c C hb,
        List.filter_cons_of_pos (p := fun x => x.content == α)
          (a := v) (l := A) hb]
      have hcl : c.length = (partnersAt α B cc).length := by
        rw [hfit.1, pairsOne_eq v cc B, ground.length_map,
          ground.listBeqEq hb]
      rw [elim.getAt_vecAdd _ _ j
          (by rw [elim.length_vecScale, hcl]; exact hj)
          (by rw [length_fvecOf B cc α r A C hfit.2]; exact hj),
        elim.getAt_vecScale (elim.dotP r v.coords) c j
          (by rw [hcl]; exact hj)]
      show (elim.dotP r v.coords * ground.getAt BPair.unit c j
          + ground.getAt BPair.unit
            (fvecOf α r ((partnersAt α B cc).length) A C)
            j).oneValue
        (ground.getAt BPair.unit c j * elim.dotP r v.coords
          + elim.dotP (chunkCol j (chunksAt α A C))
            ((A.filter (fun v => v.content == α)).map (dotRow r)))
      exact BPair.add_congr
        (BPair.oneValue_of_eq
          (BPair.mul_comm (elim.dotP r v.coords)
            (ground.getAt BPair.unit c j)))
        (getAt_fvecOf B cc α r j hj A C hfit.2)
    | false =>
      rw [fvecOf_cons_neg α r ((partnersAt α B cc).length) v A c C
          hb,
        chunksAt_cons_neg α v A c C hb,
        List.filter_cons_of_neg (p := fun x => x.content == α)
          (a := v) (l := A) (ground.boolNe hb)]
      exact getAt_fvecOf B cc α r j hj A C hfit.2

private theorem contract (B : List HVec) (cc α : List Nat) (d kA : Nat)
    (vk wl : HVec)
    (hszB : ∀ w ∈ B, sized w)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hszvk : sized vk) (hwidvk : vk.content.length = d)
    (hvkc : vk.content = α) (hdegvk : sumNat vk.content = kA)
    (hαd : α.length = d) (hwl : wl ∈ partnersAt α B cc) :
    ∀ (A : List HVec) (C : List (List BPair)),
      (∀ v ∈ A, sized v) → (∀ v ∈ A, v.content.length = d) →
      (∀ v ∈ A, sumNat v.content = kA) → chunkFit B cc A C →
      (elim.dotP (C.flatten)
          ((pairsAt A B cc).map
            (dotRow (tensorH vk wl).coords))).oneValue
        (elim.dotP
          (fvecOf α vk.coords ((partnersAt α B cc).length) A C)
          (gvec α B cc wl))
  | [], [], _, _, _, _ => by
    refine BPair.oneValue_trans
      (elim.dotP_null_tail_left ([] : List BPair) _ trivial) ?_
    exact BPair.oneValue_symm
      (elim.dotP_null_tail_left _ (gvec α B cc wl)
        (poly.unitTail_replicate _))
  | [], _ :: _, _, _, _, hfit => nomatch hfit
  | _ :: _, [], _, _, _, hfit => nomatch hfit
  | v :: A, c :: C, hsz, hwid, hdeg, hfit => by
    have hvB : v ∈ v :: A := List.Mem.head A
    have hIH := contract B cc α d kA vk wl hszB hwidB hszvk hwidvk
      hvkc hdegvk hαd hwl A C (memAll_tail hsz) (memAll_tail hwid)
      (memAll_tail hdeg) hfit.2
    have hsplit :
        (elim.dotP (c ++ C.flatten)
          ((pairsOne v B cc).map (dotRow (tensorH vk wl).coords)
            ++ (pairsAt A B cc).map
              (dotRow (tensorH vk wl).coords))).oneValue
          (elim.dotP c ((pairsOne v B cc).map
              (dotRow (tensorH vk wl).coords))
            + elim.dotP (C.flatten) ((pairsAt A B cc).map
              (dotRow (tensorH vk wl).coords))) :=
      elim.dotP_append c _ (C.flatten) _
        (by rw [ground.length_map]; exact hfit.1)
    show (elim.dotP (c ++ C.flatten)
        ((pairsOne v B cc ++ pairsAt A B cc).map
          (dotRow (tensorH vk wl).coords))).oneValue _
    rw [ground.map_append (dotRow (tensorH vk wl).coords)
      (pairsOne v B cc) (pairsAt A B cc)]
    cases hb : (v.content == α) with
    | true =>
      have hvα : v.content = α := ground.listBeqEq hb
      have hone : (pairsOne v B cc).map
          (dotRow (tensorH vk wl).coords)
          = (partnersAt α B cc).map (fun w =>
            elim.dotP (tensorH vk wl).coords
              (tensorH v w).coords) := by
        rw [pairsOne_eq v cc B, hvα,
          ground.map_map (tensorH v)
            (dotRow (tensorH vk wl).coords) (partnersAt α B cc)]
        rfl
      have hprod : poly.oneValue
          ((partnersAt α B cc).map (fun w =>
            elim.dotP (tensorH vk wl).coords (tensorH v w).coords))
          ((partnersAt α B cc).map (fun w =>
            elim.dotP vk.coords v.coords
              * elim.dotP wl.coords w.coords)) := by
        refine poly.oneValue_map _ _ (partnersAt α B cc)
          (fun w hw => ?_)
        obtain ⟨hwB, _⟩ := partners_mem hw
        obtain ⟨hwlB, _⟩ := partners_mem hwl
        exact dotP_tensorH vk wl v w hszvk (hszB wl hwlB)
          (hsz v hvB) (hszB w hwB)
          (by rw [hwidvk, hwidB wl hwlB]) (by rw [hvkc, hvα])
          (partners_content d hwidB hαd hwl hw)
      have hscale : (partnersAt α B cc).map (fun w =>
          elim.dotP vk.coords v.coords
            * elim.dotP wl.coords w.coords)
          = elim.vecScale (elim.dotP vk.coords v.coords)
            (gvec α B cc wl) := by
        show _ = ((partnersAt α B cc).map (dotRow wl.coords)).map
          (fun x => elim.dotP vk.coords v.coords * x)
        rw [ground.map_map (dotRow wl.coords)
          (fun x => elim.dotP vk.coords v.coords * x)
          (partnersAt α B cc)]
        rfl
      have hswap : (elim.dotP
          (elim.vecScale (elim.dotP vk.coords v.coords) c)
          (gvec α B cc wl)).oneValue
          (elim.dotP vk.coords v.coords
            * elim.dotP c (gvec α B cc wl)) := by
        rw [elim.dotP_comm
          (elim.vecScale (elim.dotP vk.coords v.coords) c)
          (gvec α B cc wl)]
        refine BPair.oneValue_trans
          (elim.dotP_vecScale_right (gvec α B cc wl) c
            (elim.dotP vk.coords v.coords)) ?_
        rw [elim.dotP_comm (gvec α B cc wl) c]
        exact BPair.oneValue_refl _
      have hhead : (elim.dotP c ((pairsOne v B cc).map
          (dotRow (tensorH vk wl).coords))).oneValue
          (elim.dotP
            (elim.vecScale (elim.dotP vk.coords v.coords) c)
            (gvec α B cc wl)) := by
        rw [hone]
        refine BPair.oneValue_trans
          (elim.dotP_oneValue_right c _ _ hprod) ?_
        rw [hscale]
        refine BPair.oneValue_trans
          (elim.dotP_vecScale_right c (gvec α B cc wl)
            (elim.dotP vk.coords v.coords)) ?_
        exact BPair.oneValue_symm hswap
      have hclen : (elim.vecScale (elim.dotP vk.coords v.coords)
          c).length = (partnersAt α B cc).length := by
        rw [elim.length_vecScale, hfit.1, pairsOne_eq v cc B,
          ground.length_map, hvα]
      have hglen : (gvec α B cc wl).length
          = (partnersAt α B cc).length := by
        show ((partnersAt α B cc).map (dotRow wl.coords)).length = _
        exact ground.length_map (dotRow wl.coords)
          (partnersAt α B cc)
      have hrlen : (fvecOf α vk.coords ((partnersAt α B cc).length)
          A C).length = (partnersAt α B cc).length :=
        length_fvecOf B cc α vk.coords A C hfit.2
      refine BPair.oneValue_trans hsplit ?_
      rw [fvecOf_cons_pos α vk.coords ((partnersAt α B cc).length)
        v A c C hb]
      refine BPair.oneValue_trans
        (BPair.add_congr hhead hIH) ?_
      exact BPair.oneValue_symm
        (elim.dotP_vecAdd_left
          (elim.vecScale (elim.dotP vk.coords v.coords) c)
          (fvecOf α vk.coords ((partnersAt α B cc).length) A C)
          (gvec α B cc wl)
          (by rw [hglen, hclen]; exact Nat.le_refl _)
          (by rw [hglen, hrlen]; exact Nat.le_refl _))
    | false =>
      have hvα : ¬ (v.content = α) := by
        intro he
        rw [he, ground.listEqBeq α] at hb
        exact Bool.noConfusion hb
      have hnull : poly.unitTail ((pairsOne v B cc).map
          (dotRow (tensorH vk wl).coords)) := by
        rw [pairsOne_eq v cc B,
          ground.map_map (tensorH v)
            (dotRow (tensorH vk wl).coords)
            (partnersAt v.content B cc)]
        refine poly.unitTail_map _ (partnersAt v.content B cc)
          (fun w hw => ?_)
        obtain ⟨hwB, hgw⟩ := partners_mem hw
        obtain ⟨hwlB, hgwl⟩ := partners_mem hwl
        exact dotP_tensorH_off vk wl v w
          (by rw [hwidvk, hwidB wl hwlB])
          (by rw [hwid v hvB, hwidB w hwB])
          (by rw [hdegvk, hdeg v hvB])
          (by rw [content_tensorH vk wl, content_tensorH v w,
            hvkc, hgwl, hgw])
          (by rw [hvkc]; exact fun he => hvα he.symm)
      refine BPair.oneValue_trans hsplit ?_
      rw [fvecOf_cons_neg α vk.coords ((partnersAt α B cc).length)
        v A c C hb]
      refine BPair.oneValue_trans (BPair.add_congr
        (elim.dotP_null_tail_right c _ hnull)
        (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_trans (BPair.unit_add _) hIH

private theorem chunkFit_len (B : List HVec) (cc : List Nat) :
    ∀ (A : List HVec) (C : List (List BPair)), chunkFit B cc A C →
      A.length = C.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: A, _ :: C, h =>
    congrArg Nat.succ (chunkFit_len B cc A C h.2)

private theorem perp_all_rows (n : Nat) (P : List HVec) (f : List BPair)
    (hrows : elim.rowsLen n (P.map HVec.coords))
    (h : ∀ x ∈ P, (elim.dotP f (P.map (dotRow x.coords))).oneValue
      BPair.unit) :
    ∀ l, l < (P.map HVec.coords).length →
      (elim.dotP (elim.combo n f (P.map HVec.coords))
        (ground.getAt [] (P.map HVec.coords) l)).oneValue
        BPair.unit := by
  intro l hl
  have hll : l < P.length := by
    rw [← ground.length_map HVec.coords P]
    exact hl
  have hget : ground.getAt ([] : List BPair) (P.map HVec.coords) l
      = (ground.getAt (⟨[], []⟩ : HVec) P l).coords :=
    ground.getAt_map (⟨[], []⟩ : HVec) ([] : List BPair) HVec.coords
      P l hll
  rw [hget, elim.dotP_comm]
  refine BPair.oneValue_trans
    (elim.dotP_combo f (P.map HVec.coords)
      (ground.getAt (⟨[], []⟩ : HVec) P l).coords n hrows) ?_
  rw [ground.map_map HVec.coords
    (fun row => elim.dotP (ground.getAt (⟨[], []⟩ : HVec) P l).coords
      row) P]
  exact h _ (ground.mem_getAt (⟨[], []⟩ : HVec) P l hll)

private theorem perp_fvec (B : List HVec) (cc : List Nat) (d kA : Nat)
    (hszB : ∀ w ∈ B, sized w)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (α : List Nat) (hαd : α.length = d)
    (A : List HVec) (C : List (List BPair))
    (hsz : ∀ x ∈ A, sized x)
    (hwid : ∀ x ∈ A, x.content.length = d)
    (hdeg : ∀ x ∈ A, sumNat x.content = kA)
    (hfit : chunkFit B cc A C)
    (hperp : ∀ x ∈ A, ∀ y ∈ partnersAt x.content B cc,
      (elim.dotP (C.flatten) ((pairsAt A B cc).map
        (dotRow (tensorH x y).coords))).oneValue BPair.unit)
    (vk : HVec) (hvkA : vk ∈ A) (hvkc : vk.content = α) :
    ∀ wl ∈ partnersAt α B cc,
      (elim.dotP
        (fvecOf α vk.coords ((partnersAt α B cc).length) A C)
        (gvec α B cc wl)).oneValue BPair.unit :=
  fun wl hwl =>
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (contract B cc α d kA vk wl hszB hwidB (hsz vk hvkA)
          (hwid vk hvkA) hvkc (hdeg vk hvkA) hαd hwl A C hsz hwid
          hdeg hfit))
      (hperp vk hvkA wl (by rw [hvkc]; exact hwl))

private theorem head_unit (B : List HVec) (cc : List Nat) (d kA : Nat)
    (hszB : ∀ w ∈ B, sized w)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hiB : indepAll B)
    (v : HVec) (A : List HVec) (c : List BPair)
    (C : List (List BPair))
    (hsz : ∀ x ∈ v :: A, sized x)
    (hwid : ∀ x ∈ v :: A, x.content.length = d)
    (hdeg : ∀ x ∈ v :: A, sumNat x.content = kA)
    (hiA : indepAll (v :: A))
    (hfit : chunkFit B cc (v :: A) (c :: C))
    (hperp : ∀ x ∈ v :: A, ∀ y ∈ partnersAt x.content B cc,
      (elim.dotP ((c :: C).flatten) ((pairsAt (v :: A) B cc).map
        (dotRow (tensorH x y).coords))).oneValue BPair.unit) :
    poly.unitTail c := by
  have hvmem : v ∈ v :: A := List.Mem.head A
  have hαd : v.content.length = d := hwid v hvmem
  have hcl : c.length = (partnersAt v.content B cc).length := by
    rw [hfit.1, pairsOne_eq v cc B, ground.length_map]
  have hfv : ∀ vk ∈ (v :: A).filter
      (fun w => w.content == v.content),
      poly.unitTail (fvecOf v.content vk.coords
        ((partnersAt v.content B cc).length) (v :: A) (c :: C)) := by
    intro vk hvk
    obtain ⟨hvkA, hvkb⟩ :=
      ground.mem_filter_of (fun w => w.content == v.content)
        (v :: A) vk hvk
    have hvkc : vk.content = v.content := ground.listBeqEq hvkb
    have hperpP := perp_fvec B cc d kA hszB hwidB v.content hαd
      (v :: A) (c :: C) hsz hwid hdeg hfit hperp vk hvkA hvkc
    cases hp : partnersAt v.content B cc with
    | nil =>
      rw [← hp]
      have h0 : (fvecOf v.content vk.coords
          ((partnersAt v.content B cc).length) (v :: A)
          (c :: C)).length = 0 := by
        rw [length_fvecOf B cc v.content vk.coords (v :: A) (c :: C)
          hfit, hp]
        rfl
      rw [ground.nil_of_length_zero _ h0]
      exact trivial
    | cons w0 rest =>
      rw [← hp]
      have hw0 : w0 ∈ partnersAt v.content B cc := by
        rw [hp]
        exact List.Mem.head rest
      have hgp : groupAt B w0.content
          = (partnersAt v.content B cc).map HVec.coords :=
        groupAt_partners v.content cc d B hwidB hαd w0 hw0
      have hiBb := indepAll_all hiB w0.content
      rw [hgp] at hiBb
      have hrowsB : elim.rowsLen (monomialsAt w0.content).length
          ((partnersAt v.content B cc).map HVec.coords) := by
        rw [← hgp]
        exact rowsLen_groupAt w0.content B hszB
      refine elim.indep_perp_null (monomialsAt w0.content).length
        ((partnersAt v.content B cc).map HVec.coords) hiBb _
        ?_ ?_
      · rw [ground.length_map]
        exact length_fvecOf B cc v.content vk.coords (v :: A)
          (c :: C) hfit
      · exact perp_all_rows (monomialsAt w0.content).length
          (partnersAt v.content B cc) _ hrowsB hperpP
  refine elim.unitTail_of_getAt c (fun j hj => ?_)
  have hjp : j < (partnersAt v.content B cc).length := by
    rw [← hcl]
    exact hj
  have hcolperp : ∀ vk ∈ (v :: A).filter
      (fun w => w.content == v.content),
      (elim.dotP (chunkCol j (chunksAt v.content (v :: A) (c :: C)))
        (((v :: A).filter (fun w => w.content == v.content)).map
          (dotRow vk.coords))).oneValue BPair.unit := by
    intro vk hvk
    exact BPair.oneValue_trans
      (BPair.oneValue_symm
        (getAt_fvecOf B cc v.content vk.coords j hjp (v :: A)
          (c :: C) hfit))
      (unitTail_at _ j (hfv vk hvk))
  have hcolunit : poly.unitTail
      (chunkCol j (chunksAt v.content (v :: A) (c :: C))) := by
    refine elim.indep_perp_null (monomialsAt v.content).length
      (groupAt (v :: A) v.content) (indepAll_all hiA v.content) _
      ?_ ?_
    · show ((chunksAt v.content (v :: A) (c :: C)).map
          (fun ch => ground.getAt BPair.unit ch j)).length
        = (groupAt (v :: A) v.content).length
      rw [ground.length_map, length_chunksAt v.content (v :: A)
        (c :: C) (chunkFit_len B cc (v :: A) (c :: C) hfit)]
      exact (ground.length_map HVec.coords
        ((v :: A).filter (fun w => w.content == v.content))).symm
    · exact perp_all_rows (monomialsAt v.content).length
        ((v :: A).filter (fun w => w.content == v.content)) _
        (rowsLen_groupAt v.content (v :: A) hsz) hcolperp
  have hhead := unitTail_at
    (chunkCol j (chunksAt v.content (v :: A) (c :: C))) 0 hcolunit
  have hceq : ground.getAt BPair.unit
      (chunkCol j (chunksAt v.content (v :: A) (c :: C))) 0
      = ground.getAt BPair.unit c j := by
    rw [chunksAt_cons_pos v.content v A c C
      (ground.listEqBeq v.content)]
    rfl
  rw [hceq] at hhead
  exact hhead

private theorem indepAll_tail (v : HVec) (A : List HVec)
    (h : indepAll (v :: A)) : indepAll A := by
  intro mu _
  have h1 := indepAll_all h mu
  rw [groupAt_cons v A mu] at h1
  cases hb : (v.content == mu) with
  | true =>
    rw [hb] at h1
    exact elim.indep_tail _ v.coords (groupAt A mu) h1
  | false =>
    rw [hb] at h1
    exact h1

private theorem pairs_null (B : List HVec) (cc : List Nat) (d kA : Nat)
    (hszB : ∀ w ∈ B, sized w)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hiB : indepAll B) :
    ∀ (A : List HVec) (C : List (List BPair)),
      (∀ x ∈ A, sized x) → (∀ x ∈ A, x.content.length = d) →
      (∀ x ∈ A, sumNat x.content = kA) → indepAll A →
      chunkFit B cc A C →
      (∀ x ∈ A, ∀ y ∈ partnersAt x.content B cc,
        (elim.dotP (C.flatten) ((pairsAt A B cc).map
          (dotRow (tensorH x y).coords))).oneValue BPair.unit) →
      poly.unitTail (C.flatten)
  | [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _, hfit, _ => nomatch hfit
  | _ :: _, [], _, _, _, _, hfit, _ => nomatch hfit
  | v :: A, c :: C, hsz, hwid, hdeg, hiA, hfit, hperp => by
    have hc : poly.unitTail c :=
      head_unit B cc d kA hszB hwidB hiB v A c C hsz hwid hdeg hiA
        hfit hperp
    refine elim.unitTail_append hc ?_
    refine pairs_null B cc d kA hszB hwidB hiB A C (memAll_tail hsz)
      (memAll_tail hwid) (memAll_tail hdeg) (indepAll_tail v A hiA)
      hfit.2 ?_
    intro x hx y hy
    have hall := hperp x (List.Mem.tail v hx) y hy
    rw [pairsAt_cons v A B cc,
      ground.map_append (dotRow (tensorH x y).coords)
        (pairsOne v B cc) (pairsAt A B cc)] at hall
    have hsplit := elim.dotP_append c
      ((pairsOne v B cc).map (dotRow (tensorH x y).coords))
      (C.flatten) ((pairsAt A B cc).map (dotRow (tensorH x y).coords))
      (by rw [ground.length_map]; exact hfit.1)
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr
          (elim.dotP_null_tail_left c
            ((pairsOne v B cc).map (dotRow (tensorH x y).coords)) hc)
          (BPair.oneValue_refl (elim.dotP (C.flatten)
            ((pairsAt A B cc).map
              (dotRow (tensorH x y).coords)))))
        (BPair.unit_add _))) ?_
    exact BPair.oneValue_trans (BPair.oneValue_symm hsplit) hall

/-- A group-independent pool's members are sized: a member's
coordinate row sits in its own content group, whose independence
reads the rows at the enumeration's width. -/
private theorem sized_of_indepAll (A : List HVec)
    (hiA : indepAll A) : ∀ v ∈ A, sized v := by
  intro v hv
  have hmem : v.coords ∈ groupAt A v.content :=
    ground.mem_map_to HVec.coords
      (ground.mem_filter_to (fun w => w.content == v.content) hv
        (ground.listEqBeq v.content))
  obtain ⟨k, hk, he⟩ := ground.getAt_of_mem [] hmem
  have hrl := (hiA v.content
    (ground.mem_map_to HVec.content hv)).1
  show v.coords.length = (monomialsAt v.content).length
  rw [← he]
  exact elim.rowsLen_getAt (groupAt A v.content) k hrl hk

/-- The stated pair list is independent: two pairs pair at the
factors' pairings' product, and two pairs at distinct first
contents pair at the sum's unit, so a combination reading the unit
family reads its coefficients back through the two factors in turn
— per first-factor content the second factor's group reads its own
coefficients, and the first factor's groups then read the
coefficients themselves (`lem:blockcount`(iii)); the members'
sized reads are the group independence's own. -/
theorem tensor_indep (A B : List HVec) (cc : List Nat) (d kA : Nat)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hiA : indepAll A) (hiB : indepAll B) :
    elim.indepRows (monomialsAt cc).length
      ((pairsAt A B cc).map HVec.coords) := by
  have hszA : ∀ v ∈ A, sized v := sized_of_indepAll A hiA
  have hszB : ∀ w ∈ B, sized w := sized_of_indepAll B hiB
  have hrows : elim.rowsLen (monomialsAt cc).length
      ((pairsAt A B cc).map HVec.coords) :=
    elim.rowsLen_map HVec.coords (monomialsAt cc).length
      (pairsAt A B cc) (pairs_coordLen A B cc)
  refine elim.indep_intro _ _ hrows ?_
  intro cs hcs hnull
  obtain ⟨C, hC, hfit⟩ := chunks_exists B cc A cs
    (by rw [hcs, ground.length_map])
  rw [← hC]
  refine pairs_null B cc d kA hszB hwidB hiB A C hszA hwidA hdegA
    hiA hfit ?_
  intro x hx y hy
  obtain ⟨hyB, hgy⟩ := partners_mem hy
  have hrl : (tensorH x y).coords.length = (monomialsAt cc).length := by
    rw [tensorH_sized x y, content_tensorH x y, hgy]
  have h3 : (elim.dotP cs
      (((pairsAt A B cc).map HVec.coords).map
        (fun row => elim.dotP (tensorH x y).coords row))).oneValue
      BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (elim.dotP_combo cs ((pairsAt A B cc).map HVec.coords)
          (tensorH x y).coords (monomialsAt cc).length hrows))
      (elim.dotP_null_tail_right _ _ hnull)
  rw [ground.map_map HVec.coords
    (fun row => elim.dotP (tensorH x y).coords row)
    (pairsAt A B cc)] at h3
  rw [hC]
  exact h3

private theorem filterMap_tensor (v : HVec) (cc : List Nat) :
    ∀ B : List HVec,
      (B.map (tensorH v)).filter (fun w => w.content == cc)
        = pairsOne v B cc
  | [] => rfl
  | w :: t => by
    show ((tensorH v w :: t.map (tensorH v)).filter
        (fun w => w.content == cc))
      = (if List.zipWith (fun x y => x + y) v.content w.content = cc
          then [tensorH v w] else []) ++ pairsOne v t cc
    rw [ground.filter_cons (fun w => w.content == cc) (tensorH v w)
      (t.map (tensorH v))]
    by_cases hg : List.zipWith (fun x y => x + y) v.content w.content
        = cc
    · rw [if_pos hg,
        show ((tensorH v w).content == cc) = true from by
          rw [content_tensorH v w, hg]
          exact ground.listEqBeq cc]
      show tensorH v w :: (t.map (tensorH v)).filter
          (fun w => w.content == cc)
        = tensorH v w :: pairsOne v t cc
      rw [filterMap_tensor v cc t]
    · rw [if_neg hg]
      cases hb : ((tensorH v w).content == cc) with
      | true =>
        exact absurd ((content_tensorH v w).symm.trans
          (ground.listBeqEq hb)) hg
      | false =>
        show (t.map (tensorH v)).filter (fun w => w.content == cc)
          = pairsOne v t cc
        exact filterMap_tensor v cc t

private theorem fusedAt_filter (B : List HVec) (cc : List Nat) :
    ∀ A : List HVec,
      (fusedAt A B).filter (fun w => w.content == cc)
        = pairsAt A B cc
  | [] => rfl
  | v :: A => by
    show ((B.map (tensorH v) ++ fusedAt A B).filter
        (fun w => w.content == cc))
      = pairsOne v B cc ++ pairsAt A B cc
    rw [ground.filter_append (fun w => w.content == cc)
        (B.map (tensorH v)) (fusedAt A B),
      filterMap_tensor v cc B, fusedAt_filter B cc A]

/-- The fused pool's content group is the stated pair list's
coordinate family: the fused carrier's filter at a content is the
guarded enumeration itself (`lem:blockcount`(iii)'s stated pair
list at the fused summand). -/
theorem groupAt_fused (A B : List HVec) (cc : List Nat) :
    groupAt (fusedAt A B) cc = (pairsAt A B cc).map HVec.coords := by
  show (((fusedAt A B).filter (fun w => w.content == cc)).map
    HVec.coords) = _
  rw [fusedAt_filter B cc A]

/-- The fused pool's count at a content reads the stated pair
list's own kernel dimension: the pool's content group is the pair
list's coordinate family, and an independent family is its own
collection (`lem:blockcount`(iii); `lem:lowerspan`'s
joined-collection read). -/
theorem countAt_pairs (A B : List HVec) (cc : List Nat)
    (hind : elim.indepRows (monomialsAt cc).length
      ((pairsAt A B cc).map HVec.coords)) :
    countAt (fusedAt A B) cc
      = elim.kernelDim (pairsAt A B cc).length
        (elim.crossM (units.stackedRaise cc)
          ((pairsAt A B cc).map HVec.coords)) := by
  show elim.kernelDim
      (elim.collectOf (monomialsAt cc).length
        (groupAt (fusedAt A B) cc)).length
      (elim.crossM (units.stackedRaise cc)
        (elim.collectOf (monomialsAt cc).length
          (groupAt (fusedAt A B) cc))) = _
  rw [groupAt_fused A B cc,
    elim.collect_keep (monomialsAt cc).length
      ((pairsAt A B cc).map HVec.coords) hind,
    ground.length_map]

/-! `lem:dualread`(ii)'s transport kit: the wedge tensored onto a
coordinate family reads each enumeration place as one wedge
coefficient against one place of the further factor, or as the
sum's unit where the place's split misses the factors' contents —
so the tensored family is additive and scale-equivariant in that
factor, and it withdraws at any one arrangement's own
coefficient. -/

private theorem tensorH_entry_at (u : HVec) (mu : List Nat)
    (hsu : sized u) (hlenU : u.content.length = mu.length)
    (k : Nat) (m1 m2 : List Nat)
    (hk : k < (monomialsAt (List.zipWith (fun a b => a + b)
      u.content mu)).length)
    (hcat : ground.getAt []
        (monomialsAt (List.zipWith (fun a b => a + b)
          u.content mu)) k
      = m1 ++ m2)
    (hl1 : m1.length = sumNat u.content)
    (hl2 : m2.length = sumNat mu) :
    (∃ (c : BPair) (r : Nat), r < (monomialsAt mu).length
        ∧ ∀ x : List BPair, x.length = (monomialsAt mu).length →
            (ground.getAt BPair.unit
              (tensorH u ⟨mu, x⟩).coords k).oneValue
              (c * ground.getAt BPair.unit x r))
      ∨ ∀ x : List BPair,
          (ground.getAt BPair.unit
            (tensorH u ⟨mu, x⟩).coords k).oneValue
            BPair.unit := by
  by_cases hg1 : content u.content.length m1 = u.content
  · by_cases hg2 : content mu.length m2 = mu
    · exact Or.inl ⟨coordAt u m1, rankOf m2 mu,
        (rankOf_read m2 mu hl2 hg2).1,
        fun x hx => tensor_coord_at u ⟨mu, x⟩ hlenU hsu hx k m1 m2
          hk hcat hl1 hg1 hl2 hg2⟩
    · exact Or.inr (fun x => tensor_coord_at_null u ⟨mu, x⟩ hlenU k
        m1 m2 hk hcat hl1 (fun _ hq => hg2 hq.2))
  · exact Or.inr (fun x => tensor_coord_at_null u ⟨mu, x⟩ hlenU k
      m1 m2 hk hcat hl1 (fun hq _ => hg1 hq.2))

private theorem tensorH_entryR (u : HVec) (mu : List Nat)
    (hsu : sized u) (hlenU : u.content.length = mu.length)
    (k : Nat)
    (hk : k < (monomialsAt (List.zipWith (fun a b => a + b)
      u.content mu)).length) :
    (∃ (c : BPair) (r : Nat), r < (monomialsAt mu).length
        ∧ ∀ x : List BPair, x.length = (monomialsAt mu).length →
            (ground.getAt BPair.unit
              (tensorH u ⟨mu, x⟩).coords k).oneValue
              (c * ground.getAt BPair.unit x r))
      ∨ ∀ x : List BPair,
          (ground.getAt BPair.unit
            (tensorH u ⟨mu, x⟩).coords k).oneValue
            BPair.unit := by
  match member_split u (⟨mu, ([] : List BPair)⟩ : HVec) hlenU
      (ground.getAt []
        (monomialsAt (List.zipWith (fun a b => a + b)
          u.content mu)) k)
      (member_conditions (ground.countOf_getAt_pos []
        (monomialsAt (List.zipWith (fun a b => a + b)
          u.content mu)) k hk)).1 with
  | ⟨hcat, hl1, hl2⟩ =>
    exact tensorH_entry_at u mu hsu hlenU k _ _ hk hcat hl1 hl2

private theorem tensorH_entryL_at (nu : List Nat) (u : HVec)
    (hsu : sized u) (hlenU : nu.length = u.content.length)
    (k : Nat) (m1 m2 : List Nat)
    (hk : k < (monomialsAt (List.zipWith (fun a b => a + b)
      nu u.content)).length)
    (hcat : ground.getAt []
        (monomialsAt (List.zipWith (fun a b => a + b)
          nu u.content)) k
      = m1 ++ m2)
    (hl1 : m1.length = sumNat nu)
    (hl2 : m2.length = sumNat u.content) :
    (∃ (c : BPair) (r : Nat), r < (monomialsAt nu).length
        ∧ ∀ x : List BPair, x.length = (monomialsAt nu).length →
            (ground.getAt BPair.unit
              (tensorH ⟨nu, x⟩ u).coords k).oneValue
              (ground.getAt BPair.unit x r * c))
      ∨ ∀ x : List BPair,
          (ground.getAt BPair.unit
            (tensorH ⟨nu, x⟩ u).coords k).oneValue
            BPair.unit := by
  by_cases hg1 : content nu.length m1 = nu
  · by_cases hg2 : content u.content.length m2 = u.content
    · exact Or.inl ⟨coordAt u m2, rankOf m1 nu,
        (rankOf_read m1 nu hl1 hg1).1,
        fun x hx => tensor_coord_at ⟨nu, x⟩ u hlenU hx hsu k m1 m2
          hk hcat hl1 hg1 hl2 hg2⟩
    · exact Or.inr (fun x => tensor_coord_at_null ⟨nu, x⟩ u hlenU k
        m1 m2 hk hcat hl1 (fun _ hq => hg2 hq.2))
  · exact Or.inr (fun x => tensor_coord_at_null ⟨nu, x⟩ u hlenU k
      m1 m2 hk hcat hl1 (fun hq _ => hg1 hq.2))

private theorem tensorH_entryL (nu : List Nat) (u : HVec)
    (hsu : sized u) (hlenU : nu.length = u.content.length)
    (k : Nat)
    (hk : k < (monomialsAt (List.zipWith (fun a b => a + b)
      nu u.content)).length) :
    (∃ (c : BPair) (r : Nat), r < (monomialsAt nu).length
        ∧ ∀ x : List BPair, x.length = (monomialsAt nu).length →
            (ground.getAt BPair.unit
              (tensorH ⟨nu, x⟩ u).coords k).oneValue
              (ground.getAt BPair.unit x r * c))
      ∨ ∀ x : List BPair,
          (ground.getAt BPair.unit
            (tensorH ⟨nu, x⟩ u).coords k).oneValue
            BPair.unit := by
  match member_split (⟨nu, ([] : List BPair)⟩ : HVec) u hlenU
      (ground.getAt []
        (monomialsAt (List.zipWith (fun a b => a + b)
          nu u.content)) k)
      (member_conditions (ground.countOf_getAt_pos []
        (monomialsAt (List.zipWith (fun a b => a + b)
          nu u.content)) k hk)).1 with
  | ⟨hcat, hl1, hl2⟩ =>
    exact tensorH_entryL_at nu u hsu hlenU k _ _ hk hcat hl1 hl2

private theorem tensorH_vecAddR (u : HVec) (mu : List Nat)
    (hsu : sized u) (hlenU : u.content.length = mu.length)
    (a b : List BPair)
    (ha : a.length = (monomialsAt mu).length)
    (hb : b.length = (monomialsAt mu).length) :
    poly.oneValue (tensorH u ⟨mu, elim.vecAdd a b⟩).coords
      (elim.vecAdd (tensorH u ⟨mu, a⟩).coords
        (tensorH u ⟨mu, b⟩).coords) := by
  have hab : (elim.vecAdd a b).length = (monomialsAt mu).length :=
    elim.length_vecAdd a b _ ha hb
  have hS : (tensorH u (⟨mu, elim.vecAdd a b⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        u.content mu)).length :=
    tensorH_sized u ⟨mu, elim.vecAdd a b⟩
  have hA : (tensorH u (⟨mu, a⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        u.content mu)).length := tensorH_sized u ⟨mu, a⟩
  have hB : (tensorH u (⟨mu, b⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        u.content mu)).length := tensorH_sized u ⟨mu, b⟩
  refine poly.oneValue_of_entries _ _ ?_ (fun t ht => ?_)
  · rw [hS, elim.length_vecAdd _ _ _ hA hB]
  · rw [hS] at ht
    rw [elim.getAt_vecAdd _ _ t (by rw [hA]; exact ht)
      (by rw [hB]; exact ht)]
    match tensorH_entryR u mu hsu hlenU t ht with
    | Or.inl ⟨c, r, hr, hent⟩ =>
      refine BPair.oneValue_trans (hent (elim.vecAdd a b) hab) ?_
      rw [elim.getAt_vecAdd a b r (by rw [ha]; exact hr)
          (by rw [hb]; exact hr),
        BPair.left_distrib]
      exact BPair.add_congr (BPair.oneValue_symm (hent a ha))
        (BPair.oneValue_symm (hent b hb))
    | Or.inr hnull =>
      exact BPair.oneValue_trans (hnull (elim.vecAdd a b))
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.add_congr (hnull a) (hnull b))
          (BPair.unit_add BPair.unit)))

private theorem tensorH_vecScaleR (u : HVec) (mu : List Nat)
    (hsu : sized u) (hlenU : u.content.length = mu.length)
    (c : BPair) (a : List BPair)
    (ha : a.length = (monomialsAt mu).length) :
    poly.oneValue (tensorH u ⟨mu, elim.vecScale c a⟩).coords
      (elim.vecScale c (tensorH u ⟨mu, a⟩).coords) := by
  have hca : (elim.vecScale c a).length
      = (monomialsAt mu).length := by
    rw [elim.length_vecScale c a, ha]
  have hS : (tensorH u
        (⟨mu, elim.vecScale c a⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        u.content mu)).length :=
    tensorH_sized u ⟨mu, elim.vecScale c a⟩
  have hA : (tensorH u (⟨mu, a⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        u.content mu)).length := tensorH_sized u ⟨mu, a⟩
  refine poly.oneValue_of_entries _ _ ?_ (fun t ht => ?_)
  · rw [hS, elim.length_vecScale c _, hA]
  · rw [hS] at ht
    rw [elim.getAt_vecScale c _ t (by rw [hA]; exact ht)]
    match tensorH_entryR u mu hsu hlenU t ht with
    | Or.inl ⟨c0, r, hr, hent⟩ =>
      refine BPair.oneValue_trans
        (hent (elim.vecScale c a) hca) ?_
      rw [elim.getAt_vecScale c a r (by rw [ha]; exact hr),
        show c0 * (c * ground.getAt BPair.unit a r)
            = c * (c0 * ground.getAt BPair.unit a r) from by
          rw [← BPair.mul_assoc, BPair.mul_comm c0 c,
            BPair.mul_assoc]]
      exact BPair.mul_congr (BPair.oneValue_refl c)
        (BPair.oneValue_symm (hent a ha))
    | Or.inr hnull =>
      exact BPair.oneValue_trans (hnull (elim.vecScale c a))
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl c) (hnull a))
          (BPair.mul_unit c)))

private theorem tensorH_vecAddL (nu : List Nat) (u : HVec)
    (hsu : sized u) (hlenU : nu.length = u.content.length)
    (a b : List BPair)
    (ha : a.length = (monomialsAt nu).length)
    (hb : b.length = (monomialsAt nu).length) :
    poly.oneValue (tensorH ⟨nu, elim.vecAdd a b⟩ u).coords
      (elim.vecAdd (tensorH ⟨nu, a⟩ u).coords
        (tensorH ⟨nu, b⟩ u).coords) := by
  have hab : (elim.vecAdd a b).length = (monomialsAt nu).length :=
    elim.length_vecAdd a b _ ha hb
  have hS : (tensorH (⟨nu, elim.vecAdd a b⟩ : HVec) u).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        nu u.content)).length :=
    tensorH_sized ⟨nu, elim.vecAdd a b⟩ u
  have hA : (tensorH (⟨nu, a⟩ : HVec) u).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        nu u.content)).length := tensorH_sized ⟨nu, a⟩ u
  have hB : (tensorH (⟨nu, b⟩ : HVec) u).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        nu u.content)).length := tensorH_sized ⟨nu, b⟩ u
  refine poly.oneValue_of_entries _ _ ?_ (fun t ht => ?_)
  · rw [hS, elim.length_vecAdd _ _ _ hA hB]
  · rw [hS] at ht
    rw [elim.getAt_vecAdd _ _ t (by rw [hA]; exact ht)
      (by rw [hB]; exact ht)]
    match tensorH_entryL nu u hsu hlenU t ht with
    | Or.inl ⟨c, r, hr, hent⟩ =>
      refine BPair.oneValue_trans (hent (elim.vecAdd a b) hab) ?_
      rw [elim.getAt_vecAdd a b r (by rw [ha]; exact hr)
          (by rw [hb]; exact hr),
        BPair.right_distrib]
      exact BPair.add_congr (BPair.oneValue_symm (hent a ha))
        (BPair.oneValue_symm (hent b hb))
    | Or.inr hnull =>
      exact BPair.oneValue_trans (hnull (elim.vecAdd a b))
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.add_congr (hnull a) (hnull b))
          (BPair.unit_add BPair.unit)))

private theorem tensorH_vecScaleL (nu : List Nat) (u : HVec)
    (hsu : sized u) (hlenU : nu.length = u.content.length)
    (c : BPair) (a : List BPair)
    (ha : a.length = (monomialsAt nu).length) :
    poly.oneValue (tensorH ⟨nu, elim.vecScale c a⟩ u).coords
      (elim.vecScale c (tensorH ⟨nu, a⟩ u).coords) := by
  have hca : (elim.vecScale c a).length
      = (monomialsAt nu).length := by
    rw [elim.length_vecScale c a, ha]
  have hS : (tensorH (⟨nu, elim.vecScale c a⟩ : HVec)
        u).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        nu u.content)).length :=
    tensorH_sized ⟨nu, elim.vecScale c a⟩ u
  have hA : (tensorH (⟨nu, a⟩ : HVec) u).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        nu u.content)).length := tensorH_sized ⟨nu, a⟩ u
  refine poly.oneValue_of_entries _ _ ?_ (fun t ht => ?_)
  · rw [hS, elim.length_vecScale c _, hA]
  · rw [hS] at ht
    rw [elim.getAt_vecScale c _ t (by rw [hA]; exact ht)]
    match tensorH_entryL nu u hsu hlenU t ht with
    | Or.inl ⟨c0, r, hr, hent⟩ =>
      refine BPair.oneValue_trans
        (hent (elim.vecScale c a) hca) ?_
      rw [elim.getAt_vecScale c a r (by rw [ha]; exact hr),
        show c * ground.getAt BPair.unit a r * c0
            = c * (ground.getAt BPair.unit a r * c0) from
          BPair.mul_assoc _ _ _]
      exact BPair.mul_congr (BPair.oneValue_refl c)
        (BPair.oneValue_symm (hent a ha))
    | Or.inr hnull =>
      exact BPair.oneValue_trans (hnull (elim.vecScale c a))
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl c) (hnull a))
          (BPair.mul_unit c)))

/-- The wedge tensored onto a memberwise sum: the tensored family
is the families' own tensors added, place by place.  The sized
coordinate families are load-bearing on both sides — a mis-sized
family truncates at the memberwise sum, its refusals committed —
and the width binder is the carrier's own frame, `con:places`'
`d_f`-wide contents against the wedge's letter count.  The wedge
is an instance of the general first factor here. -/
theorem tensorW_vecAdd : ∀ (d : Nat) (mu : List Nat)
    (a b : List BPair),
    mu.length = d →
    a.length = (monomialsAt mu).length →
    b.length = (monomialsAt mu).length →
    poly.oneValue
      (tensorH (wedge d d) ⟨mu, elim.vecAdd a b⟩).coords
      (elim.vecAdd (tensorH (wedge d d) ⟨mu, a⟩).coords
        (tensorH (wedge d d) ⟨mu, b⟩).coords) :=
  fun d mu a b hmu ha hb =>
    tensorH_vecAddR (wedge d d) mu (wedge_sized d d)
      (by rw [wedge_clen d d, hmu]) a b ha hb

/-- The wedge tensored onto a rescaled family: the rescaling passes
through the tensor outright.  Both binders are the carrier's frame
here — `con:places`' `d_f`-wide contents and the sized coordinate
family — the rescaling acting entry by entry on either side of the
tensor at any width.  The wedge is an instance of the general
first factor here. -/
theorem tensorW_vecScale : ∀ (d : Nat) (mu : List Nat) (c : BPair)
    (a : List BPair),
    mu.length = d →
    a.length = (monomialsAt mu).length →
    poly.oneValue
      (tensorH (wedge d d) ⟨mu, elim.vecScale c a⟩).coords
      (elim.vecScale c
        (tensorH (wedge d d) ⟨mu, a⟩).coords) :=
  fun d mu c a hmu ha =>
    tensorH_vecScaleR (wedge d d) mu (wedge_sized d d)
      (by rw [wedge_clen d d, hmu]) c a ha

private theorem polyOne_addNeg : ∀ u v : List BPair,
    u.length = v.length → poly.oneValue u v →
    poly.unitTail (elim.vecAdd u
      (elim.vecScale ((BPair.ofNat 1).swap) v))
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | x :: u, y :: v, h, hq =>
    ⟨BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl x) (negMul y))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_comm x y.swap))
          (BPair.swap_add_null (BPair.oneValue_symm hq.1))),
      polyOne_addNeg u v (Nat.succ.inj h) hq.2⟩

private theorem ovOfAddNeg {x y : BPair}
    (h : (x + (BPair.ofNat 1).swap * y).oneValue BPair.unit) :
    x.oneValue y :=
  BPair.oneValue_trans (BPair.oneValue_symm (BPair.add_unit x))
    (BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.add_congr (BPair.oneValue_refl x)
          (BPair.swap_add_null (BPair.oneValue_refl y))))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_assoc x y.swap y).symm)
        (BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl x)
                (BPair.oneValue_symm (negMul y))) h)
            (BPair.oneValue_refl y))
          (BPair.unit_add y))))

private theorem polyOne_ofAddNeg : ∀ u v : List BPair,
    u.length = v.length →
    poly.unitTail (elim.vecAdd u
      (elim.vecScale ((BPair.ofNat 1).swap) v)) →
    poly.oneValue u v
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | _ :: u, _ :: v, h, hq =>
    ⟨ovOfAddNeg hq.1, polyOne_ofAddNeg u v (Nat.succ.inj h) hq.2⟩

/-- The wedge tensored on withdraws: two coordinate families whose
wedge tensors read one value read one value themselves, the wedge's
own family off the unit tail the withdrawal's datum. -/
theorem tensorW_cancel : ∀ (d : Nat) (mu : List Nat)
    (a b : List BPair),
    mu.length = d →
    a.length = (monomialsAt mu).length →
    b.length = (monomialsAt mu).length →
    poly.oneValue (tensorH (wedge d d) ⟨mu, a⟩).coords
      (tensorH (wedge d d) ⟨mu, b⟩).coords →
    poly.oneValue a b := by
  intro d mu a b hmu ha hb h
  have hlenW : (wedge d d).content.length = mu.length := by
    rw [wedge_clen d d, hmu]
  have hnb : (elim.vecScale ((BPair.ofNat 1).swap) b).length
      = (monomialsAt mu).length := by
    rw [elim.length_vecScale _ b, hb]
  have hs : (elim.vecAdd a (elim.vecScale ((BPair.ofNat 1).swap) b)).length
      = (monomialsAt mu).length :=
    elim.length_vecAdd _ _ _ ha hnb
  have hA : (tensorH (wedge d d) (⟨mu, a⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        (wedge d d).content mu)).length :=
    tensorH_sized (wedge d d) ⟨mu, a⟩
  have hB : (tensorH (wedge d d) (⟨mu, b⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        (wedge d d).content mu)).length :=
    tensorH_sized (wedge d d) ⟨mu, b⟩
  have hN : (tensorH (wedge d d)
        (⟨mu, elim.vecScale ((BPair.ofNat 1).swap) b⟩ : HVec)).coords.length
      = (monomialsAt (List.zipWith (fun a b => a + b)
        (wedge d d).content mu)).length :=
    tensorH_sized (wedge d d) ⟨mu, elim.vecScale ((BPair.ofNat 1).swap) b⟩
  have hsum : poly.unitTail (elim.vecAdd
      (tensorH (wedge d d) (⟨mu, a⟩ : HVec)).coords
      (tensorH (wedge d d)
        (⟨mu, elim.vecScale ((BPair.ofNat 1).swap) b⟩ : HVec)).coords) := by
    refine poly.oneValue_unitTail
      (elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _)
        (tensorW_vecScale d mu ((BPair.ofNat 1).swap) b hmu hb)
        rfl (by rw [hN, elim.length_vecScale _ _, hB])) ?_
    exact polyOne_addNeg _ _ (by rw [hA, hB]) h
  have hT : poly.unitTail (tensorH (wedge d d)
      (⟨mu, elim.vecAdd a
        (elim.vecScale ((BPair.ofNat 1).swap) b)⟩ : HVec)).coords :=
    poly.oneValue_unitTail
      (tensorW_vecAdd d mu a (elim.vecScale ((BPair.ofNat 1).swap) b)
        hmu ha hnb) hsum
  refine polyOne_ofAddNeg a b (ha.trans hb.symm) ?_
  match (tensorH_unitTail (wedge d d)
      ⟨mu, elim.vecAdd a (elim.vecScale ((BPair.ofNat 1).swap) b)⟩
      (wedge_sized d d) hs hlenW).mp hT with
  | Or.inl hw => exact absurd hw (wedge_off_unit d)
  | Or.inr hx => exact hx

/-- The wedge-tensored lowering reads the sum's unit wherever the
further factor's own lowerings do: the vacant letter joins at the
unit and the occupied one rebuilds the further factor's image
inside the tensor.  The width binder and the adjacent generators'
index range (`con:units`) are load-bearing with their refusals
committed; the further factor's coordinate width is the carrier's
frame. -/
theorem lowerH_tensorW_unit : ∀ (d j : Nat) (v : HVec),
    sized v → v.content.length = d → j + 1 < d →
    (∀ w, lowerH j v = some w → poly.unitTail w.coords) →
    ∃ u, lowerH j (tensorH (wedge d d) v) = some u
      ∧ poly.unitTail u.coords := by
  intro d j v hsv hvd hj hstep
  by_cases hocc : 0 < ground.getAt 0 v.content j
  · match lowerH_tensorW d j v hsv hvd hj hocc with
    | ⟨u, u', hu, hu', _, hqu⟩ =>
      refine ⟨u, hu, poly.oneValue_unitTail hqu ?_⟩
      refine (tensorH_unitTail (wedge d d) u' (wedge_sized d d)
        (lowerH_sized hu') ?_).mpr (Or.inr (hstep u' hu'))
      rw [wedge_clen d d, (lowerH_reads hu').2,
        units.length_moveDn j v.content, hvd]
  · exact lowerH_tensorW_vacant d j v hsv hvd hj
      (Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hocc))

/-- The wedge-tensored raising reads the sum's unit exactly where
the further factor's own raising does: the letter pair's action
splits over the tensor (`act_tensorH`), the wedge arm reads the
unit at the repeat (`wedge_top`), and the tensor sits at the unit
tail exactly where the further factor does, the wedge's own family
off it (`tensorH_unitTail` at `wedge_off_unit`); at a letter vacant
in the further factor both reads are the sum's unit outright, the
action's own vacant-source read.  The width binder is load-bearing
with its committed refusal; the adjacent generators' index range is
the frame, `con:units`' own — the wedge's raised image reads the
unit at every letter pair, so the range admits its refusal at the
width alone. -/
theorem act_tensorW_unit (d j : Nat) (hj : j + 1 < d) (v : HVec)
    (hsv : sized v) (hvd : v.content.length = d) :
    (poly.unitTail (act j (j + 1) (tensorH (wedge d d) v)).coords
      ↔ poly.unitTail (act j (j + 1) v).coords) := by
  have hjd : j < d := Nat.lt_of_succ_lt hj
  have hWd : (wedge d d).content.length = d := wedge_clen d d
  have hlenWv : (wedge d d).content.length = v.content.length := by
    rw [hWd, hvd]
  have hjW : j < (wedge d d).content.length := by
    rw [hWd]
    exact hjd
  have hj1W : j + 1 < (wedge d d).content.length := by
    rw [hWd]
    exact hj
  have hsplit := act_tensorH j (j + 1) (wedge d d) v
    (wedge_sized d d) hsv hlenWv hjW hj1W
    (fun h => Nat.ne_of_lt (Nat.lt_succ_self j) h)
  have hwidA : (act j (j + 1) (wedge d d)).content.length
      = v.content.length := by
    show (moveAt j (j + 1) (wedge d d).content).length
      = v.content.length
    rw [length_moveAt, hWd, hvd]
  have hArm : poly.unitTail
      (tensorH (act j (j + 1) (wedge d d)) v).coords :=
    (tensorH_unitTail (act j (j + 1) (wedge d d)) v
      (act_sized j (j + 1) (wedge d d)) hsv hwidA).mpr
      (Or.inl (wedge_top d d j hj))
  have hwidB : (wedge d d).content.length
      = (act j (j + 1) v).content.length := by
    show (wedge d d).content.length
      = (moveAt j (j + 1) v.content).length
    rw [length_moveAt, hWd, hvd]
  constructor
  · intro hL
    by_cases hocc : 0 < ground.getAt 0 v.content (j + 1)
    · have hcEq : (tensorH (act j (j + 1) (wedge d d)) v).content
          = (tensorH (wedge d d) (act j (j + 1) v)).content := by
        show List.zipWith (fun a b => a + b)
            (moveAt j (j + 1) (wedge d d).content) v.content
          = List.zipWith (fun a b => a + b) (wedge d d).content
            (moveAt j (j + 1) v.content)
        rw [moveAt_zipWith_left j (j + 1) (wedge d d).content
            v.content
            (by rw [wedge_full_get d (j + 1) hj]
                exact Nat.succ_pos 0),
          moveAt_zipWith_right j (j + 1) (wedge d d).content
            v.content hocc]
      have hlenArm : (tensorH (act j (j + 1) (wedge d d)) v).coords.length
          = (tensorH (wedge d d) (act j (j + 1) v)).coords.length := by
        rw [tensorH_sized (act j (j + 1) (wedge d d)) v,
          tensorH_sized (wedge d d) (act j (j + 1) v), hcEq]
      have hsum : poly.unitTail (elim.vecAdd
          (tensorH (act j (j + 1) (wedge d d)) v).coords
          (tensorH (wedge d d) (act j (j + 1) v)).coords) :=
        poly.unitTail_oneValue_right hL hsplit
      have hB : poly.unitTail
          (tensorH (wedge d d) (act j (j + 1) v)).coords :=
        poly.unitTail_oneValue_right hsum
          (elim.vecAdd_null_left _ _ hlenArm hArm)
      match (tensorH_unitTail (wedge d d) (act j (j + 1) v)
          (wedge_sized d d) (act_sized j (j + 1) v) hwidB).mp hB with
      | Or.inl hw => exact absurd hw (wedge_off_unit d)
      | Or.inr hx => exact hx
    · exact units.matVec_null_unocc (moveAt j (j + 1) v.content)
        v.content j (j + 1)
        (Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hocc)) v.coords
  · intro hR
    refine poly.oneValue_unitTail hsplit (elim.unitTail_vecAdd_of
      hArm ((tensorH_unitTail (wedge d d) (act j (j + 1) v)
        (wedge_sized d d) (act_sized j (j + 1) v) hwidB).mpr
        (Or.inr hR)))

/-! `lem:dualread`(ii)'s stationarity: at a shape whose exhibit's
every interior lowering image reads the sum's unit, the closure's
first round refuses every candidate and the frontier empties, so
the span is the exhibit's own singleton. -/

private theorem foldl_tryAdd_unit :
    ∀ (cands pool : List HVec),
      (∀ v ∈ cands, poly.unitTail v.coords) →
      cands.foldl tryAdd pool = pool
  | [], _, _ => rfl
  | c :: cs, pool, h => by
    show cs.foldl tryAdd (tryAdd pool c) = pool
    rw [show tryAdd pool c = pool from
      if_pos (allU_of_unitTail c.coords
        (memAll_head (P := fun v : HVec => poly.unitTail v.coords)
          h))]
    exact foldl_tryAdd_unit cs pool (memAll_tail h)

private theorem cand_unit (v : HVec) (d : Nat)
    (h : ∀ (j : Nat) (u : HVec), j + 1 < d → lowerH j v = some u →
      poly.unitTail u.coords) :
    ∀ k : Nat, (∀ j, j < k → j + 1 < d) →
      ∀ w ∈ (List.range k).flatMap (fun j =>
          match lowerH j v with
          | some w => [w]
          | none => []), poly.unitTail w.coords
  | 0, _ => memAll_nil
  | k + 1, hk => by
    rw [range_succ k, ground.flatMap_append]
    refine ground.all_of_append _ _ _
      (cand_unit v d h k (fun j hj => hk j (Nat.lt_succ_of_lt hj))) ?_
    show ∀ w ∈ ((match lowerH k v with
        | some w => [w]
        | none => []) ++ []), poly.unitTail w.coords
    rw [ground.append_nil]
    cases hlw : lowerH k v with
    | some w =>
      exact memAll_cons (h k w (hk k (Nat.lt_succ_self k)) hlw)
        memAll_nil
    | none => exact memAll_nil

/-- The stationary span: a column exhibit whose every interior
lowering image reads the sum's unit sits alone in its block's span,
the closure's one round refusing each candidate. -/
theorem blockSpan_stationary : ∀ s : Shape,
    (∀ j u, j + 1 < s.length → lowerH j (exhibit s) = some u →
      poly.unitTail u.coords) →
    blockSpan s = [exhibit s] := by
  intro s h
  have hround : ([exhibit s].flatMap (fun v =>
      (List.range (s.length - 1)).flatMap (fun j =>
        match lowerH j v with
        | some w => [w]
        | none => []))).foldl tryAdd [exhibit s] = [exhibit s] := by
    refine foldl_tryAdd_unit _ _ ?_
    show ∀ w ∈ ((List.range (s.length - 1)).flatMap (fun j =>
        match lowerH j (exhibit s) with
        | some w => [w]
        | none => []) ++ []), poly.unitTail w.coords
    rw [ground.append_nil]
    exact cand_unit (exhibit s) s.length h (s.length - 1)
      (fun _ hj => ground.succ_lt_of_lt_pred hj)
  have key : ∀ fuel : Nat,
      closeSpan s.length fuel [exhibit s] [exhibit s]
        = [exhibit s] := by
    intro fuel
    match fuel with
    | 0 => rfl
    | f + 1 =>
      show (let pool' :=
          ([exhibit s].flatMap (fun v =>
            (List.range (s.length - 1)).flatMap (fun j =>
              match lowerH j v with
              | some w => [w]
              | none => []))).foldl tryAdd [exhibit s]
         closeSpan s.length f pool'
           (pool'.drop [exhibit s].length)) = [exhibit s]
      show closeSpan s.length f
          (([exhibit s].flatMap (fun v =>
            (List.range (s.length - 1)).flatMap (fun j =>
              match lowerH j v with
              | some w => [w]
              | none => []))).foldl tryAdd [exhibit s])
          ((([exhibit s].flatMap (fun v =>
            (List.range (s.length - 1)).flatMap (fun j =>
              match lowerH j v with
              | some w => [w]
              | none => []))).foldl tryAdd [exhibit s]).drop
            [exhibit s].length)
        = [exhibit s]
      rw [hround]
      exact closeSpan_nil s.length f [exhibit s]
  exact key (degree s * s.length)

private theorem grow_ne (pool : List HVec) (c : HVec)
    (t : List HVec) : ¬ (pool ++ [c] ++ t = pool) := by
  intro h
  have hlt : pool.length < ((pool ++ [c]) ++ t).length := by
    rw [ground.length_append (pool ++ [c]) t,
      ground.length_append pool [c]]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self pool.length)
      (Nat.le_add_right (pool.length + 1) t.length)
  rw [h] at hlt
  exact Nat.lt_irrefl _ hlt

private theorem foldl_tryAdd_fix : ∀ (cands pool : List HVec),
    cands.foldl tryAdd pool = pool →
      ∀ v ∈ cands, tryAdd pool v = pool
  | [], _, _ => memAll_nil
  | c :: cs, pool, h => by
    have h' : cs.foldl tryAdd (tryAdd pool c) = pool := h
    cases tryAdd_split pool c with
    | inl he =>
      rw [he] at h'
      exact memAll_cons he (foldl_tryAdd_fix cs pool h')
    | inr he =>
      rw [he] at h'
      obtain ⟨t, ht, _⟩ := foldl_tryAdd_reads (fun _ => True) cs
        (pool ++ [c]) (fun _ _ => trivial)
      rw [ht] at h'
      exact absurd h' (grow_ne pool c t)

/-- A seed closure at one member reads every interior lowering at
the unit tail: the round's candidates each refused the collection,
the refusal the null read or the vacant group's residual, the
residual at the vacant group the coordinates' own
(`lem:lowerspan`'s joined-collection read at the refusals). -/
theorem closeSpan_seed_line (d fuel : Nat) (w : HVec)
    (hlen : (closeSpan d (fuel + 1) [w] [w]).length = 1) :
    ∀ j v, j + 1 < d → lowerH j w = some v →
      poly.unitTail v.coords := by
  intro j v hj hl
  obtain ⟨t1, ht1, _⟩ := foldl_tryAdd_reads (fun _ => True)
    ([w].flatMap (fun u => (List.range (d - 1)).flatMap (fun k =>
      match lowerH k u with
      | some z => [z]
      | none => []))) [w] (fun _ _ => trivial)
  obtain ⟨t2, ht2, _⟩ := closeSpan_reads d (fun _ => True)
    (fun _ => True) (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) fuel
    ([w] ++ t1) t1 (fun _ _ => trivial) (fun _ _ => trivial)
  have hround : closeSpan d (fuel + 1) [w] [w] = [w] ++ t1 ++ t2 := by
    show closeSpan d fuel
        (([w].flatMap (fun u => (List.range (d - 1)).flatMap (fun k =>
          match lowerH k u with
          | some z => [z]
          | none => []))).foldl tryAdd [w])
        ((([w].flatMap (fun u => (List.range (d - 1)).flatMap (fun k =>
          match lowerH k u with
          | some z => [z]
          | none => []))).foldl tryAdd [w]).drop [w].length)
      = [w] ++ t1 ++ t2
    rw [ht1, ground.drop_append_self [w] t1]
    exact ht2
  rw [hround] at hlen
  have ht1nil : t1 = [] := by
    have hL : ([w] ++ t1 ++ t2).length
        = 1 + t1.length + t2.length := by
      rw [ground.length_append ([w] ++ t1) t2,
        ground.length_append [w] t1]
      rfl
    have h3 : 1 + (t1.length + t2.length) = 1 + 0 := by
      rw [← Nat.add_assoc, Nat.add_zero]
      exact hL.symm.trans hlen
    refine ground.nil_of_length_zero t1 (Nat.eq_zero_of_le_zero ?_)
    rw [← ground.addCancelL 1 h3]
    exact Nat.le_add_right t1.length t2.length
  rw [ht1nil, ground.append_nil] at ht1
  have hjd : j < d - 1 := by
    match d, hj with
    | _ + 1, hj => exact Nat.lt_of_succ_lt_succ hj
  have hmem : v ∈ [w].flatMap (fun u =>
      (List.range (d - 1)).flatMap (fun k =>
        match lowerH k u with
        | some z => [z]
        | none => [])) := by
    refine ground.mem_flatMap_to _ (List.Mem.head []) ?_
    refine ground.mem_flatMap_to _ (ground.memRange hjd) ?_
    rw [hl]
    exact List.Mem.head []
  have hfix : tryAdd [w] v = [w] := foldl_tryAdd_fix _ _ ht1 v hmem
  by_cases hall : allU v.coords = true
  · exact unitTail_of_allU v.coords hall
  · have hocc := (lowerH_reads hl).1
    have hcnt := (lowerH_reads hl).2
    have hne : ¬ (w.content = v.content) := by
      intro hc
      have hx := getAt_moveDn_self j w.content hocc
      rw [← hcnt, ← hc] at hx
      exact Nat.succ_ne_self _ hx
    have hgrp : groupAt [w] v.content = [] := by
      rw [groupAt_cons w [] v.content]
      cases hb : w.content == v.content with
      | true => exact absurd (ground.listBeqEq hb) hne
      | false => rfl
    have he : tryAdd [w] v
        = (let group := [w].filter (fun u => u.content == v.content)
           if poly.unitTail (elim.residV v.coords.length
               (group.map HVec.coords) v.coords)
           then [w] else [w] ++ [v]) := if_neg hall
    by_cases h2 : poly.unitTail (elim.residV v.coords.length
        (groupAt [w] v.content) v.coords)
    · rw [hgrp] at h2
      exact elim.spanRel_nil_unit v.coords.length v.coords
        ⟨trivial, rfl, h2⟩
    · exact absurd ((he.trans (if_neg h2)).symm.trans hfix)
        (fun hc => grow_ne [w] v [] (by
          rw [ground.append_nil]
          exact hc))

/-! `lem:blockcount`(iii)'s unit shape: the vacant occupancy family
carries no column, so its exhibit stands at the tensor fold's own
seed — the scalar one at the vacant content — its span is the
exhibit's own singleton, and a tensor against it reads its first
factor back. -/

private theorem exhibit_unitShape (n : Nat) :
    exhibit (List.replicate n 0)
      = (⟨List.replicate n 0, [BPair.ofNat 1]⟩ : HVec) := by
  show (columnLengths (List.replicate n 0)).foldl
      (fun acc l =>
        tensorH acc (wedge (List.replicate n 0).length l))
      ⟨List.replicate (List.replicate n 0).length 0,
        [BPair.ofNat 1]⟩
    = _
  rw [columnLengths_unitShape n]
  show (⟨List.replicate (List.replicate n 0).length 0,
      [BPair.ofNat 1]⟩ : HVec)
    = ⟨List.replicate n 0, [BPair.ofNat 1]⟩
  rw [ground.length_replicate (0 : Nat) n]

/-- The unit shape's span is its exhibit alone: every letter of the
vacant occupancy family's row list is unoccupied, so no interior
lowering is present and the closure's first round refuses outright
(`lem:blockcount`(iii)'s unit line at `blockSpan_stationary`). -/
theorem blockSpan_unitShape (n : Nat) :
    blockSpan (List.replicate n 0)
      = [exhibit (List.replicate n 0)] := by
  refine blockSpan_stationary (List.replicate n 0) ?_
  intro j u _ h
  have hg := (lowerH_reads h).1
  rw [content_exhibit (List.replicate n 0),
    places.rowList_replicate_zero n,
    ground.getAt_replicate_zero n j] at hg
  exact absurd hg (Nat.lt_irrefl 0)

/-- The tensor against the unit shape's exhibit reads its first
factor back: the content joins the vacant family at the unit
summand and the coordinates read the scalar one's own product,
place for place (`lem:blockcount`(iii)'s unit line — the vacant
second arrangement at the enumeration's split). -/
theorem tensorH_unitShape (n : Nat) (x : HVec) (hsx : sized x)
    (hxd : x.content.length = n) :
    (tensorH x (exhibit (List.replicate n 0))).content = x.content
      ∧ poly.oneValue x.coords
        (tensorH x (exhibit (List.replicate n 0))).coords := by
  rw [exhibit_unitShape n]
  exact ⟨(tensorH_seed_right n x hsx hxd).1.symm,
    (tensorH_seed_right n x hsx hxd).2⟩

/-! `lem:dualread`(ii)'s transport tier: the span walk at the
bumped shape corresponds member for member to the wedge-tensored
walk, the correspondence carried through the closure's own
induction. -/

private theorem tensorW_unit_coords (d : Nat) (mu : List Nat)
    (n : Nat) (hmu : mu.length = d)
    (hn : n = (places.monomialsAt mu).length) :
    poly.unitTail
      (tensorH (wedge d d)
        ⟨mu, List.replicate n BPair.unit⟩).coords := by
  refine (tensorH_unitTail (wedge d d)
    ⟨mu, List.replicate n BPair.unit⟩
    (wedge_sized d d) ?_ ?_).mpr (Or.inr ?_)
  · show (List.replicate n BPair.unit).length
      = (places.monomialsAt mu).length
    rw [ground.length_replicate, hn]
  · show (wedge d d).content.length = mu.length
    rw [wedge_clen, hmu]
  · show poly.unitTail (List.replicate n BPair.unit)
    clear hn
    induction n with
    | zero => exact trivial
    | succ m ih => exact ⟨BPair.oneValue_refl _, ih⟩

private theorem tensorW_combo (d : Nat) (mu : List Nat)
    (hmu : mu.length = d) :
    ∀ (cs : List BPair) (L : elim.Mat),
    elim.rowsLen (places.monomialsAt mu).length L →
    poly.oneValue
      (tensorH (wedge d d)
        ⟨mu, elim.combo (places.monomialsAt mu).length cs L⟩).coords
      (elim.combo
        (places.monomialsAt (tensorH (wedge d d)
          ⟨mu, []⟩).content).length cs
        (L.map (fun r =>
          (tensorH (wedge d d) ⟨mu, r⟩).coords)))
  | [], L, _ => by
    show poly.oneValue
      (tensorH (wedge d d)
        ⟨mu, List.replicate (places.monomialsAt mu).length
          BPair.unit⟩).coords
      (List.replicate _ BPair.unit)
    refine poly.unitTail_oneValue
      (tensorW_unit_coords d mu _ hmu rfl) ?_
    exact poly.unitTail_replicate _
  | _ :: _, [], _ => by
    show poly.oneValue
      (tensorH (wedge d d)
        ⟨mu, List.replicate (places.monomialsAt mu).length
          BPair.unit⟩).coords
      (List.replicate _ BPair.unit)
    refine poly.unitTail_oneValue
      (tensorW_unit_coords d mu _ hmu rfl) ?_
    exact poly.unitTail_replicate _
  | c :: cs, r :: L, hL => by
    show poly.oneValue
      (tensorH (wedge d d)
        ⟨mu, elim.vecAdd (elim.vecScale c r)
          (elim.combo (places.monomialsAt mu).length cs L)⟩).coords
      (elim.vecAdd
        (elim.vecScale c
          (tensorH (wedge d d) ⟨mu, r⟩).coords)
        (elim.combo _ cs (L.map (fun r' =>
          (tensorH (wedge d d) ⟨mu, r'⟩).coords))))
    refine poly.oneValue_trans
      (tensorW_vecAdd d mu (elim.vecScale c r)
        (elim.combo (places.monomialsAt mu).length cs L) hmu
        (by rw [elim.length_vecScale, hL.1])
        (elim.length_combo _ cs L hL.2)) ?_
    refine elim.polyOne_vecAdd _ _ _ _
      (tensorW_vecScale d mu c r hmu hL.1)
      (tensorW_combo d mu hmu cs L hL.2)
      ((tensorH_sized (wedge d d) ⟨mu, elim.vecScale c r⟩).trans
        ((elim.length_vecScale c
            (tensorH (wedge d d) ⟨mu, r⟩).coords).trans
          (tensorH_sized (wedge d d) ⟨mu, r⟩)).symm)
      ((tensorH_sized (wedge d d)
          ⟨mu, elim.combo (places.monomialsAt mu).length
            cs L⟩).trans
        (elim.length_combo _ cs
          (L.map (fun r' =>
            (tensorH (wedge d d) ⟨mu, r'⟩).coords))
          (elim.rowsLen_map
            (fun r' => (tensorH (wedge d d) ⟨mu, r'⟩).coords)
            (places.monomialsAt (tensorH (wedge d d)
              (⟨mu, []⟩ : HVec)).content).length L
            (fun x _ => tensorH_sized (wedge d d) ⟨mu, x⟩))).symm)

private theorem tensorW_spanRel_fwd (d : Nat) (mu : List Nat)
    (hmu : mu.length = d) (L : elim.Mat) (v : List BPair)
    (h : elim.spanRel (places.monomialsAt mu).length L v) :
    elim.spanRel
      (places.monomialsAt (tensorH (wedge d d)
        (⟨mu, []⟩ : HVec)).content).length
      (L.map (fun r => (tensorH (wedge d d) ⟨mu, r⟩).coords))
      (tensorH (wedge d d) ⟨mu, v⟩).coords := by
  obtain ⟨c₀, cs, hc₀, hcs, hone⟩ := elim.span_elim h
  refine elim.span_intro _ _ _
    (elim.rowsLen_map
      (fun r => (tensorH (wedge d d) ⟨mu, r⟩).coords)
      (places.monomialsAt (tensorH (wedge d d)
        (⟨mu, []⟩ : HVec)).content).length L
      (fun x _ => tensorH_sized (wedge d d) ⟨mu, x⟩))
    (tensorH_sized (wedge d d) ⟨mu, v⟩)
    ⟨c₀, cs, hc₀,
      by rw [ground.length_map]; exact hcs, ?_⟩
  refine poly.oneValue_trans
    (poly.oneValue_symm (tensorW_vecScale d mu c₀ v hmu h.2.1)) ?_
  refine poly.oneValue_trans ?_
    (tensorW_combo d mu hmu cs L h.1)
  exact tensorH_polyOne (wedge d d) (wedge d d)
    ⟨mu, elim.vecScale c₀ v⟩
    ⟨mu, elim.combo (places.monomialsAt mu).length cs L⟩
    (wedge_sized d d) (wedge_sized d d)
    (by show (elim.vecScale c₀ v).length
          = (places.monomialsAt mu).length
        rw [elim.length_vecScale]
        exact h.2.1)
    (by show (elim.combo (places.monomialsAt mu).length
            cs L).length
          = (places.monomialsAt mu).length
        exact elim.length_combo _ cs L h.1)
    rfl rfl (poly.oneValue_refl _) hone

private theorem tensorW_spanRel_back (d : Nat) (mu : List Nat)
    (hmu : mu.length = d) (L : elim.Mat) (v : List BPair)
    (hL : elim.rowsLen (places.monomialsAt mu).length L)
    (hv : v.length = (places.monomialsAt mu).length)
    (h : elim.spanRel
      (places.monomialsAt (tensorH (wedge d d)
        (⟨mu, []⟩ : HVec)).content).length
      (L.map (fun r => (tensorH (wedge d d) ⟨mu, r⟩).coords))
      (tensorH (wedge d d) ⟨mu, v⟩).coords) :
    elim.spanRel (places.monomialsAt mu).length L v := by
  obtain ⟨c₀, cs, hc₀, hcs, hone⟩ := elim.span_elim h
  refine elim.span_intro _ _ _ hL hv
    ⟨c₀, cs, hc₀,
      hcs.trans (ground.length_map _ L), ?_⟩
  refine tensorW_cancel d mu (elim.vecScale c₀ v)
    (elim.combo (places.monomialsAt mu).length cs L) hmu
    (by rw [elim.length_vecScale]; exact hv)
    (elim.length_combo _ cs L hL) ?_
  refine poly.oneValue_trans
    (tensorW_vecScale d mu c₀ v hmu hv) ?_
  refine poly.oneValue_trans hone ?_
  exact poly.oneValue_symm (tensorW_combo d mu hmu cs L hL)

private theorem spanRel_rows (n : Nat) (L L' : elim.Mat)
    (hL : elim.rowsLen n L) (hL' : elim.rowsLen n L')
    (hM : elim.matOneValue L L') (v : List BPair)
    (h : elim.spanRel n L v) : elim.spanRel n L' v :=
  elim.spanRel_trans n L L' v hL hL'
    (fun k hk =>
      elim.spanRel_congr n L' (ground.getAt [] L' k)
        (ground.getAt [] L k)
        (poly.oneValue_symm (elim.matOne_entries L L' hM k hk))
        (elim.spanRel_getAt n L' k
          (by rw [← elim.matOne_length hM]; exact hk) hL')
        (elim.rowsLen_getAt L k hL hk))
    h

/-! The lockstep correspondence: the bumped shape's walk beside the
wedge-tensored walk, pool against pool member for member — each
partner's content the tensor's own and its coordinates the tensor's
one-value class. -/

private def corrH (d : Nat) (v w : HVec) : Prop :=
  w.content = (tensorH (wedge d d) v).content
    ∧ poly.oneValue w.coords (tensorH (wedge d d) v).coords

private def corrP (d : Nat) : List HVec → List HVec → Prop :=
  ground.matchedOV
    ⟨corrH d, fun _ _ => inferInstanceAs (Decidable (_ = _ ∧ _))⟩

private theorem corrP_length (d : Nat) {Q P : List HVec}
    (h : corrP d Q P) : Q.length = P.length :=
  ground.matched_length h

private theorem corrP_append (d : Nat) : ∀ {Q P Q' P' : List HVec},
    corrP d Q P → corrP d Q' P' → corrP d (Q ++ Q') (P ++ P')
  | [], [], _, _, _, h' => h'
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, _, _, h, h' => ⟨h.1, corrP_append d h.2 h'⟩

private theorem unitTail_tensorW (d : Nat) (v : HVec)
    (hs : sized v) (hlen : v.content.length = d) :
    poly.unitTail (tensorH (wedge d d) v).coords
      ↔ poly.unitTail v.coords := by
  have hcl : (wedge d d).content.length = v.content.length := by
    rw [wedge_clen d d, hlen]
  constructor
  · intro h
    match (tensorH_unitTail (wedge d d) v (wedge_sized d d)
        hs hcl).mp h with
    | Or.inl hw => exact absurd hw (wedge_off_unit d)
    | Or.inr hx => exact hx
  · intro h
    exact (tensorH_unitTail (wedge d d) v (wedge_sized d d)
      hs hcl).mpr (Or.inr h)

private theorem groupAt_corr (d : Nat) : ∀ (Q P : List HVec),
    corrP d Q P → (∀ x ∈ Q, x.content.length = d) →
    ∀ mu : List Nat, mu.length = d →
    elim.matOneValue
      (groupAt P (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content)
      ((groupAt Q mu).map (fun r =>
        (tensorH (wedge d d) (⟨mu, r⟩ : HVec)).coords))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | v :: Q, w :: P, h, hd, mu, hmu => by
    rw [groupAt_cons w P
        (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content,
      groupAt_cons v Q mu]
    cases hb : v.content == mu with
    | true =>
      have hveq : v.content = mu := ground.listBeqEq hb
      have hw : w.content
          = (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content := by
        refine Eq.trans (show w.content
          = (tensorH (wedge d d) v).content from h.1.1) ?_
        show List.zipWith (fun a b => a + b) (wedge d d).content
            v.content
          = List.zipWith (fun a b => a + b) (wedge d d).content mu
        rw [hveq]
      cases hb2 : w.content
          == (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content with
      | false =>
        rw [hw, ground.listEqBeq] at hb2
        exact Bool.noConfusion hb2
      | true =>
        refine ⟨?_, groupAt_corr d Q P h.2 (memAll_tail hd) mu hmu⟩
        show poly.oneValue w.coords
          (tensorH (wedge d d) (⟨mu, v.coords⟩ : HVec)).coords
        have hv' : (⟨mu, v.coords⟩ : HVec) = v := by
          rw [← hveq]
        rw [hv']
        exact h.1.2
    | false =>
      cases hb2 : w.content
          == (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content with
      | true =>
        have hweq := ground.listBeqEq hb2
        have hveq : v.content = mu := by
          refine zipWith_add_cancelL (wedge d d).content
            v.content mu d (wedge_clen d d)
            (memAll_head
              (P := fun x : HVec => x.content.length = d) hd)
            hmu ?_
          refine Eq.trans ?_ hweq
          exact (show w.content
            = (tensorH (wedge d d) v).content from h.1.1).symm
        rw [hveq, ground.listEqBeq] at hb
        exact Bool.noConfusion hb
      | false =>
        exact groupAt_corr d Q P h.2 (memAll_tail hd) mu hmu

private theorem tryAdd_corr (d : Nat) (Qp Pp : List HVec)
    (u' u : HVec)
    (hcorr : corrP d Qp Pp)
    (hsQ : ∀ x ∈ Qp, sized x) (hsP : ∀ x ∈ Pp, sized x)
    (hdQ : ∀ x ∈ Qp, x.content.length = d)
    (hindQ : indepAll Qp) (hindP : indepAll Pp)
    (hsu' : sized u') (hsu : sized u)
    (hdu' : u'.content.length = d)
    (hcu : corrH d u' u) :
    (tryAdd Qp u' = Qp ∧ tryAdd Pp u = Pp)
      ∨ (tryAdd Qp u' = Qp ++ [u'] ∧ tryAdd Pp u = Pp ++ [u]) := by
  have hUfwd : poly.unitTail u.coords → poly.unitTail u'.coords :=
    fun h => (unitTail_tensorW d u' hsu' hdu').mp
      (poly.unitTail_oneValue_right h hcu.2)
  have hUbwd : poly.unitTail u'.coords → poly.unitTail u.coords :=
    fun h => poly.oneValue_unitTail hcu.2
      ((unitTail_tensorW d u' hsu' hdu').mpr h)
  by_cases h1 : allU u'.coords = true
  · exact Or.inl ⟨if_pos h1,
      if_pos (allU_of_unitTail _ (hUbwd (unitTail_of_allU _ h1)))⟩
  · have h1P : ¬ allU u.coords = true := fun hA =>
      h1 (allU_of_unitTail _ (hUfwd (unitTail_of_allU _ hA)))
    have hc2 : u.content
        = (tensorH (wedge d d) (⟨u'.content, []⟩ : HVec)).content :=
      hcu.1
    have hNu : u.coords.length
        = (places.monomialsAt (tensorH (wedge d d)
          (⟨u'.content, []⟩ : HVec)).content).length := by
      rw [hsu, hc2]
    have hLQ : elim.rowsLen u'.coords.length
        (groupAt Qp u'.content) := by
      have h := rowsLen_groupAt u'.content Qp hsQ
      rw [← hsu'] at h
      exact h
    have hindQ' : elim.indepRows u'.coords.length
        (groupAt Qp u'.content) := by
      have h := indepAll_all hindQ u'.content
      rw [← hsu'] at h
      exact h
    have hLP : elim.rowsLen u.coords.length
        (groupAt Pp u.content) := by
      have h := rowsLen_groupAt u.content Pp hsP
      rw [← hsu] at h
      exact h
    have hindP' : elim.indepRows u.coords.length
        (groupAt Pp u.content) := by
      have h := indepAll_all hindP u.content
      rw [← hsu] at h
      exact h
    have hM : elim.matOneValue (groupAt Pp u.content)
        ((groupAt Qp u'.content).map (fun r =>
          (tensorH (wedge d d) (⟨u'.content, r⟩ : HVec)).coords)) := by
      have h := groupAt_corr d Qp Pp hcorr hdQ u'.content hdu'
      rw [← hc2] at h
      exact h
    have hL1 : elim.rowsLen
        (places.monomialsAt (tensorH (wedge d d)
          (⟨u'.content, []⟩ : HVec)).content).length
        ((groupAt Qp u'.content).map (fun r =>
          (tensorH (wedge d d) (⟨u'.content, r⟩ : HVec)).coords)) :=
      elim.rowsLen_map
        (fun r => (tensorH (wedge d d) (⟨u'.content, r⟩ : HVec)).coords)
        (places.monomialsAt (tensorH (wedge d d)
          (⟨u'.content, []⟩ : HVec)).content).length
        (groupAt Qp u'.content)
        (fun x _ => tensorH_sized (wedge d d) ⟨u'.content, x⟩)
    have hL2 : elim.rowsLen
        (places.monomialsAt (tensorH (wedge d d)
          (⟨u'.content, []⟩ : HVec)).content).length
        (groupAt Pp u.content) := by
      rw [← hNu]
      exact hLP
    have hfwd : poly.unitTail (elim.residV u'.coords.length
          (groupAt Qp u'.content) u'.coords) →
        poly.unitTail (elim.residV u.coords.length
          (groupAt Pp u.content) u.coords) := by
      intro ht
      have hsp1 : elim.spanRel (places.monomialsAt u'.content).length
          (groupAt Qp u'.content) u'.coords := by
        rw [← hsu']
        exact elim.resid_sound _ _ _ hLQ rfl
          (elim.indep_det _ _ hindQ') ht
      have hsp2 := tensorW_spanRel_fwd d u'.content hdu'
        (groupAt Qp u'.content) u'.coords hsp1
      have hsp3 := spanRel_rows _
        ((groupAt Qp u'.content).map (fun r =>
          (tensorH (wedge d d) (⟨u'.content, r⟩ : HVec)).coords))
        (groupAt Pp u.content) hL1 hL2 (elim.matOne_symm hM)
        (tensorH (wedge d d) ⟨u'.content, u'.coords⟩).coords hsp2
      have hsp4 := elim.spanRel_congr _ (groupAt Pp u.content)
        (tensorH (wedge d d) (⟨u'.content, u'.coords⟩ : HVec)).coords
        u.coords (poly.oneValue_symm hcu.2) hsp3 hNu
      rw [← hNu] at hsp4
      exact elim.resid_complete _ _ _ hLP rfl hsp4
    have hbwd : poly.unitTail (elim.residV u.coords.length
          (groupAt Pp u.content) u.coords) →
        poly.unitTail (elim.residV u'.coords.length
          (groupAt Qp u'.content) u'.coords) := by
      intro ht
      have hsp1 : elim.spanRel
          (places.monomialsAt (tensorH (wedge d d)
            (⟨u'.content, []⟩ : HVec)).content).length
          (groupAt Pp u.content) u.coords := by
        rw [← hNu]
        exact elim.resid_sound _ _ _ hLP rfl
          (elim.indep_det _ _ hindP') ht
      have hsp2 := elim.spanRel_congr _ (groupAt Pp u.content)
        u.coords
        (tensorH (wedge d d) (⟨u'.content, u'.coords⟩ : HVec)).coords
        hcu.2 hsp1
        (tensorH_sized (wedge d d) ⟨u'.content, u'.coords⟩)
      have hsp3 := spanRel_rows _ (groupAt Pp u.content)
        ((groupAt Qp u'.content).map (fun r =>
          (tensorH (wedge d d) (⟨u'.content, r⟩ : HVec)).coords))
        hL2 hL1 hM
        (tensorH (wedge d d) (⟨u'.content, u'.coords⟩ : HVec)).coords
        hsp2
      have hsp4 := tensorW_spanRel_back d u'.content hdu'
        (groupAt Qp u'.content) u'.coords
        (by rw [← hsu']; exact hLQ) hsu' hsp3
      rw [← hsu'] at hsp4
      exact elim.resid_complete _ _ _ hLQ rfl hsp4
    by_cases h2 : poly.unitTail (elim.residV u'.coords.length
        (groupAt Qp u'.content) u'.coords)
    · exact Or.inl ⟨(if_neg h1).trans (if_pos h2),
        (if_neg h1P).trans (if_pos (hfwd h2))⟩
    · exact Or.inr ⟨(if_neg h1).trans (if_neg h2),
        (if_neg h1P).trans (if_neg (fun hp => h2 (hbwd hp)))⟩

private theorem lowerH_corr (d j : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w)
    (hvd : v.content.length = d) (hj : j + 1 < d)
    (hcw : corrH d v w) :
    ∃ y, lowerH j w = some y ∧ sized y
      ∧ ((∃ x, lowerH j v = some x ∧ sized x
            ∧ x.content.length = d ∧ corrH d x y)
        ∨ (lowerH j v = none ∧ poly.unitTail y.coords)) := by
  have hl : (tensorH (wedge d d) v).coords.length
      = w.coords.length := by
    rw [hsw, hcw.1]
    exact tensorH_sized (wedge d d) v
  by_cases hocc : 0 < ground.getAt 0 v.content j
  · match lowerH_tensorW d j v hsv hvd hj hocc with
    | ⟨u0, x, hu0, hx, hc0, hq0⟩ =>
      match lowerH_move hcw.1.symm
          (poly.oneValue_symm hcw.2) hu0 with
      | ⟨y, hy, hcy, hqy⟩ =>
        refine ⟨y, hy, lowerH_sized hy,
          Or.inl ⟨x, hx, lowerH_sized hx, ?_,
            hcy.symm.trans hc0,
            poly.oneValue_trans (poly.oneValue_symm hqy) hq0⟩⟩
        rw [(lowerH_fields hx).1, units.length_moveDn, hvd]
  · have hvac : ground.getAt 0 v.content j = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hocc)
    match lowerH_tensorW_vacant d j v hsv hvd hj hvac with
    | ⟨u0, hu0, hut⟩ =>
      match lowerH_move hcw.1.symm
          (poly.oneValue_symm hcw.2) hu0 with
      | ⟨y, hy, _, hqy⟩ =>
        exact ⟨y, hy, lowerH_sized hy,
          Or.inr ⟨if_neg hocc,
            poly.unitTail_oneValue_right hut hqy⟩⟩

private theorem tryAdd_indep (pool : List HVec) (v : HVec)
    (hs : ∀ x ∈ pool, sized x) (hv : sized v)
    (hind : indepAll pool) : indepAll (tryAdd pool v) := by
  match tryAdd_sem pool v hs hv hind with
  | Or.inl h =>
    rw [h.1]
    exact hind
  | Or.inr h =>
    rw [h.1]
    exact h.2

private theorem tryAdd_unit_eq (pool : List HVec) (y : HVec)
    (hy : poly.unitTail y.coords) : tryAdd pool y = pool :=
  if_pos (allU_of_unitTail y.coords hy)

private def corrState (d : Nat) (A B : List HVec) : Prop :=
  corrP d A B
    ∧ (∀ x ∈ A, sized x) ∧ (∀ x ∈ B, sized x)
    ∧ (∀ x ∈ A, x.content.length = d)
    ∧ indepAll A ∧ indepAll B

private theorem tryAdd_corrState (d : Nat) (A B : List HVec)
    (x y : HVec) (h : corrState d A B)
    (hsx : sized x) (hsy : sized y) (hdx : x.content.length = d)
    (hxy : corrH d x y) :
    corrState d (tryAdd A x) (tryAdd B y) := by
  match h with
  | ⟨hc, hsA, hsB, hdA, hiA, hiB⟩ =>
    have hiA' := tryAdd_indep A x hsA hsx hiA
    have hiB' := tryAdd_indep B y hsB hsy hiB
    match tryAdd_corr d A B x y hc hsA hsB hdA hiA hiB
        hsx hsy hdx hxy with
    | Or.inl ⟨hq, hp⟩ =>
      rw [hq] at hiA' ⊢
      rw [hp] at hiB' ⊢
      exact ⟨hc, hsA, hsB, hdA, hiA', hiB'⟩
    | Or.inr ⟨hq, hp⟩ =>
      rw [hq] at hiA' ⊢
      rw [hp] at hiB' ⊢
      exact ⟨corrP_append d hc ⟨hxy, trivial⟩,
        ground.all_of_append _ _ _ hsA (memAll_cons hsx memAll_nil),
        ground.all_of_append _ _ _ hsB (memAll_cons hsy memAll_nil),
        ground.all_of_append _ _ _ hdA (memAll_cons hdx memAll_nil),
        hiA', hiB'⟩

private theorem corrP_split (d : Nat) : ∀ {A B A' B' : List HVec},
    A.length = A'.length → corrP d (A ++ B) (A' ++ B') →
    corrP d A A' ∧ corrP d B B'
  | [], _, [], _, _, h => ⟨trivial, h⟩
  | [], _, _ :: _, _, hl, _ => nomatch hl
  | _ :: _, _, [], _, hl, _ => nomatch hl
  | _ :: A, B, _ :: A', B', hl, h =>
    match corrP_split d (A := A) (B := B) (A' := A') (B' := B')
        (Nat.succ.inj hl) h.2 with
    | ⟨h1, h2⟩ => ⟨⟨h.1, h1⟩, h2⟩

private theorem cand_fold_corr (d : Nat) (v w : HVec)
    (hsv : sized v) (hsw : sized w) (hvd : v.content.length = d)
    (hcw : corrH d v w) :
    ∀ (k : Nat), (∀ j, j < k → j + 1 < d) →
    ∀ (A B : List HVec), corrState d A B →
    corrState d
      (((List.range k).flatMap (fun j =>
        match lowerH j v with
        | some x => [x]
        | none => [])).foldl tryAdd A)
      (((List.range k).flatMap (fun j =>
        match lowerH j w with
        | some y => [y]
        | none => [])).foldl tryAdd B)
  | 0, _, _, _, h => h
  | k + 1, hk, A, B, h => by
    rw [range_succ k,
      ground.flatMap_append (fun j =>
        match lowerH j v with
        | some x => [x]
        | none => []),
      ground.flatMap_append (fun j =>
        match lowerH j w with
        | some y => [y]
        | none => []),
      ground.foldl_append tryAdd, ground.foldl_append tryAdd]
    have hprev := cand_fold_corr d v w hsv hsw hvd hcw k
      (fun j hj => hk j (Nat.lt_succ_of_lt hj)) A B h
    show corrState d
      ((((match lowerH k v with
          | some x => [x]
          | none => []) ++ [] : List HVec)).foldl tryAdd
        (((List.range k).flatMap (fun j =>
          match lowerH j v with
          | some x => [x]
          | none => [])).foldl tryAdd A))
      ((((match lowerH k w with
          | some y => [y]
          | none => []) ++ [] : List HVec)).foldl tryAdd
        (((List.range k).flatMap (fun j =>
          match lowerH j w with
          | some y => [y]
          | none => [])).foldl tryAdd B))
    rw [ground.append_nil (match lowerH k v with
        | some x => [x]
        | none => []),
      ground.append_nil (match lowerH k w with
        | some y => [y]
        | none => [])]
    match lowerH_corr d k v w hsv hsw hvd
        (hk k (Nat.lt_succ_self k)) hcw with
    | ⟨y, hy, hsy, Or.inl ⟨x, hx, hsx, hxd, hxy⟩⟩ =>
      rw [hx, hy]
      show corrState d
        (tryAdd ((List.range k).flatMap (fun j =>
          match lowerH j v with
          | some x => [x]
          | none => []) |>.foldl tryAdd A) x)
        (tryAdd ((List.range k).flatMap (fun j =>
          match lowerH j w with
          | some y => [y]
          | none => []) |>.foldl tryAdd B) y)
      exact tryAdd_corrState d _ _ x y hprev hsx hsy hxd hxy
    | ⟨y, hy, hsy, Or.inr ⟨hxn, hyu⟩⟩ =>
      rw [hxn, hy]
      show corrState d
        ((List.range k).flatMap (fun j =>
          match lowerH j v with
          | some x => [x]
          | none => []) |>.foldl tryAdd A)
        (tryAdd ((List.range k).flatMap (fun j =>
          match lowerH j w with
          | some y => [y]
          | none => []) |>.foldl tryAdd B) y)
      rw [tryAdd_unit_eq _ y hyu]
      exact hprev

private theorem imgs_fold_corr (d : Nat) : ∀ (FQ FP : List HVec),
    corrP d FQ FP →
    (∀ x ∈ FQ, sized x) → (∀ x ∈ FP, sized x) →
    (∀ x ∈ FQ, x.content.length = d) →
    ∀ (A B : List HVec), corrState d A B →
    corrState d ((imgsOf d FQ).foldl tryAdd A)
      ((imgsOf d FP).foldl tryAdd B)
  | [], [], _, _, _, _, _, _, h => h
  | [], _ :: _, hc, _, _, _, _, _, _ => hc.elim
  | _ :: _, [], hc, _, _, _, _, _, _ => hc.elim
  | v :: FQ, w :: FP, hc, hsQ, hsP, hdQ, A, B, h => by
    show corrState d
      ((((List.range (d - 1)).flatMap (fun j =>
          match lowerH j v with
          | some x => [x]
          | none => []) ++ imgsOf d FQ)).foldl tryAdd A)
      ((((List.range (d - 1)).flatMap (fun j =>
          match lowerH j w with
          | some y => [y]
          | none => []) ++ imgsOf d FP)).foldl tryAdd B)
    rw [ground.foldl_append tryAdd, ground.foldl_append tryAdd]
    exact imgs_fold_corr d FQ FP hc.2 (memAll_tail hsQ)
      (memAll_tail hsP) (memAll_tail hdQ) _ _
      (cand_fold_corr d v w (memAll_head hsQ) (memAll_head hsP)
        (memAll_head
          (P := fun x : HVec => x.content.length = d) hdQ)
        hc.1 (d - 1)
        (fun _ hj => ground.succ_lt_of_lt_pred hj) A B h)

private theorem front_unit_of_nomove (d : Nat)
    (meas : List Nat → Nat) (K : HVec → Prop)
    (hnomove : ∀ v : HVec, K v → meas v.content = 0 →
      ∀ j : Nat, j < d - 1 → lowerH j v = none) :
    ∀ (FQ FP : List HVec), corrP d FQ FP →
    (∀ x ∈ FQ, sized x) → (∀ x ∈ FP, sized x) →
    (∀ x ∈ FQ, x.content.length = d) →
    (∀ x ∈ FQ, K x) → (∀ x ∈ FQ, meas x.content = 0) →
    ∀ y ∈ imgsOf d FP, poly.unitTail y.coords
  | [], [], _, _, _, _, _, _ => memAll_nil
  | [], _ :: _, hc, _, _, _, _, _ => hc.elim
  | _ :: _, [], hc, _, _, _, _, _ => hc.elim
  | v :: FQ, w :: FP, hc, hsQ, hsP, hdQ, hkQ, hmQ => by
    show ∀ y ∈ ((List.range (d - 1)).flatMap (fun j =>
        match lowerH j w with
        | some y => [y]
        | none => []) ++ imgsOf d FP), poly.unitTail y.coords
    refine ground.all_of_append _ _ _ ?_
      (front_unit_of_nomove d meas K hnomove FQ FP hc.2
        (memAll_tail hsQ) (memAll_tail hsP) (memAll_tail hdQ)
        (memAll_tail hkQ) (memAll_tail hmQ))
    refine cand_unit w d ?_ (d - 1)
      (fun _ hj => ground.succ_lt_of_lt_pred hj)
    intro j y hj hy
    match lowerH_corr d j v w (memAll_head hsQ) (memAll_head hsP)
        (memAll_head
          (P := fun x : HVec => x.content.length = d) hdQ)
        hj hc.1 with
    | ⟨y', hy', _, hbr⟩ =>
      have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
      match hbr with
      | Or.inl ⟨x, hx, _, _, _⟩ =>
        rw [hnomove v (memAll_head hkQ)
          (memAll_head
            (P := fun x : HVec => meas x.content = 0) hmQ) j
          (Nat.le_pred_of_lt hj)] at hx
        exact nomatch hx
      | Or.inr ⟨_, hu⟩ =>
        rw [← hyy]
        exact hu

private theorem closeSpan_flush (d : Nat) :
    ∀ (fuelP : Nat) (poolP frontP : List HVec),
    (∀ y ∈ imgsOf d frontP, poly.unitTail y.coords) →
    closeSpan d fuelP poolP frontP = poolP
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | fp + 1, poolP, g :: gs, hunit => by
    show closeSpan d fp
        ((imgsOf d (g :: gs)).foldl tryAdd poolP)
        (((imgsOf d (g :: gs)).foldl tryAdd poolP).drop
          poolP.length)
      = poolP
    rw [foldl_tryAdd_unit _ _ hunit, ground.dropLength]
    exact closeSpan_nil d fp poolP

private theorem closeSpan_corr (d : Nat) (meas : List Nat → Nat)
    (K : HVec → Prop)
    (hK : ∀ (j : Nat) (v w : HVec), lowerH j v = some w → K v → K w)
    (hnomove : ∀ v : HVec, K v → meas v.content = 0 →
      ∀ j : Nat, j < d - 1 → lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v w : HVec), j < d - 1 →
      lowerH j v = some w → K v →
      meas w.content + 1 = meas v.content) :
    ∀ (fuelQ fuelP : Nat) (doneQ frontQ doneP frontP : List HVec),
      fuelQ ≤ fuelP →
      corrP d doneQ doneP → corrP d frontQ frontP →
      (∀ v ∈ doneQ ++ frontQ, sized v) →
      (∀ v ∈ doneP ++ frontP, sized v) →
      (∀ v ∈ doneQ ++ frontQ, v.content.length = d) →
      (∀ v ∈ doneQ ++ frontQ, K v) →
      indepAll (doneQ ++ frontQ) → indepAll (doneP ++ frontP) →
      (∀ w ∈ frontQ, meas w.content ≤ fuelQ) →
      corrP d (closeSpan d fuelQ (doneQ ++ frontQ) frontQ)
        (closeSpan d fuelP (doneP ++ frontP) frontP)
  | 0, fuelP, doneQ, frontQ, doneP, frontP, _, hcD, hcF, hsQ, hsP,
      hdQ, hkQ, _, _, hht => by
    show corrP d (doneQ ++ frontQ)
      (closeSpan d fuelP (doneP ++ frontP) frontP)
    rw [closeSpan_flush d fuelP (doneP ++ frontP) frontP
      (front_unit_of_nomove d meas K hnomove frontQ frontP hcF
        (memAll_split hsQ).2 (memAll_split hsP).2
        (memAll_split hdQ).2 (memAll_split hkQ).2
        (fun v hv => Nat.le_zero.mp (hht v hv)))]
    exact corrP_append d hcD hcF
  | _ + 1, fuelP, doneQ, [], doneP, [], _, hcD, hcF, _, _, _, _, _,
      _, _ => by
    show corrP d (doneQ ++ []) (closeSpan d fuelP (doneP ++ []) [])
    rw [closeSpan_nil d fuelP (doneP ++ [])]
    exact corrP_append d hcD hcF
  | _ + 1, _, _, [], _, _ :: _, _, _, hcF, _, _, _, _, _, _, _ =>
    hcF.elim
  | _ + 1, _, _, _ :: _, _, [], _, _, hcF, _, _, _, _, _, _, _ =>
    hcF.elim
  | fq + 1, 0, _, _ :: _, _, _ :: _, hfuel, _, _, _, _, _, _, _, _,
      _ => absurd hfuel (Nat.not_lt_zero fq)
  | fq + 1, fp + 1, doneQ, f :: fr, doneP, g :: gs, hfuel, hcD, hcF,
      hsQ, hsP, hdQ, hkQ, hiQ, hiP, hht => by
    have hkf : ∀ v ∈ f :: fr, K v := (memAll_split hkQ).2
    have himgsSQ : ∀ x ∈ imgsOf d (f :: fr), sized x :=
      imgs_of_build sized K d (f :: fr) hkf
        (fun _ _ _ _ _ heq => lowerH_sized heq)
    have himgsSP : ∀ x ∈ imgsOf d (g :: gs), sized x :=
      imgs_of_build sized sized d (g :: gs) (memAll_split hsP).2
        (fun _ _ _ _ _ heq => lowerH_sized heq)
    have himgsDQ : ∀ x ∈ imgsOf d (f :: fr),
        x.content.length = d :=
      imgs_of_build (fun x => x.content.length = d)
        (fun x => x.content.length = d) d (f :: fr)
        (memAll_split hdQ).2
        (fun v _ w hav _ heq => by
          rw [(lowerH_fields heq).1, units.length_moveDn]
          exact hav)
    have himgsKQ : ∀ x ∈ imgsOf d (f :: fr), K x :=
      imgs_of_build K K d (f :: fr) hkf
        (fun v _ w hav _ heq => hK _ v w heq hav)
    have himgsMQ : ∀ x ∈ imgsOf d (f :: fr),
        meas x.content ≤ fq := by
      refine imgs_of_build _
        (fun v => K v ∧ meas v.content ≤ fq + 1)
        d (f :: fr) (fun v hv => ⟨hkf v hv, hht v hv⟩) ?_
      intro v j w hav hj heq
      have hd := hdrop j v w hj heq hav.1
      have h2 : meas w.content + 1 ≤ fq + 1 := by
        rw [hd]
        exact hav.2
      exact Nat.le_of_succ_le_succ h2
    have hstate : corrState d (doneQ ++ (f :: fr))
        (doneP ++ (g :: gs)) :=
      ⟨corrP_append d hcD hcF, hsQ, hsP, hdQ, hiQ, hiP⟩
    have hfoldc := imgs_fold_corr d (f :: fr) (g :: gs) hcF
      (memAll_split hsQ).2 (memAll_split hsP).2
      (memAll_split hdQ).2 _ _ hstate
    match foldl_tryAdd_sem (imgsOf d (f :: fr))
        (doneQ ++ (f :: fr)) hsQ himgsSQ hiQ,
      foldl_tryAdd_sem (imgsOf d (g :: gs))
        (doneP ++ (g :: gs)) hsP himgsSP hiP with
    | ⟨extQ, heqQ, hindQ', _, htransQ⟩,
      ⟨extP, heqP, hindP', _, htransP⟩ =>
      have hcorr' : corrP d ((doneQ ++ (f :: fr)) ++ extQ)
          ((doneP ++ (g :: gs)) ++ extP) := by
        rw [← heqQ, ← heqP]
        exact hfoldc.1
      match corrP_split d
          (corrP_length d (corrP_append d hcD hcF)) hcorr' with
      | ⟨hcPool, hcExt⟩ =>
        show corrP d
          (closeSpan d fq
            ((imgsOf d (f :: fr)).foldl tryAdd
              (doneQ ++ (f :: fr)))
            (((imgsOf d (f :: fr)).foldl tryAdd
              (doneQ ++ (f :: fr))).drop
              (doneQ ++ (f :: fr)).length))
          (closeSpan d fp
            ((imgsOf d (g :: gs)).foldl tryAdd
              (doneP ++ (g :: gs)))
            (((imgsOf d (g :: gs)).foldl tryAdd
              (doneP ++ (g :: gs))).drop
              (doneP ++ (g :: gs)).length))
        rw [heqQ, heqP, ground.drop_append_self (doneQ ++ (f :: fr)) extQ,
          ground.drop_append_self (doneP ++ (g :: gs)) extP]
        exact closeSpan_corr d meas K hK hnomove hdrop fq fp
          (doneQ ++ (f :: fr)) extQ (doneP ++ (g :: gs)) extP
          (Nat.le_of_succ_le_succ hfuel) hcPool hcExt
          (ground.all_of_append _ _ _ hsQ (htransQ sized himgsSQ))
          (ground.all_of_append _ _ _ hsP (htransP sized himgsSP))
          (ground.all_of_append _ _ _ hdQ
            (htransQ (fun x => x.content.length = d) himgsDQ))
          (ground.all_of_append _ _ _ hkQ (htransQ K himgsKQ))
          hindQ' hindP' (htransQ _ himgsMQ)

private theorem corrP_getAt (d : Nat) : ∀ {A B : List HVec},
    corrP d A B → ∀ k, k < A.length →
    corrH d (getAt (⟨[], []⟩ : HVec) A k)
      (getAt (⟨[], []⟩ : HVec) B k)
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: _, _ :: _, h, k + 1, hk =>
    corrP_getAt d h.2 k (Nat.lt_of_succ_lt_succ hk)

private theorem corrP_occupancy (d : Nat) (mu : List Nat)
    (hmu : mu.length = d) : ∀ {A B : List HVec},
    corrP d A B → (∀ x ∈ A, x.content.length = d) →
    ∀ acc : Nat,
    B.foldl (fun acc v => if v.content
        = (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content
      then acc + 1 else acc) acc
    = A.foldl (fun acc v => if v.content = mu
      then acc + 1 else acc) acc
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | v :: A, w :: B, h, hd, acc => by
    show B.foldl _ (if w.content = (tensorH (wedge d d)
        (⟨mu, []⟩ : HVec)).content then acc + 1 else acc)
      = A.foldl _ (if v.content = mu then acc + 1 else acc)
    by_cases hv : v.content = mu
    · rw [if_pos hv, if_pos (show w.content = (tensorH (wedge d d)
        (⟨mu, []⟩ : HVec)).content from h.1.1.trans (by
          show List.zipWith (fun a b => a + b)
              (wedge d d).content v.content
            = List.zipWith (fun a b => a + b)
              (wedge d d).content mu
          rw [hv]))]
      exact corrP_occupancy d mu hmu h.2 (memAll_tail hd) (acc + 1)
    · rw [if_neg hv, if_neg (fun hw : w.content
          = (tensorH (wedge d d) (⟨mu, []⟩ : HVec)).content => hv
        (zipWith_add_cancelL (wedge d d).content v.content mu
          d (wedge_clen d d)
          (memAll_head
            (P := fun x : HVec => x.content.length = d) hd)
          hmu
          (show List.zipWith (fun a b => a + b)
              (wedge d d).content v.content
            = List.zipWith (fun a b => a + b)
              (wedge d d).content mu
            from h.1.1.symm.trans hw)))]
      exact corrP_occupancy d mu hmu h.2 (memAll_tail hd) acc

/-- The row list at one more full column is the wedge's content
joined to the row list, coordinate by coordinate: the exhibit's own
content read across the added column's tensor. -/
theorem rowList_addFull (lam : Shape) :
    places.rowList (ground.bumpAt (lam.length - 1) lam)
      = List.zipWith (fun a b => a + b)
        (wedge lam.length lam.length).content
        (places.rowList lam) := by
  rw [← content_exhibit, (exhibit_addFull lam).1]
  show List.zipWith (fun a b => a + b)
      (wedge lam.length lam.length).content
      (exhibit lam).content
    = _
  rw [content_exhibit lam]

private theorem blockSpan_corrP (lam : Shape)
    (meas : List Nat → Nat)
    (hnomove : ∀ v : HVec, v.content.length = lam.length →
      meas v.content = 0 → ∀ j : Nat, j < lam.length - 1 →
      lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v w : HVec), j < lam.length - 1 →
      lowerH j v = some w → v.content.length = lam.length →
      meas w.content + 1 = meas v.content)
    (hexh : meas (places.rowList lam)
      ≤ degree lam * lam.length) :
    corrP lam.length (blockSpan lam)
      (blockSpan (ground.bumpAt (lam.length - 1) lam)) := by
  have hbl : (ground.bumpAt (lam.length - 1) lam).length
      = lam.length := ground.length_bumpAt _ lam
  have hadd := exhibit_addFull lam
  have hclenQ : (exhibit lam).content.length = lam.length := by
    rw [content_exhibit lam, places.length_rowList lam]
  have hclenP : (exhibit (ground.bumpAt (lam.length - 1)
      lam)).content.length = lam.length := by
    rw [content_exhibit, places.length_rowList, hbl]
  have hrow := rowList_addFull lam
  have hfuel : degree lam * lam.length
      ≤ degree (ground.bumpAt (lam.length - 1) lam)
        * lam.length := by
    refine Nat.mul_le_mul ?_ (Nat.le_refl lam.length)
    show ground.sumNat (places.rowList lam)
      ≤ ground.sumNat (places.rowList
        (ground.bumpAt (lam.length - 1) lam))
    rw [hrow, sumNat_zipWith_add _ _ (by
      rw [wedge_clen, places.length_rowList])]
    exact Nat.le_add_left _ _
  have hmain := closeSpan_corr lam.length meas
    (fun v => v.content.length = lam.length)
    (fun _ v w heq hv => by
      rw [(lowerH_fields heq).1, units.length_moveDn]
      exact hv)
    hnomove hdrop
    (degree lam * lam.length)
    (degree (ground.bumpAt (lam.length - 1) lam) * lam.length)
    [] [exhibit lam] []
    [exhibit (ground.bumpAt (lam.length - 1) lam)]
    hfuel trivial
    ⟨⟨hadd.1, hadd.2⟩, trivial⟩
    (memAll_cons (exhibit_sized lam) memAll_nil)
    (memAll_cons (exhibit_sized _) memAll_nil)
    (memAll_cons hclenQ memAll_nil)
    (memAll_cons hclenQ memAll_nil)
    (indep_seed _ (exhibit_sized lam) (exhibit_off_unit lam))
    (indep_seed _ (exhibit_sized _) (exhibit_off_unit _))
    (memAll_cons (by
      show meas (exhibit lam).content ≤ degree lam * lam.length
      rw [content_exhibit lam]
      exact hexh) memAll_nil)
  show corrP lam.length
    (closeSpan lam.length (degree lam * lam.length)
      [exhibit lam] [exhibit lam])
    (closeSpan (ground.bumpAt (lam.length - 1) lam).length
      (degree (ground.bumpAt (lam.length - 1) lam)
        * (ground.bumpAt (lam.length - 1) lam).length)
      [exhibit (ground.bumpAt (lam.length - 1) lam)]
      [exhibit (ground.bumpAt (lam.length - 1) lam)])
  rw [hbl]
  exact hmain

/-- The bumped shape's span is the span at the wedge tensored on,
member for member (`lem:dualread`(ii)'s transport clause at a
stated measure, `lem:lowerspan`'s joined-collection discipline):
the two walks pair position by position, each partner's content the
tensor's own and its coordinates the tensor's one-value class, the
measure binders the discipline's frame (`blockSpan_sem`). -/
theorem blockSpan_addFull (lam : Shape) (meas : List Nat → Nat)
    (hnomove : ∀ v : HVec, v.content.length = lam.length →
      meas v.content = 0 → ∀ j : Nat, j < lam.length - 1 →
      lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v w : HVec), j < lam.length - 1 →
      lowerH j v = some w → v.content.length = lam.length →
      meas w.content + 1 = meas v.content)
    (hexh : meas (places.rowList lam)
      ≤ degree lam * lam.length) :
    (blockSpan (ground.bumpAt (lam.length - 1) lam)).length
      = (blockSpan lam).length
    ∧ ∀ k, k < (blockSpan lam).length →
      (getAt (⟨[], []⟩ : HVec)
          (blockSpan (ground.bumpAt (lam.length - 1) lam))
          k).content
        = (tensorH (wedge lam.length lam.length)
            (getAt (⟨[], []⟩ : HVec) (blockSpan lam) k)).content
      ∧ poly.oneValue
          (getAt (⟨[], []⟩ : HVec)
            (blockSpan (ground.bumpAt (lam.length - 1) lam))
            k).coords
          (tensorH (wedge lam.length lam.length)
            (getAt (⟨[], []⟩ : HVec) (blockSpan lam) k)).coords :=
  ⟨(corrP_length lam.length
      (blockSpan_corrP lam meas hnomove hdrop hexh)).symm,
    fun k hk => corrP_getAt lam.length
      (blockSpan_corrP lam meas hnomove hdrop hexh) k hk⟩

/-- The bumped shape's occupancies read at the shifted contents
(`lem:dualread`(ii)'s occupancy clause at the stated measure): the
span's count at a content is the mapped span's at the wedge-shifted
one, the width binder load-bearing at the shift's truncation. -/
theorem occupancy_addFull (lam : Shape) (meas : List Nat → Nat)
    (hnomove : ∀ v : HVec, v.content.length = lam.length →
      meas v.content = 0 → ∀ j : Nat, j < lam.length - 1 →
      lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v w : HVec), j < lam.length - 1 →
      lowerH j v = some w → v.content.length = lam.length →
      meas w.content + 1 = meas v.content)
    (hexh : meas (places.rowList lam)
      ≤ degree lam * lam.length)
    (mu : List Nat) (hmu : mu.length = lam.length) :
    occupancyAt (blockSpan (ground.bumpAt (lam.length - 1) lam))
      (tensorH (wedge lam.length lam.length)
        (⟨mu, []⟩ : HVec)).content
    = occupancyAt (blockSpan lam) mu := by
  have hclenQ : (exhibit lam).content.length = lam.length := by
    rw [content_exhibit lam, places.length_rowList lam]
  have hall : ∀ v ∈ blockSpan lam,
      v.content.length = lam.length := by
    match closeSpan_reads lam.length
        (fun v => v.content.length = lam.length)
        (fun _ => True)
        (fun v w _ _ hv heq => ⟨by
          rw [(lowerH_fields heq).1, units.length_moveDn]
          exact hv, trivial⟩)
        (degree lam * lam.length) [exhibit lam] [exhibit lam]
        (memAll_cons hclenQ memAll_nil)
        (memAll_cons hclenQ memAll_nil) with
    | ⟨tail, heq, htail⟩ =>
      show ∀ v ∈ closeSpan lam.length (degree lam * lam.length)
        [exhibit lam] [exhibit lam], v.content.length = lam.length
      rw [heq]
      exact ground.all_of_append _ _ _ (memAll_cons hclenQ memAll_nil)
        (fun v hv => (htail v hv).1)
  exact corrP_occupancy lam.length mu hmu
    (blockSpan_corrP lam meas hnomove hdrop hexh) hall 0

/-! `lem:blockirr`(iv)'s word tier: the words' action folded over a
walk table — `con:units`' unit space read at one adjacent letter
pair, its lowering the step and the raising the transpose, with the
commutator at the pair, the transpose identity, the distinct
letters' commutation and the content moves its laws — the moved
content the chain's own and the appended word the inner action.
The pairing walk runs on those reads alone, one table per side with
the crossing scalars tied cross-added and the pairings graded, and
`lowerTable` is the matrix units' own table, the instance the
lowering words read. -/

private theorem act_congr (i j : Nat) (v w : HVec)
    (hc : v.content = w.content)
    (hq : poly.oneValue v.coords w.coords) :
    (act i j v).content = (act i j w).content
      ∧ (act i j v).coords.length = (act i j w).coords.length
      ∧ poly.oneValue (act i j v).coords (act i j w).coords := by
  refine ⟨?_, ?_, ?_⟩
  · show moveAt i j v.content = moveAt i j w.content
    rw [hc]
  · show (elim.matVec (units.matUnitAt (moveAt i j v.content)
        v.content i j) v.coords).length
      = (elim.matVec (units.matUnitAt (moveAt i j w.content)
        w.content i j) w.coords).length
    rw [elim.matVec_length, elim.matVec_length,
      units.length_matUnitAt, units.length_matUnitAt, hc]
  · show poly.oneValue
      (elim.matVec (units.matUnitAt (moveAt i j v.content)
        v.content i j) v.coords)
      (elim.matVec (units.matUnitAt (moveAt i j w.content)
        w.content i j) w.coords)
    rw [hc]
    exact elim.matVec_congr _ _ _ hq

private theorem moveAt_swap_ne (l j : Nat) (hlj : ¬ l = j)
    (nu : List Nat) :
    moveAt (l + 1) l (moveAt j (j + 1) nu)
      = moveAt j (j + 1) (moveAt (l + 1) l nu) := by
  show bumpAt (l + 1) (dipAt l (bumpAt j (dipAt (j + 1) nu)))
    = bumpAt j (dipAt (j + 1) (bumpAt (l + 1) (dipAt l nu)))
  rw [← bumpAt_dipAt_ne j l _ (fun h => hlj h.symm),
    bumpAt_comm (l + 1) j, dipAt_comm l (j + 1),
    bumpAt_dipAt_ne (l + 1) (j + 1) _
      (fun h => hlj (Nat.succ.inj h))]

private theorem swap_coords (v : HVec) (l j : Nat)
    (hlj : ¬ l = j) (hsv : sized v)
    (hl : l + 1 < v.content.length)
    (hj : j + 1 < v.content.length) :
    (act j (j + 1) (act (l + 1) l v)).content
        = (act (l + 1) l (act j (j + 1) v)).content
      ∧ (act j (j + 1) (act (l + 1) l v)).coords.length
        = (act (l + 1) l (act j (j + 1) v)).coords.length
      ∧ poly.oneValue (act j (j + 1) (act (l + 1) l v)).coords
        (act (l + 1) l (act j (j + 1) v)).coords := by
  have hcomm := moveAt_swap_ne l j hlj v.content
  have hcont : (act j (j + 1) (act (l + 1) l v)).content
      = (act (l + 1) l (act j (j + 1) v)).content := by
    show moveAt j (j + 1) (moveAt (l + 1) l v.content)
      = moveAt (l + 1) l (moveAt j (j + 1) v.content)
    exact hcomm.symm
  have hlA : (moveAt (l + 1) l v.content).length
      = v.content.length := length_moveAt _ _ _
  have hlB : (moveAt j (j + 1) v.content).length
      = v.content.length := length_moveAt _ _ _
  refine ⟨hcont, ?_, ?_⟩
  · show (elim.matVec (units.matUnitAt _ _ j (j + 1))
        (elim.matVec (units.matUnitAt _ _ (l + 1) l)
          v.coords)).length
      = (elim.matVec (units.matUnitAt _ _ (l + 1) l)
        (elim.matVec (units.matUnitAt _ _ j (j + 1))
          v.coords)).length
    rw [elim.matVec_length, elim.matVec_length,
      units.length_matUnitAt, units.length_matUnitAt]
    show (monomialsAt (moveAt j (j + 1)
        (moveAt (l + 1) l v.content))).length
      = (monomialsAt (moveAt (l + 1) l
        (moveAt j (j + 1) v.content))).length
    rw [hcomm]
  · have hx : v.coords.length
        = (monomialsAt v.content).length := hsv
    have hsr := units.matVec_swap_read
      (moveAt (l + 1) l v.content)
      (moveAt j (j + 1) v.content)
      (moveAt j (j + 1) (moveAt (l + 1) l v.content))
      v.content j (j + 1) (l + 1) l
      (fun h => hlj h.symm)
      (fun h => hlj (Nat.succ.inj h))
      (out_gen v.content (l + 1) l hl (Nat.succ_ne_self l))
      (out_gen (moveAt (l + 1) l v.content) j (j + 1)
        (by rw [hlA]; exact Nat.lt_of_succ_lt hj)
        (Nat.ne_of_lt (Nat.lt_succ_self j)))
      (out_gen v.content j (j + 1)
        (Nat.lt_of_succ_lt hj) (Nat.ne_of_lt (Nat.lt_succ_self j)))
      (fun s m hs hm => by
        have h := out_gen (moveAt j (j + 1) v.content) (l + 1) l
          (by rw [hlB]; exact hl)
          (Nat.succ_ne_self l) s m hs hm
        rw [moveAt_swap_ne l j hlj v.content] at h
        exact h)
      v.coords hx
    show poly.oneValue
      (elim.matVec (units.matUnitAt
        (moveAt j (j + 1) (moveAt (l + 1) l v.content))
        (moveAt (l + 1) l v.content) j (j + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (l + 1) l v.content) v.content (l + 1) l)
          v.coords))
      (elim.matVec (units.matUnitAt
        (moveAt (l + 1) l (moveAt j (j + 1) v.content))
        (moveAt j (j + 1) v.content) (l + 1) l)
        (elim.matVec (units.matUnitAt
          (moveAt j (j + 1) v.content) v.content j (j + 1))
          v.coords))
    rw [moveAt_swap_ne l j hlj v.content]
    exact hsr

private theorem pair_coords (v : HVec) (j : Nat)
    (hsv : sized v) (hj : j + 1 < v.content.length)
    (hoccj : 0 < ground.getAt 0 v.content j)
    (hoccj1 : 0 < ground.getAt 0 v.content (j + 1)) :
    poly.oneValue
      (elim.vecAdd (act j (j + 1) (act (j + 1) j v)).coords
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
          v.coords))
      (elim.vecAdd (act (j + 1) j (act j (j + 1) v)).coords
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content j))
          v.coords)) := by
  have hpr := units.matVec_pair_read v.content
    (moveAt (j + 1) j v.content) (moveAt j (j + 1) v.content) j
    (out_gen v.content (j + 1) j hj (Nat.succ_ne_self j))
    (fun s m hs hm => by
      have h := out_gen (moveAt (j + 1) j v.content) j (j + 1)
        (by rw [length_moveAt]; exact Nat.lt_of_succ_lt hj)
        (Nat.ne_of_lt (Nat.lt_succ_self j)) s m hs hm
      rw [moveAt_round_at j (j + 1) v.content hoccj] at h
      exact h)
    (out_gen v.content j (j + 1)
      (Nat.lt_of_succ_lt hj) (Nat.ne_of_lt (Nat.lt_succ_self j)))
    (fun s m hs hm => by
      have h := out_gen (moveAt j (j + 1) v.content) (j + 1) j
        (by rw [length_moveAt]; exact hj)
        (Nat.succ_ne_self j) s m hs hm
      rw [moveAt_round_at (j + 1) j v.content hoccj1] at h
      exact h)
    v.coords hsv
  show poly.oneValue
    (elim.vecAdd
      (elim.matVec (units.matUnitAt
        (moveAt j (j + 1) (moveAt (j + 1) j v.content))
        (moveAt (j + 1) j v.content) j (j + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (j + 1) j v.content) v.content (j + 1) j)
          v.coords))
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
        v.coords))
    (elim.vecAdd
      (elim.matVec (units.matUnitAt
        (moveAt (j + 1) j (moveAt j (j + 1) v.content))
        (moveAt j (j + 1) v.content) (j + 1) j)
        (elim.matVec (units.matUnitAt
          (moveAt j (j + 1) v.content) v.content j (j + 1))
          v.coords))
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 v.content j))
        v.coords))
  rw [moveAt_round_at j (j + 1) v.content hoccj,
    moveAt_round_at (j + 1) j v.content hoccj1]
  exact hpr

private theorem pair_coords_vac (v : HVec) (j : Nat)
    (hsv : sized v) (hj : j + 1 < v.content.length)
    (hoccj : 0 < ground.getAt 0 v.content j)
    (hz : ground.getAt 0 v.content (j + 1) = 0) :
    poly.oneValue
      (elim.vecAdd (act j (j + 1) (act (j + 1) j v)).coords
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
          v.coords))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt v.content
          (List.replicate v.content.length 0) (j + 1) j)
          (elim.matVec (units.matUnitAt
            (List.replicate v.content.length 0) v.content
            j (j + 1)) v.coords))
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content j))
          v.coords))
      ∧ poly.unitTail
        (elim.matVec (units.matUnitAt v.content
          (List.replicate v.content.length 0) (j + 1) j)
          (elim.matVec (units.matUnitAt
            (List.replicate v.content.length 0) v.content
            j (j + 1)) v.coords)) := by
  refine ⟨?_, elim.matVec_null _ _
    (units.matVec_null_unocc _ _ j (j + 1) hz v.coords)⟩
  have hpr := units.matVec_pair_read v.content
    (moveAt (j + 1) j v.content)
    (List.replicate v.content.length 0) j
    (out_gen v.content (j + 1) j hj (Nat.succ_ne_self j))
    (fun s m hs hm => by
      have h := out_gen (moveAt (j + 1) j v.content) j (j + 1)
        (by rw [length_moveAt]; exact Nat.lt_of_succ_lt hj)
        (Nat.ne_of_lt (Nat.lt_succ_self j)) s m hs hm
      rw [moveAt_round_at j (j + 1) v.content hoccj] at h
      exact h)
    (fun s m hs hm => by
      rw [units.unitAct_nil_of_zero j (j + 1) s
        (letter_zero v.content (j + 1) hz s hs)] at hm
      exact absurd hm (Nat.lt_irrefl 0))
    (fun s m hs hm =>
      (units.no_out_zero v.content.length (j + 1) j s m hs hm).elim)
    v.coords hsv
  show poly.oneValue
    (elim.vecAdd
      (elim.matVec (units.matUnitAt
        (moveAt j (j + 1) (moveAt (j + 1) j v.content))
        (moveAt (j + 1) j v.content) j (j + 1))
        (elim.matVec (units.matUnitAt
          (moveAt (j + 1) j v.content) v.content (j + 1) j)
          v.coords))
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
        v.coords))
    _
  rw [moveAt_round_at j (j + 1) v.content hoccj]
  exact hpr

/-- The crossed composites at the vacant raised letter: the raising
is null there, so the lowering through it reads the lowered
letter's count scaling the source. -/
private theorem pair_coords_vacU (v : HVec) (j : Nat)
    (hsv : sized v) (hj : j + 1 < v.content.length)
    (hoccj : 0 < ground.getAt 0 v.content j)
    (hz : ground.getAt 0 v.content (j + 1) = 0) :
    poly.oneValue (act j (j + 1) (act (j + 1) j v)).coords
      (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content j))
        v.coords) := by
  have hrt1 : moveAt j (j + 1) (moveAt (j + 1) j v.content)
      = v.content := moveAt_round_at j (j + 1) v.content hoccj
  have hPlen : (act j (j + 1) (act (j + 1) j v)).coords.length
      = (monomialsAt v.content).length := by
    rw [act_sized j (j + 1) (act (j + 1) j v)]
    show (monomialsAt (moveAt j (j + 1)
      (moveAt (j + 1) j v.content))).length = _
    rw [hrt1]
  have hNlen : (elim.matVec (units.matUnitAt v.content
      (List.replicate v.content.length 0) (j + 1) j)
      (elim.matVec (units.matUnitAt
        (List.replicate v.content.length 0) v.content
        j (j + 1)) v.coords)).length
      = (monomialsAt v.content).length := by
    rw [elim.matVec_length, units.length_matUnitAt]
  have hS1len : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
      v.coords).length = (monomialsAt v.content).length := by
    rw [elim.length_vecScale]
    exact hsv
  have hS0len : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 v.content j))
      v.coords).length = (monomialsAt v.content).length := by
    rw [elim.length_vecScale]
    exact hsv
  have hS1unit : poly.unitTail (elim.vecScale
      (BPair.ofNat (ground.getAt 0 v.content (j + 1))) v.coords) := by
    rw [hz]
    exact elim.unitTail_vecScale_unit
      (show (BPair.ofNat 0).oneValue BPair.unit from rfl) v.coords
  match pair_coords_vac v j hsv hj hoccj hz with
  | ⟨pcv, hNull⟩ =>
    exact poly.oneValue_trans
      (poly.oneValue_symm
        (elim.vecAdd_null_right _ _ (hPlen.trans hS1len.symm) hS1unit))
      (poly.oneValue_trans pcv
        (elim.vecAdd_null_left _ _ (hNlen.trans hS0len.symm) hNull))

/-- The crossed composites at the vacant lowered letter: the
lowering is null there, so the raising through it reads the raised
letter's count scaling the source — `[E, F] = H` at the letter pair
with the lowering arm vacant. -/
private theorem pair_coords_vacD (v : HVec) (j : Nat)
    (hsv : sized v) (hj : j + 1 < v.content.length)
    (hz : ground.getAt 0 v.content j = 0)
    (hoccj1 : 0 < ground.getAt 0 v.content (j + 1)) :
    poly.oneValue (act (j + 1) j (act j (j + 1) v)).coords
      (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
        v.coords) := by
  have hrt2 : moveAt (j + 1) j (moveAt j (j + 1) v.content)
      = v.content := moveAt_round_at (j + 1) j v.content hoccj1
  have hNull : poly.unitTail
      (elim.matVec (units.matUnitAt v.content
        (List.replicate v.content.length 0) j (j + 1))
        (elim.matVec (units.matUnitAt
          (List.replicate v.content.length 0) v.content
          (j + 1) j) v.coords)) :=
    elim.matVec_null _ _
      (units.matVec_null_unocc _ _ (j + 1) j hz v.coords)
  have hNlen : (elim.matVec (units.matUnitAt v.content
      (List.replicate v.content.length 0) j (j + 1))
      (elim.matVec (units.matUnitAt
        (List.replicate v.content.length 0) v.content
        (j + 1) j) v.coords)).length
      = (monomialsAt v.content).length := by
    rw [elim.matVec_length, units.length_matUnitAt]
  have hS1len : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
      v.coords).length = (monomialsAt v.content).length := by
    rw [elim.length_vecScale]
    exact hsv
  have hS0len : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 v.content j))
      v.coords).length = (monomialsAt v.content).length := by
    rw [elim.length_vecScale]
    exact hsv
  have hS0unit : poly.unitTail (elim.vecScale
      (BPair.ofNat (ground.getAt 0 v.content j)) v.coords) := by
    rw [hz]
    exact elim.unitTail_vecScale_unit
      (show (BPair.ofNat 0).oneValue BPair.unit from rfl) v.coords
  have hPlen : (act (j + 1) j (act j (j + 1) v)).coords.length
      = (monomialsAt v.content).length := by
    rw [act_sized (j + 1) j (act j (j + 1) v)]
    show (monomialsAt (moveAt (j + 1) j
      (moveAt j (j + 1) v.content))).length = _
    rw [hrt2]
  have hpr := units.matVec_pair_read v.content
    (List.replicate v.content.length 0)
    (moveAt j (j + 1) v.content) j
    (fun s m hs hm => by
      rw [units.unitAct_nil_of_zero (j + 1) j s
        (letter_zero v.content j hz s hs)] at hm
      exact absurd hm (Nat.lt_irrefl 0))
    (fun s m hs hm =>
      (units.no_out_zero v.content.length j (j + 1) s m hs hm).elim)
    (out_gen v.content j (j + 1)
      (Nat.lt_of_succ_lt hj) (Nat.ne_of_lt (Nat.lt_succ_self j)))
    (fun s m hs hm => by
      have h := out_gen (moveAt j (j + 1) v.content) (j + 1) j
        (by rw [length_moveAt]; exact hj)
        (Nat.succ_ne_self j) s m hs hm
      rw [hrt2] at h
      exact h)
    v.coords hsv
  have hpr' : poly.oneValue
      (elim.vecAdd
        (elim.matVec (units.matUnitAt v.content
          (List.replicate v.content.length 0) j (j + 1))
          (elim.matVec (units.matUnitAt
            (List.replicate v.content.length 0) v.content
            (j + 1) j) v.coords))
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content (j + 1)))
          v.coords))
      (elim.vecAdd (act (j + 1) j (act j (j + 1) v)).coords
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content j))
          v.coords)) := by
    show poly.oneValue _
      (elim.vecAdd
        (elim.matVec (units.matUnitAt
          (moveAt (j + 1) j (moveAt j (j + 1) v.content))
          (moveAt j (j + 1) v.content) (j + 1) j)
          (elim.matVec (units.matUnitAt
            (moveAt j (j + 1) v.content) v.content j (j + 1))
            v.coords))
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 v.content j))
          v.coords))
    rw [hrt2]
    exact hpr
  exact poly.oneValue_trans
    (poly.oneValue_symm
      (elim.vecAdd_null_right _ _ (hPlen.trans hS0len.symm) hS0unit))
    (poly.oneValue_trans (poly.oneValue_symm hpr')
      (elim.vecAdd_null_left _ _ (hNlen.trans hS1len.symm) hNull))

/-- The action walks across the pairing at its own letter pair: at
an occupied consumed letter the moved image pairs a vector at the
moved content as the source pairs that vector's reversed action,
`con:units`' transpose read at the general pair
(`unit_adjoint`'s carrier instance). -/
theorem act_adjoint (v z : HVec) (a b : Nat)
    (hsv : sized v) (hsz : sized z)
    (ha : a < v.content.length) (hb : b < v.content.length)
    (hab : ¬ a = b)
    (hocc : 0 < ground.getAt 0 v.content b)
    (hm : z.content = moveAt a b v.content) :
    (elim.dotP (act a b v).coords z.coords).oneValue
      (elim.dotP v.coords (act b a z).coords) := by
  refine BPair.oneValue_trans
    (unit_adjoint a b v.content ha hb hab hocc
      v.coords z.coords hsv (by rw [hsz, hm])) ?_
  show (elim.dotP v.coords
    (elim.matVec (units.matUnitAt v.content
      (moveAt a b v.content) b a) z.coords)).oneValue
    (elim.dotP v.coords
      (elim.matVec (units.matUnitAt (moveAt b a z.content)
        z.content b a) z.coords))
  rw [hm, moveAt_round_at b a v.content hocc]
  exact BPair.oneValue_refl _

/-! The walk table: `con:units`' unit space read at one adjacent
letter pair — the two letters, the lowering `step` and its
transpose `tr`, the content moves the grading, the commutator
`[E, F] = H` at the pair with the two vacant arms, the transpose
identity and the distinct letters' commutation. -/

set_option genInjectivity false in
/-- A walk table: an adjacent letter pair's unit space read on the
homogeneous carrier — the consumed letter `dLet` and the raised
letter `uLet` in either order, the lowering `step` with its
transpose `tr`, each moving the content at its own ordered pair and
each linear at the coordinate family, the vacant consumed letter
sending the image to the sum's unit, the commutator at the pair
reading the two content entries (`cross_occ`, with `cross_vacU` and
`cross_vacD` its two vacant arms), the transpose identity
(`adjoint`) and distinct letters commuting (`comm`). -/
structure WalkTable where
  dLet : Nat → Nat
  uLet : Nat → Nat
  step : Nat → HVec → HVec
  tr : Nat → HVec → HVec
  letters : ∀ j, (dLet j = j ∧ uLet j = j + 1)
    ∨ (dLet j = j + 1 ∧ uLet j = j)
  step_content : ∀ j v, (step j v).content
    = moveAt (uLet j) (dLet j) v.content
  tr_content : ∀ j v, (tr j v).content
    = moveAt (dLet j) (uLet j) v.content
  step_sized : ∀ j v, sized (step j v)
  tr_sized : ∀ j v, sized (tr j v)
  step_congr : ∀ j v w, v.content = w.content →
    poly.oneValue v.coords w.coords →
    poly.oneValue (step j v).coords (step j w).coords
  step_vecAdd : ∀ j (mu : List Nat) (x y : List BPair),
    x.length = y.length →
    poly.oneValue (step j ⟨mu, elim.vecAdd x y⟩).coords
      (elim.vecAdd (step j ⟨mu, x⟩).coords (step j ⟨mu, y⟩).coords)
  step_vecScale : ∀ j (mu : List Nat) (c : BPair) (x : List BPair),
    poly.oneValue (step j ⟨mu, elim.vecScale c x⟩).coords
      (elim.vecScale c (step j ⟨mu, x⟩).coords)
  tr_congr : ∀ j v w, v.content = w.content →
    poly.oneValue v.coords w.coords →
    poly.oneValue (tr j v).coords (tr j w).coords
  tr_vecAdd : ∀ j (mu : List Nat) (x y : List BPair),
    x.length = y.length →
    poly.oneValue (tr j ⟨mu, elim.vecAdd x y⟩).coords
      (elim.vecAdd (tr j ⟨mu, x⟩).coords (tr j ⟨mu, y⟩).coords)
  tr_vecScale : ∀ j (mu : List Nat) (c : BPair) (x : List BPair),
    poly.oneValue (tr j ⟨mu, elim.vecScale c x⟩).coords
      (elim.vecScale c (tr j ⟨mu, x⟩).coords)
  step_unitTail : ∀ j v, poly.unitTail v.coords →
    poly.unitTail (step j v).coords
  tr_unitTail : ∀ j v, poly.unitTail v.coords →
    poly.unitTail (tr j v).coords
  step_vac : ∀ j v, ground.getAt 0 v.content (dLet j) = 0 →
    poly.unitTail (step j v).coords
  tr_vac : ∀ j v, ground.getAt 0 v.content (uLet j) = 0 →
    poly.unitTail (tr j v).coords
  adjoint : ∀ j v z, sized v → sized z → j + 1 < v.content.length →
    0 < ground.getAt 0 v.content (dLet j) →
    z.content = moveAt (uLet j) (dLet j) v.content →
    (elim.dotP (step j v).coords z.coords).oneValue
      (elim.dotP v.coords (tr j z).coords)
  cross_occ : ∀ j v, sized v → j + 1 < v.content.length →
    0 < ground.getAt 0 v.content (dLet j) →
    0 < ground.getAt 0 v.content (uLet j) →
    poly.oneValue
      (elim.vecAdd (tr j (step j v)).coords
        (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content (uLet j)))
          v.coords))
      (elim.vecAdd (step j (tr j v)).coords
        (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content (dLet j)))
          v.coords))
  cross_vacU : ∀ j v, sized v → j + 1 < v.content.length →
    0 < ground.getAt 0 v.content (dLet j) →
    ground.getAt 0 v.content (uLet j) = 0 →
    poly.oneValue (tr j (step j v)).coords
      (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content (dLet j)))
        v.coords)
  cross_vacD : ∀ j v, sized v → j + 1 < v.content.length →
    ground.getAt 0 v.content (dLet j) = 0 →
    0 < ground.getAt 0 v.content (uLet j) →
    poly.oneValue (step j (tr j v)).coords
      (elim.vecScale (BPair.ofNat (ground.getAt 0 v.content (uLet j)))
        v.coords)
  comm : ∀ l j v, ¬ l = j → sized v →
    l + 1 < v.content.length → j + 1 < v.content.length →
    (tr j (step l v)).content = (step l (tr j v)).content
      ∧ (tr j (step l v)).coords.length = (step l (tr j v)).coords.length
      ∧ poly.oneValue (tr j (step l v)).coords (step l (tr j v)).coords

/-- A table's word action: the fold of its steps from the word's tail. -/
def wactT (T : WalkTable) : List Nat → HVec → HVec
  | [], v => v
  | j :: t, v => T.step j (wactT T t v)

/-- A table's content chain: per letter the move at the table's two
letters, the step's own content read. -/
def wcontentT (T : WalkTable) : List Nat → List Nat → List Nat
  | [], mu => mu
  | j :: t, mu => moveAt (T.uLet j) (T.dLet j) (wcontentT T t mu)

/-- A word's image reads its content at the table's chain. -/
theorem wactT_content (T : WalkTable) : ∀ (ws : List Nat) (v : HVec),
    (wactT T ws v).content = wcontentT T ws v.content
  | [], _ => rfl
  | j :: t, v => by
    rw [show (wactT T (j :: t) v).content
        = moveAt (T.uLet j) (T.dLet j) (wactT T t v).content
      from T.step_content j (wactT T t v), wactT_content T t v]
    rfl

/-- A word's image keeps the width at its own content's
enumeration. -/
theorem wactT_sized (T : WalkTable) : ∀ (ws : List Nat) (v : HVec),
    sized v → sized (wactT T ws v)
  | [], _, hv => hv
  | j :: t, v, _ => T.step_sized j (wactT T t v)

/-- The content chain keeps the letter width. -/
theorem wcontentT_len (T : WalkTable) : ∀ (ws mu : List Nat),
    (wcontentT T ws mu).length = mu.length
  | [], _ => rfl
  | j :: t, mu => by
    show (moveAt (T.uLet j) (T.dLet j) (wcontentT T t mu)).length
      = mu.length
    rw [length_moveAt, wcontentT_len T t mu]

/-- The word extended on its right acts on the inner step's image. -/
private theorem wactT_append (T : WalkTable) :
    ∀ (a : List Nat) (l : Nat) (v : HVec),
    wactT T (a ++ [l]) v = wactT T a (T.step l v)
  | [], _, _ => rfl
  | j :: t, l, v => by
    show T.step j (wactT T (t ++ [l]) v)
      = T.step j (wactT T t (T.step l v))
    rw [wactT_append T t l v]

/-- A joined word acts as the outer word on the inner word's image. -/
private theorem wactT_concat (T : WalkTable) :
    ∀ (a b : List Nat) (v : HVec),
    wactT T (a ++ b) v = wactT T a (wactT T b v)
  | [], _, _ => rfl
  | j :: t, b, v => by
    show T.step j (wactT T (t ++ b) v)
      = T.step j (wactT T t (wactT T b v))
    rw [wactT_concat T t b v]

/-- A word's image reads one value at a one-value source of the same
content, keeping the content and the width. -/
private theorem wactT_congr (T : WalkTable) (C : List Nat) :
    ∀ (v w : HVec),
    v.content = w.content →
    v.coords.length = w.coords.length →
    poly.oneValue v.coords w.coords →
    (wactT T C v).content = (wactT T C w).content
      ∧ (wactT T C v).coords.length = (wactT T C w).coords.length
      ∧ poly.oneValue (wactT T C v).coords (wactT T C w).coords := by
  induction C with
  | nil => exact fun v w hc hl hq => ⟨hc, hl, hq⟩
  | cons l t ih =>
    intro v w hc hl hq
    match ih v w hc hl hq with
    | ⟨hc', hl', hq'⟩ =>
      refine ⟨?_, ?_,
        T.step_congr l (wactT T t v) (wactT T t w) hc' hq'⟩
      · show (T.step l (wactT T t v)).content
          = (T.step l (wactT T t w)).content
        rw [T.step_content l (wactT T t v),
          T.step_content l (wactT T t w), hc']
      · show (T.step l (wactT T t v)).coords.length
          = (T.step l (wactT T t w)).coords.length
        rw [T.step_sized l (wactT T t v),
          T.step_sized l (wactT T t w),
          T.step_content l (wactT T t v),
          T.step_content l (wactT T t w), hc']

/-- A word's image of a unit-tailed source is unit-tailed. -/
private theorem wactT_unitTail (T : WalkTable) :
    ∀ (C : List Nat) (v : HVec),
    poly.unitTail v.coords → poly.unitTail (wactT T C v).coords
  | [], _, hv => hv
  | _ :: t, v, hv =>
    T.step_unitTail _ _ (wactT_unitTail T t v hv)

/-- A word's image at a stated content has the chain's width. -/
private theorem wactT_len (T : WalkTable) (C : List Nat)
    (mu : List Nat) (x : List BPair)
    (hx : x.length = (monomialsAt mu).length) :
    (wactT T C (⟨mu, x⟩ : HVec)).coords.length
      = (monomialsAt (wcontentT T C mu)).length := by
  have hs : sized (wactT T C (⟨mu, x⟩ : HVec)) :=
    wactT_sized T C (⟨mu, x⟩ : HVec) hx
  show (wactT T C (⟨mu, x⟩ : HVec)).coords.length = _
  rw [hs, wactT_content T C (⟨mu, x⟩ : HVec)]

/-- A vector's content presentation at its own read. -/
private theorem hvec_eta (w : HVec) (mu : List Nat)
    (h : w.content = mu) : w = (⟨mu, w.coords⟩ : HVec) := by
  rw [← h]

/-- A word's action splits over the memberwise sum. -/
private theorem wactT_vecAdd (T : WalkTable) :
    ∀ (C : List Nat) (mu : List Nat) (x y : List BPair),
    x.length = (monomialsAt mu).length →
    y.length = (monomialsAt mu).length →
    poly.oneValue (wactT T C (⟨mu, elim.vecAdd x y⟩ : HVec)).coords
      (elim.vecAdd (wactT T C (⟨mu, x⟩ : HVec)).coords
        (wactT T C (⟨mu, y⟩ : HVec)).coords)
  | [], _, x, y, _, _ => poly.oneValue_refl (elim.vecAdd x y)
  | l :: t, mu, x, y, hx, hy => by
    have hlx := wactT_len T t mu x hx
    have hly := wactT_len T t mu y hy
    show poly.oneValue
      (T.step l (wactT T t (⟨mu, elim.vecAdd x y⟩ : HVec))).coords
      (elim.vecAdd
        (T.step l (wactT T t (⟨mu, x⟩ : HVec))).coords
        (T.step l (wactT T t (⟨mu, y⟩ : HVec))).coords)
    rw [hvec_eta (wactT T t (⟨mu, elim.vecAdd x y⟩ : HVec))
        (wcontentT T t mu) (wactT_content T t _),
      hvec_eta (wactT T t (⟨mu, x⟩ : HVec))
        (wcontentT T t mu) (wactT_content T t _),
      hvec_eta (wactT T t (⟨mu, y⟩ : HVec))
        (wcontentT T t mu) (wactT_content T t _)]
    refine poly.oneValue_trans
      (T.step_congr l _
        (⟨wcontentT T t mu,
          elim.vecAdd (wactT T t (⟨mu, x⟩ : HVec)).coords
            (wactT T t (⟨mu, y⟩ : HVec)).coords⟩ : HVec)
        rfl
        (wactT_vecAdd T t mu x y hx hy)) ?_
    exact T.step_vecAdd l (wcontentT T t mu)
      (wactT T t (⟨mu, x⟩ : HVec)).coords
      (wactT T t (⟨mu, y⟩ : HVec)).coords (hlx.trans hly.symm)

/-- A word's action keeps a clearing. -/
private theorem wactT_vecScale (T : WalkTable) :
    ∀ (C : List Nat) (mu : List Nat) (c : BPair) (x : List BPair),
    x.length = (monomialsAt mu).length →
    poly.oneValue
      (wactT T C (⟨mu, elim.vecScale c x⟩ : HVec)).coords
      (elim.vecScale c (wactT T C (⟨mu, x⟩ : HVec)).coords)
  | [], _, c, x, _ => poly.oneValue_refl (elim.vecScale c x)
  | l :: t, mu, c, x, hx => by
    show poly.oneValue
      (T.step l (wactT T t (⟨mu, elim.vecScale c x⟩ : HVec))).coords
      (elim.vecScale c
        (T.step l (wactT T t (⟨mu, x⟩ : HVec))).coords)
    rw [hvec_eta (wactT T t (⟨mu, elim.vecScale c x⟩ : HVec))
        (wcontentT T t mu) (wactT_content T t _),
      hvec_eta (wactT T t (⟨mu, x⟩ : HVec))
        (wcontentT T t mu) (wactT_content T t _)]
    refine poly.oneValue_trans
      (T.step_congr l _
        (⟨wcontentT T t mu,
          elim.vecScale c (wactT T t (⟨mu, x⟩ : HVec)).coords⟩ : HVec)
        rfl
        (wactT_vecScale T t mu c x hx)) ?_
    exact T.step_vecScale l (wcontentT T t mu) c
      (wactT T t (⟨mu, x⟩ : HVec)).coords

/-! The graded pairing against a word's image: the guard is the
chain's own content, so the pairing is linear in the acted vector's
coordinates inside the content summand and reads the sum's unit
outside it. -/

/-- The pairing reads one value in its right member at one
content. -/
private theorem dotG_congr_right (v w w' : HVec)
    (hc : w.content = w'.content)
    (hq : poly.oneValue w.coords w'.coords) :
    (dotG v w).oneValue (dotG v w') := by
  by_cases hg : v.content = w.content
  · rw [dotG_read v w hg, dotG_read v w' (by rw [← hc]; exact hg)]
    exact elim.dotP_oneValue_right v.coords _ _ hq
  · rw [dotG_off v w hg, dotG_off v w' (by rw [← hc]; exact hg)]
    exact BPair.oneValue_refl _

/-- The pairing against a word's image splits over the memberwise
sum at the chain's content. -/
private theorem dotG_addT (T : WalkTable) (X : HVec) (C : List Nat)
    (mu : List Nat) (a b : List BPair)
    (ha : a.length = (monomialsAt mu).length)
    (hb : b.length = (monomialsAt mu).length) :
    (dotG X (wactT T C (⟨mu, elim.vecAdd a b⟩ : HVec))).oneValue
      (dotG X (wactT T C (⟨mu, a⟩ : HVec))
        + dotG X (wactT T C (⟨mu, b⟩ : HVec))) := by
  have hgc : ∀ z : List BPair,
      (wactT T C (⟨mu, z⟩ : HVec)).content = wcontentT T C mu :=
    fun z => wactT_content T C (⟨mu, z⟩ : HVec)
  by_cases hg : X.content = wcontentT T C mu
  · rw [dotG_read X (wactT T C (⟨mu, elim.vecAdd a b⟩ : HVec))
        (by rw [hgc (elim.vecAdd a b)]; exact hg),
      dotG_read X (wactT T C (⟨mu, a⟩ : HVec))
        (by rw [hgc a]; exact hg),
      dotG_read X (wactT T C (⟨mu, b⟩ : HVec))
        (by rw [hgc b]; exact hg)]
    refine BPair.oneValue_trans (elim.dotP_oneValue_right X.coords _ _
      (wactT_vecAdd T C mu a b ha hb)) ?_
    exact elim.dotP_vecAdd_right X.coords _ _
      ((wactT_len T C mu a ha).trans (wactT_len T C mu b hb).symm)
  · rw [dotG_off X (wactT T C (⟨mu, elim.vecAdd a b⟩ : HVec))
        (by rw [hgc (elim.vecAdd a b)]; exact hg),
      dotG_off X (wactT T C (⟨mu, a⟩ : HVec))
        (by rw [hgc a]; exact hg),
      dotG_off X (wactT T C (⟨mu, b⟩ : HVec))
        (by rw [hgc b]; exact hg)]
    exact BPair.oneValue_symm (BPair.unit_add BPair.unit)

/-- The pairing against a word's image keeps a clearing at the
chain's content. -/
private theorem dotG_scaleT (T : WalkTable) (X : HVec) (C : List Nat)
    (mu : List Nat) (b : List BPair) (c : BPair)
    (hb : b.length = (monomialsAt mu).length) :
    (dotG X (wactT T C (⟨mu, elim.vecScale c b⟩ : HVec))).oneValue
      (c * dotG X (wactT T C (⟨mu, b⟩ : HVec))) := by
  have hgc : ∀ z : List BPair,
      (wactT T C (⟨mu, z⟩ : HVec)).content = wcontentT T C mu :=
    fun z => wactT_content T C (⟨mu, z⟩ : HVec)
  by_cases hg : X.content = wcontentT T C mu
  · rw [dotG_read X (wactT T C (⟨mu, elim.vecScale c b⟩ : HVec))
        (by rw [hgc (elim.vecScale c b)]; exact hg),
      dotG_read X (wactT T C (⟨mu, b⟩ : HVec))
        (by rw [hgc b]; exact hg)]
    refine BPair.oneValue_trans (elim.dotP_oneValue_right X.coords _ _
      (wactT_vecScale T C mu c b hb)) ?_
    exact elim.dotP_vecScale_right X.coords _ c
  · rw [dotG_off X (wactT T C (⟨mu, elim.vecScale c b⟩ : HVec))
        (by rw [hgc (elim.vecScale c b)]; exact hg),
      dotG_off X (wactT T C (⟨mu, b⟩ : HVec))
        (by rw [hgc b]; exact hg)]
    exact BPair.oneValue_symm (BPair.mul_unit c)

/-- The pairing against a word's image of a summand and a clearing. -/
private theorem dotG_push (T : WalkTable) (X : HVec) (C : List Nat)
    (mu : List Nat) (a b : List BPair) (c : BPair)
    (ha : a.length = (monomialsAt mu).length)
    (hb : b.length = (monomialsAt mu).length) :
    (dotG X (wactT T C
        (⟨mu, elim.vecAdd a (elim.vecScale c b)⟩ : HVec))).oneValue
      (dotG X (wactT T C (⟨mu, a⟩ : HVec))
        + c * dotG X (wactT T C (⟨mu, b⟩ : HVec))) :=
  BPair.oneValue_trans
    (dotG_addT T X C mu a (elim.vecScale c b) ha
      (by rw [elim.length_vecScale]; exact hb))
    (BPair.add_congr (BPair.oneValue_refl _)
      (dotG_scaleT T X C mu b c hb))

/-- The table's crossing at the word level: the two crossed
composites' pairings differ by the two content entries' scalings of
the source's own pairing — `[E, F] = H` read inside the word, both
vacant arms included. -/
private theorem crossT (T : WalkTable) (X : HVec) (C : List Nat)
    (Y : HVec) (j : Nat)
    (hsY : sized Y) (hj : j + 1 < Y.content.length) :
    (dotG X (wactT T C (T.tr j (T.step j Y)))
        + BPair.ofNat (ground.getAt 0 Y.content (T.uLet j))
          * dotG X (wactT T C Y)).oneValue
      (dotG X (wactT T (C ++ [j]) (T.tr j Y))
        + BPair.ofNat (ground.getAt 0 Y.content (T.dLet j))
          * dotG X (wactT T C Y)) := by
  rw [wactT_append T C j (T.tr j Y)]
  have hS1len : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 Y.content (T.uLet j)))
      Y.coords).length = (monomialsAt Y.content).length := by
    rw [elim.length_vecScale]
    exact hsY
  have hS0len : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 Y.content (T.dLet j)))
      Y.coords).length = (monomialsAt Y.content).length := by
    rw [elim.length_vecScale]
    exact hsY
  by_cases hD : 0 < ground.getAt 0 Y.content (T.dLet j)
  · have hc1 : (T.tr j (T.step j Y)).content = Y.content := by
      rw [T.tr_content j (T.step j Y), T.step_content j Y,
        moveAt_round_at (T.dLet j) (T.uLet j) Y.content hD]
    have hl1 : (T.tr j (T.step j Y)).coords.length
        = (monomialsAt Y.content).length := by
      rw [T.tr_sized j (T.step j Y), hc1]
    have conn1 : (dotG X (wactT T C (T.tr j (T.step j Y)))).oneValue
        (dotG X (wactT T C (⟨Y.content,
          (T.tr j (T.step j Y)).coords⟩ : HVec))) :=
      match wactT_congr T C (T.tr j (T.step j Y))
        (⟨Y.content, (T.tr j (T.step j Y)).coords⟩ : HVec)
        hc1 rfl (poly.oneValue_refl _) with
      | ⟨h1, h2, h3⟩ => dotG_congr_right X _ _ h1 h3
    by_cases hU : 0 < ground.getAt 0 Y.content (T.uLet j)
    · have hc2 : (T.step j (T.tr j Y)).content = Y.content := by
        rw [T.step_content j (T.tr j Y), T.tr_content j Y,
          moveAt_round_at (T.uLet j) (T.dLet j) Y.content hU]
      have hl2 : (T.step j (T.tr j Y)).coords.length
          = (monomialsAt Y.content).length := by
        rw [T.step_sized j (T.tr j Y), hc2]
      have conn2 : (dotG X (wactT T C (T.step j (T.tr j Y)))).oneValue
          (dotG X (wactT T C (⟨Y.content,
            (T.step j (T.tr j Y)).coords⟩ : HVec))) :=
        match wactT_congr T C (T.step j (T.tr j Y))
          (⟨Y.content, (T.step j (T.tr j Y)).coords⟩ : HVec)
          hc2 rfl (poly.oneValue_refl _) with
        | ⟨h1, h2, h3⟩ => dotG_congr_right X _ _ h1 h3
      have hmid : (dotG X (wactT T C (⟨Y.content,
            elim.vecAdd (T.tr j (T.step j Y)).coords
              (elim.vecScale (BPair.ofNat
                (ground.getAt 0 Y.content (T.uLet j)))
                Y.coords)⟩ : HVec))).oneValue
          (dotG X (wactT T C (⟨Y.content,
            elim.vecAdd (T.step j (T.tr j Y)).coords
              (elim.vecScale (BPair.ofNat
                (ground.getAt 0 Y.content (T.dLet j)))
                Y.coords)⟩ : HVec))) :=
        match wactT_congr T C
          (⟨Y.content,
            elim.vecAdd (T.tr j (T.step j Y)).coords
              (elim.vecScale (BPair.ofNat
                (ground.getAt 0 Y.content (T.uLet j)))
                Y.coords)⟩ : HVec)
          (⟨Y.content,
            elim.vecAdd (T.step j (T.tr j Y)).coords
              (elim.vecScale (BPair.ofNat
                (ground.getAt 0 Y.content (T.dLet j)))
                Y.coords)⟩ : HVec)
          rfl
          (by rw [elim.length_vecAdd _ _ _ hl1 hS1len,
            elim.length_vecAdd _ _ _ hl2 hS0len])
          (T.cross_occ j Y hsY hj hD hU) with
        | ⟨h1, h2, h3⟩ => dotG_congr_right X _ _ h1 h3
      refine BPair.oneValue_trans
        (BPair.add_congr conn1 (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans (BPair.oneValue_symm
        (dotG_push T X C Y.content (T.tr j (T.step j Y)).coords
          Y.coords
          (BPair.ofNat (ground.getAt 0 Y.content (T.uLet j)))
          hl1 hsY)) ?_
      refine BPair.oneValue_trans hmid ?_
      refine BPair.oneValue_trans
        (dotG_push T X C Y.content (T.step j (T.tr j Y)).coords
          Y.coords
          (BPair.ofNat (ground.getAt 0 Y.content (T.dLet j)))
          hl2 hsY) ?_
      exact BPair.add_congr (BPair.oneValue_symm conn2)
        (BPair.oneValue_refl _)
    · have hU0 : ground.getAt 0 Y.content (T.uLet j) = 0 :=
        Nat.eq_zero_of_not_pos hU
      have conn1' : (dotG X (wactT T C (⟨Y.content,
            (T.tr j (T.step j Y)).coords⟩ : HVec))).oneValue
          (dotG X (wactT T C (⟨Y.content,
            elim.vecScale (BPair.ofNat
              (ground.getAt 0 Y.content (T.dLet j)))
              Y.coords⟩ : HVec))) :=
        match wactT_congr T C
          (⟨Y.content, (T.tr j (T.step j Y)).coords⟩ : HVec)
          (⟨Y.content, elim.vecScale (BPair.ofNat
            (ground.getAt 0 Y.content (T.dLet j)))
            Y.coords⟩ : HVec)
          rfl (hl1.trans hS0len.symm)
          (T.cross_vacU j Y hsY hj hD hU0) with
        | ⟨h1, h2, h3⟩ => dotG_congr_right X _ _ h1 h3
      have hleft : (dotG X (wactT T C (T.tr j (T.step j Y)))).oneValue
          (BPair.ofNat (ground.getAt 0 Y.content (T.dLet j))
            * dotG X (wactT T C Y)) :=
        BPair.oneValue_trans conn1 (BPair.oneValue_trans conn1'
          (dotG_scaleT T X C Y.content Y.coords
            (BPair.ofNat (ground.getAt 0 Y.content (T.dLet j))) hsY))
      have hright : (dotG X
          (wactT T C (T.step j (T.tr j Y)))).oneValue BPair.unit :=
        dotG_null_right _ _ (wactT_unitTail T C _
          (T.step_unitTail j (T.tr j Y) (T.tr_vac j Y hU0)))
      rw [hU0]
      refine BPair.oneValue_trans
        (BPair.add_congr hleft (BPair.unit_mul _)) ?_
      refine BPair.oneValue_trans (BPair.add_unit _) ?_
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr hright (BPair.oneValue_refl _))
        (BPair.unit_add _))
  · have hD0 : ground.getAt 0 Y.content (T.dLet j) = 0 :=
      Nat.eq_zero_of_not_pos hD
    have hleft : (dotG X
        (wactT T C (T.tr j (T.step j Y)))).oneValue BPair.unit :=
      dotG_null_right _ _ (wactT_unitTail T C _
        (T.tr_unitTail j (T.step j Y) (T.step_vac j Y hD0)))
    by_cases hU : 0 < ground.getAt 0 Y.content (T.uLet j)
    · have hc2 : (T.step j (T.tr j Y)).content = Y.content := by
        rw [T.step_content j (T.tr j Y), T.tr_content j Y,
          moveAt_round_at (T.uLet j) (T.dLet j) Y.content hU]
      have hl2 : (T.step j (T.tr j Y)).coords.length
          = (monomialsAt Y.content).length := by
        rw [T.step_sized j (T.tr j Y), hc2]
      have conn2 : (dotG X (wactT T C (T.step j (T.tr j Y)))).oneValue
          (dotG X (wactT T C (⟨Y.content,
            (T.step j (T.tr j Y)).coords⟩ : HVec))) :=
        match wactT_congr T C (T.step j (T.tr j Y))
          (⟨Y.content, (T.step j (T.tr j Y)).coords⟩ : HVec)
          hc2 rfl (poly.oneValue_refl _) with
        | ⟨h1, h2, h3⟩ => dotG_congr_right X _ _ h1 h3
      have conn2' : (dotG X (wactT T C (⟨Y.content,
            (T.step j (T.tr j Y)).coords⟩ : HVec))).oneValue
          (dotG X (wactT T C (⟨Y.content,
            elim.vecScale (BPair.ofNat
              (ground.getAt 0 Y.content (T.uLet j)))
              Y.coords⟩ : HVec))) :=
        match wactT_congr T C
          (⟨Y.content, (T.step j (T.tr j Y)).coords⟩ : HVec)
          (⟨Y.content, elim.vecScale (BPair.ofNat
            (ground.getAt 0 Y.content (T.uLet j)))
            Y.coords⟩ : HVec)
          rfl (hl2.trans hS1len.symm)
          (T.cross_vacD j Y hsY hj hD0 hU) with
        | ⟨h1, h2, h3⟩ => dotG_congr_right X _ _ h1 h3
      have hright : (dotG X
          (wactT T C (T.step j (T.tr j Y)))).oneValue
          (BPair.ofNat (ground.getAt 0 Y.content (T.uLet j))
            * dotG X (wactT T C Y)) :=
        BPair.oneValue_trans conn2 (BPair.oneValue_trans conn2'
          (dotG_scaleT T X C Y.content Y.coords
            (BPair.ofNat (ground.getAt 0 Y.content (T.uLet j))) hsY))
      rw [hD0]
      refine BPair.oneValue_trans
        (BPair.add_congr hleft (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans (BPair.unit_add _) ?_
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr hright (BPair.unit_mul _))
        (BPair.add_unit _))
    · have hU0 : ground.getAt 0 Y.content (T.uLet j) = 0 :=
        Nat.eq_zero_of_not_pos hU
      have hright : (dotG X
          (wactT T C (T.step j (T.tr j Y)))).oneValue BPair.unit :=
        dotG_null_right _ _ (wactT_unitTail T C _
          (T.step_unitTail j (T.tr j Y) (T.tr_vac j Y hU0)))
      rw [hU0, hD0]
      refine BPair.oneValue_trans
        (BPair.add_congr hleft (BPair.unit_mul _)) ?_
      refine BPair.oneValue_trans (BPair.unit_add _) ?_
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr hright (BPair.unit_mul _))
        (BPair.unit_add _))

/-- The table's transpose identity at the graded pairing, total in
the guards: the step's image pairs a vector as the source pairs the
transposed image, both sides reading the sum's unit wherever the
letters are vacant or the contents miss. -/
private theorem dotG_step_tr (T : WalkTable) (j : Nat) (X Z : HVec)
    (hsX : sized X) (hsZ : sized Z)
    (hj : j + 1 < X.content.length) :
    (dotG (T.step j X) Z).oneValue (dotG X (T.tr j Z)) := by
  by_cases hD : 0 < ground.getAt 0 X.content (T.dLet j)
  · by_cases hZ : Z.content = moveAt (T.uLet j) (T.dLet j) X.content
    · rw [dotG_read (T.step j X) Z
        (by rw [T.step_content j X]; exact hZ.symm),
        dotG_read X (T.tr j Z)
        (by rw [T.tr_content j Z, hZ,
          moveAt_round_at (T.dLet j) (T.uLet j) X.content hD])]
      exact T.adjoint j X Z hsX hsZ hj hD hZ
    · rw [dotG_off (T.step j X) Z
        (by rw [T.step_content j X]; exact fun hh => hZ hh.symm)]
      by_cases hZu : 0 < ground.getAt 0 Z.content (T.uLet j)
      · have hne : ¬ X.content = (T.tr j Z).content := by
          intro hg
          refine hZ ?_
          have hg' : X.content
              = moveAt (T.dLet j) (T.uLet j) Z.content := by
            rw [hg, T.tr_content j Z]
          rw [hg',
            moveAt_round_at (T.uLet j) (T.dLet j) Z.content hZu]
        rw [dotG_off X (T.tr j Z) hne]
        exact BPair.oneValue_refl _
      · exact BPair.oneValue_symm (dotG_null_right X (T.tr j Z)
          (T.tr_vac j Z (Nat.eq_zero_of_not_pos hZu)))
  · refine BPair.oneValue_trans (dotG_null_left (T.step j X) Z
      (T.step_vac j X (Nat.eq_zero_of_not_pos hD))) ?_
    by_cases hZu : 0 < ground.getAt 0 Z.content (T.uLet j)
    · have hne : ¬ X.content = (T.tr j Z).content := by
        intro hg
        have hg' : X.content
            = bumpAt (T.dLet j) (dipAt (T.uLet j) Z.content) := by
          rw [hg, T.tr_content j Z]
          rfl
        have hlenXZ : X.content.length = Z.content.length := by
          rw [hg, T.tr_content j Z, length_moveAt]
        have hdle : T.dLet j
            < (dipAt (T.uLet j) Z.content).length := by
          rw [ground.length_dipAt, ← hlenXZ]
          match T.letters j with
          | .inl hlet => rw [hlet.1]; exact Nat.lt_of_succ_lt hj
          | .inr hlet => rw [hlet.1]; exact hj
        have hzero : ground.getAt 0 X.content (T.dLet j) = 0 :=
          Nat.eq_zero_of_not_pos hD
        rw [hg', ground.getAt_bumpAt_self (T.dLet j) _ hdle] at hzero
        exact Nat.noConfusion hzero
      rw [dotG_off X (T.tr j Z) hne]
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_symm (dotG_null_right X (T.tr j Z)
        (T.tr_vac j Z (Nat.eq_zero_of_not_pos hZu)))

/-- The transpose identity read in the other direction: the
transposed image pairs a vector as the source pairs the step's
image. -/
private theorem dotG_tr_step (T : WalkTable) (j : Nat) (A B : HVec)
    (hsA : sized A) (hsB : sized B)
    (hj : j + 1 < B.content.length) :
    (dotG (T.tr j A) B).oneValue (dotG A (T.step j B)) := by
  rw [dotG_comm (T.tr j A) B, dotG_comm A (T.step j B)]
  exact BPair.oneValue_symm (dotG_step_tr T j B A hsB hsA hj)

/-- A null crossing closes the walk: both sides' pairings read the
sum's unit, so the two displays meet there. -/
private theorem walk_null_closeT (T U : WalkTable) (t u : HVec)
    (A C : List Nat) (Z Zu : HVec)
    (hz : poly.unitTail Z.coords) (hzu : poly.unitTail Zu.coords) :
    (dotG (wactT T A t) (wactT T C Z)
        * elim.dotP u.coords u.coords).oneValue
      (dotG (wactT U A u) (wactT U C Zu)
        * elim.dotP t.coords t.coords) := by
  refine BPair.oneValue_trans (BPair.oneValue_trans
    (BPair.mul_congr (dotG_null_right _ _ (wactT_unitTail T C Z hz))
      (BPair.oneValue_refl _))
    (BPair.unit_mul _)) ?_
  exact BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr (dotG_null_right _ _ (wactT_unitTail U C Zu hzu))
      (BPair.oneValue_refl _))
    (BPair.unit_mul _))

/-! The crossing's algebra at the balance carrier: a crossing
display on each side, the two emitted scalars tied cross-added, the
shorter word's pairing and the emission's own — the cancellation
that leaves the two displays reading one value, with the two arms
where one side's crossing is the sum's unit. -/

/-- A summand's clearing distributes across a product. -/
private theorem distrib_r (a b c s : BPair) :
    (a + s * b) * c = a * c + s * (b * c) := by
  rw [BPair.right_distrib, BPair.mul_assoc]

private theorem cross_cancel_tie
    (Qt Qt' Qu Qu' Pt Pu U T s1 s0 s1' s0' : BPair)
    (ht : (Qt + s1 * Pt).oneValue (Qt' + s0 * Pt))
    (hu : (Qu + s1' * Pu).oneValue (Qu' + s0' * Pu))
    (htie : (s1 + s0').oneValue (s1' + s0))
    (hrec : (Qt' * U).oneValue (Qu' * T))
    (hemit : (Pt * U).oneValue (Pu * T)) :
    (Qt * U).oneValue (Qu * T) := by
  have hI : (Qt * U + s1 * (Pu * T)).oneValue
      (Qt' * U + s0 * (Pu * T)) := by
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_refl (Qt * U))
      (BPair.mul_congr (BPair.oneValue_refl s1)
        (BPair.oneValue_symm hemit))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (distrib_r Qt Pt U s1).symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr ht (BPair.oneValue_refl U)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (distrib_r Qt' Pt U s0)) ?_
    exact BPair.add_congr (BPair.oneValue_refl (Qt' * U))
      (BPair.mul_congr (BPair.oneValue_refl s0) hemit)
  have hII : (Qu * T + s1' * (Pu * T)).oneValue
      (Qu' * T + s0' * (Pu * T)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (distrib_r Qu Pu T s1').symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr hu (BPair.oneValue_refl T)) ?_
    exact BPair.oneValue_of_eq (distrib_r Qu' Pu T s0')
  refine BPair.add_cancel (c := (s1 + s0') * (Pu * T)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (show Qt * U + (s1 + s0') * (Pu * T)
        = Qt * U + s1 * (Pu * T) + s0' * (Pu * T) from by
      rw [BPair.right_distrib, BPair.add_assoc])) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr hI (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (BPair.add_right_comm (Qt' * U) (s0 * (Pu * T)) (s0' * (Pu * T)))) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr hrec (BPair.oneValue_refl _))
    (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_symm hII) (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (show Qu * T + s1' * (Pu * T) + s0 * (Pu * T)
        = Qu * T + (s1' + s0) * (Pu * T) from by
      rw [BPair.right_distrib, BPair.add_assoc])) ?_
  exact BPair.add_congr (BPair.oneValue_refl (Qu * T))
    (BPair.mul_congr (BPair.oneValue_symm htie)
      (BPair.oneValue_refl (Pu * T)))

/-- The crossing arm at a null first side: the first side's crossed
pairing and its emitted pairings all read the sum's unit, so the
second side's display collapses there too. -/
private theorem cross_null_t (Qt Qu Qu' Pu U T s1' s0' : BPair)
    (hQt : Qt.oneValue BPair.unit)
    (hu : (Qu + s1' * Pu).oneValue (Qu' + s0' * Pu))
    (hQu' : (Qu' * T).oneValue BPair.unit)
    (hPu : (Pu * T).oneValue BPair.unit) :
    (Qt * U).oneValue (Qu * T) := by
  refine BPair.oneValue_trans (BPair.oneValue_trans
    (BPair.mul_congr hQt (BPair.oneValue_refl U))
    (BPair.unit_mul U)) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.add_cancel (c := s1' * (Pu * T)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (distrib_r Qu Pu T s1').symm) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr hu (BPair.oneValue_refl T)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (distrib_r Qu' Pu T s0')) ?_
  refine BPair.oneValue_trans (BPair.add_congr hQu'
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s0') hPu)
      (BPair.mul_unit s0'))) ?_
  exact BPair.oneValue_symm (BPair.add_congr
    (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s1') hPu)
      (BPair.mul_unit s1')))

/-- The crossing arm at a null second side. -/
private theorem cross_null_u (Qt Qt' Qu Pt U T s1 s0 : BPair)
    (hQu : Qu.oneValue BPair.unit)
    (ht : (Qt + s1 * Pt).oneValue (Qt' + s0 * Pt))
    (hQt' : (Qt' * U).oneValue BPair.unit)
    (hPt : (Pt * U).oneValue BPair.unit) :
    (Qt * U).oneValue (Qu * T) := by
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (BPair.oneValue_trans
      (BPair.mul_congr hQu (BPair.oneValue_refl T))
      (BPair.unit_mul T)))
  refine BPair.add_cancel (c := s1 * (Pt * U)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (distrib_r Qt Pt U s1).symm) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr ht (BPair.oneValue_refl U)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (distrib_r Qt' Pt U s0)) ?_
  refine BPair.oneValue_trans (BPair.add_congr hQt'
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s0) hPt)
      (BPair.mul_unit s0))) ?_
  exact BPair.oneValue_symm (BPair.add_congr
    (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s1) hPt)
      (BPair.mul_unit s1)))

/-! `lem:blockirr`(iv)'s walk over two tables: the reversed word
walks across the transposes, each crossing folding into a content
read with a shorter word's pairing, and a raising's read at a top
is the sum's unit. -/

private theorem walkGoT (T U : WalkTable) (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u)
    (hdt : t.content.length = d) (hdu : u.content.length = d)
    (htopt : ∀ j, j + 1 < d → poly.unitTail (T.tr j t).coords)
    (htopu : ∀ j, j + 1 < d → poly.unitTail (U.tr j u).coords)
    (htie : ∀ (ws : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ ws, l + 1 < d) →
      ¬ poly.unitTail (wactT T ws t).coords →
      ¬ poly.unitTail (wactT U ws u).coords →
      ground.getAt 0 (wactT T ws t).content (T.uLet j)
          + ground.getAt 0 (wactT U ws u).content (U.dLet j)
        = ground.getAt 0 (wactT U ws u).content (U.uLet j)
          + ground.getAt 0 (wactT T ws t).content (T.dLet j))
    (n : Nat)
    (IH : ∀ ws ws' : List Nat, ws.length + ws'.length < n →
      (∀ l ∈ ws, l + 1 < d) → (∀ l ∈ ws', l + 1 < d) →
      (dotG (wactT T ws t) (wactT T ws' t)
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U ws u) (wactT U ws' u)
          * elim.dotP t.coords t.coords)) :
    ∀ (B A C : List Nat) (j : Nat),
      A.length + 1 + C.length + B.length = n →
      j + 1 < d →
      (∀ l ∈ A, l + 1 < d) → (∀ l ∈ B, l + 1 < d) →
      (∀ l ∈ C, l + 1 < d) →
      (dotG (wactT T A t) (wactT T C (T.tr j (wactT T B t)))
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U A u) (wactT U C (U.tr j (wactT U B u)))
          * elim.dotP t.coords t.coords)
  | [], A, C, j, _, hjd, _, _, _ =>
    walk_null_closeT T U t u A C _ _ (htopt j hjd) (htopu j hjd)
  | l :: B', A, C, j, hn, hjd, hA, hB, hC => by
    have hB' : ∀ x ∈ B', x + 1 < d := memAll_tail hB
    have hld : l + 1 < d := hB l (.head _)
    have hsYt : sized (wactT T B' t) := wactT_sized T B' t hst
    have hsYu : sized (wactT U B' u) := wactT_sized U B' u hsu
    have hlenYt : (wactT T B' t).content.length = d := by
      rw [wactT_content T B' t, wcontentT_len, hdt]
    have hlenYu : (wactT U B' u).content.length = d := by
      rw [wactT_content U B' u, wcontentT_len, hdu]
    have hj1t : j + 1 < (wactT T B' t).content.length := by
      rw [hlenYt]; exact hjd
    have hj1u : j + 1 < (wactT U B' u).content.length := by
      rw [hlenYu]; exact hjd
    have hltn : A.length + (C ++ B').length < n := by
      rw [← hn, ground.length_append]
      show A.length + (C.length + B'.length)
        < A.length + 1 + C.length + (B'.length + 1)
      rw [Nat.add_succ (A.length + 1 + C.length) B'.length,
        Nat.add_right_comm A.length 1 C.length,
        Nat.add_right_comm (A.length + C.length) 1 B'.length,
        Nat.add_assoc A.length C.length B'.length]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _)
    have hemit := IH A (C ++ B') hltn hA (ground.all_of_append _ _ _ hC hB')
    rw [wactT_concat T C B' t, wactT_concat U C B' u] at hemit
    have hrecArith : A.length + 1 + (C ++ [l]).length + B'.length = n := by
      rw [← hn, ground.length_append]
      show A.length + 1 + (C.length + 1) + B'.length
        = A.length + 1 + C.length + (B'.length + 1)
      rw [Nat.add_succ (A.length + 1) C.length,
        Nat.add_right_comm (A.length + 1 + C.length) 1 B'.length,
        Nat.add_succ (A.length + 1 + C.length) B'.length]
    have hrec := walkGoT T U d t u hst hsu hdt hdu htopt htopu htie
      n IH B' A (C ++ [l]) j hrecArith hjd hA hB'
      (ground.all_of_append _ _ _ hC (memAll_cons hld memAll_nil))
    show (dotG (wactT T A t)
        (wactT T C (T.tr j (T.step l (wactT T B' t))))
        * elim.dotP u.coords u.coords).oneValue
      (dotG (wactT U A u)
        (wactT U C (U.tr j (U.step l (wactT U B' u))))
        * elim.dotP t.coords t.coords)
    by_cases hlj : l = j
    · subst hlj
      by_cases hYn : poly.unitTail (wactT T B' t).coords
      · have hQu' : ((dotG (wactT U A u)
            (wactT U (C ++ [l]) (U.tr l (wactT U B' u))))
            * elim.dotP t.coords t.coords).oneValue BPair.unit :=
          BPair.oneValue_trans (BPair.oneValue_symm hrec)
            (BPair.oneValue_trans
              (BPair.mul_congr (dotG_null_right _ _
                (wactT_unitTail T (C ++ [l]) _
                  (T.tr_unitTail l _ hYn)))
                (BPair.oneValue_refl _))
              (BPair.unit_mul _))
        have hPu := BPair.oneValue_trans (BPair.oneValue_symm hemit)
          (BPair.oneValue_trans
            (BPair.mul_congr (dotG_null_right _ _
              (wactT_unitTail T C _ hYn))
              (BPair.oneValue_refl _))
            (BPair.unit_mul _))
        exact cross_null_t _ _ _ _ _ _ _ _
          (dotG_null_right _ _ (wactT_unitTail T C _
            (T.tr_unitTail l _ (T.step_unitTail l _ hYn))))
          (crossT U (wactT U A u) C (wactT U B' u) l hsYu hj1u)
          hQu' hPu
      · by_cases hY'n : poly.unitTail (wactT U B' u).coords
        · have hQt' : ((dotG (wactT T A t)
              (wactT T (C ++ [l]) (T.tr l (wactT T B' t))))
              * elim.dotP u.coords u.coords).oneValue BPair.unit :=
            BPair.oneValue_trans hrec
              (BPair.oneValue_trans
                (BPair.mul_congr (dotG_null_right _ _
                  (wactT_unitTail U (C ++ [l]) _
                    (U.tr_unitTail l _ hY'n)))
                  (BPair.oneValue_refl _))
                (BPair.unit_mul _))
          have hPt := BPair.oneValue_trans hemit
            (BPair.oneValue_trans
              (BPair.mul_congr (dotG_null_right _ _
                (wactT_unitTail U C _ hY'n))
                (BPair.oneValue_refl _))
              (BPair.unit_mul _))
          exact cross_null_u _ _ _ _ _ _ _ _
            (dotG_null_right _ _ (wactT_unitTail U C _
              (U.tr_unitTail l _ (U.step_unitTail l _ hY'n))))
            (crossT T (wactT T A t) C (wactT T B' t) l hsYt hj1t)
            hQt' hPt
        · have htieN := htie B' l hjd hB' hYn hY'n
          have htieB : (BPair.ofNat
              (ground.getAt 0 (wactT T B' t).content (T.uLet l))
              + BPair.ofNat
                (ground.getAt 0 (wactT U B' u).content (U.dLet l))).oneValue
              (BPair.ofNat
                (ground.getAt 0 (wactT U B' u).content (U.uLet l))
              + BPair.ofNat
                (ground.getAt 0 (wactT T B' t).content (T.dLet l))) :=
            BPair.oneValue_trans
              (BPair.oneValue_symm (BPair.ofNat_add _ _))
              (BPair.oneValue_trans
                (BPair.oneValue_of_eq (congrArg BPair.ofNat htieN))
                (BPair.ofNat_add _ _))
          exact cross_cancel_tie _ _ _ _ _ _ _ _ _ _ _ _
            (crossT T (wactT T A t) C (wactT T B' t) l hsYt hj1t)
            (crossT U (wactT U A u) C (wactT U B' u) l hsYu hj1u)
            htieB hrec hemit
    · have hltBt : l + 1 < (wactT T B' t).content.length := by
        rw [hlenYt]; exact hld
      have hltBu : l + 1 < (wactT U B' u).content.length := by
        rw [hlenYu]; exact hld
      have wcT := wactT_congr T C _ _
        (T.comm l j (wactT T B' t) hlj hsYt hltBt hj1t).1
        (T.comm l j (wactT T B' t) hlj hsYt hltBt hj1t).2.1
        (T.comm l j (wactT T B' t) hlj hsYt hltBt hj1t).2.2
      have wcU := wactT_congr U C _ _
        (U.comm l j (wactT U B' u) hlj hsYu hltBu hj1u).1
        (U.comm l j (wactT U B' u) hlj hsYu hltBu hj1u).2.1
        (U.comm l j (wactT U B' u) hlj hsYu hltBu hj1u).2.2
      refine BPair.oneValue_trans (BPair.mul_congr
        (dotG_congr_right (wactT T A t) _ _ wcT.1 wcT.2.2)
        (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans (BPair.mul_congr
        (BPair.oneValue_of_eq (congrArg
          (fun w => dotG (wactT T A t) w)
          (wactT_append T C l (T.tr j (wactT T B' t))).symm))
        (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans hrec ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans (BPair.mul_congr
        (dotG_congr_right (wactT U A u) _ _ wcU.1 wcU.2.2)
        (BPair.oneValue_refl _)) ?_
      exact BPair.mul_congr
        (BPair.oneValue_of_eq (congrArg
          (fun w => dotG (wactT U A u) w)
          (wactT_append U C l (U.tr j (wactT U B' u))).symm))
        (BPair.oneValue_refl _)

/-- A leading step peels onto the walk at the transposed second
word, both sides at once. -/
private theorem stepT_of_walk (T U : WalkTable) (t u : HVec)
    (j : Nat) (A ws' : List Nat)
    (hsXt : sized (wactT T A t)) (hsZt : sized (wactT T ws' t))
    (hjt : j + 1 < (wactT T A t).content.length)
    (hsXu : sized (wactT U A u)) (hsZu : sized (wactT U ws' u))
    (hju : j + 1 < (wactT U A u).content.length)
    (hw : (dotG (wactT T A t) (T.tr j (wactT T ws' t))
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U A u) (U.tr j (wactT U ws' u))
          * elim.dotP t.coords t.coords)) :
    (dotG (wactT T (j :: A) t) (wactT T ws' t)
        * elim.dotP u.coords u.coords).oneValue
      (dotG (wactT U (j :: A) u) (wactT U ws' u)
        * elim.dotP t.coords t.coords) := by
  refine BPair.oneValue_trans (BPair.mul_congr
    (dotG_step_tr T j (wactT T A t) (wactT T ws' t) hsXt hsZt hjt)
    (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans hw ?_
  exact BPair.oneValue_symm (BPair.mul_congr
    (dotG_step_tr U j (wactT U A u) (wactT U ws' u) hsXu hsZu hju)
    (BPair.oneValue_refl _))

private theorem stepGoT (T U : WalkTable) (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u)
    (hdt : t.content.length = d) (hdu : u.content.length = d)
    (htopt : ∀ j, j + 1 < d → poly.unitTail (T.tr j t).coords)
    (htopu : ∀ j, j + 1 < d → poly.unitTail (U.tr j u).coords)
    (htie : ∀ (ws : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ ws, l + 1 < d) →
      ¬ poly.unitTail (wactT T ws t).coords →
      ¬ poly.unitTail (wactT U ws u).coords →
      ground.getAt 0 (wactT T ws t).content (T.uLet j)
          + ground.getAt 0 (wactT U ws u).content (U.dLet j)
        = ground.getAt 0 (wactT U ws u).content (U.uLet j)
          + ground.getAt 0 (wactT T ws t).content (T.dLet j))
    (n : Nat)
    (IH : ∀ ws ws' : List Nat, ws.length + ws'.length < n →
      (∀ l ∈ ws, l + 1 < d) → (∀ l ∈ ws', l + 1 < d) →
      (dotG (wactT T ws t) (wactT T ws' t)
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U ws u) (wactT U ws' u)
          * elim.dotP t.coords t.coords))
    (j : Nat) (A ws' : List Nat)
    (hle : A.length + 1 + ws'.length ≤ n)
    (hjd : j + 1 < d)
    (hA : ∀ l ∈ A, l + 1 < d) (hw' : ∀ l ∈ ws', l + 1 < d) :
    (dotG (wactT T (j :: A) t) (wactT T ws' t)
        * elim.dotP u.coords u.coords).oneValue
      (dotG (wactT U (j :: A) u) (wactT U ws' u)
        * elim.dotP t.coords t.coords) :=
  stepT_of_walk T U t u j A ws'
    (wactT_sized T A t hst) (wactT_sized T ws' t hst)
    (by rw [wactT_content T A t, wcontentT_len, hdt]; exact hjd)
    (wactT_sized U A u hsu) (wactT_sized U ws' u hsu)
    (by rw [wactT_content U A u, wcontentT_len, hdu]; exact hjd)
    (walkGoT T U d t u hst hsu hdt hdu htopt htopu htie
      (A.length + 1 + ws'.length)
      (fun a b hab hba hbb => IH a b (Nat.lt_of_lt_of_le hab hle) hba hbb)
      ws' A [] j rfl hjd hA hw' memAll_nil)

/-- The words' pairings read one value across the two tables
(`lem:blockirr`(iv)'s word-pair clause at the graded pairing): at a
top per table whose transposes read the sum's unit, with the two
tables' crossing scalars tied cross-added at every live word pair,
any two words pair at the first top against the second's
self-pairing exactly as they pair at the second against the
first's, one value per word pair. -/
theorem wordGramT (T U : WalkTable) (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u)
    (hdt : t.content.length = d) (hdu : u.content.length = d)
    (htopt : ∀ j, j + 1 < d → poly.unitTail (T.tr j t).coords)
    (htopu : ∀ j, j + 1 < d → poly.unitTail (U.tr j u).coords)
    (htie : ∀ (ws : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ ws, l + 1 < d) →
      ¬ poly.unitTail (wactT T ws t).coords →
      ¬ poly.unitTail (wactT U ws u).coords →
      ground.getAt 0 (wactT T ws t).content (T.uLet j)
          + ground.getAt 0 (wactT U ws u).content (U.dLet j)
        = ground.getAt 0 (wactT U ws u).content (U.uLet j)
          + ground.getAt 0 (wactT T ws t).content (T.dLet j)) :
    ∀ ws ws' : List Nat,
      (∀ j ∈ ws, j + 1 < d) → (∀ j ∈ ws', j + 1 < d) →
      (dotG (wactT T ws t) (wactT T ws' t)
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U ws u) (wactT U ws' u)
          * elim.dotP t.coords t.coords) := by
  suffices main : ∀ (n : Nat) (ws ws' : List Nat),
      ws.length + ws'.length < n →
      (∀ j ∈ ws, j + 1 < d) → (∀ j ∈ ws', j + 1 < d) →
      (dotG (wactT T ws t) (wactT T ws' t)
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U ws u) (wactT U ws' u)
          * elim.dotP t.coords t.coords) by
    exact fun ws ws' hb hb' =>
      main (ws.length + ws'.length + 1) ws ws'
        (Nat.lt_succ_self _) hb hb'
  intro n
  induction n with
  | zero =>
    intro ws ws' hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ihn =>
    intro ws ws' hlt hb hb'
    match ws with
    | j :: A =>
      refine stepGoT T U d t u hst hsu hdt hdu htopt htopu htie n
        ihn j A ws' ?_ (hb j (.head _)) (memAll_tail hb) hb'
      show A.length + 1 + ws'.length ≤ n
      exact Nat.le_of_lt_succ hlt
    | [] =>
      match ws' with
      | [] =>
        show (dotG t t * elim.dotP u.coords u.coords).oneValue
          (dotG u u * elim.dotP t.coords t.coords)
        rw [dotG_read t t rfl, dotG_read u u rfl]
        exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
      | l :: R' =>
        rw [dotG_comm (wactT T [] t) (wactT T (l :: R') t),
          dotG_comm (wactT U [] u) (wactT U (l :: R') u)]
        refine stepGoT T U d t u hst hsu hdt hdu htopt htopu htie n
          ihn l R' [] ?_ (hb' l (.head _)) (memAll_tail hb')
          memAll_nil
        show R'.length + 1 + ([] : List Nat).length ≤ n
        have h : ([] : List Nat).length + (l :: R').length < n + 1 := hlt
        rw [show ([] : List Nat).length + (l :: R').length
            = R'.length + 1 from Nat.zero_add _] at h
        exact Nat.le_of_lt_succ h

/-- `lem:blockirr`(iv)'s crossing walk over two tables: the
reversed word walks across the transposes, each crossing folding
into a content read at the two letters with a shorter word's
pairing, and a raising's read at a top is the sum's unit — the
walk's own display at an arbitrary configuration of the outer
word, the reversed word and the crossed prefix. -/
private theorem wordGramWalkT (T U : WalkTable) (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u)
    (hdt : t.content.length = d) (hdu : u.content.length = d)
    (htopt : ∀ j, j + 1 < d → poly.unitTail (T.tr j t).coords)
    (htopu : ∀ j, j + 1 < d → poly.unitTail (U.tr j u).coords)
    (htie : ∀ (ws : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ ws, l + 1 < d) →
      ¬ poly.unitTail (wactT T ws t).coords →
      ¬ poly.unitTail (wactT U ws u).coords →
      ground.getAt 0 (wactT T ws t).content (T.uLet j)
          + ground.getAt 0 (wactT U ws u).content (U.dLet j)
        = ground.getAt 0 (wactT U ws u).content (U.uLet j)
          + ground.getAt 0 (wactT T ws t).content (T.dLet j)) :
    ∀ (B A C : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ A, l + 1 < d) → (∀ l ∈ B, l + 1 < d) →
      (∀ l ∈ C, l + 1 < d) →
      (dotG (wactT T A t) (wactT T C (T.tr j (wactT T B t)))
          * elim.dotP u.coords u.coords).oneValue
        (dotG (wactT U A u) (wactT U C (U.tr j (wactT U B u)))
          * elim.dotP t.coords t.coords) :=
  fun B A C j hjd hA hB hC =>
    walkGoT T U d t u hst hsu hdt hdu htopt htopu htie
      (A.length + 1 + C.length + B.length)
      (fun a b _ hba hbb =>
        wordGramT T U d t u hst hsu hdt hdu htopt htopu htie
          a b hba hbb)
      B A C j rfl hjd hA hB hC

/-- The walk's step at a leading letter: a word led by one letter
pairs a second word's image at the first top exactly as it does at
the second, the leading letter crossing the pairing as its
table's transpose. -/
theorem wordGramStepT (T U : WalkTable) (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u)
    (hdt : t.content.length = d) (hdu : u.content.length = d)
    (htopt : ∀ j, j + 1 < d → poly.unitTail (T.tr j t).coords)
    (htopu : ∀ j, j + 1 < d → poly.unitTail (U.tr j u).coords)
    (htie : ∀ (ws : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ ws, l + 1 < d) →
      ¬ poly.unitTail (wactT T ws t).coords →
      ¬ poly.unitTail (wactT U ws u).coords →
      ground.getAt 0 (wactT T ws t).content (T.uLet j)
          + ground.getAt 0 (wactT U ws u).content (U.dLet j)
        = ground.getAt 0 (wactT U ws u).content (U.uLet j)
          + ground.getAt 0 (wactT T ws t).content (T.dLet j))
    (j : Nat) (A ws' : List Nat) (hjd : j + 1 < d)
    (hA : ∀ l ∈ A, l + 1 < d) (hw' : ∀ l ∈ ws', l + 1 < d) :
    (dotG (wactT T (j :: A) t) (wactT T ws' t)
        * elim.dotP u.coords u.coords).oneValue
      (dotG (wactT U (j :: A) u) (wactT U ws' u)
        * elim.dotP t.coords t.coords) :=
  stepT_of_walk T U t u j A ws'
    (wactT_sized T A t hst) (wactT_sized T ws' t hst)
    (by rw [wactT_content T A t, wcontentT_len, hdt]; exact hjd)
    (wactT_sized U A u hsu) (wactT_sized U ws' u hsu)
    (by rw [wactT_content U A u, wcontentT_len, hdu]; exact hjd)
    (wordGramWalkT T U d t u hst hsu hdt hdu htopt htopu htie
      ws' A [] j hjd hA hw' memAll_nil)

/-! The matrix units' own table and the lowering words read on it:
each letter the adjacent lowering `act (j + 1) j` with the adjacent
raising `act j (j + 1)` its transpose, the laws `con:units`' own
reads at that pair. -/

/-- `con:units`' table at the adjacent letters, the lowering the
step and the raising its transpose. -/
def lowerTable : WalkTable where
  dLet := fun j => j
  uLet := fun j => j + 1
  step := fun j v => act (j + 1) j v
  tr := fun j v => act j (j + 1) v
  letters := fun _ => Or.inl ⟨rfl, rfl⟩
  step_content := fun _ _ => rfl
  tr_content := fun _ _ => rfl
  step_sized := fun j v => act_sized (j + 1) j v
  tr_sized := fun j v => act_sized j (j + 1) v
  step_congr := fun j v w hc hq =>
    (act_congr (j + 1) j v w hc hq).2.2
  step_vecAdd := fun _ _ x y hxy =>
    elim.matVec_vecAdd_free _ x y hxy
  step_vecScale := fun _ _ c x =>
    elim.matVec_vecScale_free _ c x
  tr_congr := fun j v w hc hq =>
    (act_congr j (j + 1) v w hc hq).2.2
  tr_vecAdd := fun _ _ x y hxy =>
    elim.matVec_vecAdd_free _ x y hxy
  tr_vecScale := fun _ _ c x =>
    elim.matVec_vecScale_free _ c x
  step_unitTail := fun _ _ h => elim.matVec_null _ _ h
  tr_unitTail := fun _ _ h => elim.matVec_null _ _ h
  step_vac := fun j v h =>
    units.matVec_null_unocc _ _ (j + 1) j h v.coords
  tr_vac := fun j v h =>
    units.matVec_null_unocc _ _ j (j + 1) h v.coords
  adjoint := fun j v z hsv hsz hj hD hZ =>
    act_adjoint v z (j + 1) j hsv hsz hj (Nat.lt_of_succ_lt hj)
      (Nat.succ_ne_self j) hD hZ
  cross_occ := fun j v hsv hj hD hU => pair_coords v j hsv hj hD hU
  cross_vacU := fun j v hsv hj hD hU0 =>
    pair_coords_vacU v j hsv hj hD hU0
  cross_vacD := fun j v hsv hj hD0 hU =>
    pair_coords_vacD v j hsv hj hD0 hU
  comm := fun l j v hlj hsv hl hj => swap_coords v l j hlj hsv hl hj

/-- The lowering words' action: `lowerTable`'s word action — each
letter the adjacent lowering `act (j + 1) j`, folded from the
word's tail. -/
def wact : List Nat → HVec → HVec := wactT lowerTable

/-- The word's content chain at the matrix units, `lowerTable`'s
own. -/
def wcontent : List Nat → List Nat → List Nat := wcontentT lowerTable

/-- A word's image reads its content at the chain. -/
theorem wact_content : ∀ (ws : List Nat) (v : HVec),
    (wact ws v).content = wcontent ws v.content :=
  wactT_content lowerTable

/-- A word's image keeps the width at its own content's
enumeration. -/
theorem wact_sized : ∀ (ws : List Nat) (v : HVec),
    sized v → sized (wact ws v) := wactT_sized lowerTable

private theorem wcontent_len : ∀ (ws mu' : List Nat),
    (wcontent ws mu').length = mu'.length := wcontentT_len lowerTable

/-- Two tops of one content give `lowerTable`'s crossing tie: the
two words' images share their content, so the two cross-added
scalar sums read the same two entries. -/
private theorem lowerTie (t u : HVec) (d : Nat)
    (hcu : t.content = u.content) :
    ∀ (ws : List Nat) (j : Nat), j + 1 < d →
      (∀ l ∈ ws, l + 1 < d) →
      ¬ poly.unitTail (wactT lowerTable ws t).coords →
      ¬ poly.unitTail (wactT lowerTable ws u).coords →
      ground.getAt 0 (wactT lowerTable ws t).content
          (lowerTable.uLet j)
          + ground.getAt 0 (wactT lowerTable ws u).content
            (lowerTable.dLet j)
        = ground.getAt 0 (wactT lowerTable ws u).content
            (lowerTable.uLet j)
          + ground.getAt 0 (wactT lowerTable ws t).content
            (lowerTable.dLet j) := by
  intro ws _ _ _ _ _
  rw [wactT_content lowerTable ws t, wactT_content lowerTable ws u,
    hcu]

/-- The words' pairings read the top's content alone
(`lem:blockirr`(iv)'s word-pair clause): at two tops of one
content, any two lowering words at one moved content pair at the
first top against the second's self-pairing exactly as they pair
at the second against the first's, one value per word pair — the
reversed word walks across the transposes, each crossing folding
into a content read with a shorter word's pairing, and a raising's
read at the top is the sum's unit.  The shared content, the two
top hypotheses, the sized binders and the one-moved-content binder
are load-bearing with their refusals committed; the letter bounds
and the width binder are `con:units`' index frame. -/
theorem wordGram : ∀ (d : Nat) (t u : HVec),
    sized t → sized u → t.content.length = d →
    t.content = u.content →
    (∀ j, j < d → ∀ i, i < j → poly.unitTail (act i j t).coords) →
    (∀ j, j < d → ∀ i, i < j → poly.unitTail (act i j u).coords) →
    ∀ ws ws' : List Nat,
    (∀ j ∈ ws, j + 1 < d) → (∀ j ∈ ws', j + 1 < d) →
    (wact ws t).content = (wact ws' t).content →
    (elim.dotP (wact ws t).coords (wact ws' t).coords
        * elim.dotP u.coords u.coords).oneValue
      (elim.dotP (wact ws u).coords (wact ws' u).coords
        * elim.dotP t.coords t.coords) := by
  intro d t u hst hsu hdt hcu htopt htopu ws ws' hb hb' hm
  have hmU : (wact ws u).content = (wact ws' u).content := by
    rw [wact_content ws u, wact_content ws' u, ← hcu,
      ← wact_content ws t, ← wact_content ws' t]
    exact hm
  rw [← dotG_read (wact ws t) (wact ws' t) hm,
    ← dotG_read (wact ws u) (wact ws' u) hmU]
  exact wordGramT lowerTable lowerTable d t u hst hsu hdt
    (by rw [← hcu]; exact hdt)
    (fun j hjd => htopt (j + 1) hjd j (Nat.lt_succ_self j))
    (fun j hjd => htopu (j + 1) hjd j (Nat.lt_succ_self j))
    (lowerTie t u d hcu) ws ws' hb hb'

/-! The raised word pairings (`lem:blockcount`(iii)'s transport
sentence at `lem:blockirr`(iv)'s walk): the walk nowhere restricts
to lowering words, so one leading raising per side reads through
the same crossing device — the raising's transpose partner is the
adjacent lowering, and `wordGram` closes at the extended word. -/

/-- The word pairings at one leading raising
(`lem:blockcount`(iii)'s transport sentence, the fold read against
its top's self-pairing, at `lem:blockirr`(iv)'s walk): at two tops
of one content, a raising over a lowering word pairs a second
word's image at the first top against the second top's
self-pairing exactly as it pairs at the second top against the
first's, one value per word pair — the raising crosses the
pairing as the adjacent lowering, so the display is `wordGram`'s
at the word extended by that letter.  The top, sized, width and
shared-content binders are `wordGram`'s own frame with its
committed refusals; the letter bounds are `con:units`' index
frame; the moved-content binder mirrors `wordGram`'s own — the
pairings are read at matched contents. -/
theorem wordGramRaise : ∀ (d : Nat) (t u : HVec),
    sized t → sized u → t.content.length = d →
    t.content = u.content →
    (∀ j, j < d → ∀ i, i < j → poly.unitTail (act i j t).coords) →
    (∀ j, j < d → ∀ i, i < j → poly.unitTail (act i j u).coords) →
    ∀ ws ws' : List Nat,
    (∀ j ∈ ws, j + 1 < d) → (∀ j ∈ ws', j + 1 < d) →
    ∀ i, i + 1 < d →
    (act i (i + 1) (wact ws t)).content = (wact ws' t).content →
    (elim.dotP (act i (i + 1) (wact ws t)).coords
        (wact ws' t).coords
        * elim.dotP u.coords u.coords).oneValue
      (elim.dotP (act i (i + 1) (wact ws u)).coords
        (wact ws' u).coords
        * elim.dotP t.coords t.coords) := by
  intro d t u hst hsu hdt hcu htopt htopu ws ws' hb hb' i hid hmatch
  have hmU : (act i (i + 1) (wact ws u)).content
      = (wact ws' u).content := by
    show moveAt i (i + 1) (wact ws u).content = (wact ws' u).content
    rw [wact_content ws u, wact_content ws' u, ← hcu,
      ← wact_content ws t, ← wact_content ws' t]
    exact hmatch
  rw [elim.dotP_comm (act i (i + 1) (wact ws t)).coords
      (wact ws' t).coords,
    elim.dotP_comm (act i (i + 1) (wact ws u)).coords
      (wact ws' u).coords,
    ← dotG_read (wact ws' t) (act i (i + 1) (wact ws t)) hmatch.symm,
    ← dotG_read (wact ws' u) (act i (i + 1) (wact ws u)) hmU.symm]
  exact wordGramWalkT lowerTable lowerTable d t u hst hsu hdt
    (by rw [← hcu]; exact hdt)
    (fun j hjd => htopt (j + 1) hjd j (Nat.lt_succ_self j))
    (fun j hjd => htopu (j + 1) hjd j (Nat.lt_succ_self j))
    (lowerTie t u d hcu) ws ws' [] i hid hb' hb memAll_nil

/-- The word pairings at one leading raising per side
(`lem:blockcount`(iii)'s transport sentence at
`lem:blockirr`(iv)'s walk): at two tops of one content, two
lowering words raised by one adjacent letter each pair at the
first top against the second's self-pairing exactly as they pair
at the second against the first's, one value per word pair — one
side's raising crosses the pairing as the adjacent lowering, and
the crossing it leaves is the walk's own, folded into a content
read with a shorter word's pairing.  The top, sized, width and
shared-content binders are `wordGram`'s own frame with its
committed refusals; the letter bounds are `con:units`' index
frame; the moved-content binder mirrors `wordGram`'s own — the
pairings are read at matched contents. -/
theorem wordGramRaise2 : ∀ (d : Nat) (t u : HVec),
    sized t → sized u → t.content.length = d →
    t.content = u.content →
    (∀ j, j < d → ∀ i, i < j → poly.unitTail (act i j t).coords) →
    (∀ j, j < d → ∀ i, i < j → poly.unitTail (act i j u).coords) →
    ∀ ws ws' : List Nat,
    (∀ j ∈ ws, j + 1 < d) → (∀ j ∈ ws', j + 1 < d) →
    ∀ i, i + 1 < d →
    (act i (i + 1) (wact ws t)).content
      = (act i (i + 1) (wact ws' t)).content →
    (elim.dotP (act i (i + 1) (wact ws t)).coords
        (act i (i + 1) (wact ws' t)).coords
        * elim.dotP u.coords u.coords).oneValue
      (elim.dotP (act i (i + 1) (wact ws u)).coords
        (act i (i + 1) (wact ws' u)).coords
        * elim.dotP t.coords t.coords) := by
  intro d t u hst hsu hdt hcu htopt htopu ws ws' hb hb' i hid hmatch
  have hmU : (act i (i + 1) (wact ws u)).content
      = (act i (i + 1) (wact ws' u)).content := by
    show moveAt i (i + 1) (wact ws u).content
      = moveAt i (i + 1) (wact ws' u).content
    rw [wact_content ws u, wact_content ws' u, ← hcu,
      ← wact_content ws t, ← wact_content ws' t]
    exact hmatch
  have hlenW' : (wact ws' t).content.length = d := by
    rw [wact_content, wcontent_len, hdt]
  have hlenW'u : (wact ws' u).content.length = d := by
    rw [wact_content, wcontent_len, ← hcu, hdt]
  rw [← dotG_read (act i (i + 1) (wact ws t))
      (act i (i + 1) (wact ws' t)) hmatch,
    ← dotG_read (act i (i + 1) (wact ws u))
      (act i (i + 1) (wact ws' u)) hmU]
  refine BPair.oneValue_trans (BPair.mul_congr
    (dotG_tr_step lowerTable i (wact ws t)
      (act i (i + 1) (wact ws' t))
      (wact_sized ws t hst) (act_sized i (i + 1) (wact ws' t))
      (by show i + 1 < (moveAt i (i + 1) (wact ws' t).content).length
          rw [length_moveAt, hlenW']
          exact hid))
    (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (wordGramWalkT lowerTable lowerTable d t u hst hsu hdt
      (by rw [← hcu]; exact hdt)
      (fun j hjd => htopt (j + 1) hjd j (Nat.lt_succ_self j))
      (fun j hjd => htopu (j + 1) hjd j (Nat.lt_succ_self j))
      (lowerTie t u d hcu) ws' ws [i] i hid hb hb'
      (memAll_cons hid memAll_nil)) ?_
  exact BPair.oneValue_symm (BPair.mul_congr
    (dotG_tr_step lowerTable i (wact ws u)
      (act i (i + 1) (wact ws' u))
      (wact_sized ws u hsu) (act_sized i (i + 1) (wact ws' u))
      (by show i + 1 < (moveAt i (i + 1) (wact ws' u).content).length
          rw [length_moveAt, hlenW'u]
          exact hid))
    (BPair.oneValue_refl _))

/-! The seed tier: the closure's stated data at a general top seed
— `blockSpan`'s semantics and provenance at the exhibit seeds read
again at a stated member, the exhaustion tier's engine. -/

/-- The closure's stated data at a seed: sized members at the
letter width, the group independence, and the interior closure,
`blockSpan_sem`'s reads at the seed's own pool. -/
theorem seedSpan_sem (d fuel : Nat) (meas : List Nat → Nat)
    (w : HVec)
    (hnomove : ∀ v : HVec, v.content.length = d →
      meas v.content = 0 → ∀ j : Nat, j < d - 1 →
      lowerH j v = none)
    (hdrop : ∀ (j : Nat) (v x : HVec), j < d - 1 →
      lowerH j v = some x → v.content.length = d →
      meas x.content + 1 = meas v.content)
    (hsz : sized w) (hwd : w.content.length = d)
    (hoff : ¬ poly.unitTail w.coords)
    (hfuel : meas w.content ≤ fuel) :
    (∀ v ∈ closeSpan d fuel [w] [w], sized v)
      ∧ (∀ v ∈ closeSpan d fuel [w] [w], v.content.length = d)
      ∧ indepAll (closeSpan d fuel [w] [w])
      ∧ closedAt (closeSpan d fuel [w] [w]) d := by
  have hKkeep : ∀ (j : Nat) (v x : HVec), lowerH j v = some x →
      v.content.length = d → x.content.length = d := by
    intro j v x heq hv
    rw [(lowerH_fields heq).1, units.length_moveDn j v.content]
    exact hv
  have hindseed : indepAll [w] := indep_seed w hsz hoff
  match closeSpan_sem d meas
      (fun v => v.content.length = d) hKkeep hnomove hdrop
      fuel [] [w]
      (memAll_cons hsz memAll_nil)
      (memAll_cons hwd memAll_nil) hindseed memAll_nil
      (memAll_cons hfuel memAll_nil) with
  | ⟨ext, heq, hs, hk, hind, hclosed⟩ =>
    rw [show (([] : List HVec) ++ [w]) = [w] from rfl]
      at heq hs hk hind hclosed
    refine ⟨?_, ?_, ?_, hclosed⟩
    · rw [heq]
      exact hs
    · rw [heq]
      exact hk
    · rw [heq]
      exact hind

/-- The closure's indexed provenance at a seed: the head equation
with every later member an occupied interior lowering of a member
listed at or before its predecessor, `blockSpan_prov`'s read at
the seed's own pool. -/
theorem seedSpan_prov (d fuel : Nat) (w : HVec) : ∃ tail,
    closeSpan d fuel [w] [w] = w :: tail
      ∧ ∀ k, k < tail.length →
        ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
          lowerH j (getAt (⟨[], []⟩ : HVec) (w :: tail) i)
            = some (getAt (⟨[], []⟩ : HVec) tail k) := by
  have hseed : provAt d [w] := by
    intro m hm0 hm1
    exact absurd (Nat.lt_of_lt_of_le hm0 (Nat.le_of_lt_succ hm1))
      (Nat.lt_irrefl 0)
  match closeSpan_prov d fuel [w] [w] (fun _ hv => hv) hseed with
  | ⟨t, ht, hpt⟩ =>
    refine ⟨t, ht, ?_⟩
    intro k hk
    have hkl : k + 1 < ([w] ++ t).length :=
      Nat.succ_lt_succ hk
    match hpt (k + 1) (Nat.succ_pos k) hkl with
    | ⟨i, him, j, hj, hlow⟩ =>
      exact ⟨i, Nat.le_of_lt_succ him, j, hj, hlow⟩

/-- The provenance induction at a stated pool: a read holding at
the head and kept by the occupied interior lowerings holds at
every member. -/
private theorem provAllGo (d : Nat) (v : HVec) (tailv : List HVec)
    (Q : HVec → Prop)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hbase : Q v)
    (hstep : ∀ x w (j : Nat), j + 1 < d → Q x →
      lowerH j x = some w → Q w) :
    ∀ (b k : Nat), k ≤ b → k < (v :: tailv).length →
      Q (getAt (⟨[], []⟩ : HVec) (v :: tailv) k)
  | _, 0, _, _ => hbase
  | 0, k + 1, hkb, _ => absurd hkb (Nat.not_succ_le_zero k)
  | b + 1, k + 1, hkb, hk =>
    match hprov k (Nat.lt_of_succ_lt_succ hk) with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      hstep _ _ j hjd
        (provAllGo d v tailv Q hprov hbase hstep b i
          (Nat.le_trans hik (Nat.le_of_succ_le_succ hkb))
          (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hik)
            (Nat.le_of_lt hk)))
        hlow

/-- The provenance induction's member read. -/
theorem prov_all (d : Nat) (v : HVec) (tailv : List HVec)
    (Q : HVec → Prop)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hbase : Q v)
    (hstep : ∀ x w (j : Nat), j + 1 < d → Q x →
      lowerH j x = some w → Q w) :
    ∀ x ∈ v :: tailv, Q x := by
  intro x hx
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) hx with
  | ⟨p, hp, hpe⟩ =>
    rw [← hpe]
    exact provAllGo d v tailv Q hprov hbase hstep p p
      (Nat.le_refl p) hp

/-- The closure at every distinct letter pair, at a stated pool's
provenance, closure, and head top: `lem:lowerspan`'s invariance
read at the pool's own data, `act_closed`'s seed-general twin. -/
theorem pool_act_closed (d : Nat) (v : HVec) (tailv : List HVec)
    (hall : ∀ x ∈ v :: tailv, sized x)
    (hwid : ∀ x ∈ v :: tailv, x.content.length = d)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hcl : closedAt (v :: tailv) d)
    (htop : ∀ jr, jr + 1 < d →
      poly.unitTail (act jr (jr + 1) v).coords)
    (i j : Nat) (hi : i < d) (hj : j < d) (hij : ¬ i = j) :
    ∀ x ∈ v :: tailv, settledAt (v :: tailv) (act i j x) := by
  have hallQ : ∀ x ∈ v :: tailv,
      x.content.length = d ∧ sized x
        ∧ settledAt (v :: tailv) x
        ∧ ∀ jr, jr + 1 < d →
            settledAt (v :: tailv) (act jr (jr + 1) x) := by
    refine prov_all d v tailv _ hprov
      ⟨hwid v (List.Mem.head tailv), hall v (List.Mem.head tailv),
        member_settled (v :: tailv) hall v
          (List.Mem.head tailv),
        fun jr hjr =>
          Or.inl (allU_of_unitTail _ (htop jr hjr))⟩ ?_
    intro x w jd hjd hq hlw
    have hocc : 0 < ground.getAt 0 x.content jd := by
      by_cases hg : 0 < ground.getAt 0 x.content jd
      · exact hg
      · rw [show lowerH jd x = none from if_neg hg] at hlw
        exact nomatch hlw
    have hfields := lowerH_fields hlw
    have hw : w = act (jd + 1) jd x := by
      refine hvec_eq ?_ ?_
      · show w.content = moveAt (jd + 1) jd x.content
        rw [moveAt_moveDn jd x.content]
        exact hfields.1
      · show w.coords = elim.matVec (units.matUnitAt
          (moveAt (jd + 1) jd x.content) x.content (jd + 1) jd)
          x.coords
        rw [hfields.2]
        show elim.matVec (units.matUnitAt
            (units.moveDn jd x.content) x.content (jd + 1) jd)
            x.coords
          = elim.matVec (units.matUnitAt
            (moveAt (jd + 1) jd x.content) x.content (jd + 1) jd)
            x.coords
        rw [moveAt_moveDn jd x.content]
    rw [hw]
    refine ⟨?_, act_sized (jd + 1) jd x, ?_, ?_⟩
    · show (moveAt (jd + 1) jd x.content).length = d
      rw [length_moveAt]
      exact hq.1
    · refine settled_of_span (v :: tailv) _
        (act_sized (jd + 1) jd x) ?_
      exact act_transport (v :: tailv) (jd + 1) jd hall
        (lower_imgs (v :: tailv) d jd hcl hall hjd) x.content
        x.coords hq.2.1
        (span_of_settled (v :: tailv) x hall hq.2.1 hq.2.2.1)
    · intro jr hjr
      by_cases hje : jr = jd
      · rw [hje]
        exact raise_pair (v :: tailv) d jd hall hcl hjd x
          hq.1 hq.2.1 hq.2.2.1 (by rw [← hje]; exact hq.2.2.2 jr hjr)
          hocc
      · exact raise_cross (v :: tailv) d jr jd hall hcl hjd
          hjr hje x hq.1 hq.2.1 (hq.2.2.2 jr hjr)
  match Nat.lt_or_ge i j with
  | .inl hlt =>
    match gap_of_lt j i hlt with
    | ⟨g, hg⟩ =>
      exact act_gap (v :: tailv) d hall hwid
        (fun jr hjr x hx => (hallQ x hx).2.2.2 jr hjr)
        (fun jr hjr =>
          lower_imgs (v :: tailv) d jr hcl hall hjr)
        g i j hi hj (Or.inl hg)
  | .inr hge =>
    match gap_of_lt i j
        (Nat.lt_of_le_of_ne hge (fun he => hij he.symm)) with
    | ⟨g, hg⟩ =>
      exact act_gap (v :: tailv) d hall hwid
        (fun jr hjr x hx => (hallQ x hx).2.2.2 jr hjr)
        (fun jr hjr =>
          lower_imgs (v :: tailv) d jr hcl hall hjr)
        g i j hi hj (Or.inr hg)

/-! The Cartan floor (`lem:blockcount`(iii)'s closing sentence):
the two column exhibits' tensor is a top off the sum's unit at the
column union's content, its pair heads the display's pair list, and
the coefficient family carrying the natural one at that head and
the sum's unit past it sits in the kernel list's span — so the
kernel list is occupied and the fusion count is at least one. -/

private theorem raiseNull_stacked (z : HVec) (hsz : sized z)
    (hr : ∀ j, j + 1 < z.content.length → raiseNull j z) :
    poly.unitTail (elim.matVec (units.stackedRaise z.content)
      z.coords) := by
  refine units.stackedRaise_of _ _ ?_
  intro i hi _
  exact raiseNull_top z i hsz hi (hr i hi)

private theorem tensor_exhibit_stacked (a b : Shape)
    (hba : b.length = a.length) :
    poly.unitTail (elim.matVec
      (units.stackedRaise
        (tensorH (exhibit a) (exhibit b)).content)
      (tensorH (exhibit a) (exhibit b)).coords) := by
  have hca : (exhibit a).content = rowList a := content_exhibit a
  have hcb : (exhibit b).content = rowList b := content_exhibit b
  have hal : (exhibit a).content.length = a.length := by
    rw [hca, places.length_rowList]
  have hbl : (exhibit b).content.length = a.length := by
    rw [hcb, places.length_rowList, hba]
  have hlen : (exhibit a).content.length
      = (exhibit b).content.length := by
    rw [hal, hbl]
  have hTl : (tensorH (exhibit a) (exhibit b)).content.length
      = a.length := by
    show (List.zipWith (fun x y => x + y) (exhibit a).content
      (exhibit b).content).length = a.length
    exact ground.length_zipWith (fun x y => x + y) (exhibit a).content (exhibit b).content
      a.length hal hbl
  refine raiseNull_stacked (tensorH (exhibit a) (exhibit b))
    (tensorH_sized (exhibit a) (exhibit b)) ?_
  intro j hj
  rw [hTl] at hj
  exact tensor_raiseNull j (exhibit a) (exhibit b) hlen
    (exhibit_sized a) (exhibit_sized b)
    (exhibit_raiseNull a j hj)
    (exhibit_raiseNull b j (by rw [hba]; exact hj))

private theorem pairsAt_head (v w : HVec) (A B : List HVec)
    (cc : List Nat)
    (hg : List.zipWith (fun x y => x + y) v.content w.content
      = cc) :
    ∃ rest, pairsAt (v :: A) (w :: B) cc = tensorH v w :: rest := by
  refine ⟨B.flatMap (fun w' =>
      if List.zipWith (fun x y => x + y) v.content w'.content = cc
        then [tensorH v w'] else [])
    ++ pairsAt A (w :: B) cc, ?_⟩
  show ((if List.zipWith (fun x y => x + y) v.content w.content
        = cc then [tensorH v w] else [])
      ++ B.flatMap (fun w' =>
        if List.zipWith (fun x y => x + y) v.content w'.content
          = cc then [tensorH v w'] else []))
    ++ pairsAt A (w :: B) cc = _
  rw [if_pos hg]
  rfl

private theorem dotN_replicate_unit : ∀ (r : List BPair) (k : Nat),
    elim.dotN r (List.replicate k BPair.unit) = BPair.unit
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | c :: t, k + 1 => by
    show (if (c.isUnitRep || BPair.unit.isUnitRep) = true then
        elim.dotN t (List.replicate k BPair.unit)
      else (c * BPair.unit
        + elim.dotN t (List.replicate k BPair.unit)).norm)
      = BPair.unit
    rw [if_pos (show (c.isUnitRep || BPair.unit.isUnitRep) = true
      from by cases c.isUnitRep <;> rfl)]
    exact dotN_replicate_unit t k

private theorem dotN_head_unit (c : BPair) (t : List BPair)
    (k : Nat) (hc : c.oneValue BPair.unit) :
    (elim.dotN (c :: t)
      (BPair.ofNat 1 :: List.replicate k BPair.unit)).oneValue
      BPair.unit := by
  show (if (c.isUnitRep || (BPair.ofNat 1).isUnitRep) = true then
      elim.dotN t (List.replicate k BPair.unit)
    else (c * BPair.ofNat 1
      + elim.dotN t (List.replicate k BPair.unit)).norm).oneValue
    BPair.unit
  by_cases hb : (c.isUnitRep || (BPair.ofNat 1).isUnitRep) = true
  · rw [if_pos hb, dotN_replicate_unit t k]
    exact BPair.oneValue_refl _
  · rw [if_neg hb, dotN_replicate_unit t k]
    exact BPair.oneValue_trans
      (BPair.norm_oneValue (c * BPair.ofNat 1 + BPair.unit))
      (BPair.oneValue_trans (BPair.add_unit (c * BPair.ofNat 1))
        (BPair.oneValue_trans (BPair.mul_ofNat_one c) hc))

private theorem crossM_head_null (R : elim.Mat) (h : List BPair)
    (L : elim.Mat)
    (hnull : poly.unitTail (elim.matVec R h)) :
    poly.unitTail (elim.matVec (elim.crossM R (h :: L))
      (BPair.ofNat 1 :: List.replicate L.length BPair.unit)) := by
  refine elim.unitTail_of_getAt _ ?_
  intro p hp
  rw [elim.matVec_length, elim.length_crossM] at hp
  have hrow : ground.getAt ([] : List BPair)
      (elim.crossM R (h :: L)) p
      = (h :: L).map (fun x => elim.dotN
        (ground.getAt ([] : List BPair) R p) x) :=
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => (h :: L).map (fun x => elim.dotN r x)) R p hp
  have hentry : (elim.dotN (ground.getAt ([] : List BPair) R p)
      h).oneValue BPair.unit := by
    have hg : ground.getAt BPair.unit (elim.matVec R h) p
        = elim.dotN (ground.getAt ([] : List BPair) R p) h :=
      ground.getAt_map ([] : List BPair) BPair.unit
        (fun r => elim.dotN r h) R p hp
    rw [← hg]
    exact poly.getAt_unitTail hnull p
  have hgv : ground.getAt BPair.unit
      (elim.matVec (elim.crossM R (h :: L))
        (BPair.ofNat 1
          :: List.replicate L.length BPair.unit)) p
      = elim.dotN (ground.getAt ([] : List BPair)
          (elim.crossM R (h :: L)) p)
        (BPair.ofNat 1
          :: List.replicate L.length BPair.unit) :=
    ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => elim.dotN r (BPair.ofNat 1
        :: List.replicate L.length BPair.unit))
      (elim.crossM R (h :: L)) p
      (by rw [elim.length_crossM]; exact hp)
  rw [hgv, hrow]
  exact dotN_head_unit _ _ L.length hentry

/-! `lem:blockcount`(iii)'s collecting read (`con:places`'
collecting sentence, a tensor of two combinations collecting to the
pairs at the coefficients' products): a member of each block's
content span tensors into the fused pool's own span at the summed
content.  The two clearings multiply — an off-unit product of
off-unit factors — and the double combination walks out one factor
at a time through the tensor's additivity and scale-equivariance in
each factor, the pairs of rows landing as members of the fused
pool's content group. -/

/-- The fused pool's members are the two lists' tensors outright
(`lem:blockcount`(iii)'s fused carrier). -/
theorem fusedAt_mem : ∀ (A B : List HVec) (u : HVec),
    u ∈ fusedAt A B → ∃ a y, a ∈ A ∧ y ∈ B ∧ tensorH a y = u
  | [], _, _, hu => nomatch (hu : _ ∈ ([] : List HVec))
  | v :: A, B, u, hu => by
    match ground.mem_append_of (B.map (tensorH v)) (fusedAt A B)
        hu with
    | .inl hl =>
      match ground.mem_map_of (tensorH v) B u hl with
      | ⟨w, hw, he⟩ =>
        exact ⟨v, w, List.Mem.head A, hw, he⟩
    | .inr hr =>
      match fusedAt_mem A B u hr with
      | ⟨a, y, ha, hy, he⟩ =>
        exact ⟨a, y, List.Mem.tail v ha, hy, he⟩

/-- The fused pool's members are sized, the tensor's own read. -/
theorem fusedAt_sized (A B : List HVec) (u : HVec)
    (hu : u ∈ fusedAt A B) : sized u :=
  match fusedAt_mem A B u hu with
  | ⟨a, y, _, _, he⟩ => by
    rw [← he]
    exact tensorH_sized a y

/-- The fused pool's members read the stated width, the two
factors' column union (`con:places`' one letter width). -/
theorem fusedAt_width (d : Nat) (A B : List HVec)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d) :
    ∀ u ∈ fusedAt A B, u.content.length = d := by
  intro u hu
  match fusedAt_mem A B u hu with
  | ⟨a, y, ha, hy, he⟩ =>
    rw [← he]
    exact ground.length_zipWith (fun x y => x + y) a.content y.content d (hwidA a ha)
      (hwidB y hy)

/-- The fused pool's count is the two lists' counts' product, one
tensor per pair (`lem:blockcount`(iii)'s fused carrier). -/
theorem length_fusedAt (B : List HVec) :
    ∀ A : List HVec, (fusedAt A B).length = A.length * B.length
  | [] => (Nat.zero_mul B.length).symm
  | v :: A => by
    show (B.map (tensorH v) ++ fusedAt A B).length
      = (A.length + 1) * B.length
    rw [ground.length_append, ground.length_map,
      length_fusedAt B A, Nat.succ_mul,
      Nat.add_comm (A.length * B.length) B.length]

/-- The fused pool's members read one degree, the two factors'
degrees' sum — the column union's box total
(`lem:blockcount`(iii)'s one-degree read at the fused
carrier). -/
theorem fusedAt_degree (d kA kB : Nat) (A B : List HVec)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hdegB : ∀ w ∈ B, sumNat w.content = kB) :
    ∀ u ∈ fusedAt A B, sumNat u.content = kA + kB := by
  intro u hu
  match fusedAt_mem A B u hu with
  | ⟨a, y, ha, hy, he⟩ =>
    rw [← he]
    show sumNat (List.zipWith (fun x y => x + y) a.content
      y.content) = kA + kB
    rw [sumNat_zipWith_add a.content y.content
        (by rw [hwidA a ha, hwidB y hy]),
      hdegA a ha, hdegB y hy]

/-- The fused pool's content groups are independent
(`lem:blockcount`(iii)): the group at a content is the stated pair
list's coordinate family (`groupAt_fused`), independent at the two
lists' own independence (`tensor_indep`). -/
theorem fused_indepAll (d kA : Nat) (A B : List HVec)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hiA : indepAll A) (hiB : indepAll B) :
    indepAll (fusedAt A B) := by
  intro mu _
  show elim.indepRows (places.monomialsAt mu).length
    (groupAt (fusedAt A B) mu)
  rw [groupAt_fused A B mu]
  exact tensor_indep A B mu d kA hwidA hwidB hdegA hiA hiB

/-! The fused carrier's composition, `con:places`' composition
sentence at `lem:blockcount`(iii)'s "the composition associative at
the arrangements' join": three factors at one width give one pool
in either grouping, on the nose — the coordinate families are
canonical representatives place by place, so the tensor's own
regrouping read (`tensorH_assoc`) closes at a list equality. -/

/-- The canonical representative is its own: the representative
reads one value with its datum (`BPair.norm_oneValue`) and the
representative is a function of the value alone
(`BPair.norm_congr`). -/
private theorem map_norm_norm : ∀ l : List BPair,
    (l.map BPair.norm).map BPair.norm = l.map BPair.norm
  | [] => rfl
  | a :: t => by
    show (a.norm).norm :: (t.map BPair.norm).map BPair.norm
      = a.norm :: t.map BPair.norm
    rw [BPair.norm_congr (BPair.norm_oneValue a), map_norm_norm t]

/-- Two coordinate families at one width reading one value have
one representative family, place by place. -/
private theorem normMap_eq_of_oneValue : ∀ u v : List BPair,
    u.length = v.length → poly.oneValue u v →
    u.map BPair.norm = v.map BPair.norm
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl
  | a :: u, b :: v, hl, h => by
    show a.norm :: u.map BPair.norm = b.norm :: v.map BPair.norm
    rw [BPair.norm_congr h.1,
      normMap_eq_of_oneValue u v (Nat.succ.inj hl) h.2]

/-- The tensor's coordinates are a representative family, the
scatter fold's own closing map. -/
private theorem tensorH_coords_norm (a b : HVec) :
    ∃ l : List BPair, (tensorH a b).coords = l.map BPair.norm :=
  ⟨_, rfl⟩

/-- The tensor regroups on the nose: three factors at one width
give one carrier in either grouping — the contents agree and the
coordinates read one value (`tensorH_assoc`), both families
representative place by place, so the two carriers are one. -/
theorem tensorH_assoc_eq (u v w : HVec)
    (hsu : sized u) (hsv : sized v) (hsw : sized w)
    (huv : u.content.length = v.content.length)
    (hvw : v.content.length = w.content.length) :
    tensorH (tensorH u v) w = tensorH u (tensorH v w) := by
  obtain ⟨hct, hov⟩ := tensorH_assoc u v w hsu hsv hsw huv hvw
  refine hvec_eq hct ?_
  have hlen : (tensorH (tensorH u v) w).coords.length
      = (tensorH u (tensorH v w)).coords.length := by
    rw [tensorH_sized (tensorH u v) w,
      tensorH_sized u (tensorH v w), hct]
  match tensorH_coords_norm (tensorH u v) w,
      tensorH_coords_norm u (tensorH v w) with
  | ⟨l1, h1⟩, ⟨l2, h2⟩ =>
    have h := normMap_eq_of_oneValue _ _ hlen hov
    rw [h1, h2, map_norm_norm l1, map_norm_norm l2] at h
    rw [h1, h2]
    exact h

/-- The fused pool splits over a joined first list, the flattened
family's own append read. -/
theorem fusedAt_append (C : List HVec) :
    ∀ A B : List HVec,
      fusedAt (A ++ B) C = fusedAt A C ++ fusedAt B C
  | [], _ => rfl
  | v :: A, B => by
    show C.map (tensorH v) ++ fusedAt (A ++ B) C
      = C.map (tensorH v) ++ fusedAt A C ++ fusedAt B C
    rw [fusedAt_append C A B,
      ground.append_assoc (C.map (tensorH v)) (fusedAt A C)
        (fusedAt B C)]

/-- A first factor pulled through the fusion: fusing a
first-factor-tensored list against a third list is the fused pool
tensored by that factor, the regrouping read member by member. -/
private theorem fused_map_left (d : Nat) (v : HVec)
    (hsv : sized v) (hwv : v.content.length = d)
    (C : List HVec) (hszC : ∀ y ∈ C, sized y)
    (hwidC : ∀ y ∈ C, y.content.length = d) :
    ∀ B : List HVec, (∀ w ∈ B, sized w) →
      (∀ w ∈ B, w.content.length = d) →
      fusedAt (B.map (tensorH v)) C = (fusedAt B C).map (tensorH v)
  | [], _, _ => rfl
  | w :: B, hszB, hwidB => by
    have hswB : sized w := hszB w (List.Mem.head B)
    have hwwB : w.content.length = d := hwidB w (List.Mem.head B)
    show C.map (tensorH (tensorH v w))
        ++ fusedAt (B.map (tensorH v)) C
      = (C.map (tensorH w) ++ fusedAt B C).map (tensorH v)
    rw [ground.map_append (tensorH v) (C.map (tensorH w))
        (fusedAt B C),
      ground.map_map (tensorH w) (tensorH v) C,
      fused_map_left d v hsv hwv C hszC hwidC B
        (fun x hx => hszB x (List.Mem.tail w hx))
        (fun x hx => hwidB x (List.Mem.tail w hx)),
      ground.map_congr_members (tensorH (tensorH v w))
        (fun y => tensorH v (tensorH w y)) C
        (fun y hy => tensorH_assoc_eq v w y hsv hswB
          (hszC y (ground.mem_of_countOf_pos y C hy))
          (by rw [hwv, hwwB])
          (by rw [hwwB,
            hwidC y (ground.mem_of_countOf_pos y C hy)]))]

/-- The fused carrier composes associatively at one letter width
(`con:places`' composition; `lem:blockcount`(iii)'s "the
composition associative at the arrangements' join"): the two
groupings are one list on the nose, member for member the tensor's
own regrouping (`tensorH_assoc_eq`).  The width and enumeration
binders are `con:places`' member definition at the three lists. -/
theorem fusedAt_assoc (d : Nat) (B C : List HVec)
    (hszB : ∀ w ∈ B, sized w) (hszC : ∀ y ∈ C, sized y)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hwidC : ∀ y ∈ C, y.content.length = d) :
    ∀ A : List HVec, (∀ v ∈ A, sized v) →
      (∀ v ∈ A, v.content.length = d) →
      fusedAt (fusedAt A B) C = fusedAt A (fusedAt B C)
  | [], _, _ => rfl
  | v :: A, hszA, hwidA => by
    show fusedAt (B.map (tensorH v) ++ fusedAt A B) C
      = (fusedAt B C).map (tensorH v) ++ fusedAt A (fusedAt B C)
    rw [fusedAt_append C (B.map (tensorH v)) (fusedAt A B),
      fused_map_left d v (hszA v (List.Mem.head A))
        (hwidA v (List.Mem.head A)) C hszC hwidC B hszB hwidB,
      fusedAt_assoc d B C hszB hszC hwidB hwidC A
        (fun x hx => hszA x (List.Mem.tail v hx))
        (fun x hx => hwidA x (List.Mem.tail v hx))]

private theorem tensorH_span_right (nu nw : List Nat)
    (hnn : nu.length = nw.length) (M : elim.Mat)
    (hM : elim.rowsLen (monomialsAt
      (List.zipWith (fun p q => p + q) nu nw)).length M)
    (X : List BPair) (hX : X.length = (monomialsAt nu).length) :
    ∀ (ds : List BPair) (K : elim.Mat),
      elim.rowsLen (monomialsAt nw).length K →
      (∀ l, l < K.length →
        elim.spanRel (monomialsAt
            (List.zipWith (fun p q => p + q) nu nw)).length M
          (tensorH ⟨nu, X⟩
            ⟨nw, ground.getAt [] K l⟩).coords) →
      elim.spanRel (monomialsAt
          (List.zipWith (fun p q => p + q) nu nw)).length M
        (tensorH ⟨nu, X⟩
          ⟨nw, elim.combo (monomialsAt nw).length ds K⟩).coords
  | [], _, _, _ => by
    refine elim.spanRel_null _ M _ ?_ hM (tensorH_sized _ _)
    exact (tensorH_unitTail ⟨nu, X⟩
      ⟨nw, List.replicate (monomialsAt nw).length BPair.unit⟩ hX
      (ground.length_replicate BPair.unit _) hnn).mpr
      (Or.inr (poly.unitTail_replicate _))
  | _ :: _, [], _, _ => by
    refine elim.spanRel_null _ M _ ?_ hM (tensorH_sized _ _)
    exact (tensorH_unitTail ⟨nu, X⟩
      ⟨nw, List.replicate (monomialsAt nw).length BPair.unit⟩ hX
      (ground.length_replicate BPair.unit _) hnn).mpr
      (Or.inr (poly.unitTail_replicate _))
  | c :: ds, r :: K, hK, h => by
    have hr : r.length = (monomialsAt nw).length := hK.1
    have hcm : (elim.combo (monomialsAt nw).length ds K).length
        = (monomialsAt nw).length :=
      elim.length_combo _ ds K hK.2
    have hvs : (elim.vecScale c r).length
        = (monomialsAt nw).length := by
      rw [elim.length_vecScale c r, hr]
    have h1 : elim.spanRel (monomialsAt
          (List.zipWith (fun p q => p + q) nu nw)).length M
        (tensorH ⟨nu, X⟩ ⟨nw, elim.vecScale c r⟩).coords := by
      refine elim.spanRel_congr _ M
        (elim.vecScale c (tensorH ⟨nu, X⟩ ⟨nw, r⟩).coords) _
        (poly.oneValue_symm
          (tensorH_vecScaleR ⟨nu, X⟩ nw hX hnn c r hr)) ?_
        (tensorH_sized _ _)
      exact elim.spanRel_scale _ M _ c hM (tensorH_sized _ _)
        (h 0 (Nat.succ_pos _))
    have h2 := tensorH_span_right nu nw hnn M hM X hX ds K hK.2
      (fun l hl => h (l + 1) (Nat.succ_lt_succ hl))
    refine elim.spanRel_congr _ M
      (elim.vecAdd (tensorH ⟨nu, X⟩
          ⟨nw, elim.vecScale c r⟩).coords
        (tensorH ⟨nu, X⟩
          ⟨nw, elim.combo (monomialsAt nw).length ds K⟩).coords) _
      (poly.oneValue_symm (tensorH_vecAddR ⟨nu, X⟩ nw hX hnn _ _
        hvs hcm)) ?_ (tensorH_sized _ _)
    exact elim.spanRel_add _ M _ _ hM (tensorH_sized _ _)
      (tensorH_sized _ _) h1 h2

private theorem tensorH_span_left (nu nw : List Nat)
    (hnn : nu.length = nw.length) (M : elim.Mat)
    (hM : elim.rowsLen (monomialsAt
      (List.zipWith (fun p q => p + q) nu nw)).length M)
    (Y : List BPair) (hY : Y.length = (monomialsAt nw).length) :
    ∀ (cs : List BPair) (K : elim.Mat),
      elim.rowsLen (monomialsAt nu).length K →
      (∀ k, k < K.length →
        elim.spanRel (monomialsAt
            (List.zipWith (fun p q => p + q) nu nw)).length M
          (tensorH ⟨nu, ground.getAt [] K k⟩ ⟨nw, Y⟩).coords) →
      elim.spanRel (monomialsAt
          (List.zipWith (fun p q => p + q) nu nw)).length M
        (tensorH ⟨nu, elim.combo (monomialsAt nu).length cs K⟩
          ⟨nw, Y⟩).coords
  | [], _, _, _ => by
    refine elim.spanRel_null _ M _ ?_ hM (tensorH_sized _ _)
    exact (tensorH_unitTail
      ⟨nu, List.replicate (monomialsAt nu).length BPair.unit⟩
      ⟨nw, Y⟩ (ground.length_replicate BPair.unit _) hY hnn).mpr
      (Or.inl (poly.unitTail_replicate _))
  | _ :: _, [], _, _ => by
    refine elim.spanRel_null _ M _ ?_ hM (tensorH_sized _ _)
    exact (tensorH_unitTail
      ⟨nu, List.replicate (monomialsAt nu).length BPair.unit⟩
      ⟨nw, Y⟩ (ground.length_replicate BPair.unit _) hY hnn).mpr
      (Or.inl (poly.unitTail_replicate _))
  | c :: cs, r :: K, hK, h => by
    have hr : r.length = (monomialsAt nu).length := hK.1
    have hcm : (elim.combo (monomialsAt nu).length cs K).length
        = (monomialsAt nu).length :=
      elim.length_combo _ cs K hK.2
    have hvs : (elim.vecScale c r).length
        = (monomialsAt nu).length := by
      rw [elim.length_vecScale c r, hr]
    have h1 : elim.spanRel (monomialsAt
          (List.zipWith (fun p q => p + q) nu nw)).length M
        (tensorH ⟨nu, elim.vecScale c r⟩ ⟨nw, Y⟩).coords := by
      refine elim.spanRel_congr _ M
        (elim.vecScale c (tensorH ⟨nu, r⟩ ⟨nw, Y⟩).coords) _
        (poly.oneValue_symm
          (tensorH_vecScaleL nu ⟨nw, Y⟩ hY hnn c r hr)) ?_
        (tensorH_sized _ _)
      exact elim.spanRel_scale _ M _ c hM (tensorH_sized _ _)
        (h 0 (Nat.succ_pos _))
    have h2 := tensorH_span_left nu nw hnn M hM Y hY cs K hK.2
      (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))
    refine elim.spanRel_congr _ M
      (elim.vecAdd (tensorH ⟨nu, elim.vecScale c r⟩
          ⟨nw, Y⟩).coords
        (tensorH ⟨nu, elim.combo (monomialsAt nu).length cs K⟩
          ⟨nw, Y⟩).coords) _
      (poly.oneValue_symm (tensorH_vecAddL nu ⟨nw, Y⟩ hY hnn _ _
        hvs hcm)) ?_ (tensorH_sized _ _)
    exact elim.spanRel_add _ M _ _ hM (tensorH_sized _ _)
      (tensorH_sized _ _) h1 h2

private theorem tensor_span_row (A B : List HVec) (nu nw : List Nat)
    (k l : Nat)
    (hk : k < (groupAt A nu).length)
    (hl : l < (groupAt B nw).length) :
    elim.spanRel (monomialsAt
        (List.zipWith (fun p q => p + q) nu nw)).length
      (groupAt (fusedAt A B)
        (List.zipWith (fun p q => p + q) nu nw))
      (tensorH ⟨nu, ground.getAt [] (groupAt A nu) k⟩
        ⟨nw, ground.getAt [] (groupAt B nw) l⟩).coords := by
  match groupAt_rows (fun v => v ∈ A) A (fun _ hv => hv) nu k hk,
      groupAt_rows (fun w => w ∈ B) B (fun _ hw => hw) nw l hl with
  | ⟨v, hvA, hvc, hvr⟩, ⟨w, hwB, hwc, hwr⟩ =>
    have hveq : (⟨nu, ground.getAt [] (groupAt A nu) k⟩ : HVec)
        = v := hvec_eq hvc.symm hvr
    have hweq : (⟨nw, ground.getAt [] (groupAt B nw) l⟩ : HVec)
        = w := hvec_eq hwc.symm hwr
    have hcont : (tensorH v w).content
        = List.zipWith (fun p q => p + q) nu nw := by
      show List.zipWith (fun a b => a + b) v.content w.content
        = List.zipWith (fun p q => p + q) nu nw
      rw [hvc, hwc]
    have hmem : tensorH v w ∈ fusedAt A B :=
      ground.mem_flatMap_to (fun v' => B.map (tensorH v')) hvA
        (ground.mem_map_to (tensorH v) hwB)
    have hgrp : (tensorH v w).coords
        ∈ groupAt (fusedAt A B)
          (List.zipWith (fun p q => p + q) nu nw) :=
      ground.mem_map_to HVec.coords
        (ground.mem_filter_to
          (fun u => u.content
            == List.zipWith (fun p q => p + q) nu nw) hmem
          (by
            rw [hcont]
            exact ground.listEqBeq
              (List.zipWith (fun p q => p + q) nu nw)))
    match ground.getAt_of_mem ([] : List BPair) hgrp with
    | ⟨k', hk', he⟩ =>
      rw [hveq, hweq, ← he]
      exact elim.spanRel_getAt _ _ k' hk'
        (rowsLen_groupAt _ (fusedAt A B) (fusedAt_sized A B))

set_option linter.unusedVariables false in
/-- The collecting read (`con:places`' collecting sentence at
`lem:blockcount`(iii)): a tensor of two combinations collects to
the pairs at the coefficients' products, so a member of the first
block's content span tensored against a member of the second
block's lands in the fused pool's own span at the summed content.
The two clearings multiply — the product of two off-unit factors is
off the sum's unit — and the double combination walks out one
factor at a time through the tensor's additivity and
scale-equivariance in that factor, each pair of rows a member of
the fused pool's content group.  The coordinate widths of `x` and
`y` are not binders here: `elim.spanRel` carries them.  The two
member-width binders `hwidA`, `hwidB` with their letter count `d`
are the carrier's frame, `con:places`' one letter width at both
lists; the proof consumes neither, reading the two contents' own
widths through `hnu` and `hnw` alone. -/
theorem tensor_span (A B : List HVec) (d : Nat)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (nu nw : List Nat) (hnu : nu.length = d) (hnw : nw.length = d)
    (x y : List BPair)
    (hsx : elim.spanRel (places.monomialsAt nu).length
      (groupAt A nu) x)
    (hsy : elim.spanRel (places.monomialsAt nw).length
      (groupAt B nw) y) :
    elim.spanRel
      (places.monomialsAt
        (List.zipWith (fun p q => p + q) nu nw)).length
      (groupAt (fusedAt A B)
        (List.zipWith (fun p q => p + q) nu nw))
      (tensorH ⟨nu, x⟩ ⟨nw, y⟩).coords := by
  have hnn : nu.length = nw.length := by
    rw [hnu, hnw]
  have hGC := rowsLen_groupAt
    (List.zipWith (fun p q => p + q) nu nw) (fusedAt A B)
    (fusedAt_sized A B)
  have hGA := rowsLen_groupAt nu A hszA
  have hGB := rowsLen_groupAt nw B hszB
  have hxl : x.length = (monomialsAt nu).length := hsx.2.1
  have hyl : y.length = (monomialsAt nw).length := hsy.2.1
  match elim.span_elim hsx, elim.span_elim hsy with
  | ⟨c0, cs, hc0, _, hpx⟩, ⟨d0, ds, hd0, _, hpy⟩ =>
    have hcd : ¬ (c0 * d0).oneValue BPair.unit := fun hcon =>
      hd0 (ground.mul_cancel_unit hc0 hcon)
    have hXc : (elim.combo (monomialsAt nu).length cs
        (groupAt A nu)).length = (monomialsAt nu).length :=
      elim.length_combo _ cs _ hGA
    have hYc : (elim.combo (monomialsAt nw).length ds
        (groupAt B nw)).length = (monomialsAt nw).length :=
      elim.length_combo _ ds _ hGB
    have hdouble : elim.spanRel (monomialsAt
          (List.zipWith (fun p q => p + q) nu nw)).length
        (groupAt (fusedAt A B)
          (List.zipWith (fun p q => p + q) nu nw))
        (tensorH
          ⟨nu, elim.combo (monomialsAt nu).length cs
            (groupAt A nu)⟩
          ⟨nw, elim.combo (monomialsAt nw).length ds
            (groupAt B nw)⟩).coords := by
      refine tensorH_span_left nu nw hnn _ hGC _ hYc cs
        (groupAt A nu) hGA ?_
      intro k hk
      refine tensorH_span_right nu nw hnn _ hGC _
        (elim.rowsLen_getAt (groupAt A nu) k hGA hk) ds
        (groupAt B nw) hGB ?_
      intro l hl
      exact tensor_span_row A B nu nw k l hk hl
    refine elim.spanRel_unscale _ _ (c0 * d0) _ hcd ?_
    refine elim.spanRel_congr _ _
      (tensorH
        ⟨nu, elim.combo (monomialsAt nu).length cs (groupAt A nu)⟩
        ⟨nw, elim.combo (monomialsAt nw).length ds
          (groupAt B nw)⟩).coords _ ?_ hdouble ?_
    · refine poly.oneValue_trans
        (poly.oneValue_symm (tensorH_polyOne
          ⟨nu, elim.vecScale c0 x⟩
          ⟨nu, elim.combo (monomialsAt nu).length cs (groupAt A nu)⟩
          ⟨nw, elim.vecScale d0 y⟩
          ⟨nw, elim.combo (monomialsAt nw).length ds (groupAt B nw)⟩
          (by show (elim.vecScale c0 x).length
                = (monomialsAt nu).length
              rw [elim.length_vecScale c0 x, hxl]) hXc
          (by show (elim.vecScale d0 y).length
                = (monomialsAt nw).length
              rw [elim.length_vecScale d0 y, hyl]) hYc rfl rfl
          hpx hpy)) ?_
      rw [← elim.vecScale_vecScale c0 d0 (tensorH ⟨nu, x⟩ ⟨nw, y⟩).coords]
      refine poly.oneValue_trans
        (tensorH_vecScaleL nu ⟨nw, elim.vecScale d0 y⟩
          (by show (elim.vecScale d0 y).length
                = (monomialsAt nw).length
              rw [elim.length_vecScale d0 y, hyl]) hnn c0 x
          hxl) ?_
      exact elim.vecScale_oneValue c0 _ _
        (tensorH_vecScaleR ⟨nu, x⟩ nw hxl hnn d0 y hyl)
    · rw [elim.length_vecScale (c0 * d0) _]
      exact tensorH_sized _ _

/-- The Cartan floor on shapes (`lem:blockcount`(iii)'s closing
sentence): at the column union of two shapes the fusion count is
occupied.  The tensor of the two column exhibits is a top off the
sum's unit at content `a + b` — every stacked adjacent raising
sends its every coordinate to the sum's unit, the two factors' own
top reads joined by the Leibniz fold — and it heads the display's pair list, so the coefficient
family carrying the natural one at that head and the sum's unit
past it lies in the kernel list's span; an empty kernel list would
force that family to the unit tail, so the kernel list is occupied
and its length, the count, is at least one.  The one letter width
`hba` is load-bearing with its committed refusal: a wider second
shape at a second occupied letter starves the head pair's guard
and the count reads the sum's unit. -/
theorem fusionCount_cartan (a b : Shape)
    (hba : b.length = a.length) :
    1 ≤ fusionCount a b (places.addS a b) := by
  have hcc : (tensorH (exhibit a) (exhibit b)).content
      = rowList (places.addS a b) := by
    show List.zipWith (fun x y => x + y) (exhibit a).content
      (exhibit b).content = rowList (places.addS a b)
    rw [content_exhibit a, content_exhibit b,
      places.rowList_addS a b hba]
  have hstack : poly.unitTail (elim.matVec
      (units.stackedRaise (rowList (places.addS a b)))
      (tensorH (exhibit a) (exhibit b)).coords) := by
    have h := tensor_exhibit_stacked a b hba
    rw [hcc] at h
    exact h
  show 1 ≤ elim.kernelDim
    (pairsAt (blockSpan a) (blockSpan b)
      (rowList (places.addS a b))).length
    (elim.crossM (units.stackedRaise (rowList (places.addS a b)))
      ((pairsAt (blockSpan a) (blockSpan b)
        (rowList (places.addS a b))).map HVec.coords))
  match blockSpan_prov a, blockSpan_prov b with
  | ⟨ta, hta, _⟩, ⟨tb, htb, _⟩ =>
    match pairsAt_head (exhibit a) (exhibit b) ta tb
        (rowList (places.addS a b)) hcc with
    | ⟨rest, hpairs⟩ =>
      rw [hta, htb, hpairs]
      show 1 ≤ elim.kernelDim (rest.length + 1)
        (elim.crossM (units.stackedRaise
            (rowList (places.addS a b)))
          ((tensorH (exhibit a) (exhibit b)).coords
            :: rest.map HVec.coords))
      match Nat.eq_zero_or_pos (elim.kernelDim (rest.length + 1)
          (elim.crossM (units.stackedRaise
              (rowList (places.addS a b)))
            ((tensorH (exhibit a) (exhibit b)).coords
              :: rest.map HVec.coords))) with
      | .inr hpos => exact hpos
      | .inl hz =>
        exfalso
        have hml : (rest.map HVec.coords).length = rest.length :=
          ground.length_map HVec.coords rest
        have hm : elim.rowsLen (rest.length + 1)
            (elim.crossM (units.stackedRaise
                (rowList (places.addS a b)))
              ((tensorH (exhibit a) (exhibit b)).coords
                :: rest.map HVec.coords)) := by
          have h := elim.rowsLen_crossM
            (units.stackedRaise (rowList (places.addS a b)))
            ((tensorH (exhibit a) (exhibit b)).coords
              :: rest.map HVec.coords)
          rw [show ((tensorH (exhibit a) (exhibit b)).coords
              :: rest.map HVec.coords).length = rest.length + 1
            from by rw [show ((tensorH (exhibit a) (exhibit b)).coords
              :: rest.map HVec.coords).length
                = (rest.map HVec.coords).length + 1 from rfl,
              hml]] at h
          exact h
        have he : (BPair.ofNat 1 :: List.replicate
            (rest.map HVec.coords).length BPair.unit).length
            = rest.length + 1 := by
          rw [show (BPair.ofNat 1 :: List.replicate
              (rest.map HVec.coords).length BPair.unit).length
            = (List.replicate (rest.map HVec.coords).length
                BPair.unit).length + 1 from rfl,
            ground.length_replicate BPair.unit
              (rest.map HVec.coords).length, hml]
        have hker := crossM_head_null
          (units.stackedRaise (rowList (places.addS a b)))
          (tensorH (exhibit a) (exhibit b)).coords
          (rest.map HVec.coords) hstack
        have hsp := elim.kernelList_span (rest.length + 1) _ hm _
          he hker
        have hknil : elim.kernelList (rest.length + 1)
            (elim.crossM (units.stackedRaise
                (rowList (places.addS a b)))
              ((tensorH (exhibit a) (exhibit b)).coords
                :: rest.map HVec.coords)) = [] :=
          ground.nil_of_length_zero _
            ((elim.kernelList_dim _ _).trans hz)
        rw [hknil] at hsp
        match elim.span_elim hsp with
        | ⟨c0, cs, hc0, hcsl, hpoly⟩ =>
          rw [ground.nil_of_length_zero cs hcsl] at hpoly
          have hunit : poly.unitTail (elim.vecScale c0
              (BPair.ofNat 1 :: List.replicate
                (rest.map HVec.coords).length BPair.unit)) :=
            poly.oneValue_unitTail hpoly
              (poly.unitTail_replicate (rest.length + 1))
          exact BPair.ofNat_one_off
            (ground.mul_cancel_unit hc0 hunit.1)

/-! `lem:blockcount`(iii)'s stacked pairing: the stacked raisings
are the occupied adjacent moves' blocks joined, so a pair of
images at one content pairs block by block — one term per adjacent
move at the content's own width, each the two acted vectors' own
pairing, and the vacant moves' terms at the sum's unit
(`con:units`' vacant-letter read). -/


/-- One adjacent move's block pairs the two acted vectors: at an
occupied target the block is the action's own matrix
(`moveAt_moveUp`), and at a vacant one the block is empty while the
action sends its whole image to the sum's unit
(`act_unitTail`). -/
private theorem dotP_raiseBlock (cc : List Nat) (x y : HVec)
    (hxc : x.content = cc) (hyc : y.content = cc)
    (hsx : sized x) (i : Nat)
    (hi : i + 1 < cc.length) :
    (elim.dotP
        (elim.matVec (if 0 < ground.getAt 0 cc (i + 1) then
            units.matUnitAt (units.moveUp i cc) cc i (i + 1)
          else []) x.coords)
        (elim.matVec (if 0 < ground.getAt 0 cc (i + 1) then
            units.matUnitAt (units.moveUp i cc) cc i (i + 1)
          else []) y.coords)).oneValue
      (elim.dotP (act i (i + 1) x).coords
        (act i (i + 1) y).coords) := by
  have hij : ¬ i = i + 1 := fun he => Nat.succ_ne_self i he.symm
  have hxl : i + 1 < x.content.length := by rw [hxc]; exact hi
  have hxi : i < x.content.length :=
    Nat.lt_of_succ_lt hxl
  by_cases hocc : 0 < ground.getAt 0 cc (i + 1)
  · rw [if_pos hocc]
    have hax : (act i (i + 1) x).coords
        = elim.matVec (units.matUnitAt (units.moveUp i cc) cc i
          (i + 1)) x.coords := by
      show elim.matVec (units.matUnitAt
        (moveAt i (i + 1) x.content) x.content i (i + 1))
        x.coords = _
      rw [hxc, moveAt_moveUp i cc]
    have hay : (act i (i + 1) y).coords
        = elim.matVec (units.matUnitAt (units.moveUp i cc) cc i
          (i + 1)) y.coords := by
      show elim.matVec (units.matUnitAt
        (moveAt i (i + 1) y.content) y.content i (i + 1))
        y.coords = _
      rw [hyc, moveAt_moveUp i cc]
    rw [hax, hay]
    exact BPair.oneValue_refl _
  · rw [if_neg hocc]
    have hzero : ground.getAt 0 x.content (i + 1) = 0 := by
      rw [hxc]
      match Nat.eq_zero_or_pos (ground.getAt 0 cc (i + 1)) with
      | .inl hz => exact hz
      | .inr hp => exact absurd hp hocc
    have hnull : poly.unitTail (act i (i + 1) x).coords :=
      act_unitTail x i (i + 1) hsx hxi hij hxl hzero
    show (elim.dotP ([] : List BPair) ([] : List BPair)).oneValue _
    exact BPair.oneValue_symm
      (elim.dotP_null_tail_left _ _ hnull)

/-- The stacked pairing over a stated index family: the blocks join
and the pairing adds along them. -/
private theorem dotP_stackGo (cc : List Nat) (x y : HVec)
    (hxc : x.content = cc) (hyc : y.content = cc)
    (hsx : sized x) (hsy : sized y) :
    ∀ l : List Nat, (∀ i ∈ l, i + 1 < cc.length) →
      (elim.dotP
          (elim.matVec (l.flatMap (fun i =>
            if 0 < ground.getAt 0 cc (i + 1) then
              units.matUnitAt (units.moveUp i cc) cc i (i + 1)
            else [])) x.coords)
          (elim.matVec (l.flatMap (fun i =>
            if 0 < ground.getAt 0 cc (i + 1) then
              units.matUnitAt (units.moveUp i cc) cc i (i + 1)
            else [])) y.coords)).oneValue
        (ground.famFold BPair.add BPair.unit
          (fun i => elim.dotP (act i (i + 1) x).coords
            (act i (i + 1) y).coords) l)
  | [], _ => BPair.oneValue_refl _
  | i :: t, h => by
    show (elim.dotP
        (elim.matVec ((if 0 < ground.getAt 0 cc (i + 1) then
            units.matUnitAt (units.moveUp i cc) cc i (i + 1)
          else []) ++ t.flatMap (fun i =>
            if 0 < ground.getAt 0 cc (i + 1) then
              units.matUnitAt (units.moveUp i cc) cc i (i + 1)
            else [])) x.coords)
        (elim.matVec ((if 0 < ground.getAt 0 cc (i + 1) then
            units.matUnitAt (units.moveUp i cc) cc i (i + 1)
          else []) ++ t.flatMap (fun i =>
            if 0 < ground.getAt 0 cc (i + 1) then
              units.matUnitAt (units.moveUp i cc) cc i (i + 1)
            else [])) y.coords)).oneValue
      (elim.dotP (act i (i + 1) x).coords (act i (i + 1) y).coords
        + ground.famFold BPair.add BPair.unit
          (fun i => elim.dotP (act i (i + 1) x).coords
            (act i (i + 1) y).coords) t)
    rw [elim.matVec_append, elim.matVec_append]
    refine BPair.oneValue_trans
      (elim.dotP_append _ _ _ _
        (by rw [elim.matVec_length, elim.matVec_length])) ?_
    exact BPair.add_congr
      (dotP_raiseBlock cc x y hxc hyc hsx i
        (h i (List.Mem.head t)))
      (dotP_stackGo cc x y hxc hyc hsx hsy t
        (fun j hj => h j (List.Mem.tail i hj)))

/-- The stacked raisings' pairing splits over the adjacent moves:
two vectors at one content pair through the stacked datum as the
fold, over the content's interior letters, of their two acted
images' own pairings — the vacant moves contributing the sum's
unit at either side (`lem:blockcount`(iii); `con:units`' adjacent
raisings).  Binders: `hsx` is load-bearing at the vacant arm's
unit read; `hsy` is the pairing's frame at its second member, the
statement's own symmetry, the derivation reading the vacant arm
from the left alone. -/
theorem dotP_stackedRaise (cc : List Nat) (x y : HVec)
    (hxc : x.content = cc) (hyc : y.content = cc)
    (hsx : sized x) (hsy : sized y) :
    (elim.dotP (elim.matVec (units.stackedRaise cc) x.coords)
        (elim.matVec (units.stackedRaise cc) y.coords)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => elim.dotP (act i (i + 1) x).coords
          (act i (i + 1) y).coords)
        (List.range (cc.length - 1))) := by
  refine dotP_stackGo cc x y hxc hyc hsx hsy
    (List.range (cc.length - 1)) ?_
  intro i hi
  exact ground.succ_lt_of_lt_pred
    (ground.ltOfMemRange hi)

/-! `lem:blockcount`(iii)'s flip tier: the exchanged pair's stacked
Gram.  The exchange sends each tensor to its factors' exchange, the
coordinate products commuting at every arrangement, and the
Leibniz split's four terms go over to the exchanged four — so the
two enumerations' stacked Grams read one value entry by entry. -/

/-- The memberwise sum reads a unit-tailed right summand away, at
the shorter left order. -/
private theorem vecAdd_unitR : ∀ (u z : List BPair),
    u.length ≤ z.length → poly.unitTail z →
    poly.oneValue (elim.vecAdd u z)
      (elim.vecAdd u (List.replicate u.length BPair.unit))
  | [], _, _, _ => trivial
  | _ :: _, [], h, _ => absurd h (Nat.not_succ_le_zero _)
  | a :: u, _ :: z, h, hz =>
    ⟨BPair.add_congr (BPair.oneValue_refl a) hz.1,
     vecAdd_unitR u z (Nat.le_of_succ_le_succ h) hz.2⟩

/-- The memberwise sum reads a unit-tailed left summand away, at
the shorter right order. -/
private theorem vecAdd_unitL : ∀ (z w : List BPair),
    w.length ≤ z.length → poly.unitTail z →
    poly.oneValue (elim.vecAdd z w)
      (elim.vecAdd (List.replicate w.length BPair.unit) w)
  | [], [], _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | [], _ :: _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | _ :: z, a :: w, h, hz =>
    ⟨BPair.add_congr hz.1 (BPair.oneValue_refl a),
     vecAdd_unitL z w (Nat.le_of_succ_le_succ h) hz.2⟩

/-- The pairing of two memberwise sums at one order is the four
crossed pairings. -/
private theorem dotP_vecAdd4 (n : Nat) (a b c d : List BPair)
    (ha : a.length = n) (hb : b.length = n)
    (hc : c.length = n) (hd : d.length = n) :
    (elim.dotP (elim.vecAdd a b) (elim.vecAdd c d)).oneValue
      (elim.dotP a c + elim.dotP a d
        + (elim.dotP b c + elim.dotP b d)) := by
  have hcd : (elim.vecAdd c d).length = n := by
    rw [length_vecAdd_le c d (Nat.le_of_eq (hc.trans hd.symm)), hc]
  refine BPair.oneValue_trans
    (elim.dotP_vecAdd_left a b (elim.vecAdd c d)
      (Nat.le_of_eq (hcd.trans ha.symm))
      (Nat.le_of_eq (hcd.trans hb.symm))) ?_
  exact BPair.add_congr
    (elim.dotP_vecAdd a c d (hc.trans ha.symm) (hd.trans ha.symm))
    (elim.dotP_vecAdd b c d (hc.trans hb.symm) (hd.trans hb.symm))

/-- The exchanged tensors pair as the unexchanged do: at one pair
of factor contents the two pairings are the factors' own products
commuted, and off that pair both sides sit at the sum's unit — the
exchange never reaches the split, which moves with it. -/
private theorem dotP_tensorH_flip (v w v' w' : HVec)
    (hsv : sized v) (hsw : sized w) (hsv' : sized v')
    (hsw' : sized w')
    (hlen : v.content.length = w.content.length)
    (hlen' : v'.content.length = w'.content.length)
    (hdv : sumNat v.content = sumNat v'.content)
    (hdw : sumNat w.content = sumNat w'.content)
    (hcc : (tensorH v w).content = (tensorH v' w').content) :
    (elim.dotP (tensorH w v).coords (tensorH w' v').coords).oneValue
      (elim.dotP (tensorH v w).coords
        (tensorH v' w').coords) := by
  have hcc0 : List.zipWith (fun x y => x + y) v.content w.content
      = List.zipWith (fun x y => x + y) v'.content w'.content := hcc
  have hccF : (tensorH w v).content = (tensorH w' v').content := by
    show List.zipWith (fun x y => x + y) w.content v.content
      = List.zipWith (fun x y => x + y) w'.content v'.content
    rw [ground.zipWith_add_comm w.content v.content,
      ground.zipWith_add_comm w'.content v'.content]
    exact hcc0
  by_cases hv : v.content = v'.content
  · have hvl : v'.content.length = v.content.length := by rw [hv]
    have hw : w.content = w'.content :=
      zipWith_add_cancelL v.content w.content w'.content
        v.content.length rfl hlen.symm
        (hlen'.symm.trans hvl) (hcc0.trans (by rw [hv]))
    exact BPair.oneValue_trans
      (dotP_tensorH w v w' v' hsw hsv hsw' hsv' hlen.symm hw hv)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.oneValue_symm
          (dotP_tensorH v w v' w' hsv hsw hsv' hsw' hlen hv hw)))
  · have hwne : ¬ w.content = w'.content := by
      intro he
      refine hv ?_
      have hwl : w'.content.length = w.content.length := by rw [he]
      exact zipWith_add_cancelR v.content v'.content w.content
        v.content.length rfl
        (hlen'.trans (hwl.trans hlen.symm)) hlen.symm
        (hcc0.trans (by rw [he]))
    exact BPair.oneValue_trans
      (dotP_tensorH_off w v w' v' hlen.symm hlen'.symm hdw hccF
        hwne)
      (BPair.oneValue_symm
        (dotP_tensorH_off v w v' w' hlen hlen' hdv hcc hv))

/-- The first factor's raised half at an occupied target, the
sum's unit family where the target is vacant. -/
private def raiseHalfL (i n : Nat) (v w : HVec) : List BPair :=
  if 0 < ground.getAt 0 v.content (i + 1)
    then (tensorH (act i (i + 1) v) w).coords
    else List.replicate n BPair.unit

/-- The second factor's raised half at an occupied target, the
sum's unit family where the target is vacant. -/
private def raiseHalfR (i n : Nat) (v w : HVec) : List BPair :=
  if 0 < ground.getAt 0 w.content (i + 1)
    then (tensorH v (act i (i + 1) w)).coords
    else List.replicate n BPair.unit

/-- The raised first factor's tensor sits at the moved union, at an
occupied target. -/
private theorem content_halfL (i j : Nat) (cc : List Nat) (v w : HVec)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hv : 0 < ground.getAt 0 v.content j) :
    (tensorH (act i j v) w).content = moveAt i j cc := by
  show List.zipWith (fun x y => x + y)
    (moveAt i j v.content) w.content = _
  rw [moveAt_zipWith_left i j v.content w.content hv, hg]

/-- The raised second factor's tensor sits at the moved union, at
an occupied target. -/
private theorem content_halfR (i j : Nat) (cc : List Nat) (v w : HVec)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hw : 0 < ground.getAt 0 w.content j) :
    (tensorH v (act i j w)).content = moveAt i j cc := by
  show List.zipWith (fun x y => x + y) v.content
    (moveAt i j w.content) = _
  rw [moveAt_zipWith_right i j v.content w.content hw, hg]

/-- At a vacant moved letter on the first factor the join's move
is the raise at the target letter. -/
theorem moveAt_vacL (r s : Nat) (p q cc : List Nat)
    (hpq : List.zipWith (fun x y => x + y) p q = cc)
    (hz : ground.getAt 0 p s = 0) :
    List.zipWith (fun x y => x + y) (moveAt r s p) q
      = ground.bumpAt r cc := by
  show List.zipWith (fun x y => x + y)
      (ground.bumpAt r (ground.dipAt s p)) q = _
  rw [ground.dipAt_of_zero s p hz,
    ground.bumpAt_zipWith_left r p q, hpq]

/-- At a vacant moved letter on the second factor the join's move
is the raise at the target letter. -/
theorem moveAt_vacR (r s : Nat) (p q cc : List Nat)
    (hpq : List.zipWith (fun x y => x + y) p q = cc)
    (hz : ground.getAt 0 q s = 0) :
    List.zipWith (fun x y => x + y) p (moveAt r s q)
      = ground.bumpAt r cc := by
  show List.zipWith (fun x y => x + y) p
      (ground.bumpAt r (ground.dipAt s q)) = _
  rw [ground.dipAt_of_zero s q hz,
    ground.bumpAt_zipWith_right r p q, hpq]

/-- The moved content raised back at the moved-from letter is the
source raised at the moved-to letter. -/
theorem bumpAt_moveAt (r s : Nat) (cc : List Nat)
    (hocc : 0 < ground.getAt 0 cc s) :
    ground.bumpAt s (moveAt r s cc) = ground.bumpAt r cc := by
  show ground.bumpAt s (ground.bumpAt r (ground.dipAt s cc)) = _
  rw [ground.bumpAt_comm s r (ground.dipAt s cc),
    ground.bumpAt_dipAt_self s cc hocc]

/-- At a vacant target the raised first factor only gains a box:
its tensor sits one raise above the moved union. -/
private theorem content_halfL_vac (i j : Nat) (cc : List Nat)
    (v w : HVec)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hv : ground.getAt 0 v.content j = 0)
    (hocc : 0 < ground.getAt 0 cc j) :
    (tensorH (act i j v) w).content
      = bumpAt j (moveAt i j cc) := by
  show List.zipWith (fun x y => x + y)
    (moveAt i j v.content) w.content = _
  rw [moveAt_vacL i j v.content w.content cc hg hv,
    bumpAt_moveAt i j cc hocc]

/-- At a vacant target the raised second factor only gains a box:
its tensor sits one raise above the moved union. -/
private theorem content_halfR_vac (i j : Nat) (cc : List Nat)
    (v w : HVec)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hw : ground.getAt 0 w.content j = 0)
    (hocc : 0 < ground.getAt 0 cc j) :
    (tensorH v (act i j w)).content
      = bumpAt j (moveAt i j cc) := by
  show List.zipWith (fun x y => x + y) v.content
    (moveAt i j w.content) = _
  rw [moveAt_vacR i j v.content w.content cc hg hw,
    bumpAt_moveAt i j cc hocc]

/-- The two halves read the moved union's own width. -/
private theorem length_raiseHalfL (i n : Nat) (cc : List Nat)
    (v w : HVec)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hn : n = (monomialsAt (moveAt i (i + 1) cc)).length) :
    (raiseHalfL i n v w).length = n := by
  show (if 0 < ground.getAt 0 v.content (i + 1)
      then (tensorH (act i (i + 1) v) w).coords
      else List.replicate n BPair.unit).length = n
  by_cases hv : 0 < ground.getAt 0 v.content (i + 1)
  · rw [if_pos hv, tensorH_sized (act i (i + 1) v) w,
      content_halfL i (i + 1) cc v w hg hv]
    exact hn.symm
  · rw [if_neg hv, ground.length_replicate]

private theorem length_raiseHalfR (i n : Nat) (cc : List Nat)
    (v w : HVec)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hn : n = (monomialsAt (moveAt i (i + 1) cc)).length) :
    (raiseHalfR i n v w).length = n := by
  show (if 0 < ground.getAt 0 w.content (i + 1)
      then (tensorH v (act i (i + 1) w)).coords
      else List.replicate n BPair.unit).length = n
  by_cases hw : 0 < ground.getAt 0 w.content (i + 1)
  · rw [if_pos hw, tensorH_sized v (act i (i + 1) w),
      content_halfR i (i + 1) cc v w hg hw]
    exact hn.symm
  · rw [if_neg hw, ground.length_replicate]

/-- The raising of a tensor at an occupied target reads the two
halves' memberwise sum, both halves at the moved union's width: at
an occupied factor the half is the Leibniz summand, and at a vacant
one the summand's whole image is at the sum's unit
(`act_unitTail`), the further places absorbed by the raised width's
own count (`places.length_monomialsAt_le_bumpAt`). -/
private theorem act_tensorH_half (i n : Nat) (cc : List Nat)
    (v w : HVec) (hsv : sized v) (hsw : sized w)
    (hlen : v.content.length = w.content.length)
    (hi : i + 1 < v.content.length)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hocc : 0 < ground.getAt 0 cc (i + 1))
    (hn : n = (monomialsAt (moveAt i (i + 1) cc)).length) :
    poly.oneValue (act i (i + 1) (tensorH v w)).coords
      (elim.vecAdd (raiseHalfL i n v w) (raiseHalfR i n v w)) := by
  have hij : ¬ i = i + 1 := fun he => Nat.succ_ne_self i he.symm
  have hiv : i < v.content.length := Nat.lt_of_succ_lt hi
  have hiw : i + 1 < w.content.length := by rw [← hlen]; exact hi
  have hiw' : i < w.content.length := Nat.lt_of_succ_lt hiw
  have hccl : cc.length = v.content.length := by
    rw [← hg]
    exact ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length
      rfl hlen.symm
  have hbnd : i + 1 < (moveAt i (i + 1) cc).length := by
    rw [length_moveAt, hccl]
    exact hi
  have hT := act_tensorH i (i + 1) v w hsv hsw hlen hiv hi hij
  by_cases hv : 0 < ground.getAt 0 v.content (i + 1)
  · have hL : raiseHalfL i n v w
        = (tensorH (act i (i + 1) v) w).coords := by
      show (if 0 < ground.getAt 0 v.content (i + 1)
        then (tensorH (act i (i + 1) v) w).coords
        else List.replicate n BPair.unit) = _
      rw [if_pos hv]
    by_cases hw : 0 < ground.getAt 0 w.content (i + 1)
    · have hR : raiseHalfR i n v w
          = (tensorH v (act i (i + 1) w)).coords := by
        show (if 0 < ground.getAt 0 w.content (i + 1)
          then (tensorH v (act i (i + 1) w)).coords
          else List.replicate n BPair.unit) = _
        rw [if_pos hw]
      rw [hL, hR]
      exact hT
    · have hwz : ground.getAt 0 w.content (i + 1) = 0 :=
        Nat.eq_zero_of_not_pos hw
      have hR : raiseHalfR i n v w = List.replicate n BPair.unit := by
        show (if 0 < ground.getAt 0 w.content (i + 1)
          then (tensorH v (act i (i + 1) w)).coords
          else List.replicate n BPair.unit) = _
        rw [if_neg hw]
      have hAn : (tensorH (act i (i + 1) v) w).coords.length = n := by
        rw [tensorH_sized (act i (i + 1) v) w,
          content_halfL i (i + 1) cc v w hg hv]
        exact hn.symm
      have hBl : (tensorH v (act i (i + 1) w)).coords.length
          = (monomialsAt
            (bumpAt (i + 1) (moveAt i (i + 1) cc))).length := by
        rw [tensorH_sized v (act i (i + 1) w),
          content_halfR_vac i (i + 1) cc v w hg hwz hocc]
      have hle : (tensorH (act i (i + 1) v) w).coords.length
          ≤ (tensorH v (act i (i + 1) w)).coords.length := by
        rw [hAn, hBl, hn]
        exact places.length_monomialsAt_le_bumpAt (i + 1)
          (moveAt i (i + 1) cc) hbnd
      have hnull : poly.unitTail
          (tensorH v (act i (i + 1) w)).coords :=
        (tensorH_unitTail v (act i (i + 1) w) hsv
          (act_sized i (i + 1) w)
          (by show v.content.length
                = (moveAt i (i + 1) w.content).length
              rw [length_moveAt]
              exact hlen)).mpr
          (Or.inr (act_unitTail w i (i + 1) hsw hiw' hij hiw hwz))
      rw [hL, hR, ← hAn]
      exact poly.oneValue_trans hT
        (vecAdd_unitR _ _ hle hnull)
  · have hvz : ground.getAt 0 v.content (i + 1) = 0 :=
      Nat.eq_zero_of_not_pos hv
    have hw : 0 < ground.getAt 0 w.content (i + 1) := by
      have hsum : ground.getAt 0 cc (i + 1)
          = ground.getAt 0 v.content (i + 1)
            + ground.getAt 0 w.content (i + 1) := by
        rw [← hg]
        exact ground.getAt_zipWith 0 0 0 (fun x y => x + y) v.content w.content (i + 1) hi hiw
      rw [hsum, hvz, Nat.zero_add] at hocc
      exact hocc
    have hL : raiseHalfL i n v w = List.replicate n BPair.unit := by
      show (if 0 < ground.getAt 0 v.content (i + 1)
        then (tensorH (act i (i + 1) v) w).coords
        else List.replicate n BPair.unit) = _
      rw [if_neg hv]
    have hR : raiseHalfR i n v w
        = (tensorH v (act i (i + 1) w)).coords := by
      show (if 0 < ground.getAt 0 w.content (i + 1)
        then (tensorH v (act i (i + 1) w)).coords
        else List.replicate n BPair.unit) = _
      rw [if_pos hw]
    have hBn : (tensorH v (act i (i + 1) w)).coords.length = n := by
      rw [tensorH_sized v (act i (i + 1) w),
        content_halfR i (i + 1) cc v w hg hw]
      exact hn.symm
    have hAl : (tensorH (act i (i + 1) v) w).coords.length
        = (monomialsAt
          (bumpAt (i + 1) (moveAt i (i + 1) cc))).length := by
      rw [tensorH_sized (act i (i + 1) v) w,
        content_halfL_vac i (i + 1) cc v w hg hvz hocc]
    have hle : (tensorH v (act i (i + 1) w)).coords.length
        ≤ (tensorH (act i (i + 1) v) w).coords.length := by
      rw [hBn, hAl, hn]
      exact places.length_monomialsAt_le_bumpAt (i + 1)
        (moveAt i (i + 1) cc) hbnd
    have hnull : poly.unitTail
        (tensorH (act i (i + 1) v) w).coords :=
      (tensorH_unitTail (act i (i + 1) v) w
        (act_sized i (i + 1) v) hsw
        (by show (moveAt i (i + 1) v.content).length
              = w.content.length
            rw [length_moveAt]
            exact hlen)).mpr
        (Or.inl (act_unitTail v i (i + 1) hsv hiv hij hi hvz))
    rw [hL, hR, ← hBn]
    exact poly.oneValue_trans hT (vecAdd_unitL _ _ hle hnull)

/-! The fused carrier's closure, `con:units`' split clause at
`lem:blockcount`(iii)'s fused pool: a pair's letter-pair image is
the two one-sided images' join, each a tensor of a settled image
against the partner's own member, so the collecting read carries
each half into the fused pool's own span. -/

/-- A settled first-factor image tensored against a pool member
sits in the fused pool's span at the summed content: the unit
disjunct reads the tensor at the sum's unit outright
(`tensorH_unitTail`), and the span disjunct rides the collecting
read (`tensor_span`) at the partner's own group row
(`spanRel_groupAt_mem`). -/
private theorem fused_half_spanL (d : Nat) (A B : List HVec)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (w : HVec) (hwB : w ∈ B)
    (nu : List Nat) (hnu : nu.length = d) (z : List BPair)
    (hzl : z.length = (monomialsAt nu).length)
    (hset : allU z = true
      ∨ elim.spanRel z.length (groupAt A nu) z) :
    elim.spanRel
      (monomialsAt
        (List.zipWith (fun p q => p + q) nu w.content)).length
      (groupAt (fusedAt A B)
        (List.zipWith (fun p q => p + q) nu w.content))
      (tensorH ⟨nu, z⟩ w).coords := by
  have hnw : nu.length = w.content.length := by
    rw [hnu, hwidB w hwB]
  match hset with
  | Or.inl hall =>
    refine elim.spanRel_null _ _ _ ?_
      (rowsLen_groupAt _ (fusedAt A B) (fusedAt_sized A B))
      (tensorH_sized ⟨nu, z⟩ w)
    exact (tensorH_unitTail ⟨nu, z⟩ w hzl (hszB w hwB) hnw).mpr
      (Or.inl (unitTail_of_allU z hall))
  | Or.inr hsp =>
    rw [hzl] at hsp
    exact tensor_span A B d hszA hszB hwidA hwidB nu w.content hnu
      (hwidB w hwB) z w.coords hsp
      (spanRel_groupAt_mem B w hwB hszB)

/-- The mirrored half: a pool member tensored against a settled
second-factor image sits in the fused pool's span at the summed
content. -/
private theorem fused_half_spanR (d : Nat) (A B : List HVec)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (v : HVec) (hvA : v ∈ A)
    (nw : List Nat) (hnw : nw.length = d) (z : List BPair)
    (hzl : z.length = (monomialsAt nw).length)
    (hset : allU z = true
      ∨ elim.spanRel z.length (groupAt B nw) z) :
    elim.spanRel
      (monomialsAt
        (List.zipWith (fun p q => p + q) v.content nw)).length
      (groupAt (fusedAt A B)
        (List.zipWith (fun p q => p + q) v.content nw))
      (tensorH v ⟨nw, z⟩).coords := by
  have hvn : v.content.length = nw.length := by
    rw [hnw, hwidA v hvA]
  match hset with
  | Or.inl hall =>
    refine elim.spanRel_null _ _ _ ?_
      (rowsLen_groupAt _ (fusedAt A B) (fusedAt_sized A B))
      (tensorH_sized v ⟨nw, z⟩)
    exact (tensorH_unitTail v ⟨nw, z⟩ (hszA v hvA) hzl hvn).mpr
      (Or.inr (unitTail_of_allU z hall))
  | Or.inr hsp =>
    rw [hzl] at hsp
    exact tensor_span A B d hszA hszB hwidA hwidB v.content nw
      (hwidA v hvA) hnw v.coords z
      (spanRel_groupAt_mem A v hvA hszA) hsp

/-- The fused pool is closed at the letter pairs (`con:units`'
composite clause at `lem:blockcount`(iii)'s fused carrier): the
image of a pair is the two one-sided images' memberwise join
(`act_tensorH`), each half a tensor of a settled image against the
partner's own member, so the collecting read (`tensor_span`)
carries each half into the fused pool's span and the join sits
there too (`elim.spanRel_add`).  At a vacant target letter the
whole image reads the sum's unit (`act_unitTail`); at a vacant
factor letter that factor's half does and the surviving half
carries the read alone at the shorter width
(`places.length_monomialsAt_le_bumpAt`).  The width binders are
`con:places`' one letter width at both lists, the two closure
binders the stated pools' own. -/
theorem fused_closed (d : Nat) (A B : List HVec)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hclA : ∀ v ∈ A, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt A (act i j v))
    (hclB : ∀ w ∈ B, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt B (act i j w))
    (x : HVec) (hx : x ∈ fusedAt A B)
    (i : Nat) (hi : i < d) (j : Nat) (hj : j < d) (hij : ¬ i = j) :
    settledAt (fusedAt A B) (act i j x) := by
  match fusedAt_mem A B x hx with
  | ⟨v, w, hvA, hwB, hvw⟩ =>
    subst hvw
    have hwv : v.content.length = d := hwidA v hvA
    have hww : w.content.length = d := hwidB w hwB
    have hlen : v.content.length = w.content.length := by
      rw [hwv, hww]
    have hiv : i < v.content.length := by rw [hwv]; exact hi
    have hjv : j < v.content.length := by rw [hwv]; exact hj
    have hiw : i < w.content.length := by rw [hww]; exact hi
    have hjw : j < w.content.length := by rw [hww]; exact hj
    have hccl : (tensorH v w).content.length = d :=
      ground.length_zipWith (fun x y => x + y) v.content w.content d hwv hww
    have hicc : i < (tensorH v w).content.length := by
      rw [hccl]; exact hi
    have hjcc : j < (tensorH v w).content.length := by
      rw [hccl]; exact hj
    have hjbnd : j < (moveAt i j (tensorH v w).content).length := by
      rw [length_moveAt]; exact hjcc
    have hg : List.zipWith (fun x y => x + y) v.content w.content
        = (tensorH v w).content := rfl
    by_cases hccj : 0 < ground.getAt 0 (tensorH v w).content j
    · have hGrows : elim.rowsLen
          (monomialsAt (moveAt i j (tensorH v w).content)).length
          (groupAt (fusedAt A B)
            (moveAt i j (tensorH v w).content)) :=
        rowsLen_groupAt _ (fusedAt A B) (fusedAt_sized A B)
      have hactlen : (act i j (tensorH v w)).coords.length
          = (monomialsAt
            (moveAt i j (tensorH v w).content)).length :=
        act_sized i j (tensorH v w)
      have hT := act_tensorH i j v w (hszA v hvA) (hszB w hwB)
        hlen hiv hjv hij
      refine Or.inr ?_
      show elim.spanRel (act i j (tensorH v w)).coords.length
        (groupAt (fusedAt A B)
          (moveAt i j (tensorH v w).content))
        (act i j (tensorH v w)).coords
      rw [hactlen]
      by_cases hvj : 0 < ground.getAt 0 v.content j
      · have hL : elim.spanRel
            (monomialsAt (moveAt i j (tensorH v w).content)).length
            (groupAt (fusedAt A B)
              (moveAt i j (tensorH v w).content))
            (tensorH (act i j v) w).coords := by
          have h := fused_half_spanL d A B hszA hszB hwidA hwidB w
            hwB (moveAt i j v.content)
            (by rw [length_moveAt]; exact hwv)
            (act i j v).coords (act_sized i j v)
            (hclA v hvA i hi j hj hij)
          rw [show List.zipWith (fun p q => p + q)
              (moveAt i j v.content) w.content
                = moveAt i j (tensorH v w).content from
            content_halfL i j (tensorH v w).content v w hg hvj] at h
          exact h
        by_cases hwj : 0 < ground.getAt 0 w.content j
        · have hR : elim.spanRel
              (monomialsAt
                (moveAt i j (tensorH v w).content)).length
              (groupAt (fusedAt A B)
                (moveAt i j (tensorH v w).content))
              (tensorH v (act i j w)).coords := by
            have h := fused_half_spanR d A B hszA hszB hwidA hwidB v
              hvA (moveAt i j w.content)
              (by rw [length_moveAt]; exact hww)
              (act i j w).coords (act_sized i j w)
              (hclB w hwB i hi j hj hij)
            rw [show List.zipWith (fun p q => p + q) v.content
                (moveAt i j w.content)
                  = moveAt i j (tensorH v w).content from
              content_halfR i j (tensorH v w).content v w hg hwj]
              at h
            exact h
          refine elim.spanRel_congr _ _ _ _
            (poly.oneValue_symm hT)
            (elim.spanRel_add _ _ _ _ hGrows ?_ ?_ hL hR) hactlen
          · rw [tensorH_sized (act i j v) w,
              content_halfL i j (tensorH v w).content v w hg hvj]
          · rw [tensorH_sized v (act i j w),
              content_halfR i j (tensorH v w).content v w hg hwj]
        · have hwz : ground.getAt 0 w.content j = 0 :=
            Nat.eq_zero_of_not_pos hwj
          have hAn : (tensorH (act i j v) w).coords.length
              = (monomialsAt
                (moveAt i j (tensorH v w).content)).length := by
            rw [tensorH_sized (act i j v) w,
              content_halfL i j (tensorH v w).content v w hg hvj]
          have hBl : (tensorH v (act i j w)).coords.length
              = (monomialsAt (bumpAt j
                (moveAt i j (tensorH v w).content))).length := by
            rw [tensorH_sized v (act i j w),
              content_halfR_vac i j (tensorH v w).content v w hg hwz
                hccj]
          have hle : (tensorH (act i j v) w).coords.length
              ≤ (tensorH v (act i j w)).coords.length := by
            rw [hAn, hBl]
            exact places.length_monomialsAt_le_bumpAt j
              (moveAt i j (tensorH v w).content) hjbnd
          have hnull : poly.unitTail
              (tensorH v (act i j w)).coords :=
            (tensorH_unitTail v (act i j w) (hszA v hvA)
              (act_sized i j w)
              (by show v.content.length
                    = (moveAt i j w.content).length
                  rw [length_moveAt]
                  exact hlen)).mpr
              (Or.inr (act_unitTail w i j (hszB w hwB) hiw hij hjw
                hwz))
          refine elim.spanRel_congr _ _ _ _
            (poly.oneValue_symm (poly.oneValue_trans hT
              (poly.oneValue_trans
                (vecAdd_unitR _ _ hle hnull)
                (elim.vecAdd_null_right _ _
                  (ground.length_replicate BPair.unit _).symm
                  (poly.unitTail_replicate _)))))
            hL hactlen
      · have hvz : ground.getAt 0 v.content j = 0 :=
          Nat.eq_zero_of_not_pos hvj
        have hwj : 0 < ground.getAt 0 w.content j := by
          have hsum : ground.getAt 0 (tensorH v w).content j
              = ground.getAt 0 v.content j
                + ground.getAt 0 w.content j :=
            ground.getAt_zipWith 0 0 0 (fun x y => x + y) v.content w.content j hjv hjw
          rw [hsum, hvz, Nat.zero_add] at hccj
          exact hccj
        have hR : elim.spanRel
            (monomialsAt (moveAt i j (tensorH v w).content)).length
            (groupAt (fusedAt A B)
              (moveAt i j (tensorH v w).content))
            (tensorH v (act i j w)).coords := by
          have h := fused_half_spanR d A B hszA hszB hwidA hwidB v
            hvA (moveAt i j w.content)
            (by rw [length_moveAt]; exact hww)
            (act i j w).coords (act_sized i j w)
            (hclB w hwB i hi j hj hij)
          rw [show List.zipWith (fun p q => p + q) v.content
              (moveAt i j w.content)
                = moveAt i j (tensorH v w).content from
            content_halfR i j (tensorH v w).content v w hg hwj] at h
          exact h
        have hBn : (tensorH v (act i j w)).coords.length
            = (monomialsAt
              (moveAt i j (tensorH v w).content)).length := by
          rw [tensorH_sized v (act i j w),
            content_halfR i j (tensorH v w).content v w hg hwj]
        have hAl : (tensorH (act i j v) w).coords.length
            = (monomialsAt (bumpAt j
              (moveAt i j (tensorH v w).content))).length := by
          rw [tensorH_sized (act i j v) w,
            content_halfL_vac i j (tensorH v w).content v w hg hvz
              hccj]
        have hle : (tensorH v (act i j w)).coords.length
            ≤ (tensorH (act i j v) w).coords.length := by
          rw [hBn, hAl]
          exact places.length_monomialsAt_le_bumpAt j
            (moveAt i j (tensorH v w).content) hjbnd
        have hnull : poly.unitTail (tensorH (act i j v) w).coords :=
          (tensorH_unitTail (act i j v) w (act_sized i j v)
            (hszB w hwB)
            (by show (moveAt i j v.content).length
                  = w.content.length
                rw [length_moveAt]
                exact hlen)).mpr
            (Or.inl (act_unitTail v i j (hszA v hvA) hiv hij hjv
              hvz))
        refine elim.spanRel_congr _ _ _ _
          (poly.oneValue_symm (poly.oneValue_trans hT
            (poly.oneValue_trans
              (vecAdd_unitL _ _ hle hnull)
              (elim.vecAdd_null_left _ _
                (ground.length_replicate BPair.unit _)
                (poly.unitTail_replicate _)))))
          hR hactlen
    · refine Or.inl (allU_of_unitTail _ ?_)
      exact act_unitTail (tensorH v w) i j (tensorH_sized v w) hicc
        hij hjcc (Nat.eq_zero_of_not_pos hccj)

/-- The four-term reordering at the balance carrier. -/
private theorem add4_rev (a b c d : BPair) :
    d + c + (b + a) = a + b + (c + d) := by
  rw [BPair.add_comm d c, BPair.add_comm b a,
    BPair.add_comm (c + d) (a + b)]

/-- One crossed term of the Leibniz split goes over to the
exchanged one: at both guards the two tensors' pairings are the
factors' products commuted (`dotP_tensorH_flip`), and where a guard
fails both sides read the sum's unit family. -/
private theorem dotP_halfPair (n : Nat) (c c' : Prop)
    [Decidable c] [Decidable c'] (p q p' q' : HVec)
    (hall : c → c' →
      (elim.dotP (tensorH q p).coords
          (tensorH q' p').coords).oneValue
        (elim.dotP (tensorH p q).coords (tensorH p' q').coords)) :
    (elim.dotP
        (if c then (tensorH q p).coords
          else List.replicate n BPair.unit)
        (if c' then (tensorH q' p').coords
          else List.replicate n BPair.unit)).oneValue
      (elim.dotP
        (if c then (tensorH p q).coords
          else List.replicate n BPair.unit)
        (if c' then (tensorH p' q').coords
          else List.replicate n BPair.unit)) := by
  by_cases h : c
  · by_cases h' : c'
    · rw [show (if c then (tensorH q p).coords
            else List.replicate n BPair.unit)
          = (tensorH q p).coords from if_pos h,
        show (if c then (tensorH p q).coords
            else List.replicate n BPair.unit)
          = (tensorH p q).coords from if_pos h,
        show (if c' then (tensorH q' p').coords
            else List.replicate n BPair.unit)
          = (tensorH q' p').coords from if_pos h',
        show (if c' then (tensorH p' q').coords
            else List.replicate n BPair.unit)
          = (tensorH p' q').coords from if_pos h']
      exact hall h h'
    · rw [show (if c' then (tensorH q' p').coords
            else List.replicate n BPair.unit)
          = List.replicate n BPair.unit from if_neg h',
        show (if c' then (tensorH p' q').coords
            else List.replicate n BPair.unit)
          = List.replicate n BPair.unit from if_neg h']
      exact BPair.oneValue_trans
        (elim.dotP_null_tail_right _ _ (poly.unitTail_replicate n))
        (BPair.oneValue_symm
          (elim.dotP_null_tail_right _ _ (poly.unitTail_replicate n)))
  · rw [show (if c then (tensorH q p).coords
          else List.replicate n BPair.unit)
        = List.replicate n BPair.unit from if_neg h,
      show (if c then (tensorH p q).coords
          else List.replicate n BPair.unit)
        = List.replicate n BPair.unit from if_neg h]
    exact BPair.oneValue_trans
      (elim.dotP_null_tail_left _ _ (poly.unitTail_replicate n))
      (BPair.oneValue_symm
        (elim.dotP_null_tail_left _ _ (poly.unitTail_replicate n)))

/-- One adjacent raising's pairing goes over to the exchanged
pairs': the Leibniz split's four crossed terms are the exchanged
split's own four, each the same factor products commuted, and a
vacant target sends both sides to the sum's unit. -/
private theorem dotP_act_flip (i : Nat) (cc : List Nat)
    (v w v' w' : HVec) (hsv : sized v) (hsw : sized w)
    (hsv' : sized v') (hsw' : sized w')
    (hlen : v.content.length = w.content.length)
    (hlen' : v'.content.length = w'.content.length)
    (hdv : sumNat v.content = sumNat v'.content)
    (hdw : sumNat w.content = sumNat w'.content)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hg' : List.zipWith (fun x y => x + y) v'.content w'.content
      = cc)
    (hi : i + 1 < cc.length) :
    (elim.dotP (act i (i + 1) (tensorH w v)).coords
        (act i (i + 1) (tensorH w' v')).coords).oneValue
      (elim.dotP (act i (i + 1) (tensorH v w)).coords
        (act i (i + 1) (tensorH v' w')).coords) := by
  have hij : ¬ i = i + 1 := fun he => Nat.succ_ne_self i he.symm
  have hgF : List.zipWith (fun x y => x + y) w.content v.content
      = cc := by
    rw [ground.zipWith_add_comm w.content v.content]; exact hg
  have hgF' : List.zipWith (fun x y => x + y) w'.content v'.content
      = cc := by
    rw [ground.zipWith_add_comm w'.content v'.content]; exact hg'
  have hvl : v.content.length = cc.length := by
    rw [← hg]
    exact (ground.length_zipWith (fun x y => x + y) v.content w.content v.content.length
      rfl hlen.symm).symm
  have hv'l : v'.content.length = cc.length := by
    rw [← hg']
    exact (ground.length_zipWith (fun x y => x + y) v'.content w'.content
      v'.content.length rfl hlen'.symm).symm
  have hiv : i + 1 < v.content.length := by rw [hvl]; exact hi
  have hiv' : i + 1 < v'.content.length := by rw [hv'l]; exact hi
  have hiw : i + 1 < w.content.length := by rw [← hlen]; exact hiv
  have hiw' : i + 1 < w'.content.length := by rw [← hlen']; exact hiv'
  by_cases hocc : 0 < ground.getAt 0 cc (i + 1)
  · have hn : (monomialsAt (moveAt i (i + 1) cc)).length
        = (monomialsAt (moveAt i (i + 1) cc)).length := rfl
    have hred := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) cc)).length cc v w hsv hsw
      hlen hiv hg hocc rfl
    have hred' := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) cc)).length cc v' w' hsv' hsw'
      hlen' hiv' hg' hocc rfl
    have hredF := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) cc)).length cc w v hsw hsv
      hlen.symm hiw hgF hocc rfl
    have hredF' := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) cc)).length cc w' v' hsw' hsv'
      hlen'.symm hiw' hgF' hocc rfl
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _ hredF) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right _ _ _ hredF') ?_
    refine BPair.oneValue_trans
      (dotP_vecAdd4 (monomialsAt (moveAt i (i + 1) cc)).length _ _ _ _
        (length_raiseHalfL i _ cc w v hgF rfl)
        (length_raiseHalfR i _ cc w v hgF rfl)
        (length_raiseHalfL i _ cc w' v' hgF' rfl)
        (length_raiseHalfR i _ cc w' v' hgF' rfl)) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _ hred)
      (BPair.oneValue_trans (elim.dotP_oneValue_right _ _ _ hred')
        (BPair.oneValue_trans
          (dotP_vecAdd4 (monomialsAt (moveAt i (i + 1) cc)).length
            _ _ _ _
            (length_raiseHalfL i _ cc v w hg rfl)
            (length_raiseHalfR i _ cc v w hg rfl)
            (length_raiseHalfL i _ cc v' w' hg' rfl)
            (length_raiseHalfR i _ cc v' w' hg' rfl))
          ?_)))
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_of_eq (add4_rev _ _ _ _))
    exact BPair.add_congr
      (BPair.add_congr
        (BPair.oneValue_symm
          (dotP_halfPair (monomialsAt (moveAt i (i + 1) cc)).length
          (0 < ground.getAt 0 v.content (i + 1))
          (0 < ground.getAt 0 v'.content (i + 1))
          (act i (i + 1) v) w (act i (i + 1) v') w'
          (fun hc hc' =>
            dotP_tensorH_flip (act i (i + 1) v) w
              (act i (i + 1) v') w'
              (act_sized i (i + 1) v) hsw (act_sized i (i + 1) v')
              hsw'
              (by show (moveAt i (i + 1) v.content).length
                    = w.content.length
                  rw [length_moveAt]; exact hlen)
              (by show (moveAt i (i + 1) v'.content).length
                    = w'.content.length
                  rw [length_moveAt]; exact hlen')
              (by show sumNat (moveAt i (i + 1) v.content)
                    = sumNat (moveAt i (i + 1) v'.content)
                  rw [sumNat_moveAt i (i + 1) v.content
                      (Nat.lt_of_succ_lt hiv) hc,
                    sumNat_moveAt i (i + 1) v'.content
                      (Nat.lt_of_succ_lt hiv') hc']
                  exact hdv)
              hdw
              (by rw [content_halfL i (i + 1) cc v w hg hc,
                    content_halfL i (i + 1) cc v' w' hg' hc']))))
        (BPair.oneValue_symm
          (dotP_halfPair (monomialsAt (moveAt i (i + 1) cc)).length
          (0 < ground.getAt 0 v.content (i + 1))
          (0 < ground.getAt 0 w'.content (i + 1))
          (act i (i + 1) v) w v' (act i (i + 1) w')
          (fun hc hc' =>
            dotP_tensorH_flip (act i (i + 1) v) w v'
              (act i (i + 1) w')
              (act_sized i (i + 1) v) hsw hsv'
              (act_sized i (i + 1) w')
              (by show (moveAt i (i + 1) v.content).length
                    = w.content.length
                  rw [length_moveAt]; exact hlen)
              (by show v'.content.length
                    = (moveAt i (i + 1) w'.content).length
                  rw [length_moveAt]; exact hlen')
              (by show sumNat (moveAt i (i + 1) v.content)
                    = sumNat v'.content
                  rw [sumNat_moveAt i (i + 1) v.content
                    (Nat.lt_of_succ_lt hiv) hc]
                  exact hdv)
              (by show sumNat w.content
                    = sumNat (moveAt i (i + 1) w'.content)
                  rw [sumNat_moveAt i (i + 1) w'.content
                    (Nat.lt_of_succ_lt hiw') hc']
                  exact hdw)
              (by rw [content_halfL i (i + 1) cc v w hg hc,
                    content_halfR i (i + 1) cc v' w' hg' hc'])))))
      (BPair.add_congr
        (BPair.oneValue_symm
          (dotP_halfPair (monomialsAt (moveAt i (i + 1) cc)).length
          (0 < ground.getAt 0 w.content (i + 1))
          (0 < ground.getAt 0 v'.content (i + 1))
          v (act i (i + 1) w) (act i (i + 1) v') w'
          (fun hc hc' =>
            dotP_tensorH_flip v (act i (i + 1) w)
              (act i (i + 1) v') w'
              hsv (act_sized i (i + 1) w) (act_sized i (i + 1) v')
              hsw'
              (by show v.content.length
                    = (moveAt i (i + 1) w.content).length
                  rw [length_moveAt]; exact hlen)
              (by show (moveAt i (i + 1) v'.content).length
                    = w'.content.length
                  rw [length_moveAt]; exact hlen')
              (by show sumNat v.content
                    = sumNat (moveAt i (i + 1) v'.content)
                  rw [sumNat_moveAt i (i + 1) v'.content
                    (Nat.lt_of_succ_lt hiv') hc']
                  exact hdv)
              (by show sumNat (moveAt i (i + 1) w.content)
                    = sumNat w'.content
                  rw [sumNat_moveAt i (i + 1) w.content
                    (Nat.lt_of_succ_lt hiw) hc]
                  exact hdw)
              (by rw [content_halfR i (i + 1) cc v w hg hc,
                    content_halfL i (i + 1) cc v' w' hg' hc']))))
        (BPair.oneValue_symm
          (dotP_halfPair (monomialsAt (moveAt i (i + 1) cc)).length
          (0 < ground.getAt 0 w.content (i + 1))
          (0 < ground.getAt 0 w'.content (i + 1))
          v (act i (i + 1) w) v' (act i (i + 1) w')
          (fun hc hc' =>
            dotP_tensorH_flip v (act i (i + 1) w) v'
              (act i (i + 1) w')
              hsv (act_sized i (i + 1) w) hsv'
              (act_sized i (i + 1) w')
              (by show v.content.length
                    = (moveAt i (i + 1) w.content).length
                  rw [length_moveAt]; exact hlen)
              (by show v'.content.length
                    = (moveAt i (i + 1) w'.content).length
                  rw [length_moveAt]; exact hlen')
              hdv
              (by show sumNat (moveAt i (i + 1) w.content)
                    = sumNat (moveAt i (i + 1) w'.content)
                  rw [sumNat_moveAt i (i + 1) w.content
                      (Nat.lt_of_succ_lt hiw) hc,
                    sumNat_moveAt i (i + 1) w'.content
                      (Nat.lt_of_succ_lt hiw') hc']
                  exact hdw)
              (by rw [content_halfR i (i + 1) cc v w hg hc,
                    content_halfR i (i + 1) cc v' w' hg' hc'])))))
  · have hz : ground.getAt 0 cc (i + 1) = 0 := Nat.eq_zero_of_not_pos hocc
    have hcT : (tensorH v w).content = cc := hg
    have hcF : (tensorH w v).content = cc := hgF
    have hnull : poly.unitTail (act i (i + 1) (tensorH v w)).coords :=
      act_unitTail (tensorH v w) i (i + 1) (tensorH_sized v w)
        (by rw [hcT]; exact Nat.lt_of_succ_lt hi) hij
        (by rw [hcT]; exact hi) (by rw [hcT]; exact hz)
    have hnullF : poly.unitTail (act i (i + 1) (tensorH w v)).coords :=
      act_unitTail (tensorH w v) i (i + 1) (tensorH_sized w v)
        (by rw [hcF]; exact Nat.lt_of_succ_lt hi) hij
        (by rw [hcF]; exact hi) (by rw [hcF]; exact hz)
    exact BPair.oneValue_trans
      (elim.dotP_null_tail_left _ _ hnullF)
      (BPair.oneValue_symm (elim.dotP_null_tail_left _ _ hnull))

/-- The index fold reads one value at a memberwise agreement. -/
private theorem famFold_ovAll (f g : Nat → BPair) : ∀ l : List Nat,
    (∀ i ∈ l, (f i).oneValue (g i)) →
    (ground.famFold BPair.add BPair.unit f l).oneValue
      (ground.famFold BPair.add BPair.unit g l)
  | [], _ => BPair.oneValue_refl _
  | a :: t, h =>
    BPair.add_congr (h a (List.Mem.head t))
      (famFold_ovAll f g t (fun i hi => h i (List.Mem.tail a hi)))

/-- The exchanged pair's stacked Gram entry reads the unexchanged
one: the pairing splits over the adjacent moves
(`dotP_stackedRaise`) and each move's term goes over
(`dotP_act_flip`). -/
private theorem dotP_stack_flip (cc : List Nat) (v w v' w' : HVec)
    (hsv : sized v) (hsw : sized w) (hsv' : sized v')
    (hsw' : sized w')
    (hlen : v.content.length = w.content.length)
    (hlen' : v'.content.length = w'.content.length)
    (hdv : sumNat v.content = sumNat v'.content)
    (hdw : sumNat w.content = sumNat w'.content)
    (hg : List.zipWith (fun x y => x + y) v.content w.content = cc)
    (hg' : List.zipWith (fun x y => x + y) v'.content w'.content
      = cc) :
    (elim.dotP
        (elim.matVec (units.stackedRaise cc) (tensorH w v).coords)
        (elim.matVec (units.stackedRaise cc)
          (tensorH w' v').coords)).oneValue
      (elim.dotP
        (elim.matVec (units.stackedRaise cc) (tensorH v w).coords)
        (elim.matVec (units.stackedRaise cc)
          (tensorH v' w').coords)) := by
  have hgF : List.zipWith (fun x y => x + y) w.content v.content
      = cc := by
    rw [ground.zipWith_add_comm w.content v.content]; exact hg
  have hgF' : List.zipWith (fun x y => x + y) w'.content v'.content
      = cc := by
    rw [ground.zipWith_add_comm w'.content v'.content]; exact hg'
  refine BPair.oneValue_trans
    (dotP_stackedRaise cc (tensorH w v) (tensorH w' v') hgF hgF'
      (tensorH_sized w v) (tensorH_sized w' v')) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm
      (dotP_stackedRaise cc (tensorH v w) (tensorH v' w') hg hg'
        (tensorH_sized v w) (tensorH_sized v' w')))
  refine famFold_ovAll _ _ (List.range (cc.length - 1)) ?_
  intro i hi
  exact dotP_act_flip i cc v w v' w' hsv hsw hsv' hsw' hlen hlen'
    hdv hdw hg hg'
    (ground.succ_lt_of_lt_pred (ground.ltOfMemRange hi))

/-! The exchanged enumeration: one pair list carrying the factors,
the display's own list and the exchanged list its two maps. -/

/-- The factor enumeration at a content: the first factors carried
by their own index type at a stated realization, the pairs
themselves, the guard the display's own.  The display's own
enumeration is the realization at the identity; the word tier's is
the realization at the word action. -/
def pairIdx {α : Type} (A : List α) (f : α → HVec)
    (B : List HVec) (cc : List Nat) : List (α × HVec) :=
  A.flatMap (fun v => B.flatMap (fun w =>
    if List.zipWith (fun x y => x + y) (f v).content w.content = cc
      then [(v, w)] else []))

/-- The exchanged pair list: the factor enumeration's members
tensored the other way round. -/
private def pairsFlip (A B : List HVec) (cc : List Nat) :
    List HVec :=
  (pairIdx A (fun v => v) B cc).map (fun p => tensorH p.2 p.1)

private theorem map_guardFlat {α γ : Type} (g : α × HVec → γ)
    (P : HVec → Prop) [DecidablePred P] (v : α) :
    ∀ B : List HVec,
      (B.flatMap (fun w => if P w then [(v, w)] else [])).map g
        = B.flatMap (fun w => if P w then [g (v, w)] else [])
  | [] => rfl
  | w :: t => by
    show (((if P w then [(v, w)] else []) ++ (t.flatMap (fun w =>
        if P w then [(v, w)] else []))).map g)
      = (if P w then [g (v, w)] else [])
        ++ t.flatMap (fun w => if P w then [g (v, w)] else [])
    rw [ground.map_append, map_guardFlat g P v t]
    by_cases h : P w
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl

private theorem pairIdx_mapAll {α γ : Type} (g : α × HVec → γ)
    (f : α → HVec)
    (cc : List Nat) : ∀ (A : List α) (B : List HVec),
      (pairIdx A f B cc).map g
        = A.flatMap (fun v => B.flatMap (fun w =>
            if List.zipWith (fun x y => x + y) (f v).content w.content
                = cc then [g (v, w)] else []))
  | [], _ => rfl
  | v :: t, B => by
    show ((B.flatMap (fun w =>
        if List.zipWith (fun x y => x + y) (f v).content w.content = cc
          then [(v, w)] else []) ++ pairIdx t f B cc).map g) = _
    rw [ground.map_append, map_guardFlat g _ v B,
      pairIdx_mapAll g f cc t B]
    rfl

/-- The display's pair list at a realized first-factor family is
the factor enumeration's own map. -/
private theorem pairsAt_pairIdxM {α : Type} (f : α → HVec)
    (A : List α) (B : List HVec) (cc : List Nat) :
    pairsAt (A.map f) B cc
      = (pairIdx A f B cc).map (fun p => tensorH (f p.1) p.2) := by
  rw [pairIdx_mapAll (fun p => tensorH (f p.1) p.2) f cc A B]
  show (A.map f).flatMap (fun v => B.flatMap (fun w =>
      if List.zipWith (fun x y => x + y) v.content w.content = cc
        then [tensorH v w] else [])) = _
  rw [ground.flatMap_map f _ A]

/-- The display's pair list is the factor enumeration's own map. -/
theorem pairsAt_pairIdx (A B : List HVec) (cc : List Nat) :
    pairsAt A B cc
      = (pairIdx A (fun v => v) B cc).map
        (fun p => tensorH p.1 p.2) := by
  have h := pairsAt_pairIdxM (fun v => v) A B cc
  rw [ground.map_id A] at h
  exact h

/-- Two realizations agreeing at the members' contents enumerate
one factor family: the guard reads the contents alone. -/
private theorem pairIdx_congr {α : Type} (f g : α → HVec)
    (B : List HVec) (cc : List Nat) :
    ∀ A : List α, (∀ v ∈ A, (f v).content = (g v).content) →
      pairIdx A f B cc = pairIdx A g B cc
  | [], _ => rfl
  | v :: t, h => by
    show B.flatMap (fun w =>
        if List.zipWith (fun x y => x + y) (f v).content w.content = cc
          then [(v, w)] else []) ++ pairIdx t f B cc
      = B.flatMap (fun w =>
        if List.zipWith (fun x y => x + y) (g v).content w.content = cc
          then [(v, w)] else []) ++ pairIdx t g B cc
    rw [h v (List.Mem.head t),
      pairIdx_congr f g B cc t
        (fun x hx => h x (List.Mem.tail v hx))]

/-- The factor enumeration's members sit in the two lists at the
guard. -/
theorem pairIdx_mem {α : Type} {A : List α} {f : α → HVec}
    {B : List HVec} {cc : List Nat}
    {p : α × HVec} (h : p ∈ pairIdx A f B cc) :
    p.1 ∈ A ∧ p.2 ∈ B
      ∧ List.zipWith (fun x y => x + y) (f p.1).content p.2.content
        = cc := by
  have h0 : p ∈ A.flatMap (fun v => B.flatMap (fun w =>
      if List.zipWith (fun x y => x + y) (f v).content w.content = cc
        then [(v, w)] else [])) := h
  obtain ⟨v, hv, hp⟩ := ground.mem_flatMap_of _ A p h0
  obtain ⟨w, hw, hpw⟩ := ground.mem_flatMap_of _ B p hp
  by_cases hgd : List.zipWith (fun x y => x + y) (f v).content
      w.content = cc
  · rw [if_pos hgd] at hpw
    have hpe : p = (v, w) := by
      match hpw with
      | List.Mem.head _ => rfl
      | List.Mem.tail _ h2 => nomatch h2
    rw [hpe]
    exact ⟨hv, hw, hgd⟩
  · rw [if_neg hgd] at hpw
    nomatch hpw

/-- The read family's seed. -/
private def hvNil : HVec := ⟨[], []⟩

/-- The factor enumeration's key reads: the pair at a key sits in
the two lists at the guard. -/
private theorem pairIdx_read {α : Type} (e : α) (A : List α)
    (f : α → HVec) (B : List HVec) (cc : List Nat)
    (k : Nat) (hk : k < (pairIdx A f B cc).length) :
    (ground.getAt (e, hvNil) (pairIdx A f B cc) k).1 ∈ A
      ∧ (ground.getAt (e, hvNil) (pairIdx A f B cc) k).2 ∈ B
      ∧ List.zipWith (fun x y => x + y)
          (f (ground.getAt (e, hvNil) (pairIdx A f B cc) k).1).content
          (ground.getAt (e, hvNil) (pairIdx A f B cc) k).2.content
        = cc :=
  pairIdx_mem (ground.mem_getAt (e, hvNil) (pairIdx A f B cc) k hk)

/-- The realized display's width is the factor enumeration's. -/
private theorem length_pairsAtIdxM {α : Type} (A : List α)
    (f : α → HVec) (B : List HVec) (cc : List Nat) :
    (pairsAt (A.map f) B cc).length = (pairIdx A f B cc).length := by
  rw [pairsAt_pairIdxM f A B cc, ground.length_map]

theorem length_pairsAtIdx (A B : List HVec)
    (cc : List Nat) :
    (pairsAt A B cc).length = (pairIdx A (fun v => v) B cc).length := by
  rw [pairsAt_pairIdx A B cc, ground.length_map]

private theorem length_pairsFlip (A B : List HVec) (cc : List Nat) :
    (pairsFlip A B cc).length
      = (pairIdx A (fun v => v) B cc).length :=
  ground.length_map _ _

/-- The realized display's coordinate row at a key is the enumerated
pair's own tensor. -/
private theorem getAt_pairsCoordsM {α : Type} (e : α) (A : List α)
    (f : α → HVec) (B : List HVec) (cc : List Nat)
    (k : Nat) (hk : k < (pairIdx A f B cc).length) :
    ground.getAt [] ((pairsAt (A.map f) B cc).map HVec.coords) k
      = (tensorH
          (f (ground.getAt (e, hvNil) (pairIdx A f B cc) k).1)
          (ground.getAt (e, hvNil) (pairIdx A f B cc) k).2).coords := by
  have hkl : k < (pairsAt (A.map f) B cc).length := by
    rw [length_pairsAtIdxM A f B cc]; exact hk
  rw [ground.getAt_map hvNil ([] : List BPair) HVec.coords
      (pairsAt (A.map f) B cc) k hkl,
    pairsAt_pairIdxM f A B cc,
    ground.getAt_map (e, hvNil) hvNil
      (fun p => tensorH (f p.1) p.2) (pairIdx A f B cc) k hk]

private theorem getAt_pairsCoords (A B : List HVec) (cc : List Nat)
    (k : Nat) (hk : k < (pairIdx A (fun v => v) B cc).length) :
    ground.getAt [] ((pairsAt A B cc).map HVec.coords) k
      = (tensorH
          (ground.getAt (hvNil, hvNil)
            (pairIdx A (fun v => v) B cc) k).1
          (ground.getAt (hvNil, hvNil)
            (pairIdx A (fun v => v) B cc) k).2).coords := by
  have hkl : k < (pairsAt A B cc).length := by
    rw [length_pairsAtIdx A B cc]; exact hk
  rw [ground.getAt_map hvNil ([] : List BPair) HVec.coords
      (pairsAt A B cc) k hkl,
    pairsAt_pairIdx A B cc,
    ground.getAt_map (hvNil, hvNil) hvNil
      (fun p => tensorH p.1 p.2) (pairIdx A (fun v => v) B cc) k hk]

private theorem getAt_flipCoords (A B : List HVec) (cc : List Nat)
    (k : Nat) (hk : k < (pairIdx A (fun v => v) B cc).length) :
    ground.getAt [] ((pairsFlip A B cc).map HVec.coords) k
      = (tensorH
          (ground.getAt (hvNil, hvNil)
            (pairIdx A (fun v => v) B cc) k).2
          (ground.getAt (hvNil, hvNil)
            (pairIdx A (fun v => v) B cc) k).1).coords := by
  have hkl : k < (pairsFlip A B cc).length := by
    rw [length_pairsFlip A B cc]; exact hk
  rw [ground.getAt_map hvNil ([] : List BPair) HVec.coords
      (pairsFlip A B cc) k hkl,
    show pairsFlip A B cc
        = (pairIdx A (fun v => v) B cc).map
          (fun p => tensorH p.2 p.1) from rfl,
    ground.getAt_map (hvNil, hvNil) hvNil
      (fun p => tensorH p.2 p.1) (pairIdx A (fun v => v) B cc) k hk]

/-- The exchanged list's members sit at the stated content's own
width. -/
private theorem pairsFlip_coordLen (A B : List HVec)
    (cc : List Nat) :
    ∀ u ∈ pairsFlip A B cc,
      u.coords.length = (monomialsAt cc).length := by
  intro u hu
  have hu0 : u ∈ (pairIdx A (fun v => v) B cc).map
      (fun p => tensorH p.2 p.1) := hu
  obtain ⟨p, hp, hpu⟩ :=
    ground.mem_map_of _ (pairIdx A (fun v => v) B cc) u hu0
  obtain ⟨_, _, hgd⟩ := pairIdx_mem hp
  rw [← hpu]
  show (tensorH p.2 p.1).coords.length = _
  rw [tensorH_sized p.2 p.1]
  show (monomialsAt (List.zipWith (fun x y => x + y) p.2.content
    p.1.content)).length = _
  rw [ground.zipWith_add_comm p.2.content p.1.content, hgd]

/-- The exchanged list's plain Gram entry reads the display's
own. -/
private theorem pairsFlip_gramPlain (A B : List HVec)
    (cc : List Nat) (d kA kB : Nat)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hdegB : ∀ w ∈ B, sumNat w.content = kB)
    (k l : Nat) (hk : k < (pairIdx A (fun v => v) B cc).length)
    (hl : l < (pairIdx A (fun v => v) B cc).length) :
    (elim.dotP
        (ground.getAt [] ((pairsFlip A B cc).map HVec.coords) k)
        (ground.getAt []
          ((pairsFlip A B cc).map HVec.coords) l)).oneValue
      (elim.dotP
        (ground.getAt [] ((pairsAt A B cc).map HVec.coords) k)
        (ground.getAt []
          ((pairsAt A B cc).map HVec.coords) l)) := by
  obtain ⟨hvA, hwB, hgd⟩ :=
    pairIdx_read hvNil A (fun v => v) B cc k hk
  obtain ⟨hvA', hwB', hgd'⟩ :=
    pairIdx_read hvNil A (fun v => v) B cc l hl
  rw [getAt_flipCoords A B cc k hk, getAt_flipCoords A B cc l hl,
    getAt_pairsCoords A B cc k hk, getAt_pairsCoords A B cc l hl]
  exact dotP_tensorH_flip _ _ _ _ (hszA _ hvA) (hszB _ hwB)
    (hszA _ hvA') (hszB _ hwB')
    ((hwidA _ hvA).trans (hwidB _ hwB).symm)
    ((hwidA _ hvA').trans (hwidB _ hwB').symm)
    ((hdegA _ hvA).trans (hdegA _ hvA').symm)
    ((hdegB _ hwB).trans (hdegB _ hwB').symm)
    (by show List.zipWith (fun x y => x + y) _ _
          = List.zipWith (fun x y => x + y) _ _
        rw [hgd, hgd'])

/-- The exchanged list's stacked Gram entry reads the display's
own. -/
private theorem pairsFlip_gramStack (A B : List HVec)
    (cc : List Nat) (d kA kB : Nat)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hdegB : ∀ w ∈ B, sumNat w.content = kB)
    (k l : Nat) (hk : k < (pairIdx A (fun v => v) B cc).length)
    (hl : l < (pairIdx A (fun v => v) B cc).length) :
    (elim.dotP
        (elim.matVec (units.stackedRaise cc) (ground.getAt []
          ((pairsFlip A B cc).map HVec.coords) k))
        (elim.matVec (units.stackedRaise cc) (ground.getAt []
          ((pairsFlip A B cc).map HVec.coords) l))).oneValue
      (elim.dotP
        (elim.matVec (units.stackedRaise cc) (ground.getAt []
          ((pairsAt A B cc).map HVec.coords) k))
        (elim.matVec (units.stackedRaise cc) (ground.getAt []
          ((pairsAt A B cc).map HVec.coords) l))) := by
  obtain ⟨hvA, hwB, hgd⟩ :=
    pairIdx_read hvNil A (fun v => v) B cc k hk
  obtain ⟨hvA', hwB', hgd'⟩ :=
    pairIdx_read hvNil A (fun v => v) B cc l hl
  rw [getAt_flipCoords A B cc k hk, getAt_flipCoords A B cc l hl,
    getAt_pairsCoords A B cc k hk, getAt_pairsCoords A B cc l hl]
  exact dotP_stack_flip cc _ _ _ _ (hszA _ hvA) (hszB _ hwB)
    (hszA _ hvA') (hszB _ hwB')
    ((hwidA _ hvA).trans (hwidB _ hwB).symm)
    ((hwidA _ hvA').trans (hwidB _ hwB').symm)
    ((hdegA _ hvA).trans (hdegA _ hvA').symm)
    ((hdegB _ hwB).trans (hdegB _ hwB').symm) hgd hgd'

private theorem pairsFlip_rowsLen (A B : List HVec) (cc : List Nat) :
    elim.rowsLen (monomialsAt cc).length
      ((pairsFlip A B cc).map HVec.coords) :=
  elim.rowsLen_map HVec.coords (monomialsAt cc).length
    (pairsFlip A B cc) (pairsFlip_coordLen A B cc)

/-- The exchanged list is independent exactly where the display's
list is: the two plain Grams agree entry by entry, so a null
combination's self-pairing transports across them
(`elim.dotP_comboGram` at the scales one and one), the positive
pairing withdraws it on the display's side, and the display's own
independence reads the coefficients back. -/
private theorem pairsFlip_indep (A B : List HVec) (cc : List Nat)
    (d kA kB : Nat)
    (hszA : ∀ v ∈ A, sized v) (hszB : ∀ w ∈ B, sized w)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hdegB : ∀ w ∈ B, sumNat w.content = kB)
    (hind : elim.indepRows (monomialsAt cc).length
      ((pairsAt A B cc).map HVec.coords)) :
    elim.indepRows (monomialsAt cc).length
      ((pairsFlip A B cc).map HVec.coords) := by
  have hrowsF := pairsFlip_rowsLen A B cc
  have hlenF : ((pairsFlip A B cc).map HVec.coords).length
      = ((pairsAt A B cc).map HVec.coords).length := by
    rw [ground.length_map, ground.length_map,
      length_pairsFlip A B cc, length_pairsAtIdx A B cc]
  have hgram : ∀ k, k < ((pairsAt A B cc).map HVec.coords).length →
      ∀ l, l < ((pairsAt A B cc).map HVec.coords).length →
      (BPair.ofNat 1 * elim.dotP
          (ground.getAt [] ((pairsFlip A B cc).map HVec.coords) k)
          (ground.getAt []
            ((pairsFlip A B cc).map HVec.coords) l)).oneValue
        (BPair.ofNat 1 * elim.dotP
          (ground.getAt [] ((pairsAt A B cc).map HVec.coords) k)
          (ground.getAt []
            ((pairsAt A B cc).map HVec.coords) l)) := by
    intro k hk l hl
    rw [ground.length_map, length_pairsAtIdx A B cc] at hk
    rw [ground.length_map, length_pairsAtIdx A B cc] at hl
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (pairsFlip_gramPlain A B cc d kA kB hszA hszB hwidA hwidB
        hdegA hdegB k l hk hl)
  refine elim.indep_intro (monomialsAt cc).length _ hrowsF ?_
  intro cs hcs hnull
  have htr := elim.dotP_comboGram (monomialsAt cc).length
    (BPair.ofNat 1) (BPair.ofNat 1)
    ((pairsAt A B cc).map HVec.coords)
    ((pairsFlip A B cc).map HVec.coords) hind.1 hrowsF hlenF hgram cs
  have hself := elim.dotP_null_tail_left
    (elim.combo (monomialsAt cc).length cs
      ((pairsFlip A B cc).map HVec.coords))
    (elim.combo (monomialsAt cc).length cs
      ((pairsFlip A B cc).map HVec.coords)) hnull
  exact elim.indep_elim hind cs (hcs.trans hlenF)
    (elim.dotP_self_null _
      (ground.mul_cancel_unit BPair.ofNat_one_off
        (BPair.oneValue_trans (BPair.oneValue_symm htr)
          (elim.oneValue_mul_unit _ _ hself))))

/-- The exchanged list's members are the exchanged display's own:
the guard is symmetric in the two contents. -/
private theorem pairsFlip_mem_pairsAt {A B : List HVec}
    {cc : List Nat} {u : HVec} (h : u ∈ pairsFlip A B cc) :
    u ∈ pairsAt B A cc := by
  have h0 : u ∈ (pairIdx A (fun v => v) B cc).map
      (fun p => tensorH p.2 p.1) := h
  obtain ⟨p, hp, hpu⟩ :=
    ground.mem_map_of _ (pairIdx A (fun v => v) B cc) u h0
  obtain ⟨hvA, hwB, hgd⟩ := pairIdx_mem hp
  have hgdF : List.zipWith (fun x y => x + y) p.2.content p.1.content
      = cc := by
    rw [ground.zipWith_add_comm p.2.content p.1.content]; exact hgd
  refine ground.mem_flatMap_to _ hwB
    (ground.mem_flatMap_to _ hvA ?_)
  rw [if_pos hgdF, ← hpu]
  exact List.Mem.head []

/-- The exchanged display's members are the exchanged list's
own. -/
private theorem pairsAt_mem_pairsFlip {A B : List HVec}
    {cc : List Nat} {u : HVec} (h : u ∈ pairsAt B A cc) :
    u ∈ pairsFlip A B cc := by
  obtain ⟨w, v, hwB, hvA, hgd, hvw⟩ := pairs_mem h
  have hgdF : List.zipWith (fun x y => x + y) v.content w.content
      = cc := by
    rw [ground.zipWith_add_comm v.content w.content]; exact hgd
  have hpi : (v, w) ∈ pairIdx A (fun v => v) B cc := by
    refine ground.mem_flatMap_to _ hvA
      (ground.mem_flatMap_to _ hwB ?_)
    rw [if_pos hgdF]
    exact List.Mem.head []
  have hm := ground.mem_map_to (fun p => tensorH p.2 p.1) hpi
  show u ∈ (pairIdx A (fun v => v) B cc).map
    (fun p => tensorH p.2 p.1)
  rw [← hvw]
  exact hm

/-- `lem:blockcount`(iii)'s first identity at the pair lists: the
exchanged display reads one kernel dimension with the display.  The
exchange sends each pair to the exchanged pair at the commuted
coordinate products, so the two stacked Grams agree at a matched
enumeration (`elim.kernelDim_gram`), and the exchanged enumeration
and the exchanged display carry the same members, two independent
lists of one span (`elim.kernelDim_congr`). -/
theorem kernelDim_pairs_comm (A B : List HVec) (cc : List Nat)
    (d kA kB : Nat)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d)
    (hdegA : ∀ v ∈ A, sumNat v.content = kA)
    (hdegB : ∀ w ∈ B, sumNat w.content = kB)
    (hiA : indepAll A) (hiB : indepAll B) :
    elim.kernelDim (pairsAt A B cc).length
        (elim.crossM (units.stackedRaise cc)
          ((pairsAt A B cc).map HVec.coords))
      = elim.kernelDim (pairsAt B A cc).length
        (elim.crossM (units.stackedRaise cc)
          ((pairsAt B A cc).map HVec.coords)) := by
  have hszA : ∀ v ∈ A, sized v := sized_of_indepAll A hiA
  have hszB : ∀ w ∈ B, sized w := sized_of_indepAll B hiB
  have hindAB := tensor_indep A B cc d kA hwidA hwidB hdegA hiA hiB
  have hindBA := tensor_indep B A cc d kB hwidB hwidA hdegB hiB hiA
  have hindFL := pairsFlip_indep A B cc d kA kB hszA hszB hwidA
    hwidB hdegA hdegB hindAB
  have hrowsBA : elim.rowsLen (monomialsAt cc).length
      ((pairsAt B A cc).map HVec.coords) := hindBA.1
  have hlenFL : ((pairsFlip A B cc).map HVec.coords).length
      = ((pairsAt A B cc).map HVec.coords).length := by
    rw [ground.length_map, ground.length_map,
      length_pairsFlip A B cc, length_pairsAtIdx A B cc]
  have hstep1 := elim.kernelDim_gram (monomialsAt cc).length
    (units.stackedRaise cc) ((pairsAt A B cc).map HVec.coords)
    ((pairsFlip A B cc).map HVec.coords)
    (BPair.ofNat 1) (BPair.ofNat 1)
    BPair.ofNat_one_off BPair.ofNat_one_off
    (units.rowsLen_stackedRaise cc) hindAB.1 hindFL.1 hlenFL
    (by
      intro k hk l hl
      rw [ground.length_map, length_pairsAtIdx A B cc] at hk
      rw [ground.length_map, length_pairsAtIdx A B cc] at hl
      exact BPair.mul_congr (BPair.oneValue_refl _)
        (pairsFlip_gramStack A B cc d kA kB hszA hszB hwidA hwidB
          hdegA hdegB k l hk hl))
  have hstep2 := elim.kernelDim_congr (monomialsAt cc).length
    (units.stackedRaise cc) ((pairsFlip A B cc).map HVec.coords)
    ((pairsAt B A cc).map HVec.coords)
    (units.rowsLen_stackedRaise cc) hindFL.1 hrowsBA hindFL hindBA
    (by
      intro k hk
      rw [ground.length_map] at hk
      rw [ground.getAt_map hvNil ([] : List BPair) HVec.coords
        (pairsFlip A B cc) k hk]
      exact span_of_mem (pairsAt B A cc) cc _
        (pairsFlip_mem_pairsAt
          (ground.mem_getAt hvNil (pairsFlip A B cc) k hk))
        hrowsBA)
    (by
      intro k hk
      rw [ground.length_map] at hk
      rw [ground.getAt_map hvNil ([] : List BPair) HVec.coords
        (pairsAt B A cc) k hk]
      exact span_of_mem (pairsFlip A B cc) cc _
        (pairsAt_mem_pairsFlip
          (ground.mem_getAt hvNil (pairsAt B A cc) k hk))
        hindFL.1)
  rw [← ground.length_map HVec.coords (pairsAt A B cc),
    ← ground.length_map HVec.coords (pairsAt B A cc),
    ← hstep1, hstep2]

/-! `lem:blockcount`(iii)'s cross-top tier (the transport passage's
"one word family at the shape's own top"): one word family read at
two tops of one content, tensored against one shared pool.  The
pairs' plain Grams and their stacked Grams transport across the two
tops at the cross-multiplied self-pairings — the first factors'
word pairings the walk's own reads (`wordGram`, `wordGramRaise`,
`wordGramRaise2`), the shared second factors' pairings one value on
both sides, and the distinct-first-content arms at the sum's unit
on both sides — so the two enumerations read one kernel
dimension. -/

/-- A word's image either keeps the seed's degree or reads the
sum's unit outright: an occupied source letter moves the content at
the degree (`sumNat_moveAt`), and a vacant one sends the whole
image to the unit family (`act_unitTail`).  The vacancy is the
content's own read, so two tops of one content collapse
together. -/
private theorem wact_deg_or_null : ∀ (ws c : List Nat),
    (∀ l ∈ ws, l + 1 < c.length) →
    sumNat (wcontent ws c) = sumNat c
      ∨ ∀ z : HVec, sized z → z.content = c →
          poly.unitTail (wact ws z).coords
  | [], _, _ => Or.inl rfl
  | l :: t, c, hb => by
    have hlt : l + 1 < c.length := hb l (List.Mem.head t)
    have hlw : l + 1 < (wcontent t c).length := by
      rw [wcontent_len]; exact hlt
    match wact_deg_or_null t c
        (fun x hx => hb x (List.Mem.tail l hx)) with
    | .inr hnull =>
      refine .inr (fun z hsz hzc => ?_)
      show poly.unitTail (elim.matVec (units.matUnitAt
        (moveAt (l + 1) l (wact t z).content) (wact t z).content
        (l + 1) l) (wact t z).coords)
      exact elim.matVec_null _ _ (hnull z hsz hzc)
    | .inl hdeg =>
      by_cases hocc : 0 < ground.getAt 0 (wcontent t c) l
      · refine .inl ?_
        show sumNat (moveAt (l + 1) l (wcontent t c)) = sumNat c
        rw [sumNat_moveAt (l + 1) l (wcontent t c) hlw hocc]
        exact hdeg
      · refine .inr (fun z hsz hzc => ?_)
        have hzc' : (wact t z).content = wcontent t c := by
          rw [wact_content, hzc]
        show poly.unitTail (act (l + 1) l (wact t z)).coords
        exact act_unitTail (wact t z) (l + 1) l
          (wact_sized t z hsz)
          (by rw [hzc']; exact hlw)
          (fun he => Nat.ne_of_lt (Nat.lt_succ_self l) he.symm)
          (by rw [hzc', wcontent_len]
              exact Nat.lt_of_succ_lt hlt)
          (by rw [hzc']; exact Nat.eq_zero_of_not_pos hocc)

/-- The word image's content at a top, the chain read at the top's
own content. -/
theorem wact_content_len (ws : List Nat) (x : HVec) :
    (wact ws x).content.length = x.content.length := by
  rw [wact_content, wcontent_len]

/-- The pairing of two families at a scale each reads the sum's
unit where the two pairings do. -/
private theorem mulScale_null (S S' X X' : BPair)
    (h : X.oneValue BPair.unit) (h' : X'.oneValue BPair.unit) :
    (X * S).oneValue (X' * S') :=
  BPair.oneValue_trans (elim.oneValue_unit_mul h)
    (BPair.oneValue_symm (elim.oneValue_unit_mul h'))

/-- A pair of tensors transports across two first factors at the
scales exactly where the first factors' own pairing does: at one
first content the pairing factorizes (`dotP_tensorH`), the shared
second factors' pairing the same value on both sides, and at
distinct first contents both sides read the sum's unit
(`dotP_tensorH_off`) — the two first-factor families at one content
per member, so the arms align across them. -/
private theorem dotP_tensorCross (a a' b b' y y' : HVec)
    (S S' : BPair)
    (hsa : sized a) (hsa' : sized a') (hsb : sized b)
    (hsb' : sized b') (hsy : sized y) (hsy' : sized y')
    (hab : a.content = b.content) (hab' : a'.content = b'.content)
    (hla : a.content.length = y.content.length)
    (hla' : a'.content.length = y'.content.length)
    (hdeg : sumNat a.content = sumNat a'.content)
    (hcc : (tensorH a y).content = (tensorH a' y').content)
    (htr : a.content = a'.content →
      (elim.dotP a.coords a'.coords * S).oneValue
        (elim.dotP b.coords b'.coords * S')) :
    (elim.dotP (tensorH a y).coords (tensorH a' y').coords
        * S).oneValue
      (elim.dotP (tensorH b y).coords (tensorH b' y').coords
        * S') := by
  have hlb : b.content.length = y.content.length := by
    rw [← hab]; exact hla
  have hlb' : b'.content.length = y'.content.length := by
    rw [← hab']; exact hla'
  by_cases haa : a.content = a'.content
  · have hbb : b.content = b'.content := by
      rw [← hab, ← hab']; exact haa
    have hcc0 : List.zipWith (fun x y => x + y) a.content y.content
        = List.zipWith (fun x y => x + y) a'.content y'.content := hcc
    have hyy : y.content = y'.content :=
      zipWith_add_cancelL a.content y.content y'.content
        a.content.length rfl hla.symm
        (by rw [← hla']; exact congrArg List.length haa.symm)
        (by rw [hcc0, haa])
    have hT := dotP_tensorH a y a' y' hsa hsy hsa' hsy' hla haa hyy
    have hU := dotP_tensorH b y b' y' hsb hsy hsb' hsy' hlb hbb hyy
    refine BPair.oneValue_trans (BPair.mul_congr_left hT) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left hU) ?_
    rw [BPair.mul_assoc, BPair.mul_assoc,
      BPair.mul_comm (elim.dotP y.coords y'.coords) S,
      BPair.mul_comm (elim.dotP y.coords y'.coords) S',
      ← BPair.mul_assoc, ← BPair.mul_assoc]
    exact BPair.oneValue_symm
      (BPair.mul_congr_left (htr haa))
  · have hbb : ¬ b.content = b'.content := by
      intro he
      refine haa ?_
      rw [hab, hab']
      exact he
    have hnullT := dotP_tensorH_off a y a' y' hla hla' hdeg hcc haa
    have hnullU := dotP_tensorH_off b y b' y' hlb hlb'
      (by rw [← hab, ← hab']; exact hdeg)
      (by show List.zipWith (fun x y => x + y) b.content y.content
              = List.zipWith (fun x y => x + y) b'.content y'.content
          rw [← hab, ← hab']
          exact hcc)
      hbb
    exact mulScale_null S S' _ _ hnullT hnullU


/-- The plain cross-top pair Gram (`lem:blockcount`(iii)'s transport
sentence, the fold's coefficient against its top's self-pairing):
two word images at one top, tensored against two members of the
shared pool, pair against the second top's self-pairing exactly as
the same two words' images at the second top pair against the
first's.  The matched-first-content arm factorizes at
`dotP_tensorH` with the first factors' transport `wordGram` and the
shared second factors' one pairing; the distinct-first-content arm
reads the sum's unit on both sides; and a word whose walk meets a
vacant letter sends both sides to the unit family outright, the
vacancy the shared content's own read. -/
private theorem dotP_pairWords (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u) (hdt : t.content.length = d)
    (hcu : t.content = u.content)
    (htopt : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j t).coords)
    (htopu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (ws ws' : List Nat) (hb : ∀ l ∈ ws, l + 1 < d)
    (hb' : ∀ l ∈ ws', l + 1 < d)
    (y y' : HVec) (hsy : sized y) (hsy' : sized y')
    (hwy : y.content.length = d) (hwy' : y'.content.length = d)
    (dd : List Nat)
    (hg : List.zipWith (fun x y => x + y) (wact ws t).content
      y.content = dd)
    (hg' : List.zipWith (fun x y => x + y) (wact ws' t).content
      y'.content = dd) :
    (elim.dotP (tensorH (wact ws t) y).coords
        (tensorH (wact ws' t) y').coords
        * elim.dotP u.coords u.coords).oneValue
      (elim.dotP (tensorH (wact ws u) y).coords
        (tensorH (wact ws' u) y').coords
        * elim.dotP t.coords t.coords) := by
  have hcwT : ∀ z : List Nat, (wact z u).content = (wact z t).content := by
    intro z
    rw [wact_content, wact_content, hcu]
  have hbt : ∀ l ∈ ws, l + 1 < t.content.length := by
    intro l hl; rw [hdt]; exact hb l hl
  have hbt' : ∀ l ∈ ws', l + 1 < t.content.length := by
    intro l hl; rw [hdt]; exact hb' l hl
  have hltY : (wact ws t).content.length = y.content.length := by
    rw [wact_content_len, hdt, hwy]
  have hltY' : (wact ws' t).content.length = y'.content.length := by
    rw [wact_content_len, hdt, hwy']
  have hluY : (wact ws u).content.length = y.content.length := by
    rw [wact_content_len, ← hcu, hdt, hwy]
  have hluY' : (wact ws' u).content.length = y'.content.length := by
    rw [wact_content_len, ← hcu, hdt, hwy']
  match wact_deg_or_null ws t.content hbt,
      wact_deg_or_null ws' t.content hbt' with
  | .inr hn, _ =>
    exact mulScale_null _ _ _ _
      (elim.dotP_null_tail_left _ _
        ((tensorH_unitTail (wact ws t) y (wact_sized ws t hst) hsy
          hltY).mpr (Or.inl (hn t hst rfl))))
      (elim.dotP_null_tail_left _ _
        ((tensorH_unitTail (wact ws u) y (wact_sized ws u hsu) hsy
          hluY).mpr (Or.inl (hn u hsu hcu.symm))))
  | _, .inr hn' =>
    exact mulScale_null _ _ _ _
      (elim.dotP_null_tail_right _ _
        ((tensorH_unitTail (wact ws' t) y' (wact_sized ws' t hst)
          hsy' hltY').mpr (Or.inl (hn' t hst rfl))))
      (elim.dotP_null_tail_right _ _
        ((tensorH_unitTail (wact ws' u) y' (wact_sized ws' u hsu)
          hsy' hluY').mpr (Or.inl (hn' u hsu hcu.symm))))
  | .inl hdg, .inl hdg' =>
    refine dotP_tensorCross (wact ws t) (wact ws' t) (wact ws u)
      (wact ws' u) y y' _ _
      (wact_sized ws t hst) (wact_sized ws' t hst)
      (wact_sized ws u hsu) (wact_sized ws' u hsu) hsy hsy'
      (hcwT ws).symm (hcwT ws').symm hltY hltY'
      (by rw [wact_content ws t, wact_content ws' t, hdg, hdg'])
      (by show List.zipWith (fun x y => x + y) (wact ws t).content
              y.content
            = List.zipWith (fun x y => x + y) (wact ws' t).content
              y'.content
          rw [hg, hg'])
      ?_
    intro hmm
    exact wordGram d t u hst hsu hdt hcu htopt htopu ws ws' hb hb'
      hmm

/-- The first factor's raised half at a stated guard content: two
first factors of one content share the guard, so the halves read
with one test. -/
private theorem raiseHalfL_guard (i n : Nat) (v v' w : HVec)
    (hc : v'.content = v.content) :
    raiseHalfL i n v' w
      = (if 0 < ground.getAt 0 v.content (i + 1)
          then (tensorH (act i (i + 1) v') w).coords
          else List.replicate n BPair.unit) := by
  show (if 0 < ground.getAt 0 v'.content (i + 1)
      then (tensorH (act i (i + 1) v') w).coords
      else List.replicate n BPair.unit) = _
  rw [hc]

/-- The second factor's raised half reads its own guard, the shared
factor's own. -/
private theorem raiseHalfR_unfold (i n : Nat) (v w : HVec) :
    raiseHalfR i n v w
      = (if 0 < ground.getAt 0 w.content (i + 1)
          then (tensorH v (act i (i + 1) w)).coords
          else List.replicate n BPair.unit) := rfl

/-- One crossed term of the Leibniz split transports at the scales
where its two guards pass, and reads the sum's unit at both scales
where either fails — the guards the shared contents' own tests. -/
private theorem dotP_halfCross (n : Nat) (c c' : Prop)
    [Decidable c] [Decidable c'] (S S' : BPair)
    (P Q P' Q' : List BPair)
    (hall : c → c' →
      (elim.dotP P Q * S).oneValue (elim.dotP P' Q' * S')) :
    (elim.dotP (if c then P else List.replicate n BPair.unit)
        (if c' then Q else List.replicate n BPair.unit)
        * S).oneValue
      (elim.dotP (if c then P' else List.replicate n BPair.unit)
        (if c' then Q' else List.replicate n BPair.unit) * S') := by
  by_cases h : c
  · by_cases h' : c'
    · rw [show (if c then P else List.replicate n BPair.unit)
            = P from if_pos h,
        show (if c then P' else List.replicate n BPair.unit)
            = P' from if_pos h,
        show (if c' then Q else List.replicate n BPair.unit)
            = Q from if_pos h',
        show (if c' then Q' else List.replicate n BPair.unit)
            = Q' from if_pos h']
      exact hall h h'
    · rw [show (if c' then Q else List.replicate n BPair.unit)
            = List.replicate n BPair.unit from if_neg h',
        show (if c' then Q' else List.replicate n BPair.unit)
            = List.replicate n BPair.unit from if_neg h']
      exact mulScale_null S S' _ _
        (elim.dotP_null_tail_right _ _ (poly.unitTail_replicate n))
        (elim.dotP_null_tail_right _ _ (poly.unitTail_replicate n))
  · rw [show (if c then P else List.replicate n BPair.unit)
          = List.replicate n BPair.unit from if_neg h,
      show (if c then P' else List.replicate n BPair.unit)
          = List.replicate n BPair.unit from if_neg h]
    exact mulScale_null S S' _ _
      (elim.dotP_null_tail_left _ _ (poly.unitTail_replicate n))
      (elim.dotP_null_tail_left _ _ (poly.unitTail_replicate n))

/-- The four-term sum's scale distributes term by term. -/
private theorem mul4_distrib (A B C D S : BPair) :
    (A + B + (C + D)) * S = A * S + B * S + (C * S + D * S) := by
  rw [BPair.right_distrib, BPair.right_distrib, BPair.right_distrib]

/-- One adjacent raising's cross-top pairing (`lem:blockcount`(iii)'s
transport sentence, each fold the word pairings' coefficient against
its top's self-pairing): the Leibniz split's four crossed terms go
over one at a time — the two first factors raised at
`wordGramRaise2`, one side raised at `wordGramRaise`, neither at
`wordGram` — each term's shared second factors carrying one pairing
across the tops, and a vacant target sending both sides to the sum's
unit. -/
private theorem dotP_actPair_words (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u) (hdt : t.content.length = d)
    (hcu : t.content = u.content)
    (htopt : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j t).coords)
    (htopu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (ws ws' : List Nat) (hb : ∀ l ∈ ws, l + 1 < d)
    (hb' : ∀ l ∈ ws', l + 1 < d)
    (hdeg : sumNat (wact ws t).content = sumNat (wact ws' t).content)
    (y y' : HVec) (hsy : sized y) (hsy' : sized y')
    (hwy : y.content.length = d) (hwy' : y'.content.length = d)
    (dd : List Nat)
    (hg : List.zipWith (fun x y => x + y) (wact ws t).content
      y.content = dd)
    (hg' : List.zipWith (fun x y => x + y) (wact ws' t).content
      y'.content = dd)
    (i : Nat) (hi : i + 1 < dd.length) :
    (elim.dotP (act i (i + 1) (tensorH (wact ws t) y)).coords
        (act i (i + 1) (tensorH (wact ws' t) y')).coords
        * elim.dotP u.coords u.coords).oneValue
      (elim.dotP (act i (i + 1) (tensorH (wact ws u) y)).coords
        (act i (i + 1) (tensorH (wact ws' u) y')).coords
        * elim.dotP t.coords t.coords) := by
  have hij : ¬ i = i + 1 := Nat.ne_of_lt (Nat.lt_succ_self i)
  have hcwT : ∀ z : List Nat, (wact z u).content = (wact z t).content := by
    intro z
    rw [wact_content, wact_content, hcu]
  have hltd : (wact ws t).content.length = d := by
    rw [wact_content_len, hdt]
  have hltd' : (wact ws' t).content.length = d := by
    rw [wact_content_len, hdt]
  have hlud : (wact ws u).content.length = d := by
    rw [wact_content_len, ← hcu, hdt]
  have hlud' : (wact ws' u).content.length = d := by
    rw [wact_content_len, ← hcu, hdt]
  have hltY : (wact ws t).content.length = y.content.length := by
    rw [hltd, hwy]
  have hltY' : (wact ws' t).content.length = y'.content.length := by
    rw [hltd', hwy']
  have hluY : (wact ws u).content.length = y.content.length := by
    rw [hlud, hwy]
  have hluY' : (wact ws' u).content.length = y'.content.length := by
    rw [hlud', hwy']
  have hddlen : dd.length = d := by
    rw [← hg]
    exact ground.length_zipWith (fun x y => x + y) _ _ d hltd hwy
  have hid : i + 1 < d := by rw [← hddlen]; exact hi
  have hgu : List.zipWith (fun x y => x + y) (wact ws u).content
      y.content = dd := by
    rw [hcwT ws]; exact hg
  have hgu' : List.zipWith (fun x y => x + y) (wact ws' u).content
      y'.content = dd := by
    rw [hcwT ws']; exact hg'
  by_cases hocc : 0 < ground.getAt 0 dd (i + 1)
  · have hredT := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) dd)).length dd (wact ws t) y
      (wact_sized ws t hst) hsy hltY (by rw [hltd]; exact hid) hg
      hocc rfl
    have hredT' := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) dd)).length dd (wact ws' t) y'
      (wact_sized ws' t hst) hsy' hltY' (by rw [hltd']; exact hid)
      hg' hocc rfl
    have hredU := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) dd)).length dd (wact ws u) y
      (wact_sized ws u hsu) hsy hluY (by rw [hlud]; exact hid) hgu
      hocc rfl
    have hredU' := act_tensorH_half i
      (monomialsAt (moveAt i (i + 1) dd)).length dd (wact ws' u) y'
      (wact_sized ws' u hsu) hsy' hluY' (by rw [hlud']; exact hid)
      hgu' hocc rfl
    have hL4 := BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _ hredT)
      (BPair.oneValue_trans (elim.dotP_oneValue_right _ _ _ hredT')
        (dotP_vecAdd4 (monomialsAt (moveAt i (i + 1) dd)).length
          _ _ _ _
          (length_raiseHalfL i _ dd (wact ws t) y hg rfl)
          (length_raiseHalfR i _ dd (wact ws t) y hg rfl)
          (length_raiseHalfL i _ dd (wact ws' t) y' hg' rfl)
          (length_raiseHalfR i _ dd (wact ws' t) y' hg' rfl)))
    have hR4 := BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ _ hredU)
      (BPair.oneValue_trans (elim.dotP_oneValue_right _ _ _ hredU')
        (dotP_vecAdd4 (monomialsAt (moveAt i (i + 1) dd)).length
          _ _ _ _
          (length_raiseHalfL i _ dd (wact ws u) y hgu rfl)
          (length_raiseHalfR i _ dd (wact ws u) y hgu rfl)
          (length_raiseHalfL i _ dd (wact ws' u) y' hgu' rfl)
          (length_raiseHalfR i _ dd (wact ws' u) y' hgu' rfl)))
    refine BPair.oneValue_trans (BPair.mul_congr_left hL4) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (mul4_distrib _ _ _ _ _)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left hR4) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (mul4_distrib _ _ _ _ _)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.add_congr (BPair.add_congr ?_ ?_)
      (BPair.add_congr ?_ ?_)
    · rw [raiseHalfL_guard i _ (wact ws t) (wact ws t) y rfl,
        raiseHalfL_guard i _ (wact ws' t) (wact ws' t) y' rfl,
        raiseHalfL_guard i _ (wact ws t) (wact ws u) y (hcwT ws),
        raiseHalfL_guard i _ (wact ws' t) (wact ws' u) y'
          (hcwT ws')]
      refine dotP_halfCross _ _ _ _ _ _ _ _ _ (fun hc hc' => ?_)
      refine dotP_tensorCross (act i (i + 1) (wact ws t))
        (act i (i + 1) (wact ws' t)) (act i (i + 1) (wact ws u))
        (act i (i + 1) (wact ws' u)) y y' _ _
        (act_sized i (i + 1) (wact ws t))
        (act_sized i (i + 1) (wact ws' t))
        (act_sized i (i + 1) (wact ws u))
        (act_sized i (i + 1) (wact ws' u)) hsy hsy'
        (by show moveAt i (i + 1) (wact ws t).content
              = moveAt i (i + 1) (wact ws u).content
            rw [hcwT ws])
        (by show moveAt i (i + 1) (wact ws' t).content
              = moveAt i (i + 1) (wact ws' u).content
            rw [hcwT ws'])
        (by show (moveAt i (i + 1) (wact ws t).content).length
              = y.content.length
            rw [length_moveAt]; exact hltY)
        (by show (moveAt i (i + 1) (wact ws' t).content).length
              = y'.content.length
            rw [length_moveAt]; exact hltY')
        (by show sumNat (moveAt i (i + 1) (wact ws t).content)
              = sumNat (moveAt i (i + 1) (wact ws' t).content)
            rw [sumNat_moveAt i (i + 1) (wact ws t).content
                (by rw [hltd]; exact Nat.lt_of_succ_lt hid) hc,
              sumNat_moveAt i (i + 1) (wact ws' t).content
                (by rw [hltd']; exact Nat.lt_of_succ_lt hid) hc']
            exact hdeg)
        (by rw [content_halfL i (i + 1) dd (wact ws t) y hg hc,
              content_halfL i (i + 1) dd (wact ws' t) y' hg' hc'])
        ?_
      intro hmm
      exact wordGramRaise2 d t u hst hsu hdt hcu htopt htopu ws ws'
        hb hb' i hid hmm
    · rw [raiseHalfL_guard i _ (wact ws t) (wact ws t) y rfl,
        raiseHalfL_guard i _ (wact ws t) (wact ws u) y (hcwT ws),
        raiseHalfR_unfold i _ (wact ws' t) y',
        raiseHalfR_unfold i _ (wact ws' u) y']
      refine dotP_halfCross _ _ _ _ _ _ _ _ _ (fun hc hc' => ?_)
      refine dotP_tensorCross (act i (i + 1) (wact ws t))
        (wact ws' t) (act i (i + 1) (wact ws u)) (wact ws' u) y
        (act i (i + 1) y') _ _
        (act_sized i (i + 1) (wact ws t)) (wact_sized ws' t hst)
        (act_sized i (i + 1) (wact ws u)) (wact_sized ws' u hsu)
        hsy (act_sized i (i + 1) y')
        (by show moveAt i (i + 1) (wact ws t).content
              = moveAt i (i + 1) (wact ws u).content
            rw [hcwT ws])
        (hcwT ws').symm
        (by show (moveAt i (i + 1) (wact ws t).content).length
              = y.content.length
            rw [length_moveAt]; exact hltY)
        (by show (wact ws' t).content.length
              = (moveAt i (i + 1) y'.content).length
            rw [length_moveAt]; exact hltY')
        (by show sumNat (moveAt i (i + 1) (wact ws t).content)
              = sumNat (wact ws' t).content
            rw [sumNat_moveAt i (i + 1) (wact ws t).content
              (by rw [hltd]; exact Nat.lt_of_succ_lt hid) hc]
            exact hdeg)
        (by rw [content_halfL i (i + 1) dd (wact ws t) y hg hc,
              content_halfR i (i + 1) dd (wact ws' t) y' hg' hc'])
        ?_
      intro hmm
      exact wordGramRaise d t u hst hsu hdt hcu htopt htopu ws ws'
        hb hb' i hid hmm
    · rw [raiseHalfL_guard i _ (wact ws' t) (wact ws' t) y' rfl,
        raiseHalfL_guard i _ (wact ws' t) (wact ws' u) y'
          (hcwT ws'),
        raiseHalfR_unfold i _ (wact ws t) y,
        raiseHalfR_unfold i _ (wact ws u) y]
      refine dotP_halfCross _ _ _ _ _ _ _ _ _ (fun hc hc' => ?_)
      refine dotP_tensorCross (wact ws t)
        (act i (i + 1) (wact ws' t)) (wact ws u)
        (act i (i + 1) (wact ws' u)) (act i (i + 1) y) y' _ _
        (wact_sized ws t hst) (act_sized i (i + 1) (wact ws' t))
        (wact_sized ws u hsu) (act_sized i (i + 1) (wact ws' u))
        (act_sized i (i + 1) y) hsy'
        (hcwT ws).symm
        (by show moveAt i (i + 1) (wact ws' t).content
              = moveAt i (i + 1) (wact ws' u).content
            rw [hcwT ws'])
        (by show (wact ws t).content.length
              = (moveAt i (i + 1) y.content).length
            rw [length_moveAt]; exact hltY)
        (by show (moveAt i (i + 1) (wact ws' t).content).length
              = y'.content.length
            rw [length_moveAt]; exact hltY')
        (by show sumNat (wact ws t).content
              = sumNat (moveAt i (i + 1) (wact ws' t).content)
            rw [sumNat_moveAt i (i + 1) (wact ws' t).content
              (by rw [hltd']; exact Nat.lt_of_succ_lt hid) hc']
            exact hdeg)
        (by rw [content_halfR i (i + 1) dd (wact ws t) y hg hc,
              content_halfL i (i + 1) dd (wact ws' t) y' hg' hc'])
        ?_
      intro hmm
      rw [elim.dotP_comm (wact ws t).coords
          (act i (i + 1) (wact ws' t)).coords,
        elim.dotP_comm (wact ws u).coords
          (act i (i + 1) (wact ws' u)).coords]
      exact wordGramRaise d t u hst hsu hdt hcu htopt htopu ws' ws
        hb' hb i hid hmm.symm
    · rw [raiseHalfR_unfold i _ (wact ws t) y,
        raiseHalfR_unfold i _ (wact ws u) y,
        raiseHalfR_unfold i _ (wact ws' t) y',
        raiseHalfR_unfold i _ (wact ws' u) y']
      refine dotP_halfCross _ _ _ _ _ _ _ _ _ (fun hc hc' => ?_)
      refine dotP_tensorCross (wact ws t) (wact ws' t) (wact ws u)
        (wact ws' u) (act i (i + 1) y) (act i (i + 1) y') _ _
        (wact_sized ws t hst) (wact_sized ws' t hst)
        (wact_sized ws u hsu) (wact_sized ws' u hsu)
        (act_sized i (i + 1) y) (act_sized i (i + 1) y')
        (hcwT ws).symm (hcwT ws').symm
        (by show (wact ws t).content.length
              = (moveAt i (i + 1) y.content).length
            rw [length_moveAt]; exact hltY)
        (by show (wact ws' t).content.length
              = (moveAt i (i + 1) y'.content).length
            rw [length_moveAt]; exact hltY')
        hdeg
        (by rw [content_halfR i (i + 1) dd (wact ws t) y hg hc,
              content_halfR i (i + 1) dd (wact ws' t) y' hg' hc'])
        ?_
      intro hmm
      exact wordGram d t u hst hsu hdt hcu htopt htopu ws ws' hb hb'
        hmm
  · have hz : ground.getAt 0 dd (i + 1) = 0 := Nat.eq_zero_of_not_pos hocc
    have hcT : (tensorH (wact ws t) y).content = dd := hg
    have hcU : (tensorH (wact ws u) y).content = dd := hgu
    exact mulScale_null _ _ _ _
      (elim.dotP_null_tail_left _ _
        (act_unitTail (tensorH (wact ws t) y) i (i + 1)
          (tensorH_sized _ _)
          (by rw [hcT]; exact Nat.lt_of_succ_lt hi) hij
          (by rw [hcT]; exact hi) (by rw [hcT]; exact hz)))
      (elim.dotP_null_tail_left _ _
        (act_unitTail (tensorH (wact ws u) y) i (i + 1)
          (tensorH_sized _ _)
          (by rw [hcU]; exact Nat.lt_of_succ_lt hi) hij
          (by rw [hcU]; exact hi) (by rw [hcU]; exact hz)))

/-- The index fold's scaled read transports at a memberwise
transport. -/
private theorem famFold_scaleAll (f g : Nat → BPair) (S S' : BPair) :
    ∀ l : List Nat, (∀ i ∈ l, (f i * S).oneValue (g i * S')) →
      (ground.famFold BPair.add BPair.unit f l * S).oneValue
        (ground.famFold BPair.add BPair.unit g l * S')
  | [], _ =>
    mulScale_null S S' _ _ (BPair.oneValue_refl _)
      (BPair.oneValue_refl _)
  | a :: t, h => by
    show ((f a + ground.famFold BPair.add BPair.unit f t)
        * S).oneValue
      ((g a + ground.famFold BPair.add BPair.unit g t) * S')
    rw [BPair.right_distrib, BPair.right_distrib]
    exact BPair.add_congr (h a (List.Mem.head t))
      (famFold_scaleAll f g S S' t
        (fun i hi => h i (List.Mem.tail a hi)))

/-- The stacked cross-top pair Gram (`lem:blockcount`(iii)'s
transport sentence, the stacked combination of raised pairs): two
word images at one top, tensored against two members of the shared
pool, pair through the stacked datum against the second top's
self-pairing exactly as the same words' images at the second top
pair against the first's.  The pairing splits over the adjacent
moves (`dotP_stackedRaise`) and each move's term goes over
(`dotP_actPair_words`); a word whose walk meets a vacant letter
sends both sides to the sum's unit outright. -/
private theorem dotP_stackPair_words (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u) (hdt : t.content.length = d)
    (hcu : t.content = u.content)
    (htopt : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j t).coords)
    (htopu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (ws ws' : List Nat) (hb : ∀ l ∈ ws, l + 1 < d)
    (hb' : ∀ l ∈ ws', l + 1 < d)
    (y y' : HVec) (hsy : sized y) (hsy' : sized y')
    (hwy : y.content.length = d) (hwy' : y'.content.length = d)
    (dd : List Nat)
    (hg : List.zipWith (fun x y => x + y) (wact ws t).content
      y.content = dd)
    (hg' : List.zipWith (fun x y => x + y) (wact ws' t).content
      y'.content = dd) :
    (elim.dotP
        (elim.matVec (units.stackedRaise dd)
          (tensorH (wact ws t) y).coords)
        (elim.matVec (units.stackedRaise dd)
          (tensorH (wact ws' t) y').coords)
        * elim.dotP u.coords u.coords).oneValue
      (elim.dotP
        (elim.matVec (units.stackedRaise dd)
          (tensorH (wact ws u) y).coords)
        (elim.matVec (units.stackedRaise dd)
          (tensorH (wact ws' u) y').coords)
        * elim.dotP t.coords t.coords) := by
  have hcwT : ∀ z : List Nat, (wact z u).content = (wact z t).content := by
    intro z
    rw [wact_content, wact_content, hcu]
  have hbt : ∀ l ∈ ws, l + 1 < t.content.length := by
    intro l hl; rw [hdt]; exact hb l hl
  have hbt' : ∀ l ∈ ws', l + 1 < t.content.length := by
    intro l hl; rw [hdt]; exact hb' l hl
  have hltY : (wact ws t).content.length = y.content.length := by
    rw [wact_content_len, hdt, hwy]
  have hltY' : (wact ws' t).content.length = y'.content.length := by
    rw [wact_content_len, hdt, hwy']
  have hluY : (wact ws u).content.length = y.content.length := by
    rw [wact_content_len, ← hcu, hdt, hwy]
  have hluY' : (wact ws' u).content.length = y'.content.length := by
    rw [wact_content_len, ← hcu, hdt, hwy']
  have hgu : List.zipWith (fun x y => x + y) (wact ws u).content
      y.content = dd := by
    rw [hcwT ws]; exact hg
  have hgu' : List.zipWith (fun x y => x + y) (wact ws' u).content
      y'.content = dd := by
    rw [hcwT ws']; exact hg'
  match wact_deg_or_null ws t.content hbt,
      wact_deg_or_null ws' t.content hbt' with
  | .inr hn, _ =>
    exact mulScale_null _ _ _ _
      (elim.dotP_null_tail_left _ _ (elim.matVec_null _ _
        ((tensorH_unitTail (wact ws t) y (wact_sized ws t hst) hsy
          hltY).mpr (Or.inl (hn t hst rfl)))))
      (elim.dotP_null_tail_left _ _ (elim.matVec_null _ _
        ((tensorH_unitTail (wact ws u) y (wact_sized ws u hsu) hsy
          hluY).mpr (Or.inl (hn u hsu hcu.symm)))))
  | _, .inr hn' =>
    exact mulScale_null _ _ _ _
      (elim.dotP_null_tail_right _ _ (elim.matVec_null _ _
        ((tensorH_unitTail (wact ws' t) y' (wact_sized ws' t hst)
          hsy' hltY').mpr (Or.inl (hn' t hst rfl)))))
      (elim.dotP_null_tail_right _ _ (elim.matVec_null _ _
        ((tensorH_unitTail (wact ws' u) y' (wact_sized ws' u hsu)
          hsy' hluY').mpr (Or.inl (hn' u hsu hcu.symm)))))
  | .inl hdg, .inl hdg' =>
    have hdeg : sumNat (wact ws t).content
        = sumNat (wact ws' t).content := by
      rw [wact_content ws t, wact_content ws' t, hdg, hdg']
    refine BPair.oneValue_trans (BPair.mul_congr_left
      (dotP_stackedRaise dd (tensorH (wact ws t) y)
        (tensorH (wact ws' t) y') hg hg'
        (tensorH_sized _ _) (tensorH_sized _ _))) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left
      (dotP_stackedRaise dd (tensorH (wact ws u) y)
        (tensorH (wact ws' u) y') hgu hgu'
        (tensorH_sized _ _) (tensorH_sized _ _))) ?_
    refine BPair.oneValue_symm ?_
    refine famFold_scaleAll _ _ _ _ (List.range (dd.length - 1)) ?_
    intro i hi
    exact dotP_actPair_words d t u hst hsu hdt hcu htopt htopu
      ws ws' hb hb' hdeg y y' hsy hsy' hwy hwy' dd hg hg' i
      (ground.succ_lt_of_lt_pred (ground.ltOfMemRange hi))

/-- `lem:blockcount`(iii)'s transport identity at the pair lists:
one word family read at two tops of one content, tensored against
one shared pool, reads one kernel dimension.  The two enumerations
are one factor family — the guard reads the word images' contents,
which the two tops share (`pairIdx_congr`) — and their stacked
Grams agree entry by entry at the two tops' self-pairings
(`dotP_stackPair_words`), so the cross-scaled Gram read closes the
identity (`elim.kernelDim_gram`).  The top, sized, width and
shared-content binders are `wordGram`'s own frame with its
committed refusals; the letter bounds are `con:units`' index frame;
the pool's sized and width binders are the tensor's own frame at
`con:places`' one letter width; and the two off-unit binders are
the scales' clearing, read at the tops off the sum's unit. -/
theorem kernelDim_pairs_words (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u) (hdt : t.content.length = d)
    (hcu : t.content = u.content)
    (htopt : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j t).coords)
    (htopu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (hofft : ¬ poly.unitTail t.coords)
    (hoffu : ¬ poly.unitTail u.coords)
    (gws : List (List Nat))
    (hgb : ∀ ws ∈ gws, ∀ l ∈ ws, l + 1 < d)
    (C : List HVec) (hszC : ∀ y ∈ C, sized y)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (dd : List Nat) :
    elim.kernelDim
        (pairsAt (gws.map (fun ws => wact ws t)) C dd).length
        (elim.crossM (units.stackedRaise dd)
          ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
            HVec.coords))
      = elim.kernelDim
        (pairsAt (gws.map (fun ws => wact ws u)) C dd).length
        (elim.crossM (units.stackedRaise dd)
          ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
            HVec.coords)) := by
  have hcwT : ∀ z : List Nat,
      (wact z u).content = (wact z t).content := by
    intro z
    rw [wact_content, wact_content, hcu]
  have hidx : pairIdx gws (fun ws => wact ws u) C dd
      = pairIdx gws (fun ws => wact ws t) C dd :=
    pairIdx_congr (fun ws => wact ws u) (fun ws => wact ws t) C dd
      gws (fun z _ => hcwT z)
  have hrowsT : elim.rowsLen (monomialsAt dd).length
      ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
        HVec.coords) :=
    elim.rowsLen_map HVec.coords (monomialsAt dd).length _
      (pairs_coordLen _ C dd)
  have hrowsU : elim.rowsLen (monomialsAt dd).length
      ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords) :=
    elim.rowsLen_map HVec.coords (monomialsAt dd).length _
      (pairs_coordLen _ C dd)
  have hlen : ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
        HVec.coords).length
      = ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords).length := by
    rw [ground.length_map, ground.length_map,
      length_pairsAtIdxM gws (fun ws => wact ws t) C dd,
      length_pairsAtIdxM gws (fun ws => wact ws u) C dd, hidx]
  have hstep := elim.kernelDim_gram (monomialsAt dd).length
    (units.stackedRaise dd)
    ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map HVec.coords)
    ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map HVec.coords)
    (elim.dotP t.coords t.coords) (elim.dotP u.coords u.coords)
    (fun hh => hofft (elim.dotP_self_null t.coords hh))
    (fun hh => hoffu (elim.dotP_self_null u.coords hh))
    (units.rowsLen_stackedRaise dd) hrowsU hrowsT hlen
    (by
      intro k hk l hl
      rw [ground.length_map,
        length_pairsAtIdxM gws (fun ws => wact ws u) C dd,
        hidx] at hk hl
      have hkU : k < (pairIdx gws (fun ws => wact ws u) C dd).length := by
        rw [hidx]; exact hk
      have hlU : l < (pairIdx gws (fun ws => wact ws u) C dd).length := by
        rw [hidx]; exact hl
      rw [getAt_pairsCoordsM ([] : List Nat) gws
          (fun ws => wact ws t) C dd k hk,
        getAt_pairsCoordsM ([] : List Nat) gws
          (fun ws => wact ws t) C dd l hl,
        getAt_pairsCoordsM ([] : List Nat) gws
          (fun ws => wact ws u) C dd k hkU,
        getAt_pairsCoordsM ([] : List Nat) gws
          (fun ws => wact ws u) C dd l hlU, hidx,
        BPair.mul_comm (elim.dotP u.coords u.coords),
        BPair.mul_comm (elim.dotP t.coords t.coords)]
      obtain ⟨hwG, hyC, hgd⟩ := pairIdx_read ([] : List Nat) gws
        (fun ws => wact ws t) C dd k hk
      obtain ⟨hwG', hyC', hgd'⟩ := pairIdx_read ([] : List Nat) gws
        (fun ws => wact ws t) C dd l hl
      exact dotP_stackPair_words d t u hst hsu hdt hcu htopt htopu
        _ _ (hgb _ hwG) (hgb _ hwG') _ _ (hszC _ hyC) (hszC _ hyC')
        (hwidC _ hyC) (hwidC _ hyC') dd hgd hgd')
  rw [← ground.length_map HVec.coords
      (pairsAt (gws.map (fun ws => wact ws t)) C dd),
    ← ground.length_map HVec.coords
      (pairsAt (gws.map (fun ws => wact ws u)) C dd)]
  exact hstep


/-- The pair list at the second top is independent exactly where the
pair list at the first top is (`lem:blockcount`(iii)'s transport
sentence, "the two carriers' unit reads agree at the off-unit
self-pairings by the product's injectivity"): the two plain Grams
agree entry by entry at the tops' self-pairings
(`dotP_pairWords`), so a null combination's self-pairing transports
across them (`elim.dotP_comboGram`), the first top's own
self-pairing withdraws off the sum's unit, and the first list's
independence reads the coefficients back. -/
theorem tensor_indep_words (d : Nat) (t u : HVec)
    (hst : sized t) (hsu : sized u) (hdt : t.content.length = d)
    (hcu : t.content = u.content)
    (htopt : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j t).coords)
    (htopu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (hoffu : ¬ poly.unitTail u.coords)
    (gws : List (List Nat))
    (hgb : ∀ ws ∈ gws, ∀ l ∈ ws, l + 1 < d)
    (C : List HVec) (hszC : ∀ y ∈ C, sized y)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (dd : List Nat)
    (hind : elim.indepRows (monomialsAt dd).length
      ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
        HVec.coords)) :
    elim.indepRows (monomialsAt dd).length
      ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords) := by
  have hcwT : ∀ z : List Nat,
      (wact z u).content = (wact z t).content := by
    intro z
    rw [wact_content, wact_content, hcu]
  have hidx : pairIdx gws (fun ws => wact ws u) C dd
      = pairIdx gws (fun ws => wact ws t) C dd :=
    pairIdx_congr (fun ws => wact ws u) (fun ws => wact ws t) C dd
      gws (fun z _ => hcwT z)
  have hrowsU : elim.rowsLen (monomialsAt dd).length
      ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords) :=
    elim.rowsLen_map HVec.coords (monomialsAt dd).length _
      (pairs_coordLen _ C dd)
  have hlenUT : ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords).length
      = ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
        HVec.coords).length := by
    rw [ground.length_map, ground.length_map,
      length_pairsAtIdxM gws (fun ws => wact ws t) C dd,
      length_pairsAtIdxM gws (fun ws => wact ws u) C dd, hidx]
  have hgram : ∀ k,
      k < ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
        HVec.coords).length → ∀ l,
      l < ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
        HVec.coords).length →
      (elim.dotP t.coords t.coords * elim.dotP
          (ground.getAt []
            ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
              HVec.coords) k)
          (ground.getAt []
            ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
              HVec.coords) l)).oneValue
        (elim.dotP u.coords u.coords * elim.dotP
          (ground.getAt []
            ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
              HVec.coords) k)
          (ground.getAt []
            ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map
              HVec.coords) l)) := by
    intro k hk l hl
    rw [ground.length_map,
      length_pairsAtIdxM gws (fun ws => wact ws t) C dd] at hk hl
    have hkU : k < (pairIdx gws (fun ws => wact ws u) C dd).length := by
      rw [hidx]; exact hk
    have hlU : l < (pairIdx gws (fun ws => wact ws u) C dd).length := by
      rw [hidx]; exact hl
    rw [getAt_pairsCoordsM ([] : List Nat) gws
        (fun ws => wact ws t) C dd k hk,
      getAt_pairsCoordsM ([] : List Nat) gws
        (fun ws => wact ws t) C dd l hl,
      getAt_pairsCoordsM ([] : List Nat) gws
        (fun ws => wact ws u) C dd k hkU,
      getAt_pairsCoordsM ([] : List Nat) gws
        (fun ws => wact ws u) C dd l hlU, hidx,
      BPair.mul_comm (elim.dotP u.coords u.coords),
      BPair.mul_comm (elim.dotP t.coords t.coords)]
    obtain ⟨hwG, hyC, hgd⟩ := pairIdx_read ([] : List Nat) gws
      (fun ws => wact ws t) C dd k hk
    obtain ⟨hwG', hyC', hgd'⟩ := pairIdx_read ([] : List Nat) gws
      (fun ws => wact ws t) C dd l hl
    exact BPair.oneValue_symm
      (dotP_pairWords d t u hst hsu hdt hcu htopt htopu
        _ _ (hgb _ hwG) (hgb _ hwG') _ _ (hszC _ hyC) (hszC _ hyC')
        (hwidC _ hyC) (hwidC _ hyC') dd hgd hgd')
  refine elim.indep_intro (monomialsAt dd).length _ hrowsU ?_
  intro cs hcs hnull
  have htr := elim.dotP_comboGram (monomialsAt dd).length
    (elim.dotP u.coords u.coords) (elim.dotP t.coords t.coords)
    ((pairsAt (gws.map (fun ws => wact ws t)) C dd).map HVec.coords)
    ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map HVec.coords)
    hind.1 hrowsU hlenUT hgram cs
  have hself := elim.dotP_null_tail_left
    (elim.combo (monomialsAt dd).length cs
      ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords))
    (elim.combo (monomialsAt dd).length cs
      ((pairsAt (gws.map (fun ws => wact ws u)) C dd).map
        HVec.coords)) hnull
  exact elim.indep_elim hind cs (hcs.trans hlenUT)
    (elim.dotP_self_null _
      (ground.mul_cancel_unit
        (fun hh => hoffu (elim.dotP_self_null u.coords hh))
        (BPair.oneValue_trans (BPair.oneValue_symm htr)
          (elim.oneValue_mul_unit _ _ hself))))

end blockcount
