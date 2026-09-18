import MassGap.Blockcount
import MassGap.Labels
import MassGap.Memtable
/-!
`con:slotpower` — the presentation's carrier. A factor list's slot
power is the power at one slot per factor, the units acting on an
undaggered factor's slot by the standard action and on a daggered
factor's slot by the dual action, the exchanged letters' balance
partner (`lem:dualread`(i)), both read on the one coordinate family,
the power's monomials. A label enters at its word
pair (`wordPair`: a column of the reduced shape at a length at or
below its complement's enters the top word at that many undaggered
factors, a further column the bottom word at the complement length's
daggered, the tie a column at its complement's length), its slots the
top columns' undaggered then the bottom columns' daggered (`wordSig`
at a word pair, `labelSig` at the label's, an incoming end at the
exchanged signature `endWordSig`, `endSig`). A monomial's
weight is its undaggered letter counts against its daggered, one
balance pair per letter (`weightAt`, `weightOf`), and the unit weight
is the full columns' class (`unitWeightAt`, `unitWeight` at a
monomial).

The vectors of a slot power read at their occupied monomials
(`SVec` at its slot count, the occupancy family at its collected
display, the monomials in the lexicographic order with every
coefficient canonical and off the sum's unit and every monomial at
the power's slot count, the display's collection and count the
datum's witness, `collect` the collection of a stated family at a
stated count with `sortedV` the order's read, `width_of_mem` the
count's, `instSlotpower1` two vectors' equality at their displays,
`emptyV` the vacant vector, `castV` a vector read at an equal
count, `monV` and `monsV` the vectors at stated monomials; `WVec` a
vector with its count and `WList` a list with its one count,
`instSlotpower2` and `oneValueW` their equality), the one tier at a
generating table (`con:memtable`), the letters' table its instance
(`memtable.lettersT`): the table's sparse map at one slot (`actT`),
the simple raising and lowering at a slot signature (`raiseT`,
`lowerT`, the dual action at a daggered slot), a monomial's weight
at the keys' coroot lists (`weightT`, `weightV` a vector's at its
first occupied monomial, every block member weight-homogeneous),
the weighted pairing (`monDotT` one monomial against a vector at
the weight's substitutions, `dotT`; the weight applied to a vector
`applyWt`, the tensor power at the slots read on the vector, a
monomial's pairing at a stated weight its coefficient in the
applied vector, `monDotT_apply`, so the weighted pairing is the
unit-weight pairing against the applied vector, `dotT_apply`; the
sorted walk `dotTS` against the vector at the unit weight and
against the applied vector at a stated weight with `dotTS_read` its
read as the fold, `pairT` its canonical representative with
`pairT_apply`, and `gramT` the Gram at the applied vectors read
once per member, at a symmetric weight one walk per member pair
with the lower triangle the upper's transpose (`elim.gramSym`),
with `gramT_eq` its read as the pairings' Gram), the tensor
(`tensorV`), the scale, the sum and the primitive representative
(`scaleV`, `addV`, `prim`), two vectors one value (`oneValueV`), the
lowering closure at a stated top (`blockSpanT` at the membership
read within the weight's group, `tryAddT`, `closeT`, the closure run
at the stored descents, `closeTS`, the block's pool `blockPoolT`
with its member projection `blockSpanT` and its weight grades
`blockGroupsT`, each its members, its Gram grown a row per join, its
descent and its determinant, the descent's terminal entry,
`blockGroupsT_reads` their reads at a symmetric weight with
`blockGroupsT_length` the grades' count, and `blockSpanT_eq` the
members' read at the fresh walk at the pairing's exchange,
`pairA_comm`; a stated list's weight grades at its collection
`listGroupsT` with `listGroupsT_reads`; a list's places grouped at
its members' weights `weightPlaces`, `weightPlaces_read` a grade's
places the list's members at the weight), the fused
span at stated end blocks grouped at the ends' weight lists, the
groups pairwise orthogonal at each end's own grading
(`fusedGroupsT`, `fusedSpanT`), the stacked raisings' kernel over a
pool, the invariants' list (`kernelT`, `def:elim`'s back solve;
`comboV` a kernel member as a vector), the Gram-dual solve over a
pool with its clearing (`spanCoeffsT`), the span membership at its
residual (`spanMemberT`), the projection at one pool and group by
group at the clearings' product, the vector at its reduced
representative (`projectT`, `projectGroupsT`, `reduceV`), the paired
tensor of a stated matrix at stated slot pairs (`pairTensor`, the
identity's at the weight's cleared partner the through pairing of
two ends at opposite orientations, `throughT`, and the dual pair's
at two ends of one orientation, `dualThroughT`, each cleared at its
matrix's clearing to the pairs' count), and the place action's
relabeling of the occupied monomials (`relabelV`).

The letters' own devices (`con:slotpower`): a label's block at its
word pair is the lowerings' span at its top, the top-word columns'
wedge exhibits on the undaggered slots tensored with the
bottom-word columns' dual wedges on the daggered, the wedge at the
last letters of the complement's length (`blockTop`, `dualWedge`,
`blockSpanAt` the closure at the letters' table with its weight
grades `blockGroupsAt`, `blockSpanAt_eq` its read at the fresh
walk); a wiring's tensor
reads one letter per row end, read again at the column end it
pairs (`wiringG`); the through pairing of two ends at dual labels
pairs each column's slots with its complement column's (`colMatch`
at the column layouts, `layoutOf`, at a stated key dual), a wiring
at an undaggered slot against a daggered one and the star at a tie
column, the monomials at complementary letter sets at the swap
grading's side (`starFam`) cleared at the column length's
factorial (`throughPair`, the tensor the column pairs' families'
product); a moved end's slots at the column match
(`transportSlots`, the tie columns' groups at a reversed
traversal) with the tie columns at the star's map (`starAt`), and
the identification of a vector at a moved end's slots `identifyV`
with its clearing `identifyClear`, the star at the letters
(`con:slotpower`) and the dual pair at a member (`con:memtable`),
the reads `con:fiber`'s two-end vertex and `thm:pairpencil`'s
terms' transport consume; and the top read at a table, a vector at
the sum's unit under every simple raising (`raisedUnit`,
`con:memtable`).

The finite monomial carrier is `keysRead`, and `homogRead` reads
a vector at a stated coroot weight. The monomial's weight is the
canonical vector fold (`weightT_vsum`), its coroot entries the signed
diagonal folds (`weightT_entry`); concatenating signatures adds the
weights (`weightT_append`, `homogRead_tensorV`). A sparse action's
key move adds to the whole weight at its slot (`weightT_set_add`),
and the Leibniz actions have the stored simple moves at every slot
(`homogRead_raiseT`, `homogRead_lowerT`), G2's reads the actual
Cartan rows and their balance partners.

Tensor coefficients multiply at the first factor's slot count
(`coefAt_tensorV`), so occupied factors have an occupied tensor.
At the unit weight an occupied vector's self-pairing is positive
(`pairT_self_pos`), the coordinate walk's squares. A top off its
self-pairing's unit is the first member of its stored span, with
its tail at the simple images' reads (`blockSpanT_top`,
`blockSpanT_tail`). G2's pairing is the unit weight, and its
occupied tops belong to their stored spans at every slot count.

Linear coefficient folds read through collection, tensoring and
sparse actions (`fold_tensorV`, `fold_actT`), with the raising and
lowering tensor identities at their concatenated signatures
(`raiseT_tensorV`, `lowerT_tensorV`). They preserve sums and scalar
multiplication, and tops tensor to tops (`raisedUnit_tensorV`).
The maximum of occupied monomial heights (`heightV`) drops under
standard lowerings at the key-height read. G2's shifted coroot
heights are bounded by six per slot, so its actual block's member
list is fixed beyond the stored fuel (`blockSpanT_fuel_G2`).

The finite monomial coordinates (`coordsV`) identify vectors on
their key carrier (`coordsV_injective`), read the unit pairing
(`pairT_coordsV`), and preserve combinations (`coordsV_comboV`).
The coordinate Gram reads each membership join (`joinIndep_coordsV`)
and its independent weight groups (`indepGroupsT`). At G2 the
stored lowering closure accepts every listed member's lowering in
its coordinate span (`blockSpanT_reads_G2`), and that read extends
to every member of the span (`blockSpanT_lower_span_G2`). Homogeneous
members at distinct weights pair at the sum's unit
(`pairT_homog_perp`, `blockSpanT_perp_G2`).
Each listed member is a simple lowering word at the seed
(`blockSpanT_words`), and every such word belongs to the actual
G2 block's coordinate span (`blockSpanT_word_span_G2`).
The homogeneous groups join to an independent coordinate list
(`blockSpanT_indep_G2`), whose count is bounded by the monomial
carrier. The simple commutator on standard G2 powers reads each
homogeneous coroot (`raiseT_lowerT_G2`); at a top its word induction
puts every raising image inside the actual span
(`raiseT_word_span_G2`, `blockSpanT_raise_span_G2`).

Sparse map equivalence reads the same slot action (`actT_congr`).
The signed slot action walks across the unit pairing as its
transpose (`pairT_actT`), and G2's actual simple maps give the
raising/lowering pairing identity at every signature
(`pairT_raise_lower_G2`). At one simple root, the lowering iterates
(`iterLowerT`) descend two in the chosen coroot. An occupied top
has a natural height; its iterates are occupied through that
height, terminate at the next depth and have the self-pairings
of the string coefficient product. Their two ordered raising and
lowering words read the depth's trace coefficients
(`iterLowerT_raise_G2`, `iterLowerT_term_G2`,
`iterLowerT_selfpair_G2`, `iterLowerT_trace_G2`). Equally deep
iterates at an arbitrary second seed pair at the first string's
coefficient product (`iterLowerT_pair_G2`). The occupied depths form
an independent list, their count at most the monomial carrier's
(`iterLowerT_indep_G2`, `iterLowerT_length_le_G2`), with the finite
span closed under its chosen raising and lowering
(`iterLowerT_raise_span_G2`, `iterLowerT_lower_span_G2`). The member
table's simple reflection exchanges complementary depths' weights
(`iterLowerT_reflect_G2`), and every depth beyond the height is
vacant (`iterLowerT_past_G2`).

The sparse residual (`residT`) is the determinant-scaled seed
joined to its adjugate combination's partner, computed at the
pool's sparse Gram. At the unit pairing its finite coordinates
read the elimination residual (`coordsV_residT`). It keeps the
seed and pool's key carrier and common weight, is perpendicular
to the pool, and stays in every span containing both. A refused
seed gives an occupied independent extension (`residT_refuse`).
At G2, when the raising image belongs to a processed group's span
and that group's lowerings belong to the collected span, the
residual is a top for the chosen simple (`residT_raise_G2`), the
transpose identity and positive self-pairing reading its raising
at the vacant vector. The key hypotheses state the generating
table's finite carrier, and independence states the residual's
Gram condition (`lem:lowerspan`; `lem:strings`).
-/

namespace slotpower
open ground places blockcount

/-- The reduced shape's columns, longest first. -/
def cols (s : Shape) : List Nat := blockcount.columnLengths (labels.reduce s)

/-- A column's side at the count: the top word where its length
sits at or below its complement's. -/
def topCol (d l : Nat) : Bool := l + l ≤ d

/-- The top-word columns, longest first. -/
def topCols (d : Nat) (s : Shape) : List Nat := (cols s).filter (topCol d)

/-- The bottom-word columns, longest first. -/
def botCols (d : Nat) (s : Shape) : List Nat :=
  (cols s).filter (fun l => !topCol d l)

/-- A label's word pair: the top columns' lengths against the
bottom columns' complement lengths. -/
def wordPair (d : Nat) (s : Shape) : Nat × Nat :=
  (sumNat (topCols d s), sumNat ((botCols d s).map (fun l => d - l)))

/-- A word pair's slot signature: the undaggered slots then the
daggered, `false` undaggered. -/
def wordSig (w : Nat × Nat) : List Bool :=
  List.replicate w.1 false ++ List.replicate w.2 true

/-- A label's slot signature, its word pair's. -/
def labelSig (d : Nat) (s : Shape) : List Bool := wordSig (wordPair d s)

/-- An end's slot signature at a word pair: the word's at an
outgoing end, the exchanged at an incoming, the dual block on the
one coordinate family. -/
def endWordSig (w : Nat × Nat) (out : Bool) : List Bool :=
  if out then wordSig w else (wordSig w).map not

/-- An end's slot signature, its label's word pair at the end's
orientation. -/
def endSig (d : Nat) (e : Shape × Bool) : List Bool :=
  endWordSig (wordPair d e.1) e.2

/-- A vertex's slot signature, its ends' in the incident order. -/
def vertexSig (d : Nat) (es : List (Shape × Bool)) : List Bool :=
  es.flatMap (endSig d)

/-- The undaggered slots in order. -/
def upSlots (sig : List Bool) : List Nat :=
  (List.range sig.length).filter (fun s => !getAt false sig s)

/-- The daggered slots in order. -/
def downSlots (sig : List Bool) : List Nat :=
  (List.range sig.length).filter (fun s => getAt false sig s)

/-- A weight at two contents, the undaggered count against the
daggered per letter, one balance pair each at its canonical
representative. -/
def weightAt (up dn : List Nat) : List BPair :=
  List.zipWith (fun a b => (BPair.ofNat a + (BPair.ofNat b).swap).norm) up dn

/-- A monomial's weight at a signature. -/
def weightOf (d : Nat) (sig : List Bool) (m : List Nat) : List BPair :=
  weightAt (content d ((upSlots sig).map (fun s => getAt 0 m s)))
    (content d ((downSlots sig).map (fun s => getAt 0 m s)))

/-- The unit-weight read: every letter's balance one value with the
first's, the full columns' class. -/
def unitWeightAt (w : List BPair) : Bool :=
  w.all (fun x => decide (x.oneValue (getAt BPair.unit w 0)))

/-- A monomial's unit-weight read at a signature. -/
def unitWeight (d : Nat) (sig : List Bool) (m : List Nat) : Bool :=
  unitWeightAt (weightOf d sig m)

/-! The vectors at their occupied monomials, the one tier at a
generating table. -/

/-- A vector of the slot power at a stated slot count, at its
occupied monomials with their coefficients, the occupancy family at
its collected display: the monomials in the lexicographic order,
each once, every coefficient canonical and off the sum's unit, the
display its own collection (`ground.collectBy`), and every monomial
at the power's slot count, one slot per factor (`con:slotpower`),
the two reads the datum's witness. -/
abbrev SVec (k : Nat) :=
  { v : List (List Nat × BPair) //
    collectBy lexLt (fun a b => a == b) v = v ∧ v.all (fun p => p.1.length == k) = true }

/-- A vector with its slot count, the power it sits in. -/
abbrev WVec := (k : Nat) × SVec k

/-- A list of vectors at one slot count, with the count. -/
abbrev WList := (k : Nat) × List (SVec k)

/-- The monomials collected at their keys at a stated slot count
every monomial reads, the coefficients joined at their canonical
representatives and the unit coefficients withdrawn
(`ground.collectBy`), the collection its own
(`ground.collectBy_idem`) and the keys' slot count kept
(`ground.collectBy_all_keys`). -/
def collect (k : Nat) (v : List (List Nat × BPair))
    (h : v.all (fun p => p.1.length == k) = true) : SVec k :=
  ⟨collectBy lexLt (fun a b => a == b) v,
   collectBy_idem lexLt (fun a b => a == b) lexLt_trans (fun _ _ h => listBeqEq h) lexLt_tri v,
   collectBy_all_keys lexLt (fun a b => a == b) (fun m => m.length == k) v h⟩

/-- The vacant vector at a slot count. -/
def emptyV (k : Nat) : SVec k := ⟨[], rfl, rfl⟩

/-- A display at one slot count reads an equal count. -/
private theorem widths_cast {k l : Nat} (h : k = l) (v : List (List Nat × BPair))
    (hv : v.all (fun p => p.1.length == k) = true) :
    v.all (fun p => p.1.length == l) = true := by
  rw [← h]
  exact hv

/-- A vector read at an equal slot count, the display kept. -/
def castV {k l : Nat} (h : k = l) (v : SVec k) : SVec l :=
  ⟨v.val, v.property.1, widths_cast h v.val v.property.2⟩

/-- One monomial's family reads the monomial's count. -/
private theorem monV_widths (k : Nat) (m : List Nat) (h : m.length = k) :
    [(m, BPair.ofNat 1)].all (fun p => p.1.length == k) = true := by
  show (decide (m.length = k) && true) = true
  rw [decide_eq_true h]
  rfl

/-- The vector at one monomial of a stated slot count at the
coefficient one. -/
def monV (k : Nat) (m : List Nat) (h : m.length = k) : SVec k :=
  collect k [(m, BPair.ofNat 1)] (monV_widths k m h)

/-- The vectors at stated monomials of one slot count, one per
monomial at the coefficient one. -/
def monsV (k : Nat) : (ms : List (List Nat)) → ms.all (fun m => m.length == k) = true →
    List (SVec k)
  | [], _ => []
  | m :: t, h =>
    monV k m (of_decide_eq_true (andSplitB h).1) :: monsV k t (andSplitB h).2

/-- A vector's monomials are in order, the collection sorted
(`ground.collectBy_sorted`). -/
theorem sortedV {k : Nat} (v : SVec k) : keysInOrder lexLt v.val = true := by
  rw [← v.property.1]
  exact collectBy_sorted lexLt (fun a b => a == b) lexLt_trans (fun _ _ h => listBeqEq h)
    lexLt_tri _

/-- An occupied monomial reads the vector's slot count. -/
theorem width_of_mem {k : Nat} (v : SVec k) (p : List Nat × BPair) (hp : p ∈ v.val) :
    p.1.length = k :=
  of_decide_eq_true (all_of_mem _ v.val v.property.2 p hp)

/-- Two vectors' equality decided at their displays, the witness a
proof. -/
instance instSlotpower1 (k : Nat) : DecidableEq (SVec k) :=
  fun a b => Subtype.instDecidableEq a b

/-- Two vectors with their slot counts at one count and one display
are one datum. -/
private theorem WVec.mk_eq {k l : Nat} (v : SVec k) (w : SVec l) (h1 : k = l)
    (h2 : v.val = w.val) : (⟨k, v⟩ : WVec) = ⟨l, w⟩ := by
  subst h1
  exact congrArg (Sigma.mk k) (Subtype.ext h2)

/-- Two vectors with their slot counts equal exactly at one count
and one display. -/
def WVec.decEq : (a b : WVec) → Decidable (a = b)
  | ⟨k, v⟩, ⟨l, w⟩ =>
    if h1 : k = l then
      if h2 : v.val = w.val then isTrue (WVec.mk_eq v w h1 h2)
      else isFalse (fun hh => h2 (congrArg (fun x : WVec => x.2.val) hh))
    else isFalse (fun hh => h1 (congrArg Sigma.fst hh))

instance instSlotpower2 : DecidableEq WVec := WVec.decEq

/-- Two vectors with their slot counts one value, their equality. -/
def oneValueW (a b : WVec) : Bool := decide (a = b)

/-- A monomial's coefficient in a vector, the entries' fold. -/
def coefAt (m : List Nat) {k : Nat} (v : SVec k) : BPair :=
  v.val.foldl (fun acc p => if p.1 == m then acc + p.2 else acc) BPair.unit

/-- A vector's coordinates on a stated finite monomial list. -/
def coordsV (ms : List (List Nat)) {k : Nat} (v : SVec k) : List BPair :=
  ms.map (fun m => coefAt m v)

/-- A vector's coefficients are canonical and off the sum's unit,
the collection's members (`ground.mem_normFilter`). -/
theorem canonV {k : Nat} (v : SVec k) :
    ∀ p, p ∈ v.val → p.2.norm = p.2 ∧ p.2.isUnitRep = false := by
  rw [← v.property.1]
  exact fun p hp => mem_normFilter _ p hp

/-- Two vectors one value at every occupied monomial, their displays'
equality at the collected carrier (`oneValueV_read` its read as the
walk `ground.oneValueBy`). -/
def oneValueV {k : Nat} (u v : SVec k) : Bool := decide (u = v)

/-- The displays' equality is the one-value walk: the walk reads one
fold at every key (`ground.keyFoldB_oneValueBy`), two collected
displays at one fold everywhere are one display
(`ground.sorted_unique`), and a display walks against itself
(`ground.oneValueBy_refl`). -/
theorem oneValueV_read {k : Nat} (u v : SVec k) :
    oneValueV u v = oneValueBy lexLt (fun a b => a == b) u.val v.val := by
  show decide (u = v) = oneValueBy lexLt (fun a b => a == b) u.val v.val
  cases hd : decide (u = v) with
  | true =>
    have he : u = v := of_decide_eq_true hd
    rw [he]
    exact (oneValueBy_refl lexLt (fun a b => a == b) listEqBeq v.val).symm
  | false =>
    cases ho : oneValueBy lexLt (fun a b => a == b) u.val v.val with
    | false => rfl
    | true =>
      exfalso
      have heq : u.val = v.val :=
        sorted_unique lexLt (fun a b => a == b) lexLt_trans (fun _ _ h => listBeqEq h)
          lexLt_irrefl listEqBeq u.val v.val (sortedV u) (sortedV v) (canonV u) (canonV v)
          (fun k => keyFoldB_oneValueBy lexLt (fun a b => a == b)
            (fun _ _ h => listBeqEq h) u.val v.val ho k)
      have huv : u = v := Subtype.ext heq
      rw [huv] at hd
      exact Bool.noConfusion (hd.symm.trans (decide_eq_true rfl))

/-- The scaled display reads the vector's count. -/
private theorem scaleV_widths (c : BPair) {k : Nat} (v : SVec k) :
    (v.val.map (fun p => (p.1, p.2 * c))).all (fun p => p.1.length == k) = true := by
  rw [all_map]
  exact v.property.2

/-- A vector scaled, the coefficients' products collected. -/
def scaleV (c : BPair) {k : Nat} (v : SVec k) : SVec k :=
  collect k (v.val.map (fun p => (p.1, p.2 * c))) (scaleV_widths c v)

private theorem addV_canon {k : Nat} (u v : SVec k) :
    collectBy lexLt (fun a b => a == b)
      ((mergeJoin lexLt (fun a b => a == b) (fun y x => (y + x).norm)
        (u.val.length + v.val.length) u.val v.val).filter (fun p => !p.2.isUnitRep))
      = (mergeJoin lexLt (fun a b => a == b) (fun y x => (y + x).norm)
        (u.val.length + v.val.length) u.val v.val).filter (fun p => !p.2.isUnitRep) :=
  collectBy_of_canon lexLt (fun a b => a == b) _
    (sorted_filter lexLt lexLt_trans _ _
      (mergeJoin_sorted lexLt (fun a b => a == b) _ lexLt_trans (fun _ _ h => listBeqEq h)
        lexLt_tri _ _ _ (Nat.le_refl _) (sortedV u) (sortedV v)))
    (fun p hp => by
      have hm := mem_filter_of _ _ p hp
      refine ⟨?_, ?_⟩
      · cases mem_mergeJoin lexLt (fun a b => a == b) (fun y x => (y + x).norm) _ _ _ p
          hm.1 with
        | inl h => exact (canonV u p h).1
        | inr h =>
          cases h with
          | inl h => exact (canonV v p h).1
          | inr h =>
            obtain ⟨x, y, _, _, hp⟩ := h
            rw [hp]
            exact BPair.norm_congr (BPair.norm_oneValue _)
      · have h2 := hm.2
        cases hu : p.2.isUnitRep with
        | false => rfl
        | true =>
          rw [hu] at h2
          exact Bool.noConfusion h2)

private theorem addV_widths {k : Nat} (u v : SVec k) :
    ((mergeJoin lexLt (fun a b => a == b) (fun y x => (y + x).norm)
      (u.val.length + v.val.length) u.val v.val).filter (fun p => !p.2.isUnitRep)).all
      (fun p => p.1.length == k) = true :=
  all_of_mem_intro _ _ (fun p hp => by
    have hm := (mem_filter_of _ _ p hp).1
    cases mem_mergeJoin lexLt (fun a b => a == b) (fun y x => (y + x).norm) _ _ _ p hm with
    | inl h => exact decide_eq_true (width_of_mem u p h)
    | inr h =>
      cases h with
      | inl h => exact decide_eq_true (width_of_mem v p h)
      | inr h =>
        obtain ⟨x, _, hx, _, hp⟩ := h
        rw [hp]
        exact decide_eq_true (width_of_mem u x hx))

/-- Two vectors' sum at the walk: the two displays merged at the
joined key's canonical sum with the unit entries withdrawn
(`ground.mergeJoin`), the display collected outright
(`ground.collectBy_of_canon`; `addV_read` its read as the collection
of the displays' join). -/
def addV {k : Nat} (u v : SVec k) : SVec k :=
  ⟨(mergeJoin lexLt (fun a b => a == b) (fun y x => (y + x).norm)
      (u.val.length + v.val.length) u.val v.val).filter (fun p => !p.2.isUnitRep),
   addV_canon u v, addV_widths u v⟩

/-- The merged sum is the collection of the displays' join: both
collected, and the merge's fold at every key the two displays' folds
(`ground.keyFoldB_mergeJoin`, `ground.keyFoldB_unitFilter`), the
join's fold. -/
theorem addV_read {k : Nat} (u v : SVec k) :
    (addV u v).val = collectBy lexLt (fun a b => a == b) (u.val ++ v.val) := by
  refine sorted_unique lexLt (fun a b => a == b) lexLt_trans (fun _ _ h => listBeqEq h)
    lexLt_irrefl listEqBeq _ _ (sortedV (addV u v))
    (collectBy_sorted lexLt (fun a b => a == b) lexLt_trans (fun _ _ h => listBeqEq h)
      lexLt_tri _)
    (canonV (addV u v)) (fun p hp => mem_normFilter _ p hp) (fun k => ?_)
  refine BPair.oneValue_trans (keyFoldB_unitFilter (fun a b : List Nat => a == b) k _) ?_
  refine BPair.oneValue_trans (keyFoldB_mergeJoin lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) (fun y x => (y + x).norm)
    (fun x y => BPair.norm_oneValue _) k _ u.val v.val) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (keyFoldB_collectBy lexLt (fun a b => a == b) (fun _ _ h => listBeqEq h) k _))
  exact BPair.oneValue_symm (famFold_append_ov bpairFoldLaws _ u.val v.val)

/-- The scalar one, the vacant power's own vector. -/
def unitV : SVec 0 := collect 0 [([], BPair.ofNat 1)] rfl

private theorem tensorV_widths {k l : Nat} (u : SVec k) (v : SVec l) :
    (u.val.flatMap (fun p => v.val.map (fun q => (p.1 ++ q.1, (p.2 * q.2).norm)))).all
      (fun p => p.1.length == k + l) = true := by
  rw [all_flatMap]
  refine all_of_mem_intro _ _ (fun p hp => ?_)
  rw [all_map]
  refine all_of_mem_intro _ _ (fun q hq => ?_)
  exact decide_eq_true (by
    rw [length_append, width_of_mem u p hp, width_of_mem v q hq])

/-- The tensor of two vectors, the monomials concatenated at the
coefficients' products, collected. -/
def tensorV {k l : Nat} (u : SVec k) (v : SVec l) : SVec (k + l) :=
  collect (k + l) (u.val.flatMap (fun p => v.val.map (fun q => (p.1 ++ q.1, (p.2 * q.2).norm))))
    (tensorV_widths u v)

private theorem prim_widths {k : Nat} (v : SVec k) (cs : List BPair) :
    (List.zipWith (fun p c => (p.1, c)) v.val cs).all (fun p => p.1.length == k) = true :=
  all_zipWith_left _ _ (fun p : List Nat × BPair => p.1.length == k)
    (fun _ _ h => h) v.val cs v.property.2

/-- A vector at its primitive representative, the coefficients
stripped at their shared count (`thm:windowsep`'s strip),
collected. -/
def prim {k : Nat} (v : SVec k) : SVec k :=
  let c := BPair.listContent (v.val.map Prod.snd)
  collect k (List.zipWith (fun p c => (p.1, c)) v.val (BPair.listPrim c (v.val.map Prod.snd)))
    (prim_widths v _)

private theorem ofH_widths (v : HVec) :
    ((List.zipWith (fun m x => (m, x)) (monomialsAt v.content) v.coords).filter
      (fun p => !decide (p.2.oneValue BPair.unit))).all
      (fun p => p.1.length == sumNat v.content) = true :=
  all_of_mem_intro _ _ (fun p hp =>
    all_of_mem _ _ (all_zipWith_left (fun m x => (m, x))
      (fun p : List Nat × BPair => p.1.length == sumNat v.content)
      (fun m => m.length == sumNat v.content) (fun _ _ h => h) _ v.coords
      (monomialsAt_widths v.content)) p (mem_filter_of _ _ p hp).1)

/-- A dense coordinate family's vector at its occupied monomials
(`blockcount.HVec`, the letters' exhibits). -/
def ofH (v : HVec) : SVec (sumNat v.content) :=
  collect (sumNat v.content)
    ((List.zipWith (fun m x => (m, x)) (monomialsAt v.content) v.coords).filter
      (fun p => !decide (p.2.oneValue BPair.unit)))
    (ofH_widths v)

private theorem relabelV_widths (σ : List Nat) {k : Nat} (v : SVec k) :
    (v.val.map (fun p => (places.expo p.1 σ, p.2))).all
      (fun p => p.1.length == σ.length) = true := by
  rw [all_map]
  exact all_of_pointwise _ _ (fun p => decide_eq_true (length_map _ σ))

/-- The place action on a vector at a slot permutation, the
permuted display of every occupied monomial (`con:places`): the
monomial at a slot reads the source's at the permutation's slot. -/
def relabelV (σ : List Nat) {k : Nat} (v : SVec k) : SVec σ.length :=
  collect σ.length (v.val.map (fun p => (places.expo p.1 σ, p.2))) (relabelV_widths σ v)

private theorem actT_widths (m : memtable.SMap) (neg : Bool) (s : Nat) {k : Nat}
    (v : SVec k) :
    (v.val.flatMap (fun p => m.filterMap (fun e =>
      if getAt 0 p.1 s == e.2.1 then
        some (p.1.set s e.1, if neg then (p.2 * e.2.2).swap else p.2 * e.2.2)
      else none))).all (fun p => p.1.length == k) = true := by
  rw [all_flatMap]
  refine all_of_mem_intro _ _ (fun p hp => ?_)
  refine all_filterMap_mem _ _ m (fun e _ y hy => ?_)
  by_cases hc : (getAt 0 p.1 s == e.2.1) = true
  · rw [if_pos hc] at hy
    rw [← Option.some.inj hy]
    exact decide_eq_true (by rw [length_set]; exact width_of_mem v p hp)
  · rw [if_neg hc] at hy
    exact nomatch (show (none : Option (List Nat × BPair)) = some y from hy)

/-- A sparse map's action at one slot: each entry reads the source
key at the slot to the target at the coefficient, the balance
partner at a stated side. -/
def actT (m : memtable.SMap) (neg : Bool) (s : Nat) {k : Nat} (v : SVec k) : SVec k :=
  collect k (v.val.flatMap (fun p => m.filterMap (fun e =>
    if getAt 0 p.1 s == e.2.1 then
      some (p.1.set s e.1, if neg then (p.2 * e.2.2).swap else p.2 * e.2.2)
    else none)))
    (actT_widths m neg s v)

private theorem raiseT_widths (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) :
    ((List.range sig.length).flatMap (fun s =>
      if getAt false sig s then (actT (getAt [] T.lowers i) true s v).val
      else (actT (getAt [] T.raises i) false s v).val)).all
      (fun p => p.1.length == sig.length) = true := by
  rw [all_flatMap]
  refine all_of_pointwise _ _ (fun s => ?_)
  by_cases hs : getAt false sig s = true
  · rw [if_pos hs]
    exact (actT (getAt [] T.lowers i) true s v).property.2
  · rw [if_neg hs]
    exact (actT (getAt [] T.raises i) false s v).property.2

/-- A table's simple raising at a slot signature: the raising at an
undaggered slot, and at a daggered slot the dual action, the
balance partner of the lowering (`lem:dualread`(i)). -/
def raiseT (T : memtable.Table) (sig : List Bool) (i : Nat) (v : SVec sig.length) :
    SVec sig.length :=
  collect sig.length ((List.range sig.length).flatMap (fun s =>
    if getAt false sig s then (actT (getAt [] T.lowers i) true s v).val
    else (actT (getAt [] T.raises i) false s v).val))
    (raiseT_widths T sig i v)

private theorem lowerT_widths (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) :
    ((List.range sig.length).flatMap (fun s =>
      if getAt false sig s then (actT (getAt [] T.raises i) true s v).val
      else (actT (getAt [] T.lowers i) false s v).val)).all
      (fun p => p.1.length == sig.length) = true := by
  rw [all_flatMap]
  refine all_of_pointwise _ _ (fun s => ?_)
  by_cases hs : getAt false sig s = true
  · rw [if_pos hs]
    exact (actT (getAt [] T.raises i) true s v).property.2
  · rw [if_neg hs]
    exact (actT (getAt [] T.lowers i) false s v).property.2

/-- A table's simple lowering at a slot signature, the lowering at
an undaggered slot and the balance partner of the raising at a
daggered one. -/
def lowerT (T : memtable.Table) (sig : List Bool) (i : Nat) (v : SVec sig.length) :
    SVec sig.length :=
  collect sig.length ((List.range sig.length).flatMap (fun s =>
    if getAt false sig s then (actT (getAt [] T.raises i) true s v).val
    else (actT (getAt [] T.lowers i) false s v).val))
    (lowerT_widths T sig i v)

/-- An occupied tensor monomial is the concatenation of one
occupied monomial from each factor. -/
theorem mem_tensorV {k l : Nat} (u : SVec k) (v : SVec l)
    (p : List Nat × BPair) (hp : p ∈ (tensorV u v).val) :
    ∃ a, a ∈ u.val ∧ ∃ b, b ∈ v.val ∧ a.1 ++ b.1 = p.1 := by
  obtain ⟨q, hq, hqp⟩ := mem_collectBy_key lexLt (fun a b => a == b) _ p hp
  obtain ⟨a, ha, hqa⟩ := mem_flatMap_of _ _ q hq
  obtain ⟨b, hb, hqb⟩ := mem_map_of _ _ q hqa
  refine ⟨a, ha, b, hb, ?_⟩
  exact (congrArg Prod.fst hqb).trans hqp

/-- Scaling keeps every occupied monomial inside the source
vector's support. -/
theorem mem_scaleV {k : Nat} (c : BPair) (v : SVec k)
    (p : List Nat × BPair) (hp : p ∈ (scaleV c v).val) :
    ∃ q, q ∈ v.val ∧ q.1 = p.1 := by
  obtain ⟨r, hr, hrp⟩ := mem_collectBy_key lexLt (fun a b => a == b) _ p hp
  obtain ⟨q, hq, hqr⟩ := mem_map_of _ _ r hr
  exact ⟨q, hq, (congrArg Prod.fst hqr).trans hrp⟩

/-- An occupied monomial of a sum occurs in a factor. -/
theorem mem_addV {k : Nat} (u v : SVec k)
    (p : List Nat × BPair) (hp : p ∈ (addV u v).val) :
    (∃ q, q ∈ u.val ∧ q.1 = p.1) ∨ (∃ q, q ∈ v.val ∧ q.1 = p.1) := by
  rw [addV_read] at hp
  obtain ⟨q, hq, hqp⟩ := mem_collectBy_key lexLt (fun a b => a == b) _ p hp
  cases mem_append_of u.val v.val hq with
  | inl h => exact Or.inl ⟨q, h, hqp⟩
  | inr h => exact Or.inr ⟨q, h, hqp⟩

/-- Every occupied monomial after one sparse action names its
source monomial and one stored entry at the slot's source key. -/
theorem mem_actT (M : memtable.SMap) (neg : Bool) (s : Nat) {k : Nat}
    (v : SVec k) (q : List Nat × BPair) (hq : q ∈ (actT M neg s v).val) :
    ∃ p, p ∈ v.val ∧ ∃ e, e ∈ M ∧
      getAt 0 p.1 s = e.2.1 ∧ p.1.set s e.1 = q.1 := by
  obtain ⟨r, hr, hrq⟩ := mem_collectBy_key lexLt (fun a b => a == b) _ q hq
  obtain ⟨p, hp, hrp⟩ := mem_flatMap_of _ _ r hr
  obtain ⟨e, he, her⟩ := mem_filterMap_of _ _ r hrp
  by_cases hs : (getAt 0 p.1 s == e.2.1) = true
  · rw [if_pos hs] at her
    exact ⟨p, hp, e, he, beqEqOf hs, (congrArg Prod.fst (Option.some.inj her)).trans hrq⟩
  · rw [if_neg hs] at her
    exact nomatch (show (none : Option (List Nat × BPair)) = some r from her)

/-- A simple raising's occupied monomial comes from one slot's
stored raising, or its dual lowering at a daggered slot. -/
theorem mem_raiseT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (q : List Nat × BPair) (hq : q ∈ (raiseT T sig i v).val) :
    ∃ s, s < sig.length ∧ ∃ p, p ∈ v.val ∧ ∃ e,
      e ∈ (if getAt false sig s then getAt [] T.lowers i else getAt [] T.raises i) ∧
      getAt 0 p.1 s = e.2.1 ∧ p.1.set s e.1 = q.1 := by
  obtain ⟨r, hr, hrq⟩ := mem_collectBy_key lexLt (fun a b => a == b) _ q hq
  obtain ⟨s, hs, hrs⟩ := mem_flatMap_of _ _ r hr
  refine ⟨s, ltOfMemRange hs, ?_⟩
  by_cases hd : getAt false sig s = true
  · rw [if_pos hd] at hrs
    obtain ⟨p, hp, e, he, heq, her⟩ := mem_actT _ true s v r hrs
    rw [if_pos hd]
    exact ⟨p, hp, e, he, heq, her.trans hrq⟩
  · rw [if_neg hd] at hrs
    obtain ⟨p, hp, e, he, heq, her⟩ := mem_actT _ false s v r hrs
    rw [if_neg hd]
    exact ⟨p, hp, e, he, heq, her.trans hrq⟩

/-- A simple lowering's occupied monomial comes from one slot's
stored lowering, or its dual raising at a daggered slot. -/
theorem mem_lowerT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (q : List Nat × BPair) (hq : q ∈ (lowerT T sig i v).val) :
    ∃ s, s < sig.length ∧ ∃ p, p ∈ v.val ∧ ∃ e,
      e ∈ (if getAt false sig s then getAt [] T.raises i else getAt [] T.lowers i) ∧
      getAt 0 p.1 s = e.2.1 ∧ p.1.set s e.1 = q.1 := by
  obtain ⟨r, hr, hrq⟩ := mem_collectBy_key lexLt (fun a b => a == b) _ q hq
  obtain ⟨s, hs, hrs⟩ := mem_flatMap_of _ _ r hr
  refine ⟨s, ltOfMemRange hs, ?_⟩
  by_cases hd : getAt false sig s = true
  · rw [if_pos hd] at hrs
    obtain ⟨p, hp, e, he, heq, her⟩ := mem_actT _ true s v r hrs
    rw [if_pos hd]
    exact ⟨p, hp, e, he, heq, her.trans hrq⟩
  · rw [if_neg hd] at hrs
    obtain ⟨p, hp, e, he, heq, her⟩ := mem_actT _ false s v r hrs
    rw [if_neg hd]
    exact ⟨p, hp, e, he, heq, her.trans hrq⟩

/-- A monomial's weight at a table and a signature: the keys' coroot
lists summed, an undaggered slot's own and a daggered slot's
balance partner, at the canonical representatives. -/
def weightT (T : memtable.Table) (sig : List Bool) (m : List Nat) : List BPair :=
  (List.range sig.length).foldl (fun acc s =>
    let w := memtable.keyWeight T (getAt 0 m s)
    List.zipWith (fun a b => (a + b).norm) acc
      (if getAt false sig s then w.map BPair.swap else w))
    (List.replicate T.rank BPair.unit)

/-- A vector's weight at a table, its first occupied monomial's. -/
def weightV (T : memtable.Table) (sig : List Bool) {k : Nat} (v : SVec k) : List BPair :=
  match v.val.head? with
  | none => List.replicate T.rank BPair.unit
  | some p => weightT T sig p.1

/-- Every monomial uses the stated table's keys, the finite
carrier of the slot power. -/
def keysRead (n : Nat) {k : Nat} (v : SVec k) : Prop :=
  v.val.all (fun p => p.1.all (fun i => decide (i < n))) = true

instance instSlotpower3 (n : Nat) {k : Nat} (v : SVec k) : Decidable (keysRead n v) :=
  inferInstanceAs (Decidable (_ = _))

/-- A vector is homogeneous at a stated coroot list when every
occupied monomial has that weight. The vacant vector passes at
every list. -/
def homogRead (T : memtable.Table) (sig : List Bool) {k : Nat}
    (v : SVec k) (w : List BPair) : Prop :=
  v.val.all (fun p => weightT T sig p.1 == w) = true

instance instSlotpower4 (T : memtable.Table) (sig : List Bool) {k : Nat}
    (v : SVec k) (w : List BPair) : Decidable (homogRead T sig v w) :=
  inferInstanceAs (Decidable (_ = _))

/-- A slot's signed weight has the table rank at a valid
monomial key. -/
private theorem slotWeight_length (T : memtable.Table) (sig : List Bool) (m : List Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hm : m.length = sig.length) (hk : m.all (fun i => decide (i < T.keys)) = true)
    (s : Nat) (hs : s < sig.length) :
    (if getAt false sig s then (memtable.keyWeight T (getAt 0 m s)).map BPair.swap
      else memtable.keyWeight T (getAt 0 m s)).length = T.rank := by
  have hsm : s < m.length := by rw [hm]; exact hs
  have hkey : getAt 0 m s < T.keys := of_decide_eq_true
    (all_of_mem _ m hk _ (mem_getAt 0 m s hsm))
  have hlen := memtable.keyWeight_length T hd hr _ hkey
  by_cases hdg : getAt false sig s = true
  · rw [if_pos hdg, length_map]; exact hlen
  · rw [if_neg hdg]; exact hlen

/-- At valid keys the weight has one entry per simple index,
including the vacant power. -/
theorem weightT_length (T : memtable.Table) (sig : List Bool) (m : List Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hm : m.length = sig.length) (hk : m.all (fun i => decide (i < T.keys)) = true) :
    (weightT T sig m).length = T.rank := by
  apply foldl_invariant (fun w : List BPair => w.length = T.rank)
  · exact length_replicate _ _
  · intro s hs w hw
    apply length_zipWith _ _ _ T.rank hw
    exact slotWeight_length T sig m hd hr hm hk s (ltOfMemRange hs)

/-- The slot's canonical join is the representative of the
componentwise sum. -/
private theorem weightStep_read : ∀ a b : List BPair,
    List.zipWith (fun x y => (x + y).norm) a b = poly.pnorm (elim.vecAdd a b)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => congrArg ((x + y).norm :: ·) (weightStep_read a b)

/-- Canonicalizing each slot's running sum gives the canonical
representative of the uncollected vector fold. -/
private theorem weightFold_norm (n : Nat) (g : Nat → List BPair) :
    ∀ (l : List Nat) (a : List BPair), a.length = n →
      (∀ k ∈ l, (g k).length = n) →
      l.foldl (fun acc k => List.zipWith (fun x y => (x + y).norm) acc (g k)) (poly.pnorm a)
        = poly.pnorm (l.foldl (fun acc k => elim.vecAdd acc (g k)) a)
  | [], _, _, _ => rfl
  | k :: l, a, ha, hg => by
    change l.foldl (fun acc j => List.zipWith (fun x y => (x + y).norm) acc (g j))
      (List.zipWith (fun x y => (x + y).norm) (poly.pnorm a) (g k))
      = poly.pnorm (l.foldl (fun acc j => elim.vecAdd acc (g j)) (elim.vecAdd a (g k)))
    rw [weightStep_read, elim.pnorm_vecAdd_left a (g k) (ha.trans (hg k (List.Mem.head l)).symm)]
    exact weightFold_norm n g l _ (elim.length_vecAdd a (g k) n ha (hg k (List.Mem.head l)))
      (fun j hj => hg j (List.Mem.tail k hj))

/-- The monomial weight is the canonical vector sum of its
signed slot weights at the actual key list. -/
theorem weightT_vsum (T : memtable.Table) (sig : List Bool) (m : List Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hm : m.length = sig.length) (hk : m.all (fun i => decide (i < T.keys)) = true) :
    weightT T sig m = poly.pnorm (elim.vsum T.rank
      (fun s => if getAt false sig s then (memtable.keyWeight T (getAt 0 m s)).map BPair.swap
        else memtable.keyWeight T (getAt 0 m s)) (List.range sig.length)) := by
  have hseed : poly.pnorm (List.replicate T.rank BPair.unit) = List.replicate T.rank BPair.unit := by
    change (List.replicate T.rank BPair.unit).map BPair.norm = _
    rw [map_replicate]
    rfl
  have h := weightFold_norm T.rank
    (fun s => if getAt false sig s then (memtable.keyWeight T (getAt 0 m s)).map BPair.swap
      else memtable.keyWeight T (getAt 0 m s))
    (List.range sig.length) (List.replicate T.rank BPair.unit) (length_replicate _ _) ?_
  · rw [hseed] at h
    exact h
  · intro s hs
    exact slotWeight_length T sig m hd hr hm hk s (ltOfMemRange hs)

/-- Each simple coroot of a monomial is the signed fold of
the table's stored diagonal entries at its slots. -/
theorem weightT_entry (T : memtable.Table) (sig : List Bool) (m : List Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hm : m.length = sig.length) (hk : m.all (fun i => decide (i < T.keys)) = true)
    (i : Nat) (hi : i < T.rank) :
    (getAt BPair.unit (weightT T sig m) i).oneValue
      (bsum (fun s =>
        let c := getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 m s)
        if getAt false sig s then c.swap else c) (List.range sig.length)) := by
  rw [weightT_vsum T sig m hd hr hm hk]
  refine BPair.oneValue_trans (poly.oneValue_getAt i (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans (elim.vsum_entry_members T.rank _ (List.range sig.length)
    (fun s hs => slotWeight_length T sig m hd hr hm hk s
      (ltOfMemRange (mem_of_countOf_pos _ _ hs))) i hi) ?_
  apply foldB_congr_members
  intro s hs
  have hsm : s < m.length := by
    rw [hm]; exact ltOfMemRange (mem_of_countOf_pos _ _ hs)
  have hkey : getAt 0 m s < T.keys := of_decide_eq_true
    (all_of_mem _ m hk _ (mem_getAt 0 m s hsm))
  have hi' : i < T.hdiag.length := by rw [hr]; exact hi
  by_cases hg : getAt false sig s = true
  · rw [if_pos hg, if_pos hg, getAt_mapT BPair.unit BPair.unit BPair.swap rfl,
      memtable.keyWeight_getAt T hd _ i hkey hi']
    exact BPair.oneValue_refl _
  · rw [if_neg hg, if_neg hg, memtable.keyWeight_getAt T hd _ i hkey hi']
    exact BPair.oneValue_refl _

/-- At the table's finite carrier a monomial's weight is its
own canonical representative. -/
theorem weightT_pnorm (T : memtable.Table) (sig : List Bool) (m : List Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hm : m.length = sig.length) (hk : m.all (fun i => decide (i < T.keys)) = true) :
    poly.pnorm (weightT T sig m) = weightT T sig m := by
  rw [weightT_vsum T sig m hd hr hm hk, poly.pnorm_pnorm]

/-- A concatenated monomial at the joined signatures reads
the sum of its two weights, at the canonical representative. -/
theorem weightT_append (T : memtable.Table) (sig tau : List Bool) (m n : List Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hm : m.length = sig.length) (hn : n.length = tau.length)
    (hkm : m.all (fun i => decide (i < T.keys)) = true)
    (hkn : n.all (fun i => decide (i < T.keys)) = true) :
    weightT T (sig ++ tau) (m ++ n)
      = poly.pnorm (elim.vecAdd (weightT T sig m) (weightT T tau n)) := by
  have hlen : (m ++ n).length = (sig ++ tau).length := by
    rw [length_append, length_append, hm, hn]
  have hkeys : (m ++ n).all (fun i => decide (i < T.keys)) = true := by
    rw [all_append, hkm, hkn]; rfl
  have hma := weightT_length T sig m hd hr hm hkm
  have hnb := weightT_length T tau n hd hr hn hkn
  have hmn := weightT_length T (sig ++ tau) (m ++ n) hd hr hlen hkeys
  have hadd := elim.length_vecAdd (weightT T sig m) (weightT T tau n) T.rank hma hnb
  calc
    weightT T (sig ++ tau) (m ++ n)
        = poly.pnorm (weightT T (sig ++ tau) (m ++ n)) :=
      (weightT_pnorm T (sig ++ tau) (m ++ n) hd hr hlen hkeys).symm
    _ = poly.pnorm (elim.vecAdd (weightT T sig m) (weightT T tau n)) := by
      apply poly.pnorm_congr _ _ (hmn.trans hadd.symm)
      apply poly.oneValue_of_entries _ _ (hmn.trans hadd.symm)
      intro i hi
      have hir : i < T.rank := by rw [← hmn]; exact hi
      let f := fun (s : List Bool) (a : List Nat) (j : Nat) =>
        let c := getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 a j)
        if getAt false s j then c.swap else c
      have hc := weightT_entry T (sig ++ tau) (m ++ n) hd hr hlen hkeys i hir
      have ha := weightT_entry T sig m hd hr hm hkm i hir
      have hb := weightT_entry T tau n hd hr hn hkn i hir
      have hsplit : (bsum (f (sig ++ tau) (m ++ n)) (List.range (sig ++ tau).length)).oneValue
          (bsum (f sig m) (List.range sig.length) + bsum (f tau n) (List.range tau.length)) := by
        rw [length_append, range_split sig.length tau.length]
        refine BPair.oneValue_trans (famFold_append_ov bpairFoldLaws _ _ _) ?_
        apply BPair.add_congr
        · apply bsum_congr_range_ov
          intro s hs
          have hsm : s < m.length := by rw [hm]; exact hs
          change (if getAt false (sig ++ tau) s then
              (getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 (m ++ n) s)).swap
            else getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 (m ++ n) s)).oneValue _
          rw [getAt_append false sig tau s, if_pos hs,
            getAt_append 0 m n s, if_pos hsm]
          exact BPair.oneValue_refl _
        · rw [famFold_map]
          apply bsum_congr_range_ov
          intro s _
          change (if getAt false (sig ++ tau) (sig.length + s) then
              (getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 (m ++ n) (sig.length + s))).swap
            else getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 (m ++ n) (sig.length + s))).oneValue _
          rw [getAt_append_add false sig tau s, ← hm, getAt_append_add 0 m n s]
          exact BPair.oneValue_refl _
      rw [elim.getAt_vecAdd _ _ i (by rw [hma]; exact hir) (by rw [hnb]; exact hir)]
      exact BPair.oneValue_trans hc (BPair.oneValue_trans hsplit
        (BPair.add_congr (BPair.oneValue_symm ha) (BPair.oneValue_symm hb)))

/-- The selected weight is canonical at every vector in the
table's finite carrier, the vacant vector's weight the unit list. -/
theorem weightV_pnorm (T : memtable.Table) (sig : List Bool) {k : Nat} (v : SVec k)
    (hwidth : k = sig.length)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hk : keysRead T.keys v) : poly.pnorm (weightV T sig v) = weightV T sig v := by
  cases he : v.val with
  | nil =>
    unfold weightV
    rw [he]
    change (List.replicate T.rank BPair.unit).map BPair.norm = _
    rw [map_replicate]
    rfl
  | cons p ps =>
    have hp : p ∈ v.val := by rw [he]; exact List.Mem.head _
    unfold weightV
    rw [he]
    exact weightT_pnorm T sig p.1 hd hr ((width_of_mem v p hp).trans hwidth) (all_of_mem _ v.val hk p hp)

/-- An occupied vector's selected weight is the common weight
of its occupied monomials. -/
theorem weightV_homog (T : memtable.Table) (sig : List Bool) {k : Nat}
    (v : SVec k) (w : List BPair) (h : homogRead T sig v w) (hv : v.val ≠ []) :
    weightV T sig v = w := by
  cases he : v.val with
  | nil => exact False.elim (hv he)
  | cons p ps =>
    change (v.val.all (fun p => weightT T sig p.1 == w)) = true at h
    rw [he] at h
    have hp := listBeqEq (andSplitB h).1
    unfold weightV
    rw [he]
    exact hp

/-- The selected weight has the table rank for a vector at its
slot signature and valid keys. -/
theorem weightV_length (T : memtable.Table) (sig : List Bool) {k : Nat} (v : SVec k)
    (hwidth : k = sig.length)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hk : keysRead T.keys v) : (weightV T sig v).length = T.rank := by
  cases he : v.val with
  | nil => unfold weightV; rw [he]; exact length_replicate _ _
  | cons p ps =>
    have hp : p ∈ v.val := by rw [he]; exact List.Mem.head _
    have hlen := width_of_mem v p hp
    have hkeys := all_of_mem _ v.val hk p hp
    unfold weightV
    rw [he]
    exact weightT_length T sig p.1 hd hr (hlen.trans hwidth) hkeys

/-- Scaling preserves the finite monomial carrier. -/
theorem keysRead_scaleV (n : Nat) {k : Nat} (c : BPair) (v : SVec k)
    (h : keysRead n v) : keysRead n (scaleV c v) := by
  apply all_of_mem_intro
  intro p hp
  obtain ⟨q, hq, he⟩ := mem_scaleV c v p hp
  rw [← he]
  exact all_of_mem _ v.val h q hq

/-- The sum stays in the factors' finite monomial carrier. -/
theorem keysRead_addV (n : Nat) {k : Nat} (u v : SVec k)
    (hu : keysRead n u) (hv : keysRead n v) : keysRead n (addV u v) := by
  apply all_of_mem_intro
  intro p hp
  cases mem_addV u v p hp with
  | inl h =>
    obtain ⟨q, hq, he⟩ := h
    rw [← he]; exact all_of_mem _ u.val hu q hq
  | inr h =>
    obtain ⟨q, hq, he⟩ := h
    rw [← he]; exact all_of_mem _ v.val hv q hq

/-- The tensor stays in the factors' finite monomial carrier. -/
theorem keysRead_tensorV (n : Nat) {k l : Nat} (u : SVec k) (v : SVec l)
    (hu : keysRead n u) (hv : keysRead n v) : keysRead n (tensorV u v) := by
  apply all_of_mem_intro
  intro p hp
  obtain ⟨a, ha, b, hb, he⟩ := mem_tensorV u v p hp
  rw [← he, all_append, all_of_mem _ u.val hu a ha, all_of_mem _ v.val hv b hb]
  rfl

/-- The tensor of homogeneous vectors has the joined weight,
at the sum of the two canonical coroot lists. -/
theorem homogRead_tensorV (T : memtable.Table) (sig tau : List Bool)
    {k l : Nat} (u : SVec k) (v : SVec l) (a b : List BPair)
    (hu : k = sig.length) (hv : l = tau.length)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hku : keysRead T.keys u) (hkv : keysRead T.keys v)
    (ha : homogRead T sig u a) (hb : homogRead T tau v b) :
    homogRead T (sig ++ tau) (tensorV u v) (poly.pnorm (elim.vecAdd a b)) := by
  apply all_of_mem_intro
  intro p hp
  obtain ⟨x, hx, y, hy, he⟩ := mem_tensorV u v p hp
  have hxa : weightT T sig x.1 = a := listBeqEq (all_of_mem _ u.val ha x hx)
  have hyb : weightT T tau y.1 = b := listBeqEq (all_of_mem _ v.val hb y hy)
  rw [← he, weightT_append T sig tau x.1 y.1 hd hr
    ((width_of_mem u x hx).trans hu) ((width_of_mem v y hy).trans hv)
    (all_of_mem _ u.val hku x hx) (all_of_mem _ v.val hkv y hy), hxa, hyb]
  exact listEqBeq _

/-- Scaling preserves a vector's stated homogeneous weight. -/
theorem homogRead_scaleV (T : memtable.Table) (sig : List Bool) {k : Nat}
    (c : BPair) (v : SVec k) (w : List BPair) (h : homogRead T sig v w) :
    homogRead T sig (scaleV c v) w := by
  apply all_of_mem_intro
  intro p hp
  obtain ⟨q, hq, he⟩ := mem_scaleV c v p hp
  rw [← he]
  exact all_of_mem _ v.val h q hq

/-- The sum of two vectors at one weight has that weight. -/
theorem homogRead_addV (T : memtable.Table) (sig : List Bool) {k : Nat}
    (u v : SVec k) (w : List BPair)
    (hu : homogRead T sig u w) (hv : homogRead T sig v w) :
    homogRead T sig (addV u v) w := by
  apply all_of_mem_intro
  intro p hp
  cases mem_addV u v p hp with
  | inl h =>
    obtain ⟨q, hq, he⟩ := h
    rw [← he]; exact all_of_mem _ u.val hu q hq
  | inr h =>
    obtain ⟨q, hq, he⟩ := h
    rw [← he]; exact all_of_mem _ v.val hv q hq

/-- A primitive representative keeps a vector's homogeneous
weight, the coefficient strip fixing the monomial keys. -/
theorem homogRead_prim (T : memtable.Table) (sig : List Bool) {k : Nat}
    (v : SVec k) (w : List BPair) (h : homogRead T sig v w) :
    homogRead T sig (prim v) w :=
  collectBy_all_keys lexLt (fun a b => a == b) (fun m => weightT T sig m == w) _
    (all_zipWith_left (fun (p : List Nat × BPair) (c : BPair) => (p.1, c))
      (fun p : List Nat × BPair => weightT T sig p.1 == w) (fun p => weightT T sig p.1 == w)
      (fun _ _ h => h) v.val _ h)

/-- A primitive representative stays in the finite monomial
carrier, the coefficient strip fixing the monomial keys. -/
theorem keysRead_prim (n : Nat) {k : Nat} (v : SVec k) (h : keysRead n v) :
    keysRead n (prim v) :=
  collectBy_all_keys lexLt (fun a b => a == b) (fun m => m.all (fun i => decide (i < n))) _
    (all_zipWith_left (fun (p : List Nat × BPair) (c : BPair) => (p.1, c))
      (fun p : List Nat × BPair => p.1.all (fun i => decide (i < n)))
      (fun p => p.1.all (fun i => decide (i < n)))
      (fun _ _ h => h) v.val _ h)

/-- Replacing one slot by a valid table key keeps every slot
inside the table's finite carrier. -/
private theorem keys_set (n b : Nat) (hb : b < n) : ∀ (m : List Nat) (s : Nat),
    m.all (fun i => decide (i < n)) = true →
      (m.set s b).all (fun i => decide (i < n)) = true
  | [], _, _ => rfl
  | _ :: m, 0, h => by
    change (decide (b < n) && m.all (fun i => decide (i < n))) = true
    rw [decide_eq_true hb, (andSplitB h).2]
    rfl
  | a :: m, s + 1, h => by
    change (decide (a < n) && (m.set s b).all (fun i => decide (i < n))) = true
    have ha : decide (a < n) = true := (andSplitB h).1
    rw [ha, keys_set n b hb m s (andSplitB h).2]
    rfl

/-- A change at one valid slot adds that key's signed weight
move to the monomial's whole coroot list. -/
theorem weightT_set_add (T : memtable.Table) (sig : List Bool) (m delta : List BPair)
    (ks : List Nat) (s b : Nat)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hk : ks.length = sig.length) (hkeys : ks.all (fun j => decide (j < T.keys)) = true)
    (hs : s < sig.length) (hb : b < T.keys) (hdelta : delta.length = T.rank)
    (hm : weightT T sig ks = m)
    (hmove : poly.oneValue
      (if getAt false sig s then (memtable.keyWeight T b).map BPair.swap else memtable.keyWeight T b)
      (elim.vecAdd
        (if getAt false sig s then (memtable.keyWeight T (getAt 0 ks s)).map BPair.swap
          else memtable.keyWeight T (getAt 0 ks s)) delta)) :
    weightT T sig (ks.set s b) = poly.pnorm (elim.vecAdd m delta) := by
  have hnewlen : (ks.set s b).length = sig.length := (length_set b ks s).trans hk
  have hnewkeys := keys_set T.keys b hb ks s hkeys
  have hmlen : m.length = T.rank := by rw [← hm]; exact weightT_length T sig ks hd hr hk hkeys
  have hlen := weightT_length T sig (ks.set s b) hd hr hnewlen hnewkeys
  have hadd := elim.length_vecAdd m delta T.rank hmlen hdelta
  calc
    weightT T sig (ks.set s b) = poly.pnorm (weightT T sig (ks.set s b)) :=
      (weightT_pnorm T sig (ks.set s b) hd hr hnewlen hnewkeys).symm
    _ = poly.pnorm (elim.vecAdd m delta) := by
      apply poly.pnorm_congr _ _ (hlen.trans hadd.symm)
      apply poly.oneValue_of_entries _ _ (hlen.trans hadd.symm)
      intro i hi
      have hir : i < T.rank := by rw [← hlen]; exact hi
      have hi' : i < T.hdiag.length := by rw [hr]; exact hir
      have hsk : s < ks.length := by rw [hk]; exact hs
      have hsource : getAt 0 ks s < T.keys := of_decide_eq_true
        (all_of_mem _ ks hkeys _ (mem_getAt 0 ks s hsk))
      let f := fun (a : List Nat) (j : Nat) =>
        let c := getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 a j)
        if getAt false sig j then c.swap else c
      let c := getAt BPair.unit delta i
      have hslot : (f (ks.set s b) s).oneValue (f ks s + c) := by
        have h := poly.oneValue_getAt i hmove
        rw [elim.getAt_vecAdd _ delta i
          (by rw [slotWeight_length T sig ks hd hr hk hkeys s hs]; exact hir)
          (by rw [hdelta]; exact hir)] at h
        unfold f
        rw [getAt_set_self 0 b ks s hsk]
        by_cases hg : getAt false sig s = true
        · repeat rw [if_pos hg] at h ⊢
          repeat rw [getAt_mapT BPair.unit BPair.unit BPair.swap rfl] at h
          rw [memtable.keyWeight_getAt T hd b i hb hi',
            memtable.keyWeight_getAt T hd _ i hsource hi'] at h
          exact h
        · repeat rw [if_neg hg] at h ⊢
          rw [memtable.keyWeight_getAt T hd b i hb hi',
            memtable.keyWeight_getAt T hd _ i hsource hi'] at h
          exact h
      have hfold := bsum_split (f (ks.set s b)) (f ks)
        (fun j => if j = s then c else BPair.unit) sig.length (fun j _ => by
          by_cases he : j = s
          · rw [he, if_pos rfl]; exact hslot
          · rw [if_neg he]
            have hf : f (ks.set s b) j = f ks j := by
              unfold f
              rw [getAt_set_ne 0 ks s j b he]
            rw [hf]
            exact BPair.oneValue_symm (BPair.add_unit _))
      have hsingle : (bsum (fun j => if j = s then c else BPair.unit)
          (List.range sig.length)).oneValue c :=
        foldB_pickRange _ s c sig.length hs
          (by rw [if_pos rfl]; exact BPair.oneValue_refl _)
          (fun j _ hj => by rw [if_neg hj]; exact BPair.oneValue_refl _)
      have hnew := weightT_entry T sig (ks.set s b) hd hr hnewlen hnewkeys i hir
      have hold := weightT_entry T sig ks hd hr hk hkeys i hir
      rw [hm] at hold
      rw [elim.getAt_vecAdd m delta i (by rw [hmlen]; exact hir) (by rw [hdelta]; exact hir)]
      exact BPair.oneValue_trans hnew (BPair.oneValue_trans hfold
        (BPair.add_congr (BPair.oneValue_symm hold) hsingle))

/-- A sparse action at its stated key-weight move maps a
homogeneous vector to the moved weight, at either coefficient side. -/
theorem homogRead_actT (T : memtable.Table) (sig : List Bool) (M : memtable.SMap)
    (neg : Bool) (s : Nat) (v : SVec sig.length) (w delta : List BPair)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hs : s < sig.length) (hk : keysRead T.keys v) (hw : homogRead T sig v w)
    (hmove : memtable.keyMoveRead T M (getAt false sig s) delta) :
    homogRead T sig (actT M neg s v) (poly.pnorm (elim.vecAdd w delta)) := by
  apply all_of_mem_intro
  intro q hq
  obtain ⟨p, hp, e, he, hsource, heq⟩ := mem_actT M neg s v q hq
  have hm := all_of_mem _ M hmove.2 e he
  have htarget : e.1 < T.keys := of_decide_eq_true (andSplitB (andSplitB hm).1).1
  have hgrade := of_decide_eq_true (andSplitB hm).2
  have hw' : weightT T sig p.1 = w := listBeqEq (all_of_mem _ v.val hw p hp)
  rw [← heq]
  rw [weightT_set_add T sig w delta p.1 s e.1 hd hr (width_of_mem v p hp)
    (all_of_mem _ v.val hk p hp) hs htarget hmove.1 hw' (by rw [hsource]; exact hgrade)]
  exact listEqBeq _

/-- The Leibniz raising has its simple weight move at the
standard and dual maps' stored grading reads. -/
theorem homogRead_raiseT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (w delta : List BPair)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hk : keysRead T.keys v) (hw : homogRead T sig v w)
    (hu : memtable.keyMoveRead T (getAt [] T.raises i) false delta)
    (hf : memtable.keyMoveRead T (getAt [] T.lowers i) true delta) :
    homogRead T sig (raiseT T sig i v) (poly.pnorm (elim.vecAdd w delta)) := by
  unfold homogRead raiseT collect
  apply collectBy_all_keys lexLt (fun a b : List Nat => a == b)
    (fun m => weightT T sig m == poly.pnorm (elim.vecAdd w delta))
  rw [all_flatMap]
  apply all_of_mem_intro
  intro s hs
  by_cases hg : getAt false sig s = true
  · rw [if_pos hg]
    exact homogRead_actT T sig _ true s v w delta hd hr (ltOfMemRange hs) hk hw
      (by rw [hg]; exact hf)
  · rw [if_neg hg]
    apply homogRead_actT T sig _ false s v w delta hd hr (ltOfMemRange hs) hk hw
    cases hx : getAt false sig s with
    | false => exact hu
    | true => exact False.elim (hg hx)

/-- The Leibniz lowering has its simple weight move at the
standard and dual maps' stored grading reads. -/
theorem homogRead_lowerT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (w delta : List BPair)
    (hd : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank)
    (hk : keysRead T.keys v) (hw : homogRead T sig v w)
    (hf : memtable.keyMoveRead T (getAt [] T.lowers i) false delta)
    (hu : memtable.keyMoveRead T (getAt [] T.raises i) true delta) :
    homogRead T sig (lowerT T sig i v) (poly.pnorm (elim.vecAdd w delta)) := by
  unfold homogRead lowerT collect
  apply collectBy_all_keys lexLt (fun a b : List Nat => a == b)
    (fun m => weightT T sig m == poly.pnorm (elim.vecAdd w delta))
  rw [all_flatMap]
  apply all_of_mem_intro
  intro s hs
  by_cases hg : getAt false sig s = true
  · rw [if_pos hg]
    exact homogRead_actT T sig _ true s v w delta hd hr (ltOfMemRange hs) hk hw
      (by rw [hg]; exact hu)
  · rw [if_neg hg]
    apply homogRead_actT T sig _ false s v w delta hd hr (ltOfMemRange hs) hk hw
    cases hx : getAt false sig s with
    | false => exact hf
    | true => exact False.elim (hg hx)

/-- G2's raising adds the actual Cartan row to every
homogeneous vector at a valid simple index. -/
theorem homogRead_raiseT_G2 (sig : List Bool) (i : Nat) (hi : i < 2)
    (v : SVec sig.length) (w : List BPair)
    (hk : keysRead memtable.genG2.keys v) (hw : homogRead memtable.genG2 sig v w) :
    homogRead memtable.genG2 sig (raiseT memtable.genG2 sig i v)
      (poly.pnorm (elim.vecAdd w (getAt [] sertables.tableG2.cartan i))) :=
  homogRead_raiseT memtable.genG2 sig i v w _ memtable.genG2_diagonals.1
    memtable.genG2_diagonals.2 hk hw (memtable.genG2_raisingGrade i hi).1
      (memtable.genG2_raisingGrade i hi).2

/-- G2's lowering adds the actual Cartan row's balance
partner to every homogeneous vector at a valid simple index. -/
theorem homogRead_lowerT_G2 (sig : List Bool) (i : Nat) (hi : i < 2)
    (v : SVec sig.length) (w : List BPair)
    (hk : keysRead memtable.genG2.keys v) (hw : homogRead memtable.genG2 sig v w) :
    homogRead memtable.genG2 sig (lowerT memtable.genG2 sig i v)
      (poly.pnorm (elim.vecAdd w (poly.neg (getAt [] sertables.tableG2.cartan i)))) :=
  homogRead_lowerT memtable.genG2 sig i v w _ memtable.genG2_diagonals.1
    memtable.genG2_diagonals.2 hk hw (memtable.genG2_loweringGrade i hi).1
      (memtable.genG2_loweringGrade i hi).2

/-- A sparse action whose target keys are valid keeps the
finite monomial carrier. -/
theorem keysRead_actT (n : Nat) (M : memtable.SMap)
    (hM : M.all (fun e => decide (e.1 < n)) = true)
    (neg : Bool) (s : Nat) {k : Nat} (v : SVec k) (h : keysRead n v) :
    keysRead n (actT M neg s v) := by
  apply all_of_mem_intro
  intro q hq
  obtain ⟨p, hp, e, he, _, heq⟩ := mem_actT M neg s v q hq
  rw [← heq]
  exact keys_set n e.1 (of_decide_eq_true (all_of_mem _ M hM e he)) p.1 s
    (all_of_mem _ v.val h p hp)

/-- A raising at a table whose two stored maps stay in its key
list keeps the finite monomial carrier at either slot signature. -/
theorem keysRead_raiseT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (hu : (getAt [] T.raises i).all (fun e => decide (e.1 < T.keys)) = true)
    (hd : (getAt [] T.lowers i).all (fun e => decide (e.1 < T.keys)) = true)
    (v : SVec sig.length) (h : keysRead T.keys v) : keysRead T.keys (raiseT T sig i v) := by
  apply all_of_mem_intro
  intro q hq
  obtain ⟨s, _, p, hp, e, he, _, heq⟩ := mem_raiseT T sig i v q hq
  have hek : e.1 < T.keys := by
    by_cases hg : getAt false sig s = true
    · rw [if_pos hg] at he
      exact of_decide_eq_true (all_of_mem _ _ hd e he)
    · rw [if_neg hg] at he
      exact of_decide_eq_true (all_of_mem _ _ hu e he)
  rw [← heq]
  exact keys_set T.keys e.1 hek p.1 s (all_of_mem _ v.val h p hp)

/-- A lowering at a table whose two stored maps stay in its key
list keeps the finite monomial carrier at either slot signature. -/
theorem keysRead_lowerT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (hu : (getAt [] T.raises i).all (fun e => decide (e.1 < T.keys)) = true)
    (hd : (getAt [] T.lowers i).all (fun e => decide (e.1 < T.keys)) = true)
    (v : SVec sig.length) (h : keysRead T.keys v) : keysRead T.keys (lowerT T sig i v) := by
  apply all_of_mem_intro
  intro q hq
  obtain ⟨s, _, p, hp, e, he, _, heq⟩ := mem_lowerT T sig i v q hq
  have hek : e.1 < T.keys := by
    by_cases hg : getAt false sig s = true
    · rw [if_pos hg] at he
      exact of_decide_eq_true (all_of_mem _ _ hu e he)
    · rw [if_neg hg] at he
      exact of_decide_eq_true (all_of_mem _ _ hd e he)
  rw [← heq]
  exact keys_set T.keys e.1 hek p.1 s (all_of_mem _ v.val h p hp)

/-- The unit-weight read at a table: every coroot read the sum's
unit. -/
def unitWeightT (T : memtable.Table) (sig : List Bool) (m : List Nat) : Bool :=
  (weightT T sig m).all (fun x => decide (x.oneValue BPair.unit))

/-- A table's weight read at the unit: every entry the identity's. -/
def unitWtRead (T : memtable.Table) : Bool :=
  T.wt.all (fun e => e.1 == e.2.1 && decide ((BPair.ofNat 1).oneValue e.2.2))
    && T.wt.length == T.keys

/-- A chain's weight, the entries' product. -/
private def prodW (ch : List (Nat × BPair)) : BPair :=
  ch.foldl (fun a e => a * e.2) (BPair.ofNat 1)

/-- A key's substitutions at a weight: the entries at the key as
their sources with their weights. -/
private def filt (w : memtable.SMap) (k : Nat) : List (Nat × BPair) :=
  w.filterMap (fun e => if e.1 == k then some (e.2.1, e.2.2) else none)

/-- The substitutions per slot. -/
private def subs (w : memtable.SMap) (m : List Nat) : List (List (Nat × BPair)) :=
  m.map (filt w)

/-- One monomial's weighted pairing against a vector: at the unit
weight the monomial's coefficient, and at a stated weight the
substitutions' fold, the keys' weight entries' product against the
substituted monomial's coefficient. -/
def monDotT (T : memtable.Table) (unitW : Bool) (m : List Nat) {k : Nat} (v : SVec k) : BPair :=
  if unitW then coefAt m v
  else (prodLists (subs T.wt m)).foldl (fun acc ch =>
    acc + prodW ch * coefAt (ch.map Prod.fst) v) BPair.unit

/-- The weighted pairing of two vectors at the occupied monomials. -/
def dotT (T : memtable.Table) (unitW : Bool) {k : Nat} (u v : SVec k) : BPair :=
  u.val.foldl (fun acc p => acc + p.2 * monDotT T unitW p.1 v) BPair.unit

private theorem applyWt_widths (T : memtable.Table) {k : Nat} (v : SVec k) :
    (v.val.flatMap (fun p =>
      (prodLists (subs (memtable.sT T.wt) p.1)).map (fun ch =>
        (ch.map Prod.fst, p.2 * prodW ch)))).all (fun p => p.1.length == k) = true := by
  rw [all_flatMap]
  refine all_of_mem_intro _ _ (fun p hp => ?_)
  rw [all_map]
  refine all_of_mem_intro _ _ (fun ch hch => ?_)
  have hl := (mem_prodLists_of (0, BPair.unit) _ ch hch).1
  exact decide_eq_true (by
    show (ch.map Prod.fst).length = k
    rw [length_map, hl]
    show (p.1.map (filt (memtable.sT T.wt))).length = k
    rw [length_map]
    exact width_of_mem v p hp)

/-- The weight applied to a vector, the tensor power at the slots
read on the vector (`con:memtable`'s pairing at the powers): per
occupied monomial and per slot the weight's entries at the slot's
key as their sources, every chain one monomial at the chain's
targets with the coefficient against the weights' product,
collected; a monomial's pairing at a stated weight against a vector
is its coefficient in the applied vector (`monDotT_apply`), so the
weighted pairing is the unit-weight pairing against the applied
vector (`dotT_apply`). -/
def applyWt (T : memtable.Table) {k : Nat} (v : SVec k) : SVec k :=
  collect k (v.val.flatMap (fun p =>
    (prodLists (subs (memtable.sT T.wt) p.1)).map (fun ch =>
      (ch.map Prod.fst, p.2 * prodW ch))))
    (applyWt_widths T v)

private theorem applyAt_widths (m : memtable.SMap) (slots : List Nat) {k : Nat}
    (v : SVec k) :
    (v.val.flatMap (fun p =>
      (prodLists (slots.map (fun s => filt (memtable.sT m) (getAt 0 p.1 s)))).map (fun ch =>
        ((List.zipWith (fun s e => (s, e)) slots ch).foldl
          (fun mo se => mo.set se.1 se.2.1) p.1, p.2 * prodW ch)))).all
      (fun p => p.1.length == k) = true := by
  rw [all_flatMap]
  refine all_of_mem_intro _ _ (fun p hp => ?_)
  rw [all_map]
  refine all_of_pointwise _ _ (fun ch => ?_)
  exact decide_eq_true (by
    show (List.foldl (fun mo se => mo.set se.1 se.2.1) p.1
      (List.zipWith (fun s e => (s, e)) slots ch)).length = k
    rw [foldl_length_inv (fun mo (se : Nat × Nat × BPair) => mo.set se.1 se.2.1)
      (fun mo se => length_set _ mo se.1)]
    exact width_of_mem v p hp)

/-- A sparse map applied to a vector at stated slots: per occupied
monomial the map's entries at each stated slot's key as their
sources, every chain one monomial at the slots set to the chain's
targets with the coefficient against the entries' product,
collected, the action at every stated slot in turn (`actT`) at one
collection. -/
def applyAt (m : memtable.SMap) (slots : List Nat) {k : Nat} (v : SVec k) : SVec k :=
  collect k (v.val.flatMap (fun p =>
    (prodLists (slots.map (fun s => filt (memtable.sT m) (getAt 0 p.1 s)))).map (fun ch =>
      ((List.zipWith (fun s e => (s, e)) slots ch).foldl
        (fun mo se => mo.set se.1 se.2.1) p.1, p.2 * prodW ch))))
    (applyAt_widths m slots v)

/-- The pairing at the sorted walk: the walk over the shared
monomials (`ground.mergeDot`) of the first vector against the second
at the unit weight and against the applied second at a stated
weight (`applyWt`), both in order at the carrier's own read
(`sortedV`; `dotTS_read` its read as the fold `dotT`). -/
def dotTS (T : memtable.Table) (unitW : Bool) {k : Nat} (u v : SVec k) : BPair :=
  let v' := if unitW then v else applyWt T v
  mergeDot lexLt (fun a b => a == b) (u.val.length + v'.val.length) u.val v'.val

/-- The pairing's canonical representative at the walk. -/
def pairT (T : memtable.Table) (uw : Bool) {k : Nat} (u v : SVec k) : BPair :=
  (dotTS T uw u v).norm

/-- At the unit weight an occupied vector has positive
self-pairing, the pairing walk's coefficient squares. -/
theorem pairT_self_pos (T : memtable.Table) {k : Nat} (v : SVec k) (hv : v.val ≠ []) :
    BPair.unit < pairT T true v v := by
  change BPair.unit < (mergeDot lexLt (fun a b : List Nat => a == b)
    (v.val.length + v.val.length) v.val v.val).norm
  rw [mergeDot_self lexLt (fun a b : List Nat => a == b) listEqBeq _ v.val (Nat.le_add_right _ _)]
  apply BPair.lt_congr (BPair.oneValue_refl BPair.unit) (BPair.oneValue_symm (BPair.norm_oneValue _))
  cases he : v.val with
  | nil => exact False.elim (hv he)
  | cons p ps =>
    have hp : p ∈ v.val := by rw [he]; exact List.Mem.head _
    have hcanon := canonV v p hp
    change BPair.unit < p.2 * p.2 + bsum (fun q => q.2 * q.2) ps
    exact unitLtAdd (sq_pos (canon_offUnit hcanon.1 hcanon.2))
      (foldB_nonneg_mem _ ps (fun q _ => unitLeSq q.2))

/-- A monomial's coefficient as the family fold at the key's
guard. -/
private theorem coefAt_read (m : List Nat) {k : Nat} (v : SVec k) :
    (coefAt m v).oneValue (keyFoldB (fun a b : List Nat => a == b) m v.val) :=
  BPair.oneValue_trans
    (foldB_foldl_guard (fun p : List Nat × BPair => p.1 == m)
      (fun p : List Nat × BPair => p.2) v.val BPair.unit)
    (BPair.unit_add _)

/-- A coefficient is the linear fold at the monomial's indicator. -/
theorem coefAt_fold (m : List Nat) {k : Nat} (v : SVec k) :
    (coefAt m v).oneValue (bsum (fun p => p.2 *
      (if p.1 == m then BPair.ofNat 1 else BPair.unit)) v.val) := by
  refine BPair.oneValue_trans (coefAt_read m v) ?_
  refine foldB_congr_members _ _ v.val (fun p _ => ?_)
  change (if p.1 == m then p.2 else BPair.unit).oneValue
    (p.2 * (if p.1 == m then BPair.ofNat 1 else BPair.unit))
  by_cases h : (p.1 == m) = true
  · rw [if_pos h, if_pos h]
    exact BPair.oneValue_symm (BPair.mul_ofNat_one _)
  · rw [if_neg h, if_neg h]
    exact BPair.oneValue_symm (BPair.mul_unit _)

/-- Coefficient reads determine the collected vector. -/
theorem eq_of_coefAt {k : Nat} (u v : SVec k)
    (h : ∀ m, (coefAt m u).oneValue (coefAt m v)) : u = v := by
  apply Subtype.ext
  exact sorted_unique lexLt (fun a b => a == b) lexLt_trans
    (fun _ _ he => listBeqEq he) lexLt_irrefl listEqBeq u.val v.val
    (sortedV u) (sortedV v) (canonV u) (canonV v) (fun m =>
      BPair.oneValue_trans (BPair.oneValue_symm (coefAt_read m u))
        (BPair.oneValue_trans (h m) (coefAt_read m v)))

/-- A linear read of the tensor is the two factors' coefficient
fold at concatenated monomials. -/
theorem fold_tensorV {k l : Nat} (u : SVec k) (v : SVec l) (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (tensorV u v).val).oneValue
      (bsum (fun p => p.2 * bsum (fun q => q.2 * f (p.1 ++ q.1)) v.val) u.val) := by
  refine BPair.oneValue_trans (by apply (foldB_collectBy lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) f _)) ?_
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ u.val) ?_
  refine foldB_congr_members _ _ u.val (fun p _ => ?_)
  rw [famFold_map]
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun q : List Nat × BPair => p.2 * (q.2 * f (p.1 ++ q.1))) v.val
    (fun q _ => ?_)) (by apply (foldB_mul_left p.2 _ v.val))
  exact BPair.oneValue_trans
    (BPair.mul_congr (BPair.norm_oneValue _) (BPair.oneValue_refl _))
    (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))

/-- A linear read of the sum is the sum of the two linear reads. -/
theorem fold_addV {k : Nat} (u v : SVec k) (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (addV u v).val).oneValue
      (bsum (fun p => p.2 * f p.1) u.val + bsum (fun p => p.2 * f p.1) v.val) := by
  rw [addV_read]
  exact BPair.oneValue_trans (by apply (foldB_collectBy lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) f _)) (famFold_append_ov bpairFoldLaws _ _ _)

/-- A linear read of a scaled vector is its original read at the
scalar factor. -/
theorem fold_scaleV {k : Nat} (v : SVec k) (c : BPair) (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (scaleV c v).val).oneValue
      (c * bsum (fun p => p.2 * f p.1) v.val) := by
  refine BPair.oneValue_trans (by apply (foldB_collectBy lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) f _)) ?_
  rw [bsum_map]
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => c * (p.2 * f p.1)) v.val (fun p _ => ?_))
    (by apply (foldB_mul_left c _ v.val))
  rw [BPair.mul_comm p.2 c, BPair.mul_assoc]
  exact BPair.oneValue_refl _

/-- A sparse action's linear read is the coefficient fold at its
source keys, target substitutions and signed entries. -/
theorem fold_actT (M : memtable.SMap) (neg : Bool) (s : Nat) {k : Nat}
    (v : SVec k) (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (actT M neg s v).val).oneValue
      (bsum (fun p => p.2 * bsum (fun e =>
        if getAt 0 p.1 s == e.2.1 then signedAt neg e.2.2 * f (p.1.set s e.1)
        else BPair.unit) M) v.val) := by
  refine BPair.oneValue_trans (by apply (foldB_collectBy lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) f
    (v.val.flatMap (fun p => M.filterMap (fun e =>
      if getAt 0 p.1 s == e.2.1 then
        some (p.1.set s e.1, if neg then (p.2 * e.2.2).swap else p.2 * e.2.2)
      else none))))) ?_
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ v.val) ?_
  refine foldB_congr_members _ _ v.val (fun p _ => ?_)
  refine BPair.oneValue_trans (famFold_filterMap_ov bpairFoldLaws _ _ M) ?_
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun e => p.2 * (if getAt 0 p.1 s == e.2.1 then
      signedAt neg e.2.2 * f (p.1.set s e.1) else BPair.unit)) M (fun e _ => ?_))
    (by apply (foldB_mul_left p.2 _ M))
  by_cases he : (getAt 0 p.1 s == e.2.1) = true
  · rw [if_pos he, if_pos he]
    change (signedAt neg (p.2 * e.2.2) * f (p.1.set s e.1)).oneValue
      (p.2 * (signedAt neg e.2.2 * f (p.1.set s e.1)))
    rw [signedAt_mul, BPair.mul_assoc]
    exact BPair.oneValue_refl _
  · rw [if_neg he, if_neg he]
    exact BPair.oneValue_symm (BPair.mul_unit _)

/-- The linear read of a simple raising is its slot fold, at the
standard map or its dual map according to the signature. -/
theorem fold_raiseT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (raiseT T sig i v).val).oneValue
      (bsum (fun s => if getAt false sig s then
        bsum (fun p => p.2 * f p.1) (actT (getAt [] T.lowers i) true s v).val
        else bsum (fun p => p.2 * f p.1) (actT (getAt [] T.raises i) false s v).val)
        (List.range sig.length)) := by
  refine BPair.oneValue_trans (by apply (foldB_collectBy lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) f _)) ?_
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ _) ?_
  refine foldB_congr_members _ _ _ (fun s _ => ?_)
  by_cases hs : getAt false sig s = true
  · rw [if_pos hs, if_pos hs]; exact BPair.oneValue_refl _
  · rw [if_neg hs, if_neg hs]; exact BPair.oneValue_refl _

/-- A sparse action on the first factor's slot acts on that factor
of the tensor, at every signed sparse map. -/
theorem actT_tensor_left (M : memtable.SMap) (neg : Bool) (s : Nat)
    {k l : Nat} (u : SVec k) (v : SVec l) (hs : s < k) :
    actT M neg s (tensorV u v) = tensorV (actT M neg s u) v := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (actT M neg s (tensorV u v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (tensorV (actT M neg s u) v).val) := by
    let g := fun m : List Nat => bsum (fun q => q.2 * f (m ++ q.1)) v.val
    refine BPair.oneValue_trans (by apply (fold_actT M neg s (tensorV u v) f)) ?_
    refine BPair.oneValue_trans (by apply (fold_tensorV u v (fun m => bsum (fun e => if getAt 0 m s == e.2.1 then
      signedAt neg e.2.2 * f (m.set s e.1) else BPair.unit) M))) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
      (BPair.oneValue_trans (by apply (fold_tensorV (actT M neg s u) v f))
        (by apply (fold_actT M neg s u g))))
    refine foldB_congr_members _ _ u.val (fun p hp => ?_)
    refine BPair.mul_congr (BPair.oneValue_refl p.2) ?_
    have hsp : s < p.1.length := by
      rw [width_of_mem u p (mem_of_countOf_pos _ _ hp)]; exact hs
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun q : List Nat × BPair => bsum (fun e => q.2 *
        (if getAt 0 p.1 s == e.2.1 then
          signedAt neg e.2.2 * f (p.1.set s e.1 ++ q.1) else BPair.unit)) M)
      v.val (fun q _ => ?_)) ?_
    · refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl q.2)
        (foldB_congr_members _ _ M (fun e _ => ?_)))
        (BPair.oneValue_symm (by apply (foldB_mul_left q.2 _ M)))
      rw [getAt_append 0 p.1 q.1 s, if_pos hsp, set_append_left e.1 p.1 q.1 s hsp]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (by apply (foldB_swapL _ v.val M)) ?_
      refine foldB_congr_members _ _ M (fun e _ => ?_)
      by_cases he : (getAt 0 p.1 s == e.2.1) = true
      · repeat rw [if_pos he]
        change (bsum (fun q => q.2 *
          (if getAt 0 p.1 s == e.2.1 then
            signedAt neg e.2.2 * f (p.1.set s e.1 ++ q.1) else BPair.unit)) v.val).oneValue
          (signedAt neg e.2.2 * g (p.1.set s e.1))
        refine BPair.oneValue_trans (foldB_congr_members _
          (fun q : List Nat × BPair => signedAt neg e.2.2 *
            (q.2 * f (p.1.set s e.1 ++ q.1))) v.val (fun q _ => ?_))
          (by apply (foldB_mul_left (signedAt neg e.2.2) _ v.val))
        rw [if_pos he, BPair.mul_left_comm]
        exact BPair.oneValue_refl _
      · repeat rw [if_neg he]
        apply foldB_null
        intro q _
        rw [if_neg he]
        exact BPair.mul_unit _
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- The tensor's linear read with the second factor's family
outermost, the two finite coefficient folds exchanged. -/
theorem fold_tensorV_right {k l : Nat} (u : SVec k) (v : SVec l)
    (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (tensorV u v).val).oneValue
      (bsum (fun q => q.2 * bsum (fun p => p.2 * f (p.1 ++ q.1)) u.val) v.val) := by
  refine BPair.oneValue_trans (by apply (fold_tensorV u v f)) ?_
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => bsum (fun q => p.2 *
      (q.2 * f (p.1 ++ q.1))) v.val) u.val (fun p _ =>
      BPair.oneValue_symm (by apply (foldB_mul_left p.2 _ v.val)))) ?_
  refine BPair.oneValue_trans (by apply (foldB_swapL _ u.val v.val)) ?_
  refine foldB_congr_members _ _ v.val (fun q _ => ?_)
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => q.2 * (p.2 * f (p.1 ++ q.1))) u.val
    (fun p _ => BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)))
    (by apply (foldB_mul_left q.2 _ u.val))

/-- A sparse action past the tensor seam acts on the second factor
at the slot's offset, including offsets past that factor's end. -/
theorem actT_tensor_right (M : memtable.SMap) (neg : Bool) (s : Nat)
    {k l : Nat} (u : SVec k) (v : SVec l) :
    actT M neg (k + s) (tensorV u v) = tensorV u (actT M neg s v) := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (actT M neg (k + s) (tensorV u v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (tensorV u (actT M neg s v)).val) := by
    let g := fun n : List Nat => bsum (fun p => p.2 * f (p.1 ++ n)) u.val
    refine BPair.oneValue_trans (by apply (fold_actT M neg (k + s) (tensorV u v) f)) ?_
    refine BPair.oneValue_trans (by apply (fold_tensorV_right u v (fun m => bsum (fun e => if getAt 0 m (k + s) == e.2.1 then
      signedAt neg e.2.2 * f (m.set (k + s) e.1) else BPair.unit) M))) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
      (BPair.oneValue_trans (by apply (fold_tensorV_right u (actT M neg s v) f))
        (by apply (fold_actT M neg s v g))))
    refine foldB_congr_members _ _ v.val (fun q _ => ?_)
    refine BPair.mul_congr (BPair.oneValue_refl q.2) ?_
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun p : List Nat × BPair => bsum (fun e => p.2 *
        (if getAt 0 q.1 s == e.2.1 then
          signedAt neg e.2.2 * f (p.1 ++ q.1.set s e.1) else BPair.unit)) M)
      u.val (fun p hp => ?_)) ?_
    · have hw := width_of_mem u p (mem_of_countOf_pos _ _ hp)
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl p.2)
        (foldB_congr_members _ _ M (fun e _ => ?_)))
        (BPair.oneValue_symm (by apply (foldB_mul_left p.2 _ M)))
      rw [← hw, getAt_append_add, set_append_right]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (by apply (foldB_swapL _ u.val M)) ?_
      refine foldB_congr_members _ _ M (fun e _ => ?_)
      by_cases he : (getAt 0 q.1 s == e.2.1) = true
      · repeat rw [if_pos he]
        change (bsum (fun p => p.2 *
          (if getAt 0 q.1 s == e.2.1 then
            signedAt neg e.2.2 * f (p.1 ++ q.1.set s e.1) else BPair.unit)) u.val).oneValue
          (signedAt neg e.2.2 * g (q.1.set s e.1))
        refine BPair.oneValue_trans (foldB_congr_members _
          (fun p : List Nat × BPair => signedAt neg e.2.2 *
            (p.2 * f (p.1 ++ q.1.set s e.1))) u.val (fun p _ => ?_))
          (by apply (foldB_mul_left (signedAt neg e.2.2) _ u.val))
        rw [if_pos he, BPair.mul_left_comm]
        exact BPair.oneValue_refl _
      · repeat rw [if_neg he]
        apply foldB_null
        intro p _
        rw [if_neg he]
        exact BPair.mul_unit _
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- A tensor's first factor preserves a finite sum read by every
linear coefficient fold. -/
private theorem tensor_fold_left {α : Type} [DecidableEq α] {k l : Nat}
    (L : List α) (a : α → SVec k) (u : SVec k) (v : SVec l)
    (h : ∀ f : List Nat → BPair,
      (bsum (fun p => p.2 * f p.1) u.val).oneValue
        (bsum (fun s => bsum (fun p => p.2 * f p.1) (a s).val) L))
    (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (tensorV u v).val).oneValue
      (bsum (fun s => bsum (fun p => p.2 * f p.1) (tensorV (a s) v).val) L) := by
  refine BPair.oneValue_trans (by apply (fold_tensorV_right u v f)) ?_
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun q : List Nat × BPair => bsum (fun s => q.2 *
      bsum (fun p => p.2 * f (p.1 ++ q.1)) (a s).val) L) v.val (fun q _ => ?_)) ?_
  · exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (h (fun m => f (m ++ q.1)))) (BPair.oneValue_symm (by apply (foldB_mul_left q.2 _ L)))
  · refine BPair.oneValue_trans (by apply (foldB_swapL _ v.val L)) ?_
    exact foldB_congr_members _ _ L (fun s _ =>
      BPair.oneValue_symm (by apply (fold_tensorV_right (a s) v f)))

/-- A tensor's second factor preserves a finite sum read by every
linear coefficient fold. -/
private theorem tensor_fold_right {α : Type} [DecidableEq α] {k l : Nat}
    (L : List α) (a : α → SVec l) (u : SVec k) (v : SVec l)
    (h : ∀ f : List Nat → BPair,
      (bsum (fun p => p.2 * f p.1) v.val).oneValue
        (bsum (fun s => bsum (fun p => p.2 * f p.1) (a s).val) L))
    (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (tensorV u v).val).oneValue
      (bsum (fun s => bsum (fun p => p.2 * f p.1) (tensorV u (a s)).val) L) := by
  refine BPair.oneValue_trans (by apply (fold_tensorV u v f)) ?_
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => bsum (fun s => p.2 *
      bsum (fun q => q.2 * f (p.1 ++ q.1)) (a s).val) L) u.val (fun p _ => ?_)) ?_
  · exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (h (fun m => f (p.1 ++ m)))) (BPair.oneValue_symm (by apply (foldB_mul_left p.2 _ L)))
  · refine BPair.oneValue_trans (by apply (foldB_swapL _ u.val L)) ?_
    exact foldB_congr_members _ _ L (fun s _ =>
      BPair.oneValue_symm (by apply (fold_tensorV u (a s) f)))

/-- The simple raising at concatenated signatures reads the
Leibniz sum on the two tensor factors. -/
theorem raiseT_tensorV (T : memtable.Table) (sig tau : List Bool) (i : Nat)
    (u : SVec sig.length) (v : SVec tau.length) :
    castV (length_append sig tau)
      (raiseT T (sig ++ tau) i (castV (length_append sig tau).symm (tensorV u v)))
      = addV (tensorV (raiseT T sig i u) v) (tensorV u (raiseT T tau i v)) := by
  let left := fun s => if getAt false sig s then actT (getAt [] T.lowers i) true s u
    else actT (getAt [] T.raises i) false s u
  let right := fun s => if getAt false tau s then actT (getAt [] T.lowers i) true s v
    else actT (getAt [] T.raises i) false s v
  have hl (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (raiseT T sig i u).val).oneValue
        (bsum (fun s => bsum (fun p => p.2 * f p.1) (left s).val) (List.range sig.length)) := by
    refine BPair.oneValue_trans (fold_raiseT T sig i u f) ?_
    refine foldB_congr_members _ _ _ (fun s _ => ?_)
    unfold left
    by_cases hs : getAt false sig s = true
    · repeat rw [if_pos hs]
      exact BPair.oneValue_refl _
    · repeat rw [if_neg hs]
      exact BPair.oneValue_refl _
  have hr (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (raiseT T tau i v).val).oneValue
        (bsum (fun s => bsum (fun p => p.2 * f p.1) (right s).val) (List.range tau.length)) := by
    refine BPair.oneValue_trans (fold_raiseT T tau i v f) ?_
    refine foldB_congr_members _ _ _ (fun s _ => ?_)
    unfold right
    by_cases hs : getAt false tau s = true
    · repeat rw [if_pos hs]
      exact BPair.oneValue_refl _
    · repeat rw [if_neg hs]
      exact BPair.oneValue_refl _
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1)
        (raiseT T (sig ++ tau) i (castV (length_append sig tau).symm (tensorV u v))).val).oneValue
        (bsum (fun p => p.2 * f p.1)
          (addV (tensorV (raiseT T sig i u) v) (tensorV u (raiseT T tau i v))).val) := by
    refine BPair.oneValue_trans (fold_raiseT T (sig ++ tau) i _ f) ?_
    change (bsum (fun s => if getAt false (sig ++ tau) s then
      bsum (fun p => p.2 * f p.1) (actT (getAt [] T.lowers i) true s (tensorV u v)).val
      else bsum (fun p => p.2 * f p.1) (actT (getAt [] T.raises i) false s (tensorV u v)).val)
      (List.range (sig ++ tau).length)).oneValue _
    rw [length_append, range_split]
    refine BPair.oneValue_trans (famFold_append_ov bpairFoldLaws _ _ _) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (by apply (fold_addV _ _ f)))
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
        (by apply (tensor_fold_left _ left (raiseT T sig i u) v hl f)))
      refine foldB_congr_members _ _ _ (fun s hs => ?_)
      have hsl := ltOfCountRange hs
      rw [getAt_append false sig tau s, if_pos hsl]
      unfold left
      by_cases hsig : getAt false sig s = true
      · repeat rw [if_pos hsig]
        rw [actT_tensor_left _ _ _ u v hsl]
        exact BPair.oneValue_refl _
      · repeat rw [if_neg hsig]
        rw [actT_tensor_left _ _ _ u v hsl]
        exact BPair.oneValue_refl _
    · rw [famFold_map]
      refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
        (by apply (tensor_fold_right _ right u (raiseT T tau i v) hr f)))
      refine foldB_congr_members _ _ _ (fun s _ => ?_)
      rw [getAt_append_add]
      unfold right
      by_cases htau : getAt false tau s = true
      · repeat rw [if_pos htau]
        rw [actT_tensor_right]
        exact BPair.oneValue_refl _
      · repeat rw [if_neg htau]
        rw [actT_tensor_right]
        exact BPair.oneValue_refl _
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- A sparse action preserves the sum of two vectors. -/
theorem actT_addV (M : memtable.SMap) (neg : Bool) (s : Nat) {k : Nat} (u v : SVec k) :
    actT M neg s (addV u v) = addV (actT M neg s u) (actT M neg s v) := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (actT M neg s (addV u v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (addV (actT M neg s u) (actT M neg s v)).val) := by
    refine BPair.oneValue_trans (by apply (fold_actT M neg s (addV u v) f)) ?_
    refine BPair.oneValue_trans (by apply (fold_addV u v (fun m => bsum (fun e => if getAt 0 m s == e.2.1 then
      signedAt neg e.2.2 * f (m.set s e.1) else BPair.unit) M))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_symm (by apply (fold_actT M neg s u f)))
        (BPair.oneValue_symm (by apply (fold_actT M neg s v f)))) ?_
    exact BPair.oneValue_symm (by apply (fold_addV _ _ f))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- A sparse action preserves a vector's scalar multiplication. -/
theorem actT_scaleV (M : memtable.SMap) (neg : Bool) (s : Nat) {k : Nat}
    (v : SVec k) (c : BPair) : actT M neg s (scaleV c v) = scaleV c (actT M neg s v) := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (actT M neg s (scaleV c v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (scaleV c (actT M neg s v)).val) := by
    refine BPair.oneValue_trans (by apply (fold_actT M neg s (scaleV c v) f)) ?_
    refine BPair.oneValue_trans (by apply (fold_scaleV v c (fun m => bsum (fun e => if getAt 0 m s == e.2.1 then
      signedAt neg e.2.2 * f (m.set s e.1) else BPair.unit) M))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c) (BPair.oneValue_symm (by apply (fold_actT M neg s v f)))) ?_
    exact BPair.oneValue_symm (by apply (fold_scaleV _ c f))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- A simple raising preserves the sum of two vectors. -/
theorem raiseT_addV (T : memtable.Table) (sig : List Bool) (i : Nat)
    (u v : SVec sig.length) :
    raiseT T sig i (addV u v) = addV (raiseT T sig i u) (raiseT T sig i v) := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (raiseT T sig i (addV u v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (addV (raiseT T sig i u) (raiseT T sig i v)).val) := by
    let a := fun s => if getAt false sig s then
      bsum (fun p => p.2 * f p.1) (actT (getAt [] T.lowers i) true s u).val
      else bsum (fun p => p.2 * f p.1) (actT (getAt [] T.raises i) false s u).val
    let b := fun s => if getAt false sig s then
      bsum (fun p => p.2 * f p.1) (actT (getAt [] T.lowers i) true s v).val
      else bsum (fun p => p.2 * f p.1) (actT (getAt [] T.raises i) false s v).val
    refine BPair.oneValue_trans (fold_raiseT T sig i (addV u v) f) ?_
    refine BPair.oneValue_trans (foldB_congr_members _ (fun s => a s + b s)
      (List.range sig.length) (fun s _ => ?_)) ?_
    · unfold a b
      by_cases hs : getAt false sig s = true
      · repeat rw [if_pos hs]
        rw [actT_addV]
        exact fold_addV _ _ f
      · repeat rw [if_neg hs]
        rw [actT_addV]
        exact fold_addV _ _ f
    · exact BPair.oneValue_trans (foldB_add a b (List.range sig.length))
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_symm (fold_raiseT T sig i u f))
            (BPair.oneValue_symm (fold_raiseT T sig i v f)))
          (BPair.oneValue_symm (by apply (fold_addV _ _ f))))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- A simple raising preserves scalar multiplication. -/
theorem raiseT_scaleV (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (c : BPair) :
    raiseT T sig i (scaleV c v) = scaleV c (raiseT T sig i v) := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (raiseT T sig i (scaleV c v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (scaleV c (raiseT T sig i v)).val) := by
    let a := fun s => if getAt false sig s then
      bsum (fun p => p.2 * f p.1) (actT (getAt [] T.lowers i) true s v).val
      else bsum (fun p => p.2 * f p.1) (actT (getAt [] T.raises i) false s v).val
    refine BPair.oneValue_trans (fold_raiseT T sig i (scaleV c v) f) ?_
    refine BPair.oneValue_trans (foldB_congr_members _ (fun s => c * a s)
      (List.range sig.length) (fun s _ => ?_)) ?_
    · unfold a
      by_cases hs : getAt false sig s = true
      · repeat rw [if_pos hs]
        rw [actT_scaleV]
        exact fold_scaleV _ c f
      · repeat rw [if_neg hs]
        rw [actT_scaleV]
        exact fold_scaleV _ c f
    · exact BPair.oneValue_trans (by apply (foldB_mul_left c a (List.range sig.length)))
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl c) (BPair.oneValue_symm (fold_raiseT T sig i v f)))
          (BPair.oneValue_symm (by apply (fold_scaleV _ c f))))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- A simple lowering preserves the sum, at the exchanged table
maps' raising identity. -/
theorem lowerT_addV (T : memtable.Table) (sig : List Bool) (i : Nat)
    (u v : SVec sig.length) :
    lowerT T sig i (addV u v) = addV (lowerT T sig i u) (lowerT T sig i v) :=
  raiseT_addV { T with raises := T.lowers, lowers := T.raises } sig i u v

/-- A simple lowering preserves scalar multiplication. -/
theorem lowerT_scaleV (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (c : BPair) :
    lowerT T sig i (scaleV c v) = scaleV c (lowerT T sig i v) :=
  raiseT_scaleV { T with raises := T.lowers, lowers := T.raises } sig i v c

/-- The simple lowering at concatenated signatures reads the
Leibniz sum, the exchanged table maps' raising identity. -/
theorem lowerT_tensorV (T : memtable.Table) (sig tau : List Bool) (i : Nat)
    (u : SVec sig.length) (v : SVec tau.length) :
    castV (length_append sig tau)
      (lowerT T (sig ++ tau) i (castV (length_append sig tau).symm (tensorV u v)))
      = addV (tensorV (lowerT T sig i u) v) (tensorV u (lowerT T tau i v)) :=
  raiseT_tensorV { T with raises := T.lowers, lowers := T.raises } sig tau i u v

/-- At the first occupied monomial the coefficient reads the
display's own entry, with the further keys distinct. -/
theorem coefAt_head {k : Nat} (v : SVec k) (p : List Nat × BPair)
    (l : List (List Nat × BPair)) (hv : v.val = p :: l) :
    (coefAt p.1 v).oneValue p.2 := by
  refine BPair.oneValue_trans (coefAt_read p.1 v) ?_
  rw [hv]
  apply keyFoldB_head lexLt (fun a b : List Nat => a == b) lexLt_trans
    (fun _ _ h => listBeqEq h) listEqBeq lexLt_irrefl p l
  rw [← hv]
  exact sortedV v

/-- The tensor's coefficient at a concatenated monomial is
the factors' coefficient product, split at the first slot count. -/
theorem coefAt_tensorV {k l : Nat} (u : SVec k) (v : SVec l)
    (m n : List Nat) (hm : m.length = k) :
    (coefAt (m ++ n) (tensorV u v)).oneValue (coefAt m u * coefAt n v) := by
  let eq := fun a b : List Nat => a == b
  let left := fun p : List Nat × BPair => if eq p.1 m then p.2 else BPair.unit
  let right := fun q : List Nat × BPair => if eq q.1 n then q.2 else BPair.unit
  have hterm (p : List Nat × BPair) (hp : p ∈ u.val) (q : List Nat × BPair) :
      (if eq (p.1 ++ q.1) (m ++ n) then (p.2 * q.2).norm else BPair.unit).oneValue
        (left p * right q) := by
    have hsplit (h : eq (p.1 ++ q.1) (m ++ n) = true) : p.1 = m ∧ q.1 = n :=
      append_inj_len p.1 m q.1 n ((width_of_mem u p hp).trans hm.symm) (listBeqEq h)
    change (if eq (p.1 ++ q.1) (m ++ n) then (p.2 * q.2).norm else BPair.unit).oneValue
      ((if eq p.1 m then p.2 else BPair.unit) * (if eq q.1 n then q.2 else BPair.unit))
    by_cases ha : eq p.1 m = true
    · by_cases hb : eq q.1 n = true
      · have hab : eq (p.1 ++ q.1) (m ++ n) = true := by
          rw [listBeqEq ha, listBeqEq hb]; exact listEqBeq _
        rw [if_pos ha, if_pos hb, if_pos hab]
        exact BPair.norm_oneValue _
      · rw [if_pos ha, if_neg hb,
          if_neg (fun h => hb (by rw [(hsplit h).2]; exact listEqBeq _))]
        exact BPair.oneValue_symm (BPair.mul_unit _)
    · rw [if_neg ha,
        if_neg (fun h => ha (by rw [(hsplit h).1]; exact listEqBeq _))]
      exact BPair.oneValue_symm (BPair.unit_mul _)
  have hraw :
      (keyFoldB eq (m ++ n) (u.val.flatMap (fun p =>
        v.val.map (fun q => (p.1 ++ q.1, (p.2 * q.2).norm))))).oneValue
        (keyFoldB eq m u.val * keyFoldB eq n v.val) := by
    refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ u.val) ?_
    refine BPair.oneValue_trans
      (foldB_congr_members _ (fun p => left p * keyFoldB eq n v.val) u.val (fun p hp => ?_)) ?_
    · rw [famFold_map]
      exact BPair.oneValue_trans (foldB_congr_members _ _ v.val
        (fun q _ => hterm p (mem_of_countOf_pos _ _ hp) q))
        (foldB_mul_left (left p) right v.val)
    · exact BPair.oneValue_symm (foldB_mul_right (keyFoldB eq n v.val) left u.val)
  refine BPair.oneValue_trans (coefAt_read (m ++ n) (tensorV u v)) ?_
  refine BPair.oneValue_trans
    (keyFoldB_collectBy lexLt eq (fun _ _ h => listBeqEq h) (m ++ n) _) ?_
  exact BPair.oneValue_trans hraw
    (BPair.mul_congr (BPair.oneValue_symm (coefAt_read m u))
      (BPair.oneValue_symm (coefAt_read n v)))

/-- Two occupied vectors have an occupied tensor: the first
monomials' coefficients multiply off the sum's unit. -/
theorem tensorV_occupied {k l : Nat} (u : SVec k) (v : SVec l)
    (hu : u.val ≠ []) (hv : v.val ≠ []) : (tensorV u v).val ≠ [] := by
  cases hea : u.val with
  | nil => exact False.elim (hu hea)
  | cons a as =>
    cases heb : v.val with
    | nil => exact False.elim (hv heb)
    | cons b bs =>
      have ha : a ∈ u.val := by rw [hea]; exact List.Mem.head _
      have hb : b ∈ v.val := by rw [heb]; exact List.Mem.head _
      have hac := canonV u a ha
      have hbc := canonV v b hb
      have hca := coefAt_head u a as hea
      have hcb := coefAt_head v b bs heb
      have hp := coefAt_tensorV u v a.1 b.1 (width_of_mem u a ha)
      intro hz
      have hz' : (coefAt (a.1 ++ b.1) (tensorV u v)).oneValue BPair.unit := by
        unfold coefAt
        rw [hz]
        exact BPair.oneValue_refl _
      exact mulOffUnit (canon_offUnit hac.1 hac.2) (canon_offUnit hbc.1 hbc.2)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr hca hcb))
          (BPair.oneValue_trans (BPair.oneValue_symm hp) hz'))

private theorem prodW_cons (x : Nat × BPair) (ch : List (Nat × BPair)) :
    prodW (x :: ch) = prodW ch * x.2 := by
  show ch.foldl (fun a e => a * e.2) (BPair.ofNat 1 * x.2)
    = ch.foldl (fun a e => a * e.2) (BPair.ofNat 1) * x.2
  exact (foldl_mul_seed BPair.mul BPair.mul_comm BPair.mul_assoc
    (fun e : Nat × BPair => e.2) ch (BPair.ofNat 1) x.2).symm

/-- The pairing's kernel at two monomials as the chains' fold: the
chains over the first monomial's substitutions landing on the
second at their weights. -/
private def kerF (w : memtable.SMap) (m m' : List Nat) : BPair :=
  famFold BPair.add BPair.unit
    (fun ch => if ch.map Prod.fst == m' then prodW ch else BPair.unit)
    (prodLists (subs w m))

/-- The pairing's kernel at two monomials as the slots' product of
the weight's entries. -/
private def kerW (w : memtable.SMap) : List Nat → List Nat → BPair
  | [], [] => BPair.ofNat 1
  | [], _ :: _ => BPair.unit
  | _ :: _, [] => BPair.unit
  | k :: t, k' :: t' => memtable.wtAt w k k' * kerW w t t'

/-- The pairing's kernel at a table and the unit-weight read: the
key delta at the unit weight, the slots' product otherwise. -/
private def kerAt (T : memtable.Table) (uw : Bool) (m m' : List Nat) : BPair :=
  if uw then (if m == m' then BPair.ofNat 1 else BPair.unit) else kerW T.wt m m'

private theorem filt_cons (w : memtable.SMap) (e : Nat × Nat × BPair) (k : Nat) :
    filt (e :: w) k
      = if e.1 == k then (e.2.1, e.2.2) :: filt w k else filt w k := by
  show List.filterMap
    (fun e : Nat × Nat × BPair => if e.1 == k then some (e.2.1, e.2.2) else none)
    (e :: w) = _
  rw [List.filterMap_cons]
  cases he : (e.1 == k) with
  | true => exact rfl
  | false => exact rfl

/-- The substitutions at a key folded at a source (`keyFoldB` at
the source key) read the weight's entries at the key pair. -/
private theorem filt_fold (k k' : Nat) : ∀ w : memtable.SMap,
    (keyFoldB (fun a b : Nat => a == b) k' (filt w k)).oneValue
    (famFold BPair.add BPair.unit
      (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) w)
  | [] => BPair.oneValue_refl _
  | e :: r => by
    rw [filt_cons]
    show (keyFoldB (fun a b : Nat => a == b) k'
        (if e.1 == k then (e.2.1, e.2.2) :: filt r k else filt r k)).oneValue
      ((if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit)
        + famFold BPair.add BPair.unit
          (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) r)
    cases he : (e.1 == k) with
    | true =>
      rw [if_pos rfl, Bool.true_and]
      show ((if e.2.1 == k' then e.2.2 else BPair.unit)
          + keyFoldB (fun a b : Nat => a == b) k' (filt r k)).oneValue
        ((if e.2.1 == k' then e.2.2 else BPair.unit)
          + famFold BPair.add BPair.unit
            (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) r)
      exact BPair.add_congr (BPair.oneValue_refl _) (filt_fold k k' r)
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
        Bool.false_and, if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
      show (keyFoldB (fun a b : Nat => a == b) k' (filt r k)).oneValue
        (BPair.unit + famFold BPair.add BPair.unit
          (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) r)
      exact BPair.oneValue_trans (filt_fold k k' r)
        (BPair.oneValue_symm (BPair.unit_add _))

/-- The substitutions at a key folded at a source read the weight's
entry at the key pair. -/
private theorem wtAt_filter (w : memtable.SMap) (k k' : Nat) :
    (keyFoldB (fun a b : Nat => a == b) k' (filt w k)).oneValue
      (memtable.wtAt w k k') :=
  BPair.oneValue_trans (filt_fold k k' w) (BPair.oneValue_symm (memtable.wtAt_read w k k'))

/-- The chains' fold reads the slots' product: at a grown monomial
the chains split at the head's substitutions, each chain's weight
the head's against the tail's, the head's fold the weight's entry
(`wtAt_filter`). -/
private theorem kerF_read (w : memtable.SMap) : ∀ m m' : List Nat,
    (kerF w m m').oneValue (kerW w m m')
  | [], [] => by
    show ((if ([] : List Nat) == [] then prodW [] else BPair.unit)
      + BPair.unit).oneValue (BPair.ofNat 1)
    rw [if_pos (show (([] : List Nat) == []) = true from rfl)]
    exact BPair.add_unit _
  | [], k' :: t' => by
    show ((if ([] : List Nat) == k' :: t' then prodW [] else BPair.unit)
      + BPair.unit).oneValue BPair.unit
    rw [if_neg (c := (([] : List Nat) == k' :: t') = true)
      (fun h => Bool.noConfusion (show (false : Bool) = true from h))]
    exact BPair.add_unit _
  | k :: t, m' => by
    show (famFold BPair.add BPair.unit
      (fun ch => if ch.map Prod.fst == m' then prodW ch else BPair.unit)
      ((filt w k).flatMap (fun x => (prodLists (subs w t)).map
        (fun l => x :: l)))).oneValue (kerW w (k :: t) m')
    refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (filt w k)) ?_
    refine BPair.oneValue_trans (foldB_congr_members _ _ _ (fun x _ =>
      BPair.oneValue_of_eq (famFold_map BPair.add BPair.unit _
        (fun l => x :: l) (prodLists (subs w t))))) ?_
    cases m' with
    | nil =>
      refine foldB_null _ _ (fun x _ => foldB_null _ _ (fun ch' _ => ?_))
      show (if (x.1 :: ch'.map Prod.fst) == ([] : List Nat) then prodW (x :: ch')
        else BPair.unit).oneValue BPair.unit
      rw [if_neg (c := ((x.1 :: ch'.map Prod.fst) == ([] : List Nat)) = true)
        (fun h => Bool.noConfusion (show (false : Bool) = true from h))]
      exact BPair.oneValue_refl _
    | cons k' t' =>
      show (famFold BPair.add BPair.unit (fun x => famFold BPair.add BPair.unit
        (fun ch' => if (x.1 :: ch'.map Prod.fst) == k' :: t' then prodW (x :: ch')
          else BPair.unit) (prodLists (subs w t))) (filt w k)).oneValue
        (memtable.wtAt w k k' * kerW w t t')
      refine BPair.oneValue_trans (foldB_congr_members _
        (fun x : Nat × BPair => (if x.1 == k' then x.2 else BPair.unit) * kerF w t t')
        _ (fun x _ => ?_)) ?_
      · refine BPair.oneValue_trans (foldB_congr_members _ _ _ (fun ch' _ => ?_))
          (foldB_mul_left (if x.1 == k' then x.2 else BPair.unit)
            (fun ch' : List (Nat × BPair) =>
              if ch'.map Prod.fst == t' then prodW ch' else BPair.unit)
            (prodLists (subs w t)))
        show (if ((x.1 == k') && (ch'.map Prod.fst == t')) = true
            then prodW (x :: ch') else BPair.unit).oneValue
          ((if x.1 == k' then x.2 else BPair.unit)
            * (if ch'.map Prod.fst == t' then prodW ch' else BPair.unit))
        cases h1 : (x.1 == k') with
        | true =>
          cases h2 : (ch'.map Prod.fst == t') with
          | true =>
            rw [if_pos (by decide), if_pos rfl, if_pos rfl, prodW_cons]
            exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
          | false =>
            rw [if_neg (by decide), if_pos rfl,
              if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
            exact BPair.oneValue_symm (BPair.mul_unit _)
        | false =>
          rw [Bool.false_and, if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
            if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
          exact BPair.oneValue_symm (BPair.unit_mul _)
      · refine BPair.oneValue_trans
          (BPair.oneValue_symm (foldB_mul_right (kerF w t t') _ (filt w k))) ?_
        exact BPair.mul_congr (wtAt_filter w k k') (kerF_read w t t')

/-- The slots' product at two weights whose entries exchange reads
the product at the exchanged monomials. -/
private theorem kerW_flip (w w' : memtable.SMap)
    (hs : ∀ t s, (memtable.wtAt w t s).oneValue (memtable.wtAt w' s t)) :
    ∀ m m' : List Nat, (kerW w m m').oneValue (kerW w' m' m)
  | [], [] => BPair.oneValue_refl _
  | [], _ :: _ => BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | k :: t, k' :: t' => BPair.mul_congr (hs k k') (kerW_flip w w' hs t t')

/-- The kernel exchanges at the symmetry read. -/
private theorem kerAt_symm (T : memtable.Table) (hw : memtable.symmWt T) (uw : Bool)
    (m m' : List Nat) : (kerAt T uw m m').oneValue (kerAt T uw m' m) := by
  cases uw with
  | true =>
    show (if m == m' then BPair.ofNat 1 else BPair.unit).oneValue
      (if m' == m then BPair.ofNat 1 else BPair.unit)
    rw [listBeqSymm m' m]
    exact BPair.oneValue_refl _
  | false => exact kerW_flip T.wt T.wt (memtable.wtAt_symm T hw) m m'

/-- A monomial's pairing against a vector reads the vector's fold
at the kernel: the coefficient's read at the unit weight, and the
chains' fold exchanged with the vector's fold otherwise. -/
private theorem monDotT_read (T : memtable.Table) (uw : Bool) (m : List Nat) {k : Nat}
    (v : SVec k) :
    (monDotT T uw m v).oneValue
      (famFold BPair.add BPair.unit (fun q => q.2 * kerAt T uw m q.1) v.val) := by
  cases uw with
  | true =>
    rw [show monDotT T true m v = coefAt m v from rfl]
    refine BPair.oneValue_trans (coefAt_fold m v) ?_
    refine foldB_congr_members _ _ v.val (fun q _ => ?_)
    change (q.2 * (if q.1 == m then BPair.ofNat 1 else BPair.unit)).oneValue
      (q.2 * (if m == q.1 then BPair.ofNat 1 else BPair.unit))
    rw [listBeqSymm m q.1]
    exact BPair.oneValue_refl _
  | false =>
    rw [show monDotT T false m v = (prodLists (subs T.wt m)).foldl
      (fun acc ch => acc + prodW ch * coefAt (ch.map Prod.fst) v) BPair.unit
      from rfl]
    have h1 := foldlFamO bpairFoldLaws
      (fun ch : List (Nat × BPair) => prodW ch * coefAt (ch.map Prod.fst) v)
      (prodLists (subs T.wt m)) BPair.unit
    have h2 : (famFold BPair.add BPair.unit
        (fun ch : List (Nat × BPair) => prodW ch * coefAt (ch.map Prod.fst) v)
        (prodLists (subs T.wt m))).oneValue
      (famFold BPair.add BPair.unit
        (fun ch : List (Nat × BPair) => famFold BPair.add BPair.unit
          (fun q : List Nat × BPair =>
            prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit)) v.val)
        (prodLists (subs T.wt m))) :=
      foldB_congr_members _ _ _ (fun ch _ =>
        BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (prodW ch)) (coefAt_read _ v))
          (BPair.oneValue_symm (foldB_mul_left (prodW ch)
            (fun q : List Nat × BPair =>
              if q.1 == ch.map Prod.fst then q.2 else BPair.unit) v.val)))
    have h3 := foldB_swapL (fun (ch : List (Nat × BPair)) (q : List Nat × BPair) =>
      prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit))
      (prodLists (subs T.wt m)) v.val
    have h4 : (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => famFold BPair.add BPair.unit
          (fun ch : List (Nat × BPair) =>
            prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit))
          (prodLists (subs T.wt m))) v.val).oneValue
      (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => q.2 * kerW T.wt m q.1) v.val) :=
      foldB_congr_members _ _ v.val (fun q _ => by
        refine BPair.oneValue_trans ?_
          (BPair.mul_congr (BPair.oneValue_refl q.2) (kerF_read T.wt m q.1))
        refine BPair.oneValue_trans ?_ (foldB_mul_left q.2
          (fun ch : List (Nat × BPair) =>
            if ch.map Prod.fst == q.1 then prodW ch else BPair.unit)
          (prodLists (subs T.wt m)))
        refine foldB_congr_members _ _ _ (fun ch _ => ?_)
        show (prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit)).oneValue
          (q.2 * (if ch.map Prod.fst == q.1 then prodW ch else BPair.unit))
        rw [listBeqSymm q.1 (ch.map Prod.fst)]
        cases hc : (ch.map Prod.fst == q.1) with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
        | false =>
          rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
            if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
          exact BPair.oneValue_trans (BPair.mul_unit _)
            (BPair.oneValue_symm (BPair.mul_unit _)))
    exact BPair.oneValue_trans h1 (BPair.oneValue_trans (BPair.unit_add _)
      (BPair.oneValue_trans h2 (BPair.oneValue_trans h3 h4)))

/-- The weighted pairing as the first vector's fold at the
monomials' pairings. -/
private theorem dotT_read (T : memtable.Table) (uw : Bool) {k : Nat} (u v : SVec k) :
    (dotT T uw u v).oneValue
      (famFold BPair.add BPair.unit (fun p => p.2 * monDotT T uw p.1 v) u.val) := by
  rw [show dotT T uw u v
    = u.val.foldl (fun acc p => acc + p.2 * monDotT T uw p.1 v) BPair.unit from rfl]
  have h := foldlFamO bpairFoldLaws
    (fun p : List Nat × BPair => p.2 * monDotT T uw p.1 v) u.val BPair.unit
  exact BPair.oneValue_trans h (BPair.unit_add _)

/-- A monomial's pairing at a stated weight against a vector is its
coefficient in the applied vector: the applied vector's coefficient
at the monomial is the vector's fold at the transposed chains
landing on it, each chain's fold the slots' product at the
exchanged monomials (`kerF_read`, `kerW_flip` at the transpose's
entries `memtable.wtAt_sT`), the pairing's own kernel. -/
theorem monDotT_apply (T : memtable.Table) (m : List Nat) {k : Nat} (v : SVec k) :
    (monDotT T false m v).oneValue (coefAt m (applyWt T v)) := by
  have h1 : (monDotT T false m v).oneValue
      (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => q.2 * kerW T.wt m q.1) v.val) :=
    monDotT_read T false m v
  have h2 : (coefAt m (applyWt T v)).oneValue
      (keyFoldB (fun a b : List Nat => a == b) m (v.val.flatMap (fun p =>
        (prodLists (subs (memtable.sT T.wt) p.1)).map (fun ch =>
          (ch.map Prod.fst, p.2 * prodW ch))))) :=
    BPair.oneValue_trans (coefAt_read m _)
      (keyFoldB_collectBy lexLt (fun a b => a == b) (fun _ _ h => listBeqEq h) m _)
  have h3 : ∀ q : List Nat × BPair,
      (keyFoldB (fun a b : List Nat => a == b) m
        ((prodLists (subs (memtable.sT T.wt) q.1)).map (fun ch =>
          (ch.map Prod.fst, q.2 * prodW ch)))).oneValue
        (q.2 * kerW T.wt m q.1) := fun q => by
    show (famFold BPair.add BPair.unit
      (fun p : List Nat × BPair => if p.1 == m then p.2 else BPair.unit)
      ((prodLists (subs (memtable.sT T.wt) q.1)).map (fun ch =>
        (ch.map Prod.fst, q.2 * prodW ch)))).oneValue (q.2 * kerW T.wt m q.1)
    rw [famFold_map]
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun ch : List (Nat × BPair) =>
        q.2 * (if ch.map Prod.fst == m then prodW ch else BPair.unit))
      (prodLists (subs (memtable.sT T.wt) q.1)) (fun ch _ => ?_)) ?_
    · show (if ch.map Prod.fst == m then q.2 * prodW ch else BPair.unit).oneValue
        (q.2 * (if ch.map Prod.fst == m then prodW ch else BPair.unit))
      cases hc : (ch.map Prod.fst == m) with
      | true =>
        rw [if_pos rfl, if_pos rfl]
        exact BPair.oneValue_refl _
      | false =>
        rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
          if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
        exact BPair.oneValue_symm (BPair.mul_unit _)
    · refine BPair.oneValue_trans (foldB_mul_left q.2
        (fun ch : List (Nat × BPair) => if ch.map Prod.fst == m then prodW ch else BPair.unit)
        (prodLists (subs (memtable.sT T.wt) q.1))) ?_
      exact BPair.mul_congr (BPair.oneValue_refl q.2)
        (BPair.oneValue_trans (kerF_read (memtable.sT T.wt) q.1 m)
          (kerW_flip (memtable.sT T.wt) T.wt (fun t s => memtable.wtAt_sT T.wt t s) q.1 m))
  refine BPair.oneValue_trans h1 ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm h2)
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (famFold_flatMap_ov bpairFoldLaws _ _ v.val))
  exact foldB_congr_members _ _ v.val (fun q _ => BPair.oneValue_symm (h3 q))

/-- The weighted pairing is the unit-weight pairing against the
applied second vector, monomial by monomial. -/
theorem dotT_apply (T : memtable.Table) {k : Nat} (u v : SVec k) :
    (dotT T false u v).oneValue (dotT T true u (applyWt T v)) := by
  refine BPair.oneValue_trans (dotT_read T false u v) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (dotT_read T true u _))
  refine foldB_congr_members _ _ u.val (fun p _ => ?_)
  exact BPair.mul_congr (BPair.oneValue_refl p.2) (monDotT_apply T p.1 v)

/-- The walk reads the fold: the walk is the coordinate fold at the
shared monomials (`ground.mergeDot_read`, both displays in order at
`sortedV`), against the second vector at the unit weight and against
the applied second at a stated weight (`dotT_apply`). -/
theorem dotTS_read (T : memtable.Table) (uw : Bool) {k : Nat} (u v : SVec k) :
    (dotTS T uw u v).oneValue (dotT T uw u v) := by
  show (mergeDot lexLt (fun a b => a == b)
      (u.val.length + (if uw then v else applyWt T v).val.length) u.val
      (if uw then v else applyWt T v).val).oneValue (dotT T uw u v)
  cases uw with
  | true =>
    refine BPair.oneValue_trans (mergeDot_read lexLt (fun a b => a == b) lexLt_trans
      (fun _ _ h => listBeqEq h) lexLt_irrefl _ u.val v.val (Nat.le_refl _)
      (sortedV u) (sortedV v)) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (dotT_read T true u v))
    refine foldB_congr_members _ _ u.val (fun p _ => ?_)
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (coefAt_read p.1 v))
  | false =>
    refine BPair.oneValue_trans (mergeDot_read lexLt (fun a b => a == b) lexLt_trans
      (fun _ _ h => listBeqEq h) lexLt_irrefl _ u.val (applyWt T v).val (Nat.le_refl _)
      (sortedV u) (sortedV (applyWt T v))) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (dotT_apply T u v))
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (dotT_read T true u (applyWt T v)))
    refine foldB_congr_members _ _ u.val (fun p _ => ?_)
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (coefAt_read p.1 _))

/-- The canonical pairing at a stated weight is the canonical
unit-weight pairing against the applied vector. -/
theorem pairT_apply (T : memtable.Table) {k : Nat} (u v : SVec k) :
    pairT T false u v = pairT T true u (applyWt T v) :=
  BPair.norm_congr (BPair.oneValue_trans (dotTS_read T false u v)
    (BPair.oneValue_trans (dotT_apply T u v) (BPair.oneValue_symm (dotTS_read T true u _))))

/-- The weighted pairing exchanges at a symmetric weight: the two
vectors' double fold at the kernel exchanged, the kernel one value
at its two orders. -/
theorem dotT_comm (T : memtable.Table) (hw : memtable.symmWt T) (uw : Bool) {k : Nat}
    (u v : SVec k) :
    (dotT T uw u v).oneValue (dotT T uw v u) := by
  have hu := dotT_read T uw u v
  have hv := dotT_read T uw v u
  have h2 : (famFold BPair.add BPair.unit
      (fun p : List Nat × BPair => p.2 * monDotT T uw p.1 v) u.val).oneValue
      (famFold BPair.add BPair.unit
        (fun p : List Nat × BPair => famFold BPair.add BPair.unit
          (fun q : List Nat × BPair => p.2 * (q.2 * kerAt T uw p.1 q.1)) v.val) u.val) :=
    foldB_congr_members _ _ u.val (fun p _ =>
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl p.2) (monDotT_read T uw p.1 v))
        (BPair.oneValue_symm (foldB_mul_left p.2
          (fun q : List Nat × BPair => q.2 * kerAt T uw p.1 q.1) v.val)))
  have h3 := foldB_swapL
    (fun (p q : List Nat × BPair) => p.2 * (q.2 * kerAt T uw p.1 q.1)) u.val v.val
  have h4 : (famFold BPair.add BPair.unit
      (fun q : List Nat × BPair => famFold BPair.add BPair.unit
        (fun p : List Nat × BPair => p.2 * (q.2 * kerAt T uw p.1 q.1)) u.val) v.val).oneValue
      (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => q.2 * monDotT T uw q.1 u) v.val) :=
    foldB_congr_members _ _ v.val (fun q _ => by
      refine BPair.oneValue_trans ?_ (BPair.mul_congr (BPair.oneValue_refl q.2)
        (BPair.oneValue_symm (monDotT_read T uw q.1 u)))
      refine BPair.oneValue_trans ?_ (foldB_mul_left q.2
        (fun p : List Nat × BPair => p.2 * kerAt T uw q.1 p.1) u.val)
      refine foldB_congr_members _ _ u.val (fun p _ => ?_)
      show (p.2 * (q.2 * kerAt T uw p.1 q.1)).oneValue
        (q.2 * (p.2 * kerAt T uw q.1 p.1))
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl q.2)
        (BPair.mul_congr (BPair.oneValue_refl p.2) (kerAt_symm T hw uw p.1 q.1)))
  refine BPair.oneValue_trans hu ?_
  refine BPair.oneValue_trans h2 ?_
  refine BPair.oneValue_trans h3 ?_
  exact BPair.oneValue_trans h4 (BPair.oneValue_symm hv)

/-- A vector's height is the largest sum of its occupied
monomials' key heights, the vacant vector reading the sum's unit. -/
def heightV (heights : List Nat) {k : Nat} (v : SVec k) : Nat :=
  v.val.foldl (fun h p => Nat.max h (sumNat (p.1.map (getAt 0 heights)))) 0

/-- Every occupied monomial's summed height is at or below the
vector's maximum. -/
theorem heightV_mem (heights : List Nat) {k : Nat} (v : SVec k)
    (p : List Nat × BPair) (hp : p ∈ v.val) :
    sumNat (p.1.map (getAt 0 heights)) ≤ heightV heights v :=
  foldMax_mem (fun q : List Nat × BPair => sumNat (q.1.map (getAt 0 heights))) v.val 0 p hp

/-- At a key-height cap, a vector's height is capped by its slot
count times that cap. -/
theorem heightV_bound (heights : List Nat) (cap : Nat) {k : Nat} (v : SVec k)
    (hc : heights.all (fun h => decide (h ≤ cap)) = true) :
    heightV heights v ≤ k * cap := by
  apply foldMax_le _ v.val 0 (k * cap) (Nat.zero_le _)
  intro p hp
  have he := famFold_le (getAt 0 heights) (fun _ => cap) p.1 (fun x _ => by
    cases Nat.lt_or_ge x heights.length with
    | inl hxl => exact of_decide_eq_true (all_of_mem _ heights hc _ (mem_getAt 0 heights x hxl))
    | inr hxl => rw [getAt_over 0 heights x hxl]; exact Nat.zero_le _)
  rw [famFold_const, width_of_mem v p hp] at he
  rw [sumMap]
  exact he

/-- At standard slots, every occupied lowering image has strictly
smaller maximum height when each sparse key move drops one. -/
theorem heightV_lowerT (T : memtable.Table) (sig : List Bool) (i : Nat)
    (heights : List Nat) (v : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true)
    (hd : (getAt [] T.lowers i).all (fun e =>
      getAt 0 heights e.1 + 1 == getAt 0 heights e.2.1) = true)
    (ho : (lowerT T sig i v).val ≠ []) :
    heightV heights (lowerT T sig i v) < heightV heights v := by
  have hmon (q : List Nat × BPair) (hq : q ∈ (lowerT T sig i v).val) :
      sumNat (q.1.map (getAt 0 heights)) < heightV heights v := by
    obtain ⟨s, hs, p, hp, e, he, hsource, htarget⟩ := mem_lowerT T sig i v q hq
    have hsg : getAt false sig s = false := by
      have h := all_of_mem _ sig hsig _ (mem_getAt false sig s hs)
      cases hv : getAt false sig s with
      | false => rfl
      | true => rw [hv] at h; exact Bool.noConfusion h
    rw [hsg, if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)] at he
    have hdrop : getAt 0 heights e.1 + 1 = getAt 0 heights e.2.1 :=
      of_decide_eq_true (all_of_mem _ _ hd e he)
    have hsp : s < p.1.length := by rw [width_of_mem v p hp]; exact hs
    have hsum := sumNat_map_set_join (getAt 0 heights) 0 e.1 1 p.1 s hsp
      (by rw [hsource]; exact hdrop)
    rw [htarget] at hsum
    have hlt : sumNat (q.1.map (getAt 0 heights)) < sumNat (p.1.map (getAt 0 heights)) := by
      rw [← hsum]
      exact Nat.lt_succ_self _
    exact Nat.lt_of_lt_of_le hlt (heightV_mem heights v p hp)
  change ((lowerT T sig i v).val.foldl
    (fun h p => Nat.max h (sumNat (p.1.map (getAt 0 heights)))) 0) < heightV heights v
  apply foldMax_lt
  · cases hw : (lowerT T sig i v).val with
    | nil => exact False.elim (ho hw)
    | cons q t =>
      have hq : q ∈ (lowerT T sig i v).val := by rw [hw]; exact List.Mem.head t
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hmon q hq)
  · exact hmon

/-- The lowerings of a vector at a table and a signature, the vacant
ones withdrawn. -/
def lowerings (T : memtable.Table) (sig : List Bool) (v : SVec sig.length) :
    List (SVec sig.length) :=
  ((List.range T.rank).map (fun i => lowerT T sig i v)).filter (fun w => w.val.length != 0)

/-- Every listed lowering is an occupied image at a valid
simple index. -/
private theorem lowerings_mem (T : memtable.Table) (sig : List Bool) (v w : SVec sig.length)
    (hw : w ∈ lowerings T sig v) :
    ∃ i, i < T.rank ∧ lowerT T sig i v = w ∧ w.val ≠ [] := by
  have hm := mem_filter_of _ _ w hw
  obtain ⟨i, hi, he⟩ := mem_map_of _ _ w hm.1
  refine ⟨i, ltOfMemRange hi, he, ?_⟩
  intro hz
  have hkeep : (w.val.length != 0) = true := hm.2
  rw [hz] at hkeep
  exact Bool.noConfusion hkeep

/-- A vector joined to a pool at the membership read within its
weight's group: the group's Gram with the vector at the weighted
pairing reads a determinant off the sum's unit (`elim.joinIndep`,
`lem:lowerspan`'s independence read), a member of the group's span
refused. -/
def tryAddT (T : memtable.Table) (sig : List Bool) (pool : List (SVec sig.length))
    (v : SVec sig.length) : List (SVec sig.length) :=
  let w := weightV T sig v
  let group := pool.filter (fun h => weightV T sig h == w)
  let uw := unitWtRead T
  if elim.joinIndep (pairT T uw) group v then pool ++ [v]
  else pool

/-- A membership join keeps the pool or appends its input. -/
private theorem tryAddT_split (T : memtable.Table) (sig : List Bool)
    (pool : List (SVec sig.length)) (v : SVec sig.length) :
    tryAddT T sig pool v = pool ∨ tryAddT T sig pool v = pool ++ [v] := by
  unfold tryAddT
  by_cases h : elim.joinIndep (pairT T (unitWtRead T))
      (pool.filter (fun w => weightV T sig w == weightV T sig v)) v = true
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

/-- A vector off its self-pairing's unit seeds the pool as
one member at the one-by-one Gram. -/
private theorem tryAddT_single (T : memtable.Table) (sig : List Bool) (v : SVec sig.length)
    (h : ¬ (pairT T (unitWtRead T) v v).oneValue BPair.unit) :
    tryAddT T sig [] v = [v] := by
  change (if elim.joinIndep (pairT T (unitWtRead T)) [] v then [v] else []) = [v]
  rw [elim.joinIndep_single _ v h]
  rfl

/-- The lowering closure at a table and a signature from stated
seeds, each round joining the last round's members' lowerings at
the membership read (`ground.closeBy`), a vacant lowering
withdrawn. -/
def closeT (T : memtable.Table) (sig : List Bool) :
    Nat → List (SVec sig.length) → List (SVec sig.length) → List (SVec sig.length) :=
  ground.closeBy (lowerings T sig) (tryAddT T sig)

/-- A membership join keeps any property of its pool and its
new member. -/
theorem tryAddT_all (T : memtable.Table) (sig : List Bool) (P : SVec sig.length → Prop)
    (pool : List (SVec sig.length)) (v : SVec sig.length)
    (hp : ∀ w ∈ pool, P w) (hv : P v) : ∀ w ∈ tryAddT T sig pool v, P w := by
  cases tryAddT_split T sig pool v with
  | inl he => rw [he]; exact hp
  | inr he =>
    rw [he]
    intro w hw
    cases mem_append_of pool [v] hw with
    | inl h => exact hp w h
    | inr h =>
      cases h with
      | head => exact hv
      | tail _ h => nomatch h

/-- The membership join keeps every prior pool member. -/
theorem tryAddT_mem (T : memtable.Table) (sig : List Bool)
    (pool : List (SVec sig.length)) (v w : SVec sig.length) (hw : w ∈ pool) :
    w ∈ tryAddT T sig pool v := by
  cases tryAddT_split T sig pool v with
  | inl he => rw [he]; exact hw
  | inr he => rw [he]; exact mem_append_left [v] hw

/-- The lowering closure keeps every member property preserved
by each simple lowering. -/
theorem closeT_all (T : memtable.Table) (sig : List Bool) (P : SVec sig.length → Prop)
    (hstep : ∀ v, P v → ∀ i, i < T.rank → (lowerT T sig i v).val ≠ [] → P (lowerT T sig i v))
    (fuel : Nat) (pool fresh : List (SVec sig.length))
    (hp : ∀ v ∈ pool, P v) (hf : ∀ v ∈ fresh, P v) :
    ∀ v ∈ closeT T sig fuel pool fresh, P v := by
  apply closeBy_all P (lowerings T sig) (tryAddT T sig) _
    (fun l a hl ha => tryAddT_all T sig P l a hl ha) fuel pool fresh hp hf
  intro v hv w hw
  obtain ⟨i, hi, he, ho⟩ := lowerings_mem T sig v w hw
  rw [← he] at ho ⊢
  exact hstep v hv i hi ho

/-- G2's lowering closure has its final member list at the stored
fuel. Each occupied image drops a natural monomial height, whose
starting cap is six per slot against eight keys per slot. -/
theorem closeT_fuel_G2 (sig : List Bool) (extra : Nat)
    (pool fresh : List (SVec sig.length)) (hsig : sig.all (fun b => !b) = true) :
    closeT memtable.genG2 sig (sig.length * memtable.genG2.keys + 1 + extra) pool fresh
      = closeT memtable.genG2 sig (sig.length * memtable.genG2.keys + 1) pool fresh := by
  apply closeBy_fuel (lowerings memtable.genG2 sig) (tryAddT memtable.genG2 sig)
    (heightV memtable.keyHeightsG2) (tryAddT_split memtable.genG2 sig)
  · intro v w hw
    obtain ⟨i, hi, he, ho⟩ := lowerings_mem memtable.genG2 sig v w hw
    rw [← he] at ho ⊢
    exact heightV_lowerT memtable.genG2 sig i memtable.keyHeightsG2 v hsig
      (all_range_read _ memtable.genG2_height.2.2 i hi) ho
  · intro v _
    have hcap := heightV_bound memtable.keyHeightsG2 6 v memtable.genG2_height.2.1
    exact Nat.lt_of_le_of_lt (Nat.le_trans hcap
      (Nat.mul_le_mul_left sig.length (show 6 ≤ memtable.genG2.keys from by decide +kernel)))
      (Nat.lt_succ_self _)

/-- A vector with its display applied at a table's weight, the
application the datum's witness: the pool's member at the closures,
the weight applied once per member (`lem:lowerspan`'s collection
at the Gram grown a row per join, the joined member's row the walks
against the pool). -/
abbrev AVec (T : memtable.Table) (k : Nat) :=
  { p : SVec k × SVec k // p.2 = (if unitWtRead T then p.1 else applyWt T p.1) }

/-- A vector with its application. -/
def applied (T : memtable.Table) {k : Nat} (v : SVec k) : AVec T k :=
  ⟨(v, if unitWtRead T then v else applyWt T v), rfl⟩

/-- The pool's pairing: the first member's display walked against
the second's applied display, canonical. -/
def pairA (T : memtable.Table) {k : Nat} (p q : AVec T k) : BPair :=
  (mergeDot lexLt (fun a b => a == b) (p.val.1.val.length + q.val.2.val.length)
    p.val.1.val q.val.2.val).norm

/-- The pool's pairing is the canonical pairing of the members'
displays. -/
theorem pairA_read (T : memtable.Table) {k : Nat} (p q : AVec T k) :
    pairA T p q = pairT T (unitWtRead T) p.val.1 q.val.1 := by
  show (mergeDot lexLt (fun a b => a == b) (p.val.1.val.length + q.val.2.val.length)
      p.val.1.val q.val.2.val).norm
    = (mergeDot lexLt (fun a b => a == b)
      (p.val.1.val.length + (if unitWtRead T then q.val.1 else applyWt T q.val.1).val.length)
      p.val.1.val (if unitWtRead T then q.val.1 else applyWt T q.val.1).val).norm
  rw [q.property]

/-- The pool pairing exchanges exactly at a symmetric weight: the two
walks read one value (`dotT_comm` through `dotTS_read`) and the
canonical representative is the value's own (`BPair.norm_congr`). -/
theorem pairA_comm (T : memtable.Table) (hw : memtable.symmWt T) {k : Nat}
    (p q : AVec T k) : pairA T p q = pairA T q p := by
  rw [pairA_read, pairA_read]
  show (dotTS T (unitWtRead T) p.val.1 q.val.1).norm
    = (dotTS T (unitWtRead T) q.val.1 p.val.1).norm
  exact BPair.norm_congr
    (BPair.oneValue_trans (dotTS_read T (unitWtRead T) _ _)
      (BPair.oneValue_trans (dotT_comm T hw (unitWtRead T) _ _)
        (BPair.oneValue_symm (dotTS_read T (unitWtRead T) _ _))))

/-- The lowering closure at the stored descents over the applied
pool: `closeT`'s rounds at the keyed pool's join with every member
applied once, each round's members read off the pool. -/
def closeTS (T : memtable.Table) (sig : List Bool) :
    Nat → elim.PoolS (AVec T sig.length) (List BPair) → List (AVec T sig.length) →
      elim.PoolS (AVec T sig.length) (List BPair) :=
  elim.closeK (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
    (pairA T) (fun _ => false) (fun p => (lowerings T sig p.val.1).map (applied T))

/-- A block's pool at a table: the lowerings' closure at a stated
top at the stored descents (`lem:lowerspan`'s collection, one
descent per weight grade grown a row per join), the top joined at
the vacant pool's refusal and every lowering at the collection's,
the closure's fuel the top's slot count against the keys. -/
def blockPoolT (T : memtable.Table) (sig : List Bool) (top : SVec sig.length) :
    elim.PoolS (AVec T sig.length) (List BPair) :=
  elim.closeFromK (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
    (pairA T) (fun _ => false) (fun p => (lowerings T sig p.val.1).map (applied T))
    (sig.length * T.keys + 1) (applied T top) [applied T top]

/-- A block at a table: the lowerings' span at a stated top
(`lem:lowerspan`), the pool's members in the collection's order
(`blockSpanT_eq` its read at the fresh walk). -/
def blockSpanT (T : memtable.Table) (sig : List Bool) (top : SVec sig.length) :
    List (SVec sig.length) :=
  ((blockPoolT T sig top).1.reverse).map (fun p => p.val.1)

/-- A pool's grades at a table, each at its members' displays with
its Gram, its descent and its determinant. -/
private def poolGroups (T : memtable.Table) (sig : List Bool)
    (s : elim.PoolS (AVec T sig.length) (List BPair)) :
    List (elim.GroupS (SVec sig.length)) :=
  (elim.groupsK s).map (fun g => ⟨g.mems.map (fun p => p.val.1), g.gram, g.st, g.det⟩)

/-- A block's weight grades at a table: the pool's grades in the
members' order of first appearance (`elim.groupsK`,
`lem:lowerspan`'s arrangement), each its members in the collection's
order, its Gram grown a row per join, its descent and its
determinant, the descent's terminal entry (`lem:lowerspan`'s
collection at `def:elim`'s grown descent; `blockGroupsT_reads`). -/
def blockGroupsT (T : memtable.Table) (sig : List Bool) (top : SVec sig.length) :
    List (elim.GroupS (SVec sig.length)) :=
  poolGroups T sig (blockPoolT T sig top)

/-- A stated list's weight grades at a table: the list's collection
at the stored descents keyed at the weights (`elim.collectK`,
`lem:lowerspan`'s collection, an independent list its own), its
grades in the members' order of first appearance, each its members,
its Gram, its descent and its determinant (`listGroupsT_reads`). -/
def listGroupsT (T : memtable.Table) (sig : List Bool) (l : List (SVec sig.length)) :
    List (elim.GroupS (SVec sig.length)) :=
  poolGroups T sig (elim.collectK (fun a b : List BPair => a == b)
    (fun p => weightV T sig p.val.1) (pairA T) (l.map (applied T)))

/-- The Gram at the pool's pairing is the Gram of the members'
displays at the canonical pairing. -/
private theorem gramBy_pairA (T : memtable.Table) {k : Nat} (l : List (AVec T k)) :
    elim.gramBy (pairA T) l
      = elim.gramBy (pairT T (unitWtRead T)) (l.map (fun p => p.val.1)) := by
  show l.map (fun r => l.map (fun c => pairA T r c))
    = (l.map (fun p => p.val.1)).map (fun r =>
      (l.map (fun p => p.val.1)).map (fun c => pairT T (unitWtRead T) r c))
  rw [map_map]
  refine map_congr_all _ _ (fun r => ?_) l
  show l.map (fun c => pairA T r c)
    = (l.map (fun p => p.val.1)).map (fun c => pairT T (unitWtRead T) r.val.1 c)
  rw [map_map]
  exact map_congr_all _ _ (fun c => pairA_read T r c) l

/-- The Gram of a list at the weighted pairing over the applied
members, each applied once: at a symmetric weight the walks at or
beyond the diagonal with the lower triangle their transpose
(`elim.gramSym`), and at a further weight every walk; `gramT_eq`
its read as the pairings' Gram. -/
def gramT (T : memtable.Table) {k : Nat} (l : List (SVec k)) : elim.Mat :=
  if memtable.symmWt T then elim.gramSym (pairA T) (l.map (applied T))
  else elim.gramBy (pairA T) (l.map (applied T))

/-- The Gram at the applied members is the pairings' Gram: at a
symmetric weight through the pool pairing's exchange
(`pairA_read` with `dotT_comm` through `dotTS_read`). -/
theorem gramT_eq (T : memtable.Table) {k : Nat} (l : List (SVec k)) :
    gramT T l = elim.gramBy (pairT T (unitWtRead T)) l := by
  have hm : (l.map (applied T)).map (fun p : AVec T k => p.val.1) = l := by
    rw [map_map]
    show l.map (fun v => v) = l
    exact map_id l
  show (if memtable.symmWt T then elim.gramSym (pairA T) (l.map (applied T))
    else elim.gramBy (pairA T) (l.map (applied T))) = _
  by_cases hw : memtable.symmWt T
  · rw [if_pos hw, elim.gramSym_eq (pairA T) _ (pairA_comm T hw), gramBy_pairA, hm]
  · rw [if_neg hw, gramBy_pairA, hm]

/-- The join at the fresh walk over the applied pool projects to the
join over the displays: the filtered group's displays are the
displays' filtered group, and the joined Gram is the displays'. -/
private theorem tryAddL_proj (T : memtable.Table) (sig : List Bool)
    (l : List (AVec T sig.length)) (p : AVec T sig.length) :
    (elim.tryAddL (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
        (pairA T) (fun _ => false) l p).map (fun p => p.val.1)
      = tryAddT T sig (l.map (fun p => p.val.1)) p.val.1 := by
  show (if elim.joinIndep (pairA T)
        (l.filter (fun w => weightV T sig w.val.1 == weightV T sig p.val.1)) p
      then l ++ [p] else l).map (fun p => p.val.1)
    = (if elim.joinIndep (pairT T (unitWtRead T))
        ((l.map (fun p => p.val.1)).filter
          (fun h => weightV T sig h == weightV T sig p.val.1)) p.val.1
      then l.map (fun p => p.val.1) ++ [p.val.1] else l.map (fun p => p.val.1))
  have hf : (l.map (fun p => p.val.1)).filter (fun h => weightV T sig h == weightV T sig p.val.1)
      = (l.filter (fun w => weightV T sig w.val.1 == weightV T sig p.val.1)).map
          (fun p => p.val.1) :=
    filter_map _ _ l
  have hj : elim.joinIndep (pairA T)
        (l.filter (fun w => weightV T sig w.val.1 == weightV T sig p.val.1)) p
      = elim.joinIndep (pairT T (unitWtRead T))
        ((l.map (fun p => p.val.1)).filter
          (fun h => weightV T sig h == weightV T sig p.val.1)) p.val.1 := by
    show (if (elim.detD (elim.gramBy (pairA T)
          (l.filter (fun w => weightV T sig w.val.1 == weightV T sig p.val.1) ++ [p]))).oneValue
          BPair.unit then false else true)
      = (if (elim.detD (elim.gramBy (pairT T (unitWtRead T))
          ((l.map (fun p => p.val.1)).filter
            (fun h => weightV T sig h == weightV T sig p.val.1) ++ [p.val.1]))).oneValue
          BPair.unit then false else true)
    rw [hf, gramBy_pairA, map_append]
    rfl
  rw [hj]
  cases elim.joinIndep (pairT T (unitWtRead T))
      ((l.map (fun p => p.val.1)).filter
        (fun h => weightV T sig h == weightV T sig p.val.1)) p.val.1 with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    exact map_append _ l [p]
  | false =>
    rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
      if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]

/-- The block at the stored descents is the closure at the fresh
walk at a symmetric weight: the top's join at the vacant pool seeds
the trace, every join keeps it (`elim.closeK_eq_vacant` at the
pool pairing's exchange, `pairA_comm`), and the closure over the
applied pool projects to the closure over the displays (`ground.closeBy_map`, the lowerings'
applications projecting to the lowerings and the join to the
membership read's own, `tryAddL_proj`). -/
theorem blockSpanT_eq (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) :
    blockSpanT T sig top
      = closeT T sig (sig.length * T.keys + 1) (tryAddT T sig [] top) [top] := by
  have h1 := elim.closeK_eq_vacant (fun a b : List BPair => a == b)
    (fun p : AVec T sig.length => weightV T sig p.val.1) (pairA T) (fun _ => false)
    (fun _ _ h => ground.listBeqEq h) ground.listEqBeq (pairA_comm T hw)
    (fun p => (lowerings T sig p.val.1).map (applied T))
    (sig.length * T.keys + 1) (applied T top) [applied T top]
  show ((elim.closeFromK (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false) (fun p => (lowerings T sig p.val.1).map (applied T))
      (sig.length * T.keys + 1) (applied T top) [applied T top]).1.reverse).map
      (fun p => p.val.1)
    = ground.closeBy (lowerings T sig) (tryAddT T sig) (sig.length * T.keys + 1)
        (tryAddT T sig [] top) [top]
  rw [h1]
  have h2 := ground.closeBy_map (fun p : AVec T sig.length => p.val.1)
    (fun p => (lowerings T sig p.val.1).map (applied T))
    (elim.tryAddL (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false))
    (lowerings T sig) (tryAddT T sig)
    (fun p => by
      show ((lowerings T sig p.val.1).map (applied T)).map (fun p => p.val.1)
        = lowerings T sig p.val.1
      rw [map_map]
      exact map_id _)
    (tryAddL_proj T sig)
    (sig.length * T.keys + 1)
    (elim.tryAddL (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false) [] (applied T top))
    [applied T top]
  rw [h2, tryAddL_proj T sig [] (applied T top)]
  rfl

/-- At a symmetric table weight the stored block keeps every
property of its top that the simple lowerings preserve. -/
theorem blockSpanT_all (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (P : SVec sig.length → Prop) (ht : P top)
    (hstep : ∀ v, P v → ∀ i, i < T.rank → (lowerT T sig i v).val ≠ [] → P (lowerT T sig i v)) :
    ∀ v ∈ blockSpanT T sig top, P v := by
  rw [blockSpanT_eq T sig top hw]
  apply closeT_all T sig P hstep
  · exact tryAddT_all T sig P [] top (fun _ h => nomatch h) ht
  · intro v hv
    cases hv with
    | head => exact ht
    | tail _ h => nomatch h

/-- Every listed block member is an actual lowering word at the
seed, with each letter in the table's simple index (`con:slotpower`). -/
theorem blockSpanT_words (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) : ∀ v ∈ blockSpanT T sig top,
      ∃ word : List Nat, word.all (fun i => decide (i < T.rank)) = true ∧
        word.foldl (fun v i => lowerT T sig i v) top = v := by
  apply blockSpanT_all T sig top hw
  · exact ⟨[], rfl, rfl⟩
  · intro v hv i hi _
    obtain ⟨word, hword, he⟩ := hv
    refine ⟨word ++ [i], ?_, ?_⟩
    · rw [all_append, hword]
      change (true && (decide (i < T.rank) && true)) = true
      rw [decide_eq_true hi]
      rfl
    · rw [foldl_append, he]
      rfl

/-- The stored block uses only the table's keys when its top
does and each stored simple map targets that key list. -/
theorem blockSpanT_keys (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (ht : keysRead T.keys top)
    (hu : ∀ i, i < T.rank → (getAt [] T.raises i).all (fun e => decide (e.1 < T.keys)) = true)
    (hd : ∀ i, i < T.rank → (getAt [] T.lowers i).all (fun e => decide (e.1 < T.keys)) = true) :
    ∀ v ∈ blockSpanT T sig top, keysRead T.keys v :=
  blockSpanT_all T sig top hw (keysRead T.keys) ht
    (fun v hv i hi _ => keysRead_lowerT T sig i (hu i hi) (hd i hi) v hv)

/-- Every member collected from an occupied top is occupied;
the closure's step list withdraws vacant lowerings. -/
theorem blockSpanT_occupied (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (ht : top.val ≠ []) :
    ∀ v ∈ blockSpanT T sig top, v.val ≠ [] :=
  blockSpanT_all T sig top hw (fun v => v.val ≠ []) ht (fun _ _ _ _ h => h)

/-- A top off its self-pairing's unit joins the stored block
and stays in it through every lowering round. -/
theorem blockSpanT_top (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (ht : ¬ (pairT T (unitWtRead T) top top).oneValue BPair.unit) :
    top ∈ blockSpanT T sig top := by
  rw [blockSpanT_eq T sig top hw, tryAddT_single T sig top ht]
  apply closeBy_mem (lowerings T sig) (tryAddT T sig)
    (fun l a x hx => tryAddT_mem T sig l a x hx)
  exact List.Mem.head _

/-- The stored block is its top followed by occupied simple
lowerings. A property preserved by the lowerings and a read
of each image hold throughout that tail. -/
theorem blockSpanT_tail (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (ht : ¬ (pairT T (unitWtRead T) top top).oneValue BPair.unit)
    (Q R : SVec sig.length → Prop) (hQ : Q top)
    (hstep : ∀ v, Q v → ∀ i, i < T.rank → (lowerT T sig i v).val ≠ [] →
      Q (lowerT T sig i v) ∧ R (lowerT T sig i v)) :
    ∃ tail, blockSpanT T sig top = top :: tail ∧ ∀ v ∈ tail, Q v ∧ R v := by
  rw [blockSpanT_eq T sig top hw, tryAddT_single T sig top ht]
  have hs : ∀ v ∈ [top], Q v := by
    intro v hv
    cases hv with
    | head => exact hQ
    | tail _ h => nomatch h
  apply closeBy_reads Q R (lowerings T sig) (tryAddT T sig) (tryAddT_split T sig) _
    (sig.length * T.keys + 1) [top] [top] hs hs
  intro v hv w hw
  obtain ⟨i, hi, he, ho⟩ := lowerings_mem T sig v w hw
  rw [← he] at ho ⊢
  exact hstep v hv i hi ho

/-- Every occupied G2 top is a member of its actual stored
lowering span, the generating pairing the coordinate pairing. -/
theorem blockSpanT_top_G2 (sig : List Bool) (top : SVec sig.length) (ht : top.val ≠ []) :
    top ∈ blockSpanT memtable.genG2 sig top := by
  apply blockSpanT_top memtable.genG2 sig top memtable.genG2_symmWt
  have hw : unitWtRead memtable.genG2 = true := by decide +kernel
  rw [hw]
  exact offOfUnitLt (pairT_self_pos memtable.genG2 top ht)

/-- Every weight in the stored block has the member's rank,
at the table's diagonal widths and finite action carrier. -/
theorem blockSpanT_weight_length (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (ht : keysRead T.keys top)
    (hu : ∀ i, i < T.rank → (getAt [] T.raises i).all (fun e => decide (e.1 < T.keys)) = true)
    (hd : ∀ i, i < T.rank → (getAt [] T.lowers i).all (fun e => decide (e.1 < T.keys)) = true)
    (hh : elim.rowsLen T.keys T.hdiag) (hr : T.hdiag.length = T.rank) :
    ∀ v ∈ blockSpanT T sig top, (weightV T sig v).length = T.rank :=
  fun v hv => weightV_length T sig v rfl hh hr (blockSpanT_keys T sig top hw ht hu hd v hv)

/-- G2's stored block stays in its eight generating keys at
every slot signature and every top in that carrier. -/
theorem blockSpanT_keys_G2 (sig : List Bool) (top : SVec sig.length)
    (ht : keysRead memtable.genG2.keys top) :
    ∀ v ∈ blockSpanT memtable.genG2 sig top, keysRead memtable.genG2.keys v :=
  blockSpanT_keys memtable.genG2 sig top memtable.genG2_symmWt ht
    (fun i hi => (memtable.genG2_actionKeys i hi).1)
    (fun i hi => (memtable.genG2_actionKeys i hi).2)

/-- The actual G2 block's member list equals the lowering walk
at every fuel beyond its stored bound, at every standard-slot top. -/
theorem blockSpanT_fuel_G2 (sig : List Bool) (top : SVec sig.length) (extra : Nat)
    (hsig : sig.all (fun b => !b) = true) :
    blockSpanT memtable.genG2 sig top
      = closeT memtable.genG2 sig (sig.length * memtable.genG2.keys + 1 + extra)
        (tryAddT memtable.genG2 sig [] top) [top] := by
  rw [blockSpanT_eq memtable.genG2 sig top memtable.genG2_symmWt]
  apply Eq.symm
  exact closeT_fuel_G2 sig extra _ [top] hsig

/-- G2's stored block weights are two-coroot lists. -/
theorem blockSpanT_weight_length_G2 (sig : List Bool) (top : SVec sig.length)
    (ht : keysRead memtable.genG2.keys top) :
    ∀ v ∈ blockSpanT memtable.genG2 sig top, (weightV memtable.genG2 sig v).length = 2 :=
  blockSpanT_weight_length memtable.genG2 sig top memtable.genG2_symmWt ht
    (fun i hi => (memtable.genG2_actionKeys i hi).1)
    (fun i hi => (memtable.genG2_actionKeys i hi).2)
    memtable.genG2_diagonals.1 memtable.genG2_diagonals.2

/-- A block at the uniform signature of a stated slot count and
dagger read, the members read at the count. -/
def blockSpanW (T : memtable.Table) (k : Nat) (dag : Bool) (top : SVec k) : List (SVec k) :=
  (blockSpanT T (List.replicate k dag) (castV (length_replicate dag k).symm top)).map
    (castV (length_replicate dag k))

/-- The uniform-signature block stays in the generating key
list whenever its top and simple maps do. -/
theorem blockSpanW_keys (T : memtable.Table) (k : Nat) (dag : Bool) (top : SVec k)
    (hw : memtable.symmWt T) (ht : keysRead T.keys top)
    (hu : ∀ i, i < T.rank → (getAt [] T.raises i).all (fun e => decide (e.1 < T.keys)) = true)
    (hd : ∀ i, i < T.rank → (getAt [] T.lowers i).all (fun e => decide (e.1 < T.keys)) = true) :
    ∀ v ∈ blockSpanW T k dag top, keysRead T.keys v := by
  intro v hv
  obtain ⟨w, hw', he⟩ := mem_map_of _ _ v hv
  rw [← he]
  exact blockSpanT_keys T (List.replicate k dag) _ hw ht hu hd w hw'

/-- Every occupied G2 top is a member of the uniform-signature
block at its own slot count. -/
theorem blockSpanW_top_G2 (k : Nat) (dag : Bool) (top : SVec k) (ht : top.val ≠ []) :
    top ∈ blockSpanW memtable.genG2 k dag top := by
  have hm := mem_map_to (castV (length_replicate dag k))
    (blockSpanT_top_G2 (List.replicate k dag)
      (castV (length_replicate dag k).symm top) ht)
  have he : castV (length_replicate dag k) (castV (length_replicate dag k).symm top) = top :=
    Subtype.ext rfl
  rw [he] at hm
  exact hm

/-- A pool's grades' reads at its own keys and its keyed reads: a
grade's members are the pool's members at the grade's weight, its
Gram their `gramT`, its determinant one value with the Gram's, and
every leading minor of the Gram sits off the sum's unit
(`elim.traceOf_lead` at the stored descent). -/
private theorem poolGroups_reads (T : memtable.Table) (sig : List Bool)
    (s : elim.PoolS (AVec T sig.length) (List BPair))
    (hkeys : s.2.map Prod.fst = dedupF (s.1.reverse.map (fun p => weightV T sig p.val.1)))
    (hown : ∀ i, i < s.2.length →
      elim.groupAtK (fun a b : List BPair => a == b) s
          (getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).1
        = (getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).2)
    (hr : ∀ k, (elim.groupAtK (fun a b : List BPair => a == b) s k).mems
        = s.1.reverse.filter (fun w =>
          (fun a b : List BPair => a == b) ((fun p => weightV T sig p.val.1) w) k)
      ∧ (elim.groupAtK (fun a b : List BPair => a == b) s k).gram
        = elim.gramBy (pairA T) (elim.groupAtK (fun a b : List BPair => a == b) s k).mems
      ∧ elim.traceOf (elim.groupAtK (fun a b : List BPair => a == b) s k).st
          (elim.groupAtK (fun a b : List BPair => a == b) s k).gram
      ∧ ((elim.groupAtK (fun a b : List BPair => a == b) s k).det).oneValue
          (elim.detL (elim.groupAtK (fun a b : List BPair => a == b) s k).gram))
    (i : Nat) (hi : i < (poolGroups T sig s).length) :
    (getAt (elim.vacantG _) (poolGroups T sig s) i).mems
      = (s.1.reverse.map (fun p => p.val.1)).filter (fun v => weightV T sig v
          == getAt [] (dedupF ((s.1.reverse.map (fun p => p.val.1)).map (weightV T sig))) i)
    ∧ (getAt (elim.vacantG _) (poolGroups T sig s) i).gram
      = gramT T (getAt (elim.vacantG _) (poolGroups T sig s) i).mems
    ∧ ((getAt (elim.vacantG _) (poolGroups T sig s) i).det).oneValue
      (elim.detL (getAt (elim.vacantG _) (poolGroups T sig s) i).gram)
    ∧ ∀ k, k < (getAt (elim.vacantG _) (poolGroups T sig s) i).mems.length →
      ¬ (elim.leadMinor (getAt (elim.vacantG _) (poolGroups T sig s) i).gram
          (k + 1)).oneValue BPair.unit := by
  have hkeys' : (s.1.reverse.map (fun p => p.val.1)).map (weightV T sig)
      = s.1.reverse.map (fun p => weightV T sig p.val.1) := map_map _ _ _
  have hi1 : i < s.2.length := by
    have hi' : i < ((s.2.map Prod.snd).map (fun g : elim.GroupS (AVec T sig.length) =>
        (⟨g.mems.map (fun p => p.val.1), g.gram, g.st, g.det⟩
          : elim.GroupS (SVec sig.length)))).length := hi
    rw [length_map, length_map] at hi'
    exact hi'
  have hkey : (getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).1
      = getAt [] (dedupF ((s.1.reverse.map (fun p => p.val.1)).map (weightV T sig))) i := by
    rw [hkeys', ← hkeys, getAt_map ([], elim.vacantG (AVec T sig.length)) [] Prod.fst s.2 i hi1]
  have hg : getAt (elim.vacantG _) (poolGroups T sig s) i
      = ⟨((getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).2).mems.map (fun p => p.val.1),
         ((getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).2).gram,
         ((getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).2).st,
         ((getAt ([], elim.vacantG (AVec T sig.length)) s.2 i).2).det⟩ := by
    show getAt (elim.vacantG _) ((s.2.map Prod.snd).map (fun g => (⟨g.mems.map (fun p => p.val.1),
      g.gram, g.st, g.det⟩ : elim.GroupS (SVec sig.length)))) i = _
    rw [getAt_map (elim.vacantG (AVec T sig.length)) (elim.vacantG _) _ _ i
        (by rw [length_map]; exact hi1),
      getAt_map ([], elim.vacantG (AVec T sig.length)) (elim.vacantG (AVec T sig.length))
        Prod.snd s.2 i hi1]
  rw [hg, ← hown i hi1, hkey]
  have hr' := hr (getAt [] (dedupF ((s.1.reverse.map (fun p => p.val.1)).map (weightV T sig))) i)
  refine ⟨?_, ?_, hr'.2.2.2, fun k hk => ?_⟩
  · show ((elim.groupAtK (fun a b : List BPair => a == b) s _).mems.map (fun p => p.val.1)) = _
    rw [hr'.1]
    exact (filter_map (fun p : AVec T sig.length => p.val.1)
      (fun v => weightV T sig v
        == getAt [] (dedupF ((s.1.reverse.map (fun p => p.val.1)).map (weightV T sig))) i)
      s.1.reverse).symm
  · show (elim.groupAtK (fun a b : List BPair => a == b) s _).gram
      = gramT T ((elim.groupAtK (fun a b : List BPair => a == b) s _).mems.map (fun p => p.val.1))
    rw [hr'.2.1, gramT_eq, gramBy_pairA]
  · refine elim.traceOf_lead _ _ hr'.2.2.1 k ?_
    rw [hr'.2.1, elim.length_gramBy]
    rw [length_map] at hk
    exact hk

/-- A block's grades' reads at a symmetric weight (`lem:lowerspan`'s
collection at `def:elim`'s grown descent): a grade's members are the
block's members at the grade's weight, the grades at the weights'
first appearance, its Gram their `gramT`, its determinant one value
with the Gram's, and every leading minor of the Gram sits off the
sum's unit (`elim.closeK_reads`, `elim.closeK_keys`, `elim.closeK_own`
at the pool pairing's exchange, `pairA_comm`). -/
theorem blockGroupsT_reads (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (i : Nat) (hi : i < (blockGroupsT T sig top).length) :
    (getAt (elim.vacantG _) (blockGroupsT T sig top) i).mems
      = (blockSpanT T sig top).filter (fun v => weightV T sig v
          == getAt [] (dedupF ((blockSpanT T sig top).map (weightV T sig))) i)
    ∧ (getAt (elim.vacantG _) (blockGroupsT T sig top) i).gram
      = gramT T (getAt (elim.vacantG _) (blockGroupsT T sig top) i).mems
    ∧ ((getAt (elim.vacantG _) (blockGroupsT T sig top) i).det).oneValue
      (elim.detL (getAt (elim.vacantG _) (blockGroupsT T sig top) i).gram)
    ∧ ∀ k, k < (getAt (elim.vacantG _) (blockGroupsT T sig top) i).mems.length →
      ¬ (elim.leadMinor (getAt (elim.vacantG _) (blockGroupsT T sig top) i).gram
          (k + 1)).oneValue BPair.unit :=
  poolGroups_reads T sig (blockPoolT T sig top)
    (elim.closeK_keys (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false) (fun _ _ h => listBeqEq h) listEqBeq (pairA_comm T hw)
      (fun p => (lowerings T sig p.val.1).map (applied T)) (sig.length * T.keys + 1)
      (applied T top) [applied T top])
    (fun i hi => elim.closeK_own (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false) (fun _ _ h => listBeqEq h) listEqBeq (pairA_comm T hw)
      (fun p => (lowerings T sig p.val.1).map (applied T)) (sig.length * T.keys + 1)
      (applied T top) [applied T top] _ i hi)
    (fun k => elim.closeK_reads (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false) (fun _ _ h => listBeqEq h) listEqBeq (pairA_comm T hw)
      (fun p => (lowerings T sig p.val.1).map (applied T)) (sig.length * T.keys + 1)
      (applied T top) [applied T top] k)
    i hi

/-- A stated list's grades' reads at a symmetric weight: the
collection's members at the grade's weight, the Gram their `gramT`,
the determinant the Gram's and every leading minor off the unit
(`elim.collectK_reads`, `elim.collectK_keys`, `elim.collectK_own`). -/
theorem listGroupsT_reads (T : memtable.Table) (sig : List Bool) (l : List (SVec sig.length))
    (hw : memtable.symmWt T) (i : Nat) (hi : i < (listGroupsT T sig l).length) :
    (getAt (elim.vacantG _) (listGroupsT T sig l) i).mems
      = ((elim.collectK (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
          (pairA T) (l.map (applied T))).1.reverse.map (fun p => p.val.1)).filter
          (fun v => weightV T sig v
            == getAt [] (dedupF (((elim.collectK (fun a b : List BPair => a == b)
              (fun p => weightV T sig p.val.1) (pairA T) (l.map (applied T))).1.reverse.map
                (fun p => p.val.1)).map (weightV T sig))) i)
    ∧ (getAt (elim.vacantG _) (listGroupsT T sig l) i).gram
      = gramT T (getAt (elim.vacantG _) (listGroupsT T sig l) i).mems
    ∧ ((getAt (elim.vacantG _) (listGroupsT T sig l) i).det).oneValue
      (elim.detL (getAt (elim.vacantG _) (listGroupsT T sig l) i).gram)
    ∧ ∀ k, k < (getAt (elim.vacantG _) (listGroupsT T sig l) i).mems.length →
      ¬ (elim.leadMinor (getAt (elim.vacantG _) (listGroupsT T sig l) i).gram
          (k + 1)).oneValue BPair.unit :=
  poolGroups_reads T sig _
    (elim.collectK_keys (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ _ h => listBeqEq h) listEqBeq (pairA_comm T hw) (l.map (applied T)))
    (fun i hi => elim.collectK_own (fun a b : List BPair => a == b)
      (fun p => weightV T sig p.val.1) (pairA T) (fun _ _ h => listBeqEq h) listEqBeq
      (pairA_comm T hw) (l.map (applied T)) _ i hi)
    (fun k => elim.collectK_reads (fun a b : List BPair => a == b)
      (fun p => weightV T sig p.val.1) (pairA T) (fun _ _ h => listBeqEq h) listEqBeq
      (pairA_comm T hw) (l.map (applied T)) k)
    i hi

/-- The grades' count is the members' distinct weights' count, at a
block. -/
theorem blockGroupsT_length (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) :
    (blockGroupsT T sig top).length
      = (dedupF ((blockSpanT T sig top).map (weightV T sig))).length := by
  show ((elim.groupsK (blockPoolT T sig top)).map _).length = _
  rw [length_map]
  show ((blockPoolT T sig top).2.map Prod.snd).length = _
  have hk : (blockPoolT T sig top).2.map Prod.fst
      = dedupF ((blockPoolT T sig top).1.reverse.map (fun p => weightV T sig p.val.1)) :=
    elim.closeK_keys (fun a b : List BPair => a == b) (fun p => weightV T sig p.val.1)
      (pairA T) (fun _ => false) (fun _ _ h => listBeqEq h) listEqBeq (pairA_comm T hw)
      (fun p => (lowerings T sig p.val.1).map (applied T)) (sig.length * T.keys + 1)
      (applied T top) [applied T top]
  rw [length_map, ← length_map (Prod.fst (α := List BPair) (β := elim.GroupS (AVec T sig.length))),
    hk, show ((blockSpanT T sig top).map (weightV T sig))
      = (blockPoolT T sig top).1.reverse.map (fun p => weightV T sig p.val.1) from map_map _ _ _]

/-- A list's places grouped at its members' weights, the grades in
the weights' order of first appearance (`elim.placesBy` at the
weight read, `lem:lowerspan`'s arrangement). -/
def weightPlaces (T : memtable.Table) (sig : List Bool) {k : Nat} (l : List (SVec k)) :
    List (List Nat) :=
  elim.placesBy (fun j => weightV T sig (getAt (emptyV k) l j)) l.length

/-- The weight places' count is the members' distinct weights'
count. -/
theorem weightPlaces_length (T : memtable.Table) (sig : List Bool) {k : Nat} (l : List (SVec k)) :
    (weightPlaces T sig l).length = (dedupF (l.map (weightV T sig))).length := by
  show ((dedupF ((List.range l.length).map (fun j => weightV T sig (getAt (emptyV k) l j)))).map
    _).length = _
  rw [length_map, ← map_map (getAt (emptyV k) l) (weightV T sig),
    range_map_getAt (emptyV k) l.length l rfl]

/-- A weight grade's places read the list's members at the grade's
weight: the list filtered at the weight is the places' members. -/
theorem weightPlaces_read (T : memtable.Table) (sig : List Bool) {k : Nat} (l : List (SVec k))
    (i : Nat) (hi : i < (dedupF (l.map (weightV T sig))).length) :
    l.filter (fun v => weightV T sig v == getAt [] (dedupF (l.map (weightV T sig))) i)
      = (getAt [] (weightPlaces T sig l) i).map (getAt (emptyV k) l) := by
  have hkeys : (List.range l.length).map (fun j => weightV T sig (getAt (emptyV k) l j))
      = l.map (weightV T sig) := by
    rw [← map_map (getAt (emptyV k) l) (weightV T sig), range_map_getAt (emptyV k) l.length l rfl]
  have hi' : i < (weightPlaces T sig l).length := by
    rw [weightPlaces_length]
    exact hi
  show l.filter (fun v => weightV T sig v == getAt [] (dedupF (l.map (weightV T sig))) i)
    = (getAt [] (elim.placesBy (fun j => weightV T sig (getAt (emptyV k) l j)) l.length) i).map
        (getAt (emptyV k) l)
  rw [elim.placesBy_getAt _ l.length i hi', hkeys,
    getAt_dflt (weightV T sig (getAt (emptyV k) l 0)) [] _ i hi,
    filter_map_range (emptyV k) _ l]
  refine congrArg (fun q : List Nat => q.map (getAt (emptyV k) l)) ?_
  exact filter_congr _ _ (fun j => listBeq_decide _ _) _

/-- A block's grades at the uniform signature of a stated slot count
and dagger read, the members read at the count. -/
def blockGroupsW (T : memtable.Table) (k : Nat) (dag : Bool) (top : SVec k) :
    List (elim.GroupS (SVec k)) :=
  (blockGroupsT T (List.replicate k dag) (castV (length_replicate dag k).symm top)).map
    (fun g => ⟨g.mems.map (castV (length_replicate dag k)), g.gram, g.st, g.det⟩)

set_option genInjectivity false in
/-- An end's block at a vertex: the end's slot signature, its slot
count with the signature's read of it, and the block's members in
the end's power. -/
structure EndBlock where
  sig : List Bool
  wid : Nat
  hwid : sig.length = wid
  blk : List (SVec wid)

/-- The ends' joined signature, the vertex's slot list. -/
def fusedSig (ends : List EndBlock) : List Bool := ends.flatMap EndBlock.sig

/-- The joined signature's slot count is the ends' slot counts'
sum. -/
theorem length_fusedSig : ∀ ends : List EndBlock,
    (fusedSig ends).length = sumNat (ends.map EndBlock.wid)
  | [] => rfl
  | e :: t => by
    show (e.sig ++ fusedSig t).length = e.wid + sumNat (t.map EndBlock.wid)
    rw [length_append, e.hwid, length_fusedSig t]

/-- The member lists over the ends from a stated pool, one member
per end with its count, the weight lists joined and the weights
summed. -/
private def fusedLists (T : memtable.Table) :
    List (List WVec × List (List BPair) × List BPair) → List EndBlock →
      List (List WVec × List (List BPair) × List BPair)
  | P, [] => P
  | P, e :: rest =>
    let blk := e.blk.map (fun v => (v, weightV T e.sig v))
    fusedLists T (P.flatMap (fun t => blk.map (fun b =>
      (t.1 ++ [⟨e.wid, b.1⟩], t.2.1 ++ [b.2],
       List.zipWith (fun x y => (x + y).norm) t.2.2 b.2)))) rest

/-- A member list's tensor with its count, the tensors from the
scalar one in the list's order. -/
private def foldW (l : List WVec) : WVec :=
  l.foldl (fun (a : WVec) b => ⟨a.1 + b.1, tensorV a.2 b.2⟩) ⟨0, unitV⟩

/-- The tensor fold's count is the seed's joined to the members'
counts' sum. -/
theorem foldW_width : ∀ (l : List WVec) (a : WVec),
    (l.foldl (fun (a : WVec) b => ⟨a.1 + b.1, tensorV a.2 b.2⟩) a).1
      = a.1 + sumNat (l.map Sigma.fst)
  | [], _ => rfl
  | b :: t, a => by
    show (t.foldl (fun (a : WVec) b => ⟨a.1 + b.1, tensorV a.2 b.2⟩)
      ⟨a.1 + b.1, tensorV a.2 b.2⟩).1 = a.1 + (b.1 + sumNat (t.map Sigma.fst))
    rw [foldW_width t ⟨a.1 + b.1, tensorV a.2 b.2⟩]
    exact Nat.add_assoc _ _ _

/-- Every member list over the ends reads the ends' counts after
the seed's. -/
private theorem fusedLists_widths (T : memtable.Table) :
    ∀ (ends : List EndBlock) (P : List (List WVec × List (List BPair) × List BPair))
      (pre : List Nat), (∀ t ∈ P, t.1.map Sigma.fst = pre) →
      ∀ t ∈ fusedLists T P ends, t.1.map Sigma.fst = pre ++ ends.map EndBlock.wid
  | [], P, pre, h, t, ht => by
    show t.1.map Sigma.fst = pre ++ []
    rw [append_nil]
    exact h t ht
  | e :: rest, P, pre, h, t, ht => by
    have h' := fusedLists_widths T rest _ (pre ++ [e.wid]) (fun t ht => by
      obtain ⟨t0, _, ht0⟩ := mem_flatMap_of _ _ t ht
      obtain ⟨b, _, hb⟩ := mem_map_of _ _ t ht0
      rw [← hb]
      show (t0.1 ++ [(⟨e.wid, b.1⟩ : WVec)]).map Sigma.fst = pre ++ [e.wid]
      rw [map_append, h t0 (by assumption)]
      rfl) t ht
    rw [h', append_assoc]
    rfl

/-- The unit-weight lists' tensors read the joined signature's
count. -/
private theorem fusedUnit_widths (T : memtable.Table) (ends : List EndBlock) :
    ∀ t ∈ (fusedLists T [([], [], List.replicate T.rank BPair.unit)] ends).filter
      (fun t => t.2.2.all (fun x => decide (x.oneValue BPair.unit))),
      (foldW t.1).1 = (fusedSig ends).length := fun t ht => by
  have hm := (mem_filter_of _ _ t ht).1
  have hw := fusedLists_widths T ends _ [] (fun t0 ht0 => by
    cases ht0 with
    | head => rfl
    | tail _ h => exact nomatch h) t hm
  show (t.1.foldl (fun (a : WVec) b => ⟨a.1 + b.1, tensorV a.2 b.2⟩) ⟨0, unitV⟩).1 = _
  rw [foldW_width, hw, length_fusedSig]
  show 0 + sumNat (ends.map EndBlock.wid) = _
  exact Nat.zero_add _

/-- The lists' tensors at the stated count. -/
private def castAll (W : Nat) :
    (l : List (List WVec × List (List BPair) × List BPair)) →
      (∀ t ∈ l, (foldW t.1).1 = W) → List (SVec W × List (List BPair) × List BPair)
  | [], _ => []
  | t :: r, h =>
    (castV (h t (List.Mem.head _)) (foldW t.1).2, t.2)
      :: castAll W r (fun x hx => h x (List.Mem.tail _ hx))

/-- The fused span at a table over stated end blocks grouped at the
ends' weight lists: the blocks' tensors at the unit weight, the
families at one weight list one group, the tensors read at the
unit-weight lists alone in the joined signature's power. -/
def fusedGroupsT (T : memtable.Table) (ends : List EndBlock) :
    List (List (SVec (fusedSig ends).length)) :=
  let lists := fusedLists T [([], [], List.replicate T.rank BPair.unit)] ends
  let unit := lists.filter (fun t => t.2.2.all (fun x => decide (x.oneValue BPair.unit)))
  let combos := castAll (fusedSig ends).length unit (fusedUnit_widths T ends)
  (ground.dedupF (combos.map (fun t => t.2.1))).map (fun key =>
    (combos.filter (fun t => t.2.1 == key)).map (fun t => t.1))

/-- The fused span at a table, its groups joined. -/
def fusedSpanT (T : memtable.Table) (ends : List EndBlock) :
    List (SVec (fusedSig ends).length) :=
  (fusedGroupsT T ends).flatMap (fun g => g)

/-- The stacked raisings' rows over a pool at a table: per simple
index the rows at the images' occupied monomials, the index the
images' keys collected in the lexicographic order and each image
walked once against it (`ground.mergeWith`, the unit at an index
key the image lacks), the rows the walks' transpose, one row per
image monomial at the members' image coefficients. -/
def raiseRowsT (T : memtable.Table) (sig : List Bool) (pool : List (SVec sig.length)) :
    elim.Mat :=
  (List.range T.rank).flatMap (fun i =>
    let imgs := pool.map (raiseT T sig i)
    let keys := (collectBy lexLt (fun a b => a == b) (imgs.flatMap (fun im =>
      im.val.map (fun p => (p.1, BPair.ofNat 1))))).map (fun p => (p.1, ()))
    elim.transposeM (imgs.map (fun im =>
      mergeWith lexLt (fun a b => a == b) (fun a _ => a.map (fun _ => BPair.unit))
        (fun _ _ c r => c :: r) (fun _ r => BPair.unit :: r) (fun _ r => r)
        (keys.length + im.val.length) keys im.val)))

/-- The invariants over a pool at a table: the stacked raisings'
kernel list at the back solve, one member per pivot-free column. -/
def kernelT (T : memtable.Table) (sig : List Bool) (pool : List (SVec sig.length)) :
    List (List BPair) :=
  elim.kernelList pool.length (raiseRowsT T sig pool)

private theorem comboV_widths {k : Nat} (pool : List (SVec k)) (c : List BPair) :
    ((List.zipWith (fun v c => (v, c)) pool c).flatMap (fun p =>
      p.1.val.map (fun q => (q.1, q.2 * p.2)))).all (fun p => p.1.length == k) = true := by
  rw [all_flatMap]
  refine all_of_pointwise _ _ (fun p => ?_)
  rw [all_map]
  exact p.1.property.2

/-- A combination over a pool, the coefficients' scaled sum
collected. -/
def comboV {k : Nat} (pool : List (SVec k)) (c : List BPair) : SVec k :=
  collect k ((List.zipWith (fun v c => (v, c)) pool c).flatMap (fun p =>
    p.1.val.map (fun q => (q.1, q.2 * p.2))))
    (comboV_widths pool c)

/-- The kernel list over a pool at a table, each member at its
primitive representative. -/
def kernelVecs (T : memtable.Table) (sig : List Bool) (pool : List (SVec sig.length)) :
    List (SVec sig.length) :=
  (kernelT T sig pool).map (fun k => prim (comboV pool k))

/-- The Gram-dual solve of a vector over a pool at the weighted
pairing: the bordered Gram's kernel at the primitive
representative, the coefficients with the last coordinate's margin
the clearing (`elim.solveK`, `def:elim`'s bordered descent at one
stated pairing vector), one member at an independent pool, its
last coordinate the crossed pivots' product on the upper side at
the definite Gram. -/
def spanCoeffsAt (T : memtable.Table) (G : elim.Mat) {k : Nat} (pool : List (SVec k))
    (g : SVec k) : List BPair × Pos :=
  let g' := if unitWtRead T then g else applyWt T g
  let b := pool.map (fun u => dotTS T true u g')
  let k0 := elim.solveK G b
  let k := BPair.listPrim (BPair.listContent k0) k0
  (k.take pool.length,
   posOfSucc (BPair.marginN (getAt BPair.unit k pool.length) - 1))

/-- The Gram-dual solve at the pool's own Gram. -/
def spanCoeffsT (T : memtable.Table) {k : Nat} (pool : List (SVec k)) (g : SVec k) :
    List BPair × Pos :=
  spanCoeffsAt T (gramT T pool) pool g

/-- The span membership read at a stated Gram (`lem:lowerspan`'s
residual): the vector at the solve's clearing one value with its
solved combination over the pool. -/
def spanMemberAt (T : memtable.Table) (G : elim.Mat) {k : Nat} (pool : List (SVec k))
    (g : SVec k) : Bool :=
  let c := spanCoeffsAt T G pool g
  oneValueV (scaleV (BPair.ofPos c.2) g) (comboV pool c.1)

/-- The span membership read at the pool's own Gram. -/
def spanMemberT (T : memtable.Table) {k : Nat} (pool : List (SVec k)) (g : SVec k) : Bool :=
  spanMemberAt T (gramT T pool) pool g

/-- The span membership read at a stated Gram at a vector with its
slot count: the read at the pool's count, and refused at a vector
off the pool's power. -/
def spanMemberAtW (T : memtable.Table) (G : elim.Mat) {k : Nat} (pool : List (SVec k))
    (g : WVec) : Bool :=
  if h : g.1 = k then spanMemberAt T G pool (castV h g.2) else false

/-- The span membership read at a vector with its slot count: the
read at the pool's count, and refused at a vector off the pool's
power. -/
def spanMemberW (T : memtable.Table) {k : Nat} (pool : List (SVec k)) (g : WVec) : Bool :=
  if h : g.1 = k then spanMemberT T pool (castV h g.2) else false

/-- The Gram-dual solve at a vector with its slot count: the solve
at the pool's count, and the vacant solve at a vector off the pool's
power. -/
def spanCoeffsW (T : memtable.Table) {k : Nat} (pool : List (SVec k)) (g : WVec) :
    List BPair × Pos :=
  if h : g.1 = k then spanCoeffsT T pool (castV h g.2) else ([], Pos.one)

/-- The projection onto a pool's span at the weighted pairing, the
solved combination with its clearing. -/
def projectT (T : memtable.Table) {k : Nat} (pool : List (SVec k)) (g : SVec k) :
    SVec k × Pos :=
  let c := spanCoeffsT T pool g
  (comboV pool c.1, c.2)

/-- A projection at its reduced representative: the coefficients
and the clearing divided at their shared count, one value at the
homogeneity principle, collected. -/
def reduceV {k : Nat} (p : SVec k × Pos) : SVec k × Pos :=
  let c := BPair.sharedCount (p.1.val.map Prod.snd) p.2
  (collect k (List.zipWith (fun q c => (q.1, c)) p.1.val
    (BPair.listPrim c (p.1.val.map Prod.snd))) (prim_widths p.1 _),
   posOfSucc (posVal p.2 / c - 1))

/-- The groups' scaled projections read the pool's count. -/
private theorem projectGroups_widths (k : Nat) (prs : List (SVec k × Pos)) (oth : List Pos) :
    ((List.range prs.length).flatMap (fun i =>
      let p := getAt (emptyV k, Pos.one) prs i
      p.1.val.map (fun q => (q.1, q.2 * BPair.ofPos (getAt Pos.one oth i))))).all
      (fun p => p.1.length == k) = true := by
  rw [all_flatMap]
  refine all_of_pointwise _ _ (fun i => ?_)
  rw [all_map]
  exact (getAt (emptyV k, Pos.one) prs i).1.property.2

/-- The projection onto the fused span at its groups, the ends'
weight lists' grading orthogonal (`fusedGroupsT`): each occupied
group's Gram-dual solve at its own clearing, the vector the groups'
solves each scaled by the further groups' clearings (read at every
group at once, `ground.othersAll`) at the clearings' product,
reduced. -/
def projectGroupsT (T : memtable.Table) {k : Nat} (groups : List (List (SVec k)))
    (g : SVec k) : SVec k × Pos :=
  let prs := (groups.map (fun pool => projectT T pool g)).filter (fun p =>
    p.1.val.length != 0)
  let c := prs.foldl (fun acc p => acc * p.2) Pos.one
  let oth := ground.othersAll (fun a b : Pos => a * b) Pos.one (prs.map Prod.snd)
  reduceV (collect k ((List.range prs.length).flatMap (fun i =>
    let p := getAt (emptyV k, Pos.one) prs i
    p.1.val.map (fun q => (q.1, q.2 * BPair.ofPos (getAt Pos.one oth i)))))
    (projectGroups_widths k prs oth), c)

/-- The seed's one monomial reads the slot count. -/
private theorem pairTensor_seed (n : Nat) :
    [(List.replicate n 0, BPair.ofNat 1)].all (fun p => p.1.length == n) = true := by
  show (decide ((List.replicate n 0).length = n) && true) = true
  rw [decide_eq_true (length_replicate 0 n)]
  rfl

private theorem pairTensor_widths (c : memtable.SMap) (n : Nat) :
    ∀ (pairs : List (Nat × Nat)) (acc : List (List Nat × BPair)),
      acc.all (fun p => p.1.length == n) = true →
      (pairs.foldl (fun acc ij =>
        acc.flatMap (fun p => c.map (fun e =>
          ((p.1.set ij.1 e.1).set ij.2 e.2.1, (p.2 * e.2.2).norm)))) acc).all
        (fun p => p.1.length == n) = true
  | [], _, h => h
  | ij :: t, acc, h => by
    show (t.foldl _ (acc.flatMap (fun p => c.map (fun e =>
      ((p.1.set ij.1 e.1).set ij.2 e.2.1, (p.2 * e.2.2).norm))))).all _ = true
    refine pairTensor_widths c n t _ ?_
    rw [all_flatMap]
    refine all_of_mem_intro _ _ (fun p hp => ?_)
    rw [all_map]
    refine all_of_pointwise _ _ (fun e => ?_)
    exact decide_eq_true (by
      rw [length_set, length_set]
      exact of_decide_eq_true (all_of_mem _ _ h p hp))

/-- The paired tensor of a stated matrix at stated slot pairs over
a power's slots: per pair `(i, j)` the matrix's entries at the two
slots, the product over the pairs, one monomial per entry
assignment, collected. -/
def pairTensor (c : memtable.SMap) (pairs : List (Nat × Nat)) (n : Nat) : SVec n :=
  collect n (pairs.foldl (fun acc ij =>
    acc.flatMap (fun p => c.map (fun e =>
      ((p.1.set ij.1 e.1).set ij.2 e.2.1, (p.2 * e.2.2).norm))))
    [(List.replicate n 0, BPair.ofNat 1)])
    (pairTensor_widths c n pairs _ (pairTensor_seed n))

/-- The through pairing at a table of two ends at opposite
orientations over stated slot pairs: the weight's cleared partner
per pair, `Σ wtInv_{kk'} e_k ⊗ e_{k'}`, cleared at the weight's
clearing to the pairs' count (`con:slotpower`'s through pairing at
the table's keys, the coevaluation's tensor before the
projection). -/
def throughT (T : memtable.Table) (pairs : List (Nat × Nat)) (n : Nat) : SVec n × Pos :=
  (pairTensor T.wtInv pairs n, posOfSucc (T.wtDet ^ pairs.length - 1))

/-- The through pairing at a table of two ends of one orientation
over stated slot pairs: the dual pair per pair, cleared at its
clearing to the pairs' count (`con:memtable`), vacant at a table
without one. -/
def dualThroughT (T : memtable.Table) (pairs : List (Nat × Nat)) (n : Nat) :
    Option (SVec n × Pos) :=
  T.dual.map (fun d => (pairTensor d.1 pairs n, posOfSucc (posVal d.2 ^ pairs.length - 1)))

/-! The letters' own devices. -/

/-- The dual wedge at a complement length: the wedge on the last
letters, each arrangement on its permutation's side. -/
def dualWedge (d m : Nat) : HVec :=
  blockcount.wedgeC ((List.range d).map (fun i => if d - m ≤ i then 1 else 0))

/-- A label's top at its word pair: the top columns' wedges on the
undaggered slots tensored with the bottom columns' dual wedges on
the daggered. -/
def blockTop (d : Nat) (s : Shape) : HVec :=
  (botCols d s).foldl (fun acc l => tensorH acc (dualWedge d (d - l)))
    ((topCols d s).foldl (fun acc l => tensorH acc (wedge d l))
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩)

/-- A label's block at its word pair, the lowerings' span at its
top in the word pair's power at the letters' table, vacant at a
top off that power. -/
def blockSpanAt (d : Nat) (s : Shape) : List (SVec (labelSig d s).length) :=
  if h : sumNat (blockTop d s).content = (labelSig d s).length then
    blockSpanT (memtable.lettersT d) (labelSig d s) (castV h (ofH (blockTop d s)))
  else []

/-- A label's block's weight grades at its word pair at the letters'
table (`blockGroupsT`), vacant at a top off the word pair's
power. -/
def blockGroupsAt (d : Nat) (s : Shape) :
    List (elim.GroupS (SVec (labelSig d s).length)) :=
  if h : sumNat (blockTop d s).content = (labelSig d s).length then
    blockGroupsT (memtable.lettersT d) (labelSig d s) (castV h (ofH (blockTop d s)))
  else []

/-- A label's block at the letters' table is the closure at the
fresh walk from the top's own join at the top in the word pair's
power, the letters' weight symmetric (`memtable.lettersT_symm`). -/
theorem blockSpanAt_eq (d : Nat) (s : Shape)
    (h : sumNat (blockTop d s).content = (labelSig d s).length) :
    blockSpanAt d s
      = closeT (memtable.lettersT d) (labelSig d s)
          ((labelSig d s).length * (memtable.lettersT d).keys + 1)
          (tryAddT (memtable.lettersT d) (labelSig d s) [] (castV h (ofH (blockTop d s))))
          [castV h (ofH (blockTop d s))] := by
  unfold blockSpanAt
  rw [dif_pos h]
  exact blockSpanT_eq _ _ _ (memtable.lettersT_symm d)

/-- An end's slot count is its label's. -/
theorem length_endSig (d : Nat) (e : Shape × Bool) :
    (endSig d e).length = (labelSig d e.1).length := by
  show (if e.2 then wordSig (wordPair d e.1)
    else (wordSig (wordPair d e.1)).map not).length = (wordSig (wordPair d e.1)).length
  cases e.2 with
  | true => rfl
  | false => exact length_map _ _

/-- The letters' end blocks at a vertex: per end its signature with
its label's block. -/
def endBlocks (d : Nat) (es : List (Shape × Bool)) : List EndBlock :=
  es.map (fun e => ⟨endSig d e, (labelSig d e.1).length, length_endSig d e, blockSpanAt d e.1⟩)

/-- Two ends' joined signature reads the labels' slot counts'
sum. -/
theorem twoEnds_len (d : Nat) (e1 e2 : Shape × Bool) :
    (labelSig d e1.1).length + (labelSig d e2.1).length
      = (fusedSig (endBlocks d [e1, e2])).length := by
  show _ = (endSig d e1 ++ (endSig d e2 ++ [])).length
  rw [length_append, length_append, length_endSig, length_endSig]
  rfl

private theorem wiringG_widths (d : Nat) (sig : List Bool) (σ : List Nat)
    (U D : List Nat) :
    ((allMon d U.length).map (fun ls =>
      ((List.range U.length).foldl (fun m r =>
        (m.set (getAt 0 U r) (getAt 0 ls r)).set (getAt 0 D (getAt 0 σ r))
          (getAt 0 ls r)) (List.replicate sig.length 0), BPair.ofNat 1))).all
      (fun p => p.1.length == sig.length) = true := by
  rw [all_map]
  refine all_of_pointwise _ _ (fun ls => ?_)
  exact decide_eq_true (by
    rw [foldl_length_inv _ (fun m r => by rw [length_set, length_set]),
      length_replicate])

/-- A wiring's tensor at a signature: one letter per row end, read
again at the column end it pairs, one monomial per letter
assignment. -/
def wiringG (d : Nat) (sig : List Bool) (σ : List Nat) : SVec sig.length :=
  let U := upSlots sig
  let D := downSlots sig
  collect sig.length ((allMon d U.length).map (fun ls =>
    ((List.range U.length).foldl (fun m r =>
      (m.set (getAt 0 U r) (getAt 0 ls r)).set (getAt 0 D (getAt 0 σ r))
        (getAt 0 ls r)) (List.replicate sig.length 0), BPair.ofNat 1)))
    (wiringG_widths d sig σ U D)

/-- A column layout at stated columns, the top word's against the
bottom's, each column at its key and length: per column its key
with its slots in the vertex, the top columns' slots at their
lengths then the bottom columns' at the complement lengths, from a
stated offset. -/
def layoutOf (d : Nat) (c : List (Nat × Nat) × List (Nat × Nat)) (off : Nat) :
    List (Nat × List Nat) :=
  (c.1.foldl (fun acc l =>
      (acc.1 ++ [(l.1, (List.range l.2).map (fun i => acc.2 + i))], acc.2 + l.2))
    (([] : List (Nat × List Nat)), off)
  |> fun t => c.2.foldl (fun acc l =>
      (acc.1 ++ [(l.1, (List.range (d - l.2)).map (fun i => acc.2 + i))],
       acc.2 + (d - l.2)))
    t).1

/-- A label's columns at the letters, each at its length for its
key: the top columns against the bottom columns. -/
def labelCols (d : Nat) (s : Shape) : List (Nat × Nat) × List (Nat × Nat) :=
  ((topCols d s).map (fun l => (l, l)), (botCols d s).map (fun l => (l, l)))

/-- An end's column layout, its label's columns at the offset. -/
def colLayout (d : Nat) (e : Shape) (off : Nat) : List (Nat × List Nat) :=
  layoutOf d (labelCols d e) off

/-- The column match of two layouts at a stated key dual: per
column of the first the partner in the second, at the dual key
where the two ends' traversals exchange and at the key itself
where they agree, the first unused match consumed, and the tie
flag at an exchanged match of a self-dual key; at the letters the
key a column's length and its dual the complement length. -/
def colMatch (dualKey : Nat → Nat) (rev : Bool) :
    List (Nat × List Nat) → List (Nat × List Nat) →
    List (List Nat × List Nat × Bool)
  | [], _ => []
  | (l, A) :: t, R =>
    let want := if rev then dualKey l else l
    match R.foldl
        (fun (acc : Option (Nat × List Nat) × List (Nat × List Nat)) c =>
          match acc.1 with
          | some _ => (acc.1, acc.2 ++ [c])
          | none =>
            if c.1 == want then (some c, acc.2) else (none, acc.2 ++ [c]))
        (none, []) with
    | (some c, rest) => (A, c.2, rev && (dualKey l == l)) :: colMatch dualKey rev t rest
    | (none, _) => []

/-- The star's family at a stated arrangement of letters
(`con:slotpower`'s star): every arrangement of the letters off it,
the withdrawn content's words (`places.withdrawn`), each at the
swap grading's side of the concatenated arrangement, vacant at a
letter repeated or beyond the count (`starFam_perms` its read at
the permutations opening at the arrangement). -/
def starFam (d : Nat) (I : List Nat) : List (List Nat × BPair) :=
  if wordOccupied I (List.replicate d 1) then
    (monomialsAt (withdrawn I (List.replicate d 1))).map (fun q =>
      (q, if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1))
  else []

/-- The star's family is the permutations opening at the
arrangement, each at its tail and its own side
(`places.monomialsAt_prefix` at the unit content). -/
theorem starFam_perms (d : Nat) (I : List Nat) :
    starFam d I = (perms d).filterMap (fun ls =>
      if ls.take I.length == I then
        some (ls.drop I.length,
          if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1)
      else none) := by
  rw [ground.filterMap_ite (fun ls : List Nat => ls.take I.length == I)
    (fun ls => (ls.drop I.length,
      if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1))]
  show starFam d I
    = ((monomialsAt (List.replicate d 1)).filter
        (fun ls => ls.take I.length == I)).map _
  rw [monomialsAt_prefix I (List.replicate d 1)]
  show (if wordOccupied I (List.replicate d 1) then
      (monomialsAt (withdrawn I (List.replicate d 1))).map (fun q =>
        (q, if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1))
    else []) = _
  cases hw : wordOccupied I (List.replicate d 1) with
  | true =>
    rw [if_pos rfl, if_pos rfl, ground.map_map]
    refine ground.map_congr_all _ _ (fun q => ?_) _
    show (q, if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1)
      = ((I ++ q).drop I.length,
        if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1)
    rw [ground.drop_append_self]
  | false =>
    rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
      if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
    rfl

private theorem starAt_widths (d : Nat) (slots : List Nat) {k : Nat} (v : SVec k) :
    (v.val.flatMap (fun p =>
      (starFam d (slots.map (fun s => getAt 0 p.1 s))).map (fun q =>
        ((List.zipWith (fun s l => (s, l)) slots q.1).foldl
          (fun m sl => m.set sl.1 sl.2) p.1, p.2 * q.2)))).all
      (fun p => p.1.length == k) = true := by
  rw [all_flatMap]
  refine all_of_mem_intro _ _ (fun p hp => ?_)
  rw [all_map]
  refine all_of_pointwise _ _ (fun q => ?_)
  exact decide_eq_true (by
    show (List.foldl (fun m sl => m.set sl.1 sl.2) p.1
      (List.zipWith (fun s l => (s, l)) slots q.1)).length = k
    rw [foldl_length_inv (fun m (sl : Nat × Nat) => m.set sl.1 sl.2)
      (fun m sl => length_set _ m sl.1)]
    exact width_of_mem v p hp)

/-- The star at a tie column's slots on a vector: every occupied
monomial's letters at the slots read to every arrangement of the
complementary set at the swap grading's side, the coefficient
scaled, the clearing at the column length's factorial the reader's
own (`con:slotpower`'s star as the tie column's map between its
two actions). -/
def starAt (d : Nat) (slots : List Nat) {k : Nat} (v : SVec k) : SVec k :=
  collect k (v.val.flatMap (fun p =>
    (starFam d (slots.map (fun s => getAt 0 p.1 s))).map (fun q =>
      ((List.zipWith (fun s l => (s, l)) slots q.1).foldl
        (fun m sl => m.set sl.1 sl.2) p.1, p.2 * q.2))))
    (starAt_widths d slots v)

/-- The slot map at a moved end (`con:fiber`'s two-end vertex and
`thm:pairpencil`'s terms' transport) at a stated key dual: the
moved end's columns
matched to the source end's, a column against the column of its
own key at a traversal kept and against the dual key at a
traversal reversed (`colMatch`), each moved slot at the matched
source slot in order, with the tie columns' slot groups at a
reversed traversal, the star's at the letters. -/
def transportSlots (dualKey : Nat → Nat) (rev : Bool)
    (src tgt : List (Nat × List Nat)) : List Nat × List (List Nat) :=
  let pairs := colMatch dualKey rev tgt src
  (pairs.flatMap (fun p => p.2.1),
   (pairs.filter (fun p => p.2.2)).map (fun p => p.1))

/-- A vector at the sum's unit under every simple raising at a
signature, `con:memtable`'s top read (`lem:tops`; `lem:lowerspan`'s
adjacent stack). -/
def raisedUnit (T : memtable.Table) (sig : List Bool) (v : SVec sig.length) : Bool :=
  (List.range T.rank).all (fun i => (raiseT T sig i v).val.length == 0)

/-- A tensor with a vacant first factor is vacant. -/
theorem tensorV_nil_left {k l : Nat} (u : SVec k) (v : SVec l)
    (hu : u.val = []) : (tensorV u v).val = [] := by
  change collectBy lexLt (fun a b => a == b)
    (u.val.flatMap (fun p => v.val.map (fun q => (p.1 ++ q.1, (p.2 * q.2).norm)))) = []
  rw [hu]
  rfl

/-- A tensor with a vacant second factor is vacant. -/
theorem tensorV_nil_right {k l : Nat} (u : SVec k) (v : SVec l)
    (hv : v.val = []) : (tensorV u v).val = [] := by
  change collectBy lexLt (fun a b => a == b)
    (u.val.flatMap (fun p => v.val.map (fun q => (p.1 ++ q.1, (p.2 * q.2).norm)))) = []
  rw [hv]
  change collectBy lexLt (fun a b => a == b)
    (u.val.flatMap (fun _ => ([] : List (List Nat × BPair)))) = []
  rw [flatMap_nil _ u.val (fun _ _ => rfl)]
  rfl

/-- If a simple raising reads both factors at the sum's unit,
it reads their tensor there at the concatenated signature. -/
theorem raiseT_tensor_nil (T : memtable.Table) (sig tau : List Bool) (i : Nat)
    (u : SVec sig.length) (v : SVec tau.length)
    (hu : (raiseT T sig i u).val = []) (hv : (raiseT T tau i v).val = []) :
    (raiseT T (sig ++ tau) i (castV (length_append sig tau).symm (tensorV u v))).val = [] := by
  have h := congrArg Subtype.val (raiseT_tensorV T sig tau i u v)
  change (raiseT T (sig ++ tau) i
    (castV (length_append sig tau).symm (tensorV u v))).val
    = (addV (tensorV (raiseT T sig i u) v) (tensorV u (raiseT T tau i v))).val at h
  rw [h, addV_read, tensorV_nil_left _ v hu, tensorV_nil_right u _ hv]
  rfl

/-- A tensor of two tops is a top at the concatenated signature. -/
theorem raisedUnit_tensorV (T : memtable.Table) (sig tau : List Bool)
    (u : SVec sig.length) (v : SVec tau.length)
    (hu : raisedUnit T sig u = true) (hv : raisedUnit T tau v = true) :
    raisedUnit T (sig ++ tau) (castV (length_append sig tau).symm (tensorV u v)) = true := by
  apply all_range_intro
  intro i hi
  have hui := of_decide_eq_true (all_range_read T.rank hu i hi)
  have hvi := of_decide_eq_true (all_range_read T.rank hv i hi)
  have he := raiseT_tensor_nil T sig tau i u v
    (nil_of_length_zero _ hui) (nil_of_length_zero _ hvi)
  change decide ((raiseT T (sig ++ tau) i
    (castV (length_append sig tau).symm (tensorV u v))).val.length = 0) = true
  rw [he]
  rfl

/-- The scalar one is a top at every generating table, the slot
fold over its vacant signature. -/
theorem raisedUnit_unitV (T : memtable.Table) : raisedUnit T [] unitV = true := by
  apply all_range_intro
  intro _ _
  rfl

/-- Equal signatures and coefficient displays give equal raising
displays, independently of their width witnesses. -/
theorem raiseT_val_congr (T : memtable.Table) (sig tau : List Bool) (i : Nat)
    (u : SVec sig.length) (v : SVec tau.length) (hs : sig = tau) (hv : u.val = v.val) :
    (raiseT T sig i u).val = (raiseT T tau i v).val := by
  subst hs
  have he : u = v := Subtype.ext hv
  rw [he]

/-- The tensor of two standard powers' tops is a top in their
summed power. -/
theorem raisedUnit_tensor_standard (T : memtable.Table) {k l : Nat}
    (u : SVec k) (v : SVec l)
    (hu : raisedUnit T (List.replicate k false)
      (castV (length_replicate false k).symm u) = true)
    (hv : raisedUnit T (List.replicate l false)
      (castV (length_replicate false l).symm v) = true) :
    raisedUnit T (List.replicate (k + l) false)
      (castV (length_replicate false (k + l)).symm (tensorV u v)) = true := by
  have h := raisedUnit_tensorV T (List.replicate k false) (List.replicate l false)
    (castV (length_replicate false k).symm u) (castV (length_replicate false l).symm v) hu hv
  have hsig : List.replicate k false ++ List.replicate l false
      = List.replicate (k + l) false := (replicate_append false k l).symm
  unfold raisedUnit at h ⊢
  apply all_range_intro
  intro i hi
  have hi' := all_range_read T.rank h i hi
  change decide ((raiseT T (List.replicate (k + l) false) i
    (castV (length_replicate false (k + l)).symm (tensorV u v))).val.length = 0) = true
  have he : (raiseT T (List.replicate (k + l) false) i
      (castV (length_replicate false (k + l)).symm (tensorV u v))).val
      = (raiseT T (List.replicate k false ++ List.replicate l false) i
        (castV (length_append _ _).symm
          (tensorV (castV (length_replicate false k).symm u)
            (castV (length_replicate false l).symm v)))).val := by
    exact raiseT_val_congr T _ _ i _ _ hsig.symm rfl
  rw [he]
  exact hi'


/-- The identification's clearing at a moved end: at a table without
a dual pair the tie groups' factorials, the star's clearing
(`con:slotpower`'s star cleared at the column length's factorial),
and at a table with one the pair's clearing per reversed slot, the
pair against the weight an isometry of the pairing at the clearing
(`con:memtable`'s isometry read, the pairing scaled by the
clearing's square per slot). -/
def identifyClear (T : memtable.Table) (ties : List (List Nat))
    (revs : List (List Nat × Bool)) (cl : Pos) : Pos :=
  match T.dual with
  | none => ties.foldl (fun c sl => c * posOfSucc (factorial sl.length - 1)) cl
  | some (_, nu) => revs.foldl (fun c e => e.1.foldl (fun c _ => c * nu) c) cl

/-- A vector read through the identification at a moved end's
slots: relabeled along the slot map (`relabelV`, the place action),
then at a table without a dual pair the star at every tie group
(`starAt`, the letters' identification of a tie column's block
with its complement's), and at a table with one the dual pair
against the weight at every reversed slot group, `c W` at an
outgoing end and `cᵀ W` at an incoming one (`applyAt`,
`con:memtable`'s identification of the dual block with the dual
label's block), the clearing `identifyClear`'s. -/
def identifyV (d : Nat) (T : memtable.Table) (σ : List Nat) (ties : List (List Nat))
    (revs : List (List Nat × Bool)) {k : Nat} (v : SVec k) : SVec σ.length :=
  let w := relabelV σ v
  match T.dual with
  | none => ties.foldl (fun g sl => starAt d sl g) w
  | some (c, _) =>
    let mOut := memtable.smul c T.wt
    let mIn := memtable.smul (memtable.sT c) T.wt
    revs.foldl (fun g e => applyAt (if e.2 then mOut else mIn) e.1 g) w

/-- A column pair's family: at a wiring one member per letter list,
the letters at the paired slots agreeing, and at the star one
member per arrangement of the letters over the two columns, the
complementary letter sets at the swap grading's side (`starFam`);
each member its slot assignments with its coefficient. -/
private def pairFam (d : Nat) (p : List Nat × List Nat × Bool) :
    List (List (Nat × Nat) × BPair) :=
  if p.2.2 then
    (allMon d p.1.length).flatMap (fun I =>
      (starFam d I).map (fun q =>
        (List.zipWith (fun s l => (s, l)) p.1 I
          ++ List.zipWith (fun s l => (s, l)) p.2.1 q.1, q.2)))
  else
    (allMon d p.1.length).map (fun ls =>
      (List.zipWith (fun s l => (s, l)) p.1 ls
        ++ List.zipWith (fun s l => (s, l)) p.2.1 ls,
       BPair.ofNat 1))

/-- The families' monomials at a stated slot count read the
count. -/
private theorem throughPair_widths (n : Nat) (fam : List (List (Nat × Nat) × BPair)) :
    (fam.map (fun a =>
      (a.1.foldl (fun m sl => m.set sl.1 sl.2) (List.replicate n 0), a.2))).all
      (fun p => p.1.length == n) = true := by
  rw [all_map]
  refine all_of_pointwise _ _ (fun a => ?_)
  exact decide_eq_true (by
    show (List.foldl (fun m sl => m.set sl.1 sl.2) (List.replicate n 0) a.1).length = n
    rw [foldl_length_inv (fun m (sl : Nat × Nat) => m.set sl.1 sl.2)
      (fun m sl => length_set _ m sl.1), length_replicate])

/-- The through pairing of two ends at dual labels at the letters:
each column's slots against its complement column's, a wiring at
an undaggered slot against a daggered one and the star at a tie
column, the tensor the column pairs' families' product cleared at
the tie columns' factorials; vacant off the dual pair. -/
def throughPair (d : Nat) (e1 e2 : Shape × Bool) :
    SVec ((labelSig d e1.1).length + (labelSig d e2.1).length) × Pos :=
  let same := e1.2 == e2.2
  let ok := if same then labels.reduce e2.1 == labels.reduce (labels.dualL e1.1)
    else labels.reduce e2.1 == labels.reduce e1.1
  let n1 := (labelSig d e1.1).length
  let n := n1 + (labelSig d e2.1).length
  let pairs := colMatch (fun l => d - l) same (colLayout d e1.1 0) (colLayout d e2.1 n1)
  if !ok || pairs.length != (cols e1.1).length then (emptyV n, Pos.one)
  else
    let clear := pairs.foldl (fun acc p =>
      if p.2.2 then acc * factorial p.1.length else acc) 1
    let fam := pairs.foldl (fun acc p =>
      acc.flatMap (fun a =>
        (pairFam d p).map (fun b => (a.1 ++ b.1, a.2 * b.2))))
      [(([] : List (Nat × Nat)), BPair.ofNat 1)]
    (collect n (fam.map (fun a =>
      (a.1.foldl (fun m sl => m.set sl.1 sl.2) (List.replicate n 0), a.2)))
      (throughPair_widths n fam),
     posOfSucc (clear - 1))

/-! Coordinate reads on finite monomial lists and their Gram. -/

/-- A coefficient off the vector's occupied keys is the sum's unit. -/
theorem coefAt_off (m : List Nat) {k : Nat} (v : SVec k)
    (hm : ∀ p ∈ v.val, p.1 ≠ m) : (coefAt m v).oneValue BPair.unit := by
  refine BPair.oneValue_trans (coefAt_read m v) ?_
  apply foldB_null
  intro p hp
  change (if p.1 == m then p.2 else BPair.unit).oneValue BPair.unit
  rw [if_neg (fun h => hm p (mem_of_countOf_pos _ _ hp) (listBeqEq h))]
  exact BPair.oneValue_refl _

/-- Equal finite coordinate reads identify vectors whose occupied
monomials belong to the coordinate list. -/
theorem coordsV_injective (ms : List (List Nat)) {k : Nat} (u v : SVec k)
    (hu : ∀ p ∈ u.val, p.1 ∈ ms) (hv : ∀ p ∈ v.val, p.1 ∈ ms)
    (h : poly.oneValue (coordsV ms u) (coordsV ms v)) : u = v := by
  apply eq_of_coefAt
  intro m
  cases hc : countOf m ms with
  | zero =>
    exact BPair.oneValue_trans
      (coefAt_off m u (fun p hp he => by
        have hm := countOf_pos_of_mem (hu p hp)
        rw [he, hc] at hm
        exact Nat.lt_irrefl 0 hm))
      (BPair.oneValue_symm (coefAt_off m v (fun p hp he => by
        have hm := countOf_pos_of_mem (hv p hp)
        rw [he, hc] at hm
        exact Nat.lt_irrefl 0 hm)))
  | succ n =>
    have hm : m ∈ ms := mem_of_countOf_pos m ms (by rw [hc]; exact Nat.succ_pos n)
    obtain ⟨i, hi, he⟩ := getAt_of_mem ([] : List Nat) hm
    have hr := poly.oneValue_getAt i h
    change (getAt BPair.unit (ms.map (fun m => coefAt m u)) i).oneValue
      (getAt BPair.unit (ms.map (fun m => coefAt m v)) i) at hr
    rw [getAt_map [] BPair.unit _ ms i hi, getAt_map [] BPair.unit _ ms i hi, he] at hr
    exact hr

/-- The full monomial carrier covers every occupied key of a
vector using the stated letter keys, at one occurrence each. -/
theorem coordsV_allMon_count (d : Nat) {k : Nat} (v : SVec k) (hv : keysRead d v) :
    ∀ p ∈ v.val, countOf p.1 (allMon d k) = 1 := by
  intro p hp
  exact allMon_count d k p.1 (width_of_mem v p hp) (all_of_mem _ v.val hv p hp)

/-- The unit-weight sparse pairing is the coordinate pairing on
any finite monomial list covering the first vector's keys once. -/
theorem pairT_coordsV (T : memtable.Table) (ms : List (List Nat)) {k : Nat} (u v : SVec k)
    (hu : ∀ p ∈ u.val, countOf p.1 ms = 1) :
    (elim.dotP (coordsV ms u) (coordsV ms v)).oneValue (pairT T true u v) := by
  unfold coordsV
  rw [elim.dotP_map_pair]
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun m => coefAt m v * keyFoldB (fun a b : List Nat => a == b) m u.val) ms (fun m _ => ?_)) ?_
  · rw [BPair.mul_comm]
    exact BPair.mul_congr (BPair.oneValue_refl _) (coefAt_read m u)
  · refine BPair.oneValue_trans (by apply (foldB_keyFold_linear
      (fun a b : List Nat => a == b) (fun _ _ h => listBeqEq h) listEqBeq
      ms (fun m => coefAt m v) u.val hu)) ?_
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun p : List Nat × BPair => p.2 * coefAt p.1 v) u.val
      (fun p _ => BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotT_read T true u v)) ?_
    exact BPair.oneValue_trans (BPair.oneValue_symm (dotTS_read T true u v))
      (BPair.oneValue_symm (BPair.norm_oneValue _))

/-- The coefficient read preserves a sum at every monomial. -/
theorem coefAt_addV (m : List Nat) {k : Nat} (u v : SVec k) :
    (coefAt m (addV u v)).oneValue (coefAt m u + coefAt m v) := by
  refine BPair.oneValue_trans (coefAt_fold m _) ?_
  refine BPair.oneValue_trans (by apply (fold_addV u v
    (fun n => if n == m then BPair.ofNat 1 else BPair.unit))) ?_
  exact BPair.add_congr (BPair.oneValue_symm (coefAt_fold m u))
    (BPair.oneValue_symm (coefAt_fold m v))

/-- The coefficient read preserves scalar multiplication. -/
theorem coefAt_scaleV (m : List Nat) {k : Nat} (v : SVec k) (c : BPair) :
    (coefAt m (scaleV c v)).oneValue (c * coefAt m v) := by
  refine BPair.oneValue_trans (coefAt_fold m _) ?_
  refine BPair.oneValue_trans (by apply (fold_scaleV v c
    (fun n => if n == m then BPair.ofNat 1 else BPair.unit))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl c) (BPair.oneValue_symm (coefAt_fold m v))

/-- Finite coordinates read vector addition entry by entry. -/
theorem coordsV_addV {k : Nat} (u v : SVec k) : ∀ ms : List (List Nat),
    poly.oneValue (coordsV ms (addV u v)) (elim.vecAdd (coordsV ms u) (coordsV ms v))
  | [] => trivial
  | m :: ms => ⟨coefAt_addV m u v, coordsV_addV u v ms⟩

/-- Finite coordinates read scalar multiplication entry by entry. -/
theorem coordsV_scaleV {k : Nat} (v : SVec k) (c : BPair) : ∀ ms : List (List Nat),
    poly.oneValue (coordsV ms (scaleV c v)) (elim.vecScale c (coordsV ms v))
  | [] => trivial
  | m :: ms => ⟨coefAt_scaleV m v c, coordsV_scaleV v c ms⟩

/-- The sparse Gram join equals the coordinate Gram join on a
finite monomial carrier containing every joined member's keys once. -/
theorem joinIndep_coordsV (T : memtable.Table) (ms : List (List Nat)) {k : Nat}
    (L : List (SVec k)) (v : SVec k)
    (hc : ∀ w ∈ L ++ [v], ∀ p ∈ w.val, countOf p.1 ms = 1) :
    elim.joinIndep (pairT T true) L v
      = elim.joinIndep elim.dotP (L.map (coordsV ms)) (coordsV ms v) :=
  elim.joinIndep_map (pairT T true) elim.dotP (coordsV ms) L v
    (fun a ha b _ => BPair.oneValue_symm (pairT_coordsV T ms a b (hc a ha)))

private theorem joinIndep_allMon (T : memtable.Table) (d : Nat) {k : Nat}
    (L : List (SVec k)) (v : SVec k) (hL : ∀ w ∈ L, keysRead d w) (hv : keysRead d v) :
    elim.joinIndep (pairT T true) L v
      = elim.joinIndep elim.dotP (L.map (coordsV (allMon d k))) (coordsV (allMon d k) v) :=
  joinIndep_coordsV T (allMon d k) L v (fun w hw => by
    cases mem_append_of L [v] hw with
    | inl h => exact coordsV_allMon_count d w (hL w h)
    | inr h =>
      cases h with
      | head => exact coordsV_allMon_count d v hv
      | tail _ h => nomatch h)

/-- Every occupied weight group is independent in its finite
monomial coordinates. -/
def indepGroupsT (T : memtable.Table) (sig : List Bool) (ms : List (List Nat))
    (pool : List (SVec sig.length)) : Prop :=
  ∀ w ∈ pool.map (weightV T sig), elim.indepRows ms.length
    ((pool.filter (fun v => weightV T sig v == w)).map (coordsV ms))

instance instSlotpower5 (T : memtable.Table) (sig : List Bool) (ms : List (List Nat))
    (pool : List (SVec sig.length)) : Decidable (indepGroupsT T sig ms pool) :=
  inferInstanceAs (Decidable (∀ w ∈ pool.map (weightV T sig), elim.indepRows ms.length
    ((pool.filter (fun v => weightV T sig v == w)).map (coordsV ms))))

private theorem indepGroupsT_at (T : memtable.Table) (sig : List Bool)
    (ms : List (List Nat)) (pool : List (SVec sig.length)) (h : indepGroupsT T sig ms pool)
    (w : List BPair) : elim.indepRows ms.length
      ((pool.filter (fun v => weightV T sig v == w)).map (coordsV ms)) :=
  elim.indepGroups_at (fun a b => a == b) (fun _ _ he => listBeqEq he)
    (weightV T sig) (coordsV ms) (fun _ => ms.length) pool h w

private theorem coordsV_rows (ms : List (List Nat)) {k : Nat} (L : List (SVec k)) :
    elim.rowsLen ms.length (L.map (coordsV ms)) :=
  elim.rowsLen_map (coordsV ms) ms.length L (fun _ _ => length_map _ ms)

/-- The membership join preserves independence in every weight
group at the unit pairing and the full monomial carrier. -/
theorem tryAddT_indep (T : memtable.Table) (sig : List Bool) (d : Nat)
    (pool : List (SVec sig.length)) (v : SVec sig.length)
    (hw : unitWtRead T = true) (hp : ∀ w ∈ pool, keysRead d w) (hv : keysRead d v)
    (hind : indepGroupsT T sig (allMon d sig.length) pool) :
    indepGroupsT T sig (allMon d sig.length) (tryAddT T sig pool v) := by
  let ms := allMon d sig.length
  let group := pool.filter (fun w => weightV T sig w == weightV T sig v)
  have hmap := joinIndep_allMon T d group v
    (fun w hw' => hp w (mem_filter_of _ pool w hw').1) hv
  unfold tryAddT
  rw [hw]
  change indepGroupsT T sig ms (if elim.joinIndep (pairT T true) group v then pool ++ [v] else pool)
  by_cases hj : elim.joinIndep (pairT T true) group v = true
  · rw [if_pos hj]
    have hcoords : elim.joinIndep elim.dotP (group.map (coordsV ms)) (coordsV ms v) = true := by
      rw [← hmap]; exact hj
    have hext := (elim.joinIndep_indep ms.length (group.map (coordsV ms)) (coordsV ms v)
      (coordsV_rows ms group) (length_map _ ms)).1 hcoords
    intro w _
    exact elim.indepGroups_append (fun a b => a == b) (fun _ _ h => listBeqEq h)
      listEqBeq (weightV T sig) (coordsV ms) (fun _ => ms.length) pool v
      (indepGroupsT_at T sig ms pool hind) hext w
  · rw [if_neg hj]
    exact hind

/-- Every tested vector lies in the joined pool's coordinate
span: a joined member is listed, and a refused one lies in its
independent weight group's span. -/
theorem tryAddT_span (T : memtable.Table) (sig : List Bool) (d : Nat)
    (pool : List (SVec sig.length)) (v : SVec sig.length)
    (hw : unitWtRead T = true) (hp : ∀ w ∈ pool, keysRead d w) (hv : keysRead d v)
    (hind : indepGroupsT T sig (allMon d sig.length) pool) :
    elim.spanRel (allMon d sig.length).length
      ((tryAddT T sig pool v).map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) v) := by
  let ms := allMon d sig.length
  let group := pool.filter (fun w => weightV T sig w == weightV T sig v)
  have hmap := joinIndep_allMon T d group v
    (fun w hw' => hp w (mem_filter_of _ pool w hw').1) hv
  unfold tryAddT
  rw [hw]
  change elim.spanRel ms.length
    ((if elim.joinIndep (pairT T true) group v then pool ++ [v] else pool).map (coordsV ms))
    (coordsV ms v)
  cases hj : elim.joinIndep (pairT T true) group v with
  | true =>
    rw [if_pos rfl]
    exact elim.spanRel_of_mem ms.length _ _ (coordsV_rows ms _)
      (mem_map_to (coordsV ms) (mem_append_right pool (List.Mem.head [])))
  | false =>
    rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
    have hcoords : elim.joinIndep elim.dotP (group.map (coordsV ms)) (coordsV ms v) = false := by
      rw [← hmap]; exact hj
    have hsp := (elim.joinIndep_span ms.length (group.map (coordsV ms)) (coordsV ms v)
      (length_map _ ms) (indepGroupsT_at T sig ms pool hind _)).1 hcoords
    apply elim.spanRel_sub ms.length (group.map (coordsV ms)) (pool.map (coordsV ms))
      (coordsV ms v) (coordsV_rows ms pool) _ hsp
    intro r hr
    obtain ⟨w, hw', he⟩ := mem_map_of (coordsV ms) group r hr
    rw [← he]
    exact mem_map_to (coordsV ms) (mem_filter_of _ pool w hw').1

/-- G2's actual standard-slot block has independent weight groups,
and every simple lowering of a listed member belongs to its span
on the full finite monomial carrier. -/
theorem blockSpanT_reads_G2 (sig : List Bool) (top : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top) :
    indepGroupsT memtable.genG2 sig (allMon memtable.genG2.keys sig.length)
      (blockSpanT memtable.genG2 sig top) ∧
      ∀ v ∈ blockSpanT memtable.genG2 sig top, ∀ i, i < memtable.genG2.rank →
        elim.spanRel (allMon memtable.genG2.keys sig.length).length
          ((blockSpanT memtable.genG2 sig top).map
            (coordsV (allMon memtable.genG2.keys sig.length)))
          (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i v)) := by
  let T := memtable.genG2
  let ms := allMon T.keys sig.length
  let P := fun v : SVec sig.length => keysRead T.keys v
  let I := fun L : List (SVec sig.length) => (∀ v ∈ L, P v) ∧ indepGroupsT T sig ms L
  let S := fun L : List (SVec sig.length) => fun v : SVec sig.length =>
    elim.spanRel ms.length (L.map (coordsV ms)) (coordsV ms v)
  have hw : unitWtRead T = true := by decide +kernel
  have hjoin : ∀ L v, I L → P v → I (tryAddT T sig L v) ∧ S (tryAddT T sig L v) v := by
    intro L v hL hv
    refine ⟨⟨tryAddT_all T sig P L v hL.1 hv, ?_⟩, ?_⟩
    · exact tryAddT_indep T sig T.keys L v hw hL.1 hv hL.2
    · exact tryAddT_span T sig T.keys L v hw hL.1 hv hL.2
  have hmono : ∀ L ext v, I L → I (L ++ ext) → P v → S L v → S (L ++ ext) v := by
    intro L ext v _ _ _ hs
    change elim.spanRel ms.length ((L ++ ext).map (coordsV ms)) (coordsV ms v)
    rw [map_append]
    exact elim.spanRel_mono ms.length _ _ _ (coordsV_rows ms L) (coordsV_rows ms ext) hs
  have hstep : ∀ v, P v → ∀ w ∈ lowerings T sig v,
      P w ∧ heightV memtable.keyHeightsG2 w < heightV memtable.keyHeightsG2 v := by
    intro v hv w hmem
    obtain ⟨i, hi, he, ho⟩ := lowerings_mem T sig v w hmem
    rw [← he] at ho ⊢
    exact ⟨keysRead_lowerT T sig i (memtable.genG2_actionKeys i hi).1
        (memtable.genG2_actionKeys i hi).2 v hv,
      heightV_lowerT T sig i memtable.keyHeightsG2 v hsig
        (all_range_read _ memtable.genG2_height.2.2 i hi) ho⟩
  have hempty : I [] := ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  have hseed := (hjoin [] top hempty ht).1
  have hfresh : ∀ v ∈ [top], P v ∧ heightV memtable.keyHeightsG2 v < sig.length * T.keys + 1 := by
    intro v hv
    cases hv with
    | head =>
      refine ⟨ht, ?_⟩
      exact Nat.lt_of_le_of_lt
        (Nat.le_trans (heightV_bound memtable.keyHeightsG2 6 top memtable.genG2_height.2.1)
          (Nat.mul_le_mul_left sig.length (show 6 ≤ T.keys from by decide +kernel)))
        (Nat.lt_succ_self _)
    | tail _ h => nomatch h
  have hprocessed : ∀ v ∈ tryAddT T sig [] top,
      v ∈ [top] ∨ ∀ w ∈ lowerings T sig v, S (tryAddT T sig [] top) w := by
    intro v hv
    cases tryAddT_split T sig [] top with
    | inl he => rw [he] at hv; nomatch hv
    | inr he => rw [he] at hv; exact Or.inl hv
  have hdone := closeBy_sem (lowerings T sig) (tryAddT T sig) P I S
    (heightV memtable.keyHeightsG2) (tryAddT_split T sig) hjoin hmono
    (fun _ h => h.1) hstep (sig.length * T.keys + 1) (tryAddT T sig [] top) [top]
    hseed hfresh hprocessed
  have he : blockSpanT T sig top
      = closeT T sig (sig.length * T.keys + 1) (tryAddT T sig [] top) [top] :=
    blockSpanT_eq T sig top memtable.genG2_symmWt
  change I (closeT T sig (sig.length * T.keys + 1) (tryAddT T sig [] top) [top]) ∧
    ∀ v ∈ closeT T sig (sig.length * T.keys + 1) (tryAddT T sig [] top) [top],
      ∀ w ∈ lowerings T sig v,
        S (closeT T sig (sig.length * T.keys + 1) (tryAddT T sig [] top) [top]) w at hdone
  rw [← he] at hdone
  refine ⟨hdone.1.2, ?_⟩
  intro v hv i hi
  by_cases ho : (lowerT T sig i v).val = []
  · apply elim.spanRel_null _ _ _ _ (coordsV_rows ms _) (length_map _ ms)
    apply poly.unitTail_map
    intro m _
    unfold coefAt
    rw [ho]
    exact BPair.oneValue_refl _
  · apply hdone.2 v hv
    apply mem_filter_to _ (mem_map_to (fun j => lowerT T sig j v) (memRange hi))
    change ((lowerT T sig i v).val.length != 0) = true
    have hn : (lowerT T sig i v).val.length ≠ 0 := fun hz => ho (nil_of_length_zero _ hz)
    cases he : (lowerT T sig i v).val.length with
    | zero => exact False.elim (hn he)
    | succ _ => rfl

/-- The scalar fold of a sparse combination is the fold over its
matched vectors and coefficients. -/
theorem fold_comboV {k : Nat} (pool : List (SVec k)) (cs : List BPair)
    (f : List Nat → BPair) :
    (bsum (fun p => p.2 * f p.1) (comboV pool cs).val).oneValue
      (bsum (fun p => p.2 * bsum (fun q => q.2 * f q.1) p.1.val)
        (List.zipWith (fun v c => (v, c)) pool cs)) := by
  refine BPair.oneValue_trans (by apply (foldB_collectBy lexLt (fun a b => a == b)
    (fun _ _ h => listBeqEq h) f _)) ?_
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ _) ?_
  refine foldB_congr_members _ _ _ (fun p _ => ?_)
  rw [famFold_map]
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun q : List Nat × BPair => p.2 * (q.2 * f q.1)) p.1.val (fun q _ => ?_))
    (by apply (foldB_mul_left p.2 _ p.1.val))
  rw [BPair.mul_comm q.2 p.2, BPair.mul_assoc]
  exact BPair.oneValue_refl _

/-- A combination over a vacant pool is the vacant vector. -/
theorem comboV_nil {k : Nat} (cs : List BPair) : comboV ([] : List (SVec k)) cs = emptyV k :=
  Subtype.ext rfl

/-- A combination at the vacant coefficient list is vacant. -/
theorem comboV_nil_coeffs {k : Nat} (pool : List (SVec k)) : comboV pool [] = emptyV k := by
  cases pool with
  | nil => exact Subtype.ext rfl
  | cons _ _ => exact Subtype.ext rfl

/-- A combination splits at its first matched vector and scalar. -/
theorem comboV_cons {k : Nat} (v : SVec k) (pool : List (SVec k)) (c : BPair) (cs : List BPair) :
    comboV (v :: pool) (c :: cs) = addV (scaleV c v) (comboV pool cs) := by
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (comboV (v :: pool) (c :: cs)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (addV (scaleV c v) (comboV pool cs)).val) := by
    refine BPair.oneValue_trans (by apply (fold_comboV (v :: pool) (c :: cs) f)) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (by apply (fold_addV _ _ f)))
    change (c * bsum (fun p => p.2 * f p.1) v.val
      + bsum (fun p => p.2 * bsum (fun q => q.2 * f q.1) p.1.val)
        (List.zipWith (fun v c => (v, c)) pool cs)).oneValue _
    exact BPair.add_congr (BPair.oneValue_symm (by apply (fold_scaleV v c f)))
      (BPair.oneValue_symm (by apply (fold_comboV pool cs f)))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- Combinations preserve the finite key carrier of their pool. -/
theorem keysRead_comboV (d : Nat) {k : Nat} : ∀ (pool : List (SVec k)) (cs : List BPair),
    (∀ v ∈ pool, keysRead d v) → keysRead d (comboV pool cs)
  | [], cs, _ => by rw [comboV_nil]; rfl
  | _ :: _, [], _ => by rw [comboV_nil_coeffs]; rfl
  | v :: pool, c :: cs, h => by
    rw [comboV_cons]
    exact keysRead_addV d _ _ (keysRead_scaleV d c v (h v (List.Mem.head pool)))
      (keysRead_comboV d pool cs (fun w hw => h w (List.Mem.tail v hw)))

private theorem coordsV_empty (k : Nat) (ms : List (List Nat)) :
    coordsV ms (emptyV k) = List.replicate ms.length BPair.unit :=
  map_const BPair.unit ms

/-- A sparse combination has the elimination's coordinate
combination on every stated monomial list. -/
theorem coordsV_comboV (ms : List (List Nat)) {k : Nat} : ∀ (pool : List (SVec k)) (cs : List BPair),
    poly.oneValue (coordsV ms (comboV pool cs))
      (elim.combo ms.length cs (pool.map (coordsV ms)))
  | [], cs => by rw [comboV_nil, coordsV_empty]; cases cs <;> exact poly.oneValue_refl _
  | _ :: _, [] => by rw [comboV_nil_coeffs, coordsV_empty]; exact poly.oneValue_refl _
  | v :: pool, c :: cs => by
    rw [comboV_cons]
    refine poly.oneValue_trans (coordsV_addV (scaleV c v) (comboV pool cs) ms) ?_
    change poly.oneValue
      (elim.vecAdd (coordsV ms (scaleV c v)) (coordsV ms (comboV pool cs)))
      (elim.vecAdd (elim.vecScale c (coordsV ms v)) (elim.combo ms.length cs (pool.map (coordsV ms))))
    apply elim.vecAdd_congr2
    · unfold coordsV
      rw [length_map, elim.length_vecScale, length_map]
    · change (ms.map (fun m => coefAt m (comboV pool cs))).length = _
      rw [length_map, elim.length_combo _ _ _ (coordsV_rows ms pool)]
    · exact coordsV_scaleV v c ms
    · exact coordsV_comboV ms pool cs

/-- A sparse action maps the vacant vector to itself. -/
theorem actT_emptyV (M : memtable.SMap) (neg : Bool) (s k : Nat) :
    actT M neg s (emptyV k) = emptyV k := Subtype.ext rfl

/-- Every simple raising maps the vacant vector to itself. -/
theorem raiseT_emptyV (T : memtable.Table) (sig : List Bool) (i : Nat) :
    raiseT T sig i (emptyV sig.length) = emptyV sig.length := by
  apply Subtype.ext
  change collectBy lexLt (fun a b => a == b) ((List.range sig.length).flatMap (fun s =>
    if getAt false sig s then (actT (getAt [] T.lowers i) true s (emptyV sig.length)).val
    else (actT (getAt [] T.raises i) false s (emptyV sig.length)).val)) = []
  rw [flatMap_nil _ _ (fun s _ => by
    by_cases hs : getAt false sig s = true
    · rw [if_pos hs, actT_emptyV]; rfl
    · rw [if_neg hs, actT_emptyV]; rfl)]
  rfl

/-- Every simple lowering maps the vacant vector to itself. -/
theorem lowerT_emptyV (T : memtable.Table) (sig : List Bool) (i : Nat) :
    lowerT T sig i (emptyV sig.length) = emptyV sig.length :=
  raiseT_emptyV { T with raises := T.lowers, lowers := T.raises } sig i

/-- Raising a combination is the combination of the raising
images, with the original coefficients. -/
theorem raiseT_comboV (T : memtable.Table) (sig : List Bool) (i : Nat) :
    ∀ (pool : List (SVec sig.length)) (cs : List BPair),
      raiseT T sig i (comboV pool cs) = comboV (pool.map (raiseT T sig i)) cs
  | [], cs => by rw [comboV_nil, raiseT_emptyV]; exact (comboV_nil cs).symm
  | _ :: _, [] => by rw [comboV_nil_coeffs, comboV_nil_coeffs, raiseT_emptyV]
  | v :: pool, c :: cs => by
    rw [comboV_cons, raiseT_addV, raiseT_scaleV, raiseT_comboV T sig i pool cs]
    exact (comboV_cons (raiseT T sig i v) (pool.map (raiseT T sig i)) c cs).symm

/-- Lowering a combination is the combination of the lowering
images, with the original coefficients. -/
theorem lowerT_comboV (T : memtable.Table) (sig : List Bool) (i : Nat) :
    ∀ (pool : List (SVec sig.length)) (cs : List BPair),
      lowerT T sig i (comboV pool cs) = comboV (pool.map (lowerT T sig i)) cs
  := raiseT_comboV { T with raises := T.lowers, lowers := T.raises } sig i

/-- Raising preserves a coordinate span when every listed
member's raising belongs to that span. The input vector and pool
use the slot power's stated finite key carrier (`con:slotpower`). -/
theorem raiseT_span (T : memtable.Table) (sig : List Bool) (d i : Nat)
    (pool : List (SVec sig.length)) (v : SVec sig.length)
    (hp : ∀ w ∈ pool, keysRead d w) (hv : keysRead d v)
    (himages : ∀ w ∈ pool, elim.spanRel (allMon d sig.length).length
      (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) (raiseT T sig i w)))
    (hspan : elim.spanRel (allMon d sig.length).length (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) v)) :
    elim.spanRel (allMon d sig.length).length (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) (raiseT T sig i v)) := by
  let ms := allMon d sig.length
  obtain ⟨c, cs, hc, _, he⟩ := elim.span_elim hspan
  have hcoords : poly.oneValue (coordsV ms (scaleV c v)) (coordsV ms (comboV pool cs)) :=
    poly.oneValue_trans (coordsV_scaleV v c ms)
      (poly.oneValue_trans he (poly.oneValue_symm (coordsV_comboV ms pool cs)))
  have heq : scaleV c v = comboV pool cs := by
    apply coordsV_injective ms _ _ _ _ hcoords
    · intro p hp'
      have hcount := coordsV_allMon_count d (scaleV c v) (keysRead_scaleV d c v hv) p hp'
      exact mem_of_countOf_pos _ _ (by rw [hcount]; exact Nat.succ_pos 0)
    · intro p hp'
      have hcount := coordsV_allMon_count d (comboV pool cs) (keysRead_comboV d pool cs hp) p hp'
      exact mem_of_countOf_pos _ _ (by rw [hcount]; exact Nat.succ_pos 0)
  have hraise := congrArg (raiseT T sig i) heq
  rw [raiseT_scaleV, raiseT_comboV] at hraise
  have hcombo := coordsV_comboV ms (pool.map (raiseT T sig i)) cs
  rw [← hraise] at hcombo
  have hread : poly.oneValue
      (elim.combo ms.length cs ((pool.map (raiseT T sig i)).map (coordsV ms)))
      (elim.vecScale c (coordsV ms (raiseT T sig i v))) :=
    poly.oneValue_trans (poly.oneValue_symm hcombo) (coordsV_scaleV _ c ms)
  apply elim.spanRel_unscale ms.length (pool.map (coordsV ms)) c (coordsV ms (raiseT T sig i v)) hc
  apply elim.spanRel_congr ms.length (pool.map (coordsV ms)) _ _ hread _
    ((elim.length_vecScale _ _).trans (length_map _ ms))
  apply elim.spanRel_combo ms.length (pool.map (coordsV ms)) (coordsV_rows ms pool)
    ((pool.map (raiseT T sig i)).map (coordsV ms)) cs (coordsV_rows ms _)
  intro j hj
  have hmem := mem_getAt ([] : List BPair) ((pool.map (raiseT T sig i)).map (coordsV ms)) j hj
  obtain ⟨w, hw, hew⟩ := mem_map_of (coordsV ms) _ _ hmem
  obtain ⟨u, hu, heu⟩ := mem_map_of (raiseT T sig i) pool w hw
  rw [← hew, ← heu]
  exact himages u hu

/-- Lowering preserves a coordinate span when every listed
member's lowering belongs to that span. The input vector and pool
use the slot power's stated finite key carrier (`con:slotpower`). -/
theorem lowerT_span (T : memtable.Table) (sig : List Bool) (d i : Nat)
    (pool : List (SVec sig.length)) (v : SVec sig.length)
    (hp : ∀ w ∈ pool, keysRead d w) (hv : keysRead d v)
    (himages : ∀ w ∈ pool, elim.spanRel (allMon d sig.length).length
      (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) (lowerT T sig i w)))
    (hspan : elim.spanRel (allMon d sig.length).length (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) v)) :
    elim.spanRel (allMon d sig.length).length (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) (lowerT T sig i v)) :=
  raiseT_span { T with raises := T.lowers, lowers := T.raises } sig d i pool v hp hv himages hspan

/-- Every vector in an actual G2 block's span has each simple
lowering in that span, at the standard slot signature. -/
theorem blockSpanT_lower_span_G2 (sig : List Bool) (top v : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hv : keysRead memtable.genG2.keys v) (i : Nat) (hi : i < memtable.genG2.rank)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) v)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i v)) :=
  lowerT_span memtable.genG2 sig memtable.genG2.keys i _ v
    (blockSpanT_keys_G2 sig top ht) hv
    (fun w hw => (blockSpanT_reads_G2 sig top hsig ht).2 w hw i hi) hspan

/-- Every admissible lowering word at a G2 seed belongs to its
actual stored block's coordinate span, at every word length
(`lem:lowerspan`; `con:slotpower`). -/
theorem blockSpanT_word_span_G2 (sig : List Bool) (top : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (word : List Nat) (hword : word.all (fun i => decide (i < memtable.genG2.rank)) = true) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length)
        (word.foldl (fun v i => lowerT memtable.genG2 sig i v) top)) := by
  let ms := allMon memtable.genG2.keys sig.length
  let pool := blockSpanT memtable.genG2 sig top
  let P := fun v : SVec sig.length => keysRead memtable.genG2.keys v ∧
    elim.spanRel ms.length (pool.map (coordsV ms)) (coordsV ms v)
  have htop : P top := by
    refine ⟨ht, ?_⟩
    by_cases hz : top.val = []
    · have he : top = emptyV sig.length := Subtype.ext hz
      rw [he, coordsV_empty]
      exact elim.spanRel_null _ _ _ (poly.unitTail_replicate _)
        (coordsV_rows ms pool) (length_replicate BPair.unit ms.length)
    · exact elim.spanRel_of_mem _ _ _ (coordsV_rows ms pool)
        (mem_map_to (coordsV ms) (blockSpanT_top_G2 sig top hz))
  have h := foldl_invariant P (fun v i => lowerT memtable.genG2 sig i v) word top htop (by
    intro i hi v hv
    have hidx : i < memtable.genG2.rank := of_decide_eq_true (all_of_mem _ word hword i hi)
    exact ⟨keysRead_lowerT memtable.genG2 sig i (memtable.genG2_actionKeys i hidx).1
        (memtable.genG2_actionKeys i hidx).2 v hv.1,
      blockSpanT_lower_span_G2 sig top v hsig ht hv.1 i hidx hv.2⟩)
  exact h.2

/-- G2's simple raising and lowering commutator reads the coroot
scalar on each homogeneous component of every standard slot power. -/
theorem raiseT_lowerT_G2 (sig : List Bool) (v : SVec sig.length) (w : List BPair)
    (hsig : sig.all (fun b => !b) = true) (hv : keysRead memtable.genG2.keys v)
    (hh : homogRead memtable.genG2 sig v w) (i j : Nat)
    (hi : i < memtable.genG2.rank) (hj : j < memtable.genG2.rank) :
    raiseT memtable.genG2 sig i (lowerT memtable.genG2 sig j v) =
      addV (lowerT memtable.genG2 sig j (raiseT memtable.genG2 sig i v))
        (scaleV (if i = j then getAt BPair.unit w i else BPair.unit) v) := by
  let T := memtable.genG2
  let K := fun (M : memtable.SMap) (q : Nat) (f : Nat → BPair) =>
    bsum (fun e => if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) M
  let delta := fun q r : Nat => if q == r then BPair.ofNat 1 else BPair.unit
  have hKcongr (M : memtable.SMap) (q : Nat) (f g : Nat → BPair)
      (h : ∀ e ∈ M, (f e.1).oneValue (g e.1)) : (K M q f).oneValue (K M q g) := by
    apply foldB_congr_members
    intro e he
    by_cases hs : (q == e.2.1) = true
    · rw [if_pos hs, if_pos hs]
      exact BPair.mul_congr (BPair.oneValue_refl _) (h e (mem_of_countOf_pos _ _ he))
    · rw [if_neg hs, if_neg hs]
      exact BPair.oneValue_refl _
  have hKsum {β : Type} [DecidableEq β] (M : memtable.SMap) (q : Nat)
      (f : Nat → β → BPair) (l : List β) :
      (K M q (fun s => bsum (f s) l)).oneValue
        (bsum (fun b => K M q (fun s => f s b)) l) := by
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun (e : Nat × Nat × BPair) => bsum (fun b => if q == e.2.1 then e.2.2 * f e.1 b else BPair.unit) l) M ?_)
      (foldB_swapL (fun (e : Nat × Nat × BPair) (b : β) =>
        if q == e.2.1 then e.2.2 * f e.1 b else BPair.unit) M l)
    intro e _
    by_cases he : (q == e.2.1) = true
    · rw [if_pos he]
      refine BPair.oneValue_trans (BPair.oneValue_symm (by apply (foldB_mul_left e.2.2 (f e.1) l))) ?_
      apply foldB_congr_members
      intro b _
      rw [if_pos he]
      exact BPair.oneValue_refl _
    · rw [if_neg he]
      apply BPair.oneValue_symm
      apply foldB_null
      intro b _
      rw [if_neg he]
      exact BPair.oneValue_refl _
  have hKmul (M : memtable.SMap) (q : Nat) (f : Nat → BPair) (c : BPair) :
      (K M q (fun s => f s * c)).oneValue (K M q f * c) := by
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun (e : Nat × Nat × BPair) => (if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) * c) M ?_)
      (BPair.oneValue_symm (foldB_mul_right c (fun (e : Nat × Nat × BPair) =>
        if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) M))
    intro e _
    by_cases he : (q == e.2.1) = true
    · rw [if_pos he, if_pos he, BPair.mul_assoc]
      exact BPair.oneValue_refl _
    · rw [if_neg he, if_neg he]
      exact BPair.oneValue_symm (BPair.unit_mul _)
  have hdelta (q : Nat) (hq : q < 8) (f : Nat → BPair) :
      (bsum (fun r => delta q r * f r) (List.range 8)).oneValue (f q) := by
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun r => if r == q then f q else BPair.unit) (List.range 8) ?_)
      (foldB_pickBeq q (f q) (List.range 8) (countOf_range_one hq))
    intro r _
    change ((if q == r then BPair.ofNat 1 else BPair.unit) * f r).oneValue
      (if r == q then f q else BPair.unit)
    rw [beqSymm r q]
    by_cases he : (q == r) = true
    · rw [if_pos he, if_pos he, beqEqOf he]
      exact BPair.ofNat_one_mul _
    · rw [if_neg he, if_neg he]
      exact BPair.unit_mul _
  have hKexpand (M : memtable.SMap) (hM : ∀ e ∈ M, e.1 < 8) (q : Nat) (f : Nat → BPair) :
      (K M q f).oneValue
        (bsum (fun r => K M q (fun s => delta s r) * f r) (List.range 8)) := by
    refine BPair.oneValue_trans (hKcongr M q f
      (fun s => bsum (fun r => delta s r * f r) (List.range 8))
      (fun e he => BPair.oneValue_symm (hdelta e.1 (hM e he) f))) ?_
    refine BPair.oneValue_trans (hKsum M q (fun s r => delta s r * f r) (List.range 8)) ?_
    exact foldB_congr_members _ _ _ (fun r _ => hKmul M q (fun s => delta s r) (f r))
  have hKcomp (A B : memtable.SMap) (hA : ∀ e ∈ A, e.1 < 8)
      (q : Nat) (f : Nat → BPair) :
      (K B q (fun s => K A s f)).oneValue
        (bsum (fun r => K B q (fun s => K A s (fun t => delta t r)) * f r) (List.range 8)) := by
    refine BPair.oneValue_trans (hKcongr B q (fun s => K A s f)
      (fun s => bsum (fun r => K A s (fun t => delta t r) * f r) (List.range 8))
      (fun (e : Nat × Nat × BPair) _ => by apply hKexpand A hA e.1 f)) ?_
    refine BPair.oneValue_trans (hKsum B q
      (fun s r => K A s (fun t => delta t r) * f r) (List.range 8)) ?_
    exact foldB_congr_members _ _ _ (fun r _ => by apply hKmul B q (fun s => K A s (fun t => delta t r)) (f r))
  have hcoeff : ∀ a, a < 2 → ∀ b, b < 2 → ∀ q, q < 8 → ∀ r, r < 8 →
      (K (getAt [] T.lowers b) q (fun s => K (getAt [] T.raises a) s (fun t => delta t r))).oneValue
        (K (getAt [] T.raises a) q (fun s => K (getAt [] T.lowers b) s (fun t => delta t r))
          + (if a = b then getAt BPair.unit (getAt [] T.hdiag a) q else BPair.unit) * delta q r) := by
    decide +kernel
  have hKcomm (q : Nat) (hq : q < 8) (f : Nat → BPair) :
      (K (getAt [] T.lowers j) q (fun s => K (getAt [] T.raises i) s f)).oneValue
        (K (getAt [] T.raises i) q (fun s => K (getAt [] T.lowers j) s f)
          + (if i = j then getAt BPair.unit (getAt [] T.hdiag i) q else BPair.unit) * f q) := by
    have hE : ∀ e ∈ getAt [] T.raises i, e.1 < 8 := fun e he =>
      of_decide_eq_true (all_of_mem _ _ (memtable.genG2_actionKeys i hi).1 e he)
    have hF : ∀ e ∈ getAt [] T.lowers j, e.1 < 8 := fun e he =>
      of_decide_eq_true (all_of_mem _ _ (memtable.genG2_actionKeys j hj).2 e he)
    let d := if i = j then getAt BPair.unit (getAt [] T.hdiag i) q else BPair.unit
    refine BPair.oneValue_trans (hKcomp _ _ hE q f) ?_
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun r => K (getAt [] T.raises i) q (fun s => K (getAt [] T.lowers j) s (fun t => delta t r)) * f r
        + d * (delta q r * f r)) (List.range 8) ?_) ?_
    · intro r hr
      refine BPair.oneValue_trans (BPair.mul_congr (hcoeff i hi j hj q hq r (ltOfCountRange hr))
        (BPair.oneValue_refl _)) ?_
      rw [BPair.right_distrib, BPair.mul_assoc]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (foldB_add _ _ (List.range 8)) ?_
      exact BPair.add_congr (BPair.oneValue_symm (hKcomp _ _ hF q f))
        (BPair.oneValue_trans (by apply (foldB_mul_left d _ (List.range 8)))
          (BPair.mul_congr (BPair.oneValue_refl d) (hdelta q hq f)))
  have hKcross (A B : memtable.SMap) (q r : Nat) (f : Nat → Nat → BPair) :
      (K B q (fun b => K A r (fun a => f b a))).oneValue
        (K A r (fun a => K B q (fun b => f b a))) := by
    have hex (M N : memtable.SMap) (x y : Nat) (g : Nat → Nat → BPair) :
        (K M x (fun a => K N y (g a))).oneValue
          (bsum (fun (a : Nat × Nat × BPair) => bsum (fun (b : Nat × Nat × BPair) =>
            if x == a.2.1 then
              if y == b.2.1 then a.2.2 * (b.2.2 * g a.1 b.1) else BPair.unit
            else BPair.unit) N) M) := by
      apply foldB_congr_members
      intro a _
      by_cases ha : (x == a.2.1) = true
      · rw [if_pos ha]
        refine BPair.oneValue_trans (BPair.oneValue_symm (by apply (foldB_mul_left a.2.2 _ N))) ?_
        apply foldB_congr_members
        intro b _
        rw [if_pos ha]
        by_cases hb : (y == b.2.1) = true
        · rw [if_pos hb, if_pos hb]; exact BPair.oneValue_refl _
        · rw [if_neg hb, if_neg hb]; exact BPair.mul_unit _
      · rw [if_neg ha]
        apply BPair.oneValue_symm
        apply foldB_null
        intro b _
        rw [if_neg ha]
        exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (hex B A q r f) ?_
    refine BPair.oneValue_trans (foldB_swapL _ B A) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (hex A B r q (fun a b => f b a)))
    apply foldB_congr_members
    intro a _
    apply foldB_congr_members
    intro b _
    by_cases ha : (r == a.2.1) = true <;> by_cases hb : (q == b.2.1) = true
    · rw [if_pos ha, if_pos hb, if_pos ha, if_pos hb, BPair.mul_left_comm]
      exact BPair.oneValue_refl _
    · repeat rw [if_pos ha]
      repeat rw [if_neg hb]
      exact BPair.oneValue_refl _
    · repeat rw [if_neg ha]
      repeat rw [if_pos hb]
      exact BPair.oneValue_refl _
    · repeat rw [if_neg ha]
      repeat rw [if_neg hb]
      exact BPair.oneValue_refl _
  let S := fun (M : memtable.SMap) (s : Nat) (f : List Nat → BPair) (m : List Nat) =>
    K M (getAt 0 m s) (fun a => f (m.set s a))
  let R := fun (M : memtable.SMap) (f : List Nat → BPair) (m : List Nat) =>
    bsum (fun s => S M s f m) (List.range sig.length)
  let E := getAt [] T.raises i
  let F := getAt [] T.lowers j
  let D := fun (m : List Nat) (s : Nat) =>
    if i = j then getAt BPair.unit (getAt [] T.hdiag i) (getAt 0 m s) else BPair.unit
  have hSsame (A B : memtable.SMap) (m : List Nat) (s : Nat)
      (hs : s < m.length) (f : List Nat → BPair) :
      (S B s (fun x => S A s f x) m).oneValue
        (K B (getAt 0 m s) (fun b => K A b (fun a => f (m.set s a)))) := by
    change (K B (getAt 0 m s)
      (fun b => K A (getAt 0 (m.set s b) s) (fun a => f ((m.set s b).set s a)))).oneValue
        (K B (getAt 0 m s) (fun b => K A b (fun a => f (m.set s a))))
    apply hKcongr B (getAt 0 m s)
      (fun b => K A (getAt 0 (m.set s b) s) (fun a => f ((m.set s b).set s a)))
      (fun b => K A b (fun a => f (m.set s a)))
    intro b _
    rw [getAt_set_self 0 b.1 m s hs]
    apply hKcongr A b.1 (fun a => f ((m.set s b.1).set s a)) (fun a => f (m.set s a))
    intro a _
    rw [set_set]
    exact BPair.oneValue_refl _
  have hSdiff (A B : memtable.SMap) (m : List Nat) (s t : Nat) (he : s ≠ t)
      (f : List Nat → BPair) :
      (S B s (fun x => S A t f x) m).oneValue (S A t (fun x => S B s f x) m) := by
    unfold S
    refine BPair.oneValue_trans (hKcongr B (getAt 0 m s)
      (fun b => K A (getAt 0 (m.set s b) t) (fun a => f ((m.set s b).set t a)))
      (fun b => K A (getAt 0 m t) (fun a => f ((m.set t a).set s b))) ?_) ?_
    · intro b _
      rw [getAt_set_ne 0 m s t b.1 (fun ht => he ht.symm)]
      apply hKcongr A (getAt 0 m t)
        (fun a => f ((m.set s b.1).set t a)) (fun a => f ((m.set t a).set s b.1))
      intro a _
      rw [ground.set_comm m s t b.1 a.1 he]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (hKcross A B (getAt 0 m s) (getAt 0 m t)
        (fun b a => f ((m.set t a).set s b))) ?_
      apply hKcongr A (getAt 0 m t)
        (fun a => K B (getAt 0 m s) (fun b => f ((m.set t a).set s b)))
        (fun a => K B (getAt 0 (m.set t a) s) (fun b => f ((m.set t a).set s b)))
      intro a _
      rw [getAt_set_ne 0 m t s a.1 he]
      exact BPair.oneValue_refl _
  have hScomm (m : List Nat) (hm : m.length = sig.length)
      (hk : m.all (fun q => decide (q < T.keys)) = true)
      (s t : Nat) (hs : s < sig.length) (_ht : t < sig.length) (f : List Nat → BPair) :
      (S F s (fun x => S E t f x) m).oneValue
        (S E t (fun x => S F s f x) m + if s = t then D m s * f m else BPair.unit) := by
    by_cases he : s = t
    · subst t
      rw [if_pos rfl]
      have hsm : s < m.length := by rw [hm]; exact hs
      have hq : getAt 0 m s < 8 := of_decide_eq_true
        (all_of_mem _ m hk _ (mem_getAt 0 m s hsm))
      refine BPair.oneValue_trans (hSsame E F m s hsm f) ?_
      refine BPair.oneValue_trans (hKcomm _ hq (fun a => f (m.set s a))) ?_
      rw [set_self 0 m s hsm]
      exact BPair.add_congr (BPair.oneValue_symm (hSsame F E m s hsm f))
        (BPair.oneValue_refl _)
    · rw [if_neg he]
      exact BPair.oneValue_trans (hSdiff E F m s t he f) (BPair.oneValue_symm (BPair.add_unit _))
  have hRcomp (A B : memtable.SMap) (m : List Nat) (f : List Nat → BPair) :
      (R B (R A f) m).oneValue
        (bsum (fun s => bsum (fun t => S B s (fun x => S A t f x) m)
          (List.range sig.length)) (List.range sig.length)) := by
    apply foldB_congr_members
    intro s _
    exact hKsum B (getAt 0 m s) (fun a t => S A t f (m.set s a)) (List.range sig.length)
  have hstd (s : Nat) (hs : s < sig.length) : getAt false sig s = false := by
    have h := all_of_mem _ sig hsig _ (mem_getAt false sig s hs)
    cases he : getAt false sig s with
    | false => rfl
    | true => rw [he] at h; exact Bool.noConfusion h
  have hD (m : List Nat) (hm : m.length = sig.length)
      (hk : m.all (fun q => decide (q < T.keys)) = true) :
      (bsum (D m) (List.range sig.length)).oneValue
        (if i = j then getAt BPair.unit (weightT T sig m) i else BPair.unit) := by
    by_cases he : i = j
    · rw [if_pos he]
      refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
        (weightT_entry T sig m memtable.genG2_diagonals.1 memtable.genG2_diagonals.2 hm hk i hi))
      apply foldB_congr_members
      intro s hs
      dsimp [D]
      rw [if_pos he, hstd s (ltOfCountRange hs)]
      exact BPair.oneValue_refl _
    · rw [if_neg he]
      apply foldB_null
      intro s _
      dsimp [D]
      rw [if_neg he]
      exact BPair.oneValue_refl _
  have hRcomm (m : List Nat) (hm : m.length = sig.length)
      (hk : m.all (fun q => decide (q < T.keys)) = true) (f : List Nat → BPair) :
      (R F (R E f) m).oneValue
        (R E (R F f) m + (if i = j then getAt BPair.unit (weightT T sig m) i else BPair.unit) * f m) := by
    refine BPair.oneValue_trans (hRcomp E F m f) ?_
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun s => bsum (fun t => S E t (fun x => S F s f x) m) (List.range sig.length)
        + D m s * f m) (List.range sig.length) ?_) ?_
    · intro s hs
      have hs' := ltOfCountRange hs
      refine BPair.oneValue_trans (foldB_congr_members _ _ (List.range sig.length)
        (fun t ht => hScomm m hm hk s t hs' (ltOfCountRange ht) f)) ?_
      refine BPair.oneValue_trans (foldB_add _ _ (List.range sig.length)) ?_
      apply BPair.add_congr (BPair.oneValue_refl _)
      have hsingle := bsum_range_single_of (fun t => decide (s = t)) (fun _ => D m s * f m) s sig.length hs'
        (fun t _ => ⟨fun h => (of_decide_eq_true h).symm, fun h => decide_eq_true h.symm⟩)
      have heq := famFold_congr_all BPair.add BPair.unit
        (fun t => if decide (s = t) then D m s * f m else BPair.unit)
        (fun t => if s = t then D m s * f m else BPair.unit)
        (fun t => ite_decide (s = t) (D m s * f m) BPair.unit) (List.range sig.length)
      exact BPair.oneValue_trans (BPair.oneValue_of_eq heq.symm) hsingle
    · refine BPair.oneValue_trans (foldB_add _ _ (List.range sig.length)) ?_
      apply BPair.add_congr
      · exact BPair.oneValue_trans (bsum_swap _ _ _) (BPair.oneValue_symm (hRcomp F E m f))
      · exact BPair.oneValue_trans (BPair.oneValue_symm (foldB_mul_right (f m) (D m) (List.range sig.length)))
          (BPair.mul_congr (hD m hm hk) (BPair.oneValue_refl _))
  have hreadRaise (U : memtable.Table) (k : Nat) (u : SVec sig.length) (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (raiseT U sig k u).val).oneValue
        (bsum (fun p => p.2 * R (getAt [] U.raises k) f p.1) u.val) := by
    refine BPair.oneValue_trans (by apply (fold_raiseT U sig k u f)) ?_
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun s => bsum (fun p => p.2 * S (getAt [] U.raises k) s f p.1) u.val) (List.range sig.length) ?_) ?_
    · intro s hs
      rw [hstd s (ltOfCountRange hs)]
      exact fold_actT (getAt [] U.raises k) false s u f
    · refine BPair.oneValue_trans (foldB_swapL _ (List.range sig.length) u.val) ?_
      exact foldB_congr_members _ _ u.val (fun p _ => by apply (foldB_mul_left p.2 _ (List.range sig.length)))
  have hEread := hreadRaise T i
  have hFread := hreadRaise { T with raises := T.lowers, lowers := T.raises } j
  let d := if i = j then getAt BPair.unit w i else BPair.unit
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (raiseT T sig i (lowerT T sig j v)).val).oneValue
        (bsum (fun p => p.2 * f p.1) (addV (lowerT T sig j (raiseT T sig i v)) (scaleV d v)).val) := by
    refine BPair.oneValue_trans (hEread (lowerT T sig j v) f) ?_
    refine BPair.oneValue_trans (hFread v (R E f)) ?_
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun (p : List Nat × BPair) => p.2 * R E (R F f) p.1 + d * (p.2 * f p.1)) v.val ?_) ?_
    · intro p hp
      have hp' := mem_of_countOf_pos _ _ hp
      have hg := listBeqEq (all_of_mem _ v.val hh p hp')
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (hRcomm p.1 (width_of_mem v p hp') (all_of_mem _ v.val hv p hp') f)) ?_
      rw [hg, BPair.left_distrib, BPair.mul_left_comm]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (foldB_add _ _ v.val) ?_
      refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (by apply (fold_addV _ _ f)))
      apply BPair.add_congr
      · exact BPair.oneValue_trans (BPair.oneValue_symm (hEread v (R F f)))
          (BPair.oneValue_symm (hFread (raiseT T sig i v) f))
      · exact BPair.oneValue_trans (by apply (foldB_mul_left d _ v.val))
          (BPair.oneValue_symm (by apply (fold_scaleV v d f)))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- Every simple raising of an admissible lowering word belongs
to the actual G2 block span at a homogeneous top (`lem:lowerspan`). -/
theorem raiseT_word_span_G2 (sig : List Bool) (top : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hhom : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top))
    (hraise : raisedUnit memtable.genG2 sig top = true)
    (word : List Nat) (hw : word.all (fun j => decide (j < memtable.genG2.rank)) = true)
    (i : Nat) (hi : i < memtable.genG2.rank) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length)
        (raiseT memtable.genG2 sig i (word.foldl (fun v j => lowerT memtable.genG2 sig j v) top))) := by
  let T := memtable.genG2
  let ms := allMon T.keys sig.length
  let pool := blockSpanT T sig top
  let S := fun v : SVec sig.length => elim.spanRel ms.length (pool.map (coordsV ms)) (coordsV ms v)
  let P := fun v : SVec sig.length => keysRead T.keys v ∧ ∃ w,
    homogRead T sig v w ∧ S v ∧ ∀ j, j < T.rank → S (raiseT T sig j v)
  have hSnull (v : SVec sig.length) (hv : v.val = []) : S v := by
    have he : v = emptyV sig.length := Subtype.ext hv
    change elim.spanRel ms.length (pool.map (coordsV ms)) (coordsV ms v)
    rw [he, coordsV_empty]
    exact elim.spanRel_null _ _ _ (poly.unitTail_replicate _)
      (coordsV_rows ms pool) (length_replicate BPair.unit ms.length)
  have hSadd (v u : SVec sig.length) (hv : S v) (hu : S u) : S (addV v u) :=
    elim.spanRel_congr _ _ _ _ (poly.oneValue_symm (coordsV_addV v u ms))
      (elim.spanRel_add _ _ _ _ (coordsV_rows ms pool) (length_map _ ms) (length_map _ ms) hv hu)
      (length_map _ ms)
  have hSscale (c : BPair) (v : SVec sig.length) (hv : S v) : S (scaleV c v) :=
    elim.spanRel_congr _ _ _ _ (poly.oneValue_symm (coordsV_scaleV v c ms))
      (elim.spanRel_scale _ _ _ c (coordsV_rows ms pool) (length_map _ ms) hv) (length_map _ ms)
  have htop : P top := by
    refine ⟨ht, weightV T sig top, hhom, ?_, ?_⟩
    · exact blockSpanT_word_span_G2 sig top hsig ht [] rfl
    · intro j hj
      exact hSnull _ (nil_of_length_zero _ (beqEqOf (all_range_read T.rank hraise j hj)))
  have hstep (v : SVec sig.length) (hv : P v) (j : Nat) (hj : j < T.rank) :
      P (lowerT T sig j v) := by
    obtain ⟨hk, w, hg, hs, hr⟩ := hv
    have hkl := keysRead_lowerT T sig j (memtable.genG2_actionKeys j hj).1
      (memtable.genG2_actionKeys j hj).2 v hk
    refine ⟨hkl, _, homogRead_lowerT_G2 sig j hj v w hk hg,
      blockSpanT_lower_span_G2 sig top v hsig ht hk j hj hs, ?_⟩
    intro k hki
    rw [raiseT_lowerT_G2 sig v w hsig hk hg k j hki hj]
    apply hSadd
    · exact blockSpanT_lower_span_G2 sig top (raiseT T sig k v) hsig ht
        (keysRead_raiseT T sig k (memtable.genG2_actionKeys k hki).1
          (memtable.genG2_actionKeys k hki).2 v hk) j hj (hr k hki)
    · exact hSscale _ v hs
  have h := foldl_invariant P (fun v j => lowerT T sig j v) word top htop
    (fun j hj v hv => hstep v hv j (of_decide_eq_true (all_of_mem _ word hw j hj)))
  obtain ⟨_, _, _, _, hr⟩ := h
  exact hr i hi

/-- Every simple raising preserves the actual G2 block span at
its homogeneous top, on the stated finite monomial carrier. -/
theorem blockSpanT_raise_span_G2 (sig : List Bool) (top v : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hhom : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top))
    (hraise : raisedUnit memtable.genG2 sig top = true)
    (hv : keysRead memtable.genG2.keys v) (i : Nat) (hi : i < memtable.genG2.rank)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) v)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) (raiseT memtable.genG2 sig i v)) := by
  apply raiseT_span memtable.genG2 sig memtable.genG2.keys i _ v
    (blockSpanT_keys_G2 sig top ht) hv _ hspan
  intro u hu
  obtain ⟨word, hw, he⟩ := blockSpanT_words memtable.genG2 sig top memtable.genG2_symmWt u hu
  rw [← he]
  exact raiseT_word_span_G2 sig top hsig ht hhom hraise word hw i hi

/-- Distinct homogeneous weights have perpendicular vectors at
the unit pairing: each occupied monomial belongs to one weight. -/
theorem pairT_homog_perp (T : memtable.Table) (sig : List Bool) {k : Nat}
    (u v : SVec k) (a b : List BPair)
    (hu : homogRead T sig u a) (hv : homogRead T sig v b) (hab : a ≠ b) :
    (pairT T true u v).oneValue BPair.unit := by
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  refine BPair.oneValue_trans (dotTS_read T true u v) ?_
  refine BPair.oneValue_trans (dotT_read T true u v) ?_
  apply foldB_null
  intro p hp
  change (p.2 * coefAt p.1 v).oneValue BPair.unit
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (coefAt_off p.1 v ?_))
    (BPair.mul_unit _)
  intro q hq he
  have ha := listBeqEq (all_of_mem _ u.val hu p (mem_of_countOf_pos _ _ hp))
  have hb := listBeqEq (all_of_mem _ v.val hv q hq)
  rw [he] at hb
  exact hab (ha.symm.trans hb)

/-- Every member of G2's stored span is homogeneous at its
selected weight when the seed is homogeneous there. -/
theorem blockSpanT_homog_G2 (sig : List Bool) (top : SVec sig.length)
    (ht : keysRead memtable.genG2.keys top)
    (hh : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top)) :
    ∀ v ∈ blockSpanT memtable.genG2 sig top,
      homogRead memtable.genG2 sig v (weightV memtable.genG2 sig v) := by
  have h := blockSpanT_all memtable.genG2 sig top memtable.genG2_symmWt
    (fun v => keysRead memtable.genG2.keys v ∧
      homogRead memtable.genG2 sig v (weightV memtable.genG2 sig v)) ⟨ht, hh⟩ (by
      intro v hv i hi ho
      have hg := homogRead_lowerT_G2 sig i hi v (weightV memtable.genG2 sig v) hv.1 hv.2
      refine ⟨keysRead_lowerT memtable.genG2 sig i (memtable.genG2_actionKeys i hi).1
        (memtable.genG2_actionKeys i hi).2 v hv.1, ?_⟩
      rw [weightV_homog memtable.genG2 sig (lowerT memtable.genG2 sig i v) _ hg ho]
      exact hg)
  exact fun v hv => (h v hv).2

/-- Distinct weight groups of an actual homogeneous G2 block are
perpendicular at the generating table's pairing. -/
theorem blockSpanT_perp_G2 (sig : List Bool) (top u v : SVec sig.length)
    (ht : keysRead memtable.genG2.keys top)
    (hh : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top))
    (hu : u ∈ blockSpanT memtable.genG2 sig top) (hv : v ∈ blockSpanT memtable.genG2 sig top)
    (hw : weightV memtable.genG2 sig u ≠ weightV memtable.genG2 sig v) :
    (pairT memtable.genG2 true u v).oneValue BPair.unit :=
  pairT_homog_perp memtable.genG2 sig u v _ _ (blockSpanT_homog_G2 sig top ht hh u hu)
    (blockSpanT_homog_G2 sig top ht hh v hv) hw

/-- The actual homogeneous G2 block is independent on the full
monomial carrier, its distinct weight groups perpendicular. -/
theorem blockSpanT_indep_G2 (sig : List Bool) (top : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hhom : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top)) :
    elim.indepRows (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length))) := by
  let ms := allMon memtable.genG2.keys sig.length
  let pool := blockSpanT memtable.genG2 sig top
  apply elim.indep_groups (weightV memtable.genG2 sig) (coordsV ms) ms.length pool
    (fun _ _ => length_map _ ms)
  · intro mu hmu
    have hg := (blockSpanT_reads_G2 sig top hsig ht).1 mu hmu
    have he : pool.filter (fun v => decide (weightV memtable.genG2 sig v = mu))
        = pool.filter (fun v => weightV memtable.genG2 sig v == mu) := by
      apply filter_congr
      intro v
      by_cases h : weightV memtable.genG2 sig v = mu
      · rw [decide_eq_true h, h, listEqBeq]
      · rw [decide_eq_false h]
        cases hb : (weightV memtable.genG2 sig v == mu) with
        | false => rfl
        | true => exact False.elim (h (listBeqEq hb))
    rw [he]
    exact hg
  · intro u hu v hv hne
    exact BPair.oneValue_trans
      (pairT_coordsV memtable.genG2 ms u v
        (coordsV_allMon_count memtable.genG2.keys u (blockSpanT_keys_G2 sig top ht u hu)))
      (blockSpanT_perp_G2 sig top u v ht hhom hu hv hne)

/-- The actual homogeneous G2 block's count is at most its
finite monomial-coordinate count. -/
theorem blockSpanT_length_le_G2 (sig : List Bool) (top : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hhom : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top)) :
    (blockSpanT memtable.genG2 sig top).length ≤ (allMon memtable.genG2.keys sig.length).length := by
  have h := blockSpanT_indep_G2 sig top hsig ht hhom
  have hbound := elim.indep_bound _ _ h.1 h
  rw [length_map] at hbound
  exact hbound

/-- Sparse maps at one value give the same collected slot action,
at either sign and every vector of the slot power. -/
theorem actT_congr (A B : memtable.SMap) (h : memtable.sOneValue A B = true)
    (neg : Bool) (s : Nat) {k : Nat} (v : SVec k) :
    actT A neg s v = actT B neg s v := by
  let key := fun e : Nat × Nat × BPair => (e.1, e.2.1)
  let keys := dedupF (A.map key ++ B.map key)
  have hfold (M : memtable.SMap) (hm : ∀ e ∈ M, key e ∈ A.map key ++ B.map key)
      (f : Nat × Nat → BPair) :
      (bsum (fun e => f (key e) * e.2.2) M).oneValue
        (bsum (fun q => f q * memtable.wtAt M q.1 q.2) keys) := by
    let fam := M.map (fun e => (key e, e.2.2))
    have hc : ∀ p ∈ fam, countOf p.1 keys = 1 := by
      intro p hp
      obtain ⟨e, he, hep⟩ := mem_map_of (fun e : Nat × Nat × BPair => (key e, e.2.2)) M p hp
      rw [← hep]
      exact countOf_dedupF_one (hm e he)
    have hlin := foldB_keyFold_linear pairBeq pairBeq_read pairBeq_refl keys f fam hc
    have hk (q : Nat × Nat) : (keyFoldB pairBeq q fam).oneValue (memtable.wtAt M q.1 q.2) := by
      have he : keyFoldB pairBeq q fam =
          bsum (fun e : Nat × Nat × BPair =>
            if e.1 == q.1 && e.2.1 == q.2 then e.2.2 else BPair.unit) M := by
        unfold keyFoldB fam
        rw [famFold_map]
        rfl
      exact BPair.oneValue_trans (BPair.oneValue_of_eq he)
        (BPair.oneValue_symm (memtable.wtAt_read M q.1 q.2))
    have he : bsum (fun p => f p.1 * p.2) fam = bsum (fun e => f (key e) * e.2.2) M := by
      unfold fam
      rw [bsum_map]
    rw [he] at hlin
    exact BPair.oneValue_trans (BPair.oneValue_symm hlin)
      (foldB_congr_members _ _ keys (fun q _ => BPair.mul_congr (BPair.oneValue_refl _) (hk q)))
  have hweight (f : Nat × Nat → BPair) :
      (bsum (fun e => f (key e) * e.2.2) A).oneValue
        (bsum (fun e => f (key e) * e.2.2) B) := by
    refine BPair.oneValue_trans (hfold A
      (fun e he => mem_append_left (B.map key) (mem_map_to key he)) f) ?_
    refine BPair.oneValue_trans (foldB_congr_members _ _ keys (fun q _ =>
      BPair.mul_congr (BPair.oneValue_refl _) (memtable.sOneValue_wtAt A B h q.1 q.2))) ?_
    exact BPair.oneValue_symm (hfold B
      (fun e he => mem_append_right (A.map key) (mem_map_to key he)) f)
  have hplain (M : memtable.SMap) (q : Nat) (f : Nat → BPair) :
      (bsum (fun e => if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) M).oneValue
        (bsum (fun e => (if q == (key e).2 then f (key e).1 else BPair.unit) * e.2.2) M) := by
    apply foldB_congr_members
    intro e _
    by_cases he : (q == e.2.1) = true
    · rw [if_pos he, if_pos he]
      exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
    · rw [if_neg he, if_neg he]
      exact BPair.oneValue_symm (BPair.unit_mul _)
  have hunsigned (q : Nat) (f : Nat → BPair) :
      (bsum (fun e => if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) A).oneValue
        (bsum (fun e => if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) B) :=
    BPair.oneValue_trans (hplain A q f)
      (BPair.oneValue_trans (hweight (fun e => if q == e.2 then f e.1 else BPair.unit))
        (BPair.oneValue_symm (hplain B q f)))
  have hsigned (M : memtable.SMap) (q : Nat) (f : Nat → BPair) :
      (bsum (fun e => if q == e.2.1 then signedAt neg e.2.2 * f e.1 else BPair.unit) M).oneValue
        (signedAt neg (bsum (fun e => if q == e.2.1 then e.2.2 * f e.1 else BPair.unit) M)) := by
    cases neg with
    | false => exact BPair.oneValue_refl _
    | true =>
      refine BPair.oneValue_trans (foldB_congr_members _
        (fun e : Nat × Nat × BPair => (if q == e.2.1 then e.2.2 * f e.1 else BPair.unit).swap) M ?_) ?_
      · intro e _
        by_cases he : (q == e.2.1) = true
        · rw [if_pos he, if_pos he]
          exact BPair.oneValue_of_eq (BPair.swap_mul _ _)
        · rw [if_neg he, if_neg he]
          exact BPair.oneValue_refl _
      · exact BPair.oneValue_of_eq (fold_swap _ M)
  have hkernel (q : Nat) (f : Nat → BPair) :
      (bsum (fun e => if q == e.2.1 then signedAt neg e.2.2 * f e.1 else BPair.unit) A).oneValue
        (bsum (fun e => if q == e.2.1 then signedAt neg e.2.2 * f e.1 else BPair.unit) B) := by
    refine BPair.oneValue_trans (hsigned A q f) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (hsigned B q f))
    cases neg with
    | false => exact hunsigned q f
    | true => exact swap_congr (hunsigned q f)
  have hread (f : List Nat → BPair) :
      (bsum (fun p => p.2 * f p.1) (actT A neg s v).val).oneValue
        (bsum (fun p => p.2 * f p.1) (actT B neg s v).val) := by
    refine BPair.oneValue_trans (by apply (fold_actT A neg s v f)) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (by apply (fold_actT B neg s v f)))
    exact foldB_congr_members _ _ v.val (fun p _ => BPair.mul_congr (BPair.oneValue_refl _)
      (hkernel (getAt 0 p.1 s) (fun a => f (p.1.set s a))))
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_fold m _)
    (BPair.oneValue_trans (hread (fun n => if n == m then BPair.ofNat 1 else BPair.unit))
      (BPair.oneValue_symm (coefAt_fold m _)))

/-- The unit-weight sparse pairing exchanges its two vectors. -/
theorem pairT_unit_comm (T : memtable.Table) {k : Nat} (u v : SVec k) :
    (pairT T true u v).oneValue (pairT T true v u) := by
  change (pairT (memtable.lettersT 0) true u v).oneValue (pairT (memtable.lettersT 0) true v u)
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  refine BPair.oneValue_trans (dotTS_read (memtable.lettersT 0) true u v) ?_
  refine BPair.oneValue_trans (dotT_comm (memtable.lettersT 0) (memtable.lettersT_symm 0) true u v) ?_
  exact BPair.oneValue_trans (BPair.oneValue_symm (dotTS_read (memtable.lettersT 0) true v u))
    (BPair.oneValue_symm (BPair.norm_oneValue _))

/-- A scalar in the second vector reads at the unit pairing's
scalar factor. -/
theorem pairT_unit_scale (T : memtable.Table) {k : Nat} (u v : SVec k) (c : BPair) :
    (pairT T true u (scaleV c v)).oneValue (c * pairT T true u v) := by
  have hread (x : SVec k) : (pairT T true u x).oneValue
      (bsum (fun p => p.2 * coefAt p.1 x) u.val) :=
    BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans (dotTS_read T true u x) (dotT_read T true u x))
  refine BPair.oneValue_trans (hread (scaleV c v)) ?_
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => c * (p.2 * coefAt p.1 v)) u.val ?_) ?_
  · intro p _
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl p.2) (coefAt_scaleV p.1 v c)) ?_
    rw [BPair.mul_left_comm p.2 c]
    exact BPair.oneValue_refl _
  · exact BPair.oneValue_trans (by apply (foldB_mul_left c _ u.val))
      (BPair.mul_congr (BPair.oneValue_refl c) (BPair.oneValue_symm (hread v)))

/-- The unit pairing reads vector addition as addition of the
pairings. -/
theorem pairT_unit_add (T : memtable.Table) {k : Nat} (u v z : SVec k) :
    (pairT T true u (addV v z)).oneValue (pairT T true u v + pairT T true u z) := by
  have hread (x : SVec k) : (pairT T true u x).oneValue
      (bsum (fun p => p.2 * coefAt p.1 x) u.val) :=
    BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans (dotTS_read T true u x) (dotT_read T true u x))
  refine BPair.oneValue_trans (hread (addV v z)) ?_
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => p.2 * coefAt p.1 v + p.2 * coefAt p.1 z) u.val ?_) ?_
  · intro p _
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl p.2) (coefAt_addV p.1 v z)) ?_
    rw [BPair.left_distrib]
    exact BPair.oneValue_refl _
  · exact BPair.oneValue_trans (foldB_add _ _ u.val)
      (BPair.add_congr (BPair.oneValue_symm (hread v)) (BPair.oneValue_symm (hread z)))

/-- Pairing a vector with the vacant vector reads the sum's unit. -/
theorem pairT_unit_empty (T : memtable.Table) {k : Nat} (v : SVec k) :
    (pairT T true v (emptyV k)).oneValue BPair.unit := by
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  refine BPair.oneValue_trans (dotTS_read T true v (emptyV k)) ?_
  refine BPair.oneValue_trans (dotT_read T true v (emptyV k)) ?_
  exact foldB_null _ v.val (fun p _ => BPair.mul_unit p.2)

/-- A signed sparse action at a valid slot walks across the
unit pairing as its transpose (`con:memtable`; `con:slotpower`). -/
theorem pairT_actT (T : memtable.Table) (M : memtable.SMap) (neg : Bool)
    {k : Nat} (s : Nat) (hs : s < k) (u v : SVec k) :
    (pairT T true (actT M neg s u) v).oneValue
      (pairT T true u (actT (memtable.sT M) neg s v)) := by
  let J := fun (A : memtable.SMap) (a b : List Nat) => bsum (fun e =>
    if getAt 0 a s == e.2.1 && a.set s e.1 == b then signedAt neg e.2.2 else BPair.unit) A
  have hcoef (m : List Nat) (z : SVec k) : (coefAt m z).oneValue
      (bsum (fun q => if m == q.1 then q.2 else BPair.unit) z.val) := by
    refine BPair.oneValue_trans (coefAt_read m z) ?_
    apply BPair.oneValue_of_eq
    apply famFold_congr_all
    intro q
    change (if q.1 == m then q.2 else BPair.unit) = (if m == q.1 then q.2 else BPair.unit)
    rw [listBeqSymm q.1 m]
  have hinner (A : memtable.SMap) (a : List Nat) (z : SVec k) :
      (bsum (fun e => if getAt 0 a s == e.2.1 then
        signedAt neg e.2.2 * coefAt (a.set s e.1) z else BPair.unit) A).oneValue
        (bsum (fun q => q.2 * J A a q.1) z.val) := by
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun (e : Nat × Nat × BPair) => bsum (fun q : List Nat × BPair => q.2 *
        (if getAt 0 a s == e.2.1 && a.set s e.1 == q.1 then signedAt neg e.2.2 else BPair.unit)) z.val) A ?_) ?_
    · intro e _
      by_cases he : (getAt 0 a s == e.2.1) = true
      · rw [if_pos he]
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (hcoef (a.set s e.1) z)) ?_
        refine BPair.oneValue_trans (BPair.oneValue_symm (by apply (foldB_mul_left (signedAt neg e.2.2) _ z.val))) ?_
        apply foldB_congr_members
        intro q _
        by_cases hq : (a.set s e.1 == q.1) = true
        · have hh : (getAt 0 a s == e.2.1 && a.set s e.1 == q.1) = true := by rw [he, hq]; rfl
          rw [if_pos hq, if_pos hh]
          exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
        · have hh : ¬ (getAt 0 a s == e.2.1 && a.set s e.1 == q.1) = true := fun h => hq (andSplitB h).2
          rw [if_neg hq, if_neg hh]
          exact BPair.oneValue_trans (BPair.mul_unit _) (BPair.oneValue_symm (BPair.mul_unit _))
      · rw [if_neg he]
        apply BPair.oneValue_symm
        apply foldB_null
        intro q _
        have hh : ¬ (getAt 0 a s == e.2.1 && a.set s e.1 == q.1) = true := fun h => he (andSplitB h).1
        rw [if_neg hh]
        exact BPair.mul_unit _
    · refine BPair.oneValue_trans (foldB_swapL _ A z.val) ?_
      exact foldB_congr_members _ _ z.val (fun q _ => by apply (foldB_mul_left q.2 _ A))
  have hpair (A : memtable.SMap) (x y : SVec k) :
      (pairT T true (actT A neg s x) y).oneValue
        (bsum (fun p => p.2 * bsum (fun q => q.2 * J A p.1 q.1) y.val) x.val) := by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans (dotTS_read T true (actT A neg s x) y) ?_
    refine BPair.oneValue_trans (dotT_read T true (actT A neg s x) y) ?_
    refine BPair.oneValue_trans (by apply (fold_actT A neg s x (fun m => coefAt m y))) ?_
    exact foldB_congr_members _ _ x.val (fun p _ => BPair.mul_congr (BPair.oneValue_refl _) (hinner A p.1 y))
  have hmove (a b : List Nat) (t r : Nat) (ha : s < a.length)
      (h : (getAt 0 a s == r && a.set s t == b) = true) :
      (getAt 0 b s == t && b.set s r == a) = true := by
    have hx := beqEqOf (andSplitB h).1
    have hy := listBeqEq (andSplitB h).2
    rw [← hy, getAt_set_self 0 t a s ha, eqBeqOf rfl, set_set, ← hx, set_self 0 a s ha, listEqBeq]
    rfl
  have hJ (a b : List Nat) (ha : a.length = k) (hb : b.length = k) :
      (J M a b).oneValue (J (memtable.sT M) b a) := by
    change (bsum _ M).oneValue (bsum _ (M.map (fun e => (e.2.1, e.1, e.2.2))))
    rw [bsum_map]
    apply foldB_congr_members
    intro e _
    have has : s < a.length := by rw [ha]; exact hs
    have hbs : s < b.length := by rw [hb]; exact hs
    have he : (getAt 0 a s == e.2.1 && a.set s e.1 == b)
        = (getAt 0 b s == e.1 && b.set s e.2.1 == a) := by
      cases h1 : (getAt 0 a s == e.2.1 && a.set s e.1 == b) with
      | true => exact (hmove a b e.1 e.2.1 has h1).symm
      | false =>
        cases h2 : (getAt 0 b s == e.1 && b.set s e.2.1 == a) with
        | false => rfl
        | true =>
          have h3 := hmove b a e.2.1 e.1 hbs h2
          rw [h1] at h3
          exact False.elim (Bool.noConfusion h3)
    rw [he]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (hpair M u v) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_trans
    (BPair.oneValue_symm (hpair (memtable.sT M) v u)) (pairT_unit_comm T _ u))
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => bsum (fun q : List Nat × BPair =>
      p.2 * (q.2 * J M p.1 q.1)) v.val) u.val
    (fun p _ => BPair.oneValue_symm (by apply (foldB_mul_left p.2 _ v.val)))) ?_
  refine BPair.oneValue_trans (foldB_swapL _ u.val v.val) ?_
  apply foldB_congr_members
  intro q hq
  refine BPair.oneValue_trans (foldB_congr_members _
    (fun p : List Nat × BPair => q.2 * (p.2 * J (memtable.sT M) q.1 p.1)) u.val ?_)
    (by apply (foldB_mul_left q.2 _ u.val))
  intro p hp
  rw [BPair.mul_left_comm p.2 q.2]
  exact BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_congr (BPair.oneValue_refl _)
    (hJ p.1 q.1 (width_of_mem u p (mem_of_countOf_pos _ _ hp))
      (width_of_mem v q (mem_of_countOf_pos _ _ hq))))

/-- The actual G2 simple raising walks across the unit pairing
as its lowering, at both the standard and dual slot actions. -/
theorem pairT_raise_lower_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (u v : SVec sig.length) :
    (pairT memtable.genG2 true (raiseT memtable.genG2 sig i u) v).oneValue
      (pairT memtable.genG2 true u (lowerT memtable.genG2 sig i v)) := by
  let T := memtable.genG2
  have hread (U : memtable.Table) (x y : SVec sig.length) :
      (pairT T true (raiseT U sig i x) y).oneValue
        (bsum (fun s => if getAt false sig s then
          pairT T true (actT (getAt [] U.lowers i) true s x) y
          else pairT T true (actT (getAt [] U.raises i) false s x) y) (List.range sig.length)) := by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans (dotTS_read T true (raiseT U sig i x) y) ?_
    refine BPair.oneValue_trans (dotT_read T true (raiseT U sig i x) y) ?_
    refine BPair.oneValue_trans (by apply (fold_raiseT U sig i x (fun m => coefAt m y))) ?_
    apply foldB_congr_members
    intro s _
    by_cases hs : getAt false sig s = true
    · rw [if_pos hs, if_pos hs]
      exact BPair.oneValue_trans (BPair.oneValue_symm (dotT_read T true _ y))
        (BPair.oneValue_trans (BPair.oneValue_symm (dotTS_read T true _ y))
          (BPair.oneValue_symm (BPair.norm_oneValue _)))
    · rw [if_neg hs, if_neg hs]
      exact BPair.oneValue_trans (BPair.oneValue_symm (dotT_read T true _ y))
        (BPair.oneValue_trans (BPair.oneValue_symm (dotTS_read T true _ y))
          (BPair.oneValue_symm (BPair.norm_oneValue _)))
  refine BPair.oneValue_trans (hread T u v) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_trans
    (BPair.oneValue_symm (hread { T with raises := T.lowers, lowers := T.raises } v u))
    (pairT_unit_comm T _ u))
  apply foldB_congr_members
  intro s hs
  have hslot := ltOfCountRange hs
  by_cases hd : getAt false sig s = true
  · rw [if_pos hd, if_pos hd]
    refine BPair.oneValue_trans (pairT_actT T (getAt [] T.lowers i) true s hslot u v) ?_
    rw [actT_congr _ _ (memtable.genG2_transpose i hi).2 true s v]
    exact pairT_unit_comm T u _
  · rw [if_neg hd, if_neg hd]
    refine BPair.oneValue_trans (pairT_actT T (getAt [] T.raises i) false s hslot u v) ?_
    rw [actT_congr _ _ (memtable.genG2_transpose i hi).1 false s v]
    exact pairT_unit_comm T u _

/-- Equivalent scalars give the same collected sparse vector. -/
theorem scaleV_oneValue {k : Nat} (v : SVec k) (c d : BPair) (h : c.oneValue d) :
    scaleV c v = scaleV d v := by
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_scaleV m v c)
    (BPair.oneValue_trans (BPair.mul_congr h (BPair.oneValue_refl _))
      (BPair.oneValue_symm (coefAt_scaleV m v d)))

/-- Scaling by one keeps the vector. -/
theorem scaleV_one {k : Nat} (v : SVec k) : scaleV (BPair.ofNat 1) v = v := by
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_scaleV m v (BPair.ofNat 1)) (BPair.ofNat_one_mul _)

/-- Scaling by the sum's unit gives the vacant vector. -/
theorem scaleV_unit {k : Nat} (v : SVec k) : scaleV BPair.unit v = emptyV k := by
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_scaleV m v BPair.unit) (BPair.unit_mul _)

/-- Successive scalings read the scalars' product. -/
theorem scaleV_scale {k : Nat} (v : SVec k) (c d : BPair) :
    scaleV c (scaleV d v) = scaleV (c * d) v := by
  apply eq_of_coefAt
  intro m
  refine BPair.oneValue_trans (coefAt_scaleV m (scaleV d v) c) ?_
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl c) (coefAt_scaleV m v d)) ?_
  rw [← BPair.mul_assoc]
  exact BPair.oneValue_symm (coefAt_scaleV m v (c * d))

/-- Two multiples of one vector add at the scalars' sum. -/
theorem scaleV_add {k : Nat} (v : SVec k) (c d : BPair) :
    addV (scaleV c v) (scaleV d v) = scaleV (c + d) v := by
  apply eq_of_coefAt
  intro m
  refine BPair.oneValue_trans (coefAt_addV m (scaleV c v) (scaleV d v)) ?_
  refine BPair.oneValue_trans (BPair.add_congr (coefAt_scaleV m v c) (coefAt_scaleV m v d)) ?_
  rw [← BPair.right_distrib]
  exact BPair.oneValue_symm (coefAt_scaleV m v (c + d))

/-- The vacant vector is the left unit of sparse addition. -/
theorem addV_empty_left {k : Nat} (v : SVec k) : addV (emptyV k) v = v := by
  apply eq_of_coefAt
  intro m
  exact BPair.oneValue_trans (coefAt_addV m (emptyV k) v) (BPair.unit_add _)

/-- A single-root lowering word at its depth (`lem:strings`),
the repeated simple index read by the existing word fold. -/
def iterLowerT (T : memtable.Table) (sig : List Bool) (i n : Nat)
    (v : SVec sig.length) : SVec sig.length :=
  (List.replicate n i).foldl (fun u j => lowerT T sig j u) v

/-- The next depth is the lowering of the current string member. -/
theorem iterLowerT_succ (T : memtable.Table) (sig : List Bool) (i n : Nat) (v : SVec sig.length) :
    iterLowerT T sig i (n + 1) v = lowerT T sig i (iterLowerT T sig i n v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih (lowerT T sig i v)

/-- Every G2 lowering iterate stays in the generating key carrier. -/
theorem keysRead_iterLowerT_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (hv : keysRead memtable.genG2.keys v) (n : Nat) :
    keysRead memtable.genG2.keys (iterLowerT memtable.genG2 sig i n v) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [iterLowerT_succ]
    exact keysRead_lowerT memtable.genG2 sig i (memtable.genG2_actionKeys i hi).1
      (memtable.genG2_actionKeys i hi).2 _ ih

/-- The weight of a G2 lowering iterate is the initial weight
joined to the depth's multiple of the simple root's partner. -/
theorem homogRead_iterLowerT_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w) (n : Nat) :
    homogRead memtable.genG2 sig (iterLowerT memtable.genG2 sig i n v)
      (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat n)
        (poly.neg (getAt [] sertables.tableG2.cartan i))))) := by
  let T := memtable.genG2
  let d := poly.neg (getAt [] sertables.tableG2.cartan i)
  have hd : d.length = T.rank := by
    unfold d
    rw [poly.length_neg]
    exact elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt sertables.cartanSolve_G2.1)
      (by rw [elim.sqAt_len sertables.cartanSolve_G2.1]; exact hi)
  have hsc (c : BPair) : (elim.vecScale c d).length = T.rank := (elim.length_vecScale c d).trans hd
  have hlen (b : Nat) : (elim.vecAdd w (elim.vecScale (BPair.ofNat b) d)).length = T.rank :=
    elim.length_vecAdd _ _ T.rank hw (hsc _)
  have hzero : poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat 0) d)) = poly.pnorm w :=
    poly.pnorm_congr _ _ ((hlen 0).trans hw.symm)
      (elim.vecAdd_null_right w _ (hw.trans (hsc _).symm)
        (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) d))
  have hstep (b : Nat) :
      poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat b) d))) d)
        = poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat (b + 1)) d)) := by
    rw [elim.pnorm_vecAdd_left _ d ((hlen b).trans hd.symm), elim.vecAdd_assoc]
    have hc := elim.vecScale_congr (BPair.ofNat_add b 1) d
    rw [elim.vecScale_add] at hc
    have hjoin : poly.oneValue (elim.vecAdd (elim.vecScale (BPair.ofNat b) d) d)
        (elim.vecScale (BPair.ofNat (b + 1)) d) :=
      poly.oneValue_trans
        (elim.vecAdd_congr2 _ _ _ _ rfl (hd.trans (hsc _).symm) (poly.oneValue_refl _)
          (poly.oneValue_symm (elim.vecScale_one d)))
        (poly.oneValue_symm hc)
    have hlen' : (elim.vecAdd (elim.vecScale (BPair.ofNat b) d) d).length = T.rank :=
      elim.length_vecAdd _ _ T.rank (hsc _) hd
    apply poly.pnorm_congr
    · exact (elim.length_vecAdd _ _ T.rank hw hlen').trans (hlen (b + 1)).symm
    · exact elim.vecAdd_congr2 w w _ _ rfl (hlen'.trans (hsc _).symm) (poly.oneValue_refl w) hjoin
  induction n with
  | zero =>
    change homogRead T sig v (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat 0) d)))
    rw [hzero]
    apply all_of_mem_intro
    intro p hp
    have he := listBeqEq (all_of_mem _ v.val hh p hp)
    have hn := weightT_pnorm T sig p.1 memtable.genG2_diagonals.1 memtable.genG2_diagonals.2
      (width_of_mem v p hp) (all_of_mem _ v.val hv p hp)
    rw [he] at hn
    rw [hn]
    exact all_of_mem _ v.val hh p hp
  | succ n ih =>
    rw [iterLowerT_succ]
    have hg := homogRead_lowerT_G2 sig i hi (iterLowerT T sig i n v)
      (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat n) d)))
      (keysRead_iterLowerT_G2 sig i hi v hv n) ih
    change homogRead T sig (lowerT T sig i (iterLowerT T sig i n v))
      (poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat n) d))) d)) at hg
    rw [hstep n] at hg
    exact hg

/-- The chosen coroot drops by two per lowering, as an additive
join at every occupied monomial of the iterate. -/
theorem iterLowerT_coroot_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (n : Nat) (p : List Nat × BPair) (hp : p ∈ (iterLowerT memtable.genG2 sig i n v).val) :
    (getAt BPair.unit (weightT memtable.genG2 sig p.1) i + BPair.ofNat (2 * n)).oneValue
      (getAt BPair.unit w i) := by
  let d := poly.neg (getAt [] sertables.tableG2.cartan i)
  have hd : d.length = memtable.genG2.rank := by
    unfold d
    rw [poly.length_neg]
    exact elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt sertables.cartanSolve_G2.1)
      (by rw [elim.sqAt_len sertables.cartanSolve_G2.1]; exact hi)
  have hdiag : (getAt BPair.unit d i).oneValue ((BPair.ofNat 2).swap) := by
    have h : ∀ j, j < 2 → (getAt BPair.unit (poly.neg (getAt [] sertables.tableG2.cartan j)) j).oneValue
        ((BPair.ofNat 2).swap) := by decide +kernel
    exact h i hi
  have hg := listBeqEq (all_of_mem _ _ (homogRead_iterLowerT_G2 sig i hi v w hv hw hh n) p hp)
  rw [hg]
  refine BPair.oneValue_trans (BPair.add_congr
    (poly.oneValue_getAt i (poly.pnorm_oneValue (elim.vecAdd w (elim.vecScale (BPair.ofNat n) d))))
    (BPair.oneValue_refl _)) ?_
  have hiw : i < w.length := by rw [hw]; exact hi
  have hid : i < d.length := by rw [hd]; exact hi
  rw [elim.getAt_vecAdd _ _ i hiw (by rw [elim.length_vecScale]; exact hid),
    elim.getAt_vecScale (BPair.ofNat n) d i hid]
  have hc : (BPair.ofNat n * getAt BPair.unit d i).oneValue ((BPair.ofNat (2 * n)).swap) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hdiag) ?_
    rw [BPair.mul_swap, Nat.mul_comm 2 n]
    exact swap_congr (BPair.oneValue_symm (BPair.ofNat_mul n 2))
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_congr (BPair.oneValue_refl _) hc) (BPair.oneValue_refl _))
    (BPair.add_swap_self _ _)

/-- An occupied G2 top for one simple raising has its chosen
coroot at or above the sum's unit (`lem:tops`(ii)). -/
theorem top_coroot_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (_hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (ho : v.val ≠ []) : BPair.unit ≤ getAt BPair.unit w i := by
  let T := memtable.genG2
  let y := lowerT T sig i v
  let ms := allMon T.keys sig.length
  have hy : keysRead T.keys y := keysRead_lowerT T sig i (memtable.genG2_actionKeys i hi).1
    (memtable.genG2_actionKeys i hi).2 v hv
  have hnonneg : BPair.unit ≤ pairT T true y y :=
    leB_congr_right (pairT_coordsV T ms y y (coordsV_allMon_count T.keys y hy))
      (unitLeOfSide (elim.dotP_self_side (coordsV ms y)))
  have he : raiseT T sig i y = scaleV (getAt BPair.unit w i) v := by
    rw [raiseT_lowerT_G2 sig v w hsig hv hh i i hi hi, if_pos rfl]
    have hz : raiseT T sig i v = emptyV sig.length := Subtype.ext htop
    rw [hz, lowerT_emptyV, addV_empty_left]
  have hscalar : (pairT T true y y).oneValue (getAt BPair.unit w i * pairT T true v v) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm (pairT_raise_lower_G2 sig i hi y v)) ?_
    refine BPair.oneValue_trans (pairT_unit_comm T (raiseT T sig i y) v) ?_
    rw [he]
    exact pairT_unit_scale T v v _
  have hprod := leB_congr_right hscalar hnonneg
  apply leB_of_not_lt
  intro hneg
  have hlt := ltB_mulPos hneg (pairT_self_pos T v ho)
  exact leB_not_lt hprod (BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.unit_mul (pairT T true v v)) hlt)

/-- Raising a simple G2 string member reads its depth coefficient
at the top's natural coroot height (`lem:strings`). -/
theorem iterLowerT_raise_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) :
    ∀ b : Nat, b ≤ h →
      raiseT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i (b + 1) v)
        = scaleV (BPair.ofNat ((b + 1) * (h - b))) (iterLowerT memtable.genG2 sig i b v)
  | 0, _ => by
    change raiseT memtable.genG2 sig i (lowerT memtable.genG2 sig i v)
      = scaleV (BPair.ofNat (1 * h)) v
    rw [Nat.one_mul, raiseT_lowerT_G2 sig v w hsig hv hh i i hi hi, if_pos rfl]
    have hz : raiseT memtable.genG2 sig i v = emptyV sig.length := Subtype.ext htop
    rw [hz, lowerT_emptyV, addV_empty_left]
    exact scaleV_oneValue v _ _ hheight
  | b + 1, hb => by
    let T := memtable.genG2
    let y := iterLowerT T sig i (b + 1) v
    let z := iterLowerT T sig i b v
    let c := (b + 1) * (h - b)
    let c' := (b + 1 + 1) * (h - (b + 1))
    let wy := poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat (b + 1))
      (poly.neg (getAt [] sertables.tableG2.cartan i))))
    rw [iterLowerT_succ T sig i (b + 1) v]
    change raiseT T sig i (lowerT T sig i y) = scaleV (BPair.ofNat c') y
    cases hy : y.val with
    | nil =>
      have he : y = emptyV sig.length := Subtype.ext hy
      rw [he, lowerT_emptyV, raiseT_emptyV]
      rfl
    | cons p ps =>
      have hp : p ∈ y.val := by rw [hy]; exact List.Mem.head ps
      have hhom := homogRead_iterLowerT_G2 sig i hi v w hv hw hh (b + 1)
      have hkey := keysRead_iterLowerT_G2 sig i hi v hv (b + 1)
      have hcur := iterLowerT_coroot_G2 sig i hi v w hv hw hh (b + 1) p hp
      have hweight := listBeqEq (all_of_mem _ y.val hhom p hp)
      change weightT T sig p.1 = wy at hweight
      rw [hweight] at hcur
      have hcur' := BPair.oneValue_trans hcur hheight
      obtain ⟨g, hg⟩ := Nat.le.dest hb
      have hn := ground.coeffCross b g (b + 1)
      rw [hg, ← Nat.two_mul] at hn
      change c + h = c' + 2 * (b + 1) at hn
      have hsum : ((BPair.ofNat c + getAt BPair.unit wy i) + BPair.ofNat (2 * (b + 1))).oneValue
          (BPair.ofNat c + BPair.ofNat h) := by
        rw [BPair.add_assoc]
        exact BPair.add_congr (BPair.oneValue_refl _) hcur'
      have hn' : (BPair.ofNat c' + BPair.ofNat (2 * (b + 1))).oneValue
          (BPair.ofNat c + BPair.ofNat h) :=
        BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofNat_add c' (2 * (b + 1))))
          (BPair.oneValue_trans (BPair.oneValue_of_eq (congrArg BPair.ofNat hn.symm))
            (BPair.ofNat_add c h))
      have hcoeff : (BPair.ofNat c + getAt BPair.unit wy i).oneValue (BPair.ofNat c') :=
        BPair.add_cancel (BPair.oneValue_trans hsum (BPair.oneValue_symm hn'))
      have hr : raiseT T sig i y = scaleV (BPair.ofNat c) z :=
        iterLowerT_raise_G2 sig i hi v w hv hw hh hsig htop h hheight b (Nat.le_of_succ_le hb)
      have hzy : lowerT T sig i z = y := (iterLowerT_succ T sig i b v).symm
      rw [raiseT_lowerT_G2 sig y wy hsig hkey hhom i i hi hi, if_pos rfl,
        hr, lowerT_scaleV, hzy, scaleV_add]
      exact scaleV_oneValue y _ _ hcoeff

/-- The G2 string terminates immediately beyond its top's natural
coroot height, at the positive unit pairing. -/
theorem iterLowerT_term_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) :
    iterLowerT memtable.genG2 sig i (h + 1) v = emptyV sig.length := by
  let T := memtable.genG2
  let y := iterLowerT T sig i h v
  let z := iterLowerT T sig i (h + 1) v
  have hz : raiseT T sig i z = emptyV sig.length := by
    have he := iterLowerT_raise_G2 sig i hi v w hv hw hh hsig htop h hheight h (Nat.le_refl h)
    rw [Nat.sub_self, Nat.mul_zero] at he
    exact he.trans ((scaleV_oneValue y _ _ BPair.ofNat_zero).trans (scaleV_unit y))
  have hpair := pairT_raise_lower_G2 sig i hi z y
  have hzy : lowerT T sig i y = z := (iterLowerT_succ T sig i h v).symm
  rw [hz, hzy] at hpair
  have hnull : (pairT T true z z).oneValue BPair.unit :=
    BPair.oneValue_trans (BPair.oneValue_symm hpair)
      (BPair.oneValue_trans (pairT_unit_comm T _ y) (pairT_unit_empty T y))
  by_cases he : z.val = []
  · exact Subtype.ext he
  · exact False.elim (offOfUnitLt (pairT_self_pos T z he) hnull)

/-- Pairing two equally deep lowering iterates reads the first
string's coefficient product against the seed pairing. -/
theorem iterLowerT_pair_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (z : SVec sig.length) : ∀ b : Nat, b ≤ h →
      (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig i b v)
        (iterLowerT memtable.genG2 sig i b z)).oneValue
        (BPair.ofNat (strings.coeffProd h b) * pairT memtable.genG2 true v z)
  | 0, _ => BPair.oneValue_symm (BPair.ofNat_one_mul _)
  | b + 1, hb => by
    let T := memtable.genG2
    let x := iterLowerT T sig i b v
    let y := iterLowerT T sig i (b + 1) v
    let u := iterLowerT T sig i b z
    let c := (b + 1) * (h - b)
    rw [iterLowerT_succ T sig i b z]
    refine BPair.oneValue_trans (BPair.oneValue_symm (pairT_raise_lower_G2 sig i hi y u)) ?_
    rw [iterLowerT_raise_G2 sig i hi v w hv hw hh hsig htop h hheight b (Nat.le_of_succ_le hb)]
    refine BPair.oneValue_trans (pairT_unit_comm T (scaleV (BPair.ofNat c) x) u) ?_
    refine BPair.oneValue_trans (pairT_unit_scale T u x (BPair.ofNat c)) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (pairT_unit_comm T u x)) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (iterLowerT_pair_G2 sig i hi v w hv hw hh hsig htop h hheight z b (Nat.le_of_succ_le hb))) ?_
    rw [← BPair.mul_assoc]
    apply BPair.mul_congr
    · rw [BPair.mul_comm]
      exact BPair.oneValue_symm (BPair.ofNat_mul (strings.coeffProd h b) c)
    · exact BPair.oneValue_refl _

/-- A simple G2 string's self-pairings telescope at the existing
string coefficient product. -/
theorem iterLowerT_selfpair_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) :
    ∀ b : Nat, b ≤ h →
      (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig i b v)
        (iterLowerT memtable.genG2 sig i b v)).oneValue
        (BPair.ofNat (strings.coeffProd h b) * pairT memtable.genG2 true v v)
  := fun b hb => iterLowerT_pair_G2 sig i hi v w hv hw hh hsig htop h hheight v b hb

/-- Every depth through the natural height is occupied at an
occupied G2 string top. -/
theorem iterLowerT_occupied_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (ho : v.val ≠ []) (b : Nat) (hb : b ≤ h) :
    (iterLowerT memtable.genG2 sig i b v).val ≠ [] := by
  intro he
  have hz : iterLowerT memtable.genG2 sig i b v = emptyV sig.length := Subtype.ext he
  have hp := iterLowerT_selfpair_G2 sig i hi v w hv hw hh hsig htop h hheight b hb
  rw [hz] at hp
  have hn := BPair.oneValue_trans (BPair.oneValue_symm hp) (pairT_unit_empty memtable.genG2 _)
  exact offOfUnitLt (pairT_self_pos memtable.genG2 v ho)
    (mul_cancel_unit (BPair.ofNat_off_unit _ (strings.coeffProd_pos h b hb)) hn)

/-- The two ordered G2 string words read their depth coefficients,
the diagonal data for the string trace fold (`lem:casimir`). -/
theorem iterLowerT_trace_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (b : Nat) (hb : b ≤ h) :
    raiseT memtable.genG2 sig i (lowerT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i b v))
      = scaleV (BPair.ofNat ((b + 1) * (h - b))) (iterLowerT memtable.genG2 sig i b v) ∧
    lowerT memtable.genG2 sig i (raiseT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i b v))
      = scaleV (BPair.ofNat (b * (h + 1 - b))) (iterLowerT memtable.genG2 sig i b v) := by
  constructor
  · rw [← iterLowerT_succ]
    exact iterLowerT_raise_G2 sig i hi v w hv hw hh hsig htop h hheight b hb
  · cases b with
    | zero =>
      rw [Nat.zero_mul]
      change lowerT memtable.genG2 sig i (raiseT memtable.genG2 sig i v) = scaleV (BPair.ofNat 0) v
      have hz : raiseT memtable.genG2 sig i v = emptyV sig.length := Subtype.ext htop
      rw [hz, lowerT_emptyV, scaleV_oneValue v _ _ BPair.ofNat_zero, scaleV_unit]
    | succ b =>
      rw [iterLowerT_raise_G2 sig i hi v w hv hw hh hsig htop h hheight b (Nat.le_of_succ_le hb),
        lowerT_scaleV, ← iterLowerT_succ, Nat.succ_sub_succ]

/-- Distinct depths of a homogeneous G2 lowering word are
perpendicular, including depths whose vectors are vacant. -/
theorem iterLowerT_perp_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (a b : Nat) (hab : a ≠ b) :
    (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig i a v)
      (iterLowerT memtable.genG2 sig i b v)).oneValue BPair.unit := by
  let T := memtable.genG2
  let L := fun n => iterLowerT T sig i n v
  let W := fun n => poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat n)
    (poly.neg (getAt [] sertables.tableG2.cartan i))))
  have ha := homogRead_iterLowerT_G2 sig i hi v w hv hw hh a
  have hb := homogRead_iterLowerT_G2 sig i hi v w hv hw hh b
  cases hla : (L a).val with
  | nil =>
    have he : L a = emptyV sig.length := Subtype.ext hla
    change (pairT T true (L a) (L b)).oneValue BPair.unit
    rw [he]
    exact BPair.oneValue_trans (pairT_unit_comm T _ _) (pairT_unit_empty T _)
  | cons p ps =>
    cases hlb : (L b).val with
    | nil =>
      have he : L b = emptyV sig.length := Subtype.ext hlb
      change (pairT T true (L a) (L b)).oneValue BPair.unit
      rw [he]
      exact pairT_unit_empty T _
    | cons q qs =>
      have hp : p ∈ (L a).val := by rw [hla]; exact List.Mem.head ps
      have hq : q ∈ (L b).val := by rw [hlb]; exact List.Mem.head qs
      apply pairT_homog_perp T sig (L a) (L b) (W a) (W b) ha hb
      intro he
      have hpa := iterLowerT_coroot_G2 sig i hi v w hv hw hh a p hp
      have hqb := iterLowerT_coroot_G2 sig i hi v w hv hw hh b q hq
      have hwa := listBeqEq (all_of_mem _ (L a).val ha p hp)
      have hwb := listBeqEq (all_of_mem _ (L b).val hb q hq)
      change weightT T sig p.1 = W a at hwa
      change weightT T sig q.1 = W b at hwb
      rw [hwa, he] at hpa
      rw [hwb] at hqb
      have hc := BPair.oneValue_trans hpa (BPair.oneValue_symm hqb)
      rw [BPair.add_comm (getAt BPair.unit (W b) i) (BPair.ofNat (2 * a)),
        BPair.add_comm (getAt BPair.unit (W b) i) (BPair.ofNat (2 * b))] at hc
      exact hab (Nat.eq_of_mul_eq_mul_left (by decide +kernel) (BPair.ofNat_inj (BPair.add_cancel hc)))

/-- Lowering iterates of any member of the actual G2 block span
stay in that span at every depth. -/
theorem iterLowerT_span_G2 (sig : List Bool) (top v : SVec sig.length)
    (hsig : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hv : keysRead memtable.genG2.keys v) (i : Nat) (hi : i < memtable.genG2.rank)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) v)) (n : Nat) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i n v)) := by
  induction n with
  | zero => exact hspan
  | succ n ih =>
    rw [iterLowerT_succ]
    exact blockSpanT_lower_span_G2 sig top _ hsig ht
      (keysRead_iterLowerT_G2 sig i hi v hv n) i hi ih

/-- Every iterate beyond the G2 string's terminal depth is vacant. -/
theorem iterLowerT_past_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (extra : Nat) :
    iterLowerT memtable.genG2 sig i (h + 1 + extra) v = emptyV sig.length := by
  induction extra with
  | zero => exact iterLowerT_term_G2 sig i hi v w hv hw hh hsig htop h hheight
  | succ n ih =>
    rw [← Nat.add_assoc, iterLowerT_succ, ih, lowerT_emptyV]

/-- The finite G2 string is independent on the actual monomial
carrier, its occupied depths pairwise perpendicular. -/
theorem iterLowerT_indep_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (ho : v.val ≠ []) :
    elim.indepRows (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length)
        (iterLowerT memtable.genG2 sig i b v))) := by
  let T := memtable.genG2
  let ms := allMon T.keys sig.length
  let L := fun b => iterLowerT T sig i b v
  let rows := (List.range (h + 1)).map (fun b => coordsV ms (L b))
  have hlen : rows.length = h + 1 := (length_map _ _).trans (length_range _)
  have hrow (b : Nat) (hb : b < rows.length) : getAt [] rows b = coordsV ms (L b) := by
    have hbr : b < (List.range (h + 1)).length := by rw [length_range]; rw [hlen] at hb; exact hb
    change getAt [] ((List.range (h + 1)).map (fun b => coordsV ms (L b))) b = _
    rw [getAt_map 0 [] _ _ b hbr, getAt_range (h + 1) b (by rw [hlen] at hb; exact hb)]
  apply elim.indep_of_orth ms.length rows
  · exact elim.rowsLen_map _ _ _ (fun _ _ => length_map _ ms)
  · intro a b ha hb hab
    rw [hrow a ha, hrow b hb]
    exact BPair.oneValue_trans (pairT_coordsV T ms (L a) (L b)
      (coordsV_allMon_count T.keys (L a) (keysRead_iterLowerT_G2 sig i hi v hv a)))
      (iterLowerT_perp_G2 sig i hi v w hv hw hh a b hab)
  · intro b hb hz
    rw [hrow b hb] at hz
    have hble : b ≤ h := Nat.le_of_lt_succ (by rw [hlen] at hb; exact hb)
    have hp := pairT_coordsV T ms (L b) (L b)
      (coordsV_allMon_count T.keys (L b) (keysRead_iterLowerT_G2 sig i hi v hv b))
    have hn := elim.dotP_null_tail_right (coordsV ms (L b)) (coordsV ms (L b)) hz
    exact offOfUnitLt (pairT_self_pos T (L b)
      (iterLowerT_occupied_G2 sig i hi v w hv hw hh hsig htop h hheight ho b hble))
      (BPair.oneValue_trans (BPair.oneValue_symm hp) hn)

/-- A G2 string's height successor is at most its finite
monomial-coordinate count. -/
theorem iterLowerT_length_le_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (ho : v.val ≠ []) :
    h + 1 ≤ (allMon memtable.genG2.keys sig.length).length := by
  have hind := iterLowerT_indep_G2 sig i hi v w hv hw hh hsig htop h hheight ho
  have hb := elim.indep_bound _ _ hind.1 hind
  rw [length_map, length_range] at hb
  exact hb

/-- The chosen raising preserves every vector in its finite
G2 string's span. -/
theorem iterLowerT_raise_span_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (u : SVec sig.length) (hu : keysRead memtable.genG2.keys u)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length)
        (iterLowerT memtable.genG2 sig i b v))) (coordsV (allMon memtable.genG2.keys sig.length) u)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length)
        (iterLowerT memtable.genG2 sig i b v)))
      (coordsV (allMon memtable.genG2.keys sig.length) (raiseT memtable.genG2 sig i u)) := by
  let T := memtable.genG2
  let ms := allMon T.keys sig.length
  let L := fun b => iterLowerT T sig i b v
  let pool := (List.range (h + 1)).map L
  have hkeys : ∀ x ∈ pool, keysRead T.keys x := by
    intro x hx
    obtain ⟨b, _, he⟩ := mem_map_of L (List.range (h + 1)) x hx
    rw [← he]
    exact keysRead_iterLowerT_G2 sig i hi v hv b
  have hrows := coordsV_rows ms pool
  have hsp : elim.spanRel ms.length (pool.map (coordsV ms)) (coordsV ms u) := by
    rw [map_map]
    exact hspan
  have hread := raiseT_span T sig T.keys i pool u hkeys hu (by
    intro x hx
    obtain ⟨b, hb, he⟩ := mem_map_of L (List.range (h + 1)) x hx
    rw [← he]
    have hb' := ltOfMemRange hb
    cases b with
    | zero =>
      have hz : raiseT T sig i (L 0) = emptyV sig.length := Subtype.ext htop
      rw [hz, coordsV_empty]
      exact elim.spanRel_null _ _ _ (poly.unitTail_replicate _)
        hrows (length_replicate BPair.unit _)
    | succ b =>
      have hb0 : b ≤ h := Nat.le_of_succ_le (Nat.le_of_lt_succ hb')
      rw [iterLowerT_raise_G2 sig i hi v w hv hw hh hsig htop h hheight b hb0]
      exact elim.spanRel_congr _ _ _ _ (poly.oneValue_symm (coordsV_scaleV _ _ ms))
        (elim.spanRel_scale _ _ _ _ hrows (length_map _ ms)
          (elim.spanRel_of_mem _ _ _ hrows (mem_map_to (coordsV ms)
            (mem_map_to L (memRange (Nat.lt_succ_of_le hb0))))))
        (length_map _ ms)) hsp
  rw [map_map] at hread
  exact hread

/-- The chosen lowering preserves every vector in its finite
G2 string's span, with the last member mapping to the vacant vector. -/
theorem iterLowerT_lower_span_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (u : SVec sig.length) (hu : keysRead memtable.genG2.keys u)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length)
        (iterLowerT memtable.genG2 sig i b v))) (coordsV (allMon memtable.genG2.keys sig.length) u)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length)
        (iterLowerT memtable.genG2 sig i b v)))
      (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i u)) := by
  let T := memtable.genG2
  let ms := allMon T.keys sig.length
  let L := fun b => iterLowerT T sig i b v
  let pool := (List.range (h + 1)).map L
  have hkeys : ∀ x ∈ pool, keysRead T.keys x := by
    intro x hx
    obtain ⟨b, _, he⟩ := mem_map_of L (List.range (h + 1)) x hx
    rw [← he]
    exact keysRead_iterLowerT_G2 sig i hi v hv b
  have hrows := coordsV_rows ms pool
  have hsp : elim.spanRel ms.length (pool.map (coordsV ms)) (coordsV ms u) := by
    rw [map_map]
    exact hspan
  have hread := lowerT_span T sig T.keys i pool u hkeys hu (by
    intro x hx
    obtain ⟨b, hb, he⟩ := mem_map_of L (List.range (h + 1)) x hx
    rw [← he, ← iterLowerT_succ]
    have hb' : b ≤ h := Nat.le_of_lt_succ (ltOfMemRange hb)
    cases Nat.lt_or_ge b h with
    | inl hlt =>
      exact elim.spanRel_of_mem _ _ _ hrows (mem_map_to (coordsV ms)
        (mem_map_to L (memRange (Nat.succ_lt_succ hlt))))
    | inr hge =>
      have heq := Nat.le_antisymm hb' hge
      rw [heq, iterLowerT_past_G2 sig i hi v w hv hw hh hsig htop h hheight 0, coordsV_empty]
      exact elim.spanRel_null _ _ _ (poly.unitTail_replicate _)
        hrows (length_replicate BPair.unit _)) hsp
  rw [map_map] at hread
  exact hread

/-- Complementary depths in an occupied G2 string have weights
related by the member table's actual simple reflection. -/
theorem iterLowerT_reflect_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hsig : sig.all (fun b => !b) = true) (htop : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hheight : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (ho : v.val ≠ []) (b : Nat) (hb : b ≤ h) :
    weightV memtable.genG2 sig (iterLowerT memtable.genG2 sig i (h - b) v) =
      sertables.reflAt sertables.tableG2 i (weightV memtable.genG2 sig
        (iterLowerT memtable.genG2 sig i b v)) := by
  let T := memtable.genG2
  let d := poly.neg (getAt [] sertables.tableG2.cartan i)
  let L := fun n => iterLowerT T sig i n v
  let W := fun n => poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat n) d))
  have hrowlen : (getAt [] sertables.tableG2.cartan i).length = T.rank :=
    elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt sertables.cartanSolve_G2.1)
      (by rw [elim.sqAt_len sertables.cartanSolve_G2.1]; exact hi)
  have hd : d.length = T.rank := (poly.length_neg _).trans hrowlen
  have hsc (a : BPair) : (elim.vecScale a d).length = T.rank := (elim.length_vecScale a d).trans hd
  have hraw (n : Nat) : (elim.vecAdd w (elim.vecScale (BPair.ofNat n) d)).length = T.rank :=
    elim.length_vecAdd _ _ T.rank hw (hsc _)
  have hW (n : Nat) : (W n).length = T.rank := (poly.pnorm_length _).trans (hraw n)
  have hweight (n : Nat) (hn : n ≤ h) : weightV T sig (L n) = W n :=
    weightV_homog T sig (L n) (W n) (homogRead_iterLowerT_G2 sig i hi v w hv hw hh n)
      (iterLowerT_occupied_G2 sig i hi v w hv hw hh hsig htop h hheight ho n hn)
  have hcor : (getAt BPair.unit (W b) i + BPair.ofNat (2 * b)).oneValue (BPair.ofNat h) := by
    have hob := iterLowerT_occupied_G2 sig i hi v w hv hw hh hsig htop h hheight ho b hb
    cases he : (L b).val with
    | nil => exact False.elim (hob he)
    | cons p ps =>
      have hp : p ∈ (L b).val := by rw [he]; exact List.Mem.head ps
      have hg := listBeqEq (all_of_mem _ _ (homogRead_iterLowerT_G2 sig i hi v w hv hw hh b) p hp)
      have hc := iterLowerT_coroot_G2 sig i hi v w hv hw hh b p hp
      rw [hg] at hc
      exact BPair.oneValue_trans hc hheight
  let a := getAt BPair.unit (W b) i
  have hsum : ((BPair.ofNat b + a) + BPair.ofNat b).oneValue (BPair.ofNat h) := by
    rw [BPair.add_comm (BPair.ofNat b) a, BPair.add_assoc]
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl a)
      (BPair.oneValue_symm (BPair.ofNat_add b b))) ?_
    rw [← Nat.two_mul]
    exact hcor
  have hjoin : (BPair.ofNat (h - b) + BPair.ofNat b).oneValue (BPair.ofNat h) :=
    BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofNat_add (h - b) b))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (subAdd hb)))
  have hc : (BPair.ofNat b + a).oneValue (BPair.ofNat (h - b)) :=
    BPair.add_cancel (BPair.oneValue_trans hsum (BPair.oneValue_symm hjoin))
  have hrow : assembly.cartRowV sertables.tableG2 i = getAt [] sertables.tableG2.cartan i :=
    range_map_getAt BPair.unit T.rank _ hrowlen
  rw [hweight (h - b) (Nat.sub_le h b), hweight b hb,
    ← assembly.reflF_eq sertables.tableG2 i (W b) (hW b)]
  unfold assembly.reflF
  rw [hrow]
  change poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat (h - b)) d)) =
    poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat b) d)))
      (elim.vecScale a d))
  rw [elim.pnorm_vecAdd_left _ _ ((hraw b).trans (hsc a).symm),
    elim.vecAdd_assoc, ← elim.vecScale_add]
  apply poly.pnorm_congr
  · exact (hraw (h - b)).trans (elim.length_vecAdd _ _ T.rank hw (hsc _)).symm
  · exact elim.vecAdd_congr2 w w _ _ rfl ((hsc _).trans (hsc _).symm)
      (poly.oneValue_refl w) (elim.vecScale_congr (BPair.oneValue_symm hc) d)

/-- The determinant-scaled residual at the sparse Gram, the
cleared vector joined to the adjugate combination's partner
(`lem:lowerspan`; `lem:strings`). -/
def residT (T : memtable.Table) {k : Nat} (pool : List (SVec k)) (v : SVec k) : SVec k :=
  let G := gramT T pool
  let cs := elim.adjD G (pool.map (fun u => pairT T (unitWtRead T) u v))
  addV (scaleV (elim.detD G) v)
    (scaleV ((BPair.ofNat 1).swap) (comboV pool cs))

/-- The sparse residual keeps the keys of its seed and pool. -/
theorem keysRead_residT (T : memtable.Table) (d : Nat) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead d u) (hv : keysRead d v) :
    keysRead d (residT T pool v) :=
  keysRead_addV d _ _ (keysRead_scaleV d _ v hv)
    (keysRead_scaleV d _ _ (keysRead_comboV d pool _ hp))

/-- A homogeneous seed's residual at a pool of its own weight
is homogeneous at that weight. -/
theorem homogRead_residT (T : memtable.Table) (sig : List Bool) {k : Nat}
    (pool : List (SVec k)) (v : SVec k) (w : List BPair)
    (hp : ∀ u ∈ pool, homogRead T sig u w) (hv : homogRead T sig v w) :
    homogRead T sig (residT T pool v) w := by
  have hc : ∀ (P : List (SVec k)) (cs : List BPair),
      (∀ u ∈ P, homogRead T sig u w) → homogRead T sig (comboV P cs) w := by
    intro P
    induction P with
    | nil => intro cs _; rw [comboV_nil]; rfl
    | cons u P ih =>
      intro cs hP
      cases cs with
      | nil => rw [comboV_nil_coeffs]; rfl
      | cons c cs =>
        rw [comboV_cons]
        exact homogRead_addV T sig _ _ w (homogRead_scaleV T sig c u w (hP u (List.Mem.head P)))
          (ih cs (fun z hz => hP z (List.Mem.tail u hz)))
  exact homogRead_addV T sig _ _ w (homogRead_scaleV T sig _ v w hv)
    (homogRead_scaleV T sig _ _ w (hc pool _ hp))

/-- The sparse residual's finite coordinates read the existing
elimination residual at an independent pool and the unit pairing. -/
theorem coordsV_residT (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (_hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k)))) :
    poly.oneValue (coordsV (allMon T.keys k) (residT T pool v))
      (elim.residW (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k)))
        (coordsV (allMon T.keys k) v)) := by
  let ms := allMon T.keys k
  let rows := pool.map (coordsV ms)
  let G := gramT T pool
  let H := elim.gramM rows
  let p := pool.map (fun u => pairT T true u v)
  let q := rows.map (fun r => elim.dotP r (coordsV ms v))
  have hGread : G = elim.gramBy (pairT T true) pool := by
    change gramT T pool = _
    rw [gramT_eq, hunit]
  have hGl : G.length = pool.length := (congrArg List.length hGread).trans (elim.length_gramBy _ _)
  have hHl : H.length = pool.length := (elim.length_gramBy _ _).trans (length_map _ _)
  have hGH : G.length = H.length := hGl.trans hHl.symm
  have hG : elim.rowsLen G.length G := by rw [hGread]; exact elim.gramBy_sq _ _
  have hH : elim.rowsLen H.length H := elim.gramM_sq rows
  have hrows : elim.rowsLen ms.length rows := coordsV_rows ms pool
  have hpLen : p.length = G.length := (length_map _ _).trans hGl.symm
  have hqLen : q.length = H.length := (length_map _ rows).trans (elim.length_gramBy _ rows).symm
  have hpair (u z : SVec k) (hu : u ∈ pool) :
      (pairT T true u z).oneValue (elim.dotP (coordsV ms u) (coordsV ms z)) :=
    BPair.oneValue_symm (pairT_coordsV T ms u z (coordsV_allMon_count T.keys u (hp u hu)))
  have hent : ∀ a, a < G.length → ∀ b, b < G.length →
      (getAt BPair.unit (getAt [] G a) b).oneValue (getAt BPair.unit (getAt [] H a) b) := by
    intro a ha b hb
    have haP : a < pool.length := by rw [← hGl]; exact ha
    have hbP : b < pool.length := by rw [← hGl]; exact hb
    have haR : a < rows.length := by rw [length_map]; exact haP
    have hbR : b < rows.length := by rw [length_map]; exact hbP
    rw [hGread, elim.gramBy_entry _ (emptyV k) pool a b haP hbP,
      elim.gramM_entry rows a b haR hbR,
      getAt_map (emptyV k) [] (coordsV ms) pool a haP,
      getAt_map (emptyV k) [] (coordsV ms) pool b hbP]
    exact hpair _ _ (mem_getAt (emptyV k) pool a haP)
  have hdet : (elim.detL G).oneValue (elim.detL H) := elim.detL_congr_letters G H hGH hent
  have hleadH : ∀ j, j < H.length → ¬ (elim.leadMinor H (j + 1)).oneValue BPair.unit := by
    intro j hj
    apply elim.gram_leadMinor ms.length rows hind j
    change j < (elim.gramBy elim.dotP rows).length at hj
    rw [elim.length_gramBy] at hj
    exact hj
  have hleadG : ∀ j, j < G.length → ¬ (elim.leadMinor G (j + 1)).oneValue BPair.unit := by
    intro j hj hz
    exact hleadH j (by rw [← hGH]; exact hj)
      (BPair.oneValue_trans (BPair.oneValue_symm (elim.leadMinor_congr G H hGH hent (j + 1) hj)) hz)
  have hpq : poly.oneValue p q := by
    change poly.oneValue (pool.map (fun u => pairT T true u v))
      ((pool.map (coordsV ms)).map (fun r => elim.dotP r (coordsV ms v)))
    rw [map_map]
    apply poly.oneValue_of_entries
    · rw [length_map, length_map]
    · intro j hj
      rw [length_map] at hj
      rw [getAt_map (emptyV k) BPair.unit _ pool j hj,
        getAt_map (emptyV k) BPair.unit _ pool j hj]
      exact hpair _ _ (mem_getAt (emptyV k) pool j hj)
  have hcs : poly.oneValue (elim.adjD G p) (elim.adjD H q) := by
    apply elim.matVec_inj H hH (elim.indep_det _ _ hind)
      _ _ ((elim.length_adjD _ _).trans hGH) (elim.length_adjD _ _)
    refine poly.oneValue_trans (poly.oneValue_symm
      (elim.matVec_rows_congr G.length G H hGH hG (elim.rowsLen_cast hGH.symm hH) hent _)) ?_
    refine poly.oneValue_trans (elim.adjD_matVec G hG hleadG p hpLen) ?_
    refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _ hpq) ?_
    refine poly.oneValue_trans (elim.vecScale_congr hdet q) ?_
    exact poly.oneValue_symm (elim.adjD_matVec H hH hleadH q hqLen)
  have hdetD : (elim.detD G).oneValue (elim.detD H) :=
    BPair.oneValue_trans (elim.detD_eq G hG)
      (BPair.oneValue_trans hdet (BPair.oneValue_symm (elim.detD_eq H hH)))
  have hcombo : poly.oneValue (coordsV ms (comboV pool (elim.adjD G p)))
      (elim.combo ms.length (elim.adjD H q) rows) :=
    poly.oneValue_trans (coordsV_comboV ms pool _)
      (elim.combo_congr ms.length _ _ rows
        ((elim.length_adjD _ _).trans (hGH.trans (elim.length_adjD _ _).symm)) hcs)
  have hswap : ∀ a : List BPair,
      poly.oneValue (elim.vecScale ((BPair.ofNat 1).swap) a) (poly.neg a) := by
    intro a
    induction a with
    | nil => trivial
    | cons x xs ih =>
      exact ⟨BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.swap_mul _ _))
        (swap_congr (BPair.ofNat_one_mul x)), ih⟩
  unfold residT
  rw [hunit]
  refine poly.oneValue_trans (coordsV_addV _ _ ms) ?_
  refine poly.oneValue_trans ?_ (poly.oneValue_symm (poly.pnorm_oneValue _))
  change poly.oneValue (elim.vecAdd (coordsV ms (scaleV (elim.detD G) v))
    (coordsV ms (scaleV ((BPair.ofNat 1).swap) (comboV pool (elim.adjD G p)))))
    (elim.vecAdd (elim.vecScale (elim.detD H) (coordsV ms v))
      (poly.neg (elim.combo ms.length (elim.adjD H q) rows)))
  apply elim.vecAdd_congr2
  · unfold coordsV
    rw [length_map, elim.length_vecScale, length_map]
  · unfold coordsV
    rw [length_map, poly.length_neg, elim.length_combo _ _ _ hrows]
  · exact poly.oneValue_trans (coordsV_scaleV v _ ms) (elim.vecScale_congr hdetD _)
  · exact poly.oneValue_trans (coordsV_scaleV _ _ ms)
      (poly.oneValue_trans (elim.vecScale_oneValue _ _ _ hcombo) (hswap _))

/-- A sparse vector perpendicular to a pool pairs every member
of its coordinate span at the sum's unit. -/
theorem pairT_span_unit (T : memtable.Table) (d : Nat) {k : Nat}
    (pool : List (SVec k)) (x y : SVec k) (hx : keysRead d x)
    (hperp : ∀ u ∈ pool, (pairT T true x u).oneValue BPair.unit)
    (hspan : elim.spanRel (allMon d k).length (pool.map (coordsV (allMon d k)))
      (coordsV (allMon d k) y)) : (pairT T true x y).oneValue BPair.unit := by
  let ms := allMon d k
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (pairT_coordsV T ms x y (coordsV_allMon_count d x hx))) ?_
  apply elim.perp_span ms.length (pool.map (coordsV ms)) (coordsV ms x) (coordsV ms y)
    (coordsV_rows ms pool) (length_map _ ms) _ hspan
  intro j hj
  have hjP : j < pool.length := by rw [length_map] at hj; exact hj
  rw [getAt_map (emptyV k) [] (coordsV ms) pool j hjP]
  exact BPair.oneValue_trans (pairT_coordsV T ms x _ (coordsV_allMon_count d x hx))
    (hperp _ (mem_getAt (emptyV k) pool j hjP))

/-- The sparse residual is perpendicular to every member of its
independent pool at the unit pairing. -/
theorem residT_perp (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k))))
    (u : SVec k) (hu : u ∈ pool) :
    (pairT T true u (residT T pool v)).oneValue BPair.unit := by
  let ms := allMon T.keys k
  obtain ⟨j, hj, he⟩ := getAt_of_mem (emptyV k) hu
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (pairT_coordsV T ms u _ (coordsV_allMon_count T.keys u (hp u hu)))) ?_
  refine BPair.oneValue_trans (elim.dotP_oneValue_right _ _ _ (coordsV_residT T hunit pool v hp hv hind)) ?_
  have h := elim.residW_perp ms.length (pool.map (coordsV ms)) (coordsV ms v)
    (coordsV_rows ms pool) (length_map _ ms) j (by rw [length_map]; exact hj)
  rw [getAt_map (emptyV k) [] (coordsV ms) pool j hj, he] at h
  exact h

/-- The residual of a vector and pool inside a stated coordinate
span stays in that span. -/
theorem residT_span (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k))))
    (base : List (SVec k))
    (hpool : ∀ u ∈ pool, elim.spanRel (allMon T.keys k).length
      (base.map (coordsV (allMon T.keys k))) (coordsV (allMon T.keys k) u))
    (hvspan : elim.spanRel (allMon T.keys k).length
      (base.map (coordsV (allMon T.keys k))) (coordsV (allMon T.keys k) v)) :
    elim.spanRel (allMon T.keys k).length (base.map (coordsV (allMon T.keys k)))
      (coordsV (allMon T.keys k) (residT T pool v)) := by
  let ms := allMon T.keys k
  apply elim.spanRel_congr ms.length (base.map (coordsV ms)) _ _
    (poly.oneValue_symm (coordsV_residT T hunit pool v hp hv hind)) _ (length_map _ ms)
  apply elim.spanRel_residW ms.length (pool.map (coordsV ms)) (base.map (coordsV ms))
    (coordsV ms v) (coordsV_rows ms pool) (length_map _ ms) (coordsV_rows ms base) _ hvspan
  intro j hj
  have hjP : j < pool.length := by rw [length_map] at hj; exact hj
  rw [getAt_map (emptyV k) [] (coordsV ms) pool j hjP]
  exact hpool _ (mem_getAt (emptyV k) pool j hjP)

/-- A refused span member gives an occupied residual and extends
the independent pool by that residual. -/
theorem residT_refuse (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k))))
    (hnot : ¬ elim.spanRel (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k)))
      (coordsV (allMon T.keys k) v)) :
    (residT T pool v).val ≠ [] ∧
    elim.indepRows (allMon T.keys k).length
      ((pool ++ [residT T pool v]).map (coordsV (allMon T.keys k))) := by
  let ms := allMon T.keys k
  let R := residT T pool v
  have hrows := coordsV_rows ms pool
  have hc := coordsV_residT T hunit pool v hp hv hind
  have hoff : ¬ poly.unitTail (coordsV ms R) := by
    intro hz
    have hw := poly.unitTail_oneValue_right hz hc
    have hr := poly.unitTail_oneValue_right hw
      (elim.residW_eq ms.length (pool.map (coordsV ms)) (coordsV ms v) hrows)
    exact hnot (elim.resid_sound _ _ _ hrows (length_map _ ms) (elim.indep_det _ _ hind) hr)
  have ho : R.val ≠ [] := by
    intro hz
    have he : R = emptyV k := Subtype.ext hz
    apply hoff
    rw [he, coordsV_empty]
    exact poly.unitTail_replicate _
  refine ⟨ho, ?_⟩
  rw [map_append]
  apply elim.indep_extend ms.length (pool.map (coordsV ms)) (coordsV ms R)
    hrows (length_map _ ms) hind
  intro hsp
  have hpR : ∀ u ∈ pool, (pairT T true R u).oneValue BPair.unit := fun u hu =>
    BPair.oneValue_trans (pairT_unit_comm T R u) (residT_perp T hunit pool v hp hv hind u hu)
  exact offOfUnitLt (pairT_self_pos T R ho)
    (pairT_span_unit T T.keys pool R R (keysRead_residT T T.keys pool v hp hv) hpR hsp)

/-- The residual's raising is vacant when its image belongs to
the processed group and that group's lowerings lie in the collected
span, the transpose argument of `lem:strings`. -/
theorem residT_raise_G2 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (pool above : List (SVec sig.length)) (v : SVec sig.length)
    (hp : ∀ u ∈ pool, keysRead memtable.genG2.keys u)
    (_ha : ∀ u ∈ above, keysRead memtable.genG2.keys u)
    (hv : keysRead memtable.genG2.keys v)
    (hind : elim.indepRows (allMon memtable.genG2.keys sig.length).length
      (pool.map (coordsV (allMon memtable.genG2.keys sig.length))))
    (hraise : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      (above.map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length)
        (raiseT memtable.genG2 sig i (residT memtable.genG2 pool v))))
    (hlower : ∀ u ∈ above,
      elim.spanRel (allMon memtable.genG2.keys sig.length).length
        (pool.map (coordsV (allMon memtable.genG2.keys sig.length)))
        (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i u))) :
    raiseT memtable.genG2 sig i (residT memtable.genG2 pool v) = emptyV sig.length := by
  let T := memtable.genG2
  let R := residT T pool v
  let y := raiseT T sig i R
  have hunit : unitWtRead T = true := by decide +kernel
  have hR := keysRead_residT T T.keys pool v hp hv
  have hy : keysRead T.keys y := keysRead_raiseT T sig i
    (memtable.genG2_actionKeys i hi).1 (memtable.genG2_actionKeys i hi).2 R hR
  have hperp : ∀ u ∈ pool, (pairT T true R u).oneValue BPair.unit := fun u hu =>
    BPair.oneValue_trans (pairT_unit_comm T R u) (residT_perp T hunit pool v hp hv hind u hu)
  have habove : ∀ u ∈ above, (pairT T true y u).oneValue BPair.unit := fun u hu =>
    BPair.oneValue_trans (pairT_raise_lower_G2 sig i hi R u)
      (pairT_span_unit T T.keys pool R (lowerT T sig i u) hR hperp (hlower u hu))
  have hn := pairT_span_unit T T.keys above y y hy habove hraise
  by_cases he : y.val = []
  · exact Subtype.ext he
  · exact False.elim (offOfUnitLt (pairT_self_pos T y he) hn)

end slotpower
