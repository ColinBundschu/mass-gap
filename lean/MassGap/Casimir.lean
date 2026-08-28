import MassGap.Blockirr
import MassGap.Strings
/-!
`lem:casimir` — the trace tier: the trace fold at a stated list
(`lem:lowerspan`'s trace read, the diagonal operator pairings each
cleared by the further members' self-pairings), with the operator
entering at its matrix against the content coordinates.  The
carrier is `trFold` beside the two self-pairing products `prodAll`
and `prodOff`, and the tier's landed reads are the operator ones
and the products' own: the fold is additive in the operator
(`trFold_add`, the matrix sum's action splitting entrywise at
every member) and a scalar operator's fold is the count against
the scalar at the whole product (`trFold_scalar`), both carried by
the bridge to `def:ground`'s index fold; the products read at the
withdrawn key (`prodOff_mul_self`, the guarded range fold's pick)
and off the sum's unit at off-unit self-pairings (`prodAll_off`,
the integral read at each factor), which is what lets a whole
product cancel.

The one-value theorem at two orthogonal spanning lists lands
beside them (`trace_eq`): the projection fold at one list (a
member's cleared multiple as its own coordinates against the
members, the gap perpendicular to every member and inside the
span, so null at the pairing's definiteness), the crossed fold
pairing that display against a further vector, the operator's own
crossed fold at the pairing's transpose adjoint, and the double
collapse at the two lists' cleared products — the off-diagonal at
the orthogonality, the diagonal at `prodOff_mul_self`, and one
whole product cancelled at `prodAll_off`, which is where the first
list's off-unit self-pairings are read.  That single clearing is
the theorem's whole consumption of the off-unit data: the first
list's binder is the only one, the second list's product never
cancelling.

The `C` family lands beside them: `casimirM` at a content, the
composed unit actions over the ordered letter pairs, with
`casScalar`'s block read.  Two of its three `endo_scalar` data are
here.  The shape (`casimirM_sq`) is the seed's own, kept by every
sum at a matched operand, the terms square at the moved content's
occupied enumeration through the product's transpose count.  The
top read (`casimirM_top`) collects the three letter families at
the exhibit: the equal-lettered term is the grading's scalar
twice (the move the identity at an occupied letter), the ordered
term is the general pair's exchange with the raising's image of
the exhibit the unit tail (so the exchanged composite dies and the
balance read survives, the exchange's degenerate side at an
unoccupied second letter taken through the vacant content), and
the reversed term vanishes at that same top read.  The ordered
family is where the row list's weak descent is consumed: its first
letter unoccupied forces the second unoccupied too, so the term
goes to the unit tail and the pair's balance read to the sum's
unit with it.  The scalars collect to
`casScalar`'s two folds through the accumulating sum's own index
reads.  The moved reads land the tier's third `endo_scalar` datum
(`casimirM_comm`): the `C` family commutes past every letter pair
at a general vector.  The action collects into the vector-valued
index fold (`casimirM_vsum` over `elim.vsum`, the seed null), the
per-pair join instantiates the table's display twice — at the
factor letters against the unit's, then inside the first's middle
term — leaving four guarded delta families (`termJoin`, with
`moveComm` chaining the crossed moves at the supported letters),
and the vacant-letter branches close at the closure sentence's
reads: every member null away from the unit's raise (`termNullA`),
the moved term surviving at it (`termNullB`), and the raised
letter vacant in the moved content forcing the lowered letter to
the unit's own at its one count, the surviving member closing on
the further delta family at the display's shorter instance
(`termNullC`,
the re-raised vacant content's matrix the null map by `con:units`'
grading, `offNull_jj`).  The `(p,q)`-fold then collects each
side's delta families to the one join: the inner-guarded families
pick at their keys (`pickInner`), the outer-guarded ones fold
their off-guard rows to the unit tail and pick (`pickOuter`), the
picked members identify across the chain reads (`famAC` at the
occupancy trichotomy, the moved-family identification one chain
read), and the shared summands clear at the memberwise
cancellation — the two folds a summand on both members fixing the
value, `lem:casimir`'s own display.  With the three data landed,
the eigen tier instantiates `lem:blockirr`(ii) at the block: the
block read (`casimirM_member`) is that clause's line at the top —
`⟨v,v⟩·(C w) = ⟨C v, v⟩·w` with the top read collapsing the right
pairing to `q(λ)·⟨v,v⟩`, and the exhibit's off-unit self-pairing
(the coordinate family off the unit tail at the pairing's
definiteness) the factor cancelled — carried by the memberwise
off-unit cancellation (`elim.oneValue_unscale`), and the span-level
transport (`spanRel_scalar`, the eigen rows' combination read
`comboScale` with the span witness's own clearing cancelled) lifts
it from a spanning family to every member of its span.  The trace
read (`casimirM_trace`) is `trFold_scalar` at those two: every
collected member sits in its content group's span (`lem:strings`'
terminal read) and every group row is a span member's own
coordinates, so the whole list is eigen and the fold reads the
string count against the block scalar at the whole self-pairing
product, the unoccupied content coming out of the same fold reads
at the vacant list.  The pair's own trace lands beside it
(`stringTraceUp`, `stringTraceDn`, `thm:weylchar`'s
string-by-string trace): at the exhaustion pair the two ordered
term matrices — the raising-after-lowering word `E_ij E_ji` and
the lowering-after-raising word `E_ji E_ij` at the content — have
their folds over the collected members at the two side weights
against the whole self-pairing product.  The collection is the
constant case's weighted counterpart (`trFold_weights`, the
scalar read per member rather than one for the whole list), each
member's image its own depth's clearing (`lem:strings`' two word
reads), so the fold's terms pick their weights against the whole
product and the index fold collects them to the weight list's own
sum (`ground.sumIndex` at the shared spine, `membersAt`'s width the
weight list's).

With the tier landed the trace recursion closes: `recRead_def`,
`lem:casimir`'s second discharge theorem, is `thm:weylchar`'s
recursion display at every key of the span's occupancy family.
Above one letter a reference letter pair's collected members
carry the whole identity.  The `C` family's fold splits over the
ordered letter pairs (`casimirSplit`, the double `matAdd` fold
collected by `foldTrace` with the seed's fold the sum's unit),
each ordered term's fold reads its own trace weight against the
whole product (`termTrace`: the diagonal at the letter's square
through `diagAt`, the ordered pairs transported from their own
pair's collection by `offTrace` — `trace_eq` at the two lists,
mutually spanning through their shared content group by
`elim.spanRel_trans`, with that pair's product cancelled at its
off-unit read), and the whole self-pairing product cancels
against `casimirM_trace`, leaving the block scalar's balance in
counts (`traceNat` through `casBal`, the scalar's own
square-and-pair read at `casScalar_read`'s term families, and
`ground.BPair.ofNat_inj`).  The weights' double fold splits at the diagonal's
delta and the pairs' two sides (`wAllSplit`), the per-pair string
collection sums over the letter pairs to the display's two moved
folds (`collectSum` at `strings.stringCollect`, the letter-pair
fold read as the guarded double fold by `places.pairsFold`), and
the two positional identities (`posId` at the row list and at the
content — the pair runs above and below a letter its own two
counts — with the degree shared through the span's own total,
`spanDegree`) carry the two displays through the square's split
at the entrywise join (`weylchar.sqSplit`).  The four collected identities
join at one cancellation (`recArith`).  Below two letters the
letter pairs are vacant, so the moved folds die and the display
is the count's own: at an occupied count the key is the row list
itself, its width and total the span's.  The remaining discharge
theorem (`weylchar.symRead` at the span's contents) is
`lem:strings`' own, landed at Strings as `symRead_def`.
-/

namespace casimir
open ground places blockcount

/-- The further members' self-pairing product at a withdrawn
key. -/
def prodOff (L : elim.Mat) (j : Nat) : BPair :=
  (List.range L.length).foldl
    (fun acc i =>
      if i = j then acc
      else acc * elim.dotP (getAt [] L i) (getAt [] L i))
    (BPair.ofNat 1)

/-- The whole list's self-pairing product. -/
def prodAll (L : elim.Mat) : BPair :=
  (List.range L.length).foldl
    (fun acc i => acc * elim.dotP (getAt [] L i) (getAt [] L i))
    (BPair.ofNat 1)

/-- The trace fold: the diagonal operator pairings, each cleared
by the further members' self-pairings. -/
def trFold (T L : elim.Mat) : BPair :=
  (List.range L.length).foldl
    (fun acc j =>
      acc + elim.dotP (getAt [] L j)
          (elim.matVec T (getAt [] L j)) * prodOff L j)
    BPair.unit

/-! The fold's bridge to the balance carrier's index fold
(`def:ground`'s `bsum`): the accumulating fold reads the seed
against the index fold, so the tier's reads ride `bsum`'s own kit
— the pointwise split, the reindexings and the delta pick. -/

/-- The trace fold reads the index fold at its terms. -/
private theorem trFold_read (T L : elim.Mat) :
    (trFold T L).oneValue
      (ground.bsum (fun j => elim.dotP (getAt [] L j)
        (elim.matVec T (getAt [] L j)) * prodOff L j)
        (List.range L.length)) := by
  show ((List.range L.length).foldl
    (fun a j => a + elim.dotP (getAt [] L j)
      (elim.matVec T (getAt [] L j)) * prodOff L j)
    BPair.unit).oneValue _
  refine BPair.oneValue_trans
    (ground.foldB_foldl _ (List.range L.length) BPair.unit) ?_
  exact BPair.unit_add _

/-- `lem:casimir`'s additivity: the trace fold is additive in the
operator, the matrix sum's action splitting at every member. -/
theorem trFold_add (n : Nat) (T T' L : elim.Mat)
    (hT : elim.sqAt T n) (hT' : elim.sqAt T' n)
    (hL : elim.rowsLen n L) :
    (trFold (elim.matAdd T T') L).oneValue
      (trFold T L + trFold T' L) := by
  refine BPair.oneValue_trans (trFold_read (elim.matAdd T T') L) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (BPair.add_congr (trFold_read T L)
      (trFold_read T' L)))
  refine BPair.oneValue_trans ?_
    (ground.foldB_add
      (fun j => elim.dotP (getAt [] L j)
        (elim.matVec T (getAt [] L j)) * prodOff L j)
      (fun j => elim.dotP (getAt [] L j)
        (elim.matVec T' (getAt [] L j)) * prodOff L j)
      (List.range L.length))
  refine ground.foldB_congr_members _ _ (List.range L.length) ?_
  intro j hj
  have hjr : j < L.length := ground.ltOfMem hj
  have hrow : (getAt ([] : List BPair) L j).length = n :=
    elim.rowsLen_getAt L j hL hjr
  rw [← BPair.right_distrib]
  refine BPair.mul_congr_left ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right _ _ _
      (elim.matVec_add_free n T T' (getAt [] L j)
        (elim.rowsLen_of_sqAt hT) (elim.rowsLen_of_sqAt hT'))) ?_
  refine elim.dotP_vecAdd (getAt [] L j) _ _ ?_ ?_
  · rw [elim.matVec_length, elim.sqAt_len hT, hrow]
  · rw [elim.matVec_length, elim.sqAt_len hT', hrow]

/-! The product kit: the self-pairing products as guarded range
folds — the withdrawn key picked back against its own pairing, and
the whole product off the sum's unit at the members' own reads
(the integral read at each factor).  Both are `lem:casimir`'s own
data: the trace reads clear by them. -/

/-- `lem:casimir`'s pick read: a member's self-pairing against the
further members' product is the whole product. -/
theorem prodOff_mul_self (L : elim.Mat) (j : Nat)
    (hj : j < L.length) :
    (elim.dotP (getAt [] L j) (getAt [] L j)
      * prodOff L j).oneValue (prodAll L) :=
  BPair.oneValue_of_eq ((BPair.mul_comm _ _).trans
    (ground.foldl_skip BPair.mul BPair.mul_comm BPair.mul_assoc
      (fun i => elim.dotP (getAt [] L i) (getAt [] L i)) j
      (List.range L.length) (BPair.ofNat 1)
      (countOf_range_one hj)))

/-- The accumulating product stays off the sum's unit at off-unit
factors, the integral read at each step. -/
private theorem prodOffGo (f : Nat → BPair) :
    ∀ (m : Nat) (acc : BPair),
      (∀ i, i < m → ¬ (f i).oneValue BPair.unit) →
      ¬ acc.oneValue BPair.unit →
      ¬ ((List.range m).foldl (fun a i => a * f i) acc).oneValue
        BPair.unit
  | 0, _, _, hacc => hacc
  | m + 1, acc, hf, hacc => by
    rw [ground.range_succ m, foldl_append]
    show ¬ (((List.range m).foldl (fun a i => a * f i) acc)
      * f m).oneValue BPair.unit
    intro hu
    refine prodOffGo f m acc
      (fun i hi => hf i (Nat.lt_succ_of_lt hi)) hacc ?_
    refine ground.mul_cancel_unit (hf m (Nat.lt_succ_self m)) ?_
    rw [BPair.mul_comm]
    exact hu

/-- `lem:casimir`'s clearing read: at self-pairings off the sum's
unit the whole product is off it, so it cancels. -/
theorem prodAll_off (L : elim.Mat)
    (h : ∀ p < L.length,
      ¬ (elim.dotP (getAt [] L p) (getAt [] L p)).oneValue
        BPair.unit) :
    ¬ (prodAll L).oneValue BPair.unit :=
  prodOffGo (fun i => elim.dotP (getAt [] L i) (getAt [] L i))
    L.length (BPair.ofNat 1) h BPair.ofNat_one_off

/-- The index family's constant-one fold reads the count. -/
private theorem countFold : ∀ n : Nat,
    ground.famFold Nat.add 0 (fun _ => 1) (List.range n) = n
  | 0 => rfl
  | n + 1 => by
    rw [ground.range_succ n,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun _ => 1) (List.range n) [n],
      countFold n]
    rfl

/-- `lem:casimir`'s count read: a scalar operator's trace fold is
the count against the scalar at the whole product. -/
theorem trFold_scalar (T L : elim.Mat) (c : BPair)
    (hc : ∀ j < L.length,
      poly.oneValue (elim.matVec T (getAt [] L j))
        (elim.vecScale c (getAt [] L j))) :
    (trFold T L).oneValue
      (BPair.ofNat L.length * c * prodAll L) := by
  refine BPair.oneValue_trans (trFold_read T L) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun _ => BPair.ofNat 1 * (c * prodAll L))
      (List.range L.length) ?_) ?_
  · intro j hj
    have hjr : j < L.length := ground.ltOfMem hj
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.mul_ofNat_one (c * prodAll L))))
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (elim.dotP_oneValue_right _ _ _ (hc j hjr))
          (elim.dotP_vecScale_right (getAt [] L j)
            (getAt [] L j) c))) ?_
    rw [BPair.mul_assoc]
    exact BPair.mul_congr (BPair.oneValue_refl c)
      (prodOff_mul_self L j hjr)
  · refine BPair.oneValue_trans
      (ground.bsum_scalar (fun _ => 1) (c * prodAll L)
        (List.range L.length)) ?_
    rw [countFold L.length, ← BPair.mul_assoc]
    exact BPair.oneValue_refl _

/-! The projection tier: at a pairwise perpendicular list a span
member's whole-product multiple is its own coordinates against the
members, each cleared by the further members' self-pairings — the
gap perpendicular to every member and inside the span, so null at
the pairing's definiteness.  The swap reads (the pairing of a
memberwise swap, and the sum's unit at a swapped partner) and the
off-unit cancellation are the tier's own plumbing; the crossed
fold pairs the display against a further vector, and the operator
crossed fold rides the pairing's transpose adjoint. -/

/-- The six-factor product's shuffle: the double fold's term at
the second list's crossed pairing. -/
private theorem mulSix (o ya oa yb ob c : BPair) :
    o * (ya * oa * (yb * ob * c))
      = oa * ob * c * (ya * o * yb) := by
  rw [BPair.mul_assoc ya oa (yb * ob * c),
    BPair.mul_assoc yb ob c,
    BPair.mul_assoc oa ob c,
    BPair.mul_assoc ya o yb,
    BPair.mul_assoc oa (ob * c) (ya * (o * yb)),
    BPair.mul_assoc ob c (ya * (o * yb)),
    BPair.mul_left_comm ya oa (yb * (ob * c)),
    BPair.mul_left_comm o oa (ya * (yb * (ob * c))),
    BPair.mul_left_comm yb ob c,
    BPair.mul_left_comm ya ob (yb * c),
    BPair.mul_left_comm o ob (ya * (yb * c)),
    BPair.mul_comm yb c,
    BPair.mul_left_comm ya c yb,
    BPair.mul_left_comm o c (ya * yb),
    BPair.mul_left_comm o ya yb]

/-- The diagonal term's shuffle: the picked key's own self-pairing
against its withdrawn product. -/
private theorem mulFive (oa c d B : BPair) :
    oa * oa * c * (d * B) = d * oa * B * (c * oa) := by
  rw [BPair.mul_assoc oa oa c,
    BPair.mul_assoc oa (oa * c) (d * B),
    BPair.mul_assoc oa c (d * B),
    BPair.mul_assoc d oa B,
    BPair.mul_assoc d (oa * B) (c * oa),
    BPair.mul_assoc oa B (c * oa),
    BPair.mul_left_comm c d B,
    BPair.mul_left_comm oa d (c * B),
    BPair.mul_left_comm oa d (oa * (c * B)),
    BPair.mul_comm c B,
    BPair.mul_left_comm oa B c,
    BPair.mul_comm oa c]

/-- The projection's coefficients: a vector's own pairing against
each member, cleared by the further members' self-pairings. -/
private def projCoef (X : elim.Mat) (v : List BPair) : List BPair :=
  (List.range X.length).map
    (fun a => elim.dotP v (getAt [] X a) * prodOff X a)

/-- The coefficients count the members. -/
private theorem projCoef_len (X : elim.Mat) (v : List BPair) :
    (projCoef X v).length = X.length :=
  ground.length_mapRange _ X.length

/-- The coefficient at a member's key is that member's cleared
pairing. -/
private theorem projCoef_get (X : elim.Mat) (v : List BPair)
    (a : Nat) (ha : a < X.length) :
    ground.getAt BPair.unit (projCoef X v) a
      = elim.dotP v (getAt [] X a) * prodOff X a := by
  show ground.getAt BPair.unit ((List.range X.length).map
    (fun i => elim.dotP v (getAt [] X i) * prodOff X i)) a = _
  rw [ground.getAt_map 0 BPair.unit
      (fun i => elim.dotP v (getAt [] X i) * prodOff X i)
      (List.range X.length) a
      (by rw [ground.length_range]; exact ha),
    ground.getAt_range X.length a ha]

/-- A combination against a vector reads the index fold of the
coefficients at the members' own pairings. -/
private theorem combo_dotP (n : Nat) (X : elim.Mat)
    (cs z : List BPair) (hX : elim.rowsLen n X) (hz : z.length = n)
    (hcs : cs.length = X.length) :
    (elim.dotP (elim.combo n cs X) z).oneValue
      (ground.bsum (fun i => ground.getAt BPair.unit cs i
        * elim.dotP (getAt [] X i) z) (List.range X.length)) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (elim.dotP_matVec n cs X z hX hz hcs)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right cs _ _ (elim.matVec_dotPmap X z)) ?_
  rw [elim.dotP_fold X.length cs (X.map (fun r => elim.dotP r z))
    hcs (ground.length_map _ X)]
  refine ground.foldB_congr_members _ _ (List.range X.length) ?_
  intro i hi
  rw [ground.getAt_map ([] : List BPair) BPair.unit
    (fun r => elim.dotP r z) X i (ground.ltOfMem hi)]
  exact BPair.oneValue_refl _

/-- `lem:casimir`'s projection fold: at a pairwise perpendicular
list a span member's whole-product multiple reads its own
coordinates against the members — the gap perpendicular to every
member and inside the span, so null at the pairing's
definiteness. -/
private theorem projFold (n : Nat) (X : elim.Mat) (v : List BPair)
    (hX : elim.rowsLen n X) (hv : v.length = n)
    (hperp : ∀ p < X.length, ∀ q < X.length, ¬ p = q →
      (elim.dotP (getAt [] X p) (getAt [] X q)).oneValue
        BPair.unit)
    (hsp : elim.spanRel n X v) :
    poly.oneValue (elim.vecScale (prodAll X) v)
      (elim.combo n (projCoef X v) X) := by
  have hL : (elim.vecScale (prodAll X) v).length = n := by
    rw [elim.length_vecScale]
    exact hv
  have hR : (elim.combo n (projCoef X v) X).length = n :=
    elim.length_combo n (projCoef X v) X hX
  have hRs : ((elim.combo n (projCoef X v) X).map
      BPair.swap).length = n := by
    rw [ground.length_map]
    exact hR
  have hg : (elim.vecAdd (elim.vecScale (prodAll X) v)
      ((elim.combo n (projCoef X v) X).map
        BPair.swap)).length = n :=
    elim.length_vecAdd _ _ n hL hRs
  have hperpg : ∀ p, p < X.length →
      (elim.dotP (elim.vecAdd (elim.vecScale (prodAll X) v)
          ((elim.combo n (projCoef X v) X).map BPair.swap))
        (getAt [] X p)).oneValue BPair.unit := by
    intro p hp
    have hXp : (getAt ([] : List BPair) X p).length = n :=
      elim.rowsLen_getAt X p hX hp
    refine BPair.oneValue_trans
      (elim.dotP_vecAdd_left _ _ _
        (Nat.le_of_eq (Eq.symm (by rw [hL, hXp])))
        (Nat.le_of_eq (Eq.symm (by rw [hRs, hXp])))) ?_
    rw [elim.dotP_comm
        ((elim.combo n (projCoef X v) X).map BPair.swap)
        (getAt [] X p),
      elim.dotP_swapMap (getAt [] X p) (elim.combo n (projCoef X v) X),
      BPair.add_comm]
    refine BPair.swap_add_null ?_
    have hLp : (elim.dotP (elim.vecScale (prodAll X) v)
        (getAt [] X p)).oneValue
        (prodAll X * elim.dotP v (getAt [] X p)) := by
      rw [elim.dotP_comm (elim.vecScale (prodAll X) v)
        (getAt [] X p)]
      refine BPair.oneValue_trans
        (elim.dotP_vecScale_right (getAt [] X p) v (prodAll X)) ?_
      rw [elim.dotP_comm (getAt [] X p) v]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm hLp)
    rw [elim.dotP_comm (getAt [] X p)
      (elim.combo n (projCoef X v) X)]
    refine BPair.oneValue_trans
      (combo_dotP n X (projCoef X v) (getAt [] X p) hX hXp
        (projCoef_len X v)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun i => if p = i then
          elim.dotP v (getAt [] X i) * prodOff X i
            * elim.dotP (getAt [] X i) (getAt [] X p)
          else BPair.unit)
        (List.range X.length) ?_) ?_
    · intro i hi
      have hix : i < X.length := ground.ltOfMem hi
      rw [projCoef_get X v i hix]
      by_cases hpi : p = i
      · rw [if_pos hpi]
        exact BPair.oneValue_refl _
      · rw [if_neg hpi]
        exact elim.oneValue_mul_unit _ _
          (hperp i hix p hp (fun he => hpi he.symm))
    · refine BPair.oneValue_trans
        (ground.bsum_pick _ (List.range X.length) p ?_) ?_
      · rw [ground.countOf_range_one hp]
      · rw [BPair.mul_assoc (elim.dotP v (getAt [] X p))
            (prodOff X p)
            (elim.dotP (getAt [] X p) (getAt [] X p)),
          BPair.mul_comm (prodOff X p)
            (elim.dotP (getAt [] X p) (getAt [] X p)),
          BPair.mul_comm (prodAll X)
            (elim.dotP v (getAt [] X p))]
        exact BPair.mul_congr (BPair.oneValue_refl _)
          (prodOff_mul_self X p hp)
  have hspg : elim.spanRel n X
      (elim.vecAdd (elim.vecScale (prodAll X) v)
        ((elim.combo n (projCoef X v) X).map BPair.swap)) := by
    refine elim.spanRel_add n X _ _ hX hL hRs
      (elim.spanRel_scale n X v (prodAll X) hX hv hsp) ?_
    refine elim.spanRel_congr n X _ _
      (poly.oneValue_symm (elim.swapMap_scale _)) ?_
      (by rw [ground.length_map]; exact hR)
    refine elim.spanRel_scale n X _ _ hX hR ?_
    exact elim.spanRel_combo n X hX X (projCoef X v) hX
      (fun i hi => elim.spanRel_getAt n X i hi hX)
  exact elim.oneValue_of_null_swap _ _ (hL.trans hR.symm)
    (elim.dotP_self_null _
      (elim.perp_span n X _ _ hX hg hperpg hspg))

/-- `lem:casimir`'s crossed fold: the projection display paired
against a further vector, the coordinates' fold at the members'
own pairings. -/
private theorem crossFold (n : Nat) (X : elim.Mat)
    (v w : List BPair) (hX : elim.rowsLen n X) (hv : v.length = n)
    (hw : w.length = n)
    (hperp : ∀ p < X.length, ∀ q < X.length, ¬ p = q →
      (elim.dotP (getAt [] X p) (getAt [] X q)).oneValue
        BPair.unit)
    (hsp : elim.spanRel n X v) :
    (elim.dotP v w * prodAll X).oneValue
      (ground.bsum (fun a => elim.dotP v (getAt [] X a)
        * prodOff X a * elim.dotP (getAt [] X a) w)
        (List.range X.length)) := by
  rw [elim.dotP_comm v w,
    BPair.mul_comm (elim.dotP w v) (prodAll X)]
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (elim.dotP_vecScale_right w v (prodAll X))) ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right w _ _
      (projFold n X v hX hv hperp hsp)) ?_
  rw [elim.dotP_comm w (elim.combo n (projCoef X v) X)]
  refine BPair.oneValue_trans
    (combo_dotP n X (projCoef X v) w hX hw (projCoef_len X v)) ?_
  refine ground.foldB_congr_members _ _ (List.range X.length) ?_
  intro i hi
  rw [projCoef_get X v i (ground.ltOfMem hi)]
  exact BPair.oneValue_refl _

/-- The operator's crossed fold: an operator pairing at a span
member reads the member's coordinates against the operator's own
pairings with the list, the transpose adjoint the carrier. -/
private theorem opCross (n : Nat) (T X : elim.Mat)
    (v z : List BPair) (hT : elim.sqAt T n)
    (hX : elim.rowsLen n X) (hv : v.length = n) (hz : z.length = n)
    (hperp : ∀ p < X.length, ∀ q < X.length, ¬ p = q →
      (elim.dotP (getAt [] X p) (getAt [] X q)).oneValue
        BPair.unit)
    (hsp : elim.spanRel n X v) :
    (elim.dotP z (elim.matVec T v) * prodAll X).oneValue
      (ground.bsum (fun b => elim.dotP v (getAt [] X b)
        * prodOff X b
        * elim.dotP z (elim.matVec T (getAt [] X b)))
        (List.range X.length)) := by
  have hTn : elim.rowsLen n T := elim.rowsLen_of_sqAt hT
  have hzT : z.length = T.length := by
    rw [elim.sqAt_len hT]
    exact hz
  refine BPair.oneValue_trans
    (BPair.mul_congr_left
      (elim.dotP_matVec n z T v hTn hv hzT)) ?_
  rw [elim.dotP_comm (elim.combo n z T) v]
  refine BPair.oneValue_trans
    (crossFold n X v (elim.combo n z T) hX hv
      (elim.length_combo n z T hTn) hperp hsp) ?_
  refine ground.foldB_congr_members _ _ (List.range X.length) ?_
  intro b hb
  refine BPair.mul_congr (BPair.oneValue_refl _) ?_
  rw [elim.dotP_comm (getAt [] X b) (elim.combo n z T)]
  exact BPair.oneValue_symm (elim.dotP_matVec n z T (getAt [] X b)
    hTn (elim.rowsLen_getAt X b hX (ground.ltOfMem hb)) hzT)

/-- The double fold's term: the operator's pairing at a pair of
the first list's members, cleared by their withdrawn products,
against the second list's own crossed pairing. -/
private def trTerm (T X Y : elim.Mat) (a b j : Nat) : BPair :=
  prodOff X a * prodOff X b
      * elim.dotP (getAt [] X a) (elim.matVec T (getAt [] X b))
    * (elim.dotP (getAt [] X a) (getAt [] Y j) * prodOff Y j
      * elim.dotP (getAt [] Y j) (getAt [] X b))

/-- `lem:casimir`'s one-value theorem: two orthogonal spanning
lists read one trace at the lists' cleared products — the double
collapse at the crossed folds, the off-diagonal at the
orthogonality, the diagonal at the withdrawn key's own pick, and
one whole product cancelled at its off-unit read. -/
theorem trace_eq (n : Nat) (T X Y : elim.Mat)
    (hT : elim.sqAt T n) (hX : elim.rowsLen n X)
    (hY : elim.rowsLen n Y)
    (hpX : ∀ p < X.length, ∀ q < X.length, ¬ p = q →
      (elim.dotP (getAt [] X p) (getAt [] X q)).oneValue
        BPair.unit)
    (hpY : ∀ p < Y.length, ∀ q < Y.length, ¬ p = q →
      (elim.dotP (getAt [] Y p) (getAt [] Y q)).oneValue
        BPair.unit)
    (hoX : ∀ p < X.length,
      ¬ (elim.dotP (getAt [] X p) (getAt [] X p)).oneValue
        BPair.unit)
    (hXY : ∀ p < X.length, elim.spanRel n Y (getAt [] X p))
    (hYX : ∀ q < Y.length, elim.spanRel n X (getAt [] Y q)) :
    (trFold T X * prodAll Y).oneValue
      (trFold T Y * prodAll X) := by
  have hAB : ∀ a, a < X.length → ∀ b, b < X.length →
      (ground.bsum (fun j => trTerm T X Y a b j)
        (List.range Y.length)).oneValue
        (prodOff X a * prodOff X b
            * elim.dotP (getAt [] X a)
              (elim.matVec T (getAt [] X b))
          * (elim.dotP (getAt [] X a) (getAt [] X b)
            * prodAll Y)) := by
    intro a ha b hb
    show (ground.bsum (fun j => prodOff X a * prodOff X b
        * elim.dotP (getAt [] X a) (elim.matVec T (getAt [] X b))
      * (elim.dotP (getAt [] X a) (getAt [] Y j) * prodOff Y j
        * elim.dotP (getAt [] Y j) (getAt [] X b)))
      (List.range Y.length)).oneValue _
    refine BPair.oneValue_trans
      (ground.foldB_mul_left _ _ (List.range Y.length)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    exact BPair.oneValue_symm
      (crossFold n Y (getAt [] X a) (getAt [] X b) hY
        (elim.rowsLen_getAt X a hX ha)
        (elim.rowsLen_getAt X b hX hb) hpY (hXY a ha))
  have hDiag : ∀ a, a < X.length →
      (ground.bsum (fun b => ground.bsum
          (fun j => trTerm T X Y a b j) (List.range Y.length))
        (List.range X.length)).oneValue
        (prodAll X * prodAll Y
          * (elim.dotP (getAt [] X a)
              (elim.matVec T (getAt [] X a)) * prodOff X a)) := by
    intro a ha
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun b => if a = b then prodOff X a * prodOff X b
            * elim.dotP (getAt [] X a)
              (elim.matVec T (getAt [] X b))
          * (elim.dotP (getAt [] X a) (getAt [] X b) * prodAll Y)
          else BPair.unit)
        (List.range X.length) ?_) ?_
    · intro b hb
      have hbx : b < X.length := ground.ltOfMem hb
      refine BPair.oneValue_trans (hAB a ha b hbx) ?_
      by_cases hab : a = b
      · rw [if_pos hab]
        exact BPair.oneValue_refl _
      · rw [if_neg hab]
        exact elim.oneValue_mul_unit _ _
          (elim.oneValue_unit_mul (hpX a ha b hbx hab))
    · refine BPair.oneValue_trans
        (ground.bsum_pick _ (List.range X.length) a ?_) ?_
      · rw [ground.countOf_range_one ha]
      · rw [mulFive (prodOff X a)
          (elim.dotP (getAt [] X a) (elim.matVec T (getAt [] X a)))
          (elim.dotP (getAt [] X a) (getAt [] X a)) (prodAll Y)]
        exact BPair.mul_congr_left
          (BPair.mul_congr_left (prodOff_mul_self X a ha))
  have hJ : ∀ j, j < Y.length →
      (prodAll X * (prodAll X * (elim.dotP (getAt [] Y j)
          (elim.matVec T (getAt [] Y j)) * prodOff Y j))).oneValue
        (ground.bsum (fun a => ground.bsum
          (fun b => trTerm T X Y a b j) (List.range X.length))
          (List.range X.length)) := by
    intro j hj
    have hYj : (getAt ([] : List BPair) Y j).length = n :=
      elim.rowsLen_getAt Y j hY hj
    have hsp : elim.spanRel n X (getAt [] Y j) := hYX j hj
    have hTY : (elim.matVec T (getAt [] Y j)).length = n := by
      rw [elim.matVec_length, elim.sqAt_len hT]
    have hin : ∀ a, a < X.length →
        (prodAll X * (elim.dotP (getAt [] Y j) (getAt [] X a)
            * prodOff X a
            * elim.dotP (getAt [] X a)
              (elim.matVec T (getAt [] Y j)))).oneValue
          (ground.bsum (fun b =>
            elim.dotP (getAt [] Y j) (getAt [] X a) * prodOff X a
              * (elim.dotP (getAt [] Y j) (getAt [] X b)
                * prodOff X b
                * elim.dotP (getAt [] X a)
                  (elim.matVec T (getAt [] X b))))
            (List.range X.length)) := by
      intro a ha
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_comm _ _))
            (opCross n T X (getAt [] Y j) (getAt [] X a) hT hX
              hYj (elim.rowsLen_getAt X a hX ha) hpX hsp))) ?_
      exact BPair.oneValue_symm
        (ground.foldB_mul_left _ _ (List.range X.length))
    have hAAs : (prodAll X * (prodAll X
          * elim.dotP (getAt [] Y j)
            (elim.matVec T (getAt [] Y j)))).oneValue
        (ground.bsum (fun a => ground.bsum (fun b =>
          elim.dotP (getAt [] Y j) (getAt [] X a) * prodOff X a
            * (elim.dotP (getAt [] Y j) (getAt [] X b)
              * prodOff X b
              * elim.dotP (getAt [] X a)
                (elim.matVec T (getAt [] X b))))
          (List.range X.length)) (List.range X.length)) := by
      rw [BPair.mul_comm (prodAll X) (elim.dotP (getAt [] Y j)
        (elim.matVec T (getAt [] Y j)))]
      refine BPair.oneValue_trans (BPair.mul_congr
        (BPair.oneValue_refl _)
        (crossFold n X (getAt [] Y j)
          (elim.matVec T (getAt [] Y j)) hX hYj hTY hpX hsp)) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_symm
          (ground.foldB_mul_left _ _ (List.range X.length))) ?_
      exact ground.foldB_congr_members _ _ (List.range X.length)
        (fun a ha => hin a (ground.ltOfMem ha))
    rw [BPair.mul_comm (elim.dotP (getAt [] Y j)
          (elim.matVec T (getAt [] Y j))) (prodOff Y j),
      BPair.mul_left_comm (prodAll X) (prodOff Y j)
        (elim.dotP (getAt [] Y j)
          (elim.matVec T (getAt [] Y j))),
      BPair.mul_left_comm (prodAll X) (prodOff Y j)
        (prodAll X * elim.dotP (getAt [] Y j)
          (elim.matVec T (getAt [] Y j)))]
    refine BPair.oneValue_trans (BPair.mul_congr
      (BPair.oneValue_refl _) hAAs) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (ground.foldB_mul_left _ _ (List.range X.length))) ?_
    refine ground.foldB_congr_members _ _
      (List.range X.length) ?_
    intro a _
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (ground.foldB_mul_left _ _ (List.range X.length))) ?_
    refine ground.foldB_congr_members _ _
      (List.range X.length) ?_
    intro b _
    refine BPair.oneValue_of_eq ?_
    show prodOff Y j * (elim.dotP (getAt [] Y j) (getAt [] X a)
          * prodOff X a
          * (elim.dotP (getAt [] Y j) (getAt [] X b)
            * prodOff X b
            * elim.dotP (getAt [] X a)
              (elim.matVec T (getAt [] X b))))
        = prodOff X a * prodOff X b
            * elim.dotP (getAt [] X a)
              (elim.matVec T (getAt [] X b))
          * (elim.dotP (getAt [] X a) (getAt [] Y j)
            * prodOff Y j
            * elim.dotP (getAt [] Y j) (getAt [] X b))
    rw [elim.dotP_comm (getAt [] X a) (getAt [] Y j)]
    exact mulSix _ _ _ _ _ _
  have hkey : (prodAll X * (prodAll X * trFold T Y)).oneValue
      (prodAll X * (trFold T X * prodAll Y)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (trFold_read T Y))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.oneValue_trans
        (ground.foldB_mul_left _ _ (List.range Y.length))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (ground.foldB_mul_left _ _ (List.range Y.length))))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _ _ (List.range Y.length)
        (fun j hj => hJ j (ground.ltOfMem hj))) ?_
    refine BPair.oneValue_trans
      (ground.bsum_swap (fun j a => ground.bsum
        (fun b => trTerm T X Y a b j) (List.range X.length))
        (List.range Y.length) (List.range X.length)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _ _ (List.range X.length)
        (fun a ha => BPair.oneValue_trans
          (ground.bsum_swap (fun j b => trTerm T X Y a b j)
            (List.range Y.length) (List.range X.length))
          (hDiag a (ground.ltOfMem ha)))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_mul_left _ _ (List.range X.length)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (trFold_read T X))) ?_
    rw [BPair.mul_assoc (prodAll X) (prodAll Y) (trFold T X),
      BPair.mul_comm (prodAll Y) (trFold T X)]
    exact BPair.oneValue_refl _
  rw [BPair.mul_comm (trFold T Y) (prodAll X)]
  exact BPair.oneValue_symm
    (ground.mulCancel (prodAll_off X hoX) hkey)

/-! The `C` family: the Casimir's matrix at a content, the fold
over the ordered letter pairs of the composed unit actions with
the diagonal pairs included, beside its block scalar. -/

/-- The Casimir's matrix at a content: the fold over ordered letter
pairs of the composed unit actions, the diagonal pairs included. -/
def casimirM (d : Nat) (mu : List Nat) : elim.Mat :=
  (List.range d).foldl (fun acc p =>
    (List.range d).foldl (fun acc2 q =>
      elim.matAdd acc2
        (elim.matMul
          (units.matUnitAt mu (moveAt q p mu) p q)
          (units.matUnitAt (moveAt q p mu) mu q p)))
      acc)
    (List.replicate (places.monomialsAt mu).length
      (List.replicate (places.monomialsAt mu).length BPair.unit))

/-- The block scalar at a content: the square fold with the pair
fold, `q(mu)` and the sum over `p < q` of the pair's balance
read. -/
def casScalar (mu : List Nat) : BPair :=
  BPair.sum ((List.range mu.length).map (fun i =>
    BPair.ofNat (getAt 0 mu i * getAt 0 mu i)))
  + BPair.sum ((List.range mu.length).flatMap (fun p =>
      (List.range mu.length).flatMap (fun q =>
        if p < q then
          [BPair.ofNat (getAt 0 mu p)
            + (BPair.ofNat (getAt 0 mu q)).swap]
        else [])))

/-! The family's shape: the seed is square at the content's own
enumeration, the entrywise sum keeps a matched shape, and every
term is the composed units' product — its rows the outer unit's,
its columns the inner unit's transpose at the moved content's
occupied enumeration.  The two folds keep the shape by the same
preservation read. -/

/-- The square shape at the content's enumeration, the two reads
carried together. -/
private def sqShape (n : Nat) (M : elim.Mat) : Prop :=
  M.length = n ∧ elim.rowsLen n M

/-- A fold whose every step keeps the square shape keeps it. -/
private theorem foldShape (n : Nat)
    (step : elim.Mat → Nat → elim.Mat)
    (hstep : ∀ (a : elim.Mat) (k : Nat), sqShape n a →
      sqShape n (step a k)) :
    ∀ (l : List Nat) (acc : elim.Mat), sqShape n acc →
      sqShape n (l.foldl step acc)
  | [], _, h => h
  | k :: t, acc, h =>
    foldShape n step hstep t (step acc k) (hstep acc k h)

/-- The composed units' product at a letter pair is square at the
content's enumeration. -/
private theorem termShape (mu : List Nat) (p q : Nat) :
    sqShape (places.monomialsAt mu).length
      (elim.matMul (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) := by
  have hne : 0 < (units.matUnitAt (moveAt q p mu) mu q p).length := by
    rw [units.length_matUnitAt]
    exact places.monomialsAt_occupied (moveAt q p mu)
  refine ⟨?_, ?_⟩
  · rw [elim.length_matMul]
    exact units.length_matUnitAt mu (moveAt q p mu) p q
  · exact elim.rowsLen_cast
      (elim.length_transposeM (units.matUnitAt (moveAt q p mu) mu q p)
        (units.rowsLen_matUnitAt (moveAt q p mu) mu q p) hne)
      (elim.rowsLen_matMul (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p))

/-- The sum against a square term keeps the square shape. -/
private theorem stepShape (n : Nat) (a t : elim.Mat)
    (ha : sqShape n a) (ht : sqShape n t) :
    sqShape n (elim.matAdd a t) :=
  ⟨(elim.length_matAdd a t (ha.1.trans ht.1.symm)).trans ha.1,
   elim.rowsLen_matAdd n a t ha.2 ht.2⟩

/-- `lem:casimir`'s shape datum: the `C` family is square at the
content's enumeration, the seed's shape kept by every sum. -/
theorem casimirM_sq (d : Nat) (mu : List Nat) :
    elim.sqAt (casimirM d mu) (places.monomialsAt mu).length := by
  have hseed : sqShape (places.monomialsAt mu).length
      (List.replicate (places.monomialsAt mu).length
        (List.replicate (places.monomialsAt mu).length
          BPair.unit)) :=
    ⟨ground.length_replicate _ _,
     elim.rowsLen_replicate (places.monomialsAt mu).length _⟩
  have hall : sqShape (places.monomialsAt mu).length
      (casimirM d mu) := by
    refine foldShape (places.monomialsAt mu).length _ ?_
      (List.range d) _ hseed
    intro a p ha
    refine foldShape (places.monomialsAt mu).length _ ?_
      (List.range d) a ha
    intro a2 q ha2
    exact stepShape _ a2 _ ha2 (termShape mu p q)
  exact elim.sqAt_of hall.1 hall.2

/-! The block scalar's index reads run through `def:ground`'s own
balance-sum kit (`BPair.sum_map`, `BPair.sum_flatMap`,
`BPair.sum_cons`): the display's two list folds against the index
fold, the accumulating sum reading its seed, so a joined family
splits and a flattened one collects its per-member folds.  The
pair fold's guarded singletons are the per-key reads the
collection consumes. -/

/-! The per-pair scalars: the diagonal pair's letter-count square,
the ordered pair's balance read, and the whole term's scalar at the
three families — the collection to `casScalar`'s two folds. -/

/-- The diagonal pair's scalar: the letter's occupancy square. -/
private def sqTerm (mu : List Nat) (p : Nat) : BPair :=
  BPair.ofNat (getAt 0 mu p * getAt 0 mu p)

/-- The ordered pair's scalar: the balance read at the two
occupancies, the sum's unit off the order. -/
private def prTerm (mu : List Nat) (p q : Nat) : BPair :=
  if p < q then
    BPair.ofNat (getAt 0 mu p) + (BPair.ofNat (getAt 0 mu q)).swap
  else BPair.unit

/-- The term's scalar at a letter pair. -/
private def cTerm (mu : List Nat) (p q : Nat) : BPair :=
  if p = q then sqTerm mu p else prTerm mu p q

/-- The term scalars' double fold reads the block scalar: the
diagonal picked at its own key, the ordered pairs collected at the
guarded singletons. -/
private theorem casScalar_read (mu : List Nat) :
    (ground.bsum (fun p => ground.bsum (fun q => cTerm mu p q)
        (List.range mu.length))
      (List.range mu.length)).oneValue (casScalar mu) := by
  have hsplit : ∀ p, p < mu.length →
      (ground.bsum (fun q => cTerm mu p q)
        (List.range mu.length)).oneValue
        (sqTerm mu p + ground.bsum (fun q => prTerm mu p q)
          (List.range mu.length)) := by
    intro p hp
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun q => (if p = q then sqTerm mu p else BPair.unit)
          + prTerm mu p q)
        (List.range mu.length) ?_) ?_
    · intro q _
      by_cases hpq : p = q
      · rw [show cTerm mu p q = sqTerm mu p from by
            show (if p = q then sqTerm mu p else prTerm mu p q)
              = sqTerm mu p
            rw [if_pos hpq],
          if_pos hpq,
          show prTerm mu p q = BPair.unit from by
            show (if p < q then _ else BPair.unit) = BPair.unit
            rw [if_neg (fun hlt => by
              rw [hpq] at hlt
              exact absurd hlt (Nat.lt_irrefl q))]]
        exact BPair.oneValue_symm (BPair.add_unit _)
      · rw [show cTerm mu p q = prTerm mu p q from by
            show (if p = q then sqTerm mu p else prTerm mu p q)
              = prTerm mu p q
            rw [if_neg hpq],
          if_neg hpq]
        exact BPair.oneValue_symm (BPair.unit_add _)
    · refine BPair.oneValue_trans
        (ground.foldB_add _ _ (List.range mu.length)) ?_
      refine BPair.add_congr ?_ (BPair.oneValue_refl _)
      exact ground.bsum_pick (fun _ => sqTerm mu p)
        (List.range mu.length) p
        (by rw [ground.countOf_range_one hp])
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun p => sqTerm mu p + ground.bsum (fun q => prTerm mu p q)
        (List.range mu.length))
      (List.range mu.length)
      (fun p hp => hsplit p (ground.ltOfMem hp))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_add _ _ (List.range mu.length)) ?_
  refine BPair.oneValue_symm (BPair.add_congr ?_ ?_)
  · exact BPair.sum_map
      (fun i => BPair.ofNat (getAt 0 mu i * getAt 0 mu i))
      (List.range mu.length)
  · refine BPair.oneValue_trans
      (BPair.sum_flatMap _ (List.range mu.length)) ?_
    refine ground.foldB_congr_members _ _ (List.range mu.length) ?_
    intro p _
    refine BPair.oneValue_trans
      (BPair.sum_flatMap _ (List.range mu.length)) ?_
    refine ground.foldB_congr_members _ _ (List.range mu.length) ?_
    intro q _
    by_cases hpq : p < q
    · rw [if_pos hpq,
        show prTerm mu p q = BPair.ofNat (getAt 0 mu p)
            + (BPair.ofNat (getAt 0 mu q)).swap from by
          show (if p < q then _ else BPair.unit) = _
          rw [if_pos hpq]]
      exact BPair.oneValue_trans
        (BPair.sum_cons _ ([] : List BPair)) (BPair.add_unit _)
    · rw [if_neg hpq,
        show prTerm mu p q = BPair.unit from by
          show (if p < q then _ else BPair.unit) = BPair.unit
          rw [if_neg hpq]]
      exact BPair.oneValue_refl _

/-! The exhibit's reads at the letter pairs: the equal-lettered
term acts as the letter count's square (the grading's scalar twice,
the move the identity at an occupied letter), the ordered term at
the general pair's exchange (the raising's image of the exhibit the
unit tail, so the exchanged composite dies and the balance read
survives), and the reversed term vanishes at the same top read.
The unoccupied letters are the same reads' degenerate side: the
consumed letter unoccupied sends a term to the unit tail, and the
row list's weak descent sends the pair's balance read with it. -/

/-- The equal-lettered move at an occupied letter is the
identity. -/
private theorem moveAt_self (p : Nat) (mu : List Nat)
    (h : 0 < getAt 0 mu p) : moveAt p p mu = mu :=
  bumpAt_dipAt_self p mu h

/-- The row list's weak descent at a key pair. -/
private theorem rowLe (s : Shape) : ∀ q p : Nat, p ≤ q →
    q < s.length →
    getAt 0 (places.rowList s) q ≤ getAt 0 (places.rowList s) p
  | 0, p, hpq, _ => by
    match p, hpq with
    | 0, _ => exact Nat.le_refl _
    | p' + 1, h => exact absurd h (Nat.not_succ_le_zero p')
  | q + 1, p, hpq, hlen =>
    match Nat.eq_or_lt_of_le hpq with
    | .inl he => by
      rw [he]
      exact Nat.le_refl _
    | .inr hlt =>
      Nat.le_trans (places.rowList_le s q hlen)
        (rowLe s q p (Nat.le_of_lt_succ hlt)
          (Nat.lt_of_succ_lt hlen))

/-- A term whose inner action is a unit tail is null at the
vector. -/
private theorem termNull (A B : elim.Mat) (n : Nat)
    (hB : elim.rowsLen n B) (x : List BPair) (hx : x.length = n)
    (hnull : poly.unitTail (elim.matVec B x)) :
    poly.oneValue (elim.matVec (elim.matMul A B) x)
      (elim.vecScale BPair.unit x) :=
  poly.unitTail_oneValue
    (poly.oneValue_unitTail (elim.matVec_matMul A B n hB x hx)
      (elim.matVec_null A (elim.matVec B x) hnull))
    (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) x)

/-- The equal-lettered term acts as the letter count's square. -/
private theorem diagAt (mu : List Nat) (p : Nat) (hp : p < mu.length)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    poly.oneValue
      (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt p p mu) p p)
          (units.matUnitAt (moveAt p p mu) mu p p)) x)
      (elim.vecScale (sqTerm mu p) x) := by
  by_cases hocc : 0 < getAt 0 mu p
  · rw [moveAt_self p mu hocc]
    have hE : elim.rowsLen (monomialsAt mu).length
        (units.matUnitAt mu mu p p) :=
      units.rowsLen_matUnitAt mu mu p p
    have hlen : (elim.matVec (units.matUnitAt mu mu p p) x).length
        = (elim.vecScale (BPair.ofNat (getAt 0 mu p)) x).length := by
      rw [units.matVec_matUnitAt_length,
        elim.length_vecScale, hx]
    refine poly.oneValue_trans
      (elim.matVec_matMul (units.matUnitAt mu mu p p)
        (units.matUnitAt mu mu p p) (monomialsAt mu).length hE
        x hx) ?_
    refine poly.oneValue_trans
      (elim.matVec_congr (units.matUnitAt mu mu p p) _ _
        (units.matVec_diag_read mu p hp x hx)) ?_
    refine poly.oneValue_trans
      (units.matVec_diag_read mu p hp
        (elim.vecScale (BPair.ofNat (getAt 0 mu p)) x)
        (by rw [elim.length_vecScale]; exact hx)) ?_
    rw [elim.vecScale_vecScale]
    exact elim.vecScale_congr
      (BPair.oneValue_symm
        (BPair.ofNat_mul (getAt 0 mu p) (getAt 0 mu p))) x
  · have hz : getAt 0 mu p = 0 :=
      match Nat.eq_zero_or_pos (getAt 0 mu p) with
      | .inl h => h
      | .inr h => absurd h hocc
    refine poly.oneValue_trans
      (termNull _ _ (monomialsAt mu).length
        (units.rowsLen_matUnitAt (moveAt p p mu) mu p p) x hx
        (units.matVec_null_unocc (moveAt p p mu) mu p p hz x)) ?_
    refine elim.vecScale_congr ?_ x
    show BPair.unit.oneValue
      (BPair.ofNat (getAt 0 mu p * getAt 0 mu p))
    rw [hz]
    exact BPair.oneValue_refl _

/-- The ordered term at a top vector: the general pair's exchange
with the raising's image the unit tail, the balance read the
survivor. -/
private theorem pairAt (mu : List Nat) (i j : Nat) (hij : ¬ i = j)
    (hi : i < mu.length) (hj : j < mu.length)
    (hocc : 0 < getAt 0 mu i)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length)
    (htop : poly.unitTail
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x)) :
    poly.oneValue
      (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt j i mu) i j)
          (units.matUnitAt (moveAt j i mu) mu j i)) x)
      (elim.vecScale (BPair.ofNat (getAt 0 mu i)
        + (BPair.ofNat (getAt 0 mu j)).swap) x) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hUp := blockcount.out_gen (moveAt j i mu) i j
    (by rw [length_moveAt]; exact hi) hij
  rw [blockcount.moveAt_round_at i j mu hocc] at hUp
  have hTerm : (elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt j i mu) i j)
        (units.matUnitAt (moveAt j i mu) mu j i)) x).length
      = (monomialsAt mu).length := by
    rw [elim.matVec_length, elim.length_matMul,
      units.length_matUnitAt]
  have hSc : ∀ c : BPair, (elim.vecScale c x).length
      = (monomialsAt mu).length := by
    intro c
    rw [elim.length_vecScale]
    exact hx
  have hsplit : poly.oneValue
      (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt j i mu) i j)
          (units.matUnitAt (moveAt j i mu) mu j i)) x)
      (elim.matVec (units.matUnitAt mu (moveAt j i mu) i j)
        (elim.matVec (units.matUnitAt (moveAt j i mu) mu j i) x)) :=
    elim.matVec_matMul _ _ (monomialsAt mu).length
      (units.rowsLen_matUnitAt (moveAt j i mu) mu j i) x hx
  have hkey : ∀ muB : List Nat,
      (∀ s m : List Nat,
        0 < ground.countOf s (monomialsAt mu) →
        0 < ground.countOf m (units.unitAct i j s) →
        m.length = sumNat muB ∧ content muB.length m = muB) →
      (∀ s m : List Nat,
        0 < ground.countOf s (monomialsAt muB) →
        0 < ground.countOf m (units.unitAct j i s) →
        m.length = sumNat mu ∧ content mu.length m = mu) →
      poly.unitTail
        (elim.matVec (units.matUnitAt muB mu i j) x) →
      poly.oneValue
        (elim.vecAdd
          (elim.matVec (elim.matMul
              (units.matUnitAt mu (moveAt j i mu) i j)
              (units.matUnitAt (moveAt j i mu) mu j i)) x)
          (elim.vecScale (BPair.ofNat (getAt 0 mu j)) x))
        (elim.vecScale (BPair.ofNat (getAt 0 mu i)) x) := by
    intro muB hUp' hDn' hnull
    have hlenA : (elim.matVec
        (units.matUnitAt mu (moveAt j i mu) i j)
        (elim.matVec (units.matUnitAt (moveAt j i mu) mu j i)
          x)).length = (monomialsAt mu).length := by
      rw [units.matVec_matUnitAt_length]
    refine poly.oneValue_trans
      (elim.polyOne_vecAdd _ _ _ _ hsplit (poly.oneValue_refl _)
        (hTerm.trans hlenA.symm) rfl) ?_
    refine poly.oneValue_trans
      (units.matVec_gpair_read mu (moveAt j i mu) muB i j
        (blockcount.out_gen mu j i hj hji) hUp hUp' hDn' x hx) ?_
    refine elim.vecAdd_null_left _ _ ?_
      (elim.matVec_null _ _ hnull)
    rw [units.matVec_matUnitAt_length,
      elim.length_vecScale, hx]
  have hone : poly.oneValue
      (elim.vecAdd
        (elim.matVec (elim.matMul
            (units.matUnitAt mu (moveAt j i mu) i j)
            (units.matUnitAt (moveAt j i mu) mu j i)) x)
        (elim.vecScale (BPair.ofNat (getAt 0 mu j)) x))
      (elim.vecScale (BPair.ofNat (getAt 0 mu i)) x) := by
    by_cases hoj : 0 < getAt 0 mu j
    · have hDn' := blockcount.out_gen (moveAt i j mu) j i
        (by rw [length_moveAt]; exact hj) hji
      rw [blockcount.moveAt_round_at j i mu hoj] at hDn'
      exact hkey (moveAt i j mu)
        (blockcount.out_gen mu i j hi hij) hDn' htop
    · have hz : getAt 0 mu j = 0 :=
        match Nat.eq_zero_or_pos (getAt 0 mu j) with
        | .inl h => h
        | .inr h => absurd h hoj
      refine hkey ([] : List Nat) ?_ ?_
        (units.matVec_null_unocc ([] : List Nat) mu i j hz x)
      · intro y m hy hm
        rw [units.unitAct_nil_of_zero i j y
          (places.letter_zero mu j hz y hy)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      · intro y m hy hm
        rw [units.unitAct_nil_of_zero j i y
          (places.letter_zero ([] : List Nat) i rfl y hy)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
  refine elim.vecAdd_cancel_right
    (elim.matVec (elim.matMul
      (units.matUnitAt mu (moveAt j i mu) i j)
      (units.matUnitAt (moveAt j i mu) mu j i)) x)
    (elim.vecScale (BPair.ofNat (getAt 0 mu i)
      + (BPair.ofNat (getAt 0 mu j)).swap) x)
    (elim.vecScale (BPair.ofNat (getAt 0 mu j)) x)
    (hTerm.trans (hSc _).symm) (hTerm.trans (hSc _).symm) ?_
  refine poly.oneValue_trans hone ?_
  rw [← elim.vecScale_add]
  refine elim.vecScale_congr ?_ x
  rw [BPair.add_assoc]
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null
        (BPair.oneValue_refl (BPair.ofNat (getAt 0 mu j))))) ?_
  exact BPair.add_unit _

/-- The term's read at the exhibit: the three letter families at
their own reads, the unoccupied letters riding the row list's weak
descent. -/
private theorem termAct (s : Shape) (p q : Nat)
    (hp : p < s.length) (hq : q < s.length)
    (hx : (exhibit s).coords.length
      = (monomialsAt (places.rowList s)).length) :
    poly.oneValue
      (elim.matVec (elim.matMul
          (units.matUnitAt (places.rowList s)
            (moveAt q p (places.rowList s)) p q)
          (units.matUnitAt (moveAt q p (places.rowList s))
            (places.rowList s) q p)) (exhibit s).coords)
      (elim.vecScale (cTerm (places.rowList s) p q)
        (exhibit s).coords) := by
  have hrl : (places.rowList s).length = s.length :=
    places.length_rowList s
  have hpL : p < (places.rowList s).length := by
    rw [hrl]
    exact hp
  have hqL : q < (places.rowList s).length := by
    rw [hrl]
    exact hq
  by_cases hpq : p = q
  · have hc : cTerm (places.rowList s) p q
        = sqTerm (places.rowList s) p := by
      show (if p = q then _ else _) = _
      rw [if_pos hpq]
    rw [hc, ← hpq]
    exact diagAt (places.rowList s) p hpL (exhibit s).coords hx
  · have hc : cTerm (places.rowList s) p q
        = prTerm (places.rowList s) p q := by
      show (if p = q then _ else _) = _
      rw [if_neg hpq]
    rw [hc]
    by_cases hlt : p < q
    · have hcp : prTerm (places.rowList s) p q
          = BPair.ofNat (getAt 0 (places.rowList s) p)
            + (BPair.ofNat (getAt 0 (places.rowList s) q)).swap := by
        show (if p < q then _ else BPair.unit) = _
        rw [if_pos hlt]
      rw [hcp]
      by_cases hocc : 0 < getAt 0 (places.rowList s) p
      · exact pairAt (places.rowList s) p q hpq hpL hqL hocc
          (exhibit s).coords hx
          (blockcount.exhibit_top_all s p q hlt hq)
      · have hzp : getAt 0 (places.rowList s) p = 0 :=
          match Nat.eq_zero_or_pos (getAt 0 (places.rowList s) p) with
          | .inl h => h
          | .inr h => absurd h hocc
        have hzq : getAt 0 (places.rowList s) q = 0 := by
          have hle := rowLe s q p (Nat.le_of_lt hlt) hq
          rw [hzp] at hle
          exact Nat.le_antisymm hle (Nat.zero_le _)
        have hnull : (BPair.ofNat (getAt 0 (places.rowList s) p)
            + (BPair.ofNat
              (getAt 0 (places.rowList s) q)).swap).oneValue
            BPair.unit := by
          rw [hzp, hzq, BPair.add_comm]
          exact BPair.swap_add_null
            (BPair.oneValue_refl (BPair.ofNat 0))
        refine poly.oneValue_trans
          (termNull _ _ (monomialsAt (places.rowList s)).length
            (units.rowsLen_matUnitAt
              (moveAt q p (places.rowList s)) (places.rowList s) q p)
            (exhibit s).coords hx
            (units.matVec_null_unocc
              (moveAt q p (places.rowList s)) (places.rowList s)
              q p hzp (exhibit s).coords)) ?_
        exact elim.vecScale_congr (BPair.oneValue_symm hnull)
          (exhibit s).coords
    · have hqp : q < p :=
        match Nat.lt_or_ge q p with
        | .inl h => h
        | .inr hge =>
          match Nat.eq_or_lt_of_le hge with
          | .inl he => absurd he hpq
          | .inr h => absurd h hlt
      have hcu : prTerm (places.rowList s) p q = BPair.unit := by
        show (if p < q then _ else BPair.unit) = BPair.unit
        rw [if_neg hlt]
      rw [hcu]
      exact termNull _ _ (monomialsAt (places.rowList s)).length
        (units.rowsLen_matUnitAt
          (moveAt q p (places.rowList s)) (places.rowList s) q p)
        (exhibit s).coords hx
        (blockcount.exhibit_top_all s q p hqp hp)

/-! The fold's action: the seed is null at every vector, and a fold
whose every step adds a term acting as a clearing acts as the
collected clearing — the double fold's scalar the term scalars'
own double fold. -/

/-- A fold whose every step adds a clearing acts as the collected
clearing, the shape carried along. -/
private theorem foldAct (n : Nat) (x : List BPair)
    (step : elim.Mat → Nat → elim.Mat) (c : Nat → BPair) :
    ∀ (l : List Nat),
      (∀ (m : elim.Mat) (k : Nat), 0 < ground.countOf k l →
        sqShape n m → ∀ a : BPair,
        poly.oneValue (elim.matVec m x) (elim.vecScale a x) →
        sqShape n (step m k)
          ∧ poly.oneValue (elim.matVec (step m k) x)
            (elim.vecScale (a + c k) x)) →
      ∀ (acc : elim.Mat) (a : BPair), sqShape n acc →
        poly.oneValue (elim.matVec acc x) (elim.vecScale a x) →
        sqShape n (l.foldl step acc)
          ∧ poly.oneValue (elim.matVec (l.foldl step acc) x)
            (elim.vecScale (a + ground.bsum c l) x)
  | [], _, acc, a, hs, ha =>
    ⟨hs, poly.oneValue_trans ha
      (elim.vecScale_congr
        (BPair.oneValue_symm (BPair.add_unit a)) x)⟩
  | k :: t, hstep, acc, a, hs, ha => by
    have hk := hstep acc k
      (by rw [ground.countOf_head]; exact Nat.succ_pos _) hs a ha
    have hrec := foldAct n x step c t
      (fun m k' hk' => hstep m k'
        (Nat.lt_of_lt_of_le hk' (Nat.le_add_left _ _)))
      (step acc k) (a + c k) hk.1 hk.2
    refine ⟨hrec.1, ?_⟩
    refine poly.oneValue_trans hrec.2 ?_
    rw [BPair.add_assoc]
    exact poly.oneValue_refl _

/-- `lem:casimir`'s top read: the `C` family at the exhibit is the
block scalar's multiple — the diagonal pairs' squares, the ordered
pairs' balance reads, and the reversed pairs' vanishing collected
over the double range. -/
theorem casimirM_top (s : Shape) :
    poly.oneValue
      (elim.matVec (casimirM s.length (places.rowList s))
        (exhibit s).coords)
      (elim.vecScale (casScalar (places.rowList s))
        (exhibit s).coords) := by
  have hrl : (places.rowList s).length = s.length :=
    places.length_rowList s
  have hx : (exhibit s).coords.length
      = (monomialsAt (places.rowList s)).length := by
    have h : (exhibit s).coords.length
        = (monomialsAt (exhibit s).content).length :=
      blockcount.exhibit_sized s
    rw [blockcount.content_exhibit s] at h
    exact h
  have hseed : sqShape (monomialsAt (places.rowList s)).length
      (List.replicate (places.monomialsAt (places.rowList s)).length
        (List.replicate
          (places.monomialsAt (places.rowList s)).length
          BPair.unit)) :=
    ⟨ground.length_replicate _ _,
     elim.rowsLen_replicate (monomialsAt (places.rowList s)).length _⟩
  have hseedAct : poly.oneValue
      (elim.matVec
        (List.replicate
          (places.monomialsAt (places.rowList s)).length
          (List.replicate
            (places.monomialsAt (places.rowList s)).length
            BPair.unit)) (exhibit s).coords)
      (elim.vecScale BPair.unit (exhibit s).coords) :=
    poly.unitTail_oneValue
      (elim.matVec_replicate_null
        (monomialsAt (places.rowList s)).length _
        (exhibit s).coords)
      (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit)
        (exhibit s).coords)
  have hinner : ∀ (p : Nat), p < s.length →
      ∀ (m : elim.Mat), sqShape
        (monomialsAt (places.rowList s)).length m →
      ∀ a : BPair,
        poly.oneValue (elim.matVec m (exhibit s).coords)
          (elim.vecScale a (exhibit s).coords) →
      sqShape (monomialsAt (places.rowList s)).length
          ((List.range s.length).foldl (fun acc2 q =>
            elim.matAdd acc2
              (elim.matMul
                (units.matUnitAt (places.rowList s)
                  (moveAt q p (places.rowList s)) p q)
                (units.matUnitAt (moveAt q p (places.rowList s))
                  (places.rowList s) q p))) m)
        ∧ poly.oneValue
          (elim.matVec ((List.range s.length).foldl (fun acc2 q =>
            elim.matAdd acc2
              (elim.matMul
                (units.matUnitAt (places.rowList s)
                  (moveAt q p (places.rowList s)) p q)
                (units.matUnitAt (moveAt q p (places.rowList s))
                  (places.rowList s) q p))) m) (exhibit s).coords)
          (elim.vecScale (a + ground.bsum
            (fun q => cTerm (places.rowList s) p q)
            (List.range s.length)) (exhibit s).coords) := by
    intro p hp m hm a ha
    refine foldAct (monomialsAt (places.rowList s)).length
      (exhibit s).coords _ _ (List.range s.length) ?_ m a hm ha
    intro m2 q hq hm2 a2 ha2
    have hqr : q < s.length := ground.ltOfMem hq
    have hterm := termShape (places.rowList s) p q
    refine ⟨stepShape _ m2 _ hm2 hterm, ?_⟩
    refine poly.oneValue_trans
      (elim.matVec_add_free (monomialsAt (places.rowList s)).length
        m2 _ (exhibit s).coords hm2.2 hterm.2) ?_
    rw [elim.vecScale_add]
    refine elim.polyOne_vecAdd _ _ _ _ ha2
      (termAct s p q hp hqr hx) ?_ ?_
    · rw [elim.matVec_length, elim.length_vecScale, hm2.1, hx]
    · rw [elim.matVec_length, elim.length_vecScale, hterm.1, hx]
  have hmain := foldAct (monomialsAt (places.rowList s)).length
    (exhibit s).coords _
    (fun p => ground.bsum (fun q => cTerm (places.rowList s) p q)
      (List.range s.length))
    (List.range s.length)
    (fun m p hp hm a ha => hinner p (ground.ltOfMem hp) m hm a ha)
    _ BPair.unit hseed hseedAct
  have hread := casScalar_read (places.rowList s)
  rw [hrl] at hread
  refine poly.oneValue_trans hmain.2 ?_
  exact elim.vecScale_congr
    (BPair.oneValue_trans (BPair.unit_add _) hread)
    (exhibit s).coords

/-! The commutation's carrier tier: the `C` family's action
collected into the vector-valued index fold, the per-pair join at
the table's two instantiations, and the vacant-letter branches at
the closure sentence's reads. -/

/-- The fold's action at a vector: every step's own summand
collected into the index fold. -/
private theorem foldVec (n : Nat) (x : List BPair)
    (step : elim.Mat → Nat → elim.Mat) (G : Nat → List BPair)
    (hG : ∀ k, (G k).length = n)
    (hstep : ∀ (m : elim.Mat) (k : Nat), sqShape n m →
      sqShape n (step m k)
        ∧ poly.oneValue (elim.matVec (step m k) x)
          (elim.vecAdd (elim.matVec m x) (G k))) :
    ∀ (l : List Nat) (acc : elim.Mat), sqShape n acc →
      sqShape n (l.foldl step acc)
        ∧ poly.oneValue (elim.matVec (l.foldl step acc) x)
          (elim.vecAdd (elim.matVec acc x) (elim.vsum n G l))
  | [], acc, hacc =>
    ⟨hacc, poly.oneValue_symm (elim.vecAdd_null_right _ _
      (by rw [elim.matVec_length, hacc.1,
        elim.length_vsum n G [] (fun k' _ => hG k')])
      (poly.unitTail_replicate n))⟩
  | k :: t, acc, hacc => by
    have hk := hstep acc k hacc
    have hrec := foldVec n x step G hG hstep t (step acc k) hk.1
    refine ⟨hrec.1, ?_⟩
    refine poly.oneValue_trans hrec.2 ?_
    refine poly.oneValue_trans
      (elim.polyOne_vecAdd _ _ _ _ hk.2 (poly.oneValue_refl _)
        ((elim.matVec_length _ x).trans (hk.1.1.trans
          (elim.length_vecAdd _ _ n
            ((elim.matVec_length _ x).trans hacc.1)
            (hG k)).symm))
        rfl) ?_
    rw [elim.vecAdd_assoc]
    refine elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _) ?_
      rfl ?_
    · exact poly.oneValue_symm (elim.vsum_cons n G hG k t)
    · rw [elim.length_vecAdd _ _ n (hG k)
        (elim.length_vsum n G t (fun k' _ => hG k')),
        elim.length_vsum n G (k :: t) (fun k' _ => hG k')]

/-- The `C` family's action at a vector: the double index fold of
the ordered pairs' composed actions. -/
private theorem casimirM_vsum (d : Nat) (mu : List Nat)
    (x : List BPair) :
    poly.oneValue (elim.matVec (casimirM d mu) x)
      (elim.vsum (monomialsAt mu).length
        (fun p => elim.vsum (monomialsAt mu).length
          (fun q => elim.matVec (elim.matMul
            (units.matUnitAt mu (moveAt q p mu) p q)
            (units.matUnitAt (moveAt q p mu) mu q p)) x)
          (List.range d))
        (List.range d)) := by
  have hterm : ∀ p q, (elim.matVec (elim.matMul
      (units.matUnitAt mu (moveAt q p mu) p q)
      (units.matUnitAt (moveAt q p mu) mu q p)) x).length
        = (monomialsAt mu).length := by
    intro p q
    rw [elim.matVec_length]
    exact (termShape mu p q).1
  have hin : ∀ p : Nat, ∀ (m : elim.Mat) (q : Nat),
      sqShape (monomialsAt mu).length m →
      sqShape (monomialsAt mu).length (elim.matAdd m
          (elim.matMul (units.matUnitAt mu (moveAt q p mu) p q)
            (units.matUnitAt (moveAt q p mu) mu q p)))
        ∧ poly.oneValue (elim.matVec (elim.matAdd m
            (elim.matMul (units.matUnitAt mu (moveAt q p mu) p q)
              (units.matUnitAt (moveAt q p mu) mu q p))) x)
          (elim.vecAdd (elim.matVec m x)
            (elim.matVec (elim.matMul
              (units.matUnitAt mu (moveAt q p mu) p q)
              (units.matUnitAt (moveAt q p mu) mu q p)) x)) := by
    intro p m q hm
    exact ⟨stepShape _ m _ hm (termShape mu p q),
      elim.matVec_add_free (monomialsAt mu).length m _ x hm.2
        (termShape mu p q).2⟩
  have hseed : sqShape (monomialsAt mu).length
      (List.replicate (places.monomialsAt mu).length
        (List.replicate (places.monomialsAt mu).length
          BPair.unit)) :=
    ⟨ground.length_replicate _ _,
     elim.rowsLen_replicate (monomialsAt mu).length _⟩
  have hout := foldVec (monomialsAt mu).length x _
    (fun p => elim.vsum (monomialsAt mu).length
      (fun q => elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x)
      (List.range d))
    (fun p => elim.length_vsum _ _ _
      (fun q _ => hterm p q))
    (fun m p hm => foldVec (monomialsAt mu).length x _
      (fun q => elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x)
      (fun q => hterm p q) (fun m' q hm' => hin p m' q hm')
      (List.range d) m hm)
    (List.range d) _ hseed
  refine poly.oneValue_trans hout.2 ?_
  exact elim.vecAdd_null_left _ _
    (by
      rw [elim.matVec_length, ground.length_replicate,
        elim.length_vsum _ _ _ (fun p _ => elim.length_vsum _ _ _
          (fun q _ => hterm p q))])
    (elim.matVec_replicate_null (monomialsAt mu).length _ x)

/-! The per-pair join: the table's two instantiations at the
factor letters, the second read inside the first's middle term, and
the four guarded delta families they leave.  The families are named
here so the collection can pick them off the double range. -/

/-- The diagonal action's content read: an equal-lettered action
keeps the source monomial, so the content is the source's. -/
private theorem out_diag (mu : List Nat) (e : Nat) :
    ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (units.unitAct e e s) →
      m.length = sumNat mu ∧ content mu.length m = mu := by
  intro s m hs hm
  have hmem : s.length = sumNat mu ∧ content mu.length s = mu := by
    rw [countOf_monomialsAt mu s] at hs
    by_cases hcc : s.length = sumNat mu ∧ content mu.length s = mu
    · exact hcc
    · rw [if_neg hcc] at hs
      exact absurd hs (Nat.lt_irrefl 0)
  rw [units.countOf_unitAct_diag e s m] at hm
  by_cases hms : m = s
  · rw [hms]
    exact hmem
  · rw [if_neg hms] at hm
    exact absurd hm (Nat.lt_irrefl 0)

/-- The inner factor's image: the pair's lowering at the source
content. -/
private def yV (mu : List Nat) (p q : Nat) (x : List BPair) :
    List BPair :=
  elim.matVec (units.matUnitAt (moveAt q p mu) mu q p) x

/-- The delta family at the shared second letter. -/
private def aFam (mu : List Nat) (i j p q : Nat) (x : List BPair) :
    List BPair :=
  if q = i then
    elim.matVec (units.matUnitAt (moveAt i j mu) (moveAt q p mu) p j)
      (yV mu p q x)
  else List.replicate (monomialsAt (moveAt i j mu)).length
    BPair.unit

/-- The delta family at the shared first letter. -/
private def bFam (mu : List Nat) (i j p q : Nat) (x : List BPair) :
    List BPair :=
  if p = j then
    elim.matVec (units.matUnitAt (moveAt i j mu) (moveAt q p mu) i q)
      (yV mu p q x)
  else List.replicate (monomialsAt (moveAt i j mu)).length
    BPair.unit

/-- The moved family at the shared second letter. -/
private def cFam (mu : List Nat) (i j p q : Nat) (x : List BPair) :
    List BPair :=
  if q = j then
    elim.matVec (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (elim.matVec (units.matUnitAt
        (moveAt q p (moveAt i j mu)) mu i p) x)
  else List.replicate (monomialsAt (moveAt i j mu)).length
    BPair.unit

/-- The moved family at the shared first letter. -/
private def dFam (mu : List Nat) (i j p q : Nat) (x : List BPair) :
    List BPair :=
  if p = i then
    elim.matVec (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (elim.matVec (units.matUnitAt
        (moveAt q p (moveAt i j mu)) mu q j) x)
  else List.replicate (monomialsAt (moveAt i j mu)).length
    BPair.unit

/-- The action carries a guarded summand to its own guard. -/
private theorem matVec_if (T : elim.Mat) (g : Prop) [Decidable g]
    (u : List BPair) (n m : Nat) (hT : T.length = m) :
    poly.oneValue
      (elim.matVec T (if g then u else List.replicate n BPair.unit))
      (if g then elim.matVec T u
        else List.replicate m BPair.unit) := by
  by_cases hgv : g
  · rw [if_pos hgv, if_pos hgv]
    exact poly.oneValue_refl _
  · rw [if_neg hgv, if_neg hgv, ← hT]
    exact poly.unitTail_oneValue
      (elim.matVec_null T _ (poly.unitTail_replicate n))
      (poly.unitTail_replicate T.length)

/-- The guarded summand's width, at both branches. -/
private theorem lenIf (g : Prop) [Decidable g] (T : elim.Mat)
    (u : List BPair) (n : Nat) (hT : T.length = n) :
    (if g then elim.matVec T u
      else List.replicate n BPair.unit).length = n := by
  by_cases hgv : g
  · rw [if_pos hgv, elim.matVec_length]
    exact hT
  · rw [if_neg hgv]
    exact ground.length_replicate _ _


/-- The four delta families' widths. -/
private theorem len_aFam (mu : List Nat) (i j p q : Nat)
    (x : List BPair) : (aFam mu i j p q x).length
      = (monomialsAt (moveAt i j mu)).length :=
  lenIf (q = i) _ _ _ (units.length_matUnitAt _ _ p j)

private theorem len_bFam (mu : List Nat) (i j p q : Nat)
    (x : List BPair) : (bFam mu i j p q x).length
      = (monomialsAt (moveAt i j mu)).length :=
  lenIf (p = j) _ _ _ (units.length_matUnitAt _ _ i q)

private theorem len_cFam (mu : List Nat) (i j p q : Nat)
    (x : List BPair) : (cFam mu i j p q x).length
      = (monomialsAt (moveAt i j mu)).length :=
  lenIf (q = j) _ _ _ (units.length_matUnitAt _ _ p q)

private theorem len_dFam (mu : List Nat) (i j p q : Nat)
    (x : List BPair) : (dFam mu i j p q x).length
      = (monomialsAt (moveAt i j mu)).length :=
  lenIf (p = i) _ _ _ (units.length_matUnitAt _ _ p q)

/-- The raised letter is occupied at the moved content. -/
private theorem occ_moveAt (mu : List Nat) (a b : Nat)
    (ha : a < mu.length) : 0 < getAt 0 (moveAt a b mu) a := by
  show 0 < getAt 0 (bumpAt a (dipAt b mu)) a
  rw [getAt_bumpAt_self a (dipAt b mu)
    (by rw [length_dipAt]; exact ha)]
  exact Nat.succ_pos _

/-- The action's content read at every letter pair, the equal
letters included: the move's own content at the supported letter. -/
private theorem outMove (mu : List Nat) (a b : Nat)
    (ha : a < mu.length) (hb : 0 < getAt 0 mu b) :
    ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (units.unitAct a b s) →
      m.length = sumNat (moveAt a b mu)
        ∧ content (moveAt a b mu).length m = moveAt a b mu := by
  by_cases hab : a = b
  · rw [hab, moveAt_self b mu hb]
    exact out_diag mu b
  · exact blockcount.out_gen mu a b ha hab

/-- The two moves commute at the supported letters: off the
crossed letters by the move's own exchange, and where they cross by
the chain reads at the supported letter. -/
private theorem moveComm (mu : List Nat) (i j p q : Nat)
    (hij : ¬ i = j) (hmj : 0 < getAt 0 mu j)
    (hmp : 0 < getAt 0 mu p)
    (hnp : 0 < getAt 0 (moveAt i j mu) p) :
    moveAt i j (moveAt q p mu) = moveAt q p (moveAt i j mu) := by
  by_cases hpq2 : p = q
  · rw [← hpq2, moveAt_self p mu hmp,
      moveAt_self p (moveAt i j mu) hnp]
  by_cases hip : i = p
  · by_cases hqj : q = j
    · rw [hip, hqj, moveAt_round_at p j mu hmp,
        moveAt_round_at j p mu hmj]
    · rw [hip,
        moveAt_chain' q p j mu hqj
          (fun he => hij (hip.trans he)) hmp,
        moveAt_chain q p j mu]
  · by_cases hqj : q = j
    · rw [hqj, moveAt_chain i j p mu,
        moveAt_chain' i j p mu hip
          (fun he => hpq2 (he.symm.trans hqj.symm)) hmj]
    · exact moveAt_comm i j q p mu hip hqj

/-- The per-pair join's display: the term against the moved
content's, each with its two guarded delta families. -/
private def joinAt (mu : List Nat) (i j p q : Nat) (x : List BPair) :
    Prop :=
  poly.oneValue
    (elim.vecAdd (elim.vecAdd
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.matVec (elim.matMul
            (units.matUnitAt mu (moveAt q p mu) p q)
            (units.matUnitAt (moveAt q p mu) mu q p)) x))
        (aFam mu i j p q x))
      (dFam mu i j p q x))
    (elim.vecAdd (elim.vecAdd
        (elim.matVec (elim.matMul
            (units.matUnitAt (moveAt i j mu)
              (moveAt q p (moveAt i j mu)) p q)
            (units.matUnitAt (moveAt q p (moveAt i j mu))
              (moveAt i j mu) q p))
          (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x))
        (cFam mu i j p q x))
      (bFam mu i j p q x))

/-- A guarded summand at a null term reads the unit tail. -/
private theorem nullIf (g : Prop) [Decidable g] (u : List BPair)
    (n : Nat) (hu : poly.unitTail u) :
    poly.unitTail
      (if g then u else List.replicate n BPair.unit) := by
  by_cases hgv : g
  · rw [if_pos hgv]
    exact hu
  · rw [if_neg hgv]
    exact poly.unitTail_replicate n

/-- A guarded summand at a refused guard reads the unit tail. -/
private theorem nullIfNeg (g : Prop) [Decidable g] (u : List BPair)
    (n : Nat) (hg : ¬ g) :
    poly.unitTail
      (if g then u else List.replicate n BPair.unit) := by
  rw [if_neg hg]
  exact poly.unitTail_replicate n

/-- A guarded summand whose term is null under its own guard reads
the unit tail. -/
private theorem nullIfOf (g : Prop) [Decidable g] (u : List BPair)
    (n : Nat) (hu : g → poly.unitTail u) :
    poly.unitTail
      (if g then u else List.replicate n BPair.unit) := by
  by_cases hgv : g
  · rw [if_pos hgv]
    exact hu hgv
  · rw [if_neg hgv]
    exact poly.unitTail_replicate n

/-- Off the moved letters the entry is the source's. -/
private theorem getMove (i j p : Nat) (mu : List Nat)
    (hpi : ¬ p = i) (hpj : ¬ p = j) :
    getAt 0 (moveAt i j mu) p = getAt 0 mu p := by
  show getAt 0 (bumpAt i (dipAt j mu)) p = getAt 0 mu p
  rw [getAt_bumpAt_ne i (dipAt j mu) p hpi,
    getAt_dipAt_ne j mu p hpj]

/-- The composed term's action is null at a null inner factor. -/
private theorem compNull (A B : elim.Mat) (n : Nat)
    (hB : elim.rowsLen n B) (x : List BPair) (hx : x.length = n)
    (hnull : poly.unitTail (elim.matVec B x)) :
    poly.unitTail (elim.matVec (elim.matMul A B) x) :=
  poly.oneValue_unitTail (elim.matVec_matMul A B n hB x hx)
    (elim.matVec_null A (elim.matVec B x) hnull)

/-- `lem:casimir`'s per-pair join: the table's two instantiations
at the factor letters, chained through the first's middle term,
leaving the four guarded delta families. -/
private theorem termJoin (mu : List Nat) (i j p q : Nat)
    (hij : ¬ i = j) (hi : i < mu.length) (hp : p < mu.length)
    (hq : q < mu.length) (hmj : 0 < getAt 0 mu j)
    (hmp : 0 < getAt 0 mu p)
    (hnp : 0 < getAt 0 (moveAt i j mu) p)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    joinAt mu i j p q x := by
  show poly.oneValue
    (elim.vecAdd (elim.vecAdd _ (aFam mu i j p q x))
      (dFam mu i j p q x))
    (elim.vecAdd (elim.vecAdd _ (cFam mu i j p q x))
      (bFam mu i j p q x))
  have hcomm : moveAt i j (moveAt q p mu)
      = moveAt q p (moveAt i j mu) :=
    moveComm mu i j p q hij hmj hmp hnp
  have hlenNu : (moveAt i j mu).length = mu.length :=
    length_moveAt i j mu
  have hlenMu1 : (moveAt q p mu).length = mu.length :=
    length_moveAt q p mu
  have hlenNu1 : (moveAt q p (moveAt i j mu)).length = mu.length := by
    rw [length_moveAt, hlenNu]
  -- the second display's source vector
  have hy : (yV mu p q x).length
      = (monomialsAt (moveAt q p mu)).length := by
    show (elim.matVec (units.matUnitAt (moveAt q p mu) mu q p)
      x).length = _
    rw [units.matVec_matUnitAt_length]
  -- the four unguarded content reads
  have hIJmu := blockcount.out_gen mu i j hi hij
  have hIJmu1 : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt (moveAt q p mu)) →
      0 < ground.countOf m (units.unitAct i j s) →
      m.length = sumNat (moveAt q p (moveAt i j mu))
        ∧ content (moveAt q p (moveAt i j mu)).length m
          = moveAt q p (moveAt i j mu) := by
    have h := blockcount.out_gen (moveAt q p mu) i j
      (by rw [hlenMu1]; exact hi) hij
    rw [hcomm] at h
    exact h
  have hQPnu := outMove (moveAt i j mu) q p
    (by rw [hlenNu]; exact hq) hnp
  have hQPmu := outMove mu q p hq hmp
  have hPQnu1 : ∀ s m : List Nat,
      0 < ground.countOf s
        (monomialsAt (moveAt q p (moveAt i j mu))) →
      0 < ground.countOf m (units.unitAct p q s) →
      m.length = sumNat (moveAt i j mu)
        ∧ content (moveAt i j mu).length m = moveAt i j mu := by
    have h := outMove (moveAt q p (moveAt i j mu)) p q
      (by rw [hlenNu1]; exact hp)
      (occ_moveAt (moveAt i j mu) q p (by rw [hlenNu]; exact hq))
    rw [moveAt_round_at p q (moveAt i j mu) hnp] at h
    exact h
  have hPQmu1 : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt (moveAt q p mu)) →
      0 < ground.countOf m (units.unitAct p q s) →
      m.length = sumNat mu ∧ content mu.length m = mu := by
    have h := outMove (moveAt q p mu) p q
      (by rw [hlenMu1]; exact hp) (occ_moveAt mu q p hq)
    rw [moveAt_round_at p q mu hmp] at h
    exact h
  -- the first display, at the factor letters against the unit's
  have hD1 := units.matVec_table_read (moveAt i j mu) (moveAt q p mu)
    (moveAt q p (moveAt i j mu)) mu q p i j
    hIJmu hQPnu hQPmu hIJmu1
    (fun hgv => by
      by_cases hip : i = p
      · have heq : moveAt q p (moveAt i j mu) = mu := by
          rw [hgv, hip]
          exact moveAt_round_at j p mu hmj
        rw [heq, hip]
        exact out_diag mu p
      · by_cases hjp : j = p
        · have heq : moveAt q p (moveAt i j mu) = moveAt i j mu := by
            rw [hgv, ← hjp]
            exact moveAt_self j (moveAt i j mu)
              (by
                have h := hnp
                rw [← hjp] at h
                exact h)
          rw [heq, ← hjp]
          exact blockcount.out_gen mu i j hi hij
        · have heq : moveAt q p (moveAt i j mu) = moveAt i p mu := by
            rw [hgv]
            exact moveAt_chain' i j p mu hip hjp hmj
          rw [heq]
          exact blockcount.out_gen mu i p hi hip)
    (fun hgv => by
      by_cases hqj : q = j
      · have heq : moveAt q p (moveAt i j mu) = mu := by
          rw [hgv, hqj]
          exact moveAt_round_at j i mu hmj
        rw [heq, hqj]
        exact out_diag mu j
      · have heq : moveAt q p (moveAt i j mu) = moveAt q j mu := by
          rw [hgv]
          exact moveAt_chain q i j mu
        rw [heq]
        exact blockcount.out_gen mu q j hq hqj) x hx
  -- the second display, inside the first's middle term
  have hD2 := units.matVec_table_read
    (moveAt q p (moveAt i j mu)) mu (moveAt i j mu) (moveAt q p mu)
    p q i j
    hIJmu1 hPQnu1 hPQmu1 hIJmu
    (fun hgv => by
      by_cases hiq : i = q
      · have hsrc : moveAt q p mu = moveAt i j mu := by
          rw [hgv, ← hiq]
        rw [hsrc, ← hiq]
        exact out_diag (moveAt i j mu) i
      · have heq : moveAt i q (moveAt q p mu) = moveAt i j mu := by
          rw [hgv]
          exact moveAt_chain i q j mu
        have h := blockcount.out_gen (moveAt q p mu) i q
          (by rw [hlenMu1]; exact hi) hiq
        rw [heq] at h
        exact h)
    (fun hgv => by
      by_cases hpj : p = j
      · have hsrc : moveAt q p mu = moveAt i j mu := by
          rw [hgv, hpj]
        rw [hsrc, hpj]
        exact out_diag (moveAt i j mu) j
      · have heq : moveAt p j (moveAt q p mu) = moveAt i j mu := by
          rw [hgv]
          exact moveAt_chain' i p j mu hij hpj hmp
        have h := blockcount.out_gen (moveAt q p mu) p j
          (by rw [hlenMu1]; exact hp) hpj
        rw [heq] at h
        exact h)
    (yV mu p q x) hy
  -- the outer factor at the moved content, applied to the first
  have hPlen : (units.matUnitAt (moveAt i j mu)
      (moveAt q p (moveAt i j mu)) p q).length
      = (monomialsAt (moveAt i j mu)).length :=
    units.length_matUnitAt _ _ p q
  have hN1 : ∀ (T : elim.Mat) (c : List Nat), T.length
      = (monomialsAt c).length → ∀ v : List BPair,
      (elim.matVec T v).length = (monomialsAt c).length := by
    intro T c hT v
    rw [elim.matVec_length]
    exact hT
  have hL1a := hN1 (units.matUnitAt (moveAt q p (moveAt i j mu))
    (moveAt i j mu) q p) (moveAt q p (moveAt i j mu))
    (units.length_matUnitAt _ _ q p)
  have hL1b := lenIf (q = j) (units.matUnitAt
    (moveAt q p (moveAt i j mu)) mu i p) x
    (monomialsAt (moveAt q p (moveAt i j mu))).length
    (units.length_matUnitAt _ _ i p)
  have hR1a := hN1 (units.matUnitAt (moveAt q p (moveAt i j mu))
    (moveAt q p mu) i j) (moveAt q p (moveAt i j mu))
    (units.length_matUnitAt _ _ i j)
  have hR1b := lenIf (p = i) (units.matUnitAt
    (moveAt q p (moveAt i j mu)) mu q j) x
    (monomialsAt (moveAt q p (moveAt i j mu))).length
    (units.length_matUnitAt _ _ q j)
  have hD1P : poly.oneValue
      (elim.vecAdd
        (elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (elim.matVec (units.matUnitAt
            (moveAt q p (moveAt i j mu)) (moveAt i j mu) q p)
            (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
              x)))
        (elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (if q = j then elim.matVec (units.matUnitAt
              (moveAt q p (moveAt i j mu)) mu i p) x
            else List.replicate
              (monomialsAt (moveAt q p (moveAt i j mu))).length
              BPair.unit)))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (elim.matVec (units.matUnitAt
            (moveAt q p (moveAt i j mu)) (moveAt q p mu) i j)
            (yV mu p q x)))
        (elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (if p = i then elim.matVec (units.matUnitAt
              (moveAt q p (moveAt i j mu)) mu q j) x
            else List.replicate
              (monomialsAt (moveAt q p (moveAt i j mu))).length
              BPair.unit))) := by
    refine poly.oneValue_trans
      (poly.oneValue_symm (elim.matVec_vecAdd _
        (monomialsAt (moveAt q p (moveAt i j mu))).length
        (units.rowsLen_matUnitAt _ _ p q) _ _
        (hL1a _) hL1b)) ?_
    refine poly.oneValue_trans
      (elim.matVec_congr _ _ _ hD1) ?_
    exact elim.matVec_vecAdd _
      (monomialsAt (moveAt q p (moveAt i j mu))).length
      (units.rowsLen_matUnitAt _ _ p q) _ _ (hR1a _) hR1b
  -- the families' widths and the two product conversions
  have hMlen : (units.matUnitAt (moveAt i j mu) mu i j).length
      = (monomialsAt (moveAt i j mu)).length :=
    units.length_matUnitAt _ _ i j
  have hMx := hN1 _ (moveAt i j mu) hMlen x
  have hLL' : poly.oneValue
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt q p mu) p q)
          (units.matUnitAt (moveAt q p mu) mu q p)) x))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.matVec (units.matUnitAt mu (moveAt q p mu) p q)
          (yV mu p q x))) :=
    elim.matVec_congr _ _ _
      (elim.matVec_matMul _ _ (monomialsAt mu).length
        (units.rowsLen_matUnitAt (moveAt q p mu) mu q p) x hx)
  have hRR' : poly.oneValue
      (elim.matVec (elim.matMul
          (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (units.matUnitAt (moveAt q p (moveAt i j mu))
            (moveAt i j mu) q p))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x))
      (elim.matVec (units.matUnitAt (moveAt i j mu)
          (moveAt q p (moveAt i j mu)) p q)
        (elim.matVec (units.matUnitAt
          (moveAt q p (moveAt i j mu)) (moveAt i j mu) q p)
          (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
            x))) :=
    elim.matVec_matMul _ _ (monomialsAt (moveAt i j mu)).length
      (units.rowsLen_matUnitAt _ _ q p) _ hMx
  have hlenRR : (elim.matVec (elim.matMul
      (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (units.matUnitAt (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        x)).length = (monomialsAt (moveAt i j mu)).length := by
    rw [elim.matVec_length, elim.length_matMul]
    exact hPlen
  have hD2' : poly.oneValue
      (elim.vecAdd
        (elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (elim.matVec (units.matUnitAt
            (moveAt q p (moveAt i j mu)) (moveAt q p mu) i j)
            (yV mu p q x)))
        (bFam mu i j p q x))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.matVec (units.matUnitAt mu (moveAt q p mu) p q)
            (yV mu p q x)))
        (aFam mu i j p q x)) := hD2
  refine poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      (elim.polyOne_vecAdd _ _ _ _ hLL' (poly.oneValue_refl _)
        (by rw [elim.matVec_length, elim.matVec_length]) rfl)
      (poly.oneValue_refl _)
      (by rw [elim.length_vecAdd _ _ _
          (hN1 _ (moveAt i j mu) hMlen _) (len_aFam mu i j p q x),
        elim.length_vecAdd _ _ _
          (hN1 _ (moveAt i j mu) hMlen _) (len_aFam mu i j p q x)])
      rfl) ?_
  refine poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_symm hD2') (poly.oneValue_refl _)
      (by rw [elim.length_vecAdd _ _ _
          (hN1 _ (moveAt i j mu) hMlen _) (len_aFam mu i j p q x),
        elim.length_vecAdd _ _ _
          (hN1 _ (moveAt i j mu) hPlen _) (len_bFam mu i j p q x)])
      rfl) ?_
  rw [elim.vecAdd_assoc, elim.vecAdd_comm (bFam mu i j p q x)
    (dFam mu i j p q x), ← elim.vecAdd_assoc]
  refine elim.polyOne_vecAdd _ _ _ _ ?_ (poly.oneValue_refl _)
    (by rw [elim.length_vecAdd _ _ _
        (hN1 _ (moveAt i j mu) hPlen _) (len_dFam mu i j p q x),
      elim.length_vecAdd _ _ _ hlenRR (len_cFam mu i j p q x)])
    rfl
  refine poly.oneValue_symm (poly.oneValue_trans ?_
    (poly.oneValue_trans hD1P ?_))
  · exact elim.polyOne_vecAdd _ _ _ _ hRR'
      (poly.oneValue_symm (matVec_if _ (q = j) _ _ _ hPlen))
      (by rw [hlenRR, elim.matVec_length, hPlen])
      (by rw [len_cFam, elim.matVec_length, hPlen])
  · exact elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_refl _) (matVec_if _ (p = i) _ _ _ hPlen)
      rfl (by rw [elim.matVec_length, hPlen, len_dFam])

/-! The vacant-letter branches: at a factor's letter off the
content's support the term's surviving members close at the
display's own shorter instance (`lem:casimir`'s closure sentence),
the unit's letter supported throughout. -/

/-- The lowered letter vacant, away from the unit's raise: every
member of the join reads the unit tail. -/
private theorem termNullA (mu : List Nat) (i j p q : Nat)
    (_hij : ¬ i = j) (_hi : i < mu.length) (hip : ¬ i = p)
    (hmj : 0 < getAt 0 mu j) (hz : getAt 0 mu p = 0)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    joinAt mu i j p q x := by
  have hjp : ¬ p = j := by
    intro he
    rw [he] at hz
    rw [hz] at hmj
    exact absurd hmj (Nat.lt_irrefl 0)
  have hnz : getAt 0 (moveAt i j mu) p = 0 := by
    rw [getMove i j p mu (fun he => hip he.symm) hjp]
    exact hz
  have hyv : poly.unitTail (yV mu p q x) :=
    units.matVec_null_unocc (moveAt q p mu) mu q p hz x
  have hMx : (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
      x).length = (monomialsAt (moveAt i j mu)).length := by
    rw [units.matVec_matUnitAt_length]
  have hL : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i j mu) mu i j)
      (elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x)) :=
    elim.matVec_null _ _
      (compNull _ _ (monomialsAt mu).length
        (units.rowsLen_matUnitAt (moveAt q p mu) mu q p) x hx hyv)
  have hR : poly.unitTail (elim.matVec (elim.matMul
      (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (units.matUnitAt (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x)) :=
    compNull _ _ (monomialsAt (moveAt i j mu)).length
      (units.rowsLen_matUnitAt _ _ q p) _ hMx
      (units.matVec_null_unocc (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p hnz _)
  show poly.oneValue (elim.vecAdd (elim.vecAdd _ _) _)
    (elim.vecAdd (elim.vecAdd _ _) _)
  refine poly.unitTail_oneValue
    (elim.unitTail_vecAdd_of (elim.unitTail_vecAdd_of hL ?_) ?_)
    (elim.unitTail_vecAdd_of (elim.unitTail_vecAdd_of hR ?_) ?_)
  · exact nullIf (q = i) _ _ (elim.matVec_null _ _ hyv)
  · exact nullIfNeg (p = i) _ _ (fun he => hip he.symm)
  · exact nullIf (q = j) _ _ (elim.matVec_null _ _
      (units.matVec_null_unocc (moveAt q p (moveAt i j mu)) mu i p
        hz x))
  · exact nullIf (p = j) _ _ (elim.matVec_null _ _ hyv)

/-- The lowered letter vacant at the unit's own raise: the term's
surviving members are the moved family and the moved term, and they
close at the display's shorter instance through the vacant
content. -/
private theorem termNullB (mu : List Nat) (i j p q : Nat)
    (hij : ¬ i = j) (hi : i < mu.length) (hq : q < mu.length)
    (hgp : i = p) (hmj : 0 < getAt 0 mu j)
    (hz : getAt 0 mu p = 0)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    joinAt mu i j p q x := by
  have hlenNu : (moveAt i j mu).length = mu.length :=
    length_moveAt i j mu
  have hpj : ¬ p = j := by
    intro he
    rw [he] at hz
    rw [hz] at hmj
    exact absurd hmj (Nat.lt_irrefl 0)
  have hnp : 0 < getAt 0 (moveAt i j mu) p := by
    rw [← hgp]
    exact occ_moveAt mu i j hi
  have hyv : poly.unitTail (yV mu p q x) :=
    units.matVec_null_unocc (moveAt q p mu) mu q p hz x
  have hMx : (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
      x).length = (monomialsAt (moveAt i j mu)).length := by
    rw [units.matVec_matUnitAt_length]
  have hPlen : (units.matUnitAt (moveAt i j mu)
      (moveAt q p (moveAt i j mu)) p q).length
      = (monomialsAt (moveAt i j mu)).length :=
    units.length_matUnitAt _ _ p q
  have hvac : ∀ (c : List Nat) (a b : Nat), getAt 0 c b = 0 →
      ∀ s m : List Nat,
        0 < ground.countOf s (monomialsAt c) →
        0 < ground.countOf m (units.unitAct a b s) →
        m.length = sumNat ([] : List Nat)
          ∧ content ([] : List Nat).length m = ([] : List Nat) := by
    intro c a b hcb s m hs hm
    rw [units.unitAct_nil_of_zero a b s
      (places.letter_zero c b hcb s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  have hvacNil : ∀ (c : List Nat) (a b : Nat),
      ∀ s m : List Nat,
        0 < ground.countOf s (monomialsAt ([] : List Nat)) →
        0 < ground.countOf m (units.unitAct a b s) →
        m.length = sumNat c ∧ content c.length m = c := by
    intro c a b s m hs hm
    rw [units.unitAct_nil_of_zero a b s
      (places.letter_zero ([] : List Nat) b rfl s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  have hread := units.matVec_table_read (moveAt i j mu)
    ([] : List Nat) (moveAt q p (moveAt i j mu)) mu q p i j
    (blockcount.out_gen mu i j hi hij)
    (outMove (moveAt i j mu) q p (by rw [hlenNu]; exact hq) hnp)
    (hvac mu q p hz) (hvacNil (moveAt q p (moveAt i j mu)) i j)
    (fun hgv => by
      have heq : moveAt q p (moveAt i j mu) = mu := by
        rw [hgv, ← hgp]
        exact moveAt_round_at j i mu hmj
      rw [heq, ← hgp]
      exact out_diag mu i)
    (fun _ => by
      have heq : moveAt q p (moveAt i j mu) = moveAt q j mu := by
        rw [← hgp]
        exact moveAt_chain q i j mu
      rw [heq]
      exact outMove mu q j hq hmj)
    x hx
  -- the shorter instance: the two vacant members drop
  have hcore : poly.oneValue
      (elim.matVec (units.matUnitAt
        (moveAt q p (moveAt i j mu)) (moveAt i j mu) q p)
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x))
      (elim.matVec (units.matUnitAt
        (moveAt q p (moveAt i j mu)) mu q j) x) := by
    have h1 : poly.unitTail (if q = j then elim.matVec
        (units.matUnitAt (moveAt q p (moveAt i j mu)) mu i p) x
      else List.replicate
        (monomialsAt (moveAt q p (moveAt i j mu))).length
        BPair.unit) :=
      nullIf (q = j) _ _
        (units.matVec_null_unocc _ mu i p hz x)
    have h2 : poly.unitTail (elim.matVec (units.matUnitAt
        (moveAt q p (moveAt i j mu)) ([] : List Nat) i j)
        (elim.matVec (units.matUnitAt ([] : List Nat) mu q p) x)) :=
      elim.matVec_null _ _
        (units.matVec_null_unocc ([] : List Nat) mu q p hz x)
    have hlq : ∀ T : elim.Mat, T.length
        = (monomialsAt (moveAt q p (moveAt i j mu))).length →
        ∀ v : List BPair, (elim.matVec T v).length
          = (monomialsAt (moveAt q p (moveAt i j mu))).length := by
      intro T hT v
      rw [elim.matVec_length]
      exact hT
    refine poly.oneValue_trans
      (poly.oneValue_symm (elim.vecAdd_null_right _ _
        (by rw [hlq _ (units.length_matUnitAt _ _ q p) _,
          lenIf (q = j) (units.matUnitAt
            (moveAt q p (moveAt i j mu)) mu i p) x _
            (units.length_matUnitAt _ _ i p)]) h1)) ?_
    refine poly.oneValue_trans hread ?_
    refine poly.oneValue_trans (elim.vecAdd_null_left _ _
      (by rw [hlq _ (units.length_matUnitAt _ _ i j) _,
        lenIf (p = i) (units.matUnitAt
          (moveAt q p (moveAt i j mu)) mu q j) x _
          (units.length_matUnitAt _ _ q j)]) h2) ?_
    rw [if_pos hgp.symm]
    exact poly.oneValue_refl _
  have hL : poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i j mu) mu i j)
      (elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x)) :=
    elim.matVec_null _ _
      (compNull _ _ (monomialsAt mu).length
        (units.rowsLen_matUnitAt (moveAt q p mu) mu q p) x hx hyv)
  have hRlen : (elim.matVec (elim.matMul
      (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (units.matUnitAt (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        x)).length = (monomialsAt (moveAt i j mu)).length := by
    rw [elim.matVec_length, elim.length_matMul]
    exact hPlen
  have hLlen : (elim.matVec
      (units.matUnitAt (moveAt i j mu) mu i j)
      (elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x)).length
      = (monomialsAt (moveAt i j mu)).length := by
    rw [elim.matVec_length]
    exact units.length_matUnitAt _ _ i j
  have hDR : poly.oneValue (dFam mu i j p q x)
      (elim.matVec (elim.matMul
          (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (units.matUnitAt (moveAt q p (moveAt i j mu))
            (moveAt i j mu) q p))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          x)) := by
    show poly.oneValue (if p = i then _ else _) _
    rw [if_pos hgp.symm]
    refine poly.oneValue_trans ?_ (poly.oneValue_symm
      (elim.matVec_matMul _ _ (monomialsAt (moveAt i j mu)).length
        (units.rowsLen_matUnitAt _ _ q p) _ hMx))
    exact elim.matVec_congr _ _ _
      (poly.oneValue_symm hcore)
  show poly.oneValue (elim.vecAdd (elim.vecAdd _ _) _)
    (elim.vecAdd (elim.vecAdd _ _) _)
  refine poly.oneValue_trans
    (elim.vecAdd_null_left _ _
      (by rw [elim.length_vecAdd _ _ _ hLlen (len_aFam mu i j p q x),
        len_dFam])
      (elim.unitTail_vecAdd_of hL
        (nullIf (q = i) _ _ (elim.matVec_null _ _ hyv)))) ?_
  refine poly.oneValue_trans hDR ?_
  refine poly.oneValue_symm (poly.oneValue_trans
    (elim.vecAdd_null_right _ _
      (by rw [elim.length_vecAdd _ _ _ hRlen (len_cFam mu i j p q x),
        len_bFam])
      (nullIfNeg (p = j) _ _ hpj)) ?_)
  exact elim.vecAdd_null_right _ _
    (by rw [hRlen, len_cFam])
    (nullIf (q = j) _ _ (elim.matVec_null _ _
      (units.matVec_null_unocc (moveAt q p (moveAt i j mu)) mu i p
        hz x)))

/-- The unit's letter re-raised at its vacant moved content names a
content the raising does not reach: the matrix between them is the
null map (`con:units`' grading). -/
private theorem offNull_jj (mu : List Nat) (i j : Nat)
    (hij : ¬ i = j) (hi : i < mu.length) (hj : j < mu.length)
    (hnzj : getAt 0 (moveAt i j mu) j = 0) :
    elim.matNull (units.matUnitAt
      (moveAt j j (moveAt i j mu)) mu i j) := by
  refine units.matUnitAt_null_offcontent _ mu i j ?_
  intro s m hs hm hc
  have hgen := blockcount.out_gen mu i j hi hij s m hs hm
  have hlen1 : (moveAt j j (moveAt i j mu)).length = mu.length := by
    rw [length_moveAt, length_moveAt]
  have hlen2 : (moveAt i j mu).length = mu.length :=
    length_moveAt i j mu
  have h2 : content (moveAt i j mu).length m
      = moveAt j j (moveAt i j mu) := by
    have h2' := hc.2
    rw [hlen1, ← hlen2] at h2'
    exact h2'
  have heq : moveAt i j mu = moveAt j j (moveAt i j mu) :=
    hgen.2.symm.trans h2
  have hread := congrArg (fun l => getAt 0 l j) heq
  have hup : getAt 0 (moveAt j j (moveAt i j mu)) j
      = getAt 0 (dipAt j (moveAt i j mu)) j + 1 := by
    show getAt 0 (bumpAt j (dipAt j (moveAt i j mu))) j = _
    exact getAt_bumpAt_self j (dipAt j (moveAt i j mu))
      (by rw [length_dipAt, hlen2]; exact hj)
  rw [hnzj, hup] at hread
  exact Nat.noConfusion hread

/-- The raised letter vacant at the moved content (the lowered
letter the unit's own at its one count): the moved term, both
moved families and one delta family read the unit tail, and the
term's surviving member closes on the further delta family at the
display's shorter instance. -/
private theorem termNullC (mu : List Nat) (i j p q : Nat)
    (hij : ¬ i = j) (hi : i < mu.length) (hj : j < mu.length)
    (_hq : q < mu.length) (hmj : 0 < getAt 0 mu j)
    (hmp : 0 < getAt 0 mu p)
    (hnz : getAt 0 (moveAt i j mu) p = 0)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    joinAt mu i j p q x := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hpj : p = j := by
    by_cases hh : p = j
    · exact hh
    · by_cases hpi : p = i
      · rw [hpi] at hnz
        have hocc := occ_moveAt mu i j hi
        rw [hnz] at hocc
        exact absurd hocc (Nat.lt_irrefl 0)
      · rw [getMove i j p mu hpi hh] at hnz
        rw [hnz] at hmp
        exact absurd hmp (Nat.lt_irrefl 0)
  have hpi : ¬ p = i := fun he => hij (he.symm.trans hpj)
  have hnzj : getAt 0 (moveAt i j mu) j = 0 := by
    have h := hnz
    rw [hpj] at h
    exact h
  have hmj1 : getAt 0 mu j = 1 := by
    have hd := getAt_dipAt_self j mu hmj
    have hb : getAt 0 (moveAt i j mu) j
        = getAt 0 (dipAt j mu) j := by
      show getAt 0 (bumpAt i (dipAt j mu)) j = _
      exact getAt_bumpAt_ne i (dipAt j mu) j hji
    have hnzj' : getAt 0 (dipAt j mu) j = 0 := by
      rw [← hb]
      exact hnzj
    rw [hnzj'] at hd
    exact hd.symm
  have hMx : (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
      x).length = (monomialsAt (moveAt i j mu)).length := by
    rw [units.matVec_matUnitAt_length]
  have hRN : poly.unitTail (elim.matVec (elim.matMul
      (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (units.matUnitAt (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x)) :=
    compNull _ _ (monomialsAt (moveAt i j mu)).length
      (units.rowsLen_matUnitAt _ _ q p) _ hMx
      (units.matVec_null_unocc (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p hnz _)
  have haN : poly.unitTail (aFam mu i j p q x) := by
    refine nullIfOf (q = i) _ _ (fun he => ?_)
    refine units.matVec_null_unocc (moveAt i j mu)
      (moveAt q p mu) p j ?_ (yV mu p q x)
    have hjq : ¬ j = q := fun hh => hij ((hh.trans he).symm)
    show getAt 0 (bumpAt q (dipAt p mu)) j = 0
    rw [getAt_bumpAt_ne q (dipAt p mu) j hjq, hpj]
    have hd := getAt_dipAt_self j mu hmj
    rw [hmj1] at hd
    exact Nat.succ.inj hd
  have hcN : poly.unitTail (cFam mu i j p q x) := by
    refine nullIfOf (q = j) _ _ (fun he => ?_)
    show poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (elim.matVec (units.matUnitAt
        (moveAt q p (moveAt i j mu)) mu i p) x))
    rw [he, hpj]
    exact elim.matVec_null _ _
      (elim.matVec_matNull _ x (offNull_jj mu i j hij hi hj hnzj))
  have hdN : poly.unitTail (dFam mu i j p q x) :=
    nullIfNeg (p = i) _ _ hpi
  have hLB : poly.oneValue
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt q p mu) p q)
          (units.matUnitAt (moveAt q p mu) mu q p)) x))
      (bFam mu i j p q x) := by
    rw [hpj]
    have hbf : bFam mu i j j q x
        = elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q j mu) i q) (yV mu j q x) := by
      show (if (j : Nat) = j then _ else _) = _
      rw [if_pos rfl]
    rw [hbf]
    by_cases hqj : q = j
    · rw [hqj]
      have hyveq : yV mu j j x
          = elim.matVec (units.matUnitAt (moveAt j j mu) mu j j)
            x := rfl
      have hms : moveAt j j mu = mu := moveAt_self j mu hmj
      have hone : poly.oneValue (elim.vecScale (sqTerm mu j) x) x := by
        have hsq : sqTerm mu j = BPair.ofNat 1 := by
          show BPair.ofNat (getAt 0 mu j * getAt 0 mu j) = _
          rw [hmj1]
        rw [hsq]
        exact elim.vecScale_one x
      have hone2 : poly.oneValue
          (elim.vecScale (BPair.ofNat (getAt 0 mu j)) x) x := by
        rw [hmj1]
        exact elim.vecScale_one x
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _
          (diagAt mu j hj x hx)) ?_
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _ hone) ?_
      refine poly.oneValue_symm ?_
      rw [hyveq, hms]
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _
          (units.matVec_diag_read mu j hj x hx)) ?_
      exact elim.matVec_congr _ _ _ hone2
    · have hz1 : getAt 0 (moveAt q j mu) j = 0 := by
        show getAt 0 (bumpAt q (dipAt j mu)) j = 0
        rw [getAt_bumpAt_ne q (dipAt j mu) j
          (fun hh => hqj hh.symm)]
        have hd := getAt_dipAt_self j mu hmj
        rw [hmj1] at hd
        exact Nat.succ.inj hd
      have hy : (yV mu j q x).length
          = (monomialsAt (moveAt q j mu)).length := by
        show (elim.matVec (units.matUnitAt (moveAt q j mu) mu q j)
          x).length = _
        rw [units.matVec_matUnitAt_length]
      have hvac1 : ∀ s m : List Nat,
          0 < ground.countOf s (monomialsAt (moveAt q j mu)) →
          0 < ground.countOf m (units.unitAct i j s) →
          m.length = sumNat ([] : List Nat)
            ∧ content ([] : List Nat).length m
              = ([] : List Nat) := by
        intro s m hs hm
        rw [units.unitAct_nil_of_zero i j s
          (places.letter_zero (moveAt q j mu) j hz1 s hs)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      have hvac2 : ∀ s m : List Nat,
          0 < ground.countOf s (monomialsAt ([] : List Nat)) →
          0 < ground.countOf m (units.unitAct j q s) →
          m.length = sumNat (moveAt i j mu)
            ∧ content (moveAt i j mu).length m
              = moveAt i j mu := by
        intro s m hs hm
        rw [units.unitAct_nil_of_zero j q s
          (places.letter_zero ([] : List Nat) q rfl s hs)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      have hvac3 : i = q → ∀ s m : List Nat,
          0 < ground.countOf s (monomialsAt (moveAt q j mu)) →
          0 < ground.countOf m (units.unitAct j j s) →
          m.length = sumNat (moveAt i j mu)
            ∧ content (moveAt i j mu).length m
              = moveAt i j mu := by
        intro _ s m hs hm
        rw [units.unitAct_nil_of_zero j j s
          (places.letter_zero (moveAt q j mu) j hz1 s hs)] at hm
        exact absurd hm (Nat.lt_irrefl 0)
      have hIQ : j = j → ∀ s m : List Nat,
          0 < ground.countOf s (monomialsAt (moveAt q j mu)) →
          0 < ground.countOf m (units.unitAct i q s) →
          m.length = sumNat (moveAt i j mu)
            ∧ content (moveAt i j mu).length m
              = moveAt i j mu := by
        intro _
        by_cases hiq : i = q
        · have heq : moveAt q j mu = moveAt i j mu := by
            rw [hiq]
          rw [heq]
          intro s m hs hm
          rw [hiq] at hm
          exact out_diag (moveAt i j mu) q s m hs hm
        · have h := blockcount.out_gen (moveAt q j mu) i q
            (by rw [length_moveAt]; exact hi) hiq
          rw [moveAt_chain i q j mu] at h
          exact h
      have hJQ : ∀ s m : List Nat,
          0 < ground.countOf s (monomialsAt (moveAt q j mu)) →
          0 < ground.countOf m (units.unitAct j q s) →
          m.length = sumNat mu ∧ content mu.length m = mu := by
        have h := blockcount.out_gen (moveAt q j mu) j q
          (by rw [length_moveAt]; exact hj) (fun hh => hqj hh.symm)
        rw [moveAt_round_at j q mu hmj] at h
        exact h
      have hread := units.matVec_table_read mu ([] : List Nat)
        (moveAt i j mu) (moveAt q j mu) i j j q
        hJQ (blockcount.out_gen mu i j hi hij)
        hvac1 hvac2 hvac3 hIQ (yV mu j q x) hy
      have hlm : ∀ T : elim.Mat, T.length
          = (monomialsAt (moveAt i j mu)).length →
          ∀ v : List BPair, (elim.matVec T v).length
            = (monomialsAt (moveAt i j mu)).length := by
        intro T hT v
        rw [elim.matVec_length]
        exact hT
      have hd1 : poly.unitTail (if i = q then
          elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q j mu) j j) (yV mu j q x)
        else List.replicate
          (monomialsAt (moveAt i j mu)).length BPair.unit) :=
        nullIf (i = q) _ _
          (units.matVec_null_unocc (moveAt i j mu)
            (moveAt q j mu) j j hz1 (yV mu j q x))
      have hd2 : poly.unitTail (elim.matVec (units.matUnitAt
          (moveAt i j mu) ([] : List Nat) j q)
          (elim.matVec (units.matUnitAt ([] : List Nat)
            (moveAt q j mu) i j) (yV mu j q x))) :=
        elim.matVec_null _ _
          (units.matVec_null_unocc ([] : List Nat)
            (moveAt q j mu) i j hz1 (yV mu j q x))
      have hcore : poly.oneValue
          (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
            (elim.matVec (units.matUnitAt mu (moveAt q j mu) j q)
              (yV mu j q x)))
          (elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q j mu) i q) (yV mu j q x)) := by
        refine poly.oneValue_trans
          (poly.oneValue_symm (elim.vecAdd_null_right _ _
            (by rw [hlm _ (units.length_matUnitAt _ _ i j) _,
              lenIf (i = q) (units.matUnitAt (moveAt i j mu)
                (moveAt q j mu) j j) (yV mu j q x) _
                (units.length_matUnitAt _ _ j j)]) hd1)) ?_
        refine poly.oneValue_trans hread ?_
        refine poly.oneValue_trans (elim.vecAdd_null_left _ _
          (by rw [hlm _ (units.length_matUnitAt _ _ j q) _,
            lenIf (j = j) (units.matUnitAt (moveAt i j mu)
              (moveAt q j mu) i q) (yV mu j q x) _
              (units.length_matUnitAt _ _ i q)]) hd2) ?_
        rw [if_pos rfl]
        exact poly.oneValue_refl _
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _
          (elim.matVec_matMul _ _ (monomialsAt mu).length
            (units.rowsLen_matUnitAt (moveAt q j mu) mu q j)
            x hx)) ?_
      exact hcore
  have hLlen : (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
      (elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x)).length
      = (monomialsAt (moveAt i j mu)).length := by
    rw [units.matVec_matUnitAt_length]
  have hRlen : (elim.matVec (elim.matMul
      (units.matUnitAt (moveAt i j mu)
        (moveAt q p (moveAt i j mu)) p q)
      (units.matUnitAt (moveAt q p (moveAt i j mu))
        (moveAt i j mu) q p))
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        x)).length = (monomialsAt (moveAt i j mu)).length := by
    rw [elim.matVec_length, elim.length_matMul,
      units.length_matUnitAt]
  show poly.oneValue (elim.vecAdd (elim.vecAdd _ _) _)
    (elim.vecAdd (elim.vecAdd _ _) _)
  refine poly.oneValue_trans
    (elim.vecAdd_null_right _ _
      (by rw [elim.length_vecAdd _ _ _ hLlen
          (len_aFam mu i j p q x), len_dFam]) hdN) ?_
  refine poly.oneValue_trans
    (elim.vecAdd_null_right _ _
      (by rw [hLlen, len_aFam]) haN) ?_
  refine poly.oneValue_trans hLB ?_
  refine poly.oneValue_symm ?_
  exact elim.vecAdd_null_left _ _
    (by rw [elim.length_vecAdd _ _ _ hRlen
        (len_cFam mu i j p q x), len_bFam])
    (elim.unitTail_vecAdd_of hRN hcN)

/-! The collection: the per-pair joins summed over the double
range, the delta families picked at their guards, the two family
identifications at the chain reads, and the shared summands
cleared at the memberwise cancellation. -/

/-- The dispatcher: every letter configuration's join, the
occupancy trichotomy at the factor's lowered letter. -/
private theorem joinAll (mu : List Nat) (i j p q : Nat)
    (hij : ¬ i = j) (hi : i < mu.length) (hj : j < mu.length)
    (hp : p < mu.length) (hq : q < mu.length)
    (hmj : 0 < getAt 0 mu j)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    joinAt mu i j p q x := by
  by_cases hmp : 0 < getAt 0 mu p
  · by_cases hnp : 0 < getAt 0 (moveAt i j mu) p
    · exact termJoin mu i j p q hij hi hp hq hmj hmp hnp x hx
    · exact termNullC mu i j p q hij hi hj hq hmj hmp
        (match Nat.eq_zero_or_pos (getAt 0 (moveAt i j mu) p) with
          | .inl h => h
          | .inr h => absurd h hnp) x hx
  · have hz : getAt 0 mu p = 0 :=
      match Nat.eq_zero_or_pos (getAt 0 mu p) with
      | .inl h => h
      | .inr h => absurd h hmp
    by_cases hip : i = p
    · exact termNullB mu i j p q hij hi hq hip hmj hz x hx
    · exact termNullA mu i j p q hij hi hip hmj hz x hx

/-- A guarded summand's width, either branch. -/
private theorem lenIfGen (g : Prop) [Decidable g] (u : List BPair)
    (m : Nat) (hu : u.length = m) :
    (if g then u else List.replicate m BPair.unit).length = m := by
  by_cases hgv : g
  · rw [if_pos hgv]
    exact hu
  · rw [if_neg hgv]
    exact ground.length_replicate _ _

/-- The guarded summand reads its guard either way round. -/
private theorem ifSymm (a b : Nat) (u : List BPair) (n : Nat) :
    (if a = b then u else List.replicate n BPair.unit)
      = (if b = a then u else List.replicate n BPair.unit) := by
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

/-- Two families reading one value at the fold's members read one
value at the fold. -/
private theorem vsumCongrMem (n : Nat) (g g' : Nat → List BPair)
    (hg : ∀ k, (g k).length = n) (hg' : ∀ k, (g' k).length = n) :
    ∀ l : List Nat,
      (∀ k, 0 < ground.countOf k l →
        poly.oneValue (g k) (g' k)) →
      poly.oneValue (elim.vsum n g l) (elim.vsum n g' l)
  | [], _ => poly.oneValue_refl _
  | k :: t, h =>
    poly.oneValue_trans (elim.vsum_cons n g hg k t)
      (poly.oneValue_trans
        (elim.polyOne_vecAdd _ _ _ _
          (h k (by rw [ground.countOf_head]; exact Nat.succ_pos _))
          (vsumCongrMem n g g' hg hg' t (fun k' hk' =>
            h k' (Nat.lt_of_lt_of_le hk' (Nat.le_add_left _ _))))
          ((hg k).trans (hg' k).symm)
          ((elim.length_vsum n g t (fun a _ => hg a)).trans
            (elim.length_vsum n g' t (fun a _ => hg' a)).symm))
        (poly.oneValue_symm (elim.vsum_cons n g' hg' k t)))

/-- The inner-guarded family's double read picks its own key. -/
private theorem pickInner (m d i : Nat) (hi : i < d)
    (body : Nat → List BPair)
    (hbody : ∀ q, (body q).length = m) :
    poly.oneValue
      (elim.vsum m (fun q => if q = i then body q
        else List.replicate m BPair.unit) (List.range d))
      (body i) := by
  refine poly.oneValue_trans
    (elim.vsum_congr m _
      (fun q => if i = q then body q
        else List.replicate m BPair.unit)
      (fun q => lenIfGen (q = i) (body q) m (hbody q))
      (fun q => lenIfGen (i = q) (body q) m (hbody q))
      (fun q => by
        rw [ifSymm q i]
        exact poly.oneValue_refl _) (List.range d)) ?_
  exact elim.vsum_pick m body hbody (List.range d) i
    (by rw [countOf_range_one hi])

/-- The outer-guarded family's double read picks its own key, the
off-guard rows folding to the unit tail. -/
private theorem pickOuter (m d i : Nat) (hi : i < d)
    (body : Nat → Nat → List BPair)
    (hbody : ∀ p q, (body p q).length = m) :
    poly.oneValue
      (elim.vsum m (fun p => elim.vsum m
        (fun q => if p = i then body p q
          else List.replicate m BPair.unit) (List.range d))
        (List.range d))
      (elim.vsum m (fun q => body i q) (List.range d)) := by
  have hlenIn : ∀ p, (elim.vsum m
      (fun q => if p = i then body p q
        else List.replicate m BPair.unit) (List.range d)).length
      = m :=
    fun p => elim.length_vsum m _ _
      (fun q _ => lenIfGen (p = i) (body p q) m (hbody p q))
  have hG : ∀ p, (elim.vsum m (fun q => body p q)
      (List.range d)).length = m :=
    fun p => elim.length_vsum m _ _ (fun q _ => hbody p q)
  refine poly.oneValue_trans
    (elim.vsum_congr m _
      (fun p => if i = p then elim.vsum m (fun q => body p q)
        (List.range d) else List.replicate m BPair.unit)
      hlenIn
      (fun p => lenIfGen (i = p) _ m (hG p))
      (fun p => ?_) (List.range d)) ?_
  · by_cases hip : i = p
    · rw [if_pos hip]
      refine elim.vsum_congr m _ _
        (fun q => lenIfGen (p = i) (body p q) m (hbody p q))
        (fun q => hbody p q)
        (fun q => by
          rw [if_pos hip.symm]
          exact poly.oneValue_refl _) (List.range d)
    · rw [if_neg hip]
      refine poly.unitTail_oneValue
        (elim.vsum_null m _
          (fun q => lenIfGen (p = i) (body p q) m (hbody p q))
          (List.range d) (fun q _ => ?_))
        (poly.unitTail_replicate m)
      rw [if_neg (fun he => hip he.symm)]
      exact poly.unitTail_replicate m
  · exact elim.vsum_pick m
      (fun p => elim.vsum m (fun q => body p q) (List.range d))
      hG (List.range d) i
      (by rw [countOf_range_one hi])

/-- The picked families identify: the first family's inner-picked
member at the shared second letter is the moved family's, the
contents chained at the supported unit letter with the vacant
configurations null on both members. -/
private theorem famAC (mu : List Nat) (i j p : Nat)
    (hij : ¬ i = j) (hi : i < mu.length) (hj : j < mu.length)
    (hmj : 0 < getAt 0 mu j)
    (x : List BPair) :
    poly.oneValue
      (elim.matVec (units.matUnitAt (moveAt i j mu)
          (moveAt i p mu) p j)
        (elim.matVec (units.matUnitAt (moveAt i p mu) mu i p) x))
      (elim.matVec (units.matUnitAt (moveAt i j mu)
          (moveAt j p (moveAt i j mu)) p j)
        (elim.matVec (units.matUnitAt
          (moveAt j p (moveAt i j mu)) mu i p) x)) := by
  by_cases hpi : p = i
  · by_cases hoi : 0 < getAt 0 mu i
    · rw [hpi, moveAt_self i mu hoi, moveAt_round_at j i mu hmj]
      exact poly.oneValue_refl _
    · have hz : getAt 0 mu i = 0 :=
        match Nat.eq_zero_or_pos (getAt 0 mu i) with
        | .inl h => h
        | .inr h => absurd h hoi
      rw [hpi]
      exact poly.unitTail_oneValue
        (elim.matVec_null _ _
          (units.matVec_null_unocc (moveAt i i mu) mu i i hz x))
        (elim.matVec_null _ _
          (units.matVec_null_unocc
            (moveAt j i (moveAt i j mu)) mu i i hz x))
  · by_cases hpj2 : p = j
    · by_cases hnu : 0 < getAt 0 (moveAt i j mu) j
      · rw [hpj2, moveAt_self j (moveAt i j mu) hnu]
        exact poly.oneValue_refl _
      · have hzn : getAt 0 (moveAt i j mu) j = 0 :=
          match Nat.eq_zero_or_pos
            (getAt 0 (moveAt i j mu) j) with
          | .inl h => h
          | .inr h => absurd h hnu
        rw [hpj2]
        refine poly.unitTail_oneValue
          (units.matVec_null_unocc (moveAt i j mu)
            (moveAt i j mu) j j hzn _) ?_
        exact elim.matVec_null _ _
          (elim.matVec_matNull _ x (offNull_jj mu i j hij hi hj hzn))
    · rw [moveAt_chain' i j p mu (fun he => hpi he.symm)
        (fun he => hpj2 he.symm) hmj]
      exact poly.oneValue_refl _

/-- The double fold splits over the join's three summands. -/
private theorem splitSums (m : Nat)
    (F G H : Nat → Nat → List BPair) (l : List Nat)
    (hF : ∀ p q, (F p q).length = m)
    (hG : ∀ p q, (G p q).length = m)
    (hH : ∀ p q, (H p q).length = m) :
    poly.oneValue
      (elim.vsum m (fun p => elim.vsum m (fun q =>
        elim.vecAdd (elim.vecAdd (F p q) (G p q)) (H p q)) l) l)
      (elim.vecAdd (elim.vecAdd
          (elim.vsum m (fun p => elim.vsum m
            (fun q => F p q) l) l)
          (elim.vsum m (fun p => elim.vsum m
            (fun q => G p q) l) l))
        (elim.vsum m (fun p => elim.vsum m
          (fun q => H p q) l) l)) := by
  have hFG : ∀ p q, (elim.vecAdd (F p q) (G p q)).length = m :=
    fun p q => elim.length_vecAdd _ _ m (hF p q) (hG p q)
  have hFGH : ∀ p q, (elim.vecAdd (elim.vecAdd (F p q) (G p q))
      (H p q)).length = m :=
    fun p q => elim.length_vecAdd _ _ m (hFG p q) (hH p q)
  have hvF : ∀ p, (elim.vsum m (fun q => F p q) l).length = m :=
    fun p => elim.length_vsum m _ _ (fun q _ => hF p q)
  have hvG : ∀ p, (elim.vsum m (fun q => G p q) l).length = m :=
    fun p => elim.length_vsum m _ _ (fun q _ => hG p q)
  have hvH : ∀ p, (elim.vsum m (fun q => H p q) l).length = m :=
    fun p => elim.length_vsum m _ _ (fun q _ => hH p q)
  have hstep : ∀ p, poly.oneValue
      (elim.vsum m (fun q =>
        elim.vecAdd (elim.vecAdd (F p q) (G p q)) (H p q)) l)
      (elim.vecAdd (elim.vecAdd
          (elim.vsum m (fun q => F p q) l)
          (elim.vsum m (fun q => G p q) l))
        (elim.vsum m (fun q => H p q) l)) := by
    intro p
    refine poly.oneValue_trans
      (elim.vsum_vecAdd m
        (fun q => elim.vecAdd (F p q) (G p q))
        (fun q => H p q) (hFG p) (hH p) l) ?_
    refine elim.polyOne_vecAdd _ _ _ _
      (elim.vsum_vecAdd m (fun q => F p q) (fun q => G p q)
        (hF p) (hG p) l)
      (poly.oneValue_refl _)
      (by rw [elim.length_vsum m _ l (fun q _ => hFG p q),
        elim.length_vecAdd _ _ m (hvF p) (hvG p)])
      rfl
  refine poly.oneValue_trans
    (elim.vsum_congr m _
      (fun p => elim.vecAdd (elim.vecAdd
          (elim.vsum m (fun q => F p q) l)
          (elim.vsum m (fun q => G p q) l))
        (elim.vsum m (fun q => H p q) l))
      (fun p => elim.length_vsum m _ _ (fun q _ => hFGH p q))
      (fun p => elim.length_vecAdd _ _ m
        (elim.length_vecAdd _ _ m (hvF p) (hvG p)) (hvH p))
      hstep l) ?_
  refine poly.oneValue_trans
    (elim.vsum_vecAdd m
      (fun p => elim.vecAdd (elim.vsum m (fun q => F p q) l)
        (elim.vsum m (fun q => G p q) l))
      (fun p => elim.vsum m (fun q => H p q) l)
      (fun p => elim.length_vecAdd _ _ m (hvF p) (hvG p))
      hvH l) ?_
  refine elim.polyOne_vecAdd _ _ _ _
    (elim.vsum_vecAdd m
      (fun p => elim.vsum m (fun q => F p q) l)
      (fun p => elim.vsum m (fun q => G p q) l) hvF hvG l)
    (poly.oneValue_refl _)
    (by rw [elim.length_vsum m _ l (fun p _ =>
        elim.length_vecAdd _ _ m (hvF p) (hvG p)),
      elim.length_vecAdd _ _ m
        (elim.length_vsum m _ l (fun p _ => hvF p))
        (elim.length_vsum m _ l (fun p _ => hvG p))])
    rfl

/-- `lem:casimir`'s moved reads: the `C` family commutes past every
letter pair — the `(p,q)`-fold collects each side's delta families
to the one join, the two folds a summand on both members fixing the
value. -/
theorem casimirM_comm (d : Nat) (mu : List Nat) (i j : Nat)
    (hi : i < d) (hj : j < d) (hij : ¬ i = j) (hd : mu.length = d)
    (x : List BPair)
    (hx : x.length = (places.monomialsAt mu).length) :
    poly.oneValue
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.matVec (casimirM d mu) x))
      (elim.matVec (casimirM d (moveAt i j mu))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          x)) := by
  by_cases hmj : 0 < getAt 0 mu j
  · have hiL : i < mu.length := by rw [hd]; exact hi
    have hjL : j < mu.length := by rw [hd]; exact hj
    have hlenC : (casimirM d mu).length
        = (monomialsAt mu).length :=
      elim.sqAt_len (casimirM_sq d mu)
    have hMx : (elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j) x).length
        = (monomialsAt (moveAt i j mu)).length := by
      rw [units.matVec_matUnitAt_length]
    have hterm : ∀ p q, (elim.matVec (elim.matMul
        (units.matUnitAt mu (moveAt q p mu) p q)
        (units.matUnitAt (moveAt q p mu) mu q p)) x).length
          = (monomialsAt mu).length := by
      intro p q
      rw [elim.matVec_length]
      exact (termShape mu p q).1
    have hLpq : ∀ p q, (elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt q p mu) p q)
          (units.matUnitAt (moveAt q p mu) mu q p)) x)).length
        = (monomialsAt (moveAt i j mu)).length := by
      intro p q
      rw [units.matVec_matUnitAt_length]
    have hRpq : ∀ p q, (elim.matVec (elim.matMul
        (units.matUnitAt (moveAt i j mu)
          (moveAt q p (moveAt i j mu)) p q)
        (units.matUnitAt (moveAt q p (moveAt i j mu))
          (moveAt i j mu) q p))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          x)).length = (monomialsAt (moveAt i j mu)).length := by
      intro p q
      rw [elim.matVec_length, elim.length_matMul,
        units.length_matUnitAt]
    -- the bridge: the left side to the double fold
    have hLb : poly.oneValue
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.matVec (casimirM d mu) x))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => elim.matVec
              (units.matUnitAt (moveAt i j mu) mu i j)
              (elim.matVec (elim.matMul
                (units.matUnitAt mu (moveAt q p mu) p q)
                (units.matUnitAt (moveAt q p mu) mu q p)) x))
            (List.range d))
          (List.range d)) := by
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _
          (casimirM_vsum d mu x)) ?_
      refine poly.oneValue_trans
        (elim.matVec_vsum (monomialsAt mu).length
          (units.matUnitAt (moveAt i j mu) mu i j)
          _ (fun p => elim.length_vsum _ _ _
            (fun q _ => hterm p q))
          (List.range d)) ?_
      rw [units.length_matUnitAt]
      refine elim.vsum_congr (monomialsAt (moveAt i j mu)).length
        _ _
        (fun p => by
          rw [units.matVec_matUnitAt_length])
        (fun p => elim.length_vsum _ _ _
          (fun q _ => hLpq p q))
        (fun p => ?_) (List.range d)
      refine poly.oneValue_trans
        (elim.matVec_vsum (monomialsAt mu).length
          (units.matUnitAt (moveAt i j mu) mu i j)
          _ (fun q => hterm p q) (List.range d)) ?_
      rw [units.length_matUnitAt]
      exact poly.oneValue_refl _
    -- the bridge: the right side is the double fold outright
    have hRb := casimirM_vsum d (moveAt i j mu)
      (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j) x)
    -- the joined folds agree, the per-pair join at every member
    have hS : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => elim.vecAdd (elim.vecAdd
                (elim.matVec
                  (units.matUnitAt (moveAt i j mu) mu i j)
                  (elim.matVec (elim.matMul
                    (units.matUnitAt mu (moveAt q p mu) p q)
                    (units.matUnitAt (moveAt q p mu) mu q p))
                    x))
                (aFam mu i j p q x))
              (dFam mu i j p q x))
            (List.range d))
          (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => elim.vecAdd (elim.vecAdd
                (elim.matVec (elim.matMul
                    (units.matUnitAt (moveAt i j mu)
                      (moveAt q p (moveAt i j mu)) p q)
                    (units.matUnitAt (moveAt q p (moveAt i j mu))
                      (moveAt i j mu) q p))
                  (elim.matVec
                    (units.matUnitAt (moveAt i j mu) mu i j) x))
                (cFam mu i j p q x))
              (bFam mu i j p q x))
            (List.range d))
          (List.range d)) := by
      refine vsumCongrMem _ _ _
        (fun p => elim.length_vsum _ _ _ (fun q _ =>
          elim.length_vecAdd _ _ _
            (elim.length_vecAdd _ _ _ (hLpq p q)
              (len_aFam mu i j p q x))
            (len_dFam mu i j p q x)))
        (fun p => elim.length_vsum _ _ _ (fun q _ =>
          elim.length_vecAdd _ _ _
            (elim.length_vecAdd _ _ _ (hRpq p q)
              (len_cFam mu i j p q x))
            (len_bFam mu i j p q x)))
        (List.range d) (fun p hp => ?_)
      refine vsumCongrMem _ _ _
        (fun q => elim.length_vecAdd _ _ _
          (elim.length_vecAdd _ _ _ (hLpq p q)
            (len_aFam mu i j p q x))
          (len_dFam mu i j p q x))
        (fun q => elim.length_vecAdd _ _ _
          (elim.length_vecAdd _ _ _ (hRpq p q)
            (len_cFam mu i j p q x))
          (len_bFam mu i j p q x))
        (List.range d) (fun q hq2 => ?_)
      exact joinAll mu i j p q hij hiL hjL
        (by rw [hd]; exact ground.ltOfMem hp)
        (by rw [hd]; exact ground.ltOfMem hq2) hmj x hx
    -- the splits
    have hsplitL := splitSums
      (monomialsAt (moveAt i j mu)).length
      (fun p q => elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.matVec (elim.matMul
          (units.matUnitAt mu (moveAt q p mu) p q)
          (units.matUnitAt (moveAt q p mu) mu q p)) x))
      (fun p q => aFam mu i j p q x)
      (fun p q => dFam mu i j p q x)
      (List.range d) hLpq (fun p q => len_aFam mu i j p q x)
      (fun p q => len_dFam mu i j p q x)
    have hsplitR := splitSums
      (monomialsAt (moveAt i j mu)).length
      (fun p q => elim.matVec (elim.matMul
          (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (units.matUnitAt (moveAt q p (moveAt i j mu))
            (moveAt i j mu) q p))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          x))
      (fun p q => cFam mu i j p q x)
      (fun p q => bFam mu i j p q x)
      (List.range d) hRpq (fun p q => len_cFam mu i j p q x)
      (fun p q => len_bFam mu i j p q x)
    -- the four family picks
    have hA : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => aFam mu i j p q x) (List.range d))
          (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt i p mu) p j)
            (yV mu p i x)) (List.range d)) := by
      refine elim.vsum_congr _ _ _
        (fun p => elim.length_vsum _ _ _
          (fun q _ => len_aFam mu i j p q x))
        (fun p => by
          rw [units.matVec_matUnitAt_length])
        (fun p => ?_) (List.range d)
      exact pickInner (monomialsAt (moveAt i j mu)).length d i hi
        (fun q => elim.matVec (units.matUnitAt (moveAt i j mu)
          (moveAt q p mu) p j) (yV mu p q x))
        (fun q => by
          rw [units.matVec_matUnitAt_length])
    have hC : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => cFam mu i j p q x) (List.range d))
          (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt j p (moveAt i j mu)) p j)
            (elim.matVec (units.matUnitAt
              (moveAt j p (moveAt i j mu)) mu i p) x))
          (List.range d)) := by
      refine elim.vsum_congr _ _ _
        (fun p => elim.length_vsum _ _ _
          (fun q _ => len_cFam mu i j p q x))
        (fun p => by
          rw [units.matVec_matUnitAt_length])
        (fun p => ?_) (List.range d)
      exact pickInner (monomialsAt (moveAt i j mu)).length d j hj
        (fun q => elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (elim.matVec (units.matUnitAt
            (moveAt q p (moveAt i j mu)) mu i p) x))
        (fun q => by
          rw [units.matVec_matUnitAt_length])
    have hAC : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt i p mu) p j)
            (yV mu p i x)) (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt j p (moveAt i j mu)) p j)
            (elim.matVec (units.matUnitAt
              (moveAt j p (moveAt i j mu)) mu i p) x))
          (List.range d)) :=
      elim.vsum_congr _ _ _
        (fun p => by
          rw [units.matVec_matUnitAt_length])
        (fun p => by
          rw [units.matVec_matUnitAt_length])
        (fun p => famAC mu i j p hij hiL hjL hmj x)
        (List.range d)
    have hD : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => dFam mu i j p q x) (List.range d))
          (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt q i (moveAt i j mu)) i q)
            (elim.matVec (units.matUnitAt
              (moveAt q i (moveAt i j mu)) mu q j) x))
          (List.range d)) :=
      pickOuter (monomialsAt (moveAt i j mu)).length d i hi
        (fun p q => elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p (moveAt i j mu)) p q)
          (elim.matVec (units.matUnitAt
            (moveAt q p (moveAt i j mu)) mu q j) x))
        (fun p q => by
          rw [units.matVec_matUnitAt_length])
    have hB : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun p => elim.vsum
            (monomialsAt (moveAt i j mu)).length
            (fun q => bFam mu i j p q x) (List.range d))
          (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt q j mu) i q)
            (yV mu j q x)) (List.range d)) :=
      pickOuter (monomialsAt (moveAt i j mu)).length d j hj
        (fun p q => elim.matVec (units.matUnitAt (moveAt i j mu)
            (moveAt q p mu) i q) (yV mu p q x))
        (fun p q => by
          rw [units.matVec_matUnitAt_length])
    have hBD : poly.oneValue
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt q i (moveAt i j mu)) i q)
            (elim.matVec (units.matUnitAt
              (moveAt q i (moveAt i j mu)) mu q j) x))
          (List.range d))
        (elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => elim.matVec (units.matUnitAt (moveAt i j mu)
              (moveAt q j mu) i q)
            (yV mu j q x)) (List.range d)) :=
      elim.vsum_congr _ _ _
        (fun q => by
          rw [units.matVec_matUnitAt_length])
        (fun q => by
          rw [units.matVec_matUnitAt_length])
        (fun q => by
          rw [moveAt_chain q i j mu]
          exact poly.oneValue_refl _)
        (List.range d)
    -- the assembly at the cancellation
    have hSL : (elim.vsum (monomialsAt (moveAt i j mu)).length
        (fun p => elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => elim.matVec
            (units.matUnitAt (moveAt i j mu) mu i j)
            (elim.matVec (elim.matMul
              (units.matUnitAt mu (moveAt q p mu) p q)
              (units.matUnitAt (moveAt q p mu) mu q p)) x))
          (List.range d)) (List.range d)).length
        = (monomialsAt (moveAt i j mu)).length :=
      elim.length_vsum _ _ _ (fun p _ =>
        elim.length_vsum _ _ _ (fun q _ => hLpq p q))
    have hSR : (elim.vsum (monomialsAt (moveAt i j mu)).length
        (fun p => elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => elim.matVec (elim.matMul
              (units.matUnitAt (moveAt i j mu)
                (moveAt q p (moveAt i j mu)) p q)
              (units.matUnitAt (moveAt q p (moveAt i j mu))
                (moveAt i j mu) q p))
            (elim.matVec
              (units.matUnitAt (moveAt i j mu) mu i j) x))
          (List.range d)) (List.range d)).length
        = (monomialsAt (moveAt i j mu)).length :=
      elim.length_vsum _ _ _ (fun p _ =>
        elim.length_vsum _ _ _ (fun q _ => hRpq p q))
    have hSa : (elim.vsum (monomialsAt (moveAt i j mu)).length
        (fun p => elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => aFam mu i j p q x) (List.range d))
        (List.range d)).length
        = (monomialsAt (moveAt i j mu)).length :=
      elim.length_vsum _ _ _ (fun p _ =>
        elim.length_vsum _ _ _
          (fun q _ => len_aFam mu i j p q x))
    have hSb : (elim.vsum (monomialsAt (moveAt i j mu)).length
        (fun p => elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => bFam mu i j p q x) (List.range d))
        (List.range d)).length
        = (monomialsAt (moveAt i j mu)).length :=
      elim.length_vsum _ _ _ (fun p _ =>
        elim.length_vsum _ _ _
          (fun q _ => len_bFam mu i j p q x))
    have hSc : (elim.vsum (monomialsAt (moveAt i j mu)).length
        (fun p => elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => cFam mu i j p q x) (List.range d))
        (List.range d)).length
        = (monomialsAt (moveAt i j mu)).length :=
      elim.length_vsum _ _ _ (fun p _ =>
        elim.length_vsum _ _ _
          (fun q _ => len_cFam mu i j p q x))
    have hSd : (elim.vsum (monomialsAt (moveAt i j mu)).length
        (fun p => elim.vsum (monomialsAt (moveAt i j mu)).length
          (fun q => dFam mu i j p q x) (List.range d))
        (List.range d)).length
        = (monomialsAt (moveAt i j mu)).length :=
      elim.length_vsum _ _ _ (fun p _ =>
        elim.length_vsum _ _ _
          (fun q _ => len_dFam mu i j p q x))
    have hca := poly.oneValue_trans hC
      (poly.oneValue_trans (poly.oneValue_symm hAC)
        (poly.oneValue_symm hA))
    have hbd := poly.oneValue_trans hB
      (poly.oneValue_trans (poly.oneValue_symm hBD)
        (poly.oneValue_symm hD))
    have h1 := poly.oneValue_trans (poly.oneValue_symm hsplitL)
      (poly.oneValue_trans hS hsplitR)
    have h2 := elim.polyOne_vecAdd _ _ _ _
      (elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _) hca
        (by rw [hSR]) (by rw [hSc, hSa]))
      hbd
      (by rw [elim.length_vecAdd _ _ _ hSR hSc,
        elim.length_vecAdd _ _ _ hSR hSa])
      (by rw [hSb, hSd])
    have h3 := poly.oneValue_trans h1 h2
    have h4 := elim.vecAdd_cancel_right _ _ _
      (by rw [elim.length_vecAdd _ _ _ hSL hSa,
        elim.length_vecAdd _ _ _ hSR hSa])
      (by rw [elim.length_vecAdd _ _ _ hSL hSa, hSd]) h3
    have h5 := elim.vecAdd_cancel_right _ _ _
      (by rw [hSL, hSR]) (by rw [hSL, hSa]) h4
    exact poly.oneValue_trans hLb
      (poly.oneValue_trans h5 (poly.oneValue_symm hRb))
  · have hz : getAt 0 mu j = 0 :=
      match Nat.eq_zero_or_pos (getAt 0 mu j) with
      | .inl h => h
      | .inr h => absurd h hmj
    exact poly.unitTail_oneValue
      (units.matVec_null_unocc (moveAt i j mu) mu i j hz _)
      (elim.matVec_null _ _
        (units.matVec_null_unocc (moveAt i j mu) mu i j hz x))
/-! `lem:casimir`'s eigen tier: the `C` family's three
`endo_scalar` data instantiated at the block, so the family acts on
every span member as the one block scalar, and the trace fold at a
pair's collected members reads the count against that scalar at the
whole self-pairing product.  The clearing tier's own plumbing is
the off-unit cancellation lifted memberwise (`elim.oneValue_unscale` over
`ground.mulCancel`, the pairs' integral read) and the combination's
eigen transport (`comboScale`, the action's combination read at
rows the family scales alike); the span-level read
(`spanRel_scalar`) then carries the scalar from a spanning family
to every member of its span, the span witness's own clearing
cancelled at the end.  The block read (`casimirM_member`) is
`lem:blockirr`(ii) at the top: the exhibit's line
`⟨v,v⟩·(C w) = ⟨C v, v⟩·w` with the top read collapsing the right
pairing to `q(λ)·⟨v,v⟩`, and the exhibit's off-unit self-pairing —
the coordinate family off the unit tail at the pairing's
definiteness — the factor that cancels.  The trace read
(`casimirM_trace`) is `trFold_scalar` at it: every collected member
sits in its content group's span (`lem:strings`' terminal read) and
every group row is a pool member's own coordinates, so the whole
list is eigen and the fold reads the string count against the block
scalar, the unoccupied content coming out of the same fold reads at
the vacant list. -/

/-- The action's combination read at eigen rows: a matrix scaling
every row of a family by one clearing scales every combination of
that family by it. -/
private theorem comboScale (n : Nat) (T : elim.Mat) (c : BPair)
    (hT : elim.rowsLen n T) (hTl : T.length = n) :
    ∀ (cs : List BPair) (G : elim.Mat), elim.rowsLen n G →
      (∀ k, k < G.length →
        poly.oneValue (elim.matVec T (getAt [] G k))
          (elim.vecScale c (getAt [] G k))) →
      poly.oneValue (elim.matVec T (elim.combo n cs G))
        (elim.vecScale c (elim.combo n cs G))
  | [], _, _, _ =>
    poly.unitTail_oneValue
      (elim.matVec_null T _ (poly.unitTail_replicate n))
      (elim.unitTail_vecScale c _ (poly.unitTail_replicate n))
  | _ :: _, [], _, _ =>
    poly.unitTail_oneValue
      (elim.matVec_null T _ (poly.unitTail_replicate n))
      (elim.unitTail_vecScale c _ (poly.unitTail_replicate n))
  | a :: cs, r :: G, hG, hr => by
    have hrn : r.length = n := hG.1
    have hcn : (elim.combo n cs G).length = n :=
      elim.length_combo n cs G hG.2
    have hsn : (elim.vecScale a r).length = n :=
      (elim.length_vecScale a r).trans hrn
    show poly.oneValue
      (elim.matVec T (elim.vecAdd (elim.vecScale a r)
        (elim.combo n cs G)))
      (elim.vecScale c (elim.vecAdd (elim.vecScale a r)
        (elim.combo n cs G)))
    rw [elim.vecScale_vecAdd c (elim.vecScale a r)
        (elim.combo n cs G),
      elim.vecScale_vecScale c a r, BPair.mul_comm c a,
      ← elim.vecScale_vecScale a c r]
    refine poly.oneValue_trans
      (elim.matVec_vecAdd T n hT _ _ hsn hcn) ?_
    refine elim.polyOne_vecAdd _ _ _ _ ?_ ?_ ?_ ?_
    · exact poly.oneValue_trans
        (elim.matVec_vecScale_free T a r)
        (elim.vecScale_oneValue a _ _
          (hr 0 (Nat.succ_pos G.length)))
    · exact comboScale n T c hT hTl cs G hG.2
        (fun k hk => hr (k + 1) (Nat.succ_lt_succ hk))
    · rw [elim.matVec_length T (elim.vecScale a r), hTl,
        elim.length_vecScale a (elim.vecScale c r),
        elim.length_vecScale c r, hrn]
    · rw [elim.matVec_length T (elim.combo n cs G), hTl,
        elim.length_vecScale c (elim.combo n cs G), hcn]

/-- The span-level eigen read: a matrix scaling every row of a
family by one clearing scales every member of that family's span,
the span witness's own clearing cancelled at the pairs' integral
read. -/
private theorem spanRel_scalar (n : Nat) (T G : elim.Mat)
    (c : BPair) (y : List BPair) (hT : elim.sqAt T n)
    (hG : elim.rowsLen n G)
    (hrows : ∀ k, k < G.length →
      poly.oneValue (elim.matVec T (getAt [] G k))
        (elim.vecScale c (getAt [] G k)))
    (hy : elim.spanRel n G y) :
    poly.oneValue (elim.matVec T y) (elim.vecScale c y) := by
  have hTr : elim.rowsLen n T := elim.rowsLen_of_sqAt hT
  have hTl : T.length = n := elim.sqAt_len hT
  match elim.span_elim hy with
  | ⟨c₀, cs, hc₀, _, hone⟩ =>
    have hyl : y.length = n := hy.2.1
    have hlen : (elim.vecScale c₀ y).length
        = (elim.combo n cs G).length := by
      rw [elim.length_vecScale c₀ y, hyl,
        elim.length_combo n cs G hG]
    refine elim.oneValue_unscale c₀ hc₀ _ _ ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (elim.matVec_vecScale_free T c₀ y)) ?_
    refine poly.oneValue_trans
      (elim.matVec_congr T _ _ hone) ?_
    refine poly.oneValue_trans
      (comboScale n T c hTr hTl cs G hG hrows) ?_
    rw [elim.vecScale_vecScale c₀ c y, BPair.mul_comm c₀ c,
      ← elim.vecScale_vecScale c c₀ y]
    exact elim.vecScale_oneValue c _ _ (poly.oneValue_symm hone)

/-- `lem:casimir`'s block read: on the block at top content `λ` the
`C` family is the one scalar `q(λ)`, read at the top —
`lem:blockirr`(ii)'s line divided by the exhibit's own off-unit
self-pairing. -/
theorem casimirM_member (s : Shape) : ∀ w ∈ blockSpan s,
    poly.oneValue
      (elim.matVec (casimirM s.length w.content) w.coords)
      (elim.vecScale (casScalar (rowList s)) w.coords) := by
  match blockcount.blockSpan_prov s with
  | ⟨tail, ht, hprov⟩ =>
    have hsz : ∀ w ∈ exhibit s :: tail, sized w := by
      rw [← ht]
      exact (lowerspan.spanReads s).1
    have hwid : ∀ w ∈ exhibit s :: tail,
        w.content.length = s.length := by
      rw [← ht]
      exact blockcount.blockSpan_width s
    have hexsz : sized (exhibit s) := exhibit_sized s
    have hxc : (exhibit s).content = rowList s := content_exhibit s
    have hgl : (casimirM s.length (exhibit s).content).length
        = (monomialsAt (exhibit s).content).length :=
      elim.sqAt_len (casimirM_sq s.length (exhibit s).content)
    have hG : elim.rowsLen (monomialsAt (exhibit s).content).length
        (groupAt (blockSpan s) (exhibit s).content) :=
      rowsLen_groupAt (exhibit s).content (blockSpan s)
        (lowerspan.spanReads s).1
    have hgcons : groupAt (blockSpan s) (exhibit s).content
        = (exhibit s).coords
          :: groupAt tail (exhibit s).content := by
      rw [ht, groupAt_cons (exhibit s) tail (exhibit s).content,
        ground.listEqBeq (exhibit s).content]
    have hrow : elim.spanRel
        (monomialsAt (exhibit s).content).length
        (groupAt (blockSpan s) (exhibit s).content)
        (exhibit s).coords := by
      have hk : 0 < (groupAt (blockSpan s)
          (exhibit s).content).length := by
        rw [hgcons]
        exact Nat.succ_pos _
      have h := elim.spanRel_getAt
        (monomialsAt (exhibit s).content).length
        (groupAt (blockSpan s) (exhibit s).content) 0 hk hG
      rw [show ground.getAt ([] : List BPair)
          (groupAt (blockSpan s) (exhibit s).content) 0
          = (exhibit s).coords from by
        rw [hgcons]
        rfl] at h
      exact h
    have htop : poly.oneValue
        (elim.vecScale (casScalar (rowList s)) (exhibit s).coords)
        (elim.matVec (casimirM s.length (exhibit s).content)
          (exhibit s).coords) := by
      rw [hxc]
      exact poly.oneValue_symm (casimirM_top s)
    have hval : settledAt (exhibit s :: tail)
        ⟨(exhibit s).content,
          elim.matVec (casimirM s.length (exhibit s).content)
            (exhibit s).coords⟩ := by
      refine Or.inr ?_
      show elim.spanRel
        (elim.matVec (casimirM s.length (exhibit s).content)
          (exhibit s).coords).length
        (groupAt (exhibit s :: tail) (exhibit s).content)
        (elim.matVec (casimirM s.length (exhibit s).content)
          (exhibit s).coords)
      rw [elim.matVec_length, hgl, ← ht]
      refine elim.spanRel_congr _ _ _ _ htop
        (elim.spanRel_scale _ _ _ (casScalar (rowList s)) hG
          hexsz hrow) ?_
      rw [elim.matVec_length]
      exact hgl
    have hkey := blockirr.endo_scalar s.length (exhibit s) tail
      (fun c => casimirM s.length c) hsz hwid hprov
      (fun w hw => by
        rw [hsz w hw]
        exact casimirM_sq s.length w.content)
      hval
      (fun w hw i hi j hj hij =>
        casimirM_comm s.length w.content i j hi hj hij
          (hwid w hw) w.coords (hsz w hw))
    have hD : ¬ (elim.dotP (exhibit s).coords
        (exhibit s).coords).oneValue BPair.unit :=
      fun h => exhibit_off_unit s
        (elim.dotP_self_null (exhibit s).coords h)
    have hE : (elim.dotP
          (elim.matVec (casimirM s.length (exhibit s).content)
            (exhibit s).coords) (exhibit s).coords).oneValue
        (casScalar (rowList s)
          * elim.dotP (exhibit s).coords (exhibit s).coords) := by
      refine BPair.oneValue_trans
        (elim.dotP_oneValue_left _ _ (exhibit s).coords
          (poly.oneValue_symm htop)) ?_
      rw [elim.dotP_comm
        (elim.vecScale (casScalar (rowList s)) (exhibit s).coords)
        (exhibit s).coords]
      exact elim.dotP_vecScale_right (exhibit s).coords
        (exhibit s).coords (casScalar (rowList s))
    intro w hw
    refine elim.oneValue_unscale
      (elim.dotP (exhibit s).coords (exhibit s).coords) hD _ _ ?_
    refine poly.oneValue_trans
      (hkey w (by rw [← ht]; exact hw)) ?_
    rw [elim.vecScale_vecScale
        (elim.dotP (exhibit s).coords (exhibit s).coords)
        (casScalar (rowList s)) w.coords,
      BPair.mul_comm
        (elim.dotP (exhibit s).coords (exhibit s).coords)
        (casScalar (rowList s))]
    exact elim.vecScale_congr hE w.coords

/-- `lem:casimir`'s trace read at a pair's collected members: the
fold is the string count against the block scalar at the whole
self-pairing product — every collected member sits in its content
group's span and every group row is a span member's own
coordinates, so the whole list is eigen. -/
theorem casimirM_trace (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) :
    (trFold (casimirM s.length nu)
      (strings.membersAt i j
        (strings.walk i j (blockSpan s)) nu)).oneValue
      (BPair.ofNat (strings.stringCount i j
          (strings.walk i j (blockSpan s)) nu)
        * casScalar (rowList s)
        * prodAll (strings.membersAt i j
            (strings.walk i j (blockSpan s)) nu)) := by
  refine trFold_scalar (casimirM s.length nu) _
    (casScalar (rowList s)) ?_
  intro p hp
  refine spanRel_scalar (monomialsAt nu).length
    (casimirM s.length nu) (groupAt (blockSpan s) nu)
    (casScalar (rowList s)) _ (casimirM_sq s.length nu)
    (rowsLen_groupAt nu (blockSpan s) (lowerspan.spanReads s).1)
    ?_ (strings.walk_span s i j hi hj hij nu p hp)
  intro k hk
  match groupAt_rows (fun v => v ∈ blockSpan s) (blockSpan s)
      (fun _ hv => hv) nu k hk with
  | ⟨v, hv, hvc, hvg⟩ =>
    rw [hvg, ← hvc]
    exact casimirM_member s v hv


/-! `thm:weylchar`'s per-pair string traces: at the exhaustion
pair the two ordered term matrices' folds over the collected
members read the string weights — the raising-after-lowering word
`E_ij E_ji` at `stringWeightUp` and the lowering-after-raising
word `E_ji E_ij` at `stringWeightDn`, each against the whole
self-pairing product.  The collection is the constant case's own
with the scalar read per member: every member's image is its own
depth's clearing (`lem:strings`' two word reads), so the fold's
terms pick their weights against the whole product and the index
fold collects them to the weight list's sum, `membersAt`'s spine
and the weight list's the same. -/

/-- `lem:casimir`'s weighted count read: an operator clearing each
member by its own weight has the trace fold at the weights' index
fold against the whole product, the constant case's collection
with the scalar read per member. -/
private theorem trFold_weights (T L : elim.Mat) (c : Nat → Nat)
    (hc : ∀ j < L.length,
      poly.oneValue (elim.matVec T (getAt [] L j))
        (elim.vecScale (BPair.ofNat (c j)) (getAt [] L j))) :
    (trFold T L).oneValue
      (BPair.ofNat
          (ground.famFold Nat.add 0 c (List.range L.length))
        * prodAll L) := by
  refine BPair.oneValue_trans (trFold_read T L) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => BPair.ofNat (c j) * prodAll L)
      (List.range L.length) ?_) ?_
  · intro j hj
    have hjr : j < L.length := ground.ltOfMem hj
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (elim.dotP_oneValue_right _ _ _ (hc j hjr))
          (elim.dotP_vecScale_right (getAt [] L j)
            (getAt [] L j) (BPair.ofNat (c j))))) ?_
    rw [BPair.mul_assoc]
    exact BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat (c j)))
      (prodOff_mul_self L j hjr)
  · exact ground.bsum_scalar c (prodAll L) (List.range L.length)

/-- `thm:weylchar`'s raising-side string trace: the composite
`E_ij E_ji` at the pair's content has its fold over the collected
members at the raising-side string weight against the whole
self-pairing product. -/
theorem stringTraceUp (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) :
    (trFold
      (elim.matMul (units.matUnitAt nu (moveAt j i nu) i j)
        (units.matUnitAt (moveAt j i nu) nu j i))
      (strings.membersAt i j
        (strings.walk i j (blockSpan s)) nu)).oneValue
      (BPair.ofNat (strings.stringWeightUp i j
          (strings.walk i j (blockSpan s)) nu)
        * prodAll (strings.membersAt i j
            (strings.walk i j (blockSpan s)) nu)) := by
  have hw := trFold_weights
    (elim.matMul (units.matUnitAt nu (moveAt j i nu) i j)
      (units.matUnitAt (moveAt j i nu) nu j i))
    (strings.membersAt i j (strings.walk i j (blockSpan s)) nu)
    (fun k => getAt 0
      (strings.weightList i j (fun ht b => (b + 1) * (ht - b))
        (strings.walk i j (blockSpan s)) nu) k)
    (fun k hk => strings.walk_traceUp s i j hi hj hij nu k hk)
  have hsum : ground.famFold Nat.add 0
      (fun k => getAt 0
        (strings.weightList i j (fun ht b => (b + 1) * (ht - b))
          (strings.walk i j (blockSpan s)) nu) k)
      (List.range (strings.membersAt i j
        (strings.walk i j (blockSpan s)) nu).length)
      = strings.stringWeightUp i j
        (strings.walk i j (blockSpan s)) nu := by
    rw [← strings.weightList_length i j
        (fun ht b => (b + 1) * (ht - b))
        (strings.walk i j (blockSpan s)) nu,
      (strings.stringWeight_reads i j
        (strings.walk i j (blockSpan s)) nu).1]
    exact ground.sumIndex _
  rw [hsum] at hw
  exact hw

/-- `thm:weylchar`'s lowering-side string trace: the composite
`E_ji E_ij` at the pair's content has its fold over the collected
members at the lowering-side string weight against the whole
self-pairing product. -/
theorem stringTraceDn (s : Shape) (i j : Nat)
    (hi : i < s.length) (hj : j < s.length) (hij : ¬ i = j)
    (nu : List Nat) :
    (trFold
      (elim.matMul (units.matUnitAt nu (moveAt i j nu) j i)
        (units.matUnitAt (moveAt i j nu) nu i j))
      (strings.membersAt i j
        (strings.walk i j (blockSpan s)) nu)).oneValue
      (BPair.ofNat (strings.stringWeightDn i j
          (strings.walk i j (blockSpan s)) nu)
        * prodAll (strings.membersAt i j
            (strings.walk i j (blockSpan s)) nu)) := by
  have hw := trFold_weights
    (elim.matMul (units.matUnitAt nu (moveAt i j nu) j i)
      (units.matUnitAt (moveAt i j nu) nu i j))
    (strings.membersAt i j (strings.walk i j (blockSpan s)) nu)
    (fun k => getAt 0
      (strings.weightList i j (fun ht b => b * (ht - b + 1))
        (strings.walk i j (blockSpan s)) nu) k)
    (fun k hk => strings.walk_traceDn s i j hi hj hij nu k hk)
  have hsum : ground.famFold Nat.add 0
      (fun k => getAt 0
        (strings.weightList i j (fun ht b => b * (ht - b + 1))
          (strings.walk i j (blockSpan s)) nu) k)
      (List.range (strings.membersAt i j
        (strings.walk i j (blockSpan s)) nu).length)
      = strings.stringWeightDn i j
        (strings.walk i j (blockSpan s)) nu := by
    rw [← strings.weightList_length i j
        (fun ht b => b * (ht - b + 1))
        (strings.walk i j (blockSpan s)) nu,
      (strings.stringWeight_reads i j
        (strings.walk i j (blockSpan s)) nu).2]
    exact ground.sumIndex _
  rw [hsum] at hw
  exact hw

/-! `thm:weylchar`'s recursion display: the positional kit the two
sides of the trace recursion read.  The row and content lists enter
the display through the same two identities — the square's split at
the entrywise join (`weylchar.sqSplit`, the doubled dot the cross term) and
the letter pairs' own positional identity (`posId`: at a stated
letter count the pairs' first entries against the pairs' second
entries close on the unit display's dot, the pair counts above and
below a letter the run lengths `ground.aboveRun` and
`places.belowRun`).  The
identity is the list's alone, so the display's `λ`-side and its
`ν`-side are the one lemma at two instantiations. -/

/-- The per-letter read at the positional identity. -/
private theorem posArith (t a g : Nat) :
    (a + 1 + g + 1) * t + t * g = t * a + 2 * (t * (1 + g)) := by
  rw [Nat.mul_comm (a + 1 + g + 1) t,
    ← Nat.left_distrib t (a + 1 + g + 1) g,
    Nat.two_mul (t * (1 + g)),
    ← Nat.left_distrib t (1 + g) (1 + g),
    ← Nat.left_distrib t a (1 + g + (1 + g)),
    Nat.add_assoc a 1 g, Nat.add_assoc (a + (1 + g)) 1 g,
    Nat.add_assoc a (1 + g) (1 + g)]

/-- `thm:weylchar`'s positional identity at a stated letter count:
the letter pairs' first entries against their second entries close
on the unit display's dot, the pair runs above and below a letter
the letter's own two counts. -/
private theorem posId (z : List Nat) (d : Nat) (hz : z.length = d) :
    (d + 1) * sumNat z
        + ground.famFold Nat.add 0 (fun ab => getAt 0 z ab.1)
            (pairsOf d)
      = ground.famFold Nat.add 0 (fun ab => getAt 0 z ab.2)
            (pairsOf d)
        + 2 * ground.dotNat z (unitDisp d) := by
  have key : ∀ a, 0 < ground.countOf a (List.range d) →
      (d + 1) * getAt 0 z a
          + ground.famFold Nat.add 0
              (fun b => if a < b then getAt 0 z a else 0)
              (List.range d)
        = ground.famFold Nat.add 0
              (fun b => if b < a then getAt 0 z a else 0)
              (List.range d)
          + 2 * (getAt 0 z a * getAt 0 (unitDisp d) a) := by
    intro a ha
    have had : a < d := ground.ltOfMem ha
    obtain ⟨g, hg⟩ := Nat.le.dest had
    have hsh : a + 1 + g = 1 + g + a := by
      rw [Nat.add_assoc 1 g a, Nat.add_comm 1 (g + a),
        Nat.add_assoc g a 1, Nat.add_comm g (a + 1)]
    have hu : getAt 0 (unitDisp d) a = 1 + g := by
      rw [weylchar.getAt_unitDisp d a had, ← hg, hsh]
      exact addSubSelfR (1 + g) a
    have hab : ground.famFold Nat.add 0
        (fun b => if a < b then getAt 0 z a else 0) (List.range d)
        = getAt 0 z a * g := by
      rw [← hg]
      exact ground.aboveRun a (getAt 0 z a) g
    have hbe : ground.famFold Nat.add 0
        (fun b => if b < a then getAt 0 z a else 0) (List.range d)
        = getAt 0 z a * a := by
      rw [show d = a + (1 + g) from by
        rw [← hg, Nat.add_assoc a 1 g]]
      exact places.belowRun a (getAt 0 z a) (1 + g)
    rw [hab, hbe, hu, ← hg]
    exact posArith (getAt 0 z a) a g
  have hLHS : (d + 1) * sumNat z
      + ground.famFold Nat.add 0 (fun ab => getAt 0 z ab.1)
          (pairsOf d)
    = ground.famFold Nat.add 0 (fun a => (d + 1) * getAt 0 z a
        + ground.famFold Nat.add 0
          (fun b => if a < b then getAt 0 z a else 0)
          (List.range d))
      (List.range d) := by
    rw [places.pairsFold (fun ab => getAt 0 z ab.1) d, ← ground.sumIndex z, hz,
      ground.famFold_mul (d + 1) (fun i => getAt 0 z i)
        (List.range d)]
    exact (ground.famFold_add_split
      (fun a => (d + 1) * getAt 0 z a)
      (fun a => ground.famFold Nat.add 0
        (fun b => if a < b then getAt 0 z a else 0) (List.range d))
      (List.range d)).symm
  have hRHS : ground.famFold Nat.add 0 (fun ab => getAt 0 z ab.2)
          (pairsOf d)
      + 2 * ground.dotNat z (unitDisp d)
    = ground.famFold Nat.add 0 (fun a =>
        ground.famFold Nat.add 0
          (fun b => if b < a then getAt 0 z a else 0)
          (List.range d)
        + 2 * (getAt 0 z a * getAt 0 (unitDisp d) a))
      (List.range d) := by
    rw [places.pairsFold (fun ab => getAt 0 z ab.2) d,
      ground.famFold_swap
        (fun a b => if a < b then getAt 0 z b else 0)
        (List.range d) (List.range d),
      ground.dotNat_index z (unitDisp d)
        (by rw [places.length_unitDisp d, hz]), hz,
      ground.famFold_mul 2
        (fun i => getAt 0 z i * getAt 0 (unitDisp d) i)
        (List.range d)]
    exact (ground.famFold_add_split
      (fun a => ground.famFold Nat.add 0
        (fun b => if b < a then getAt 0 z a else 0) (List.range d))
      (fun a => 2 * (getAt 0 z a * getAt 0 (unitDisp d) a))
      (List.range d)).symm
  rw [hLHS, hRHS]
  exact ground.famFold_congr_members Nat.add 0 _ _ (List.range d) key

/-! `lem:casimir`'s trace identity at a content: the block
scalar's own balance read, the `C` family's fold split over the
ordered letter pairs, and the two collected sides. -/

/-- A memberwise balance read collects: at every occupied key the
family joined by the second side's count reads the first side's,
so the folds do. -/
private theorem balFold (F : Nat → BPair) (f g : Nat → Nat) :
    ∀ l : List Nat,
      (∀ p, 0 < ground.countOf p l →
        (F p + BPair.ofNat (g p)).oneValue (BPair.ofNat (f p))) →
      (ground.bsum F l
        + BPair.ofNat (ground.famFold Nat.add 0 g l)).oneValue
        (BPair.ofNat (ground.famFold Nat.add 0 f l))
  | [], _ => BPair.add_unit BPair.unit
  | a :: t, h => by
    show (F a + ground.bsum F t
        + BPair.ofNat (g a + ground.famFold Nat.add 0 g t)).oneValue
      (BPair.ofNat (f a + ground.famFold Nat.add 0 f t))
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.ofNat_add (g a) _)) ?_
    rw [BPair.add_add_comm (F a) (ground.bsum F t)
      (BPair.ofNat (g a))
      (BPair.ofNat (ground.famFold Nat.add 0 g t))]
    refine BPair.oneValue_trans
      (BPair.add_congr
        (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
        (balFold F f g t (fun q hq =>
          h q (Nat.lt_of_lt_of_le hq (Nat.le_add_left _ _))))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_add (f a) _)

/-- The term scalar's own balance at a letter pair: the guarded
second entry joins the term to the guarded first entry, the
diagonal's square picked at its key. -/
private theorem cTermBal (mu : List Nat) (p q : Nat) :
    (cTerm mu p q
      + BPair.ofNat (if p < q then getAt 0 mu q else 0)).oneValue
      (BPair.ofNat ((if q = p then getAt 0 mu p * getAt 0 mu p
          else 0)
        + (if p < q then getAt 0 mu p else 0))) := by
  by_cases hpq : p = q
  · have hnl : ¬ p < q := by
      rw [hpq]
      exact Nat.lt_irrefl q
    rw [if_neg hnl, if_neg hnl, if_pos hpq.symm,
      show cTerm mu p q = sqTerm mu p from by
        show (if p = q then sqTerm mu p else prTerm mu p q) = _
        rw [if_pos hpq]]
    exact BPair.add_unit _
  · rw [if_neg (fun he : q = p => hpq he.symm), Nat.zero_add,
      show cTerm mu p q = prTerm mu p q from by
        show (if p = q then sqTerm mu p else prTerm mu p q) = _
        rw [if_neg hpq]]
    by_cases hlt : p < q
    · rw [if_pos hlt, if_pos hlt,
        show prTerm mu p q = BPair.ofNat (getAt 0 mu p)
            + (BPair.ofNat (getAt 0 mu q)).swap from by
          show (if p < q then _ else BPair.unit) = _
          rw [if_pos hlt],
        BPair.add_assoc]
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (show ((BPair.ofNat (getAt 0 mu q)).swap
              + BPair.ofNat (getAt 0 mu q)).oneValue BPair.unit
            from BPair.swap_add_null (BPair.oneValue_refl _))) ?_
      exact BPair.add_unit _
    · rw [if_neg hlt, if_neg hlt,
        show prTerm mu p q = BPair.unit from by
          show (if p < q then _ else BPair.unit) = _
          rw [if_neg hlt]]
      exact BPair.add_unit _

/-- The per-letter balance: the term scalars at a stated first
letter join their guarded second entries to the letter's square
against the guarded first entries. -/
private theorem cRowBal (mu : List Nat) (p : Nat)
    (hp : p < mu.length) :
    (ground.bsum (fun q => cTerm mu p q) (List.range mu.length)
      + BPair.ofNat (ground.famFold Nat.add 0
          (fun q => if p < q then getAt 0 mu q else 0)
          (List.range mu.length))).oneValue
      (BPair.ofNat (getAt 0 mu p * getAt 0 mu p
        + ground.famFold Nat.add 0
            (fun q => if p < q then getAt 0 mu p else 0)
            (List.range mu.length))) := by
  have hsplit : ground.famFold Nat.add 0
      (fun q => (if q = p then getAt 0 mu p * getAt 0 mu p else 0)
        + (if p < q then getAt 0 mu p else 0))
      (List.range mu.length)
    = getAt 0 mu p * getAt 0 mu p
      + ground.famFold Nat.add 0
          (fun q => if p < q then getAt 0 mu p else 0)
          (List.range mu.length) := by
    rw [ground.famFold_add_split _ _ (List.range mu.length),
      ground.famFold_pick (fun _ => getAt 0 mu p * getAt 0 mu p) p
        (List.range mu.length)
        (by rw [ground.countOf_range_one hp])]
  rw [← hsplit]
  exact balFold (fun q => cTerm mu p q) _ _ (List.range mu.length)
    (fun q _ => cTermBal mu p q)

/-- `lem:casimir`'s block scalar as a balance: the scalar joined by
the letter pairs' second entries reads the square fold against the
pairs' first entries. -/
private theorem casBal (mu : List Nat) :
    (casScalar mu
      + BPair.ofNat (ground.famFold Nat.add 0
          (fun ab => getAt 0 mu ab.2)
          (pairsOf mu.length))).oneValue
      (BPair.ofNat (weylchar.stdSq mu
        + ground.famFold Nat.add 0
            (fun ab => getAt 0 mu ab.1)
            (pairsOf mu.length))) := by
  rw [places.pairsFold (fun ab => getAt 0 mu ab.2) mu.length,
    places.pairsFold (fun ab => getAt 0 mu ab.1) mu.length,
    weylchar.stdSq_index mu,
    ← ground.famFold_add_split
      (fun p => getAt 0 mu p * getAt 0 mu p)
      (fun p => ground.famFold Nat.add 0
        (fun q => if p < q then getAt 0 mu p else 0)
        (List.range mu.length))
      (List.range mu.length)]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_symm (casScalar_read mu))
      (BPair.oneValue_refl _)) ?_
  exact balFold (fun p => ground.bsum (fun q => cTerm mu p q)
      (List.range mu.length)) _ _ (List.range mu.length)
    (fun p hp => cRowBal mu p (ground.ltOfMem hp))

/-- The `C` family's term at an ordered letter pair: the composed
unit actions at the pair's own move. -/
private def cMat (mu : List Nat) (p q : Nat) : elim.Mat :=
  elim.matMul (units.matUnitAt mu (moveAt q p mu) p q)
    (units.matUnitAt (moveAt q p mu) mu q p)

/-- The term is square at the content's enumeration. -/
private theorem sqAt_cMat (mu : List Nat) (p q : Nat) :
    elim.sqAt (cMat mu p q) (monomialsAt mu).length :=
  elim.sqAt_of (termShape mu p q).1 (termShape mu p q).2

/-- The inner fold keeps the square shape. -/
private theorem sqAt_rowFold (mu : List Nat) (p : Nat) :
    ∀ (l : List Nat) (acc : elim.Mat),
      elim.sqAt acc (monomialsAt mu).length →
      elim.sqAt (l.foldl (fun a q => elim.matAdd a (cMat mu p q))
        acc) (monomialsAt mu).length := by
  intro l acc h
  have hs := foldShape (monomialsAt mu).length
    (fun a q => elim.matAdd a (cMat mu p q))
    (fun a q h2 => stepShape _ a _ h2 (termShape mu p q))
    l acc ⟨elim.sqAt_len h, elim.rowsLen_of_sqAt h⟩
  exact elim.sqAt_of hs.1 hs.2

/-- The seed is the null map. -/
private theorem seedNull (n : Nat) : ∀ m : Nat,
    elim.matNull (List.replicate m (List.replicate n BPair.unit))
  | 0 => trivial
  | m + 1 => ⟨poly.unitTail_replicate n, seedNull n m⟩

/-- The seed is square at the content's enumeration. -/
private theorem sqAt_seed (n : Nat) :
    elim.sqAt (List.replicate n (List.replicate n BPair.unit)) n :=
  elim.sqAt_of (ground.length_replicate _ _)
    (elim.rowsLen_replicate n _)

/-- The seed's trace fold is the sum's unit. -/
private theorem seedTrace (n : Nat) (L : elim.Mat) :
    (trFold (List.replicate n (List.replicate n BPair.unit))
      L).oneValue BPair.unit := by
  refine BPair.oneValue_trans (trFold_read _ L) ?_
  refine ground.foldB_nullRange _ L.length ?_
  intro j _
  rw [BPair.mul_comm]
  exact elim.oneValue_mul_unit _ _
    (elim.dotP_null_tail_right _ _
      (elim.matVec_matNull _ _ (seedNull n n)))

/-- A fold whose every step's trace adds a stated summand has its
own trace at the seed's against the summands' collection. -/
private theorem foldTrace (n : Nat) (R : elim.Mat)
    (step : elim.Mat → Nat → elim.Mat) (F : Nat → BPair)
    (hstep : ∀ (a : elim.Mat) (k : Nat), elim.sqAt a n →
      elim.sqAt (step a k) n)
    (hval : ∀ (a : elim.Mat) (k : Nat), elim.sqAt a n →
      (trFold (step a k) R).oneValue (trFold a R + F k)) :
    ∀ (l : List Nat) (acc : elim.Mat), elim.sqAt acc n →
      (trFold (l.foldl step acc) R).oneValue
        (trFold acc R + ground.bsum F l)
  | [], _, _ => BPair.oneValue_symm (BPair.add_unit _)
  | k :: t, acc, hacc => by
    show (trFold (t.foldl step (step acc k)) R).oneValue
      (trFold acc R + (F k + ground.bsum F t))
    refine BPair.oneValue_trans
      (foldTrace n R step F hstep hval t (step acc k)
        (hstep acc k hacc)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (hval acc k hacc)
        (BPair.oneValue_refl _)) ?_
    rw [BPair.add_assoc]
    exact BPair.oneValue_refl _

/-- `lem:casimir`'s trace split: the `C` family's fold over a
collected list is the ordered letter pairs' own folds collected,
the seed's fold the sum's unit and every sum splitting. -/
private theorem casimirSplit (d : Nat) (mu : List Nat)
    (R : elim.Mat)
    (hR : elim.rowsLen (monomialsAt mu).length R) :
    (trFold (casimirM d mu) R).oneValue
      (ground.bsum (fun p => ground.bsum
        (fun q => trFold (cMat mu p q) R) (List.range d))
        (List.range d)) := by
  have houter := foldTrace (monomialsAt mu).length R
    (fun acc p => (List.range d).foldl
      (fun a q => elim.matAdd a (cMat mu p q)) acc)
    (fun p => ground.bsum (fun q => trFold (cMat mu p q) R)
      (List.range d))
    (fun a p ha => sqAt_rowFold mu p (List.range d) a ha)
    (fun a p ha => foldTrace (monomialsAt mu).length R
      (fun a2 q => elim.matAdd a2 (cMat mu p q))
      (fun q => trFold (cMat mu p q) R)
      (fun a2 q h2 => elim.sqAt_matAdd _ a2 _ h2 (sqAt_cMat mu p q))
      (fun a2 q h2 => trFold_add (monomialsAt mu).length a2
        (cMat mu p q) R h2 (sqAt_cMat mu p q) hR)
      (List.range d) a ha)
    (List.range d)
    (List.replicate (monomialsAt mu).length
      (List.replicate (monomialsAt mu).length BPair.unit))
    (sqAt_seed _)
  refine BPair.oneValue_trans houter ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (seedTrace _ R) (BPair.oneValue_refl _)) ?_
  exact BPair.unit_add _

/-- The collected members' width at a content: the group's own
rows at an occupied content, the vacant list at an empty one. -/
private theorem memRows (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) :
    elim.rowsLen (monomialsAt nu).length
      (strings.membersAt i j (strings.walk i j (blockSpan lam))
        nu) := by
  by_cases hoc : 0 < occupancyAt (blockSpan lam) nu
  · exact (strings.walk_spanRowL lam i j hi hj hij nu 0
      (by rw [groupAt_occupancy]; exact hoc)).1
  · have hz : (strings.membersAt i j
        (strings.walk i j (blockSpan lam)) nu).length = 0 := by
      show strings.stringCount i j
        (strings.walk i j (blockSpan lam)) nu = 0
      rw [strings.walk_count lam i j hi hj hij nu]
      match Nat.eq_zero_or_pos (occupancyAt (blockSpan lam) nu) with
      | .inl h => exact h
      | .inr h => exact absurd h hoc
    rw [ground.nil_of_length_zero _ hz]
    trivial

/-- The collected members' whole product sits off the sum's unit,
the members' own off-unit self-pairings. -/
private theorem memProdOff (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) :
    ¬ (prodAll (strings.membersAt i j
      (strings.walk i j (blockSpan lam)) nu)).oneValue
      BPair.unit :=
  prodAll_off _ (fun p hp hbad =>
    strings.walk_off lam i j hi hj hij nu p hp
      (elim.dotP_self_null _ hbad))

/-- The equal-lettered term's trace at a collected list: the count
against the letter's own square. -/
private theorem diagTrace (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) (p : Nat) (hp : p < nu.length) :
    (trFold (cMat nu p p)
      (strings.membersAt i j (strings.walk i j (blockSpan lam))
        nu)).oneValue
      (BPair.ofNat ((strings.membersAt i j
          (strings.walk i j (blockSpan lam)) nu).length
        * (getAt 0 nu p * getAt 0 nu p))
        * prodAll (strings.membersAt i j
            (strings.walk i j (blockSpan lam)) nu)) := by
  have hR := memRows lam i j hi hj hij nu
  refine BPair.oneValue_trans
    (trFold_scalar (cMat nu p p) _ (sqTerm nu p)
      (fun k hk => diagAt nu p hp (getAt [] _ k)
        (elim.rowsLen_getAt _ k hR hk))) ?_
  exact BPair.mul_congr_left
    (BPair.oneValue_symm (BPair.ofNat_mul _ _))

/-- `lem:casimir`'s trace transport: an operator whose fold over
one pair's collected members reads a count against that list's
whole product reads the same count at every other pair's, the two
lists mutually spanning through their shared content group. -/
private theorem offTrace (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (a b : Nat) (ha : a < lam.length) (hb : b < lam.length)
    (hab : ¬ a = b) (nu : List Nat) (T : elim.Mat)
    (hT : elim.sqAt T (monomialsAt nu).length) (w : Nat)
    (hw : (trFold T (strings.membersAt a b
        (strings.walk a b (blockSpan lam)) nu)).oneValue
      (BPair.ofNat w * prodAll (strings.membersAt a b
        (strings.walk a b (blockSpan lam)) nu))) :
    (trFold T (strings.membersAt i j
      (strings.walk i j (blockSpan lam)) nu)).oneValue
      (BPair.ofNat w * prodAll (strings.membersAt i j
        (strings.walk i j (blockSpan lam)) nu)) := by
  have hX := memRows lam a b ha hb hab nu
  have hY := memRows lam i j hi hj hij nu
  have hG := rowsLen_groupAt nu (blockSpan lam)
    (lowerspan.spanReads lam).1
  have htr := trace_eq (monomialsAt nu).length T
    (strings.membersAt a b (strings.walk a b (blockSpan lam)) nu)
    (strings.membersAt i j (strings.walk i j (blockSpan lam)) nu)
    hT hX hY
    (fun p hp q hq hpq =>
      strings.walk_perp lam a b ha hb hab nu p q hp hq hpq)
    (fun p hp q hq hpq =>
      strings.walk_perp lam i j hi hj hij nu p q hp hq hpq)
    (fun p hp hbad => strings.walk_off lam a b ha hb hab nu p hp
      (elim.dotP_self_null _ hbad))
    (fun p hp => elim.spanRel_trans (monomialsAt nu).length
      (groupAt (blockSpan lam) nu) _ _ hG hY
      (strings.walk_spanRowL lam i j hi hj hij nu)
      (strings.walk_span lam a b ha hb hab nu p hp))
    (fun q hq => elim.spanRel_trans (monomialsAt nu).length
      (groupAt (blockSpan lam) nu) _ _ hG hX
      (strings.walk_spanRowL lam a b ha hb hab nu)
      (strings.walk_span lam i j hi hj hij nu q hq))
  refine BPair.oneValue_symm
    (ground.mulCancel (memProdOff lam a b ha hb hab nu) ?_)
  rw [BPair.mul_left_comm
      (prodAll (strings.membersAt a b
        (strings.walk a b (blockSpan lam)) nu))
      (BPair.ofNat w)
      (prodAll (strings.membersAt i j
        (strings.walk i j (blockSpan lam)) nu)),
    ← BPair.mul_assoc (BPair.ofNat w),
    BPair.mul_comm
      (prodAll (strings.membersAt a b
        (strings.walk a b (blockSpan lam)) nu))
      (trFold T (strings.membersAt i j
        (strings.walk i j (blockSpan lam)) nu))]
  exact BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.oneValue_symm hw)) htr

/-- The pair's collected members at the block span. -/
private def memAt (lam : Shape) (i j : Nat) (nu : List Nat) :
    elim.Mat :=
  strings.membersAt i j (strings.walk i j (blockSpan lam)) nu

/-- The collected members' count is the content's multiplicity. -/
private theorem memLen (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) :
    (memAt lam i j nu).length
      = ground.countOf nu ((blockSpan lam).map HVec.content) := by
  show strings.stringCount i j
    (strings.walk i j (blockSpan lam)) nu = _
  rw [strings.walk_count lam i j hi hj hij nu, blockcount.span_countOf lam nu]

/-- The trace weight at an ordered letter pair: the diagonal's
count against the letter's square, the ordered pair's own string
weight at the pair's orientation. -/
private def wAll (lam : Shape) (nu : List Nat) (c p q : Nat) :
    Nat :=
  if p = q then c * (getAt 0 nu p * getAt 0 nu p)
  else if p < q then
    strings.stringWeightUp p q
      (strings.walk p q (blockSpan lam)) nu
  else
    strings.stringWeightDn q p
      (strings.walk q p (blockSpan lam)) nu

/-- `lem:casimir`'s per-pair trace at a reference list: every
ordered term's fold over the reference pair's collected members
reads its own trace weight against the whole product — the
diagonal at the letter's square, the ordered pairs transported
from their own pair's collection. -/
private theorem termTrace (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) (hlen : nu.length = lam.length) (p q : Nat)
    (hp : p < lam.length) (hq : q < lam.length) :
    (trFold (cMat nu p q) (memAt lam i j nu)).oneValue
      (BPair.ofNat (wAll lam nu (memAt lam i j nu).length p q)
        * prodAll (memAt lam i j nu)) := by
  by_cases hpq : p = q
  · subst hpq
    rw [show wAll lam nu (memAt lam i j nu).length p p
        = (memAt lam i j nu).length
          * (getAt 0 nu p * getAt 0 nu p) from by
      show (if p = p then _ else _) = _
      rw [if_pos rfl]]
    exact diagTrace lam i j hi hj hij nu p (by rw [hlen]; exact hp)
  · by_cases hlt : p < q
    · rw [show wAll lam nu (memAt lam i j nu).length p q
          = strings.stringWeightUp p q
            (strings.walk p q (blockSpan lam)) nu from by
        show (if p = q then _ else if p < q then _ else _) = _
        rw [if_neg hpq, if_pos hlt]]
      exact offTrace lam i j hi hj hij p q hp hq hpq nu
        (cMat nu p q) (sqAt_cMat nu p q) _
        (stringTraceUp lam p q hp hq hpq nu)
    · rw [show wAll lam nu (memAt lam i j nu).length p q
          = strings.stringWeightDn q p
            (strings.walk q p (blockSpan lam)) nu from by
        show (if p = q then _ else if p < q then _ else _) = _
        rw [if_neg hpq, if_neg hlt]]
      exact offTrace lam i j hi hj hij q p hq hp
        (fun he => hpq he.symm) nu
        (cMat nu p q) (sqAt_cMat nu p q) _
        (stringTraceDn lam q p hq hp (fun he => hpq he.symm) nu)

/-- The collected trace at a per-pair count read: the whole fold
is the counts' double fold against the list's own product. -/
private theorem traceCollect (d : Nat) (nu : List Nat)
    (R : elim.Mat) (hR : elim.rowsLen (monomialsAt nu).length R)
    (c : Nat → Nat → Nat)
    (hterm : ∀ p, 0 < ground.countOf p (List.range d) →
      ∀ q, 0 < ground.countOf q (List.range d) →
      (trFold (cMat nu p q) R).oneValue
        (BPair.ofNat (c p q) * prodAll R)) :
    (trFold (casimirM d nu) R).oneValue
      (BPair.ofNat (ground.famFold Nat.add 0
          (fun p => ground.famFold Nat.add 0 (fun q => c p q)
            (List.range d))
          (List.range d))
        * prodAll R) := by
  refine BPair.oneValue_trans (casimirSplit d nu R hR) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun p => BPair.ofNat (ground.famFold Nat.add 0
        (fun q => c p q) (List.range d)) * prodAll R)
      (List.range d) (fun p hp => BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun q => BPair.ofNat (c p q) * prodAll R)
          (List.range d) (fun q hq => hterm p hp q hq))
        (ground.bsum_scalar (fun q => c p q) (prodAll R)
          (List.range d)))) ?_
  exact ground.bsum_scalar
    (fun p => ground.famFold Nat.add 0 (fun q => c p q)
      (List.range d)) (prodAll R) (List.range d)

/-- `lem:casimir`'s trace balance at a content: the block scalar
against the content's multiplicity reads the ordered pairs' trace
weights collected, the whole self-pairing product cancelled at its
off-unit read. -/
private theorem traceBal (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) (hlen : nu.length = lam.length) :
    (BPair.ofNat (memAt lam i j nu).length
      * casScalar (rowList lam)).oneValue
      (BPair.ofNat (ground.famFold Nat.add 0
        (fun p => ground.famFold Nat.add 0
          (fun q => wAll lam nu (memAt lam i j nu).length p q)
          (List.range lam.length))
        (List.range lam.length))) := by
  refine ground.mulCancel (memProdOff lam i j hi hj hij nu) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_of_eq (BPair.mul_comm _ _))
  exact BPair.oneValue_trans
    (BPair.oneValue_symm (casimirM_trace lam i j hi hj hij nu))
    (traceCollect lam.length nu (memAt lam i j nu)
      (memRows lam i j hi hj hij nu) _
      (fun p hp q hq => termTrace lam i j hi hj hij nu hlen p q
        (ground.ltOfMem hp) (ground.ltOfMem hq)))

/-- `lem:casimir`'s trace identity as counts: the multiplicity
against the block scalar's own square-and-pair read collects the
ordered pairs' trace weights. -/
private theorem traceNat (lam : Shape) (i j : Nat)
    (hi : i < lam.length) (hj : j < lam.length) (hij : ¬ i = j)
    (nu : List Nat) (hlen : nu.length = lam.length) :
    (memAt lam i j nu).length
        * (weylchar.stdSq (rowList lam)
          + ground.famFold Nat.add 0
              (fun ab => getAt 0 (rowList lam) ab.1)
              (pairsOf (rowList lam).length))
      = ground.famFold Nat.add 0
          (fun p => ground.famFold Nat.add 0
            (fun q => wAll lam nu (memAt lam i j nu).length p q)
            (List.range lam.length))
          (List.range lam.length)
        + (memAt lam i j nu).length
          * ground.famFold Nat.add 0
              (fun ab => getAt 0 (rowList lam) ab.2)
              (pairsOf (rowList lam).length) := by
  refine (ground.BPair.ofNat_inj (BPair.oneValue_trans
    (BPair.ofNat_add _ _) ?_)).symm
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_symm (traceBal lam i j hi hj hij nu hlen))
      (BPair.ofNat_mul _ _)) ?_
  rw [← BPair.left_distrib]
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (casBal (rowList lam))) ?_
  exact BPair.oneValue_symm (BPair.ofNat_mul _ _)

/-- The trace weight's three-family read at a letter pair: the
diagonal's delta, the raising side above the order, the lowering
side below it. -/
private theorem wAllPt (lam : Shape) (nu : List Nat) (c p q : Nat) :
    wAll lam nu c p q
      = (if q = p then c * (getAt 0 nu p * getAt 0 nu p) else 0)
        + ((if p < q then strings.stringWeightUp p q
              (strings.walk p q (blockSpan lam)) nu else 0)
          + (if q < p then strings.stringWeightDn q p
              (strings.walk q p (blockSpan lam)) nu else 0)) := by
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos (rfl : p = p), if_neg (Nat.lt_irrefl p),
      if_neg (Nat.lt_irrefl p),
      show wAll lam nu c p p
          = c * (getAt 0 nu p * getAt 0 nu p) from by
        show (if p = p then _ else _) = _
        rw [if_pos rfl]]
    rfl
  · have hne : ¬ q = p := fun he => hpq he.symm
    rw [if_neg hne, Nat.zero_add,
      show wAll lam nu c p q
          = if p < q then strings.stringWeightUp p q
              (strings.walk p q (blockSpan lam)) nu
            else strings.stringWeightDn q p
              (strings.walk q p (blockSpan lam)) nu from by
        show (if p = q then _ else _) = _
        rw [if_neg hpq]]
    by_cases hlt : p < q
    · rw [if_pos hlt, if_pos hlt,
        if_neg (fun h2 => Nat.lt_irrefl p (Nat.lt_trans hlt h2))]
      rfl
    · have hqp : q < p :=
        match Nat.lt_or_ge q p with
        | .inl h => h
        | .inr h =>
          match Nat.eq_or_lt_of_le h with
          | .inl he => absurd he hpq
          | .inr hl => absurd hl hlt
      rw [if_neg hlt, if_neg hlt, if_pos hqp, Nat.zero_add]

/-- The trace weights' double fold splits: the diagonal at the
content's square fold, the ordered pairs at the letter pairs' own
two-sided fold. -/
private theorem wAllSplit (lam : Shape) (nu : List Nat) (c : Nat)
    (hlen : nu.length = lam.length) :
    ground.famFold Nat.add 0
        (fun p => ground.famFold Nat.add 0
          (fun q => wAll lam nu c p q) (List.range lam.length))
        (List.range lam.length)
      = c * weylchar.stdSq nu
        + ground.famFold Nat.add 0
            (fun ab => strings.stringWeightUp ab.1 ab.2
                (strings.walk ab.1 ab.2 (blockSpan lam)) nu
              + strings.stringWeightDn ab.1 ab.2
                (strings.walk ab.1 ab.2 (blockSpan lam)) nu)
            (pairsOf lam.length) := by
  have hrow : ∀ p, 0 < ground.countOf p (List.range lam.length) →
      ground.famFold Nat.add 0 (fun q => wAll lam nu c p q)
          (List.range lam.length)
        = c * (getAt 0 nu p * getAt 0 nu p)
          + (ground.famFold Nat.add 0
              (fun q => if p < q then strings.stringWeightUp p q
                (strings.walk p q (blockSpan lam)) nu else 0)
              (List.range lam.length)
            + ground.famFold Nat.add 0
              (fun q => if q < p then strings.stringWeightDn q p
                (strings.walk q p (blockSpan lam)) nu else 0)
              (List.range lam.length)) := by
    intro p hp
    rw [ground.famFold_congr_all Nat.add 0 _ _
        (fun q => wAllPt lam nu c p q) (List.range lam.length),
      ground.famFold_add_split _ _ (List.range lam.length),
      ground.famFold_add_split _ _ (List.range lam.length),
      ground.famFold_pick
        (fun _ => c * (getAt 0 nu p * getAt 0 nu p)) p
        (List.range lam.length)
        (by rw [ground.countOf_range_one
          (ground.ltOfMem hp)])]
  rw [ground.famFold_congr_members Nat.add 0 _ _
      (List.range lam.length) hrow,
    ground.famFold_add_split _ _ (List.range lam.length),
    ground.famFold_add_split _ _ (List.range lam.length),
    ← ground.famFold_mul c
      (fun p => getAt 0 nu p * getAt 0 nu p)
      (List.range lam.length),
    ground.famFold_swap
      (fun p q => if q < p then strings.stringWeightDn q p
        (strings.walk q p (blockSpan lam)) nu else 0)
      (List.range lam.length) (List.range lam.length),
    ← places.pairsFold (fun ab => strings.stringWeightUp ab.1 ab.2
        (strings.walk ab.1 ab.2 (blockSpan lam)) nu)
      lam.length,
    ← places.pairsFold (fun ab => strings.stringWeightDn ab.1 ab.2
        (strings.walk ab.1 ab.2 (blockSpan lam)) nu)
      lam.length,
    ← ground.famFold_add_split _ _ (pairsOf lam.length),
    weylchar.stdSq_index nu, hlen]

/-- `thm:weylchar`'s collected recursion at the letter pairs: the
per-pair string collection summed over the pairs, the moved folds
the display's own two sides. -/
private theorem collectSum (lam : Shape) (nu : List Nat)
    (hlen : nu.length = lam.length) :
    ground.famFold Nat.add 0
          (fun ab => strings.stringWeightUp ab.1 ab.2
              (strings.walk ab.1 ab.2 (blockSpan lam)) nu
            + strings.stringWeightDn ab.1 ab.2
              (strings.walk ab.1 ab.2 (blockSpan lam)) nu)
          (pairsOf lam.length)
        + 2 * weylchar.movedSnd
            (fun chi => ground.countOf chi
              ((blockSpan lam).map HVec.content)) nu
        + ground.countOf nu ((blockSpan lam).map HVec.content)
          * ground.famFold Nat.add 0 (fun ab => getAt 0 nu ab.2)
              (pairsOf lam.length)
      = 2 * weylchar.movedFst
            (fun chi => ground.countOf chi
              ((blockSpan lam).map HVec.content)) nu
        + ground.countOf nu ((blockSpan lam).map HVec.content)
          * ground.famFold Nat.add 0 (fun ab => getAt 0 nu ab.1)
              (pairsOf lam.length) := by
  have hms : weylchar.movedSnd
      (fun chi => ground.countOf chi
        ((blockSpan lam).map HVec.content)) nu
      = ground.famFold Nat.add 0
        (fun ab => weylchar.gSnd
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
        (pairsOf lam.length) := by
    show ground.famFold Nat.add 0
      (fun ab => weylchar.gSnd
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (pairsOf nu.length) = _
    rw [hlen]
  have hmf : weylchar.movedFst
      (fun chi => ground.countOf chi
        ((blockSpan lam).map HVec.content)) nu
      = ground.famFold Nat.add 0
        (fun ab => weylchar.gFst
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
        (pairsOf lam.length) := by
    show ground.famFold Nat.add 0
      (fun ab => weylchar.gFst
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (pairsOf nu.length) = _
    rw [hlen]
  rw [hms, hmf,
    ground.famFold_mul 2
      (fun ab => weylchar.gSnd
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (pairsOf lam.length),
    ground.famFold_mul 2
      (fun ab => weylchar.gFst
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (pairsOf lam.length),
    ground.famFold_mul
      (ground.countOf nu ((blockSpan lam).map HVec.content))
      (fun ab => getAt 0 nu ab.2) (pairsOf lam.length),
    ground.famFold_mul
      (ground.countOf nu ((blockSpan lam).map HVec.content))
      (fun ab => getAt 0 nu ab.1) (pairsOf lam.length),
    ← ground.famFold_add_split
      (fun ab => strings.stringWeightUp ab.1 ab.2
          (strings.walk ab.1 ab.2 (blockSpan lam)) nu
        + strings.stringWeightDn ab.1 ab.2
          (strings.walk ab.1 ab.2 (blockSpan lam)) nu)
      (fun ab => 2 * weylchar.gSnd
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (pairsOf lam.length),
    ← ground.famFold_add_split
      (fun ab => strings.stringWeightUp ab.1 ab.2
            (strings.walk ab.1 ab.2 (blockSpan lam)) nu
          + strings.stringWeightDn ab.1 ab.2
            (strings.walk ab.1 ab.2 (blockSpan lam)) nu
        + 2 * weylchar.gSnd
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (fun ab => ground.countOf nu
          ((blockSpan lam).map HVec.content) * getAt 0 nu ab.2)
      (pairsOf lam.length),
    ← ground.famFold_add_split
      (fun ab => 2 * weylchar.gFst
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
      (fun ab => ground.countOf nu
          ((blockSpan lam).map HVec.content) * getAt 0 nu ab.1)
      (pairsOf lam.length)]
  rw [places.pairsFold
      (fun ab => strings.stringWeightUp ab.1 ab.2
            (strings.walk ab.1 ab.2 (blockSpan lam)) nu
          + strings.stringWeightDn ab.1 ab.2
            (strings.walk ab.1 ab.2 (blockSpan lam)) nu
        + 2 * weylchar.gSnd
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2
        + ground.countOf nu ((blockSpan lam).map HVec.content)
          * getAt 0 nu ab.2)
      lam.length,
    places.pairsFold
      (fun ab => 2 * weylchar.gFst
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2
        + ground.countOf nu ((blockSpan lam).map HVec.content)
          * getAt 0 nu ab.1)
      lam.length]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range lam.length) (fun a ha => ?_)
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range lam.length) (fun b hb => ?_)
  by_cases hab : a < b
  · rw [if_pos hab, if_pos hab]
    exact strings.stringCollect lam a b (ground.ltOfMem ha)
      (ground.ltOfMem hb)
      (fun he : a = b =>
        absurd hab (by rw [he]; exact Nat.lt_irrefl b))
      nu hlen
  · rw [if_neg hab, if_neg hab]

/-! The display's closure: the four collected identities — the
trace balance, the collected recursion and the two positional
reads — join at one cancellation, the shuffles the sums' own. -/

/-- The joined triple's shuffle: the leading summand withdrawn to
the tail. -/
private theorem acA (a s w o : Nat) :
    a + (s + w + o) = a + w + o + s := by
  rw [← Nat.add_assoc a (s + w) o, ← Nat.add_assoc a s w,
    Nat.add_right_comm a s w, Nat.add_right_comm (a + w) s o]

/-- The crossed pair's shuffle at the same withdrawal. -/
private theorem acB (q s m z n : Nat) :
    q + (s + m) + (z + n) = q + m + z + n + s := by
  rw [← Nat.add_assoc q s m, ← Nat.add_assoc (q + s + m) z n,
    Nat.add_right_comm q s m, Nat.add_right_comm (q + m) s z,
    Nat.add_right_comm (q + m + z) s n]

/-- The joined summand exchanges with the standing one. -/
private theorem acD (b n o y : Nat) :
    b + n + (o + y) = b + y + (o + n) := by
  rw [← Nat.add_assoc (b + n) o y,
    Nat.add_right_comm (b + n) o y, Nat.add_right_comm b n y,
    Nat.add_right_comm (b + y) n o, Nat.add_assoc (b + y) o n]

/-- The join's members spread to the left-associated sum. -/
private theorem acE (p l w k : Nat) :
    p + w + (k + l) = p + l + w + k := by
  rw [← Nat.add_assoc (p + w) k l,
    Nat.add_right_comm (p + w) k l, Nat.add_right_comm p w l]

/-- The join opens with its first member withdrawn. -/
private theorem acF (p w m x : Nat) :
    p + w + (m + x) = p + w + x + m := by
  rw [← Nat.add_assoc (p + w) m x, Nat.add_right_comm (p + w) m x]

/-- The display's closure as counts: the trace balance, the
collected recursion and the two positional identities cancel to
the recursion display. -/
private theorem recArith (P Q L M N O S K X Y V W Z : Nat)
    (F1 : P + L = Q + (S + M))
    (F2 : S + W + O = Z + N)
    (F3 : K + L = M + X)
    (F4 : K + N = O + Y) :
    P + X + V + W = Q + Y + V + Z := by
  have e1 : P + L + (S + W + O) = Q + (S + M) + (Z + N) := by
    rw [F1, F2]
  have e3 : P + L + W + O = Q + M + Z + N :=
    ground.addCancelR S (by
      rw [← acA (P + L) S W O, ← acB Q S M Z N]
      exact e1)
  have e4 : P + L + W + O + (K + N)
      = Q + M + Z + N + (O + Y) := by
    rw [e3, F4]
  have e6 : P + L + W + K = Q + M + Z + Y :=
    ground.addCancelR (O + N) (by
      rw [← Nat.add_add_add_comm (P + L + W) O K N, ← acD (Q + M + Z) N O Y]
      exact e4)
  have e8 : P + W + (M + X) = Q + M + Z + Y := by
    rw [← F3, acE P L W K]
    exact e6
  have e10 : P + W + X = Q + Z + Y :=
    ground.addCancelR M (by
      rw [← acF P W M X, ← ground.addRotTail3 Q M Z Y]
      exact e8)
  rw [← ground.addRotTail3 P W X V, ← ground.addRotTail3 Q Z Y V, e10]

/-- The scalar's passage across a doubling. -/
private theorem mulTwo (c t : Nat) : c * (2 * t) = 2 * (c * t) := by
  rw [← ground.mulAssoc c 2 t, Nat.mul_comm c 2,
    ground.mulAssoc 2 c t]

/-- The display's product read: the split square against a count. -/
private theorem distC (c A B C : Nat) :
    (A + 2 * B + C) * c = c * A + 2 * (c * B) + c * C := by
  rw [ground.mulAddR (A + 2 * B) C c, ground.mulAddR A (2 * B) c,
    Nat.mul_comm A c, Nat.mul_comm C c, ground.mulAssoc 2 B c,
    Nat.mul_comm B c]

/-! The keys' degree: every span content carries the shape's own
box total, the exhibit's row list at the base and the adjacent
lowering's total preserved at an occupied letter inside the
width. -/

/-- Every span member carries the shape's letter width and box
total. -/
private theorem spanDegree (lam : Shape) :
    ∀ v ∈ blockSpan lam, v.content.length = lam.length
      ∧ sumNat v.content = degree lam := by
  refine blockSpan_all lam
    (fun v => v.content.length = lam.length
      ∧ sumNat v.content = degree lam) ?_ ?_
  · rw [content_exhibit lam]
    exact ⟨places.length_rowList lam, rfl⟩
  · intro v w j hj hv hlw
    rw [(lowerH_reads hlw).2, units.length_moveDn j v.content,
      units.sumNat_moveDn j v.content (by rw [hv.1]; exact hj)
        (lowerH_reads hlw).1]
    exact hv

/-- A mapped occurrence exhibits its own member. -/
private theorem memMapContent (nu : List Nat) :
    ∀ l : List HVec, nu ∈ l.map HVec.content →
      ∃ v, v ∈ l ∧ v.content = nu
  | [], h => nomatch h
  | v :: t, h => by
    cases h with
    | head => exact ⟨v, List.Mem.head t, rfl⟩
    | tail _ h' =>
      match memMapContent nu t h' with
      | ⟨w, hw, hwc⟩ => exact ⟨w, List.Mem.tail v hw, hwc⟩

/-- An occupied key carries the shape's box total. -/
private theorem degreeOfCount (lam : Shape) (nu : List Nat)
    (h : 0 < ground.countOf nu
      ((blockSpan lam).map HVec.content)) :
    sumNat nu = degree lam := by
  match memMapContent nu (blockSpan lam)
      (ground.mem_of_countOf_pos nu _ h) with
  | ⟨v, hv, hvc⟩ =>
    rw [← hvc]
    exact (spanDegree lam v hv).2

/-- Two short contents at one width and one total are equal. -/
private theorem shortEq : ∀ (x y : List Nat),
    x.length = y.length → x.length ≤ 1 →
    sumNat x = sumNat y → x = y
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => Nat.noConfusion h
  | _ :: _, [], h, _, _ => Nat.noConfusion h
  | [_], [_], _, _, h => congrArg (fun z => [z]) h
  | [_], _ :: _ :: _, h, _, _ =>
    Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, [_], h, _, _ =>
    Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: t, _ :: _ :: _, _, hl, _ =>
    absurd (Nat.le_of_succ_le_succ hl) (Nat.not_succ_le_zero t.length)

/-- The letter pairs are vacant below two letters. -/
private theorem pairsNil : ∀ d : Nat, d ≤ 1 → pairsOf d = []
  | 0, _ => rfl
  | 1, _ => rfl
  | d + 2, h =>
    absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero d)

/-- `lem:casimir`'s trace recursion at the block span, the second
discharge theorem: `thm:weylchar`'s recursion display holds at
every key of the span's own occupancy family.  At two letters or
more the reference pair's collected members carry the whole
identity — the `C` family's fold splits over the ordered letter
pairs (`casimirSplit`), the diagonal terms read the letters'
squares against the count and the ordered terms are transported
from their own pair's collection (`termTrace` through `offTrace`,
the two lists mutually spanning through their shared content
group), and the whole self-pairing product cancels at its
off-unit read, leaving the block scalar's balance (`traceNat`).
The per-pair string collection sums over the letter pairs to the
display's two moved folds (`collectSum`), and the two positional
identities (`posId` at the row list and at the content, the
degree shared through the span's own total) carry the two
displays; the four join at one cancellation (`recArith`).  Below
two letters the letter pairs are vacant, so the moved folds die
and the display is the count's own — the key is the row list
itself at an occupied count, its width and total the span's. -/
theorem recRead_def (lam : Shape) :
    weylchar.recRead lam ((blockSpan lam).map HVec.content) := by
  intro nu _ hlen
  match Nat.lt_or_ge lam.length 2 with
  | .inl hsmall =>
    have hle : lam.length ≤ 1 := Nat.le_of_lt_succ hsmall
    have hz : weylchar.movedSnd
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu = 0 := by
      show ground.famFold Nat.add 0
        (fun ab => weylchar.gSnd
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
        (pairsOf nu.length) = 0
      rw [hlen, pairsNil lam.length hle]
      rfl
    have hz' : weylchar.movedFst
        (fun chi => ground.countOf chi
          ((blockSpan lam).map HVec.content)) nu = 0 := by
      show ground.famFold Nat.add 0
        (fun ab => weylchar.gFst
          (fun chi => ground.countOf chi
            ((blockSpan lam).map HVec.content)) nu ab.1 ab.2)
        (pairsOf nu.length) = 0
      rw [hlen, pairsNil lam.length hle]
      rfl
    rw [hz, hz']
    by_cases hcpos : 0 < ground.countOf nu
        ((blockSpan lam).map HVec.content)
    · rw [shortEq nu (rowList lam)
        (by rw [hlen, places.length_rowList lam])
        (by rw [hlen]; exact hle)
        (show sumNat nu = sumNat (rowList lam) from
          degreeOfCount lam nu hcpos),
        weylchar.display_zip lam]
    · rw [show ground.countOf nu
          ((blockSpan lam).map HVec.content) = 0 from
        match Nat.eq_zero_or_pos (ground.countOf nu
            ((blockSpan lam).map HVec.content)) with
        | .inl h0 => h0
        | .inr hp => absurd hp hcpos]
      rfl
  | .inr hbig =>
    have hi0 : (0 : Nat) < lam.length :=
      Nat.lt_of_lt_of_le (Nat.succ_pos 1) hbig
    have hj1 : (1 : Nat) < lam.length := hbig
    have hij : ¬ (0 : Nat) = 1 := fun he => Nat.noConfusion he
    have hdeg : ground.countOf nu
          ((blockSpan lam).map HVec.content) * sumNat nu
        = ground.countOf nu
          ((blockSpan lam).map HVec.content)
          * sumNat (rowList lam) :=
      match Nat.eq_zero_or_pos (ground.countOf nu
          ((blockSpan lam).map HVec.content)) with
      | .inl h0 => by rw [h0, Nat.zero_mul, Nat.zero_mul]
      | .inr hp => by
        rw [show sumNat nu = sumNat (rowList lam) from
          degreeOfCount lam nu hp]
    have F1 := traceNat lam 0 1 hi0 hj1 hij nu hlen
    rw [memLen lam 0 1 hi0 hj1 hij nu, places.length_rowList lam,
      wAllSplit lam nu
        (ground.countOf nu ((blockSpan lam).map HVec.content))
        hlen,
      Nat.left_distrib
        (ground.countOf nu ((blockSpan lam).map HVec.content))
        (weylchar.stdSq (rowList lam))
        (ground.famFold Nat.add 0
          (fun ab => getAt 0 (rowList lam) ab.1)
          (pairsOf lam.length)),
      Nat.add_assoc
        (ground.countOf nu ((blockSpan lam).map HVec.content)
          * weylchar.stdSq nu)
        (ground.famFold Nat.add 0
          (fun ab => strings.stringWeightUp ab.1 ab.2
              (strings.walk ab.1 ab.2 (blockSpan lam)) nu
            + strings.stringWeightDn ab.1 ab.2
              (strings.walk ab.1 ab.2 (blockSpan lam)) nu)
          (pairsOf lam.length))
        (ground.countOf nu ((blockSpan lam).map HVec.content)
          * ground.famFold Nat.add 0
              (fun ab => getAt 0 (rowList lam) ab.2)
              (pairsOf lam.length))] at F1
    have F3 : ground.countOf nu
            ((blockSpan lam).map HVec.content)
            * ((lam.length + 1) * sumNat (rowList lam))
          + ground.countOf nu ((blockSpan lam).map HVec.content)
            * ground.famFold Nat.add 0
                (fun ab => getAt 0 (rowList lam) ab.1)
                (pairsOf lam.length)
        = ground.countOf nu ((blockSpan lam).map HVec.content)
            * ground.famFold Nat.add 0
                (fun ab => getAt 0 (rowList lam) ab.2)
                (pairsOf lam.length)
          + 2 * (ground.countOf nu
              ((blockSpan lam).map HVec.content)
            * ground.dotNat (rowList lam) (unitDisp lam.length)) := by
      rw [← Nat.left_distrib, ← mulTwo, ← Nat.left_distrib,
        posId (rowList lam) lam.length
          (places.length_rowList lam)]
    have F4 : ground.countOf nu
            ((blockSpan lam).map HVec.content)
            * ((lam.length + 1) * sumNat (rowList lam))
          + ground.countOf nu ((blockSpan lam).map HVec.content)
            * ground.famFold Nat.add 0
                (fun ab => getAt 0 nu ab.1)
                (pairsOf lam.length)
        = ground.countOf nu ((blockSpan lam).map HVec.content)
            * ground.famFold Nat.add 0
                (fun ab => getAt 0 nu ab.2)
                (pairsOf lam.length)
          + 2 * (ground.countOf nu
              ((blockSpan lam).map HVec.content)
            * ground.dotNat nu (unitDisp lam.length)) := by
      rw [ground.mulLeftComm
          (ground.countOf nu ((blockSpan lam).map HVec.content))
          (lam.length + 1) (sumNat (rowList lam)),
        ← hdeg,
        ← ground.mulLeftComm
          (ground.countOf nu ((blockSpan lam).map HVec.content))
          (lam.length + 1) (sumNat nu),
        ← Nat.left_distrib, ← mulTwo, ← Nat.left_distrib,
        posId nu lam.length hlen]
    rw [show weylchar.stdSq (display lam)
        = weylchar.stdSq (rowList lam)
          + 2 * ground.dotNat (rowList lam) (unitDisp lam.length)
          + weylchar.stdSq (unitDisp lam.length) from by
        rw [weylchar.display_zip lam]
        exact weylchar.sqSplit (rowList lam) (unitDisp lam.length)
          (by rw [places.length_rowList lam, places.length_unitDisp lam.length]),
      weylchar.sqSplit nu (unitDisp lam.length)
        (by rw [hlen, places.length_unitDisp lam.length]),
      distC (ground.countOf nu ((blockSpan lam).map HVec.content))
        (weylchar.stdSq (rowList lam))
        (ground.dotNat (rowList lam) (unitDisp lam.length))
        (weylchar.stdSq (unitDisp lam.length)),
      distC (ground.countOf nu ((blockSpan lam).map HVec.content))
        (weylchar.stdSq nu)
        (ground.dotNat nu (unitDisp lam.length))
        (weylchar.stdSq (unitDisp lam.length))]
    exact recArith _ _ _ _ _ _ _ _ _ _ _ _ _ F1
      (collectSum lam nu hlen) F3 F4

end casimir
