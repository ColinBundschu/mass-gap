import MassGap.Poly
import MassGap.C2hat
import MassGap.Weyldim
import MassGap.Steinberg
import MassGap.Adjchar
import MassGap.Channels
import MassGap.Labels
/-!
`lem:rankstable`(i)'s `casPoly` tier: the banded family's member
at a residue count and the Casimir's cleared read there, one
quadratic polynomial in the count.  The member is the reduced
shape `member P Q d` — the top word `P` at the leading keys, the
bottom word `Q` reversed at the trailing keys below the full
column, the middle vacant — read at the family frame's reach
clearance, the theorem's own floor the structural
`a + b + 1 ≤ d`.  Its row list
splits into three blocks (`rowList_member`): the top rows at
`m + p_i` above the bottom word's total `m`, the run of rows at
that height, and the bottom rows, the bottom word's prefix sums
descending (`bots`).  `casPoly` is the coefficient list at the
word folds — the successor-weighted folds `wtSum` of the two
words with the blocks' own squares and gap folds, each
coefficient a balance pair's gap of counts — and `casPoly_eval`
states the agreement: at every residue count from the floor the
polynomial's value is `c2hat.dfQ` of the member.  The route is
`c2hat.squareAll`'s exchange of the pairwise gap content for the
additive row squares against the degree's square, the block
splits of `sumSq` and of `rho2` (the crossed fold across two
blocks, evaluated at the three block pairs), and the degree join
`degree + Σ_i i·Q_i = d·m + Σ_i i·P_i`.  `lem:genericlift`'s
polynomial-pair calculus is the read the consumers take this
through.

The dimension tier reads the same member through `cor:weyldim`.
At the floor the member's display splits into three blocks — the
top word's rows raised by the bottom word's total against the
leading run, the run block at that total, and the bottom rows
against the trailing run — and the unit display splits at the same
seams, so the gap product's factors fall into four classes.  The
run–run factors are one, a run's gap product being its count's own
at any floor; the within-word factors are residue-free, the two
words' own rows against the unit runs; the word-against-run
factors telescope, the display's rising window against the unit's
at each key, and the two windows cross-multiply to the binomial
pairs — the top rows at their tail sums, the bottom rows'
reflection at the bottom word's own tail sums, the bottom row at a
key reading the word's row at the complementary key against the
word's total (`bots_row_join`); and the cross factors are one
linear pair per key pair at the position-gap join `i + t + g = d`.
`dimNum` and `dimDen` build the two members from those classes —
the within-word gap products with the numerators' windows against
the unit runs' own products with the denominators' — and
`dimPair_eval` states the cross-multiplied agreement: at every
residue count from the same structural floor the first member's
value is `weyldim.dimOf` of the member against the second
member's.

The diagonal tier reads the same member through `cor:steinberg` at
the adjoint (`lem:rankstable`(ii)).  At matched degree the
θ-contents are the all-ones list at multiplicity `d - 1` and the
2-0-1 lists at one each (`adjchar.multRead_cases`), so at the
diagonal target — the member raised by one full column,
`places.display_full`'s own read — the identity permutation
contributes the all-ones tie on the even side and exactly one odd
adjacent exchange contributes per unit gap of the display, every
further permutation refused at the two squeezes (`places.tieOnes`
forces the identity, `places.tieMove` forces an exchange at a unit
gap).  The two graded sums therefore join at the display's
consecutive unit-gap count `clearGaps` against `d - 1`
(`diagJoin`), at every shape of the stated width, the gap keys
themselves enumerated once each (`gapKeys`) and carried onto the
exchange list by the committed fold devices.  At a member the
display's consecutive gap is the shape's own occupancy raised by
one, so the unit gaps sit exactly at the vacant keys: the three
blocks' vacancy count fills the residue against the two words'
occupied keys and the diagonal is the member-key count `suppCount`
(`rowDiag`).

Off the diagonal the same two sums part by at most one
(`rowOffOne`), at every shape of the width.  A contribution's
content is the all-ones list or a 2-0-1 list
(`adjchar.multRead_cases`) and both squeezes read the raised
display: `places.tieOnes` forces the identity permutation with the
raised display, `places.tieMove` forces an exchange with the same
raised display, and `places.display_inj` reads the target back as
the full-column bump (`display_diag`) against the stated refusal.
So every permutation off the identity contributes the vacant tie —
the even fold reads its identity term against a vacant remainder
(`ground.famFold_off`) — and the identity's own tie is refused the
all-ones arm, falling to the letter-pair arm's one.  The
diagonal's exclusion and the width are the statement's own data:
at the diagonal target the two sums part by the key count itself,
and off the stated width the tie survives on the permuted display
alone, the further entries at the default read.

At a member an occupied target is confined (`rowConfined`).  The
occupied gap names a contributing permutation
(`ground.famFold_pos_witness`), which is the identity or carries
the raised display, and the raised display is the diagonal's own —
vacant across the member's middle block off the full column.  Off
it the identity's entrywise read (`ground.tieGap_reads` at
`ground.range_map_getAt`) joins the target's display to the
member's at the content, and across the middle block the member's
display steps by one (`display_gap` at `member_vac`).  At a
clear-window key the two neighbouring pairs refuse the content's
raised and lowered places — an interior raise would hand the
target display a vanishing gap one key below, an interior lower
the same one key above, both against `places.display_desc` — so
the key's own gap is the all-ones remainder's and the target's
occupancy there is the two places' gap, vacant.  The window's
margins are exact at both ends, one key inside each word's own
reach.

The row itself is `adjRow`, the label calculus' word list at the
adjoint, at the displays' closed reads: the full-column bump
enters exactly where the diagonal's occupied-gap read clears
(`clearGaps` against the width, the diagonal join `diagJoin`'s own
comparison), each raise-lower survivor of the weak descent `descB`
— the row lists' own shape — enters outright (`survivor_pos`, the
identity's tie at the letter-pair content with every further
permutation's tie at the raised display alone), and each member
reduces to its class (`labels.reduce`).  The fast count is the
definitional one at matched widths (`adjCount_eq`): the two
factors exchange at the block counts
(`blockcount.fusionCount_comm`), `cor:steinberg`'s display reads
the graded gap on both sides (`steinberg.readAll`), and the
content formula agrees with the adjoint's span occupancy
(`channels.sumsWith_agree`).

The row is the definitional enumeration's own (`adjRow_eq`): at
every label the matched-degree shapes' reduction and the occupied
candidates' reduction hold one count.  Forward, an occupied
matched-degree shape is a candidate — the occupied gap names a
contributing permutation (`ground.famFold_pos_witness`) whose
content is the all-ones list or a letter-pair move
(`adjchar.multRead_cases`), the identity's all-ones tie and every
off-identity move read the raised display (`places.tieOnes`,
`places.tieMove`) and so the raised row list, and the identity's
letter-pair tie reads the raise-lower survivor at the pair's own
places, the staircase cancelling key by key.  Back, each candidate
carries the stated width and the degree `deg λ + d`
(`adjchar.degree_theta`), the raise adding one box per key and the
lowering withdrawing the one it added at an occupied key.  Both
sides hold each label at most once: the enumeration lists each
shape once (`places.countOf_allShapes_le`), the candidates are
distinct — the raised key parts the head from every survivor and
the two moved keys read a survivor's pair back — and the reduction
is injective at one width and one degree, the prefixes agreeing at
the split with the degree tying the last occupancies.
-/

namespace rankstable
open ground places

/-- The member shape at a residue count: the top word at the
leading keys, the bottom word's reverse at the trailing keys below
the full column, the middle vacant. -/
def member (P Q : List Nat) (d : Nat) : Shape :=
  P ++ List.replicate (d - 1 - P.length - Q.length) 0
    ++ Q.reverse ++ [0]

/-- The bottom rows `σ_{b-1}, …, σ_0`, the bottom word's prefix
sums in descending row order. -/
private def bots (Q : List Nat) : List Nat :=
  (places.rowList (Q.reverse ++ [0])).tail

/-- The successor-weighted fold `Σ_i i · l_i` at keys from one. -/
private def wtSum : List Nat → Nat
  | [] => 0
  | x :: t => x + wtSum t + ground.sumNat t

/-- The Casimir's cleared read as a quadratic in the residue
count: the coefficient list at the word folds, in the balance
pair's own gap spelling. -/
def casPoly (P Q : List Nat) : poly.Poly :=
  let a := P.length
  let b := Q.length
  let m := ground.sumNat Q
  let T := (places.rowList P).map (fun x => m + x)
  let B := bots Q
  let SP := ground.sumNat (places.rowList P)
  let SB := ground.sumNat B
  let JP := wtSum P
  let JQ := wtSum Q
  let A0 := c2hat.sumSq T + c2hat.sumSq B
  [⟨ground.posOfSucc (2 * (JP * JQ)),
    ground.posOfSucc (JP * JP + JQ * JQ)⟩,
   ⟨ground.posOfSucc (A0 + c2hat.rho2 T + c2hat.rho2 B
      + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m)),
    ground.posOfSucc (a * SB + (a + b) * (m * m + SP + b * m)
      + 2 * (JP * m))⟩,
   ⟨ground.posOfSucc (SP + b * m), ground.posOfSucc SB⟩]

/-! The row list over a join: the first block's rows carry the
second block's total, the second block's rows its own. -/

/-- The row list splits over a join. -/
private theorem rowList_append : ∀ xs ys : List Nat,
    places.rowList (xs ++ ys)
      = (places.rowList xs).map (fun x => ground.sumNat ys + x)
        ++ places.rowList ys
  | [], _ => rfl
  | x :: t, ys => by
    show (x + sumNat (t ++ ys)) :: rowList (t ++ ys)
      = (sumNat ys + (x + sumNat t))
        :: ((rowList t).map (fun z => sumNat ys + z) ++ rowList ys)
    rw [
      rowList_append t ys,
      sumNat_append t ys,
      ← Nat.add_assoc x (sumNat t) (sumNat ys),
      Nat.add_comm (x + sumNat t) (sumNat ys)]

/-- A joined family's row list reads its total at the first row. -/
private theorem rowList_snoc : ∀ (l : List Nat) (x : Nat),
    places.rowList (l ++ [x])
      = ground.sumNat (l ++ [x]) :: (places.rowList (l ++ [x])).tail
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- The bottom block's row list: the bottom word's total at the
head, the bottom rows below it. -/
private theorem rowList_bot (Q : List Nat) :
    places.rowList (Q.reverse ++ [0])
      = ground.sumNat Q :: bots Q := by
  have hs : sumNat (Q.reverse ++ [0]) = sumNat Q := by
    rw [
      sumNat_append,
      sumNat_reverse]
    rfl
  show rowList (Q.reverse ++ [0]) = sumNat Q :: bots Q
  rw [
    ← hs]
  exact rowList_snoc Q.reverse 0

/-! The bottom block's reads: its member bound, its length, and
the prefix sums' join against the successor-weighted fold. -/

/-- A member of a family's tail is a member of the family. -/
private theorem mem_of_mem_tail : ∀ (l : List Nat) {y : Nat},
    y ∈ l.tail → y ∈ l
  | [], _, h => h
  | x :: _, _, h => List.Mem.tail x h

/-- Every row sits below the family's total. -/
private theorem rowList_mem_le : ∀ (l : List Nat) {y : Nat},
    y ∈ places.rowList l → y ≤ ground.sumNat l
  | [], _, h => nomatch h
  | x :: t, y, h => by
    have h2 : y ∈ (x + sumNat t) :: rowList t := h
    cases h2 with
    | head => exact Nat.le_refl (x + sumNat t)
    | tail _ h3 =>
      exact Nat.le_trans (rowList_mem_le t h3)
        (Nat.le_add_left (sumNat t) x)

/-- Every bottom row sits below the bottom word's total. -/
private theorem bots_le (Q : List Nat) {y : Nat} (h : y ∈ bots Q) :
    y ≤ ground.sumNat Q := by
  have h1 : y ∈ places.rowList (Q.reverse ++ [0]) :=
    mem_of_mem_tail _ h
  have h2 := rowList_mem_le (Q.reverse ++ [0]) h1
  rw [
    sumNat_append,
    sumNat_reverse] at h2
  exact h2

/-- The bottom block reads the bottom word's own length. -/
private theorem bots_length (Q : List Nat) :
    (bots Q).length = Q.length := by
  have h1 : (places.rowList (Q.reverse ++ [0])).length
      = (Q.reverse ++ [0]).length := places.length_rowList _
  rw [
    rowList_bot Q,
    ground.length_append,
    ground.length_reverse] at h1
  exact Nat.succ.inj h1

/-- The successor-weighted fold is the row list's total. -/
private theorem wtSum_rowList : ∀ l : List Nat,
    wtSum l = ground.sumNat (places.rowList l)
  | [] => rfl
  | x :: t => by
    show x + wtSum t + sumNat t
      = x + sumNat t + sumNat (rowList t)
    rw [
      wtSum_rowList t,
      Nat.add_assoc x (sumNat (rowList t)) (sumNat t),
      Nat.add_comm (sumNat (rowList t)) (sumNat t),
      ← Nat.add_assoc x (sumNat t) (sumNat (rowList t))]

/-- The fold at a trailing letter: the letter enters at its own
key, one beyond the word's length. -/
private theorem wtSum_snoc : ∀ (l : List Nat) (x : Nat),
    wtSum (l ++ [x]) = wtSum l + (l.length + 1) * x
  | [], x => by
    show x + 0 + 0 = 0 + (0 + 1) * x
    rw [
      Nat.one_mul x,
      Nat.zero_add x]
    rfl
  | y :: t, x => by
    show y + wtSum (t ++ [x]) + sumNat (t ++ [x])
      = y + wtSum t + sumNat t + (t.length + 1 + 1) * x
    rw [
      wtSum_snoc t x,
      sumNat_append t [x]]
    show y + (wtSum t + (t.length + 1) * x) + (sumNat t + (x + 0))
      = y + wtSum t + sumNat t + (t.length + 1 + 1) * x
    rw [
      Nat.add_zero x,
      ground.mulAddR (t.length + 1) 1 x,
      Nat.one_mul x,
      ← Nat.add_assoc y (wtSum t) ((t.length + 1) * x),
      Nat.add_assoc (y + wtSum t) ((t.length + 1) * x) (sumNat t + x),
      Nat.add_left_comm ((t.length + 1) * x) (sumNat t) x,
      ← Nat.add_assoc (y + wtSum t) (sumNat t) ((t.length + 1) * x + x)]

/-- The word and its reverse share the keys' complement: the two
folds join at the length's successor against the total. -/
private theorem wtSum_rev : ∀ l : List Nat,
    wtSum l.reverse + wtSum l = (l.length + 1) * ground.sumNat l
  | [] => rfl
  | q :: R => by
    rw [
      ground.reverse_cons q R,
      wtSum_snoc R.reverse q,
      ground.length_reverse R]
    show wtSum R.reverse + (R.length + 1) * q + (q + wtSum R + sumNat R)
      = (R.length + 1 + 1) * (q + sumNat R)
    rw [
      Nat.left_distrib (R.length + 1 + 1) q (sumNat R),
      ground.mulAddR (R.length + 1) 1 q,
      Nat.one_mul q,
      ground.mulAddR (R.length + 1) 1 (sumNat R),
      Nat.one_mul (sumNat R),
      ← wtSum_rev R,
      Nat.add_assoc (wtSum R.reverse) ((R.length + 1) * q)
        (q + wtSum R + sumNat R),
      Nat.add_assoc ((R.length + 1) * q) q
        (wtSum R.reverse + wtSum R + sumNat R),
      Nat.add_left_comm (wtSum R.reverse) ((R.length + 1) * q)
        (q + wtSum R + sumNat R),
      Nat.add_assoc q (wtSum R) (sumNat R),
      Nat.add_assoc (wtSum R.reverse) (wtSum R) (sumNat R)]
    exact congrArg (fun z => (R.length + 1) * q + z)
      (Nat.add_left_comm (wtSum R.reverse) q (wtSum R + sumNat R))

/-- The bottom rows' total joins the successor-weighted fold at
the word's length against its total. -/
private theorem bots_join (Q : List Nat) :
    ground.sumNat (bots Q) + wtSum Q
      = Q.length * ground.sumNat Q := by
  have h1 : wtSum (Q.reverse ++ [0])
      = ground.sumNat (places.rowList (Q.reverse ++ [0])) :=
    wtSum_rowList _
  rw [
    rowList_bot Q,
    wtSum_snoc Q.reverse 0,
    Nat.mul_zero,
    Nat.add_zero] at h1
  have h1' : wtSum Q.reverse
      = ground.sumNat Q + ground.sumNat (bots Q) := h1
  have h2 := wtSum_rev Q
  rw [
    h1'] at h2
  show sumNat (bots Q) + wtSum Q = Q.length * sumNat Q
  refine ground.addCancelL (sumNat Q) ?_
  rw [
    ← Nat.add_assoc (sumNat Q) (sumNat (bots Q)) (wtSum Q),
    h2,
    ground.mulAddR Q.length 1 (sumNat Q),
    Nat.one_mul (sumNat Q),
    Nat.add_comm (Q.length * sumNat Q) (sumNat Q)]

/-! The block laws of the two folds: the row squares split over a
join, the gap fold splits with the crossed pairs, and the constant
block's reads. -/

/-- The row squares' fold splits over a join. -/
private theorem sumSq_append : ∀ xs ys : List Nat,
    c2hat.sumSq (xs ++ ys) = c2hat.sumSq xs + c2hat.sumSq ys
  | [], _ => (Nat.zero_add _).symm
  | x :: t, ys => by
    show x * x + c2hat.sumSq (t ++ ys)
      = x * x + c2hat.sumSq t + c2hat.sumSq ys
    rw [
      sumSq_append t ys,
      Nat.add_assoc]

/-- A constant block's row squares. -/
private theorem sumSq_replicate (c : Nat) : ∀ k : Nat,
    c2hat.sumSq (List.replicate k c) = k * (c * c)
  | 0 => (Nat.zero_mul (c * c)).symm
  | k + 1 => by
    show c * c + c2hat.sumSq (List.replicate k c) = (k + 1) * (c * c)
    rw [
      sumSq_replicate c k,
      ground.mulAddR k 1 (c * c),
      Nat.one_mul (c * c),
      Nat.add_comm (c * c) (k * (c * c))]

/-- The crossed gap fold over two blocks: each member of the first
against the whole second. -/
private def cross : List Nat → List Nat → Nat
  | [], _ => 0
  | x :: t, ys => ys.foldl (fun acc y => acc + (x - y)) 0 + cross t ys

/-- The gap fold splits over a join, the crossed fold reading the
pairs across the blocks. -/
private theorem rho2_append : ∀ xs ys : List Nat,
    c2hat.rho2 (xs ++ ys)
      = c2hat.rho2 xs + c2hat.rho2 ys + cross xs ys
  | [], ys => by
    show c2hat.rho2 ys = 0 + c2hat.rho2 ys + 0
    rw [
      Nat.zero_add,
      Nat.add_zero]
  | x :: t, ys => by
    show (t ++ ys).foldl (fun acc y => acc + (x - y)) 0
        + c2hat.rho2 (t ++ ys)
      = t.foldl (fun acc y => acc + (x - y)) 0 + c2hat.rho2 t
        + c2hat.rho2 ys
        + (ys.foldl (fun acc y => acc + (x - y)) 0 + cross t ys)
    rw [
      ground.foldl_append (fun acc y => acc + (x - y)) t ys 0,
      ground.foldlSeed (fun y => x - y) ys
        (t.foldl (fun acc y => acc + (x - y)) 0),
      rho2_append t ys,
      Nat.add_add_add_comm (t.foldl (fun acc y => acc + (x - y)) 0)
        (ys.foldl (fun acc y => acc + (x - y)) 0)
        (c2hat.rho2 t + c2hat.rho2 ys) (cross t ys),
      ← Nat.add_assoc (t.foldl (fun acc y => acc + (x - y)) 0)
        (c2hat.rho2 t) (c2hat.rho2 ys)]

/-- The crossed fold splits over a join in the second block. -/
private theorem cross_appendR : ∀ xs ys zs : List Nat,
    cross xs (ys ++ zs) = cross xs ys + cross xs zs
  | [], _, _ => rfl
  | x :: t, ys, zs => by
    show (ys ++ zs).foldl (fun acc y => acc + (x - y)) 0
        + cross t (ys ++ zs)
      = ys.foldl (fun acc y => acc + (x - y)) 0 + cross t ys
        + (zs.foldl (fun acc y => acc + (x - y)) 0 + cross t zs)
    rw [
      ground.foldl_append (fun acc y => acc + (x - y)) ys zs 0,
      ground.foldlSeed (fun y => x - y) zs
        (ys.foldl (fun acc y => acc + (x - y)) 0),
      cross_appendR t ys zs,
      Nat.add_add_add_comm (ys.foldl (fun acc y => acc + (x - y)) 0)
        (zs.foldl (fun acc y => acc + (x - y)) 0) (cross t ys) (cross t zs)]

/-- A constant first block reads the second block's fold once per
member. -/
private theorem cross_replicateL (c : Nat) : ∀ (k : Nat) (ys : List Nat),
    cross (List.replicate k c) ys
      = k * ys.foldl (fun acc y => acc + (c - y)) 0
  | 0, ys => (Nat.zero_mul (ys.foldl (fun acc y => acc + (c - y)) 0)).symm
  | k + 1, ys => by
    show ys.foldl (fun acc y => acc + (c - y)) 0
        + cross (List.replicate k c) ys
      = (k + 1) * ys.foldl (fun acc y => acc + (c - y)) 0
    rw [
      cross_replicateL c k ys,
      ground.mulAddR k 1 (ys.foldl (fun acc y => acc + (c - y)) 0),
      Nat.one_mul (ys.foldl (fun acc y => acc + (c - y)) 0),
      Nat.add_comm (ys.foldl (fun acc y => acc + (c - y)) 0)
        (k * ys.foldl (fun acc y => acc + (c - y)) 0)]

/-- The gap fold against a dominated block: each member's gap
rejoins its own value, one top per member. -/
private theorem gapFold_join (X : Nat) : ∀ l : List Nat,
    (∀ y : Nat, y ∈ l → y ≤ X) →
    l.foldl (fun acc y => acc + (X - y)) 0 + ground.sumNat l
      = l.length * X
  | [], _ => (Nat.zero_mul X).symm
  | y :: t, h => by
    have hy : y ≤ X := h y (List.Mem.head t)
    have hs : t.foldl (fun acc z => acc + (X - z)) (0 + (X - y))
        = 0 + (X - y) + t.foldl (fun acc z => acc + (X - z)) 0 :=
      ground.foldlSeed (fun z => X - z) t (0 + (X - y))
    have hih := gapFold_join X t (fun z hz => h z (List.Mem.tail y hz))
    show t.foldl (fun acc z => acc + (X - z)) (0 + (X - y))
        + (y + ground.sumNat t) = (t.length + 1) * X
    rw [
      hs,
      Nat.zero_add (X - y),
      ground.mulAddR t.length 1 X,
      Nat.one_mul X,
      Nat.add_add_add_comm (X - y) (t.foldl (fun acc z => acc + (X - z)) 0)
        y (ground.sumNat t),
      hih,
      Nat.add_comm (X - y) y,
      ground.natAddSubCancel hy,
      Nat.add_comm X (t.length * X)]

/-- The top rows against the run: each top row's gap over the run
is that row's own excess. -/
private theorem cross_map_replicate (m u : Nat) : ∀ l : List Nat,
    cross (l.map (fun x => m + x)) (List.replicate u m)
      = u * ground.sumNat l
  | [] => by
    show (0 : Nat) = u * 0
    rw [
      Nat.mul_zero]
  | x :: t => by
    show (List.replicate u m).foldl (fun acc y => acc + (m + x - y)) 0
        + cross (t.map (fun z => m + z)) (List.replicate u m)
      = u * (x + ground.sumNat t)
    rw [
      c2hat.gapFold_replicate (m + x) m u 0,
      Nat.zero_add,
      ground.addSubSelfL m x,
      cross_map_replicate m u t,
      Nat.left_distrib u x (ground.sumNat t)]

/-- The top rows against the bottom block: every bottom row sits
below every top row, so the crossed gaps join the bottom total. -/
private theorem cross_map_bots (m : Nat) (B : List Nat)
    (hB : ∀ y : Nat, y ∈ B → y ≤ m) : ∀ l : List Nat,
    cross (l.map (fun x => m + x)) B + l.length * ground.sumNat B
      = B.length * (l.length * m + ground.sumNat l)
  | [] => by
    show 0 + 0 * ground.sumNat B = B.length * (0 * m + 0)
    rw [
      Nat.zero_mul (ground.sumNat B),
      Nat.zero_add,
      Nat.zero_mul m,
      Nat.add_zero,
      Nat.mul_zero]
  | x :: t => by
    have hdom : ∀ y : Nat, y ∈ B → y ≤ m + x := fun y hy =>
      Nat.le_trans (hB y hy) (Nat.le_add_right m x)
    have hj := gapFold_join (m + x) B hdom
    have hih := cross_map_bots m B hB t
    show B.foldl (fun acc y => acc + (m + x - y)) 0
        + cross (t.map (fun z => m + z)) B
        + (t.length + 1) * ground.sumNat B
      = B.length * ((t.length + 1) * m + (x + ground.sumNat t))
    rw [
      ground.mulAddR t.length 1 (ground.sumNat B),
      Nat.one_mul (ground.sumNat B),
      Nat.add_comm (t.length * ground.sumNat B) (ground.sumNat B),
      Nat.add_add_add_comm (B.foldl (fun acc y => acc + (m + x - y)) 0)
        (cross (t.map (fun z => m + z)) B) (ground.sumNat B)
        (t.length * ground.sumNat B),
      hj,
      hih,
      ← Nat.left_distrib B.length (m + x) (t.length * m + ground.sumNat t),
      ground.mulAddR t.length 1 m,
      Nat.one_mul m,
      Nat.add_add_add_comm m x (t.length * m) (ground.sumNat t),
      Nat.add_comm m (t.length * m)]

/-! The member's own display: the vacant middle's count at the
floor, the shape's three blocks, and the row list's own. -/

/-- The vacant middle's count at the floor. -/
private theorem middle_count (a b k : Nat) :
    a + b + k + 1 - 1 - a - b = k := by
  show a + b + k - a - b = k
  rw [
    Nat.add_assoc a b k,
    ground.addSubSelfL a (b + k),
    ground.addSubSelfL b k]

/-- The member's three blocks at the floor. -/
private theorem member_split (P Q : List Nat) (k : Nat) :
    member P Q (P.length + Q.length + k + 1)
      = P ++ (List.replicate k 0 ++ (Q.reverse ++ [0])) := by
  show P ++ List.replicate
      (P.length + Q.length + k + 1 - 1 - P.length - Q.length) 0
      ++ Q.reverse ++ [0]
    = P ++ (List.replicate k 0 ++ (Q.reverse ++ [0]))
  rw [
    middle_count P.length Q.length k,
    ground.append_assoc (P ++ List.replicate k 0) Q.reverse [0],
    ground.append_assoc P (List.replicate k 0) (Q.reverse ++ [0])]

/-- The member's length is the residue count. -/
private theorem member_length (P Q : List Nat) (k : Nat) :
    (member P Q (P.length + Q.length + k + 1)).length
      = P.length + Q.length + k + 1 := by
  rw [
    member_split P Q k,
    ground.length_append P (List.replicate k 0 ++ (Q.reverse ++ [0])),
    ground.length_append (List.replicate k 0) (Q.reverse ++ [0]),
    ground.length_replicate 0 k,
    ground.length_append Q.reverse [0],
    ground.length_reverse Q]
  show P.length + (k + (Q.length + 1)) = P.length + Q.length + k + 1
  rw [
    ← Nat.add_assoc k Q.length 1,
    Nat.add_comm k Q.length,
    ← Nat.add_assoc P.length (Q.length + k) 1,
    ← Nat.add_assoc P.length Q.length k]

/-- A constant block absorbs its own member at the head of the
tail. -/
private theorem replicate_cons_app (c : Nat) : ∀ (k : Nat) (t : List Nat),
    List.replicate k c ++ c :: t = List.replicate (k + 1) c ++ t
  | 0, _ => rfl
  | k + 1, t => congrArg (List.cons c) (replicate_cons_app c k t)

/-- The member's row list: the top rows at the bottom word's total
above the top word's own, the run at that total, and the bottom
rows below. -/
private theorem rowList_member (P Q : List Nat) (k : Nat) :
    places.rowList (member P Q (P.length + Q.length + k + 1))
      = (places.rowList P).map (fun x => ground.sumNat Q + x)
        ++ (List.replicate (k + 1) (ground.sumNat Q) ++ bots Q) := by
  have hs2 : ground.sumNat (Q.reverse ++ [0]) = ground.sumNat Q := by
    rw [
      ground.sumNat_append,
      ground.sumNat_reverse]
    rfl
  have hs1 : ground.sumNat (List.replicate k 0 ++ (Q.reverse ++ [0]))
      = ground.sumNat Q := by
    rw [
      ground.sumNat_append,
      ground.sumNat_replicate_zero,
      hs2,
      Nat.zero_add]
  rw [
    member_split P Q k,
    rowList_append P (List.replicate k 0 ++ (Q.reverse ++ [0])),
    hs1]
  refine congrArg (fun z =>
    (places.rowList P).map (fun x => ground.sumNat Q + x) ++ z) ?_
  rw [
    rowList_append (List.replicate k 0) (Q.reverse ++ [0]),
    hs2,
    places.rowList_replicate_zero k,
    ground.map_replicate (fun x => ground.sumNat Q + x) 0 k,
    rowList_bot Q]
  show List.replicate k (ground.sumNat Q)
      ++ ground.sumNat Q :: bots Q
    = List.replicate (k + 1) (ground.sumNat Q) ++ bots Q
  exact replicate_cons_app (ground.sumNat Q) k (bots Q)

/-! The Nat identities the closed form reads: the sum's square,
the sixteen blocks' regrouping, and the coefficient collection at
the residue count. -/

/-- The regrouping at the sixteen blocks. -/
private theorem blockShuffle (a b c d e f g h i j k l n o p q : Nat) :
    a + b + c + (d + e + f + g + h + i + j + (k + l + (n + (o + p)))) + q
      = d + (b + e) + (f + g + l + o + h)
        + (q + (a + k + n) + c + (i + p)) + j := by
  conv => lhs; rw [
    ← Nat.add_assoc (a + b + c) (d + e + f + g + h + i + j)
      (k + l + (n + (o + p))),
    ← Nat.add_assoc (a + b + c) (d + e + f + g + h + i) j,
    ← Nat.add_assoc (a + b + c) (d + e + f + g + h) i,
    ← Nat.add_assoc (a + b + c) (d + e + f + g) h,
    ← Nat.add_assoc (a + b + c) (d + e + f) g,
    ← Nat.add_assoc (a + b + c) (d + e) f,
    ← Nat.add_assoc (a + b + c) d e,
    ← Nat.add_assoc (a + b + c + d + e + f + g + h + i + j) (k + l)
      (n + (o + p)),
    ← Nat.add_assoc (a + b + c + d + e + f + g + h + i + j) k l,
    ← Nat.add_assoc (a + b + c + d + e + f + g + h + i + j + k + l) n
      (o + p),
    ← Nat.add_assoc (a + b + c + d + e + f + g + h + i + j + k + l + n) o p]
  conv => rhs; rw [
    ← Nat.add_assoc d b e,
    ← Nat.add_assoc (d + b + e) (f + g + l + o) h,
    ← Nat.add_assoc (d + b + e) (f + g + l) o,
    ← Nat.add_assoc (d + b + e) (f + g) l,
    ← Nat.add_assoc (d + b + e) f g,
    ← Nat.add_assoc (d + b + e + f + g + l + o + h) (q + (a + k + n) + c)
      (i + p),
    ← Nat.add_assoc (d + b + e + f + g + l + o + h) (q + (a + k + n)) c,
    ← Nat.add_assoc (d + b + e + f + g + l + o + h) q (a + k + n),
    ← Nat.add_assoc (d + b + e + f + g + l + o + h + q) (a + k) n,
    ← Nat.add_assoc (d + b + e + f + g + l + o + h + q) a k,
    ← Nat.add_assoc (d + b + e + f + g + l + o + h + q + a + k + n + c) i p,
    Nat.add_right_comm (d + b + e + f + g + l + o + h) q a,
    Nat.add_right_comm (d + b + e + f + g + l + o) h a,
    Nat.add_right_comm (d + b + e + f + g + l) o a,
    Nat.add_right_comm (d + b + e + f + g) l a,
    Nat.add_right_comm (d + b + e + f) g a,
    Nat.add_right_comm (d + b + e) f a,
    Nat.add_right_comm (d + b) e a,
    Nat.add_right_comm d b a,
    Nat.add_comm d a,
    Nat.add_right_comm a d b,
    Nat.add_right_comm (a + b + d + e + f + g + l + o + h + q + k) n c,
    Nat.add_right_comm (a + b + d + e + f + g + l + o + h + q) k c,
    Nat.add_right_comm (a + b + d + e + f + g + l + o + h) q c,
    Nat.add_right_comm (a + b + d + e + f + g + l + o) h c,
    Nat.add_right_comm (a + b + d + e + f + g + l) o c,
    Nat.add_right_comm (a + b + d + e + f + g) l c,
    Nat.add_right_comm (a + b + d + e + f) g c,
    Nat.add_right_comm (a + b + d + e) f c,
    Nat.add_right_comm (a + b + d) e c,
    Nat.add_right_comm (a + b) d c,
    Nat.add_right_comm (a + b + c + d + e + f + g + l) o h,
    Nat.add_right_comm (a + b + c + d + e + f + g) l h,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + l + o + q + k) n i,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + l + o + q) k i,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + l + o) q i,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + l) o i,
    Nat.add_right_comm (a + b + c + d + e + f + g + h) l i,
    Nat.add_right_comm
      (a + b + c + d + e + f + g + h + i + l + o + q + k + n) p j,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + l + o + q + k) n
      j,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + l + o + q) k j,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + l + o) q j,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + l) o j,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i) l j,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + j + l + o) q k,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + j + l) o k,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + j) l k,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + j + k + l + o) q
      n,
    Nat.add_right_comm (a + b + c + d + e + f + g + h + i + j + k + l) o n,
    Nat.add_right_comm
      (a + b + c + d + e + f + g + h + i + j + k + l + n + o) q p]

/-- The blocks' identity at the residue count: the run's count
carries the three block sums against the degree join. -/
private theorem blockAlg (a b m SP SB JQ ST SQ RT RB u d : Nat)
    (hd : a + b + u = d) (h5 : JQ + SB = b * m) :
    m * (d * m) + 2 * (m * SP)
        + (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB
            + 2 * (JQ * m) + d * (SP + b * m)) + a * SB
      = ST + (u * (m * m) + SQ)
        + (RT + RB + u * SP + u * JQ + b * (a * m + SP))
        + (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB)
        + 2 * (m * JQ) := by
  have e5 : u * (b * m) = u * JQ + u * SB := by
    rw [
      ← h5,
      Nat.left_distrib u JQ SB]
  rw [
    ← hd,
    ground.mulLeftComm m (a + b + u) m,
    Nat.left_distrib (a + b + u) SP (b * m),
    ground.mulAddR (a + b) u (m * m),
    ground.mulAddR (a + b) u SP,
    ground.mulAddR (a + b) u (b * m),
    e5,
    Nat.left_distrib (a + b) (m * m + SP) (b * m),
    Nat.left_distrib (a + b) (m * m) SP,
    ground.mulAddR (a + b) u SB,
    Nat.mul_comm SP m,
    Nat.mul_comm JQ m]
  exact blockShuffle ((a + b) * (m * m)) (u * (m * m)) (2 * (m * SP)) ST SQ
    RT RB
    (b * (a * m + SP)) ((a + b) * SB) (2 * (m * JQ)) ((a + b) * SP) (u * SP)
    ((a + b) * (b * m)) (u * JQ) (u * SB) (a * SB)

/-- The cleared read's closed form: the quadratic's coefficients
against the square identity, the block splits and the degree
join. -/
private theorem coreAlg (a b m SP SB JQ ST SQ RT RB u d F G SS RH : Nat)
    (hd : a + b + u = d)
    (h1 : F + G * G = d * SS + d * RH)
    (h2 : SS = ST + (u * (m * m) + SQ))
    (h3 : RH + a * SB = RT + RB + u * SP + u * JQ + b * (a * m + SP))
    (h4 : G + JQ = d * m + SP)
    (h5 : JQ + SB = b * m) :
    2 * (SP * JQ)
        + d * (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB
            + 2 * (JQ * m) + d * (SP + b * m))
      = F + (SP * SP + JQ * JQ
          + d * (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m)
              + d * SB)) := by
  have e2 : (G + JQ) * (G + JQ) = (d * m + SP) * (d * m + SP) :=
    congrArg (fun z => z * z) h4
  rw [
    ground.sqAdd G JQ,
    ground.sqAdd (d * m) SP] at e2
  have e3 : (G + JQ) * JQ = (d * m + SP) * JQ :=
    congrArg (fun z => z * JQ) h4
  rw [
    ground.mulAddR G JQ JQ,
    ground.mulAddR (d * m) SP JQ] at e3
  have e4 : G * G + 2 * (d * m * JQ) + 2 * (SP * JQ)
      = d * m * (d * m) + 2 * (d * m * SP) + (SP * SP + JQ * JQ) := by
    rw [
      Nat.add_assoc (G * G) (2 * (d * m * JQ)) (2 * (SP * JQ)),
      ← Nat.left_distrib 2 (d * m * JQ) (SP * JQ),
      ← e3,
      Nat.left_distrib 2 (G * JQ) (JQ * JQ),
      ← Nat.add_assoc (G * G) (2 * (G * JQ)) (2 * (JQ * JQ)),
      Nat.two_mul (JQ * JQ),
      ← Nat.add_assoc (G * G + 2 * (G * JQ)) (JQ * JQ) (JQ * JQ),
      e2,
      Nat.add_assoc (d * m * (d * m) + 2 * (d * m * SP)) (SP * SP) (JQ * JQ)]
  have e1 : F + G * G + d * (a * SB)
      = d * (ST + (u * (m * m) + SQ))
        + d * (RT + RB + u * SP + u * JQ + b * (a * m + SP)) := by
    rw [
      h1,
      ← h3,
      Nat.left_distrib d RH (a * SB),
      ← h2,
      Nat.add_assoc (d * SS) (d * RH) (d * (a * SB))]
  refine ground.addCancelR (G * G + d * (a * SB) + 2 * (d * m * JQ)) ?_
  conv => lhs; rw [
    ← Nat.add_assoc
      (2 * (SP * JQ) + d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))) (G * G + d * (a * SB)) (2 * (d * m * JQ)),
    ← Nat.add_assoc
      (2 * (SP * JQ) + d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))) (G * G) (d * (a * SB)),
    Nat.add_right_comm (2 * (SP * JQ))
      (d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))) (G * G),
    Nat.add_comm (2 * (SP * JQ)) (G * G),
    Nat.add_right_comm
      (G * G + 2 * (SP * JQ) + d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))) (d * (a * SB)) (2 * (d * m * JQ)),
    Nat.add_right_comm (G * G + 2 * (SP * JQ))
      (d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))) (2 * (d * m * JQ)),
    Nat.add_right_comm (G * G) (2 * (SP * JQ)) (2 * (d * m * JQ))]
  conv => rhs; rw [
    ← Nat.add_assoc F (SP * SP + JQ * JQ)
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB)),
    ← Nat.add_assoc
      (F + (SP * SP + JQ * JQ) +
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB)))
      (G * G + d * (a * SB)) (2 * (d * m * JQ)),
    ← Nat.add_assoc
      (F + (SP * SP + JQ * JQ) +
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB)))
      (G * G) (d * (a * SB)),
    Nat.add_right_comm (F + (SP * SP + JQ * JQ))
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB))
      (G * G),
    Nat.add_right_comm F (SP * SP + JQ * JQ) (G * G),
    Nat.add_right_comm (F + G * G + (SP * SP + JQ * JQ))
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB))
      (d * (a * SB)),
    Nat.add_right_comm (F + G * G) (SP * SP + JQ * JQ) (d * (a * SB))]
  rw [
    e4,
    e1]
  conv => lhs; rw [
    Nat.add_right_comm (d * m * (d * m) + 2 * (d * m * SP))
      (SP * SP + JQ * JQ)
      (d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))),
    Nat.add_right_comm
      (d * m * (d * m) + 2 * (d * m * SP) +
      (d *
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m)))) (SP * SP + JQ * JQ) (d * (a * SB))]
  conv => rhs; rw [
    Nat.add_right_comm
      (d * (ST + (u * (m * m) + SQ)) +
      (d * (RT + RB + u * SP + u * JQ + b * (a * m + SP))))
      (SP * SP + JQ * JQ)
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB)),
    Nat.add_right_comm
      (d * (ST + (u * (m * m) + SQ)) +
      (d * (RT + RB + u * SP + u * JQ + b * (a * m + SP))) +
      (d *
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB)))
      (SP * SP + JQ * JQ) (2 * (d * m * JQ))]
  refine congrArg (fun z => z + (SP * SP + JQ * JQ)) ?_
  rw [
    ground.mulAssoc d m (d * m),
    ground.mulAssoc d m SP,
    ground.mulLeftComm 2 d (m * SP),
    ground.mulAssoc d m JQ,
    ground.mulLeftComm 2 d (m * JQ),
    ← Nat.left_distrib d (m * (d * m)) (2 * (m * SP)),
    ← Nat.left_distrib d (m * (d * m) + 2 * (m * SP))
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m)),
    ← Nat.left_distrib d
      (m * (d * m) + 2 * (m * SP) +
      (ST + SQ + RT + RB + b * (a * m + SP) + (a + b) * SB + 2 * (JQ * m) +
      d * (SP + b * m))) (a * SB),
    ← Nat.left_distrib d (ST + (u * (m * m) + SQ))
      (RT + RB + u * SP + u * JQ + b * (a * m + SP)),
    ← Nat.left_distrib d
      (ST + (u * (m * m) + SQ) +
      (RT + RB + u * SP + u * JQ + b * (a * m + SP)))
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB),
    ← Nat.left_distrib d
      (ST + (u * (m * m) + SQ) +
      (RT + RB + u * SP + u * JQ + b * (a * m + SP)) +
      (a * SB + (a + b) * (m * m + SP + b * m) + 2 * (SP * m) + d * SB))
      (2 * (m * JQ))]
  exact congrArg (fun z => d * z)
    (blockAlg a b m SP SB JQ ST SQ RT RB u d hd h5)

/-- A raised block's total: the raise once per member above the
block's own total. -/
private theorem sumNat_mapAdd (c : Nat) : ∀ l : List Nat,
    ground.sumNat (l.map (fun x => c + x))
      = l.length * c + ground.sumNat l
  | [] => (Nat.zero_mul c).symm
  | x :: t => by
    show c + x + ground.sumNat (t.map (fun z => c + z))
      = (t.length + 1) * c + (x + ground.sumNat t)
    rw [
      sumNat_mapAdd c t,
      ground.mulAddR t.length 1 c,
      Nat.one_mul c,
      Nat.add_add_add_comm c x (t.length * c) (ground.sumNat t),
      Nat.add_comm c (t.length * c)]

/-! The member's block reads and the evaluation agreement at the
floor's own spelling. -/

/-- The evaluation agreement at the floor's own spelling. -/
private theorem evalAt (P Q : List Nat) (k : Nat) :
    (poly.eval (casPoly P Q)
        (ground.BPair.ofNat (P.length + Q.length + k + 1))).oneValue
      (ground.BPair.ofNat (c2hat.dfQ
        (member P Q (P.length + Q.length + k + 1)))) := by
  have hb : ∀ y : Nat, y ∈ bots Q → y ≤ ground.sumNat Q :=
    fun _ hy => bots_le Q hy
  have h5 : wtSum Q + ground.sumNat (bots Q)
      = Q.length * ground.sumNat Q := by
    rw [
      Nat.add_comm (wtSum Q) (ground.sumNat (bots Q))]
    exact bots_join Q
  have hfold : (bots Q).foldl
      (fun acc y => acc + (ground.sumNat Q - y)) 0 = wtSum Q := by
    refine ground.addCancelR (ground.sumNat (bots Q)) ?_
    rw [
      gapFold_join (ground.sumNat Q) (bots Q) hb,
      bots_length Q]
    exact h5.symm
  have hrow := rowList_member P Q k
  have hlen := member_length P Q k
  have hsq : (member P Q (P.length + Q.length + k + 1)).length
        * c2hat.sumSq (places.rowList
            (member P Q (P.length + Q.length + k + 1)))
      = places.degree (member P Q (P.length + Q.length + k + 1))
          * places.degree (member P Q (P.length + Q.length + k + 1))
        + c2hat.sqGaps (places.rowList
            (member P Q (P.length + Q.length + k + 1))) :=
    c2hat.squareAll (member P Q (P.length + Q.length + k + 1))
  rw [
    hlen] at hsq
  have h1 : c2hat.dfQ (member P Q (P.length + Q.length + k + 1))
        + places.degree (member P Q (P.length + Q.length + k + 1))
          * places.degree (member P Q (P.length + Q.length + k + 1))
      = (P.length + Q.length + k + 1)
          * c2hat.sumSq (places.rowList
              (member P Q (P.length + Q.length + k + 1)))
        + (P.length + Q.length + k + 1)
          * c2hat.rho2 (places.rowList
              (member P Q (P.length + Q.length + k + 1))) := by
    show c2hat.sqGaps (places.rowList
          (member P Q (P.length + Q.length + k + 1)))
        + (member P Q (P.length + Q.length + k + 1)).length
          * c2hat.rho2 (places.rowList
              (member P Q (P.length + Q.length + k + 1)))
        + _ = _
    rw [
      hlen,
      hsq,
      Nat.add_right_comm
        (c2hat.sqGaps
        (places.rowList (member P Q (P.length + Q.length + k + 1))))
        ((P.length + Q.length + k + 1) * c2hat.rho2
        (places.rowList (member P Q (P.length + Q.length + k + 1))))
        (places.degree (member P Q (P.length + Q.length + k + 1)) *
        places.degree (member P Q (P.length + Q.length + k + 1))),
      Nat.add_comm
        (c2hat.sqGaps
        (places.rowList (member P Q (P.length + Q.length + k + 1))))
        (places.degree (member P Q (P.length + Q.length + k + 1)) *
        places.degree (member P Q (P.length + Q.length + k + 1)))]
  have h2 : c2hat.sumSq (places.rowList
        (member P Q (P.length + Q.length + k + 1)))
      = c2hat.sumSq ((places.rowList P).map (fun x => ground.sumNat Q + x))
        + ((k + 1) * (ground.sumNat Q * ground.sumNat Q)
          + c2hat.sumSq (bots Q)) := by
    rw [
      hrow,
      sumSq_append ((places.rowList P).map (fun x => ground.sumNat Q + x))
        (List.replicate (k + 1) (ground.sumNat Q) ++ bots Q),
      sumSq_append (List.replicate (k + 1) (ground.sumNat Q)) (bots Q),
      sumSq_replicate (ground.sumNat Q) (k + 1)]
  have hcb := cross_map_bots (ground.sumNat Q) (bots Q) hb (places.rowList
    P)
  rw [
    places.length_rowList P,
    bots_length Q] at hcb
  have h3 : c2hat.rho2 (places.rowList
        (member P Q (P.length + Q.length + k + 1)))
        + P.length * ground.sumNat (bots Q)
      = c2hat.rho2 ((places.rowList P).map (fun x => ground.sumNat Q + x)) +
        c2hat.rho2 (bots Q)
        + (k + 1) * ground.sumNat (places.rowList P)
        + (k + 1) * wtSum Q
        + Q.length * (P.length * ground.sumNat Q
          + ground.sumNat (places.rowList P)) := by
    rw [
      hrow,
      rho2_append ((places.rowList P).map (fun x => ground.sumNat Q + x))
        (List.replicate (k + 1) (ground.sumNat Q) ++ bots Q),
      rho2_append (List.replicate (k + 1) (ground.sumNat Q)) (bots Q),
      c2hat.rho2_replicate (ground.sumNat Q) (k + 1),
      cross_appendR ((places.rowList P).map (fun x => ground.sumNat Q + x))
        (List.replicate (k + 1) (ground.sumNat Q)) (bots Q),
      cross_replicateL (ground.sumNat Q) (k + 1) (bots Q),
      hfold,
      cross_map_replicate (ground.sumNat Q) (k + 1) (places.rowList P),
      Nat.zero_add (c2hat.rho2 (bots Q))]
    conv => lhs; rw [
      ← Nat.add_assoc
        (c2hat.rho2 ((places.rowList P).map (fun x => ground.sumNat Q + x)))
        (c2hat.rho2 (bots Q)) ((k + 1) * wtSum Q),
      ← Nat.add_assoc
        (c2hat.rho2 ((places.rowList P).map (fun x => ground.sumNat Q + x))
        + c2hat.rho2 (bots Q) + ((k + 1) * wtSum Q))
        ((k + 1) * ground.sumNat (places.rowList P))
        (cross ((places.rowList P).map (fun x => ground.sumNat Q + x))
        (bots Q)),
      Nat.add_right_comm
        (c2hat.rho2 ((places.rowList P).map (fun x => ground.sumNat Q + x))
        + c2hat.rho2 (bots Q)) ((k + 1) * wtSum Q)
        ((k + 1) * ground.sumNat (places.rowList P)),
      Nat.add_assoc
        (c2hat.rho2 ((places.rowList P).map (fun x => ground.sumNat Q + x))
        + c2hat.rho2 (bots Q) + ((k + 1) * ground.sumNat (places.rowList P))
        + ((k + 1) * wtSum Q))
        (cross ((places.rowList P).map (fun x => ground.sumNat Q + x))
        (bots Q)) (P.length * ground.sumNat (bots Q)),
      hcb]
  have h4 : places.degree (member P Q (P.length + Q.length + k + 1))
        + wtSum Q
      = (P.length + Q.length + (k + 1)) * ground.sumNat Q
        + ground.sumNat (places.rowList P) := by
    show ground.sumNat (places.rowList
        (member P Q (P.length + Q.length + k + 1))) + wtSum Q = _
    rw [
      hrow,
      ground.sumNat_append
        ((places.rowList P).map (fun x => ground.sumNat Q + x))
        (List.replicate (k + 1) (ground.sumNat Q) ++ bots Q),
      ground.sumNat_append (List.replicate (k + 1) (ground.sumNat Q))
        (bots Q),
      sumNat_mapAdd (ground.sumNat Q) (places.rowList P),
      ground.sumNat_replicate (ground.sumNat Q) (k + 1),
      places.length_rowList P,
      ground.mulAddR (P.length + Q.length) (k + 1) (ground.sumNat Q),
      ground.mulAddR P.length Q.length (ground.sumNat Q)]
    conv => lhs; rw [
      ← Nat.add_assoc
        (P.length * ground.sumNat Q + ground.sumNat (places.rowList P))
        ((k + 1) * ground.sumNat Q) (ground.sumNat (bots Q)),
      Nat.add_right_comm (P.length * ground.sumNat Q)
        (ground.sumNat (places.rowList P)) ((k + 1) * ground.sumNat Q),
      Nat.add_right_comm
        (P.length * ground.sumNat Q + ((k + 1) * ground.sumNat Q) +
        ground.sumNat (places.rowList P)) (ground.sumNat (bots Q)) (wtSum Q),
      Nat.add_assoc
        (P.length * ground.sumNat Q + ((k + 1) * ground.sumNat Q) +
        ground.sumNat (places.rowList P)) (wtSum Q) (ground.sumNat (bots Q)),
      h5,
      Nat.add_right_comm
        (P.length * ground.sumNat Q + ((k + 1) * ground.sumNat Q))
        (ground.sumNat (places.rowList P)) (Q.length * ground.sumNat Q),
      Nat.add_right_comm (P.length * ground.sumNat Q)
        ((k + 1) * ground.sumNat Q) (Q.length * ground.sumNat Q)]
  refine poly.reads_ov
    (poly.reads_step
      (poly.reads_step
        (poly.reads_step poly.reads_unit _ _ _) _ _ _) _ _ _) ?_
  rw [
    wtSum_rowList P]
  exact coreAlg P.length Q.length (ground.sumNat Q)
    (ground.sumNat (places.rowList P)) (ground.sumNat (bots Q)) (wtSum Q)
    (c2hat.sumSq ((places.rowList P).map (fun x => ground.sumNat Q + x)))
      (c2hat.sumSq (bots Q))
    (c2hat.rho2 ((places.rowList P).map (fun x => ground.sumNat Q + x)))
      (c2hat.rho2 (bots Q))
    (k + 1) (P.length + Q.length + k + 1)
    (c2hat.dfQ (member P Q (P.length + Q.length + k + 1)))
    (places.degree (member P Q (P.length + Q.length + k + 1)))
    (c2hat.sumSq (places.rowList (member P Q (P.length + Q.length + k +
      1))))
    (c2hat.rho2 (places.rowList (member P Q (P.length + Q.length + k + 1))))
    rfl h1 h2 h3 h4 h5

/-- The evaluation agreement: at every residue count from the
floor, the Casimir polynomial's value is the member's cleared
read. -/
theorem casPoly_eval : ∀ (P Q : List Nat) (d : Nat),
    P.length + Q.length + 1 ≤ d →
    (poly.eval (casPoly P Q) (ground.BPair.ofNat d)).oneValue
      (ground.BPair.ofNat (c2hat.dfQ (member P Q d))) := by
  intro P Q d h
  have hk : ∃ k : Nat, d = P.length + Q.length + k + 1 :=
    ⟨d - (P.length + Q.length + 1), by
      rw [
        Nat.add_right_comm (P.length + Q.length)
          (d - (P.length + Q.length + 1)) 1]
      exact (ground.natAddSubCancel h).symm⟩
  cases hk with
  | intro k hk =>
    subst hk
    exact evalAt P Q k

/-! The dimension tier: the member's gap product against the unit
display's, the four factor classes and the polynomial pair they
build. -/

/-- The dimension pair's first member: the within-word gap
products, the word-against-run binomial numerators (one linear
factor per box of each word), and the cross factors' first
members, one linear factor per key pair. -/
def dimNum (P Q : List Nat) : poly.Poly :=
  let b := Q.length
  let base : poly.Poly := [ground.BPair.ofNat
    (weyldim.gapProd (List.zipWith (fun x y => x + y) (places.rowList P)
        (weyldim.descRun 1 P.length))
      * weyldim.gapProd (List.zipWith (fun x y => x + y) (bots Q)
        (weyldim.descRun 1 Q.length)))]
  let top := (List.range P.length).foldl (fun acc i =>
    (List.range (ground.getAt 0 (places.rowList P) i)).foldl
      (fun acc2 j => poly.mul acc2
        [⟨ground.posOfSucc (j + 1), ground.posOfSucc (b + i + 1)⟩,
         ground.BPair.ofNat 1]) acc) base
  let bot := (List.range Q.length).foldl (fun acc t =>
    (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
      (fun acc2 j => poly.mul acc2
        [⟨ground.posOfSucc (j + 1), ground.posOfSucc (t + P.length + 1)⟩,
         ground.BPair.ofNat 1]) acc) top
  (List.range P.length).foldl (fun acc i =>
    (List.range Q.length).foldl (fun acc2 t => poly.mul acc2
      [⟨ground.posOfSucc (ground.getAt 0 (places.rowList P) i
          + ground.getAt 0 (places.rowList Q) t),
        ground.posOfSucc (i + 1 + t)⟩,
       ground.BPair.ofNat 1]) acc) bot

/-- The dimension pair's second member: the unit-side constants —
the two run superproducts with the binomial denominators — and the
cross factors' position gaps, one linear factor per key pair. -/
def dimDen (P Q : List Nat) : poly.Poly :=
  let a := P.length
  let b := Q.length
  let base : poly.Poly := [ground.BPair.ofNat
    (weyldim.gapProd (weyldim.descRun 1 P.length)
      * weyldim.gapProd (weyldim.descRun 1 Q.length)
      * (List.range P.length).foldl (fun n i =>
          (List.range (ground.getAt 0 (places.rowList P) i)).foldl
            (fun n2 j => n2 * (a - (i + 1) + (j + 1))) n) 1
      * (List.range Q.length).foldl (fun n t =>
          (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
            (fun n2 j => n2 * (b - (t + 1) + (j + 1))) n) 1)]
  (List.range P.length).foldl (fun acc i =>
    (List.range Q.length).foldl (fun acc2 t => poly.mul acc2
      [⟨ground.posOfSucc 0, ground.posOfSucc (i + 1 + t)⟩,
       ground.BPair.ofNat 1]) acc) base


/-! The rising products at this tier: the window's growth at its
top and the telescope's crossed identity, over `ground.rise`'s
floor and its split at a step. -/

/-- The rising product grows at its top. -/
private theorem rise_snoc (c k : Nat) :
    ground.rise c (k + 1) = ground.rise c k * (c + k) := by
  rw [ground.rise_split c k 1]
  show ground.rise c k * ((c + k) * 1) = ground.rise c k * (c + k)
  rw [Nat.mul_one]

/-- The range fold of a rising window is the rising product. -/
private theorem riseFold (c : Nat) : ∀ k : Nat,
    ground.famFold Nat.mul 1 (fun j => c + (j + 1)) (List.range k)
      = ground.rise (c + 1) k
  | 0 => rfl
  | k + 1 => by
    rw [ground.range_cons k]
    show (c + (0 + 1)) * ground.famFold Nat.mul 1 (fun j => c + (j + 1))
        ((List.range k).map (fun j => j + 1))
      = (c + 1) * ground.rise (c + 1 + 1) k
    rw [ground.famFold_map Nat.mul 1 (fun j => c + (j + 1))
        (fun j => j + 1) (List.range k),
      ground.famFold_congr_all Nat.mul 1 (fun j => c + (j + 1 + 1))
        (fun j => c + 1 + (j + 1))
        (fun j => by
          rw [Nat.add_right_comm c 1 (j + 1), Nat.add_assoc c (j + 1) 1])
        (List.range k),
      riseFold (c + 1) k,
      Nat.zero_add 1]

/-! The block products: the crossed product over two blocks, the
tail's own fold, and the join laws beneath them. -/

/-- The five-factor product's exchange. -/
private theorem mul5 (a b c d e : Nat) :
    a * b * (c * (d * e)) = a * c * (b * d * e) := by
  rw [ground.mulAssoc a b (c * (d * e)), ground.mulLeftComm b c (d * e),
    ← ground.mulAssoc a c (b * (d * e)), ground.mulAssoc b d e]

/-- The unit family's product. -/
private theorem famFold_ones : ∀ l : List Nat,
    ground.famFold Nat.mul 1 (fun _ => 1) l = 1
  | [] => rfl
  | _ :: t => by
    show 1 * ground.famFold Nat.mul 1 (fun _ => (1 : Nat)) t = 1
    rw [famFold_ones t, Nat.one_mul]

/-- The crossed gap product over two blocks: each member of the
first against the whole second. -/
private def crossP (X Y : List Nat) : Nat :=
  ground.famFold Nat.mul 1 (fun x => weyldim.gapHead x Y) X

/-- The block's gap fold against a stated member below it. -/
private def gapTail (y : Nat) (X : List Nat) : Nat :=
  ground.famFold Nat.mul 1 (fun x => x - y) X

/-- The gap product splits over a join, the crossed product reading
the pairs across the blocks. -/
private theorem gapProd_app (Y : List Nat) : ∀ X : List Nat,
    weyldim.gapProd (X ++ Y)
      = weyldim.gapProd X * (crossP X Y * weyldim.gapProd Y)
  | [] => by
    show weyldim.gapProd Y = 1 * (1 * weyldim.gapProd Y)
    rw [Nat.one_mul, Nat.one_mul]
  | x :: t => by
    show weyldim.gapProd (x :: (t ++ Y))
      = weyldim.gapProd (x :: t)
        * (weyldim.gapHead x Y * crossP t Y * weyldim.gapProd Y)
    rw [weyldim.gapProd_cons x (t ++ Y), weyldim.gapHead_append x t Y,
      gapProd_app Y t, weyldim.gapProd_cons x t]
    exact mul5 (weyldim.gapHead x t) (weyldim.gapHead x Y)
      (weyldim.gapProd t) (crossP t Y) (weyldim.gapProd Y)

/-- The crossed product splits over a join in the second block. -/
private theorem crossP_appendR (Y Z : List Nat) : ∀ X : List Nat,
    crossP X (Y ++ Z) = crossP X Y * crossP X Z
  | [] => (Nat.one_mul 1).symm
  | x :: t => by
    show weyldim.gapHead x (Y ++ Z) * crossP t (Y ++ Z)
      = weyldim.gapHead x Y * crossP t Y
        * (weyldim.gapHead x Z * crossP t Z)
    rw [weyldim.gapHead_append x Y Z, crossP_appendR Y Z t]
    exact ground.mulMulMulComm (weyldim.gapHead x Y) (weyldim.gapHead x Z)
      (crossP t Y) (crossP t Z)

/-- The crossed product read from the second block: each of its
members against the whole first. -/
private theorem crossP_swap (Y : List Nat) : ∀ X : List Nat,
    crossP X Y = ground.famFold Nat.mul 1 (fun y => gapTail y X) Y
  | [] => by
    show (1 : Nat) = ground.famFold Nat.mul 1 (fun _ => (1 : Nat)) Y
    rw [famFold_ones Y]
  | x :: t => by
    show ground.famFold Nat.mul 1 (fun y => x - y) Y * crossP t Y
      = ground.famFold Nat.mul 1
          (fun y => (x - y) * gapTail y t) Y
    rw [ground.famFold_mul_split (fun y => x - y) (fun y => gapTail y t) Y,
      crossP_swap Y t]

/-- The head's gap fold over a run: the rising product at the
head's own margin. -/
private theorem gapHead_run (c : Nat) : ∀ (k w x : Nat), k + w + c = x →
    weyldim.gapHead x (weyldim.descRun c k) = ground.rise (w + 1) k
  | 0, _, _, _ => rfl
  | k + 1, w, x, h => by
    have h1 : x - (k + c) = w + 1 := by
      rw [← h, Nat.add_right_comm k 1 w, Nat.add_right_comm (k + w) 1 c,
        Nat.add_right_comm k w c, Nat.add_assoc (k + c) w 1]
      exact ground.addSubSelfL (k + c) (w + 1)
    have h2 : k + (w + 1) + c = x := by
      rw [← h, Nat.add_right_comm k 1 w, Nat.add_assoc k w 1]
    show (x - (k + c)) * weyldim.gapHead x (weyldim.descRun c k)
      = (w + 1) * ground.rise (w + 1 + 1) k
    rw [h1, gapHead_run c k (w + 1) x h2]

/-- The block's gap fold over a run against a member below its
floor: the rising product at the member's own margin. -/
private theorem gapTail_run (c : Nat) : ∀ (k y w : Nat), y + w = c →
    gapTail y (weyldim.descRun c k) = ground.rise w k
  | 0, _, _, _ => rfl
  | k + 1, y, w, h => by
    have h1 : k + c - y = w + k := by
      rw [← h, Nat.add_left_comm k y w, ground.addSubSelfL y (k + w),
        Nat.add_comm k w]
    show (k + c - y) * gapTail y (weyldim.descRun c k) = ground.rise w (k + 1)
    rw [h1, gapTail_run c k y w h, rise_snoc w k, Nat.mul_comm (w + k)]

/-- The gap product is blind to a constant raise. -/
private theorem gapProd_shift (c : Nat) : ∀ l : List Nat,
    weyldim.gapProd (l.map (fun x => c + x)) = weyldim.gapProd l
  | [] => rfl
  | x :: t => by
    show weyldim.gapProd ((c + x) :: t.map (fun z => c + z))
      = weyldim.gapProd (x :: t)
    rw [weyldim.gapProd_cons (c + x) (t.map (fun z => c + z)),
      weyldim.gapProd_cons x t, gapProd_shift c t]
    refine congrArg (fun z => z * weyldim.gapProd t) ?_
    show ground.famFold Nat.mul 1 (fun y => c + x - y)
        (t.map (fun z => c + z))
      = ground.famFold Nat.mul 1 (fun y => x - y) t
    rw [ground.famFold_map Nat.mul 1 (fun y => c + x - y)
      (fun z => c + z) t]
    exact ground.famFold_congr_all Nat.mul 1 _ _ (fun z => by
      rw [Nat.add_comm c x, Nat.add_comm c z,
        ground.addSubAddR x z c]) t

/-- The run splits at a stated step: the raised run above the
run at the floor. -/
private theorem descRun_split (c y : Nat) : ∀ x : Nat,
    weyldim.descRun c (x + y)
      = weyldim.descRun (c + y) x ++ weyldim.descRun c y
  | 0 => by
    rw [Nat.zero_add]
    rfl
  | x + 1 => by
    rw [Nat.add_right_comm x 1 y]
    show (x + y + c) :: weyldim.descRun c (x + y)
      = (x + (c + y)) :: (weyldim.descRun (c + y) x
        ++ weyldim.descRun c y)
    rw [descRun_split c y x, Nat.add_assoc x y c, Nat.add_comm y c]


/-! The reversal kit: the key range's own reversal and the
reflected reindexing, the product fold's reversal the ground
general's. -/

/-- The key range's reversal is the range at the reflected key. -/
private theorem revRange : ∀ n : Nat,
    (List.range n).reverse = (List.range n).map (fun t => n - (t + 1))
  | 0 => rfl
  | n + 1 => by
    have hhead : n + 1 - (0 + 1) = n := ground.addSubAddR n 0 1
    have htail : (List.range n).map (fun x => n + 1 - (x + 1 + 1))
        = (List.range n).map (fun t => n - (t + 1)) :=
      ground.map_congr_all _ _ (fun x => ground.addSubAddR n (x + 1) 1)
        (List.range n)
    conv => lhs; rw [ground.range_succ n,
      ground.reverse_append (List.range n) [n], revRange n]
    rw [ground.range_cons n]
    show n :: (List.range n).map (fun t => n - (t + 1))
      = (n + 1 - (0 + 1)) :: ((List.range n).map (fun j => j + 1)).map
          (fun t => n + 1 - (t + 1))
    rw [ground.map_map (fun j => j + 1) (fun t => n + 1 - (t + 1))
        (List.range n),
      hhead, htail]

/-- The reflected reindexing: two families paired at the reflected
keys have one product over the range. -/
private theorem revFold (F G : Nat → Nat) (n : Nat)
    (h : ∀ t s : Nat, t + s + 1 = n → F t = G s) :
    ground.famFold Nat.mul 1 F (List.range n)
      = ground.famFold Nat.mul 1 G (List.range n) := by
  rw [← ground.famFold_rev Nat.mul 1 ground.mulAssoc Nat.one_mul
      Nat.mul_comm F (List.range n), revRange n,
    ground.famFold_map Nat.mul 1 F (fun t => n - (t + 1)) (List.range n)]
  refine ground.famFold_congr_members Nat.mul 1 _ _ (List.range n) ?_
  intro t ht
  have htn : t < n := ground.ltOfMem ht
  refine h (n - (t + 1)) t ?_
  rw [Nat.add_assoc (n - (t + 1)) t 1,
    Nat.add_comm (n - (t + 1)) (t + 1)]
  exact ground.natAddSubCancel htn

/-! The bottom block's reflection: the bottom rows and the bottom
word's rows read the word's total at reflected keys. -/

/-- The prefix and the row at one key join the family's total. -/
private theorem rowPrefix : ∀ (l : List Nat) (k : Nat), k < l.length →
    ground.prefixAt k l + ground.getAt 0 (places.rowList l) k
      = ground.sumNat l
  | [], k, h => absurd h (Nat.not_lt_zero k)
  | x :: t, 0, _ => Nat.zero_add (x + ground.sumNat t)
  | x :: t, k + 1, h => by
    show x + ground.prefixAt k t + ground.getAt 0 (places.rowList t) k
      = x + ground.sumNat t
    rw [Nat.add_assoc x (ground.prefixAt k t)
        (ground.getAt 0 (places.rowList t) k),
      rowPrefix t k (Nat.lt_of_succ_lt_succ h)]

/-- A prefix inside the first block ignores the join. -/
private theorem prefixAt_app : ∀ (k : Nat) (l r : List Nat),
    k ≤ l.length → ground.prefixAt k (l ++ r) = ground.prefixAt k l
  | 0, l, r, _ => by
    rw [ground.prefixAt_zero (l ++ r), ground.prefixAt_zero l]
  | k + 1, [], _, h => absurd h (Nat.not_succ_le_zero k)
  | k + 1, x :: l, r, h => by
    show x + ground.prefixAt k (l ++ r) = x + ground.prefixAt k l
    rw [prefixAt_app k l r (Nat.le_of_succ_le_succ h)]

/-- The bottom row at a key joins the bottom word's row at the
reflected key to the word's total. -/
private theorem bots_row_join (Q : List Nat) (t s : Nat)
    (h : t + s + 1 = Q.length) :
    ground.getAt 0 (bots Q) t + ground.getAt 0 (places.rowList Q) s
      = ground.sumNat Q := by
  have hts : t + 1 ≤ Q.length := by
    rw [← h]
    exact Nat.succ_le_succ (Nat.le_add_right t s)
  have hs : s < Q.length := by
    rw [← h]
    exact Nat.lt_succ_of_le (Nat.le_add_left s t)
  have hb : Q.reverse.length = Q.length := ground.length_reverse Q
  have hlen : (Q.reverse ++ [0]).length = Q.length + 1 := by
    rw [ground.length_append, hb]
    rfl
  have hsum : ground.sumNat (Q.reverse ++ [0]) = ground.sumNat Q := by
    rw [ground.sumNat_append, ground.sumNat_reverse]
    rfl
  have h1 := rowPrefix (Q.reverse ++ [0]) (t + 1)
    (by rw [hlen]; exact Nat.succ_lt_succ hts)
  rw [prefixAt_app (t + 1) Q.reverse [0] (by rw [hb]; exact hts),
    hsum, ground.getAt_tail 0 (places.rowList (Q.reverse ++ [0])) t] at h1
  have h2 := ground.prefix_reverse_join (t + 1) Q s
    (by rw [← h, Nat.add_right_comm t 1 s])
  have h3 := rowPrefix Q s hs
  have h4 : ground.getAt 0 (bots Q) t = ground.prefixAt s Q :=
    ground.addCancelL _ (h1.trans h2.symm)
  rw [h4]
  exact h3

/-! The dimension pair's shuffles: the eleven block factors'
regrouping at the two telescope pairs. -/

/-- The eleven factors' regrouping: the two telescope pairs
collected at the front. -/
private theorem blockProd (al X CF mu Y be al' TC BC be' CD : Nat) :
    al * (X * CF * (mu * (Y * be))) * (al' * (TC * (BC * (be' * CD))))
      = al * (X * TC * (Y * BC
          * (CF * (mu * be) * (al' * (be' * CD))))) := by
  rw [ground.mulAssoc X CF (mu * (Y * be)),
    ground.mulAssoc al (X * (CF * (mu * (Y * be))))
      (al' * (TC * (BC * (be' * CD)))),
    ground.mulLeftComm al' TC (BC * (be' * CD)),
    ground.mulMulMulComm X (CF * (mu * (Y * be))) TC (al' * (BC * (be' * CD))),
    ground.mulLeftComm mu Y be,
    ground.mulLeftComm CF Y (mu * be),
    ground.mulLeftComm al' BC (be' * CD),
    ground.mulMulMulComm Y (CF * (mu * be)) BC (al' * (be' * CD))]

/-- The seven constant factors' regrouping. -/
private theorem tailShuffle (al CF mu be al' be' CD : Nat) :
    al * (CF * (mu * be) * (al' * (be' * CD)))
      = al' * (CD * (mu * be') * (al * (be * CF))) := by
  conv => lhs; rw [
    ground.mulAssoc CF (mu * be) (al' * (be' * CD)),
    ground.mulAssoc mu be (al' * (be' * CD)),
    ground.mulLeftComm be al' (be' * CD),
    ground.mulLeftComm mu al' (be * (be' * CD)),
    ground.mulLeftComm CF al' (mu * (be * (be' * CD))),
    ground.mulLeftComm mu be (be' * CD),
    ground.mulLeftComm CF be (mu * (be' * CD)),
    ground.mulLeftComm mu be' CD,
    ground.mulLeftComm CF be' (mu * CD),
    ground.mulLeftComm CF mu CD]
  conv => rhs; rw [
    ground.mulAssoc CD (mu * be') (al * (be * CF)),
    ground.mulAssoc mu be' (al * (be * CF)),
    ground.mulLeftComm be' al (be * CF),
    ground.mulLeftComm mu al (be' * (be * CF)),
    ground.mulLeftComm CD al (mu * (be' * (be * CF))),
    ground.mulLeftComm al' al (CD * (mu * (be' * (be * CF)))),
    ground.mulLeftComm be' be CF,
    ground.mulLeftComm mu be (be' * CF),
    ground.mulLeftComm CD be (mu * (be' * CF)),
    ground.mulLeftComm mu be' CF,
    ground.mulLeftComm CD be' (mu * CF),
    ground.mulLeftComm CD mu CF,
    Nat.mul_comm CD CF]

/-- The cross-multiplied regrouping at the two telescope
identities. -/
private theorem dimShuffle (al X CF mu Y be al' TC BC be' CD
    X' TF Y' BF : Nat) (hX : X * TC = X' * TF) (hY : Y * BC = Y' * BF) :
    al * (X * CF * (mu * (Y * be))) * (al' * (TC * (BC * (be' * CD))))
      = al' * (X' * CD * (mu * (Y' * be')))
        * (al * (TF * (BF * (be * CF)))) := by
  rw [blockProd al X CF mu Y be al' TC BC be' CD,
    blockProd al' X' CD mu Y' be' al TF BF be CF, hX, hY,
    ground.mulLeftComm al (X' * TF)
      (Y' * BF * (CF * (mu * be) * (al' * (be' * CD)))),
    ground.mulLeftComm al (Y' * BF) (CF * (mu * be) * (al' * (be' * CD))),
    ground.mulLeftComm al' (X' * TF)
      (Y' * BF * (CD * (mu * be') * (al * (be * CF)))),
    ground.mulLeftComm al' (Y' * BF) (CD * (mu * be') * (al * (be * CF))),
    tailShuffle al CF mu be al' be' CD]

/-- The per-key telescope: the display's window against the unit's,
the two rising products crossed. -/
private theorem topKey (p g u : Nat) :
    ground.rise (p + g + 1) u * ground.rise (g + 1) p
      = ground.rise (g + 1) u * ground.rise (g + u + 1) p := by
  rw [Nat.add_comm p g, Nat.add_right_comm g p 1,
    Nat.add_right_comm g u 1]
  exact ground.rise_rect (g + 1) p u

/-! The dimension classes' joins: the block entries' reads at the
runs' floors. -/

/-- The top block's entry against the run's floor. -/
private theorem topJoin (u p g b m : Nat) :
    u + (p + g) + (1 + b + m)
      = m + p + (g + (1 + (u + b))) := by
  conv => lhs; rw [
    ← Nat.add_assoc (u + (p + g)) (1 + b) m,
    ← Nat.add_assoc (u + (p + g)) 1 b,
    ← Nat.add_assoc u p g,
    Nat.add_right_comm (u + p + g + 1) b m,
    Nat.add_comm u p,
    Nat.add_right_comm p u g,
    Nat.add_right_comm (p + g) u 1,
    Nat.add_right_comm (p + g + 1) u m,
    Nat.add_right_comm (p + g) 1 m,
    Nat.add_right_comm p g m,
    Nat.add_comm p m]
  conv => rhs; rw [
    ← Nat.add_assoc (m + p) g (1 + (u + b)),
    ← Nat.add_assoc (m + p + g) 1 (u + b),
    ← Nat.add_assoc (m + p + g + 1) u b]

/-- The unit display's top entry against the run's floor. -/
private theorem topJoinU (u g b : Nat) :
    u + g + (1 + b)
      = g + (1 + (u + b)) := by
  conv => lhs; rw [
    ← Nat.add_assoc (u + g) 1 b,
    Nat.add_comm u g,
    Nat.add_right_comm g u 1]
  conv => rhs; rw [
    ← Nat.add_assoc g 1 (u + b),
    ← Nat.add_assoc (g + 1) u b]

/-- The bottom block's entry against the run's floor. -/
private theorem botJoin (B s r t : Nat) :
    B + (s + 1) + (r + t + 1)
      = 1 + (t + 1 + s) + (B + r) := by
  conv => lhs; rw [
    ← Nat.add_assoc (B + (s + 1)) (r + t) 1,
    ← Nat.add_assoc (B + (s + 1)) r t,
    ← Nat.add_assoc B s 1,
    Nat.add_right_comm (B + s + 1) r t,
    Nat.add_right_comm (B + s + 1 + t) r 1,
    Nat.add_comm B s,
    Nat.add_right_comm s B 1,
    Nat.add_right_comm (s + 1) B t,
    Nat.add_right_comm (s + 1 + t) B 1,
    Nat.add_comm s 1,
    Nat.add_right_comm 1 s t,
    Nat.add_right_comm (1 + t) s 1]
  conv => rhs; rw [
    ← Nat.add_assoc (1 + (t + 1 + s)) B r,
    ← Nat.add_assoc 1 (t + 1) s,
    ← Nat.add_assoc 1 t 1]

/-- The unit display's bottom entry against the run's floor. -/
private theorem botJoinU (s t : Nat) :
    s + 1 + (t + 1)
      = 1 + (t + 1 + s) := by
  conv => lhs; rw [
    ← Nat.add_assoc (s + 1) t 1,
    Nat.add_comm s 1,
    Nat.add_right_comm 1 s t,
    Nat.add_right_comm (1 + t) s 1]
  conv => rhs; rw [
    ← Nat.add_assoc 1 (t + 1) s,
    ← Nat.add_assoc 1 t 1]

/-- The cross class's gap at the two blocks' entries. -/
private theorem crossJoin (B s p r g t u : Nat) :
    B + (s + 1) + (p + r + (g + t + u + 1))
      = B + r + p + (g + (1 + (u + (t + 1 + s)))) := by
  conv => lhs; rw [
    ← Nat.add_assoc (B + (s + 1)) (p + r) (g + t + u + 1),
    ← Nat.add_assoc (B + (s + 1) + (p + r)) (g + t + u) 1,
    ← Nat.add_assoc (B + (s + 1) + (p + r)) (g + t) u,
    ← Nat.add_assoc (B + (s + 1) + (p + r)) g t,
    ← Nat.add_assoc (B + (s + 1)) p r,
    ← Nat.add_assoc B s 1,
    Nat.add_right_comm B s 1,
    Nat.add_right_comm (B + 1) s p,
    Nat.add_right_comm (B + 1 + p) s r,
    Nat.add_right_comm (B + 1 + p + r) s g,
    Nat.add_right_comm (B + 1 + p + r + g) s t,
    Nat.add_right_comm (B + 1 + p + r + g + t) s u,
    Nat.add_right_comm (B + 1 + p + r + g + t + u) s 1,
    Nat.add_right_comm (B + 1 + p + r + g) t u,
    Nat.add_right_comm B 1 p,
    Nat.add_right_comm (B + p) 1 r,
    Nat.add_right_comm (B + p + r) 1 g,
    Nat.add_right_comm B p r]
  conv => rhs; rw [
    ← Nat.add_assoc (B + r + p) g (1 + (u + (t + 1 + s))),
    ← Nat.add_assoc (B + r + p + g) 1 (u + (t + 1 + s)),
    ← Nat.add_assoc (B + r + p + g + 1) u (t + 1 + s),
    ← Nat.add_assoc (B + r + p + g + 1 + u) (t + 1) s,
    ← Nat.add_assoc (B + r + p + g + 1 + u) t 1]

/-- The unit display's cross gap at the two runs' entries. -/
private theorem crossJoinU (s g t u : Nat) :
    s + 1 + (g + t + u + 1)
      = g + (1 + (u + (t + 1 + s))) := by
  conv => lhs; rw [
    ← Nat.add_assoc (s + 1) (g + t + u) 1,
    ← Nat.add_assoc (s + 1) (g + t) u,
    ← Nat.add_assoc (s + 1) g t,
    Nat.add_comm s 1,
    Nat.add_right_comm 1 s g,
    Nat.add_right_comm (1 + g) s t,
    Nat.add_right_comm (1 + g + t) s u,
    Nat.add_right_comm (1 + g + t + u) s 1,
    Nat.add_right_comm (1 + g) t u,
    Nat.add_comm 1 g]
  conv => rhs; rw [
    ← Nat.add_assoc g 1 (u + (t + 1 + s)),
    ← Nat.add_assoc (g + 1) u (t + 1 + s),
    ← Nat.add_assoc (g + 1 + u) (t + 1) s,
    ← Nat.add_assoc (g + 1 + u) t 1]

/-! The class evaluations: the member's display against the unit
display's, one identity per factor class. -/

/-- A list's product fold reads as the fold over its key range. -/
private theorem famFold_list_range (F : Nat → Nat) (X : List Nat) (n : Nat)
    (h : X.length = n) :
    ground.famFold Nat.mul 1 F X
      = ground.famFold Nat.mul 1 (fun i => F (ground.getAt 0 X i))
        (List.range n) :=
  (ground.famFold_getAt Nat.mul 1 F 0 X n h).symm

/-- The crossed product as a fold over the first block's keys. -/
private theorem crossP_range (X Y : List Nat) (n : Nat) (h : X.length = n) :
    crossP X Y = ground.famFold Nat.mul 1
      (fun i => weyldim.gapHead (ground.getAt 0 X i) Y) (List.range n) :=
  famFold_list_range (fun x => weyldim.gapHead x Y) X n h

/-- The head's gap fold as a fold over the tail's keys. -/
private theorem gapHead_range (x : Nat) (Y : List Nat) (n : Nat)
    (h : Y.length = n) :
    weyldim.gapHead x Y = ground.famFold Nat.mul 1
      (fun t => x - ground.getAt 0 Y t) (List.range n) :=
  famFold_list_range (fun y => x - y) Y n h

/-- The run's entry at a key: the key's complement above the
floor. -/
private theorem getAt_run (c k i g : Nat) (h : i < k) (hg : i + 1 + g = k) :
    ground.getAt 0 (weyldim.descRun c k) i = g + c := by
  refine ground.addCancelL i (ground.addCancelR 1 ?_)
  rw [weyldim.getAt_descRun c k i h, ← hg, Nat.add_right_comm i 1 g,
    Nat.add_right_comm (i + g) 1 c, Nat.add_assoc i g c]

/-- A stated join reads the gap. -/
private theorem sub_of_add {x y z : Nat} (h : y + z = x) : x - y = z := by
  rw [← h, ground.addSubSelfL]

/-- The reflected key at a stated join. -/
private theorem sub_of_join {t s n : Nat} (h : t + s + 1 = n) :
    n - (t + 1) = s := by
  rw [← h, Nat.add_right_comm t s 1, ground.addSubSelfL]

/-- Two paired folds over one key range agree at their pointwise
products. -/
private theorem famFold_pair_congr (f g f' g' : Nat → Nat) (n : Nat)
    (h : ∀ i : Nat, i < n → f i * g i = f' i * g' i) :
    ground.famFold Nat.mul 1 f (List.range n)
        * ground.famFold Nat.mul 1 g (List.range n)
      = ground.famFold Nat.mul 1 f' (List.range n)
        * ground.famFold Nat.mul 1 g' (List.range n) := by
  rw [← ground.famFold_mul_split f g (List.range n),
    ← ground.famFold_mul_split f' g' (List.range n)]
  refine ground.famFold_congr_members Nat.mul 1 _ _ (List.range n) ?_
  intro i hi
  exact h i (ground.ltOfMem hi)

/-- A fold at the reflected keys. -/
private theorem revIdx (F : Nat → Nat) (n : Nat) :
    ground.famFold Nat.mul 1 F (List.range n)
      = ground.famFold Nat.mul 1 (fun t => F (n - (t + 1)))
        (List.range n) :=
  (revFold (fun t => F (n - (t + 1))) F n
    (fun _ _ hj => congrArg F (sub_of_join hj))).symm

/-- Two paired folds agree at their products across the reflected
keys. -/
private theorem famFold_pair_rev (f g f' g' : Nat → Nat) (n : Nat)
    (h : ∀ t s : Nat, t + s + 1 = n → f t * g s = f' t * g' s) :
    ground.famFold Nat.mul 1 f (List.range n)
        * ground.famFold Nat.mul 1 g (List.range n)
      = ground.famFold Nat.mul 1 f' (List.range n)
        * ground.famFold Nat.mul 1 g' (List.range n) := by
  rw [revIdx g n, revIdx g' n]
  refine famFold_pair_congr f (fun t => g (n - (t + 1))) f'
    (fun t => g' (n - (t + 1))) n ?_
  intro t ht
  refine h t (n - (t + 1)) ?_
  rw [Nat.add_right_comm t (n - (t + 1)) 1]
  exact ground.natAddSubCancel ht

/-- The word-against-run class at the top word: the display's
windows against the unit display's, the binomial denominators
against the numerators. -/
private theorem topClass (Rw : List Nat) (a b m u : Nat)
    (ha : Rw.length = a) :
    crossP (List.zipWith (fun x y => x + y) (Rw.map (fun x => m + x))
          (weyldim.descRun (1 + (u + b)) a))
        (weyldim.descRun (1 + b + m) u)
      * ground.famFold Nat.mul 1 (fun i =>
          ground.famFold Nat.mul 1 (fun j => a - (i + 1) + (j + 1))
            (List.range (ground.getAt 0 Rw i))) (List.range a)
    = crossP (weyldim.descRun (1 + (u + b)) a) (weyldim.descRun (1 + b) u)
      * ground.famFold Nat.mul 1 (fun i =>
          ground.famFold Nat.mul 1 (fun j => a - (i + 1) + u + (j + 1))
            (List.range (ground.getAt 0 Rw i))) (List.range a) := by
  have hmap : (Rw.map (fun x => m + x)).length = a := by
    rw [ground.length_map, ha]
  have hlen : (List.zipWith (fun x y => x + y) (Rw.map (fun x => m + x))
      (weyldim.descRun (1 + (u + b)) a)).length = a :=
    ground.length_zipWith _ _ _ a hmap (weyldim.length_descRun _ a)
  rw [crossP_range _ _ a hlen,
    crossP_range _ _ a (weyldim.length_descRun (1 + (u + b)) a)]
  refine famFold_pair_congr _ _ _ _ a ?_
  intro i hia
  have hg : i + 1 + (a - (i + 1)) = a := ground.natAddSubCancel hia
  have hU1 : ground.getAt 0 (weyldim.descRun (1 + (u + b)) a) i
      = a - (i + 1) + (1 + (u + b)) :=
    getAt_run (1 + (u + b)) a i (a - (i + 1)) hia hg
  have hT : ground.getAt 0 (List.zipWith (fun x y => x + y)
        (Rw.map (fun x => m + x)) (weyldim.descRun (1 + (u + b)) a)) i
      = m + ground.getAt 0 Rw i + (a - (i + 1) + (1 + (u + b))) := by
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y)
        (Rw.map (fun x => m + x)) (weyldim.descRun (1 + (u + b)) a) i
        (by rw [hmap]; exact hia)
        (by rw [weyldim.length_descRun]; exact hia),
      ground.getAt_map 0 0 (fun x => m + x) Rw i (by rw [ha]; exact hia),
      hU1]
  rw [hT, hU1,
    gapHead_run (1 + b + m) u (ground.getAt 0 Rw i + (a - (i + 1)))
      (m + ground.getAt 0 Rw i + (a - (i + 1) + (1 + (u + b))))
      (topJoin u (ground.getAt 0 Rw i) (a - (i + 1)) b m),
    gapHead_run (1 + b) u (a - (i + 1))
      (a - (i + 1) + (1 + (u + b))) (topJoinU u (a - (i + 1)) b),
    riseFold (a - (i + 1)) (ground.getAt 0 Rw i),
    riseFold (a - (i + 1) + u) (ground.getAt 0 Rw i)]
  exact topKey (ground.getAt 0 Rw i) (a - (i + 1)) u

/-- The word-against-run class at the bottom word: the reflected
windows, the binomial denominators against the numerators. -/
private theorem botClass (Bt Rq : List Nat) (b m u : Nat)
    (hB : Bt.length = b)
    (hjoin : ∀ t s : Nat, t + s + 1 = b →
      ground.getAt 0 Bt t + ground.getAt 0 Rq s = m) :
    crossP (weyldim.descRun (1 + b + m) u)
        (List.zipWith (fun x y => x + y) Bt (weyldim.descRun 1 b))
      * ground.famFold Nat.mul 1 (fun s =>
          ground.famFold Nat.mul 1 (fun j => b - (s + 1) + (j + 1))
            (List.range (ground.getAt 0 Rq s))) (List.range b)
    = crossP (weyldim.descRun (1 + b) u) (weyldim.descRun 1 b)
      * ground.famFold Nat.mul 1 (fun s =>
          ground.famFold Nat.mul 1 (fun j => b - (s + 1) + u + (j + 1))
            (List.range (ground.getAt 0 Rq s))) (List.range b) := by
  have hlen : (List.zipWith (fun x y => x + y) Bt
      (weyldim.descRun 1 b)).length = b :=
    ground.length_zipWith _ _ _ b hB (weyldim.length_descRun 1 b)
  rw [crossP_swap (List.zipWith (fun x y => x + y) Bt (weyldim.descRun 1 b))
      (weyldim.descRun (1 + b + m) u),
    crossP_swap (weyldim.descRun 1 b) (weyldim.descRun (1 + b) u),
    famFold_list_range (fun y => gapTail y (weyldim.descRun (1 + b + m) u))
      (List.zipWith (fun x y => x + y) Bt (weyldim.descRun 1 b)) b hlen,
    famFold_list_range (fun y => gapTail y (weyldim.descRun (1 + b) u))
      (weyldim.descRun 1 b) b (weyldim.length_descRun 1 b)]
  refine famFold_pair_rev _ _ _ _ b ?_
  intro t s hj
  have htb : t < b := by
    rw [← hj]
    exact Nat.lt_succ_of_le (Nat.le_add_right t s)
  have hts : t + 1 + s = b := by
    rw [← hj, Nat.add_right_comm t s 1]
  have hst : s + t + 1 = b := by
    rw [← hj, Nat.add_comm s t]
  have hbr := hjoin t s hj
  have hsub : b - (s + 1) = t := sub_of_join hst
  have hU3 : ground.getAt 0 (weyldim.descRun 1 b) t = s + 1 :=
    getAt_run 1 b t s htb hts
  have hBd : ground.getAt 0 (List.zipWith (fun x y => x + y) Bt
        (weyldim.descRun 1 b)) t
      = ground.getAt 0 Bt t + (s + 1) := by
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) Bt
        (weyldim.descRun 1 b) t (by rw [hB]; exact htb)
        (by rw [weyldim.length_descRun]; exact htb),
      hU3]
  rw [hBd, hU3, hsub,
    gapTail_run (1 + b + m) u (ground.getAt 0 Bt t + (s + 1))
      (ground.getAt 0 Rq s + t + 1)
      (by
        rw [← hbr, ← hts]
        exact botJoin (ground.getAt 0 Bt t) s (ground.getAt 0 Rq s) t),
    gapTail_run (1 + b) u (s + 1) (t + 1)
      (by
        rw [← hts]
        exact botJoinU s t),
    riseFold t (ground.getAt 0 Rq s),
    riseFold (t + u) (ground.getAt 0 Rq s)]
  exact topKey (ground.getAt 0 Rq s) t u

/-- The cross class at the two words: one linear factor per key
pair, the position gaps joined. -/
private theorem crossClass (Rw Bt Rq : List Nat) (a b m u : Nat)
    (ha : Rw.length = a) (hB : Bt.length = b)
    (hjoin : ∀ t s : Nat, t + s + 1 = b →
      ground.getAt 0 Bt t + ground.getAt 0 Rq s = m) :
    crossP (List.zipWith (fun x y => x + y) (Rw.map (fun x => m + x))
          (weyldim.descRun (1 + (u + b)) a))
        (List.zipWith (fun x y => x + y) Bt (weyldim.descRun 1 b))
      = ground.famFold Nat.mul 1 (fun i =>
          ground.famFold Nat.mul 1 (fun s =>
            ground.getAt 0 Rw i + ground.getAt 0 Rq s
              + (a - (i + 1) + (b - (s + 1)) + u + 1))
            (List.range b)) (List.range a) := by
  have hmap : (Rw.map (fun x => m + x)).length = a := by
    rw [ground.length_map, ha]
  have hlenT : (List.zipWith (fun x y => x + y) (Rw.map (fun x => m + x))
      (weyldim.descRun (1 + (u + b)) a)).length = a :=
    ground.length_zipWith _ _ _ a hmap (weyldim.length_descRun _ a)
  have hlenB : (List.zipWith (fun x y => x + y) Bt
      (weyldim.descRun 1 b)).length = b :=
    ground.length_zipWith _ _ _ b hB (weyldim.length_descRun 1 b)
  rw [crossP_range _ _ a hlenT]
  refine ground.famFold_congr_members Nat.mul 1 _ _ (List.range a) ?_
  intro i hi
  have hia : i < a := ground.ltOfMem hi
  have hg : i + 1 + (a - (i + 1)) = a := ground.natAddSubCancel hia
  have hU1 : ground.getAt 0 (weyldim.descRun (1 + (u + b)) a) i
      = a - (i + 1) + (1 + (u + b)) :=
    getAt_run (1 + (u + b)) a i (a - (i + 1)) hia hg
  have hT : ground.getAt 0 (List.zipWith (fun x y => x + y)
        (Rw.map (fun x => m + x)) (weyldim.descRun (1 + (u + b)) a)) i
      = m + ground.getAt 0 Rw i + (a - (i + 1) + (1 + (u + b))) := by
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y)
        (Rw.map (fun x => m + x)) (weyldim.descRun (1 + (u + b)) a) i
        (by rw [hmap]; exact hia)
        (by rw [weyldim.length_descRun]; exact hia),
      ground.getAt_map 0 0 (fun x => m + x) Rw i (by rw [ha]; exact hia),
      hU1]
  rw [hT, gapHead_range _ _ b hlenB]
  refine revFold _ _ b ?_
  intro t s hj
  have htb : t < b := by
    rw [← hj]
    exact Nat.lt_succ_of_le (Nat.le_add_right t s)
  have hts : t + 1 + s = b := by
    rw [← hj, Nat.add_right_comm t s 1]
  have hst : s + t + 1 = b := by
    rw [← hj, Nat.add_comm s t]
  have hbr := hjoin t s hj
  have hsub : b - (s + 1) = t := sub_of_join hst
  have hU3 : ground.getAt 0 (weyldim.descRun 1 b) t = s + 1 :=
    getAt_run 1 b t s htb hts
  have hBd : ground.getAt 0 (List.zipWith (fun x y => x + y) Bt
        (weyldim.descRun 1 b)) t
      = ground.getAt 0 Bt t + (s + 1) := by
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) Bt
        (weyldim.descRun 1 b) t (by rw [hB]; exact htb)
        (by rw [weyldim.length_descRun]; exact htb),
      hU3]
  rw [hBd, hsub]
  refine sub_of_add ?_
  rw [← hbr, ← hts]
  exact crossJoin (ground.getAt 0 Bt t) s (ground.getAt 0 Rw i)
    (ground.getAt 0 Rq s) (a - (i + 1)) t u

/-- The cross class at the unit display: the position gaps
alone. -/
private theorem crossClassU (a b u : Nat) :
    crossP (weyldim.descRun (1 + (u + b)) a) (weyldim.descRun 1 b)
      = ground.famFold Nat.mul 1 (fun i =>
          ground.famFold Nat.mul 1 (fun s =>
            a - (i + 1) + (b - (s + 1)) + u + 1) (List.range b))
        (List.range a) := by
  rw [crossP_range _ _ a (weyldim.length_descRun (1 + (u + b)) a)]
  refine ground.famFold_congr_members Nat.mul 1 _ _ (List.range a) ?_
  intro i hi
  have hia : i < a := ground.ltOfMem hi
  have hg : i + 1 + (a - (i + 1)) = a := ground.natAddSubCancel hia
  rw [getAt_run (1 + (u + b)) a i (a - (i + 1)) hia hg,
    gapHead_range _ _ b (weyldim.length_descRun 1 b)]
  refine revFold _ _ b ?_
  intro t s hj
  have htb : t < b := by
    rw [← hj]
    exact Nat.lt_succ_of_le (Nat.le_add_right t s)
  have hts : t + 1 + s = b := by
    rw [← hj, Nat.add_right_comm t s 1]
  have hst : s + t + 1 = b := by
    rw [← hj, Nat.add_comm s t]
  have hsub : b - (s + 1) = t := sub_of_join hst
  rw [getAt_run 1 b t s htb hts, hsub]
  refine sub_of_add ?_
  rw [← hts]
  exact crossJoinU s (a - (i + 1)) t u

/-! The member's display in blocks, the run block at the bottom
word's total between the two words' own. -/

/-- The top block's gap product is the shadow's: the display's
constant raise leaves the gaps. -/
private theorem gapProd_top (Rw : List Nat) (a b m u : Nat) :
    weyldim.gapProd (List.zipWith (fun x y => x + y)
        (Rw.map (fun x => m + x)) (weyldim.descRun (1 + (u + b)) a))
      = weyldim.gapProd (List.zipWith (fun x y => x + y) Rw
          (weyldim.descRun 1 a)) := by
  have h1 : weyldim.descRun (1 + (u + b)) a
      = (weyldim.descRun 1 a).map (fun x => u + b + x) := by
    rw [weyldim.map_descRun (u + b) 1 a, Nat.add_comm (u + b) 1]
  rw [h1, ground.zipWith_add_mapL m Rw
      ((weyldim.descRun 1 a).map (fun x => u + b + x)),
    ground.zipWith_add_mapR (u + b) Rw (weyldim.descRun 1 a),
    gapProd_shift m _, gapProd_shift (u + b) _]

/-- The gap product over three blocks. -/
private theorem gapProd_split (X Y Z : List Nat) :
    weyldim.gapProd (X ++ (Y ++ Z))
      = weyldim.gapProd X * (crossP X Y * crossP X Z
        * (weyldim.gapProd Y * (crossP Y Z * weyldim.gapProd Z))) := by
  rw [gapProd_app (Y ++ Z) X, gapProd_app Z Y, crossP_appendR Y Z X]

/-- The member's display in blocks: the top word's rows against the
leading run, the run block at the bottom word's total, and the
bottom rows against the trailing run. -/
private theorem display_member (P Q : List Nat) (k : Nat) :
    places.display (member P Q (P.length + Q.length + k + 1))
      = List.zipWith (fun x y => x + y)
          ((places.rowList P).map (fun x => ground.sumNat Q + x))
          (weyldim.descRun (1 + (k + 1 + Q.length)) P.length)
        ++ (weyldim.descRun (1 + Q.length + ground.sumNat Q) (k + 1)
          ++ List.zipWith (fun x y => x + y) (bots Q)
            (weyldim.descRun 1 Q.length)) := by
  have hd : P.length + Q.length + k + 1
      = P.length + (k + 1 + Q.length) := by
    rw [Nat.add_assoc (P.length + Q.length) k 1,
      Nat.add_assoc P.length Q.length (k + 1),
      Nat.add_comm Q.length (k + 1)]
  rw [weylchar.display_zip (member P Q (P.length + Q.length + k + 1)),
    member_length P Q k, rowList_member P Q k,
    weyldim.unitDisp_descRun (P.length + Q.length + k + 1), hd,
    descRun_split 1 (k + 1 + Q.length) P.length,
    descRun_split 1 Q.length (k + 1),
    ground.zipWith_append (fun x y => x + y)
      ((places.rowList P).map (fun x => ground.sumNat Q + x))
      (List.replicate (k + 1) (ground.sumNat Q) ++ bots Q)
      (weyldim.descRun (1 + (k + 1 + Q.length)) P.length)
      (weyldim.descRun (1 + Q.length) (k + 1) ++ weyldim.descRun 1 Q.length)
      (by rw [ground.length_map, places.length_rowList,
        weyldim.length_descRun]),
    ground.zipWith_append (fun x y => x + y)
      (List.replicate (k + 1) (ground.sumNat Q)) (bots Q)
      (weyldim.descRun (1 + Q.length) (k + 1))
      (weyldim.descRun 1 Q.length)
      (by rw [ground.length_replicate, weyldim.length_descRun]),
    weyldim.zipWith_descRun (ground.sumNat Q) (1 + Q.length) (k + 1)]

/-! The two members' counts and the cross-multiplied agreement. -/

/-- The dimension pair's first member at a residue count. -/
private def numVal (P Q : List Nat) (k : Nat) : Nat :=
  weyldim.gapProd (List.zipWith (fun x y => x + y) (places.rowList P)
      (weyldim.descRun 1 P.length))
    * weyldim.gapProd (List.zipWith (fun x y => x + y) (bots Q)
      (weyldim.descRun 1 Q.length))
    * ground.famFold Nat.mul 1 (fun i =>
        ground.famFold Nat.mul 1
          (fun j => P.length - (i + 1) + (k + 1) + (j + 1))
          (List.range (ground.getAt 0 (places.rowList P) i)))
        (List.range P.length)
    * ground.famFold Nat.mul 1 (fun t =>
        ground.famFold Nat.mul 1
          (fun j => Q.length - (t + 1) + (k + 1) + (j + 1))
          (List.range (ground.getAt 0 (places.rowList Q) t)))
        (List.range Q.length)
    * ground.famFold Nat.mul 1 (fun i =>
        ground.famFold Nat.mul 1 (fun t =>
          ground.getAt 0 (places.rowList P) i
            + ground.getAt 0 (places.rowList Q) t
            + (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1))
          (List.range Q.length))
        (List.range P.length)

/-- The dimension pair's second member at a residue count. -/
private def denVal (P Q : List Nat) (k : Nat) : Nat :=
  weyldim.gapProd (weyldim.descRun 1 P.length)
    * weyldim.gapProd (weyldim.descRun 1 Q.length)
    * ground.famFold Nat.mul 1 (fun i =>
        ground.famFold Nat.mul 1 (fun j => P.length - (i + 1) + (j + 1))
          (List.range (ground.getAt 0 (places.rowList P) i)))
        (List.range P.length)
    * ground.famFold Nat.mul 1 (fun t =>
        ground.famFold Nat.mul 1 (fun j => Q.length - (t + 1) + (j + 1))
          (List.range (ground.getAt 0 (places.rowList Q) t)))
        (List.range Q.length)
    * ground.famFold Nat.mul 1 (fun i =>
        ground.famFold Nat.mul 1 (fun t =>
          P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1)
          (List.range Q.length))
        (List.range P.length)

/-- The five factors' regrouping at the first member. -/
private theorem mulNum (Aw Bd TF BF CF : Nat) :
    Aw * Bd * TF * BF * CF = Aw * (TF * (BF * (Bd * CF))) := by
  conv => lhs; rw [
    ground.mulRightComm Aw Bd TF,
    ground.mulRightComm (Aw * TF) Bd BF]
  conv => rhs; rw [
    ← ground.mulAssoc Aw TF (BF * (Bd * CF)),
    ← ground.mulAssoc (Aw * TF) BF (Bd * CF),
    ← ground.mulAssoc (Aw * TF * BF) Bd CF]

/-- The cross-multiplied agreement of the two counts with the
member's gap product against the unit display's. -/
private theorem dimMaster (P Q : List Nat) (k : Nat) :
    weyldim.gapProd (places.display (member P Q
          (P.length + Q.length + k + 1)))
        * denVal P Q k
      = weyldim.gapProd (weyldim.descRun 1
          (P.length + Q.length + k + 1)) * numVal P Q k := by
  have hd : P.length + Q.length + k + 1
      = P.length + (k + 1 + Q.length) := by
    rw [Nat.add_assoc (P.length + Q.length) k 1,
      Nat.add_assoc P.length Q.length (k + 1),
      Nat.add_comm Q.length (k + 1)]
  have hdisp : weyldim.gapProd (places.display (member P Q
        (P.length + Q.length + k + 1)))
      = weyldim.gapProd (List.zipWith (fun x y => x + y) (places.rowList P)
          (weyldim.descRun 1 P.length))
        * (crossP (List.zipWith (fun x y => x + y)
              ((places.rowList P).map (fun x => ground.sumNat Q + x))
              (weyldim.descRun (1 + (k + 1 + Q.length)) P.length))
            (weyldim.descRun (1 + Q.length + ground.sumNat Q) (k + 1))
          * ground.famFold Nat.mul 1 (fun i =>
              ground.famFold Nat.mul 1 (fun t =>
                ground.getAt 0 (places.rowList P) i
                  + ground.getAt 0 (places.rowList Q) t
                  + (P.length - (i + 1) + (Q.length - (t + 1))
                    + (k + 1) + 1))
                (List.range Q.length))
              (List.range P.length)
          * (weyldim.gapProd (weyldim.descRun (1 + Q.length) (k + 1))
            * (crossP (weyldim.descRun (1 + Q.length + ground.sumNat Q)
                  (k + 1))
                (List.zipWith (fun x y => x + y) (bots Q)
                  (weyldim.descRun 1 Q.length))
              * weyldim.gapProd (List.zipWith (fun x y => x + y) (bots Q)
                  (weyldim.descRun 1 Q.length))))) := by
    rw [display_member P Q k, gapProd_split,
      gapProd_top (places.rowList P) P.length Q.length
        (ground.sumNat Q) (k + 1),
      weyldim.gapProd_descRun (1 + Q.length + ground.sumNat Q)
        (1 + Q.length) (k + 1),
      crossClass (places.rowList P) (bots Q) (places.rowList Q)
        P.length Q.length (ground.sumNat Q) (k + 1)
        (places.length_rowList P) (bots_length Q)
        (fun t s hj => bots_row_join Q t s hj)]
  have hunit : weyldim.gapProd (weyldim.descRun 1
        (P.length + Q.length + k + 1))
      = weyldim.gapProd (weyldim.descRun 1 P.length)
        * (crossP (weyldim.descRun (1 + (k + 1 + Q.length)) P.length)
            (weyldim.descRun (1 + Q.length) (k + 1))
          * ground.famFold Nat.mul 1 (fun i =>
              ground.famFold Nat.mul 1 (fun t =>
                P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1)
                (List.range Q.length))
              (List.range P.length)
          * (weyldim.gapProd (weyldim.descRun (1 + Q.length) (k + 1))
            * (crossP (weyldim.descRun (1 + Q.length) (k + 1))
                (weyldim.descRun 1 Q.length)
              * weyldim.gapProd (weyldim.descRun 1 Q.length)))) := by
    rw [hd, descRun_split 1 (k + 1 + Q.length) P.length,
      descRun_split 1 Q.length (k + 1), gapProd_split,
      weyldim.gapProd_descRun (1 + (k + 1 + Q.length)) 1 P.length,
      crossClassU P.length Q.length (k + 1)]
  rw [hdisp, hunit, numVal, denVal, mulNum, mulNum]
  exact dimShuffle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (topClass (places.rowList P) P.length Q.length (ground.sumNat Q)
      (k + 1) (places.length_rowList P))
    (botClass (bots Q) (places.rowList Q) Q.length (ground.sumNat Q)
      (k + 1) (bots_length Q) (fun t s hj => bots_row_join Q t s hj))

/-! The evaluation's reads: each linear factor at the residue
count, the two members' own values, and the agreement. -/

/-- The top word's linear factor reads its binomial numerator. -/
private theorem topEval (a b i g k j : Nat) (hg : i + 1 + g = a) :
    b + i + 1 + (g + (k + 1) + (j + 1)) = j + 1 + (a + b + k + 1) := by
  rw [← hg]
  conv => lhs; rw [
    ← Nat.add_assoc (b + i + 1) (g + (k + 1)) (j + 1),
    ← Nat.add_assoc (b + i + 1 + (g + (k + 1))) j 1,
    ← Nat.add_assoc (b + i + 1) g (k + 1),
    ← Nat.add_assoc (b + i + 1 + g) k 1,
    Nat.add_right_comm (b + i + 1 + g) k 1,
    Nat.add_right_comm (b + i + 1 + g + 1) k j,
    Nat.add_comm b i,
    Nat.add_right_comm i b 1,
    Nat.add_right_comm (i + 1) b g,
    Nat.add_right_comm (i + 1 + g) b 1,
    Nat.add_right_comm (i + 1 + g + 1) b j,
    Nat.add_right_comm (i + 1) g 1,
    Nat.add_right_comm (i + 1 + 1) g j,
    Nat.add_right_comm (i + 1) 1 j,
    Nat.add_comm i 1,
    Nat.add_right_comm 1 i j,
    Nat.add_comm 1 j]
  conv => rhs; rw [
    ← Nat.add_assoc (j + 1) (i + 1 + g + b + k) 1,
    ← Nat.add_assoc (j + 1) (i + 1 + g + b) k,
    ← Nat.add_assoc (j + 1) (i + 1 + g) b,
    ← Nat.add_assoc (j + 1) (i + 1) g,
    ← Nat.add_assoc (j + 1) i 1]

/-- The bottom word's linear factor reads its binomial
numerator. -/
private theorem botEval (a b s t k j : Nat) (ht : s + 1 + t = b) :
    s + a + 1 + (t + (k + 1) + (j + 1)) = j + 1 + (a + b + k + 1) := by
  rw [← ht]
  conv => lhs; rw [
    ← Nat.add_assoc (s + a + 1) (t + (k + 1)) (j + 1),
    ← Nat.add_assoc (s + a + 1 + (t + (k + 1))) j 1,
    ← Nat.add_assoc (s + a + 1) t (k + 1),
    ← Nat.add_assoc (s + a + 1 + t) k 1,
    Nat.add_right_comm (s + a + 1 + t) k 1,
    Nat.add_right_comm (s + a + 1 + t + 1) k j,
    Nat.add_right_comm (s + a + 1) t 1,
    Nat.add_right_comm (s + a + 1 + 1) t j,
    Nat.add_right_comm (s + a + 1) 1 j,
    Nat.add_comm s a,
    Nat.add_right_comm a s 1,
    Nat.add_right_comm (a + 1) s j,
    Nat.add_comm a 1,
    Nat.add_right_comm 1 a j,
    Nat.add_comm 1 j]
  conv => rhs; rw [
    ← Nat.add_assoc (j + 1) (a + (s + 1 + t) + k) 1,
    ← Nat.add_assoc (j + 1) (a + (s + 1 + t)) k,
    ← Nat.add_assoc (j + 1) a (s + 1 + t),
    ← Nat.add_assoc (j + 1 + a) (s + 1) t,
    ← Nat.add_assoc (j + 1 + a) s 1]

/-- The cross class's linear factor reads its first member. -/
private theorem crossEval (a b i s g t k p r : Nat) (hg : i + 1 + g = a)
    (ht : s + 1 + t = b) :
    i + 1 + s + (p + r + (g + t + (k + 1) + 1))
      = p + r + (a + b + k + 1) := by
  rw [← hg, ← ht]
  conv => lhs; rw [
    ← Nat.add_assoc (i + 1 + s) (p + r) (g + t + (k + 1) + 1),
    ← Nat.add_assoc (i + 1 + s + (p + r)) (g + t + (k + 1)) 1,
    ← Nat.add_assoc (i + 1 + s + (p + r)) (g + t) (k + 1),
    ← Nat.add_assoc (i + 1 + s + (p + r) + (g + t)) k 1,
    ← Nat.add_assoc (i + 1 + s + (p + r)) g t,
    ← Nat.add_assoc (i + 1 + s) p r,
    Nat.add_right_comm (i + 1 + s + p + r + g + t) k 1,
    Nat.add_right_comm (i + 1 + s + p + r + g) t 1,
    Nat.add_right_comm (i + 1) s p,
    Nat.add_right_comm (i + 1 + p) s r,
    Nat.add_right_comm (i + 1 + p + r) s g,
    Nat.add_right_comm i 1 p,
    Nat.add_right_comm (i + p) 1 r,
    Nat.add_comm i p,
    Nat.add_right_comm p i r]
  conv => rhs; rw [
    ← Nat.add_assoc (p + r) (i + 1 + g + (s + 1 + t) + k) 1,
    ← Nat.add_assoc (p + r) (i + 1 + g + (s + 1 + t)) k,
    ← Nat.add_assoc (p + r) (i + 1 + g) (s + 1 + t),
    ← Nat.add_assoc (p + r + (i + 1 + g)) (s + 1) t,
    ← Nat.add_assoc (p + r + (i + 1 + g)) s 1,
    ← Nat.add_assoc (p + r) (i + 1) g,
    ← Nat.add_assoc (p + r) i 1]

/-- The cross class's position gap at the unit display. -/
private theorem crossEvalU (a b i s g t k : Nat) (hg : i + 1 + g = a)
    (ht : s + 1 + t = b) :
    i + 1 + s + (g + t + (k + 1) + 1) = 0 + (a + b + k + 1) := by
  rw [Nat.zero_add, ← hg, ← ht]
  conv => lhs; rw [
    ← Nat.add_assoc (i + 1 + s) (g + t + (k + 1)) 1,
    ← Nat.add_assoc (i + 1 + s) (g + t) (k + 1),
    ← Nat.add_assoc (i + 1 + s + (g + t)) k 1,
    ← Nat.add_assoc (i + 1 + s) g t,
    Nat.add_right_comm (i + 1 + s + g + t) k 1,
    Nat.add_right_comm (i + 1 + s + g) t 1,
    Nat.add_right_comm (i + 1) s g]
  conv => rhs; rw [
    ← Nat.add_assoc (i + 1 + g) (s + 1) t,
    ← Nat.add_assoc (i + 1 + g) s 1]

/-- The first member's evaluation at a residue count. -/
private theorem numRead (P Q : List Nat) (k : Nat) :
    (poly.eval (dimNum P Q)
        (ground.BPair.ofNat (P.length + Q.length + k + 1))).oneValue
      (ground.BPair.ofNat (numVal P Q k)) := by
  have hbase := poly.constRead
    (weyldim.gapProd (List.zipWith (fun x y => x + y) (places.rowList P)
        (weyldim.descRun 1 P.length))
      * weyldim.gapProd (List.zipWith (fun x y => x + y) (bots Q)
        (weyldim.descRun 1 Q.length)))
    (P.length + Q.length + k + 1)
  have htop := poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 (places.rowList P) i)).foldl
        (fun acc2 j => poly.mul acc2
          [⟨ground.posOfSucc (j + 1),
            ground.posOfSucc (Q.length + i + 1)⟩,
           ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 (places.rowList P) i)).foldl
        (fun n2 j => n2 * (P.length - (i + 1) + (k + 1) + (j + 1))) n)
    (fun x => x < P.length)
    (fun acc n i hi hacc =>
      poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
        (fun (acc2 : poly.Poly) (j : Nat) => poly.mul acc2
          [⟨ground.posOfSucc (j + 1),
            ground.posOfSucc (Q.length + i + 1)⟩,
           ground.BPair.ofNat 1])
        (fun (n2 j : Nat) => n2 * (P.length - (i + 1) + (k + 1) + (j + 1)))
        (fun x => x < ground.getAt 0 (places.rowList P) i)
        (fun acc2 n2 j _ h2 =>
          poly.eval_mulStep (poly.linRead (j + 1) (Q.length + i + 1) 1
            (P.length - (i + 1) + (k + 1) + (j + 1))
            (P.length + Q.length + k + 1)
            (by
              rw [Nat.mul_one]
              exact topEval P.length Q.length i (P.length - (i + 1)) k j
                (ground.natAddSubCancel hi))) acc2 n2 h2)
        (List.range (ground.getAt 0 (places.rowList P) i))
        (fun x hx => ground.ltOfMemRange hx) acc n hacc)
    (List.range P.length) (fun x hx => ground.ltOfMemRange hx) _ _ hbase
  have hbot := poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
    (fun (acc : poly.Poly) (t : Nat) =>
      (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
        (fun acc2 j => poly.mul acc2
          [⟨ground.posOfSucc (j + 1),
            ground.posOfSucc (t + P.length + 1)⟩,
           ground.BPair.ofNat 1]) acc)
    (fun (n t : Nat) =>
      (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
        (fun n2 j => n2 * (Q.length - (t + 1) + (k + 1) + (j + 1))) n)
    (fun x => x < Q.length)
    (fun acc n t ht hacc =>
      poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
        (fun (acc2 : poly.Poly) (j : Nat) => poly.mul acc2
          [⟨ground.posOfSucc (j + 1),
            ground.posOfSucc (t + P.length + 1)⟩,
           ground.BPair.ofNat 1])
        (fun (n2 j : Nat) => n2 * (Q.length - (t + 1) + (k + 1) + (j + 1)))
        (fun x => x < ground.getAt 0 (places.rowList Q) t)
        (fun acc2 n2 j _ h2 =>
          poly.eval_mulStep (poly.linRead (j + 1) (t + P.length + 1) 1
            (Q.length - (t + 1) + (k + 1) + (j + 1))
            (P.length + Q.length + k + 1)
            (by
              rw [Nat.mul_one]
              exact botEval P.length Q.length t (Q.length - (t + 1)) k j
                (ground.natAddSubCancel ht))) acc2 n2 h2)
        (List.range (ground.getAt 0 (places.rowList Q) t))
        (fun x hx => ground.ltOfMemRange hx) acc n hacc)
    (List.range Q.length) (fun x hx => ground.ltOfMemRange hx) _ _ htop
  have hcross := poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range Q.length).foldl (fun acc2 t => poly.mul acc2
        [⟨ground.posOfSucc (ground.getAt 0 (places.rowList P) i
            + ground.getAt 0 (places.rowList Q) t),
          ground.posOfSucc (i + 1 + t)⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range Q.length).foldl (fun n2 t => n2 *
        (ground.getAt 0 (places.rowList P) i
          + ground.getAt 0 (places.rowList Q) t
          + (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1))) n)
    (fun x => x < P.length)
    (fun acc n i hi hacc =>
      poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
        (fun (acc2 : poly.Poly) (t : Nat) => poly.mul acc2
          [⟨ground.posOfSucc (ground.getAt 0 (places.rowList P) i
              + ground.getAt 0 (places.rowList Q) t),
            ground.posOfSucc (i + 1 + t)⟩,
           ground.BPair.ofNat 1])
        (fun (n2 t : Nat) => n2 *
          (ground.getAt 0 (places.rowList P) i
            + ground.getAt 0 (places.rowList Q) t
            + (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1)))
        (fun x => x < Q.length)
        (fun acc2 n2 t ht h2 =>
          poly.eval_mulStep (poly.linRead
            (ground.getAt 0 (places.rowList P) i
              + ground.getAt 0 (places.rowList Q) t)
            (i + 1 + t) 1
            (ground.getAt 0 (places.rowList P) i
              + ground.getAt 0 (places.rowList Q) t
              + (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1))
            (P.length + Q.length + k + 1)
            (by
              rw [Nat.mul_one]
              exact crossEval P.length Q.length i t (P.length - (i + 1))
                (Q.length - (t + 1)) k (ground.getAt 0 (places.rowList P) i)
                (ground.getAt 0 (places.rowList Q) t)
                (ground.natAddSubCancel hi) (ground.natAddSubCancel ht)))
            acc2 n2 h2)
        (List.range Q.length) (fun x hx => ground.ltOfMemRange hx) acc n hacc)
    (List.range P.length) (fun x hx => ground.ltOfMemRange hx) _ _ hbot
  have hval : (List.range P.length).foldl
      (fun (n i : Nat) => (List.range Q.length).foldl (fun n2 t => n2 *
        (ground.getAt 0 (places.rowList P) i
          + ground.getAt 0 (places.rowList Q) t
          + (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1))) n)
      ((List.range Q.length).foldl
        (fun (n t : Nat) =>
          (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
            (fun n2 j => n2 * (Q.length - (t + 1) + (k + 1) + (j + 1))) n)
        ((List.range P.length).foldl
          (fun (n i : Nat) =>
            (List.range (ground.getAt 0 (places.rowList P) i)).foldl
              (fun n2 j => n2 * (P.length - (i + 1) + (k + 1) + (j + 1))) n)
          (weyldim.gapProd (List.zipWith (fun x y => x + y)
              (places.rowList P) (weyldim.descRun 1 P.length))
            * weyldim.gapProd (List.zipWith (fun x y => x + y) (bots Q)
              (weyldim.descRun 1 Q.length)))))
      = numVal P Q k := by
    rw [ground.foldl_nest (fun i j => P.length - (i + 1) + (k + 1) + (j + 1))
        (fun i => List.range (ground.getAt 0 (places.rowList P) i))
        (List.range P.length) _,
      ground.foldl_nest (fun t j => Q.length - (t + 1) + (k + 1) + (j + 1))
        (fun t => List.range (ground.getAt 0 (places.rowList Q) t))
        (List.range Q.length) _,
      ground.foldl_nest (fun i t => ground.getAt 0 (places.rowList P) i
          + ground.getAt 0 (places.rowList Q) t
          + (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1))
        (fun _ => List.range Q.length) (List.range P.length) _,
      numVal]
  rw [← hval]
  exact hcross

/-- The second member's evaluation at a residue count. -/
private theorem denRead (P Q : List Nat) (k : Nat) :
    (poly.eval (dimDen P Q)
        (ground.BPair.ofNat (P.length + Q.length + k + 1))).oneValue
      (ground.BPair.ofNat (denVal P Q k)) := by
  have hbase := poly.constRead
    (weyldim.gapProd (weyldim.descRun 1 P.length)
      * weyldim.gapProd (weyldim.descRun 1 Q.length)
      * (List.range P.length).foldl (fun n i =>
          (List.range (ground.getAt 0 (places.rowList P) i)).foldl
            (fun n2 j => n2 * (P.length - (i + 1) + (j + 1))) n) 1
      * (List.range Q.length).foldl (fun n t =>
          (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
            (fun n2 j => n2 * (Q.length - (t + 1) + (j + 1))) n) 1)
    (P.length + Q.length + k + 1)
  have hcross := poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range Q.length).foldl (fun acc2 t => poly.mul acc2
        [⟨ground.posOfSucc 0, ground.posOfSucc (i + 1 + t)⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range Q.length).foldl (fun n2 t => n2 *
        (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1)) n)
    (fun x => x < P.length)
    (fun acc n i hi hacc =>
      poly.eval_fold (ground.BPair.ofNat (P.length + Q.length + k + 1))
        (fun (acc2 : poly.Poly) (t : Nat) => poly.mul acc2
          [⟨ground.posOfSucc 0, ground.posOfSucc (i + 1 + t)⟩,
           ground.BPair.ofNat 1])
        (fun (n2 t : Nat) => n2 *
          (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1))
        (fun x => x < Q.length)
        (fun acc2 n2 t ht h2 =>
          poly.eval_mulStep (poly.linRead 0 (i + 1 + t) 1
            (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1)
            (P.length + Q.length + k + 1)
            (by
              rw [Nat.mul_one]
              exact crossEvalU P.length Q.length i t (P.length - (i + 1))
                (Q.length - (t + 1)) k (ground.natAddSubCancel hi)
                (ground.natAddSubCancel ht))) acc2 n2 h2)
        (List.range Q.length) (fun x hx => ground.ltOfMemRange hx) acc n hacc)
    (List.range P.length) (fun x hx => ground.ltOfMemRange hx) _ _ hbase
  have hval : (List.range P.length).foldl
      (fun (n i : Nat) => (List.range Q.length).foldl (fun n2 t => n2 *
        (P.length - (i + 1) + (Q.length - (t + 1)) + (k + 1) + 1)) n)
      (weyldim.gapProd (weyldim.descRun 1 P.length)
        * weyldim.gapProd (weyldim.descRun 1 Q.length)
        * (List.range P.length).foldl (fun n i =>
            (List.range (ground.getAt 0 (places.rowList P) i)).foldl
              (fun n2 j => n2 * (P.length - (i + 1) + (j + 1))) n) 1
        * (List.range Q.length).foldl (fun n t =>
            (List.range (ground.getAt 0 (places.rowList Q) t)).foldl
              (fun n2 j => n2 * (Q.length - (t + 1) + (j + 1))) n) 1)
      = denVal P Q k := by
    rw [ground.foldl_nest (fun i j => P.length - (i + 1) + (j + 1))
        (fun i => List.range (ground.getAt 0 (places.rowList P) i))
        (List.range P.length) 1,
      ground.foldl_nest (fun t j => Q.length - (t + 1) + (j + 1))
        (fun t => List.range (ground.getAt 0 (places.rowList Q) t))
        (List.range Q.length) 1,
      ground.foldl_nest (fun i t => P.length - (i + 1) + (Q.length - (t + 1))
          + (k + 1) + 1)
        (fun _ => List.range Q.length) (List.range P.length) _,
      Nat.one_mul, Nat.one_mul, denVal]
  rw [← hval]
  exact hcross

/-- The dimension's cross-multiplied read: the member's dimension
against the second member is the first. -/
private theorem dimKey (P Q : List Nat) (k : Nat) :
    weyldim.dimOf (member P Q (P.length + Q.length + k + 1))
        * denVal P Q k
      = numVal P Q k := by
  have hread : weyldim.dimOf (member P Q (P.length + Q.length + k + 1))
      * weyldim.gapProd (places.display (List.replicate
          (member P Q (P.length + Q.length + k + 1)).length 0))
      = weyldim.gapProd (places.display (member P Q
          (P.length + Q.length + k + 1))) :=
    weyldim.readAll (member P Q (P.length + Q.length + k + 1))
  have hpos : 0 < weyldim.gapProd (places.display (List.replicate
      (member P Q (P.length + Q.length + k + 1)).length 0)) :=
    weyldim.gapProdU_pos (member P Q (P.length + Q.length + k + 1))
  rw [member_length P Q k] at hread hpos
  have hu : places.display (List.replicate (P.length + Q.length + k + 1) 0)
      = weyldim.descRun 1 (P.length + Q.length + k + 1) :=
    weyldim.unitDisp_descRun (P.length + Q.length + k + 1)
  rw [hu] at hread hpos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← dimMaster P Q k, ← hread,
    ground.mulLeftComm (weyldim.gapProd (weyldim.descRun 1
        (P.length + Q.length + k + 1)))
      (weyldim.dimOf (member P Q (P.length + Q.length + k + 1)))
      (denVal P Q k),
    ground.mulAssoc (weyldim.dimOf (member P Q
        (P.length + Q.length + k + 1)))
      (weyldim.gapProd (weyldim.descRun 1 (P.length + Q.length + k + 1)))
      (denVal P Q k)]

/-- The dimension pair's agreement: at every residue count from the
floor the first member's value is the member's dimension against
the second member's. -/
theorem dimPair_eval : ∀ (P Q : List Nat) (d : Nat),
    P.length + Q.length + 1 ≤ d →
    (poly.eval (dimNum P Q) (ground.BPair.ofNat d)).oneValue
      (ground.BPair.ofNat (weyldim.dimOf (member P Q d))
        * poly.eval (dimDen P Q) (ground.BPair.ofNat d)) := by
  intro P Q d h
  have hk : ∃ k : Nat, d = P.length + Q.length + k + 1 :=
    ⟨d - (P.length + Q.length + 1), by
      rw [Nat.add_right_comm (P.length + Q.length)
        (d - (P.length + Q.length + 1)) 1]
      exact (ground.natAddSubCancel h).symm⟩
  cases hk with
  | intro k hk =>
    subst hk
    refine ground.BPair.oneValue_trans (numRead P Q k) ?_
    rw [← dimKey P Q k]
    refine ground.BPair.oneValue_trans
      (ground.BPair.ofNat_mul
        (weyldim.dimOf (member P Q (P.length + Q.length + k + 1)))
        (denVal P Q k)) ?_
    exact ground.BPair.mul_congr (ground.BPair.oneValue_refl _)
      (ground.BPair.oneValue_symm (denRead P Q k))

/-! `lem:rankstable`(ii)'s diagonal tier: `cor:steinberg` at the
adjoint on the same member's beta-set display. -/

/-- The consecutive unit-gap count of a display. -/
def clearGaps : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: t => (if x = y + 1 then 1 else 0) + clearGaps (y :: t)

/-- The occupied-key count of a word. -/
def suppCount : List Nat → Nat
  | [] => 0
  | x :: t => (if 0 < x then 1 else 0) + suppCount t

/-- The display at an occupied tail: the head is the tail's own
head raised by the head occupancy and one. -/
private theorem display_cons (x : Nat) : ∀ t : Shape, 0 < t.length →
    places.display (x :: t)
      = (ground.getAt 0 (places.display t) 0 + x + 1) :: places.display t
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: u, _ => by
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · show (places.display (x :: a :: u)).length
        = (places.display (a :: u)).length + 1
      rw [places.length_display, places.length_display]
      rfl
    · intro i hi
      rw [places.length_display] at hi
      cases i with
      | zero =>
        rw [places.getAt_display (x :: a :: u) 0 hi]
        show x + ground.sumNat (a :: u) + ((a :: u).length + 1)
          = ground.getAt 0 (places.display (a :: u)) 0 + x + 1
        rw [places.getAt_display (a :: u) 0 (Nat.succ_pos u.length)]
        show x + ground.sumNat (a :: u) + ((a :: u).length + 1)
          = ground.sumNat (a :: u) + (a :: u).length + x + 1
        rw [Nat.add_comm x (ground.sumNat (a :: u)),
          ← Nat.add_assoc (ground.sumNat (a :: u) + x) (a :: u).length 1,
          Nat.add_right_comm (ground.sumNat (a :: u)) x (a :: u).length]
      | succ j =>
        have hj : j < (a :: u).length := Nat.lt_of_succ_lt_succ hi
        rw [places.getAt_display (x :: a :: u) (j + 1) hi]
        show ground.getAt 0 (places.rowList (a :: u)) j
            + ((a :: u).length + 1 - (j + 1))
          = ground.getAt 0 (places.display (a :: u)) j
        rw [Nat.succ_sub_succ (a :: u).length j,
          places.getAt_display (a :: u) j hj]

/-- The display's unit gaps over a trailing vacancy: one at every
vacant key of the word, the occupied keys the complement. -/
private theorem clearGaps_snoc : ∀ (l : List Nat) (z : Nat),
    clearGaps (places.display (l ++ [z])) + suppCount l = l.length
  | [], _ => rfl
  | x :: l, z => by
    have hne : 0 < (l ++ [z]).length := by
      rw [ground.length_append]
      show 0 < l.length + 1
      exact Nat.succ_pos l.length
    have hd : 0 < (places.display (l ++ [z])).length := by
      rw [places.length_display]
      exact hne
    have hrec := clearGaps_snoc l z
    cases hdd : places.display (l ++ [z]) with
    | nil =>
      rw [hdd] at hd
      exact absurd hd (Nat.lt_irrefl 0)
    | cons b t =>
      rw [hdd] at hrec
      have hind : (if b + x + 1 = b + 1 then 1 else 0)
          + (if 0 < x then 1 else 0) = 1 := by
        cases x with
        | zero =>
          rw [if_pos (show b + 0 + 1 = b + 1 from rfl),
            if_neg (Nat.lt_irrefl 0)]
        | succ x0 =>
          rw [if_neg (show ¬ b + (x0 + 1) + 1 = b + 1 from by
              intro he
              rw [Nat.add_assoc b (x0 + 1) 1] at he
              exact Nat.noConfusion (Nat.succ.inj (ground.addCancelL b he))),
            if_pos (Nat.succ_pos x0)]
      show clearGaps (places.display (x :: (l ++ [z])))
          + ((if 0 < x then 1 else 0) + suppCount l) = l.length + 1
      rw [display_cons x (l ++ [z]) hne, hdd]
      show (if b + x + 1 = b + 1 then 1 else 0) + clearGaps (b :: t)
          + ((if 0 < x then 1 else 0) + suppCount l) = l.length + 1
      rw [Nat.add_add_add_comm (if b + x + 1 = b + 1 then 1 else 0)
          (clearGaps (b :: t)) (if 0 < x then 1 else 0) (suppCount l),
        hind, hrec]
      exact Nat.add_comm 1 l.length

/-- The occupied-key count splits over a join. -/
private theorem suppCount_append : ∀ xs ys : List Nat,
    suppCount (xs ++ ys) = suppCount xs + suppCount ys
  | [], ys => by
    show suppCount ys = 0 + suppCount ys
    rw [Nat.zero_add]
  | x :: t, ys => by
    show (if 0 < x then 1 else 0) + suppCount (t ++ ys)
      = (if 0 < x then 1 else 0) + suppCount t + suppCount ys
    rw [suppCount_append t ys,
      Nat.add_assoc (if 0 < x then 1 else 0) (suppCount t) (suppCount ys)]

/-- A vacant block carries no occupied key. -/
private theorem suppCount_replicate_zero : ∀ k : Nat,
    suppCount (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by
    show (if 0 < 0 then 1 else 0) + suppCount (List.replicate k 0) = 0
    rw [if_neg (Nat.lt_irrefl 0), suppCount_replicate_zero k]

/-- The occupied-key count is reflection-free. -/
private theorem suppCount_reverse : ∀ l : List Nat,
    suppCount l.reverse = suppCount l
  | [] => rfl
  | x :: t => by
    rw [ground.reverse_cons x t, suppCount_append t.reverse [x],
      suppCount_reverse t]
    show suppCount t + ((if 0 < x then 1 else 0) + 0)
      = (if 0 < x then 1 else 0) + suppCount t
    rw [Nat.add_zero]
    exact Nat.add_comm (suppCount t) _

/-- The unit-gap keys of a display, in key order. -/
private def gapKeys : List Nat → List Nat
  | [] => []
  | [_] => []
  | x :: y :: t =>
    (if x = y + 1 then [0] else [])
      ++ (gapKeys (y :: t)).map (fun k => k + 1)

/-- The gap-key list's length is the unit-gap count. -/
private theorem length_gapKeys : ∀ y : List Nat,
    (gapKeys y).length = clearGaps y
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
    show ((if x = y + 1 then [0] else [])
        ++ (gapKeys (y :: t)).map (fun k => k + 1)).length
      = (if x = y + 1 then 1 else 0) + clearGaps (y :: t)
    rw [ground.length_append, ground.length_map, length_gapKeys (y :: t)]
    by_cases hxy : x = y + 1
    · rw [if_pos hxy, if_pos hxy]
      rfl
    · rw [if_neg hxy, if_neg hxy]
      rfl

/-- The raised family counts its own raised key. -/
private theorem countOf_map_succ (k : Nat) : ∀ L : List Nat,
    ground.countOf (k + 1) (L.map (fun j => j + 1))
      = ground.countOf k L :=
  fun L => ground.countOf_map_inj (fun j => j + 1) k L
    (fun _ _ he => Nat.succ.inj he)

/-- The raised family carries no vacant key. -/
private theorem countOf_map_succ_zero : ∀ L : List Nat,
    ground.countOf 0 (L.map (fun j => j + 1)) = 0 :=
  fun L => ground.countOf_map_none (fun j => j + 1) 0 L
    (fun _ _ he => Nat.noConfusion he)

/-- The gap-key list's first key: the head's own gap. -/
private theorem countOf_gapKeys_zero (x y : Nat) (t : List Nat) :
    ground.countOf 0 (gapKeys (x :: y :: t))
      = if x = y + 1 then 1 else 0 := by
  show ground.countOf 0 ((if x = y + 1 then [0] else [])
      ++ (gapKeys (y :: t)).map (fun k => k + 1))
    = if x = y + 1 then 1 else 0
  rw [ground.countOf_append 0 (if x = y + 1 then [0] else [])
      ((gapKeys (y :: t)).map (fun k => k + 1)),
    countOf_map_succ_zero (gapKeys (y :: t)), Nat.add_zero]
  by_cases hxy : x = y + 1
  · rw [if_pos hxy, if_pos hxy]
    show (if (0 : Nat) = 0 then 1 else 0) + 0 = 1
    rw [if_pos rfl]
  · rw [if_neg hxy, if_neg hxy]
    rfl

/-- The gap-key list's further keys are the tail's own, raised. -/
private theorem countOf_gapKeys_succ (x y : Nat) (t : List Nat) (k : Nat) :
    ground.countOf (k + 1) (gapKeys (x :: y :: t))
      = ground.countOf k (gapKeys (y :: t)) := by
  show ground.countOf (k + 1) ((if x = y + 1 then [0] else [])
      ++ (gapKeys (y :: t)).map (fun j => j + 1))
    = ground.countOf k (gapKeys (y :: t))
  rw [ground.countOf_append (k + 1) (if x = y + 1 then [0] else [])
      ((gapKeys (y :: t)).map (fun j => j + 1)),
    countOf_map_succ k (gapKeys (y :: t))]
  by_cases hxy : x = y + 1
  · rw [if_pos hxy]
    show (if k + 1 = 0 then 1 else 0) + 0
        + ground.countOf k (gapKeys (y :: t))
      = ground.countOf k (gapKeys (y :: t))
    rw [if_neg (fun he => Nat.noConfusion he)]
    exact Nat.zero_add _
  · rw [if_neg hxy]
    show 0 + ground.countOf k (gapKeys (y :: t))
      = ground.countOf k (gapKeys (y :: t))
    rw [Nat.zero_add]

/-- A unit gap of a display is a gap key, counted once. -/
private theorem countOf_gapKeys : ∀ (y : List Nat) (k : Nat),
    k + 1 < y.length →
    ground.getAt 0 y k = ground.getAt 0 y (k + 1) + 1 →
    ground.countOf k (gapKeys y) = 1
  | [], k, hk, _ => absurd hk (Nat.not_lt_zero (k + 1))
  | [_], k, hk, _ =>
    absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero k)
  | x :: y :: t, 0, _, hgap => by
    rw [countOf_gapKeys_zero x y t,
      if_pos (show x = y + 1 from hgap)]
  | x :: y :: t, k + 1, hk, hgap => by
    rw [countOf_gapKeys_succ x y t k]
    exact countOf_gapKeys (y :: t) k (Nat.lt_of_succ_lt_succ hk) hgap

/-- A gap key names its own unit gap. -/
private theorem gapKeys_read : ∀ (y : List Nat) (k : Nat),
    0 < ground.countOf k (gapKeys y) →
    k + 1 < y.length
      ∧ ground.getAt 0 y k = ground.getAt 0 y (k + 1) + 1
  | [], k, h => absurd h (Nat.lt_irrefl 0)
  | [_], k, h => absurd h (Nat.lt_irrefl 0)
  | x :: y :: t, 0, h => by
    rw [countOf_gapKeys_zero x y t] at h
    by_cases hxy : x = y + 1
    · exact ⟨Nat.succ_lt_succ (Nat.succ_pos t.length), hxy⟩
    · rw [if_neg hxy] at h
      exact absurd h (Nat.lt_irrefl 0)
  | x :: y :: t, k + 1, h => by
    rw [countOf_gapKeys_succ x y t k] at h
    obtain ⟨hlt, hg⟩ := gapKeys_read (y :: t) k h
    exact ⟨Nat.succ_lt_succ hlt, hg⟩

/-- The diagonal target's display: the full column raises every
display member by one. -/
private theorem display_diag (d : Nat) (s : Shape) (hs : s.length = d) :
    places.display (ground.bumpAt (d - 1) s)
      = (places.display s).map (fun x => x + 1) := by
  rw [← hs]
  exact places.display_full s

/-- The identity permutation's tie at the diagonal target is the
unit-monomial content, read at the residue's count. -/
private theorem tieDiagId (d : Nat) (s : Shape) (hs : s.length = d) :
    weylchar.multAtGap (adjchar.multRead d)
      (places.display (ground.bumpAt (d - 1) s))
      (places.expo (places.display s) (List.range d)) = d - 1 := by
  have hdl : (places.display s).length = d := by
    rw [places.length_display, hs]
  have hexpo : places.expo (places.display s) (List.range d)
      = places.display s :=
    ground.range_map_getAt 0 d (places.display s) hdl
  have htie : ground.tieGap
      (places.display (ground.bumpAt (d - 1) s))
      (places.expo (places.display s) (List.range d))
      = some (List.replicate d 1) := by
    rw [hexpo, display_diag d s hs]
    refine ground.tieGap_make _ _ _ ?_ ?_ ?_
    · rw [ground.length_replicate, ground.length_map, hdl]
    · rw [ground.length_map]
    · intro i hi
      rw [ground.length_map, hdl] at hi
      rw [ground.getAt_replicate 0 1 d i hi,
        ground.getAt_map 0 0 (fun x => x + 1) (places.display s) i
          (by rw [hdl]; exact hi)]
      exact Nat.add_comm 1 _
  show (match ground.tieGap
      (places.display (ground.bumpAt (d - 1) s))
      (places.expo (places.display s) (List.range d)) with
    | some nu => adjchar.multRead d nu
    | none => 0) = d - 1
  rw [htie]
  exact adjchar.multRead_ones d

/-- An adjacent exchange at a unit gap contributes one: the tie is
the letter-pair move at the exchanged places. -/
private theorem tieDiagSwap (d : Nat) (s : Shape) (hs : s.length = d)
    (k : Nat) (hk : k + 1 < d)
    (hgap : ground.getAt 0 (places.display s) k
      = ground.getAt 0 (places.display s) (k + 1) + 1) :
    weylchar.multAtGap (adjchar.multRead d)
      (places.display (ground.bumpAt (d - 1) s))
      (places.expo (places.display s)
        (ground.adjSwap k (List.range d))) = 1 := by
  obtain ⟨w, hw⟩ := Nat.le.dest (show k + 2 ≤ d from hk)
  have hkw : k + (w + 2) = d := by
    rw [Nat.add_comm w 2, ← Nat.add_assoc k 2 w]
    exact hw
  have hdl : (places.display s).length = d := by
    rw [places.length_display, hs]
  have hrep : (List.replicate k (1 : Nat)).length = k :=
    ground.length_replicate 1 k
  have hMl : (List.replicate k 1 ++ 2 :: 0 :: List.replicate w 1
      : List Nat).length = d := by
    rw [ground.length_append, hrep]
    show k + ((List.replicate w (1 : Nat)).length + 1 + 1) = d
    rw [ground.length_replicate]
    exact hkw
  have htie : ground.tieGap
      (places.display (ground.bumpAt (d - 1) s))
      (places.expo (places.display s)
        (ground.adjSwap k (List.range d)))
      = some (List.replicate k 1 ++ 2 :: 0 :: List.replicate w 1) := by
    rw [display_diag d s hs]
    refine ground.tieGap_make _ _ _ ?_ ?_ ?_
    · rw [hMl, ground.length_map, hdl]
    · show ((ground.adjSwap k (List.range d)).map
          (ground.getAt 0 (places.display s))).length
        = ((places.display s).map (fun x => x + 1)).length
      rw [ground.length_map, ground.length_adjSwap, ground.length_range,
        ground.length_map, hdl]
    · intro i hi
      rw [ground.length_map, hdl] at hi
      rw [places.getAt_expo (places.display s)
          (ground.adjSwap k (List.range d)) i
          (by rw [ground.length_adjSwap, ground.length_range]; exact hi),
        ground.getAt_adjSwap_range d k i hk hi,
        ground.getAt_swapWit k w i (by rw [hkw]; exact hi),
        ground.getAt_map 0 0 (fun x => x + 1) (places.display s) i
          (by rw [hdl]; exact hi)]
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik, hik, hgap]
        exact Nat.add_comm 2 _
      · rw [if_neg hik, if_neg hik]
        by_cases hik2 : i = k + 1
        · rw [if_pos hik2, if_pos hik2, hik2, hgap, Nat.zero_add]
        · rw [if_neg hik2, if_neg hik2]
          exact Nat.add_comm 1 _
  have hc0 : ground.countOf 0
      (List.replicate k 1 ++ 2 :: 0 :: List.replicate w 1) = 1 := by
    rw [ground.countOf_append, ground.countOf_replicate_ne 0 1 (by decide +kernel) k,
      ground.countOf_head_ne (show (0 : Nat) ≠ 2 by decide +kernel),
      ground.countOf_head, ground.countOf_replicate_ne 0 1 (by decide +kernel) w]
  have hc2 : ground.countOf 2
      (List.replicate k 1 ++ 2 :: 0 :: List.replicate w 1) = 1 := by
    rw [ground.countOf_append, ground.countOf_replicate_ne 2 1 (by decide +kernel) k,
      ground.countOf_head, ground.countOf_head_ne
        (show (2 : Nat) ≠ 0 by decide +kernel),
      ground.countOf_replicate_ne 2 1 (by decide +kernel) w]
  have hc1 : ground.countOf 1
      (List.replicate k 1 ++ 2 :: 0 :: List.replicate w 1) + 2 = d := by
    rw [ground.countOf_append, ground.countOf_replicate 1 k,
      ground.countOf_head_ne (show (1 : Nat) ≠ 2 by decide +kernel),
      ground.countOf_head_ne (show (1 : Nat) ≠ 0 by decide +kernel),
      ground.countOf_replicate 1 w]
    rw [← hkw, Nat.add_assoc k w 2]
  show (match ground.tieGap
      (places.display (ground.bumpAt (d - 1) s))
      (places.expo (places.display s)
        (ground.adjSwap k (List.range d))) with
    | some nu => adjchar.multRead d nu
    | none => 0) = 1
  rw [htie]
  exact adjchar.multRead_move d _ hMl hc0 hc2 hc1

/-- The unit gaps' adjacent exchanges, one per gap key of the
display. -/
private def swapsOf (d : Nat) (s : Shape) : List (List Nat) :=
  (gapKeys (places.display s)).map
    (fun k => ground.adjSwap k (List.range d))

/-- The exchange list holds each of its members at its own key's
count. -/
private theorem swapCount (d k0 : Nat) (hk0 : k0 + 1 < d)
    (L : List Nat) (hL : ∀ x, 0 < ground.countOf x L → x + 1 < d) :
    ground.countOf (ground.adjSwap k0 (List.range d))
        (L.map (fun t => ground.adjSwap t (List.range d)))
      = ground.countOf k0 L :=
  ground.countOf_map_inj (fun t => ground.adjSwap t (List.range d)) k0 L
    (fun x hx he => ground.adjSwap_range_inj d x k0 (hL x hx) hk0 he)

/-- A unit gap's exchange sits in the exchange list once. -/
private theorem swapsOf_count (d : Nat) (s : Shape) (hs : s.length = d)
    (k : Nat) (hk : k + 1 < d)
    (hgap : ground.getAt 0 (places.display s) k
      = ground.getAt 0 (places.display s) (k + 1) + 1) :
    ground.countOf (ground.adjSwap k (List.range d)) (swapsOf d s) = 1 := by
  have hdl : (places.display s).length = d := by
    rw [places.length_display, hs]
  show ground.countOf (ground.adjSwap k (List.range d))
    ((gapKeys (places.display s)).map
      (fun t => ground.adjSwap t (List.range d))) = 1
  rw [swapCount d k hk (gapKeys (places.display s))
      (fun x hx => by
        rw [← hdl]
        exact (gapKeys_read (places.display s) x hx).1),
    countOf_gapKeys (places.display s) k (by rw [hdl]; exact hk) hgap]

/-- An exchange-list member names its gap key. -/
private theorem swapsOf_member (d : Nat) (s : Shape) (p : List Nat)
    (hm : 0 < ground.countOf p (swapsOf d s)) :
    ∃ k, 0 < ground.countOf k (gapKeys (places.display s))
      ∧ p = ground.adjSwap k (List.range d) := by
  have hmem : p ∈ (gapKeys (places.display s)).map
      (fun t => ground.adjSwap t (List.range d)) :=
    ground.mem_of_countOf_pos p (swapsOf d s) hm
  obtain ⟨t, ht, hft⟩ := ground.mem_map_of
    (fun t => ground.adjSwap t (List.range d))
    (gapKeys (places.display s)) p hmem
  exact ⟨t, ground.countOf_pos_of_mem ht, hft.symm⟩

/-- The diagonal's two graded sums: the residue's count at the
identity on the even side against the display's unit gaps on the
odd, at every shape of the width. -/
theorem diagJoin : ∀ (d : Nat) (s : Shape), s.length = d →
    (steinberg.sumsWith (adjchar.multRead d) d s
        (ground.bumpAt (d - 1) s)).1
      + clearGaps (places.display s)
    = (steinberg.sumsWith (adjchar.multRead d) d s
        (ground.bumpAt (d - 1) s)).2 + (d - 1) := by
  intro d s hs
  have hdl : (places.display s).length = d := by
    rw [places.length_display, hs]
  have hstepE : ∀ p ∈ places.perms d, p ≠ List.range d →
      (if places.parity p = false then
        weylchar.multAtGap (adjchar.multRead d)
          (places.display (ground.bumpAt (d - 1) s))
          (places.expo (places.display s) p)
      else 0) = 0 := by
    intro p hpm hpr
    by_cases hpar : places.parity p = false
    · rw [if_pos hpar]
      have hp : 0 < ground.countOf p (places.perms d) :=
        ground.countOf_pos_of_mem hpm
      match Nat.eq_zero_or_pos (weylchar.multAtGap (adjchar.multRead d)
          (places.display (ground.bumpAt (d - 1) s))
          (places.expo (places.display s) p)) with
      | .inl hz => exact hz
      | .inr hpos =>
        obtain ⟨m, hg, hmpos⟩ := weylchar.multAtGap_pos (adjchar.multRead d) _ _ hpos
        cases adjchar.multRead_cases d m hmpos with
        | inl harm =>
          exact absurd (places.tieOnes d s (ground.bumpAt (d - 1) s)
            hs p hp m hg harm.2.1).1 hpr
        | inr harm =>
          obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
          obtain ⟨k, hk1, _, hpk, _⟩ :=
            places.tieMove d s (ground.bumpAt (d - 1) s) hs p hp hpr
              m hg i j h2 h0 h1
          rw [hpk, places.parity_adjSwap_range d k hk1] at hpar
          exact Bool.noConfusion hpar
    · rw [if_neg hpar]
  have heven : ground.famFold Nat.add 0
      (fun p => if places.parity p = false then
        weylchar.multAtGap (adjchar.multRead d)
          (places.display (ground.bumpAt (d - 1) s))
          (places.expo (places.display s) p)
      else 0) (places.perms d) = d - 1 := by
    rw [ground.famFold_off _ (List.range d) (places.perms d) hstepE,
      places.countRangePerms d, places.parity_range d,
      if_pos rfl, tieDiagId d s hs, Nat.one_mul]
  have hstepO : ∀ p, 0 < ground.countOf p (places.perms d) →
      (if places.parity p = true then
        weylchar.multAtGap (adjchar.multRead d)
          (places.display (ground.bumpAt (d - 1) s))
          (places.expo (places.display s) p)
      else 0) = ground.countOf p (swapsOf d s) := by
    intro p hp
    by_cases hpar : places.parity p = true
    · rw [if_pos hpar]
      by_cases hmem : 0 < ground.countOf p (swapsOf d s)
      · obtain ⟨k, hk, hpk⟩ := swapsOf_member d s p hmem
        obtain ⟨hkl, hkg⟩ := gapKeys_read (places.display s) k hk
        rw [hdl] at hkl
        rw [hpk, swapsOf_count d s hs k hkl hkg]
        exact tieDiagSwap d s hs k hkl hkg
      · have hz : ground.countOf p (swapsOf d s) = 0 :=
          match Nat.eq_zero_or_pos (ground.countOf p (swapsOf d s)) with
          | .inl hz0 => hz0
          | .inr hp0 => absurd hp0 hmem
        rw [hz]
        match Nat.eq_zero_or_pos
            (weylchar.multAtGap (adjchar.multRead d)
              (places.display (ground.bumpAt (d - 1) s))
              (places.expo (places.display s) p)) with
        | .inl hz0 => exact hz0
        | .inr hpos =>
          obtain ⟨m, hg, hmpos⟩ := weylchar.multAtGap_pos (adjchar.multRead d) _ _ hpos
          by_cases hpr : p = List.range d
          · rw [hpr, places.parity_range d] at hpar
            exact Bool.noConfusion hpar
          · cases adjchar.multRead_cases d m hmpos with
            | inl harm =>
              exact absurd (places.tieOnes d s (ground.bumpAt (d - 1) s)
                hs p hp m hg harm.2.1).1 hpr
            | inr harm =>
              obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
              obtain ⟨k, hk1, hgk, hpk, _⟩ :=
                places.tieMove d s (ground.bumpAt (d - 1) s) hs p hp
                  hpr m hg i j h2 h0 h1
              refine absurd ?_ hmem
              rw [hpk, swapsOf_count d s hs k hk1 hgk]
              exact Nat.succ_pos 0
    · rw [if_neg hpar]
      have hz : ground.countOf p (swapsOf d s) = 0 :=
        match Nat.eq_zero_or_pos (ground.countOf p (swapsOf d s)) with
        | .inl hz0 => hz0
        | .inr hp0 => by
          obtain ⟨k, hk, hpk⟩ := swapsOf_member d s p hp0
          obtain ⟨hkl, _⟩ := gapKeys_read (places.display s) k hk
          rw [hdl] at hkl
          rw [hpk, places.parity_adjSwap_range d k hkl] at hpar
          exact absurd rfl hpar
      rw [hz]
  have hodd : ground.famFold Nat.add 0
      (fun p => if places.parity p = true then
        weylchar.multAtGap (adjchar.multRead d)
          (places.display (ground.bumpAt (d - 1) s))
          (places.expo (places.display s) p)
      else 0) (places.perms d) = clearGaps (places.display s) := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun p => ground.countOf p (swapsOf d s)) (places.perms d) hstepO,
      ground.famFold_countSwap (places.perms d) (swapsOf d s),
      ground.famFold_congr_members Nat.add 0 _ (fun _ => (1 : Nat))
        (swapsOf d s) (fun q hq => by
          obtain ⟨k, _, hqk⟩ := swapsOf_member d s q hq
          rw [hqk, places.countOf_adjSwap_perms d k]),
      ground.famFold_length (swapsOf d s)]
    show ((gapKeys (places.display s)).map
        (fun t => ground.adjSwap t (List.range d))).length
      = clearGaps (places.display s)
    rw [ground.length_map, length_gapKeys (places.display s)]
  have hsum : steinberg.sumsWith (adjchar.multRead d) d s
      (ground.bumpAt (d - 1) s)
      = (d - 1, clearGaps (places.display s)) := by
    rw [steinberg.sumsWith_split (adjchar.multRead d) d s
      (ground.bumpAt (d - 1) s), heven, hodd]
  rw [hsum]
  show d - 1 + clearGaps (places.display s)
    = clearGaps (places.display s) + (d - 1)
  exact Nat.add_comm _ _

/-- The member's unit gaps against its occupied keys: the display's
gap at a key is the member's own occupancy raised by one, so the
unit gaps sit at the vacant keys and the two counts fill the
residue. -/
private theorem memberGaps (P Q : List Nat) (k : Nat) :
    clearGaps (places.display (member P Q (P.length + Q.length + k + 1)))
      + (suppCount P + suppCount Q)
    = P.length + Q.length + k := by
  have hmem : member P Q (P.length + Q.length + k + 1)
      = ((P ++ List.replicate k 0) ++ Q.reverse) ++ [0] := by
    show P ++ List.replicate
        (P.length + Q.length + k + 1 - 1 - P.length - Q.length) 0
        ++ Q.reverse ++ [0]
      = ((P ++ List.replicate k 0) ++ Q.reverse) ++ [0]
    rw [middle_count P.length Q.length k]
  have hsupp : suppCount ((P ++ List.replicate k 0) ++ Q.reverse)
      = suppCount P + suppCount Q := by
    rw [suppCount_append (P ++ List.replicate k 0) Q.reverse,
      suppCount_append P (List.replicate k 0),
      suppCount_replicate_zero k, suppCount_reverse Q, Nat.add_zero]
  have hlen : ((P ++ List.replicate k 0) ++ Q.reverse).length
      = P.length + Q.length + k := by
    rw [ground.length_append (P ++ List.replicate k 0) Q.reverse,
      ground.length_append P (List.replicate k 0),
      ground.length_replicate 0 k, ground.length_reverse Q,
      Nat.add_right_comm P.length k Q.length]
  have hrec := clearGaps_snoc ((P ++ List.replicate k 0) ++ Q.reverse) 0
  rw [hsupp, hlen] at hrec
  rw [hmem]
  exact hrec

/-- The join's cancellation: a shared gap withdraws from both
sides. -/
private theorem joinCancel (A B C S T : Nat) (h1 : A + C = B + T)
    (h2 : C + S = T) : A = B + S := by
  refine ground.addCancelR C ?_
  rw [h1, ← h2, Nat.add_comm C S, Nat.add_assoc]

/-- The diagonal at a member: the two graded sums part by the two
words' occupied keys, the member-key count. -/
theorem rowDiag : ∀ (P Q : List Nat) (d : Nat),
    P.length + Q.length + 1 ≤ d →
    (steinberg.sumsWith (adjchar.multRead d) d (member P Q d)
        (ground.bumpAt (d - 1) (member P Q d))).1
    = (steinberg.sumsWith (adjchar.multRead d) d (member P Q d)
        (ground.bumpAt (d - 1) (member P Q d))).2
      + (suppCount P + suppCount Q) := by
  intro P Q d h
  have hk : ∃ k : Nat, d = P.length + Q.length + k + 1 :=
    ⟨d - (P.length + Q.length + 1), by
      rw [Nat.add_right_comm (P.length + Q.length)
        (d - (P.length + Q.length + 1)) 1]
      exact (ground.natAddSubCancel h).symm⟩
  cases hk with
  | intro k hk =>
    subst hk
    exact joinCancel _ _ _ _ _
      (diagJoin (P.length + Q.length + k + 1)
        (member P Q (P.length + Q.length + k + 1))
        (member_length P Q k))
      (memberGaps P Q k)

/-! `lem:rankstable`(ii)'s off-diagonal tier: `cor:steinberg` at
the adjoint on a target off the full-column bump. -/

/-- The gap's own shuffle: the occupancy against the display's
step. -/
private theorem gapJoin (A B C : Nat) : A + B + (1 + C) = B + C + A + 1 := by
  rw [Nat.add_comm 1 C, ← Nat.add_assoc (A + B) C 1,
    Nat.add_comm A B, Nat.add_right_comm B A C]

/-- The display's consecutive gap is the shape's own occupancy
raised by one. -/
private theorem display_gap (s : Shape) (k : Nat) (hk : k + 1 < s.length) :
    ground.getAt 0 (places.display s) k
      = ground.getAt 0 (places.display s) (k + 1)
        + ground.getAt 0 s k + 1 := by
  have hk0 : k < s.length := Nat.lt_of_succ_lt hk
  have h1 : (k + 1) + (s.length - (k + 1)) = s.length :=
    ground.natAddSubCancel (Nat.le_of_lt hk)
  have h2 : k + (s.length - k) = s.length :=
    ground.natAddSubCancel (Nat.le_of_lt hk0)
  have h3 : k + (s.length - k) = k + (1 + (s.length - (k + 1))) := by
    rw [h2, ← Nat.add_assoc k 1 (s.length - (k + 1))]
    exact h1.symm
  have hsub : s.length - k = 1 + (s.length - (k + 1)) :=
    ground.addCancelL k h3
  rw [places.getAt_display s k hk0, places.getAt_display s (k + 1) hk,
    places.rowList_gap s k hk0, hsub]
  exact gapJoin _ _ _

/-- The raised display names the diagonal target: two shapes at one
display are one shape. -/
private theorem diag_of_display (d : Nat) (s c : Shape) (hs : s.length = d)
    (hd : places.display c = (places.display s).map (fun x => x + 1)) :
    c = ground.bumpAt (d - 1) s :=
  places.display_inj c (ground.bumpAt (d - 1) s)
    (by rw [hd, display_diag d s hs])

/-- Off the diagonal target every permutation but the identity
reads the vacant tie: the all-ones content forces the identity and
either content forces the raised display. -/
private theorem offVanish (d : Nat) (s c : Shape) (hs : s.length = d)
    (hne : ¬ c = ground.bumpAt (d - 1) s)
    (p : List Nat) (hp : 0 < ground.countOf p (places.perms d))
    (hpr : ¬ p = List.range d) :
    weylchar.multAtGap (adjchar.multRead d) (places.display c)
      (places.expo (places.display s) p) = 0 := by
  match Nat.eq_zero_or_pos (weylchar.multAtGap (adjchar.multRead d)
      (places.display c) (places.expo (places.display s) p)) with
  | .inl hz => exact hz
  | .inr hpos =>
    obtain ⟨m, hg, hmpos⟩ :=
      weylchar.multAtGap_pos (adjchar.multRead d) _ _ hpos
    cases adjchar.multRead_cases d m hmpos with
    | inl harm =>
      exact absurd (diag_of_display d s c hs
        (places.tieOnes d s c hs p hp m hg harm.2.1).2) hne
    | inr harm =>
      obtain ⟨i, _, j, _, _, h2, h0, h1⟩ := harm.2.1
      obtain ⟨_, _, _, _, hdisp⟩ :=
        places.tieMove d s c hs p hp hpr m hg i j h2 h0 h1
      exact absurd (diag_of_display d s c hs hdisp) hne

/-- The identity's own tie off the diagonal target reads at one:
the all-ones content would force the raised display, so the
letter-pair arm is the read. -/
private theorem idBound (d : Nat) (s c : Shape) (hs : s.length = d)
    (hne : ¬ c = ground.bumpAt (d - 1) s) :
    weylchar.multAtGap (adjchar.multRead d) (places.display c)
      (places.expo (places.display s) (List.range d)) ≤ 1 := by
  match Nat.eq_zero_or_pos (weylchar.multAtGap (adjchar.multRead d)
      (places.display c)
      (places.expo (places.display s) (List.range d))) with
  | .inl hz =>
    rw [hz]
    exact Nat.zero_le 1
  | .inr hpos =>
    obtain ⟨m, hg, hmpos⟩ :=
      weylchar.multAtGap_pos (adjchar.multRead d) _ _ hpos
    have hpid : 0 < ground.countOf (List.range d) (places.perms d) := by
      rw [places.countRangePerms d]
      exact Nat.succ_pos 0
    have hval : weylchar.multAtGap (adjchar.multRead d) (places.display c)
        (places.expo (places.display s) (List.range d))
        = adjchar.multRead d m := by
      show (match ground.tieGap (places.display c)
          (places.expo (places.display s) (List.range d)) with
        | some nu => adjchar.multRead d nu
        | none => 0) = adjchar.multRead d m
      rw [hg]
    cases adjchar.multRead_cases d m hmpos with
    | inl harm =>
      exact absurd (diag_of_display d s c hs
        (places.tieOnes d s c hs (List.range d) hpid m hg harm.2.1).2) hne
    | inr harm => exact Nat.le_of_eq (hval.trans harm.2.2)

/-- Off the diagonal target the even sum is at most one: every
further permutation reads the vacant tie and the identity's own tie
reads the letter-pair arm, at every shape of the width. -/
theorem rowOffOne : ∀ (d : Nat) (s c : Shape), s.length = d →
    ¬ c = ground.bumpAt (d - 1) s →
    (steinberg.sumsWith (adjchar.multRead d) d s c).1
      ≤ (steinberg.sumsWith (adjchar.multRead d) d s c).2 + 1 := by
  intro d s c hs hne
  have hstep : ∀ p ∈ places.perms d, p ≠ List.range d →
      (if places.parity p = false then
        weylchar.multAtGap (adjchar.multRead d) (places.display c)
          (places.expo (places.display s) p)
      else 0) = 0 := by
    intro p hpm hpr
    by_cases hpar : places.parity p = false
    · rw [if_pos hpar]
      exact offVanish d s c hs hne p (ground.countOf_pos_of_mem hpm) hpr
    · rw [if_neg hpar]
  have hfst : (steinberg.sumsWith (adjchar.multRead d) d s c).1 ≤ 1 := by
    rw [steinberg.sumsWith_split (adjchar.multRead d) d s c]
    show ground.famFold Nat.add 0
        (fun p => if places.parity p = false then
          weylchar.multAtGap (adjchar.multRead d) (places.display c)
            (places.expo (places.display s) p)
        else 0) (places.perms d) ≤ 1
    rw [ground.famFold_off _ (List.range d) (places.perms d) hstep,
      places.countRangePerms d, places.parity_range d, if_pos rfl,
      Nat.one_mul]
    exact idBound d s c hs hne
  exact Nat.le_trans hfst (Nat.succ_le_succ (Nat.zero_le _))

/-- The member is vacant across the middle block: between the top
word and the bottom word's reflection every key reads the vacant
occupancy. -/
private theorem member_vac (P Q : List Nat) (k0 t : Nat)
    (h1 : P.length ≤ t) (h2 : t < P.length + k0) :
    ground.getAt 0 (member P Q (P.length + Q.length + k0 + 1)) t = 0 := by
  rw [member_split P Q k0,
    ground.getAt_append 0 P (List.replicate k0 0 ++ (Q.reverse ++ [0])) t,
    if_neg (Nat.not_lt_of_ge h1),
    ground.getAt_append 0 (List.replicate k0 0) (Q.reverse ++ [0])
      (t - P.length),
    ground.length_replicate 0 k0,
    if_pos (ground.subLt h1 h2)]
  exact ground.getAt_replicate_zero k0 (t - P.length)

/-- A raised place against the all-ones remainder: the key's own
step sits below the raised neighbour's. -/
private theorem stepBound (x X : Nat) (h : x ≤ 1) : x + (X + 1) ≤ 2 + X := by
  rw [Nat.add_comm X 1, ← Nat.add_assoc x 1 X]
  exact Nat.add_le_add_right (Nat.succ_le_succ h) X

/-- A lowered place against the all-ones remainder: the successor
key's step sits at or above the lowered neighbour's. -/
private theorem stepBoundR (x X : Nat) (h : 1 ≤ x) : X + 1 ≤ x + X := by
  rw [Nat.add_comm x X]
  exact Nat.add_le_add_left h X

/-- The window's join: the key's own gap is the two places' gap and
the raised place caps it at the vacant occupancy. -/
private theorem confJoin (m1 m2 g Y : Nat)
    (hA : m1 + (Y + 1) = m2 + Y + g + 1)
    (hb1 : m1 ≤ 1) (hb2 : 1 ≤ m2) : g = 0 := by
  have hA' : m1 + Y + 1 = m2 + g + Y + 1 := by
    rw [Nat.add_assoc m1 Y 1, Nat.add_right_comm m2 g Y]
    exact hA
  have hEq : m1 = m2 + g :=
    ground.addCancelR Y (ground.addCancelR 1 hA')
  have hb1' : m2 + g ≤ 1 := by
    rw [← hEq]
    exact hb1
  exact Nat.eq_zero_of_le_zero (ground.leCancelL 1
    (show 1 + g ≤ 1 + 0 from
      Nat.le_trans (Nat.add_le_add_right hb2 g) hb1'))

/-- The identity's letter-pair tie at a clear-window key: the
neighbouring pairs refuse the raised and the lowered place — an
interior raise or lower would hand the target display a vanishing
gap — so the key's own gap is the all-ones remainder's and the
target is vacant there. -/
private theorem confinedCore (d t : Nat) (s c : Shape) (m : List Nat)
    (i j : Nat) (hsl : s.length = d) (hcl : c.length = d)
    (hlt3 : t + 3 < d)
    (hv0 : ground.getAt 0 s t = 0)
    (hv1 : ground.getAt 0 s (t + 1) = 0)
    (hv2 : ground.getAt 0 s (t + 2) = 0)
    (hent : ∀ u, u < d →
      ground.getAt 0 m u + ground.getAt 0 (places.display s) u
        = ground.getAt 0 (places.display c) u)
    (h2 : ground.getAt 0 m i = 2) (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ u, u < d → ¬ u = i → ¬ u = j → ground.getAt 0 m u = 1) :
    ground.getAt 0 c (t + 1) = 0 := by
  have hlt2 : t + 2 < d := Nat.lt_of_succ_lt hlt3
  have hlt1 : t + 1 < d := Nat.lt_of_succ_lt hlt2
  have hlt0 : t < d := Nat.lt_of_succ_lt hlt1
  have hg0 : ground.getAt 0 (places.display s) t
      = ground.getAt 0 (places.display s) (t + 1) + 1 := by
    have hh := display_gap s t (by rw [hsl]; exact hlt1)
    rw [hv0] at hh
    exact hh
  have hg1 : ground.getAt 0 (places.display s) (t + 1)
      = ground.getAt 0 (places.display s) (t + 2) + 1 := by
    have hh := display_gap s (t + 1) (by rw [hsl]; exact hlt2)
    rw [hv1] at hh
    exact hh
  have hg2 : ground.getAt 0 (places.display s) (t + 2)
      = ground.getAt 0 (places.display s) (t + 3) + 1 := by
    have hh := display_gap s (t + 2) (by rw [hsl]; exact hlt3)
    rw [hv2] at hh
    exact hh
  have hRi : ¬ (t + 1) = i := by
    intro hi
    have hdesc := places.display_desc c t (by rw [hcl]; exact hlt1)
    have hct := hent t hlt0
    have hct1 := hent (t + 1) hlt1
    have hmi : ground.getAt 0 m (t + 1) = 2 := by
      rw [hi]
      exact h2
    have hmt : ground.getAt 0 m t ≤ 1 := by
      by_cases htj : t = j
      · rw [htj, h0]
        exact Nat.zero_le 1
      · rw [h1 t hlt0
          (fun he => absurd (he.trans hi.symm).symm (Nat.succ_ne_self t)) htj]
        exact Nat.le_refl 1
    refine absurd hdesc (Nat.not_lt_of_ge ?_)
    rw [← hct, ← hct1, hmi, hg0]
    exact stepBound _ _ hmt
  have hRj : ¬ (t + 2) = j := by
    intro hj
    have hdesc := places.display_desc c (t + 2) (by rw [hcl]; exact hlt3)
    have hct2 := hent (t + 2) hlt2
    have hct3 := hent (t + 3) hlt3
    have hmj : ground.getAt 0 m (t + 2) = 0 := by
      rw [hj]
      exact h0
    have hm3 : 1 ≤ ground.getAt 0 m (t + 3) := by
      by_cases h3i : t + 3 = i
      · rw [h3i, h2]
        exact Nat.le_succ 1
      · rw [h1 (t + 3) hlt3 h3i
          (fun he => absurd (he.trans hj.symm) (Nat.succ_ne_self (t + 2)))]
        exact Nat.le_refl 1
    refine absurd hdesc (Nat.not_lt_of_ge ?_)
    rw [← hct2, ← hct3, hmj, Nat.zero_add, hg2]
    exact stepBoundR _ _ hm3
  have hct1 := hent (t + 1) hlt1
  have hct2 := hent (t + 2) hlt2
  have hm1 : ground.getAt 0 m (t + 1) ≤ 1 := by
    by_cases h1j : t + 1 = j
    · rw [h1j, h0]
      exact Nat.zero_le 1
    · rw [h1 (t + 1) hlt1 hRi h1j]
      exact Nat.le_refl 1
  have hm2 : 1 ≤ ground.getAt 0 m (t + 2) := by
    by_cases h2i : t + 2 = i
    · rw [h2i, h2]
      exact Nat.le_succ 1
    · rw [h1 (t + 2) hlt2 h2i hRj]
      exact Nat.le_refl 1
  have hgc : ground.getAt 0 (places.display c) (t + 1)
      = ground.getAt 0 (places.display c) (t + 2)
        + ground.getAt 0 c (t + 1) + 1 :=
    display_gap c (t + 1) (by rw [hcl]; exact hlt2)
  refine confJoin (ground.getAt 0 m (t + 1)) (ground.getAt 0 m (t + 2))
    (ground.getAt 0 c (t + 1))
    (ground.getAt 0 (places.display s) (t + 2)) ?_ hm1 hm2
  rw [← hg1, hct1, hgc, ← hct2]

/-- At the raised display the target is the diagonal, vacant across
the member's middle block off the full column. -/
private theorem confinedDiag (P Q : List Nat) (k0 t : Nat) (c : Shape)
    (hd : places.display c
      = (places.display (member P Q (P.length + Q.length + k0 + 1))).map
        (fun x => x + 1))
    (ha : P.length ≤ t) (hw : t + 3 ≤ P.length + k0) :
    ground.getAt 0 c (t + 1) = 0 := by
  have hwt1 : t + 1 < P.length + k0 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self (t + 1))
      (Nat.le_succ (t + 2))) hw
  have hne' : ¬ (t + 1) = P.length + Q.length + k0 + 1 - 1 := by
    show ¬ (t + 1) = P.length + Q.length + k0
    intro he
    rw [he] at hwt1
    exact absurd hwt1 (Nat.not_lt_of_ge (Nat.add_le_add_right
      (Nat.le_add_right P.length Q.length) k0))
  rw [diag_of_display (P.length + Q.length + k0 + 1)
      (member P Q (P.length + Q.length + k0 + 1)) c
      (member_length P Q k0) hd,
    ground.getAt_bumpAt_ne _ _ (t + 1) hne']
  exact member_vac P Q k0 (t + 1) (Nat.le_succ_of_le ha) hwt1

/-- The member's confinement window: at a target the two graded
sums part at, every off-word key at distance two from both words
reads the target's occupancy vacant. -/
theorem rowConfined : ∀ (P Q : List Nat) (d : Nat) (c : Shape),
    (steinberg.sumsWith (adjchar.multRead d) d (member P Q d) c).2
      < (steinberg.sumsWith (adjchar.multRead d) d (member P Q d) c).1 →
    ∀ k, P.length + 1 ≤ k → k + Q.length + 3 ≤ d →
    ground.getAt 0 c k = 0 := by
  intro P Q d c hlt k hk1 hk2
  have hfl : P.length + Q.length + 1 ≤ d :=
    Nat.le_trans
      (Nat.le_trans
        (Nat.le_trans
          (by
            rw [Nat.add_right_comm P.length Q.length 1]
            exact Nat.le_refl (P.length + 1 + Q.length))
          (Nat.add_le_add_right hk1 Q.length))
        (Nat.le_add_right (k + Q.length) 3))
      hk2
  obtain ⟨k0, rfl⟩ : ∃ k0 : Nat, d = P.length + Q.length + k0 + 1 :=
    ⟨d - (P.length + Q.length + 1), by
      rw [Nat.add_right_comm (P.length + Q.length)
        (d - (P.length + Q.length + 1)) 1]
      exact (ground.natAddSubCancel hfl).symm⟩
  have hkp : 0 < k := Nat.lt_of_lt_of_le (Nat.succ_pos P.length) hk1
  obtain ⟨t, rfl⟩ : ∃ t : Nat, k = t + 1 :=
    ⟨k - 1, (ground.subAdd hkp).symm⟩
  have ha : P.length ≤ t := Nat.le_of_succ_le_succ hk1
  have hwsum : t + 3 + (Q.length + 1) ≤ P.length + k0 + (Q.length + 1) := by
    rw [show t + 3 + (Q.length + 1) = t + 1 + Q.length + 3 from by
        rw [← Nat.add_assoc (t + 3) Q.length 1,
          Nat.add_right_comm t 3 Q.length,
          Nat.add_right_comm t 1 Q.length,
          Nat.add_right_comm (t + Q.length) 1 3],
      show P.length + k0 + (Q.length + 1)
          = P.length + Q.length + k0 + 1 from by
        rw [← Nat.add_assoc (P.length + k0) Q.length 1,
          Nat.add_right_comm P.length k0 Q.length]]
    exact hk2
  have hw : t + 3 ≤ P.length + k0 := ground.leCancelR (Q.length + 1) hwsum
  have hmid : P.length + k0 ≤ P.length + Q.length + k0 :=
    Nat.add_le_add_right (Nat.le_add_right P.length Q.length) k0
  have hlt3 : t + 3 < P.length + Q.length + k0 + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans hw hmid)
  have hlt2 : t + 2 < P.length + Q.length + k0 + 1 := Nat.lt_of_succ_lt hlt3
  have hlt1 : t + 1 < P.length + Q.length + k0 + 1 := Nat.lt_of_succ_lt hlt2
  have hwt : t < P.length + k0 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self t)
      (Nat.le_trans (Nat.le_succ (t + 1)) (Nat.le_succ (t + 2)))) hw
  have hwt1 : t + 1 < P.length + k0 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self (t + 1))
      (Nat.le_succ (t + 2))) hw
  have hwt2 : t + 2 < P.length + k0 :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (t + 2)) hw
  have hsl : (member P Q (P.length + Q.length + k0 + 1)).length
      = P.length + Q.length + k0 + 1 := member_length P Q k0
  have hdl : (places.display
      (member P Q (P.length + Q.length + k0 + 1))).length
      = P.length + Q.length + k0 + 1 := by
    rw [places.length_display, hsl]
  have hexpo : places.expo
      (places.display (member P Q (P.length + Q.length + k0 + 1)))
      (List.range (P.length + Q.length + k0 + 1))
      = places.display (member P Q (P.length + Q.length + k0 + 1)) :=
    ground.range_map_getAt 0 (P.length + Q.length + k0 + 1) _ hdl
  have hpos : 0 < (steinberg.sumsWith
      (adjchar.multRead (P.length + Q.length + k0 + 1))
      (P.length + Q.length + k0 + 1)
      (member P Q (P.length + Q.length + k0 + 1)) c).1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hfst : (steinberg.sumsWith
        (adjchar.multRead (P.length + Q.length + k0 + 1))
        (P.length + Q.length + k0 + 1)
        (member P Q (P.length + Q.length + k0 + 1)) c).1
      = ground.famFold Nat.add 0
        (fun p => if places.parity p = false then
          weylchar.multAtGap
            (adjchar.multRead (P.length + Q.length + k0 + 1))
            (places.display c)
            (places.expo (places.display
              (member P Q (P.length + Q.length + k0 + 1))) p)
        else 0) (places.perms (P.length + Q.length + k0 + 1)) := by
    rw [steinberg.sumsWith_split
      (adjchar.multRead (P.length + Q.length + k0 + 1))
      (P.length + Q.length + k0 + 1)
      (member P Q (P.length + Q.length + k0 + 1)) c]
  rw [hfst] at hpos
  obtain ⟨p, hp, hgp⟩ := ground.famFold_pos_witness _
    (places.perms (P.length + Q.length + k0 + 1)) hpos
  have hgp' : 0 < (if places.parity p = false then
      weylchar.multAtGap (adjchar.multRead (P.length + Q.length + k0 + 1))
        (places.display c)
        (places.expo (places.display
          (member P Q (P.length + Q.length + k0 + 1))) p)
    else 0) := hgp
  have hpar : places.parity p = false := by
    by_cases hb : places.parity p = false
    · exact hb
    · rw [if_neg hb] at hgp'
      exact absurd hgp' (Nat.lt_irrefl 0)
  rw [if_pos hpar] at hgp'
  obtain ⟨m, hg, hmpos⟩ := weylchar.multAtGap_pos
    (adjchar.multRead (P.length + Q.length + k0 + 1)) _ _ hgp'
  cases adjchar.multRead_cases (P.length + Q.length + k0 + 1) m hmpos with
  | inl harm =>
    exact confinedDiag P Q k0 t c
      (places.tieOnes (P.length + Q.length + k0 + 1)
        (member P Q (P.length + Q.length + k0 + 1)) c hsl p hp m hg
        harm.2.1).2 ha hw
  | inr harm =>
    obtain ⟨i, _, j, _, _, h2, h0, h1⟩ := harm.2.1
    by_cases hpr : p = List.range (P.length + Q.length + k0 + 1)
    · rw [hpr, hexpo] at hg
      obtain ⟨_, hzl, hent0⟩ := ground.tieGap_reads _ _ _ hg
      have hcdl : (places.display c).length
          = P.length + Q.length + k0 + 1 := by
        rw [← hzl]
        exact hdl
      have hcl : c.length = P.length + Q.length + k0 + 1 := by
        rw [← places.length_display c]
        exact hcdl
      exact confinedCore (P.length + Q.length + k0 + 1) t
        (member P Q (P.length + Q.length + k0 + 1)) c m i j hsl hcl hlt3
        (member_vac P Q k0 t ha hwt)
        (member_vac P Q k0 (t + 1) (Nat.le_succ_of_le ha) hwt1)
        (member_vac P Q k0 (t + 2)
          (Nat.le_trans ha (Nat.le_add_right t 2)) hwt2)
        (fun u hu => hent0 u (by rw [hcdl]; exact hu)) h2 h0 h1
    · obtain ⟨_, _, _, _, hdisp⟩ :=
        places.tieMove (P.length + Q.length + k0 + 1)
          (member P Q (P.length + Q.length + k0 + 1)) c hsl p hp hpr m hg
          i j h2 h0 h1
      exact confinedDiag P Q k0 t c hdisp ha hw

/-- The weak descent's test, the row lists' own shape. -/
private def descB : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => Nat.ble b a && descB (b :: t)

/-- The raise-lower survivors at the matched degree: per place
pair the moved raised row list, kept exactly at the weak descent
and read back as its shape. -/
private def moveCands (d : Nat) (s : Shape) : List Shape :=
  let r1 := (places.rowList s).map (fun x => x + 1)
  (List.range d).flatMap (fun i =>
    (List.range d).filterMap (fun j =>
      if i == j then none
      else
        let y := ground.dipAt j (ground.bumpAt i r1)
        if descB y then some (places.shapeOf y) else none))

/-- The matched-degree move candidates: the raised row list at the
full-column bump with the raise-lower survivors, every kept list a
shape's own row list at the weak descent. -/
private def adjCands (d : Nat) (s : Shape) : List Shape :=
  places.shapeOf ((places.rowList s).map (fun x => x + 1))
    :: moveCands d s

/-- The adjoint fusion row's word read at the label calculus: the
full-column bump at the diagonal's occupied-gap read with the
raise-lower survivors, each reduced to its class — the counts the
displays' own (`lem:rankstable`(ii)), the diagonal the occupied
coordinates' count over the gap keys and each kept move at one. -/
def adjRow (d : Nat) (s : Shape) : List Shape :=
  (if clearGaps (places.display s) < d - 1
    then [labels.reduce (ground.bumpAt (d - 1) s)] else [])
  ++ (moveCands d s).map (fun c => labels.reduce c)

/-- The definitional count reads the fast count at matched widths:
the factors exchange at the block counts and the content formula
agrees at the adjoint's span. -/
theorem adjCount_eq (d : Nat) (s c : Shape)
    (hs : s.length = d) (hc : c.length = d) (hd : 2 ≤ d) :
    steinberg.count s (adjchar.theta d) c
      = channels.adjCount d s c := by
  have hts : (adjchar.theta d).length = s.length := by
    rw [adjchar.length_theta, hs]
  have hcs : c.length = s.length := by rw [hc, hs]
  have hst : s.length = (adjchar.theta d).length := hts.symm
  have hct : c.length = (adjchar.theta d).length := by
    rw [hc, adjchar.length_theta]
  have h1 : blockcount.fusionCount s (adjchar.theta d) c
      + (steinberg.gradedSums s (adjchar.theta d) c).2
      = (steinberg.gradedSums s (adjchar.theta d) c).1 :=
    steinberg.readAll s (adjchar.theta d) c hts hcs
  have h2 : blockcount.fusionCount (adjchar.theta d) s c
      + (steinberg.gradedSums (adjchar.theta d) s c).2
      = (steinberg.gradedSums (adjchar.theta d) s c).1 :=
    steinberg.readAll (adjchar.theta d) s c hst hct
  show (steinberg.gradedSums s (adjchar.theta d) c).1
      - (steinberg.gradedSums s (adjchar.theta d) c).2
    = (steinberg.sumsWith (adjchar.multRead d) d s c).1
      - (steinberg.sumsWith (adjchar.multRead d) d s c).2
  rw [← channels.sumsWith_agree d s c hd hc, ← h1, ← h2,
    ground.addSubSelfR, ground.addSubSelfR,
    blockcount.fusionCount_comm s (adjchar.theta d) c hts]

/-- The weak descent's test reads the entrywise descent back. -/
private theorem desc_of_descB : ∀ (l : List Nat), descB l = true →
    ∀ k, k + 1 < l.length →
      ground.getAt 0 l (k + 1) ≤ ground.getAt 0 l k
  | [], _, k, hk => absurd hk (Nat.not_lt_zero (k + 1))
  | [_], _, k, hk => absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero k)
  | a :: b :: t, h, 0, _ => by
    have hh : (Nat.ble b a && descB (b :: t)) = true := h
    exact ground.bleLe (ground.andSplitB hh).1
  | a :: b :: t, h, k + 1, hk => by
    have hh : (Nat.ble b a && descB (b :: t)) = true := h
    exact desc_of_descB (b :: t) (ground.andSplitB hh).2 k
      (Nat.lt_of_succ_lt_succ hk)

/-- The entrywise descent reads the weak descent's test back. -/
private theorem descB_of_desc : ∀ (l : List Nat),
    (∀ k, k + 1 < l.length →
      ground.getAt 0 l (k + 1) ≤ ground.getAt 0 l k) →
    descB l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    show (Nat.ble b a && descB (b :: t)) = true
    rw [ground.leBle (show b ≤ a from
        h 0 (Nat.succ_lt_succ (Nat.succ_pos t.length))),
      descB_of_desc (b :: t)
        (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))]
    rfl

/-- A raise at every key adds one box per key. -/
private theorem sumNat_map_succ : ∀ l : List Nat,
    ground.sumNat (l.map (fun x => x + 1))
      = ground.sumNat l + l.length
  | [] => rfl
  | a :: t => by
    show a + 1 + ground.sumNat (t.map (fun x => x + 1))
      = a + ground.sumNat t + (t.length + 1)
    rw [sumNat_map_succ t,
      Nat.add_assoc a 1 (ground.sumNat t + t.length),
      Nat.add_assoc a (ground.sumNat t) (t.length + 1),
      Nat.add_comm 1 (ground.sumNat t + t.length),
      Nat.add_assoc (ground.sumNat t) t.length 1]

/-- The raised row list's entry read. -/
private theorem getAt_raise (d : Nat) (s : Shape) (hs : s.length = d) :
    ∀ k, k < d →
      ground.getAt 0 ((places.rowList s).map (fun x => x + 1)) k
        = ground.getAt 0 (places.rowList s) k + 1 := by
  intro k hk
  exact ground.getAt_map 0 0 (fun x => x + 1) (places.rowList s) k
    (by rw [places.length_rowList, hs]; exact hk)

/-- The raised row list descends weakly, the rows' own descent
carried key by key. -/
private theorem raise_desc (s : Shape) : ∀ k,
    k + 1 < ((places.rowList s).map (fun x => x + 1)).length →
      ground.getAt 0 ((places.rowList s).map (fun x => x + 1)) (k + 1)
        ≤ ground.getAt 0 ((places.rowList s).map (fun x => x + 1)) k := by
  intro k hk
  rw [ground.length_map, places.length_rowList] at hk
  rw [ground.getAt_map 0 0 (fun x => x + 1) (places.rowList s) (k + 1)
      (by rw [places.length_rowList]; exact hk),
    ground.getAt_map 0 0 (fun x => x + 1) (places.rowList s) k
      (by rw [places.length_rowList]; exact Nat.lt_of_succ_lt hk)]
  exact Nat.succ_le_succ (places.rowList_le s k hk)

/-- The raised row list's total: the shape's degree with one box
per key. -/
private theorem sumNat_raise (s : Shape) :
    ground.sumNat ((places.rowList s).map (fun x => x + 1))
      = places.degree s + s.length := by
  show ground.sumNat ((places.rowList s).map (fun x => x + 1))
    = ground.sumNat (places.rowList s) + s.length
  rw [sumNat_map_succ (places.rowList s), places.length_rowList]

/-- The reduction is injective at one width and one degree: the
prefixes agree at the split and the degree ties the last
occupancies. -/
private theorem reduce_inj (r : Nat) (c c' : Shape)
    (hc : c.length = r + 1) (hc' : c'.length = r + 1)
    (hdeg : places.degree c = places.degree c')
    (h : labels.reduce c = labels.reduce c') : c = c' := by
  obtain ⟨u, a, hu, hul⟩ := ground.snoc_split r c hc
  obtain ⟨v, b, hv, hvl⟩ := ground.snoc_split r c' hc'
  rw [hu, hv, labels.reduce_snoc u a, labels.reduce_snoc v b] at h
  have huv : u = v := ground.snoc_inj u v 0 h
  have hdeg' : places.degree u + a * (u.length + 1)
      = places.degree u + b * (u.length + 1) := by
    rw [← places.degree_snoc u a, ← places.degree_snoc u b, ← hu,
      show u ++ [b] = c' from by rw [huv]; exact hv.symm]
    exact hdeg
  have hab : a = b := Nat.eq_of_mul_eq_mul_right
    (Nat.succ_pos u.length) (ground.addCancelL _ hdeg')
  rw [hu, hv, huv, hab]

/-- A keyed image counts a value at most once where the source
counts each member at most once and the emission distinguishes its
sources. -/
private theorem countOf_filterMap_le_one {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → Option β) (y : β) :
    ∀ l : List α, (∀ a, ground.countOf a l ≤ 1) →
      (∀ a b, 0 < ground.countOf a l → 0 < ground.countOf b l →
        f a = some y → f b = some y → a = b) →
      ground.countOf y (l.filterMap f) ≤ 1
  | [], _, _ => Nat.zero_le 1
  | x :: t, hc, hinj => by
    have hct : ∀ a, ground.countOf a t ≤ 1 := fun a =>
      Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _)
        (Nat.le_of_eq (ground.countOf_cons a x t).symm)) (hc a)
    have hinjt : ∀ a b, 0 < ground.countOf a t → 0 < ground.countOf b t →
        f a = some y → f b = some y → a = b := fun a b ha hb =>
      hinj a b (ground.countOf_cons_pos ha) (ground.countOf_cons_pos hb)
    cases hf : f x with
    | none =>
      have hx : List.filterMap f (x :: t) = t.filterMap f := by
        show (match f x with
              | none => t.filterMap f
              | some c => c :: t.filterMap f) = t.filterMap f
        rw [hf]
      rw [hx]
      exact countOf_filterMap_le_one f y t hct hinjt
    | some z =>
      have hx : List.filterMap f (x :: t) = z :: t.filterMap f := by
        show (match f x with
              | none => t.filterMap f
              | some c => c :: t.filterMap f) = z :: t.filterMap f
        rw [hf]
      rw [hx, ground.countOf_cons]
      by_cases hyz : y = z
      · have hzero : ground.countOf y (t.filterMap f) = 0 := by
          match Nat.eq_zero_or_pos (ground.countOf y (t.filterMap f)) with
          | .inl h0 => exact h0
          | .inr hp =>
            obtain ⟨w, hw, hfw⟩ := ground.filterMap_pre f t y hp
            have hwx : w = x := hinj w x (ground.countOf_cons_pos hw)
              (by rw [ground.countOf_head]; exact Nat.succ_pos _)
              hfw (by rw [hf, hyz])
            rw [hwx] at hw
            have hle : ground.countOf x t + 1 ≤ 1 := by
              rw [← ground.countOf_head x t]
              exact hc x
            exact absurd (Nat.lt_of_lt_of_le hw
              (Nat.le_of_succ_le_succ hle)) (Nat.lt_irrefl 0)
        rw [if_pos hyz, hzero]
        exact Nat.le_refl 1
      · rw [if_neg hyz, Nat.zero_add]
        exact countOf_filterMap_le_one f y t hct hinjt

/-- The occupied emission's reads: the count is positive and the
value is the source's own class. -/
private theorem emit_reads {n : Nat} {a x : Shape}
    (h : (if 0 < n then some (labels.reduce a) else none) = some x) :
    0 < n ∧ labels.reduce a = x := by
  by_cases hp : 0 < n
  · rw [if_pos hp] at h
    exact ⟨hp, Option.some.inj h⟩
  · rw [if_neg hp] at h
    exact nomatch (show (none : Option Shape) = some x from h)

/-- A raised display reads the raised row list: the staircase
cancels key by key. -/
private theorem rowList_of_raise (d : Nat) (s c : Shape)
    (hs : s.length = d) (hc : c.length = d)
    (hdisp : places.display c = (places.display s).map (fun x => x + 1)) :
    places.rowList c = (places.rowList s).map (fun x => x + 1) := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [places.length_rowList, ground.length_map, places.length_rowList,
      hs, hc]
  · intro k hk
    rw [places.length_rowList, hc] at hk
    have he : ground.getAt 0 (places.display c) k
        = ground.getAt 0 (places.display s) k + 1 := by
      rw [hdisp, ground.getAt_map 0 0 (fun x => x + 1)
        (places.display s) k
        (by rw [places.length_display, hs]; exact hk)]
    rw [places.getAt_display c k (by rw [hc]; exact hk),
      places.getAt_display s k (by rw [hs]; exact hk), hc, hs] at he
    rw [ground.getAt_map 0 0 (fun x => x + 1) (places.rowList s) k
      (by rw [places.length_rowList, hs]; exact hk)]
    refine ground.addCancelR (d - k) ?_
    rw [he, Nat.add_right_comm (ground.getAt 0 (places.rowList s) k)
      (d - k) 1]

/-- The head candidate: a raised display names the raised row
list's own shape. -/
private theorem head_mem (d : Nat) (s c : Shape)
    (hs : s.length = d) (hc : c.length = d)
    (hdisp : places.display c = (places.display s).map (fun x => x + 1)) :
    c ∈ adjCands d s := by
  have hcs : places.shapeOf ((places.rowList s).map (fun x => x + 1))
      = c := by
    rw [← rowList_of_raise d s c hs hc hdisp, places.shapeOf_rowList c]
  rw [← hcs]
  exact List.Mem.head _

/-- A letter-pair tie at the identity reads the raise-lower
survivor: the staircase cancels and the content's three places
land on the raised row list. -/
private theorem rowList_of_move (d : Nat) (s c : Shape) (m : List Nat)
    (hs : s.length = d) (hc : c.length = d)
    (i j : Nat) (hi : i < d) (hj : j < d) (hij : ¬ i = j)
    (h2 : ground.getAt 0 m i = 2) (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < d → ¬ k = i → ¬ k = j → ground.getAt 0 m k = 1)
    (hent : ∀ t, t < d →
      ground.getAt 0 m t + ground.getAt 0 (places.display s) t
        = ground.getAt 0 (places.display c) t) :
    places.rowList c
      = ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))) := by
  have hr1len : ((places.rowList s).map (fun x => x + 1)).length = d := by
    rw [ground.length_map, places.length_rowList, hs]
  have hr1 := getAt_raise d s hs
  have hrow : ∀ k, k < d →
      ground.getAt 0 (places.rowList c) k
        = ground.getAt 0 m k + ground.getAt 0 (places.rowList s) k := by
    intro k hk
    have he := hent k hk
    rw [places.getAt_display s k (by rw [hs]; exact hk),
      places.getAt_display c k (by rw [hc]; exact hk), hs, hc,
      ← Nat.add_assoc (ground.getAt 0 m k)
        (ground.getAt 0 (places.rowList s) k) (d - k)] at he
    exact (ground.addCancelR (d - k) he).symm
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [places.length_rowList, ground.length_dipAt, ground.length_bumpAt,
      hr1len, hc]
  · intro k hk
    rw [places.length_rowList, hc] at hk
    rw [hrow k hk]
    by_cases hkj : k = j
    · rw [hkj, h0, Nat.zero_add,
        ground.getAt_dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))),
        ground.getAt_bumpAt_ne i ((places.rowList s).map (fun x => x + 1))
          j (fun he => hij he.symm),
        hr1 j hj,
        ground.addSubSelfR (ground.getAt 0 (places.rowList s) j) 1]
    · rw [ground.getAt_dipAt_ne j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))) k hkj]
      by_cases hki : k = i
      · rw [hki, h2,
          ground.getAt_bumpAt_self i
            ((places.rowList s).map (fun x => x + 1))
            (by rw [hr1len]; exact hi),
          hr1 i hi,
          Nat.add_comm 2 (ground.getAt 0 (places.rowList s) i)]
      · rw [ground.getAt_bumpAt_ne i
            ((places.rowList s).map (fun x => x + 1)) k hki,
          hr1 k hk, h1 k hk hki hkj,
          Nat.add_comm 1 (ground.getAt 0 (places.rowList s) k)]

/-- The raise-lower survivor is a candidate: the row list's own
descent keeps the slot and the pair's places name it. -/
private theorem move_mem (d : Nat) (s c : Shape)
    (i j : Nat) (hi : i < d) (hj : j < d) (hij : ¬ i = j)
    (hrl : places.rowList c
      = ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1)))) :
    c ∈ adjCands d s := by
  have hdesc : descB (ground.dipAt j (ground.bumpAt i
      ((places.rowList s).map (fun x => x + 1)))) = true := by
    rw [← hrl]
    refine descB_of_desc (places.rowList c) ?_
    intro k hk
    rw [places.length_rowList] at hk
    exact places.rowList_le c k hk
  have hshape : places.shapeOf (ground.dipAt j (ground.bumpAt i
      ((places.rowList s).map (fun x => x + 1)))) = c := by
    rw [← hrl, places.shapeOf_rowList c]
  refine List.Mem.tail _ ?_
  refine ground.mem_flatMap_to _ (a := i) ?_ ?_
  · exact ground.memRange hi
  · refine ground.mem_filterMap_to _ (a := j) ?_ ?_
    · exact ground.memRange hj
    · have hb : (i == j) = false := ground.neBeqOf hij
      show (if i == j then (none : Option Shape)
        else if descB (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))))
          then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1)))))
          else none) = some c
      rw [hb]
      show (if descB (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))))
          then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1)))))
          else none) = some c
      rw [if_pos hdesc, hshape]

/-- A slot's emission names its pair: the refused diagonal, the
kept descent and the survivor's own shape. -/
private theorem slot_reads (s : Shape) (i j : Nat) (c : Shape)
    (h : (if i == j then (none : Option Shape)
      else if descB (ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))))
        then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1)))))
        else none) = some c) :
    ¬ i = j
      ∧ places.rowList c
        = ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))) := by
  by_cases hij : i = j
  · have hb : (i == j) = true := ground.eqBeqOf hij
    rw [hb] at h
    exact nomatch (show (none : Option Shape) = some c from h)
  · have hb : (i == j) = false := ground.neBeqOf hij
    rw [hb] at h
    have h' : (if descB (ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))))
        then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1)))))
        else none) = some c := h
    by_cases hdb : descB (ground.dipAt j (ground.bumpAt i
        ((places.rowList s).map (fun x => x + 1)))) = true
    · rw [if_pos hdb] at h'
      refine ⟨hij, ?_⟩
      rw [← Option.some.inj h']
      exact places.rowList_shapeOf _ (desc_of_descB _ hdb)
    · rw [if_neg hdb] at h'
      exact nomatch (show (none : Option Shape) = some c from h')

/-- A survivor's slot is its own: the raised key and the lowered
key read the pair back. -/
private theorem move_slot (d : Nat) (s : Shape) (hs : s.length = d)
    (i j i' j' : Nat) (hi : i < d) (hj : j < d) (hij : ¬ i = j)
    (hi' : i' < d) (hj' : j' < d) (hij' : ¬ i' = j')
    (heq : ground.dipAt j (ground.bumpAt i
        ((places.rowList s).map (fun x => x + 1)))
      = ground.dipAt j' (ground.bumpAt i'
        ((places.rowList s).map (fun x => x + 1)))) :
    i = i' ∧ j = j' := by
  have hr1len : ((places.rowList s).map (fun x => x + 1)).length = d := by
    rw [ground.length_map, places.length_rowList, hs]
  have hr1 := getAt_raise d s hs
  have hself : ∀ a b : Nat, a < d → ¬ a = b →
      ground.getAt 0 (ground.dipAt b (ground.bumpAt a
          ((places.rowList s).map (fun x => x + 1)))) a
        = ground.getAt 0 (places.rowList s) a + 1 + 1 := by
    intro a b ha hab
    rw [ground.getAt_dipAt_ne b (ground.bumpAt a
        ((places.rowList s).map (fun x => x + 1))) a hab,
      ground.getAt_bumpAt_self a ((places.rowList s).map (fun x => x + 1))
        (by rw [hr1len]; exact ha),
      hr1 a ha]
  have hlow : ∀ a b : Nat, b < d → ¬ a = b →
      ground.getAt 0 (ground.dipAt b (ground.bumpAt a
          ((places.rowList s).map (fun x => x + 1)))) b
        = ground.getAt 0 (places.rowList s) b := by
    intro a b hb hab
    rw [ground.getAt_dipAt b (ground.bumpAt a
        ((places.rowList s).map (fun x => x + 1))),
      ground.getAt_bumpAt_ne a ((places.rowList s).map (fun x => x + 1)) b
        (fun he => hab he.symm),
      hr1 b hb,
      ground.addSubSelfR (ground.getAt 0 (places.rowList s) b) 1]
  have hother : ∀ a b k : Nat, k < d → ¬ k = a → ¬ k = b →
      ground.getAt 0 (ground.dipAt b (ground.bumpAt a
          ((places.rowList s).map (fun x => x + 1)))) k
        = ground.getAt 0 (places.rowList s) k + 1 := by
    intro a b k hk hka hkb
    rw [ground.getAt_dipAt_ne b (ground.bumpAt a
        ((places.rowList s).map (fun x => x + 1))) k hkb,
      ground.getAt_bumpAt_ne a ((places.rowList s).map (fun x => x + 1))
        k hka,
      hr1 k hk]
  have hii : i = i' := by
    by_cases hc : i = i'
    · exact hc
    · have h2 : ground.getAt 0 (ground.dipAt j' (ground.bumpAt i'
          ((places.rowList s).map (fun x => x + 1)))) i
          ≤ ground.getAt 0 (places.rowList s) i + 1 := by
        by_cases hc2 : i = j'
        · rw [hc2, hlow i' j' hj' hij']
          exact Nat.le_succ _
        · rw [hother i' j' i hi hc hc2]
          exact Nat.le_refl _
      have h1 : ground.getAt 0 (ground.dipAt j' (ground.bumpAt i'
          ((places.rowList s).map (fun x => x + 1)))) i
          = ground.getAt 0 (places.rowList s) i + 1 + 1 := by
        rw [← heq]
        exact hself i j hi hij
      exact absurd (Nat.le_trans (Nat.le_of_eq h1.symm) h2)
        (Nat.lt_irrefl _)
  have hjj : j = j' := by
    by_cases hc : j = j'
    · exact hc
    · have h2 : ground.getAt 0 (places.rowList s) j + 1
          ≤ ground.getAt 0 (ground.dipAt j' (ground.bumpAt i'
            ((places.rowList s).map (fun x => x + 1)))) j := by
        by_cases hc2 : j = i'
        · rw [hc2, hself i' j' hi' hij']
          exact Nat.le_succ _
        · rw [hother i' j' j hj hc2 hc]
          exact Nat.le_refl _
      have h1 : ground.getAt 0 (ground.dipAt j' (ground.bumpAt i'
          ((places.rowList s).map (fun x => x + 1)))) j
          = ground.getAt 0 (places.rowList s) j := by
        rw [← heq]
        exact hlow i j hj hij
      exact absurd (Nat.le_trans h2 (Nat.le_of_eq h1)) (Nat.lt_irrefl _)
  exact ⟨hii, hjj⟩

/-- The raised row list is no survivor: the raised key parts
them. -/
private theorem head_ne_move (d : Nat) (s : Shape) (hs : s.length = d)
    (i j : Nat) (hi : i < d) (hij : ¬ i = j)
    (heq : (places.rowList s).map (fun x => x + 1)
      = ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1)))) : False := by
  have hr1len : ((places.rowList s).map (fun x => x + 1)).length = d := by
    rw [ground.length_map, places.length_rowList, hs]
  have hr1 := getAt_raise d s hs
  have h1 : ground.getAt 0 ((places.rowList s).map (fun x => x + 1)) i
      = ground.getAt 0 (ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1)))) i :=
    congrArg (fun l => ground.getAt 0 l i) heq
  rw [hr1 i hi,
    ground.getAt_dipAt_ne j (ground.bumpAt i
      ((places.rowList s).map (fun x => x + 1))) i hij,
    ground.getAt_bumpAt_self i ((places.rowList s).map (fun x => x + 1))
      (by rw [hr1len]; exact hi),
    hr1 i hi] at h1
  have hlt : ground.getAt 0 (places.rowList s) i + 1
      < ground.getAt 0 (places.rowList s) i + 1 + 1 := Nat.lt_succ_self _
  rw [← h1] at hlt
  exact Nat.lt_irrefl _ hlt

/-- An occupied survivor count names its pair: the places, their
refused diagonal and the moved raised row list. -/
private theorem move_of_count (d : Nat) (s c : Shape)
    (hp : 0 < ground.countOf c (moveCands d s)) :
    ∃ i j, i < d ∧ j < d ∧ ¬ i = j
      ∧ places.rowList c = ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))) := by
  have hcnt : 0 < ground.countOf c
      ((List.range d).flatMap (fun i =>
        (List.range d).filterMap (fun j =>
          if i == j then none
          else if descB (ground.dipAt j (ground.bumpAt i
              ((places.rowList s).map (fun x => x + 1))))
            then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
              ((places.rowList s).map (fun x => x + 1)))))
            else none))) := hp
  rw [ground.countOf_flatMap] at hcnt
  obtain ⟨i, hicnt, hif⟩ := ground.famFold_pos_witness _ (List.range d) hcnt
  have hi : i < d := by
    by_cases hlt : i < d
    · exact hlt
    · rw [ground.countOf_range i d, if_neg hlt] at hicnt
      exact absurd hicnt (Nat.lt_irrefl 0)
  obtain ⟨j, hjcnt, hjf⟩ := ground.filterMap_pre _ (List.range d) c hif
  have hj : j < d := by
    by_cases hlt : j < d
    · exact hlt
    · rw [ground.countOf_range j d, if_neg hlt] at hjcnt
      exact absurd hjcnt (Nat.lt_irrefl 0)
  obtain ⟨hij, hrl⟩ := slot_reads s i j c hjf
  exact ⟨i, j, hi, hj, hij, hrl⟩

/-- Every candidate is a matched-degree shape of the stated width:
the raised row list and each survivor read one degree. -/
private theorem cand_reads (d : Nat) (s c : Shape) (hs : s.length = d)
    (hpos : 0 < ground.countOf c (adjCands d s)) :
    c.length = d ∧ places.degree c = places.degree s + d := by
  have hr1len : ((places.rowList s).map (fun x => x + 1)).length = d := by
    rw [ground.length_map, places.length_rowList, hs]
  have hr1 := getAt_raise d s hs
  have hcnt : 0 < ground.countOf c
      (places.shapeOf ((places.rowList s).map (fun x => x + 1))
        :: moveCands d s) := hpos
  rw [ground.countOf_cons] at hcnt
  by_cases hch : c = places.shapeOf
      ((places.rowList s).map (fun x => x + 1))
  · refine ⟨?_, ?_⟩
    · rw [hch, places.length_shapeOf, hr1len]
    · show ground.sumNat (places.rowList c) = places.degree s + d
      rw [hch, places.rowList_shapeOf _ (raise_desc s), sumNat_raise s, hs]
  · rw [if_neg hch, Nat.zero_add] at hcnt
    obtain ⟨i, j, hi, hj, hij, hrl⟩ := move_of_count d s c hcnt
    have hocc : 0 < ground.getAt 0 (ground.bumpAt i
        ((places.rowList s).map (fun x => x + 1))) j := by
      rw [ground.getAt_bumpAt_ne i
        ((places.rowList s).map (fun x => x + 1)) j
        (fun he => hij he.symm), hr1 j hj]
      exact Nat.succ_pos _
    refine ⟨?_, ?_⟩
    · rw [← places.length_rowList c, hrl, ground.length_dipAt,
        ground.length_bumpAt, hr1len]
    · have hsum : ground.sumNat (ground.dipAt j (ground.bumpAt i
          ((places.rowList s).map (fun x => x + 1))))
          = ground.sumNat ((places.rowList s).map (fun x => x + 1)) := by
        refine ground.addCancelR 1 ?_
        rw [ground.sumNat_dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))) hocc,
          ground.sumNat_bumpAt i ((places.rowList s).map (fun x => x + 1))
            (by rw [hr1len]; exact hi)]
      show ground.sumNat (places.rowList c) = places.degree s + d
      rw [hrl, hsum, sumNat_raise s, hs]

/-- The candidates are listed once each: the head's own raise
refuses every survivor and the moved keys read the pair back. -/
private theorem countOf_cands_le (d : Nat) (s : Shape) (hs : s.length = d)
    (c : Shape) : ground.countOf c (adjCands d s) ≤ 1 := by
  have hpre : ∀ i : Nat, i < d →
      0 < ground.countOf c ((List.range d).filterMap (fun j =>
        if i == j then none
        else if descB (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))))
          then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1)))))
          else none)) →
      ∃ j, j < d ∧ ¬ i = j ∧ places.rowList c
        = ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))) := by
    intro i _ hp
    obtain ⟨j, hjcnt, hjf⟩ := ground.filterMap_pre _ (List.range d) c hp
    have hj : j < d := by
      by_cases hlt : j < d
      · exact hlt
      · rw [ground.countOf_range j d, if_neg hlt] at hjcnt
        exact absurd hjcnt (Nat.lt_irrefl 0)
    obtain ⟨hij, hrl⟩ := slot_reads s i j c hjf
    exact ⟨j, hj, hij, hrl⟩
  have hmem : ∀ i : Nat, 0 < ground.countOf i (List.range d) → i < d := by
    intro i hic
    by_cases hlt : i < d
    · exact hlt
    · rw [ground.countOf_range i d, if_neg hlt] at hic
      exact absurd hic (Nat.lt_irrefl 0)
  have hinner : ∀ i : Nat, i < d →
      ground.countOf c ((List.range d).filterMap (fun j =>
        if i == j then none
        else if descB (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1))))
          then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
            ((places.rowList s).map (fun x => x + 1)))))
          else none)) ≤ 1 := by
    intro i hi
    refine countOf_filterMap_le_one _ c _
      (fun a => ground.distinctList_all (ground.distinctList_range d) a) ?_
    intro j j' hjc hjc' hfj hfj'
    obtain ⟨hij, hrl⟩ := slot_reads s i j c hfj
    obtain ⟨hij', hrl'⟩ := slot_reads s i j' c hfj'
    exact (move_slot d s hs i j i j' hi (hmem j hjc) hij hi
      (hmem j' hjc') hij' (hrl.symm.trans hrl')).2
  show ground.countOf c
      (places.shapeOf ((places.rowList s).map (fun x => x + 1))
        :: (List.range d).flatMap (fun i =>
          (List.range d).filterMap (fun j =>
            if i == j then none
            else if descB (ground.dipAt j (ground.bumpAt i
                ((places.rowList s).map (fun x => x + 1))))
              then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
                ((places.rowList s).map (fun x => x + 1)))))
              else none))) ≤ 1
  rw [ground.countOf_cons, ground.countOf_flatMap]
  by_cases hch : c = places.shapeOf
      ((places.rowList s).map (fun x => x + 1))
  · have hrh : places.rowList c
        = (places.rowList s).map (fun x => x + 1) := by
      rw [hch]
      exact places.rowList_shapeOf _ (raise_desc s)
    have hz : ground.famFold Nat.add 0
        (fun i => ground.countOf c ((List.range d).filterMap (fun j =>
          if i == j then none
          else if descB (ground.dipAt j (ground.bumpAt i
              ((places.rowList s).map (fun x => x + 1))))
            then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
              ((places.rowList s).map (fun x => x + 1)))))
            else none))) (List.range d) = 0 := by
      refine ground.famFold_null_ov ground.natFoldLaws _ (List.range d) ?_
      intro i hic
      match Nat.eq_zero_or_pos (ground.countOf c
          ((List.range d).filterMap (fun j =>
            if i == j then none
            else if descB (ground.dipAt j (ground.bumpAt i
                ((places.rowList s).map (fun x => x + 1))))
              then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
                ((places.rowList s).map (fun x => x + 1)))))
              else none))) with
      | .inl h0 => exact h0
      | .inr hp =>
        obtain ⟨j, hj, hij, hrl⟩ := hpre i (hmem i hic) hp
        exact absurd (hrh.symm.trans hrl)
          (fun he => head_ne_move d s hs i j (hmem i hic) hij he)
    rw [if_pos hch, hz]
    exact Nat.le_refl 1
  · rw [if_neg hch, Nat.zero_add]
    match Nat.eq_zero_or_pos (ground.famFold Nat.add 0
        (fun i => ground.countOf c ((List.range d).filterMap (fun j =>
          if i == j then none
          else if descB (ground.dipAt j (ground.bumpAt i
              ((places.rowList s).map (fun x => x + 1))))
            then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
              ((places.rowList s).map (fun x => x + 1)))))
            else none))) (List.range d)) with
    | .inl h0 =>
      rw [h0]
      exact Nat.zero_le 1
    | .inr hp =>
      obtain ⟨i0, hi0c, hi0f⟩ :=
        ground.famFold_pos_witness _ (List.range d) hp
      obtain ⟨j0, hj0, hij0, hrl0⟩ := hpre i0 (hmem i0 hi0c) hi0f
      refine ground.famFold_le_one_at _ i0 (List.range d) ?_
        (hinner i0 (hmem i0 hi0c))
        (ground.distinctList_all (ground.distinctList_range d) i0)
      intro i hic hii
      match Nat.eq_zero_or_pos (ground.countOf c
          ((List.range d).filterMap (fun j =>
            if i == j then none
            else if descB (ground.dipAt j (ground.bumpAt i
                ((places.rowList s).map (fun x => x + 1))))
              then some (places.shapeOf (ground.dipAt j (ground.bumpAt i
                ((places.rowList s).map (fun x => x + 1)))))
              else none))) with
      | .inl h0 => exact h0
      | .inr hpi =>
        obtain ⟨j, hj, hij, hrl⟩ := hpre i (hmem i hic) hpi
        exact absurd (move_slot d s hs i j i0 j0 (hmem i hic) hj hij
          (hmem i0 hi0c) hj0 hij0 (hrl.symm.trans hrl0)).1 hii

/-- A positively counted matched-degree shape is a candidate: the
occupied gap names a contributing permutation whose content is the
all-ones list or a letter-pair move, and the three arms read the
raised row list or the raise-lower survivor at the pair's own
places. -/
private theorem mem_adjCands (d : Nat) (s c : Shape)
    (hs : s.length = d) (hc : c.length = d)
    (hpos : 0 < (steinberg.sumsWith (adjchar.multRead d) d s c).1) :
    c ∈ adjCands d s := by
  have hdl : (places.display s).length = d := by
    rw [places.length_display, hs]
  have hcdl : (places.display c).length = d := by
    rw [places.length_display, hc]
  have hfst : (steinberg.sumsWith (adjchar.multRead d) d s c).1
      = ground.famFold Nat.add 0
        (fun p => if places.parity p = false then
          weylchar.multAtGap (adjchar.multRead d) (places.display c)
            (places.expo (places.display s) p)
        else 0) (places.perms d) := by
    rw [steinberg.sumsWith_split (adjchar.multRead d) d s c]
  rw [hfst] at hpos
  obtain ⟨p, hp, hgp⟩ := ground.famFold_pos_witness _ (places.perms d) hpos
  have hgp' : 0 < (if places.parity p = false then
      weylchar.multAtGap (adjchar.multRead d) (places.display c)
        (places.expo (places.display s) p)
    else 0) := hgp
  have hpar : places.parity p = false := by
    by_cases hb : places.parity p = false
    · exact hb
    · rw [if_neg hb] at hgp'
      exact absurd hgp' (Nat.lt_irrefl 0)
  rw [if_pos hpar] at hgp'
  obtain ⟨m, hg, hmpos⟩ :=
    weylchar.multAtGap_pos (adjchar.multRead d) _ _ hgp'
  cases adjchar.multRead_cases d m hmpos with
  | inl harm =>
    exact head_mem d s c hs hc
      (places.tieOnes d s c hs p hp m hg harm.2.1).2
  | inr harm =>
    obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
    by_cases hpr : p = List.range d
    · have hexpo : places.expo (places.display s) (List.range d)
          = places.display s :=
        ground.range_map_getAt 0 d (places.display s) hdl
      rw [hpr, hexpo] at hg
      obtain ⟨_, _, hent⟩ := ground.tieGap_reads _ _ _ hg
      refine move_mem d s c i j hi hj hij ?_
      refine rowList_of_move d s c m hs hc i j hi hj hij h2 h0 h1 ?_
      intro t ht
      exact hent t (by rw [hcdl]; exact ht)
    · obtain ⟨_, _, _, _, hdisp⟩ :=
        places.tieMove d s c hs p hp hpr m hg i j h2 h0 h1
      exact head_mem d s c hs hc hdisp

/-- The permuted zip's entry at the join: the tie's constructor. -/
private theorem tieGap_intro : ∀ (m z : List Nat),
    m.length = z.length →
    ground.tieGap (List.zipWith (fun a b => a + b) m z) z = some m
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | a :: m, b :: z, h => by
    show (if b ≤ a + b then
        match ground.tieGap (List.zipWith (fun a b => a + b) m z) z with
        | some mm => some ((a + b - b) :: mm)
        | none => none
      else none) = some (a :: m)
    rw [if_pos (Nat.le_add_left b a), tieGap_intro m z (Nat.succ.inj h),
      ground.addSubSelfR a b]

/-- The zip's entry read at a key inside both lists. -/
private theorem getAt_zip_add : ∀ (u v : List Nat) (k : Nat),
    k < u.length → k < v.length →
    ground.getAt 0 (List.zipWith (fun a b => a + b) u v) k
      = ground.getAt 0 u k + ground.getAt 0 v k
  | [], _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], k, _, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: u, _ :: v, k + 1, hu, hv =>
    getAt_zip_add u v k (Nat.lt_of_succ_lt_succ hu)
      (Nat.lt_of_succ_lt_succ hv)

/-- The full-column bump's row list is the raised one. -/
private theorem rowList_bumpLast : ∀ (s : Shape) (n : Nat),
    s.length = n + 1 →
    places.rowList (ground.bumpAt n s)
      = (places.rowList s).map (fun x => x + 1)
  | [], _, h => Nat.noConfusion h
  | [_], 0, _ => rfl
  | [_], n + 1, h => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, 0, h =>
    Nat.noConfusion (Nat.succ.inj h)
  | a :: b :: t, n + 1, h => by
    show (a + ground.sumNat (ground.bumpAt n (b :: t)))
        :: places.rowList (ground.bumpAt n (b :: t))
      = (a + ground.sumNat (b :: t) + 1)
        :: (places.rowList (b :: t)).map (fun x => x + 1)
    rw [rowList_bumpLast (b :: t) n (Nat.succ.inj h),
      ground.sumNat_bumpAt n (b :: t)
        (by rw [Nat.succ.inj h]; exact Nat.lt_succ_self n),
      ← Nat.add_assoc a (ground.sumNat (b :: t)) 1]

/-- The head candidate is the full-column bump. -/
private theorem head_eq_bump (d : Nat) (s : Shape) (hs : s.length = d)
    (hd1 : 1 ≤ d) :
    places.shapeOf ((places.rowList s).map (fun x => x + 1))
      = ground.bumpAt (d - 1) s := by
  have h1 : d - 1 + 1 = d := ground.subAdd hd1
  rw [← rowList_bumpLast s (d - 1) (by rw [hs]; exact h1.symm)]
  exact places.shapeOf_rowList _

/-- The gap of a sum against itself extended reads the unit. -/
private theorem sub_add_zero : ∀ (a k : Nat), a - (a + k) = 0
  | 0, k => by
    rw [Nat.zero_add]
    exact Nat.zero_sub k
  | a + 1, k => by
    rw [Nat.add_right_comm a 1 k, Nat.succ_sub_succ]
    exact sub_add_zero a k

/-- A survivor's fast count is occupied: the identity's own tie at
the letter-pair content with every further permutation's tie at the
raised display alone. -/
private theorem survivor_pos (d : Nat) (s c : Shape)
    (hs : s.length = d)
    (hmc : 0 < ground.countOf c (moveCands d s)) :
    0 < channels.adjCount d s c := by
  obtain ⟨i, j, hi, hj, hij, hrl⟩ := move_of_count d s c hmc
  have hd1 : 1 ≤ d := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hr1len : ((places.rowList s).map (fun x => x + 1)).length = d := by
    rw [ground.length_map, places.length_rowList, hs]
  have hr1 := getAt_raise d s hs
  have hcl : c.length = d := by
    rw [← places.length_rowList c, hrl, ground.length_dipAt,
      ground.length_bumpAt, hr1len]
  have hdl : (places.display s).length = d := by
    rw [places.length_display, hs]
  have hcdl : (places.display c).length = d := by
    rw [places.length_display, hcl]
  have hbl : places.rowList (ground.bumpAt (d - 1) s)
      = (places.rowList s).map (fun x => x + 1) :=
    rowList_bumpLast s (d - 1)
      (by rw [hs, ground.subAdd hd1])
  have hne : ¬ c = ground.bumpAt (d - 1) s := by
    intro he
    rw [he, hbl] at hrl
    have h3 := congrArg (fun l => ground.getAt 0 l i) hrl
    rw [ground.getAt_dipAt_ne j (ground.bumpAt i
        ((places.rowList s).map (fun x => x + 1))) i hij,
      ground.getAt_bumpAt_self i
        ((places.rowList s).map (fun x => x + 1))
        (by rw [hr1len]; exact hi)] at h3
    exact absurd h3 (Nat.ne_of_lt (Nat.lt_succ_self _))
  have hmlen : (blockcount.moveAt i j (List.replicate d 1)).length
      = d := by
    rw [blockcount.length_moveAt, ground.length_replicate]
  have hm2 : ground.getAt 0 (blockcount.moveAt i j (List.replicate d 1))
      i = 2 := by
    rw [blockcount.getAt_moveAt_fst i j _ hij
        (by rw [ground.length_replicate]; exact hi),
      ground.getAt_replicate 0 1 d i hi]
  have hm0 : ground.getAt 0 (blockcount.moveAt i j (List.replicate d 1))
      j = 0 := by
    have h := blockcount.getAt_moveAt_snd i j (List.replicate d 1) hij
      (by rw [ground.getAt_replicate 0 1 d j hj]; exact Nat.succ_pos 0)
    rw [ground.getAt_replicate 0 1 d j hj] at h
    exact Nat.succ.inj h
  have hm1 : ∀ k, k < d → ¬ k = i → ¬ k = j →
      ground.getAt 0 (blockcount.moveAt i j (List.replicate d 1)) k
        = 1 := by
    intro k hk hki hkj
    rw [blockcount.getAt_moveAt_ne i j _ k hki hkj,
      ground.getAt_replicate 0 1 d k hk]
  obtain ⟨hc0, hc2, hc1⟩ := ground.countOf_pattern2
    (blockcount.moveAt i j (List.replicate d 1)) i j
    (by rw [hmlen]; exact hi) (by rw [hmlen]; exact hj) hij hm2 hm0
    (fun k hk => hm1 k (by rw [← hmlen]; exact hk))
  have hmr : adjchar.multRead d (blockcount.moveAt i j (List.replicate d 1))
      = 1 :=
    adjchar.multRead_move d _ hmlen hc0 hc2
      (by rw [hc1, hmlen])
  have hdisp : places.display c
      = List.zipWith (fun a b => a + b)
          (blockcount.moveAt i j (List.replicate d 1))
          (places.display s) := by
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [hcdl, ground.length_zipWith _ _ _ d hmlen hdl]
    · intro k hk
      rw [hcdl] at hk
      rw [getAt_zip_add _ _ k (by rw [hmlen]; exact hk)
          (by rw [hdl]; exact hk),
        places.getAt_display c k (by rw [hcl]; exact hk), hcl,
        places.getAt_display s k (by rw [hs]; exact hk), hs, hrl]
      by_cases hki : k = i
      · rw [hki, ground.getAt_dipAt_ne j _ i hij,
          ground.getAt_bumpAt_self i
            ((places.rowList s).map (fun x => x + 1))
            (by rw [hr1len]; exact hi),
          hr1 i hi, hm2,
          Nat.add_right_comm (ground.getAt 0 (places.rowList s) i
            + 1) 1 (d - i),
          Nat.add_right_comm (ground.getAt 0 (places.rowList s) i)
            1 (d - i),
          Nat.add_assoc (ground.getAt 0 (places.rowList s) i
            + (d - i)) 1 1,
          Nat.add_comm 2 (ground.getAt 0 (places.rowList s) i
            + (d - i))]
      · by_cases hkj : k = j
        · rw [hkj, ground.getAt_dipAt j _,
            ground.getAt_bumpAt_ne i _ j (fun he => hij he.symm),
            hr1 j hj,
            ground.addSubSelfR (ground.getAt 0
              (places.rowList s) j) 1,
            hm0, Nat.zero_add]
        · rw [ground.getAt_dipAt_ne j _ k hkj,
            ground.getAt_bumpAt_ne i _ k hki, hr1 k hk,
            hm1 k hk hki hkj,
            Nat.add_right_comm (ground.getAt 0 (places.rowList s) k)
              1 (d - k),
            Nat.add_comm (ground.getAt 0 (places.rowList s) k
              + (d - k)) 1]
  have htie : ground.tieGap (places.display c)
      (places.expo (places.display s) (List.range d))
      = some (blockcount.moveAt i j (List.replicate d 1)) := by
    show ground.tieGap (places.display c)
      ((List.range d).map (ground.getAt 0 (places.display s)))
      = some (blockcount.moveAt i j (List.replicate d 1))
    rw [ground.range_map_getAt 0 d (places.display s) hdl, hdisp]
    exact tieGap_intro _ (places.display s) (by rw [hmlen, hdl])
  have hsplit := steinberg.sumsWith_split (adjchar.multRead d) d s c
  have hzero2 : (steinberg.sumsWith (adjchar.multRead d) d s c).2
      = 0 := by
    rw [hsplit]
    refine ground.famFold_null_ov ground.natFoldLaws _
      (places.perms d) ?_
    intro p hp
    by_cases hpar : places.parity p = true
    · rw [if_pos hpar]
      have hpne : ¬ p = List.range d := by
        intro he
        rw [he, places.parity_range d] at hpar
        exact Bool.noConfusion hpar
      exact offVanish d s c hs hne p hp hpne
    · rw [if_neg hpar]
  have hpos1 : 0 < (steinberg.sumsWith (adjchar.multRead d) d s c).1
      := by
    rw [hsplit]
    show 0 < ground.famFold Nat.add 0
      (fun p => if places.parity p = false then
        weylchar.multAtGap (adjchar.multRead d) (places.display c)
          (places.expo (places.display s) p)
      else 0) (places.perms d)
    rw [ground.famFold_eraseFirst Nat.add 0
      (fun x y => Nat.add_comm x y)
      (fun x y z => Nat.add_assoc x y z) _ (places.perms d)
      (List.range d)
      (by rw [places.countRangePerms d]; exact Nat.succ_pos 0)]
    have hval : (if places.parity (List.range d) = false then
        weylchar.multAtGap (adjchar.multRead d) (places.display c)
          (places.expo (places.display s) (List.range d))
      else 0) = 1 := by
      rw [if_pos (places.parity_range d)]
      show (match ground.tieGap (places.display c)
          (places.expo (places.display s) (List.range d)) with
        | some nu => adjchar.multRead d nu
        | none => 0) = 1
      rw [htie]
      exact hmr
    rw [hval]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
  show 0 < (steinberg.sumsWith (adjchar.multRead d) d s c).1
    - (steinberg.sumsWith (adjchar.multRead d) d s c).2
  rw [hzero2]
  exact hpos1

/-- A joined comparison's gap: the pair identity at a lower
first weight reads the occupied difference. -/
private theorem join_pos (X Y C D : Nat) (hj : X + C = Y + D)
    (h : C < D) : 0 < X - Y := by
  obtain ⟨g, hg⟩ := Nat.le.dest h
  rw [← hg, Nat.add_assoc C 1 g, Nat.add_comm C (1 + g),
    ← Nat.add_assoc Y (1 + g) C] at hj
  have h1 := ground.addCancelR C hj
  rw [h1, Nat.add_comm Y (1 + g), ground.addSubSelfR (1 + g) Y]
  exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 g)

/-- A joined comparison's gap at a covered first weight reads the
unit. -/
private theorem join_zero (X Y C D : Nat) (hj : X + C = Y + D)
    (h : D ≤ C) : X - Y = 0 := by
  obtain ⟨e, he⟩ := Nat.le.dest h
  rw [← he, ← Nat.add_assoc X D e, Nat.add_right_comm X D e] at hj
  have h1 := ground.addCancelR D hj
  rw [← h1]
  exact sub_add_zero X e

/-- The head's fast count is occupied exactly off the full clear:
the diagonal join at the gap read. -/
private theorem head_pos (d : Nat) (s : Shape) (hs : s.length = d)
    (h : clearGaps (places.display s) < d - 1) :
    0 < channels.adjCount d s (ground.bumpAt (d - 1) s) :=
  join_pos _ _ _ _ (diagJoin d s hs) h

/-- The head's fast count reads the unit at the full clear. -/
private theorem head_zero (d : Nat) (s : Shape) (hs : s.length = d)
    (h : ¬ clearGaps (places.display s) < d - 1) :
    channels.adjCount d s (ground.bumpAt (d - 1) s) = 0 := by
  have hle : d - 1 ≤ clearGaps (places.display s) := by
    cases Nat.lt_or_ge (clearGaps (places.display s)) (d - 1) with
    | inl hlt => exact absurd hlt h
    | inr hge => exact hge
  exact join_zero _ _ _ _ (diagJoin d s hs) hle

/-- The keyed image's occupied head: one emission at the stated
value. -/
private theorem filterMap_cons_some {α β : Type} (F : α → Option β)
    (a : α) (t : List α) (b : β) (hf : F a = some b) :
    (a :: t).filterMap F = b :: t.filterMap F := by
  show (match F a with
        | none => t.filterMap F
        | some c => c :: t.filterMap F) = b :: t.filterMap F
  rw [hf]

/-- The keyed image's refused head: the tail's own image. -/
private theorem filterMap_cons_none {α β : Type} (F : α → Option β)
    (a : α) (t : List α) (hf : F a = none) :
    (a :: t).filterMap F = t.filterMap F := by
  show (match F a with
        | none => t.filterMap F
        | some c => c :: t.filterMap F) = t.filterMap F
  rw [hf]

/-- A filter passing at every occupied member reads the map. -/
private theorem filterMap_pos_map (d : Nat) (s : Shape) :
    ∀ l : List Shape,
    (∀ c, 0 < ground.countOf c l → 0 < channels.adjCount d s c) →
    l.filterMap (fun c => if 0 < channels.adjCount d s c
        then some (labels.reduce c) else none)
      = l.map (fun c => labels.reduce c)
  | [], _ => rfl
  | a :: t, h => by
    have ha : 0 < channels.adjCount d s a :=
      h a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    rw [filterMap_cons_some (fun c =>
        if 0 < channels.adjCount d s c
        then some (labels.reduce c) else none) a t
        (labels.reduce a) (if_pos ha),
      filterMap_pos_map d s t
        (fun c hc => h c (ground.countOf_cons_pos hc))]
    rfl

/-- The row's filter spelling: the closed reads against the fast
count, the diagonal at the gap read and each survivor occupied. -/
private theorem adjRow_filter (d : Nat) (s : Shape)
    (hs : s.length = d) (hd : 2 ≤ d) :
    adjRow d s = (adjCands d s).filterMap (fun c =>
      if 0 < channels.adjCount d s c then some (labels.reduce c)
      else none) := by
  have hd1 : 1 ≤ d := Nat.le_trans (Nat.le_succ 1) hd
  have hhb : channels.adjCount d s
      (places.shapeOf ((places.rowList s).map (fun x => x + 1)))
      = channels.adjCount d s (ground.bumpAt (d - 1) s) := by
    rw [head_eq_bump d s hs hd1]
  have hmap := filterMap_pos_map d s (moveCands d s)
    (fun c hc => survivor_pos d s c hs hc)
  show (if clearGaps (places.display s) < d - 1
      then [labels.reduce (ground.bumpAt (d - 1) s)] else [])
    ++ (moveCands d s).map (fun c => labels.reduce c)
    = (places.shapeOf ((places.rowList s).map (fun x => x + 1))
        :: moveCands d s).filterMap (fun c =>
      if 0 < channels.adjCount d s c then some (labels.reduce c)
      else none)
  by_cases hcg : clearGaps (places.display s) < d - 1
  · have hhp : 0 < channels.adjCount d s
        (places.shapeOf ((places.rowList s).map (fun x => x + 1)))
      := by
      rw [hhb]
      exact head_pos d s hs hcg
    rw [filterMap_cons_some (fun c =>
        if 0 < channels.adjCount d s c
        then some (labels.reduce c) else none)
        (places.shapeOf ((places.rowList s).map (fun x => x + 1)))
        (moveCands d s)
        (labels.reduce (places.shapeOf
          ((places.rowList s).map (fun x => x + 1))))
        (if_pos hhp),
      hmap, if_pos hcg, head_eq_bump d s hs hd1]
    rfl
  · have hhz : (if 0 < channels.adjCount d s
        (places.shapeOf ((places.rowList s).map (fun x => x + 1)))
        then some (labels.reduce (places.shapeOf
          ((places.rowList s).map (fun x => x + 1)))) else none)
        = none := by
      rw [hhb, head_zero d s hs hcg]
      exact if_neg (Nat.lt_irrefl 0)
    rw [filterMap_cons_none (fun c =>
        if 0 < channels.adjCount d s c
        then some (labels.reduce c) else none)
        (places.shapeOf ((places.rowList s).map (fun x => x + 1)))
        (moveCands d s) hhz,
      hmap, if_neg hcg]
    rfl

/-- The definitional row reads the fast row at every label: the
matched-degree filterMap at the definitional count and the occupied
candidates' reduction hold one count at every shape. -/
theorem adjRow_eq (d : Nat) (s : Shape)
    (hs : s.length = d) (hd : 2 ≤ d) (x : Shape) :
    ground.countOf x
      ((places.allShapes d (places.degree s
          + places.degree (adjchar.theta d))).filterMap
        (fun c => if 0 < steinberg.count s (adjchar.theta d) c
          then some (labels.reduce c) else none))
      = ground.countOf x (adjRow d s) := by
  obtain ⟨e, he⟩ := Nat.le.dest hd
  have hde : d = e + 1 + 1 := by
    rw [← he, Nat.add_comm 2 e]
  have hdt : places.degree (adjchar.theta d) = d :=
    adjchar.degree_theta d hd
  have hinj : ∀ a b : Shape, a.length = d → b.length = d →
      places.degree a = places.degree s + d →
      places.degree b = places.degree s + d →
      labels.reduce a = labels.reduce b → a = b := by
    intro a b hal hbl hda hdb hr
    exact reduce_inj (e + 1) a b (by rw [hal, hde]) (by rw [hbl, hde])
      (by rw [hda, hdb]) hr
  have hLle : ground.countOf x
      ((places.allShapes d (places.degree s
          + places.degree (adjchar.theta d))).filterMap
        (fun c => if 0 < steinberg.count s (adjchar.theta d) c
          then some (labels.reduce c) else none)) ≤ 1 := by
    refine countOf_filterMap_le_one _ x _
      (fun a => places.countOf_allShapes_le d _ a) ?_
    intro a b ha hb hfa hfb
    have hfa' : (if 0 < steinberg.count s (adjchar.theta d) a
        then some (labels.reduce a) else none) = some x := hfa
    have hfb' : (if 0 < steinberg.count s (adjchar.theta d) b
        then some (labels.reduce b) else none) = some x := hfb
    obtain ⟨_, hxa⟩ := emit_reads hfa'
    obtain ⟨_, hxb⟩ := emit_reads hfb'
    obtain ⟨hal, hda⟩ := places.allShapes_sound d _ a
      (ground.mem_of_countOf_pos a _ ha)
    obtain ⟨hbl, hdb⟩ := places.allShapes_sound d _ b
      (ground.mem_of_countOf_pos b _ hb)
    exact hinj a b hal hbl (by rw [hda, hdt]) (by rw [hdb, hdt])
      (hxa.trans hxb.symm)
  have hRle : ground.countOf x (adjRow d s) ≤ 1 := by
    rw [adjRow_filter d s hs hd]
    refine countOf_filterMap_le_one _ x _
      (fun a => countOf_cands_le d s hs a) ?_
    intro a b ha hb hfa hfb
    have hfa' : (if 0 < channels.adjCount d s a
        then some (labels.reduce a) else none) = some x := hfa
    have hfb' : (if 0 < channels.adjCount d s b
        then some (labels.reduce b) else none) = some x := hfb
    obtain ⟨_, hxa⟩ := emit_reads hfa'
    obtain ⟨_, hxb⟩ := emit_reads hfb'
    obtain ⟨hal, hda⟩ := cand_reads d s a hs ha
    obtain ⟨hbl, hdb⟩ := cand_reads d s b hs hb
    exact hinj a b hal hbl hda hdb (hxa.trans hxb.symm)
  have hLR : 0 < ground.countOf x
      ((places.allShapes d (places.degree s
          + places.degree (adjchar.theta d))).filterMap
        (fun c => if 0 < steinberg.count s (adjchar.theta d) c
          then some (labels.reduce c) else none)) →
      0 < ground.countOf x (adjRow d s) := by
    intro hp
    rw [adjRow_filter d s hs hd]
    obtain ⟨c, hc, hfc⟩ := ground.filterMap_pre _
      (places.allShapes d (places.degree s
        + places.degree (adjchar.theta d))) x hp
    have hfc' : (if 0 < steinberg.count s (adjchar.theta d) c
        then some (labels.reduce c) else none) = some x := hfc
    obtain ⟨hcnt, hxc⟩ := emit_reads hfc'
    obtain ⟨hcl, _⟩ := places.allShapes_sound d _ c
      (ground.mem_of_countOf_pos c _ hc)
    have hfast : 0 < channels.adjCount d s c := by
      rw [← adjCount_eq d s c hs hcl hd]
      exact hcnt
    have hsum : 0 < (steinberg.sumsWith (adjchar.multRead d) d s c).1 := by
      have hf : 0 < (steinberg.sumsWith (adjchar.multRead d) d s c).1
          - (steinberg.sumsWith (adjchar.multRead d) d s c).2 := hfast
      exact Nat.lt_of_lt_of_le hf (Nat.sub_le _ _)
    refine ground.countOf_pos_of_mem ?_
    show x ∈ (adjCands d s).filterMap
      (fun c => if 0 < channels.adjCount d s c
        then some (labels.reduce c) else none)
    refine ground.mem_filterMap_to _ (mem_adjCands d s c hs hcl hsum) ?_
    show (if 0 < channels.adjCount d s c
      then some (labels.reduce c) else none) = some x
    rw [if_pos hfast, hxc]
  have hRL : 0 < ground.countOf x (adjRow d s) →
      0 < ground.countOf x
        ((places.allShapes d (places.degree s
            + places.degree (adjchar.theta d))).filterMap
          (fun c => if 0 < steinberg.count s (adjchar.theta d) c
            then some (labels.reduce c) else none)) := by
    intro hp
    rw [adjRow_filter d s hs hd] at hp
    obtain ⟨c, hc, hfc⟩ := ground.filterMap_pre _ (adjCands d s) x hp
    have hfc' : (if 0 < channels.adjCount d s c
        then some (labels.reduce c) else none) = some x := hfc
    obtain ⟨hcnt, hxc⟩ := emit_reads hfc'
    obtain ⟨hcl, hcd⟩ := cand_reads d s c hs hc
    have hdef : 0 < steinberg.count s (adjchar.theta d) c := by
      rw [adjCount_eq d s c hs hcl hd]
      exact hcnt
    have hmem : c ∈ places.allShapes d (places.degree s
        + places.degree (adjchar.theta d)) := by
      have h0 := places.mem_allShapes d c hcl
      rw [hcd, show places.degree s + d
        = places.degree s + places.degree (adjchar.theta d)
        from by rw [hdt]] at h0
      exact h0
    refine ground.countOf_pos_of_mem ?_
    refine ground.mem_filterMap_to _ hmem ?_
    show (if 0 < steinberg.count s (adjchar.theta d) c
      then some (labels.reduce c) else none) = some x
    rw [if_pos hdef, hxc]
  match Nat.eq_zero_or_pos (ground.countOf x (adjRow d s)) with
  | .inl hz =>
    match Nat.eq_zero_or_pos (ground.countOf x
        ((places.allShapes d (places.degree s
            + places.degree (adjchar.theta d))).filterMap
          (fun c => if 0 < steinberg.count s (adjchar.theta d) c
            then some (labels.reduce c) else none))) with
    | .inl hz' => rw [hz', hz]
    | .inr hp' =>
      exact absurd (hLR hp') (by rw [hz]; exact Nat.lt_irrefl 0)
  | .inr hp =>
    rw [Nat.le_antisymm hLle (hRL hp), Nat.le_antisymm hRle hp]

end rankstable
