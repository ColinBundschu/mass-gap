/-!
`def:ground` — the ground data are the positive naturals, generated
from one by the successor and closed under the sum and the product,
each injective in each argument.  The carrier stores the count of
successor steps from one on the kernel's accelerated naturals, a
term's value the stored count's successor: zero is unrepresentable
by the denotation's shape (every term denotes a successor), the
generation from one by the successor is the carrier's own recursion
(`peanoRec`, its step read `peanoRec_succ` definitional), and every
arithmetic read reduces in the kernel at machine integers, the
committed magnitudes' feasibility the check module's exhibits.  The
stored count stays private to this module (the linter's hygiene
clause); every consumer reads the displayed operations; and the
count-level kit is hand-rolled wherever the core lemma's proof
reads through `propext`, the axiom gate's floor.

Order is gap-existence: `a < b` is the existence of the gap `g` at
`a + g = b`, one value by the sum's injectivity, and `trich` is the
trichotomy read, data — a gap one way, the equality, or a gap the
other way, with the exclusivity reads beside it.  The scalar datum
is the pair `[a : b]` (`Pair`), the balance pair `⟨u : v⟩` (`BPair`)
reads jointly, and the composite pair `[⟨u : v⟩ : c]` (`CPair`)
is the balance pair of its members' pairs at the one shared second
datum; each carrier's displayed reads are its whole interface, and
the one-value reads are decidable.  The composite carries the fold
clause's own kit — the sum seeded at the equal-membered unit with
its head and append splits (`CPair.sum_cons`, `CPair.sum_append`),
the product distributing and regrouping (`CPair.mul_add`,
`CPair.mul_assoc`), the swap keeping the one-value read
(`CPair.swap_congr`) with a member against its swap joining to the
sum's unit (`CPair.add_swap_unit`), the one-member entries
multiplying and congruent (`CPair.ofPair_mul`,
`CPair.ofPair_congr`, `CPair.mul_left_congr`), and a one-member
factor keeping the side at the swap comparison
(`CPair.mul_lt_swap`).  A balance pair's magnitude
crosses to the count carrier as its margin (`BPair.marginN`, the
exceeding member's gap at the stored counts, an equal-membered pair
reading nought), the one read this module's own stored count
serves outright — `thm:windowsep`'s division descent, whose content
arithmetic runs at the counts' own greatest common divisor, the
recorded consumer.  The margin kit beside it reads the crossing
whole: one count per one-value class (`BPair.marginN_congr`),
additive over pairs at or beyond the sum's unit
(`BPair.marginN_add`), each natural entry's count read back
(`BPair.marginN_ofNat`) and returned to its entry at one value
(`BPair.ofNat_marginN`).  The homogeneity principle's
reads are the `oneValue` congruence theorems: every displayed read
maps representatives at one value to one value.  The occupied read
is the one named form, a pair off the sum's unit
(`BPair.offUnit`), the certificate conjuncts' shared spelling.

The fold clause: a finite family sums by the fold over its index
order (`famFold`, at every carrier with its displayed sum and unit),
the displayed sum's laws entering as the one-value bundles —
`CommLaws` the reordering fragment (the relation's reflexive and
transitive reads with the sum's congruence, commutation and
reassociation) and `FoldLaws` the whole, the symmetry with the unit
dropping on either side — with the accumulator fold's parametrized
reads on the bundle (`foldlAddO` against the seed, `sumConsO` the
head split, `sumAppendO` the joined family's split) and the
carrier instances beside them (`bpairFoldLaws`, `natFoldLaws`,
`natMulFoldLaws` at the product's own monoid); and two fold orders
are equal by the ground identities — the member counts are the
fold order's datum (`countOf`), `famFold_relist` the one value at
matched counts, `famFold_congr_all` the fold's one value at one
read per member, and `famFold_reindex` the reindexing read at a
distinct family with a two-sided witness map, the graded folds'
device.  The count clause reads at the predicate count (`countBy`,
one unit per member the stated condition accepts, the head splits
`countBy_cons_true` and `countBy_cons_false`), the membership and
order counts its instances (`countOf`, `countAbove`, `countBelow`,
each with its head-split bridge at the condition's own ite:
`countOf_cons`, `countAbove_cons`, `countBelow_cons`).

The Nat-fold kit beside it: the pointwise-unoccupied fold at the
count's unit (`famFold_zero`), the pointwise-sum split
(`famFold_add_split`), the right distribution (`mulAddR`) with the
reassociation (`mulAssoc`) and the gap's homogeneity in a shared
factor (`subMulR`, over the shared summand's drop `addSubAddR`),
the ordered pair's rejoining gap
(`natAddSubCancel`) with the strict comparison's occupied gap
(`subPos`), the nested folds' exchange (`famFold_swap`),
the scalar passes (`famFold_mul`, `famFold_mulR`), the point
collapses at a counted key (`famFold_pick`, `famFold_pickZero`,
`famFold_le_one_at` the bound at a fold vacant off one key),
the flattened family's fold (`famFold_flatMap`), the product
lists over a family of domains (`prodLists`, one list per selection
of a member from each domain, with their count, membership and
distinctness reads), the indicator's
count read (`countOf_fold`, the mirrored indicator's fold at
`famFold_indicatorFlip`), the rising product from a floor with
its split (`rise`, `rise_split`), and the collect-by-count read
(`famFold_countCollect`, a family's fold as the
multiplicity-weighted fold over a base holding each member once).
The product fold over a key list (`prodOver`) reads its own kit:
the pointwise bound at the members (`prodOver_le`), the occupied
read (`prodOver_pos`), the unit-valued filter's drop
(`prodOver_filter`), the withdrawn-key read at a key occupied once
(`prodOver_pick`), the constant family's length read
(`prodOver_const`), and the constant range product's seam split
with its base floor (`prodConst_split`, `prodConst_ge`).
Beside it the hand-rolled sum reads the consumers share: the join's
two cancellations (`addCancelR`, `addCancelL`), the ordered
triple's consecutive gaps joining to the outer gap (`subJoin`),
the four-term
regrouping at the exchanged inner members (core's
`Nat.add_add_add_comm`), the seed's
hoist out of an additive fold (`foldlSeed`), and, at the positional
kit, the vacant family's read at every key
(`getAt_replicate_zero`) beside the repeated family's own
(`getAt_replicate`, its member at every key below the count) with
the head's dominance over the tail at a weak descent (`headDom`).
The keyed entry edit is `editAt`, the family read changed at one
key with every further coordinate kept, the raise and the lowering
(`bumpAt`, `dipAt`) its one-box instances at the successor and the
truncating subtraction.
The positional kit's adjacent exchange is `adjSwap`, at every
member type: the pair at a key and its successor trade places, with
the count read (`length_adjSwap`), the three entry reads
(`getAt_adjSwap_fst`, `_snd`, `_ne`) with their transposition
join (`getAt_adjSwap`), the involution
(`adjSwap_adjSwap`), the strike's shift (`eraseIdx_adjSwap`) and
the entry map's composition (`adjSwap_map`) — `def:places`'s
grading and `def:elim`'s row expansion its consumers.  The segment
move rides on it (`moveOne`, `moveK`: a member past its followers
one exchange each, a segment past the members after it one member
at a time, the moved members last in their order), with the count
kept, the map passing through, the exchanges' count (`moveCount`),
the key read at the move (`mvIx`, its three region reads joined at
`getAt_moveK`, kept below the order and injective there) and the
balance partner iterated (`BPair.swapN`) — `lem:inertia`'s
kernel-column collection its consumer.

The partition tier closes that kit: the constant-one fold reads the
length (`famFold_length`), a fold over a list is the fold of its
members' counts against the weights over a distinct covering index
(`famFold_partition`, `famFold_countCollect` at the covering read)
with the length its unit-weight instance (`countOf_partition`), and
the covering index itself is the distinct index at the first
appearance (`dedupF`, its two membership reads `mem_dedupF` and
`mem_of_dedupF`, the counts at one at most, `countOf_dedupF_le`,
and a listed member's count one, `countOf_dedupF_one`).

The occupancy families' enumeration closes the count kit:
`sublistsOf` lists a seed's families, the tail's own without and
with the head, with the membership test `containsB` (the count's
own decide, its head reads `containsB_head` and
`containsB_cons_ne`), the entries' containment
(`sublists_entries`), the filter's membership (`filter_member`),
the one-count read at a distinct seed (`sublists_count_le`), and
the characterization read, a member its own entries' filter of the
seed (`sublists_char`) — `thm:assembly`'s subset fold with
`cor:weyldim`'s place-pair instance the consumers.

The count carrier's key-list and reversal kit closes the tier:
the range's length and entry reads (`length_range`, `length_mapRange`, `getAt_range`,
`getAt_map_range`, `range_map_getAt`) with the head and end splits
(`range_cons`, `range_split`, `endSplit`) and the extension at a
vanishing tail (`foldExtend`, `foldExtend'`); the range's counts
(`countOf_range` with its occupied reads, `distinctList_range`,
`memRange`, `ltOfMem`, and the range fold's member congruence at
the key binder, `famFold_congr_range`) and the guarded run's fold
(`aboveRun`); the sorted word's whole-key read (`sortedAll`, the
keys at or beyond the length at the vacant default);
the matrix at an entry formula over two key ranges (`matOf` with
its length, row, width, entry and congruence reads); the key
lists over a family of domains (`prodLists`, its count the domains'
length product, its members' count one at distinct domains) and
the box at stated per-key bounds (`boxAll`, the product lists at
the bounds' ranges, its count the bounds' successor product
`boxAll_length` and its member count one at the matched length
with every key at or below its bound, vacant off that read,
`boxAll_countOf`) with the family rotation
(`rotAt`);
the family fold over the key range (`famFold_getAt`); the
reversal's reads (`reverse_cons`, `length_reverse`,
`countOf_reverse`, `reverse_append`, `reverse_reverse`,
`map_reverse`, `getAt_reverse`); the count family's total
(`sumNat`, the count carrier's family fold at the identity read,
`sumMap` its mapped bridge) with the raise, lowering, join,
pointwise-split, replicate and reversal reads, the
leading-segment reads
(`prefixAt_full`, `prefix_reverse_join`), and the vacant-total
reads (`getAt_zero_of_sum`, `replicate_of_zeros`,
`replicate_of_sum_zero`); the entry-count reads
(`getAt_ne_of_distinct`, `countOf_adjSwap`)
with the pigeonhole at the key range (`length_le_of_distinct`);
the parity pair (`xorFalse`, `xorNot`), `con:places`' grading the
consumer; and the guard kit at withheld values — two values at one
guard summing at the guard (`if_add`) and nested guards exchanging
(`if_swap`) — `con:units`' action commutation, the character fold
and the path-square counts the consumers.

The balance carrier's list fold `BPair.sum` carries its own index
reads: the accumulating fold against its seed (`BPair.foldlAdd`),
the head split (`BPair.sum_cons`), the joined family's split
(`BPair.sum_append`) — each the bundle kit's instance at
`bpairFoldLaws` — and the two bridges to the index fold: a
mapped family's (`BPair.sum_map`) and a flattened family's, the
latter reading the per-member folds (`BPair.sum_flatMap`).

The balance carrier's own fold and order stand at the same tier:
the index fold `bsum` (`famFold` at the balance sum and unit) with
its reindexing (`bsum_map`), nested exchange (`bsum_swap`), count
collection (`bsum_scalar`) and delta pick (`bsum_pick`); the fold's
generic reads at one value per occupied member
(`foldB_congr_members`), at the pointwise unit (`foldB_null`), at a
pointwise sum (`foldB_add`), at a key's own delta against its count
(`foldB_indicator`), at a key occupied once against a family at
the unit off it (`foldB_pick`), at a scalar (`foldB_mul_left`) and
at the memberwise swap (`fold_swap`, over the swap's own congruence
`swap_congr`); the additive left fold as the family fold
(`foldlSum`); the running product's seed carry with the
one-key skip reads at a commutative associative product
(`foldl_mul_seed`, `foldl_skip_absent`, `foldl_skip`), the products of
every member but one at one pass (`othersAll`, `getAt_othersAll`); and the balance order `≤` with its `leB_*` kit —
the cross-added members' at-or-below read over the ground order's sum,
cancellation, shift and refutation (`posLeAdd`, `posLeCancelR`,
`posLeShift`, `posLtLe`), with its congruences, the unit reads,
the count scalings, the comparison fold `bsum_le`, and the
trichotomy's converse round trip (`leB_not_lt`,
`leB_of_not_lt`).  `def:elim`'s pairing reads and the form tiers
`lem:fpcap` and `lem:loopcap` are the consumers.

A read is decidable at every argument, so a family of reads over an
index range is one Boolean datum: `all_range_read` reads that fold
back key by key and `all_range_intro` states it from the pointwise
reads, the fold form the definition and the pointwise form its
derived read.  The window hypotheses of `lem:fpcap` and
`lem:loopcap` are stated at that fold, so each is decided at its
window rather than quantified.  The list fold's own kit sits
beside the range's: `all_getAt` reads the fold back at a key,
`all_of_getAt` and `all_of_pointwise` state it from the keyed and
the key-free pointwise reads, and `all_map` reads the fold across
a map as the composed read's own.
-/

namespace ground

set_option genInjectivity false in
/-- The positive naturals: the stored count of successor steps from
one, a term's value the count's successor, so zero is
unrepresentable by the denotation's shape. -/
structure Pos : Type where
  pred : Nat

/-- The unit, the generation's seed. -/
def Pos.one : Pos := ⟨0⟩

/-- The successor. -/
def succ (p : Pos) : Pos := ⟨p.pred + 1⟩

/-- The sum: `(a + 1) + (b + 1) = (a + b + 1) + 1` at the stored
counts. -/
def add (p q : Pos) : Pos := ⟨p.pred + q.pred + 1⟩

instance instGround1 : Add Pos := ⟨add⟩

/-- The product: `(a + 1)(b + 1) = (ab + a + b) + 1` at the stored
counts. -/
def mul (p q : Pos) : Pos := ⟨p.pred * q.pred + p.pred + q.pred⟩

instance instGround2 : Mul Pos := ⟨mul⟩

/-- Decidable equality, the stored counts' own (hand-written: the
generated `injEq` route is disabled with the injectivity lemmas). -/
def decEq : (p q : Pos) → Decidable (p = q)
  | ⟨x⟩, ⟨y⟩ =>
    match Nat.decEq x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse n => isFalse (fun hh => n (congrArg Pos.pred hh))

instance instGround3 : DecidableEq Pos := decEq

/-- The unit test, one count read. -/
def Pos.isOne (p : Pos) : Bool := p.pred == 0

/-- Numerals: the literal's predecessor is the stored count; the
instance exists at positive literals alone, so a zero literal has
no elaboration. -/
instance instGround4 (n : Nat) : OfNat Pos (n + 1) := ⟨⟨n⟩⟩

/-- A count's successor as a positive natural, the occupancy
converter (`n` reads `n + 1`). -/
def posOfSucc (n : Nat) : Pos := ⟨n⟩

/-- A count at or beyond one as a positive natural, the successor of
its predecessor. -/
def posOfNat (n : Nat) : Pos := ⟨n - 1⟩

/-! The generation from one by the successor, the carrier's own
recursion: the motive read at a stored count, the recursion
structural there, and the step read definitional. -/

/-- Peano recursion on the carrier: the stored count's own
recursion, the motive read through the denotation's shape. -/
def peanoRec {motive : Pos → Sort u} (h1 : motive .one)
    (hs : ∀ q, motive q → motive (succ q)) (p : Pos) : motive p :=
  Nat.rec (motive := fun n => motive ⟨n⟩) h1 (fun n ih => hs ⟨n⟩ ih)
    p.pred

/-- The derived recursion's step read, definitional on this
carrier: `peanoRec` at a successor is the step applied at the
value, the generation's own fold identity. -/
theorem peanoRec_succ (p : Pos) {motive : Pos → Sort u}
    (h1 : motive .one) (hs : ∀ q, motive q → motive (succ q)) :
    peanoRec h1 hs (succ p) = hs p (peanoRec h1 hs p) := rfl

/-! The count-level kit: the value read `posVal p` is the
denotation, the laws lift through it, and the helpers are
hand-rolled where the core lemma's proof reads through `propext`. -/

/-- The value read: the successor of the carried count, the
occupancy converter's inverse at `con:places`' successor-name
pattern. -/
def posVal (p : Pos) : Nat := p.pred + 1

/-- Every value read is occupied. -/
theorem posVal_pos (p : Pos) : 0 < posVal p := Nat.succ_pos p.pred

/-- The stored count's injectivity read, the constructor's own: two
positives at one value are one stored count. -/
theorem posMkInj {a b : Nat} (h : (⟨a⟩ : Pos) = ⟨b⟩) : a = b :=
  congrArg Pos.pred h

private theorem val_inj {p q : Pos} (h : posVal p = posVal q) : p = q :=
  congrArg Pos.mk (Nat.succ.inj h)

private theorem val_add (p q : Pos) : posVal (p + q) = posVal p + posVal q :=
  congrArg (· + 1) (Nat.succ_add p.pred q.pred).symm

/-- The value read is multiplicative: a product's read is the
reads' product. -/
theorem val_mul (p q : Pos) : posVal (p * q) = posVal p * posVal q := by
  show p.pred * q.pred + p.pred + q.pred + 1
      = (p.pred + 1) * (q.pred + 1)
  rw [Nat.add_right_comm (p.pred * q.pred) p.pred q.pred,
    Nat.mul_succ, Nat.succ_mul]
  exact Nat.add_assoc _ _ _

/-- One step deeper is one gap fewer, at every depth inside the
height. -/
theorem subSuccAdd : ∀ {k n : Nat}, k + 1 ≤ n →
    n - (k + 1) + 1 = n - k
  | _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | 0, n + 1, _ => by
    rw [Nat.succ_sub_succ]
    rfl
  | k + 1, n + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    exact subSuccAdd (Nat.le_of_succ_le_succ h)

/-- A summand reads back off the join, the gap's own cancel. -/
theorem addSubSelfL : ∀ a b : Nat, (a + b) - a = b
  | 0, b => by rw [Nat.zero_add, Nat.sub_zero]
  | a + 1, b => by
    rw [Nat.succ_add, Nat.succ_sub_succ]
    exact addSubSelfL a b

/-- A natural sits below itself joined with any successor. -/
theorem ltAddSucc (a d : Nat) : a < a + (d + 1) :=
  Nat.succ_le_succ (Nat.le_add_right a d)

/-- The join's other summand reads back, the commuted cancel. -/
theorem addSubSelfR (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm a b]
  exact addSubSelfL b a

/-- The join's cancel at an ordered pair: the gap rejoins its
lower member. -/
theorem natAddSubCancel : ∀ {m n : Nat}, m ≤ n → m + (n - m) = n
  | 0, n, _ => Nat.zero_add n
  | _ + 1, 0, h => nomatch h
  | m + 1, n + 1, h => by
    rw [Nat.succ_sub_succ n m, Nat.succ_add]
    exact congrArg Nat.succ (natAddSubCancel (Nat.le_of_succ_le_succ h))

/-- A gap read below the second summand: at an ordered first
summand, the strict comparison withdraws it. -/
theorem subLt {a p b : Nat} (hap : a ≤ p) (h : p < a + b) :
    p - a < b := by
  have h2 : a + (p - a) < a + b := by
    rw [natAddSubCancel hap]
    exact h
  exact Nat.lt_of_add_lt_add_left h2

/-- The gap rejoins its lower member at the commuted order. -/
theorem subAdd {m n : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.add_comm]
  exact natAddSubCancel h

/-- A natural at or below one is the count's unit or the one. -/
theorem leOneCases : ∀ {A : Nat}, A ≤ 1 → A = 0 ∨ A = 1
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | _ + 2, h => absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero _)

/-- A vanishing double vanishes. -/
theorem twoMulZero : ∀ {n : Nat}, 2 * n = 0 → n = 0
  | 0, _ => rfl
  | _ + 1, h => absurd h (fun hc => Nat.noConfusion hc)

/-- A natural sits at or below its predecessor's successor. -/
theorem lePredSucc : ∀ n : Nat, n ≤ n - 1 + 1
  | 0 => Nat.zero_le 1
  | n + 1 => Nat.le_refl (n + 1)

/-- One joined with any natural is occupied. -/
theorem oneAddNeZero (x : Nat) : ¬ 1 + x = 0 :=
  fun hc => Nat.noConfusion ((Nat.add_comm 1 x).symm.trans hc)

/-- The four summands exchange the outer members inward,
`a + b + c + d = (a + d) + (b + c)`. -/
theorem addExch4 (a b c d : Nat) :
    a + b + c + d = (a + d) + (b + c) := by
  rw [Nat.add_right_comm (a + b) c d, Nat.add_right_comm a b d,
    Nat.add_assoc]

/-- An occupied natural's predecessor sits below it. -/
theorem subOneLt {A : Nat} (hA : 0 < A) : A - 1 < A := by
  show A - 1 + 1 ≤ A
  rw [subAdd hA]
  exact Nat.le_refl A

/-- An ordered gap at or past the whole reads the count's unit. -/
theorem subLe : ∀ (a b : Nat), a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => by
    rw [Nat.succ_sub_succ]
    exact subLe a b (Nat.le_of_succ_le_succ h)

/-- Two successive clearings read the joined clearing. -/
theorem subSub : ∀ (n m k : Nat), n - m - k = n - (m + k)
  | _, _, 0 => rfl
  | n, m, k + 1 => congrArg (fun x => x - 1) (subSub n m k)

/-- The predecessor's remainder at an exceeded key stays inside the
count. -/
theorem predSubLt {x n : Nat} (hx : x < n) : (n - 1) - x < n := by
  match n, hx with
  | n + 1, _ =>
    rw [Nat.succ_sub_succ]
    show (n - 0) - x < n + 1
    exact Nat.lt_succ_of_le (Nat.sub_le n x)

/-- The gap at a strict comparison is occupied. -/
theorem subPos : ∀ {m n : Nat}, m < n → 0 < n - m
  | 0, _ + 1, _ => Nat.succ_pos _
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | m + 1, n + 1, h => by
    rw [Nat.succ_sub_succ n m]
    exact subPos (Nat.lt_of_succ_lt_succ h)

/-- The boolean at-or-below read joins the order, one direction of
the kernel comparison's bridge. -/
theorem bleLe : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (bleLe (a := a) (b := b) h)

/-- The order joins the boolean at-or-below read, the bridge's
other direction. -/
theorem leBle : ∀ {a b : Nat}, a ≤ b → Nat.ble a b = true
  | 0, 0, _ => rfl
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h =>
    leBle (a := a) (b := b) (Nat.le_of_succ_le_succ h)

/-- The lesser of two counts at the kernel's own comparison:
core `Nat.min`'s `if` clears a `Decidable` wrapper the kernel
walks per call, where `Nat.ble` is the kernel's accelerated
comparison. -/
def natMin (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => a
  | false => b

/-- The least member over a list from a seed at a boolean at-or-below
read, one trichotomy fold: the seed kept where it sits at or below
the member and the member taken otherwise. -/
def leastBy {α : Type} (le : α → α → Bool) (x : α) : List α → α
  | [] => x
  | y :: t => leastBy le (if le x y then x else y) t

/-- The boolean strict read joins the order, the successor's
at-or-below. -/
theorem bltLt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  bleLe h

/-- The order joins the boolean strict read. -/
theorem ltBlt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  leBle h

/-- A strict comparison's gap rejoins its members,
`x + (y - x - 1) + 1 = y`. -/
theorem natGapEq {x y : Nat} (h : x < y) :
    x + (y - x - 1) + 1 = y :=
  (Nat.succ_add x (y - (x + 1))).symm.trans (natAddSubCancel h)

/-- The join cancels its right member, the hand-rolled read. -/
theorem addCancelR : ∀ {a b : Nat} (c : Nat),
    a + c = b + c → a = b
  | _, _, 0, h => h
  | _, _, c + 1, h => addCancelR c (Nat.succ.inj h)

/-- The join cancels its left member, the hand-rolled read. -/
theorem addCancelL (a : Nat) {b c : Nat} (h : a + b = a + c) :
    b = c := by
  rw [Nat.add_comm a b, Nat.add_comm a c] at h
  exact addCancelR a h

/-- Two consecutive gaps of an ordered triple join to the outer
gap. -/
theorem subJoin {a b c : Nat} (hcb : c ≤ b) (hba : b ≤ a) :
    (a - b) + (b - c) = a - c := by
  refine addCancelR c ?_
  rw [Nat.add_assoc, subAdd hcb, subAdd hba,
    subAdd (Nat.le_trans hcb hba)]

/-- A summand against a gap reads the joined sum's gap, the
subtrahend hoisted across the join. -/
theorem addSubAssoc {u hv : Nat} (hle : u ≤ hv) (c : Nat) :
    c + (hv - u) = (c + hv) - u := by
  refine addCancelR u ?_
  rw [Nat.add_assoc c (hv - u) u, subAdd hle,
    subAdd (Nat.le_trans hle (Nat.le_add_left hv c))]

/-- The order cancels its shared left summand. -/
theorem leCancelL : ∀ (a : Nat) {b c : Nat},
    a + b ≤ a + c → b ≤ c
  | 0, _, _, h => by
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | a + 1, b, c, h => by
    rw [Nat.succ_add, Nat.succ_add] at h
    exact leCancelL a (Nat.le_of_succ_le_succ h)

/-- A key below the orders' sum sits in the leading order or is the
leading order joined to a key below the trailing one. -/
theorem blockIdx (a b i : Nat) (hi : i < a + b) :
    i < a ∨ ∃ k, k < b ∧ i = a + k := by
  cases Nat.lt_or_ge i a with
  | inl h => exact Or.inl h
  | inr h =>
    obtain ⟨k, hk⟩ := Nat.le.dest h
    refine Or.inr ⟨k, ?_, hk.symm⟩
    rw [← hk] at hi
    exact leCancelL a hi

/-- The strict order cancels its shared left factor: the trichotomy
against the factor's monotone read. -/
theorem ltCancelMulL {c a b : Nat} (h : c * a < c * b) : a < b :=
  match Nat.lt_or_ge a b with
  | Or.inl hab => hab
  | Or.inr hba =>
    absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left c hba)) (Nat.lt_irrefl _)

/-- The lesser of a count with itself is that count, both arms of
the accelerated branch reading the one member. -/
theorem natMin_self (a : Nat) : natMin a a = a := by
  show (match Nat.ble a a with | true => a | false => a) = a
  cases Nat.ble a a with
  | true => rfl
  | false => rfl

/-- The lesser sits at or below its first member. -/
theorem natMin_le_left (a b : Nat) : natMin a b ≤ a := by
  show (match Nat.ble a b with | true => a | false => b) ≤ a
  cases hb : Nat.ble a b with
  | true => exact Nat.le_refl a
  | false =>
    cases Nat.le_total a b with
    | inl h =>
      exact absurd h (Nat.not_le_of_not_ble_eq_true
        (fun he => Bool.noConfusion (hb.symm.trans he)))
    | inr h => exact h

/-- The lesser sits at or below its second member. -/
theorem natMin_le_right (a b : Nat) : natMin a b ≤ b := by
  show (match Nat.ble a b with | true => a | false => b) ≤ b
  cases hb : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true hb
  | false => exact Nat.le_refl b

/-- A natural below both members sits below their least. -/
theorem le_natMin {k a b : Nat} (ha : k ≤ a) (hb : k ≤ b) :
    k ≤ natMin a b := by
  show k ≤ (match Nat.ble a b with | true => a | false => b)
  cases Nat.ble a b with
  | true => exact ha
  | false => exact hb

/-- The order cancels its shared right summand. -/
theorem leCancelR (c : Nat) {a b : Nat}
    (h : a + c ≤ b + c) : a ≤ b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact leCancelL c h

/-- The bounded first-hit search: from a start key, the least key
whose read holds, the budget's end at exhaustion. -/
def firstAt (P : Nat → Prop) [DecidablePred P] : Nat → Nat → Nat
  | k, 0 => k
  | k, j + 1 => if P k then k else firstAt P (k + 1) j

/-- The walk's answer sits at or beyond its start. -/
theorem firstAt_ge (P : Nat → Prop) [DecidablePred P] :
    ∀ (j k : Nat), k ≤ firstAt P k j
  | 0, k => Nat.le_refl k
  | j + 1, k => by
    show k ≤ (if P k then k else firstAt P (k + 1) j)
    match (inferInstance : Decidable (P k)) with
    | isTrue hc =>
      rw [if_pos hc]
      exact Nat.le_refl k
    | isFalse hc =>
      rw [if_neg hc]
      exact Nat.le_trans (Nat.le_succ k) (firstAt_ge P j (k + 1))

/-- The walk's answer sits inside its budget. -/
theorem firstAt_le (P : Nat → Prop) [DecidablePred P] :
    ∀ (j k : Nat), firstAt P k j ≤ k + j
  | 0, k => Nat.le_refl k
  | j + 1, k => by
    show (if P k then k else firstAt P (k + 1) j) ≤ k + (j + 1)
    match (inferInstance : Decidable (P k)) with
    | isTrue hc =>
      rw [if_pos hc]
      exact Nat.le_add_right k (j + 1)
    | isFalse hc =>
      rw [if_neg hc]
      refine Nat.le_trans (firstAt_le P j (k + 1)) ?_
      rw [Nat.add_right_comm k 1 j]
      exact Nat.le_refl _

/-- Every key before the walk's answer refuses the read. -/
theorem firstAt_below (P : Nat → Prop) [DecidablePred P] :
    ∀ (j k m : Nat), k ≤ m → m < firstAt P k j → ¬ P m
  | 0, _, m, hkm, hm => absurd hm (Nat.not_lt_of_ge hkm)
  | j + 1, k, m, hkm, hm => by
    match (inferInstance : Decidable (P k)) with
    | isTrue hc =>
      have : firstAt P k (j + 1) = k := by
        show (if P k then k else firstAt P (k + 1) j) = k
        rw [if_pos hc]
      rw [this] at hm
      exact absurd hm (Nat.not_lt_of_ge hkm)
    | isFalse hc =>
      have hstep : firstAt P k (j + 1) = firstAt P (k + 1) j := by
        show (if P k then k else firstAt P (k + 1) j) = firstAt P (k + 1) j
        rw [if_neg hc]
      rw [hstep] at hm
      match Nat.lt_or_ge k m with
      | Or.inr hge =>
        rw [Nat.le_antisymm hge hkm]
        exact hc
      | Or.inl hlt =>
        exact firstAt_below P j (k + 1) m hlt hm

/-- The read at the budget's end reads the walk's answer. -/
theorem firstAt_hit (P : Nat → Prop) [DecidablePred P] :
    ∀ (j k : Nat), P (k + j) → P (firstAt P k j)
  | 0, _, h => h
  | j + 1, k, h => by
    show P (if P k then k else firstAt P (k + 1) j)
    match (inferInstance : Decidable (P k)) with
    | isTrue hc =>
      rw [if_pos hc]
      exact hc
    | isFalse hc =>
      rw [if_neg hc]
      refine firstAt_hit P j (k + 1) ?_
      rw [Nat.add_right_comm k 1 j]
      exact h

/-- A walk whose answer refuses ran its whole budget. -/
theorem firstAt_miss (P : Nat → Prop) [DecidablePred P] :
    ∀ (j k : Nat), ¬ P (firstAt P k j) → firstAt P k j = k + j
  | 0, _, _ => rfl
  | j + 1, k, h => by
    match (inferInstance : Decidable (P k)) with
    | isTrue hc =>
      refine absurd ?_ h
      show P (if P k then k else firstAt P (k + 1) j)
      rw [if_pos hc]
      exact hc
    | isFalse hc =>
      have hstep : firstAt P k (j + 1) = firstAt P (k + 1) j := by
        show (if P k then k else firstAt P (k + 1) j) = firstAt P (k + 1) j
        rw [if_neg hc]
      rw [hstep] at h ⊢
      rw [firstAt_miss P j (k + 1) h, Nat.add_right_comm k 1 j]
      exact Nat.add_assoc k j 1

/-- A walk stopping short of its budget stops at a hit. -/
theorem firstAt_stop (P : Nat → Prop) [DecidablePred P] :
    ∀ (j k : Nat), firstAt P k j < k + j → P (firstAt P k j)
  | 0, k, h => absurd h (Nat.not_lt_of_ge (Nat.le_refl k))
  | j + 1, k, h => by
    match (inferInstance : Decidable (P k)) with
    | isTrue hc =>
      have heq : firstAt P k (j + 1) = k := by
        show (if P k then k else firstAt P (k + 1) j) = k
        rw [if_pos hc]
      rw [heq]
      exact hc
    | isFalse hc =>
      have hstep : firstAt P k (j + 1) = firstAt P (k + 1) j := by
        show (if P k then k else firstAt P (k + 1) j) = firstAt P (k + 1) j
        rw [if_neg hc]
      rw [hstep]
      rw [hstep, ← Nat.add_assoc k j 1, Nat.add_right_comm k j 1] at h
      exact firstAt_stop P j (k + 1) h

/-- A count's square at its self-product. -/
theorem sqRead (a : Nat) : a ^ 2 = a * a := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

/-- A count's cube at its three-fold product. -/
theorem pow3Read (a : Nat) : a ^ 3 = a * a * a := by
  rw [Nat.pow_succ, sqRead]

/-- A count's fourth power at its four-fold product. -/
theorem pow4Read (a : Nat) : a ^ 4 = a * a * a * a := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero,
    Nat.one_mul]

/-- A count's fifth power at its five-fold product. -/
theorem pow5Read (a : Nat) : a ^ 5 = a * a * a * a * a := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero,
    Nat.one_mul]

/-- A count's eighth power at its eight-fold product. -/
theorem pow8Read (a : Nat) : a ^ 8 = a * a * a * a * a * a * a * a := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ,
    Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

/-- A count's square reads back the count's order. -/
theorem leOfSqLe {a b : Nat} (h : a * a ≤ b * b) : a ≤ b := by
  match Nat.lt_or_ge b a with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    have ha : 1 ≤ a := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le b)) hlt
    have e1 : (b + 1) * a = b * a + a := Nat.succ_mul b a
    have h2 : b * a + a ≤ a * a := by
      rw [← e1]
      exact Nat.mul_le_mul_right a hlt
    have h3 : b * a + 1 ≤ b * a + a := Nat.add_le_add_left ha (b * a)
    have h4 : b * b ≤ b * a := Nat.mul_le_mul_left b (Nat.le_of_lt hlt)
    exact absurd
      (Nat.le_trans (Nat.le_trans (Nat.add_le_add_right h4 1) h3)
        (Nat.le_trans h2 h))
      (Nat.not_succ_le_self (b * b))


/-- The index transposition as a function, the reindexing
device. -/
def swapIx (i j : Nat) (t : Nat) : Nat :=
  if t = i then j else if t = j then i else t

theorem swapIx_invol (i j : Nat) :
    ∀ t, swapIx i j (swapIx i j t) = t := by
  intro t
  show swapIx i j (if t = i then j else if t = j then i else t) = t
  by_cases hti : t = i
  · rw [if_pos hti]
    show (if j = i then j else if j = j then i else j) = t
    by_cases hji : j = i
    · rw [if_pos hji, hji, hti]
    · rw [if_neg hji, if_pos rfl, hti]
  · rw [if_neg hti]
    by_cases htj : t = j
    · rw [if_pos htj]
      show (if i = i then j else _) = t
      rw [if_pos rfl, htj]
    · rw [if_neg htj]
      show (if t = i then j else if t = j then i else t) = t
      rw [if_neg hti, if_neg htj]

theorem swapIx_lt {i j d : Nat} (hi : i < d) (hj : j < d) :
    ∀ t, t < d → swapIx i j t < d := by
  intro t ht
  show (if t = i then j else if t = j then i else t) < d
  by_cases hti : t = i
  · rw [if_pos hti]
    exact hj
  · rw [if_neg hti]
    by_cases htj : t = j
    · rw [if_pos htj]
      exact hi
    · rw [if_neg htj]
      exact ht

/-- The transposition at its first place. -/
theorem swapIx_fst (i j : Nat) : swapIx i j i = j := by
  show (if i = i then j else _) = j
  rw [if_pos rfl]

/-- The transposition at its second place. -/
theorem swapIx_snd {i j : Nat} (h : ¬ j = i) :
    swapIx i j j = i := by
  show (if j = i then j else if j = j then i else j) = i
  rw [if_neg h, if_pos rfl]

/-- The transposition off its two places. -/
theorem swapIx_off {i j t : Nat} (h1 : ¬ t = i) (h2 : ¬ t = j) :
    swapIx i j t = t := by
  show (if t = i then j else if t = j then i else t) = t
  rw [if_neg h1, if_neg h2]

/-- The double gap returns the member at the bound. -/
theorem natSubSubCancel (M x : Nat) (h : x ≤ M) : M - (M - x) = x := by
  have h1 : x + (M - x) = M := natAddSubCancel h
  have h2 : (M - x) ≤ M :=
    Nat.le.intro (Nat.add_comm x (M - x) ▸ h1)
  have h3 : (M - x) + (M - (M - x)) = M := natAddSubCancel h2
  exact addCancelL (M - x)
    (h3.trans ((Nat.add_comm x (M - x)).symm.trans h1).symm)

/-! The step reads. -/

theorem add_one (p : Pos) : p + Pos.one = succ p := rfl

theorem one_add (q : Pos) : Pos.one + q = succ q :=
  congrArg Pos.mk (congrArg (· + 1) (Nat.zero_add q.pred))

theorem succ_add (p q : Pos) : succ p + q = succ (p + q) :=
  congrArg Pos.mk (congrArg (· + 1) (Nat.succ_add p.pred q.pred))

theorem add_succ (p q : Pos) : p + succ q = succ (p + q) := rfl

theorem succ_ne_one (p : Pos) : succ p ≠ Pos.one :=
  fun h => nomatch congrArg Pos.pred h

theorem succ_inj {p q : Pos} (h : succ p = succ q) : p = q :=
  congrArg Pos.mk (Nat.succ.inj (congrArg Pos.pred h))

/-! The sum's laws and its injectivity, lifted through the value
read. -/

theorem add_comm (p q : Pos) : p + q = q + p :=
  congrArg Pos.mk (congrArg (· + 1) (Nat.add_comm p.pred q.pred))

theorem add_assoc (p q r : Pos) : p + q + r = p + (q + r) :=
  val_inj (by
    rw [val_add (p + q) r, val_add p q, val_add p (q + r), val_add q r,
      Nat.add_assoc])

theorem add_left_comm (a b c : Pos) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem add_right_cancel {a b c : Pos} (h : a + c = b + c) : a = b := by
  have h' : posVal a + posVal c = posVal b + posVal c := by
    rw [← val_add, ← val_add, h]
  exact val_inj (addCancelR _ h')

theorem add_left_cancel {a b c : Pos} (h : a + b = a + c) : b = c :=
  add_right_cancel (by rw [add_comm b a, add_comm c a]; exact h)

theorem add_right_comm (a b c : Pos) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

theorem add_add_comm (a b c d : Pos) : a + b + (c + d) = a + c + (b + d) := by
  rw [add_assoc, add_assoc, add_left_comm b c d]

theorem add_add_comm' (a b c d : Pos) : a + b + (c + d) = a + d + (b + c) := by
  rw [add_comm c d, add_add_comm]

/-- The sum moves: `p + g` is never `p` back, the exclusivity's seed. -/
theorem add_ne_left (p g : Pos) : p + g ≠ p := fun h =>
  nomatch addCancelR (a := posVal g) (b := 0) (posVal p) (by
    rw [Nat.zero_add, Nat.add_comm (posVal g) (posVal p), ← val_add, h])

/-! The trichotomy read, data: the gap off the stored counts'
comparison, its naming identity the hand-rolled subtraction kit's. -/

set_option genInjectivity false in
/-- The trichotomy's data: a gap one way, the equality, or a gap the
other way, the gap the stated order's witness. -/
inductive Trich (a b : Pos) : Type where
  | lt (g : Pos) (h : a + g = b)
  | eq (h : a = b)
  | gt (g : Pos) (h : b + g = a)

/-- The trichotomy read: of two naturals exactly one of three holds
(the exclusivity reads follow), and the read is data, the gap
constructed with the outcome off the counts' comparison. -/
def trich (a b : Pos) : Trich a b :=
  match Nat.decEq a.pred b.pred with
  | isTrue h => .eq (congrArg Pos.mk h)
  | isFalse ne =>
    match Nat.decLt a.pred b.pred with
    | isTrue h => .lt ⟨b.pred - a.pred - 1⟩ (congrArg Pos.mk (natGapEq h))
    | isFalse nlt =>
      .gt ⟨a.pred - b.pred - 1⟩ (congrArg Pos.mk (natGapEq
        (match Nat.lt_or_ge b.pred a.pred with
         | .inl h' => h'
         | .inr ge => absurd (Nat.lt_of_le_of_ne ge ne) nlt)))

/-- Order as gap-existence. -/
instance instGround5 : LT Pos := ⟨fun a b => ∃ g, a + g = b⟩

instance instGround6 (a b : Pos) : Decidable (a < b) :=
  match trich a b with
  | .lt g h => isTrue ⟨g, h⟩
  | .eq h => isFalse (fun ⟨g, hg⟩ => add_ne_left a g (by rw [hg, h]))
  | .gt g h => isFalse (fun ⟨g', hg'⟩ =>
      add_ne_left b (g + g') (by rw [← add_assoc, h, hg']))

/-- At or beyond: the equality or the gap. -/
instance instGround7 : LE Pos := ⟨fun a b => a = b ∨ a < b⟩

instance instGround8 (a b : Pos) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a = b ∨ a < b))

/-- The gap is one value by the sum's injectivity. -/
theorem gap_unique {a b g g' : Pos} (h : a + g = b) (h' : a + g' = b) :
    g = g' :=
  add_left_cancel (h.trans h'.symm)

/-- The exclusivity read one way: a gap forbids the equality. -/
theorem lt_ne {a b : Pos} (h : a < b) : a ≠ b := by
  obtain ⟨g, hg⟩ := h
  intro e
  exact add_ne_left a g (by rw [hg, ← e])

/-- The exclusivity read the other: gaps both ways compose to a
moved sum. -/
theorem lt_asymm {a b : Pos} (h : a < b) (h' : b < a) : False := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact add_ne_left a (g + g') (by rw [← add_assoc, hg, hg'])

/-- A derived order's witness composes by formula through the sum. -/
theorem lt_trans {a b c : Pos} (h : a < b) (h' : b < c) : a < c := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g + g', by rw [← add_assoc, hg, hg']⟩

/-- A strict read followed by an at-or-below read is strict, the
equality outcome keeping the witness and the gap outcome composing
it. -/
theorem lt_of_lt_of_le {a b c : Pos} (h : a < b) (h' : b ≤ c) : a < c :=
  match h' with
  | Or.inl e => by rw [← e]; exact h
  | Or.inr h'' => lt_trans h h''

/-- A summand on both sides keeps the order, the witness carried
across the added datum. -/
private theorem addLtAddR {a b : Pos} (c : Pos) (h : a < b) :
    a + c < b + c := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [add_right_comm a c g, hg]⟩

/-- The doubled sum keeps the order, the summand carried on both
sides in turn. -/
private theorem addSelfLt {a b : Pos} (h : a < b) : a + a < b + b := by
  have h1 : a + a < b + a := addLtAddR a h
  have h2 : b + a < b + b := by
    rw [add_comm b a]
    exact addLtAddR b h
  exact lt_trans h1 h2

/-- The doubled sum reflects the order, the trichotomy against the
doubled gap. -/
private theorem ltOfAddSelfLt {a b : Pos} (h : a + a < b + b) : a < b :=
  match trich a b with
  | .lt g hg => ⟨g, hg⟩
  | .eq e => absurd h (by
      subst e
      exact fun ⟨g, hg⟩ => add_ne_left (a + a) g hg)
  | .gt g hg => absurd h (fun h' => lt_asymm h' (addSelfLt ⟨g, hg⟩))

/-- The ground data start at their own one: nothing sits strictly
below it, so a sum never lands there. -/
theorem not_lt_one (p : Pos) : ¬ (p < Pos.one) := by
  intro h
  obtain ⟨g, hg⟩ := h
  have h2 : p.pred + g.pred + 1 = 0 := congrArg Pos.pred hg
  exact Nat.noConfusion h2

/-! The product's laws and its injectivity, lifted through the
value read. -/

theorem mul_one (p : Pos) : p * Pos.one = p :=
  val_inj (by rw [val_mul]; exact Nat.mul_one (posVal p))

theorem one_mul (q : Pos) : Pos.one * q = q :=
  val_inj (by rw [val_mul]; exact Nat.one_mul (posVal q))

theorem mul_comm (p q : Pos) : p * q = q * p :=
  val_inj (by
    rw [val_mul p q, val_mul q p, Nat.mul_comm (posVal p) (posVal q)])

theorem left_distrib (a b c : Pos) : a * (b + c) = a * b + a * c :=
  val_inj (by
    rw [val_mul a (b + c), val_add b c, Nat.left_distrib,
      val_add (a * b) (a * c), val_mul a b, val_mul a c])

theorem right_distrib (a b c : Pos) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

/-- The natural product reassociates, the hand-rolled read. -/
theorem mulAssoc : ∀ a b c : Nat, (a * b) * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c + 1 => by
    show (a * b) * c + a * b = a * (b * c + b)
    rw [Nat.left_distrib a (b * c) b, mulAssoc a b c]

theorem mul_assoc (a b c : Pos) : a * b * c = a * (b * c) :=
  val_inj (by
    rw [val_mul (a * b) c, val_mul a b, val_mul a (b * c), val_mul b c,
      mulAssoc])

theorem mul_left_comm (a b c : Pos) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

theorem mul_mul_mul_comm (a b c d : Pos) : a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, mul_assoc, mul_left_comm b c d]

theorem mul_mul_comm' (a b c d : Pos) : a * b * (c * d) = a * d * (b * c) := by
  rw [mul_comm c d, mul_mul_mul_comm]

/-- The doubling at the positive carrier: two against a member is
that member joined to itself. -/
theorem two_mul (p : Pos) : 2 * p = p + p := by
  rw [show (2 : Pos) = Pos.one + Pos.one from rfl, right_distrib, one_mul p]

/-- The product's monotonicity: a gap rescales to a gap, the witness
composed by formula. -/
theorem mul_lt_mul_right {a b : Pos} (c : Pos) (h : a < b) :
    a * c < b * c := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g * c, by rw [← right_distrib, hg]⟩

/-- The ground order composes. -/
theorem le_trans {a b c : Pos} (h : a ≤ b) (h' : b ≤ c) : a ≤ c :=
  match h with
  | Or.inl e => by rw [e]; exact h'
  | Or.inr l =>
    match h' with
    | Or.inl e' => by rw [← e']; exact Or.inr l
    | Or.inr l' => Or.inr (lt_trans l l')

/-- The ground order rescales on the right. -/
theorem mul_le_mul_right {a b : Pos} (c : Pos) (h : a ≤ b) :
    a * c ≤ b * c :=
  match h with
  | Or.inl e => Or.inl (by rw [e])
  | Or.inr hl => Or.inr (mul_lt_mul_right c hl)

/-- The product's injectivity: `a c = b c` forces `a = b`, the read
off the trichotomy against the moved sum. -/
theorem mul_right_cancel {a b c : Pos} (h : a * c = b * c) : a = b :=
  match trich a b with
  | .eq e => e
  | .lt g hg => absurd h (fun e => by
      have : a * c + g * c = a * c := by
        rw [← right_distrib, hg, e]
      exact add_ne_left (a * c) (g * c) this)
  | .gt g hg => absurd h (fun e => by
      have : b * c + g * c = b * c := by
        rw [← right_distrib, hg, ← e]
      exact add_ne_left (b * c) (g * c) this)

theorem mul_left_cancel {a b c : Pos} (h : a * b = a * c) : b = c :=
  mul_right_cancel (c := a) (by rw [mul_comm b a, mul_comm c a]; exact h)

theorem mul_right_comm (a b c : Pos) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b c, ← mul_assoc]

theorem mul_right_comm' (a b c : Pos) : a * (b * c) = a * c * b := by
  rw [← mul_assoc a b c, mul_right_comm a b c]

/-- The trailing factor rotates to the lead across the product. -/
theorem mul_rotate (a b c : Pos) : c * (a * b) = a * (b * c) := by
  rw [mul_left_comm c a b, mul_comm c b]

/-- The rotation at a fourth factor riding: the third member leads
with the first folded past the second onto the fourth. -/
theorem mul_rotate' (a b c d : Pos) :
    a * b * (c * d) = c * (a * (b * d)) := by
  rw [mul_assoc a b (c * d), mul_left_comm b c d,
    mul_left_comm a c (b * d)]

/-- A square reads its root: `a a = b b` forces `a = b`, the
trichotomy against the product's strict monotonicity. -/
theorem mul_self_cancel {a b : Pos} (h : a * a = b * b) : a = b :=
  match trich a b with
  | .eq e => e
  | .lt g hg =>
    absurd h (by
      have h1 : a * a < b * a := mul_lt_mul_right a ⟨g, hg⟩
      have h2 : b * a < b * b := by
        rw [mul_comm b a]
        exact mul_lt_mul_right b ⟨g, hg⟩
      exact lt_ne (lt_trans h1 h2))
  | .gt g hg =>
    absurd h.symm (by
      have h1 : b * b < a * b := mul_lt_mul_right b ⟨g, hg⟩
      have h2 : a * b < a * a := by
        rw [mul_comm a b]
        exact mul_lt_mul_right a ⟨g, hg⟩
      exact lt_ne (lt_trans h1 h2))

/-- The cofactor is one value by the product's injectivity where it
exists, the witness a field of its stated factorization. -/
theorem cofactor_unique {y c c' x : Pos} (h : y * c = x)
    (h' : y * c' = x) : c = c' :=
  mul_left_cancel (h.trans h'.symm)

/-- The ground datum's power at a natural key, the product's own
fold from the unit. -/
def Pos.pow (a : Pos) : Nat → Pos
  | 0 => Pos.one
  | k + 1 => a * Pos.pow a k

/-- The power's computing read at the stored count, the kernel's
own literal power: the value sites read here, while a display
reads the defining fold `Pos.pow`, the recursion's own
spelling. -/
def Pos.powC (a : Pos) (k : Nat) : Pos :=
  ⟨Nat.pow (a.pred + 1) k - 1⟩

private theorem pow_pred_succ (a : Pos) :
    ∀ k : Nat, (Pos.pow a k).pred + 1 = Nat.pow (a.pred + 1) k
  | 0 => rfl
  | k + 1 => by
    show a.pred * (Pos.pow a k).pred + a.pred + (Pos.pow a k).pred + 1
      = Nat.pow (a.pred + 1) (k + 1)
    rw [show Nat.pow (a.pred + 1) (k + 1)
        = Nat.pow (a.pred + 1) k * (a.pred + 1) from rfl,
      ← pow_pred_succ a k, Nat.succ_mul, Nat.mul_succ,
      Nat.mul_comm (Pos.pow a k).pred a.pred,
      Nat.add_assoc (a.pred * (Pos.pow a k).pred) a.pred
        (Pos.pow a k).pred,
      Nat.add_comm a.pred (Pos.pow a k).pred,
      ← Nat.add_assoc (a.pred * (Pos.pow a k).pred)
        (Pos.pow a k).pred a.pred,
      Nat.add_assoc (a.pred * (Pos.pow a k).pred + (Pos.pow a k).pred)
        a.pred 1]

/-- The computing read is the displayed fold, key by key. -/
theorem Pos.powC_eq (a : Pos) (k : Nat) : Pos.powC a k = Pos.pow a k := by
  show (⟨Nat.pow (a.pred + 1) k - 1⟩ : Pos) = Pos.pow a k
  rw [← pow_pred_succ a k]
  rfl

/-- The unit base's power reads the unit at every count. -/
theorem Pos.powC_one : ∀ k : Nat, Pos.powC Pos.one k = Pos.one
  | 0 => rfl
  | k + 1 => by
    rw [Pos.powC_eq,
      show Pos.pow Pos.one (k + 1) = Pos.one * Pos.pow Pos.one k
        from rfl,
      one_mul, ← Pos.powC_eq, Pos.powC_one k]

/-- The power's product splits over its base. -/
theorem Pos.pow_mul (x y : Pos) : ∀ q : Nat,
    Pos.pow (x * y) q = Pos.pow x q * Pos.pow y q
  | 0 => (mul_one Pos.one).symm
  | q + 1 => by
    show x * y * Pos.pow (x * y) q
      = x * Pos.pow x q * (y * Pos.pow y q)
    rw [Pos.pow_mul x y q,
      mul_mul_mul_comm x (Pos.pow x q) y (Pos.pow y q)]

/-- The power at a summed key is the powers' product, the fold's own
regrouping. -/
theorem Pos.pow_add (a : Pos) (m : Nat) : ∀ n : Nat,
    Pos.pow a (m + n) = Pos.pow a m * Pos.pow a n
  | 0 => (mul_one (Pos.pow a m)).symm
  | n + 1 => by
    show a * Pos.pow a (m + n) = Pos.pow a m * (a * Pos.pow a n)
    rw [Pos.pow_add a m n, mul_left_comm]

/-- The second power is the square. -/
theorem Pos.pow_two (x : Pos) : Pos.pow x 2 = x * x := by
  show x * (x * Pos.one) = x * x
  rw [mul_one x]

/-- The power is monotone in its base. -/
theorem Pos.pow_le {x y : Pos} (h : x ≤ y) : ∀ q : Nat,
    Pos.pow x q ≤ Pos.pow y q
  | 0 => Or.inl rfl
  | q + 1 => by
    show x * Pos.pow x q ≤ y * Pos.pow y q
    refine le_trans (mul_le_mul_right (Pos.pow x q) h) ?_
    rw [mul_comm y (Pos.pow x q), mul_comm y (Pos.pow y q)]
    exact mul_le_mul_right y (Pos.pow_le h q)

/-! The division with remainder: the quotient and the remainder as
occupancy data (`none` the absent value at the read's own
occupancy), off the kernel's division at the values. -/

/-- The division with remainder at `a` against `b` (`def:ground`'s
division read): the quotient and the remainder, `a = b q + r` with
`r` below `b` at the occupancy reads, the naming identity
`natDivRead`'s at the values. -/
def divMod (a b : Pos) : Option Pos × Option Pos :=
  (match (a.pred + 1) / (b.pred + 1) with
    | 0 => none
    | n + 1 => some ⟨n⟩,
   match (a.pred + 1) % (b.pred + 1) with
    | 0 => none
    | n + 1 => some ⟨n⟩)

/-- The division's naming read at its output, decidable: the
reconstruction `b q + r = a` with the remainder below the divisor. -/
def divModRead (a b : Pos) : Prop :=
  match divMod a b with
  | (some q, some r) => b * q + r = a ∧ r < b
  | (some q, none) => b * q = a
  | (none, some r) => r = a ∧ r < b
  | (none, none) => False

instance instGround9 (a b : Pos) : Decidable (divModRead a b) :=
  match h : divMod a b with
  | (some _, some _) => by
    unfold divModRead; rw [h]; exact inferInstanceAs (Decidable (_ ∧ _))
  | (some _, none) => by
    unfold divModRead; rw [h]; exact inferInstanceAs (Decidable (_ = _))
  | (none, some _) => by
    unfold divModRead; rw [h]; exact inferInstanceAs (Decidable (_ ∧ _))
  | (none, none) => by
    unfold divModRead; rw [h]; exact inferInstanceAs (Decidable False)

/-! The division equation, axiom-free: core `Nat.div` and
`Nat.modCore` compute by one fuel descent each (`Nat.div.go` and
`Nat.modCore.go`, structural on the fuel, their step equations
bare `rfl`; the two outer defs open at `delta`, the tree's own
spelling), the two descents matched step for step, and the joint
invariant reads the naming identity along the fuel. -/

private theorem divGoStep (y : Nat) (hy : 0 < y) (fuel x : Nat)
    (h : x < fuel + 1) :
    Nat.div.go y hy (fuel + 1) x h
      = if hle : y ≤ x then
          Nat.div.go y hy fuel (x - y)
            (Nat.lt_of_lt_of_le
              (Nat.sub_lt (Nat.lt_of_lt_of_le hy hle) hy)
              (Nat.le_of_lt_succ h)) + 1
        else 0 := rfl

private theorem modGoStep (y : Nat) (hy : 0 < y) (fuel x : Nat)
    (h : x < fuel + 1) :
    Nat.modCore.go y hy (fuel + 1) x h
      = if hle : y ≤ x then
          Nat.modCore.go y hy fuel (x - y)
            (Nat.lt_of_lt_of_le
              (Nat.sub_lt (Nat.lt_of_lt_of_le hy hle) hy)
              (Nat.le_of_lt_succ h))
        else x := rfl

private theorem goSpec (y : Nat) (hy : 0 < y) :
    ∀ (fuel x : Nat) (h : x < fuel),
      y * Nat.div.go y hy fuel x h
          + Nat.modCore.go y hy fuel x h = x
  | 0, x, h => absurd h (Nat.not_lt_zero x)
  | fuel + 1, x, h => by
    rw [divGoStep y hy fuel x h, modGoStep y hy fuel x h]
    by_cases hle : y ≤ x
    · rw [dif_pos hle, dif_pos hle]
      have hlt : x - y < fuel :=
        Nat.lt_of_lt_of_le
          (Nat.sub_lt (Nat.lt_of_lt_of_le hy hle) hy)
          (Nat.le_of_lt_succ h)
      rw [Nat.mul_succ, Nat.add_right_comm,
        goSpec y hy fuel (x - y) hlt,
        subAdd hle]
    · rw [dif_neg hle, dif_neg hle, Nat.mul_zero, Nat.zero_add]

private theorem divEqGo (A B : Nat) (hB : 0 < B) :
    A / B = Nat.div.go B hB (A + 1) A
      (Nat.lt_succ_of_le (Nat.le_refl A)) := by
  show Nat.div A B = _
  delta Nat.div
  show (if hy : 0 < B then Nat.div.go B hy (A + 1) A
      (Nat.lt_succ_of_le (Nat.le_refl A)) else 0) = _
  rw [dif_pos hB]

private theorem modCoreEqGo (A B : Nat) (hB : 0 < B) :
    Nat.modCore A B = Nat.modCore.go B hB (A + 1) A
      (Nat.lt_succ_of_le (Nat.le_refl A)) := by
  delta Nat.modCore
  show (if hy : 0 < B then Nat.modCore.go B hy (A + 1) A
      (Nat.lt_succ_of_le (Nat.le_refl A)) else A) = _
  rw [dif_pos hB]

private theorem goCongr (y : Nat) (hy : 0 < y) (fuel : Nat)
    {x x' : Nat} (hx : x = x') (h : x < fuel) :
    Nat.div.go y hy fuel x h = Nat.div.go y hy fuel x' (hx ▸ h) := by
  cases hx; rfl

private theorem goMul (y : Nat) (hy : 0 < y) :
    ∀ (a fuel : Nat) (h : a * y < fuel),
      Nat.div.go y hy fuel (a * y) h = a
  | 0, fuel + 1, h => by
    rw [goCongr y hy (fuel + 1) (Nat.zero_mul y) h]
    show (if _ : y ≤ 0 then Nat.div.go y hy fuel (0 - y) _ + 1
      else 0) = 0
    rw [dif_neg (fun hc => Nat.not_succ_le_zero _
      (Nat.lt_of_lt_of_le hy hc))]
  | a + 1, fuel + 1, h => by
    have hle : y ≤ (a + 1) * y := by
      rw [Nat.succ_mul]
      exact Nat.le_add_left y (a * y)
    have hsub : (a + 1) * y - y = a * y := by
      rw [Nat.succ_mul, Nat.add_comm (a * y) y]
      exact addSubSelfL y (a * y)
    have hlt : a * y < fuel := by
      have h2 : a * y < (a + 1) * y := by
        rw [Nat.succ_mul, Nat.add_comm (a * y) y]
        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left hy)
          (Nat.le_refl _)
      exact Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ h)
    show (if _ : y ≤ (a + 1) * y then
        Nat.div.go y hy fuel ((a + 1) * y - y) _ + 1 else 0) = a + 1
    rw [dif_pos hle, goCongr y hy fuel hsub, goMul y hy a fuel hlt]

theorem divMulSelf (a y : Nat) (hy : 0 < y) :
    (a * y) / y = a := by
  show Nat.div (a * y) y = a
  delta Nat.div
  rw [dif_pos hy]
  exact goMul y hy a ((a * y).succ) (Nat.lt_succ_self _)

/-- The division's naming identity at core `Nat.div` and
`Nat.mod`: the reconstruction with the remainder below the
divisor, at every occupied divisor.  A theorem, not a read: the
name follows `divModRead_all`'s family, the decidable read it
generalizes standing beside it. -/
theorem natDivRead (A B : Nat) (hB : 0 < B) :
    B * (A / B) + A % B = A ∧ A % B < B := by
  refine ⟨?_, Nat.mod_lt A hB⟩
  match A with
  | 0 =>
    have hd : 0 / B = 0 := by
      rw [divEqGo 0 B hB, divGoStep B hB 0 0,
        dif_neg (fun hle : B ≤ 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hB hle))]
    show B * (0 / B) + 0 = 0
    rw [hd, Nat.mul_zero]
  | n + 1 =>
    by_cases hle : B ≤ n + 1
    · have hm : (n + 1) % B = Nat.modCore (n + 1) B := by
        show (if B ≤ n + 1 then Nat.modCore (n + 1) B else n + 1) = _
        rw [if_pos hle]
      rw [hm, divEqGo (n + 1) B hB, modCoreEqGo (n + 1) B hB]
      exact goSpec B hB (n + 2) (n + 1)
        (Nat.lt_succ_of_le (Nat.le_refl (n + 1)))
    · have hm : (n + 1) % B = n + 1 := by
        show (if B ≤ n + 1 then Nat.modCore (n + 1) B else n + 1) = _
        rw [if_neg hle]
      rw [hm, divEqGo (n + 1) B hB, divGoStep B hB (n + 1) (n + 1),
        dif_neg hle, Nat.mul_zero, Nat.zero_add]

/-- A count whose divisor multiple sits at or below a natural sits
at or below the quotient: the naming identity's reconstruction
against the remainder bound, one more multiple exceeding. -/
theorem le_div_of_mul_le (m d K : Nat) (hd : 0 < d) (h : d * m ≤ K) :
    m ≤ K / d := by
  cases Nat.lt_or_ge (K / d) m with
  | inr hge => exact hge
  | inl hlt =>
    have h1 : d * (K / d + 1) ≤ K :=
      Nat.le_trans (Nat.mul_le_mul_left d hlt) h
    have h2 := natDivRead K d hd
    rw [Nat.mul_succ] at h1
    have h3 : d * (K / d) + d ≤ d * (K / d) + K % d :=
      Nat.le_trans h1 (Nat.le_of_eq h2.1.symm)
    exact absurd (Nat.lt_of_le_of_lt (leCancelL _ h3) h2.2)
      (Nat.lt_irrefl d)

/-- The ends' sum halved sits strictly inside a segment of length two
or beyond: the foot's successor sits at or below the quotient at its
double (`le_div_of_mul_le`), and the division's naming identity
(`natDivRead`) reads the halved sum's double at or below the sum. -/
theorem halfSum_inside (lo hi : Nat) (h : lo + 1 < hi) :
    lo < (lo + hi) / 2 ∧ (lo + hi) / 2 < hi := by
  obtain ⟨e, _⟩ := natDivRead (lo + hi) 2 (Nat.succ_pos 1)
  constructor
  · refine le_div_of_mul_le (lo + 1) 2 (lo + hi) (Nat.succ_pos 1) ?_
    rw [Nat.two_mul, Nat.add_assoc, Nat.add_comm 1 (lo + 1)]
    exact Nat.add_le_add_left h lo
  · match Nat.lt_or_ge ((lo + hi) / 2) hi with
    | Or.inl h1 => exact h1
    | Or.inr h1 =>
      have h2 : 2 * hi ≤ 2 * ((lo + hi) / 2) := Nat.mul_le_mul_left 2 h1
      have h3 : 2 * hi ≤ lo + hi := by
        rw [← e]
        exact Nat.le_trans h2 (Nat.le_add_right _ _)
      have h4 : lo + hi < 2 * hi := by
        rw [Nat.two_mul]
        exact Nat.add_lt_add_right (Nat.lt_trans (Nat.lt_succ_self lo) h) hi
      exact absurd (Nat.lt_of_lt_of_le h4 h3) (Nat.lt_irrefl _)

/-- The halving search on a segment: at a read refused at the foot and
held at the top, a held key whose predecessor refuses (`bisect_read`),
the least held key at a read stepping up the keys
(`bisectFrom_eq_firstAt`); the midpoint the ends' sum halved, the depth
the search's budget, the top at exhaustion. -/
def bisect (P : Nat → Prop) [DecidablePred P] : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (fun m => if P m then bisect P f lo m else bisect P f m hi) ((lo + hi) / 2)
    else hi

/-- The halving search from a stated start at a stated budget: the
start where the read holds there, and the segment's search from the
start to the budget's end otherwise. -/
def bisectFrom (P : Nat → Prop) [DecidablePred P] (s b : Nat) : Nat :=
  if P s then s else bisect P b s (s + b)

/-- A read stepping up the keys holds at every sum beyond a held key. -/
theorem stepMono_add (P : Nat → Prop) (hm : ∀ k, P k → P (k + 1)) :
    ∀ (d k : Nat), P k → P (k + d)
  | 0, _, h => h
  | d + 1, k, h => hm _ (stepMono_add P hm d k h)

/-- A read stepping up the keys holds at or beyond a held key. -/
theorem stepMono_of_le (P : Nat → Prop) (hm : ∀ k, P k → P (k + 1)) {a b : Nat}
    (h : a ≤ b) (ha : P a) : P b := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd]
  exact stepMono_add P hm d a ha

/-- The segment's search reads a held key beyond the foot whose
predecessor refuses: at a foot refusing, a top holding, and a budget
at or beyond the segment's length. -/
theorem bisect_read (P : Nat → Prop) [DecidablePred P] :
    ∀ (f lo hi : Nat), ¬ P lo → P hi → lo < hi → hi ≤ lo + f →
      P (bisect P f lo hi) ∧ lo < bisect P f lo hi
      ∧ ∃ j, bisect P f lo hi = j + 1 ∧ ¬ P j
  | 0, lo, _, _, _, hlt, hle => absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl lo)
  | f + 1, lo, hi, hlo, hhi, hlt, hle => by
    have hunf : bisect P (f + 1) lo hi
        = if lo + 1 < hi then
            (fun m => if P m then bisect P f lo m else bisect P f m hi) ((lo + hi) / 2)
          else hi := rfl
    rw [hunf]
    match (inferInstance : Decidable (lo + 1 < hi)) with
    | isFalse h =>
      rw [if_neg h]
      exact ⟨hhi, hlt, lo, Nat.le_antisymm (Nat.le_of_not_lt h) hlt, hlo⟩
    | isTrue h =>
      rw [if_pos h]
      have hm : ∀ m, lo < m → m < hi →
          P (if P m then bisect P f lo m else bisect P f m hi)
          ∧ lo < (if P m then bisect P f lo m else bisect P f m hi)
          ∧ ∃ j, (if P m then bisect P f lo m else bisect P f m hi) = j + 1 ∧ ¬ P j := by
        intro m hlom hmhi
        match (inferInstance : Decidable (P m)) with
        | isTrue hp =>
          rw [if_pos hp]
          exact bisect_read P f lo m hlo hp hlom
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hmhi hle))
        | isFalse hp =>
          rw [if_neg hp]
          obtain ⟨h1, h2, h3⟩ := bisect_read P f m hi hp hhi hmhi (by
            refine Nat.le_trans hle ?_
            show lo + f + 1 ≤ m + f
            rw [Nat.add_right_comm lo f 1]
            exact Nat.add_le_add_right hlom f)
          exact ⟨h1, Nat.lt_trans hlom h2, h3⟩
      exact hm _ (halfSum_inside lo hi h).1 (halfSum_inside lo hi h).2

/-- At a read stepping up the keys and refused at the top, the
segment's search reads the top: every midpoint refuses with it. -/
theorem bisect_exhaust (P : Nat → Prop) [DecidablePred P] (hm : ∀ k, P k → P (k + 1)) :
    ∀ (f lo hi : Nat), ¬ P hi → bisect P f lo hi = hi
  | 0, _, _, _ => rfl
  | f + 1, lo, hi, hhi => by
    have hunf : bisect P (f + 1) lo hi
        = if lo + 1 < hi then
            (fun m => if P m then bisect P f lo m else bisect P f m hi) ((lo + hi) / 2)
          else hi := rfl
    rw [hunf]
    match (inferInstance : Decidable (lo + 1 < hi)) with
    | isFalse h => rw [if_neg h]
    | isTrue h =>
      rw [if_pos h]
      show (if P ((lo + hi) / 2) then bisect P f lo ((lo + hi) / 2)
        else bisect P f ((lo + hi) / 2) hi) = hi
      have hp : ¬ P ((lo + hi) / 2) := fun hp =>
        hhi (stepMono_of_le P hm (Nat.le_of_lt (halfSum_inside lo hi h).2) hp)
      rw [if_neg hp]
      exact bisect_exhaust P hm f _ hi hhi

/-- The segment's search sits at or beyond its foot. -/
theorem bisect_ge (P : Nat → Prop) [DecidablePred P] :
    ∀ (f lo hi : Nat), lo ≤ hi → lo ≤ bisect P f lo hi
  | 0, _, _, h => h
  | f + 1, lo, hi, hlh => by
    have hunf : bisect P (f + 1) lo hi
        = if lo + 1 < hi then
            (fun m => if P m then bisect P f lo m else bisect P f m hi) ((lo + hi) / 2)
          else hi := rfl
    rw [hunf]
    match (inferInstance : Decidable (lo + 1 < hi)) with
    | isFalse h => rw [if_neg h]; exact hlh
    | isTrue h =>
      rw [if_pos h]
      show lo ≤ (if P ((lo + hi) / 2) then bisect P f lo ((lo + hi) / 2)
        else bisect P f ((lo + hi) / 2) hi)
      match (inferInstance : Decidable (P ((lo + hi) / 2))) with
      | isTrue hp =>
        rw [if_pos hp]
        exact bisect_ge P f lo _ (Nat.le_of_lt (halfSum_inside lo hi h).1)
      | isFalse hp =>
        rw [if_neg hp]
        exact Nat.le_trans (Nat.le_of_lt (halfSum_inside lo hi h).1)
          (bisect_ge P f _ hi (Nat.le_of_lt (halfSum_inside lo hi h).2))

/-- The search from a start sits at or beyond its start. -/
theorem bisectFrom_ge (P : Nat → Prop) [DecidablePred P] (s b : Nat) :
    s ≤ bisectFrom P s b := by
  have hunf : bisectFrom P s b = if P s then s else bisect P b s (s + b) := rfl
  rw [hunf]
  match (inferInstance : Decidable (P s)) with
  | isTrue h => rw [if_pos h]; exact Nat.le_refl s
  | isFalse h => rw [if_neg h]; exact bisect_ge P b s (s + b) (Nat.le_add_right s b)

/-- The read at the budget's end reads the search's answer. -/
theorem bisectFrom_hit (P : Nat → Prop) [DecidablePred P] (s b : Nat) (hb : P (s + b)) :
    P (bisectFrom P s b) := by
  have hunf : bisectFrom P s b = if P s then s else bisect P b s (s + b) := rfl
  rw [hunf]
  match (inferInstance : Decidable (P s)) with
  | isTrue h => rw [if_pos h]; exact h
  | isFalse h =>
    rw [if_neg h]
    cases b with
    | zero => exact absurd hb h
    | succ b =>
      exact (bisect_read P (b + 1) s (s + (b + 1)) h hb
        (Nat.lt_add_of_pos_right (Nat.succ_pos b)) (Nat.le_refl _)).1

/-- At a read stepping up the keys and refused at the budget's end,
the search reads the budget's end. -/
theorem bisectFrom_miss (P : Nat → Prop) [DecidablePred P] (hm : ∀ k, P k → P (k + 1))
    (s b : Nat) (hb : ¬ P (s + b)) : bisectFrom P s b = s + b := by
  have hunf : bisectFrom P s b = if P s then s else bisect P b s (s + b) := rfl
  have hs : ¬ P s := fun h => hb (stepMono_of_le P hm (Nat.le_add_right s b) h)
  rw [hunf, if_neg hs]
  exact bisect_exhaust P hm b s (s + b) hb

/-- At a read stepping up the keys, every key from the start below
the search's answer refuses. -/
theorem bisectFrom_below (P : Nat → Prop) [DecidablePred P] (hm : ∀ k, P k → P (k + 1))
    (s b : Nat) : ∀ j, s ≤ j → j < bisectFrom P s b → ¬ P j := by
  intro j hsj hj hpj
  match (inferInstance : Decidable (P (s + b))) with
  | isFalse hb =>
    rw [bisectFrom_miss P hm s b hb] at hj
    exact hb (stepMono_of_le P hm (Nat.le_of_lt hj) hpj)
  | isTrue hb =>
    have hunf : bisectFrom P s b = if P s then s else bisect P b s (s + b) := rfl
    rw [hunf] at hj
    match (inferInstance : Decidable (P s)) with
    | isTrue h =>
      rw [if_pos h] at hj
      exact absurd hsj (Nat.not_le_of_lt hj)
    | isFalse h =>
      rw [if_neg h] at hj
      cases b with
      | zero => exact absurd hb h
      | succ b =>
        obtain ⟨_, _, k, hk, hpk⟩ := bisect_read P (b + 1) s (s + (b + 1)) h hb
          (Nat.lt_add_of_pos_right (Nat.succ_pos b)) (Nat.le_refl _)
        rw [hk] at hj
        exact hpk (stepMono_of_le P hm (Nat.le_of_lt_succ hj) hpj)

/-- The least natural at a read from a start is one key: two held
keys at or beyond the start with every key from the start below each
refusing are equal, the smaller refused by the larger's read. -/
theorem least_unique (P : Nat → Prop) (s a b : Nat) (hsa : s ≤ a) (hsb : s ≤ b)
    (ha : P a) (hb : P b) (la : ∀ j, s ≤ j → j < a → ¬ P j)
    (lb : ∀ j, s ≤ j → j < b → ¬ P j) : a = b := by
  match Nat.lt_or_ge a b with
  | Or.inl h => exact absurd ha (lb a hsa h)
  | Or.inr h =>
    match Nat.lt_or_ge b a with
    | Or.inl h' => exact absurd hb (la b hsb h')
    | Or.inr h' => exact Nat.le_antisymm h' h

/-- The halving search and the walk read one key at a read stepping
up the keys: the least held natural from the start, or the budget's
end where the read refuses throughout. -/
theorem bisectFrom_eq_firstAt (P : Nat → Prop) [DecidablePred P]
    (hm : ∀ k, P k → P (k + 1)) (s b : Nat) : bisectFrom P s b = firstAt P s b := by
  match (inferInstance : Decidable (P (s + b))) with
  | isTrue hb =>
    exact least_unique P s _ _ (bisectFrom_ge P s b) (firstAt_ge P b s)
      (bisectFrom_hit P s b hb) (firstAt_hit P b s hb) (bisectFrom_below P hm s b)
      (fun j hsj hj => firstAt_below P b s j hsj hj)
  | isFalse hb =>
    have hf : ¬ P (firstAt P s b) := fun h =>
      hb (stepMono_of_le P hm (firstAt_le P b s) h)
    rw [bisectFrom_miss P hm s b hb, firstAt_miss P b s hf]

/-- The clearing quotient at an occupied divisor: the least count
whose divisor multiple clears the datum, the division at the datum
joined to the divisor's predecessor. -/
def ceilAt (N A : Nat) : Nat := (N + (A - 1)) / A

/-- The quotient's multiple clears the datum. -/
theorem ceilAt_ge (N A : Nat) (hA : 0 < A) : N ≤ A * ceilAt N A := by
  have h := natDivRead (N + (A - 1)) A hA
  have hr : (N + (A - 1)) % A ≤ A - 1 := by
    refine Nat.le_of_lt_succ ?_
    show (N + (A - 1)) % A < A - 1 + 1
    rw [subAdd hA]
    exact h.2
  have h1 : A * ((N + (A - 1)) / A) + (N + (A - 1)) % A
      ≤ A * ((N + (A - 1)) / A) + (A - 1) :=
    Nat.add_le_add_left hr _
  rw [h.1] at h1
  exact leCancelR (A - 1) h1

/-- The quotient is least at the comparison. -/
theorem ceilAt_least (N A q : Nat) (hA : 0 < A) (hq : N ≤ A * q) : ceilAt N A ≤ q := by
  refine Nat.le_of_not_lt (fun hlt => ?_)
  have h := natDivRead (N + (A - 1)) A hA
  have h3 : A * (q + 1) ≤ A * ceilAt N A := Nat.mul_le_mul_left A hlt
  have h4 : A * ceilAt N A ≤ N + (A - 1) := by
    rw [← h.1]
    exact Nat.le_add_right _ _
  have h5 : N + (A - 1) < A * q + A := Nat.add_lt_add_of_le_of_lt hq (subOneLt hA)
  rw [Nat.mul_succ] at h3
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h3 h4) h5)

/-- The division read holds at every pair: the general theorem, the
reconstruction and the remainder bound off the naming identity. -/
theorem divModRead_all (a b : Pos) : divModRead a b := by
  have hB : 0 < b.pred + 1 := Nat.succ_pos b.pred
  have hread := natDivRead (a.pred + 1) (b.pred + 1) hB
  unfold divModRead divMod
  match hq : (a.pred + 1) / (b.pred + 1),
      hr : (a.pred + 1) % (b.pred + 1) with
  | 0, 0 =>
    rw [hq, hr, Nat.mul_zero] at hread
    exact Nat.noConfusion hread.1
  | q + 1, 0 =>
    rw [hq, hr, Nat.add_zero, Nat.mul_succ] at hread
    show Pos.mk (b.pred * q + b.pred + q) = a
    have h1 : b.pred * q + b.pred + q + 1
        = (b.pred + 1) * q + (b.pred + 1) := by
      rw [Nat.succ_mul b.pred q,
        Nat.add_right_comm (b.pred * q) b.pred q, Nat.add_assoc]
    exact congrArg Pos.mk (Nat.succ.inj (h1.trans hread.1))
  | 0, r + 1 =>
    rw [hq, hr, Nat.mul_zero, Nat.zero_add] at hread
    refine ⟨?_, ?_⟩
    · exact congrArg Pos.mk (Nat.succ.inj hread.1)
    · exact ⟨⟨b.pred - (r + 1)⟩, by
        show Pos.mk (r + (b.pred - (r + 1)) + 1) = b
        have hle2 : r + 1 ≤ b.pred := Nat.le_of_lt_succ hread.2
        exact congrArg Pos.mk (by
          rw [Nat.add_right_comm r (b.pred - (r + 1)) 1]
          exact natAddSubCancel hle2)⟩
  | q + 1, r + 1 =>
    refine ⟨?_, ?_⟩
    · show Pos.mk (b.pred * q + b.pred + q + r + 1) = a
      rw [hq, hr] at hread
      have h1 : b.pred * q + b.pred + q + r + 1 + 1
          = (b.pred + 1) * q + (b.pred + 1) + (r + 1) := by
        rw [Nat.succ_mul b.pred q,
          Nat.add_right_comm (b.pred * q) b.pred q,
          Nat.add_assoc (b.pred * q + q + b.pred) r 1,
          Nat.add_assoc (b.pred * q + q + b.pred) (r + 1) 1,
          ← Nat.add_assoc (b.pred * q + q) b.pred 1,
          Nat.add_assoc (b.pred * q + q + b.pred) 1 (r + 1),
          Nat.add_comm 1 (r + 1)]
      exact congrArg Pos.mk (Nat.succ.inj (h1.trans hread.1))
    · rw [hq, hr] at hread
      exact ⟨⟨b.pred - (r + 1)⟩, by
        show Pos.mk (r + (b.pred - (r + 1)) + 1) = b
        have hle2 : r + 1 ≤ b.pred := Nat.le_of_lt_succ hread.2
        exact congrArg Pos.mk (by
          rw [Nat.add_right_comm r (b.pred - (r + 1)) 1]
          exact (natAddSubCancel hle2))⟩

/-- The remainder at a vacant divisor is the value itself. -/
theorem modZero : ∀ (x : Nat), x % 0 = x
  | 0 => rfl
  | n + 1 => by
    show (if 0 ≤ n + 1 then Nat.modCore (n + 1) 0 else n + 1) = n + 1
    rw [if_pos (Nat.zero_le (n + 1))]
    delta Nat.modCore
    exact dif_neg (Nat.lt_irrefl 0)

/-- The remainder's uniqueness: a stated reconstruction with its
remainder below the divisor reads the core remainder, the naming
identity's one value. -/
theorem modOf {d q r x : Nat} (hd : 0 < d) (he : d * q + r = x)
    (hr : r < d) : x % d = r := by
  have hn := natDivRead x d hd
  cases Nat.lt_or_ge (x / d) q with
  | inl hlt =>
    match Nat.le.dest hlt with
    | ⟨g, hg⟩ =>
      have hq : q = x / d + 1 + g := by rw [← hg]
      have harith : d * (x / d + 1 + g) + r
          = d * (x / d) + (d + (d * g + r)) := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc (d * (x / d) + d) (d * g) r,
          Nat.add_assoc (d * (x / d)) d (d * g + r)]
      rw [hq] at he
      have h3 : d * (x / d) + (d + (d * g + r)) = x :=
        harith.symm.trans he
      have hcan : x % d = d + (d * g + r) :=
        addCancelL (d * (x / d)) (hn.1.trans h3.symm)
      have hge2 : d ≤ x % d := by
        rw [hcan]; exact Nat.le_add_right d (d * g + r)
      exact (Nat.lt_irrefl d (Nat.lt_of_le_of_lt hge2 hn.2)).elim
  | inr hge =>
    cases Nat.lt_or_ge q (x / d) with
    | inl hlt' =>
      match Nat.le.dest hlt' with
      | ⟨g, hg⟩ =>
        have hq : x / d = q + 1 + g := by rw [← hg]
        have hn1 := hn.1
        rw [hq] at hn1
        have harith : d * (q + 1 + g) + x % d
            = d * q + (d + (d * g + x % d)) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one,
            Nat.add_assoc (d * q + d) (d * g) (x % d),
            Nat.add_assoc (d * q) d (d * g + x % d)]
        have h3 : d * q + (d + (d * g + x % d)) = x :=
          harith.symm.trans hn1
        have hcan : r = d + (d * g + x % d) :=
          addCancelL (d * q) (he.trans h3.symm)
        have hge2 : d ≤ r := by
          rw [hcan]; exact Nat.le_add_right d (d * g + x % d)
        exact (Nat.lt_irrefl d (Nat.lt_of_le_of_lt hge2 hr)).elim
    | inr hge' =>
      have hq : q = x / d := Nat.le_antisymm hge hge'
      rw [hq] at he
      exact addCancelL (d * (x / d)) (hn.1.trans he.symm)

/-- A divisor's multiple withdraws from the remainder. -/
theorem modAddMul (x a d : Nat) : (x + a * d) % d = x % d := by
  match d with
  | 0 => rw [Nat.mul_zero, Nat.add_zero]
  | e + 1 =>
    have hd : 0 < e + 1 := Nat.succ_pos e
    have hn := natDivRead x (e + 1) hd
    refine modOf (q := x / (e + 1) + a) hd ?_ hn.2
    rw [Nat.mul_add, Nat.add_right_comm, hn.1,
      Nat.mul_comm (e + 1) a]

/-- The vacant value's remainder. -/
theorem modZeroLeft (d : Nat) : 0 % d = 0 := by
  match d with
  | 0 => exact modZero 0
  | e + 1 =>
    exact modOf (q := 0) (Nat.succ_pos e)
      (by rw [Nat.mul_zero]) (Nat.succ_pos e)

/-- The remainder of a divisor's multiple, the unit count. -/
theorem modMulSelf (a d : Nat) : (a * d) % d = 0 := by
  have h := modAddMul 0 a d
  rw [Nat.zero_add] at h
  rw [h]
  exact modZeroLeft d

/-- The remainder of a sum reads at the parts' remainders. -/
theorem modAdd (x y d : Nat) : (x % d + y % d) % d = (x + y) % d := by
  match d with
  | 0 => rw [modZero x, modZero y]
  | e + 1 =>
    have hd : 0 < e + 1 := Nat.succ_pos e
    have hx := natDivRead x (e + 1) hd
    have hy := natDivRead y (e + 1) hd
    have hs : x % (e + 1) + y % (e + 1)
          + (x / (e + 1) + y / (e + 1)) * (e + 1) = x + y := by
      rw [Nat.mul_comm (x / (e + 1) + y / (e + 1)) (e + 1),
        Nat.mul_add (e + 1) (x / (e + 1)) (y / (e + 1)),
        Nat.add_add_add_comm (x % (e + 1)) (y % (e + 1))
          ((e + 1) * (x / (e + 1))) ((e + 1) * (y / (e + 1))),
        Nat.add_comm (x % (e + 1)) ((e + 1) * (x / (e + 1))),
        Nat.add_comm (y % (e + 1)) ((e + 1) * (y / (e + 1))),
        hx.1, hy.1]
    rw [← hs, modAddMul]

/-- The remainder is its own remainder, the residue read once. -/
theorem modMod (x n : Nat) : x % n % n = x % n := by
  have h := modAdd x 0 n
  rw [modZeroLeft n, Nat.add_zero, Nat.add_zero] at h
  exact h

/-- A value below the divisor is its own remainder. -/
theorem modOfLt (x c : Nat) (h : x < c) : x % c = x :=
  modOf (q := 0) (Nat.lt_of_le_of_lt (Nat.zero_le x) h)
    (by rw [Nat.mul_zero, Nat.zero_add]) h


/-- The quotient at a vacant divisor reads the count's unit. -/
theorem divZero (x : Nat) : x / 0 = 0 := by
  show Nat.div x 0 = 0
  delta Nat.div
  rw [dif_neg (fun h : 0 < 0 => Nat.lt_irrefl 0 h)]

/-- The vacant value's quotient. -/
theorem divZeroLeft : ∀ n : Nat, 0 / n = 0
  | 0 => divZero 0
  | e + 1 => by
    have h := divMulSelf 0 (e + 1) (Nat.succ_pos e)
    rw [Nat.zero_mul] at h
    exact h

/-- A quotient sits at or below its dividend: the naming identity's
reconstruction at an occupied divisor, the vacant divisor's read
outright. -/
theorem divLeSelf (a b : Nat) : a / b ≤ a := by
  match Nat.eq_zero_or_pos b with
  | Or.inl hb =>
    rw [hb, divZero]
    exact Nat.zero_le a
  | Or.inr hb =>
    have h1 := (natDivRead a b hb).1
    have h2 : b * (a / b) ≤ a := by
      have h2' : b * (a / b) ≤ b * (a / b) + a % b :=
        Nat.le_add_right _ _
      rw [h1] at h2'
      exact h2'
    have h3 : 1 * (a / b) ≤ b * (a / b) :=
      Nat.mul_le_mul_right (a / b) hb
    rw [Nat.one_mul] at h3
    exact Nat.le_trans h3 h2

/-- Increasing the dividend increases the quotient at a fixed
divisor, at the naming identity's multiple below the dividend. -/
theorem divMono (a b d : Nat) (h : a ≤ b) : a / d ≤ b / d := by
  cases d with
  | zero => rw [divZero, divZero]; exact Nat.le_refl 0
  | succ e =>
    obtain ⟨hdiv, _⟩ := natDivRead a (e + 1) (Nat.succ_pos e)
    exact le_div_of_mul_le (a / (e + 1)) (e + 1) b (Nat.succ_pos e)
      (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hdiv)) h)

/-- The remainder at the divisor joined once. -/
theorem modAddSelf (t L : Nat) : (t + L) % L = t % L := by
  have h := modAddMul t 1 L
  rw [Nat.one_mul] at h
  exact h

/-- The quotient at the divisor joined once to its multiple: the
successor. -/
theorem divAddSelf (t L : Nat) (hL : 0 < L) (ht : t % L = 0) :
    (t + L) / L = t / L + 1 := by
  have hd := (natDivRead t L hL).1
  rw [ht, Nat.add_zero] at hd
  have he : t + L = (t / L + 1) * L := by
    rw [Nat.succ_mul (t / L) L, Nat.mul_comm (t / L) L, hd]
  rw [he]
  exact divMulSelf (t / L + 1) L hL

/-- A divisor's own remainder, the count's unit. -/
theorem modSelf (L : Nat) : L % L = 0 := by
  have h := modMulSelf 1 L
  rw [Nat.one_mul] at h
  exact h

/-- A divisor's own quotient, one. -/
theorem divSelf (L : Nat) (hL : 0 < L) : L / L = 1 := by
  have h := divMulSelf 1 L hL
  rw [Nat.one_mul] at h
  exact h

/-- The entry at a key, the stated default beyond the list's top
(the core `getD` reads through a propext-bearing path). -/
def getAt {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | h :: _, 0 => h
  | _ :: t, n + 1 => getAt d t n

/-- A join's leading part at the first list's count is the first
list. -/
theorem take_append_self {α : Type} : ∀ (u v : List α),
    List.take u.length (u ++ v) = u
  | [], _ => rfl
  | a :: u, v => congrArg (List.cons a) (take_append_self u v)

/-- A join dropped at the first list's count is the second list. -/
theorem drop_append_self {α : Type} : ∀ (u v : List α),
    List.drop u.length (u ++ v) = v
  | [], _ => rfl
  | _ :: u, v => drop_append_self u v

/-- A read below the count is one value at every default. -/
theorem getAt_dflt {α : Type} (d d' : α) :
    ∀ (l : List α) (i : Nat), i < l.length → getAt d l i = getAt d' l i
  | [], i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, 0, _ => rfl
  | _ :: t, i + 1, hi => getAt_dflt d d' t i (Nat.lt_of_succ_lt_succ hi)

/-- Beyond a list's top the entry is the stated default. -/
theorem getAt_over {α : Type} (d : α) : ∀ (l : List α) (k : Nat),
    l.length ≤ k → getAt d l k = d
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: l, k + 1, h => getAt_over d l k (Nat.le_of_succ_le_succ h)

/-- A word sorted inside its length is sorted at every key: the
keys at or beyond the length read the vacant default. -/
theorem sortedAll (W : List Nat)
    (h : ∀ i, i + 1 < W.length →
      getAt 0 W (i + 1) ≤ getAt 0 W i) :
    ∀ i, getAt 0 W (i + 1) ≤ getAt 0 W i := by
  intro i
  by_cases hlt : i + 1 < W.length
  · exact h i hlt
  · rw [getAt_over 0 W (i + 1) (Nat.le_of_not_lt hlt)]
    exact Nat.zero_le _

/-- The componentwise gap of matched lists at the order, the tie's
lattice solution: the entry the gap where the order or the
equality holds, the solution absent at any reversed entry or an
unmatched length. -/
def tieGap : List Nat → List Nat → Option (List Nat)
  | [], [] => some []
  | [], _ :: _ => none
  | _ :: _, [] => none
  | a :: s, b :: t =>
    if b ≤ a then
      match tieGap s t with
      | some m => some ((a - b) :: m)
      | none => none
    else none

/-- The tie's reads at an occupied solution: the lengths match and
every entry joins the second display to the first. -/
theorem tieGap_reads : ∀ (y z m : List Nat),
    tieGap y z = some m →
    m.length = y.length ∧ z.length = y.length
      ∧ ∀ i, i < y.length →
          getAt 0 m i + getAt 0 z i = getAt 0 y i
  | [], [], m, h => by
    rw [← Option.some.inj h]
    exact ⟨rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: s, b :: t, m, h => by
    have h' : (if b ≤ a then
        match tieGap s t with
        | some m' => some ((a - b) :: m')
        | none => none
      else none) = some m := h
    by_cases hba : b ≤ a
    · rw [if_pos hba] at h'
      cases hst : tieGap s t with
      | none =>
        rw [hst] at h'
        exact nomatch h'
      | some m' =>
        rw [hst] at h'
        obtain ⟨hl, hzl, hent⟩ := tieGap_reads s t m' hst
        rw [← Option.some.inj h']
        refine ⟨congrArg Nat.succ hl, congrArg Nat.succ hzl, ?_⟩
        intro i hi
        match i with
        | 0 =>
          show a - b + b = a
          exact subAdd hba
        | i + 1 =>
          exact hent i (Nat.lt_of_succ_lt_succ hi)
    · rw [if_neg hba] at h'
      exact nomatch h'

/-- The tie's construction: matched lengths with every entry
joining name the occupied solution. -/
theorem tieGap_make : ∀ (y z m : List Nat),
    m.length = y.length → z.length = y.length →
    (∀ i, i < y.length →
      getAt 0 m i + getAt 0 z i = getAt 0 y i) →
    tieGap y z = some m
  | [], [], [], _, _, _ => rfl
  | [], [], _ :: _, hm, _, _ => Nat.noConfusion hm
  | [], _ :: _, _, _, hz, _ => Nat.noConfusion hz
  | _ :: _, _, [], hm, _, _ => Nat.noConfusion hm
  | _ :: _, [], _ :: _, _, hz, _ => Nat.noConfusion hz
  | a :: s, b :: t, c :: m, hm, hz, hent => by
    have h0 : c + b = a := hent 0 (Nat.succ_pos _)
    have hba : b ≤ a := by
      rw [← h0]
      exact Nat.le_add_left b c
    show (if b ≤ a then
        match tieGap s t with
        | some m' => some ((a - b) :: m')
        | none => none
      else none) = some (c :: m)
    rw [if_pos hba,
      tieGap_make s t m (Nat.succ.inj hm) (Nat.succ.inj hz)
        (fun i hi => hent (i + 1) (Nat.succ_lt_succ hi))]
    show some ((a - b) :: m) = some (c :: m)
    rw [show a - b = c from by rw [← h0]; exact addSubSelfR c b]

/-- The family read changed at one key: the entry rewritten at the
stated read, every further coordinate kept; beyond the list's top
the family is unchanged, the write's own default. The letter-pair
moves read it at their stated reads (`con:units`; `thm:weylchar`'s
recursion display), the raise and the lowering its one-box
instances. -/
def editAt (f : Nat → Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | 0, a :: t => f a :: t
  | n + 1, a :: t => a :: editAt f n t

/-- The occupancy raised by one at a key, the entry write beside
`getAt`'s read; beyond the list's top the family is unchanged, the
write's own default. -/
def bumpAt : Nat → List Nat → List Nat := editAt (fun x => x + 1)

/-- The occupancy lowered by one at a key, `bumpAt`'s mirror;
beyond the list's top the family is unchanged, and at an
unoccupied key the entry stays at the floor. -/
def dipAt : Nat → List Nat → List Nat := editAt (fun x => x - 1)

/-- The edit keeps the family's length. -/
theorem length_editAt (f : Nat → Nat) :
    ∀ (i : Nat) (l : List Nat), (editAt f i l).length = l.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | i + 1, _ :: t => congrArg Nat.succ (length_editAt f i t)

/-- The edit's own key reads the entry at the stated read. -/
theorem getAt_editAt_self (f : Nat → Nat) :
    ∀ (k : Nat) (l : List Nat), k < l.length →
      getAt 0 (editAt f k l) k = f (getAt 0 l k)
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, _ :: _, _ => rfl
  | k + 1, _ :: t, h =>
    getAt_editAt_self f k t (Nat.lt_of_succ_lt_succ h)

/-- Off the edited key the entries are the source's. -/
theorem getAt_editAt_ne (f : Nat → Nat) :
    ∀ (k t : Nat) (l : List Nat), ¬ t = k →
      getAt 0 (editAt f k l) t = getAt 0 l t
  | 0, _, [], _ => rfl
  | _ + 1, _, [], _ => rfl
  | 0, 0, _ :: _, h => absurd rfl h
  | 0, _ + 1, _ :: _, _ => rfl
  | _ + 1, 0, _ :: _, _ => rfl
  | k + 1, t + 1, _ :: l, h =>
    getAt_editAt_ne f k t l (fun he => h (congrArg Nat.succ he))

/-- Two edits at distinct keys exchange. -/
theorem editAt_comm (f g : Nat → Nat) :
    ∀ (a b : Nat) (l : List Nat), ¬ a = b →
      editAt f a (editAt g b l) = editAt g b (editAt f a l)
  | 0, 0, [], _ => rfl
  | 0, _ + 1, [], _ => rfl
  | _ + 1, 0, [], _ => rfl
  | _ + 1, _ + 1, [], _ => rfl
  | 0, 0, _ :: _, h => absurd rfl h
  | 0, _ + 1, _ :: _, _ => rfl
  | _ + 1, 0, _ :: _, _ => rfl
  | a + 1, b + 1, x :: l, h => by
    show x :: editAt f a (editAt g b l)
      = x :: editAt g b (editAt f a l)
    rw [editAt_comm f g a b l (fun he => h (congrArg Nat.succ he))]

/-- Two edits at one key fuse to the composed read. -/
theorem editAt_fuse (f g : Nat → Nat) :
    ∀ (k : Nat) (l : List Nat),
      editAt f k (editAt g k l) = editAt (fun x => f (g x)) k l
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | k + 1, x :: l => by
    show x :: editAt f k (editAt g k l)
      = x :: editAt (fun x => f (g x)) k l
    rw [editAt_fuse f g k l]

/-- Two reads at one value at every argument edit alike. -/
theorem editAt_congr (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    ∀ (k : Nat) (l : List Nat), editAt f k l = editAt g k l
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, a :: t => by
    show f a :: t = g a :: t
    rw [h a]
  | k + 1, a :: t => by
    show a :: editAt f k t = a :: editAt g k t
    rw [editAt_congr f g h k t]

/-- Two reads at one value at the key's own entry edit alike: the
further coordinates are kept either way. -/
theorem editAt_congr_entry (f g : Nat → Nat) :
    ∀ (k : Nat) (l : List Nat),
      f (getAt 0 l k) = g (getAt 0 l k) → editAt f k l = editAt g k l
  | 0, [], _ => rfl
  | _ + 1, [], _ => rfl
  | 0, a :: t, h => by
    show f a :: t = g a :: t
    rw [show f a = g a from h]
  | k + 1, a :: t, h => by
    show a :: editAt f k t = a :: editAt g k t
    rw [editAt_congr_entry f g k t h]

/-- The identity read's edit is the family itself. -/
theorem editAt_id : ∀ (k : Nat) (l : List Nat),
    editAt (fun x => x) k l = l
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | k + 1, a :: t => by
    show a :: editAt (fun x => x) k t = a :: t
    rw [editAt_id k t]

/-- A write keeps the family's length. -/
theorem length_set {α : Type} (b : α) :
    ∀ (m : List α) (k : Nat), (m.set k b).length = m.length
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, k + 1 => congrArg Nat.succ (length_set b t k)

/-- A write inside the first list leaves the appended list fixed. -/
theorem set_append_left {α : Type} (x : α) : ∀ (a b : List α) (i : Nat),
    i < a.length → (a ++ b).set i x = a.set i x ++ b
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | y :: a, b, i + 1, h =>
    congrArg (List.cons y) (set_append_left x a b i (Nat.lt_of_succ_lt_succ h))

/-- A write past the first list is the corresponding write in the
appended list, including indices past its end. -/
theorem set_append_right {α : Type} (x : α) : ∀ (a b : List α) (i : Nat),
    (a ++ b).set (a.length + i) x = a ++ b.set i x
  | [], b, i => by
    change b.set (0 + i) x = b.set i x
    rw [Nat.zero_add]
  | y :: a, b, i => by
    rw [show (y :: a).length + i = (a.length + i) + 1 from Nat.succ_add _ _]
    exact congrArg (List.cons y) (set_append_right x a b i)

/-- A fold of steps each keeping the length keeps the length. -/
theorem foldl_length_inv {α β : Type} (st : List α → β → List α)
    (h : ∀ m x, (st m x).length = m.length) :
    ∀ (l : List β) (m : List α), (l.foldl st m).length = m.length
  | [], _ => rfl
  | x :: t, m => by
    show (t.foldl st (st m x)).length = m.length
    rw [foldl_length_inv st h t (st m x), h]

/-- The written key reads the written value. -/
theorem getAt_set_self {α : Type} (d b : α) :
    ∀ (m : List α) (k : Nat), k < m.length →
      getAt d (m.set k b) k = b
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: t, k + 1, h =>
    getAt_set_self d b t k (Nat.lt_of_succ_lt_succ h)

/-- Off the written key the entries are the source's: a write
keeps every further key. -/
theorem getAt_set_ne {α : Type} (d : α) :
    ∀ (m : List α) (k x : Nat) (b : α), x ≠ k →
      getAt d (m.set k b) x = getAt d m x
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, k + 1, x + 1, b, h =>
    getAt_set_ne d t k x b (fun he => h (congrArg Nat.succ he))

/-- A key written at its own read is the family itself. -/
theorem set_self {α : Type} (d : α) :
    ∀ (m : List α) (k : Nat), k < m.length →
      m.set k (getAt d m k) = m
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | a :: t, k + 1, h => by
    show a :: t.set k (getAt d t k) = a :: t
    rw [set_self d t k (Nat.lt_of_succ_lt_succ h)]

/-- Reading a list through a map commutes with replacing one key. -/
theorem map_set {α β : Type} (f : α → β) (a : α) : ∀ (l : List α) (i : Nat),
    (l.set i a).map f = (l.map f).set i (f a)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | b :: l, i + 1 => congrArg (List.cons (f b)) (map_set f a l i)

/-- Two replacements at one list key read the later datum. -/
theorem set_set {α : Type} (a b : α) : ∀ (l : List α) (i : Nat),
    (l.set i a).set i b = l.set i b
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | c :: l, i + 1 => congrArg (List.cons c) (set_set a b l i)

/-- Two writes at distinct positions commute, including
positions beyond the list. -/
theorem set_comm {α : Type} :
    ∀ (l : List α) (p q : Nat) (u v : α), ¬ p = q →
      List.set (List.set l p u) q v = List.set (List.set l q v) p u
  | [], _, _, _, _, _ => rfl
  | _ :: _, 0, 0, _, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _, _ => rfl
  | a :: t, p + 1, q + 1, u, v, h => by
    show a :: List.set (List.set t p u) q v
      = a :: List.set (List.set t q v) p u
    rw [set_comm t p q u v (fun he => h (congrArg Nat.succ he))]

/-- The written key's withdrawal reads the source's own. -/
theorem eraseIdx_set {α : Type} (b : α) :
    ∀ (m : List α) (k : Nat),
      (m.set k b).eraseIdx k = m.eraseIdx k
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: t, k + 1 => by
    show a :: (t.set k b).eraseIdx k = a :: t.eraseIdx k
    rw [eraseIdx_set b t k]

/-- The edit passes across the memberwise sum at its first summand
where the read passes across the key's entry sum. -/
theorem editAt_zipWith_left (f : Nat → Nat) :
    ∀ (j : Nat) (a b : List Nat),
      f (getAt 0 a j) + getAt 0 b j = f (getAt 0 a j + getAt 0 b j) →
      List.zipWith (fun x y => x + y) (editAt f j a) b
        = editAt f j (List.zipWith (fun x y => x + y) a b)
  | 0, [], _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | 0, _ :: _, [], _ => rfl
  | _ + 1, _ :: _, [], _ => rfl
  | 0, x :: t, y :: u, h => by
    show (f x + y) :: List.zipWith (fun x y => x + y) t u
      = f (x + y) :: List.zipWith (fun x y => x + y) t u
    rw [show f x + y = f (x + y) from h]
  | j + 1, x :: t, y :: u, h =>
    congrArg (List.cons (x + y)) (editAt_zipWith_left f j t u h)

/-- The edit passes across the memberwise sum at its second summand
where the read passes across the key's entry sum. -/
theorem editAt_zipWith_right (f : Nat → Nat) :
    ∀ (j : Nat) (a b : List Nat),
      getAt 0 a j + f (getAt 0 b j) = f (getAt 0 a j + getAt 0 b j) →
      List.zipWith (fun x y => x + y) a (editAt f j b)
        = editAt f j (List.zipWith (fun x y => x + y) a b)
  | 0, [], _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | 0, _ :: _, [], _ => rfl
  | _ + 1, _ :: _, [], _ => rfl
  | 0, x :: t, y :: u, h => by
    show (x + f y) :: List.zipWith (fun x y => x + y) t u
      = f (x + y) :: List.zipWith (fun x y => x + y) t u
    rw [show x + f y = f (x + y) from h]
  | j + 1, x :: t, y :: u, h =>
    congrArg (List.cons (x + y)) (editAt_zipWith_right f j t u h)

/-- Beyond the top there is nothing to raise: the empty family is
its own image. -/
theorem bumpAt_nil : ∀ i : Nat, bumpAt i [] = []
  | 0 => rfl
  | _ + 1 => rfl

/-- Beyond the top there is nothing to lower: the empty family is
its own image. -/
theorem dipAt_nil : ∀ j : Nat, dipAt j [] = []
  | 0 => rfl
  | _ + 1 => rfl

/-- The raised key's dip reads the family back, the round trip at
the bumped entry. -/
theorem dipAt_bumpAt_self : ∀ (j : Nat) (mu : List Nat),
    dipAt j (bumpAt j mu) = mu
  := fun j mu =>
    (editAt_fuse (fun x => x - 1) (fun x => x + 1) j mu).trans
      ((editAt_congr (fun x => x + 1 - 1) (fun x => x)
          (fun _ => rfl) j mu).trans
        (editAt_id j mu))

/-- The lowered key's bump reads the family back at an occupied
key, the round trip's other order. -/
theorem bumpAt_dipAt_self : ∀ (i : Nat) (l : List Nat),
    0 < getAt 0 l i → bumpAt i (dipAt i l) = l
  := fun i l h =>
    (editAt_fuse (fun x => x + 1) (fun x => x - 1) i l).trans
      ((editAt_congr_entry (fun x => x - 1 + 1) (fun x => x) i l
          (subAdd h)).trans
        (editAt_id i l))

/-- The predecessor comparison joins the successor's. -/
theorem succ_lt_of_lt_pred {j d : Nat} (h : j < d - 1) :
    j + 1 < d :=
  match d, h with
  | _ + 1, h => Nat.succ_lt_succ h

/-- A vacant key's dip reads the family back, the truncating
subtraction at the unoccupied entry. -/
theorem dipAt_of_zero : ∀ (j : Nat) (l : List Nat),
    getAt 0 l j = 0 → dipAt j l = l
  := fun j l h =>
    (editAt_congr_entry (fun x => x - 1) (fun x => x) j l
        (by rw [h])).trans
      (editAt_id j l)

/-- Two raises commute at every key pair. -/
theorem bumpAt_comm : ∀ (i a : Nat) (l : List Nat),
    bumpAt i (bumpAt a l) = bumpAt a (bumpAt i l)
  := fun i a l => by
    by_cases hia : i = a
    · rw [hia]
    · exact editAt_comm (fun x => x + 1) (fun x => x + 1) i a l hia

/-- A strict order's gap witness at the successor join. -/
theorem gap_of_lt : ∀ (j i : Nat), i < j →
    ∃ g, j = i + (g + 1)
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | j + 1, i, h =>
    match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | .inl he => ⟨0, by rw [← he]⟩
    | .inr hl =>
      match gap_of_lt j i hl with
      | ⟨g, hg⟩ =>
        ⟨g + 1, by rw [hg]; exact Nat.add_assoc i (g + 1) 1⟩

/-- The lowering at an occupied key passes across the memberwise
sum on the left. -/
theorem dipAt_zipWith_left : ∀ (j : Nat) (a b : List Nat),
    0 < ground.getAt 0 a j →
    List.zipWith (fun x y => x + y) (dipAt j a) b
      = dipAt j (List.zipWith (fun x y => x + y) a b)
  := fun j a b h =>
    editAt_zipWith_left (fun x => x - 1) j a b (by
      rw [Nat.add_comm (getAt 0 a j - 1) (getAt 0 b j),
        addSubAssoc h (getAt 0 b j),
        Nat.add_comm (getAt 0 b j) (getAt 0 a j)])

/-- The lowering at an occupied key passes across the memberwise
sum on the right. -/
theorem dipAt_zipWith_right : ∀ (j : Nat) (a b : List Nat),
    0 < ground.getAt 0 b j →
    List.zipWith (fun x y => x + y) a (dipAt j b)
      = dipAt j (List.zipWith (fun x y => x + y) a b) :=
  fun j a b h =>
    editAt_zipWith_right (fun x => x - 1) j a b
      (addSubAssoc h (getAt 0 a j))

/-- Two lowerings commute at every key pair. -/
theorem dipAt_comm : ∀ (j b : Nat) (l : List Nat),
    dipAt j (dipAt b l) = dipAt b (dipAt j l)
  := fun j b l => by
    by_cases hjb : j = b
    · rw [hjb]
    · exact editAt_comm (fun x => x - 1) (fun x => x - 1) j b l hjb

/-- A raise and a lowering at distinct keys commute. -/
theorem bumpAt_dipAt_ne : ∀ (i b : Nat) (l : List Nat),
    ¬ i = b → bumpAt i (dipAt b l) = dipAt b (bumpAt i l) :=
  fun i b l h => editAt_comm (fun x => x + 1) (fun x => x - 1) i b l h

/-- The leading segment's count at a covered key count. -/
theorem length_take {α : Type} : ∀ (k : Nat) (l : List α),
    k <= l.length -> (l.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => absurd h (Nat.not_succ_le_zero _)
  | k + 1, _ :: t, h =>
    congrArg Nat.succ (length_take k t (Nat.le_of_succ_le_succ h))

/-- The leading segment of a mapped family is the mapped leading
segment. -/
theorem take_map {α β : Type} (f : α → β) : ∀ (k : Nat) (l : List α),
    List.take k (l.map f) = (List.take k l).map f
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, a :: t => congrArg (fun r => f a :: r) (take_map f k t)

/-- The trailing segment's count joins the withdrawn count to the
family's own. -/
theorem length_drop {α : Type} : ∀ (k : Nat) (l : List α),
    k ≤ l.length → (l.drop k).length + k = l.length
  | 0, _, _ => rfl
  | _ + 1, [], h => absurd h (Nat.not_succ_le_zero _)
  | k + 1, _ :: t, h => by
    show (t.drop k).length + (k + 1) = t.length + 1
    rw [← Nat.add_assoc, length_drop k t (Nat.le_of_succ_le_succ h)]

/-- The trailing segment's entry at a key: the family's own at the
key past the withdrawn count. -/
theorem getAt_drop {α : Type} (d : α) : ∀ (k : Nat) (l : List α)
    (i : Nat), ground.getAt d (l.drop k) i = ground.getAt d l (k + i)
  | 0, l, i => by
    show getAt d l i = getAt d l (0 + i)
    rw [Nat.zero_add]
  | _ + 1, [], _ => rfl
  | k + 1, a :: t, i => by
    show getAt d (t.drop k) i = getAt d (a :: t) (k + 1 + i)
    rw [Nat.add_right_comm k 1 i]
    show getAt d (t.drop k) i = getAt d t (k + i)
    exact getAt_drop d k t i

/-- The leading segment's entry within its own count is the
family's own at that key. -/
theorem getAt_take {α : Type} (d : α) : ∀ (k : Nat) (l : List α)
    (i : Nat), i < k → ground.getAt d (l.take k) i = ground.getAt d l i
  | 0, _, i, h => absurd h (Nat.not_lt_zero i)
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, _ => rfl
  | k + 1, _ :: t, i + 1, h => getAt_take d k t i (Nat.lt_of_succ_lt_succ h)

/-- The trailing segment at an occupied key is its own entry over
the further tail. -/
theorem drop_getAt_cons {α : Type} (d : α) : ∀ (k : Nat) (l : List α),
    k < l.length → l.drop k = ground.getAt d l k :: l.drop (k + 1)
  | 0, [], h => absurd h (Nat.not_lt_zero _)
  | 0, _ :: _, _ => rfl
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | k + 1, _ :: t, h => drop_getAt_cons d k t (Nat.lt_of_succ_lt_succ h)

/-- An occupied trailing segment reads its withdrawn count inside
the family's own. -/
theorem lt_of_drop_pos {α : Type} : ∀ (k : Nat) (l : List α),
    0 < (l.drop k).length → k < l.length
  | 0, [], h => absurd h (Nat.not_lt_zero _)
  | 0, _ :: _, _ => Nat.succ_pos _
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | k + 1, _ :: t, h => Nat.succ_lt_succ (lt_of_drop_pos k t h)

/-- A key inside the family occupies its trailing segment. -/
theorem drop_pos_of_lt {α : Type} : ∀ (i : Nat) (l : List α),
    i < l.length → 0 < (l.drop i).length
  | 0, [], h => absurd h (Nat.not_lt_zero 0)
  | 0, _ :: _, _ => Nat.succ_pos _
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | i + 1, _ :: t, h => drop_pos_of_lt i t (Nat.lt_of_succ_lt_succ h)

/-- The prefix sum at a key: the leading entries' total, the
dominance order's reasoning read. -/
def prefixAt : Nat → List Nat → Nat
  | 0, [] => 0
  | 0, _ :: _ => 0
  | _ + 1, [] => 0
  | k + 1, a :: t => a + prefixAt k t

/-- The vacant prefix. -/
theorem prefixAt_zero : ∀ mu : List Nat, prefixAt 0 mu = 0
  | [] => rfl
  | _ :: _ => rfl

/-- The vacant list's prefix. -/
theorem prefixAt_nil : ∀ k : Nat, prefixAt k [] = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- The one-key prefix is the head's own entry. -/
theorem prefixAt_one : ∀ l : List Nat, prefixAt 1 l = getAt 0 l 0
  | [] => rfl
  | a :: t => by
    show a + prefixAt 0 t = a
    rw [prefixAt_zero t, Nat.add_zero]

/-- The prefix grows by the key's own entry. -/
theorem prefixAt_succ : ∀ (mu : List Nat) (k : Nat),
    k < mu.length →
    prefixAt (k + 1) mu = prefixAt k mu + ground.getAt 0 mu k
  | [], k, hk => absurd hk (Nat.not_lt_zero k)
  | a :: t, 0, _ => by
    show a + prefixAt 0 t = prefixAt 0 (a :: t) + a
    rw [prefixAt_zero t, prefixAt_zero (a :: t), Nat.zero_add]
    exact rfl
  | a :: t, k + 1, hk => by
    show a + prefixAt (k + 1) t
      = a + prefixAt k t + ground.getAt 0 t k
    rw [prefixAt_succ t k (Nat.lt_of_succ_lt_succ hk), Nat.add_assoc]

/-- A raise beyond the prefix leaves it: the bumped key sits at or
past the read's count. -/
theorem prefixAt_bumpAt : ∀ (j : Nat) (x : List Nat) (k : Nat),
    k ≤ j → prefixAt k (ground.bumpAt j x) = prefixAt k x
  | j, [], _, _ => by rw [ground.bumpAt_nil j]
  | _, _ :: _, 0, _ => by rw [prefixAt_zero, prefixAt_zero]
  | 0, _ :: _, k + 1, hk => absurd hk (Nat.not_succ_le_zero k)
  | j + 1, a :: t, k + 1, hk => by
    show a + prefixAt k (ground.bumpAt j t) = a + prefixAt k t
    rw [prefixAt_bumpAt j t k (Nat.le_of_succ_le_succ hk)]

/-- The lowering at an occupied key drops the prefix through it by
the one box. -/
theorem prefixAt_dipAt : ∀ (i : Nat) (mu : List Nat),
    0 < ground.getAt 0 mu i →
    prefixAt (i + 1) (ground.dipAt i mu) + 1 = prefixAt (i + 1) mu
  | _, [], h => absurd h (Nat.lt_irrefl 0)
  | 0, a :: t, h => by
    show a - 1 + prefixAt 0 t + 1 = a + prefixAt 0 t
    rw [prefixAt_zero t, Nat.add_zero, Nat.add_zero]
    exact ground.subAdd h
  | i + 1, a :: t, h => by
    show a + prefixAt (i + 1) (ground.dipAt i t) + 1
      = a + prefixAt (i + 1) t
    rw [Nat.add_assoc, prefixAt_dipAt i t h]

/-- The memberwise sum's leading segment: at matched counts the
joined family's prefix at a key is the two prefixes' sum. -/
theorem prefixAt_zipAdd : ∀ (x y : List Nat), x.length = y.length →
    ∀ k, prefixAt k (List.zipWith (fun u w => u + w) x y)
      = prefixAt k x + prefixAt k y
  | [], [], _, k => by
    show prefixAt k ([] : List Nat)
      = prefixAt k [] + prefixAt k []
    rw [prefixAt_nil k]
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | _ :: _, _ :: _, _, 0 => rfl
  | a :: s, b :: t, h, k + 1 => by
    show a + b + prefixAt k (List.zipWith (fun u w => u + w) s t)
      = a + prefixAt k s + (b + prefixAt k t)
    rw [prefixAt_zipAdd s t (Nat.succ.inj h) k,
      Nat.add_assoc a b (prefixAt k s + prefixAt k t),
      Nat.add_left_comm b (prefixAt k s) (prefixAt k t),
      ← Nat.add_assoc a (prefixAt k s) (b + prefixAt k t)]

/-- A constant block's leading segment: inside the block the prefix
at a key is the key count against the repeated entry. -/
theorem prefixAt_replicate : ∀ (d m k : Nat), k ≤ d →
    prefixAt k (List.replicate d m) = k * m
  | d, m, 0, _ => by
    rw [prefixAt_zero (List.replicate d m), Nat.zero_mul]
  | 0, _, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | d + 1, m, k + 1, h => by
    show m + prefixAt k (List.replicate d m) = (k + 1) * m
    have hm : (k + 1) * m = k * m + m := Nat.succ_mul k m
    rw [prefixAt_replicate d m k (Nat.le_of_succ_le_succ h), hm,
      Nat.add_comm (k * m) m]

/-- The raise keeps the family's length. -/
theorem length_bumpAt : ∀ (i : Nat) (l : List Nat),
    (bumpAt i l).length = l.length :=
  length_editAt (fun x => x + 1)

/-- The lowering keeps the family's length. -/
theorem length_dipAt : ∀ (j : Nat) (l : List Nat),
    (dipAt j l).length = l.length :=
  length_editAt (fun x => x - 1)

/-- The raise's own key reads one beyond the source's entry. -/
theorem getAt_bumpAt_self : ∀ (i : Nat) (l : List Nat),
    i < l.length →
    getAt 0 (bumpAt i l) i = getAt 0 l i + 1 :=
  getAt_editAt_self (fun x => x + 1)

/-- Off the raised key the entries are the source's. -/
theorem getAt_bumpAt_ne : ∀ (i : Nat) (l : List Nat)
    (x : Nat), ¬ x = i →
    getAt 0 (bumpAt i l) x = getAt 0 l x :=
  fun i l x hx => getAt_editAt_ne (fun v => v + 1) i x l hx

/-- At an occupied key the lowering's entry is one below the
source's, the read stated without subtraction. -/
theorem getAt_dipAt_self : ∀ (j : Nat) (l : List Nat),
    0 < getAt 0 l j →
    getAt 0 (dipAt j l) j + 1 = getAt 0 l j
  := fun j l h => by
    have hlen : j < l.length := by
      match Nat.lt_or_ge j l.length with
      | .inl hl => exact hl
      | .inr hge =>
        rw [getAt_over 0 l j hge] at h
        exact absurd h (Nat.lt_irrefl 0)
    show getAt 0 (editAt (fun x => x - 1) j l) j + 1 = getAt 0 l j
    rw [getAt_editAt_self (fun x => x - 1) j l hlen]
    exact subAdd h

/-- Off the lowered key the entries are the source's. -/
theorem getAt_dipAt_ne : ∀ (j : Nat) (l : List Nat)
    (x : Nat), ¬ x = j →
    getAt 0 (dipAt j l) x = getAt 0 l x :=
  fun j l x hx => getAt_editAt_ne (fun v => v - 1) j x l hx

/-- The lowered key's entry read at the truncating subtraction, the
unoccupied key's floor included. -/
theorem getAt_dipAt : ∀ (j : Nat) (l : List Nat),
    getAt 0 (dipAt j l) j = getAt 0 l j - 1
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | j + 1, _ :: t => getAt_dipAt j t

/-- The family repeated at its own default reads that member at
every key, the keys beyond the count included. -/
theorem getAt_replicate_self {α : Type} (a : α) : ∀ (n p : Nat),
    getAt a (List.replicate n a) p = a
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, p + 1 => getAt_replicate_self a n p

/-- A vanishing natural sum vanishes at both members. -/
theorem addZeroN : ∀ {a b : Nat}, a + b = 0 → a = 0 ∧ b = 0
  | 0, 0, _ => ⟨rfl, rfl⟩
  | _ + 1, 0, h => Nat.noConfusion h
  | _, _ + 1, h => Nat.noConfusion h

/-- The vacant family reads vacant at every key. -/
theorem getAt_replicate_zero (n p : Nat) :
    getAt 0 (List.replicate n 0) p = 0 :=
  getAt_replicate_self 0 n p

/-- The constant family splits at any join of its count. -/
theorem replicate_append {α : Type} (x : α) :
    ∀ (a b : Nat), List.replicate (a + b) x
      = List.replicate a x ++ List.replicate b x
  | 0, b => by rw [Nat.zero_add]; rfl
  | a + 1, b => by
    rw [Nat.succ_add]
    show x :: List.replicate (a + b) x
      = x :: (List.replicate a x ++ List.replicate b x)
    rw [replicate_append x a b]

/-- The repeated family reads its own member at every key below
the count, at any carrier and any default. -/
theorem getAt_replicate {α : Type} (dflt a : α) :
    ∀ (m p : Nat), p < m →
      getAt dflt (List.replicate m a) p = a
  | 0, p, hp => absurd hp (Nat.not_lt_zero p)
  | _ + 1, 0, _ => rfl
  | m + 1, p + 1, hp =>
    getAt_replicate dflt a m p (Nat.lt_of_succ_lt_succ hp)

/-- A member of a repeated family is the repeated datum. -/
theorem mem_replicate_eq {α : Type} (u : α) : ∀ (m : Nat) (l : α),
    l ∈ List.replicate m u → l = u
  | 0, _, h => nomatch h
  | m + 1, l, h => by
    have h' : l ∈ u :: List.replicate m u := h
    cases h' with
    | head => rfl
    | tail _ hm => exact mem_replicate_eq u m l hm

/-- A leading repeated family at the default shifts the key read:
below the count the default, at or beyond it the further list at
the key's gap. -/
theorem getAt_replicate_append {α : Type} (u : α) :
    ∀ (a : Nat) (v : List α) (j : Nat),
      getAt u (List.replicate a u ++ v) j
        = if a ≤ j then getAt u v (j - a) else u
  | 0, v, j => by
    show getAt u v j = if 0 ≤ j then getAt u v (j - 0) else u
    rw [if_pos (Nat.zero_le j), Nat.sub_zero]
  | a + 1, _, 0 => by
    show u = if a + 1 ≤ 0 then _ else u
    rw [if_neg (Nat.not_succ_le_zero a)]
  | a + 1, v, j + 1 => by
    show getAt u (List.replicate a u ++ v) j
      = if a + 1 ≤ j + 1 then getAt u v (j + 1 - (a + 1)) else u
    rw [Nat.succ_sub_succ j a, getAt_replicate_append u a v j]
    by_cases h : a ≤ j
    · rw [if_pos h, if_pos (Nat.succ_le_succ h)]
    · rw [if_neg h, if_neg (fun hc => h (Nat.le_of_succ_le_succ hc))]

/-- A trailing repeated family at the default reads the leading
list back at every key. -/
theorem getAt_append_replicate {α : Type} (u : α) (k : Nat) :
    ∀ (f : List α) (t : Nat),
      getAt u (f ++ List.replicate k u) t = getAt u f t
  | [], t => getAt_replicate_self u k t
  | _ :: _, 0 => rfl
  | _ :: f, t + 1 => getAt_append_replicate u k f t

/-- A bounded count family either reads nought throughout its key
range or names an occupied key inside it. -/
theorem getAt_vac_or_occ (c : List Nat) : ∀ n : Nat,
    (∀ i, i < n → getAt 0 c i = 0)
      ∨ ∃ i, i < n ∧ ¬ getAt 0 c i = 0
  | 0 => Or.inl (fun i hi => absurd hi (Nat.not_lt_zero i))
  | n + 1 => by
    match getAt_vac_or_occ c n with
    | Or.inr ⟨i, hi, h⟩ => exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, h⟩
    | Or.inl hall =>
      by_cases h : getAt 0 c n = 0
      · refine Or.inl (fun i hi => ?_)
        match Nat.lt_or_ge i n with
        | Or.inl hin => exact hall i hin
        | Or.inr hin =>
          rw [Nat.le_antisymm (Nat.le_of_lt_succ hi) hin]
          exact h
      · exact Or.inr ⟨n, Nat.lt_succ_self n, h⟩

/-- The adjacent exchange at a key: the pair of entries at the key
and its successor trade places, the further keys keeping theirs.
Beyond the list's top, and at a list of one member, the family
reads itself. -/
def adjSwap {α : Type} : Nat → List α → List α
  | 0, [] => []
  | _ + 1, [] => []
  | 0, [a] => [a]
  | 0, a :: b :: t => b :: a :: t
  | k + 1, a :: t => a :: adjSwap k t

/-- The exchange keeps the list's count. -/
theorem length_adjSwap {α : Type} : ∀ (k : Nat) (m : List α),
    (adjSwap k m).length = m.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | k + 1, _ :: t => congrArg Nat.succ (length_adjSwap k t)

/-- The entry read at the exchange's first key. -/
theorem getAt_adjSwap_fst {α : Type} (d : α) :
    ∀ (k : Nat) (m : List α), k + 1 < m.length →
      getAt d (adjSwap k m) k = getAt d m (k + 1)
  | 0, [], hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, [], hk => absurd hk (Nat.not_lt_zero _)
  | 0, [_], hk => absurd hk (Nat.lt_irrefl 1)
  | 0, _ :: _ :: _, _ => rfl
  | k + 1, _ :: t, hk =>
    getAt_adjSwap_fst d k t (Nat.lt_of_succ_lt_succ hk)

/-- The entry read at the exchange's second key. -/
theorem getAt_adjSwap_snd {α : Type} (d : α) :
    ∀ (k : Nat) (m : List α), k + 1 < m.length →
      getAt d (adjSwap k m) (k + 1) = getAt d m k
  | 0, [], hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, [], hk => absurd hk (Nat.not_lt_zero _)
  | 0, [_], hk => absurd hk (Nat.lt_irrefl 1)
  | 0, _ :: _ :: _, _ => rfl
  | k + 1, _ :: t, hk =>
    getAt_adjSwap_snd d k t (Nat.lt_of_succ_lt_succ hk)

/-- The entry read off the exchange's two keys. -/
theorem getAt_adjSwap_ne {α : Type} (d : α) :
    ∀ (k : Nat) (m : List α) (i : Nat), i ≠ k → i ≠ k + 1 →
      getAt d (adjSwap k m) i = getAt d m i
  | 0, [], _, _, _ => rfl
  | _ + 1, [], _, _, _ => rfl
  | 0, [_], _, _, _ => rfl
  | 0, _ :: _ :: _, 0, h0, _ => absurd rfl h0
  | 0, _ :: _ :: _, 1, _, h1 => absurd rfl h1
  | 0, _ :: _ :: _, _ + 2, _, _ => rfl
  | _ + 1, _ :: _, 0, _, _ => rfl
  | k + 1, _ :: t, i + 1, h0, h1 =>
    getAt_adjSwap_ne d k t i (fun e => h0 (congrArg Nat.succ e))
      (fun e => h1 (congrArg Nat.succ e))

/-- The adjacent exchange's entry read at the index
transposition, the three key reads joined. -/
theorem getAt_adjSwap {α : Type} (d : α)
    (k : Nat) (m : List α) (h : k + 1 < m.length) (t : Nat) :
    getAt d (adjSwap k m) t = getAt d m (swapIx k (k + 1) t) := by
  by_cases h1 : t = k
  · rw [h1, swapIx_fst k (k + 1)]
    exact getAt_adjSwap_fst d k m h
  · by_cases h2 : t = k + 1
    · rw [h2, swapIx_snd (Nat.succ_ne_self k)]
      exact getAt_adjSwap_snd d k m h
    · rw [swapIx_off h1 h2]
      exact getAt_adjSwap_ne d k m t h1 h2

/-- Exchanging two places at one entry value fixes the list. -/
theorem adjSwap_of_eq {α : Type} (d : α) : ∀ (k : Nat) (l : List α),
    getAt d l k = getAt d l (k + 1) → adjSwap k l = l
  | 0, [], _ => rfl
  | 0, [_], _ => rfl
  | 0, a :: b :: l, h => by
    change a = b at h
    rw [h]
    rfl
  | _ + 1, [], _ => rfl
  | k + 1, a :: l, h => congrArg (List.cons a) (adjSwap_of_eq d k l h)

/-- The exchange is an involution. -/
theorem adjSwap_adjSwap {α : Type} : ∀ (k : Nat) (m : List α),
    adjSwap k (adjSwap k m) = m
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | k + 1, a :: t => by
    show a :: adjSwap k (adjSwap k t) = a :: t
    rw [adjSwap_adjSwap k t]

/-- The strike at the exchange's first key reads the strike at its
second: the traded member is the one the strike keeps. -/
theorem eraseIdx_adjSwap {α : Type} :
    ∀ (k : Nat) (m : List α), k + 1 < m.length →
      (adjSwap k m).eraseIdx k = m.eraseIdx (k + 1)
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, [_], h =>
    absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero 0)
  | 0, _ :: _ :: _, _ => rfl
  | k + 1, a :: t, h => by
    show a :: (adjSwap k t).eraseIdx k = a :: t.eraseIdx (k + 1)
    rw [eraseIdx_adjSwap k t (Nat.lt_of_succ_lt_succ h)]

/-- The exchange composes with an entry map. -/
theorem adjSwap_map {α β : Type} (f : α → β) :
    ∀ (k : Nat) (m : List α),
      adjSwap k (m.map f) = (adjSwap k m).map f
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | k + 1, a :: t => by
    show f a :: adjSwap k (t.map f) = f a :: (adjSwap k t).map f
    rw [adjSwap_map f k t]

/-- The weak-descent guard decides: the successor-guarded bounded
read `∀ p, p + 1 < n → P p` synthesizes through the strict-bound
instance one step down. -/
instance instGround10 (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∀ p, p + 1 < n → P p) :=
  match n with
  | 0 => isTrue (fun p h => absurd h (Nat.not_lt_zero (p + 1)))
  | k + 1 =>
    match Nat.decidableBallLT k (fun p _ => P p) with
    | isTrue h => isTrue (fun p hp => h p (Nat.lt_of_succ_lt_succ hp))
    | isFalse h => isFalse (fun hall =>
        h (fun p hp => hall p (Nat.succ_lt_succ hp)))

/-- The bounded existential search, the guard's dual to the
bounded read: some key below the stated bound at the read, the
walk down the bound with the top key its own test (the core
existential instances take a `propext`-bearing route, so the
search is the tree's own). -/
private def decExLT (P : Nat → Prop) [DecidablePred P] :
    ∀ n, Decidable (∃ p, p < n ∧ P p)
  | 0 =>
    isFalse (fun h =>
      match h with
      | ⟨p, hp, _⟩ => absurd hp (Nat.not_lt_zero p))
  | n + 1 =>
    match decExLT P n with
    | isTrue h =>
      isTrue (match h with
        | ⟨p, hp, hP⟩ => ⟨p, Nat.lt_succ_of_lt hp, hP⟩)
    | isFalse h =>
      match inferInstanceAs (Decidable (P n)) with
      | isTrue hn => isTrue ⟨n, Nat.lt_succ_self n, hn⟩
      | isFalse hn =>
        isFalse (fun hex =>
          match hex with
          | ⟨p, hp, hP⟩ =>
            match Nat.lt_or_ge p n with
            | .inl hlt => h ⟨p, hlt, hP⟩
            | .inr hge =>
              hn (by
                rw [Nat.le_antisymm hge (Nat.le_of_lt_succ hp)]
                exact hP))

/-- The bounded existential reads through the finite key walk. -/
instance instGroundExistsLT (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∃ p, p < n ∧ P p) := decExLT P n

/-- The successor-guarded existential decides: `∃ p, p + 1 < n ∧ P p`
through the bounded search one step down. -/
instance instGround11 (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∃ p, p + 1 < n ∧ P p) :=
  match n with
  | 0 =>
    isFalse (fun h =>
      match h with
      | ⟨p, hp, _⟩ => absurd hp (Nat.not_lt_zero (p + 1)))
  | k + 1 =>
    match decExLT P k with
    | isTrue h =>
      isTrue (match h with
        | ⟨p, hp, hP⟩ => ⟨p, Nat.succ_lt_succ hp, hP⟩)
    | isFalse h =>
      isFalse (fun hex =>
        match hex with
        | ⟨p, hp, hP⟩ => h ⟨p, Nat.lt_of_succ_lt_succ hp, hP⟩)

/-- The weak-bounded existential decides: `∃ p, p ≤ n ∧ P p` through
the bounded search one step up. -/
instance instGround12 (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∃ p, p ≤ n ∧ P p) :=
  match decExLT P (n + 1) with
  | isTrue h =>
    isTrue (match h with
      | ⟨p, hp, hP⟩ => ⟨p, Nat.le_of_lt_succ hp, hP⟩)
  | isFalse h =>
    isFalse (fun hex =>
      match hex with
      | ⟨p, hp, hP⟩ => h ⟨p, Nat.lt_succ_of_le hp, hP⟩)

/-- The head dominates the tail's entries at a weak descent. -/
theorem headDom (x : Nat) (t : List Nat)
    (hdesc : ∀ p, p + 1 < (x :: t).length →
      getAt 0 (x :: t) (p + 1) ≤ getAt 0 (x :: t) p) :
    ∀ q, q < t.length → getAt 0 t q ≤ x
  | 0, h => hdesc 0 (Nat.succ_lt_succ h)
  | q + 1, h =>
    Nat.le_trans (hdesc (q + 1) (Nat.succ_lt_succ h))
      (headDom x t hdesc q (Nat.lt_of_succ_lt h))

/-- Two gaps below a shared top identify their subtrahends. -/
theorem subInj {d a b : Nat} (ha : a ≤ d) (hb : b ≤ d)
    (h : d - a = d - b) : a = b := by
  have h2 : (d - b) + a = d := by
    rw [← h]
    exact subAdd ha
  exact addCancelL (d - b) (h2.trans (subAdd hb).symm)

/-- The descent walks a gap: an entry at a deeper key sits at or
below its shallower fellow. -/
theorem descGap (l : List Nat)
    (hdesc : ∀ a, a + 1 < l.length →
      getAt 0 l (a + 1) ≤ getAt 0 l a) :
    ∀ (g p : Nat), p + g < l.length →
      getAt 0 l (p + g) ≤ getAt 0 l p
  | 0, _, _ => Nat.le_refl _
  | g + 1, p, h =>
    Nat.le_trans (hdesc (p + g) h)
      (descGap l hdesc g p (Nat.lt_of_succ_lt h))

/-- The chained descent: a deeper key reads at or below any
shallower one. -/
theorem descLe (l : List Nat) (p q : Nat)
    (hdesc : ∀ a, a + 1 < l.length →
      getAt 0 l (a + 1) ≤ getAt 0 l a)
    (hpq : p ≤ q) (hq : q < l.length) :
    getAt 0 l q ≤ getAt 0 l p := by
  have hgap : p + (q - p) = q := natAddSubCancel hpq
  rw [← hgap] at hq ⊢
  exact descGap l hdesc (q - p) p hq

/-! The scalar pair `[a : b]`, its reads the pair's whole
interface. -/

set_option genInjectivity false in
/-- The scalar datum `[a : b]`: two positive naturals, the colon a
separator of its data.  The representative fields stay private to
this module; every consumer reads pairs through the displayed
reads. -/
structure Pair where
  num : Pos
  den : Pos

/-- A natural enters as `[a : 1]`. -/
def Pair.ofPos (a : Pos) : Pair := ⟨a, .one⟩

/-- `[a:b] + [c:d] = [ad + cb : bd]`. -/
def Pair.add (x y : Pair) : Pair :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den⟩

instance instGround13 : Add Pair := ⟨Pair.add⟩

/-- `[a:b][c:d] = [ac : bd]`. -/
def Pair.mul (x y : Pair) : Pair := ⟨x.num * y.num, x.den * y.den⟩

instance instGround14 : Mul Pair := ⟨Pair.mul⟩

/-- Two pairs are one value exactly at `ad = cb`, the orientation
read of two rays. -/
def Pair.oneValue (x y : Pair) : Prop := x.num * y.den = y.num * x.den

instance instGround15 (x y : Pair) : Decidable (x.oneValue y) :=
  inferInstanceAs (Decidable (x.num * y.den = y.num * x.den))

/-- The order `[a:b] < [c:d]` is the natural read `ad < cb`. -/
instance instGround16 : LT Pair := ⟨fun x y => x.num * y.den < y.num * x.den⟩

instance instGround17 (x y : Pair) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.num * y.den < y.num * x.den))

/-- At or below over the pairs: the trichotomy's one-value and below
outcomes. -/
instance instGround41 : LE Pair := ⟨fun x y => x.oneValue y ∨ x < y⟩

instance instGround42 (x y : Pair) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The pair's trichotomy is the cross products' own, data. -/
def Pair.trich (x y : Pair) : Trich (x.num * y.den) (y.num * x.den) :=
  ground.trich _ _

/-- On pairs the cofactor is total, the construction at the
components' cross products. -/
def Pair.cofactor (x y : Pair) : Pair := ⟨x.num * y.den, x.den * y.num⟩

/-- Sums read one value at either order, a ground identity of the
fold. -/
theorem Pair.add_comm (x y : Pair) : x + y = y + x := by
  show Pair.mk (x.num * y.den + y.num * x.den) (x.den * y.den)
      = Pair.mk (y.num * x.den + x.num * y.den) (y.den * x.den)
  rw [ground.add_comm (x.num * y.den) (y.num * x.den),
    ground.mul_comm x.den y.den]

/-- Two fold orders are equal by the ground identities. -/
theorem Pair.add_assoc (x y z : Pair) : x + y + z = x + (y + z) := by
  show Pair.mk
      ((x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den))
      (x.den * y.den * z.den)
    = Pair.mk
      (x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den)
      (x.den * (y.den * z.den))
  rw [right_distrib, right_distrib,
    mul_assoc x.num y.den z.den, mul_right_comm y.num x.den z.den,
    show z.num * (x.den * y.den) = z.num * y.den * x.den from by
      rw [mul_assoc, ground.mul_comm y.den x.den],
    ground.add_assoc, mul_assoc x.den y.den z.den]

theorem Pair.oneValue_refl (x : Pair) : x.oneValue x := rfl

theorem Pair.oneValue_symm {x y : Pair} (h : x.oneValue y) :
    y.oneValue x := h.symm

theorem Pair.oneValue_trans {x y z : Pair} (h1 : x.oneValue y)
    (h2 : y.oneValue z) : x.oneValue z := by
  apply mul_right_cancel (c := y.den)
  calc x.num * z.den * y.den
      = x.num * y.den * z.den := by
        rw [mul_assoc, mul_assoc, mul_comm z.den y.den]
    _ = y.num * x.den * z.den := by rw [h1]
    _ = y.num * z.den * x.den := by
        rw [mul_assoc, mul_assoc, mul_comm x.den z.den]
    _ = z.num * y.den * x.den := by rw [h2]
    _ = z.num * x.den * y.den := by
        rw [mul_assoc, mul_assoc, mul_comm y.den x.den]

/-- The homogeneity principle at the sum: the displayed read maps
every representative of its arguments to one value. -/
theorem Pair.add_congr {x x' y y' : Pair} (hx : x.oneValue x')
    (hy : y.oneValue y') : (x + y).oneValue (x' + y') := by
  show (x.num * y.den + y.num * x.den) * (x'.den * y'.den)
      = (x'.num * y'.den + y'.num * x'.den) * (x.den * y.den)
  rw [right_distrib, right_distrib]
  have e1 : x.num * y.den * (x'.den * y'.den)
      = x.num * x'.den * (y.den * y'.den) :=
    mul_mul_mul_comm x.num y.den x'.den y'.den
  have e2 : y.num * x.den * (x'.den * y'.den)
      = y.num * y'.den * (x.den * x'.den) :=
    mul_mul_comm' y.num x.den x'.den y'.den
  have e3 : x'.num * y'.den * (x.den * y.den)
      = x'.num * x.den * (y.den * y'.den) := by
    rw [mul_mul_mul_comm, mul_comm y'.den y.den]
  have e4 : y'.num * x'.den * (x.den * y.den)
      = y'.num * y.den * (x.den * x'.den) := by
    rw [mul_mul_comm', mul_comm x'.den x.den]
  rw [e1, e2, e3, e4, hx, hy]

/-- The homogeneity principle at the product. -/
theorem Pair.mul_congr {x x' y y' : Pair} (hx : x.oneValue x')
    (hy : y.oneValue y') : (x * y).oneValue (x' * y') := by
  show x.num * y.num * (x'.den * y'.den)
      = x'.num * y'.num * (x.den * y.den)
  calc x.num * y.num * (x'.den * y'.den)
      = x.num * x'.den * (y.num * y'.den) := by
        rw [mul_assoc, mul_assoc, mul_left_comm y.num x'.den]
    _ = x'.num * x.den * (y'.num * y.den) := by rw [hx, hy]
    _ = x'.num * y'.num * (x.den * y.den) := by
        rw [mul_assoc, mul_assoc, mul_left_comm x.den y'.num]

/-- The order reflects off a shared positive factor: the trichotomy
against the moved sum. -/
theorem lt_of_mul_lt {a b c : Pos} (h : a * c < b * c) : a < b :=
  match trich a b with
  | .lt g hg => ⟨g, hg⟩
  | .eq e => absurd h (by
      subst e
      exact fun ⟨g, hg⟩ => add_ne_left (a * c) g hg)
  | .gt g hg => absurd h (fun ⟨g', hg'⟩ => by
      have : b * c + (g * c + g') = b * c := by
        rw [← add_assoc, ← right_distrib, hg, hg']
      exact add_ne_left (b * c) (g * c + g') this)

/-- The at-or-below order reflects off a shared positive factor,
`lt_of_mul_lt` joined to the product's injectivity. -/
theorem le_of_mul_le {a b c : Pos} (h : a * c ≤ b * c) : a ≤ b :=
  match h with
  | Or.inl e => Or.inl (mul_right_cancel e)
  | Or.inr l => Or.inr (lt_of_mul_lt l)

/-- The homogeneity principle at the order: a comparison holds
exactly at its rescaling. -/
theorem Pair.lt_congr {x x' y y' : Pair} (hx : x.oneValue x')
    (hy : y.oneValue y') (h : x < y) : x' < y' := by
  obtain ⟨g, hg⟩ := h
  apply lt_of_mul_lt (c := x.den * y.den)
  refine ⟨g * (x'.den * y'.den), ?_⟩
  have e1 : x'.num * y'.den * (x.den * y.den)
      = x.num * y.den * (x'.den * y'.den) := by
    calc x'.num * y'.den * (x.den * y.den)
        = x'.num * x.den * (y.den * y'.den) := by
          rw [mul_mul_mul_comm, mul_comm y'.den y.den]
      _ = x.num * x'.den * (y.den * y'.den) := by rw [hx]
      _ = x.num * y.den * (x'.den * y'.den) :=
          mul_mul_mul_comm x.num x'.den y.den y'.den
  have e2 : y.num * x.den * (x'.den * y'.den)
      = y'.num * x'.den * (x.den * y.den) := by
    calc y.num * x.den * (x'.den * y'.den)
        = y.num * y'.den * (x.den * x'.den) :=
          mul_mul_comm' y.num x.den x'.den y'.den
      _ = y'.num * y.den * (x.den * x'.den) := by rw [hy]
      _ = y'.num * x'.den * (x.den * y.den) := by
          rw [mul_mul_comm', mul_comm y.den x.den]
  rw [e1, ← right_distrib, hg, e2]

/-- The cofactor's naming identity: `y` against the cofactor is one
value with `x`. -/
theorem Pair.cofactor_read (x y : Pair) : (y * x.cofactor y).oneValue x := by
  show y.num * (x.num * y.den) * x.den = x.num * (y.den * (x.den * y.num))
  rw [mul_left_comm y.num x.num y.den,
    mul_assoc x.num (y.num * y.den) x.den,
    mul_assoc y.num y.den x.den, mul_left_comm y.num y.den x.den,
    ground.mul_comm y.num x.den]

/-- The product's congruence reflects: two products against one `y`
at one value read their cofactors at one value. -/
theorem Pair.mul_cancel {y c c' : Pair} (h : (y * c).oneValue (y * c')) :
    c.oneValue c' := by
  have h' : y.num * y.den * (c.num * c'.den)
      = y.num * y.den * (c'.num * c.den) := by
    rw [mul_mul_mul_comm y.num y.den c.num c'.den,
      mul_mul_mul_comm y.num y.den c'.num c.den]
    exact h
  exact mul_left_cancel h'

/-- The cofactor is one value among the pairs solving its naming
identity. -/
theorem Pair.cofactor_unique {y c c' x : Pair}
    (h : (y * c).oneValue x) (h' : (y * c').oneValue x) :
    c.oneValue c' :=
  Pair.mul_cancel (Pair.oneValue_trans h (Pair.oneValue_symm h'))

/-! The scalar pair's arithmetic: the product's identities are the
components' own, the sum's distribution and the doubling read hold
at one value, the shared summand and the square drop off a read,
and the order's gap is itself a pair. -/

/-- The product commutes, the components' own commutation. -/
theorem Pair.mul_comm (x y : Pair) : x * y = y * x := by
  show Pair.mk (x.num * y.num) (x.den * y.den)
      = Pair.mk (y.num * x.num) (y.den * x.den)
  rw [ground.mul_comm x.num y.num, ground.mul_comm x.den y.den]

/-- The product associates, the components' own association. -/
theorem Pair.mul_assoc (x y z : Pair) : x * y * z = x * (y * z) := by
  show Pair.mk (x.num * y.num * z.num) (x.den * y.den * z.den)
      = Pair.mk (x.num * (y.num * z.num)) (x.den * (y.den * z.den))
  rw [ground.mul_assoc x.num y.num z.num, ground.mul_assoc x.den y.den z.den]

/-- A product's outer factors exchange. -/
theorem Pair.mul_right_comm (x y z : Pair) : x * y * z = x * z * y := by
  rw [Pair.mul_assoc, Pair.mul_comm y z, ← Pair.mul_assoc]

/-- A sum's outer summands exchange. -/
theorem Pair.add_right_comm (x y z : Pair) : x + y + z = x + z + y := by
  rw [Pair.add_assoc, Pair.add_comm y z, ← Pair.add_assoc]

/-- A representative rescaled by a positive factor reads one value
with its own pair. -/
private theorem Pair.scale_oneValue (p : Pair) (s : Pos) :
    (Pair.mk (p.num * s) (p.den * s)).oneValue p := by
  show p.num * s * p.den = p.num * (p.den * s)
  rw [ground.mul_assoc, ground.mul_comm s p.den]

/-- The product distributes over the sum from the right: the two
displays read one value, the factor's denominator the rescaling. -/
theorem Pair.right_distrib (x y z : Pair) :
    ((x + y) * z).oneValue (x * z + y * z) := by
  have h : x * z + y * z
      = Pair.mk (((x + y) * z).num * z.den) (((x + y) * z).den * z.den) := by
    show Pair.mk (x.num * z.num * (y.den * z.den)
          + y.num * z.num * (x.den * z.den))
        (x.den * z.den * (y.den * z.den))
      = Pair.mk ((x.num * y.den + y.num * x.den) * z.num * z.den)
        (x.den * y.den * z.den * z.den)
    rw [ground.right_distrib (x.num * y.den) (y.num * x.den) z.num,
      ground.right_distrib (x.num * y.den * z.num) (y.num * x.den * z.num)
        z.den,
      ground.mul_right_comm x.num y.den z.num,
      ground.mul_right_comm y.num x.den z.num,
      ground.mul_assoc (x.num * z.num) y.den z.den,
      ground.mul_assoc (y.num * z.num) x.den z.den,
      ground.mul_assoc (x.den * y.den) z.den z.den,
      ground.mul_mul_mul_comm x.den z.den y.den z.den]
  rw [h]
  exact Pair.oneValue_symm (Pair.scale_oneValue _ _)

/-- The product distributes over the sum from the left, the
commuted read. -/
theorem Pair.left_distrib (x y z : Pair) :
    (x * (y + z)).oneValue (x * y + x * z) := by
  rw [Pair.mul_comm x (y + z), Pair.mul_comm x y, Pair.mul_comm x z]
  exact Pair.right_distrib y z x

/-- A pair at the product's unit reads the partner alone. -/
theorem Pair.one_mul (x : Pair) :
    (Pair.ofPos Pos.one * x).oneValue x := by
  show (Pos.one * x.num) * x.den = x.num * (Pos.one * x.den)
  rw [ground.one_mul x.num, ground.one_mul x.den]

/-- The defect root against its square clearing: `[1:a] · a² = a`. -/
theorem Pair.root_scale (a : Pos) :
    (Pair.mk Pos.one a * Pair.ofPos (a * a)).oneValue
      (Pair.ofPos a) := by
  show (Pos.one * (a * a)) * Pos.one = a * (a * Pos.one)
  rw [ground.one_mul (a * a), ground.mul_one (a * a), ground.mul_one a]

/-- The defect root's square against the clearing: `[1:a]² · a² = 1`. -/
theorem Pair.root_sq_scale (a : Pos) :
    (Pair.mk Pos.one a * Pair.mk Pos.one a * Pair.ofPos (a * a)).oneValue
      (Pair.ofPos Pos.one) := by
  show ((Pos.one * Pos.one) * (a * a)) * Pos.one
    = Pos.one * ((a * a) * Pos.one)
  rw [ground.mul_one ((Pos.one * Pos.one) * (a * a)),
    ground.mul_one (a * a), ground.one_mul Pos.one]

/-- Doubling reads the sum of a pair with itself. -/
theorem Pair.two_mul (x : Pair) :
    (Pair.ofPos 2 * x).oneValue (x + x) := by
  show (2 : Pos) * x.num * (x.den * x.den)
      = (x.num * x.den + x.num * x.den) * (Pos.one * x.den)
  rw [show (2 : Pos) = Pos.one + Pos.one from rfl,
    ground.right_distrib Pos.one Pos.one x.num, ground.one_mul x.num,
    ground.one_mul x.den,
    ground.right_distrib x.num x.num (x.den * x.den),
    ground.right_distrib (x.num * x.den) (x.num * x.den) x.den,
    ground.mul_assoc x.num x.den x.den]

/-- A summand shared by two sums drops off their one-value read. -/
theorem Pair.add_cancel {x y z : Pair} (h : (x + z).oneValue (y + z)) :
    x.oneValue y := by
  have e1 : (x.num * z.den + z.num * x.den) * (y.den * z.den)
      = x.num * y.den * (z.den * z.den) + z.num * x.den * y.den * z.den := by
    rw [ground.right_distrib (x.num * z.den) (z.num * x.den)
        (y.den * z.den),
      ground.mul_mul_mul_comm x.num z.den y.den z.den,
      ← ground.mul_assoc (z.num * x.den) y.den z.den]
  have e2 : (y.num * z.den + z.num * y.den) * (x.den * z.den)
      = y.num * x.den * (z.den * z.den) + z.num * x.den * y.den * z.den := by
    rw [ground.right_distrib (y.num * z.den) (z.num * y.den)
        (x.den * z.den),
      ground.mul_mul_mul_comm y.num z.den x.den z.den,
      ← ground.mul_assoc (z.num * y.den) x.den z.den,
      ground.mul_right_comm z.num y.den x.den]
  have h' : x.num * y.den * (z.den * z.den)
      = y.num * x.den * (z.den * z.den) :=
    ground.add_right_cancel (by rw [← e1, ← e2]; exact h)
  exact mul_right_cancel h'

/-- Two squares at one value have their roots at one value, the
count-level square read at the cross products. -/
theorem Pair.mul_self_cancel {x y : Pair} (h : (x * x).oneValue (y * y)) :
    x.oneValue y := by
  refine ground.mul_self_cancel (a := x.num * y.den) (b := y.num * x.den) ?_
  rw [ground.mul_mul_mul_comm x.num y.den x.num y.den,
    ground.mul_mul_mul_comm y.num x.den y.num x.den]
  exact h

/-- A sum sits strictly above its first summand. -/
theorem Pair.lt_add_right (x g : Pair) : x < x + g := by
  refine ⟨g.num * x.den * x.den, ?_⟩
  show x.num * (x.den * g.den) + g.num * x.den * x.den
      = (x.num * g.den + g.num * x.den) * x.den
  rw [ground.right_distrib (x.num * g.den) (g.num * x.den) x.den,
    ← ground.mul_assoc x.num x.den g.den,
    ground.mul_right_comm x.num x.den g.den]

/-- A join at a stated gap sits inside the gap's band: the joined
side refuses the gap's excess on either flank. -/
theorem Pair.band_of_join {x y g : Pair} (h : (x + g).oneValue y) :
    ¬ (x + g < y) ∧ ¬ (y + g < x) := by
  refine ⟨fun hlt => ?_, fun hlt => ?_⟩
  · exact ground.lt_ne
      (Pair.lt_congr h (Pair.oneValue_refl y) hlt) rfl
  · have e : (y + g).oneValue (x + g + g) :=
      Pair.add_congr (Pair.oneValue_symm h) (Pair.oneValue_refl g)
    have hx : x + g + g < x :=
      Pair.lt_congr e (Pair.oneValue_refl x) hlt
    rw [Pair.add_assoc x g g] at hx
    exact ground.lt_asymm (Pair.lt_add_right x (g + g)) hx

/-- The pair's trichotomy at pair gaps: two pairs read one value,
or one of them joins a pair gap to read the other, the gap built at
the cross products' own gap over the joined denominators. -/
theorem Pair.gap_trich (x y : Pair) :
    x.oneValue y ∨ (∃ g : Pair, (x + g).oneValue y)
      ∨ (∃ g : Pair, (y + g).oneValue x) :=
  match Pair.trich x y with
  | .eq h => Or.inl h
  | .lt g h => Or.inr (Or.inl ⟨Pair.mk g (x.den * y.den), by
      show (x.num * (x.den * y.den) + g * x.den) * y.den
          = y.num * (x.den * (x.den * y.den))
      rw [ground.right_distrib (x.num * (x.den * y.den)) (g * x.den) y.den,
        ground.mul_assoc g x.den y.den,
        show x.num * (x.den * y.den) * y.den
            = x.num * y.den * (x.den * y.den) from by
          rw [← ground.mul_assoc x.num x.den y.den,
            ground.mul_right_comm x.num x.den y.den,
            ground.mul_assoc (x.num * y.den) x.den y.den],
        ← ground.right_distrib (x.num * y.den) g (x.den * y.den), h,
        ← ground.mul_assoc y.num x.den (x.den * y.den)]⟩)
  | .gt g h => Or.inr (Or.inr ⟨Pair.mk g (y.den * x.den), by
      show (y.num * (y.den * x.den) + g * y.den) * x.den
          = x.num * (y.den * (y.den * x.den))
      rw [ground.right_distrib (y.num * (y.den * x.den)) (g * y.den) x.den,
        ground.mul_assoc g y.den x.den,
        show y.num * (y.den * x.den) * x.den
            = y.num * x.den * (y.den * x.den) from by
          rw [← ground.mul_assoc y.num y.den x.den,
            ground.mul_right_comm y.num y.den x.den,
            ground.mul_assoc (y.num * x.den) y.den x.den],
        ← ground.right_distrib (y.num * x.den) g (y.den * x.den), h,
        ← ground.mul_assoc x.num y.den (y.den * x.den)]⟩)

/-- The gap's square read, the binomial at the pair:
`(x + g)² + x² = 2 x (x + g) + g²`. -/
theorem Pair.sq_gap (x g : Pair) :
    ((x + g) * (x + g) + x * x).oneValue
      (Pair.ofPos 2 * x * (x + g) + g * g) := by
  have e1 : ((x + g) * (x + g)).oneValue
      ((x * x + x * g) + (x * g + g * g)) := by
    refine Pair.oneValue_trans (Pair.right_distrib x g (x + g)) ?_
    refine Pair.add_congr ?_ ?_
    · rw [Pair.mul_comm x (x + g), Pair.mul_comm x g]
      exact Pair.right_distrib x g x
    · rw [Pair.mul_comm g (x + g)]
      exact Pair.right_distrib x g g
  have e2 : (Pair.ofPos 2 * x * (x + g)).oneValue
      ((x * x + x * x) + (x * g + x * g)) := by
    rw [Pair.mul_comm (Pair.ofPos 2 * x) (x + g)]
    refine Pair.oneValue_trans (Pair.right_distrib x g (Pair.ofPos 2 * x)) ?_
    refine Pair.add_congr ?_ ?_
    · rw [show x * (Pair.ofPos 2 * x) = Pair.ofPos 2 * (x * x) from by
        rw [← Pair.mul_assoc, Pair.mul_comm x (Pair.ofPos 2), Pair.mul_assoc]]
      exact Pair.two_mul (x * x)
    · rw [show g * (Pair.ofPos 2 * x) = Pair.ofPos 2 * (x * g) from by
        rw [← Pair.mul_assoc, Pair.mul_comm g (Pair.ofPos 2), Pair.mul_assoc,
          Pair.mul_comm g x]]
      exact Pair.two_mul (x * g)
  have hac : ((x * x + x * g) + (x * g + g * g)) + x * x
      = ((x * x + x * x) + (x * g + x * g)) + g * g := by
    rw [← Pair.add_assoc (x * x + x * g) (x * g) (g * g),
      Pair.add_right_comm ((x * x + x * g) + x * g) (g * g) (x * x),
      Pair.add_right_comm (x * x + x * g) (x * g) (x * x),
      Pair.add_right_comm (x * x) (x * g) (x * x),
      Pair.add_assoc (x * x + x * x) (x * g) (x * g)]
  refine Pair.oneValue_trans (Pair.add_congr e1 (Pair.oneValue_refl (x * x))) ?_
  rw [hac]
  exact Pair.oneValue_symm (Pair.add_congr e2 (Pair.oneValue_refl (g * g)))

/-- The harmonic numbers `H_k = Σ_{j ≤ k} [1 : j]`, the fold over
the index order by the derived recursion. -/
def harmonic (k : Pos) : Pair :=
  peanoRec (motive := fun _ => Pair)
    (Pair.ofPos .one) (fun j h => h + ⟨.one, succ j⟩) k

/-- The fold's defining step, the derived recursion's own read
(`peanoRec_succ`), definitional on this carrier. -/
theorem harmonic_succ (k : Pos) :
    harmonic (succ k) = harmonic k + ⟨.one, succ k⟩ := rfl

/-! The balance pair `⟨u : v⟩`: two ground data read jointly. -/

set_option genInjectivity false in
/-- The balance pair `⟨u : v⟩`, the colon a separator of its data. -/
structure BPair where
  fst : Pos
  snd : Pos

/-- Sums add componentwise. -/
def BPair.add (x y : BPair) : BPair := ⟨x.fst + y.fst, x.snd + y.snd⟩

instance instGround18 : Add BPair := ⟨BPair.add⟩

/-- The product reads cross-added:
`⟨u:v⟩⟨u':v'⟩ = ⟨uu' + vv' : uv' + vu'⟩`. -/
def BPair.mul (x y : BPair) : BPair :=
  ⟨x.fst * y.fst + x.snd * y.snd, x.fst * y.snd + x.snd * y.fst⟩

instance instGround19 : Mul BPair := ⟨BPair.mul⟩

/-- Decidable equality on the balance pairs, the components'
own. -/
def BPair.decEq : (x y : BPair) → Decidable (x = y)
  | ⟨a, b⟩, ⟨c, d⟩ =>
    if h1 : a = c then
      if h2 : b = d then
        isTrue (by rw [h1, h2])
      else isFalse (fun hh => h2 (congrArg BPair.snd hh))
    else isFalse (fun hh => h1 (congrArg BPair.fst hh))

instance instGround20 : DecidableEq BPair := BPair.decEq

/-- Two balance pairs are one value exactly at `u + v' = u' + v`, a
summand on both members fixing the value. -/
def BPair.oneValue (x y : BPair) : Prop := x.fst + y.snd = y.fst + x.snd

instance instGround21 (x y : BPair) : Decidable (x.oneValue y) :=
  inferInstanceAs (Decidable (x.fst + y.snd = y.fst + x.snd))

/-- The order is the cross-added read `u + v' < u' + v`. -/
instance instGround22 : LT BPair := ⟨fun x y => x.fst + y.snd < y.fst + x.snd⟩

instance instGround23 (x y : BPair) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.fst + y.snd < y.fst + x.snd))

/-- The equal-membered class is the sum's unit; a fold over a finite
family seeds at it. -/
def BPair.unit : BPair := ⟨.one, .one⟩

/-- The occupied read: a pair off the sum's unit. -/
def BPair.offUnit (x : BPair) : Prop := ¬ x.oneValue BPair.unit

instance instGround24 (x : BPair) : Decidable (x.offUnit) :=
  inferInstanceAs (Decidable (¬ _))

/-- The memberwise swap. -/
def BPair.swap (x : BPair) : BPair := ⟨x.snd, x.fst⟩

/-- A ground datum enters at a one-member site:
`⟨u:v⟩ + w = ⟨u+w : v⟩`. -/
def BPair.addPos (x : BPair) (w : Pos) : BPair := ⟨x.fst + w, x.snd⟩

/-- The pair's side is its two members' own trichotomy read; the
exceeding member's gap is its margin. -/
def BPair.side (x : BPair) : Trich x.fst x.snd := trich x.fst x.snd

/-- The gap of an ordered pair of balance pairs is the cross-added
data's own, `w` at `(u + v') + w = u' + v`. -/
def BPair.gap (x y : BPair) : Trich (x.fst + y.snd) (y.fst + x.snd) :=
  trich _ _

/-- The canonical representative: the side's one-member display,
one value with the datum (`norm_oneValue`), the representative the
homogeneity principle's gauge motion. -/
def BPair.norm (x : BPair) : BPair :=
  match x.side with
  | .lt g _ => ⟨.one, succ g⟩
  | .eq _ => BPair.unit
  | .gt g _ => ⟨succ g, .one⟩

/-- The canonical representative is one value with the datum. -/
theorem BPair.norm_oneValue (x : BPair) : (x.norm).oneValue x := by
  unfold BPair.norm
  cases x.side with
  | lt g hg =>
    show Pos.one + x.snd = x.fst + succ g
    rw [← hg, ground.add_left_comm Pos.one x.fst g, one_add]
  | eq he =>
    show Pos.one + x.snd = x.fst + Pos.one
    rw [he, ground.add_comm]
  | gt g hg =>
    show succ g + x.snd = x.fst + Pos.one
    rw [← hg, succ_add, add_one, ground.add_comm g x.snd]

/-- The canonical unit's test, two constructor reads. -/
def BPair.isUnitRep (x : BPair) : Bool := x.fst.isOne && x.snd.isOne

/-- A summand on both members fixes the value, the unit's law. -/
theorem BPair.addBoth_oneValue (x : BPair) (w : Pos) :
    BPair.oneValue ⟨x.fst + w, x.snd + w⟩ x := by
  show x.fst + w + x.snd = x.fst + (x.snd + w)
  rw [add_assoc, add_comm w x.snd]

theorem BPair.oneValue_refl (x : BPair) : x.oneValue x := rfl

theorem BPair.oneValue_symm {x y : BPair} (h : x.oneValue y) :
    y.oneValue x := h.symm

/-- Equal pairs are one value, the read at an equation. -/
theorem BPair.oneValue_of_eq : ∀ {x y : BPair}, x = y →
    x.oneValue y
  | _, _, rfl => BPair.oneValue_refl _

theorem BPair.oneValue_trans {x y z : BPair} (h1 : x.oneValue y)
    (h2 : y.oneValue z) : x.oneValue z := by
  apply add_right_cancel (c := y.snd)
  calc x.fst + z.snd + y.snd
      = x.fst + y.snd + z.snd := by
        rw [add_assoc, add_assoc, add_comm z.snd y.snd]
    _ = y.fst + x.snd + z.snd := by rw [h1]
    _ = y.fst + z.snd + x.snd := by
        rw [add_assoc, add_assoc, add_comm x.snd z.snd]
    _ = z.fst + y.snd + x.snd := by rw [h2]
    _ = z.fst + x.snd + y.snd := by
        rw [add_assoc, add_assoc, add_comm y.snd x.snd]

/-- A gap one way against an equality: the two sides' data cannot
both hold, the gap moving a member off itself. -/
private theorem BPair.clash_lt_eq {x y : BPair} (h : x.oneValue y) {g : Pos}
    (hg : x.fst + g = x.snd) (he : y.fst = y.snd) : False := by
  have h' : x.fst + y.snd = y.fst + x.snd := h
  rw [← he, ← hg, ← ground.add_assoc, ground.add_comm y.fst x.fst] at h'
  exact ground.add_ne_left _ _ h'.symm

/-- Gaps the two ways against each other: the crossed sum carries
both gaps over itself. -/
private theorem BPair.clash_lt_gt {x y : BPair} (h : x.oneValue y) {g g' : Pos}
    (hg : x.fst + g = x.snd) (hg' : y.snd + g' = y.fst) : False := by
  have h' : x.fst + y.snd = y.fst + x.snd := h
  rw [← hg, ← hg', ground.add_add_comm, ground.add_comm y.snd x.fst] at h'
  exact ground.add_ne_left _ _ h'.symm

/-- An equality against a gap the other way, the mirror clash. -/
private theorem BPair.clash_eq_gt {x y : BPair} (h : x.oneValue y)
    (he : x.fst = x.snd) {g' : Pos} (hg' : y.snd + g' = y.fst) : False := by
  have h' : x.fst + y.snd = y.fst + x.snd := h
  rw [← hg', ← he, ground.add_assoc, ground.add_comm g' x.fst,
    ← ground.add_assoc, ground.add_comm y.snd x.fst] at h'
  exact ground.add_ne_left _ _ h'.symm

/-- The canonical representative is the value's own: one value in,
one representative out — the sides agree at the crossed sum and the
gaps are the same gap, so the representative is a function of the
value alone (`norm_oneValue`'s converse read). -/
theorem BPair.norm_congr {x y : BPair} (h : x.oneValue y) :
    x.norm = y.norm := by
  have h' : x.fst + y.snd = y.fst + x.snd := h
  unfold BPair.norm
  cases hx : x.side with
  | lt g1 hg1 =>
    cases hy : y.side with
    | lt g2 hg2 =>
      rw [← hg1, ← hg2, ← ground.add_assoc, ← ground.add_assoc,
        ground.add_comm y.fst x.fst] at h'
      show (⟨Pos.one, succ g1⟩ : BPair) = ⟨Pos.one, succ g2⟩
      rw [ground.add_left_cancel h']
    | eq he => exact absurd he (fun he => BPair.clash_lt_eq h hg1 he)
    | gt g2 hg2 => exact absurd hg2 (fun hg2 => BPair.clash_lt_gt h hg1 hg2)
  | eq he1 =>
    cases hy : y.side with
    | lt g2 hg2 =>
      exact absurd he1 (fun he1 =>
        BPair.clash_lt_eq (BPair.oneValue_symm h) hg2 he1)
    | eq _ => rfl
    | gt g2 hg2 => exact absurd hg2 (fun hg2 => BPair.clash_eq_gt h he1 hg2)
  | gt g1 hg1 =>
    cases hy : y.side with
    | lt g2 hg2 =>
      exact absurd hg1 (fun hg1 =>
        BPair.clash_lt_gt (BPair.oneValue_symm h) hg2 hg1)
    | eq he2 =>
      exact absurd he2 (fun he2 =>
        BPair.clash_eq_gt (BPair.oneValue_symm h) he2 hg1)
    | gt g2 hg2 =>
      have e1 : x.snd + g1 + y.snd = x.snd + y.snd + g1 := by
        rw [ground.add_assoc, ground.add_comm g1 y.snd, ← ground.add_assoc]
      have e2 : y.snd + g2 + x.snd = x.snd + y.snd + g2 := by
        rw [ground.add_assoc, ground.add_comm g2 x.snd, ← ground.add_assoc,
          ground.add_comm y.snd x.snd]
      rw [← hg1, ← hg2, e1, e2] at h'
      show (⟨succ g1, Pos.one⟩ : BPair) = ⟨succ g2, Pos.one⟩
      rw [ground.add_left_cancel h']

/-- The representative at a witnessed gap the low way: the side's
one-member display reads the gap's successor at the second member. -/
theorem BPair.norm_of_gapLt {x : BPair} {g : Pos}
    (h : x.fst + g = x.snd) : x.norm = ⟨Pos.one, succ g⟩ := by
  unfold BPair.norm
  cases hx : x.side with
  | lt g1 hg1 =>
    show (⟨Pos.one, succ g1⟩ : BPair) = ⟨Pos.one, succ g⟩
    rw [ground.add_left_cancel (hg1.trans h.symm)]
  | eq he =>
    exact absurd he (fun he =>
      BPair.clash_lt_eq (BPair.oneValue_refl x) h he)
  | gt g2 hg2 =>
    exact absurd hg2 (fun hg2 =>
      BPair.clash_lt_gt (BPair.oneValue_refl x) h hg2)

/-- The representative at a witnessed gap the high way: the side's
one-member display reads the gap's successor at the first member. -/
theorem BPair.norm_of_gapGt {x : BPair} {g : Pos}
    (h : x.snd + g = x.fst) : x.norm = ⟨succ g, Pos.one⟩ := by
  unfold BPair.norm
  cases hx : x.side with
  | lt g1 hg1 =>
    exact absurd hg1 (fun hg1 =>
      BPair.clash_lt_gt (BPair.oneValue_refl x) hg1 h)
  | eq he =>
    exact absurd he (fun he =>
      BPair.clash_eq_gt (BPair.oneValue_refl x) he h)
  | gt g2 hg2 =>
    show (⟨succ g2, Pos.one⟩ : BPair) = ⟨succ g, Pos.one⟩
    rw [ground.add_left_cancel (hg2.trans h.symm)]

/-- The homogeneity principle at the balance sum. -/
theorem BPair.add_congr {x x' y y' : BPair} (hx : x.oneValue x')
    (hy : y.oneValue y') : (x + y).oneValue (x' + y') := by
  show x.fst + y.fst + (x'.snd + y'.snd)
      = x'.fst + y'.fst + (x.snd + y.snd)
  calc x.fst + y.fst + (x'.snd + y'.snd)
      = x.fst + x'.snd + (y.fst + y'.snd) := by
        rw [add_assoc, add_assoc, add_left_comm y.fst x'.snd]
    _ = x'.fst + x.snd + (y'.fst + y.snd) := by rw [hx, hy]
    _ = x'.fst + y'.fst + (x.snd + y.snd) := by
        rw [add_assoc, add_assoc, add_left_comm x.snd y'.fst]

/-- Sums read one value at either order, a ground identity of the
fold. -/
theorem BPair.add_comm (x y : BPair) : x + y = y + x := by
  show BPair.mk (x.fst + y.fst) (x.snd + y.snd)
      = BPair.mk (y.fst + x.fst) (y.snd + x.snd)
  rw [ground.add_comm x.fst y.fst, ground.add_comm x.snd y.snd]

/-- Two fold orders are equal by the ground identities. -/
theorem BPair.add_assoc (x y z : BPair) : x + y + z = x + (y + z) := by
  show BPair.mk (x.fst + y.fst + z.fst) (x.snd + y.snd + z.snd)
      = BPair.mk (x.fst + (y.fst + z.fst)) (x.snd + (y.snd + z.snd))
  rw [ground.add_assoc x.fst y.fst z.fst,
    ground.add_assoc x.snd y.snd z.snd]

/-- The cross-added product reads one value at either order. -/
theorem BPair.mul_comm (x y : BPair) : x * y = y * x := by
  show BPair.mk (x.fst * y.fst + x.snd * y.snd)
      (x.fst * y.snd + x.snd * y.fst)
    = BPair.mk (y.fst * x.fst + y.snd * x.snd)
      (y.fst * x.snd + y.snd * x.fst)
  rw [ground.mul_comm x.fst y.fst, ground.mul_comm x.snd y.snd,
    ground.mul_comm x.fst y.snd, ground.mul_comm x.snd y.fst,
    ground.add_comm (y.snd * x.fst) (y.fst * x.snd)]

/-- A ground datum enters the balance carrier at the one-member
site over the unit: `a` reads as `⟨a + 1 : 1⟩`. -/
def BPair.ofPos (a : Pos) : BPair := ⟨a + .one, .one⟩
/-- A count enters the balance carrier as an occupancy read: the
absent count at the sum's unit, an occupied one at its one-member
site. -/
def BPair.ofNat : Nat → BPair
  | 0 => BPair.unit
  | n + 1 => BPair.ofPos (posOfSucc n)

/-- A positive datum's entry is its value read's own. -/
theorem BPair.ofPos_val (p : Pos) : BPair.ofPos p = BPair.ofNat (posVal p) := rfl

/-- A natural's one-member entry is already its canonical
representative. -/
theorem BPair.norm_ofNat : ∀ n : Nat, (BPair.ofNat n).norm = BPair.ofNat n
  | 0 => rfl
  | n + 1 => by
    have h : (BPair.ofNat (n + 1)).snd + posOfSucc n = (BPair.ofNat (n + 1)).fst :=
      ground.add_comm Pos.one (posOfSucc n)
    rw [BPair.norm_of_gapGt h]
    rfl

theorem BPair.add_left_comm (a b c : BPair) :
    a + (b + c) = b + (a + c) := by
  rw [← BPair.add_assoc, BPair.add_comm a b, BPair.add_assoc]

theorem BPair.add_add_comm (a b c d : BPair) :
    a + b + (c + d) = a + c + (b + d) := by
  rw [BPair.add_assoc, BPair.add_assoc, BPair.add_left_comm b c d]

/-- The seeded sum exchanges its two trailing summands, the
right-hand mirror of `BPair.add_left_comm`. -/
theorem BPair.add_right_comm (x y z : BPair) : x + y + z = x + z + y := by
  rw [BPair.add_assoc, BPair.add_comm y z, ← BPair.add_assoc]

/-- The natural one sits off the sum's unit, the seed read's own
side. -/
theorem BPair.ofNat_one_off :
    ¬ (BPair.ofNat 1).oneValue BPair.unit := by decide +kernel

/-- Every occupied count sits off the sum's unit, the seed read at
the general occupancy. -/
theorem BPair.ofNat_off_unit : ∀ n : Nat, 0 < n →
    ¬ (BPair.ofNat n).oneValue BPair.unit
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | n + 1, _, hone =>
    ground.add_ne_left Pos.one (posOfSucc n)
      (by
        rw [ground.add_comm Pos.one (posOfSucc n)]
        exact ground.add_right_cancel
          (show (posOfSucc n + Pos.one) + Pos.one
            = Pos.one + Pos.one from hone))

/-- An occupied count's memberwise swap sits off the sum's unit,
the general occupancy read at the balance partner. -/
theorem BPair.ofNat_swap_off (N : Nat) (h : 0 < N) :
    ¬ ((BPair.ofNat N).swap).oneValue BPair.unit := fun hh => by
  refine BPair.ofNat_off_unit N h ?_
  show (BPair.ofNat N).fst + Pos.one = Pos.one + (BPair.ofNat N).snd
  have h' : (BPair.ofNat N).snd + Pos.one
      = Pos.one + (BPair.ofNat N).fst := hh
  rw [ground.add_comm (BPair.ofNat N).fst Pos.one,
    ground.add_comm Pos.one (BPair.ofNat N).snd]
  exact h'.symm

/-- The natural one's memberwise swap, the general read at its own
first occupancy. -/
theorem BPair.ofNat_one_swap_off :
    ¬ ((BPair.ofNat 1).swap).oneValue BPair.unit :=
  BPair.ofNat_swap_off 1 (by decide +kernel)

/-- A shared summand cancels from a one-value read. -/
theorem BPair.add_cancel {a b c : BPair}
    (h : (a + c).oneValue (b + c)) : a.oneValue b := by
  show a.fst + b.snd = b.fst + a.snd
  refine ground.add_right_cancel (c := c.fst + c.snd) ?_
  have h' : a.fst + c.fst + (b.snd + c.snd)
      = b.fst + c.fst + (a.snd + c.snd) := h
  rw [ground.add_add_comm a.fst c.fst b.snd c.snd,
    ground.add_add_comm b.fst c.fst a.snd c.snd] at h'
  exact h'

/-- The sum's unit drops on its left, the equal-membered class's
law. -/
theorem BPair.unit_add (x : BPair) : (BPair.unit + x).oneValue x := by
  show Pos.one + x.fst + x.snd = x.fst + (Pos.one + x.snd)
  rw [ground.add_comm Pos.one x.fst, ground.add_assoc]

/-- The sum's unit drops on its right. -/
theorem BPair.add_unit (x : BPair) : (x + BPair.unit).oneValue x := by
  show x.fst + Pos.one + x.snd = x.fst + (x.snd + Pos.one)
  rw [ground.add_assoc, ground.add_comm Pos.one x.snd]

/-- Two summands at the sum's unit read the sum there. -/
theorem BPair.add_units {x y : BPair} (hx : x.oneValue BPair.unit)
    (hy : y.oneValue BPair.unit) : (x + y).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.add_congr hx hy)
    (BPair.unit_add BPair.unit)

/-- The sum's unit swallows the product on its left. -/
theorem BPair.unit_mul (x : BPair) :
    (BPair.unit * x).oneValue BPair.unit := by
  show Pos.one * x.fst + Pos.one * x.snd + Pos.one
      = Pos.one + (Pos.one * x.snd + Pos.one * x.fst)
  rw [one_mul, one_mul, ground.add_comm x.fst x.snd, ground.add_comm]

/-- The sum's unit swallows the product on its right. -/
theorem BPair.mul_unit (x : BPair) :
    (x * BPair.unit).oneValue BPair.unit := by
  show x.fst * Pos.one + x.snd * Pos.one + Pos.one
      = Pos.one + (x.fst * Pos.one + x.snd * Pos.one)
  rw [ground.add_comm]

/-- The vacant count's pair is the sum's unit. -/
theorem BPair.ofNat_zero : (BPair.ofNat 0).oneValue BPair.unit := rfl

/-- The cross-added product distributes over the componentwise
sum. -/
theorem BPair.left_distrib (x y z : BPair) :
    x * (y + z) = x * y + x * z := by
  show BPair.mk (x.fst * (y.fst + z.fst) + x.snd * (y.snd + z.snd))
      (x.fst * (y.snd + z.snd) + x.snd * (y.fst + z.fst))
    = BPair.mk
      (x.fst * y.fst + x.snd * y.snd + (x.fst * z.fst + x.snd * z.snd))
      (x.fst * y.snd + x.snd * y.fst + (x.fst * z.snd + x.snd * z.fst))
  rw [ground.left_distrib, ground.left_distrib, ground.left_distrib,
    ground.left_distrib,
    ground.add_add_comm (x.fst * y.fst) (x.fst * z.fst)
      (x.snd * y.snd) (x.snd * z.snd),
    ground.add_add_comm (x.fst * y.snd) (x.fst * z.snd)
      (x.snd * y.fst) (x.snd * z.fst)]

theorem BPair.right_distrib (x y z : BPair) :
    (x + y) * z = x * z + y * z := by
  rw [BPair.mul_comm, BPair.left_distrib, BPair.mul_comm z x,
    BPair.mul_comm z y]

/-- The cross-added product associates. -/
theorem BPair.mul_assoc (x y z : BPair) : x * y * z = x * (y * z) := by
  show BPair.mk
      ((x.fst * y.fst + x.snd * y.snd) * z.fst
        + (x.fst * y.snd + x.snd * y.fst) * z.snd)
      ((x.fst * y.fst + x.snd * y.snd) * z.snd
        + (x.fst * y.snd + x.snd * y.fst) * z.fst)
    = BPair.mk
      (x.fst * (y.fst * z.fst + y.snd * z.snd)
        + x.snd * (y.fst * z.snd + y.snd * z.fst))
      (x.fst * (y.fst * z.snd + y.snd * z.fst)
        + x.snd * (y.fst * z.fst + y.snd * z.snd))
  rw [ground.right_distrib, ground.right_distrib, ground.right_distrib,
    ground.right_distrib, ground.left_distrib, ground.left_distrib,
    ground.left_distrib, ground.left_distrib,
    ← ground.mul_assoc x.fst y.fst z.fst,
    ← ground.mul_assoc x.fst y.snd z.snd,
    ← ground.mul_assoc x.snd y.fst z.snd,
    ← ground.mul_assoc x.snd y.snd z.fst,
    ← ground.mul_assoc x.fst y.fst z.snd,
    ← ground.mul_assoc x.fst y.snd z.fst,
    ← ground.mul_assoc x.snd y.fst z.fst,
    ← ground.mul_assoc x.snd y.snd z.snd,
    ground.add_add_comm (x.fst * y.fst * z.fst) (x.snd * y.snd * z.fst)
      (x.fst * y.snd * z.snd) (x.snd * y.fst * z.snd),
    ground.add_comm (x.snd * y.snd * z.fst) (x.snd * y.fst * z.snd),
    ground.add_add_comm (x.fst * y.fst * z.snd) (x.snd * y.snd * z.snd)
      (x.fst * y.snd * z.fst) (x.snd * y.fst * z.fst),
    ground.add_comm (x.snd * y.snd * z.snd) (x.snd * y.fst * z.fst)]

theorem BPair.mul_left_comm (x y z : BPair) :
    x * (y * z) = y * (x * z) := by
  rw [← BPair.mul_assoc, BPair.mul_comm x y, BPair.mul_assoc]

/-- The seeded product exchanges its two trailing factors, the
right-hand mirror of `BPair.mul_left_comm`. -/
theorem BPair.mul_right_comm (x y z : BPair) : x * y * z = x * z * y := by
  rw [BPair.mul_assoc, BPair.mul_comm y z, ← BPair.mul_assoc]

/-- Three factors read at their reversal, the ends exchanged with
the middle standing, stated at the joined product's own
bracketing. -/
theorem BPair.mul_rot3r (x y z : BPair) : x * (y * z) = z * (y * x) := by
  rw [← BPair.mul_assoc, BPair.mul_comm (x * y) z, BPair.mul_comm x y]

/-- The head passes inside the trailing product, the tightened
association's read of `BPair.mul_left_comm`. -/
theorem BPair.mul_left_comm' (x y z : BPair) : x * (y * z) = y * x * z := by
  rw [BPair.mul_left_comm x y z, ← BPair.mul_assoc y x z]

/-- The trailing factors exchange across the head, the loosened
association's read of `BPair.mul_right_comm`. -/
theorem BPair.mul_right_comm' (x y z : BPair) : x * (y * z) = x * z * y := by
  rw [← BPair.mul_assoc x y z, BPair.mul_right_comm x y z]

/-- Three factors rotate leftward, the mirror of
`BPair.mul_rot3r`. -/
theorem BPair.mul_rot3l (x y z : BPair) : x * (y * z) = y * (z * x) := by
  rw [BPair.mul_left_comm x y z, BPair.mul_comm x z]

/-- The fold over a finite family of balance pairs seeds at the
sum's unit and adds the members, total at every family. -/
def BPair.sum (l : List BPair) : BPair := l.foldl BPair.add BPair.unit

/-- The displayed operation's reordering laws at a carrier read
through the carrier's own one-value relation: the relation's three
reads, the operation's congruence across it, and its commutation
and reassociation — the exchanging-and-regrouping fragment of
`def:ground`'s fold clauses, with no unit read among the fields, so
a literal equality with the two reordering identities instantiates
it at a bare operation. -/
structure CommLaws (γ : Type) (op : γ → γ → γ)
    (ov : γ → γ → Prop) : Prop where
  ovRefl : ∀ x, ov x x
  ovSymm : ∀ {x y}, ov x y → ov y x
  ovTrans : ∀ {x y z}, ov x y → ov y z → ov x z
  opCongr : ∀ {x x' y y'}, ov x x' → ov y y' →
    ov (op x y) (op x' y')
  opComm : ∀ x y, ov (op x y) (op y x)
  opAssoc : ∀ x y z,
    ov (op (op x y) z) (op x (op y z))

/-- The displayed operation's laws at a carrier read through the
carrier's own one-value relation: the reordering fragment with the
unit dropping on either side.  The fold clause of `def:ground`
reads at every carrier with this bundle. -/
structure FoldLaws (γ : Type) (op : γ → γ → γ) (unit : γ)
    (ov : γ → γ → Prop) : Prop extends CommLaws γ op ov where
  unitOp : ∀ x, ov (op unit x) x
  opUnit : ∀ x, ov (op x unit) x

/-- The operation's left exchange, `x + (y + z)` against
`y + (x + z)`, the reordering bundle's own consequence. -/
theorem opLeftCommO {γ : Type} {op : γ → γ → γ}
    {ov : γ → γ → Prop} (C : CommLaws γ op ov)
    (x y z : γ) :
    ov (op x (op y z)) (op y (op x z)) :=
  C.ovTrans (C.ovSymm (C.opAssoc x y z))
    (C.ovTrans (C.opCongr (C.opComm x y) (C.ovRefl z))
      (C.opAssoc y x z))

/-- The four members exchange across the joined reads,
`(a + b) + (c + d)` against `(a + c) + (b + d)`, the reordering
bundle's own consequence. -/
theorem opExchO {γ : Type} {op : γ → γ → γ}
    {ov : γ → γ → Prop} (C : CommLaws γ op ov) (a b c d : γ) :
    ov (op (op a b) (op c d)) (op (op a c) (op b d)) :=
  C.ovTrans (C.opAssoc a b (op c d))
    (C.ovTrans (C.opCongr (C.ovRefl a) (opLeftCommO C b c d))
      (C.ovSymm (C.opAssoc a c (op b d))))

/-- The accumulating fold reads its seed against the family's own
fold, at every carrier with the displayed sum's laws. -/
theorem foldlAddO {γ : Type} {add : γ → γ → γ} {unit : γ}
    {ov : γ → γ → Prop} (L : FoldLaws γ add unit ov) :
    ∀ (m : List γ) (acc : γ),
      ov (m.foldl add acc) (add acc (m.foldl add unit))
  | [], acc => L.ovSymm (L.opUnit acc)
  | b :: t, acc => by
    show ov (t.foldl add (add acc b))
      (add acc (t.foldl add (add unit b)))
    refine L.ovTrans (foldlAddO L t (add acc b)) ?_
    refine L.ovSymm ?_
    refine L.ovTrans
      (L.opCongr (L.ovRefl acc) (foldlAddO L t (add unit b))) ?_
    exact L.ovTrans
      (L.ovSymm (L.opAssoc acc (add unit b) (t.foldl add unit)))
      (L.opCongr (L.opCongr (L.ovRefl acc) (L.unitOp b))
        (L.ovRefl _))

/-- The head splits off the family's fold, at every carrier with
the displayed sum's laws. -/
theorem sumConsO {γ : Type} {add : γ → γ → γ} {unit : γ}
    {ov : γ → γ → Prop} (L : FoldLaws γ add unit ov)
    (b : γ) (m : List γ) :
    ov ((b :: m).foldl add unit) (add b (m.foldl add unit)) := by
  show ov (m.foldl add (add unit b)) (add b (m.foldl add unit))
  refine L.ovTrans (foldlAddO L m (add unit b)) ?_
  exact L.opCongr (L.unitOp b) (L.ovRefl _)

/-- The joined family's fold splits, at every carrier with the
displayed sum's laws. -/
theorem sumAppendO {γ : Type} {add : γ → γ → γ} {unit : γ}
    {ov : γ → γ → Prop} (L : FoldLaws γ add unit ov) :
    ∀ u w : List γ,
      ov ((u ++ w).foldl add unit)
        (add (u.foldl add unit) (w.foldl add unit))
  | [], w => L.ovSymm (L.unitOp (w.foldl add unit))
  | b :: u, w => by
    show ov ((b :: (u ++ w)).foldl add unit)
      (add ((b :: u).foldl add unit) (w.foldl add unit))
    refine L.ovTrans (sumConsO L b (u ++ w)) ?_
    refine L.ovTrans
      (L.opCongr (L.ovRefl b) (sumAppendO L u w)) ?_
    exact L.ovTrans
      (L.ovSymm (L.opAssoc b (u.foldl add unit)
        (w.foldl add unit)))
      (L.opCongr (L.ovSymm (sumConsO L b u)) (L.ovRefl _))

/-- The balance pair's displayed sum at its one-value relation. -/
theorem bpairFoldLaws :
    FoldLaws BPair BPair.add BPair.unit BPair.oneValue where
  ovRefl := BPair.oneValue_refl
  ovSymm := BPair.oneValue_symm
  ovTrans := BPair.oneValue_trans
  opCongr := BPair.add_congr
  opComm := fun x y => BPair.oneValue_of_eq (BPair.add_comm x y)
  opAssoc := fun x y z =>
    BPair.oneValue_of_eq (BPair.add_assoc x y z)
  unitOp := BPair.unit_add
  opUnit := BPair.add_unit

/-- The natural sum at the literal equality. -/
theorem natFoldLaws : FoldLaws Nat Nat.add 0 Eq where
  ovRefl := fun _ => rfl
  ovSymm := fun h => h.symm
  ovTrans := fun h1 h2 => h1.trans h2
  opCongr := fun h1 h2 => by rw [h1, h2]
  opComm := Nat.add_comm
  opAssoc := Nat.add_assoc
  unitOp := Nat.zero_add
  opUnit := Nat.add_zero

/-- The accumulating sum fold reads its seed against the list's own
fold. -/
theorem BPair.foldlAdd : ∀ (m : List BPair) (acc : BPair),
    (m.foldl BPair.add acc).oneValue (acc + BPair.sum m) :=
  foldlAddO bpairFoldLaws

/-- The head splits off the family's fold. -/
theorem BPair.sum_cons (b : BPair) (m : List BPair) :
    (BPair.sum (b :: m)).oneValue (b + BPair.sum m) :=
  sumConsO bpairFoldLaws b m

/-- The joined family's fold splits. -/
theorem BPair.sum_append : ∀ u w : List BPair,
    (BPair.sum (u ++ w)).oneValue (BPair.sum u + BPair.sum w) :=
  sumAppendO bpairFoldLaws

/-- The rescaling of both members by a ground datum, the composite
displays' access. -/
def BPair.scale (x : BPair) (w : Pos) : BPair := ⟨x.fst * w, x.snd * w⟩

/-- A balance read carried over a clearing denominator joins
another at the cross-multiplied numerators, the clearings' product
the joined clearing. -/
def BPair.addQ (p q : BPair × Pos) : BPair × Pos :=
  (p.1.scale q.2 + q.1.scale p.2, p.2 * q.2)

theorem BPair.scale_add (x y : BPair) (w : Pos) :
    (x + y).scale w = x.scale w + y.scale w := by
  show BPair.mk ((x.fst + y.fst) * w) ((x.snd + y.snd) * w)
      = BPair.mk (x.fst * w + y.fst * w) (x.snd * w + y.snd * w)
  rw [ground.right_distrib, ground.right_distrib]

theorem BPair.scale_addW (x : BPair) (a b : Pos) :
    x.scale (a + b) = x.scale a + x.scale b := by
  show BPair.mk (x.fst * (a + b)) (x.snd * (a + b))
    = BPair.mk (x.fst * a + x.fst * b) (x.snd * a + x.snd * b)
  rw [ground.left_distrib, ground.left_distrib]

theorem BPair.scale_scale (x : BPair) (a b : Pos) :
    (x.scale a).scale b = x.scale (a * b) := by
  show BPair.mk (x.fst * a * b) (x.snd * a * b)
      = BPair.mk (x.fst * (a * b)) (x.snd * (a * b))
  rw [ground.mul_assoc, ground.mul_assoc]

/-- Two clearings commute past a rescaling, the clearings' product
exchanged. -/
theorem BPair.scale_comm (x : BPair) (a b : Pos) :
    (x.scale a).scale b = (x.scale b).scale a := by
  rw [BPair.scale_scale, BPair.scale_scale, ground.mul_comm a b]

theorem BPair.scale_mul (x y : BPair) (a b : Pos) :
    (x * y).scale (a * b) = x.scale a * y.scale b := by
  show BPair.mk ((x.fst * y.fst + x.snd * y.snd) * (a * b))
      ((x.fst * y.snd + x.snd * y.fst) * (a * b))
    = BPair.mk (x.fst * a * (y.fst * b) + x.snd * a * (y.snd * b))
      (x.fst * a * (y.snd * b) + x.snd * a * (y.fst * b))
  rw [ground.right_distrib, ground.right_distrib,
    mul_mul_mul_comm x.fst y.fst a b, mul_mul_mul_comm x.snd y.snd a b,
    mul_mul_mul_comm x.fst y.snd a b, mul_mul_mul_comm x.snd y.fst a b]

/-- A rescaled factor's product is the product rescaled, the
one-sided read of `BPair.scale_mul`. -/
theorem BPair.mul_scale (x y : BPair) (c : Pos) :
    x * y.scale c = (x * y).scale c := by
  show BPair.mk (x.fst * (y.fst * c) + x.snd * (y.snd * c))
      (x.fst * (y.snd * c) + x.snd * (y.fst * c))
    = BPair.mk ((x.fst * y.fst + x.snd * y.snd) * c)
      ((x.fst * y.snd + x.snd * y.fst) * c)
  rw [ground.right_distrib, ground.right_distrib,
    ground.mul_assoc x.fst y.fst c, ground.mul_assoc x.snd y.snd c,
    ground.mul_assoc x.fst y.snd c, ground.mul_assoc x.snd y.fst c]

/-- The one-sided read at the leading factor, `BPair.mul_scale`'s
exchange. -/
theorem BPair.scale_mul_left (x y : BPair) (c : Pos) :
    (x * y).scale c = x.scale c * y := by
  rw [BPair.mul_comm x y, ← BPair.mul_scale y x c,
    BPair.mul_comm y (x.scale c)]

/-- The rescaling keeps the one-value read. -/
theorem BPair.scale_congr {x y : BPair} (w : Pos) (h : x.oneValue y) :
    (x.scale w).oneValue (y.scale w) := by
  show x.fst * w + y.snd * w = y.fst * w + x.snd * w
  rw [← ground.right_distrib, ← ground.right_distrib, h]

/-- The rescaling reflects the one-value read, the product's
injectivity. -/
theorem BPair.scale_cancel {x y : BPair} {w : Pos}
    (h : (x.scale w).oneValue (y.scale w)) : x.oneValue y := by
  have h' : (x.fst + y.snd) * w = (y.fst + x.snd) * w := by
    rw [ground.right_distrib, ground.right_distrib]; exact h
  exact mul_right_cancel h'

/-- The rescaling keeps the order, the gap's witness composed by
formula. -/
theorem BPair.scale_lt {x y : BPair} (w : Pos) (h : x < y) :
    x.scale w < y.scale w := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g * w, ?_⟩
  show x.fst * w + y.snd * w + g * w = y.fst * w + x.snd * w
  rw [← ground.right_distrib, ← ground.right_distrib,
    ← ground.right_distrib, hg]

/-- The rescaling reflects the order, the trichotomy against the
moved sum. -/
theorem BPair.lt_of_scale_lt {x y : BPair} {w : Pos}
    (h : x.scale w < y.scale w) : x < y := by
  obtain ⟨g, hg⟩ := h
  have hg' : (x.fst + y.snd) * w + g = (y.fst + x.snd) * w := by
    rw [ground.right_distrib, ground.right_distrib]; exact hg
  cases trich (x.fst + y.snd) (y.fst + x.snd) with
  | lt g' h' => exact ⟨g', h'⟩
  | eq e =>
    exfalso
    rw [e] at hg'
    exact add_ne_left _ g hg'
  | gt g' h' =>
    exfalso
    rw [← h', ground.right_distrib, ground.add_assoc] at hg'
    exact add_ne_left _ _ hg'

/-- The homogeneity principle at the balance order. -/
theorem BPair.lt_congr {x x' y y' : BPair} (hx : x.oneValue x')
    (hy : y.oneValue y') (h : x < y) : x' < y' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  apply add_right_cancel (c := x.snd + y.snd)
  calc x'.fst + y'.snd + g + (x.snd + y.snd)
      = x'.fst + x.snd + (y'.snd + y.snd) + g := by
        rw [ground.add_right_comm (x'.fst + y'.snd) g (x.snd + y.snd),
          ground.add_add_comm x'.fst y'.snd x.snd y.snd]
    _ = x.fst + x'.snd + (y'.snd + y.snd) + g := by rw [← hx]
    _ = x.fst + y.snd + g + (x'.snd + y'.snd) := by
        rw [add_add_comm' x.fst x'.snd y'.snd y.snd,
          ground.add_right_comm (x.fst + y.snd) (x'.snd + y'.snd) g]
    _ = y.fst + x.snd + (x'.snd + y'.snd) := by rw [hg]
    _ = y.fst + y'.snd + (x.snd + x'.snd) := by
        rw [add_add_comm' y.fst x.snd x'.snd y'.snd]
    _ = y'.fst + y.snd + (x.snd + x'.snd) := by rw [hy]
    _ = y'.fst + x'.snd + (x.snd + y.snd) := by
        rw [add_add_comm' y'.fst y.snd x.snd x'.snd,
          ground.add_comm y.snd x.snd]

/-- The homogeneity principle at the balance product, one factor. -/
theorem BPair.mul_congr_left {x x' y : BPair} (hx : x.oneValue x') :
    (x * y).oneValue (x' * y) := by
  show x.fst * y.fst + x.snd * y.snd + (x'.fst * y.snd + x'.snd * y.fst)
      = x'.fst * y.fst + x'.snd * y.snd + (x.fst * y.snd + x.snd * y.fst)
  have collect : ∀ a b : BPair,
      a.fst * y.fst + a.snd * y.snd + (b.fst * y.snd + b.snd * y.fst)
        = y.fst * (a.fst + b.snd) + y.snd * (a.snd + b.fst) := by
    intro a b
    rw [ground.left_distrib, ground.left_distrib,
      ground.mul_comm a.fst y.fst,
      ground.mul_comm b.snd y.fst, ground.mul_comm a.snd y.snd,
      ground.mul_comm b.fst y.snd, ground.add_assoc, ground.add_assoc,
      ground.add_comm (y.snd * b.fst) (y.fst * b.snd),
      ground.add_left_comm (y.snd * a.snd) (y.fst * b.snd)
        (y.snd * b.fst)]
  rw [collect x x', collect x' x, ground.add_comm x.snd x'.fst,
    ground.add_comm x'.snd x.fst, hx]

/-- The homogeneity principle at the balance product: a rescaling of
any datum maps every representative to one value. -/
theorem BPair.mul_congr {x x' y y' : BPair} (hx : x.oneValue x')
    (hy : y.oneValue y') : (x * y).oneValue (x' * y') :=
  BPair.oneValue_trans (BPair.mul_congr_left hx) (by
    rw [BPair.mul_comm x' y, BPair.mul_comm x' y']
    exact BPair.mul_congr_left hy)

/-! The memberwise swap's reads: the swap commutes with the sum and
the product outright, exchanges the canonical representative's
members, keeps the canonical unit's test, and a swapped datum joins
its one-value partner to the sum's unit. -/

/-- The natural entries' sum reads componentwise, one value at the
cross-added identity. -/
theorem BPair.ofNat_succ (n : Nat) :
    (BPair.ofNat (n + 1)).oneValue (BPair.ofNat n + BPair.ofNat 1) := by
  match n with
  | 0 => rfl
  | m + 1 => rfl

theorem BPair.ofNat_add (a : Nat) :
    ∀ b : Nat, (BPair.ofNat (a + b)).oneValue
      (BPair.ofNat a + BPair.ofNat b)
  | 0 => BPair.oneValue_symm (BPair.add_unit (BPair.ofNat a))
  | b + 1 => by
    refine BPair.oneValue_trans (BPair.ofNat_succ (a + b))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.ofNat_add a b)
          (BPair.oneValue_refl (BPair.ofNat 1))) ?_)
    rw [BPair.add_assoc]
    exact BPair.add_congr (BPair.oneValue_refl (BPair.ofNat a))
      (BPair.oneValue_symm (BPair.ofNat_succ b))

/-- The natural one is the product's unit at the one-value read. -/
theorem BPair.mul_ofNat_one (x : BPair) :
    (x * BPair.ofNat 1).oneValue x := by
  show x.fst * (Pos.one + Pos.one) + x.snd * Pos.one + x.snd
      = x.fst + (x.fst * Pos.one + x.snd * (Pos.one + Pos.one))
  rw [ground.left_distrib, ground.left_distrib, ground.mul_one,
    ground.mul_one, ground.add_assoc, ground.add_assoc]

/-- The unit count's scale reads its datum, the product's other
order. -/
theorem BPair.ofNat_one_mul (x : BPair) :
    (BPair.ofNat 1 * x).oneValue x :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ x))
    (BPair.mul_ofNat_one x)

/-- The balance pairs' displayed product at its one-value relation,
the exchange and the regrouping with the unit `1` dropping on either
side. -/
theorem bpairMulLaws :
    FoldLaws BPair (fun a b : BPair => a * b) (BPair.ofNat 1) BPair.oneValue where
  ovRefl := BPair.oneValue_refl
  ovSymm := BPair.oneValue_symm
  ovTrans := BPair.oneValue_trans
  opCongr := BPair.mul_congr
  opComm := fun x y => BPair.oneValue_of_eq (BPair.mul_comm x y)
  opAssoc := fun x y z =>
    BPair.oneValue_of_eq (BPair.mul_assoc x y z)
  unitOp := BPair.ofNat_one_mul
  opUnit := BPair.mul_ofNat_one

/-- A zip fold whose every term reads the unit sums to the unit: a
coefficient list against a row family at one key, each term's read
the unit. -/
theorem zipTermUnit (j : Nat) : ∀ (f : List Nat)
    (M : List (List BPair)),
    (∀ k, k < f.length →
      (BPair.ofNat (getAt 0 f k)
        * getAt BPair.unit (getAt [] M k) j).oneValue BPair.unit) →
    (BPair.sum (List.zipWith
      (fun c row => BPair.ofNat c * getAt BPair.unit row j)
      f M)).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | c :: f, row :: M, h => by
    show (BPair.sum ((BPair.ofNat c * getAt BPair.unit row j)
      :: List.zipWith
        (fun c row => BPair.ofNat c * getAt BPair.unit row j)
        f M)).oneValue BPair.unit
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (h 0 (Nat.succ_pos _))
      (zipTermUnit j f M (fun k hk => h (k + 1)
        (Nat.succ_lt_succ hk)))) ?_
    exact BPair.unit_add _

/-- The natural entries' product reads cross-added, one value at
the identity. -/
theorem BPair.ofNat_mul (a : Nat) :
    ∀ b : Nat, (BPair.ofNat (a * b)).oneValue
      (BPair.ofNat a * BPair.ofNat b)
  | 0 => BPair.oneValue_symm (BPair.mul_unit (BPair.ofNat a))
  | b + 1 => by
    refine BPair.oneValue_trans (BPair.ofNat_add (a * b) a)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.ofNat_mul a b)
          (BPair.oneValue_symm (BPair.mul_ofNat_one (BPair.ofNat a))))
        ?_)
    rw [← BPair.left_distrib]
    exact BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat a))
      (BPair.oneValue_symm (BPair.ofNat_succ b))

/-- A count product against a further factor regroups, the count
entering factor by factor. -/
theorem BPair.ofNat_mul_mul (a b : Nat) (z : BPair) :
    (BPair.ofNat (a * b) * z).oneValue
      (BPair.ofNat a * (BPair.ofNat b * z)) := by
  refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_mul a b)) ?_
  exact BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)


/-- The memberwise swap is an involution. -/
theorem BPair.swap_swap (x : BPair) : x.swap.swap = x := rfl

theorem BPair.swap_add (x y : BPair) :
    x.swap + y.swap = (x + y).swap := rfl

theorem BPair.mul_swap (x y : BPair) : x * y.swap = (x * y).swap := rfl

/-- The memberwise swap commutes with a rescaling. -/
theorem BPair.scale_swap (x : BPair) (w : Pos) :
    x.swap.scale w = (x.scale w).swap := rfl

/-- A balance pair is its first member's site joined to its second
member's site swapped. -/
theorem BPair.mk_read (a b : Pos) :
    (⟨a, b⟩ : BPair).oneValue (BPair.ofPos a + (BPair.ofPos b).swap) := by
  show a + (Pos.one + (b + Pos.one)) = a + Pos.one + Pos.one + b
  rw [ground.add_assoc a Pos.one Pos.one,
    ground.add_assoc a (Pos.one + Pos.one) b,
    ground.add_assoc Pos.one Pos.one b,
    ground.add_comm b Pos.one]

/-- The memberwise swap on the left factor, the product's own
exchange read once. -/
theorem BPair.swap_mul (x y : BPair) : x.swap * y = (x * y).swap := by
  rw [BPair.mul_comm x.swap y, BPair.mul_swap y x, BPair.mul_comm y x]

/-- The four-factor exchange at the middle pair, the product's
commutativity read once inside the join. -/
theorem BPair.mul_mul_mul_comm (x y z w : BPair) :
    x * y * (z * w) = x * z * (y * w) := by
  rw [BPair.mul_assoc, BPair.mul_left_comm y z w, ← BPair.mul_assoc]

/-- The square's expansion at a sum. -/
theorem BPair.sq_expand (p q : BPair) :
    (p + q) * (p + q) = p * p + q * q + (p * q + p * q) := by
  rw [BPair.right_distrib, BPair.left_distrib, BPair.left_distrib,
    BPair.mul_comm q p, BPair.add_comm (p * q) (q * q),
    BPair.add_add_comm (p * p) (p * q) (q * q) (p * q)]

/-- Two swapped factors' product is the data's own. -/
theorem BPair.swap_mul_swap (x y : BPair) :
    x.swap * y.swap = x * y := by
  show BPair.mk (x.snd * y.snd + x.fst * y.fst)
      (x.snd * y.fst + x.fst * y.snd)
    = BPair.mk (x.fst * y.fst + x.snd * y.snd)
      (x.fst * y.snd + x.snd * y.fst)
  rw [ground.add_comm (x.snd * y.snd) (x.fst * y.fst),
    ground.add_comm (x.snd * y.fst) (x.fst * y.snd)]

/-- The swapped datum's square is the datum's own. -/
theorem BPair.swap_sq (q : BPair) : q.swap * q.swap = q * q :=
  BPair.swap_mul_swap q q

/-- The composite pair's sum at a balance-pair first datum,
`def:ground`'s display: the first members cross-added against the
second members' product, normalized. -/
def cpAdd (x y : BPair × BPair) : BPair × BPair :=
  ((x.1 * y.2 + y.1 * x.2).norm, (x.2 * y.2).norm)

/-- The square's expansion at a gap. -/
theorem BPair.sq_expand_swap (p q : BPair) :
    (p + q.swap) * (p + q.swap)
      = p * p + q * q + ((p * q).swap + (p * q).swap) := by
  rw [BPair.sq_expand p q.swap, BPair.swap_sq q, BPair.mul_swap]

/-- A unit representative is the unit outright, the stored counts'
read. -/
theorem BPair.unit_of_isUnitRep : ∀ {x : BPair},
    x.isUnitRep = true → x = BPair.unit
  | ⟨⟨0⟩, ⟨0⟩⟩, _ => rfl
  | ⟨⟨_ + 1⟩, _⟩, h => nomatch h
  | ⟨⟨0⟩, ⟨_ + 1⟩⟩, h => nomatch h

/-- A datum at the sum's unit has the unit representative: the
representative is a function of the value alone, so the unit's own
representative is read back. -/
theorem BPair.isUnitRep_norm_of_unit {x : BPair}
    (h : x.oneValue BPair.unit) : x.norm.isUnitRep = true := by
  rw [BPair.norm_congr h]
  rfl

theorem BPair.isUnitRep_swap (x : BPair) :
    x.swap.isUnitRep = x.isUnitRep := by
  show (x.snd.isOne && x.fst.isOne) = (x.fst.isOne && x.snd.isOne)
  cases x.fst.isOne <;> cases x.snd.isOne <;> rfl

/-- The canonical representative's memberwise swap, the side's case
read: the swap's representative is the representative's swap. -/
theorem BPair.norm_swap (x : BPair) : x.swap.norm = x.norm.swap := by
  unfold BPair.norm
  cases x.swap.side with
  | lt g1 h1 =>
    have hg1 : x.snd + g1 = x.fst := h1
    cases x.side with
    | lt g2 hg2 =>
      exact absurd (by rw [← ground.add_assoc, hg1, hg2] :
        x.snd + (g1 + g2) = x.snd) (add_ne_left _ _)
    | eq h2 =>
      rw [h2] at hg1
      exact absurd hg1 (add_ne_left _ _)
    | gt g2 hg2 =>
      have e := gap_unique hg1 hg2
      subst e
      rfl
  | eq h1 =>
    have he1 : x.snd = x.fst := h1
    cases x.side with
    | lt g2 hg2 =>
      rw [he1] at hg2
      exact absurd hg2 (add_ne_left _ _)
    | eq h2 => rfl
    | gt g2 hg2 =>
      rw [← he1] at hg2
      exact absurd hg2 (add_ne_left _ _)
  | gt g1 h1 =>
    have hg1 : x.fst + g1 = x.snd := h1
    cases x.side with
    | lt g2 hg2 =>
      have e := gap_unique hg1 hg2
      subst e
      rfl
    | eq h2 =>
      rw [← h2] at hg1
      exact absurd hg1 (add_ne_left _ _)
    | gt g2 hg2 =>
      exact absurd (by rw [← ground.add_assoc, hg1, hg2] :
        x.fst + (g1 + g2) = x.fst) (add_ne_left _ _)

/-- A swapped datum against its one-value partner reads the sum's
unit, the site identity's own read. -/
theorem BPair.swap_add_null {x y : BPair} (h : x.oneValue y) :
    (x.swap + y).oneValue BPair.unit := by
  show x.snd + y.fst + Pos.one = Pos.one + (x.fst + y.snd)
  rw [h, ground.add_comm x.snd y.fst,
    ground.add_comm (y.fst + x.snd) Pos.one]

/-- A datum whose sum with a second reads the sum's unit is the
second's balance partner. -/
theorem BPair.swap_of_add_unit {u v : BPair}
    (h : (u + v).oneValue BPair.unit) : u.oneValue v.swap := by
  have h' : u.fst + v.fst + Pos.one = Pos.one + (u.snd + v.snd) := h
  show u.fst + v.fst = v.snd + u.snd
  rw [ground.add_comm v.snd u.snd]
  refine ground.add_right_cancel (c := Pos.one) ?_
  rw [h', ground.add_comm Pos.one (u.snd + v.snd)]

/-- A member joined to its own swap reads the balance null. -/
theorem BPair.add_swap_null (x : BPair) : (x + x.swap).oneValue BPair.unit :=
  BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm x x.swap))
    (BPair.swap_add_null (BPair.oneValue_refl x))

/-- A member's join with its own swap withdraws from a sum, the
joined read at the balance null. -/
theorem BPair.add_swap_cancel (u v : BPair) :
    (u + (v + u.swap)).oneValue v := by
  rw [BPair.add_comm v u.swap, ← BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_swap_null u) (BPair.oneValue_refl v))
    (BPair.unit_add v)

/-- A member's swap-join withdraws from a sum's tail. -/
theorem BPair.add_swap_self (r d : BPair) : (r + d.swap + d).oneValue r :=
  BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm (r + d.swap) d))
    (BPair.add_swap_cancel d r)

/-- Completing the square over the balance pairs: a square less
its double product against a datum, joined to a constant, is the
shifted square joined to the constant less the datum's square. -/
theorem complete_sq (δ u v : BPair) :
    (δ * δ + v + (u * δ + u * δ).swap).oneValue
      ((δ + u.swap) * (δ + u.swap) + (v + (u * u).swap)) := by
  rw [BPair.sq_expand_swap δ u, BPair.swap_add, BPair.mul_comm δ u]
  have e1 : δ * δ + u * u + (u * δ + u * δ).swap + (v + (u * u).swap)
      = δ * δ + v + (u * δ + u * δ).swap + (u * u + (u * u).swap) := by
    rw [BPair.add_right_comm (δ * δ) (u * u) ((u * δ + u * δ).swap),
      BPair.add_assoc (δ * δ + (u * δ + u * δ).swap) (u * u) (v + (u * u).swap),
      BPair.add_left_comm (u * u) v ((u * u).swap),
      ← BPair.add_assoc (δ * δ + (u * δ + u * δ).swap) v (u * u + (u * u).swap),
      BPair.add_right_comm (δ * δ) ((u * δ + u * δ).swap) v]
  rw [e1]
  exact BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_swap_null (u * u)))
    (BPair.add_unit _))

/-- The unit rescaling is the datum itself. -/
theorem BPair.scale_one (x : BPair) : x.scale Pos.one = x := by
  show BPair.mk (x.fst * Pos.one) (x.snd * Pos.one) = x
  rw [mul_one, mul_one]

/-- The doubling at the balance carrier: the rescaling by two is the
datum joined to itself. -/
theorem BPair.scale_two (z : BPair) : z.scale 2 = z + z := by
  rw [show (2 : Pos) = Pos.one + Pos.one from rfl, BPair.scale_addW,
    BPair.scale_one]

/-- A ground datum entering the balance carrier at the one-member
site is the memberwise rescaling: `[w] · d` is one value with
`d.scale w`. -/
theorem BPair.ofPos_scale (w : Pos) (d : BPair) :
    (BPair.ofPos w * d).oneValue (d.scale w) := by
  show (w + Pos.one) * d.fst + Pos.one * d.snd + d.snd * w
    = d.fst * w + ((w + Pos.one) * d.snd + Pos.one * d.fst)
  rw [ground.right_distrib, ground.right_distrib, ground.one_mul,
    ground.one_mul, ground.mul_comm d.snd w, ground.mul_comm d.fst w,
    ground.add_assoc (w * d.fst + d.fst) d.snd (w * d.snd),
    ground.add_assoc (w * d.fst) d.fst (d.snd + w * d.snd),
    ground.add_comm d.snd (w * d.snd),
    ground.add_comm d.fst (w * d.snd + d.snd)]

/-- The count two against a datum is the datum joined to itself. -/
theorem BPair.ofNat_two_mul (z : BPair) : (BPair.ofNat 2 * z).oneValue (z + z) := by
  rw [← BPair.scale_two z]
  exact BPair.ofPos_scale 2 z

/-- A sited datum sits off the sum's unit: the one-member site is
an occupied count's own read. -/
theorem BPair.ofPos_off (a : Pos) : (BPair.ofPos a).offUnit :=
  BPair.ofNat_off_unit (a.pred + 1) (Nat.succ_pos a.pred)

/-- A pair against a positive datum's pair reads the pair rescaled
by the datum. -/
theorem BPair.mul_ofPos (x : BPair) (d : Pos) :
    (x * BPair.ofPos d).oneValue (x.scale d) := by
  show x.fst * (d + Pos.one) + x.snd * Pos.one + x.snd * d
    = x.fst * d + (x.fst * Pos.one + x.snd * (d + Pos.one))
  rw [ground.left_distrib, ground.left_distrib, ground.mul_one,
    ground.mul_one, ground.add_assoc (x.fst * d) x.fst x.snd,
    ground.add_assoc (x.fst * d) (x.fst + x.snd) (x.snd * d),
    ground.add_assoc x.fst x.snd (x.snd * d),
    ground.add_comm x.snd (x.snd * d)]

/-- A one-member site's rescaling by a ground datum is the sited
product: `[w] · v` is one value with `[wv]`. -/
theorem BPair.scale_ofPos (w v : Pos) :
    ((BPair.ofPos w).scale v).oneValue (BPair.ofPos (w * v)) := by
  show (w + Pos.one) * v + Pos.one = w * v + Pos.one + Pos.one * v
  rw [ground.right_distrib w Pos.one v, ground.one_mul v,
    ground.add_right_comm (w * v) v Pos.one]

/-- The one-member sites multiply at the ground product:
`[a][b]` is one value with `[ab]`. -/
theorem BPair.ofPos_mul (a b : Pos) :
    (BPair.ofPos a * BPair.ofPos b).oneValue (BPair.ofPos (a * b)) :=
  BPair.oneValue_trans (BPair.ofPos_scale a (BPair.ofPos b))
    (BPair.oneValue_trans (BPair.scale_ofPos b a)
      (BPair.oneValue_of_eq
        (congrArg BPair.ofPos (ground.mul_comm b a))))

/-- The unit's one-member read multiplies as the unit. -/
theorem BPair.ofPos_one_mul (z : BPair) :
    (BPair.ofPos Pos.one * z).oneValue z :=
  BPair.oneValue_trans (BPair.ofPos_scale Pos.one z)
    (BPair.oneValue_of_eq (BPair.scale_one z))

/-- The one-member site is additive in the ground datum: the summed
datum's site is the two sites' own sum. -/
theorem BPair.ofPos_add (a b : Pos) :
    (BPair.ofPos (a + b)).oneValue (BPair.ofPos a + BPair.ofPos b) := by
  show a + b + Pos.one + (Pos.one + Pos.one)
    = a + Pos.one + (b + Pos.one) + Pos.one
  rw [ground.add_add_comm a Pos.one b Pos.one,
    ground.add_assoc (a + b) Pos.one (Pos.one + Pos.one),
    ground.add_assoc (a + b) (Pos.one + Pos.one) Pos.one,
    ground.add_assoc Pos.one Pos.one Pos.one]

/-- The power at a natural key, the product's fold. -/
def bpow (x : BPair) : Nat → BPair
  | 0 => BPair.ofPos .one
  | m + 1 => (x * bpow x m).norm

/-- The pair's margin as a natural: the exceeding member's gap, an
equal-membered pair reading nought — the magnitude's ground read,
`pred` the ground module's own. -/
def BPair.marginN (x : BPair) : Nat :=
  if x.fst.pred ≤ x.snd.pred then x.snd.pred - x.fst.pred
  else x.fst.pred - x.snd.pred

/-- Exchanging the members keeps their gap's magnitude. -/
theorem BPair.marginN_swap (x : BPair) : x.swap.marginN = x.marginN := by
  change (if x.snd.pred ≤ x.fst.pred then x.fst.pred - x.snd.pred
      else x.snd.pred - x.fst.pred)
    = if x.fst.pred ≤ x.snd.pred then x.snd.pred - x.fst.pred
      else x.fst.pred - x.snd.pred
  by_cases h : x.fst.pred ≤ x.snd.pred
  · by_cases h' : x.snd.pred ≤ x.fst.pred
    · rw [if_pos h, if_pos h', Nat.le_antisymm h h']
    · rw [if_pos h, if_neg h']
  · rw [if_neg h, if_pos (Nat.le_of_lt (Nat.lt_of_not_le h))]

private theorem marginParity (a b : Nat) :
    (if a ≤ b then b - a else a - b) % 2 = (a + b) % 2 := by
  by_cases h : a ≤ b
  · rw [if_pos h]
    obtain ⟨k, hk⟩ := Nat.le.dest h
    rw [← hk, ground.addSubSelfL]
    have he : a + (a + k) = k + a * 2 := by
      rw [Nat.mul_succ, Nat.mul_one, ← Nat.add_assoc, Nat.add_comm (a + a) k]
    rw [he, ground.modAddMul]
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Nat.le.dest (Nat.le_of_lt (Nat.lt_of_not_le h))
    rw [← hk, ground.addSubSelfL]
    have he : b + k + b = k + b * 2 := by
      rw [Nat.mul_succ, Nat.mul_one, Nat.add_right_comm b k b, Nat.add_comm (b + b) k]
    rw [he, ground.modAddMul]

/-- A balance value's parity is its two stored counts' sum's
parity, independent of the larger member. -/
theorem BPair.marginN_mod_two (x : BPair) :
    x.marginN % 2 = (x.fst.pred + x.snd.pred) % 2 := marginParity _ _

/-- The margin's parity adds across a balance-pair sum. -/
theorem BPair.marginN_add_mod_two (x y : BPair) :
    (x + y).marginN % 2 = (x.marginN + y.marginN) % 2 := by
  rw [BPair.marginN_mod_two (x + y), ← ground.modAdd x.marginN y.marginN 2,
    BPair.marginN_mod_two x, BPair.marginN_mod_two y, ground.modAdd]
  change ((x.fst.pred + y.fst.pred + 1) + (x.snd.pred + y.snd.pred + 1)) % 2
    = ((x.fst.pred + x.snd.pred) + (y.fst.pred + y.snd.pred)) % 2
  rw [Nat.add_add_add_comm (x.fst.pred + y.fst.pred) 1 (x.snd.pred + y.snd.pred) 1,
    Nat.add_add_add_comm x.fst.pred y.fst.pred x.snd.pred y.snd.pred,
    ground.modAddSelf]

/-- Joining a pair to itself has even margin. -/
theorem BPair.marginN_double (x : BPair) : (x + x).marginN % 2 = 0 := by
  rw [BPair.marginN_add_mod_two]
  have h := ground.modAddMul 0 x.marginN 2
  rw [Nat.zero_add, Nat.mul_succ, Nat.mul_one] at h
  exact h

/-- Two pairs at one margin parity have an even joined margin. -/
theorem BPair.marginN_add_even (x y : BPair) (h : x.marginN % 2 = y.marginN % 2) :
    (x + y).marginN % 2 = 0 := by
  rw [BPair.marginN_add_mod_two, ← ground.modAdd x.marginN y.marginN 2, h]
  have hm := ground.modAddMul 0 (y.marginN % 2) 2
  rw [Nat.zero_add, Nat.mul_succ, Nat.mul_one] at hm
  exact hm

/-- A list's content, the greatest common divisor of its members'
margins — the coefficients' one shared count (`thm:windowsep`'s
primitive strip), the kernel's own `Nat.gcd`. -/
def BPair.listContent (l : List BPair) : Nat :=
  l.foldl (fun k x => Nat.gcd k (BPair.marginN x)) 0

/-- A list's shared count with a clearing: the greatest common
divisor of the members' content and the clearing's value, the
reduced representative's divisor. -/
def BPair.sharedCount (l : List BPair) (c : Pos) : Nat :=
  Nat.gcd (BPair.listContent l) (posVal c)

/-- The list stripped at a stated count: each member's margin divided
exactly at its own side, a member off the division kept, the vacant
count the identity. -/
def BPair.listPrim (n : Nat) (l : List BPair) : List BPair :=
  l.map (fun x =>
    if n == 0 then x
    else if BPair.marginN x % n == 0 then
      match x.side with
      | .lt _ _ => ⟨.one, posOfSucc (BPair.marginN x / n)⟩
      | .eq _ => BPair.unit
      | .gt _ _ => ⟨posOfSucc (BPair.marginN x / n), .one⟩
    else x)

/-- A keyed join into an association list: the key's entry joined
at the stated sum, a fresh key appended at its datum. -/
def joinBy {α β : Type} (eq : α → α → Bool) (add : β → β → β)
    (k : α) (x : β) : List (α × β) → List (α × β)
  | [] => [(k, x)]
  | (v, y) :: t =>
    if eq v k then (v, add y x) :: t else (v, y) :: joinBy eq add k x t

/-- The lexicographic order on natural lists, the shorter list
first at a shared prefix. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: s, y :: t => x < y || (x == y && lexLt s t)

/-- A list's two halves, the members alternating. -/
def halvesL {α : Type} : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t => let h := halvesL t; (x :: h.1, y :: h.2)

/-- A keyed list's keys in a stated order: every consecutive pair
at the relation, the strict order reading no two keys equal. -/
def keysInOrder {α β : Type} (rel : α → α → Bool) : List (α × β) → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => rel x.1 y.1 && keysInOrder rel (y :: t)

/-- Two keyed lists sorted at a stated order walked together, one
member per key on each side: at a shared key the stated join of
the two members with the walk's rest, at a key one list alone
occupies that side's step, and the two lists at the fuel's end the
stated stop; the fuel the counts' sum. -/
def mergeWith {α β γ δ : Type} (lt eq : α → α → Bool)
    (stop : List (α × β) → List (α × γ) → δ)
    (both : α → β → γ → δ → δ) (left : α × β → δ → δ)
    (right : α × γ → δ → δ) :
    Nat → List (α × β) → List (α × γ) → δ
  | 0, a, b => stop a b
  | _ + 1, [], b => stop [] b
  | _ + 1, x :: s, [] => stop (x :: s) []
  | fuel + 1, x :: s, y :: t =>
    if eq x.1 y.1 then
      both x.1 x.2 y.2 (mergeWith lt eq stop both left right fuel s t)
    else if lt x.1 y.1 then
      left x (mergeWith lt eq stop both left right fuel s (y :: t))
    else right y (mergeWith lt eq stop both left right fuel (x :: s) t)

/-- The merge of two keyed lists sorted at a stated order, two
members at one key joined at the stated sum, a key one list alone
occupies kept, the lists at the fuel's end joined (`mergeWith`). -/
def mergeJoin {α β : Type} (lt eq : α → α → Bool) (add : β → β → β) :
    Nat → List (α × β) → List (α × β) → List (α × β) :=
  mergeWith lt eq (fun a b => a ++ b) (fun k x y r => (k, add x y) :: r)
    (fun x r => x :: r) (fun y r => y :: r)

/-- A keyed list sorted at a stated order with equal keys joined at
the stated sum, the merge descent over the halves at the count's
fuel: the collected family at its sorted keys. -/
def sortJoin {α β : Type} (lt eq : α → α → Bool) (add : β → β → β) :
    Nat → List (α × β) → List (α × β)
  | 0, l => l
  | fuel + 1, l =>
    match l with
    | [] => []
    | [x] => [x]
    | _ :: _ :: _ =>
      let h := halvesL l
      let a := sortJoin lt eq add fuel h.1
      let b := sortJoin lt eq add fuel h.2
      mergeJoin lt eq add (a.length + b.length) a b

/-- Two keyed lists of runs sorted at a stated order walked
together at the stated product: at a shared key every member of
the one run against every member of the other, one output per
member pair, a key one list alone occupies walked past
(`mergeWith`). -/
def mergeCross {α β γ δ : Type} (lt eq : α → α → Bool) (mul : β → γ → δ) :
    Nat → List (α × List β) → List (α × List γ) → List δ :=
  mergeWith lt eq (fun _ _ => [])
    (fun _ xs ys r => xs.flatMap (fun p => ys.map (mul p)) ++ r)
    (fun _ r => r) (fun _ r => r)

/-- Two keyed lists sorted at a stated order, one member per key,
one value at every key either occupies: the members one value at a
shared key and at the stated unit at a key one list alone occupies
(`mergeWith`). -/
def mergeEqBy {α β : Type} (lt eq : α → α → Bool) (isUnit : β → Bool)
    (eqB : β → β → Bool) : Nat → List (α × β) → List (α × β) → Bool :=
  mergeWith lt eq
    (fun a b => a.all (fun x => isUnit x.2) && b.all (fun y => isUnit y.2))
    (fun _ x y r => eqB x y && r) (fun x r => isUnit x.2 && r)
    (fun y r => isUnit y.2 && r)

/-- A keyed list's adjacent members at one key gathered into one
run, the keys' order kept. -/
def groupRuns {α β : Type} (eq : α → α → Bool) : List (α × β) → List (α × List β)
  | [] => []
  | x :: t =>
    match groupRuns eq t with
    | (k, ys) :: r => if eq x.1 k then (x.1, x.2 :: ys) :: r else (x.1, [x.2]) :: (k, ys) :: r
    | [] => [(x.1, [x.2])]

/-- A keyed list sorted at a stated order into its runs, every
member kept: a list whose keys are already in order at the stated
order's reflexive closure gathers its runs outright, and every
further list sorts at the runs' join (`sortJoin`). -/
def sortRuns {α β : Type} (lt eq : α → α → Bool) (l : List (α × β)) :
    List (α × List β) :=
  if keysInOrder (fun x y => !lt y x) l then groupRuns eq l
  else sortJoin lt eq (fun u v => u ++ v) l.length (l.map (fun p => (p.1, [p.2])))

/-- A keyed family of balance pairs collected at its keys in the
keys' order: the coefficients at one key joined and every
coefficient read at its canonical representative (`sortJoin`;
`BPair.norm`), the members at the sum's unit withdrawn, so the
collected family is the occupancy family of the read; a family
already at strictly increasing keys is its own sorted join. -/
def collectBy {α : Type} (lt eq : α → α → Bool) (l : List (α × BPair)) :
    List (α × BPair) :=
  ((if keysInOrder lt l then l else sortJoin lt eq (fun y x => (y + x).norm) l.length l).map
    (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep)

/-- Two keyed families one value at every key either occupies, the
collected families walked together (`mergeEqBy`). -/
def oneValueBy {α : Type} (lt eq : α → α → Bool) (a b : List (α × BPair)) : Bool :=
  let a' := collectBy lt eq a
  let b' := collectBy lt eq b
  mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
    (fun x y => decide (x.oneValue y)) (a'.length + b'.length) a' b'

/-! The composite pair `[⟨u : v⟩ : c]`, the balance pair of its
members' pairs at the one shared second datum; the reads are the two
displays' compositions, displayed once. -/

set_option genInjectivity false in
/-- The composite `[⟨u : v⟩ : c]` at a balance-pair first datum and
a shared second datum. -/
structure CPair where
  num : BPair
  den : Pos

/-- `[⟨u:v⟩:c] + [⟨u':v'⟩:c'] = [⟨uc'+u'c : vc'+v'c⟩ : cc']`. -/
def CPair.add (x y : CPair) : CPair :=
  ⟨⟨x.num.fst * y.den + y.num.fst * x.den,
    x.num.snd * y.den + y.num.snd * x.den⟩, x.den * y.den⟩

instance instGround25 : Add CPair := ⟨CPair.add⟩

/-- `[⟨u:v⟩:c][⟨u':v'⟩:c'] = [⟨uu'+vv' : uv'+vu'⟩ : cc']`. -/
def CPair.mul (x y : CPair) : CPair := ⟨x.num * y.num, x.den * y.den⟩

instance instGround26 : Mul CPair := ⟨CPair.mul⟩

/-- One value exactly at the cross-added equality
`uc' + v'c = u'c + vc'`. -/
def CPair.oneValue (x y : CPair) : Prop :=
  x.num.fst * y.den + y.num.snd * x.den
    = y.num.fst * x.den + x.num.snd * y.den

instance instGround27 (x y : CPair) : Decidable (x.oneValue y) :=
  inferInstanceAs (Decidable (_ = _))


/-- The order is the cross-added read `uc' + v'c < u'c + vc'`. -/
instance instGround28 : LT CPair := ⟨fun x y =>
  x.num.fst * y.den + y.num.snd * x.den
    < y.num.fst * x.den + x.num.snd * y.den⟩

instance instGround29 (x y : CPair) : Decidable (x < y) :=
  inferInstanceAs (Decidable
    ((x.num.fst * y.den + y.num.snd * x.den : Pos)
      < y.num.fst * x.den + x.num.snd * y.den))

/-- At or below over the composites: the trichotomy's one-value and
below outcomes. -/
instance instGround30 : LE CPair := ⟨fun x y => x.oneValue y ∨ x < y⟩

instance instGround31 (x y : CPair) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The side is the first datum's own at every second datum. -/
def CPair.side (x : CPair) : Trich x.num.fst x.num.snd := x.num.side

/-- The memberwise swap at the first datum, the balance-pair swap's
composite instance at the shared second datum. -/
def CPair.swap (x : CPair) : CPair := ⟨x.num.swap, x.den⟩

/-- A scalar pair enters at a one-member site through the members'
display: `[a : b]` is `[⟨a + w : w⟩ : b]` at every `w`, one value. -/
def CPair.ofPair (p : Pair) (w : Pos) : CPair :=
  ⟨⟨p.num + w, w⟩, p.den⟩

/-- The one-member entries at two paddings are one value. -/
theorem CPair.ofPair_oneValue (p : Pair) (w w' : Pos) :
    (CPair.ofPair p w).oneValue (CPair.ofPair p w') := by
  show (p.num + w) * p.den + w' * p.den = (p.num + w') * p.den + w * p.den
  rw [right_distrib, right_distrib, ground.add_assoc, ground.add_assoc,
    ground.add_comm (w * p.den) (w' * p.den)]

/-- Two one-member entries at one scalar value are one value at
every pair of paddings, the composite's read of the scalar
congruence. -/
theorem CPair.ofPair_congr {p q : Pair} (h : p.oneValue q)
    (u v : Pos) :
    (CPair.ofPair p u).oneValue (CPair.ofPair q v) := by
  show (p.num + u) * q.den + v * p.den
    = (q.num + v) * p.den + u * q.den
  rw [right_distrib, right_distrib,
    show p.num * q.den = q.num * p.den from h,
    ground.add_assoc, ground.add_assoc,
    ground.add_comm (u * q.den) (v * p.den)]

/-- Sums read one value at either order, a ground identity of the
fold. -/
theorem CPair.add_comm (x y : CPair) : x + y = y + x := by
  show CPair.mk
      (BPair.mk (x.num.fst * y.den + y.num.fst * x.den)
        (x.num.snd * y.den + y.num.snd * x.den)) (x.den * y.den)
    = CPair.mk
      (BPair.mk (y.num.fst * x.den + x.num.fst * y.den)
        (y.num.snd * x.den + x.num.snd * y.den)) (y.den * x.den)
  rw [ground.add_comm (x.num.fst * y.den) (y.num.fst * x.den),
    ground.add_comm (x.num.snd * y.den) (y.num.snd * x.den),
    ground.mul_comm x.den y.den]

/-- Two fold orders are equal by the ground identities. -/
theorem CPair.add_assoc (x y z : CPair) : x + y + z = x + (y + z) := by
  show CPair.mk
      (BPair.mk
        ((x.num.fst * y.den + y.num.fst * x.den) * z.den
          + z.num.fst * (x.den * y.den))
        ((x.num.snd * y.den + y.num.snd * x.den) * z.den
          + z.num.snd * (x.den * y.den)))
      (x.den * y.den * z.den)
    = CPair.mk
      (BPair.mk
        (x.num.fst * (y.den * z.den)
          + (y.num.fst * z.den + z.num.fst * y.den) * x.den)
        (x.num.snd * (y.den * z.den)
          + (y.num.snd * z.den + z.num.snd * y.den) * x.den))
      (x.den * (y.den * z.den))
  rw [right_distrib, right_distrib, right_distrib, right_distrib,
    mul_assoc x.num.fst y.den z.den, mul_assoc x.num.snd y.den z.den,
    mul_right_comm y.num.fst x.den z.den,
    mul_right_comm y.num.snd x.den z.den,
    show z.num.fst * (x.den * y.den) = z.num.fst * y.den * x.den from by
      rw [mul_assoc, ground.mul_comm y.den x.den],
    show z.num.snd * (x.den * y.den) = z.num.snd * y.den * x.den from by
      rw [mul_assoc, ground.mul_comm y.den x.den],
    ground.add_assoc, ground.add_assoc, mul_assoc x.den y.den z.den]

/-- The fold over a finite family of composites seeds at the sum's
unit, the equal-membered class, and adds the members, total at
every family. -/
def CPair.sum (l : List CPair) : CPair :=
  l.foldl CPair.add ⟨⟨.one, .one⟩, .one⟩

/-- The equal-membered class is the composite's sum unit as well, a
summand on both members fixing the value at every second datum. -/
theorem CPair.opUnit_oneValue (x : CPair) (w c : Pos) :
    (x + ⟨⟨w, w⟩, c⟩).oneValue x := by
  show (x.num.fst * c + w * x.den) * x.den + x.num.snd * (x.den * c)
      = x.num.fst * (x.den * c) + (x.num.snd * c + w * x.den) * x.den
  rw [right_distrib, right_distrib, mul_assoc x.num.fst c x.den,
    ground.mul_comm c x.den,
    show x.num.snd * (x.den * c) = x.num.snd * c * x.den from by
      rw [mul_assoc, ground.mul_comm x.den c],
    ground.add_assoc,
    ground.add_comm (w * x.den * x.den) (x.num.snd * c * x.den)]

/-- A representative rescaling read through the shared second datum:
the one-value read scaled by any `w`. -/
theorem CPair.scale_congr_den {x x' : CPair} (hx : x.oneValue x')
    (w : Pos) : BPair.oneValue (x.num.scale (x'.den * w))
      (x'.num.scale (x.den * w)) := by
  have h := BPair.scale_congr (w := w)
    (x := x.num.scale x'.den) (y := x'.num.scale x.den) hx
  rw [BPair.scale_scale, BPair.scale_scale] at h
  exact h

theorem CPair.oneValue_refl (x : CPair) : x.oneValue x := rfl

theorem CPair.oneValue_symm {x y : CPair} (h : x.oneValue y) :
    y.oneValue x := h.symm

/-- The composite's one-value read is a class read, transitivity by
the shared datum's cancellation. -/
theorem CPair.oneValue_trans {x y z : CPair} (h1 : x.oneValue y)
    (h2 : y.oneValue z) : x.oneValue z := by
  show BPair.oneValue (x.num.scale z.den) (z.num.scale x.den)
  refine BPair.scale_cancel (w := y.den) ?_
  rw [BPair.scale_scale, BPair.scale_scale]
  have hA := CPair.scale_congr_den h1 z.den
  have hB := CPair.scale_congr_den h2 x.den
  rw [ground.mul_comm z.den y.den, ground.mul_comm x.den y.den]
  rw [ground.mul_comm x.den z.den] at hA
  exact BPair.oneValue_trans hA hB

/-- The composite pair's first-component congruence at a shared
second datum: the members' cross-add clears at the one
distributivity. -/
theorem CPair.num_oneValue {p p' : BPair} (h : p.oneValue p')
    (c : Pos) : CPair.oneValue ⟨p, c⟩ ⟨p', c⟩ := by
  show p.fst * c + p'.snd * c = p'.fst * c + p.snd * c
  rw [← ground.right_distrib, ← ground.right_distrib,
    show p.fst + p'.snd = p'.fst + p.snd from h]

/-- The one-value read moves across a first-component one-value at
a shared second datum, both ways. -/
theorem CPair.num_congr {p p' : BPair} (h : p.oneValue p')
    (c : Pos) (y : CPair) :
    CPair.oneValue ⟨p, c⟩ y ↔ CPair.oneValue ⟨p', c⟩ y :=
  ⟨fun e => CPair.oneValue_trans
    (CPair.oneValue_symm (CPair.num_oneValue h c)) e,
   fun e => CPair.oneValue_trans (CPair.num_oneValue h c) e⟩

private theorem CPair.cross_fst {x x' : CPair} (hx : x.oneValue x')
    (y y' : CPair) : BPair.oneValue
      (x.num.scale (y.den * (x'.den * y'.den)))
      (x'.num.scale (y'.den * (x.den * y.den))) := by
  rw [mul_left_comm y.den x'.den y'.den,
    mul_left_comm y'.den x.den y.den, ground.mul_comm y'.den y.den]
  exact CPair.scale_congr_den hx (y.den * y'.den)

private theorem CPair.cross_snd {y y' : CPair} (hy : y.oneValue y')
    (x x' : CPair) : BPair.oneValue
      (y.num.scale (x.den * (x'.den * y'.den)))
      (y'.num.scale (x'.den * (x.den * y.den))) := by
  rw [ground.mul_comm x'.den y'.den, mul_left_comm x.den y'.den x'.den,
    mul_left_comm x'.den x.den y.den, ground.mul_comm x'.den y.den,
    mul_left_comm x.den y.den x'.den]
  exact CPair.scale_congr_den hy (x.den * x'.den)

/-- The homogeneity principle at the composite sum. -/
theorem CPair.add_congr {x x' y y' : CPair} (hx : x.oneValue x')
    (hy : y.oneValue y') : (x + y).oneValue (x' + y') := by
  show BPair.oneValue
    ((x.num.scale y.den + y.num.scale x.den).scale (x'.den * y'.den))
    ((x'.num.scale y'.den + y'.num.scale x'.den).scale (x.den * y.den))
  rw [BPair.scale_add, BPair.scale_add, BPair.scale_scale,
    BPair.scale_scale, BPair.scale_scale, BPair.scale_scale]
  exact BPair.add_congr (CPair.cross_fst hx y y') (CPair.cross_snd hy x x')

/-- The homogeneity principle at the composite product. -/
theorem CPair.mul_congr {x x' y y' : CPair} (hx : x.oneValue x')
    (hy : y.oneValue y') : (x * y).oneValue (x' * y') := by
  show BPair.oneValue ((x.num * y.num).scale (x'.den * y'.den))
      ((x'.num * y'.num).scale (x.den * y.den))
  rw [BPair.scale_mul, BPair.scale_mul]
  exact BPair.mul_congr hx hy

/-- The homogeneity principle at the composite order: a comparison
holds exactly at its rescaling. -/
theorem CPair.lt_congr {x x' y y' : CPair} (hx : x.oneValue x')
    (hy : y.oneValue y') (h : x < y) : x' < y' := by
  show (x'.num.scale y'.den) < (y'.num.scale x'.den)
  refine BPair.lt_of_scale_lt (w := x.den * y.den) ?_
  rw [BPair.scale_scale, BPair.scale_scale]
  have h' := BPair.scale_lt (x := x.num.scale y.den)
    (y := y.num.scale x.den) (x'.den * y'.den) h
  rw [BPair.scale_scale, BPair.scale_scale] at h'
  exact BPair.lt_congr (CPair.cross_fst hx y y') (CPair.cross_snd hy x x') h'

/-- The sum's unit drops on its left at the composite carrier. -/
private theorem CPair.unitOp (x : CPair) :
    ((⟨⟨.one, .one⟩, .one⟩ : CPair) + x).oneValue x := by
  rw [CPair.add_comm]
  exact CPair.opUnit_oneValue x .one .one

/-- A composite equality reads at the one-value relation. -/
private theorem CPair.oneValue_of_eq : ∀ {x y : CPair}, x = y →
    x.oneValue y
  | _, _, rfl => CPair.oneValue_refl _

/-- The composite's displayed sum at its one-value relation. -/
private theorem cpairFoldLaws :
    FoldLaws CPair CPair.add ⟨⟨.one, .one⟩, .one⟩ CPair.oneValue where
  ovRefl := CPair.oneValue_refl
  ovSymm := CPair.oneValue_symm
  ovTrans := CPair.oneValue_trans
  opCongr := CPair.add_congr
  opComm := fun x y => CPair.oneValue_of_eq (CPair.add_comm x y)
  opAssoc := fun x y z =>
    CPair.oneValue_of_eq (CPair.add_assoc x y z)
  unitOp := CPair.unitOp
  opUnit := fun x => CPair.opUnit_oneValue x .one .one

/-- The head splits off the composite family's fold. -/
theorem CPair.sum_cons (b : CPair) (m : List CPair) :
    (CPair.sum (b :: m)).oneValue (b + CPair.sum m) :=
  sumConsO cpairFoldLaws b m

/-- The joined family's composite fold splits. -/
theorem CPair.sum_append : ∀ u w : List CPair,
    (CPair.sum (u ++ w)).oneValue (CPair.sum u + CPair.sum w) :=
  sumAppendO cpairFoldLaws

/-- A representative rescaling: the numerator and the second datum
scaled by one `w` read the original. -/
theorem CPair.scale_oneValue (p : BPair) (c w : Pos) :
    CPair.oneValue ⟨p.scale w, c * w⟩ ⟨p, c⟩ := by
  show p.fst * w * c + p.snd * (c * w) = p.fst * (c * w) + p.snd * w * c
  rw [ground.mul_assoc p.fst w c, ground.mul_comm w c,
    ground.mul_assoc p.snd w c, ground.mul_comm w c]

/-- The composite product distributes across the sum at the
one-value read, the two sides parting by the repeated second
datum. -/
theorem CPair.mul_add (x y z : CPair) :
    (x * (y + z)).oneValue (x * y + x * z) := by
  have hnum : (x * y + x * z).num = (x * (y + z)).num.scale x.den := by
    show (x.num * y.num).scale (x.den * z.den)
        + (x.num * z.num).scale (x.den * y.den)
      = (x.num * (y.num.scale z.den + z.num.scale y.den)).scale x.den
    rw [BPair.left_distrib, BPair.mul_scale, BPair.mul_scale,
      BPair.scale_add, BPair.scale_scale, BPair.scale_scale,
      ground.mul_comm z.den x.den, ground.mul_comm y.den x.den]
  have hden : (x * y + x * z).den = (x * (y + z)).den * x.den := by
    show x.den * y.den * (x.den * z.den)
      = x.den * (y.den * z.den) * x.den
    rw [ground.mul_mul_mul_comm x.den y.den x.den z.den,
      ground.mul_right_comm x.den (y.den * z.den) x.den]
  have h : (x * y + x * z)
      = CPair.mk ((x * (y + z)).num.scale x.den)
        ((x * (y + z)).den * x.den) := by
    rw [← hnum, ← hden]
  rw [h]
  exact CPair.oneValue_symm
    (CPair.scale_oneValue (x * (y + z)).num (x * (y + z)).den x.den)

/-- Two composites at one second datum join at that datum. -/
theorem CPair.add_same (u v : BPair) (w : Pos) :
    ((⟨u, w⟩ : CPair) + ⟨v, w⟩).oneValue ⟨u + v, w⟩ := by
  have he : ((⟨u, w⟩ : CPair) + ⟨v, w⟩) = ⟨(u + v).scale w, w * w⟩ := by
    show CPair.mk ⟨u.fst * w + v.fst * w, u.snd * w + v.snd * w⟩ (w * w)
      = ⟨(u + v).scale w, w * w⟩
    rw [← right_distrib, ← right_distrib]
    rfl
  rw [he]
  exact CPair.scale_oneValue (u + v) w w

/-- A composite at the second datum's own rewriting. -/
theorem CPair.den_congr {u : BPair} {c e : Pos} (h : c = e) :
    (⟨u, c⟩ : CPair).oneValue ⟨u, e⟩ := by
  rw [h]
  exact CPair.oneValue_refl _

/-- The composite at-or-below read moves across the one-value
read. -/
theorem CPair.le_congr {x x' y y' : CPair} (hx : x.oneValue x')
    (hy : y.oneValue y') (h : x ≤ y) : x' ≤ y' :=
  match h with
  | Or.inl e =>
    Or.inl (CPair.oneValue_trans (CPair.oneValue_symm hx)
      (CPair.oneValue_trans e hy))
  | Or.inr e => Or.inr (CPair.lt_congr hx hy e)

/-- A member joined to its own memberwise swap lands on the sum's
unit: the joined pair's two members are the one datum, a summand on
both members fixing the value. -/
theorem CPair.add_swap_unit (x y : CPair) :
    (y + (x + x.swap)).oneValue y := by
  have h : x + x.swap
      = CPair.mk ⟨x.num.fst * x.den + x.num.snd * x.den,
          x.num.fst * x.den + x.num.snd * x.den⟩ (x.den * x.den) := by
    show CPair.mk ⟨x.num.fst * x.den + x.num.snd * x.den,
        x.num.snd * x.den + x.num.fst * x.den⟩ (x.den * x.den) = _
    rw [ground.add_comm (x.num.snd * x.den) (x.num.fst * x.den)]
  rw [h]
  exact CPair.opUnit_oneValue y _ _

/-- The memberwise swap keeps the one-value read, the cross-added
equation read at its exchanged members. -/
theorem CPair.swap_congr {x y : CPair} (h : x.oneValue y) :
    x.swap.oneValue y.swap := by
  show x.num.snd * y.den + y.num.fst * x.den
    = y.num.snd * x.den + x.num.fst * y.den
  rw [ground.add_comm (x.num.snd * y.den) (y.num.fst * x.den),
    ground.add_comm (y.num.snd * x.den) (x.num.fst * y.den)]
  exact h.symm

/-- A member sits below its swap exactly at its first datum's own
side. -/
private theorem CPair.lt_swap_of (y : CPair)
    (h : y.num.fst < y.num.snd) : y < y.swap := by
  show y.num.fst * y.den + y.num.fst * y.den
    < y.num.snd * y.den + y.num.snd * y.den
  exact addSelfLt (mul_lt_mul_right y.den h)

/-- The swap comparison reads the first datum's side back. -/
private theorem CPair.num_lt_of_lt_swap {y : CPair} (h : y < y.swap) :
    y.num.fst < y.num.snd := by
  have h' : y.num.fst * y.den + y.num.fst * y.den
      < y.num.snd * y.den + y.num.snd * y.den := h
  exact lt_of_mul_lt (ltOfAddSelfLt h')

/-- A shared summand cancels on the right of the ground order's
strict read. -/
theorem posLtCancelR {a b c : Pos} (h : a + c < b + c) : a < b := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ground.add_right_cancel (c := c) ?_⟩
  rw [ground.add_right_comm a g c]
  exact hg

/-- A one-member factor keeps the side at the swap comparison: the
factor's own member joins both sides equally and its first datum
rescales the gap. -/
theorem CPair.mul_lt_swap (u : Pair) (w : Pos) (x : CPair) :
    (CPair.ofPair u w * x < (CPair.ofPair u w * x).swap) ↔
      (x < x.swap) := by
  have e1 : (CPair.ofPair u w * x).num.fst
      = u.num * x.num.fst + (w * x.num.fst + w * x.num.snd) := by
    show (u.num + w) * x.num.fst + w * x.num.snd
      = u.num * x.num.fst + (w * x.num.fst + w * x.num.snd)
    rw [ground.right_distrib, ground.add_assoc]
  have e2 : (CPair.ofPair u w * x).num.snd
      = u.num * x.num.snd + (w * x.num.fst + w * x.num.snd) := by
    show (u.num + w) * x.num.snd + w * x.num.fst
      = u.num * x.num.snd + (w * x.num.fst + w * x.num.snd)
    rw [ground.right_distrib, ground.add_assoc,
      ground.add_comm (w * x.num.snd) (w * x.num.fst)]
  constructor
  · intro h
    have h1 : (CPair.ofPair u w * x).num.fst
        < (CPair.ofPair u w * x).num.snd :=
      CPair.num_lt_of_lt_swap h
    rw [e1, e2] at h1
    have h2 : u.num * x.num.fst < u.num * x.num.snd := posLtCancelR h1
    have h3 : x.num.fst * u.num < x.num.snd * u.num := by
      rw [ground.mul_comm x.num.fst u.num, ground.mul_comm x.num.snd u.num]
      exact h2
    exact CPair.lt_swap_of x (lt_of_mul_lt h3)
  · intro h
    have h1 : x.num.fst < x.num.snd := CPair.num_lt_of_lt_swap h
    have h2 : u.num * x.num.fst < u.num * x.num.snd := by
      rw [ground.mul_comm u.num x.num.fst, ground.mul_comm u.num x.num.snd]
      exact mul_lt_mul_right u.num h1
    refine CPair.lt_swap_of (CPair.ofPair u w * x) ?_
    rw [e1, e2]
    exact addLtAddR _ h2

/-- The one-member entries' cross-added product, the paddings'
summands collecting on both members. -/
private theorem addShuffle (P U W1 V Q : Pos) :
    P + U + (W1 + V + (Q + V)) = P + W1 + (Q + V) + V + U := by
  rw [ground.add_right_comm P U (W1 + V + (Q + V)),
    ground.add_assoc W1 V (Q + V), ground.add_comm V (Q + V),
    ← ground.add_assoc P W1 (Q + V + V),
    ← ground.add_assoc (P + W1) (Q + V) V]

/-- Two one-member entries multiply at the composite: the scalar
product's own entry is one value with the entries' product, at
every three paddings. -/
theorem CPair.ofPair_mul (p q : Pair) (u v w : Pos) :
    (CPair.ofPair (p * q) u).oneValue
      (CPair.ofPair p v * CPair.ofPair q w) := by
  refine CPair.num_oneValue (p := ⟨p.num * q.num + u, u⟩)
    (p' := ⟨p.num + v, v⟩ * ⟨q.num + w, w⟩) ?_ (p.den * q.den)
  show p.num * q.num + u + ((p.num + v) * w + v * (q.num + w))
    = (p.num + v) * (q.num + w) + v * w + u
  rw [ground.right_distrib p.num v w, ground.left_distrib v q.num w,
    ground.right_distrib p.num v (q.num + w),
    ground.left_distrib p.num q.num w, ground.left_distrib v q.num w]
  exact addShuffle (p.num * q.num) u (p.num * w) (v * w) (v * q.num)

/-- Two product orders are equal by the ground identities, the
first datum's cross-added product and the shared datum each
associating. -/
theorem CPair.mul_assoc (x y z : CPair) : x * y * z = x * (y * z) := by
  show CPair.mk (x.num * y.num * z.num) (x.den * y.den * z.den)
    = CPair.mk (x.num * (y.num * z.num)) (x.den * (y.den * z.den))
  rw [BPair.mul_assoc x.num y.num z.num,
    ground.mul_assoc x.den y.den z.den]

/-- The composite product exchanges. -/
theorem CPair.mul_comm (x y : CPair) : x * y = y * x := by
  show CPair.mk (x.num * y.num) (x.den * y.den)
    = CPair.mk (y.num * x.num) (y.den * x.den)
  rw [BPair.mul_comm x.num y.num, ground.mul_comm x.den y.den]

/-- A shared left factor regroups across the composite product at
the one-value read. -/
theorem CPair.mul_left_congr {x y z : CPair} (h : x.oneValue (y * z))
    (w : CPair) : (x * w).oneValue (y * (z * w)) := by
  rw [← CPair.mul_assoc]
  exact CPair.mul_congr h (CPair.oneValue_refl w)

/-! The fold clause (`def:ground`): a finite family sums by the fold
over its index order, seeded at the sum's unit and adding the
members, total at every family, in every carrier with its displayed
sum's unit, and two fold orders are equal by the ground identities.
The family enters as an index list, a fold order is a member-count
datum (`countOf`), and the clause's reads are `famFold_relist` — the
fold's one value at matched member counts — with `famFold_map` and
the witness-map counts `countOf_map` beneath it, the reindexing read
`famFold_reindex` the graded folds' device, and the pointwise-unit
and one-key reads at a stated relation (`famFold_null_ov`,
`famFold_pick_ov`) the carriers' shared derivations. -/

/-- The fold over a finite family at a carrier's displayed sum and
unit, adding the members along the index order. -/
def famFold {α β : Type} (add : β → β → β) (unit : β) (f : α → β) :
    List α → β
  | [] => unit
  | a :: t => add (f a) (famFold add unit f t)

/-- A mapped family's balance fold reads the index fold. -/
theorem BPair.sum_map {α : Type} (f : α → BPair) :
    ∀ l : List α,
    (BPair.sum (l.map f)).oneValue
      (famFold BPair.add BPair.unit f l)
  | [] => BPair.oneValue_refl _
  | a :: t =>
    BPair.oneValue_trans (BPair.sum_cons (f a) (t.map f))
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.sum_map f t))

/-- A flattened family's balance fold reads the fold of the
per-member folds. -/
theorem BPair.sum_flatMap {α : Type} (g : α → List BPair) :
    ∀ l : List α,
      (BPair.sum (l.flatMap g)).oneValue
        (famFold BPair.add BPair.unit
          (fun a => BPair.sum (g a)) l)
  | [] => BPair.oneValue_refl _
  | a :: t => by
    show (BPair.sum (g a ++ t.flatMap g)).oneValue
      (BPair.sum (g a) + famFold BPair.add BPair.unit
        (fun b => BPair.sum (g b)) t)
    exact BPair.oneValue_trans (BPair.sum_append (g a) (t.flatMap g))
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.sum_flatMap g t))

/-! The predicate count: `def:ground`'s count clause — how often a
stated condition holds over a finite family — at the family fold's
carrier, with the accumulator bridge to the core list count, the
monotone comparison at a pointwise implication, and the equal
counts' reversal. -/

/-- The predicate count at a list, the family fold's own read: one
unit per member the predicate accepts. -/
def countBy {α : Type} (p : α → Bool) (l : List α) : Nat :=
  famFold Nat.add 0 (fun a => cond (p a) 1 0) l

/-- An accepted head carries one unit past the count. -/
theorem countBy_cons_true {α : Type} (p : α → Bool) {a : α}
    (t : List α) (h : p a = true) : countBy p (a :: t) = 1 + countBy p t := by
  show cond (p a) 1 0 + countBy p t = 1 + countBy p t
  rw [h]
  rfl

/-- A refused head leaves the count. -/
theorem countBy_cons_false {α : Type} (p : α → Bool) {a : α}
    (t : List α) (h : p a = false) : countBy p (a :: t) = countBy p t := by
  show cond (p a) 1 0 + countBy p t = countBy p t
  rw [h]
  exact Nat.zero_add _

/-- The accumulator's read: the fold from a stated seed is that seed
past the family fold. -/
theorem countP_go {α : Type} (p : α → Bool) : ∀ (l : List α) (n : Nat),
    List.countP.go p l n = n + countBy p l
  | [], _ => rfl
  | a :: t, n => by
    show (cond (p a) (List.countP.go p t (n + 1)) (List.countP.go p t n))
      = n + (cond (p a) 1 0 + countBy p t)
    cases hpa : p a with
    | true =>
      rw [countP_go p t (n + 1)]
      show n + 1 + countBy p t = n + (1 + countBy p t)
      rw [Nat.add_assoc]
    | false =>
      rw [countP_go p t n]
      show n + countBy p t = n + (0 + countBy p t)
      rw [Nat.zero_add]

/-- The list count is the family fold at the predicate's indicator. -/
theorem countP_read {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = countBy p l := by
  show List.countP.go p l 0 = countBy p l
  rw [countP_go p l 0]
  exact Nat.zero_add _

/-- A pointwise implication makes the counts monotone. -/
theorem countBy_mono {α : Type} (P Q : α → Bool)
    (himp : ∀ a, P a = true → Q a = true) : ∀ l : List α,
    countBy P l ≤ countBy Q l
  | [] => Nat.le_refl 0
  | a :: t => by
    have ht := countBy_mono P Q himp t
    cases hpa : P a with
    | true =>
      rw [countBy_cons_true P t hpa, countBy_cons_true Q t (himp a hpa)]
      exact Nat.add_le_add_left ht 1
    | false =>
      rw [countBy_cons_false P t hpa]
      cases hqa : Q a with
      | true =>
        rw [countBy_cons_true Q t hqa]
        exact Nat.le_trans ht (Nat.le_add_left (countBy Q t) 1)
      | false =>
        rw [countBy_cons_false Q t hqa]
        exact ht

/-- Equal counts at a pointwise implication reverse it member by
member: every member the wider predicate accepts is accepted by the
narrower one. -/
theorem countBy_eq_all {α : Type} (P Q : α → Bool)
    (himp : ∀ a, P a = true → Q a = true) : ∀ l : List α,
    countBy P l = countBy Q l → (l.all (fun a => P a || !(Q a))) = true
  | [], _ => rfl
  | a :: t, h => by
    show ((P a || !(Q a)) && t.all (fun b => P b || !(Q b))) = true
    cases hpa : P a with
    | true =>
      have hqa : Q a = true := himp a hpa
      show t.all (fun b => P b || !(Q b)) = true
      refine countBy_eq_all P Q himp t ?_
      refine ground.addCancelL 1 ?_
      rw [← countBy_cons_true P t hpa, ← countBy_cons_true Q t hqa]
      exact h
    | false =>
      cases hqa : Q a with
      | true =>
        have hle := countBy_mono P Q himp t
        rw [countBy_cons_false P t hpa, countBy_cons_true Q t hqa] at h
        rw [h, Nat.add_comm 1 (countBy Q t)] at hle
        exact absurd hle (Nat.lt_irrefl (countBy Q t))
      | false =>
        show t.all (fun b => P b || !(Q b)) = true
        refine countBy_eq_all P Q himp t ?_
        rw [← countBy_cons_false P t hpa, ← countBy_cons_false Q t hqa]
        exact h

/-- A member's count in an index list, one comparison per member. -/
def countOf {α : Type} [DecidableEq α] (a : α) (l : List α) : Nat :=
  countBy (fun b => decide (a = b)) l

/-- The head splits the count at its membership indicator: one unit
where the head is the stated member, none past the tail's count. -/
theorem countOf_cons {α : Type} [DecidableEq α] (a b : α)
    (t : List α) :
    countOf a (b :: t) = (if a = b then 1 else 0) + countOf a t := by
  show cond (decide (a = b)) 1 0 + countOf a t
    = (if a = b then 1 else 0) + countOf a t
  by_cases h : a = b
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

/-- The count of members beyond a stated value, one comparison per
member. -/
def countAbove (c : Nat) (l : List Nat) : Nat :=
  countBy (fun b => decide (c < b)) l

/-- The head splits the count at its order indicator: one unit where
the head lies beyond the stated value, none past the tail's count. -/
theorem countAbove_cons (c b : Nat) (t : List Nat) :
    countAbove c (b :: t)
      = (if c < b then 1 else 0) + countAbove c t := by
  show cond (decide (c < b)) 1 0 + countAbove c t
    = (if c < b then 1 else 0) + countAbove c t
  by_cases h : c < b
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

/-- The count of members below a stated value, one comparison per
member. -/
def countBelow (c : Nat) (l : List Nat) : Nat :=
  countBy (fun b => decide (b < c)) l

/-- The head splits the count at its order indicator: one unit where
the head lies below the stated value, none past the tail's count. -/
theorem countBelow_cons (c b : Nat) (t : List Nat) :
    countBelow c (b :: t)
      = (if b < c then 1 else 0) + countBelow c t := by
  show cond (decide (b < c)) 1 0 + countBelow c t
    = (if b < c then 1 else 0) + countBelow c t
  by_cases h : b < c
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

/-- An index list is distinct where every member's count is at most
one, the read bounded at the list's own members. -/
def distinctList {α : Type} [DecidableEq α] (l : List α) : Prop :=
  ∀ x ∈ l, countOf x l ≤ 1

instance instGround32 {α : Type} [DecidableEq α] (l : List α) :
    Decidable (distinctList l) :=
  inferInstanceAs (Decidable (∀ x ∈ l, countOf x l ≤ 1))

/-- The first occurrence withdrawn, the further members kept. -/
def eraseFirst {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: t => if a = b then t else b :: eraseFirst a t

/-- The boolean equality at a shared natural, the reflexive read. -/
theorem beqRefl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beqRefl n

/-- The boolean equality's true read is the equality, the hand-rolled
bridge at the natural carrier. -/
theorem beqEq : ∀ a b : Nat, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | _ + 1, _ + 1, h => congrArg Nat.succ (beqEq _ _ h)
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h

/-- A refused equality reads the boolean equality false, the
bridge's false side. -/
theorem beqFalse : ∀ {a b : Nat}, ¬ a = b → Nat.beq a b = false
  | 0, 0, h => absurd rfl h
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | a + 1, b + 1, h =>
    beqFalse (a := a) (b := b) (fun he => h (congrArg (· + 1) he))

/-- The boolean equality false names the members distinct. -/
theorem beqNe {a b : Nat} (h : Nat.beq a b = false) : ¬ a = b := by
  intro he
  rw [he, beqRefl b] at h
  exact Bool.noConfusion h

/-- The boolean strict read false refuses the order. -/
theorem bltFalse {a b : Nat} (h : Nat.blt a b = false) :
    ¬ a < b := fun hlt => Bool.noConfusion ((ltBlt hlt).symm.trans h)

/-- The Boolean equality read at a decidable carrier: a true read
is the equality, and back. -/
theorem beqEqOf {α : Type} [DecidableEq α] {a b : α}
    (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

/-- A refused equality reads the comparison false, at any decided
carrier. -/
theorem neBeqOf {α : Type} [DecidableEq α] {a b : α}
    (h : ¬ a = b) : (a == b) = false := by
  cases hb : a == b with
  | true => exact absurd (beqEqOf hb) h
  | false => rfl

theorem eqBeqOf {α : Type} [DecidableEq α] {a b : α}
    (h : a = b) : (a == b) = true :=
  decide_eq_true h

/-- A false Boolean is not the true read, the refusal's own
bridge. -/
theorem boolNe {c : Bool} (h : c = false) : ¬ (c = true) :=
  fun hh => Bool.noConfusion (h.symm.trans hh)

/-- The Boolean equality read is symmetric at a decidable
carrier. -/
theorem beqSymm {α : Type} [DecidableEq α] (a b : α) :
    (a == b) = (b == a) := by
  cases h : a == b with
  | true => rw [eqBeqOf (beqEqOf h).symm]
  | false =>
    cases h2 : b == a with
    | true =>
      rw [eqBeqOf (beqEqOf h2).symm] at h
      exact Bool.noConfusion h
    | false => rfl

/-- The Boolean carrier's comparison reads the equality. -/
theorem boolBeqEq : ∀ {a b : Bool}, (a == b) = true → a = b
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, h => Bool.noConfusion h
  | false, true, h => Bool.noConfusion h

/-- The Boolean carrier's comparison at one value reads true. -/
theorem boolEqBeq : ∀ a : Bool, ((a == a) : Bool) = true
  | true => rfl
  | false => rfl

/-- The list comparison reads the equality at any element
comparison that does: the cons splits at the head's read. -/
theorem listBeqRead {α : Type} [BEq α]
    (helem : ∀ a b : α, (a == b) = true → a = b) :
    ∀ {u w : List α}, (u == w) = true → u = w
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: u, b :: w, h => by
    have hsplit : (a == b) = true ∧ ((u == w) : Bool) = true := by
      cases hab : (a == b) with
      | false =>
        rw [show ((a :: u : List α) == b :: w)
            = ((a == b) && (u == w)) from rfl, hab] at h
        exact Bool.noConfusion h
      | true =>
        rw [show ((a :: u : List α) == b :: w)
            = ((a == b) && (u == w)) from rfl, hab] at h
        exact ⟨rfl, h⟩
    rw [helem a b hsplit.1, listBeqRead helem hsplit.2]

/-- The list comparison at one family reads true wherever the
element comparison at one member does. -/
theorem listBeqIntro {α : Type} [BEq α]
    (helem : ∀ a : α, ((a == a) : Bool) = true) :
    ∀ u : List α, ((u == u) : Bool) = true
  | [] => rfl
  | a :: u => by
    rw [show ((a :: u : List α) == a :: u)
        = ((a == a) && (u == u)) from rfl, helem a,
      listBeqIntro helem u]
    rfl

/-- A refused list equality reads the comparison false at any
element comparison reading the equality. -/
theorem listBeqRefuse {α : Type} [BEq α]
    (helem : ∀ a b : α, (a == b) = true → a = b)
    {u w : List α} (h : ¬ u = w) : (u == w) = false := by
  cases hb : ((u == w) : Bool) with
  | true => exact absurd (listBeqRead helem hb) h
  | false => rfl

/-- The pair comparison reads the equality at its two components'
comparisons. -/
theorem prodBeqRead {α β : Type} [BEq α] [BEq β]
    (hA : ∀ a b : α, (a == b) = true → a = b)
    (hB : ∀ a b : β, (a == b) = true → a = b) :
    ∀ {x y : α × β}, (x == y) = true → x = y
  | (a, b), (c, d), h => by
    have hsplit : (a == c) = true ∧ ((b == d) : Bool) = true := by
      cases hac : (a == c) with
      | false =>
        rw [show (((a, b) : α × β) == (c, d))
            = ((a == c) && (b == d)) from rfl, hac] at h
        exact Bool.noConfusion h
      | true =>
        rw [show (((a, b) : α × β) == (c, d))
            = ((a == c) && (b == d)) from rfl, hac] at h
        exact ⟨rfl, h⟩
    rw [hA a c hsplit.1, hB b d hsplit.2]

/-- The pair comparison at one pair reads true at its components'
own reads. -/
theorem prodBeqIntro {α β : Type} [BEq α] [BEq β]
    (hA : ∀ a : α, ((a == a) : Bool) = true)
    (hB : ∀ b : β, ((b == b) : Bool) = true) :
    ∀ x : α × β, ((x == x) : Bool) = true
  | (a, b) => by
    rw [show (((a, b) : α × β) == (a, b))
        = ((a == a) && (b == b)) from rfl, hA a, hB b]
    rfl

/-- A refused pair equality reads the comparison false. -/
theorem prodBeqRefuse {α β : Type} [BEq α] [BEq β]
    (hA : ∀ a b : α, (a == b) = true → a = b)
    (hB : ∀ a b : β, (a == b) = true → a = b)
    {x y : α × β} (h : ¬ x = y) : (x == y) = false := by
  cases hb : ((x == y) : Bool) with
  | true => exact absurd (prodBeqRead hA hB hb) h
  | false => rfl

/-- The list carrier's Boolean equality reads componentwise, the
true read the equality. -/
theorem listBeqEq {α : Type} [DecidableEq α] :
    ∀ {u w : List α}, (u == w) = true → u = w :=
  listBeqRead (fun _ _ h => beqEqOf h)

theorem listEqBeq {α : Type} [DecidableEq α] :
    ∀ u : List α, ((u == u) : Bool) = true :=
  listBeqIntro (fun _ => eqBeqOf rfl)

/-- Two lists' equality test at a stated member equality is the
equality's own decision. -/
theorem listBeq_decide {α : Type} [DecidableEq α] (u w : List α) :
    (u == w) = decide (u = w) := by
  cases hb : (u == w) with
  | true => rw [decide_eq_true (listBeqEq hb)]
  | false =>
    cases hd : decide (u = w) with
    | true => rw [of_decide_eq_true hd, listEqBeq w] at hb; exact Bool.noConfusion hb
    | false => rfl

/-- The list carrier's Boolean equality read is symmetric. -/
theorem listBeqSymm {α : Type} [DecidableEq α] (u w : List α) :
    (u == w) = (w == u) := by
  cases h : (u == w) with
  | true =>
    rw [listBeqEq h]
    exact (listEqBeq w).symm
  | false =>
    cases h2 : (w == u) with
    | true =>
      rw [listBeqEq h2, listEqBeq u] at h
      exact Bool.noConfusion h
    | false => rfl

/-- The filter's one-step read, the definition's own match. -/
theorem filter_cons {α : Type} (p : α → Bool) (a : α) (l : List α) :
    (a :: l).filter p
      = match p a with
        | true => a :: l.filter p
        | false => l.filter p := rfl


/-- Predicates agreeing at every member filter alike. -/
theorem filter_congr {α : Type} (p q : α → Bool) (h : ∀ a, p a = q a) :
    ∀ l : List α, l.filter p = l.filter q
  | [] => rfl
  | a :: t => by
    rw [filter_cons p a t, filter_cons q a t, h a, filter_congr p q h t]

/-- Two filters in succession read the conjoined predicate, the
outer one applied at the inner's survivors. -/
theorem filter_filter {α : Type} (p q : α → Bool) :
    ∀ l : List α, (l.filter q).filter p = l.filter (fun a => q a && p a)
  | [] => rfl
  | a :: t => by
    show (match q a with
          | true => a :: t.filter q
          | false => t.filter q).filter p
       = (match q a && p a with
          | true => a :: t.filter (fun b => q b && p b)
          | false => t.filter (fun b => q b && p b))
    cases hq : q a with
    | false => exact filter_filter p q t
    | true =>
      show (match p a with
            | true => a :: (t.filter q).filter p
            | false => (t.filter q).filter p)
         = (match p a with
            | true => a :: t.filter (fun b => q b && p b)
            | false => t.filter (fun b => q b && p b))
      cases hp : p a with
      | false => exact filter_filter p q t
      | true => exact congrArg (List.cons a) (filter_filter p q t)

/-- The joined family's entries read at one key: the stated
projection's own join of the two families, entry by entry. -/
theorem map_getAt_zipWith {α β γ : Type} (d : γ) (f : α → β → List γ)
    (k : Nat) (π : α → β → γ) (hf : ∀ a b, getAt d (f a b) k = π a b) :
    ∀ (ra : List α) (rb : List β),
    (List.zipWith f ra rb).map (fun p => getAt d p k) = List.zipWith π ra rb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: ra, b :: rb => by
    show getAt d (f a b) k :: (List.zipWith f ra rb).map (fun p => getAt d p k)
      = π a b :: List.zipWith π ra rb
    rw [hf a b, map_getAt_zipWith d f k π hf ra rb]

/-- The two-level joined family's entries read at one key, row by
row: the projection's own two-level join. -/
theorem map2_getAt_zipWith {α β γ : Type} (d : γ) (f : α → β → List γ)
    (k : Nat) (π : α → β → γ) (hf : ∀ a b, getAt d (f a b) k = π a b) :
    ∀ (A : List (List α)) (S : List (List β)),
    (List.zipWith (List.zipWith f) A S).map
      (fun r => r.map (fun p => getAt d p k))
      = List.zipWith (List.zipWith π) A S
  | [], _ => rfl
  | _ :: _, [] => rfl
  | ra :: A, rb :: S => by
    show (List.zipWith f ra rb).map (fun p => getAt d p k)
      :: (List.zipWith (List.zipWith f) A S).map
        (fun r => r.map (fun p => getAt d p k))
      = List.zipWith π ra rb :: List.zipWith (List.zipWith π) A S
    rw [map_getAt_zipWith d f k π hf ra rb, map2_getAt_zipWith d f k π hf A S]

/-- The join reading its first family through a map, at a first
family at or below its partner's count. -/
theorem zipWith_leftMap {α β γ : Type} (g : α → γ) :
    ∀ (u : List α) (v : List β), u.length ≤ v.length →
    List.zipWith (fun a _ => g a) u v = u.map g
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | a :: u, _ :: v, h => by
    show g a :: List.zipWith (fun a _ => g a) u v = g a :: u.map g
    rw [zipWith_leftMap g u v (Nat.le_of_succ_le_succ h)]

/-- The join reading its second family through a map, at a second
family at or below its partner's count. -/
theorem zipWith_rightMap {α β γ : Type} (g : β → γ) :
    ∀ (u : List α) (v : List β), v.length ≤ u.length →
    List.zipWith (fun _ b => g b) u v = v.map g
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: u, b :: v, h => by
    show g b :: List.zipWith (fun _ b => g b) u v = g b :: v.map g
    rw [zipWith_rightMap g u v (Nat.le_of_succ_le_succ h)]

/-- The two-level join reading its first family through a map, at
rows and widths at or below the partners'. -/
theorem zipWith2_leftMap {α β γ : Type} (g : α → γ) :
    ∀ (A : List (List α)) (S : List (List β)), A.length ≤ S.length →
    (∀ i, i < A.length →
      (getAt ([] : List α) A i).length ≤ (getAt ([] : List β) S i).length) →
    List.zipWith (List.zipWith (fun a _ => g a)) A S = A.map (fun r => r.map g)
  | [], _, _, _ => rfl
  | _ :: _, [], h, _ => absurd h (Nat.not_succ_le_zero _)
  | ra :: A, rb :: S, h, hr => by
    show List.zipWith (fun a _ => g a) ra rb
      :: List.zipWith (List.zipWith (fun a _ => g a)) A S
      = ra.map g :: A.map (fun r => r.map g)
    rw [zipWith_leftMap g ra rb (hr 0 (Nat.succ_pos _)),
      zipWith2_leftMap g A S (Nat.le_of_succ_le_succ h)
        (fun i hi => hr (i + 1) (Nat.succ_lt_succ hi))]

/-- The two-level join reading its second family through a map, at
rows and widths at or below the partners'. -/
theorem zipWith2_rightMap {α β γ : Type} (g : β → γ) :
    ∀ (A : List (List α)) (S : List (List β)), S.length ≤ A.length →
    (∀ i, i < S.length →
      (getAt ([] : List β) S i).length ≤ (getAt ([] : List α) A i).length) →
    List.zipWith (List.zipWith (fun _ b => g b)) A S = S.map (fun r => r.map g)
  | [], [], _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | ra :: A, rb :: S, h, hr => by
    show List.zipWith (fun _ b => g b) ra rb
      :: List.zipWith (List.zipWith (fun _ b => g b)) A S
      = rb.map g :: S.map (fun r => r.map g)
    rw [zipWith_rightMap g ra rb (hr 0 (Nat.succ_pos _)),
      zipWith2_rightMap g A S (Nat.le_of_succ_le_succ h)
        (fun i hi => hr (i + 1) (Nat.succ_lt_succ hi))]

/-- The componentwise join's length at matched widths. -/
theorem length_zipWith {α γ β : Type} (f : α → γ → β) :
    ∀ (u : List α) (v : List γ) (n : Nat),
    u.length = n → v.length = n →
    (List.zipWith f u v).length = n
  | [], [], _, hu, _ => hu
  | [], _ :: vt, _, hu, hv =>
    nomatch (show Nat.succ vt.length = 0 from hv.trans hu.symm)
  | _ :: ut, [], _, hu, hv =>
    nomatch (show Nat.succ ut.length = 0 from hu.trans hv.symm)
  | _ :: u, _ :: v, n, hu, hv => by
    match n, hu with
    | m + 1, hu =>
      show (List.zipWith f u v).length + 1 = m + 1
      rw [length_zipWith f u v m (Nat.succ.inj hu)
        (Nat.succ.inj hv)]

/-- The componentwise walk over a vacant second family is vacant at
every first family, the walk's own recursion read at its shorter
side. -/
theorem zipWith_nil_right {α β γ : Type} (f : α → β → γ) :
    ∀ l : List α, List.zipWith f l ([] : List β) = []
  | [] => rfl
  | _ :: _ => rfl

/-- The componentwise walk splits at a matched seam: at a first
pair of equal counts the joined lists' walk is the two walks
joined. -/
theorem zipWith_append {α β γ : Type} (f : α → β → γ) :
    ∀ (u1 u2 : List α) (v1 v2 : List β), u1.length = v1.length →
      List.zipWith f (u1 ++ u2) (v1 ++ v2)
        = List.zipWith f u1 v1 ++ List.zipWith f u2 v2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => nomatch h
  | _ :: _, _, [], _, h => nomatch h
  | a :: u1, u2, b :: v1, v2, h => by
    show f a b :: List.zipWith f (u1 ++ u2) (v1 ++ v2)
      = f a b :: (List.zipWith f u1 v1 ++ List.zipWith f u2 v2)
    rw [zipWith_append f u1 u2 v1 v2 (Nat.succ.inj h)]

/-- The componentwise list's entry read: the entry function at the
two lists' own entries. -/
theorem getAt_zipWith {α β γ : Type} (da : α) (db : β) (dc : γ)
    (f : α → β → γ) :
    ∀ (u : List α) (v : List β) (i : Nat), i < u.length → i < v.length →
      getAt dc (List.zipWith f u v) i
        = f (getAt da u i) (getAt db v i)
  | [], _, i, h, _ => absurd h (Nat.not_lt_zero i)
  | _ :: _, [], i, _, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: u, _ :: v, i + 1, h, h' =>
    getAt_zipWith da db dc f u v i (Nat.lt_of_succ_lt_succ h)
      (Nat.lt_of_succ_lt_succ h')

/-- The zip's length stays at or below its first family's. -/
theorem length_zipWith_le {α β γ : Type} (f : α → β → γ) :
    ∀ (u : List α) (v : List β),
      (List.zipWith f u v).length ≤ u.length
  | [], _ => Nat.le_refl 0
  | _ :: _, [] => Nat.zero_le _
  | _ :: s2, _ :: t => Nat.succ_le_succ (length_zipWith_le f s2 t)

/-- The componentwise walk's width at matched family widths on both
sides, the truncation reading the two orders alone. -/
theorem length_zipWith_congr {α β γ : Type} (f : α → β → γ) :
    ∀ (u u' : List α) (w w' : List β),
      u.length = u'.length → w.length = w'.length →
      (List.zipWith f u w).length = (List.zipWith f u' w').length
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h
  | _ :: _, _ :: _, [], [], _, _ => rfl
  | _ :: _, _ :: _, [], _ :: _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, h => nomatch h
  | _ :: u, _ :: u', _ :: w, _ :: w', hu, hw =>
    congrArg Nat.succ
      (length_zipWith_congr f u u' w w' (Nat.succ.inj hu)
        (Nat.succ.inj hw))

/-- Two maps over one family zipped are the family's own map at the
zipped pair. -/
theorem zipWith_map_map {α β γ δ : Type} (h : β → γ → δ)
    (f : α → β) (g : α → γ) : ∀ l : List α,
      List.zipWith h (l.map f) (l.map g) = l.map (fun x => h (f x) (g x))
  | [] => rfl
  | x :: t => by
    show h (f x) (g x) :: List.zipWith h (t.map f) (t.map g)
      = h (f x) (g x) :: t.map (fun x => h (f x) (g x))
    rw [zipWith_map_map h f g t]

/-- An addend's map on the first list passes through the
componentwise join, the raise carried outside the zip. -/
theorem zipWith_add_mapL (c : Nat) : ∀ l r : List Nat,
    List.zipWith (fun x y => x + y) (l.map (fun x => c + x)) r
      = (List.zipWith (fun x y => x + y) l r).map (fun x => c + x)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: r => by
    show (c + x + y) :: List.zipWith (fun x y => x + y)
        (l.map (fun x => c + x)) r
      = (c + (x + y)) :: (List.zipWith (fun x y => x + y) l r).map
        (fun x => c + x)
    rw [zipWith_add_mapL c l r, Nat.add_assoc c x y]

/-- An addend's map on the second list passes through the
componentwise join, the raise carried outside the zip. -/
theorem zipWith_add_mapR (c : Nat) : ∀ l r : List Nat,
    List.zipWith (fun x y => x + y) l (r.map (fun x => c + x))
      = (List.zipWith (fun x y => x + y) l r).map (fun x => c + x)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: r => by
    show (x + (c + y)) :: List.zipWith (fun x y => x + y) l
        (r.map (fun x => c + x))
      = (c + (x + y)) :: (List.zipWith (fun x y => x + y) l r).map
        (fun x => c + x)
    rw [zipWith_add_mapR c l r, Nat.add_left_comm x c y]

/-- The sum's zip exchanges its arguments. -/
theorem zipWith_add_comm : ∀ (x y : List Nat),
    List.zipWith (fun u w => u + w) x y = List.zipWith (fun u w => u + w) y x
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by
    show (a + b) :: List.zipWith (fun u w => u + w) s t
      = (b + a) :: List.zipWith (fun u w => u + w) t s
    rw [Nat.add_comm a b, zipWith_add_comm s t]

/-- The filter keeps a passing head. -/
theorem filter_cons_true {α : Type} {p : α → Bool} {a : α}
    {l : List α} (h : p a = true) :
    (a :: l).filter p = a :: l.filter p := by
  rw [filter_cons p a l, h]

/-- The filter drops a refused head. -/
theorem filter_cons_false {α : Type} {p : α → Bool} {a : α}
    {l : List α} (h : p a = false) :
    (a :: l).filter p = l.filter p := by
  rw [filter_cons p a l, h]

/-- A filter's length sits at or below the family's. -/
theorem length_filter_le {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: t => by
    cases hp : p a with
    | true =>
      rw [filter_cons_true hp]
      exact Nat.succ_le_succ (length_filter_le p t)
    | false =>
      rw [filter_cons_false hp]
      exact Nat.le_succ_of_le (length_filter_le p t)

/-- A filter and its complement's filter split the family's
length. -/
theorem length_filter_split {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun x => !(p x))).length
      = l.length
  | [] => rfl
  | a :: t => by
    cases hp : p a with
    | true =>
      rw [filter_cons_true hp,
        @filter_cons_false α (fun x => !(p x)) a t (by rw [hp]; rfl)]
      show (t.filter p).length + 1 + (t.filter (fun x => !(p x))).length
        = t.length + 1
      rw [Nat.add_right_comm, length_filter_split p t]
    | false =>
      rw [filter_cons_false hp,
        @filter_cons_true α (fun x => !(p x)) a t (by rw [hp]; rfl)]
      show (t.filter p).length + ((t.filter (fun x => !(p x))).length + 1)
        = t.length + 1
      rw [← Nat.add_assoc, length_filter_split p t]

/-- The three filters at a predicate pair partition the family's
count: the first read, the joint refusal, and the second read off
the first. -/
theorem length_filter_three {α : Type} (T Q : α → Bool) (l : List α) :
    (l.filter T).length
      + ((l.filter (fun z => !(T z || Q z))).length
        + (l.filter (fun z => !(T z) && Q z)).length) = l.length := by
  have h1 := length_filter_split T l
  have h2 := length_filter_split Q (l.filter (fun z => !(T z)))
  rw [filter_filter Q (fun z => !(T z)) l,
    filter_filter (fun z => !(Q z)) (fun z => !(T z)) l,
    filter_congr (fun a => !(T a) && !(Q a)) (fun z => !(T z || Q z))
      (fun a => by cases T a <;> cases Q a <;> rfl) l] at h2
  rw [← h1, ← h2, Nat.add_comm ((l.filter (fun z => !(T z || Q z))).length)]

/-- A filter map at a guarded image is the filter's map. -/
theorem filterMap_ite {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α,
      l.filterMap (fun x => if p x then some (f x) else none)
        = (l.filter p).map f
  | [] => rfl
  | a :: t => by
    rw [List.filterMap_cons]
    cases hp : p a with
    | true =>
      rw [if_pos rfl, filter_cons_true hp]
      show f a :: t.filterMap (fun x => if p x then some (f x) else none)
        = f a :: (t.filter p).map f
      rw [filterMap_ite p f t]
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
        filter_cons_false hp]
      exact filterMap_ite p f t

/-- The filter keeps a family every member passes. -/
theorem filter_all {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | a :: t, h => by
    rw [filter_cons_true (h a (List.Mem.head t)),
      filter_all p t (fun x hx => h x (List.Mem.tail a hx))]

/-- The leading segment's count never exceeds a member's. -/
theorem countOf_take : ∀ (x k : Nat) (l : List Nat),
    countOf x (l.take k) <= countOf x l
  | _, 0, [] => Nat.le_refl 0
  | x, 0, _ :: _ => Nat.zero_le _
  | _, _ + 1, [] => Nat.le_refl 0
  | x, k + 1, b :: t => by
    show countOf x (b :: t.take k) <= countOf x (b :: t)
    rw [countOf_cons, countOf_cons]
    exact Nat.add_le_add_left (countOf_take x k t) _

/-- The filter splits over the join. -/
theorem filter_append {α : Type} (p : α → Bool) :
    ∀ u w : List α, (u ++ w).filter p = u.filter p ++ w.filter p
  | [], _ => rfl
  | a :: u, w => by
    show ((a :: (u ++ w)).filter p) = (a :: u).filter p ++ w.filter p
    rw [filter_cons p a (u ++ w), filter_cons p a u]
    cases hp : p a with
    | true =>
      show a :: (u ++ w).filter p = (a :: u.filter p) ++ w.filter p
      rw [filter_append p u w]
      rfl
    | false =>
      show (u ++ w).filter p = u.filter p ++ w.filter p
      exact filter_append p u w

theorem countOf_head {α : Type} [DecidableEq α] (a : α) (t : List α) :
    countOf a (a :: t) = countOf a t + 1 := by
  rw [countOf_cons, if_pos rfl, Nat.add_comm]

theorem countOf_head_ne {α : Type} [DecidableEq α] {a b : α}
    (hab : a ≠ b) (t : List α) : countOf a (b :: t) = countOf a t := by
  rw [countOf_cons, if_neg hab, Nat.zero_add]

/-- An occupied count is kept by a cons: the head's own term only
adds to the tail's count. -/
theorem countOf_cons_pos {α : Type} [DecidableEq α]
    {x a : α} {t : List α} (h : 0 < countOf x t) :
    0 < countOf x (a :: t) := by
  rw [countOf_cons]
  exact Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)

/-- The filter after a map reads the image predicate at the
sources. -/
theorem filter_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α,
      (l.map f).filter p = (l.filter (fun a => p (f a))).map f
  | [] => rfl
  | a :: t => by
    show (match p (f a) with
          | true => f a :: (t.map f).filter p
          | false => (t.map f).filter p)
       = ((match p (f a) with
           | true => a :: t.filter (fun b => p (f b))
           | false => t.filter (fun b => p (f b))).map f)
    cases hp : p (f a) with
    | false => exact filter_map f p t
    | true => exact congrArg (List.cons (f a)) (filter_map f p t)

/-- Two filters at one guard read per occupied member are one
list. -/
theorem filter_congr_mem {α : Type} [DecidableEq α]
    (P Q : α → Bool) : ∀ l : List α,
    (∀ x, 0 < countOf x l → P x = Q x) →
    l.filter P = l.filter Q
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (by rw [countOf_head]; exact Nat.succ_pos _)
    have htail := filter_congr_mem P Q l
      (fun x hx => h x (countOf_cons_pos hx))
    cases hqa : Q a with
    | true =>
      rw [filter_cons_true (ha.trans hqa),
        filter_cons_true hqa, htail]
    | false =>
      rw [filter_cons_false (ha.trans hqa),
        filter_cons_false hqa, htail]

/-- The filter's count: the key's own at a passing guard, the
count's unit at a refused one. -/
theorem countOf_filter {α : Type} [DecidableEq α]
    (P : α → Bool) (x : α) : ∀ l : List α,
    countOf x (l.filter P)
      = if P x then countOf x l else 0
  | [] => by
    cases hp : P x with
    | true => rw [if_pos rfl]; rfl
    | false => rw [if_neg (boolNe rfl)]; rfl
  | a :: l => by
    cases hpa : P a with
    | true =>
      rw [filter_cons_true hpa]
      by_cases hxa : x = a
      · rw [hxa, countOf_head, countOf_filter P a l,
          countOf_head, hpa, if_pos rfl, if_pos rfl]
      · rw [countOf_head_ne hxa, countOf_filter P x l,
          countOf_head_ne hxa]
    | false =>
      rw [filter_cons_false hpa, countOf_filter P x l]
      by_cases hxa : x = a
      · rw [hxa, hpa, if_neg (boolNe rfl),
          if_neg (boolNe rfl)]
      · rw [countOf_head_ne hxa]

/-- An occupied product's two factors are occupied. -/
theorem mulPosSplit {a b : Nat} (h : 0 < a * b) :
    0 < a ∧ 0 < b :=
  match a, b, h with
  | 0, _, h => by
    rw [Nat.zero_mul] at h
    exact absurd h (Nat.lt_irrefl 0)
  | _ + 1, 0, h => by
    rw [Nat.mul_zero] at h
    exact absurd h (Nat.lt_irrefl 0)
  | _ + 1, _ + 1, _ => ⟨Nat.succ_pos _, Nat.succ_pos _⟩

/-- An occupied sum names an occupied summand. -/
theorem posOr : ∀ {a b : Nat}, 0 < a + b → 0 < a ∨ 0 < b
  | 0, _, h => Or.inr (by rw [Nat.zero_add] at h; exact h)
  | _ + 1, _, _ => Or.inl (Nat.succ_pos _)

/-- An occupied fold names an occupied member at a positive
value. -/
theorem famFold_pos_mem {α : Type} (f : α → Nat) : ∀ l : List α,
    0 < famFold Nat.add 0 f l → ∃ x, x ∈ l ∧ 0 < f x
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: l, h => by
    cases hfa : f a with
    | succ m =>
      exact ⟨a, List.Mem.head l, by rw [hfa]; exact Nat.succ_pos m⟩
    | zero =>
      have hh : 0 < f a + famFold Nat.add 0 f l := h
      rw [hfa, Nat.zero_add] at hh
      match famFold_pos_mem f l hh with
      | ⟨x, hx, hfx⟩ => exact ⟨x, List.Mem.tail a hx, hfx⟩

/-- An occupied fold names an occupied count, the membership's
counted read. -/
theorem famFold_pos_witness {α : Type} [DecidableEq α]
    (f : α → Nat) : ∀ l : List α,
    0 < famFold Nat.add 0 f l →
    ∃ x, 0 < countOf x l ∧ 0 < f x
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: l, h => by
    cases hfa : f a with
    | succ m =>
      exact ⟨a, by rw [countOf_head]; exact Nat.succ_pos _,
        by rw [hfa]; exact Nat.succ_pos m⟩
    | zero =>
      have hh : 0 < f a + famFold Nat.add 0 f l := h
      rw [hfa, Nat.zero_add] at hh
      obtain ⟨x, hx, hfx⟩ := famFold_pos_witness f l hh
      exact ⟨x, countOf_cons_pos hx, hfx⟩

/-- A keyed filter's survivors all read a stated fold where every
source member's image does, the membership walked one head at a
time. -/
theorem all_filterMap_mem {α β : Type} (f : α → Option β)
    (P : β → Bool) :
    ∀ l : List α,
      (∀ x, x ∈ l → ∀ y, f x = some y → P y = true) →
      (l.filterMap f).all P = true
  | [], _ => rfl
  | x :: t, h => by
    have ht := all_filterMap_mem f P t
      (fun z hz y hy => h z (List.Mem.tail x hz) y hy)
    match hf : f x with
    | none =>
      show (match f x with
        | none => t.filterMap f
        | some d => d :: t.filterMap f).all P = true
      rw [hf]
      exact ht
    | some y =>
      show (match f x with
        | none => t.filterMap f
        | some d => d :: t.filterMap f).all P = true
      rw [hf]
      show (P y && (t.filterMap f).all P) = true
      rw [h x (List.Mem.head t) y hf, ht]
      rfl

/-- A member's count is occupied, `mem_of_countOf_pos`'s
converse. -/
theorem countOf_pos_of_mem {α : Type} [DecidableEq α]
    {x : α} : ∀ {l : List α}, x ∈ l → 0 < countOf x l
  | b :: t, h => by
    cases h with
    | head =>
      rw [countOf_head]
      exact Nat.succ_pos _
    | tail _ hm =>
      by_cases hxb : x = b
      · rw [hxb, countOf_head]
        exact Nat.succ_pos _
      · rw [countOf_head_ne hxb]
        exact countOf_pos_of_mem hm

/-- An occupied count in a one-member family names the member. -/
theorem countOf_single {α : Type} [DecidableEq α] {x a : α}
    (h : 0 < countOf x [a]) : x = a := by
  by_cases he : x = a
  · exact he
  · rw [countOf_head_ne he] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- A counted letter is a member: the count's positivity exhibits
the occurrence. -/
theorem mem_of_countOf_pos {α : Type} [DecidableEq α] (x : α) :
    ∀ l : List α, 0 < countOf x l → x ∈ l
  | [], h => absurd h (Nat.lt_irrefl 0)
  | b :: t, h => by
    by_cases hxb : x = b
    · rw [hxb]
      exact List.Mem.head t
    · rw [countOf_head_ne hxb] at h
      exact List.Mem.tail b (mem_of_countOf_pos x t h)

/-- A member of a one-member list is that member. -/
theorem eq_of_mem_single {α : Type} {x y : α} (h : x ∈ [y]) : x = y := by
  cases h with
  | head => rfl
  | tail _ h2 => exact nomatch h2

/-- A key off the family counts at the sum's unit. -/
theorem countOf_zero_of_not_mem {α : Type} [DecidableEq α] {x : α}
    {l : List α} (h : ¬ x ∈ l) : countOf x l = 0 := by
  cases hc : countOf x l with
  | zero => rfl
  | succ n =>
    exact absurd (mem_of_countOf_pos x l (by rw [hc]; exact Nat.succ_pos n)) h

/-- Equality of counts on both families' members determines
every count, since a key outside both families has vacant counts. -/
theorem countOf_eq_of_members {α : Type} [DecidableEq α] (A B : List α)
    (hA : ∀ x ∈ A, countOf x A = countOf x B)
    (hB : ∀ x ∈ B, countOf x A = countOf x B) (x : α) : countOf x A = countOf x B := by
  cases Nat.eq_zero_or_pos (countOf x A) with
  | inr hp => exact hA x (mem_of_countOf_pos x A hp)
  | inl hz =>
    cases Nat.eq_zero_or_pos (countOf x B) with
    | inr hp => exact hB x (mem_of_countOf_pos x B hp)
    | inl hz' => rw [hz, hz']

/-- A count-preserving involution reads every point: a map whose
square is the identity wherever its image is occupied, and whose
counts agree at the family's own members, carries the count at
every letter — off the family a positive image count would carry
the member's read back through the square, so both counts sit at
the sum's unit. -/
theorem countOf_invol {α : Type} [DecidableEq α] (f : α → α) (L : List α)
    (hinv : ∀ a, 0 < countOf (f a) L → f (f a) = a)
    (hmem : ∀ a ∈ L, countOf (f a) L = countOf a L) :
    ∀ x, countOf (f x) L = countOf x L := by
  intro x
  match Nat.eq_zero_or_pos (countOf x L) with
  | .inr hpos => exact hmem x (mem_of_countOf_pos x L hpos)
  | .inl hzero =>
    rw [hzero]
    match Nat.eq_zero_or_pos (countOf (f x) L) with
    | .inl hz => exact hz
    | .inr hp =>
      have h2 := hmem (f x) (mem_of_countOf_pos (f x) L hp)
      rw [hinv x hp, hzero] at h2
      exact absurd hp (by rw [← h2]; exact Nat.lt_irrefl 0)

/-- The distinct read at every letter: off the family the count is
zero, inside it the bounded read's own. -/
theorem distinctList_all {α : Type} [DecidableEq α] {l : List α}
    (h : distinctList l) (x : α) : countOf x l ≤ 1 :=
  match Nat.eq_zero_or_pos (countOf x l) with
  | .inl hz => by rw [hz]; exact Nat.zero_le 1
  | .inr hp => h x (mem_of_countOf_pos x l hp)

/-- A family at every member count zero is the seed family. -/
theorem eq_nil_of_countOf {α : Type} [DecidableEq α] :
    ∀ l : List α, (∀ x, countOf x l = 0) → l = []
  | [], _ => rfl
  | b :: t, h => by
    have hb := h b
    rw [countOf_head] at hb
    exact Nat.noConfusion hb

/-- A family whose counts read one value's indicator is that
value's own one-member family. -/
theorem single_of_counts {α : Type} [DecidableEq α] (x : α) :
    ∀ l : List α,
      (∀ y, countOf y l = if y = x then 1 else 0) → l = [x]
  | [], h => by
    have h0 : countOf x ([] : List α) = 1 := by
      rw [h x, if_pos rfl]
    exact Nat.noConfusion h0
  | b :: t, h => by
    have hb : countOf b t + 1 = if b = x then 1 else 0 := by
      rw [← countOf_head b t]
      exact h b
    have hbx : b = x := by
      by_cases hc : b = x
      · exact hc
      · rw [if_neg hc] at hb
        exact Nat.noConfusion hb
    have hb' : countOf x t + 1 = 1 := by
      rw [← hbx, hb, hbx, if_pos rfl]
    have hzero : ∀ y, countOf y t = 0 := by
      intro y
      by_cases hy : y = x
      · rw [hy]
        exact addCancelR 1 (hb'.trans (Nat.zero_add 1).symm)
      · have hy2 := h y
        rw [hbx, countOf_head_ne hy, if_neg hy] at hy2
        exact hy2
    rw [hbx, eq_nil_of_countOf t hzero]

/-- The withdrawn member's count sits one below, at an occupied
count. -/
theorem countOf_eraseFirst_self {α : Type} [DecidableEq α] :
    ∀ (l : List α) (a : α), 0 < countOf a l →
      countOf a l = countOf a (eraseFirst a l) + 1
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | b :: t, a, h => by
    by_cases hab : a = b
    · show countOf a (b :: t)
        = countOf a (if a = b then t else b :: eraseFirst a t) + 1
      rw [if_pos hab, hab, countOf_head]
    · have h' : 0 < countOf a t := by
        rw [countOf_head_ne hab] at h; exact h
      show countOf a (b :: t)
        = countOf a (if a = b then t else b :: eraseFirst a t) + 1
      rw [if_neg hab, countOf_head_ne hab, countOf_head_ne hab,
        countOf_eraseFirst_self t a h']

/-- A further member's count reads through the withdrawal. -/
theorem countOf_eraseFirst_ne {α : Type} [DecidableEq α] :
    ∀ (l : List α) (a x : α), x ≠ a →
      countOf x (eraseFirst a l) = countOf x l
  | [], _, _, _ => rfl
  | b :: t, a, x, hxa => by
    by_cases hab : a = b
    · show countOf x (if a = b then t else b :: eraseFirst a t)
        = countOf x (b :: t)
      rw [if_pos hab, countOf_head_ne (hab ▸ hxa)]
    · show countOf x (if a = b then t else b :: eraseFirst a t)
        = countOf x (b :: t)
      rw [if_neg hab]
      by_cases hxb : x = b
      · rw [hxb, countOf_head, countOf_head,
          countOf_eraseFirst_ne t a b (hxb ▸ hxa)]
      · rw [countOf_head_ne hxb, countOf_head_ne hxb,
          countOf_eraseFirst_ne t a x hxa]

/-- The fold at a mapped index list is the composed read's fold, the
map's own fusion. -/
theorem famFold_map {α γ β : Type} (add : β → β → β) (unit : β)
    (f : γ → β) (g : α → γ) :
    ∀ l : List α, famFold add unit f (l.map g)
      = famFold add unit (fun x => f (g x)) l
  | [] => rfl
  | a :: t => by
    show add (f (g a)) (famFold add unit f (t.map g)) = _
    rw [famFold_map add unit f g t]
    rfl

/-- A cons's count is at least the tail's. -/
theorem countOf_cons_le {α : Type} [DecidableEq α]
    (x b : α) (t : List α) : countOf x t ≤ countOf x (b :: t) :=
  Nat.le_add_left _ _

private theorem countOf_map_mem {α : Type} [DecidableEq α]
    {l : List α} {g h : α → α} {y : α} (hy : 0 < countOf y l)
    (hgh : ∀ x, 0 < countOf x l → h (g x) = x)
    (hhg : ∀ x, 0 < countOf x l → g (h x) = x) :
    ∀ t : List α, (∀ x, 0 < countOf x t → 0 < countOf x l) →
      countOf y (t.map g) = countOf (h y) t
  | [], _ => rfl
  | b :: t, hsub => by
    have hb : 0 < countOf b l := hsub b (by
      rw [countOf_head]; exact Nat.succ_pos _)
    have ht : ∀ x, 0 < countOf x t → 0 < countOf x l := fun x hx =>
      hsub x (Nat.lt_of_lt_of_le hx (countOf_cons_le x b t))
    show countOf y (g b :: t.map g) = countOf (h y) (b :: t)
    rw [countOf_cons, countOf_cons]
    by_cases hyb : y = g b
    · rw [if_pos hyb, if_pos (by rw [hyb, hgh b hb]),
        countOf_map_mem hy hgh hhg t ht]
    · rw [if_neg hyb,
        if_neg (fun hc : h y = b => hyb (by rw [← hc, hhg y hy])),
        countOf_map_mem hy hgh hhg t ht]

private theorem countOf_map_out {α : Type} [DecidableEq α]
    {l : List α} {g : α → α} {y : α} (hy : countOf y l = 0)
    (hgm : ∀ x, 0 < countOf x l → 0 < countOf (g x) l) :
    ∀ t : List α, (∀ x, 0 < countOf x t → 0 < countOf x l) →
      countOf y (t.map g) = 0
  | [], _ => rfl
  | b :: t, hsub => by
    have hb : 0 < countOf b l := hsub b (by
      rw [countOf_head]; exact Nat.succ_pos _)
    have ht : ∀ x, 0 < countOf x t → 0 < countOf x l := fun x hx =>
      hsub x (Nat.lt_of_lt_of_le hx (countOf_cons_le x b t))
    show countOf y (g b :: t.map g) = 0
    rw [countOf_cons, if_neg (fun hc : y = g b => by
        have hgb := hgm b hb
        rw [← hc, hy] at hgb
        exact absurd hgb (Nat.lt_irrefl 0)),
      Nat.zero_add]
    exact countOf_map_out hy hgm t ht

/-- The counts transport along a map at a pointwise pairing: the
image's count at a key is the family's at the paired key, each
member's image read matching exactly at the pair. -/
theorem countOf_map_iff {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) : ∀ (l : List α) (x : β) (y : α),
      (∀ v, 0 < countOf v l → (x = f v ↔ y = v)) →
      countOf x (l.map f) = countOf y l
  | [], _, _, _ => rfl
  | a :: t, x, y, h => by
    show countOf x (f a :: t.map f) = countOf y (a :: t)
    rw [countOf_cons, countOf_cons]
    have ha := h a (by
      rw [countOf_head]
      exact Nat.succ_pos _)
    rw [countOf_map_iff f t x y
      (fun v hv => h v (countOf_cons_pos hv))]
    by_cases hxa : x = f a
    · rw [if_pos hxa, if_pos (ha.mp hxa)]
    · rw [if_neg hxa, if_neg (fun hy => hxa (ha.mpr hy))]

/-- The witness map's counts: at a distinct family, a map with a
two-sided witness on the members and member closure both ways reads
every count across, the reindexing's whole datum. -/
theorem countOf_map {α : Type} [DecidableEq α] {l : List α}
    {g h : α → α} (hdist : distinctList l)
    (hgh : ∀ x, 0 < countOf x l → h (g x) = x)
    (hhg : ∀ x, 0 < countOf x l → g (h x) = x)
    (hgm : ∀ x, 0 < countOf x l → 0 < countOf (g x) l)
    (hhm : ∀ x, 0 < countOf x l → 0 < countOf (h x) l)
    (y : α) : countOf y (l.map g) = countOf y l := by
  match Nat.eq_zero_or_pos (countOf y l) with
  | .inl hzero =>
    rw [hzero]
    exact countOf_map_out hzero hgm l (fun _ hx => hx)
  | .inr hpos =>
    rw [countOf_map_mem hpos hgh hhg l (fun _ hx => hx),
      Nat.le_antisymm (distinctList_all hdist (h y)) (hhm y hpos),
      Nat.le_antisymm (distinctList_all hdist y) hpos]

/-! The reordering reads at a carrier equality: the reordering
theorems with the displayed sum's identities read at the carrier's
own one-value relation, the spelling every carrier whose equality
is not literal (a polynomial's list, say) satisfies; the literal-Eq
reordering reads below are their instances at the equality itself.
The list facts beneath them are structural and stay at `Eq`.  A
general here reads the smallest bundle covering its consumed laws
(`CommLaws` where no unit read enters, `FoldLaws` where one does);
where a caller's carrier holds no covering bundle — the literal
equality at a bare operation with a unit identity but no
commutation — a private core threads exactly the shared laws. -/

/-- The fold's occupied member joins in front, at every carrier
with the reordering bundle. -/
theorem famFold_eraseFirst_ov {α β : Type} [DecidableEq α]
    {ov : β → β → Prop} {add : β → β → β}
    (C : CommLaws β add ov) (unit : β)
    (f : α → β) :
    ∀ (l : List α) (a : α), 0 < countOf a l →
      ov (add (f a) (famFold add unit f (eraseFirst a l)))
        (famFold add unit f l)
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | b :: t, a, h => by
    by_cases hab : a = b
    · show ov (add (f a)
          (famFold add unit f (if a = b then t else b :: eraseFirst a t)))
        (add (f b) (famFold add unit f t))
      rw [if_pos hab, hab]
      exact C.ovRefl _
    · have h' : 0 < countOf a t := by
        rw [countOf_head_ne hab] at h; exact h
      show ov (add (f a)
          (famFold add unit f (if a = b then t else b :: eraseFirst a t)))
        (add (f b) (famFold add unit f t))
      rw [if_neg hab]
      show ov (add (f a)
          (add (f b) (famFold add unit f (eraseFirst a t))))
        (add (f b) (famFold add unit f t))
      exact C.ovTrans
        (C.ovTrans (C.opComm (f a) (add (f b) (famFold add unit f (eraseFirst a t))))
          (C.ovTrans
            (C.opAssoc (f b) (famFold add unit f (eraseFirst a t)) (f a))
            (C.opCongr (C.ovRefl (f b))
              (C.opComm (famFold add unit f (eraseFirst a t)) (f a)))))
        (C.opCongr (C.ovRefl (f b))
          (famFold_eraseFirst_ov C unit f t a h'))

/-- A family reading the unit at every occupied member folds to
the unit, at a stated relation with the displayed sum's laws. -/
theorem famFold_null_ov {α β : Type} [DecidableEq α]
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov)
    (f : α → β) : ∀ l : List α,
      (∀ x, 0 < countOf x l → ov (f x) unit) →
      ov (famFold add unit f l) unit
  | [], _ => L.ovRefl unit
  | a :: t, h =>
    L.ovTrans
      (L.opCongr (h a (by rw [countOf_head]; exact Nat.succ_pos _))
        (famFold_null_ov L f t (fun x hx =>
            h x (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))))
      (L.unitOp unit)

/-- The fold at a family reading the unit off one key occupied
once reads that key's own datum, at a stated relation with the
displayed sum's laws: the key's member withdraws at the head
(`famFold_eraseFirst_ov`) and the further members fold to the
unit. -/
theorem famFold_pick_ov {α β : Type} [DecidableEq α]
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov)
    (F : α → β) (i : α) (X : β) (l : List α)
    (h : countOf i l = 1) (hon : ov (F i) X)
    (hoff : ∀ x, 0 < countOf x l → ¬ x = i → ov (F x) unit) :
    ov (famFold add unit F l) X := by
  have hpi : 0 < countOf i l := by
    rw [h]
    exact Nat.succ_pos 0
  have hea : countOf i (eraseFirst i l) = 0 := by
    have h2 := countOf_eraseFirst_self l i hpi
    rw [h] at h2
    exact (Nat.succ.inj h2).symm
  have htail : ov (famFold add unit F (eraseFirst i l)) unit :=
    famFold_null_ov L F (eraseFirst i l)
      (fun x hx => by
        have hxi : ¬ x = i := fun he => by
          rw [he, hea] at hx
          exact absurd hx (Nat.lt_irrefl 0)
        exact hoff x (by
          rw [← countOf_eraseFirst_ne l i x hxi]
          exact hx) hxi)
  exact L.ovTrans
    (L.ovSymm (famFold_eraseFirst_ov L.toCommLaws unit F l i hpi))
    (L.ovTrans (L.opCongr hon htail) (L.opUnit X))

/-- Two fold orders read one value at a carrier equality: at
matched member counts the folds carry the same value, in every
carrier with a commutative and associative displayed sum read at
that equality. -/
theorem famFold_relist_ov {α β : Type} [DecidableEq α]
    {ov : β → β → Prop} {add : β → β → β}
    (C : CommLaws β add ov) (unit : β)
    (f : α → β) :
    ∀ (l l' : List α), (∀ x, countOf x l = countOf x l') →
      ov (famFold add unit f l) (famFold add unit f l')
  | [], l', h => by
    rw [eq_nil_of_countOf l' (fun x => (h x).symm)]
    exact C.ovRefl _
  | a :: t, l', h => by
    have ha : 0 < countOf a l' := by
      rw [← h a, countOf_head]
      exact Nat.succ_pos _
    have hc : ∀ x, countOf x t = countOf x (eraseFirst a l') := by
      intro x
      by_cases hxa : x = a
      · have hself := countOf_eraseFirst_self l' a ha
        have hh := h a
        rw [countOf_head, hself] at hh
        rw [hxa]
        exact Nat.succ.inj hh
      · rw [countOf_eraseFirst_ne l' a x hxa, ← h x,
          countOf_head_ne hxa]
    show ov (add (f a) (famFold add unit f t)) (famFold add unit f l')
    exact C.ovTrans
      (C.opCongr (C.ovRefl (f a))
        (famFold_relist_ov C unit f t (eraseFirst a l') hc))
      (famFold_eraseFirst_ov C unit f l' a ha)

/-- The reindexing read at a carrier equality: at a distinct family
and a two-sided witness map, the fold carries one value at the
composed spelling, the map's fusion (`famFold_map`) structural
beneath it. -/
theorem famFold_reindex_ov {α β : Type} [DecidableEq α]
    {ov : β → β → Prop} {add : β → β → β}
    (C : CommLaws β add ov) (unit : β)
    (f : α → β) {l : List α} {g h : α → α} (hdist : distinctList l)
    (hgh : ∀ x, 0 < countOf x l → h (g x) = x)
    (hhg : ∀ x, 0 < countOf x l → g (h x) = x)
    (hgm : ∀ x, 0 < countOf x l → 0 < countOf (g x) l)
    (hhm : ∀ x, 0 < countOf x l → 0 < countOf (h x) l) :
    ov (famFold add unit f l)
      (famFold add unit (fun x => f (g x)) l) := by
  rw [← famFold_map add unit f g l]
  exact famFold_relist_ov C unit f l (l.map g)
    (fun y => (countOf_map hdist hgh hhg hgm hhm y).symm)

/-- The memberwise congruence at a one-value relation: two reads at
one value on every occupied member fold to one value. -/
theorem famFold_congr_members_ov {α β : Type} [DecidableEq α]
    (ov : β → β → Prop) (add : β → β → β) (unit : β)
    (hrefl : ∀ x, ov x x)
    (hcongr : ∀ {x x' y y'}, ov x x' → ov y y' →
      ov (add x y) (add x' y'))
    (f g : α → β) :
    ∀ l : List α, (∀ x, 0 < countOf x l → ov (f x) (g x)) →
      ov (famFold add unit f l) (famFold add unit g l)
  | [], _ => hrefl _
  | a :: t, h =>
    hcongr (h a (by rw [countOf_head]; exact Nat.succ_pos _))
      (famFold_congr_members_ov ov add unit hrefl hcongr f g t
        (fun x hx => h x (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _))))

/-- The bijection congruence at a one-value relation: at a distinct
family, a two-sided witness map and members read at the moved key,
the two folds read one value, the memberwise congruence composed
with the reindexing read. -/
theorem famFold_bij_ov {α β : Type} [DecidableEq α]
    {ov : β → β → Prop} {add : β → β → β}
    (C : CommLaws β add ov) (unit : β)
    (F G : α → β) {l : List α} {g h : α → α}
    (hdist : distinctList l)
    (hgh : ∀ x, 0 < countOf x l → h (g x) = x)
    (hhg : ∀ x, 0 < countOf x l → g (h x) = x)
    (hgm : ∀ x, 0 < countOf x l → 0 < countOf (g x) l)
    (hhm : ∀ x, 0 < countOf x l → 0 < countOf (h x) l)
    (hFG : ∀ x, 0 < countOf x l → ov (F x) (G (g x))) :
    ov (famFold add unit F l) (famFold add unit G l) :=
  C.ovTrans
    (famFold_congr_members_ov ov add unit C.ovRefl C.opCongr
      F (fun x => G (g x)) l hFG)
    (C.ovSymm (famFold_reindex_ov C unit G hdist hgh hhg hgm hhm))

/-- The fold splits over a pointwise sum at a one-value relation,
the members' four-way exchange the one law the split reads. -/
theorem famFold_add_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov)
    (f g : α → β) :
    ∀ l : List α,
      ov (famFold add unit (fun x => add (f x) (g x)) l)
        (add (famFold add unit f l) (famFold add unit g l))
  | [] => L.ovSymm (L.opUnit unit)
  | a :: t =>
    L.ovTrans
      (L.opCongr (L.ovRefl (add (f a) (g a)))
        (famFold_add_ov L f g t))
      (opExchO L.toCommLaws (f a) (g a) (famFold add unit f t)
        (famFold add unit g t))

/-- A fold at unit reads throughout is the unit, the per-key read
unconditional. -/
theorem famFold_unit_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov)
    (f : α → β) (h : ∀ x, ov (f x) unit) :
    ∀ l : List α, ov (famFold add unit f l) unit
  | [] => L.ovRefl unit
  | a :: t =>
    L.ovTrans
      (L.opCongr (h a) (famFold_unit_ov L f h t))
      (L.unitOp unit)

/-- With every refused member reading the fold's unit, the
filtered and full lists fold to one value. -/
theorem famFold_filter_read {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov)
    (f : α → β) (t : α → Bool)
    (h : ∀ v, t v = false → ov (f v) unit) :
    ∀ K : List α,
      ov (famFold add unit f (K.filter t)) (famFold add unit f K)
  | [] => L.ovRefl unit
  | v :: K => by
    cases hv : t v with
    | true =>
      rw [filter_cons_true hv]
      show ov (add (f v) (famFold add unit f (K.filter t)))
        (add (f v) (famFold add unit f K))
      exact L.opCongr (L.ovRefl (f v)) (famFold_filter_read L f t h K)
    | false =>
      rw [filter_cons_false hv]
      show ov (famFold add unit f (K.filter t))
        (add (f v) (famFold add unit f K))
      exact L.ovTrans (famFold_filter_read L f t h K)
        (L.ovSymm (L.ovTrans (L.opCongr (h v hv) (L.ovRefl _)) (L.unitOp _)))

/-- A filter whose refused members equal the fold's unit reads
the full list's fold. -/
theorem famFold_filter_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov)
    (f : α → β) (t : α → Bool)
    (h : ∀ v, t v = false → f v = unit) (K : List α) :
    ov (famFold add unit f (K.filter t)) (famFold add unit f K) :=
  famFold_filter_read L f t (fun v hv => by rw [h v hv]; exact L.ovRefl _) K

/-- A factor passes across the fold at a stated distribution and
its unit read, one member at a time. -/
theorem famFold_mul_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov) (mul : β → β → β) (c : β)
    (hnil : ov (mul c unit) unit)
    (hdist : ∀ x y, ov (mul c (add x y)) (add (mul c x) (mul c y)))
    (f : α → β) :
    ∀ l : List α,
      ov (mul c (famFold add unit f l))
        (famFold add unit (fun x => mul c (f x)) l)
  | [] => hnil
  | a :: t =>
    L.ovTrans (hdist (f a) (famFold add unit f t))
      (L.opCongr (L.ovRefl (mul c (f a)))
        (famFold_mul_ov L mul c hnil hdist f t))

/-- The factor passes across the fold on the right, the mirrored
distribution and unit reads the data. -/
theorem famFold_mulR_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov) (mul : β → β → β) (c : β)
    (hnil : ov (mul unit c) unit)
    (hdist : ∀ x y, ov (mul (add x y) c) (add (mul x c) (mul y c)))
    (f : α → β) :
    ∀ l : List α,
      ov (famFold add unit (fun x => mul (f x) c) l)
        (mul (famFold add unit f l) c)
  | [] => L.ovSymm hnil
  | a :: t =>
    L.ovTrans
      (L.opCongr (L.ovRefl (mul (f a) c))
        (famFold_mulR_ov L mul c hnil hdist f t))
      (L.ovSymm (hdist (f a) (famFold add unit f t)))

/-- The nested folds exchange their two index families at a
stated relation. -/
theorem famFold_swap_ov {α γ β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov) (F : α → γ → β) :
    ∀ (ls : List α) (ms : List γ),
      ov (famFold add unit (fun a => famFold add unit (F a) ms) ls)
        (famFold add unit (fun b =>
          famFold add unit (fun a => F a b) ls) ms)
  | [], ms =>
    L.ovSymm (famFold_unit_ov L
      (fun b => famFold add unit (fun a => F a b) [])
      (fun _ => L.ovRefl unit) ms)
  | a :: t, ms =>
    L.ovTrans
      (L.opCongr (L.ovRefl (famFold add unit (F a) ms))
        (famFold_swap_ov L F t ms))
      (L.ovSymm (famFold_add_ov L (F a)
        (fun b => famFold add unit (fun x => F x b) t) ms))

/-- The fold splits at a joined index list at a stated relation
with the sum's reassociation and its unit's left read alone, the
reading the bundled form below and its literal-equality instance
share. -/
private theorem famFold_append_core {α β : Type}
    (ov : β → β → Prop) (add : β → β → β) (unit : β)
    (hrefl : ∀ x, ov x x)
    (htrans : ∀ {x y z}, ov x y → ov y z → ov x z)
    (hcongr : ∀ {x x' y y'}, ov x x' → ov y y' →
      ov (add x y) (add x' y'))
    (hassocR : ∀ x y z, ov (add x (add y z)) (add (add x y) z))
    (hunitL : ∀ x, ov x (add unit x))
    (f : α → β) :
    ∀ u v : List α,
      ov (famFold add unit f (u ++ v))
        (add (famFold add unit f u) (famFold add unit f v))
  | [], _ => hunitL _
  | a :: u, v =>
    htrans
      (hcongr (hrefl (f a))
        (famFold_append_core ov add unit hrefl htrans hcongr hassocR
          hunitL f u v))
      (hassocR (f a) (famFold add unit f u) (famFold add unit f v))

/-- The fold splits at a joined index list at a one-value
relation. -/
theorem famFold_append_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov) (f : α → β) (u v : List α) :
    ov (famFold add unit f (u ++ v))
      (add (famFold add unit f u) (famFold add unit f v)) :=
  famFold_append_core ov add unit L.ovRefl L.ovTrans L.opCongr
    (fun x y z => L.ovSymm (L.opAssoc x y z))
    (fun x => L.ovSymm (L.unitOp x)) f u v

/-- The merge's fold at a read additive at a shared key reads the
two lists' folds joined, at every fuel: a shared key's joined
member reads its two members' join, every further member enters
once, and the fuel's end joins the two tails
(`famFold_append_ov`). -/
theorem mergeJoin_fold_ov {α β γ : Type}
    {ov : γ → γ → Prop} {gadd : γ → γ → γ} {unit : γ}
    (L : FoldLaws γ gadd unit ov) (lt eq : α → α → Bool)
    (add : β → β → β) (f : α × β → γ)
    (hf : ∀ x y : α × β, eq x.1 y.1 = true →
      ov (f (x.1, add x.2 y.2)) (gadd (f x) (f y))) :
    ∀ (fuel : Nat) (a b : List (α × β)),
      ov (famFold gadd unit f (mergeJoin lt eq add fuel a b))
        (gadd (famFold gadd unit f a) (famFold gadd unit f b))
  | 0, a, b => famFold_append_ov L f a b
  | _ + 1, [], b => L.ovSymm (L.unitOp _)
  | _ + 1, x :: s, [] => famFold_append_ov L f (x :: s) []
  | fuel + 1, x :: s, y :: t => by
    show ov (famFold gadd unit f (if eq x.1 y.1 then
        (x.1, add x.2 y.2) :: mergeJoin lt eq add fuel s t
      else if lt x.1 y.1 then x :: mergeJoin lt eq add fuel s (y :: t)
      else y :: mergeJoin lt eq add fuel (x :: s) t))
      (gadd (gadd (f x) (famFold gadd unit f s))
        (gadd (f y) (famFold gadd unit f t)))
    cases he : eq x.1 y.1 with
    | true =>
      rw [if_pos rfl]
      show ov (gadd (f (x.1, add x.2 y.2))
        (famFold gadd unit f (mergeJoin lt eq add fuel s t))) _
      refine L.ovTrans (L.opCongr (hf x y he)
        (mergeJoin_fold_ov L lt eq add f hf fuel s t)) ?_
      exact opExchO L.toCommLaws _ _ _ _
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
      cases hl : lt x.1 y.1 with
      | true =>
        rw [if_pos rfl]
        show ov (gadd (f x)
          (famFold gadd unit f (mergeJoin lt eq add fuel s (y :: t)))) _
        refine L.ovTrans (L.opCongr (L.ovRefl _)
          (mergeJoin_fold_ov L lt eq add f hf fuel s (y :: t))) ?_
        exact L.ovSymm (L.opAssoc _ _ _)
      | false =>
        rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
        show ov (gadd (f y)
          (famFold gadd unit f (mergeJoin lt eq add fuel (x :: s) t))) _
        refine L.ovTrans (L.opCongr (L.ovRefl _)
          (mergeJoin_fold_ov L lt eq add f hf fuel (x :: s) t)) ?_
        exact opLeftCommO L.toCommLaws _ _ _

/-- The folds over the alternating halves join to the list's
fold at the displayed sum's regrouping and exchange. -/
theorem famFold_halves_ov {α β : Type}
    {ov : β → β → Prop} {add : β → β → β} {unit : β}
    (L : FoldLaws β add unit ov) (f : α → β) :
    ∀ l : List α,
      ov (add (famFold add unit f (halvesL l).1)
        (famFold add unit f (halvesL l).2)) (famFold add unit f l)
  | [] => L.opUnit _
  | [_] => L.opUnit _
  | x :: y :: t => by
    change ov (add (add (f x) (famFold add unit f (halvesL t).1))
      (add (f y) (famFold add unit f (halvesL t).2)))
      (add (f x) (add (f y) (famFold add unit f t)))
    exact L.ovTrans (L.opAssoc _ _ _)
      (L.opCongr (L.ovRefl _) (L.ovTrans
        (opLeftCommO L.toCommLaws _ _ _)
        (L.opCongr (L.ovRefl _) (famFold_halves_ov L f t))))

/-- Sorting with shared keys joined preserves a read additive at
those joins, at every structural fuel. -/
theorem sortJoin_fold_ov {α β γ : Type}
    {ov : γ → γ → Prop} {gadd : γ → γ → γ} {unit : γ}
    (L : FoldLaws γ gadd unit ov) (lt eq : α → α → Bool)
    (add : β → β → β) (f : α × β → γ)
    (hf : ∀ x y : α × β, eq x.1 y.1 = true →
      ov (f (x.1, add x.2 y.2)) (gadd (f x) (f y))) :
    ∀ (fuel : Nat) (l : List (α × β)),
      ov (famFold gadd unit f (sortJoin lt eq add fuel l))
        (famFold gadd unit f l)
  | 0, _ => L.ovRefl _
  | _ + 1, [] => L.ovRefl _
  | _ + 1, [_] => L.ovRefl _
  | fuel + 1, x :: y :: t => by
    change ov (famFold gadd unit f (mergeJoin lt eq add
      ((sortJoin lt eq add fuel (halvesL (x :: y :: t)).1).length
        + (sortJoin lt eq add fuel (halvesL (x :: y :: t)).2).length)
      (sortJoin lt eq add fuel (halvesL (x :: y :: t)).1)
      (sortJoin lt eq add fuel (halvesL (x :: y :: t)).2)))
      (famFold gadd unit f (x :: y :: t))
    exact L.ovTrans (mergeJoin_fold_ov L lt eq add f hf _ _ _)
      (L.ovTrans (L.opCongr (sortJoin_fold_ov L lt eq add f hf fuel _)
        (sortJoin_fold_ov L lt eq add f hf fuel _)) (famFold_halves_ov L f _))

/-- The fold over a flattened family reads the fold of the
per-member folds at a one-value relation. -/
theorem famFold_flatMap_ov {α β γ : Type}
    {ov : γ → γ → Prop} {add : γ → γ → γ} {unit : γ}
    (L : FoldLaws γ add unit ov)
    (F : β → γ) (g : α → List β) :
    ∀ l : List α,
      ov (famFold add unit F (l.flatMap g))
        (famFold add unit (fun x => famFold add unit F (g x)) l)
  | [] => L.ovRefl _
  | a :: t =>
    L.ovTrans
      (famFold_append_ov L F (g a) (t.flatMap g))
      (L.opCongr (L.ovRefl (famFold add unit F (g a)))
        (famFold_flatMap_ov L F g t))

/-- The literal equality with the two reordering identities is the
reordering bundle's instance at a bare operation. -/
private theorem eqCommLaws {β : Type} {add : β → β → β}
    (hcomm : ∀ x y, add x y = add y x)
    (hassoc : ∀ x y z, add (add x y) z = add x (add y z)) :
    CommLaws β add Eq :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2,
    fun h1 h2 => by rw [h1, h2], hcomm, hassoc⟩

/-- The fold reads an occupied member first, the further members'
fold beside it, by the carrier's displayed identities: the
carrier-equality read's instance at the literal equality. -/
theorem famFold_eraseFirst {α β : Type} [DecidableEq α]
    (add : β → β → β) (unit : β)
    (hcomm : ∀ x y, add x y = add y x)
    (hassoc : ∀ x y z, add (add x y) z = add x (add y z))
    (f : α → β) (l : List α) (a : α) (h : 0 < countOf a l) :
    famFold add unit f l
      = add (f a) (famFold add unit f (eraseFirst a l)) :=
  (famFold_eraseFirst_ov (eqCommLaws hcomm hassoc)
    unit f l a h).symm

/-- Two fold orders are equal by the ground identities: at matched
member counts the folds read one value, in every carrier with a
commutative and associative displayed sum — the carrier-equality
read's instance at the literal equality. -/
theorem famFold_relist {α β : Type} [DecidableEq α]
    (add : β → β → β) (unit : β)
    (hcomm : ∀ x y, add x y = add y x)
    (hassoc : ∀ x y z, add (add x y) z = add x (add y z))
    (f : α → β) (l l' : List α)
    (h : ∀ x, countOf x l = countOf x l') :
    famFold add unit f l = famFold add unit f l' :=
  famFold_relist_ov (eqCommLaws hcomm hassoc)
    unit f l l' h

/-- The reindexing read: at a distinct family and a two-sided
witness map, the fold reads one value at the composed spelling —
the carrier-equality read's instance at the literal equality. -/
theorem famFold_reindex {α β : Type} [DecidableEq α]
    (add : β → β → β) (unit : β)
    (hcomm : ∀ x y, add x y = add y x)
    (hassoc : ∀ x y z, add (add x y) z = add x (add y z))
    (f : α → β) {l : List α} {g h : α → α} (hdist : distinctList l)
    (hgh : ∀ x, 0 < countOf x l → h (g x) = x)
    (hhg : ∀ x, 0 < countOf x l → g (h x) = x)
    (hgm : ∀ x, 0 < countOf x l → 0 < countOf (g x) l)
    (hhm : ∀ x, 0 < countOf x l → 0 < countOf (h x) l) :
    famFold add unit f l = famFold add unit (fun x => f (g x)) l :=
  famFold_reindex_ov (eqCommLaws hcomm hassoc)
    unit f hdist hgh hhg hgm hhm

/-- A mapped member's count at an injective-on-members map is the
member's own. -/
theorem countOf_map_inj {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (a : α) :
    ∀ l : List α, (∀ x, 0 < countOf x l → f x = f a → x = a) →
      countOf (f a) (l.map f) = countOf a l
  | [], _ => rfl
  | b :: t, h => by
    show countOf (f a) (f b :: t.map f) = countOf a (b :: t)
    rw [countOf_cons, countOf_cons,
      countOf_map_inj f a t (fun x hx => h x
        (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))]
    by_cases hab : a = b
    · rw [if_pos (by rw [hab]), if_pos hab]
    · rw [if_neg (fun he : f a = f b => hab
        ((h b (by rw [countOf_head]; exact Nat.succ_pos _)
          he.symm).symm)), if_neg hab]

/-- A value off every mapped member counts at nought in the mapped
family. -/
theorem countOf_map_none {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → β) (y : β) :
    ∀ l : List α, (∀ x, 0 < countOf x l → ¬ f x = y) →
      countOf y (l.map f) = 0
  | [], _ => rfl
  | b :: t, h => by
    show countOf y (f b :: t.map f) = 0
    rw [countOf_cons,
      countOf_map_none f y t (fun x hx => h x
        (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _))),
      if_neg (fun he : y = f b =>
        h b (by rw [countOf_head]; exact Nat.succ_pos _) he.symm)]

/-- A member's count adds over a joined family. -/
theorem countOf_append {α : Type} [DecidableEq α] (x : α) :
    ∀ u v : List α, countOf x (u ++ v) = countOf x u + countOf x v
  | [], v => (Nat.zero_add _).symm
  | b :: u, v => by
    show countOf x (b :: (u ++ v)) = countOf x (b :: u) + countOf x v
    rw [countOf_cons, countOf_cons, countOf_append x u v, Nat.add_assoc]

/-- The repeated family counts its own member. -/
theorem countOf_replicate {α : Type} [DecidableEq α] (a : α) :
    ∀ n : Nat, countOf a (List.replicate n a) = n
  | 0 => rfl
  | n + 1 => by
    show countOf a (a :: List.replicate n a) = n + 1
    rw [countOf_cons, if_pos rfl, countOf_replicate a n, Nat.add_comm]

/-- The repeated family counts a further letter at the fold's
unit. -/
theorem countOf_replicate_ne {α : Type} [DecidableEq α] (a b : α)
    (hab : ¬ a = b) : ∀ n : Nat,
    countOf a (List.replicate n b) = 0
  | 0 => rfl
  | n + 1 => by
    show countOf a (b :: List.replicate n b) = 0
    rw [countOf_cons, if_neg hab, countOf_replicate_ne a b hab n]

/-- A member's count over a keyed union splits as the fold of the
per-key counts. -/
theorem countOf_flatMap {α γ : Type} [DecidableEq α] (x : α)
    (f : γ → List α) :
    ∀ l : List γ, countOf x (l.flatMap f)
      = famFold Nat.add 0 (fun i => countOf x (f i)) l
  | [] => rfl
  | b :: t => by
    show countOf x (f b ++ List.flatMap f t) = _
    rw [countOf_append, countOf_flatMap x f t]
    rfl

/-- The seed monomial's count over a family of grown lists is
absent, every member a grown list. -/
theorem countOf_nil_consMap {α : Type} [DecidableEq α] (i : α) :
    ∀ l : List (List α),
      countOf ([] : List α) (l.map (fun t => i :: t)) = 0
  | [] => rfl
  | b :: l => by
    show (if ([] : List α) = i :: b then 1 else 0)
        + countOf ([] : List α) (l.map (fun t => i :: t)) = 0
    rw [if_neg (fun hc : ([] : List α) = i :: b => nomatch hc),
      countOf_nil_consMap i l]

/-- A member's count over a family of grown lists: the head must
match, the tail's count reading through. -/
theorem countOf_consMap {α : Type} [DecidableEq α] (a i : α) :
    ∀ (l : List (List α)) (m : List α),
      countOf (a :: m) (l.map (fun t => i :: t))
        = if a = i then countOf m l else 0
  | [], m => by
    by_cases h : a = i
    · rw [if_pos h]; rfl
    · rw [if_neg h]; rfl
  | b :: l, m => by
    show countOf (a :: m) ((i :: b) :: l.map (fun t => i :: t))
      = if a = i then countOf m (b :: l) else 0
    rw [countOf_cons, countOf_cons, countOf_consMap a i l m]
    by_cases hai : a = i
    · rw [if_pos hai, if_pos hai]
      by_cases hmb : m = b
      · rw [if_pos hmb, if_pos (by rw [hai, hmb])]
      · rw [if_neg hmb,
          if_neg (fun hc : a :: m = i :: b =>
            hmb (List.cons.inj hc).2)]
    · rw [if_neg hai, if_neg hai,
        if_neg (fun hc : a :: m = i :: b =>
          hai (List.cons.inj hc).1)]

/-- The occupancy families of a list: the tail's own, each without
and with the head (`thm:assembly`'s subset fold at the positive
list, `cor:weyldim`'s at the place pairs). -/
def sublistsOf {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => sublistsOf l ++ (sublistsOf l).map (fun S => a :: S)

/-- The insertion of a member by descending natural key, the keyed
insertion sort's one step. -/
def insertKeyDesc {α : Type} (key : α → Nat) (x : α) :
    List α → List α
  | [] => [x]
  | h :: t =>
    if key h < key x then x :: h :: t
    else h :: insertKeyDesc key x t

/-- A keyed insertion preserves the head-and-tail member counts,
independently of the key order. -/
theorem countOf_insertKeyDesc {α : Type} [DecidableEq α]
    (key : α → Nat) (mu x : α) : ∀ l : List α,
      ground.countOf x (ground.insertKeyDesc key mu l)
        = ground.countOf x (mu :: l)
  | [] => rfl
  | nu :: t => by
    show ground.countOf x
        (if key nu < key mu then mu :: nu :: t
         else nu :: ground.insertKeyDesc key mu t)
      = ground.countOf x (mu :: nu :: t)
    by_cases hc : key nu < key mu
    · rw [if_pos hc]
    · rw [if_neg hc]
      rw [ground.countOf_cons x nu (ground.insertKeyDesc key mu t),
        ground.countOf_cons x mu (nu :: t),
        ground.countOf_cons x nu t,
        countOf_insertKeyDesc key mu x t, ground.countOf_cons x mu t]
      show (if x = nu then 1 else 0)
          + ((if x = mu then 1 else 0) + ground.countOf x t)
        = (if x = mu then 1 else 0)
          + ((if x = nu then 1 else 0) + ground.countOf x t)
      rw [Nat.add_left_comm]

/-- The membership test, the count's own decide. -/
def containsB {α : Type} [DecidableEq α] (S : List α) (j : α) : Bool :=
  decide (0 < countOf j S)

/-- The head's own membership read. -/
theorem containsB_head {α : Type} [DecidableEq α]
    (a : α) (S : List α) :
    containsB (a :: S) a = true := by
  show decide (0 < countOf a (a :: S)) = true
  refine decide_eq_true ?_
  rw [countOf_cons, if_pos rfl]
  exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)

/-- The membership read past an off-key head. -/
theorem containsB_cons_ne {α : Type} [DecidableEq α]
    {j a : α} (h : j ≠ a) (S : List α) :
    containsB (a :: S) j = containsB S j := by
  show decide (0 < countOf j (a :: S))
    = decide (0 < countOf j S)
  have hc : countOf j (a :: S) = countOf j S := by
    rw [countOf_cons, if_neg h, Nat.zero_add]
  rw [hc]

/-- A member off every grown spelling is absent from the grown
family, `countOf_consMap`'s guarded read. -/
private theorem countOf_consMap_ne {α : Type} [DecidableEq α]
    {S : List α} {a : α}
    (h : ∀ S', S ≠ a :: S') (L : List (List α)) :
    countOf S (L.map (fun T => a :: T)) = 0 := by
  cases S with
  | nil => exact countOf_nil_consMap a L
  | cons b S' =>
    rw [countOf_consMap b a L S',
      if_neg (fun hba : b = a => h S' (by rw [hba]))]

/-- An occupied count over the grown family names its seed,
`countOf_consMap`'s preimage read. -/
private theorem map_cons_pre {α : Type} [DecidableEq α]
    {a : α} {S : List α} {L : List (List α)}
    (h : 0 < countOf S (L.map (fun T => a :: T))) :
    ∃ S', S = a :: S' ∧ 0 < countOf S' L := by
  cases S with
  | nil =>
    rw [countOf_nil_consMap] at h
    exact absurd h (Nat.lt_irrefl 0)
  | cons b S' =>
    rw [countOf_consMap b a L S'] at h
    by_cases hb : b = a
    · rw [if_pos hb] at h
      exact ⟨S', by rw [hb], h⟩
    · rw [if_neg hb] at h
      exact absurd h (Nat.lt_irrefl 0)

/-- A member's entries sit in the seed. -/
theorem sublists_entries {α : Type} [DecidableEq α] : ∀ (l S : List α),
    0 < countOf S (sublistsOf l) →
    ∀ x, 0 < countOf x S → 0 < countOf x l
  | [], S, hS, x, hx => by
    by_cases he : S = []
    · rw [he] at hx
      exact absurd hx (Nat.lt_irrefl 0)
    · have hz : countOf S (sublistsOf []) = 0 := countOf_head_ne he []
      rw [hz] at hS
      exact absurd hS (Nat.lt_irrefl 0)
  | a :: l, S, hS, x, hx => by
    have hSa : 0 < countOf S (sublistsOf l)
        + countOf S ((sublistsOf l).map (fun T => a :: T)) := by
      rw [← countOf_append]
      exact hS
    cases posOr hSa with
    | inl hin => exact countOf_cons_pos (sublists_entries l S hin x hx)
    | inr hin =>
      obtain ⟨S', hS', hin'⟩ := map_cons_pre hin
      rw [hS'] at hx
      by_cases hxa : x = a
      · rw [hxa, countOf_head]
        exact Nat.succ_pos _
      · rw [countOf_head_ne hxa] at hx ⊢
        exact sublists_entries l S' hin' x hx

/-- The filter's family membership: every guard's image sits in
the enumeration. -/
theorem filter_member {α : Type} [DecidableEq α]
    (P : α → Bool) : ∀ l : List α,
    0 < countOf (List.filter P l) (sublistsOf l)
  | [] => Nat.succ_pos 0
  | a :: l => by
    show 0 < countOf (List.filter P (a :: l))
      (sublistsOf l ++ (sublistsOf l).map (fun T => a :: T))
    rw [countOf_append]
    cases hpa : P a with
    | true =>
      rw [filter_cons_true hpa]
      refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
      rw [countOf_consMap a a (sublistsOf l) (List.filter P l),
        if_pos rfl]
      exact filter_member P l
    | false =>
      rw [filter_cons_false hpa]
      exact Nat.lt_of_lt_of_le (filter_member P l)
        (Nat.le_add_right _ _)

/-- The enumeration counts each family once at a distinct seed. -/
theorem sublists_count_le {α : Type} [DecidableEq α] :
    ∀ l : List α,
    (∀ x, countOf x l ≤ 1) →
    ∀ S, countOf S (sublistsOf l) ≤ 1
  | [], _, S => by
    show countOf S ([] :: []) ≤ 1
    rw [countOf_cons]
    by_cases he : S = []
    · rw [if_pos he]
      exact Nat.le.refl
    · rw [if_neg he]
      exact Nat.le.step Nat.le.refl
  | a :: l, h, S => by
    have hal : countOf a l = 0 := by
      have := h a
      rw [countOf_head] at this
      cases hc : countOf a l with
      | zero => rfl
      | succ m =>
        rw [hc] at this
        exact absurd (Nat.lt_of_succ_lt_succ
          (Nat.lt_of_succ_le this)) (Nat.not_lt_zero m)
    have htail : ∀ x, countOf x l ≤ 1 :=
      fun x => Nat.le_trans (countOf_cons_le x a l) (h x)
    show countOf S
      (sublistsOf l ++ (sublistsOf l).map (fun T => a :: T)) ≤ 1
    rw [countOf_append]
    cases S with
    | nil =>
      rw [countOf_consMap_ne
        (fun S' he => Nat.noConfusion (congrArg List.length he))
        (sublistsOf l)]
      exact sublists_count_le l htail []
    | cons b S' =>
      by_cases hb : b = a
      · rw [hb]
        have hleft : countOf (a :: S')
            (sublistsOf l) = 0 := by
          cases hc : countOf (a :: S') (sublistsOf l) with
          | zero => rfl
          | succ m =>
            have hx : 0 < countOf a (a :: S') := by
              rw [countOf_head]
              exact Nat.succ_pos _
            have := sublists_entries l (a :: S')
              (by rw [hc]; exact Nat.succ_pos m) a hx
            rw [hal] at this
            exact absurd this (Nat.lt_irrefl 0)
        rw [hleft, Nat.zero_add,
          countOf_consMap a a (sublistsOf l) S', if_pos rfl]
        exact sublists_count_le l htail S'
      · rw [countOf_consMap_ne
          (fun T he => hb (List.cons.inj he).1) (sublistsOf l)]
        exact sublists_count_le l htail (b :: S')

/-- A distinct-seeded family member is its own entries' filter of
the seed: the enumeration's characterization read. -/
theorem sublists_char {α : Type} [DecidableEq α] : ∀ l : List α,
    (∀ x, countOf x l ≤ 1) →
    ∀ S, 0 < countOf S (sublistsOf l) →
    S = List.filter (containsB S) l
  | [], _, S, hS => by
    by_cases he : S = []
    · exact he
    · have hz : countOf S (sublistsOf []) = 0 := countOf_head_ne he []
      rw [hz] at hS
      exact absurd hS (Nat.lt_irrefl 0)
  | a :: l, h, S, hS => by
    have hal : countOf a l = 0 := by
      have := h a
      rw [countOf_head] at this
      cases hc : countOf a l with
      | zero => rfl
      | succ m =>
        rw [hc] at this
        exact absurd (Nat.lt_of_succ_lt_succ
          (Nat.lt_of_succ_le this)) (Nat.not_lt_zero m)
    have htail : ∀ x, countOf x l ≤ 1 :=
      fun x => Nat.le_trans (countOf_cons_le x a l) (h x)
    have hSa : 0 < countOf S (sublistsOf l)
        + countOf S ((sublistsOf l).map (fun T => a :: T)) := by
      rw [← countOf_append]
      exact hS
    cases posOr hSa with
    | inl hin =>
      have hna : countOf a S = 0 := by
        cases hc : countOf a S with
        | zero => rfl
        | succ m =>
          have := sublists_entries l S hin a
            (by rw [hc]; exact Nat.succ_pos m)
          rw [hal] at this
          exact absurd this (Nat.lt_irrefl 0)
      have hcb : containsB S a = false := by
        show decide (0 < countOf a S) = false
        rw [hna]
        rfl
      rw [filter_cons_false hcb]
      exact sublists_char l htail S hin
    | inr hin =>
      obtain ⟨S', hS', hin'⟩ := map_cons_pre hin
      have hnas : countOf a S' = 0 := by
        cases hc : countOf a S' with
        | zero => rfl
        | succ m =>
          have := sublists_entries l S' hin' a
            (by rw [hc]; exact Nat.succ_pos m)
          rw [hal] at this
          exact absurd this (Nat.lt_irrefl 0)
      have hcb : containsB S a = true := by
        show decide (0 < countOf a S) = true
        refine decide_eq_true ?_
        rw [hS', countOf_head]
        exact Nat.succ_pos _
      rw [filter_cons_true hcb, hS']
      have hfc : List.filter (containsB (a :: S')) l
          = List.filter (containsB S') l := by
        refine filter_congr_mem _ _ l (fun x hx => ?_)
        have hxa : ¬ x = a := fun he => by
          rw [he, hal] at hx
          exact absurd hx (Nat.lt_irrefl 0)
        show decide (0 < countOf x (a :: S'))
          = decide (0 < countOf x S')
        rw [countOf_head_ne hxa]
      rw [hfc]
      exact congrArg _ (sublists_char l htail S' hin')

/-- The joined family's fold splits, at the displayed identities
(the core join lemmas read through `propext`, so the join kit below
is hand-rolled). -/
theorem famFold_append {α β : Type} (add : β → β → β) (unit : β)
    (hassoc : ∀ x y z, add (add x y) z = add x (add y z))
    (hunit : ∀ x, add unit x = x) (f : α → β) :
    ∀ u v : List α, famFold add unit f (u ++ v)
      = add (famFold add unit f u) (famFold add unit f v) :=
  famFold_append_core Eq add unit (fun _ => rfl) Eq.trans
    (fun h1 h2 => by rw [h1, h2])
    (fun x y z => (hassoc x y z).symm)
    (fun x => (hunit x).symm) f

/-- The join associates. -/
theorem append_assoc {α : Type} :
    ∀ u v w : List α, u ++ v ++ w = u ++ (v ++ w)
  | [], _, _ => rfl
  | a :: u, v, w => by
    show a :: (u ++ v ++ w) = a :: (u ++ (v ++ w))
    rw [append_assoc u v w]

/-- The accumulating fold over a join runs the second family at
the first's value. -/
theorem foldl_append {α β : Type} (g : β → α → β) :
    ∀ (l m : List α) (acc : β),
      (l ++ m).foldl g acc = m.foldl g (l.foldl g acc)
  | [], _, _ => rfl
  | a :: t, m, acc => foldl_append g t m (g acc a)

/-- The join's length adds. -/
theorem length_append {α : Type} :
    ∀ u v : List α, (u ++ v).length = u.length + v.length
  | [], v => (Nat.zero_add _).symm
  | a :: u, v => by
    show (u ++ v).length + 1 = u.length + 1 + v.length
    rw [length_append u v, Nat.add_right_comm]

/-- Two joins at a matched first count agree at both halves: the
prefixes read off each other and the suffixes follow. -/
theorem append_inj_len {α : Type} :
    ∀ (a c b d : List α), a.length = c.length →
      a ++ b = c ++ d → a = c ∧ b = d
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => nomatch hl
  | _ :: _, [], _, _, hl, _ => nomatch hl
  | x :: a, y :: c, b, d, hl, h => by
    have hx : x = y := (List.cons.inj h).1
    match append_inj_len a c b d (Nat.succ.inj hl)
        (List.cons.inj h).2 with
    | ⟨hac, hbd⟩ =>
      exact ⟨by rw [hx, hac], hbd⟩

/-- A family splits at every count within its own: the two halves
join back to it, the first at the stated count. -/
theorem listSplit {α : Type} : ∀ (cs : List α) (k : Nat),
    k ≤ cs.length → ∃ a b : List α, cs = a ++ b ∧ a.length = k
  | cs, 0, _ => ⟨[], cs, rfl, rfl⟩
  | [], _ + 1, hk => absurd hk (Nat.not_lt_zero _)
  | c :: t, k + 1, hk => by
    obtain ⟨a, b, he, hl⟩ := listSplit t k (Nat.le_of_lt_succ hk)
    refine ⟨c :: a, b, ?_, ?_⟩
    · rw [he]; rfl
    · show a.length + 1 = k + 1
      rw [hl]

/-- The map splits over the join. -/
theorem map_append {α γ : Type} (g : α → γ) :
    ∀ u v : List α, (u ++ v).map g = u.map g ++ v.map g
  | [], _ => rfl
  | a :: u, v => by
    show g a :: (u ++ v).map g = g a :: (u.map g ++ v.map g)
    rw [map_append g u v]

/-- The map's length is the family's. -/
theorem length_map {α γ : Type} (g : α → γ) :
    ∀ l : List α, (l.map g).length = l.length
  | [] => rfl
  | a :: l => by
    show (l.map g).length + 1 = l.length + 1
    rw [length_map g l]

/-- A mapped list's dropped tail is the dropped tail's map. -/
theorem map_drop {α γ : Type} (g : α → γ) :
    ∀ (l : List α) (k : Nat), (l.map g).drop k = (l.drop k).map g
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: t, k + 1 => map_drop g t k

/-- The entry read over a join: within the first family its own,
beyond it the second's at the gap key. -/
theorem getAt_append {α : Type} (d : α) :
    ∀ (u v : List α) (i : Nat), getAt d (u ++ v) i
      = if i < u.length then getAt d u i else getAt d v (i - u.length)
  | [], v, i => by
    show getAt d v i
      = if i < 0 then getAt d ([] : List α) i else getAt d v (i - 0)
    rw [if_neg (Nat.not_lt_zero i)]
    rfl
  | a :: u, v, 0 => by
    show a
      = if 0 < u.length + 1 then getAt d (a :: u) 0
        else getAt d v (0 - (u.length + 1))
    rw [if_pos (Nat.succ_pos u.length)]
    rfl
  | a :: u, v, i + 1 => by
    show getAt d (u ++ v) i
      = if i + 1 < u.length + 1 then getAt d u i
        else getAt d v (i + 1 - (u.length + 1))
    have hsub : i + 1 - (u.length + 1) = i - u.length :=
      Nat.succ_sub_succ i u.length
    rw [getAt_append d u v i, hsub]
    by_cases h : i < u.length
    · rw [if_pos h, if_pos (Nat.succ_lt_succ h)]
    · rw [if_neg h, if_neg (fun hs => h (Nat.lt_of_succ_lt_succ hs))]

/-- The entry read past a join's seam at a stated offset: the
joined family's own. -/
theorem getAt_append_add {α : Type} (e : α) :
    ∀ (u v : List α) (r : Nat),
      getAt e (u ++ v) (u.length + r) = getAt e v r
  | [], v, r => by
    show getAt e v (0 + r) = getAt e v r
    rw [Nat.zero_add]
  | a :: u, v, r => by
    show getAt e (a :: (u ++ v)) (u.length + 1 + r) = getAt e v r
    rw [Nat.add_right_comm u.length 1 r]
    show getAt e (u ++ v) (u.length + r) = getAt e v r
    exact getAt_append_add e u v r

/-- The product against one reads the datum back, the
multiplicative unit's law at the displayed product. -/
theorem BPair.mul_one_read (c : BPair) :
    (c * BPair.ofPos Pos.one).oneValue c := by
  show c.fst * (Pos.one + Pos.one) + c.snd * Pos.one + c.snd
      = c.fst + (c.fst * Pos.one + c.snd * (Pos.one + Pos.one))
  rw [ground.left_distrib c.fst Pos.one Pos.one,
    ground.left_distrib c.snd Pos.one Pos.one,
    ground.mul_one c.fst, ground.mul_one c.snd,
    ground.add_assoc (c.fst + c.fst) c.snd c.snd,
    ground.add_assoc c.fst c.fst (c.snd + c.snd)]

/-- The one's powers read the one. -/
theorem bpow_one : ∀ n : Nat,
    (bpow (BPair.ofPos Pos.one) n).oneValue (BPair.ofPos Pos.one)
  | 0 => BPair.oneValue_refl _
  | n + 1 =>
    BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (bpow_one n))
        (BPair.mul_one_read _))

/-- The first power reads the base, the seed's unit factor
absorbing. -/
theorem bpow_one_read (x : BPair) : (bpow x 1).oneValue x :=
  BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_one_read x)

/-- The successor power reads the base against the power, the
recursion's own read. -/
theorem bpow_succ_read (x : BPair) (j : Nat) :
    (bpow x (j + 1)).oneValue (x * bpow x j) :=
  BPair.norm_oneValue _

/-- The unit's power beyond the constant key reads the sum's unit,
the product absorbing. -/
theorem bpow_unit_succ (k : Nat) :
    (bpow BPair.unit (k + 1)).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.unit_mul _)

/-- The power at a summed key is the powers' product. -/
theorem bpow_add (x : BPair) (a : Nat) : ∀ b : Nat,
    (bpow x (a + b)).oneValue (bpow x a * bpow x b)
  | 0 => BPair.oneValue_symm (BPair.mul_one_read _)
  | b + 1 => by
    show ((x * bpow x (a + b)).norm).oneValue
      (bpow x a * (x * bpow x b).norm)
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl x) (bpow_add x a b)) ?_
    refine BPair.oneValue_trans ?_
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.norm_oneValue _)))
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc, BPair.mul_comm x (bpow x a), BPair.mul_assoc]

/-- The positive power's balance read: the power at the positive
carrier is the balance power of its entry. -/
theorem ofPos_pow (c : Pos) : ∀ k : Nat,
    (BPair.ofPos (Pos.pow c k)).oneValue (ground.bpow (BPair.ofPos c) k)
  | 0 => BPair.oneValue_refl _
  | k + 1 => by
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.norm_oneValue
        (BPair.ofPos c * ground.bpow (BPair.ofPos c) k)))
    refine BPair.oneValue_trans ?_
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos c))
        (ofPos_pow c k))
    show (BPair.ofPos (c * Pos.pow c k)).oneValue
      (BPair.ofPos c * BPair.ofPos (Pos.pow c k))
    exact BPair.oneValue_symm (BPair.ofPos_mul c (Pos.pow c k))

/-- The power passes the product. -/
theorem bpow_mul (a b : BPair) : ∀ k : Nat,
    (bpow (a * b) k).oneValue
      (bpow a k * bpow b k)
  | 0 => BPair.oneValue_symm (BPair.mul_one_read _)
  | k + 1 => by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (a * b)) (bpow_mul a b k)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm a b (bpow a k) (bpow b k))) ?_
    exact BPair.mul_congr
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (BPair.oneValue_symm (BPair.norm_oneValue _))

/-- The entry read through a map at tied defaults: every key's read
of the mapped family is the map at the key's own read, the
over-range keys riding the defaults' tie. -/
theorem getAt_mapT {α γ : Type} (d : α) (e : γ) (f : α → γ)
    (hd : f d = e) : ∀ (m : List α) (t : Nat),
      getAt e (m.map f) t = f (getAt d m t)
  | [], _ => hd.symm
  | _ :: _, 0 => rfl
  | _ :: m, t + 1 => getAt_mapT d e f hd m t

/-- The entry read through a map. -/
theorem getAt_map {α γ : Type} (d : α) (e : γ) (f : α → γ) :
    ∀ (m : List α) (t : Nat), t < m.length →
      getAt e (m.map f) t = f (getAt d m t)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: m, t + 1, h =>
    getAt_map d e f m t (Nat.lt_of_succ_lt_succ h)

/-- A leading part at or beyond the list's count is the list
itself. -/
theorem take_of_le {α : Type} :
    ∀ (l : List α) (n : Nat), l.length ≤ n → l.take n = l
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a :: t, n + 1, h =>
    congrArg (a :: ·) (take_of_le t n (Nat.le_of_succ_le_succ h))

/-- A read at every key of a join assembles from the two sides'
own: the joined key reads the first side below its count and the
second side at the gap. -/
theorem getAt_append_all {α : Type} (d : α) (P : α → Prop)
    (A B : List α)
    (hA : ∀ k, k < A.length → P (getAt d A k))
    (hB : ∀ k, k < B.length → P (getAt d B k)) :
    ∀ k, k < (A ++ B).length → P (getAt d (A ++ B) k) := by
  intro k hk
  rw [getAt_append d A B k]
  by_cases h : k < A.length
  · rw [if_pos h]
    exact hA k h
  · rw [if_neg h]
    refine hB (k - A.length) (subLt (Nat.le_of_not_lt h) ?_)
    rw [← length_append A B]
    exact hk

/-- The entry at a key inside the list is a member. -/
theorem mem_getAt {α : Type} (e : α) :
    ∀ (l : List α) (k : Nat), k < l.length → getAt e l k ∈ l
  | [], k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: t, 0, _ => List.Mem.head t
  | a :: t, k + 1, hk =>
    List.Mem.tail a (mem_getAt e t k (Nat.lt_of_succ_lt_succ hk))

/-- A member sits at a key, the position its own. -/
theorem getAt_of_mem {α : Type} (e : α) {x : α} :
    ∀ {l : List α}, x ∈ l → ∃ k, k < l.length ∧ getAt e l k = x
  | [], h => nomatch h
  | _ :: t, h => by
    cases h with
    | head => exact ⟨0, Nat.succ_pos t.length, rfl⟩
    | tail _ hm =>
      match getAt_of_mem e hm with
      | ⟨k, hk, he⟩ => exact ⟨k + 1, Nat.succ_lt_succ hk, he⟩

/-- A member of a mapped family names its source. -/
theorem mem_map_of {α β : Type} (f : α → β) :
    ∀ (l : List α) (x : β), x ∈ l.map f → ∃ a, a ∈ l ∧ f a = x
  | [], _, h => nomatch h
  | z :: t, x, h => by
    have h' : x ∈ f z :: t.map f := h
    cases h' with
    | head => exact ⟨z, List.Mem.head t, rfl⟩
    | tail _ hm =>
      match mem_map_of f t x hm with
      | ⟨a, ha, hax⟩ => exact ⟨a, List.Mem.tail z ha, hax⟩

/-- A member's image joins the mapped family. -/
theorem mem_map_to {α β : Type} (f : α → β) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ∈ l.map f
  | [], h => nomatch h
  | z :: t, h => by
    cases h with
    | head => exact List.Mem.head (t.map f)
    | tail _ hm => exact List.Mem.tail (f z) (mem_map_to f hm)

/-- A member of the left side is a member of the join. -/
theorem mem_append_left {α : Type} {a : α} :
    ∀ {l : List α} (l' : List α), a ∈ l → a ∈ l ++ l'
  | [], _, h => nomatch h
  | z :: t, l', h => by
    have h' : a ∈ z :: t := h
    show a ∈ z :: (t ++ l')
    cases h' with
    | head => exact List.Mem.head (t ++ l')
    | tail _ hm => exact List.Mem.tail z (mem_append_left l' hm)

/-- A member of the right side is a member of the join. -/
theorem mem_append_right {α : Type} {a : α} :
    ∀ (l : List α) {l' : List α}, a ∈ l' → a ∈ l ++ l'
  | [], _, h => h
  | z :: t, _, h => List.Mem.tail z (mem_append_right t h)

/-- A member of a join sits on one of its two sides. -/
theorem mem_append_of {α : Type} {a : α} :
    ∀ (l l' : List α), a ∈ l ++ l' → a ∈ l ∨ a ∈ l'
  | [], _, h => Or.inr h
  | z :: t, l', h => by
    have h' : a ∈ z :: (t ++ l') := h
    cases h' with
    | head => exact Or.inl (List.Mem.head t)
    | tail _ hm =>
      cases mem_append_of t l' hm with
      | inl hl => exact Or.inl (List.Mem.tail z hl)
      | inr hr => exact Or.inr hr

/-- A member's own member joins the flattened family. -/
theorem mem_flatMap_to {α β : Type} (f : α → List β) {a : α}
    {x : β} : ∀ {l : List α}, a ∈ l → x ∈ f a → x ∈ l.flatMap f
  | [], h, _ => nomatch h
  | z :: t, h, hx => by
    have h' : a ∈ z :: t := h
    show x ∈ f z ++ t.flatMap f
    cases h' with
    | head => exact mem_append_left (t.flatMap f) hx
    | tail _ hm => exact mem_append_right (f z) (mem_flatMap_to f hm hx)

/-- A member of a flattened family names the source it came
from. -/
theorem mem_flatMap_of {α β : Type} (f : α → List β) :
    ∀ (l : List α) (x : β), x ∈ l.flatMap f →
      ∃ a, a ∈ l ∧ x ∈ f a
  | [], _, h => nomatch h
  | z :: t, x, h => by
    have h' : x ∈ f z ++ t.flatMap f := h
    cases mem_append_of (f z) (t.flatMap f) h' with
    | inl hz => exact ⟨z, List.Mem.head t, hz⟩
    | inr ht =>
      match mem_flatMap_of f t x ht with
      | ⟨a, ha, hax⟩ => exact ⟨a, List.Mem.tail z ha, hax⟩

/-- A member reading the predicate true survives the filter. -/
theorem mem_filter_to {α : Type} (p : α → Bool) {x : α} :
    ∀ {l : List α}, x ∈ l → p x = true → x ∈ l.filter p
  | [], h, _ => nomatch h
  | z :: t, h, hp => by
    have h' : x ∈ z :: t := h
    cases h' with
    | head =>
      rw [List.filter_cons_of_pos hp]
      exact List.Mem.head (t.filter p)
    | tail _ hm =>
      by_cases hpz : p z = true
      · rw [List.filter_cons_of_pos hpz]
        exact List.Mem.tail z (mem_filter_to p hm hp)
      · rw [List.filter_cons_of_neg hpz]
        exact mem_filter_to p hm hp

/-- A member of a filtered family is a member reading the predicate
true. -/
theorem mem_filter_of {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l.filter p → x ∈ l ∧ p x = true
  | [], _, h => nomatch h
  | z :: t, x, h => by
    by_cases hpz : p z = true
    · rw [List.filter_cons_of_pos hpz] at h
      have h' : x ∈ z :: t.filter p := h
      cases h' with
      | head => exact ⟨List.Mem.head t, hpz⟩
      | tail _ hm =>
        match mem_filter_of p t x hm with
        | ⟨hx, hpx⟩ => exact ⟨List.Mem.tail z hx, hpx⟩
    · rw [List.filter_cons_of_neg hpz] at h
      match mem_filter_of p t x h with
      | ⟨hx, hpx⟩ => exact ⟨List.Mem.tail z hx, hpx⟩

/-- A distinct family's filter is distinct. -/
theorem distinctList_filter {α : Type} [DecidableEq α] (P : α → Bool)
    (l : List α) (h : distinctList l) : distinctList (l.filter P) := by
  intro x hx
  rw [countOf_filter P x l, if_pos (mem_filter_of P l x hx).2]
  exact h x (mem_filter_of P l x hx).1

/-- Two distinct families off each other join to a distinct
family. -/
theorem distinctList_append_disjoint {α : Type} [DecidableEq α]
    (u v : List α) (hu : distinctList u) (hv : distinctList v)
    (hdis : ∀ x, x ∈ u → x ∈ v → False) : distinctList (u ++ v) := by
  intro x hx
  rw [countOf_append]
  cases mem_append_of u v hx with
  | inl h1 =>
    rw [countOf_zero_of_not_mem (fun h2 => hdis x h1 h2), Nat.add_zero]
    exact hu x h1
  | inr h2 =>
    rw [countOf_zero_of_not_mem (fun h1 => hdis x h1 h2), Nat.zero_add]
    exact hv x h2

/-- A member reads the membership test true. -/
theorem containsB_of_mem {α : Type} [DecidableEq α] {x : α}
    {l : List α} (h : x ∈ l) : containsB l x = true :=
  decide_eq_true (countOf_pos_of_mem h)

/-- The membership test's passing read names a member. -/
theorem mem_of_containsB {α : Type} [DecidableEq α] {x : α}
    {l : List α} (h : containsB l x = true) : x ∈ l :=
  mem_of_countOf_pos x l (of_decide_eq_true h)

/-- A key off the family reads the membership test false. -/
theorem containsB_of_not_mem {α : Type} [DecidableEq α] {x : α}
    {l : List α} (h : ¬ x ∈ l) : containsB l x = false := by
  cases hc : containsB l x with
  | false => rfl
  | true => exact absurd (mem_of_containsB hc) h

/-- The membership test at a filtered family reads a member's own
guard. -/
theorem containsB_filter_mem {α : Type} [DecidableEq α]
    (P : α → Bool) (l : List α) (x : α) (hx : x ∈ l) :
    containsB (l.filter P) x = P x := by
  cases hp : P x with
  | true => exact containsB_of_mem (mem_filter_to P hx hp)
  | false =>
    refine containsB_of_not_mem (fun hm => ?_)
    have h := (mem_filter_of P l x hm).2
    rw [hp] at h
    exact Bool.noConfusion h

/-- A member's occupied image joins the keyed family. -/
theorem mem_filterMap_to {α β : Type} (f : α → Option β) {a : α}
    {b : β} : ∀ {l : List α}, a ∈ l → f a = some b →
      b ∈ l.filterMap f
  | [], h, _ => nomatch h
  | z :: t, h, hf => by
    cases h with
    | head =>
      have hx : List.filterMap f (a :: t) = b :: t.filterMap f := by
        show (match f a with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = b :: t.filterMap f
        rw [hf]
      rw [hx]
      exact List.Mem.head (t.filterMap f)
    | tail _ hm =>
      cases hz : f z with
      | none =>
        have hx : List.filterMap f (z :: t) = t.filterMap f := by
          show (match f z with
                | none => t.filterMap f
                | some d => d :: t.filterMap f) = t.filterMap f
          rw [hz]
        rw [hx]
        exact mem_filterMap_to f hm hf
      | some c =>
        have hx : List.filterMap f (z :: t) = c :: t.filterMap f := by
          show (match f z with
                | none => t.filterMap f
                | some d => d :: t.filterMap f) = c :: t.filterMap f
          rw [hz]
        rw [hx]
        exact List.Mem.tail c (mem_filterMap_to f hm hf)

/-- A member of a keyed family names the source whose image it
is, `mem_filterMap_to`'s converse. -/
theorem mem_filterMap_of {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (b : β), b ∈ l.filterMap f →
      ∃ a, a ∈ l ∧ f a = some b
  | [], _, h => nomatch h
  | z :: t, b, h => by
    cases hz : f z with
    | none =>
      have hx : List.filterMap f (z :: t) = t.filterMap f := by
        show (match f z with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = t.filterMap f
        rw [hz]
      rw [hx] at h
      match mem_filterMap_of f t b h with
      | ⟨a, ha, hfa⟩ => exact ⟨a, List.Mem.tail z ha, hfa⟩
    | some c =>
      have hx : List.filterMap f (z :: t) = c :: t.filterMap f := by
        show (match f z with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = c :: t.filterMap f
        rw [hz]
      rw [hx] at h
      have h' : b ∈ c :: t.filterMap f := h
      cases h' with
      | head => exact ⟨z, List.Mem.head t, by rw [hz]⟩
      | tail _ hm =>
        match mem_filterMap_of f t b hm with
        | ⟨a, ha, hfa⟩ => exact ⟨a, List.Mem.tail z ha, hfa⟩

/-- A member reading a predicate true folds the occupancy read to
its own true. -/
theorem any_of_mem {α : Type} (f : α → Bool) {x : α} :
    ∀ {l : List α}, x ∈ l → f x = true → l.any f = true
  | [], h, _ => nomatch h
  | z :: t, h, hf => by
    cases h with
    | head =>
      show (f x || t.any f) = true
      rw [hf]
      rfl
    | tail _ hm =>
      show (f z || t.any f) = true
      rw [any_of_mem f hm hf]
      cases f z <;> rfl

/-- The any-fold over a mapped family is the fold at the
composite. -/
theorem any_map {α β : Type} (f : α → β) (g : β → Bool) :
    ∀ (l : List α), (l.map f).any g = l.any (fun a => g (f a))
  | [] => rfl
  | a :: t => by
    show (g (f a) || (t.map f).any g) = (g (f a) || t.any (fun a => g (f a)))
    rw [any_map f g t]

/-- Two occupancy folds at pointwise equal reads are one value. -/
theorem any_congr_all {α : Type} (f g : α → Bool) (h : ∀ x, f x = g x) :
    ∀ l : List α, l.any f = l.any g
  | [] => rfl
  | a :: t => by
    show (f a || t.any f) = (g a || t.any g)
    rw [h a, any_congr_all f g h t]

/-- A fold over a mapped family is the fold at the composite step. -/
theorem foldl_map {α β γ : Type} (f : α → β) (g : γ → β → γ) :
    ∀ (l : List α) (a : γ), (l.map f).foldl g a = l.foldl (fun a u => g a (f u)) a
  | [], _ => rfl
  | _ :: t, _ => foldl_map f g t _

/-- A left fold preserves a predicate carried by its seed and
kept by every listed step. -/
theorem foldl_invariant {α β : Type} (P : β → Prop) (step : β → α → β) :
    ∀ (l : List α) (s : β), P s → (∀ x ∈ l, ∀ a, P a → P (step a x)) → P (l.foldl step s)
  | [], _, hs, _ => hs
  | x :: l, s, hs, hstep =>
    foldl_invariant P step l (step s x) (hstep x (List.Mem.head l) s hs)
      (fun y hy a ha => hstep y (List.Mem.tail x hy) a ha)


/-- An optional accumulating sum whose listed steps all return
their stated summands returns the finite sum at its seed. -/
theorem foldl_some_sum {α : Type} (step : Option BPair → α → Option BPair) (f : α → BPair) :
    ∀ (l : List α) (a : BPair),
      (∀ x ∈ l, ∀ b, ∃ c, step (some b) x = some c ∧ c.oneValue (b + f x)) →
      ∃ b, l.foldl step (some a) = some b ∧ b.oneValue (a + ground.famFold BPair.add BPair.unit f l)
  | [], a, _ => ⟨a, rfl, BPair.oneValue_symm (BPair.add_unit a)⟩
  | x :: l, a, h => by
    obtain ⟨b, hb, hv⟩ := h x (List.Mem.head l) a
    obtain ⟨c, hc, hw⟩ := foldl_some_sum step f l b (fun y hy => h y (List.Mem.tail x hy))
    refine ⟨c, ?_, ?_⟩
    · change l.foldl step (step (some a) x) = some c
      rw [hb]
      exact hc
    · exact BPair.oneValue_trans hw (BPair.oneValue_trans
        (BPair.add_congr hv (BPair.oneValue_refl _))
        (BPair.oneValue_of_eq (BPair.add_assoc a (f x) (ground.famFold BPair.add BPair.unit f l))))

/-- A left fold moves across its seed's read, the step's
congruence in the accumulator the one consumed law. -/
theorem foldl_congr_seed {α β : Type} (ov : β → β → Prop)
    (op : β → α → β)
    (hop : ∀ {a b : β} (x : α), ov a b → ov (op a x) (op b x)) :
    ∀ (l : List α) {a b : β}, ov a b → ov (l.foldl op a) (l.foldl op b)
  | [], _, _, h => h
  | x :: t, _, _, h => foldl_congr_seed ov op hop t (hop x h)

/-- A passing fold names an index: the first passing member's own
key, the read at the stated default. -/
theorem getAt_of_any {α : Type} (f : α → Bool) (d : α) :
    ∀ l : List α, l.any f = true →
      ∃ i, i < l.length ∧ f (getAt d l i) = true
  | [], h => Bool.noConfusion h
  | z :: t, h => by
    cases hz : f z with
    | true => exact ⟨0, Nat.succ_pos _, hz⟩
    | false =>
      have h' : t.any f = true := by
        have h0 : (f z || t.any f) = true := h
        rw [hz] at h0
        exact h0
      have ⟨i, hi, hf⟩ := getAt_of_any f d t h'
      exact ⟨i + 1, Nat.succ_lt_succ hi, hf⟩

/-- A fold's join reads either part's fold. -/
theorem any_append {α : Type} (f : α → Bool) :
    ∀ u v : List α, (u ++ v).any f = (u.any f || v.any f)
  | [], _ => rfl
  | a :: u, v => by
    show (f a || (u ++ v).any f) = (f a || u.any f || v.any f)
    rw [any_append f u v, Bool.or_assoc]

/-- Two folds agreeing at every member agree. -/
theorem any_congr_of_mem {α : Type} (f g : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    show (f a || l.any f) = (g a || l.any g)
    rw [h a (List.Mem.head l),
      any_congr_of_mem f g l (fun x hx => h x (List.Mem.tail a hx))]

/-- A list off every member is the vacant list. -/
theorem nil_of_not_mem {α : Type} (l : List α) (h : ∀ x, ¬ x ∈ l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t => exact absurd (List.Mem.head t) (h a)

/-- An occupied fold exhibits its member. -/
theorem mem_of_any {α : Type} (f : α → Bool) :
    ∀ l : List α, l.any f = true → ∃ x, x ∈ l ∧ f x = true
  | [], h => Bool.noConfusion h
  | z :: t, h => by
    cases hz : f z with
    | true => exact ⟨z, List.Mem.head t, hz⟩
    | false =>
      have h' : t.any f = true := by
        have h0 : (f z || t.any f) = true := h
        rw [hz] at h0
        exact h0
      match mem_of_any f t h' with
      | ⟨x, hx, hfx⟩ => exact ⟨x, List.Mem.tail z hx, hfx⟩

/-- A vacant keyed image refuses every occupied key: no source
member reads a value. -/
theorem filterMap_none {α β : Type} [DecidableEq α]
    (f : α → Option β) : ∀ l : List α,
    (l.filterMap f).length = 0 → ∀ e, 0 < countOf e l → f e = none
  | [], _, _, he => absurd he (Nat.lt_irrefl 0)
  | x :: t, h, e, he => by
    cases hf : f x with
    | some c =>
      have hx : List.filterMap f (x :: t) = c :: t.filterMap f := by
        show (match f x with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = c :: t.filterMap f
        rw [hf]
      rw [hx] at h
      exact Nat.noConfusion h
    | none =>
      have hx : List.filterMap f (x :: t) = t.filterMap f := by
        show (match f x with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = t.filterMap f
        rw [hf]
      rw [hx] at h
      by_cases hex : e = x
      · rw [hex]
        exact hf
      · rw [countOf_head_ne hex] at he
        exact filterMap_none f t h e he

/-- The keyed image reads through maps agreeing at every occupied
member. -/
theorem filterMap_congr_members {α β : Type} [DecidableEq α]
    (f g : α → Option β) : ∀ l : List α,
    (∀ e, 0 < countOf e l → f e = g e) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | e :: t, h => by
    have he : f e = g e :=
      h e (by rw [countOf_head]; exact Nat.succ_pos _)
    have ht : t.filterMap f = t.filterMap g :=
      filterMap_congr_members f g t (fun x hx => h x (countOf_cons_pos hx))
    rw [List.filterMap_cons, List.filterMap_cons, he, ht]

/-- A one-key image over a family off the key is vacant. -/
theorem filterMap_key_off {α β : Type} [DecidableEq α] (b : α) (v : β) :
    ∀ l : List α, countOf b l = 0 →
      l.filterMap (fun c => if c = b then some v else none) = []
  | [], _ => rfl
  | c :: t, h => by
    have hc : ¬ c = b := fun hc => by
      rw [hc, countOf_head] at h
      exact Nat.noConfusion h
    rw [List.filterMap_cons, if_neg hc]
    exact filterMap_key_off b v t (by
      rw [countOf_head_ne (fun h' => hc h'.symm)] at h
      exact h)

/-- A one-key image over a family holding its key once reads the
key's value alone. -/
theorem filterMap_key_once {α β : Type} [DecidableEq α] (b : α) (v : β) :
    ∀ l : List α, countOf b l = 1 →
      l.filterMap (fun c => if c = b then some v else none) = [v]
  | [], h => Nat.noConfusion h
  | c :: t, h => by
    by_cases hc : c = b
    · rw [hc, countOf_head] at h
      rw [List.filterMap_cons, if_pos hc, filterMap_key_off b v t (Nat.succ.inj h)]
    · rw [List.filterMap_cons, if_neg hc]
      exact filterMap_key_once b v t (by
        rw [countOf_head_ne (fun h' => hc h'.symm)] at h
        exact h)

/-- An occupied image key names its source member. -/
theorem filterMap_pre {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → Option β) :
    ∀ (l : List α) (y : β),
    0 < countOf y (l.filterMap f) →
      ∃ x, 0 < countOf x l ∧ f x = some y
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | x :: t, y, h => by
    cases hf : f x with
    | none =>
      have hx : List.filterMap f (x :: t) = t.filterMap f := by
        show (match f x with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = t.filterMap f
        rw [hf]
      rw [hx] at h
      obtain ⟨z, hz, hfz⟩ := filterMap_pre f t y h
      exact ⟨z, countOf_cons_pos hz, hfz⟩
    | some c =>
      have hx : List.filterMap f (x :: t) = c :: t.filterMap f := by
        show (match f x with
              | none => t.filterMap f
              | some d => d :: t.filterMap f) = c :: t.filterMap f
        rw [hf]
      rw [hx] at h
      by_cases hyc : y = c
      · exact ⟨x, by rw [countOf_head]; exact Nat.succ_pos _,
          by rw [hf, hyc]⟩
      · rw [countOf_head_ne hyc] at h
        obtain ⟨z, hz, hfz⟩ := filterMap_pre f t y h
        exact ⟨z, countOf_cons_pos hz, hfz⟩

/-- A keyed image counts a value at most once where the source
counts each member at most once and the emission distinguishes its
sources. -/
theorem countOf_filterMap_le_one {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → Option β) (y : β) :
    ∀ l : List α, (∀ a, countOf a l ≤ 1) →
      (∀ a b, 0 < countOf a l → 0 < countOf b l →
        f a = some y → f b = some y → a = b) →
      countOf y (l.filterMap f) ≤ 1
  | [], _, _ => Nat.zero_le 1
  | x :: t, hc, hinj => by
    have hct : ∀ a, countOf a t ≤ 1 := fun a =>
      Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _)
        (Nat.le_of_eq (countOf_cons a x t).symm)) (hc a)
    have hinjt : ∀ a b, 0 < countOf a t → 0 < countOf b t →
        f a = some y → f b = some y → a = b := fun a b ha hb =>
      hinj a b (countOf_cons_pos ha) (countOf_cons_pos hb)
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
      rw [hx, countOf_cons]
      by_cases hyz : y = z
      · have hzero : countOf y (t.filterMap f) = 0 := by
          match Nat.eq_zero_or_pos (countOf y (t.filterMap f)) with
          | .inl h0 => exact h0
          | .inr hp =>
            obtain ⟨w, hw, hfw⟩ := filterMap_pre f t y hp
            have hwx : w = x := hinj w x (countOf_cons_pos hw)
              (by rw [countOf_head]; exact Nat.succ_pos _)
              hfw (by rw [hf, hyz])
            rw [hwx] at hw
            have hle : countOf x t + 1 ≤ 1 := by
              rw [← countOf_head x t]
              exact hc x
            exact absurd (Nat.lt_of_lt_of_le hw
              (Nat.le_of_succ_le_succ hle)) (Nat.lt_irrefl 0)
        rw [if_pos hyz, hzero]
        exact Nat.le_refl 1
      · rw [if_neg hyz, Nat.zero_add]
        exact countOf_filterMap_le_one f y t hct hinjt

/-- A filter at one matching member of a distinct list reads that
member alone: its length is one. -/
theorem filter_single {α : Type} [DecidableEq α] (p : α → Bool) (x : α) :
    ∀ l : List α, x ∈ l → (∀ y, y ∈ l → p y = true → y = x) →
      p x = true → countOf x l ≤ 1 → (l.filter p).length = 1
  | [], hx, _, _, _ => nomatch hx
  | y :: t, hx, hall, hpx, hc => by
    by_cases hyx : y = x
    · rw [hyx] at hc ⊢
      rw [filter_cons_true hpx]
      have hxt : countOf x t = 0 := by
        have h1 : countOf x t + 1 ≤ 1 := by
          rw [← countOf_head x t]
          exact hc
        exact Nat.le_antisymm (Nat.le_of_succ_le_succ h1) (Nat.zero_le _)
      have hnil : t.filter p = [] := by
        cases hl : t.filter p with
        | nil => rfl
        | cons z r =>
          have hz : z ∈ t.filter p := by
            rw [hl]
            exact List.Mem.head _
          obtain ⟨hzt, hpz⟩ := mem_filter_of p t z hz
          have hzx : z = x := hall z (List.Mem.tail _ hzt) hpz
          rw [hzx] at hzt
          have := countOf_pos_of_mem hzt
          rw [hxt] at this
          exact absurd this (Nat.lt_irrefl 0)
      rw [hnil]
      rfl
    · have hpy : p y = false := by
        cases hp : p y with
        | false => rfl
        | true => exact absurd (hall y (List.Mem.head _) hp) hyx
      rw [filter_cons_false hpy]
      have hxt : x ∈ t := by
        cases hx with
        | head => exact absurd rfl hyx
        | tail _ h => exact h
      exact filter_single p x t hxt (fun z hz => hall z (List.Mem.tail _ hz))
        hpx (Nat.le_trans (countOf_cons_le x y t) hc)

/-- A cons map at a varying head over one tail counts a list at
its head's count at the one matching tail, the vacant read at every
other tail. -/
theorem countOf_consMapTail {α : Type} [DecidableEq α] (l0 : α)
    (b0 b : List α) (ls : List α) :
    countOf (l0 :: b0) (ls.map (fun l => l :: b))
      = if b0 = b then countOf l0 ls else 0 := by
  by_cases hb : b0 = b
  · rw [if_pos hb, hb]
    exact countOf_map_inj (fun l => l :: b) l0 ls
      (fun x _ hx => (List.cons.inj hx).1)
  · rw [if_neg hb]
    exact countOf_map_none _ _ ls (fun x _ hx => hb (List.cons.inj hx).2.symm)

/-- A member's count sits at or below the family's length. -/
theorem countOf_le_length {α : Type} [DecidableEq α] (x : α) :
    ∀ l : List α, countOf x l ≤ l.length
  | [] => Nat.le_refl 0
  | a :: t => by
    rw [countOf_cons]
    by_cases h : x = a
    · rw [if_pos h, Nat.add_comm]
      exact Nat.succ_le_succ (countOf_le_length x t)
    · rw [if_neg h, Nat.zero_add]
      exact Nat.le_succ_of_le (countOf_le_length x t)

/-- The one-valued map reads the replicate. -/
theorem map_const {α β : Type} (c : β) : ∀ l : List α,
    l.map (fun _ => c) = List.replicate l.length c
  | [] => rfl
  | _ :: l => by
    show c :: l.map (fun _ => c) = c :: List.replicate l.length c
    rw [map_const c l]

/-- Two maps at one read per member are one family. -/
theorem map_congr_all {α γ : Type} (f g : α → γ)
    (h : ∀ x, f x = g x) : ∀ l : List α, l.map f = l.map g
  | [] => rfl
  | a :: l => by
    show f a :: l.map f = g a :: l.map g
    rw [h a, map_congr_all f g h l]

/-- The unit join on the right reads the family back. -/
theorem append_nil {α : Type} : ∀ l : List α, l ++ [] = l
  | [] => rfl
  | a :: t => congrArg (List.cons a) (append_nil t)

/-- A family dropped at its own width is the seed family
(`List.drop_length` is propext-bearing; this is the clean
spelling). -/
theorem dropLength {α : Type} : ∀ l : List α, l.drop l.length = []
  | [] => rfl
  | _ :: t => dropLength t


/-- The occupied count's predecessor joins the successor across:
one member moved between two summands. -/
theorem subOneJoin (a b : Nat) (h : 0 < a) :
    a - 1 + (b + 1) = a + b := by
  match a, h with
  | 0, hh => exact absurd hh (Nat.lt_irrefl 0)
  | a' + 1, _ =>
    show a' + (b + 1) = a' + 1 + b
    rw [Nat.succ_add a' b]
    rfl

/-- A family at the vacant length is the seed list itself. -/
theorem nil_of_length_zero {α : Type} :
    ∀ l : List α, l.length = 0 → l = []
  | [], _ => rfl
  | _ :: _, h => Nat.noConfusion h

/-- The vacant family joins on the left as the unit summand,
entry by entry. -/
theorem zipWith_zero_left : ∀ (n : Nat) (b : List Nat),
    b.length = n →
    List.zipWith (fun x y => x + y) (List.replicate n 0) b = b
  | 0, [], _ => rfl
  | 0, _ :: _, h => Nat.noConfusion h
  | _ + 1, [], h => Nat.noConfusion h
  | n + 1, c :: t, h => by
    show (0 + c) :: List.zipWith (fun x y => x + y)
      (List.replicate n 0) t = c :: t
    rw [zipWith_zero_left n t (Nat.succ.inj h), Nat.zero_add]

/-- The repeated family grows at its tail by its own member. -/
theorem replicate_snoc {α : Type} (a : α) :
    ∀ n : Nat, List.replicate n a ++ [a] = List.replicate (n + 1) a
  | 0 => rfl
  | n + 1 => congrArg (List.cons a) (replicate_snoc a n)

/-- The repeated family's length is its count. -/
theorem length_replicate {α : Type} (a : α) :
    ∀ n : Nat, (List.replicate n a).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (length_replicate a n)

/-- The map reads through the repeated family. -/
theorem map_replicate {α β : Type} (f : α → β) (a : α) :
    ∀ n : Nat, (List.replicate n a).map f = List.replicate n (f a)
  | 0 => rfl
  | n + 1 => congrArg (List.cons (f a)) (map_replicate f a n)

/-- The exchange's tie witness: the unit places with the double at
the exchanged key and the vacancy at its successor. -/
theorem getAt_swapWit (k w : Nat) : ∀ t, t < k + (w + 2) →
    getAt 0
        (List.replicate k 1 ++ 2 :: 0 :: List.replicate w 1) t
      = if t = k then 2 else if t = k + 1 then 0 else 1 := by
  intro t ht
  have hrep : (List.replicate k (1 : Nat)).length = k :=
    length_replicate 1 k
  cases Nat.lt_or_ge t k with
  | inl hlt =>
    have hne2 : ¬ t = k + 1 := by
      intro he
      rw [he] at hlt
      exact Nat.lt_irrefl k (Nat.lt_of_succ_lt hlt)
    rw [getAt_append 0 (List.replicate k 1)
        (2 :: 0 :: List.replicate w 1) t,
      if_pos (show t < (List.replicate k (1 : Nat)).length from by
        rw [hrep]; exact hlt),
      getAt_replicate 0 1 k t hlt,
      if_neg (Nat.ne_of_lt hlt), if_neg hne2]
  | inr hge =>
    obtain ⟨r, hr⟩ := Nat.le.dest hge
    have hx := getAt_append_add 0 (List.replicate k 1)
      (2 :: 0 :: List.replicate w 1) r
    rw [hrep] at hx
    rw [← hr, hx]
    cases r with
    | zero =>
      rw [if_pos (show k + 0 = k from rfl)]
      rfl
    | succ r1 =>
      cases r1 with
      | zero =>
        rw [if_neg (Nat.succ_ne_self k), if_pos rfl]
        rfl
      | succ r2 =>
        have hne0 : ¬ k + (r2 + 1 + 1) = k := by
          intro he
          exact Nat.noConfusion (addCancelL k
            (show k + (r2 + 1 + 1) = k + 0 by
              rw [Nat.add_zero]; exact he))
        have hne1 : ¬ k + (r2 + 1 + 1) = k + 1 := by
          intro he
          exact Nat.noConfusion (Nat.succ.inj (addCancelL k he))
        have hr2 : r2 < w := by
          rw [← hr] at ht
          exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
            (Nat.lt_of_add_lt_add_left ht))
        rw [if_neg hne0, if_neg hne1]
        show getAt 0 (List.replicate w 1) r2 = 1
        exact getAt_replicate 0 1 w r2 hr2

/-- The keyed union splits over a joined family. -/
theorem flatMap_append {α β : Type} (f : α → List β) :
    ∀ u v : List α, (u ++ v).flatMap f = u.flatMap f ++ v.flatMap f
  | [], _ => rfl
  | x :: t, v => by
    show f x ++ (t ++ v).flatMap f
      = (f x ++ t.flatMap f) ++ v.flatMap f
    rw [flatMap_append f t v, append_assoc]

/-- A flattening at vacant member families is vacant. -/
theorem flatMap_nil {α β : Type} (f : α → List β) :
    ∀ l : List α, (∀ x ∈ l, f x = []) → l.flatMap f = []
  | [], _ => rfl
  | a :: t, h => by
    show f a ++ t.flatMap f = []
    rw [h a (List.Mem.head t)]
    exact flatMap_nil f t (fun x hx => h x (List.Mem.tail a hx))

/-- A map fixing every member reads the list itself. -/
theorem map_eq_self_of_mem {α : Type} (f : α → α) :
    ∀ l : List α, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: t, h => by
    show f x :: t.map f = x :: t
    rw [h x (List.Mem.head t), map_eq_self_of_mem f t (fun y hy => h y (List.Mem.tail x hy))]

/-- A map at the identity reads the list itself, the fixing map's
instance. -/
theorem map_id {α : Type} (l : List α) : l.map (fun x => x) = l :=
  map_eq_self_of_mem _ l (fun _ _ => rfl)

/-- The two-level join reading its first family back. -/
theorem zipWith2_left {α β : Type} (A : List (List α)) (S : List (List β))
    (h : A.length ≤ S.length)
    (hr : ∀ i, i < A.length →
      (getAt ([] : List α) A i).length ≤ (getAt ([] : List β) S i).length) :
    List.zipWith (List.zipWith (fun a _ => a)) A S = A := by
  rw [zipWith2_leftMap (fun a => a) A S h hr,
    map_congr_all _ _ (fun r => map_id r) A, map_id A]

/-- The two-level join reading its second family back. -/
theorem zipWith2_right {α β : Type} (A : List (List α)) (S : List (List β))
    (h : S.length ≤ A.length)
    (hr : ∀ i, i < S.length →
      (getAt ([] : List β) S i).length ≤ (getAt ([] : List α) A i).length) :
    List.zipWith (List.zipWith (fun _ b => b)) A S = S := by
  rw [zipWith2_rightMap (fun b => b) A S h hr,
    map_congr_all _ _ (fun r => map_id r) S, map_id S]

/-- The map reads through a keyed union, member family by member
family. -/
theorem map_flatMap {α β γ : Type} (f : α → List β) (g : β → γ) :
    ∀ l : List α, (l.flatMap f).map g = l.flatMap (fun x => (f x).map g)
  | [] => rfl
  | x :: t => by
    show (f x ++ t.flatMap f).map g
      = (f x).map g ++ t.flatMap (fun y => (f y).map g)
    rw [map_append g (f x) (t.flatMap f), map_flatMap f g t]

/-- Two keyed unions at one value per key read one value. -/
theorem flatMap_congr_all {α β : Type} (f g : α → List β)
    (h : ∀ a, f a = g a) : ∀ l : List α, l.flatMap f = l.flatMap g
  | [] => rfl
  | x :: t => by
    show f x ++ t.flatMap f = g x ++ t.flatMap g
    rw [h x, flatMap_congr_all f g h t]

/-- The filter passes into a flat map, row by row. -/
theorem filter_flatMap {α β : Type} (p : β → Bool) (h : α → List β) :
    ∀ l : List α, (l.flatMap h).filter p = l.flatMap (fun x => (h x).filter p)
  | [] => rfl
  | x :: t => by
    show (h x ++ t.flatMap h).filter p
      = (h x).filter p ++ t.flatMap (fun x => (h x).filter p)
    rw [filter_append, filter_flatMap p h t]

/-- A flat map over a filtered list is the flat map with the
filter's refusals read vacant. -/
theorem flatMap_filter {α β : Type} (q : α → Bool) (h : α → List β) :
    ∀ l : List α,
      (l.filter q).flatMap h = l.flatMap (fun x => if q x then h x else [])
  | [] => rfl
  | x :: t => by
    rw [filter_cons q x t]
    cases hq : q x with
    | true =>
      show h x ++ (t.filter q).flatMap h
        = (if q x then h x else []) ++ t.flatMap (fun x => if q x then h x else [])
      rw [if_pos hq, flatMap_filter q h t]
    | false =>
      show (t.filter q).flatMap h
        = (if q x then h x else []) ++ t.flatMap (fun x => if q x then h x else [])
      rw [if_neg (fun h' => Bool.false_ne_true (hq.symm.trans h')), flatMap_filter q h t]
      rfl

/-- A flat map at a family holding one key once, every further
member's row vacant, reads that key's row alone. -/
theorem flatMap_pick {α β : Type} [DecidableEq α] (h : α → List β)
    (a : α) : ∀ l : List α,
    (∀ x ∈ l, ¬ x = a → h x = []) → countOf a l = 1 → l.flatMap h = h a
  | [], _, hc => Nat.noConfusion hc
  | x :: t, hoff, hc => by
    have hc' : (if a = x then 1 else 0) + countOf a t = 1 :=
      (countOf_cons a x t).symm.trans hc
    show h x ++ t.flatMap h = h a
    by_cases hax : a = x
    · have ht : countOf a t = 0 := by
        rw [if_pos hax] at hc'
        exact addCancelL 1 (by rw [Nat.add_zero]; exact hc')
      rw [← hax, flatMap_nil h t (fun y hy => hoff y (List.Mem.tail x hy)
        (fun hya => Nat.lt_irrefl 0 (by
          have := countOf_pos_of_mem (hya ▸ hy : a ∈ t)
          rw [ht] at this
          exact this))), append_nil]
    · rw [hoff x (List.Mem.head t) (fun he => hax he.symm)]
      show t.flatMap h = h a
      rw [if_neg hax, Nat.zero_add] at hc'
      exact flatMap_pick h a t (fun y hy => hoff y (List.Mem.tail x hy)) hc'

/-- A keyed union over a mapped family reads at the images. -/
theorem flatMap_map {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ l : List α, (l.map f).flatMap g = l.flatMap (fun x => g (f x))
  | [] => rfl
  | x :: t => by
    show g (f x) ++ (t.map f).flatMap g
      = g (f x) ++ t.flatMap (fun y => g (f y))
    rw [flatMap_map f g t]

/-- The erasure at an in-range key drops the length by one, the
successor spelling. -/
theorem length_eraseIdx {α : Type} :
    ∀ (l : List α) (j : Nat), j < l.length →
      (l.eraseIdx j).length + 1 = l.length
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: t, j + 1, h =>
    congrArg Nat.succ (length_eraseIdx t j (Nat.lt_of_succ_lt_succ h))

/-- A mapped family's erasure is the erased family's map. -/
theorem eraseIdx_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (k : Nat),
      (l.map f).eraseIdx k = (l.eraseIdx k).map f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | a :: l, k + 1 => by
    show f a :: (l.map f).eraseIdx k = f a :: (l.eraseIdx k).map f
    rw [eraseIdx_map f l k]

/-- The maps compose. -/
theorem map_map {α γ δ : Type} (f : α → γ) (g : γ → δ) :
    ∀ l : List α, (l.map f).map g = l.map (fun x => g (f x))
  | [] => rfl
  | a :: l => by
    show g (f a) :: (l.map f).map g = g (f a) :: l.map (fun x => g (f x))
    rw [map_map f g l]

/-- Two maps at one read per occupied member are one family. -/
theorem map_congr_members {α γ : Type} [DecidableEq α]
    (f g : α → γ) :
    ∀ l : List α, (∀ x, 0 < countOf x l → f x = g x) →
      l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    show f a :: l.map f = g a :: l.map g
    rw [h a (by rw [countOf_head]; exact Nat.succ_pos _),
      map_congr_members f g l (fun x hx =>
        h x (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))]

/-- Two folds at one read per member are one value. -/
theorem famFold_congr_all {α β : Type} (add : β → β → β) (unit : β)
    (f g : α → β) (h : ∀ x, f x = g x) :
    ∀ l : List α, famFold add unit f l = famFold add unit g l
  | [] => rfl
  | a :: l => by
    show add (f a) (famFold add unit f l)
      = add (g a) (famFold add unit g l)
    rw [h a, famFold_congr_all add unit f g h l]

/-! The raise's counts and the descent's cap: a strictly descending
family carries every value at most once, and the raise at a key
trades one occurrence of the key's entry for one of its successor,
every other value's count untouched. -/

/-- A strictly descending display reads across every index gap. -/
theorem desc_lt {b : List Nat}
    (hd : ∀ i, i + 1 < b.length →
      getAt 0 b (i + 1) < getAt 0 b i) :
    ∀ (k j : Nat), j < k → k < b.length →
    getAt 0 b k < getAt 0 b j
  | 0, j, hjk, _ => absurd hjk (Nat.not_lt_zero j)
  | k + 1, j, hjk, hkl =>
    match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hjk) with
    | .inl he => by rw [he]; exact hd k hkl
    | .inr hlt =>
      Nat.lt_trans (hd k hkl)
        (desc_lt hd k j hlt (Nat.lt_of_succ_lt hkl))

/-- A strictly descending family names its places back: one place
per value. -/
theorem desc_inj {l : List Nat}
    (hd : ∀ i, i + 1 < l.length →
      getAt 0 l (i + 1) < getAt 0 l i)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length)
    (he : getAt 0 l i = getAt 0 l j) : i = j := by
  cases Nat.lt_or_ge i j with
  | inl hlt =>
    exact absurd (desc_lt hd j i hlt hj)
      (by rw [he]; exact Nat.lt_irrefl _)
  | inr hge =>
    cases Nat.lt_or_ge j i with
    | inl hlt =>
      exact absurd (desc_lt hd i j hlt hi)
        (by rw [he]; exact Nat.lt_irrefl _)
    | inr hge' => exact Nat.le_antisymm hge' hge

/-- A memberwise descending list descends across every step
count. -/
theorem descChain (W : List Nat)
    (hs : ∀ i, getAt 0 W (i + 1) ≤ getAt 0 W i) (s : Nat) :
    ∀ k, getAt 0 W (s + k) ≤ getAt 0 W s
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_trans (hs (s + k)) (descChain W hs s k)

/-- Two weakly descending families with equal occurrence counts
are the same list, including repeated and zero entries. -/
theorem descLeUnique : ∀ (z y : List Nat),
    z.length = y.length →
    (∀ i, i + 1 < z.length → getAt 0 z (i + 1) ≤ getAt 0 z i) →
    (∀ i, i + 1 < y.length → getAt 0 y (i + 1) ≤ getAt 0 y i) →
    (∀ v, countOf v z = countOf v y) → z = y
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _, _, _ => Nat.noConfusion hl
  | a :: zs, b :: ys, hl, hdz, hdy, hc => by
    have headLe (u w : List Nat)
        (hd : ∀ i, i + 1 < w.length → getAt 0 w (i + 1) ≤ getAt 0 w i)
        (hcount : ∀ x, countOf x u = countOf x w)
        (x : Nat) (hx : 0 < countOf x u) : x ≤ getAt 0 w 0 := by
      have hp : 0 < countOf x w := by rw [← hcount x]; exact hx
      obtain ⟨i, _, hi⟩ := getAt_of_mem 0 (mem_of_countOf_pos x w hp)
      have h := descChain w (sortedAll w hd) 0 i
      rw [Nat.zero_add, hi] at h
      exact h
    have hab : a = b := Nat.le_antisymm
      (headLe (a :: zs) (b :: ys) hdy hc a (by rw [countOf_head]; exact Nat.succ_pos _))
      (headLe (b :: ys) (a :: zs) hdz (fun x => (hc x).symm) b
        (by rw [countOf_head]; exact Nat.succ_pos _))
    have hct : ∀ v, countOf v zs = countOf v ys := by
      intro v
      have h := hc v
      rw [countOf_cons, countOf_cons, hab] at h
      exact addCancelL _ h
    rw [hab, descLeUnique zs ys (Nat.succ.inj hl)
      (fun i hi => hdz (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hdy (i + 1) (Nat.succ_lt_succ hi)) hct]

/-- Two strictly descending families at one member count are one
family: the sorted key is the content's own spelling. -/
theorem descUnique (z y : List Nat) (hl : z.length = y.length)
    (hdz : ∀ i, i + 1 < z.length → getAt 0 z (i + 1) < getAt 0 z i)
    (hdy : ∀ i, i + 1 < y.length → getAt 0 y (i + 1) < getAt 0 y i)
    (hc : ∀ v, countOf v z = countOf v y) : z = y :=
  descLeUnique z y hl (fun i hi => Nat.le_of_lt (hdz i hi))
    (fun i hi => Nat.le_of_lt (hdy i hi)) hc

/-- A descending family's head is absent from its tail. -/
private theorem countOf_desc_head : ∀ (a : Nat) (t : List Nat),
    (∀ i, i + 1 < (a :: t).length →
      getAt 0 (a :: t) (i + 1) < getAt 0 (a :: t) i) →
    countOf a t = 0
  | a, t, hd => by
    match hc : countOf a t with
    | 0 => rfl
    | n + 1 =>
      have hpos : 0 < countOf a t := by
        rw [hc]
        exact Nat.succ_pos n
      obtain ⟨k, hk, hget⟩ :=
        getAt_of_mem 0 (mem_of_countOf_pos a t hpos)
      have hlt : getAt 0 t k < a :=
        desc_lt hd (k + 1) 0 (Nat.succ_pos k) (Nat.succ_lt_succ hk)
      rw [hget] at hlt
      exact absurd hlt (Nat.lt_irrefl a)

/-- A strictly descending family carries every value at most once:
the descent refuses a repeat. -/
theorem countOf_desc_le (z : List Nat)
    (hz : ∀ i, i + 1 < z.length →
      getAt 0 z (i + 1) < getAt 0 z i) (v : Nat) :
    countOf v z ≤ 1 := by
  match z, hz with
  | [], _ => exact Nat.le_succ 0
  | a :: t, hz =>
    by_cases hva : v = a
    · rw [hva, countOf_head, countOf_desc_head a t hz]
      exact Nat.le_refl 1
    · rw [countOf_head_ne hva]
      exact countOf_desc_le t
        (fun i hi => hz (i + 1) (Nat.succ_lt_succ hi)) v

/-- The raise gains one occurrence of the raised entry's
successor. -/
theorem countOf_bumpAt_top : ∀ (i : Nat) (l : List Nat),
    i < l.length →
    countOf (getAt 0 l i + 1) (bumpAt i l)
      = countOf (getAt 0 l i + 1) l + 1
  | _, [], hi => absurd hi (Nat.not_lt_zero _)
  | 0, a :: t, _ => by
    show countOf (a + 1) ((a + 1) :: t) = countOf (a + 1) (a :: t) + 1
    rw [countOf_head, countOf_head_ne (Nat.ne_of_gt (Nat.lt_succ_self a))]
  | i + 1, a :: t, hi => by
    have hit : i < t.length := Nat.lt_of_succ_lt_succ hi
    show countOf (getAt 0 t i + 1) (a :: bumpAt i t)
      = countOf (getAt 0 t i + 1) (a :: t) + 1
    rw [countOf_cons, countOf_cons, countOf_bumpAt_top i t hit,
      Nat.add_assoc (if getAt 0 t i + 1 = a then 1 else 0)
        (countOf (getAt 0 t i + 1) t) 1]

/-- The raise loses one occurrence of the raised entry. -/
theorem countOf_bumpAt_at : ∀ (i : Nat) (l : List Nat),
    i < l.length →
    countOf (getAt 0 l i) (bumpAt i l) + 1
      = countOf (getAt 0 l i) l
  | _, [], hi => absurd hi (Nat.not_lt_zero _)
  | 0, a :: t, _ => by
    show countOf a ((a + 1) :: t) + 1 = countOf a (a :: t)
    rw [countOf_head,
      countOf_head_ne (fun h : a = a + 1 =>
        Nat.ne_of_gt (Nat.lt_succ_self a) h.symm)]
  | i + 1, a :: t, hi => by
    have hit : i < t.length := Nat.lt_of_succ_lt_succ hi
    show countOf (getAt 0 t i) (a :: bumpAt i t) + 1
      = countOf (getAt 0 t i) (a :: t)
    rw [countOf_cons, countOf_cons,
      Nat.add_assoc (if getAt 0 t i = a then 1 else 0)
        (countOf (getAt 0 t i) (bumpAt i t)) 1,
      countOf_bumpAt_at i t hit]

/-- The raise passes through the componentwise sum at its first
summand. -/
theorem bumpAt_zipWith_left : ∀ (i : Nat) (a b : List Nat),
    List.zipWith (fun x y => x + y) (bumpAt i a) b
      = bumpAt i (List.zipWith (fun x y => x + y) a b) :=
  fun i a b =>
    editAt_zipWith_left (fun x => x + 1) i a b
      (Nat.add_right_comm (getAt 0 a i) 1 (getAt 0 b i))

/-- The raise passes through the componentwise sum at its second
summand. -/
theorem bumpAt_zipWith_right : ∀ (i : Nat) (a b : List Nat),
    List.zipWith (fun x y => x + y) a (bumpAt i b)
      = bumpAt i (List.zipWith (fun x y => x + y) a b) :=
  fun i a b =>
    editAt_zipWith_right (fun x => x + 1) i a b
      ((Nat.add_assoc (getAt 0 a i) (getAt 0 b i) 1).symm)

/-- Off the raised entry and its successor the raise keeps every
value's count. -/
theorem countOf_bumpAt_ne : ∀ (i : Nat) (l : List Nat) (v : Nat),
    ¬ v = getAt 0 l i → ¬ v = getAt 0 l i + 1 →
    countOf v (bumpAt i l) = countOf v l
  | i, [], _, _, _ => by rw [bumpAt_nil i]
  | 0, a :: t, v, h1, h2 => by
    have h1' : ¬ v = a := h1
    have h2' : ¬ v = a + 1 := h2
    show countOf v ((a + 1) :: t) = countOf v (a :: t)
    rw [countOf_head_ne h2', countOf_head_ne h1']
  | i + 1, a :: t, v, h1, h2 => by
    show countOf v (a :: bumpAt i t) = countOf v (a :: t)
    rw [countOf_cons, countOf_cons, countOf_bumpAt_ne i t v h1 h2]

/-! The keyed table: entries a key with its two graded counts, the
read the counts' sum over the matching keys, the insert merging at
key equality, and the merge the keyed merge (`mergeJoin`) at the
key equality and the counts' sum — the read blind to the order,
the fold's own sum at every shape. -/

/-- The table's read at a key test and a side: the matching
entries' counts' sum. -/
def tabRead {α : Type} (P : α → Bool) (s : Bool)
    (T : List (α × Nat × Nat)) : Nat :=
  famFold Nat.add 0
    (fun kv => if P kv.1 then (if s then kv.2.2 else kv.2.1) else 0)
    T

/-- The merging insert at key equality. -/
def tabAdd {α : Type} [DecidableEq α] :
    α × Nat × Nat → List (α × Nat × Nat) → List (α × Nat × Nat)
  | kv, [] => [kv]
  | kv, b :: T =>
    if kv.1 = b.1 then (b.1, kv.2.1 + b.2.1, kv.2.2 + b.2.2) :: T
    else b :: tabAdd kv T

/-- The insert moves the read by the entry's own. -/
theorem tabAdd_read {α : Type} [DecidableEq α] (P : α → Bool)
    (s : Bool) : ∀ (kv : α × Nat × Nat) (T : List (α × Nat × Nat)),
    tabRead P s (tabAdd kv T)
      = (if P kv.1 then (if s then kv.2.2 else kv.2.1) else 0)
        + tabRead P s T
  | _, [] => rfl
  | kv, b :: T => by
    show tabRead P s (if kv.1 = b.1
        then (b.1, kv.2.1 + b.2.1, kv.2.2 + b.2.2) :: T
        else b :: tabAdd kv T) = _
    by_cases h : kv.1 = b.1
    · rw [if_pos h]
      show (if P b.1 then (if s then kv.2.2 + b.2.2
          else kv.2.1 + b.2.1) else 0) + tabRead P s T
        = (if P kv.1 then (if s then kv.2.2 else kv.2.1) else 0)
          + ((if P b.1 then (if s then b.2.2 else b.2.1) else 0)
            + tabRead P s T)
      rw [h, ← Nat.add_assoc]
      by_cases hp : P b.1 = true
      · rw [if_pos hp, if_pos hp, if_pos hp]
        cases s with
        | true => rfl
        | false => rfl
      · rw [if_neg hp, if_neg hp, if_neg hp]
    · rw [if_neg h]
      show (if P b.1 then (if s then b.2.2 else b.2.1) else 0)
          + tabRead P s (tabAdd kv T)
        = (if P kv.1 then (if s then kv.2.2 else kv.2.1) else 0)
          + ((if P b.1 then (if s then b.2.2 else b.2.1) else 0)
            + tabRead P s T)
      rw [tabAdd_read P s kv T, Nat.add_left_comm]

/-- The insert-fold's read: the seed's read joined to the entries'
fold. -/
theorem tabAdd_fold_read {α β : Type} [DecidableEq α] (P : α → Bool)
    (s : Bool) (f : β → α × Nat × Nat) :
    ∀ (l : List β) (T : List (α × Nat × Nat)),
    tabRead P s (l.foldl (fun tab x => tabAdd (f x) tab) T)
      = tabRead P s T
        + famFold Nat.add 0 (fun x => if P (f x).1 then
            (if s then (f x).2.2 else (f x).2.1) else 0) l
  | [], _ => rfl
  | x :: l, T => by
    show tabRead P s (l.foldl _ (tabAdd (f x) T)) = _
    rw [tabAdd_fold_read P s f l (tabAdd (f x) T), tabAdd_read,
      Nat.add_assoc, Nat.add_left_comm]
    rfl

/-- The read adds over a joined table. -/
theorem tabRead_append {α : Type} (P : α → Bool) (s : Bool)
    (u v : List (α × Nat × Nat)) :
    tabRead P s (u ++ v) = tabRead P s u + tabRead P s v :=
  famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add _ u v

/-- The graded counts' sum, the two tables' join at one key. -/
def tabSum (p q : Nat × Nat) : Nat × Nat := (p.1 + q.1, p.2 + q.2)

/-- The merge at the tables' joined count: the keyed merge
(`mergeJoin`) at the key equality and the graded counts' sum. -/
def tabMerge {α : Type} [DecidableEq α] (lt : α → α → Bool)
    (u v : List (α × Nat × Nat)) : List (α × Nat × Nat) :=
  mergeJoin lt (fun a b => decide (a = b)) tabSum (u.length + v.length) u v

/-- The merge's read is the two tables' sum, at every fuel: the
merge's fold at the graded read (`mergeJoin_fold_ov`), a shared
key's joined counts reading the two counts' sum. -/
theorem mergeJoin_tabRead {α : Type} [DecidableEq α]
    (lt : α → α → Bool) (P : α → Bool) (s : Bool)
    (n : Nat) (u v : List (α × Nat × Nat)) :
    tabRead P s (mergeJoin lt (fun a b => decide (a = b)) tabSum n u v)
      = tabRead P s u + tabRead P s v :=
  mergeJoin_fold_ov natFoldLaws lt (fun a b => decide (a = b)) tabSum
    (fun kv => if P kv.1 then (if s then kv.2.2 else kv.2.1) else 0)
    (fun x y he => by
      have h : x.1 = y.1 := of_decide_eq_true he
      rw [← h]
      show (if P x.1 then (if s then x.2.2 + y.2.2 else x.2.1 + y.2.1) else 0)
        = (if P x.1 then (if s then x.2.2 else x.2.1) else 0)
          + (if P x.1 then (if s then y.2.2 else y.2.1) else 0)
      cases P x.1 with
      | true => cases s with | true => rfl | false => rfl
      | false => rfl) n u v

/-- The merge's read at the stated count. -/
theorem tabMerge_read {α : Type} [DecidableEq α]
    (lt : α → α → Bool) (P : α → Bool) (s : Bool)
    (u v : List (α × Nat × Nat)) :
    tabRead P s (tabMerge lt u v) = tabRead P s u + tabRead P s v :=
  mergeJoin_tabRead lt P s (u.length + v.length) u v

/-- A keyed list's read at a query key and a stated equality test:
the first matching entry's value, the stated default off the stored
keys. -/
def keyAt {α β : Type} (eq : α → α → Bool) (d : β) (c : α)
    (l : List (α × β)) : β :=
  l.foldr (fun e r => cond (eq e.1 c) e.2 r) d

/-- A store whose every entry holds a read's value at its key, read
back at a key with the read itself the default: a matching entry's
value is the read's own there, so the keyed read is the read at
every key — the store one term shared across its queries. -/
theorem keyAt_store {α β : Type} (eq : α → α → Bool)
    (hs : ∀ a b, eq a b = true → a = b) (f : α → β) (k : α) :
    ∀ st : List (α × β), (∀ e, e ∈ st → e.2 = f e.1) →
      keyAt eq (f k) k st = f k
  | [], _ => rfl
  | e :: t, h => by
    show cond (eq e.1 k) e.2 (keyAt eq (f k) k t) = f k
    cases he : eq e.1 k with
    | true =>
      show e.2 = f k
      rw [h e (List.Mem.head t), hs e.1 k he]
    | false =>
      exact keyAt_store eq hs f k t (fun x hx => h x (List.Mem.tail e hx))

/-- A read stored over a stated key list is read back at every
key, `keyAt_store` at the mapped store. -/
theorem keyAt_memo {α β : Type} (eq : α → α → Bool)
    (hs : ∀ a b, eq a b = true → a = b) (f : α → β) (k : α)
    (keys : List α) :
    keyAt eq (f k) k (keys.map (fun s => (s, f s))) = f k :=
  keyAt_store eq hs f k _ (fun e he => by
    obtain ⟨s, _, hse⟩ := mem_map_of (fun s => (s, f s)) keys e he
    rw [← hse])

/-- A read stored over a stated key list is read back at every
stored key at any default, the test reflexive. -/
theorem keyAt_map_mem {α β : Type} (eq : α → α → Bool)
    (hs : ∀ a b, eq a b = true → a = b) (hr : ∀ a, eq a a = true)
    (f : α → β) (d : β) (k : α) :
    ∀ keys : List α, k ∈ keys →
      keyAt eq d k (keys.map (fun s => (s, f s))) = f k
  | [], h => nomatch h
  | s :: t, h => by
    show cond (eq s k) (f s) (keyAt eq d k (t.map (fun s => (s, f s)))) = f k
    cases he : eq s k with
    | true =>
      show f s = f k
      rw [hs s k he]
    | false =>
      refine keyAt_map_mem eq hs hr f d k t ?_
      cases h with
      | head => rw [hr k] at he; exact Bool.noConfusion he
      | tail _ h' => exact h'

/-- A keyed list with a key's entry replaced, the entry appended
where the key is unstored. -/
def keyPut {α β : Type} (eq : α → α → Bool) (k : α) (v : β) :
    List (α × β) → List (α × β)
  | [] => [(k, v)]
  | e :: t => if eq e.1 k then (k, v) :: t else e :: keyPut eq k v t

/-- The replaced store's keys: the prior keys at a stored key, the
key appended at an unstored one, at a test reading equality and
reflexive. -/
theorem keyPut_keys {α β : Type} (eq : α → α → Bool)
    (hs : ∀ a b, eq a b = true → a = b) (hr : ∀ a, eq a a = true)
    [DecidableEq α] (k : α) (v : β) :
    ∀ l : List (α × β),
      (keyPut eq k v l).map Prod.fst
        = if 0 < countOf k (l.map Prod.fst) then l.map Prod.fst
          else l.map Prod.fst ++ [k]
  | [] => by
    show [k] = if 0 < countOf k [] then [] else [] ++ [k]
    rfl
  | e :: t => by
    show (if eq e.1 k then (k, v) :: t else e :: keyPut eq k v t).map Prod.fst
      = if 0 < countOf k (e.1 :: t.map Prod.fst) then e.1 :: t.map Prod.fst
        else e.1 :: t.map Prod.fst ++ [k]
    cases he : eq e.1 k with
    | true =>
      rw [if_pos rfl, hs e.1 k he, countOf_cons, if_pos rfl]
      rw [if_pos (Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _))]
      rfl
    | false =>
      rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
      have hne : ¬ k = e.1 := fun hk => by
        rw [hk, hr e.1] at he
        exact Bool.noConfusion he
      show e.1 :: (keyPut eq k v t).map Prod.fst = _
      rw [keyPut_keys eq hs hr k v t, countOf_cons, if_neg hne, Nat.zero_add]
      cases hc : decide (0 < countOf k (t.map Prod.fst)) with
      | true =>
        rw [if_pos (of_decide_eq_true hc), if_pos (of_decide_eq_true hc)]
      | false =>
        rw [if_neg (of_decide_eq_false hc), if_neg (of_decide_eq_false hc)]
        rfl

/-- A store at distinct keys reads every entry back at its own key,
at a test reading equality and reflexive. -/
theorem keyAt_getAt {α β : Type} (eq : α → α → Bool)
    (hs : ∀ a b, eq a b = true → a = b) (hr : ∀ a, eq a a = true)
    [DecidableEq α] (d : β) (e0 : α × β) :
    ∀ (l : List (α × β)) (i : Nat), i < l.length →
      (∀ x, countOf x (l.map Prod.fst) ≤ 1) →
      keyAt eq d (getAt e0 l i).1 l = (getAt e0 l i).2
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | e :: t, 0, _, _ => by
    show cond (eq e.1 e.1) e.2 (keyAt eq d e.1 t) = e.2
    rw [hr e.1]
    rfl
  | e :: t, i + 1, hi, hd => by
    show cond (eq e.1 (getAt e0 t i).1) e.2 (keyAt eq d (getAt e0 t i).1 t) = (getAt e0 t i).2
    have hit : i < t.length := Nat.lt_of_succ_lt_succ hi
    cases he : eq e.1 (getAt e0 t i).1 with
    | true =>
      have h1 : countOf e.1 (e.1 :: t.map Prod.fst) ≤ 1 := hd e.1
      rw [countOf_cons, if_pos rfl] at h1
      have h2 : 0 < countOf e.1 (t.map Prod.fst) := by
        rw [hs e.1 _ he]
        exact countOf_pos_of_mem (mem_map_to Prod.fst (mem_getAt e0 t i hit))
      exact absurd (Nat.lt_of_lt_of_le (Nat.add_lt_add_left h2 1) h1) (by decide)
    | false =>
      exact keyAt_getAt eq hs hr d e0 t i hit (fun x => by
        have h1 : countOf x (e.1 :: t.map Prod.fst) ≤ 1 := hd x
        rw [countOf_cons] at h1
        exact Nat.le_trans (Nat.le_add_left _ _) h1)

/-- The replaced store reads the new value at its key and the prior
store's values elsewhere, at a test reading equality and reflexive. -/
theorem keyAt_keyPut {α β : Type} (eq : α → α → Bool)
    (hs : ∀ a b, eq a b = true → a = b) (hr : ∀ a, eq a a = true)
    (d : β) (k k' : α) (v : β) :
    ∀ l : List (α × β),
      keyAt eq d k' (keyPut eq k v l) = cond (eq k k') v (keyAt eq d k' l)
  | [] => rfl
  | e :: t => by
    show keyAt eq d k' (if eq e.1 k then (k, v) :: t else e :: keyPut eq k v t)
      = cond (eq k k') v (cond (eq e.1 k') e.2 (keyAt eq d k' t))
    cases he : eq e.1 k with
    | true =>
      rw [if_pos rfl]
      show cond (eq k k') v (keyAt eq d k' t)
        = cond (eq k k') v (cond (eq e.1 k') e.2 (keyAt eq d k' t))
      rw [hs e.1 k he]
      cases eq k k' with
      | true => rfl
      | false => rfl
    | false =>
      rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
      show cond (eq e.1 k') e.2 (keyAt eq d k' (keyPut eq k v t))
        = cond (eq k k') v (cond (eq e.1 k') e.2 (keyAt eq d k' t))
      rw [keyAt_keyPut eq hs hr d k k' v t]
      cases he' : eq e.1 k' with
      | true =>
        have hkk : eq k k' = false := by
          rw [← hs e.1 k' he']
          cases hk : eq k e.1 with
          | false => rfl
          | true =>
            rw [hs k e.1 hk, hr e.1] at he
            exact Bool.noConfusion he
        rw [hkk]
        rfl
      | false => rfl

/-- Two folds at one read per occupied member are one value. -/
theorem famFold_congr_members {α β : Type} [DecidableEq α]
    (add : β → β → β) (unit : β) (f g : α → β) :
    ∀ l : List α, (∀ x, 0 < countOf x l → f x = g x) →
      famFold add unit f l = famFold add unit g l :=
  famFold_congr_members_ov Eq add unit (fun _ => rfl)
    (fun h1 h2 => by rw [h1, h2]) f g

/-- The accumulating product carries a factor into its seed, at a
commutative associative product. -/
theorem foldl_mul_seed {α β : Type} (mul : β → β → β)
    (hcomm : ∀ a b, mul a b = mul b a)
    (hassoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (f : α → β) :
    ∀ (l : List α) (acc c : β),
      mul (l.foldl (fun a x => mul a (f x)) acc) c
        = l.foldl (fun a x => mul a (f x)) (mul acc c)
  | [], _, _ => rfl
  | x :: t, acc, c => by
    show mul (t.foldl (fun a y => mul a (f y)) (mul acc (f x))) c
      = t.foldl (fun a y => mul a (f y)) (mul (mul acc c) (f x))
    rw [foldl_mul_seed mul hcomm hassoc f t (mul acc (f x)) c,
      hassoc acc (f x) c, hcomm (f x) c, ← hassoc acc c (f x)]

/-- At an absent key the skipping product is the plain one. -/
theorem foldl_skip_absent {α β : Type} [DecidableEq α]
    (mul : β → β → β) (f : α → β) (mu : α) :
    ∀ (l : List α) (acc : β), countOf mu l = 0 →
      l.foldl (fun a x => if x = mu then a else mul a (f x)) acc
        = l.foldl (fun a x => mul a (f x)) acc
  | [], _, _ => rfl
  | x :: t, acc, h => by
    have hsum : (if mu = x then 1 else 0) + countOf mu t = 0 :=
      (countOf_cons mu x t).symm.trans h
    have hx : ¬ mu = x := by
      intro he
      rw [if_pos he, Nat.add_comm] at hsum
      exact Nat.noConfusion hsum
    have ht : countOf mu t = 0 := by
      rw [if_neg hx, Nat.zero_add] at hsum
      exact hsum
    show t.foldl (fun a y => if y = mu then a else mul a (f y))
        (if x = mu then acc else mul acc (f x))
      = t.foldl (fun a y => mul a (f y)) (mul acc (f x))
    rw [if_neg (fun he => hx he.symm)]
    exact foldl_skip_absent mul f mu t (mul acc (f x)) ht

/-- The skipped key's factor rejoins the product: at a key
occupied once the skipping product against that key's own datum
is the plain product over every key. -/
theorem foldl_skip {α β : Type} [DecidableEq α]
    (mul : β → β → β)
    (hcomm : ∀ a b, mul a b = mul b a)
    (hassoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (f : α → β) (mu : α) :
    ∀ (l : List α) (acc : β), countOf mu l = 1 →
      mul (l.foldl (fun a x => if x = mu then a else mul a (f x))
          acc) (f mu)
        = l.foldl (fun a x => mul a (f x)) acc
  | [], _, h => Nat.noConfusion h
  | x :: t, acc, h => by
    have hsum : (if mu = x then 1 else 0) + countOf mu t = 1 :=
      (countOf_cons mu x t).symm.trans h
    show mul (t.foldl (fun a y => if y = mu then a else mul a (f y))
        (if x = mu then acc else mul acc (f x))) (f mu)
      = t.foldl (fun a y => mul a (f y)) (mul acc (f x))
    by_cases hx : mu = x
    · have ht : countOf mu t = 0 := by
        rw [if_pos hx] at hsum
        exact addCancelL 1 (by rw [Nat.add_zero]; exact hsum)
      rw [if_pos hx.symm,
        foldl_skip_absent mul f mu t acc ht,
        foldl_mul_seed mul hcomm hassoc f t acc (f mu), hx]
    · have ht : countOf mu t = 1 := by
        rw [if_neg hx, Nat.zero_add] at hsum
        exact hsum
      rw [if_neg (fun he => hx he.symm)]
      exact foldl_skip mul hcomm hassoc f mu t (mul acc (f x)) ht

/-- A pointwise-unoccupied read's fold is the count's unit. -/
theorem famFold_zero {α : Type} (F : α → Nat)
    (h : ∀ x, F x = 0) : ∀ l : List α,
    famFold Nat.add 0 F l = 0
  | [] => rfl
  | a :: t => by
    show F a + famFold Nat.add 0 F t = 0
    rw [h a, Nat.zero_add, famFold_zero F h t]

/-- The fold splits over a pointwise sum. -/
theorem famFold_add_split {α : Type} (f g : α → Nat) :
    ∀ l : List α, famFold Nat.add 0 (fun x => f x + g x) l
      = famFold Nat.add 0 f l + famFold Nat.add 0 g l :=
  famFold_add_ov natFoldLaws f g

/-- A filter at the sum's unit is no filter at all. -/
theorem famFold_add_filter {α : Type} (g : α → Nat) (t : α → Bool)
    (h : ∀ v, t v = false → g v = 0) (K : List α) :
    famFold Nat.add 0 g (K.filter t) = famFold Nat.add 0 g K :=
  famFold_filter_ov natFoldLaws g t h K

/-- The sum over a distinct family reads a second distinct family
holding the same occupied members, the further weights at the
sum's unit. -/
theorem famFold_add_occupied {α : Type} [DecidableEq α]
    (g : α → Nat) (P Q : List α)
    (hPd : distinctList P) (hQd : distinctList Q)
    (hPQ : ∀ x, 0 < countOf x P → 0 < g x → 0 < countOf x Q)
    (hQP : ∀ x, 0 < countOf x Q → 0 < g x → 0 < countOf x P) :
    famFold Nat.add 0 g P = famFold Nat.add 0 g Q := by
  have hoff : ∀ v : α, (decide (0 < g v)) = false → g v = 0 := by
    intro v hv
    match hgv : g v with
    | 0 => rfl
    | w + 1 =>
      rw [hgv] at hv
      exact Bool.noConfusion
        ((decide_eq_true (Nat.succ_pos w)).symm.trans hv)
  rw [← famFold_add_filter g (fun v => decide (0 < g v)) hoff P,
    ← famFold_add_filter g (fun v => decide (0 < g v)) hoff Q]
  refine famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc g _ _
    (fun x => ?_)
  rw [countOf_filter (fun v => decide (0 < g v)) x P,
    countOf_filter (fun v => decide (0 < g v)) x Q]
  show (if decide (0 < g x) = true then countOf x P else 0)
    = (if decide (0 < g x) = true then countOf x Q else 0)
  cases hgx : decide (0 < g x) with
  | false => rfl
  | true =>
    show countOf x P = countOf x Q
    have hg : 0 < g x := of_decide_eq_true hgx
    match hP : countOf x P, hQ : countOf x Q with
    | 0, 0 => rfl
    | 0, q + 1 =>
      exact absurd (hQP x (by rw [hQ]; exact Nat.succ_pos q) hg)
        (by rw [hP]; exact Nat.lt_irrefl 0)
    | p + 1, 0 =>
      exact absurd (hPQ x (by rw [hP]; exact Nat.succ_pos p) hg)
        (by rw [hQ]; exact Nat.lt_irrefl 0)
    | p + 1, q + 1 =>
      have hp1 : countOf x P ≤ 1 := distinctList_all hPd x
      have hq1 : countOf x Q ≤ 1 := distinctList_all hQd x
      rw [hP] at hp1
      rw [hQ] at hq1
      rw [Nat.le_antisymm (Nat.le_of_succ_le_succ hp1) (Nat.zero_le p),
        Nat.le_antisymm (Nat.le_of_succ_le_succ hq1) (Nat.zero_le q)]


/-- The natural product distributes on its right, the hand-rolled
read. -/
theorem mulAddR (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a,
    Nat.mul_comm c b]

/-- The consecutive string coefficients read the coroot's
additive join at the next depth (`lem:strings`). -/
theorem coeffCross (b g m : Nat) :
    (b + 1) * ((b + 1 + g) - b) + (m + g)
      = (b + 1 + 1) * ((b + 1 + g) - (b + 1)) + (m + (b + 1)) := by
  rw [Nat.add_assoc b 1 g, addSubSelfL b (1 + g),
    ← Nat.add_assoc b 1 g, addSubSelfL (b + 1) g,
    Nat.left_distrib (b + 1) 1 g, Nat.mul_one,
    mulAddR (b + 1) 1 g, Nat.one_mul g]
  have h (X Y m g : Nat) : X + Y + (m + g) = Y + g + (m + X) := by
    rw [Nat.add_assoc Y g (m + X), Nat.add_comm g (m + X),
      ← Nat.add_assoc Y (m + X) g, ← Nat.add_assoc (X + Y) m g,
      Nat.add_comm X Y, Nat.add_assoc Y X m, Nat.add_comm X m]
  exact h (b + 1) ((b + 1) * g) m g
/-- The successor's square at the two-apart product. -/
theorem sqJoin (n : Nat) : (n + 1) * (n + 1) = n * (n + 2) + 1 := by
  rw [mulAddR n 1 (n + 1), Nat.left_distrib n n 1, Nat.mul_one n,
    Nat.one_mul (n + 1), Nat.left_distrib n n 2, Nat.mul_comm n 2,
    Nat.two_mul n]
  repeat rw [Nat.add_assoc]

/-- The successor square's expansion at the joined counts. -/
theorem sqSucc (n : Nat) : (n + 1) * (n + 1) = n * n + (n + n + 1) := by
  rw [sqJoin n, Nat.left_distrib n n 2, Nat.mul_two n, Nat.add_assoc]

/-- The join's square at the doubled cross term. -/
theorem sqAdd (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Nat.left_distrib (a + b) a b, mulAddR a b a,
    mulAddR a b b, Nat.mul_comm b a,
    Nat.add_assoc (a * a) (a * b) (a * b + b * b),
    ← Nat.add_assoc (a * b) (a * b) (b * b),
    ← Nat.two_mul (a * b), ← Nat.add_assoc (a * a) (2 * (a * b))
      (b * b)]

/-- Two nested folds exchange their index families. -/
theorem famFold_swap {α β : Type} (F : α → β → Nat) :
    ∀ (l : List α) (m : List β),
      famFold Nat.add 0
        (fun x => famFold Nat.add 0 (fun y => F x y) m) l
      = famFold Nat.add 0
        (fun y => famFold Nat.add 0 (fun x => F x y) l) m
  | [], m => by
    show (0 : Nat)
      = famFold Nat.add 0 (fun _ => (0 : Nat)) m
    rw [famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) m]
  | a :: t, m => by
    show famFold Nat.add 0 (fun y => F a y) m
        + famFold Nat.add 0
          (fun x => famFold Nat.add 0 (fun y => F x y) m) t
      = famFold Nat.add 0
        (fun y => F a y
          + famFold Nat.add 0 (fun x => F x y) t) m
    rw [famFold_swap F t m,
      ← famFold_add_split (fun y => F a y)
        (fun y => famFold Nat.add 0 (fun x => F x y) t) m]

/-- A guarded outer fold exchanges with its inner: the guard
distributes into the inner fold and the two folds swap, the
refused guard's row the count's unit both ways. -/
theorem famFold_guard_swap {α γ : Type} (P : α → Prop)
    [DecidablePred P] (g : α → γ → Nat) (l : List α) (m : List γ) :
    famFold Nat.add 0
      (fun a => if P a then famFold Nat.add 0 (g a) m else 0) l
    = famFold Nat.add 0
      (fun c => famFold Nat.add 0
        (fun a => if P a then g a c else 0) l) m := by
  refine Eq.trans (famFold_congr_all Nat.add 0 _ _ (fun a => ?_) l)
    (famFold_swap (fun a c => if P a then g a c else 0) l m)
  by_cases h : P a
  · rw [if_pos h]
    exact famFold_congr_all Nat.add 0 _ _ (fun c => (if_pos h).symm) m
  · rw [if_neg h]
    exact (famFold_zero _ (fun c => if_neg h) m).symm

/-- A left scalar passes into the fold. -/
theorem famFold_mul (c : Nat) {α : Type} (F : α → Nat) :
    ∀ l : List α,
      c * famFold Nat.add 0 F l
        = famFold Nat.add 0 (fun x => c * F x) l
  | [] => Nat.mul_zero c
  | a :: t => by
    show c * (F a + famFold Nat.add 0 F t)
      = c * F a + famFold Nat.add 0 (fun x => c * F x) t
    rw [Nat.left_distrib c (F a) (famFold Nat.add 0 F t),
      famFold_mul c F t]

/-- A right scalar passes into the fold. -/
theorem famFold_mulR {α : Type} (c : Nat) (F : α → Nat) :
    ∀ l : List α,
      famFold Nat.add 0 (fun x => F x * c) l
        = famFold Nat.add 0 F l * c
  | [] => (Nat.zero_mul c).symm
  | a :: t => by
    show F a * c + famFold Nat.add 0 (fun x => F x * c) t
      = (F a + famFold Nat.add 0 F t) * c
    rw [famFold_mulR c F t, mulAddR (F a) (famFold Nat.add 0 F t) c]

/-- An accumulating pass whose steps keep the accumulator at every
member off one key reads its seed where the key is absent. -/
theorem foldl_off {α β : Type} [DecidableEq α] (F : β → α → β)
    (x0 : α) : ∀ (L : List α),
    (∀ x ∈ L, ¬ x = x0 → ∀ acc, F acc x = acc) →
    countOf x0 L = 0 → ∀ a : β, L.foldl F a = a
  | [], _, _, _ => rfl
  | p :: t, hmem, hz, a => by
    have hz' : (if x0 = p then 1 else 0) + countOf x0 t = 0 :=
      (countOf_cons x0 p t).symm.trans hz
    have hne : ¬ x0 = p := by
      intro he
      rw [if_pos he, Nat.add_comm] at hz'
      exact Nat.noConfusion hz'
    have hzt : countOf x0 t = 0 := by
      rw [if_neg hne, Nat.zero_add] at hz'
      exact hz'
    show t.foldl F (F a p) = a
    rw [hmem p (List.Mem.head t) (fun he => hne he.symm) a]
    exact foldl_off F x0 t
      (fun q hq => hmem q (List.Mem.tail p hq)) hzt a

/-- An accumulating pass whose steps keep the accumulator off one
key reads that key's own step at its single occurrence. -/
theorem foldl_pick {α β : Type} [DecidableEq α] (F : β → α → β)
    (x0 : α) (g : β → β) (hat : ∀ acc, F acc x0 = g acc) :
    ∀ (L : List α),
    (∀ x ∈ L, ¬ x = x0 → ∀ acc, F acc x = acc) →
    countOf x0 L = 1 → ∀ a : β, L.foldl F a = g a
  | [], _, hz, _ => Nat.noConfusion hz
  | p :: t, hmem, h1, a => by
    have h1' : (if x0 = p then 1 else 0) + countOf x0 t = 1 :=
      (countOf_cons x0 p t).symm.trans h1
    by_cases he : x0 = p
    · have hzt : countOf x0 t = 0 := by
        rw [if_pos he] at h1'
        exact addCancelL 1 (by rw [Nat.add_zero]; exact h1')
      show t.foldl F (F a p) = g a
      rw [← he, hat a]
      exact foldl_off F x0 t
        (fun q hq => hmem q (List.Mem.tail p hq)) hzt (g a)
    · have h1t : countOf x0 t = 1 := by
        rw [if_neg he, Nat.zero_add] at h1'
        exact h1'
      show t.foldl F (F a p) = g a
      rw [hmem p (List.Mem.head t) (fun hpe => he hpe.symm) a]
      exact foldl_pick F x0 g hat t
        (fun q hq => hmem q (List.Mem.tail p hq)) h1t a

/-- The guarded fold at a family holding the key at the count's
unit reads that unit. -/
theorem famFold_pickZero {α : Type} [DecidableEq α]
    (F : α → Nat) (x₀ : α) :
    ∀ K : List α, countOf x₀ K = 0 →
      famFold Nat.add 0
        (fun w => if w = x₀ then F w else 0) K = 0 :=
  fun K h =>
  famFold_null_ov natFoldLaws _ K
    (fun x hx => if_neg (fun he => by
      rw [he, h] at hx
      exact absurd hx (Nat.lt_irrefl 0)))

/-- The point collapse: the guarded fold at a family holding the
key once reads the key's member. -/
theorem famFold_pick {α : Type} [DecidableEq α]
    (F : α → Nat) (x₀ : α) :
    ∀ K : List α, countOf x₀ K = 1 →
      famFold Nat.add 0
        (fun w => if w = x₀ then F w else 0) K = F x₀ :=
  fun K h =>
  famFold_pick_ov natFoldLaws _ x₀ (F x₀) K h (if_pos rfl)
    (fun _ _ hxi => if_neg hxi)

/-- A fold vacant at every occupied member off one key reads at
most that key's own value where the key occurs at most once. -/
theorem famFold_le_one_at {α : Type} [DecidableEq α]
    (F : α → Nat) (x₀ : α) (K : List α)
    (hoff : ∀ x, 0 < countOf x K → ¬ x = x₀ → F x = 0)
    (h₀ : F x₀ ≤ 1) (hK : countOf x₀ K ≤ 1) :
    famFold Nat.add 0 F K ≤ 1 := by
  have hcongr : famFold Nat.add 0 F K
      = famFold Nat.add 0 (fun w => if w = x₀ then F w else 0) K := by
    refine famFold_congr_members Nat.add 0 _ _ K ?_
    intro w hw
    by_cases hwx : w = x₀
    · rw [if_pos hwx]
    · rw [if_neg hwx, hoff w hw hwx]
  rw [hcongr]
  match Nat.eq_zero_or_pos (countOf x₀ K) with
  | .inl hz =>
    rw [famFold_pickZero F x₀ K hz]
    exact Nat.zero_le 1
  | .inr hp =>
    rw [famFold_pick F x₀ K (Nat.le_antisymm hK hp)]
    exact h₀

/-- The fold over a flattened family is the fold of the per-member
folds. -/
theorem famFold_flatMap {α β : Type} (F : β → Nat)
    (g : α → List β) :
    ∀ l : List α,
      famFold Nat.add 0 F (l.flatMap g)
        = famFold Nat.add 0
          (fun x => famFold Nat.add 0 F (g x)) l :=
  famFold_flatMap_ov natFoldLaws F g

/-- A mapped family's count is the guarded fold over the source:
one indicator read per key. -/
theorem countOf_map_famFold (x : Nat) (f : Nat → Nat) :
    ∀ m : List Nat, countOf x (m.map f)
      = famFold Nat.add 0
          (fun j => if x = f j then 1 else 0) m
  | [] => rfl
  | a :: m => by
    show countOf x (f a :: m.map f)
      = Nat.add (if x = f a then 1 else 0)
        (famFold Nat.add 0 (fun j => if x = f j then 1 else 0) m)
    rw [countOf_cons, countOf_map_famFold x f m]
    rfl

/-- The member count read as its own delta fold. -/
theorem countOf_fold {α : Type} [DecidableEq α] (a : α) :
    ∀ l : List α, countOf a l
      = famFold Nat.add 0 (fun x => if a = x then 1 else 0) l
  | [] => rfl
  | b :: t => (countOf_cons a b t).trans
      (congrArg (fun z => (if a = b then 1 else 0) + z)
        (countOf_fold a t))

/-- The mirrored indicator's fold reads the key's count, the guard
at the member's own side. -/
theorem famFold_indicatorFlip {α : Type} [DecidableEq α]
    (t : α) (l : List α) :
    famFold Nat.add 0
      (fun x => if x = t then (1 : Nat) else 0) l
      = countOf t l := by
  rw [countOf_fold t l]
  refine famFold_congr_all Nat.add 0 _ _ ?_ l
  intro x
  by_cases h : x = t
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

/-- The double count: a fold of one list's counts in the other reads
at either order, each side the indicator's double fold. -/
theorem famFold_countSwap {α : Type} [DecidableEq α] :
    ∀ (L S : List α),
      famFold Nat.add 0 (fun a => countOf a S) L
        = famFold Nat.add 0 (fun s => countOf s L) S := by
  intro L S
  rw [famFold_congr_all Nat.add 0 (fun a => countOf a S)
      (fun a => famFold Nat.add 0
        (fun s => if a = s then (1 : Nat) else 0) S)
      (fun a => countOf_fold a S) L,
    famFold_congr_all Nat.add 0 (fun s => countOf s L)
      (fun s => famFold Nat.add 0
        (fun a => if a = s then (1 : Nat) else 0) L)
      (fun s => (famFold_indicatorFlip s L).symm) S,
    famFold_swap (fun a s => if a = s then (1 : Nat) else 0) L S]

/-- A guarded family fold reads its one key's value at the key's
count, every further member reading the sum's unit. -/
theorem famFold_off {α : Type} [DecidableEq α]
    (g : α → Nat) (x0 : α) : ∀ (W : List α),
    (∀ x ∈ W, x ≠ x0 → g x = 0) →
    famFold Nat.add 0 g W = countOf x0 W * g x0
  | [], _ => by
    show 0 = 0 * g x0
    rw [Nat.zero_mul]
  | q :: W, hyp => by
    show g q + famFold Nat.add 0 g W
      = countOf x0 (q :: W) * g x0
    rw [famFold_off g x0 W
        (fun x hx hne => hyp x (List.Mem.tail q hx) hne),
      countOf_cons]
    by_cases hq : q = x0
    · rw [hq]
      show g x0 + countOf x0 W * g x0
        = ((if x0 = x0 then 1 else 0) + countOf x0 W) * g x0
      rw [if_pos rfl, Nat.add_comm 1 (countOf x0 W),
        Nat.succ_mul (countOf x0 W) (g x0)]
      exact Nat.add_comm (g x0) (countOf x0 W * g x0)
    · rw [hyp q (List.Mem.head W) hq, Nat.zero_add]
      show countOf x0 W * g x0
        = ((if x0 = q then 1 else 0) + countOf x0 W) * g x0
      rw [if_neg (fun hh => hq hh.symm), Nat.zero_add]

/-- The product's left exchange, `a (b c) = b (a c)`: the
regrouping at the commuted head (`Nat.mul_left_comm` is
propext-bearing; this is the clean spelling). -/
theorem mulLeftComm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mulAssoc a b c, Nat.mul_comm a b, mulAssoc b a c]

/-- The product's head exchange at the regrouped tail,
`a (b c) = b a c`. -/
theorem mulHeadComm (a b c : Nat) : a * (b * c) = b * a * c := by
  rw [mulLeftComm a b c, ← mulAssoc b a c]

/-- The four-factor exchange at the inner members,
`(a b)(c d) = (a c)(b d)` (`Nat.mul_mul_mul_comm` is
propext-bearing; this is the clean spelling). -/
theorem mulMulMulComm (a b c d : Nat) :
    a * b * (c * d) = a * c * (b * d) := by
  rw [mulAssoc a b (c * d), mulAssoc a c (b * d), mulLeftComm b c d]

/-- The three-fold multiplier read, the literal's expansion. -/
theorem threeMul (n : Nat) : 3 * n = n + n + n := by
  rw [Nat.mul_comm 3 n]
  show 0 + n + n + n = n + n + n
  rw [Nat.zero_add n]

/-- The four-fold multiplier read, the doubled pair's expansion. -/
theorem fourMul (k : Nat) : 4 * k = 2 * k + 2 * k := by
  rw [Nat.mul_comm 4 k, Nat.mul_comm 2 k]
  show 0 + k + k + k + k = 0 + k + k + (0 + k + k)
  rw [Nat.zero_add k, Nat.add_assoc (k + k) k k]

/-- The four-factor product's head regroup,
`u v s t = u (v s t)`. -/
theorem mulFour (u v s t : Nat) :
    u * v * s * t = u * (v * s * t) := by
  rw [mulAssoc (u * v) s t, mulAssoc u v (s * t), mulAssoc v s t]

/-- The natural product at the literal equality, the fold laws
read at the product and its own unit. -/
theorem natMulFoldLaws : FoldLaws Nat Nat.mul 1 Eq where
  ovRefl := fun _ => rfl
  ovSymm := fun h => h.symm
  ovTrans := fun h1 h2 => h1.trans h2
  opCongr := fun h1 h2 => by rw [h1, h2]
  opComm := Nat.mul_comm
  opAssoc := mulAssoc
  unitOp := Nat.one_mul
  opUnit := Nat.mul_one

/-- The crossed square at a shifted pair: a member's product with
its own double shift joins the shifts' crossed product to the two
shifted members' product. -/
theorem crossMul (x a b : Nat) :
    x * (x + a + b) + a * b = (x + a) * (x + b) := by
  rw [Nat.left_distrib x (x + a) b, Nat.left_distrib x x a,
    ground.mulAddR x a (x + b), Nat.left_distrib x x b,
    Nat.left_distrib a x b, Nat.mul_comm a x,
    Nat.add_add_add_comm (x * x) (x * b) (x * a) (a * b),
    Nat.add_assoc (x * x + x * a) (x * b) (a * b)]

/-- The right-hand factor's exchange, `a b c = a c b`. -/
theorem mulRightComm (a b c : Nat) : a * b * c = a * c * b := by
  rw [mulAssoc a b c, Nat.mul_comm b c, ← mulAssoc a c b]

/-- The rising product from a floor, one factor per step. -/
def rise (c : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => c * rise (c + 1) k

/-- The rising product splits at a stated step. -/
theorem rise_split (c : Nat) : ∀ k j : Nat,
    rise c (k + j) = rise c k * rise (c + k) j
  | 0, j => by
    rw [Nat.zero_add j]
    show rise c j = 1 * rise (c + 0) j
    rw [Nat.add_zero c, Nat.one_mul]
  | k + 1, j => by
    rw [Nat.add_right_comm k 1 j]
    show c * rise (c + 1) (k + j)
      = c * rise (c + 1) k * rise (c + (k + 1)) j
    rw [rise_split (c + 1) k j, mulAssoc,
      Nat.add_assoc c 1 k, Nat.add_comm 1 k]

/-- The rising products' rectangle: the two split orders of one
rise agree, `(c+p)↑u · c↑p = c↑u · (c+u)↑p`. -/
theorem rise_rect (c p u : Nat) :
    rise (c + p) u * rise c p = rise c u * rise (c + u) p := by
  rw [Nat.mul_comm (rise (c + p) u) (rise c p),
    ← rise_split c p u, ← rise_split c u p, Nat.add_comm p u]

/-- The Pascal count at a height and a key: the count of the key's
selections from the height, each raised step joining the two counts
one height below. -/
def pasc : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, t + 1 => pasc j t + pasc j (t + 1)

/-- A key above the height reads nought. -/
theorem pasc_beyond : ∀ j t : Nat, j < t → pasc j t = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | j + 1, t + 1, h => by
    show pasc j t + pasc j (t + 1) = 0
    rw [pasc_beyond j t (Nat.lt_of_succ_lt_succ h),
      pasc_beyond j (t + 1) (Nat.lt_of_succ_lt h)]

/-- The key at its own height reads one. -/
theorem pasc_self : ∀ j : Nat, pasc j j = 1
  | 0 => rfl
  | j + 1 => by
    show pasc j j + pasc j (j + 1) = 1
    rw [pasc_self j, pasc_beyond j (j + 1) (Nat.lt_succ_self j)]

/-- A Pascal count at a key at or below its row is occupied. -/
theorem pasc_pos : ∀ j t : Nat, t ≤ j → 0 < pasc j t
  | 0, 0, _ => Nat.zero_lt_one
  | _ + 1, 0, _ => Nat.zero_lt_one
  | 0, t + 1, h => absurd h (Nat.not_succ_le_zero t)
  | j + 1, t + 1, h => by
    show 0 < pasc j t + pasc j (t + 1)
    exact Nat.lt_of_lt_of_le (pasc_pos j t (Nat.le_of_succ_le_succ h)) (Nat.le_add_right _ _)

/-- The nought key reads one at every height. -/
private theorem pascBase (j : Nat) : pasc j 0 = 1 := by
  match j with
  | 0 => rfl
  | _ + 1 => rfl

/-- The raised height's raised key joins the two counts one height
below, the definition's own step read. -/
private theorem pascStep (j t : Nat) :
    pasc (j + 1) (t + 1) = pasc j t + pasc j (t + 1) := rfl

/-- The triple's ends exchange, `a + b + c = c + b + a`. -/
theorem addSwapEnds (a b c : Nat) : a + b + c = c + b + a := by
  rw [Nat.add_assoc a b c, Nat.add_comm a (b + c), Nat.add_comm b c,
    Nat.add_assoc c b a]

/-- The joined pair's head opens at the front and the standing
second closes at the tail,
`a + b + (c + d) = c + (a + d) + b`. -/
theorem addJoinHeadOut (a b c d : Nat) :
    a + b + (c + d) = c + (a + d) + b := by
  rw [Nat.add_assoc a b (c + d), Nat.add_assoc c (a + d) b,
    Nat.add_assoc a d b, Nat.add_left_comm c a (d + b),
    Nat.add_comm d b, Nat.add_left_comm c b d]

/-- The joined pair's head opens at the front,
`a + b + (c + d) = c + a + (b + d)`. -/
theorem addJoinHeadFront (a b c d : Nat) :
    a + b + (c + d) = c + a + (b + d) := by
  rw [Nat.add_assoc a b (c + d), Nat.add_left_comm b c d,
    Nat.add_assoc c a (b + d), Nat.add_left_comm a c (b + d)]

/-- The second summand withdraws to the tail,
`a + b + c + d = a + c + d + b`. -/
theorem addRotTail3 (a b c d : Nat) :
    a + b + c + d = a + c + d + b := by
  rw [Nat.add_right_comm a b c, Nat.add_right_comm (a + c) b d]

/-- A shared summand drops from both members of a gap. -/
theorem addSubAddR : ∀ n m k : Nat, n + k - (m + k) = n - m
  | _, _, 0 => rfl
  | n, m, k + 1 => by
    show n + k + 1 - (m + k + 1) = n - m
    rw [Nat.succ_sub_succ (n + k) (m + k)]
    exact addSubAddR n m k

/-- The gap is homogeneous in a shared factor: a difference's
product is the products' difference. -/
theorem subMulR : ∀ a b c : Nat, (a - b) * c = a * c - b * c
  | a, 0, c => by
    rw [Nat.sub_zero a, Nat.zero_mul c, Nat.sub_zero (a * c)]
  | 0, b + 1, c => by
    rw [Nat.zero_sub (b + 1), Nat.zero_mul c,
      Nat.zero_sub ((b + 1) * c)]
  | a + 1, b + 1, c => by
    rw [Nat.succ_sub_succ a b, Nat.succ_mul a c, Nat.succ_mul b c,
      addSubAddR (a * c) (b * c) c]
    exact subMulR a b c

private theorem foldIndicatorNil {α : Type} [DecidableEq α]
    (F : α → Nat) (a : α) :
    ∀ basis : List α, countOf a basis = 0 →
      famFold Nat.add 0
        (fun m => (if m = a then 1 else 0) * F m) basis = 0
  | [], _ => rfl
  | b :: rest, h => by
    have h' : (if a = b then 1 else 0) + countOf a rest = 0 :=
      (countOf_cons a b rest).symm.trans h
    by_cases hab : a = b
    · rw [if_pos hab, Nat.add_comm 1 (countOf a rest)] at h'
      have hpos : 0 < countOf a rest + 1 := Nat.succ_pos _
      rw [h'] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
    · rw [if_neg hab, Nat.zero_add] at h'
      show (if b = a then 1 else 0) * F b
        + famFold Nat.add 0
            (fun m => (if m = a then 1 else 0) * F m) rest = 0
      rw [if_neg (fun hc => hab hc.symm), Nat.zero_mul, Nat.zero_add,
        foldIndicatorNil F a rest h']

private theorem foldIndicatorOne {α : Type} [DecidableEq α]
    (F : α → Nat) (a : α) :
    ∀ basis : List α, countOf a basis = 1 →
      famFold Nat.add 0
        (fun m => (if m = a then 1 else 0) * F m) basis = F a
  | [], h => by
    have h' : (0 : Nat) = 1 := h
    have hlt : (0 : Nat) < 1 := Nat.succ_pos 0
    rw [← h'] at hlt
    exact absurd hlt (Nat.lt_irrefl 0)
  | b :: rest, h => by
    have h' : (if a = b then 1 else 0) + countOf a rest = 1 :=
      (countOf_cons a b rest).symm.trans h
    by_cases hab : a = b
    · rw [if_pos hab, Nat.add_comm 1 (countOf a rest)] at h'
      have hrest : countOf a rest = 0 := Nat.succ.inj h'
      show (if b = a then 1 else 0) * F b
        + famFold Nat.add 0
            (fun m => (if m = a then 1 else 0) * F m) rest = F a
      rw [if_pos hab.symm, Nat.one_mul,
        foldIndicatorNil F a rest hrest, Nat.add_zero, hab]
    · rw [if_neg hab, Nat.zero_add] at h'
      show (if b = a then 1 else 0) * F b
        + famFold Nat.add 0
            (fun m => (if m = a then 1 else 0) * F m) rest = F a
      rw [if_neg (fun hc => hab hc.symm), Nat.zero_mul, Nat.zero_add,
        foldIndicatorOne F a rest h']

/-- A fold over a family collects by value on a base list holding
each member once: the base's fold at the multiplicity-weighted
read. -/
theorem famFold_countCollect {α : Type} [DecidableEq α]
    (F : α → Nat) : ∀ (l basis : List α),
    (∀ x, 0 < countOf x l → countOf x basis = 1) →
    famFold Nat.add 0 F l
      = famFold Nat.add 0 (fun m => countOf m l * F m) basis
  | [], basis, _ => by
    show (0 : Nat)
      = famFold Nat.add 0
        (fun m => countOf m ([] : List α) * F m) basis
    rw [famFold_zero (fun m => countOf m ([] : List α) * F m)
      (fun x => Nat.zero_mul (F x)) basis]
  | a :: t, basis, h => by
    have hbase : countOf a basis = 1 :=
      h a (by rw [countOf_head]; exact Nat.succ_pos _)
    have ht : ∀ x, 0 < countOf x t → countOf x basis = 1 :=
      fun x hx => h x (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _))
    have e1 : famFold Nat.add 0
          (fun m => countOf m (a :: t) * F m) basis
        = famFold Nat.add 0
          (fun m => (if m = a then 1 else 0) * F m + countOf m t * F m)
          basis :=
      famFold_congr_all Nat.add 0 _ _
        (fun x => by rw [countOf_cons]; exact mulAddR _ _ _) basis
    have e2 := famFold_add_split (fun m => (if m = a then 1 else 0) * F m)
      (fun m => countOf m t * F m) basis
    show F a + famFold Nat.add 0 F t
      = famFold Nat.add 0 (fun m => countOf m (a :: t) * F m) basis
    rw [e1, e2, foldIndicatorOne F a basis hbase,
      ← famFold_countCollect F t basis ht]

/-! The partition tier: a fold over a list is the fold of its
members' counts against the weights over a distinct covering index,
with the distinct index the dedup walk builds — the content
grading's own count read, shared by the irreducibility count and
the fusion data's tier. -/

/-- The constant-one fold reads the length. -/
theorem famFold_length {α : Type} :
    ∀ l : List α, famFold Nat.add 0 (fun _ => (1 : Nat)) l = l.length
  | [] => rfl
  | _ :: t => by
    show 1 + famFold Nat.add 0 (fun _ => (1 : Nat)) t = t.length + 1
    rw [famFold_length t]
    exact Nat.add_comm 1 t.length

/-- A distinct list reads its member's count at one. -/
theorem countOf_distinct_one {α : Type} [DecidableEq α]
    {b : α} {D : List α} (hd : distinctList D) (hb : b ∈ D) :
    countOf b D = 1 :=
  Nat.le_antisymm (hd b hb) (countOf_pos_of_mem hb)

/-- The weighted partition: a fold over a list is the fold of its
members' counts against the weights over a distinct covering
index, `countOf_partition` the unit-weight instance. -/
theorem famFold_partition {α : Type} [DecidableEq α] (F : α → Nat) :
    ∀ (l D : List α), distinctList D → (∀ x ∈ l, x ∈ D) →
      famFold Nat.add 0 F l
        = famFold Nat.add 0 (fun k => countOf k l * F k) D :=
  fun l D hd hcov =>
    famFold_countCollect F l D (fun x hx =>
      countOf_distinct_one hd (hcov x (mem_of_countOf_pos x l hx)))

/-- The partition: a list's length is the fold of its members'
counts over a distinct covering index. -/
theorem countOf_partition {α : Type} [DecidableEq α] :
    ∀ (l D : List α), distinctList D → (∀ x ∈ l, x ∈ D) →
      famFold Nat.add 0 (fun a => countOf a l) D = l.length :=
  fun l D hd hcov => by
    rw [← famFold_length l,
      famFold_partition (fun _ => (1 : Nat)) l D hd hcov]
    exact famFold_congr_all Nat.add 0 _ _
      (fun k => (Nat.mul_one (countOf k l)).symm) D


/-- Two lists one value at a stated member equality, memberwise at
one length. -/
def listEqBy {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: s, b :: t => eq a b && listEqBy eq s t

/-- The distinct index at a list, the first occurrence kept, the
members in their order of first appearance. -/
def dedupF {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a]) []

/-- A first-kept fold adds at most one entry per input member. -/
private theorem length_dedupF_fold_le {α : Type} [DecidableEq α] :
    ∀ (l acc : List α),
      (l.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a]) acc).length
        ≤ acc.length + l.length
  | [], acc => Nat.le_refl acc.length
  | a :: l, acc => by
    change (l.foldl _ (if 0 < countOf a acc then acc else acc ++ [a])).length
      ≤ acc.length + (l.length + 1)
    by_cases h : 0 < countOf a acc
    · rw [if_pos h]
      exact Nat.le_trans (length_dedupF_fold_le l acc)
        (Nat.le_succ (acc.length + l.length))
    · rw [if_neg h]
      have hb := length_dedupF_fold_le l (acc ++ [a])
      rw [length_append] at hb
      change (l.foldl _ (acc ++ [a])).length ≤ (acc.length + 1) + l.length at hb
      rw [Nat.add_right_comm acc.length 1 l.length] at hb
      exact hb

/-- Keeping first occurrences cannot increase a list's count. -/
theorem length_dedupF_le {α : Type} [DecidableEq α] (l : List α) :
    (dedupF l).length ≤ l.length := by
  have h := length_dedupF_fold_le l []
  change (dedupF l).length ≤ 0 + l.length at h
  rw [Nat.zero_add] at h
  exact h

/-- The first-kept index's fold from a stated accumulator: a member
of the accumulator or of the list is a member of the fold. -/
theorem mem_dedupF_fold {α : Type} [DecidableEq α] {x : α} :
    ∀ (l acc : List α), x ∈ acc ∨ x ∈ l →
      x ∈ l.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a]) acc
  | [], _, h => match h with
    | .inl h => h
    | .inr h => nomatch h
  | a :: t, acc, h => by
    show x ∈ t.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a])
      (if 0 < countOf a acc then acc else acc ++ [a])
    refine mem_dedupF_fold t _ ?_
    by_cases hc : 0 < countOf a acc
    · rw [if_pos hc]
      match h with
      | .inl h => exact .inl h
      | .inr (.head _) => exact .inl (mem_of_countOf_pos _ acc hc)
      | .inr (.tail _ h') => exact .inr h'
    · rw [if_neg hc]
      match h with
      | .inl h =>
        refine .inl (mem_of_countOf_pos x _ ?_)
        rw [countOf_append]
        exact Nat.lt_of_lt_of_le (countOf_pos_of_mem h) (Nat.le_add_right _ _)
      | .inr (.head _) =>
        refine .inl (mem_of_countOf_pos _ _ ?_)
        rw [countOf_append, countOf_cons, if_pos rfl]
        exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_left _ _)
      | .inr (.tail _ h') => exact .inr h'

/-- A member of the first-kept index's fold is a member of the
accumulator or of the list. -/
theorem mem_of_dedupF_fold {α : Type} [DecidableEq α] {x : α} :
    ∀ (l acc : List α),
      x ∈ l.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a]) acc →
      x ∈ acc ∨ x ∈ l
  | [], _, h => .inl h
  | a :: t, acc, h => by
    have h' : x ∈ (if 0 < countOf a acc then acc else acc ++ [a]) ∨ x ∈ t :=
      mem_of_dedupF_fold t _ h
    by_cases hc : 0 < countOf a acc
    · rw [if_pos hc] at h'
      match h' with
      | .inl h => exact .inl h
      | .inr h => exact .inr (.tail a h)
    · rw [if_neg hc] at h'
      match h' with
      | .inl h =>
        match mem_append_of acc [a] h with
        | .inl h => exact .inl h
        | .inr (.head _) => exact .inr (.head t)
      | .inr h => exact .inr (.tail a h)

/-- The first-kept index's fold keeps a member's count at or below
one from an accumulator so. -/
theorem countOf_dedupF_fold_le {α : Type} [DecidableEq α] (x : α) :
    ∀ (l acc : List α), countOf x acc ≤ 1 →
      countOf x (l.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a]) acc) ≤ 1
  | [], _, h => h
  | a :: t, acc, h => by
    show countOf x (t.foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a])
      (if 0 < countOf a acc then acc else acc ++ [a])) ≤ 1
    refine countOf_dedupF_fold_le x t _ ?_
    by_cases hc : 0 < countOf a acc
    · rw [if_pos hc]
      exact h
    · rw [if_neg hc, countOf_append, countOf_cons]
      by_cases hx : x = a
      · rw [if_pos hx, hx, Nat.le_antisymm (Nat.le_of_not_lt hc) (Nat.zero_le _)]
        exact Nat.le_refl 1
      · rw [if_neg hx]
        exact h

/-- The first-kept distinct index grown by one member: the index
itself at a member already reached, the member appended
otherwise. -/
theorem dedupF_append_single {α : Type} [DecidableEq α] (l : List α) (a : α) :
    dedupF (l ++ [a]) = if 0 < countOf a (dedupF l) then dedupF l else dedupF l ++ [a] := by
  show (l ++ [a]).foldl (fun acc a => if 0 < countOf a acc then acc else acc ++ [a]) [] = _
  rw [foldl_append]
  rfl

/-- A member reaches the first-kept distinct index. -/
theorem mem_dedupF {α : Type} [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
    x ∈ dedupF l :=
  mem_dedupF_fold l [] (.inr h)

/-- The first-kept distinct index's members sit in the list. -/
theorem mem_of_dedupF {α : Type} [DecidableEq α] {x : α} {l : List α} (h : x ∈ dedupF l) :
    x ∈ l :=
  match mem_of_dedupF_fold l [] h with
  | .inl h => nomatch h
  | .inr h => h

/-- Every member's count in the first-kept distinct index is at or
below one. -/
theorem countOf_dedupF_le {α : Type} [DecidableEq α] (x : α) (l : List α) :
    countOf x (dedupF l) ≤ 1 :=
  countOf_dedupF_fold_le x l [] (Nat.zero_le 1)

/-- A member's count in the first-kept distinct index is one. -/
theorem countOf_dedupF_one {α : Type} [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
    countOf x (dedupF l) = 1 :=
  Nat.le_antisymm (countOf_dedupF_le x l) (countOf_pos_of_mem (mem_dedupF h))

/-- The closure from stated seeds at a step and a join over a pool
with its own data, the members read off the pool by a projection:
each round joins the fresh members' steps to the pool at the join, the
next fresh members the projected pool's new members, the fuel the
rounds' bound. -/
def closeByS {α σ : Type} (step : α → List α) (join : σ → α → σ)
    (proj : σ → List α) : Nat → σ → List α → σ
  | 0, pool, _ => pool
  | fuel + 1, pool, fresh =>
    match fresh with
    | [] => pool
    | _ :: _ =>
      let pool' := (fresh.flatMap step).foldl join pool
      closeByS step join proj fuel pool'
        ((proj pool').drop (proj pool).length)

/-- The closure from stated seeds at a step and a join: each round
joins the fresh members' steps to the pool at the join, the next
fresh members the round's new members, the fuel the rounds' bound (the
projected closure at the pool itself). -/
def closeBy {α : Type} (step : α → List α) (join : List α → α → List α) :
    Nat → List α → List α → List α :=
  closeByS step join (fun l => l)

/-- A member after a leading segment is withdrawn was a member
of the whole list. -/
theorem mem_drop_of {α : Type} {x : α} : ∀ (n : Nat) (l : List α),
    x ∈ l.drop n → x ∈ l
  | 0, _, h => h
  | _ + 1, [], h => nomatch h
  | n + 1, a :: l, h => List.Mem.tail a (mem_drop_of n l h)

/-- A closure preserves every member property kept by its step
and its join, at every number of rounds. -/
theorem closeBy_all {α : Type} (P : α → Prop) (step : α → List α)
    (join : List α → α → List α)
    (hs : ∀ a, P a → ∀ b ∈ step a, P b)
    (hj : ∀ l a, (∀ b ∈ l, P b) → P a → ∀ b ∈ join l a, P b) :
    ∀ fuel pool fresh, (∀ a ∈ pool, P a) → (∀ a ∈ fresh, P a) →
      ∀ a ∈ closeBy step join fuel pool fresh, P a
  | 0, _, _, hp, _ => hp
  | _ + 1, _, [], hp, _ => hp
  | fuel + 1, pool, a :: fresh, hp, hf => by
    have hstep : ∀ b ∈ (a :: fresh).flatMap step, P b := by
      intro b hb
      obtain ⟨c, hc, hcb⟩ := mem_flatMap_of step (a :: fresh) b hb
      exact hs c (hf c hc) b hcb
    have hpool : ∀ b ∈ ((a :: fresh).flatMap step).foldl join pool, P b :=
      foldl_invariant (fun l => ∀ b ∈ l, P b) join _ pool hp
        (fun b hb l hl => hj l b hl (hstep b hb))
    exact closeBy_all P step join hs hj fuel _ _ hpool
      (fun b hb => hpool b (mem_drop_of pool.length _ hb))

/-- A closure keeps each accumulated member when every join
keeps the prior pool, independently of the step list. -/
theorem closeBy_mem {α : Type} (step : α → List α) (join : List α → α → List α)
    (hkeep : ∀ l a x, x ∈ l → x ∈ join l a) :
    ∀ fuel pool fresh x, x ∈ pool → x ∈ closeBy step join fuel pool fresh
  | 0, _, _, _, h => h
  | _ + 1, _, [], _, h => h
  | fuel + 1, pool, a :: fresh, x, h => by
    have hp : x ∈ ((a :: fresh).flatMap step).foldl join pool :=
      foldl_invariant (fun l => x ∈ l) join _ pool h
        (fun a _ l hx => hkeep l a x hx)
    exact closeBy_mem step join hkeep fuel _ _ x hp

/-- A fold of joins which keep or append their input adds
only members of the stated input family. -/
theorem foldl_join_reads {α : Type} (join : List α → α → List α)
    (hj : ∀ l a, join l a = l ∨ join l a = l ++ [a]) (P : α → Prop) :
    ∀ (cands pool : List α), (∀ a ∈ cands, P a) →
      ∃ tail, cands.foldl join pool = pool ++ tail ∧ ∀ a ∈ tail, P a
  | [], pool, _ => ⟨[], (append_nil pool).symm, fun _ h => nomatch h⟩
  | a :: cands, pool, h => by
    change ∃ tail, cands.foldl join (join pool a) = pool ++ tail ∧ ∀ b ∈ tail, P b
    cases hj pool a with
    | inl he =>
      rw [he]
      exact foldl_join_reads join hj P cands pool (fun b hb => h b (List.Mem.tail a hb))
    | inr he =>
      rw [he]
      obtain ⟨tail, ht, hp⟩ := foldl_join_reads join hj P cands (pool ++ [a])
        (fun b hb => h b (List.Mem.tail a hb))
      refine ⟨a :: tail, ?_, ?_⟩
      · rw [ht, append_assoc]; rfl
      · intro b hb
        cases hb with
        | head => exact h a (List.Mem.head _)
        | tail _ hb => exact hp b hb

/-- A closure whose joins keep or append their input is the
seed pool followed by step images. A preserved member property
and a read of each step hold throughout that appended tail. -/
theorem closeBy_reads {α : Type} (Q R : α → Prop) (step : α → List α)
    (join : List α → α → List α)
    (hj : ∀ l a, join l a = l ∨ join l a = l ++ [a])
    (hs : ∀ a, Q a → ∀ b ∈ step a, Q b ∧ R b) :
    ∀ fuel pool fresh, (∀ a ∈ pool, Q a) → (∀ a ∈ fresh, Q a) →
      ∃ tail, closeBy step join fuel pool fresh = pool ++ tail ∧ ∀ a ∈ tail, Q a ∧ R a
  | 0, pool, _, _, _ => ⟨[], (append_nil pool).symm, fun _ h => nomatch h⟩
  | _ + 1, pool, [], _, _ => ⟨[], (append_nil pool).symm, fun _ h => nomatch h⟩
  | fuel + 1, pool, a :: fresh, hp, hf => by
    have hc : ∀ b ∈ (a :: fresh).flatMap step, Q b ∧ R b := by
      intro b hb
      obtain ⟨v, hv, hvb⟩ := mem_flatMap_of step (a :: fresh) b hb
      exact hs v (hf v hv) b hvb
    obtain ⟨t1, ht1, hqr1⟩ := foldl_join_reads join hj (fun a => Q a ∧ R a)
      ((a :: fresh).flatMap step) pool hc
    change ∃ tail, closeBy step join fuel (((a :: fresh).flatMap step).foldl join pool)
      ((((a :: fresh).flatMap step).foldl join pool).drop pool.length) = pool ++ tail
      ∧ ∀ a ∈ tail, Q a ∧ R a
    rw [ht1, drop_append_self]
    have hp' : ∀ b ∈ pool ++ t1, Q b := by
      intro b hb
      cases mem_append_of pool t1 hb with
      | inl h => exact hp b h
      | inr h => exact (hqr1 b h).1
    obtain ⟨t2, ht2, hqr2⟩ := closeBy_reads Q R step join hj hs fuel (pool ++ t1) t1 hp'
      (fun b hb => (hqr1 b hb).1)
    refine ⟨t1 ++ t2, ?_, ?_⟩
    · rw [ht2, append_assoc]
    · intro b hb
      cases mem_append_of t1 t2 hb with
      | inl h => exact hqr1 b h
      | inr h => exact hqr2 b h

/-- A closure at a vacant fresh list returns its pool at every
fuel, independently of the step and join. -/
theorem closeBy_nil {α : Type} (step : α → List α) (join : List α → α → List α)
    (fuel : Nat) (pool : List α) : closeBy step join fuel pool [] = pool := by
  cases fuel with
  | zero => rfl
  | succ _ => rfl

/-- A natural height descending at every step bounds the rounds
of a closure whose joins keep or append their input. -/
theorem closeBy_fuel {α : Type} (step : α → List α) (join : List α → α → List α)
    (height : α → Nat)
    (hj : ∀ l a, join l a = l ∨ join l a = l ++ [a])
    (hs : ∀ a b, b ∈ step a → height b < height a) :
    ∀ (fuel extra : Nat) (pool fresh : List α),
      (∀ a ∈ fresh, height a < fuel) →
      closeBy step join (fuel + extra) pool fresh = closeBy step join fuel pool fresh
  | 0, extra, pool, fresh, hf => by
    have he : fresh = [] := by
      cases fresh with
      | nil => rfl
      | cons a t => exact False.elim (Nat.not_lt_zero _ (hf a (List.Mem.head t)))
    rw [he, closeBy_nil, closeBy_nil]
  | fuel + 1, extra, pool, [], _ => by rw [closeBy_nil, closeBy_nil]
  | fuel + 1, extra, pool, a :: fresh, hf => by
    have hc : ∀ b ∈ (a :: fresh).flatMap step, height b < fuel := by
      intro b hb
      obtain ⟨x, hx, hxb⟩ := mem_flatMap_of step (a :: fresh) b hb
      exact Nat.lt_of_lt_of_le (hs x b hxb) (Nat.le_of_lt_succ (hf x hx))
    obtain ⟨tail, ht, hh⟩ := foldl_join_reads join hj (fun b => height b < fuel)
      ((a :: fresh).flatMap step) pool hc
    rw [Nat.succ_add]
    change closeBy step join (fuel + extra) (((a :: fresh).flatMap step).foldl join pool)
      ((((a :: fresh).flatMap step).foldl join pool).drop pool.length)
      = closeBy step join fuel (((a :: fresh).flatMap step).foldl join pool)
        ((((a :: fresh).flatMap step).foldl join pool).drop pool.length)
    rw [ht, drop_append_self]
    exact closeBy_fuel step join height hj hs fuel extra (pool ++ tail) tail hh

/-- A fold of membership joins preserves its pool read and places
every input in the final pool's accepted family. -/
theorem foldl_join_sem {α : Type} (join : List α → α → List α)
    (P : α → Prop) (I : List α → Prop) (S : List α → α → Prop)
    (hj : ∀ L a, join L a = L ∨ join L a = L ++ [a])
    (hjoin : ∀ L a, I L → P a → I (join L a) ∧ S (join L a) a)
    (hmono : ∀ L ext a, I L → I (L ++ ext) → P a → S L a → S (L ++ ext) a) :
    ∀ (inputs pool : List α), I pool → (∀ a ∈ inputs, P a) →
      I (inputs.foldl join pool) ∧ ∀ a ∈ inputs, S (inputs.foldl join pool) a
  | [], pool, hi, _ => ⟨hi, fun _ h => nomatch h⟩
  | a :: inputs, pool, hi, hp => by
    have ha := hp a (List.Mem.head inputs)
    have hjp := hjoin pool a hi ha
    have htail := foldl_join_sem join P I S hj hjoin hmono inputs (join pool a) hjp.1
      (fun b hb => hp b (List.Mem.tail a hb))
    refine ⟨htail.1, ?_⟩
    intro b hb
    cases hb with
    | head =>
      obtain ⟨ext, he, _⟩ := foldl_join_reads join hj P inputs (join pool a)
        (fun b hb => hp b (List.Mem.tail a hb))
      have hI : I (join pool a ++ ext) := by rw [← he]; exact htail.1
      change S (inputs.foldl join (join pool a)) a
      rw [he]
      exact hmono (join pool a) ext a hjp.1 hI ha hjp.2
    | tail _ hb => exact htail.2 b hb

/-- A descending-height closure completes its pool read and
accepts every step from every final member. Pending members enter
at heights below the fuel, and earlier members have their step
reads in the current pool already. -/
theorem closeBy_sem {α : Type} (step : α → List α) (join : List α → α → List α)
    (P : α → Prop) (I : List α → Prop) (S : List α → α → Prop) (height : α → Nat)
    (hj : ∀ L a, join L a = L ∨ join L a = L ++ [a])
    (hjoin : ∀ L a, I L → P a → I (join L a) ∧ S (join L a) a)
    (hmono : ∀ L ext a, I L → I (L ++ ext) → P a → S L a → S (L ++ ext) a)
    (hvalid : ∀ L, I L → ∀ a ∈ L, P a)
    (hstep : ∀ a, P a → ∀ b ∈ step a, P b ∧ height b < height a) :
    ∀ (fuel : Nat) (pool fresh : List α), I pool →
      (∀ a ∈ fresh, P a ∧ height a < fuel) →
      (∀ a ∈ pool, a ∈ fresh ∨ ∀ b ∈ step a, S pool b) →
      I (closeBy step join fuel pool fresh) ∧
        ∀ a ∈ closeBy step join fuel pool fresh, ∀ b ∈ step a,
          S (closeBy step join fuel pool fresh) b
  | 0, pool, fresh, hi, hf, hp => by
    refine ⟨hi, ?_⟩
    intro a ha b hb
    cases hp a ha with
    | inl h => exact False.elim (Nat.not_lt_zero _ (hf a h).2)
    | inr h => exact h b hb
  | _ + 1, pool, [], hi, _, hp => by
    refine ⟨hi, ?_⟩
    intro a ha b hb
    cases hp a ha with
    | inl h => nomatch h
    | inr h => exact h b hb
  | fuel + 1, pool, a :: fresh, hi, hf, hp => by
    let inputs := (a :: fresh).flatMap step
    have hc : ∀ b ∈ inputs, P b ∧ height b < fuel := by
      intro b hb
      obtain ⟨v, hv, hvb⟩ := mem_flatMap_of step (a :: fresh) b hb
      have h := hstep v (hf v hv).1 b hvb
      exact ⟨h.1, Nat.lt_of_lt_of_le h.2 (Nat.le_of_lt_succ (hf v hv).2)⟩
    obtain ⟨ext, he, hnew⟩ := foldl_join_reads join hj (fun b => P b ∧ height b < fuel)
      inputs pool hc
    have hfold := foldl_join_sem join P I S hj hjoin hmono inputs pool hi (fun b hb => (hc b hb).1)
    have hi' : I (pool ++ ext) := by rw [← he]; exact hfold.1
    have hread : ∀ b ∈ inputs, S (pool ++ ext) b := by rw [← he]; exact hfold.2
    change I (closeBy step join fuel (inputs.foldl join pool)
      ((inputs.foldl join pool).drop pool.length)) ∧
      ∀ v ∈ closeBy step join fuel (inputs.foldl join pool)
        ((inputs.foldl join pool).drop pool.length), ∀ w ∈ step v,
          S (closeBy step join fuel (inputs.foldl join pool)
            ((inputs.foldl join pool).drop pool.length)) w
    rw [he, drop_append_self]
    apply closeBy_sem step join P I S height hj hjoin hmono hvalid hstep
      fuel (pool ++ ext) ext hi' hnew
    intro v hv
    cases mem_append_of pool ext hv with
    | inr h => exact Or.inl h
    | inl h =>
      refine Or.inr ?_
      intro b hb
      cases hp v h with
      | inl hfresh => exact hread b (mem_flatMap_to step hfresh hb)
      | inr hdone =>
        exact hmono pool ext b hi hi' (hstep v (hvalid pool hi v h) b hb).1 (hdone b hb)

/-- A fold of joins reads through a map of its members: at a join
whose image is the image's join at the mapped member, the folded
pool's image is the mapped members' fold from the pool's image. -/
theorem foldl_map_join {α β : Type} (f : α → β) (join' : List α → α → List α)
    (join : List β → β → List β)
    (hj : ∀ l a, (join' l a).map f = join (l.map f) (f a)) :
    ∀ (l : List α) (s : List α), (l.foldl join' s).map f = (l.map f).foldl join (s.map f)
  | [], _ => rfl
  | a :: t, s => by
    show (t.foldl join' (join' s a)).map f = (t.map f).foldl join (join (s.map f) (f a))
    rw [foldl_map_join f join' join hj t (join' s a), hj s a]

/-- The closure reads through a map of its members: at a step and a
join whose images are the image's step and join, the closure's
image is the closure at the images from the mapped seeds and the
mapped last round. -/
theorem closeBy_map {α β : Type} (f : α → β) (step' : α → List α)
    (join' : List α → α → List α) (step : β → List β) (join : List β → β → List β)
    (hs : ∀ a, (step' a).map f = step (f a))
    (hj : ∀ l a, (join' l a).map f = join (l.map f) (f a)) :
    ∀ (fuel : Nat) (s fr : List α),
      (closeBy step' join' fuel s fr).map f = closeBy step join fuel (s.map f) (fr.map f)
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | fuel + 1, s, a :: fr => by
    show ((closeByS step' join' (fun l => l) fuel (((a :: fr).flatMap step').foldl join' s)
        ((((a :: fr).flatMap step').foldl join' s).drop s.length))).map f
      = closeByS step join (fun l => l) fuel ((((a :: fr).map f).flatMap step).foldl join
          (s.map f))
        (((((a :: fr).map f).flatMap step).foldl join (s.map f)).drop (s.map f).length)
    have hfm : ((a :: fr).flatMap step').map f = ((a :: fr).map f).flatMap step := by
      rw [map_flatMap, flatMap_map f step (a :: fr)]
      exact flatMap_congr_all _ _ hs (a :: fr)
    have hpool : (((a :: fr).flatMap step').foldl join' s).map f
        = (((a :: fr).map f).flatMap step).foldl join (s.map f) := by
      rw [foldl_map_join f join' join hj, hfm]
    rw [← hpool, length_map, map_drop]
    exact closeBy_map f step' join' step join hs hj fuel _ _

/-- A join kept by a read and projecting to a list join folds to the
list fold at the projection, the read kept along the fold. -/
theorem foldl_proj {α σ : Type} (join : σ → α → σ)
    (joinL : List α → α → List α) (proj : σ → List α) (I : σ → Prop)
    (hI : ∀ s a, I s → I (join s a))
    (hp : ∀ s a, I s → proj (join s a) = joinL (proj s) a) :
    ∀ (l : List α) (s : σ), I s →
      I (l.foldl join s) ∧ proj (l.foldl join s) = l.foldl joinL (proj s)
  | [], _, hs => ⟨hs, rfl⟩
  | a :: t, s, hs => by
    show I (t.foldl join (join s a))
      ∧ proj (t.foldl join (join s a)) = t.foldl joinL (joinL (proj s) a)
    rw [← hp s a hs]
    exact foldl_proj join joinL proj I hI hp t (join s a) (hI s a hs)

/-- The closure over a pool with its own data projects to the
closure at the list join: the read kept by the join and the join
projecting to the list join at the read, the two closures read one
member list round by round. -/
theorem closeByS_proj {α σ : Type} (step : α → List α)
    (join : σ → α → σ) (joinL : List α → α → List α)
    (proj : σ → List α) (I : σ → Prop)
    (hI : ∀ s a, I s → I (join s a))
    (hp : ∀ s a, I s → proj (join s a) = joinL (proj s) a) :
    ∀ (fuel : Nat) (s : σ) (fr : List α), I s →
      I (closeByS step join proj fuel s fr)
      ∧ proj (closeByS step join proj fuel s fr)
        = closeBy step joinL fuel (proj s) fr
  | 0, _, _, hs => ⟨hs, rfl⟩
  | _ + 1, _, [], hs => ⟨hs, rfl⟩
  | fuel + 1, s, a :: fr, hs => by
    show I (closeByS step join proj fuel
        (((a :: fr).flatMap step).foldl join s)
        ((proj (((a :: fr).flatMap step).foldl join s)).drop
          (proj s).length))
      ∧ proj (closeByS step join proj fuel
        (((a :: fr).flatMap step).foldl join s)
        ((proj (((a :: fr).flatMap step).foldl join s)).drop
          (proj s).length))
      = closeBy step joinL fuel
          (((a :: fr).flatMap step).foldl joinL (proj s))
          ((((a :: fr).flatMap step).foldl joinL (proj s)).drop
            (proj s).length)
    obtain ⟨hI', hp'⟩ := foldl_proj join joinL proj I hI hp
      ((a :: fr).flatMap step) s hs
    have hrec := closeByS_proj step join joinL proj I hI hp fuel
      (((a :: fr).flatMap step).foldl join s)
      ((proj (((a :: fr).flatMap step).foldl join s)).drop
        (proj s).length) hI'
    rw [hp'] at hrec
    rw [hp']
    exact hrec




/-- Two lists at one count per member are one length: each length
is the counts' fold over one joined covering index. -/
theorem length_eq_of_countOf {α : Type} [DecidableEq α]
    (l1 l2 : List α)
    (h : ∀ x, countOf x l1 = countOf x l2) :
    l1.length = l2.length := by
  have hd : distinctList (dedupF (l1 ++ l2)) :=
    fun x _ => countOf_dedupF_le x _
  have h1 := countOf_partition l1 (dedupF (l1 ++ l2)) hd
    (fun x hx => mem_dedupF (mem_append_left _ hx))
  have h2 := countOf_partition l2 (dedupF (l1 ++ l2)) hd
    (fun x hx => mem_dedupF (mem_append_right _ hx))
  rw [← h1, ← h2]
  exact famFold_congr_all Nat.add 0 _ _ h (dedupF (l1 ++ l2))
/-- A positional read is a member, its count occupied. -/
theorem countOf_getAt_pos {α : Type} [DecidableEq α]
    (d : α) : ∀ (l : List α) (q : Nat), q < l.length →
      0 < countOf (getAt d l q) l
  | [], q, hq => absurd hq (Nat.not_lt_zero q)
  | a :: t, 0, _ => by
    show 0 < countOf a (a :: t)
    rw [countOf_cons, if_pos rfl, Nat.add_comm]
    exact Nat.succ_pos _
  | a :: t, q + 1, hq => by
    show 0 < countOf (getAt d t q) (a :: t)
    rw [countOf_cons]
    exact Nat.lt_of_lt_of_le
      (countOf_getAt_pos d t q (Nat.lt_of_succ_lt_succ hq))
      (Nat.le_add_left _ _)

/-- Two distinct keys at one value put the value's count at two or
beyond. -/
theorem countOf_two_pos {α : Type} [DecidableEq α] (d : α) :
    ∀ (l : List α) (p q : Nat), p < l.length → q < l.length →
      ¬ p = q → getAt d l p = getAt d l q →
      2 ≤ countOf (getAt d l p) l
  | [], p, _, hp, _, _, _ => absurd hp (Nat.not_lt_zero p)
  | _ :: _, 0, 0, _, _, hne, _ => absurd rfl hne
  | a :: t, 0, q + 1, _, hq, _, heq => by
    show 2 ≤ countOf a (a :: t)
    rw [countOf_cons, if_pos rfl, Nat.add_comm]
    refine Nat.succ_le_succ ?_
    have heq' : a = getAt d t q := heq
    rw [heq']
    exact countOf_getAt_pos d t q (Nat.lt_of_succ_lt_succ hq)
  | a :: t, p + 1, 0, hp, _, _, heq => by
    show 2 ≤ countOf (getAt d t p) (a :: t)
    rw [countOf_cons]
    have heq' : getAt d t p = a := heq
    rw [heq', if_pos rfl, Nat.add_comm]
    refine Nat.succ_le_succ ?_
    rw [← heq']
    exact countOf_getAt_pos d t p (Nat.lt_of_succ_lt_succ hp)
  | a :: t, p + 1, q + 1, hp, hq, hne, heq => by
    show 2 ≤ countOf (getAt d t p) (a :: t)
    rw [countOf_cons]
    exact Nat.le_trans
      (countOf_two_pos d t p q (Nat.lt_of_succ_lt_succ hp)
        (Nat.lt_of_succ_lt_succ hq)
        (fun he => hne (congrArg Nat.succ he)) heq)
      (Nat.le_add_left _ _)

/-- A distinct family's tail is distinct. -/
theorem distinct_tail {α : Type} [DecidableEq α] {a : α}
    {t : List α} (h : distinctList (a :: t)) :
    distinctList t := by
  intro x _
  refine Nat.le_trans ?_ (distinctList_all h x)
  show countOf x t ≤ countOf x (a :: t)
  rw [countOf_cons]
  exact Nat.le_add_left _ _

/-- The positional read is injective on a distinct family. -/
theorem getAt_inj_distinct {α : Type} [DecidableEq α]
    (d : α) : ∀ (l : List α), distinctList l →
      ∀ p q, p < l.length → q < l.length →
      getAt d l p = getAt d l q → p = q
  | [], _, p, _, hp, _, _ => absurd hp (Nat.not_lt_zero p)
  | a :: t, h, 0, 0, _, _, _ => rfl
  | a :: t, h, 0, q + 1, _, hq, heq => by
    have h2 : 2 ≤ countOf a (a :: t) := by
      rw [countOf_cons, if_pos rfl, Nat.add_comm]
      refine Nat.succ_le_succ ?_
      have heq' : a = getAt d t q := heq
      rw [heq']
      exact countOf_getAt_pos d t q (Nat.lt_of_succ_lt_succ hq)
    exact absurd (Nat.le_trans h2 (distinctList_all h a))
      (Nat.not_succ_le_self 1)
  | a :: t, h, p + 1, 0, hp, _, heq => by
    have h2 : 2 ≤ countOf a (a :: t) := by
      rw [countOf_cons, if_pos rfl, Nat.add_comm]
      refine Nat.succ_le_succ ?_
      have heq' : getAt d t p = a := heq
      rw [← heq']
      exact countOf_getAt_pos d t p (Nat.lt_of_succ_lt_succ hp)
    exact absurd (Nat.le_trans h2 (distinctList_all h a))
      (Nat.not_succ_le_self 1)
  | a :: t, h, p + 1, q + 1, hp, hq, heq =>
    congrArg Nat.succ (getAt_inj_distinct d t (distinct_tail h) p q
      (Nat.lt_of_succ_lt_succ hp) (Nat.lt_of_succ_lt_succ hq) heq)

/-- Distinct mapped keys identify their original family members. -/
theorem map_inj_distinct {α β : Type} [DecidableEq β] (f : α → β) (l : List α)
    (hd : distinctList (l.map f)) (p q : α) (hp : p ∈ l) (hq : q ∈ l) (he : f p = f q) : p = q := by
  obtain ⟨i, hi, hip⟩ := getAt_of_mem p hp
  obtain ⟨j, hj, hjq⟩ := getAt_of_mem p hq
  have hij : i = j := getAt_inj_distinct (f p) (l.map f) hd i j
    (by rw [length_map]; exact hi) (by rw [length_map]; exact hj) (by
      rw [getAt_map p (f p) f l i hi, getAt_map p (f p) f l j hj, hip, hjq]
      exact he)
  rw [hij] at hip
  exact hip.symm.trans hjq

/-- A family member counts once where its mapped keys are distinct. -/
theorem countOf_distinct_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) (hd : distinctList (l.map f)) (p : α) (hp : p ∈ l) : countOf p l = 1 := by
  have h := countOf_map_inj f p l
    (fun q hq he => map_inj_distinct f l hd q p (mem_of_countOf_pos q l hq) hp he)
  rw [← h]
  exact countOf_distinct_one hd (mem_map_to f hp)

/-- A family read injectively at its keys is distinct,
`getAt_inj_distinct`'s converse. -/
theorem distinct_of_getAt_inj {α : Type} [DecidableEq α]
    (d : α) : ∀ l : List α,
      (∀ p q, p < l.length → q < l.length →
        getAt d l p = getAt d l q → p = q) → distinctList l
  | [], _ => fun x hx => nomatch hx
  | a :: t, h => by
    have ht : distinctList t :=
      distinct_of_getAt_inj d t (fun p q hp hq he =>
        Nat.succ.inj (h (p + 1) (q + 1) (Nat.succ_lt_succ hp)
          (Nat.succ_lt_succ hq) he))
    have ha : countOf a t = 0 := by
      match Nat.eq_zero_or_pos (countOf a t) with
      | .inl hz => exact hz
      | .inr hpos =>
        match getAt_of_mem d (mem_of_countOf_pos a t hpos) with
        | ⟨k, hk, he⟩ =>
          exact absurd (h 0 (k + 1) (Nat.succ_pos t.length)
              (Nat.succ_lt_succ hk) he.symm)
            (fun hc => Nat.noConfusion hc)
    intro x _
    rw [countOf_cons]
    by_cases hxa : x = a
    · rw [if_pos hxa, hxa, ha]
      exact Nat.le_refl 1
    · rw [if_neg hxa, Nat.zero_add]
      exact distinctList_all ht x

/-- Two families at one length and every entry equal are one
family. -/
theorem getAt_ext {α : Type} (d : α) :
    ∀ u v : List α, u.length = v.length →
      (∀ i, i < u.length → getAt d u i = getAt d v i) → u = v
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl
  | a :: u, b :: v, hl, he => by
    rw [show a = b from he 0 (Nat.succ_pos _),
      getAt_ext d u v (Nat.succ.inj hl)
        (fun i hi => he (i + 1) (Nat.succ_lt_succ hi))]

/-! The balance carrier's order: the cross-added members' own
at-or-below read, with the ground order's sum, transitivity and
cancellation hand-rolled beneath it (the core's `le` kit reads
through `propext`). -/

/-- The memberwise swap keeps the one-value read. -/
theorem swap_congr {x y : BPair} (h : x.oneValue y) :
    x.swap.oneValue y.swap := by
  show x.snd + y.fst = y.snd + x.fst
  exact ((add_comm x.snd y.fst).trans h.symm).trans
    (add_comm x.fst y.snd)

/-- At or below at the balance carrier: the cross-added members'
own order. -/
instance instGround33 : LE BPair := ⟨fun x y => x.fst + y.snd ≤ y.fst + x.snd⟩

instance instGround34 (x y : BPair) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.fst + y.snd ≤ y.fst + x.snd))

/-- The ground order sums. -/
theorem posLeAdd {a b c d : Pos} (h : a ≤ b)
    (h' : c ≤ d) : a + c ≤ b + d :=
  match h, h' with
  | Or.inl e, Or.inl e' => Or.inl (by rw [e, e'])
  | Or.inl e, Or.inr ⟨g, hg⟩ =>
    Or.inr ⟨g, by rw [e, ground.add_assoc, hg]⟩
  | Or.inr ⟨g, hg⟩, Or.inl e' =>
    Or.inr ⟨g, by rw [e', ground.add_right_comm, hg]⟩
  | Or.inr ⟨g, hg⟩, Or.inr ⟨g', hg'⟩ =>
    Or.inr ⟨g + g', by rw [ground.add_add_comm, hg, hg']⟩

/-- A shared summand cancels on the right of the ground order. -/
theorem posLeCancelR {a b c : Pos}
    (h : a + c ≤ b + c) : a ≤ b :=
  match h with
  | Or.inl e => Or.inl (ground.add_right_cancel e)
  | Or.inr ⟨g, hg⟩ => Or.inr ⟨g, ground.add_right_cancel
      (show a + g + c = b + c by
        rw [ground.add_right_comm a g c]; exact hg)⟩

/-- The unit enters both sides of the ground order. -/
theorem posLeShift {a b : Pos} (h : a ≤ b) :
    Pos.one + a ≤ b + Pos.one :=
  match h with
  | Or.inl e => Or.inl (by rw [e, ground.add_comm])
  | Or.inr ⟨g, hg⟩ =>
    Or.inr ⟨g, by rw [ground.add_assoc, hg, ground.add_comm]⟩

/-- At or below forbids the strict read the other way. -/
theorem posLtLe {a b : Pos} (h : a ≤ b) (h' : b < a) :
    False :=
  match h with
  | Or.inl e => ground.lt_ne h' e.symm
  | Or.inr hl => ground.lt_asymm hl h'

/-- The square carries the ground order's strict read up. -/
theorem posSqLt {a b : Pos} (h : a < b) : a * a < b * b := by
  refine lt_trans (mul_lt_mul_right a h) ?_
  rw [mul_comm b a]
  exact mul_lt_mul_right b h

/-- A square reads its root's order: the comparison of the squares
is the comparison, the trichotomy against the strict read. -/
theorem posSqLe {a b : Pos} (h : a * a ≤ b * b) : a ≤ b :=
  match trich a b with
  | Trich.eq e => Or.inl e
  | Trich.lt g hg => Or.inr ⟨g, hg⟩
  | Trich.gt g hg =>
    absurd (posSqLt (show b < a from ⟨g, hg⟩)) (posLtLe h)

/-- A square carries the ground order. -/
theorem posSqMono {a b : Pos} (h : a ≤ b) : a * a ≤ b * b :=
  le_trans (mul_le_mul_right a h)
    (by rw [mul_comm b a]; exact mul_le_mul_right b h)

/-- The ground unit is the order's floor: every ground datum sits at
or above it, the one-member site the least. -/
theorem posOneLe : ∀ p : Pos, Pos.one ≤ p
  | ⟨0⟩ => Or.inl rfl
  | ⟨n + 1⟩ => Or.inr ⟨⟨n⟩, by
      show Pos.mk (0 + n + 1) = Pos.mk (n + 1)
      rw [Nat.zero_add]⟩

/-- A ground datum sits below its own joined sum. -/
theorem posLtSelfAdd (a c : Pos) : a < a + c := ⟨c, rfl⟩

/-- A ground datum sits at or below its own joined sum. -/
theorem posLeSelfAdd (a c : Pos) : a ≤ a + c := Or.inr (posLtSelfAdd a c)

/-- The division's occupied quotient brackets the dividend: at
`(divMod a b).1 = some q` the dividend sits between `b * q` and
`b * (q + 1)`, the reconstruction read at its own remainder. -/
theorem divQuot_read (a b q : Pos) (h : (divMod a b).1 = some q) :
    b * q ≤ a ∧ a < b * succ q := by
  have hsucc : b * succ q = b * q + b := by
    show b * (q + Pos.one) = b * q + b
    rw [left_distrib, mul_one]
  have hread := divModRead_all a b
  unfold divModRead at hread
  match hdm : divMod a b with
  | (some q', some r) =>
    rw [hdm] at hread
    rw [hdm] at h
    have hq : q' = q := Option.some.inj h
    rw [hq] at hread
    refine ⟨Or.inr ⟨r, hread.1⟩, ?_⟩
    obtain ⟨g, hg⟩ := hread.2
    refine ⟨g, ?_⟩
    rw [hsucc, ← hread.1, add_assoc, hg]
  | (some q', none) =>
    rw [hdm] at hread
    rw [hdm] at h
    have hq : q' = q := Option.some.inj h
    rw [hq] at hread
    exact ⟨Or.inl hread, ⟨b, by rw [hsucc, ← hread]⟩⟩
  | (none, some r) =>
    rw [hdm] at h
    exact nomatch (show (none : Option Pos) = some q from h)
  | (none, none) =>
    rw [hdm] at h
    exact nomatch (show (none : Option Pos) = some q from h)

/-- The division's vacant quotient prices the dividend below the
divisor, the remainder arm the whole dividend. -/
theorem divQuot_vac (a b : Pos) (h : (divMod a b).1 = none) :
    a < b := by
  have hread := divModRead_all a b
  unfold divModRead at hread
  match hdm : divMod a b with
  | (some q', some r) =>
    rw [hdm] at h
    exact nomatch (show some q' = (none : Option Pos) from h)
  | (some q', none) =>
    rw [hdm] at h
    exact nomatch (show some q' = (none : Option Pos) from h)
  | (none, some r) =>
    rw [hdm] at hread
    rw [← hread.1]
    exact hread.2
  | (none, none) =>
    rw [hdm] at hread
    exact hread.elim

/-- The bracket names the quotient: a dividend between `b * q` and
`b * (q + 1)` reads the division's quotient as `q`, the uniqueness
against the trichotomy. -/
theorem divQuot_eq (a b q : Pos)
    (h1 : b * q ≤ a) (h2 : a < b * succ q) :
    (divMod a b).1 = some q := by
  have mulLeL : ∀ {x y : Pos} (c : Pos), x ≤ y → c * x ≤ c * y := by
    intro x y c hxy
    rw [mul_comm c x, mul_comm c y]
    exact mul_le_mul_right c hxy
  have succLe : ∀ {x y g : Pos}, x + g = y → succ x ≤ y := by
    intro x y g hgg
    match trich Pos.one g with
    | .lt g' hg' =>
      exact Or.inr ⟨g', by
        show x + Pos.one + g' = y
        rw [add_assoc, hg', hgg]⟩
    | .eq he =>
      exact Or.inl (by
        show x + Pos.one = y
        rw [he, hgg])
    | .gt g' hg' =>
      exact absurd (show g < Pos.one from ⟨g', hg'⟩) (not_lt_one g)
  cases hc : (divMod a b).1 with
  | none =>
    have hv := divQuot_vac a b hc
    have hh : b * Pos.one ≤ b * q := mulLeL b (posOneLe q)
    rw [mul_one] at hh
    exact (posLtLe (le_trans hh h1) hv).elim
  | some q' =>
    have hr := divQuot_read a b q' hc
    have hq : q' = q := by
      match trich q' q with
      | .eq he => exact he
      | .lt g hgg =>
        exact absurd (le_trans (mulLeL b (succLe hgg)) h1)
          (fun hx => posLtLe hx hr.2)
      | .gt g hgg =>
        exact absurd (le_trans (mulLeL b (succLe hgg)) hr.1)
          (fun hx => posLtLe hx h2)
    exact congrArg some hq

/-- The split's square identity: at a datum split as a part and its
gap, the gap against the datum joined to the part, together with
the part's square, is the datum's square — `thm:groundreads`(v)'s
cleared product identity. -/
theorem Pos.sq_split (x g N : Pos) (h : x + g = N) :
    g * (N + x) + x * x = N * N := by
  subst h
  rw [left_distrib g (x + g) x, right_distrib x g (x + g),
    left_distrib g x g, left_distrib x x g,
    mul_comm x g,
    add_assoc (g * x + g * g) (g * x) (x * x),
    add_comm (g * x) (x * x),
    add_comm (g * x + g * g) (x * x + g * x)]

/-- The cleared Bernoulli display's upper side: at a datum split as
a part and its gap, the datum's power sits at or below the gap's
power joined to the count's multiple of the part against the
datum's prior power — `thm:groundreads`(v)'s bracket base. -/
theorem Pos.bernoulli_le (a g b : Pos) (h : a + g = b) :
    ∀ k : Nat, Pos.pow b (k + 1)
      ≤ Pos.pow g (k + 1) + posOfSucc k * a * Pos.pow b k
  | 0 => by
    show b * Pos.pow b 0 ≤ g * Pos.pow g 0 + posOfSucc 0 * a * Pos.pow b 0
    rw [show Pos.pow b 0 = Pos.one from rfl,
      show Pos.pow g 0 = Pos.one from rfl,
      mul_one b, mul_one g,
      show posOfSucc 0 = Pos.one from rfl, one_mul a, mul_one a,
      add_comm g a, h]
    exact Or.inl rfl
  | k + 1 => by
    have hgb : g ≤ b := by
      rw [← h, add_comm a g]
      exact posLeSelfAdd g a
    have h1 : b * Pos.pow b (k + 1)
        ≤ b * (Pos.pow g (k + 1)
          + posOfSucc k * a * Pos.pow b k) := by
      rw [mul_comm b (Pos.pow b (k + 1)),
        mul_comm b (Pos.pow g (k + 1)
          + posOfSucc k * a * Pos.pow b k)]
      exact mul_le_mul_right b (Pos.bernoulli_le a g b h k)
    have h2 : b * (Pos.pow g (k + 1)
          + posOfSucc k * a * Pos.pow b k)
        = (a * Pos.pow g (k + 1) + g * Pos.pow g (k + 1))
          + posOfSucc k * a * Pos.pow b (k + 1) := by
      rw [left_distrib b (Pos.pow g (k + 1))
          (posOfSucc k * a * Pos.pow b k),
        show b * (posOfSucc k * a * Pos.pow b k)
            = posOfSucc k * a * Pos.pow b (k + 1) from by
          rw [mul_comm b (posOfSucc k * a * Pos.pow b k),
            mul_assoc (posOfSucc k * a) (Pos.pow b k) b,
            mul_comm (Pos.pow b k) b]
          rfl,
        ← h, right_distrib a g (Pos.pow g (k + 1)), h]
    have h3 : a * Pos.pow g (k + 1) ≤ a * Pos.pow b (k + 1) := by
      rw [mul_comm a (Pos.pow g (k + 1)), mul_comm a (Pos.pow b (k + 1))]
      exact mul_le_mul_right a (Pos.pow_le hgb (k + 1))
    have h4 : (a * Pos.pow b (k + 1) + g * Pos.pow g (k + 1))
          + posOfSucc k * a * Pos.pow b (k + 1)
        = g * Pos.pow g (k + 1)
          + posOfSucc (k + 1) * a * Pos.pow b (k + 1) := by
      rw [add_comm (a * Pos.pow b (k + 1)) (g * Pos.pow g (k + 1)),
        add_assoc (g * Pos.pow g (k + 1)) (a * Pos.pow b (k + 1))
          (posOfSucc k * a * Pos.pow b (k + 1)),
        show a * Pos.pow b (k + 1)
              + posOfSucc k * a * Pos.pow b (k + 1)
            = posOfSucc (k + 1) * a * Pos.pow b (k + 1) from by
          have h1 : Pos.one + posOfSucc k = posOfSucc (k + 1) :=
            ground.one_add (posOfSucc k)
          rw [← h1, right_distrib Pos.one (posOfSucc k) a,
            one_mul, right_distrib a (posOfSucc k * a) (Pos.pow b (k + 1))]]
    show b * Pos.pow b (k + 1)
      ≤ g * Pos.pow g (k + 1)
        + posOfSucc (k + 1) * a * Pos.pow b (k + 1)
    refine le_trans h1 ?_
    rw [h2, ← h4]
    exact posLeAdd (posLeAdd h3 (Or.inl rfl)) (Or.inl rfl)

/-- The cleared Bernoulli display's lower side: at a datum split as
a part and its gap, the gap's power joined to the count's multiple
of the part against the gap's own prior power sits at or below the
datum's power — `thm:groundreads`(v)'s bracket base, the display's
other side. -/
theorem Pos.bernoulli_ge (a g b : Pos) (h : a + g = b) :
    ∀ k : Nat, Pos.pow g (k + 1) + posOfSucc k * a * Pos.pow g k
      ≤ Pos.pow b (k + 1)
  | 0 => by
    show g * Pos.pow g 0 + posOfSucc 0 * a * Pos.pow g 0
      ≤ b * Pos.pow b 0
    rw [show Pos.pow b 0 = Pos.one from rfl,
      show Pos.pow g 0 = Pos.one from rfl,
      mul_one b, mul_one g,
      show posOfSucc 0 = Pos.one from rfl, one_mul a, mul_one a,
      add_comm g a, h]
    exact Or.inl rfl
  | k + 1 => by
    have hb : Pos.pow b (k + 1) * b = Pos.pow b (k + 1 + 1) :=
      (mul_comm (Pos.pow b (k + 1)) b).trans rfl
    have h1 : (Pos.pow g (k + 1) + posOfSucc k * a * Pos.pow g k) * b
        ≤ Pos.pow b (k + 1) * b :=
      mul_le_mul_right b (Pos.bernoulli_ge a g b h k)
    have e1 : Pos.pow g (k + 1) * g = Pos.pow g (k + 1 + 1) :=
      (mul_comm (Pos.pow g (k + 1)) g).trans rfl
    have e2 : posOfSucc k * a * Pos.pow g k * g
        = posOfSucc k * a * Pos.pow g (k + 1) := by
      rw [mul_assoc (posOfSucc k * a) (Pos.pow g k) g,
        mul_comm (Pos.pow g k) g]
      rfl
    have e3 : a * Pos.pow g (k + 1) + posOfSucc k * a * Pos.pow g (k + 1)
        = posOfSucc (k + 1) * a * Pos.pow g (k + 1) := by
      have hone : Pos.one + posOfSucc k = posOfSucc (k + 1) :=
        one_add (posOfSucc k)
      rw [← hone, right_distrib Pos.one (posOfSucc k) a, one_mul,
        right_distrib a (posOfSucc k * a) (Pos.pow g (k + 1))]
    have e4 : posOfSucc k * a * Pos.pow g k * a
        = posOfSucc k * (a * a) * Pos.pow g k := by
      rw [mul_assoc (posOfSucc k * a) (Pos.pow g k) a,
        mul_comm (Pos.pow g k) a,
        ← mul_assoc (posOfSucc k * a) a (Pos.pow g k),
        mul_assoc (posOfSucc k) a a]
    have h2 : (Pos.pow g (k + 1) + posOfSucc k * a * Pos.pow g k) * b
        = Pos.pow g (k + 1 + 1)
          + posOfSucc (k + 1) * a * Pos.pow g (k + 1)
          + posOfSucc k * (a * a) * Pos.pow g k := by
      rw [← h, right_distrib (Pos.pow g (k + 1))
          (posOfSucc k * a * Pos.pow g k) (a + g),
        left_distrib (Pos.pow g (k + 1)) a g,
        left_distrib (posOfSucc k * a * Pos.pow g k) a g,
        e1, e2, e4, mul_comm (Pos.pow g (k + 1)) a,
        add_comm (a * Pos.pow g (k + 1)) (Pos.pow g (k + 1 + 1)),
        add_comm (posOfSucc k * (a * a) * Pos.pow g k)
          (posOfSucc k * a * Pos.pow g (k + 1)),
        ← add_assoc (Pos.pow g (k + 1 + 1) + a * Pos.pow g (k + 1))
          (posOfSucc k * a * Pos.pow g (k + 1))
          (posOfSucc k * (a * a) * Pos.pow g k),
        add_assoc (Pos.pow g (k + 1 + 1)) (a * Pos.pow g (k + 1))
          (posOfSucc k * a * Pos.pow g (k + 1)),
        e3]
    refine le_trans (posLeSelfAdd
      (Pos.pow g (k + 1 + 1) + posOfSucc (k + 1) * a * Pos.pow g (k + 1))
      (posOfSucc k * (a * a) * Pos.pow g k)) ?_
    rw [← h2, ← hb]
    exact h1


/-- The ground order's strict read sums against an at-or-below
read. -/
theorem posLtAddLe {a b c d : Pos} (h : a < b) (h' : c ≤ d) :
    a + c < b + d :=
  match h, h' with
  | ⟨g, hg⟩, Or.inl e =>
    ⟨g, by rw [ground.add_right_comm a c g, hg, e]⟩
  | ⟨g, hg⟩, Or.inr ⟨g', hg'⟩ =>
    ⟨g + g', by rw [ground.add_add_comm a c g g', hg, hg']⟩

/-- The unit enters both sides of the ground order's strict read. -/
theorem posLtShift {a b : Pos} (h : a < b) :
    Pos.one + a < b + Pos.one :=
  match h with
  | ⟨g, hg⟩ => ⟨g, by rw [ground.add_assoc, hg, ground.add_comm]⟩

/-- At or below both ways is the ground identity. -/
theorem posLeAntisymm {a b : Pos} (h : a ≤ b) (h' : b ≤ a) : a = b :=
  match h with
  | Or.inl e => e
  | Or.inr hl => absurd (posLtLe h' hl) (fun hf => hf)

/-- The balance order's refutation read. -/
theorem leB_not_lt {x y : BPair} (h : x ≤ y) : ¬ (y < x) :=
  fun hl => posLtLe h hl

/-- The refutation read back: a refused strict order the other way
is the at-or-below read, the trichotomy the source. -/
theorem leB_of_not_lt : ∀ {x y : BPair}, ¬ (y < x) → x ≤ y := by
  intro x y h
  match trich (x.fst + y.snd) (y.fst + x.snd) with
  | Trich.lt g hg => exact Or.inr ⟨g, hg⟩
  | Trich.eq he => exact Or.inl he
  | Trich.gt g hg => exact absurd (show y < x from ⟨g, hg⟩) h

/-- The balance order at a datum with itself. -/
theorem leB_refl (x : BPair) : x ≤ x := Or.inl rfl

/-- The strict order joins the balance order, the trichotomy's own
arm. -/
theorem leB_of_lt {x y : BPair} (h : x < y) : x ≤ y := Or.inr h

/-- The balance order sums. -/
theorem leB_add {x y x' y' : BPair} (h : x ≤ y)
    (h' : x' ≤ y') : x + x' ≤ y + y' := by
  show x.fst + x'.fst + (y.snd + y'.snd)
    ≤ y.fst + y'.fst + (x.snd + x'.snd)
  rw [ground.add_add_comm x.fst x'.fst y.snd y'.snd,
    ground.add_add_comm y.fst y'.fst x.snd x'.snd]
  exact posLeAdd h h'

/-- The balance order composes. -/
theorem leB_trans {x y z : BPair} (h : x ≤ y)
    (h' : y ≤ z) : x ≤ z := by
  show x.fst + z.snd ≤ z.fst + x.snd
  refine posLeCancelR (c := y.fst + y.snd) ?_
  have e1 : x.fst + z.snd + (y.fst + y.snd)
      = x.fst + y.snd + (y.fst + z.snd) := by
    rw [ground.add_add_comm' x.fst z.snd y.fst y.snd,
      ground.add_comm z.snd y.fst]
  have e2 : z.fst + x.snd + (y.fst + y.snd)
      = y.fst + x.snd + (z.fst + y.snd) := by
    rw [ground.add_add_comm z.fst x.snd y.fst y.snd,
      ground.add_add_comm y.fst x.snd z.fst y.snd,
      ground.add_comm z.fst y.fst]
  rw [e1, e2]
  exact posLeAdd h h'

/-- The homogeneity principle at the balance order, the first
datum. -/
theorem leB_congr_left {x x' y : BPair} (hx : x.oneValue x')
    (h : x ≤ y) : x' ≤ y := by
  show x'.fst + y.snd ≤ y.fst + x'.snd
  refine posLeCancelR (c := x.snd) ?_
  have e1 : x'.fst + y.snd + x.snd = x.fst + y.snd + x'.snd := by
    rw [ground.add_right_comm x'.fst y.snd x.snd, ← hx,
      ground.add_right_comm x.fst x'.snd y.snd]
  have e2 : y.fst + x'.snd + x.snd = y.fst + x.snd + x'.snd :=
    ground.add_right_comm y.fst x'.snd x.snd
  rw [e1, e2]
  exact posLeAdd h (Or.inl rfl)

/-- The homogeneity principle at the balance order, the second
datum. -/
theorem leB_congr_right {x y y' : BPair} (hy : y.oneValue y')
    (h : x ≤ y) : x ≤ y' := by
  show x.fst + y'.snd ≤ y'.fst + x.snd
  refine posLeCancelR (c := y.snd) ?_
  have e1 : x.fst + y'.snd + y.snd = x.fst + y.snd + y'.snd :=
    ground.add_right_comm x.fst y'.snd y.snd
  have e2 : y'.fst + x.snd + y.snd = y.fst + x.snd + y'.snd := by
    rw [ground.add_right_comm y'.fst x.snd y.snd, ← hy,
      ground.add_right_comm y.fst y'.snd x.snd]
  rw [e1, e2]
  exact posLeAdd h (Or.inl rfl)

/-- The homogeneity principle at the balance order. -/
theorem leB_congr {x x' y y' : BPair} (hx : x.oneValue x')
    (hy : y.oneValue y') (h : x ≤ y) : x' ≤ y' :=
  leB_congr_right hy (leB_congr_left hx h)

/-- A split sum at a value prices its first summand at or below
that value, the second summand's at-or-above-unit read the
margin. -/
theorem dom_of_split {A B C : BPair} (h : (A + B).oneValue C)
    (hB : BPair.unit ≤ B) : A ≤ C :=
  leB_congr_right h
    (leB_congr_left (BPair.add_unit A)
      (leB_add (leB_refl A) hB))

/-- A datum at or above the unit joins the swapped datum's read. -/
theorem leB_unit_add {U V : BPair} (h : V.swap ≤ U) :
    BPair.unit ≤ U + V := by
  show Pos.one + (U.snd + V.snd)
    ≤ U.fst + V.fst + Pos.one
  rw [ground.add_comm U.snd V.snd]
  exact posLeShift h

/-- The read back: a sum at or above the unit prices its second
member's swap. -/
theorem leB_of_unit_add {U V : BPair}
    (h : BPair.unit ≤ U + V) : V.swap ≤ U := by
  show V.snd + U.snd ≤ U.fst + V.fst
  refine posLeCancelR (c := Pos.one) ?_
  have h' : Pos.one + (U.snd + V.snd)
      ≤ U.fst + V.fst + Pos.one := h
  rw [ground.add_comm (V.snd + U.snd) Pos.one,
    ground.add_comm V.snd U.snd]
  exact h'

/-- The strict read at the unit: a sum below the unit prices its
first member strictly below its second member's swap, the gap
carried across unchanged. -/
theorem ltB_of_add_unit {U V : BPair}
    (h : U + V < BPair.unit) : U < V.swap := by
  obtain ⟨g, hg⟩ := h
  have hg' : U.fst + V.fst + Pos.one + g
      = Pos.one + (U.snd + V.snd) := hg
  refine ⟨g, ?_⟩
  show U.fst + V.fst + g = V.snd + U.snd
  refine ground.add_right_cancel (c := Pos.one) ?_
  rw [ground.add_right_comm (U.fst + V.fst) g Pos.one, hg',
    ground.add_comm U.snd V.snd,
    ground.add_comm Pos.one (V.snd + U.snd)]

/-- The count's successor scales at the step: the count's scale
joined to the datum itself. -/
theorem ofNat_succ_mul (k : Nat) (z : BPair) :
    (BPair.ofNat (k + 1) * z).oneValue (BPair.ofNat k * z + z) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.ofNat_succ k)) ?_
  rw [BPair.right_distrib]
  exact BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofNat 1) z))
      (BPair.mul_ofNat_one z))

/-- A count scales a datum at or above the unit to one. -/
theorem leB_unit_mul : ∀ (k : Nat) {z : BPair},
    BPair.unit ≤ z → BPair.unit ≤ BPair.ofNat k * z
  | 0, z, _ =>
    leB_congr_right (BPair.oneValue_symm (BPair.unit_mul z))
      (leB_refl BPair.unit)
  | k + 1, z, h => by
    exact leB_congr_right
      (BPair.oneValue_symm (ofNat_succ_mul k z))
      (leB_congr_left (BPair.unit_add BPair.unit)
        (leB_add (leB_unit_mul k h) h))

/-- A count's growth prices a datum at or above the unit. -/
theorem leB_scale_mono {a b : Nat} (h : a ≤ b) {z : BPair}
    (hz : BPair.unit ≤ z) :
    BPair.ofNat a * z ≤ BPair.ofNat b * z := by
  have hb : a + (b - a) = b := ground.natAddSubCancel h
  have key : (BPair.ofNat a * z + BPair.ofNat (b - a) * z).oneValue
      (BPair.ofNat b * z) := by
    rw [← BPair.right_distrib]
    refine BPair.mul_congr_left ?_
    have hadd := BPair.ofNat_add a (b - a)
    rw [hb] at hadd
    exact BPair.oneValue_symm hadd
  exact leB_congr_right key
    (leB_congr_left (BPair.add_unit _)
      (leB_add (leB_refl _) (leB_unit_mul (b - a) hz)))

/-! The margin kit: the count-carrier crossing read whole — one
count per one-value class, additive over pairs at or beyond the
sum's unit, the natural entries' counts read back and returned at
one value.  The branch reads beneath it stay at the stored counts,
this module's own; the kit sits at the balance order's tier for its
unit reads. -/

/-- The cross identity's gap transport: the first pair's gap reads
off the second's members. -/
private theorem natCrossGap {u v u' v' : Nat} (h : u + v' = u' + v)
    (hle : u ≤ v) : v' = u' + (v - u) := by
  refine addCancelL u ?_
  rw [← Nat.add_assoc, Nat.add_comm u u', Nat.add_assoc,
    natAddSubCancel hle]
  exact h

/-- The margin at a dominant first member: the first count's gap. -/
private theorem BPair.marginN_fst {x : BPair}
    (h : x.snd.pred ≤ x.fst.pred) :
    x.marginN = x.fst.pred - x.snd.pred := by
  show (if x.fst.pred ≤ x.snd.pred then x.snd.pred - x.fst.pred
    else x.fst.pred - x.snd.pred) = x.fst.pred - x.snd.pred
  by_cases hle : x.fst.pred ≤ x.snd.pred
  · rw [if_pos hle, Nat.le_antisymm hle h]
  · rw [if_neg hle]

/-- The margin at a dominant second member: the second count's
gap. -/
private theorem BPair.marginN_snd {x : BPair}
    (h : x.fst.pred ≤ x.snd.pred) :
    x.marginN = x.snd.pred - x.fst.pred := by
  show (if x.fst.pred ≤ x.snd.pred then x.snd.pred - x.fst.pred
    else x.fst.pred - x.snd.pred) = x.snd.pred - x.fst.pred
  rw [if_pos h]

/-- A pair at or beyond the sum's unit reads its second count at or
below its first, the margin branch's own side. -/
private theorem BPair.unitLe_pred {x : BPair} (h : BPair.unit ≤ x) :
    x.snd.pred ≤ x.fst.pred := by
  cases h with
  | inl he =>
    have e1 : 0 + x.snd.pred = x.fst.pred + 0 :=
      Nat.succ.inj (congrArg Pos.pred he)
    rw [Nat.zero_add] at e1
    have e2 : x.snd.pred = x.fst.pred := e1
    rw [e2]
    exact Nat.le_refl _
  | inr hlt =>
    obtain ⟨g, hg⟩ := hlt
    have e1 : 0 + x.snd.pred + 1 + g.pred = x.fst.pred + 0 :=
      Nat.succ.inj (congrArg Pos.pred hg)
    rw [Nat.zero_add] at e1
    have e2 : x.snd.pred + (1 + g.pred) = x.fst.pred := by
      rw [← Nat.add_assoc]
      exact e1
    rw [← e2]
    exact Nat.le_add_right _ _

/-- The margin respects the one-value class: one value in, one
count out. -/
theorem BPair.marginN_congr {a b : BPair} (h : a.oneValue b) :
    a.marginN = b.marginN := by
  have hn : a.fst.pred + b.snd.pred = b.fst.pred + a.snd.pred :=
    Nat.succ.inj (congrArg Pos.pred h)
  by_cases hle : a.fst.pred ≤ a.snd.pred
  · have hb : b.snd.pred = b.fst.pred + (a.snd.pred - a.fst.pred) :=
      natCrossGap hn hle
    have hleb : b.fst.pred ≤ b.snd.pred := by
      rw [hb]
      exact Nat.le_add_right _ _
    rw [BPair.marginN_snd hle, BPair.marginN_snd hleb, hb, addSubSelfL]
  · have hvu : a.snd.pred ≤ a.fst.pred :=
      Nat.le_of_lt (Nat.lt_of_not_le hle)
    have hn' : a.snd.pred + b.fst.pred = b.snd.pred + a.fst.pred := by
      rw [Nat.add_comm a.snd.pred b.fst.pred,
        Nat.add_comm b.snd.pred a.fst.pred]
      exact hn.symm
    have hb : b.fst.pred = b.snd.pred + (a.fst.pred - a.snd.pred) :=
      natCrossGap hn' hvu
    have hleb : b.snd.pred ≤ b.fst.pred := by
      rw [hb]
      exact Nat.le_add_right _ _
    rw [BPair.marginN_fst hvu, BPair.marginN_fst hleb, hb, addSubSelfL]

/-- The margin adds over pairs at or beyond the sum's unit: the
sum's margin is the margins' sum. -/
theorem BPair.marginN_add {a b : BPair} (ha : BPair.unit ≤ a)
    (hb : BPair.unit ≤ b) :
    (BPair.add a b).marginN = a.marginN + b.marginN := by
  have hva := BPair.unitLe_pred ha
  have hvb := BPair.unitLe_pred hb
  have hsum : (BPair.add a b).snd.pred ≤ (BPair.add a b).fst.pred := by
    show a.snd.pred + b.snd.pred + 1 ≤ a.fst.pred + b.fst.pred + 1
    exact Nat.succ_le_succ (Nat.add_le_add hva hvb)
  rw [BPair.marginN_fst hsum, BPair.marginN_fst hva,
    BPair.marginN_fst hvb]
  show a.fst.pred + b.fst.pred + 1 - (a.snd.pred + b.snd.pred + 1)
    = a.fst.pred - a.snd.pred + (b.fst.pred - b.snd.pred)
  rw [Nat.succ_sub_succ]
  have he : a.snd.pred + b.snd.pred
      + (a.fst.pred - a.snd.pred + (b.fst.pred - b.snd.pred))
      = a.fst.pred + b.fst.pred := by
    rw [Nat.add_add_add_comm, natAddSubCancel hva, natAddSubCancel hvb]
  rw [← he, addSubSelfL]

/-- The natural entries read their margins back. -/
theorem BPair.marginN_ofNat : ∀ n : Nat, (BPair.ofNat n).marginN = n
  | 0 => rfl
  | n + 1 => by
    show (if n + 1 ≤ 0 then 0 - (n + 1) else n + 1 - 0) = n + 1
    rw [if_neg (Nat.not_succ_le_zero n)]
    rfl

/-- Two naturals entering the pair carrier at one value are one
natural, the margin read at both entries. -/
theorem BPair.ofNat_inj {u v : Nat}
    (h : (BPair.ofNat u).oneValue (BPair.ofNat v)) : u = v := by
  rw [← BPair.marginN_ofNat u, ← BPair.marginN_ofNat v]
  exact BPair.marginN_congr h

/-- A count's first member is its successor. -/
theorem BPair.ofNat_fst : ∀ n : Nat, (BPair.ofNat n).fst = posOfSucc n
  | 0 => rfl
  | _ + 1 => rfl

/-- A count's second member is the unit. -/
theorem BPair.ofNat_snd : ∀ n : Nat, (BPair.ofNat n).snd = Pos.one
  | 0 => rfl
  | _ + 1 => rfl

/-- A pair at or beyond the sum's unit returns to its margin's
natural entry, one value. -/
theorem BPair.ofNat_marginN {b : BPair} (h : BPair.unit ≤ b) :
    b.oneValue (BPair.ofNat b.marginN) := by
  have hv := BPair.unitLe_pred h
  rw [BPair.marginN_fst hv]
  show b.fst + (BPair.ofNat (b.fst.pred - b.snd.pred)).snd
    = (BPair.ofNat (b.fst.pred - b.snd.pred)).fst + b.snd
  rw [BPair.ofNat_fst, BPair.ofNat_snd]
  exact congrArg Pos.mk (by
    show b.fst.pred + 0 + 1 = b.fst.pred - b.snd.pred + b.snd.pred + 1
    rw [subAdd hv])

/-- A datum beyond the sum's unit has an occupied margin. -/
theorem BPair.marginN_pos {x : BPair} (h : BPair.unit < x) :
    0 < BPair.marginN x := by
  match Nat.eq_zero_or_pos (BPair.marginN x) with
  | Or.inr hp => exact hp
  | Or.inl h0 =>
    have hx := BPair.ofNat_marginN (ground.leB_of_lt h)
    rw [h0] at hx
    exact absurd
      (BPair.lt_congr (BPair.oneValue_refl BPair.unit) hx h)
      (by decide +kernel)

/-- A collapse beyond the sum's unit returns its margin's one-member
site, the occupancy converter at the margin count's predecessor. -/
def BPair.marginPos (b : BPair) : Pos := posOfNat b.marginN

/-- The margin's site reads its own datum back. -/
theorem BPair.marginPos_read {b : BPair} (h : BPair.unit < b) :
    (BPair.ofPos (BPair.marginPos b)).oneValue b := by
  have hp : 0 < b.marginN := BPair.marginN_pos h
  have he : BPair.ofPos (BPair.marginPos b) = BPair.ofNat b.marginN := by
    show BPair.ofNat (b.marginN - 1 + 1) = BPair.ofNat b.marginN
    rw [subAdd hp]
  rw [he]
  exact BPair.oneValue_symm (BPair.ofNat_marginN (leB_of_lt h))

/-! The side bridges at the balance carrier: the order against the
sum's unit is the members' own order, both directions and both
strictnesses, with the cross-multiplied comparison beneath them and
the off-unit sharpening at the end. -/

/-- A datum at or above the sum's unit has its lower member at or
below its upper. -/
theorem sideOfUnitLe {x : BPair} (h : BPair.unit ≤ x) :
    x.snd ≤ x.fst := by
  refine posLeCancelR (c := Pos.one) ?_
  rw [add_comm x.snd Pos.one]
  exact h

/-- The converse read: the members' order prices the datum against
the sum's unit. -/
theorem unitLeOfSide {x : BPair} (h : x.snd ≤ x.fst) :
    BPair.unit ≤ x := posLeShift h

/-- A gap above transports along the one-value class. -/
theorem gapCongr {x y : BPair} {g : Pos} (h : x.oneValue y)
    (hg : x.snd + g = x.fst) : y.snd + g = y.fst := by
  have h' : x.fst + y.snd = y.fst + x.snd := h
  rw [← hg] at h'
  refine add_left_cancel
    (show x.snd + (y.snd + g) = x.snd + y.fst from ?_)
  rw [add_comm y.snd g, ← add_assoc x.snd g y.snd,
    h', add_comm y.fst x.snd]

/-- A gap below transports along the one-value class, the swap's
own reading of `gapCongr`. -/
theorem gapCongrL {x y : BPair} {g : Pos} (h : x.oneValue y)
    (hg : x.fst + g = x.snd) : y.fst + g = y.snd :=
  gapCongr (swap_congr h) hg

/-- A side at or above transports along the one-value class. -/
theorem side_congr {x y : BPair} (h : x.oneValue y)
    (hx : x.snd ≤ x.fst) : y.snd ≤ y.fst := by
  have h' : x.fst + y.snd = y.fst + x.snd := h
  match hx with
  | Or.inl he =>
    refine Or.inl ?_
    rw [← he] at h'
    exact add_left_cancel
      (show x.snd + y.snd = x.snd + y.fst from by
        rw [h', add_comm y.fst x.snd])
  | Or.inr ⟨g, hg⟩ => exact Or.inr ⟨g, gapCongr h hg⟩

/-- A datum strictly above the sum's unit has its lower member
strictly below its upper. -/
theorem sideOfUnitLt {x : BPair} (h : BPair.unit < x) :
    x.snd < x.fst := by
  obtain ⟨g, hg⟩ := h
  have hg' : Pos.one + x.snd + g = x.fst + Pos.one := hg
  refine ⟨g, ?_⟩
  refine add_left_cancel (a := Pos.one) ?_
  rw [← add_assoc, hg']
  exact add_comm x.fst Pos.one

/-- The four-term regrouping the cross-multiplied gap runs on. -/
private theorem posAC (A B C D : Pos) :
    A + B + (A + C) + D = A + C + (B + D) + A := by
  rw [add_add_comm A B A C, add_add_comm A C B D,
    add_assoc (A + A) (B + C) D, add_assoc B C D,
    add_assoc (A + B) (C + D) A,
    add_comm (C + D) A,
    ← add_assoc (A + B) A (C + D),
    add_assoc A B A, add_comm B A,
    ← add_assoc A A B,
    add_assoc (A + A) B (C + D)]

/-- The cross-multiplied comparison's gap identity: two gaps join
their product onto the crossed sum.  The balance carrier's margin
rule is this identity read at the product's two members, the
descent's exact cofactor its consumer. -/
theorem crossGap {p q r t g h : Pos} (hp : q + g = p)
    (ht : r + h = t) :
    p * r + q * t + g * h = p * t + q * r := by
  rw [← hp, ← ht, right_distrib q g r,
    right_distrib q g (r + h), left_distrib q r h,
    left_distrib g r h]
  exact posAC (q * r) (g * r) (q * h) (g * h)

/-- Two at-or-below reads cross-multiply. -/
theorem crossLe {p q r t : Pos} (hp : q ≤ p) (ht : r ≤ t) :
    p * r + q * t ≤ p * t + q * r := by
  match hp, ht with
  | Or.inl e, _ =>
    refine Or.inl ?_
    rw [← e]
    exact add_comm (q * r) (q * t)
  | Or.inr _, Or.inl e =>
    refine Or.inl ?_
    rw [← e]
  | Or.inr ⟨g, hg⟩, Or.inr ⟨h, hh⟩ => exact Or.inr ⟨g * h, crossGap hg hh⟩

/-- Two strict reads cross-multiply strictly. -/
theorem crossLt {p q r t : Pos} (hp : q < p) (ht : r < t) :
    p * r + q * t < p * t + q * r := by
  obtain ⟨g, hg⟩ := hp
  obtain ⟨h, hh⟩ := ht
  exact ⟨g * h, crossGap hg hh⟩

/-- A datum at or above the sum's unit and off it sits strictly
above. -/
theorem ltOfLeOff {z : BPair} (h : BPair.unit ≤ z)
    (hne : ¬ z.oneValue BPair.unit) : BPair.unit < z :=
  match h with
  | Or.inl e =>
    absurd (show z.fst + Pos.one = Pos.one + z.snd from e.symm) hne
  | Or.inr hl => hl

/-- The sum's unit reads one value with its own positive scale. -/
theorem unitScale (w : Pos) :
    BPair.unit.oneValue (BPair.unit.scale w) := by
  show Pos.one + Pos.one * w = Pos.one * w + Pos.one
  exact add_comm _ _

/-! The order kit at a positive rescaling: the comparison against
the sum's unit passes both ways through a clearing. -/

/-- A lower-side datum keeps its side at every positive scale. -/
theorem scaleLtUnit {y : BPair} (w : Pos) (h : y < BPair.unit) :
    y.scale w < BPair.unit :=
  BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (unitScale w)) (BPair.scale_lt w h)

/-- The scale reflects the lower side, the clearing read back. -/
theorem ltUnitOfScale {y : BPair} {w : Pos}
    (h : y.scale w < BPair.unit) : y < BPair.unit :=
  BPair.lt_of_scale_lt
    (BPair.lt_congr (BPair.oneValue_refl _) (unitScale w) h)

/-- The scale reflects the at-or-above read. -/
theorem unitLeOfScale {y : BPair} {w : Pos}
    (h : BPair.unit ≤ y.scale w) : BPair.unit ≤ y :=
  leB_of_not_lt (fun hlt => leB_not_lt h (scaleLtUnit w hlt))

/-- An at-or-above read keeps its side at every positive scale. -/
theorem unitLeScale {y : BPair} (w : Pos)
    (h : BPair.unit ≤ y) : BPair.unit ≤ y.scale w :=
  leB_of_not_lt (fun hlt => leB_not_lt h (ltUnitOfScale hlt))

/-- The scale's monotone read at a member at or beyond the unit:
the larger weight keeps the side. -/
theorem leB_scaleMono {z : BPair} (hz : BPair.unit ≤ z)
    {a b : Pos} (h : a ≤ b) : z.scale a ≤ z.scale b :=
  match h with
  | Or.inl e =>
    leB_congr_right
      (BPair.oneValue_of_eq (congrArg z.scale e)) (leB_refl _)
  | Or.inr ⟨g, hg⟩ =>
    leB_congr_right
      (BPair.oneValue_of_eq (congrArg z.scale hg))
      (leB_congr_right
        (BPair.oneValue_of_eq (BPair.scale_addW z a g).symm)
        (leB_congr_left (BPair.add_unit (z.scale a))
          (leB_add (leB_refl (z.scale a))
            (unitLeScale g hz))))

/-- A member at or beyond its own swap sits at or beyond the
unit, the doubled member's read. -/
theorem unitLeOfSwap {z : BPair} (h : z.swap ≤ z) :
    BPair.unit ≤ z :=
  unitLeOfScale (w := 2)
    (leB_congr_right
      (BPair.oneValue_of_eq (BPair.scale_two z).symm)
      (leB_unit_add h))

/-- A refused decidable read is the refusal. -/
theorem notOfBang {P : Prop} {inst : Decidable P}
    (h : (!@decide P inst) = true) : ¬ P :=
  match inst, h with
  | isTrue _, hh => Bool.noConfusion hh
  | isFalse hn, _ => hn

/-- One value at two data is the sum's unit at the crossed
difference. -/
theorem unitOfOne {x y : BPair} (h : x.oneValue y) :
    (x + y.swap).oneValue BPair.unit := by
  show x.fst + y.snd + Pos.one = Pos.one + (x.snd + y.fst)
  rw [h, add_comm Pos.one (x.snd + y.fst),
    add_comm x.snd y.fst]

/-- A pair at equal members sits at the sum's unit: the members'
one value crosses against the unit on each side. -/
theorem BPair.oneValue_of_eqMem {x : BPair} (h : x.fst = x.snd) :
    x.oneValue BPair.unit := by
  show x.fst + Pos.one = Pos.one + x.snd
  rw [h]
  exact ground.add_comm x.snd Pos.one

/-- The sum's unit rescales to itself at every second datum. -/
theorem BPair.unit_scale (w : Pos) :
    (BPair.unit.scale w).oneValue BPair.unit :=
  BPair.oneValue_of_eqMem
    (rfl : (BPair.unit.scale w).fst = (BPair.unit.scale w).snd)

/-- A datum reading its own memberwise swap sits at the sum's unit:
the two members' doublings agree, and a gap either way would move
the doubled member off itself, so the members are equal. -/
theorem BPair.unitOfSwap {x : BPair} (h : x.oneValue x.swap) :
    x.oneValue BPair.unit := by
  have h' : x.fst + x.fst = x.snd + x.snd := h
  have heq : x.fst = x.snd := by
    match x.side with
    | Trich.eq he => exact he
    | Trich.lt g hg =>
      rw [← hg, ground.add_add_comm x.fst g x.fst g] at h'
      exact absurd h'.symm (ground.add_ne_left (x.fst + x.fst) (g + g))
    | Trich.gt g hg =>
      rw [← hg, ground.add_add_comm x.snd g x.snd g] at h'
      exact absurd h' (ground.add_ne_left (x.snd + x.snd) (g + g))
  exact BPair.oneValue_of_eqMem heq

/-- The converse read: the sum's unit at the crossed difference is
one value at the two data. -/
theorem oneOfUnit {x y : BPair}
    (h : (x + y.swap).oneValue BPair.unit) : x.oneValue y := by
  show x.fst + y.snd = y.fst + x.snd
  have h' : x.fst + y.snd + Pos.one = Pos.one + (x.snd + y.fst) := h
  refine add_right_cancel (c := Pos.one) ?_
  rw [h', add_comm Pos.one (x.snd + y.fst),
    add_comm x.snd y.fst]

/-! The membership residual's arithmetic: the cancellation at an
off-unit factor, the equal-membered read's bridge to the sum's
unit, the squares' one-sided reads with the balanced sum forcing
each summand, and the swap-sum's inversion — the positive pairing's
whole ground kit. -/

/-- The unit clears from both sides of a ground identity, the
balance read's own cancellation. -/
theorem add_cancel_ones {a b : Pos}
    (h : a + Pos.one = Pos.one + b) : a = b :=
  add_left_cancel
    ((add_comm Pos.one a).trans h)

/-- The converse read: a pair at the sum's unit has equal members,
the unit cleared from both sides. -/
theorem BPair.eqMem_of_oneValue {x : BPair}
    (h : x.oneValue BPair.unit) : x.fst = x.snd :=
  add_cancel_ones h

/-- The cancellation at an off-unit factor: the pairs' integral
read, a product at the sum's unit with one factor off it forcing
the other there. -/
theorem mul_cancel_unit {c x : BPair}
    (hc : ¬ c.oneValue BPair.unit)
    (h : (c * x).oneValue BPair.unit) : x.oneValue BPair.unit := by
  have h' : c.fst * x.fst + c.snd * x.snd
      = c.fst * x.snd + c.snd * x.fst := add_cancel_ones h
  match c.side with
  | Trich.eq he =>
    exact absurd (show c.fst + Pos.one = Pos.one + c.snd from by
      rw [he, add_comm]) hc
  | Trich.lt g hg =>
    -- c.snd = c.fst + g
    have h2 : c.fst * x.fst + (c.fst * x.snd + g * x.snd)
        = c.fst * x.snd + (c.fst * x.fst + g * x.fst) := by
      have h3 : c.snd * x.snd = c.fst * x.snd + g * x.snd := by
        rw [← hg, right_distrib]
      have h4 : c.snd * x.fst = c.fst * x.fst + g * x.fst := by
        rw [← hg, right_distrib]
      rw [← h3, ← h4]
      exact h'
    have h5 : g * x.snd = g * x.fst := by
      have h6 : (c.fst * x.fst + c.fst * x.snd) + g * x.snd
          = (c.fst * x.fst + c.fst * x.snd) + g * x.fst := by
        rw [add_assoc, h2, ← add_assoc,
          add_comm (c.fst * x.fst) (c.fst * x.snd),
          add_assoc]
      exact add_left_cancel h6
    exact BPair.oneValue_of_eqMem (mul_left_cancel h5).symm
  | Trich.gt g hg =>
    -- c.fst = c.snd + g
    have h3 : c.fst * x.fst = c.snd * x.fst + g * x.fst := by
      rw [← hg, right_distrib]
    have h4 : c.fst * x.snd = c.snd * x.snd + g * x.snd := by
      rw [← hg, right_distrib]
    have h5 : (c.snd * x.fst + g * x.fst) + c.snd * x.snd
        = (c.snd * x.snd + g * x.snd) + c.snd * x.fst := by
      rw [← h3, ← h4]
      exact h'
    rw [add_right_comm (c.snd * x.fst) (g * x.fst)
        (c.snd * x.snd),
      add_right_comm (c.snd * x.snd) (g * x.snd)
        (c.snd * x.fst),
      add_comm (c.snd * x.snd) (c.snd * x.fst)] at h5
    exact BPair.oneValue_of_eqMem (mul_left_cancel (add_left_cancel h5))

/-- A product of two members off the equal-membered class sits off it,
`mul_cancel_unit`'s contrapositive at the two factors. -/
theorem mulOffUnit {c x : BPair} (hc : ¬ c.oneValue BPair.unit)
    (hx : ¬ x.oneValue BPair.unit) : ¬ (c * x).oneValue BPair.unit :=
  fun h => hx (mul_cancel_unit hc h)

/-- The square's expansion at a gap: the two members' squares
against the cross products, the gap's square the difference. -/
private theorem sq_gap (p g : Pos) :
    p * p + (p + g) * (p + g)
      = (p * (p + g) + (p + g) * p) + g * g := by
  rw [right_distrib p g (p + g), left_distrib p p g,
    left_distrib g p g, right_distrib p g p,
    mul_comm g p]
  -- LHS: p*p + ((p*p + p*g) + (p*g + g*g))
  -- RHS: ((p*p + p*g) + (p*p + p*g)) + g*g
  rw [← add_assoc (p * p) (p * p + p * g) (p * g + g * g),
    ← add_assoc (p * p + (p * p + p * g)) (p * g) (g * g)]
  refine congrArg (fun z => z + g * g) ?_
  -- (p*p + (p*p + p*g)) + p*g = (p*p + p*g) + (p*p + p*g)
  rw [add_add_comm (p * p) (p * g) (p * p) (p * g),
    ← add_assoc (p * p) (p * p) (p * g),
    add_assoc (p * p + p * p) (p * g) (p * g)]

/-- A square's side: the second member at or below the first, the
gap the trichotomy gap's square. -/
theorem sq_side (x : BPair) :
    (x * x).snd ≤ (x * x).fst := by
  match trich x.fst x.snd with
  | Trich.eq he =>
    refine Or.inl ?_
    show x.fst * x.snd + x.snd * x.fst
      = x.fst * x.fst + x.snd * x.snd
    rw [he]
  | Trich.lt g hg =>
    refine Or.inr ⟨g * g, ?_⟩
    show (x.fst * x.snd + x.snd * x.fst) + g * g
      = x.fst * x.fst + x.snd * x.snd
    have hq := sq_gap x.fst g
    rw [hg] at hq
    exact hq.symm
  | Trich.gt g hg =>
    refine Or.inr ⟨g * g, ?_⟩
    show (x.fst * x.snd + x.snd * x.fst) + g * g
      = x.fst * x.fst + x.snd * x.snd
    have hq := sq_gap x.snd g
    rw [hg] at hq
    rw [add_comm (x.fst * x.fst) (x.snd * x.snd),
      add_comm (x.fst * x.snd) (x.snd * x.fst)]
    exact hq.symm

/-- A balanced square reads its entry balanced: the square at the
sum's unit forces the members equal. -/
theorem entry_of_sq_null {x : BPair}
    (h : (x * x).oneValue BPair.unit) : x.oneValue BPair.unit := by
  have h' : (x * x).fst = (x * x).snd := add_cancel_ones h
  match trich x.fst x.snd with
  | Trich.eq he =>
    show x.fst + Pos.one = Pos.one + x.snd
    rw [he, add_comm]
  | Trich.lt g hg =>
    have hq := sq_gap x.fst g
    rw [hg] at hq
    -- hq : (x*x).fst-form = (x*x).snd-form + g*g; h' equates the
    -- two forms, so the gap's square joins a value to itself.
    have h2 : (x.fst * x.snd + x.snd * x.fst) + g * g
        = x.fst * x.snd + x.snd * x.fst := hq.symm.trans h'
    exact absurd h2 (add_ne_left _ (g * g))
  | Trich.gt g hg =>
    have hq := sq_gap x.snd g
    rw [hg] at hq
    have h2 : (x.snd * x.fst + x.fst * x.snd) + g * g
        = x.snd * x.fst + x.fst * x.snd := by
      have h3 : x.snd * x.snd + x.fst * x.fst
          = (x.snd * x.fst + x.fst * x.snd) + g * g := hq
      rw [← h3, add_comm (x.snd * x.snd) (x.fst * x.fst)]
      have h4 : x.fst * x.fst + x.snd * x.snd
          = x.fst * x.snd + x.snd * x.fst := h'
      rw [h4, add_comm (x.fst * x.snd) (x.snd * x.fst)]
    exact absurd h2 (add_ne_left _ (g * g))

/-- A square off equal members sits strictly above the sum's unit:
the square's side with the balanced square's refusal, the strict
read the clearing scalars' positivity (`lem:inertia`'s determinant
clearing). -/
theorem sq_pos {x : BPair} (h : ¬ x.oneValue BPair.unit) :
    BPair.unit < x * x := by
  match sq_side x with
  | Or.inl he =>
    exact absurd (entry_of_sq_null
      (show (x * x).fst + Pos.one = Pos.one + (x * x).snd by
        rw [he, add_comm])) h
  | Or.inr ⟨g, hg⟩ =>
    refine ⟨g, ?_⟩
    show Pos.one + (x * x).snd + g = (x * x).fst + Pos.one
    rw [add_assoc, hg, add_comm]

/-- A square sits at or above the sum's unit. -/
theorem unitLeSq (x : BPair) : BPair.unit ≤ x * x :=
  unitLeOfSide (sq_side x)

/-- The converse of the strict side read: the members' strict order
prices the datum strictly above the sum's unit. -/
theorem unitLtOfSide {x : BPair} (h : x.snd < x.fst) :
    BPair.unit < x := posLtShift h

/-- The margin's site read as the gap's join: at `a < b` the margin
of `⟨b : a⟩` joins `a` to `b`, the gap of `def:ground`'s order at
the difference read. -/
theorem BPair.marginPos_join {a b : Pos} (h : a < b) :
    a + BPair.marginPos ⟨b, a⟩ = b := by
  have e := BPair.marginPos_read (unitLtOfSide (x := ⟨b, a⟩) h)
  have e' : BPair.marginPos ⟨b, a⟩ + Pos.one + a = b + Pos.one := e
  rw [ground.add_right_comm (BPair.marginPos ⟨b, a⟩) Pos.one a] at e'
  rw [ground.add_comm a (BPair.marginPos ⟨b, a⟩)]
  exact ground.add_right_cancel e'

/-- At or below both ways at the balance carrier is one value. -/
theorem leB_antisymm {x y : BPair} (h : x ≤ y) (h' : y ≤ x) :
    x.oneValue y := posLeAntisymm h h'

/-- The balance order's strict read sums against an at-or-below
read. -/
theorem ltB_add {x y x' y' : BPair} (h : x < y)
    (h' : x' ≤ y') : x + x' < y + y' := by
  show x.fst + x'.fst + (y.snd + y'.snd)
    < y.fst + y'.fst + (x.snd + x'.snd)
  rw [ground.add_add_comm x.fst x'.fst y.snd y'.snd,
    ground.add_add_comm y.fst y'.fst x.snd x'.snd]
  exact posLtAddLe h h'

/-- A datum below another joins the second's swap below the sum's
unit, the gap carried across unchanged. -/
theorem ltUnit_of_lt {L R : BPair} (h : L < R) : L + R.swap < BPair.unit :=
  BPair.lt_congr (BPair.oneValue_refl _) (BPair.add_swap_null R)
    (ltB_add h (leB_refl R.swap))

/-- The balance order's strict read composes with an at-or-below
read on its right. -/
theorem ltB_trans_le {x y z : BPair} (h : x < y) (h' : y ≤ z) :
    x < z := by
  show x.fst + z.snd < z.fst + x.snd
  refine posLtCancelR (c := y.fst + y.snd) ?_
  have e1 : x.fst + z.snd + (y.fst + y.snd)
      = x.fst + y.snd + (y.fst + z.snd) := by
    rw [ground.add_add_comm' x.fst z.snd y.fst y.snd,
      ground.add_comm z.snd y.fst]
  have e2 : z.fst + x.snd + (y.fst + y.snd)
      = y.fst + x.snd + (z.fst + y.snd) := by
    rw [ground.add_add_comm z.fst x.snd y.fst y.snd,
      ground.add_add_comm y.fst x.snd z.fst y.snd,
      ground.add_comm z.fst y.fst]
  rw [e1, e2]
  exact posLtAddLe h h'

/-- Two data at or above the sum's unit join there. -/
theorem unitLeAdd {x y : BPair} (hx : BPair.unit ≤ x)
    (hy : BPair.unit ≤ y) : BPair.unit ≤ x + y :=
  leB_congr_left (BPair.unit_add BPair.unit) (leB_add hx hy)

/-- A datum strictly above the sum's unit joined to one at or above
it sits strictly above. -/
theorem unitLtAdd {x y : BPair} (hx : BPair.unit < x)
    (hy : BPair.unit ≤ y) : BPair.unit < x + y :=
  BPair.lt_congr (BPair.unit_add BPair.unit)
    (BPair.oneValue_refl _) (ltB_add hx hy)

/-- A datum strictly above a summand's balance partner joins it
strictly above the sum's unit. -/
theorem unitLt_of_swap_lt {U V : BPair} (h : V.swap < U) :
    BPair.unit < U + V := by
  refine ground.unitLtOfSide ?_
  show U.snd + V.snd < U.fst + V.fst
  have h' : V.snd + U.snd < U.fst + V.fst := h
  rw [ground.add_comm U.snd V.snd]
  exact h'

/-- The strict read back at the unit: a sum strictly above the
sum's unit prices its second member's swap strictly below its
first. -/
theorem swapLt_of_unitLt {U V : BPair} (h : BPair.unit < U + V) :
    V.swap < U :=
  Decidable.byCases (p := V.swap < U) (fun hlt => hlt) (fun hn =>
    absurd h (leB_not_lt
      (leB_congr_right (BPair.swap_add_null (BPair.oneValue_refl V))
        (leB_add (leB_of_not_lt hn) (leB_refl V)))))

/-- A summand strictly above the sum's unit moves a datum strictly
up. -/
theorem ltB_addPos {x y : BPair} (hy : BPair.unit < y) :
    x < x + y :=
  BPair.lt_congr (BPair.unit_add x)
    (BPair.oneValue_of_eq (BPair.add_comm y x))
    (ltB_add hy (leB_refl x))

/-- A shared summand cancels from the balance order. -/
theorem leB_cancelL {x a b : BPair} (h : x + a ≤ x + b) : a ≤ b := by
  show a.fst + b.snd ≤ b.fst + a.snd
  refine posLeCancelR (c := x.fst + x.snd) ?_
  have h' : x.fst + a.fst + (x.snd + b.snd)
      ≤ x.fst + b.fst + (x.snd + a.snd) := h
  rw [ground.add_add_comm x.fst a.fst x.snd b.snd,
    ground.add_add_comm x.fst b.fst x.snd a.snd,
    ground.add_comm (x.fst + x.snd) (a.fst + b.snd),
    ground.add_comm (x.fst + x.snd) (b.fst + a.snd)] at h'
  exact h'

/-- A withdrawn member's swap crosses the comparison: the member
rejoins on the upper side. -/
theorem leB_swapL {X Y W : BPair} (h : X + Y.swap ≤ W) : X ≤ W + Y :=
  leB_congr_left (BPair.add_swap_self X Y) (leB_add h (leB_refl Y))

/-- A partner on the upper side crosses the comparison: the member
joins the lower side. -/
theorem leB_swapR {A B C : BPair} (h : A ≤ B + C.swap) : A + C ≤ B :=
  leB_congr_right (BPair.add_swap_self B C) (leB_add h (leB_refl C))

/-- The memberwise swap reverses the balance order's strict read. -/
theorem ltB_swap {x y : BPair} (h : x < y) : y.swap < x.swap := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  show y.snd + x.fst + g = x.snd + y.fst
  rw [ground.add_comm y.snd x.fst, hg, ground.add_comm y.fst x.snd]

/-- A datum strictly above the sum's unit sits off it. -/
theorem offOfUnitLt {x : BPair} (h : BPair.unit < x) :
    ¬ x.oneValue BPair.unit := fun he =>
  leB_not_lt (leB_refl BPair.unit)
    (BPair.lt_congr (BPair.oneValue_refl BPair.unit) he h)

/-- A datum strictly below the sum's unit sits off it. -/
theorem offOfLtUnit {x : BPair} (h : x < BPair.unit) :
    ¬ x.oneValue BPair.unit := fun he =>
  leB_not_lt (leB_refl BPair.unit)
    (BPair.lt_congr he (BPair.oneValue_refl BPair.unit) h)

/-- The strict order below the sum's unit at the members' own
read. -/
theorem ltUnitOfSide {x : BPair} (h : x.fst < x.snd) :
    x < BPair.unit :=
  ltB_swap
    (unitLtOfSide (x := x.swap)
      (show x.swap.snd < x.swap.fst from h))

/-- The members' read at a datum below the sum's unit. -/
theorem sideOfLtUnit {x : BPair} (h : x < BPair.unit) :
    x.fst < x.snd :=
  sideOfUnitLt (x := x.swap)
    (show BPair.unit < x.swap from ltB_swap h)

/-- The memberwise swap reverses the balance order. -/
theorem leB_swap {a b : BPair} (h : a ≤ b) :
    b.swap ≤ a.swap := by
  show b.snd + a.fst ≤ a.snd + b.fst
  have h' : a.fst + b.snd ≤ b.fst + a.snd := h
  rw [ground.add_comm b.snd a.fst, ground.add_comm a.snd b.fst]
  exact h'

/-- A datum whose partner sits at or beyond the unit sits at or
below it. -/
theorem leUnitOfSwap {z : BPair} (h : BPair.unit ≤ z.swap) :
    z ≤ BPair.unit := by
  show z.fst + Pos.one ≤ Pos.one + z.snd
  have h' : Pos.one + z.fst ≤ z.snd + Pos.one := h
  rw [ground.add_comm z.fst Pos.one, ground.add_comm Pos.one z.snd]
  exact h'

/-- The at-or-below read passes a common rescaling. -/
theorem leB_scale {u v : BPair} (h : u ≤ v) (w : Pos) :
    u.scale w ≤ v.scale w := by
  have h' : u.oneValue v ∨ u < v := h
  match h' with
  | Or.inl e => exact Or.inl (BPair.scale_congr w e)
  | Or.inr hl => exact Or.inr (BPair.scale_lt w hl)

/-- The at-or-below read reflects a common rescaling. -/
theorem leB_of_scale {u v : BPair} {w : Pos}
    (h : u.scale w ≤ v.scale w) : u ≤ v := by
  have h' : (u.scale w).oneValue (v.scale w) ∨ u.scale w < v.scale w := h
  match h' with
  | Or.inl e => exact Or.inl (BPair.scale_cancel (w := w) e)
  | Or.inr hl => exact Or.inr (BPair.lt_of_scale_lt hl)

/-- The composite at-or-below read at a datum with itself. -/
theorem CPair.le_refl (x : CPair) : x ≤ x :=
  Or.inl (CPair.oneValue_refl x)

/-- The composite at-or-below read composes. -/
theorem CPair.le_trans {x y z : CPair} (h1 : x ≤ y) (h2 : y ≤ z) :
    x ≤ z := by
  obtain ⟨xn, xc⟩ := x
  obtain ⟨yn, yc⟩ := y
  obtain ⟨zn, zc⟩ := z
  have a1 : xn.scale yc ≤ yn.scale xc := h1
  have a2 : yn.scale zc ≤ zn.scale yc := h2
  have b1 := leB_scale a1 zc
  have b2 := leB_scale a2 xc
  rw [BPair.scale_scale, BPair.scale_scale] at b1
  rw [BPair.scale_scale, BPair.scale_scale] at b2
  rw [ground.mul_comm xc zc] at b1
  have b3 := ground.leB_trans b1 b2
  rw [ground.mul_comm yc zc, ground.mul_comm yc xc,
    ← BPair.scale_scale, ← BPair.scale_scale] at b3
  exact leB_of_scale b3

/-- The composite order is total at the at-or-below read. -/
theorem CPair.le_total (x y : CPair) : x ≤ y ∨ y ≤ x := by
  obtain ⟨xn, xc⟩ := x
  obtain ⟨yn, yc⟩ := y
  match ground.trich (xn.fst * yc + yn.snd * xc)
      (yn.fst * xc + xn.snd * yc) with
  | .lt g h => exact Or.inl (Or.inr ⟨g, h⟩)
  | .eq h => exact Or.inl (Or.inl h)
  | .gt g h => exact Or.inr (Or.inr ⟨g, h⟩)

/-- The composite at-or-below read both ways is one value. -/
theorem CPair.le_antisymm {x y : CPair} (h : x ≤ y) (h' : y ≤ x) :
    x.oneValue y :=
  match x, y, h, h' with
  | ⟨xn, xc⟩, ⟨yn, yc⟩, h, h' =>
    ground.leB_antisymm (x := xn.scale yc) (y := yn.scale xc) h h'

/-- One value refuses the strict composite order. -/
theorem CPair.not_lt_of_one {x y : CPair} (h : x.oneValue y)
    (hlt : x < y) : False :=
  match x, y, h, hlt with
  | ⟨xn, xc⟩, ⟨yn, yc⟩, h, hlt =>
    ground.posLtLe
      (show yn.fst * xc + xn.snd * yc
          ≤ xn.fst * yc + yn.snd * xc from Or.inl h.symm)
      hlt

/-- The composite sum keeps the order on both summands. -/
theorem CPair.le_add : ∀ {x y z w : CPair}, x ≤ y → z ≤ w → x + z ≤ y + w
  | ⟨a, ac⟩, ⟨b, bc⟩, ⟨c, cc⟩, ⟨d, dc⟩, h1, h2 => by
    have g1 : a.scale bc ≤ b.scale ac := h1
    have g2 : c.scale dc ≤ d.scale cc := h2
    have k1 := leB_scale g1 (cc * dc)
    have k2 := leB_scale g2 (ac * bc)
    rw [BPair.scale_scale, BPair.scale_scale] at k1
    rw [BPair.scale_scale, BPair.scale_scale] at k2
    rw [show bc * (cc * dc) = cc * (bc * dc) from
        mul_left_comm bc cc dc,
      show ac * (cc * dc) = dc * (ac * cc) from by
        rw [mul_left_comm dc ac cc, ground.mul_comm cc dc]] at k1
    rw [show dc * (ac * bc) = ac * (bc * dc) from by
        rw [mul_left_comm dc ac bc, ground.mul_comm dc bc],
      show cc * (ac * bc) = bc * (ac * cc) from by
        rw [mul_left_comm cc ac bc, mul_left_comm bc ac cc,
          ground.mul_comm cc bc]] at k2
    show (a.scale cc + c.scale ac).scale (bc * dc)
      ≤ (b.scale dc + d.scale bc).scale (ac * cc)
    rw [BPair.scale_add, BPair.scale_add, BPair.scale_scale,
      BPair.scale_scale, BPair.scale_scale, BPair.scale_scale]
    exact ground.leB_add k1 k2

/-- The composite sum's left exchange. -/
theorem CPair.add_left_comm (x y z : CPair) :
    x + (y + z) = y + (x + z) := by
  rw [← CPair.add_assoc, CPair.add_comm x y, CPair.add_assoc]

/-- The composite order's at-or-below read refuses the reversed
strict side. -/
theorem CPair.le_not_lt : ∀ {x y : CPair}, x ≤ y → ¬ (y < x)
  | ⟨a, ac⟩, ⟨b, bc⟩, h, hlt => by
    have h' : a.scale bc ≤ b.scale ac := h
    have hlt' : b.scale ac < a.scale bc := hlt
    exact ground.leB_not_lt h' hlt'

/-- The composite memberwise swap reverses the at-or-below read. -/
theorem CPair.le_swap : ∀ {x y : CPair}, x ≤ y →
    CPair.swap y ≤ CPair.swap x
  | ⟨xn, xc⟩, ⟨yn, yc⟩, h => by
    have h0 : xn.scale yc ≤ yn.scale xc := h
    show yn.swap.scale xc ≤ xn.swap.scale yc
    exact ground.leB_swap h0

/-- The composite memberwise swap reverses the strict order. -/
theorem CPair.lt_swap : ∀ {x y : CPair}, x < y → CPair.swap y < CPair.swap x
  | ⟨xn, xc⟩, ⟨yn, yc⟩, h =>
    ground.ltB_swap (x := xn.scale yc) (y := yn.scale xc) h

/-- The memberwise swap at a left factor is the product's swap. -/
theorem CPair.swap_mul : ∀ x y : CPair, CPair.swap x * y = CPair.swap (x * y)
  | ⟨xn, xc⟩, ⟨yn, yc⟩ => by
    show CPair.mk (xn.swap * yn) (xc * yc) = CPair.mk ((xn * yn).swap) (xc * yc)
    rw [BPair.swap_mul]

/-- The composite product's crossed regrouping. -/
theorem CPair.mul_mul_mul_comm (a b c d : CPair) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [CPair.mul_assoc a b (c * d), ← CPair.mul_assoc b c d,
    CPair.mul_comm b c, CPair.mul_assoc c b d, ← CPair.mul_assoc a c (b * d)]

/-- The composite product distributes across the sum on the right at
the one-value read. -/
theorem CPair.add_mul (x y z : CPair) :
    ((x + y) * z).oneValue (x * z + y * z) := by
  rw [CPair.mul_comm (x + y) z, CPair.mul_comm x z, CPair.mul_comm y z]
  exact CPair.mul_add z x y

/-- A shared right summand withdraws from the strict composite
order. -/
theorem CPair.lt_of_add_lt_add_right {x y z : CPair} (h : x + z < y + z) :
    x < y :=
  match CPair.le_total y x with
  | Or.inl hyx =>
    absurd h (CPair.le_not_lt (CPair.le_add hyx (CPair.le_refl z)))
  | Or.inr (Or.inl hov) =>
    (CPair.not_lt_of_one (CPair.add_congr hov (CPair.oneValue_refl z)) h).elim
  | Or.inr (Or.inr hlt) => hlt


/-- A product of two data at or above the sum's unit sits there. -/
theorem unitLeMul {x y : BPair} (hx : BPair.unit ≤ x)
    (hy : BPair.unit ≤ y) : BPair.unit ≤ x * y :=
  unitLeOfSide (crossLe (sideOfUnitLe hx) (sideOfUnitLe hy))


/-- A second-factor comparison keeps under a first factor at or
beyond the unit. -/
theorem leB_mulR {x y y' : BPair} (hx : BPair.unit ≤ x)
    (h : y ≤ y') : x * y ≤ x * y' := by
  refine ground.leB_of_unit_add (U := x * y') (V := (x * y).swap) ?_
  have hsw : (x * y).swap = x * y.swap := by
    rw [BPair.mul_comm x y, ← BPair.swap_mul y x,
      BPair.mul_comm y.swap x]
  rw [hsw, ← BPair.left_distrib]
  refine ground.unitLeMul hx ?_
  exact ground.leB_unit_add (U := y') (V := y.swap) h

/-- A first-factor comparison keeps under a second factor at or
beyond the unit. -/
theorem leB_mulL {x y c : BPair} (hc : BPair.unit ≤ c) (h : x ≤ y) :
    x * c ≤ y * c :=
  ground.leB_congr (BPair.oneValue_of_eq (BPair.mul_comm c x))
    (BPair.oneValue_of_eq (BPair.mul_comm c y)) (ground.leB_mulR hc h)

/-- The product's two-sided comparison at factors from the sum's
unit. -/
theorem leB_mul_mono {a b u v : BPair} (hu : BPair.unit ≤ u)
    (hb : BPair.unit ≤ b) (h1 : a ≤ b) (h2 : u ≤ v) : a * u ≤ b * v :=
  ground.leB_trans
    (ground.leB_congr
      (BPair.oneValue_of_eq (BPair.mul_comm u a))
      (BPair.oneValue_of_eq (BPair.mul_comm u b))
      (ground.leB_mulR hu h1))
    (ground.leB_mulR hb h2)

/-- A count sits at or above the sum's unit. -/
theorem unitLeOfNat (n : Nat) : BPair.unit ≤ BPair.ofNat n :=
  ground.leB_congr_right (BPair.mul_ofNat_one (BPair.ofNat n))
    (ground.leB_unit_mul n (by decide +kernel))

/-- The positive carrier's order carries onto the balance
pairs. -/
theorem leB_ofPos {a b : Pos} (h : a ≤ b) :
    BPair.ofPos a ≤ BPair.ofPos b :=
  match h with
  | Or.inl e => Or.inl (by rw [e])
  | Or.inr ⟨g, hg⟩ => Or.inr ⟨g, by
      show a + Pos.one + Pos.one + g = b + Pos.one + Pos.one
      rw [ground.add_right_comm (a + Pos.one) Pos.one g,
        ground.add_right_comm a Pos.one g, hg]⟩

/-- The counts' order carries onto the balance pairs. -/
theorem leB_ofNat {a b : Nat} (h : a ≤ b) :
    BPair.ofNat a ≤ BPair.ofNat b := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd]
  exact ground.leB_congr (BPair.add_unit (BPair.ofNat a))
    (BPair.oneValue_symm (BPair.ofNat_add a d))
    (ground.leB_add (ground.leB_refl (BPair.ofNat a))
      (ground.unitLeOfNat d))

/-- The counts' order reads back off the balance pairs: a stated
at-or-below read of two counts' pairs is the counts' own. -/
theorem leB_ofNat_cancel {a b : Nat}
    (h : BPair.ofNat a ≤ BPair.ofNat b) : a ≤ b := by
  match Nat.lt_or_ge b a with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    obtain ⟨k, hk⟩ := Nat.le.dest hlt
    have hd : a = b + (k + 1) :=
      hk.symm.trans ((Nat.succ_add b k).trans (Nat.add_succ b k).symm)
    have h' : BPair.ofNat (b + (k + 1)) ≤ BPair.ofNat b := by
      rw [← hd]; exact h
    have h1 : BPair.ofNat b + BPair.ofNat (k + 1) ≤ BPair.ofNat b :=
      ground.leB_congr_left (BPair.ofNat_add b (k + 1)) h'
    have h2 : BPair.ofNat b + BPair.ofNat (k + 1)
        ≤ BPair.ofNat b + BPair.unit :=
      ground.leB_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.add_unit (BPair.ofNat b))) h1
    have h3 : BPair.unit ≤ BPair.ofNat (k + 1) :=
      ground.leB_congr (BPair.oneValue_refl _)
        (BPair.mul_ofNat_one (BPair.ofNat (k + 1)))
        (ground.leB_unit_mul (k + 1)
          (z := BPair.ofNat 1) (by decide +kernel))
    exact absurd (ground.leB_antisymm (ground.leB_cancelL h2) h3)
      (BPair.ofNat_off_unit (k + 1) (Nat.succ_pos k))

/-- The doubled cross product priced at the squares' sum under a
factor at or beyond the sum's unit: the gap's square collects the
comparison, `con:coeff`'s device at a weighted entry. -/
theorem leB_crossSq {A : BPair} (hA : BPair.unit ≤ A) (p q : BPair) :
    A * (p * q + p * q) ≤ A * (p * p + q * q) := by
  have hnn : BPair.unit ≤ A * ((p + q.swap) * (p + q.swap)) :=
    unitLeMul hA (unitLeSq _)
  rw [BPair.sq_expand_swap p q, BPair.left_distrib,
    show A * ((p * q).swap + (p * q).swap)
        = (A * (p * q + p * q)).swap by
      rw [BPair.swap_add, BPair.mul_swap]] at hnn
  exact leB_of_unit_add hnn

/-- The pricing the other way: the doubled cross product's swap
sits at or below the weighted squares' sum. -/
theorem leB_crossSqSwap {A : BPair} (hA : BPair.unit ≤ A)
    (p q : BPair) :
    (A * (p * q + p * q)).swap ≤ A * (p * p + q * q) := by
  have hnn : BPair.unit ≤ A * ((p + q) * (p + q)) :=
    unitLeMul hA (unitLeSq _)
  rw [BPair.sq_expand p q, BPair.left_distrib] at hnn
  exact leB_of_unit_add hnn


/-- A datum whose square sits at or below a stated read joined to a
stated factor's multiple of the datum sits, squared, at or below twice
the read joined to the factor's square, the doubled cross product
priced at the squares' sum. -/
theorem leB_sq_selfcap {X A M : BPair} (h : X * X ≤ A + M * X) :
    X * X ≤ BPair.ofNat 2 * A + M * M := by
  have hc : M * X + M * X ≤ M * M + X * X :=
    leB_congr (BPair.ofNat_one_mul _) (BPair.ofNat_one_mul _)
      (leB_crossSq (unitLeOfNat 1) M X)
  have h2 : X * X + X * X ≤ A + A + (M * M + X * X) := by
    refine leB_trans (leB_add h h) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)) ?_
    exact leB_add (leB_refl _) hc
  refine leB_cancelL (x := X * X) ?_
  refine leB_congr (BPair.oneValue_refl _) ?_ h2
  rw [BPair.add_comm (M * M) (X * X), ← BPair.add_assoc,
    BPair.add_right_comm (A + A) (X * X) (M * M), BPair.add_comm (A + A + M * M) (X * X)]
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  exact BPair.add_congr (BPair.oneValue_symm (BPair.ofNat_two_mul A)) (BPair.oneValue_refl _)

/-- A count beyond zero sits strictly above the sum's unit. -/
theorem unitLtOfNat (n : Nat) :
    BPair.unit < BPair.ofNat (n + 1) :=
  BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (BPair.ofNat_succ n))
    (BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq
        (BPair.add_comm (BPair.ofNat 1) (BPair.ofNat n)))
      (ground.unitLtAdd (by decide +kernel) (unitLeOfNat n)))

/-- The counts' strict order carries onto the balance pairs. -/
theorem ltB_ofNat {a b : Nat} (h : a < b) :
    BPair.ofNat a < BPair.ofNat b := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  have hd' : a + (d + 1) = b :=
    (Nat.add_succ a d).trans ((Nat.succ_add a d).symm.trans hd)
  rw [← hd']
  exact BPair.lt_congr (BPair.unit_add (BPair.ofNat a))
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_symm (BPair.ofNat_add a (d + 1))))
    (ground.ltB_add (ground.unitLtOfNat d) (ground.leB_refl (BPair.ofNat a)))

/-- A positive datum's balance pair sits strictly above the sum's
unit, the side read at the one-member site. -/
theorem unitLtOfPos (w : Pos) : BPair.unit < BPair.ofPos w :=
  ground.unitLtOfSide (show (BPair.ofPos w).snd < (BPair.ofPos w).fst from by
    show Pos.one < w + Pos.one
    rw [ground.add_comm w Pos.one]
    exact ground.posLtSelfAdd Pos.one w)

/-- A datum at or beyond the sum's unit keeps that side at every
power. -/
theorem unitLeBpow {a : BPair} (h : BPair.unit ≤ a) :
    ∀ k : Nat, BPair.unit ≤ bpow a k
  | 0 => leB_of_lt (unitLtOfPos Pos.one)
  | k + 1 =>
    leB_congr_right
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (unitLeMul h (unitLeBpow h k))

/-- A product of two data strictly above the sum's unit sits
strictly above it. -/
theorem unitLtMul {x y : BPair} (hx : BPair.unit < x)
    (hy : BPair.unit < y) : BPair.unit < x * y :=
  unitLtOfSide (crossLt (sideOfUnitLt hx) (sideOfUnitLt hy))

/-- A power of a datum strictly above the sum's unit sits strictly
above it. -/
theorem unitLtBpow {a : BPair} (h : BPair.unit < a) :
    ∀ k : Nat, BPair.unit < bpow a k
  | 0 => unitLtOfPos Pos.one
  | k + 1 =>
    BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (unitLtMul h (unitLtBpow h k))

/-- The powers compare at comparing bases from the sum's unit. -/
theorem bpow_mono {a b : BPair} (ha : BPair.unit ≤ a) (h : a ≤ b) :
    ∀ k : Nat, bpow a k ≤ bpow b k
  | 0 => leB_refl _
  | k + 1 => by
    have hb : BPair.unit ≤ b := leB_trans ha h
    have hstep : a * bpow a k ≤ b * bpow b k :=
      leB_trans (leB_mulR ha (bpow_mono ha h k))
        (leB_congr
          (BPair.oneValue_of_eq (BPair.mul_comm (bpow b k) a))
          (BPair.oneValue_of_eq (BPair.mul_comm (bpow b k) b))
          (leB_mulR (unitLeBpow hb k) h))
    exact leB_congr
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (BPair.oneValue_symm (BPair.norm_oneValue _)) hstep


/-- A count's power enters the pair carrier at the one-member site as
the carrier's power. -/
theorem bpow_ofNat (a : Nat) : ∀ j : Nat,
    (BPair.ofNat (a ^ j)).oneValue (bpow (BPair.ofNat a) j)
  | 0 => BPair.oneValue_refl _
  | j + 1 => by
    show (BPair.ofNat (a ^ j * a)).oneValue (bpow (BPair.ofNat a) (j + 1))
    refine BPair.oneValue_trans (BPair.ofNat_mul _ _) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (bpow_ofNat a j) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    exact BPair.oneValue_symm (bpow_succ_read _ j)

/-- A power at a base at or beyond one sits at or beyond one. -/
theorem oneLeBpow {a : BPair} (h : BPair.ofPos .one ≤ a) :
    ∀ k : Nat, BPair.ofPos .one ≤ bpow a k
  | 0 => leB_refl _
  | k + 1 => by
    refine leB_congr_right (BPair.oneValue_symm (bpow_succ_read a k)) ?_
    refine leB_congr_left (BPair.ofPos_one_mul _) ?_
    exact leB_mul_mono (leB_of_lt (unitLtOfPos .one))
      (leB_trans (leB_of_lt (unitLtOfPos .one)) h) h (oneLeBpow h k)

/-- A base at or beyond one sits at or below its power at an occupied
key. -/
theorem le_bpow_self {a : BPair} (h : BPair.ofPos .one ≤ a) :
    ∀ k : Nat, 1 ≤ k → a ≤ bpow a k
  | k' + 1, _ => by
    refine leB_congr_right (BPair.oneValue_symm (bpow_succ_read a k')) ?_
    refine leB_congr_left (BPair.mul_one_read a) ?_
    exact leB_mulR (leB_trans (leB_of_lt (unitLtOfPos .one)) h) (oneLeBpow h k')

/-- A power at a key at or below a further key sits at or below the
further power, at a base at or beyond one. -/
theorem bpow_le_exp {z : BPair} (hz : BPair.ofPos .one ≤ z) {i m : Nat}
    (h : i ≤ m) : bpow z i ≤ bpow z m := by
  obtain ⟨t, ht⟩ := Nat.le.dest h
  rw [← ht]
  refine leB_congr_right (BPair.oneValue_symm (bpow_add z i t)) ?_
  refine leB_congr_left (BPair.mul_one_read _) ?_
  exact leB_mulR (unitLeBpow (leB_trans (leB_of_lt (unitLtOfPos .one)) hz) i)
    (oneLeBpow hz t)

/-- A count beyond nought sits strictly above the sum's unit. -/
theorem unitLtNat : ∀ {n : Nat}, 0 < n → BPair.unit < BPair.ofNat n
  | _ + 1, _ => unitLtOfNat _

/-- The carrier's integrality at the sum's unit: a datum strictly
above it sits at or above the natural one, the members' gap at or
above the ground unit. -/
theorem oneLeOfUnitLt {z : BPair} (h : BPair.unit < z) :
    BPair.ofNat 1 ≤ z := by
  obtain ⟨g, hg⟩ := sideOfUnitLt h
  show Pos.one + Pos.one + z.snd ≤ z.fst + Pos.one
  rw [← hg, add_right_comm z.snd g Pos.one,
    add_comm (Pos.one + Pos.one) z.snd, ← add_assoc z.snd Pos.one Pos.one]
  exact posLeAdd (Or.inl rfl) (posOneLe g)

/-- The cap read of a balance pair: the first member's count, a
count at or beyond every count the pair bounds. -/
def BPair.capN (b : BPair) : Nat := b.fst.pred + 1

/-- The carrier is archimedean over the counts: every datum sits at
or below its own cap's read. -/
theorem leB_ofNat_bound (z : BPair) : ∃ n : Nat, z ≤ BPair.ofNat n :=
  ⟨BPair.capN z, Or.inr ⟨z.snd, rfl⟩⟩

/-- The cap read's defining bound: a count entering the carrier at
or below a pair sits at or below the pair's cap. -/
theorem BPair.ofNat_le_capN : ∀ {n : Nat} {b : BPair},
    BPair.ofNat n ≤ b → n ≤ BPair.capN b
  | 0, _, _ => Nat.zero_le _
  | m + 1, b, h => by
    have h' : m + 1 + b.snd.pred + 1 ≤ b.fst.pred + 1 :=
      match h with
      | Or.inl e => Nat.le_of_eq (congrArg Pos.pred e)
      | Or.inr ⟨g, hg⟩ =>
        Nat.le_trans (Nat.le_add_right _ (g.pred + 1))
          (Nat.le_of_eq ((Nat.add_assoc (m + 1 + b.snd.pred + 1)
            g.pred 1).symm.trans (congrArg Pos.pred hg)))
    exact Nat.le_trans
      (Nat.le_trans (Nat.le_add_right (m + 1) b.snd.pred)
        (Nat.le_add_right (m + 1 + b.snd.pred) 1)) h'

/-- A one-value read transports the unit read. -/
theorem BPair.unit_iff {a b : BPair} (h : a.oneValue b) :
    a.oneValue BPair.unit ↔ b.oneValue BPair.unit :=
  ⟨fun ha => BPair.oneValue_trans (BPair.oneValue_symm h) ha,
   fun hb => BPair.oneValue_trans h hb⟩

/-- A product reads the unit exactly where a factor does. -/
theorem BPair.mul_unit_iff (s e : BPair) :
    (s * e).oneValue BPair.unit
      ↔ (s.oneValue BPair.unit ∨ e.oneValue BPair.unit) := by
  constructor
  · intro h
    by_cases hs : s.oneValue BPair.unit
    · exact Or.inl hs
    · exact Or.inr (mul_cancel_unit hs h)
  · intro h
    match h with
    | .inl hs =>
      exact BPair.oneValue_trans (BPair.mul_congr_left hs)
        (BPair.unit_mul e)
    | .inr he =>
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl s) he) (BPair.mul_unit s)

/-- A pair off the unit keeps its powers off the unit. -/
theorem bpow_off (x : BPair) (hx : ¬ x.oneValue BPair.unit) :
    ∀ n : Nat, ¬ (bpow x n).oneValue BPair.unit
  | 0, h => BPair.ofPos_off Pos.one h
  | n + 1, h => by
    have h' : (x * bpow x n).oneValue BPair.unit :=
      BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.norm_oneValue (x * bpow x n))) h
    match (BPair.mul_unit_iff x (bpow x n)).mp h' with
    | .inl hx' => exact hx hx'
    | .inr hb => exact bpow_off x hx n hb

/-- A power of a factor off the unit against a further factor reads
the unit exactly where the further factor does, the product's
injectivity at the power. -/
theorem BPair.powMul_unit_iff (x y : BPair) (n : Nat)
    (hx : ¬ x.oneValue BPair.unit) :
    (bpow x n * y).oneValue BPair.unit ↔ y.oneValue BPair.unit :=
  Iff.intro (fun h => mul_cancel_unit (bpow_off x hx n) h)
    (fun h => (BPair.mul_unit_iff _ _).mpr (Or.inr h))

/-- The balance power carries a one-value read at its base. -/
theorem bpow_congr {x y : BPair} (h : x.oneValue y) :
    ∀ n : Nat, (bpow x n).oneValue (bpow y n)
  | 0 => BPair.oneValue_refl _
  | n + 1 =>
    BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr h (bpow_congr h n))
        (BPair.oneValue_symm (BPair.norm_oneValue _)))

/-- A factor off equal members cancels from a one-value read. -/
theorem mulCancel {c x y : BPair} (hc : ¬ c.oneValue BPair.unit)
    (h : (c * x).oneValue (c * y)) : x.oneValue y := by
  refine oneOfUnit (mul_cancel_unit hc ?_)
  rw [BPair.left_distrib, BPair.mul_swap]
  exact unitOfOne h

/-- Two consecutive balance gaps join to the endpoints' gap. -/
theorem BPair.gap_join (a b c : BPair) :
    (a + b.swap + (b + c.swap)).oneValue (a + c.swap) := by
  rw [← BPair.add_assoc]
  exact BPair.add_congr (BPair.add_swap_self a b) (BPair.oneValue_refl _)

/-- Withdrawing twice a balance value reads its partner. -/
theorem BPair.add_mul_swap_two (x : BPair) :
    (x + x * (BPair.ofNat 2).swap).oneValue x.swap := by
  rw [BPair.mul_swap, BPair.mul_comm x (BPair.ofNat 2)]
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl x) (swap_congr (BPair.ofNat_two_mul x))) ?_
  rw [← BPair.swap_add]
  exact BPair.add_swap_cancel x x.swap

/-- Exchanging two paired coordinates changes the pairing by the
product of their two gaps. -/
theorem BPair.exchange_gap (a b r s : BPair) :
    (a * r + b * s + (b + a.swap) * (r + s.swap)).oneValue (b * r + a * s) := by
  have h : (b + a.swap) * (r + s.swap) = (b * r + a * s) + (a * r + b * s).swap := by
    rw [BPair.right_distrib, BPair.left_distrib, BPair.left_distrib,
      BPair.mul_swap, BPair.swap_mul, BPair.swap_mul_swap,
      BPair.add_comm (a * r).swap (a * s), BPair.add_add_comm,
      BPair.add_comm (b * s).swap (a * r).swap, BPair.swap_add]
  rw [h]
  exact BPair.add_swap_cancel _ _

/-- Exchanging and flipping a coordinate pair changes its pairing
by the partnered coordinate sum against the weight sum. -/
theorem BPair.pair_flip_gap (a b r s : BPair) :
    (a * r + b * s + (a + b).swap * (r + s)).oneValue (b.swap * r + a.swap * s) := by
  have h : (a + b) * (r + s) = (a * r + b * s) + (b * r + a * s) := by
    rw [BPair.right_distrib, BPair.left_distrib, BPair.left_distrib,
      BPair.add_comm (b * r) (b * s), BPair.add_add_comm, BPair.add_comm (a * s) (b * r)]
  rw [BPair.swap_mul (a + b) (r + s), h, ← BPair.swap_add (a * r + b * s) (b * r + a * s),
    BPair.swap_mul b r, BPair.swap_mul a s, BPair.swap_add (b * r) (a * s)]
  rw [BPair.add_comm (a * r + b * s).swap (b * r + a * s).swap]
  exact BPair.add_swap_cancel _ _

/-- Ordered coordinates paired against oppositely ordered weights
strictly increase their pairing when exchanged. -/
theorem BPair.exchange_lt (a b r s : BPair) (hab : a < b) (hsr : s < r) :
    a * r + b * s < b * r + a * s := by
  have hg : BPair.unit < (b + a.swap) * (r + s.swap) := ground.unitLtMul
    (ground.unitLt_of_swap_lt hab) (ground.unitLt_of_swap_lt hsr)
  exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.exchange_gap a b r s) (ground.ltB_addPos hg)

/-- A lower-side coordinate sum against an upper-side weight sum
strictly increases the pairing at the exchanged partners. -/
theorem BPair.pair_flip_lt (a b r s : BPair) (hab : a + b < BPair.unit)
    (hrs : BPair.unit < r + s) : a * r + b * s < b.swap * r + a.swap * s := by
  have hg : BPair.unit < (a + b).swap * (r + s) := ground.unitLtMul (ground.ltB_swap hab) hrs
  exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.pair_flip_gap a b r s) (ground.ltB_addPos hg)

/-- Two pairs on their upper sides at one margin read one value. -/
theorem BPair.oneValue_of_marginN {x y : BPair} (hx : BPair.unit ≤ x) (hy : BPair.unit ≤ y)
    (h : x.marginN = y.marginN) : x.oneValue y := by
  refine BPair.oneValue_trans (BPair.ofNat_marginN hx) ?_
  rw [h]
  exact BPair.oneValue_symm (BPair.ofNat_marginN hy)

/-- The weak order of upper-side pairs is the natural margins'
order, including equal members. -/
theorem BPair.marginN_le {x y : BPair} (hx : BPair.unit ≤ x) (h : x ≤ y) :
    x.marginN ≤ y.marginN :=
  ground.leB_ofNat_cancel (ground.leB_congr (BPair.ofNat_marginN hx)
    (BPair.ofNat_marginN (ground.leB_trans hx h)) h)

/-- The strict order of upper-side pairs is the margins' strict
order. -/
theorem BPair.marginN_lt {x y : BPair} (hx : BPair.unit ≤ x)
    (h : x < y) : x.marginN < y.marginN := by
  cases Nat.lt_or_ge x.marginN y.marginN with
  | inl hlt => exact hlt
  | inr hle =>
    have hn := BPair.lt_congr (BPair.ofNat_marginN hx)
      (BPair.ofNat_marginN (ground.leB_trans hx (ground.leB_of_lt h))) h
    exact False.elim (ground.leB_not_lt (ground.leB_ofNat hle) hn)

/-- A pair beyond both a datum and its partner has
margin beyond that datum's. -/
theorem BPair.marginN_lt_of_sides {x y : BPair}
    (hxy : x < y) (hxs : x.swap < y) : x.marginN < y.marginN := by
  by_cases hx : x < BPair.unit
  · have h := BPair.marginN_lt (ground.leB_of_lt (ground.ltB_swap hx)) hxs
    rw [BPair.marginN_swap] at h
    exact h
  · exact BPair.marginN_lt (ground.leB_of_not_lt hx) hxy

/-- A strictly decreasing balance-pair display has one key per
value, at every pair of keys in the stated range. -/
theorem bDesc_inj (D : List BPair) (l : Nat)
    (hdesc : ∀ i j, i < j → j < l → getAt BPair.unit D j < getAt BPair.unit D i)
    (i j : Nat) (hi : i < l) (hj : j < l)
    (he : (getAt BPair.unit D i).oneValue (getAt BPair.unit D j)) : i = j := by
  cases Nat.lt_or_ge i j with
  | inl hij =>
    exact False.elim ((leB_not_lt (show getAt BPair.unit D i ≤ getAt BPair.unit D j
      from Or.inl he)) (hdesc i j hij hj))
  | inr hji =>
    cases Nat.lt_or_ge j i with
    | inl hji' =>
      exact False.elim ((leB_not_lt (show getAt BPair.unit D j ≤ getAt BPair.unit D i
        from Or.inl (BPair.oneValue_symm he))) (hdesc j i hji' hi))
    | inr hij => exact Nat.le_antisymm hij hji

/-- A display whose earlier entries exceed both sides of every
later entry has one key per value even after a memberwise swap. -/
theorem bDesc_swap_inj (D : List BPair) (l : Nat)
    (hdesc : ∀ i j, i < j → j < l →
      getAt BPair.unit D j < getAt BPair.unit D i
        ∧ (getAt BPair.unit D j).swap < getAt BPair.unit D i)
    (i j : Nat) (hi : i < l) (hj : j < l)
    (he : (getAt BPair.unit D i).oneValue (getAt BPair.unit D j)
      ∨ (getAt BPair.unit D i).oneValue (getAt BPair.unit D j).swap) : i = j := by
  cases he with
  | inl h => exact bDesc_inj D l (fun a b hab hb => (hdesc a b hab hb).1) i j hi hj h
  | inr h =>
    cases Nat.lt_or_ge i j with
    | inl hij =>
      exact False.elim ((leB_not_lt (show getAt BPair.unit D i ≤ (getAt BPair.unit D j).swap
        from Or.inl h)) (hdesc i j hij hj).2)
    | inr hji =>
      cases Nat.lt_or_ge j i with
      | inl hji' =>
        exact False.elim ((leB_not_lt (show getAt BPair.unit D j ≤ (getAt BPair.unit D i).swap
          from Or.inl (BPair.oneValue_symm (swap_congr h)))) (hdesc j i hji' hi).2)
      | inr hij => exact Nat.le_antisymm hij hji

/-! The balance carrier's index fold: the fold over an index family
with its scalar passes, pointwise splits, nested exchange,
memberwise swap and delta pick, with the generic reads at one value
per occupied member beneath them. -/

/-- The balance carrier's fold over an index family. -/
def bsum {α : Type} (f : α → BPair) (l : List α) : BPair :=
  ground.famFold BPair.add BPair.unit f l

/-- The fold through a reindexing map. -/
theorem bsum_map {α β : Type} (f : α → BPair) (g : β → α)
    (l : List β) : bsum f (l.map g) = bsum (fun x => f (g x)) l :=
  ground.famFold_map BPair.add BPair.unit f g l

/-- The pointwise-unit fold at the sum's unit. -/
theorem foldB_null {α : Type} [DecidableEq α]
    (f : α → BPair) : ∀ l : List α,
      (∀ x, 0 < ground.countOf x l → (f x).oneValue BPair.unit) →
      (ground.famFold BPair.add BPair.unit f l).oneValue BPair.unit :=
  fun l h =>
  famFold_null_ov bpairFoldLaws f l h

/-- The accumulating sum fold reads its seed against the index
fold. -/
theorem foldB_foldl {α : Type} (g : α → BPair) :
    ∀ (l : List α) (acc : BPair),
      (l.foldl (fun a j => a + g j) acc).oneValue
        (acc + famFold BPair.add BPair.unit g l)
  | [], acc => BPair.oneValue_symm (BPair.add_unit acc)
  | a :: t, acc => by
    show (t.foldl (fun a j => a + g j) (acc + g a)).oneValue
      (acc + (g a + famFold BPair.add BPair.unit g t))
    refine BPair.oneValue_trans (foldB_foldl g t (acc + g a)) ?_
    rw [BPair.add_assoc]
    exact BPair.oneValue_refl _

/-- The guarded accumulating fold reads its seed against the
guarded index fold, a refused member keeping the accumulator. -/
theorem foldB_foldl_guard {α : Type} (P : α → Bool) (g : α → BPair) :
    ∀ (l : List α) (acc : BPair),
      (l.foldl (fun a x => if P x then a + g x else a) acc).oneValue
        (acc + famFold BPair.add BPair.unit
          (fun x => if P x then g x else BPair.unit) l)
  | [], acc => BPair.oneValue_symm (BPair.add_unit acc)
  | a :: t, acc => by
    show (t.foldl (fun a x => if P x then a + g x else a)
        (if P a then acc + g a else acc)).oneValue
      (acc + ((if P a then g a else BPair.unit)
        + famFold BPair.add BPair.unit
            (fun x => if P x then g x else BPair.unit) t))
    refine BPair.oneValue_trans (foldB_foldl_guard P g t _) ?_
    cases hc : P a with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _)
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
        if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
      exact BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.unit_add _))

/-- Two folds at one read per occupied member are one value. -/
theorem foldB_congr_members {α : Type} [DecidableEq α]
    (f g : α → BPair) : ∀ l : List α,
      (∀ x, 0 < ground.countOf x l → (f x).oneValue (g x)) →
      (ground.famFold BPair.add BPair.unit f l).oneValue
        (ground.famFold BPair.add BPair.unit g l) :=
  famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
    BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) f g

/-- The fold splits over a pointwise sum. -/
theorem foldB_add {α : Type} (f g : α → BPair) : ∀ l : List α,
    (ground.famFold BPair.add BPair.unit
      (fun x => f x + g x) l).oneValue
      (ground.famFold BPair.add BPair.unit f l
        + ground.famFold BPair.add BPair.unit g l) :=
  famFold_add_ov bpairFoldLaws f g

/-- The balance pair of two counts: the first count against the
second, one member per grading side. -/
def BPair.ofCounts (e o : Nat) : BPair :=
  BPair.add (BPair.ofNat e) ((BPair.ofNat o).swap)

/-- Two counts at the sum's unit read the unit pair. -/
theorem BPair.ofCounts_zero :
    (BPair.ofCounts 0 0).oneValue BPair.unit := rfl

/-- The count pair sits at the sum's unit exactly at two equal
counts. -/
theorem BPair.ofCounts_unit {a b : Nat} :
    (BPair.ofCounts a b).oneValue BPair.unit ↔ a = b := by
  constructor
  · intro h
    have h' : (BPair.ofNat a).fst + (BPair.ofNat b).snd + Pos.one
        = Pos.one + ((BPair.ofNat a).snd + (BPair.ofNat b).fst) := h
    rw [BPair.ofNat_fst a, BPair.ofNat_snd a, BPair.ofNat_fst b,
      BPair.ofNat_snd b] at h'
    have h2 : posOfSucc a + (Pos.one + Pos.one)
        = posOfSucc b + (Pos.one + Pos.one) := by
      rw [← ground.add_assoc (posOfSucc a) Pos.one Pos.one, h',
        ground.add_comm (posOfSucc b) (Pos.one + Pos.one),
        ground.add_assoc Pos.one Pos.one (posOfSucc b)]
    exact congrArg Pos.pred (ground.add_right_cancel h2)
  · intro h
    rw [h]
    show (BPair.ofNat b).fst + (BPair.ofNat b).snd + Pos.one
      = Pos.one + ((BPair.ofNat b).snd + (BPair.ofNat b).fst)
    rw [BPair.ofNat_fst b, BPair.ofNat_snd b,
      ground.add_assoc (posOfSucc b) Pos.one Pos.one,
      ground.add_comm (posOfSucc b) (Pos.one + Pos.one),
      ground.add_assoc Pos.one Pos.one (posOfSucc b)]

/-- The count pair's additivity: the joined counts' pair reads the
pairs' sum. -/
theorem BPair.ofCounts_add (a b c d : Nat) :
    (BPair.ofCounts (a + c) (b + d)).oneValue
      (BPair.ofCounts a b + BPair.ofCounts c d) := by
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.ofNat_add a c)
      (ground.swap_congr (BPair.ofNat_add b d))) ?_
  rw [← BPair.swap_add]
  rw [BPair.add_add_comm]
  exact BPair.oneValue_refl _

/-- Two count pairs at the crossed balance read one value:
`a + d = c + b` crosses the grading sides. -/
theorem BPair.ofCounts_crossed {a b c d : Nat} (h : a + d = c + b) :
    (BPair.ofCounts a b).oneValue (BPair.ofCounts c d) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.add_unit (BPair.ofCounts a b))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm
        ((BPair.ofCounts_unit (a := d) (b := d)).mpr rfl))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofCounts_add a b d d)) ?_
  rw [h, Nat.add_comm b d]
  exact BPair.oneValue_trans (BPair.ofCounts_add c d b b)
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        ((BPair.ofCounts_unit (a := b) (b := b)).mpr rfl))
      (BPair.add_unit _))

/-- Two count pairs at one value cross-add, the crossed balance
read's converse. -/
theorem BPair.ofCounts_cross {a b c d : Nat}
    (h : (BPair.ofCounts a b).oneValue (BPair.ofCounts c d)) :
    a + d = c + b := by
  have h2 : (BPair.ofCounts (a + d) (b + c)).oneValue BPair.unit :=
    BPair.oneValue_trans (BPair.ofCounts_add a b d c)
      (BPair.oneValue_trans (BPair.add_congr h (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.ofCounts_add c d d c))
          (BPair.ofCounts_unit.mpr (Nat.add_comm c d))))
  exact (BPair.ofCounts_unit.mp h2).trans (Nat.add_comm b c)

/-- Two count folds' pair reads the memberwise pairs' fold. -/
theorem foldB_ofCounts {α : Type} (f g : α → Nat) : ∀ l : List α,
    (BPair.ofCounts (ground.famFold Nat.add 0 f l)
      (ground.famFold Nat.add 0 g l)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun x => BPair.ofCounts (f x) (g x)) l)
  | [] => rfl
  | a :: t => by
    show (BPair.ofCounts (f a + ground.famFold Nat.add 0 f t)
        (g a + ground.famFold Nat.add 0 g t)).oneValue
      (BPair.ofCounts (f a) (g a)
        + ground.famFold BPair.add BPair.unit
            (fun x => BPair.ofCounts (f x) (g x)) t)
    exact BPair.oneValue_trans
      (BPair.ofCounts_add (f a) (g a)
        (ground.famFold Nat.add 0 f t) (ground.famFold Nat.add 0 g t))
      (BPair.add_congr (BPair.oneValue_refl _) (foldB_ofCounts f g t))

/-- The grading's signed entry: a datum at its side, the odd side
the memberwise swap. -/
def signedAt (s : Bool) (x : BPair) : BPair := if s then x.swap else x

/-- A signed entry at a unit-valued datum reads the unit. -/
theorem signedAt_unit {x : BPair} (s : Bool)
    (h : x.oneValue BPair.unit) :
    (signedAt s x).oneValue BPair.unit := by
  match s with
  | false => exact h
  | true => exact ground.swap_congr h

/-- The first erasure at an occupied count drops the length by
one. -/
theorem length_eraseFirst {α : Type} [DecidableEq α] (a : α) :
    ∀ l : List α, 0 < countOf a l →
      (eraseFirst a l).length + 1 = l.length
  | b :: t, h => by
    show (if a = b then t else b :: eraseFirst a t).length + 1
      = t.length + 1
    exact if hab : a = b then by rw [if_pos hab]
    else by
      rw [if_neg hab]
      have h' : 0 < countOf a t := by
        have hc := countOf_cons a b t
        rw [hc, if_neg hab, Nat.zero_add] at h
        exact h
      show (eraseFirst a t).length + 1 + 1 = t.length + 1
      rw [length_eraseFirst a t h']

/-- Off the flipped grading: a key at one side is off every pair
at the other. -/
theorem ne_flipSide {α : Type} {k k' : α} (s : Bool) :
    (k, s) ≠ (k', !s) := fun he => by
  have h2 : s = !s := congrArg Prod.snd he
  cases s
  · exact Bool.noConfusion h2
  · exact Bool.noConfusion h2

/-- A signed fold reads the unit where every occupied key sits at
its two graded counts one value or at a unit-valued datum: a
matched key pairs a side against its partner and the rest die
memberwise. -/
theorem signedFold_null {α : Type} [DecidableEq α] (X : α → BPair) :
    ∀ (n : Nat) (W : List (α × Bool)), W.length ≤ n →
    (∀ k : α, 0 < countOf (k, true) W + countOf (k, false) W →
      countOf (k, true) W = countOf (k, false) W
        ∨ (X k).oneValue BPair.unit) →
    (famFold BPair.add BPair.unit
      (fun vp => signedAt vp.2 (X vp.1)) W).oneValue BPair.unit
  | _, [], _, _ => BPair.oneValue_refl _
  | n + 1, vp :: rest, hlen, hyp => by
    have hcons : ∀ (k : α) (s : Bool),
        countOf (k, s) (vp :: rest)
          = (if (k, s) = vp then 1 else 0) + countOf (k, s) rest :=
      fun k s => countOf_cons (k, s) vp rest
    have hconsSelf : countOf (vp.1, vp.2) (vp :: rest)
        = 1 + countOf (vp.1, vp.2) rest := by
      rw [hcons vp.1 vp.2, if_pos rfl]
    have hconsFlip : countOf (vp.1, !vp.2) (vp :: rest)
        = countOf (vp.1, !vp.2) rest := by
      rw [hcons vp.1 (!vp.2), if_neg (ne_flipSide vp.2).symm,
        Nat.zero_add]
    exact if hX : (X vp.1).oneValue BPair.unit then by
      show (signedAt vp.2 (X vp.1) + famFold BPair.add BPair.unit
        (fun vq => signedAt vq.2 (X vq.1)) rest).oneValue BPair.unit
      have hrest : ∀ k : α,
          0 < countOf (k, true) rest + countOf (k, false) rest →
          countOf (k, true) rest = countOf (k, false) rest
            ∨ (X k).oneValue BPair.unit := by
        intro k hk
        exact if hkv : k = vp.1 then Or.inr (by rw [hkv]; exact hX)
        else by
          have hT : countOf (k, true) (vp :: rest)
              = countOf (k, true) rest := by
            rw [hcons k true, if_neg (fun he =>
              hkv (congrArg Prod.fst he)), Nat.zero_add]
          have hF : countOf (k, false) (vp :: rest)
              = countOf (k, false) rest := by
            rw [hcons k false, if_neg (fun he =>
              hkv (congrArg Prod.fst he)), Nat.zero_add]
          rcases hyp k (by rw [hT, hF]; exact hk) with hb | hx
          · exact Or.inl (by rw [← hT, ← hF]; exact hb)
          · exact Or.inr hx
      exact BPair.oneValue_trans
        (BPair.add_congr (signedAt_unit vp.2 hX)
          (signedFold_null X n rest (Nat.le_of_succ_le_succ hlen) hrest))
        (BPair.unit_add BPair.unit)
    else by
      have hposSelf : 0 < countOf (vp.1, vp.2) (vp :: rest) := by
        rw [hconsSelf]
        exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
      have hocc : 0 < countOf (vp.1, true) (vp :: rest)
          + countOf (vp.1, false) (vp :: rest) := by
        cases hb : vp.2
        · rw [hb] at hposSelf
          exact Nat.lt_of_lt_of_le hposSelf (Nat.le_add_left _ _)
        · rw [hb] at hposSelf
          exact Nat.lt_of_lt_of_le hposSelf (Nat.le_add_right _ _)
      rcases hyp vp.1 hocc with hbal | hx
      · have hposBoth : ∀ s : Bool,
            0 < countOf (vp.1, s) (vp :: rest) := by
          intro s
          cases s
          · cases hb : vp.2
            · rw [hb] at hposSelf; exact hposSelf
            · rw [hb] at hposSelf; rw [← hbal]; exact hposSelf
          · cases hb : vp.2
            · rw [hb] at hposSelf; rw [hbal]; exact hposSelf
            · rw [hb] at hposSelf; exact hposSelf
        have hpart : 0 < countOf (vp.1, !vp.2) rest := by
          rw [← hconsFlip]; exact hposBoth (!vp.2)
        have herase : famFold BPair.add BPair.unit
            (fun vq => signedAt vq.2 (X vq.1)) rest
              = signedAt (!vp.2) (X vp.1)
                + famFold BPair.add BPair.unit
                    (fun vq => signedAt vq.2 (X vq.1))
                    (eraseFirst (vp.1, !vp.2) rest) :=
          famFold_eraseFirst BPair.add BPair.unit
            BPair.add_comm BPair.add_assoc
            (fun vq => signedAt vq.2 (X vq.1)) rest (vp.1, !vp.2) hpart
        show (signedAt vp.2 (X vp.1) + famFold BPair.add BPair.unit
          (fun vq => signedAt vq.2 (X vq.1)) rest).oneValue BPair.unit
        rw [herase, ← BPair.add_assoc]
        have hpair : (signedAt vp.2 (X vp.1)
            + signedAt (!vp.2) (X vp.1)).oneValue BPair.unit := by
          cases hb : vp.2
          · show (X vp.1 + (X vp.1).swap).oneValue BPair.unit
            rw [BPair.add_comm]
            exact BPair.swap_add_null (BPair.oneValue_refl _)
          · show ((X vp.1).swap + X vp.1).oneValue BPair.unit
            exact BPair.swap_add_null (BPair.oneValue_refl _)
        have hlenE := length_eraseFirst (vp.1, !vp.2) rest hpart
        have hlen' : (eraseFirst (vp.1, !vp.2) rest).length ≤ n := by
          have hr : rest.length ≤ n := Nat.le_of_succ_le_succ hlen
          rw [← hlenE] at hr
          exact Nat.le_of_succ_le hr
        refine BPair.oneValue_trans
          (BPair.add_congr hpair (signedFold_null X n _ hlen' ?_))
          (BPair.unit_add BPair.unit)
        intro k hk
        exact if hkv : k = vp.1 then by
          refine Or.inl ?_
          rw [hkv]
          cases hb : vp.2
          · -- the head at the odd side: the erased partner even
            have hpart' : 0 < countOf (vp.1, true) rest := by
              rw [hb] at hpart; exact hpart
            have hWs' : countOf (vp.1, false)
                (eraseFirst (vp.1, true) rest)
                  = countOf (vp.1, false) rest :=
              countOf_eraseFirst_ne rest (vp.1, true) (vp.1, false)
                (fun he => Bool.noConfusion (congrArg Prod.snd he))
            have hWf' : countOf (vp.1, true) rest
                = countOf (vp.1, true)
                    (eraseFirst (vp.1, true) rest) + 1 :=
              countOf_eraseFirst_self rest (vp.1, true) hpart'
            have hflip' : countOf (vp.1, true) (vp :: rest)
                = countOf (vp.1, true) rest := by
              rw [hcons vp.1 true, if_neg (fun he =>
                Bool.noConfusion (hb ▸ congrArg Prod.snd he)),
                Nat.zero_add]
            have hself' : countOf (vp.1, false) (vp :: rest)
                = 1 + countOf (vp.1, false) rest := by
              rw [hb] at hconsSelf; exact hconsSelf
            have h2 : countOf (vp.1, true)
                (eraseFirst (vp.1, true) rest) + 1
                  = 1 + countOf (vp.1, false)
                      (eraseFirst (vp.1, true) rest) := by
              rw [← hWf', ← hflip', hbal, hself', hWs']
            rw [Nat.add_comm 1 (countOf (vp.1, false)
              (eraseFirst (vp.1, true) rest))] at h2
            exact Nat.succ.inj h2
          · -- the head at the even side: the erased partner odd
            have hpart' : 0 < countOf (vp.1, false) rest := by
              rw [hb] at hpart; exact hpart
            have hWs' : countOf (vp.1, true)
                (eraseFirst (vp.1, false) rest)
                  = countOf (vp.1, true) rest :=
              countOf_eraseFirst_ne rest (vp.1, false) (vp.1, true)
                (fun he => Bool.noConfusion (congrArg Prod.snd he))
            have hWf' : countOf (vp.1, false) rest
                = countOf (vp.1, false)
                    (eraseFirst (vp.1, false) rest) + 1 :=
              countOf_eraseFirst_self rest (vp.1, false) hpart'
            have hflip' : countOf (vp.1, false) (vp :: rest)
                = countOf (vp.1, false) rest := by
              rw [hcons vp.1 false, if_neg (fun he =>
                Bool.noConfusion (hb ▸ congrArg Prod.snd he)),
                Nat.zero_add]
            have hself' : countOf (vp.1, true) (vp :: rest)
                = 1 + countOf (vp.1, true) rest := by
              rw [hb] at hconsSelf; exact hconsSelf
            have h2 : countOf (vp.1, false)
                (eraseFirst (vp.1, false) rest) + 1
                  = 1 + countOf (vp.1, true)
                      (eraseFirst (vp.1, false) rest) := by
              rw [← hWf', ← hflip', ← hbal, hself', hWs']
            rw [Nat.add_comm 1 (countOf (vp.1, true)
              (eraseFirst (vp.1, false) rest))] at h2
            exact (Nat.succ.inj h2).symm
        else by
          have hoff : ∀ s : Bool,
              countOf (k, s) (eraseFirst (vp.1, !vp.2) rest)
                = countOf (k, s) (vp :: rest) := by
            intro s
            rw [countOf_eraseFirst_ne rest (vp.1, !vp.2) (k, s)
                (fun he => hkv (congrArg Prod.fst he)),
              hcons k s, if_neg (fun he =>
                hkv (congrArg Prod.fst he)), Nat.zero_add]
          rcases hyp k (by rw [← hoff true, ← hoff false]; exact hk)
            with hb | hx
          · exact Or.inl (by rw [hoff true, hoff false]; exact hb)
          · exact Or.inr hx
      · exact absurd hx hX

/-- A guarded constant's fold collects at the guard's own count. -/
theorem foldB_guard {α : Type} (P : α → Prop)
    [DecidablePred P] (X : BPair) : ∀ l : List α,
    (famFold BPair.add BPair.unit
      (fun x => if P x then X else BPair.unit) l).oneValue
      (BPair.ofNat (famFold Nat.add 0
        (fun x => if P x then 1 else 0) l) * X)
  | [] => BPair.oneValue_symm (BPair.unit_mul X)
  | a :: t => by
    show ((if P a then X else BPair.unit)
        + famFold BPair.add BPair.unit
            (fun x => if P x then X else BPair.unit) t).oneValue
      (BPair.ofNat ((if P a then 1 else 0)
        + famFold Nat.add 0
            (fun x => if P x then 1 else 0) t) * X)
    by_cases ha : P a
    · rw [if_pos ha, if_pos ha]
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl X) (foldB_guard P X t)) ?_
      refine BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofNat_add 1 _)) ?_)
      rw [BPair.right_distrib]
      refine BPair.add_congr ?_ (BPair.oneValue_refl _)
      exact BPair.ofNat_one_mul X
    · rw [if_neg ha, if_neg ha, Nat.zero_add]
      exact BPair.oneValue_trans (BPair.unit_add _) (foldB_guard P X t)

/-- The delta family's fold at a key: the key's own datum enters at
the key's count in the family — the guarded fold at the equality
test. -/
theorem foldB_indicator {α : Type} [DecidableEq α] (c : α)
    (X : BPair) : ∀ l : List α,
    (ground.famFold BPair.add BPair.unit
      (fun x => if x = c then X else BPair.unit) l).oneValue
      (BPair.ofNat (countOf c l) * X) := fun l => by
  refine BPair.oneValue_trans (foldB_guard (fun x => x = c) X l) ?_
  rw [show famFold Nat.add 0 (fun x => if x = c then 1 else 0) l
      = countOf c l from by
    rw [countOf_fold c l]
    exact famFold_congr_members Nat.add 0 _ _ l (fun x _ => by
      by_cases h : x = c
      · rw [if_pos h, if_pos (h ▸ rfl)]
      · rw [if_neg h, if_neg (fun hc : c = x => h hc.symm)])]
  exact BPair.oneValue_refl _

/-- The fold at a family reading the unit off one key occupied
once: the key's own read is the fold's (`famFold_pick_ov` at the
balance carrier). -/
theorem foldB_pick {α : Type} [DecidableEq α] (F : α → BPair)
    (i : α) (X : BPair) (l : List α) (h : countOf i l = 1)
    (hon : (F i).oneValue X)
    (hoff : ∀ x, 0 < countOf x l → ¬ x = i →
      (F x).oneValue BPair.unit) :
    (ground.famFold BPair.add BPair.unit F l).oneValue X :=
  famFold_pick_ov bpairFoldLaws F i X l h hon hoff

/-- A scalar passes into the fold. -/
theorem foldB_mul_left {α : Type} (c : BPair)
    (f : α → BPair) : ∀ l : List α,
      (ground.famFold BPair.add BPair.unit
        (fun x => c * f x) l).oneValue
        (c * ground.famFold BPair.add BPair.unit f l)
  | [] => BPair.oneValue_symm (BPair.mul_unit c)
  | a :: t => by
    show (c * f a
        + ground.famFold BPair.add BPair.unit
          (fun x => c * f x) t).oneValue
      (c * (f a + ground.famFold BPair.add BPair.unit f t))
    rw [BPair.left_distrib]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (foldB_mul_left c f t)

/-- The stored keys sit below a stated bound. -/
def keysBelow (w : Nat) : List (Nat × BPair) → Prop
  | [] => True
  | (k, _) :: es => k < w ∧ keysBelow w es

def decKeysBelow (w : Nat) : ∀ es : List (Nat × BPair),
    Decidable (keysBelow w es)
  | [] => isTrue trivial
  | (_, _) :: es => @instDecidableAnd _ _ inferInstance
      (decKeysBelow w es)

instance instGround35 (w : Nat) (es : List (Nat × BPair)) :
    Decidable (keysBelow w es) := decKeysBelow w es

/-- Two key lists below one bound join below it. -/
theorem keysBelow_append (w : Nat) :
    ∀ a b : List (Nat × BPair), keysBelow w a → keysBelow w b →
      keysBelow w (a ++ b)
  | [], _, _, hb => hb
  | (_, _) :: a, b, ha, hb =>
    ⟨ha.1, keysBelow_append w a b ha.2 hb⟩

/-- The rate's decay read along a width family, one comparison per
consecutive pair: each member cleared at the rate's second member
sits at or below its predecessor cleared at the first. -/
def widthRate (rn rd : Pos) : List BPair → Prop
  | [] => True
  | [_] => True
  | w :: w' :: t => w'.scale rd ≤ w.scale rn ∧ widthRate rn rd (w' :: t)

def decWidthRate (rn rd : Pos) : ∀ ws : List BPair,
    Decidable (widthRate rn rd ws)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | _ :: w' :: t => @instDecidableAnd _ _ inferInstance
      (decWidthRate rn rd (w' :: t))

instance instGround36 (rn rd : Pos) (ws : List BPair) :
    Decidable (widthRate rn rd ws) := decWidthRate rn rd ws

/-- The family's last member sits at or above the sum's unit, the
telescope's one consumed positivity. -/
def unitLast : List BPair → Prop
  | [] => True
  | [w] => BPair.unit ≤ w
  | _ :: w' :: t => unitLast (w' :: t)

def decUnitLast : ∀ ws : List BPair, Decidable (unitLast ws)
  | [] => isTrue trivial
  | [w] => inferInstanceAs (Decidable (BPair.unit ≤ w))
  | _ :: w' :: t => decUnitLast (w' :: t)

instance instGround37 (ws : List BPair) : Decidable (unitLast ws) :=
  decUnitLast ws

/-- The width sum against a decaying family: at a rate split
`rn + gr = rd`, a family whose successive members decay by the rate
read and whose last member sits at or above the sum's unit has its
whole fold, cleared at the gap `gr`, at or below its head cleared
at `rd` — the telescope absorbing the tail into the head's own
margin. -/
theorem widthSum (rn gr rd : Pos) (hg : rn + gr = rd) :
    ∀ ws : List BPair, widthRate rn rd ws → unitLast ws →
    (ground.bsum id ws).scale gr
      ≤ (ground.getAt BPair.unit ws 0).scale rd := by
  intro ws
  induction ws with
  | nil =>
    intro _ _
    show BPair.unit.scale gr ≤ BPair.unit.scale rd
    exact ground.leB_congr (ground.unitScale gr) (ground.unitScale rd)
      (ground.leB_refl BPair.unit)
  | cons w t ih =>
    intro hrate hpos
    have heq : w.scale gr + w.scale rn = w.scale rd := by
      rw [← BPair.scale_addW, ground.add_comm gr rn, hg]
    have key : (ground.bsum id t).scale gr ≤ w.scale rn := by
      cases t with
      | nil =>
        exact ground.leB_congr_left (ground.unitScale gr)
          (ground.unitLeScale rn hpos)
      | cons w' t' =>
        exact ground.leB_trans (ih hrate.2 hpos) hrate.1
    show (w + ground.bsum id t).scale gr ≤ w.scale rd
    rw [BPair.scale_add, ← heq]
    exact ground.leB_add (ground.leB_refl _) key

/-- The memberwise swap passes through the fold. -/
theorem fold_swap {α : Type} (f : α → BPair) :
    ∀ l : List α,
      ground.famFold BPair.add BPair.unit (fun x => (f x).swap) l
        = (ground.famFold BPair.add BPair.unit f l).swap
  | [] => rfl
  | a :: t => by
    show (f a).swap
        + ground.famFold BPair.add BPair.unit
          (fun x => (f x).swap) t
      = ((ground.famFold BPair.add BPair.unit f (a :: t))).swap
    rw [fold_swap f t]
    exact BPair.swap_add (f a) (ground.famFold BPair.add
      BPair.unit f t)

/-- The grading passes through a fold. -/
theorem signedAt_fold {α : Type} (s : Bool) (f : α → BPair)
    (l : List α) :
    signedAt s (famFold BPair.add BPair.unit f l)
      = famFold BPair.add BPair.unit
          (fun x => signedAt s (f x)) l := by
  cases s
  · rfl
  · show (famFold BPair.add BPair.unit f l).swap = _
    exact (fold_swap f l).symm


/-- The grading passes through a guarded entry. -/
theorem signedAt_if (s : Bool) (P : Prop) [Decidable P]
    (x : BPair) :
    signedAt s (if P then x else BPair.unit)
      = if P then signedAt s x else BPair.unit := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    cases s <;> rfl


/-- The grading passes a scalar. -/
theorem signedAt_mul (s : Bool) (c x : BPair) :
    signedAt s (c * x) = c * signedAt s x := by
  cases s
  · rfl
  · exact (BPair.mul_swap c x).symm


/-- The grading passes through a sum. -/
theorem signedAt_add (s : Bool) (a b : BPair) :
    signedAt s (a + b)
      = signedAt s a + signedAt s b := by
  cases s
  · rfl
  · exact BPair.swap_add a b


/-- The grading passes a memberwise swap. -/
theorem signedAt_swap (s : Bool) (x : BPair) :
    signedAt s x.swap = (signedAt s x).swap := by
  cases s <;> rfl


/-- The grading respects the one-value class. -/
theorem signedAt_congr {x y : BPair} (s : Bool)
    (h : x.oneValue y) :
    (signedAt s x).oneValue (signedAt s y) := by
  cases s
  · exact h
  · exact swap_congr h


/-- The order's mixed composition: an at-or-below read against a
strict one on its right. -/
theorem leB_ltB_trans {x y z : BPair} (h : x ≤ y)
    (h' : y < z) : x < z :=
  if hc : x < z then hc
  else absurd (ltB_trans_le h' (leB_of_not_lt hc))
    (leB_not_lt h)

/-- The balance order's strict read scales at a factor strictly
above the sum's unit. -/
theorem ltB_mulPos {x y c : BPair} (h : x < y)
    (hc : BPair.unit < c) : x * c < y * c := by
  have hd : BPair.unit < y + x.swap :=
    BPair.lt_congr (BPair.add_swap_null x) (BPair.oneValue_refl _)
      (ltB_add h (leB_refl x.swap))
  have hxd : (x + (y + x.swap)).oneValue y := BPair.add_swap_cancel x y
  have hstep : x * c < x * c + (y + x.swap) * c :=
    ltB_addPos (unitLtMul hd hc)
  refine BPair.lt_congr (BPair.oneValue_refl (x * c)) ?_ hstep
  rw [← BPair.right_distrib]
  exact BPair.mul_congr_left hxd

/-- The order's cancellation at a right factor at or above the sum's
unit, the strict side. -/
theorem ltB_unscale {x y c : BPair} (hc : BPair.unit ≤ c)
    (h : x * c < y * c) : x < y :=
  if hlt : x < y then hlt
  else absurd h (leB_not_lt
    (leB_congr
      (BPair.oneValue_of_eq (BPair.mul_comm c y))
      (BPair.oneValue_of_eq (BPair.mul_comm c x))
      (leB_mulR hc (leB_of_not_lt hlt))))

/-- A factor at or beyond the sum's unit withdraws from a strict
floor at the unit, the strict cancellation's instance. -/
theorem unitLt_unscale {c x : BPair} (hc : BPair.unit ≤ c)
    (h : BPair.unit < c * x) : BPair.unit < x :=
  ltB_unscale hc
    (BPair.lt_congr
      (BPair.oneValue_symm (BPair.unit_mul c))
      (BPair.oneValue_of_eq (BPair.mul_comm c x)) h)

/-- A product at one member below the unit against one beyond
reads below the unit. -/
theorem mulNegPos {a b : BPair} (ha : a < BPair.unit)
    (hb : BPair.unit < b) : a * b < BPair.unit :=
  BPair.lt_congr (BPair.oneValue_refl (a * b)) (BPair.unit_mul b)
    (ltB_mulPos ha hb)

/-- The order's cancellation at a factor strictly above the sum's
unit. -/
theorem leB_unscale {x y c : BPair} (hc : BPair.unit < c)
    (h : x * c ≤ y * c) : x ≤ y :=
  leB_of_not_lt (fun hlt => leB_not_lt (leB_refl (x * c))
    (leB_ltB_trans h (ltB_mulPos hlt hc)))

/-- The order's cancellation at a left factor strictly above the sum's
unit. -/
theorem leB_unscale_left {X Y c : BPair} (hc : BPair.unit < c)
    (h : c * X ≤ c * Y) : X ≤ Y := by
  refine leB_unscale hc ?_
  rw [BPair.mul_comm X c, BPair.mul_comm Y c]
  exact h

/-- The square carries the balance order's strict read up at a
lower member at or beyond the sum's unit. -/
theorem ltB_sq_mono {x y : BPair} (hx : BPair.unit ≤ x)
    (h : x < y) : x * x < y * y :=
  leB_ltB_trans (leB_mulR hx (leB_of_lt h))
    (ltB_mulPos h (leB_ltB_trans hx h))

/-- The squared comparison reads back at the trichotomy: a datum
whose square sits at or below the square of one at or above the
sum's unit sits at or below it. -/
theorem leB_of_sq_le {a b : BPair} (hb : BPair.unit ≤ b)
    (h : ¬ (b * b < a * a)) : a ≤ b :=
  leB_of_not_lt (fun hlt => h (ltB_sq_mono hb hlt))

/-- The trichotomy of squares: a datum whose square sits strictly
below the square of one at or beyond the sum's unit sits strictly
below it. -/
theorem ltB_of_sq {x y : BPair} (hx : BPair.unit ≤ x)
    (h : y * y < x * x) : y < x :=
  Decidable.byCases (p := y < x) (fun hlt => hlt) (fun hn =>
    absurd h (leB_not_lt
      (leB_mul_mono hx (leB_trans hx (leB_of_not_lt hn))
        (leB_of_not_lt hn) (leB_of_not_lt hn))))

/-- A count strictly above the sum's unit cancels off an
at-or-above-unit read of its scale. -/
theorem unitLeUnscale {z : BPair} {k : Nat}
    (hk : BPair.unit < BPair.ofNat k)
    (h : BPair.unit ≤ BPair.ofNat k * z) : BPair.unit ≤ z :=
  leB_unscale hk
    (leB_congr_right
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofNat k) z))
      (leB_congr_left (BPair.oneValue_symm
        (BPair.unit_mul (BPair.ofNat k))) h))

/-! The order kit's join and split at the balance carrier: a sum's
one-value read against two at-or-below summand reads splits into
the summands' own, and a sum strictly above the sum's unit at two
at-or-above summands carries a summand strictly above it
(`def:ground`'s order tier); beside them the per-root reads at the
two clearings, `thm:detector`'s side comparison and `lem:split`'s
root side carried at the pair carrier, placed here at the
statements' own objects. -/

/-- A sum reading one value under two at-or-below summand reads
splits: each summand reads one value with its partner. -/
theorem addOneValue_of_le {x y u v : BPair} (hx : x ≤ y) (hu : u ≤ v)
    (he : (x + u).oneValue (y + v)) : x.oneValue y ∧ u.oneValue v := by
  have hxy : x.oneValue y :=
    leB_antisymm hx (leB_of_not_lt (fun hlt =>
      leB_not_lt (show y + v ≤ x + u from Or.inl (BPair.oneValue_symm he))
        (ltB_add hlt hu)))
  refine ⟨hxy, BPair.add_cancel (c := x) ?_⟩
  refine BPair.oneValue_trans
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm u x)) he) ?_
  exact BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm y v))
    (BPair.add_congr (BPair.oneValue_refl v) (BPair.oneValue_symm hxy))

/-- A sum strictly above the sum's unit at two summands at or above
it carries a summand strictly above it. -/
theorem posOfAddPos {x u : BPair} (hx : BPair.unit ≤ x)
    (hu : BPair.unit ≤ u) (hp : BPair.unit < x + u) :
    BPair.unit < x ∨ BPair.unit < u := by
  have hx' : BPair.unit.oneValue x ∨ BPair.unit < x := hx
  match hx' with
  | Or.inr hlt => exact Or.inl hlt
  | Or.inl he =>
    have hu' : BPair.unit.oneValue u ∨ BPair.unit < u := hu
    match hu' with
    | Or.inr hlt => exact Or.inr hlt
    | Or.inl he' =>
      have hle : x + u ≤ BPair.unit :=
        Or.inl (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_symm he)
            (BPair.oneValue_symm he'))
          (BPair.unit_add BPair.unit))
      exact absurd hp (leB_not_lt hle)

/-- A located root at the kernel point or at or beyond the edge
sits at or above the sum's unit, the root's side read at the two
clearings. -/
theorem rootUnitLe {nj : BPair} {dj E0 p q : Pos}
    (hread : nj.oneValue BPair.unit
      ∨ ¬ (nj.scale q < BPair.ofPos (E0 * p * dj))) :
    BPair.unit ≤ nj := by
  match hread with
  | Or.inl hz => exact Or.inl (BPair.oneValue_symm hz)
  | Or.inr hnl =>
    have hle : BPair.ofPos (E0 * p * dj) ≤ nj.scale q :=
      ground.leB_of_not_lt hnl
    have h1 : BPair.unit.scale q ≤ nj.scale q :=
      ground.leB_congr_left (ground.unitScale q)
        (ground.leB_trans (Or.inr (ground.unitLtOfPos (E0 * p * dj))) hle)
    exact ground.leB_of_not_lt
      (fun hlt => ground.leB_not_lt h1 (BPair.scale_lt q hlt))

/-- The per-root comparison: a located root at the kernel point or
at or beyond the edge prices the gap's summand against the
square's at the two clearings, `thm:detector`'s side read at
`lem:split`'s root data. -/
theorem termLe {vj kj nj gj : BPair} {dj E0 p q : Pos}
    (hgpos : BPair.unit < gj)
    (hv : vj.oneValue (nj * gj))
    (hk : (BPair.ofPos dj * kj).oneValue (nj * (nj * gj)))
    (hread : nj.oneValue BPair.unit
      ∨ ¬ (nj.scale q < BPair.ofPos (E0 * p * dj))) :
    vj.scale (E0 * p) ≤ kj.scale q := by
  refine ground.leB_congr_left
    (BPair.scale_congr (E0 * p) (BPair.oneValue_symm hv)) ?_
  refine ground.leB_unscale (ground.unitLtOfPos dj) ?_
  rw [BPair.mul_comm ((nj * gj).scale (E0 * p)) (BPair.ofPos dj),
    BPair.mul_comm (kj.scale q) (BPair.ofPos dj),
    BPair.mul_scale (BPair.ofPos dj) (nj * gj) (E0 * p),
    BPair.mul_scale (BPair.ofPos dj) kj q]
  refine ground.leB_congr_right
    (BPair.scale_congr q (BPair.oneValue_symm hk)) ?_
  rw [show BPair.ofPos dj * (nj * gj) = gj * (nj * BPair.ofPos dj) from by
      rw [BPair.mul_left_comm (BPair.ofPos dj) nj gj,
        BPair.mul_comm (BPair.ofPos dj) gj,
        BPair.mul_left_comm nj gj (BPair.ofPos dj)],
    show nj * (nj * gj) = gj * (nj * nj) from by
      rw [BPair.mul_comm nj gj, BPair.mul_left_comm nj gj nj],
    ← BPair.mul_scale gj (nj * BPair.ofPos dj) (E0 * p),
    ← BPair.mul_scale gj (nj * nj) q]
  refine ground.leB_mulR (Or.inr hgpos) ?_
  rw [← BPair.mul_scale nj (BPair.ofPos dj) (E0 * p),
    ← BPair.mul_scale nj nj q]
  match hread with
  | Or.inl hz =>
    exact ground.leB_congr
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left hz) (BPair.unit_mul _)))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left hz) (BPair.unit_mul _)))
      (ground.leB_refl BPair.unit)
  | Or.inr hnl =>
    have hle : BPair.ofPos (E0 * p * dj) ≤ nj.scale q := ground.leB_of_not_lt hnl
    have hpos : BPair.unit ≤ nj := rootUnitLe (Or.inr hnl)
    refine ground.leB_congr_left ?_ (ground.leB_mulR hpos hle)
    refine BPair.mul_congr (BPair.oneValue_refl nj) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.scale_ofPos dj (E0 * p)) ?_)
    rw [ground.mul_comm dj (E0 * p)]
    exact BPair.oneValue_refl _


/-- A read carried by both halves of a join is carried by the
join. -/
theorem all_of_append {α : Type} (P : α → Prop) :
    ∀ (u v : List α), (∀ x ∈ u, P x) → (∀ x ∈ v, P x) →
    ∀ x ∈ u ++ v, P x
  | [], _, _, hv => fun x hx => hv x hx
  | a :: u, v, hu, hv => by
    intro x hx
    cases hx with
    | head as => exact hu a (List.Mem.head _)
    | tail b h =>
      exact all_of_append P u v
        (fun z hz => hu z (List.Mem.tail _ hz)) hv _ h


/-- A read carried by every image is carried by the mapped list. -/
theorem all_of_map {α β : Type} (P : β → Prop) (f : α → β)
    (h : ∀ a, P (f a)) : ∀ (l : List α), ∀ x ∈ l.map f, P x
  | [] => fun _ hx => nomatch hx
  | a :: l => by
    intro x hx
    cases hx with
    | head as => exact h a
    | tail b hx' => exact all_of_map P f h l _ hx'


/-- A read carried by every block is carried by the flattened
family. -/
theorem all_of_flatMap {α β : Type} (P : β → Prop)
    (g : α → List β) (h : ∀ a, ∀ x ∈ g a, P x) :
    ∀ (l : List α), ∀ x ∈ l.flatMap g, P x
  | [] => fun _ hx => nomatch hx
  | a :: l => by
    show ∀ x ∈ g a ++ l.flatMap g, P x
    exact all_of_append P (g a) (l.flatMap g) (h a)
      (all_of_flatMap P g h l)


/-- The kept members carry the seed's read and the test's own. -/
theorem all_of_filter {α : Type} (P : α → Prop)
    (q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, P x) →
    ∀ x ∈ l.filter q, P x ∧ q x = true
  | [], _ => fun _ hx => nomatch hx
  | a :: l, h => by
    have hrec := all_of_filter P q l
      (fun z hz => h z (List.Mem.tail _ hz))
    show ∀ x ∈ (match q a with
      | true => a :: List.filter q l
      | false => List.filter q l), P x ∧ q x = true
    cases hq : q a
    · exact hrec
    · intro x hx
      cases hx with
      | head as => exact ⟨h a (List.Mem.head _), hq⟩
      | tail b hx' => exact hrec _ hx'


/-- The odd side reads the member's swap. -/
theorem signedAt_not (s : Bool) (x : BPair) :
    signedAt (!s) x = (signedAt s x).swap := by
  cases s
  · rfl
  · rfl


/-- A count pair's swap reads the flipped counts. -/
theorem BPair.ofCounts_swap (a b : Nat) :
    (BPair.ofCounts a b).swap = BPair.ofCounts b a := by
  show (BPair.ofNat a + (BPair.ofNat b).swap).swap = _
  rw [← BPair.swap_add (BPair.ofNat a) ((BPair.ofNat b).swap),
    BPair.add_comm]
  rfl


/-- A count pair against its flip reads the unit. -/
theorem BPair.ofCounts_pair (a b : Nat) :
    (BPair.ofCounts b a + BPair.ofCounts a b).oneValue BPair.unit := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofCounts_add b a a b)) ?_
  rw [Nat.add_comm a b]
  exact BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm _ _))
    (BPair.swap_add_null (BPair.oneValue_refl (BPair.ofNat (b + a))))


/-- Two family folds exchange, at any two carriers (the
range-indexed exchange's list-general form). -/
theorem foldB_swapL {α β : Type} [DecidableEq β]
    (T : α → β → BPair) :
    ∀ (l : List α) (m : List β),
    (famFold BPair.add BPair.unit
      (fun a => famFold BPair.add BPair.unit (T a) m)
      l).oneValue
      (famFold BPair.add BPair.unit
        (fun b => famFold BPair.add BPair.unit
          (fun a => T a b) l) m)
  | [], m => BPair.oneValue_symm (foldB_null _ m
      (fun _ _ => BPair.oneValue_refl _))
  | a :: l', m => by
    show (famFold BPair.add BPair.unit (T a) m
      + famFold BPair.add BPair.unit
          (fun a' => famFold BPair.add BPair.unit (T a') m)
          l').oneValue _
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (foldB_swapL T l' m)) ?_
    exact BPair.oneValue_symm (foldB_add
      (fun b => T a b)
      (fun b => famFold BPair.add BPair.unit
        (fun a' => T a' b) l') m)

/-- The nested exchange at the count index, the two-carrier
exchange's instance. -/
theorem bsum_swap (F : Nat → Nat → BPair) :
    ∀ (l m : List Nat),
    (bsum (fun i => bsum (fun j => F i j) m) l).oneValue
      (bsum (fun j => bsum (fun i => F i j) l) m) :=
  fun l m => foldB_swapL F l m

/-- A constant family's fold is the family's count against the
constant. -/
theorem foldB_const {α : Type} (c : BPair) : ∀ l : List α,
    (ground.famFold BPair.add BPair.unit (fun _ => c) l).oneValue
      (BPair.ofNat l.length * c)
  | [] => BPair.oneValue_symm (BPair.unit_mul c)
  | _ :: t => by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl c) (foldB_const c t)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm c (BPair.ofNat t.length * c))) ?_
    exact BPair.oneValue_symm (ground.ofNat_succ_mul t.length c)

/-- A count family against one datum collects at the counts'
fold. -/
theorem bsum_scalar {α : Type} (c : α → Nat) (z : BPair) :
    ∀ l : List α,
    (bsum (fun i => BPair.ofNat (c i) * z) l).oneValue
      (BPair.ofNat (ground.famFold Nat.add 0 c l) * z)
  | [] => BPair.oneValue_symm (BPair.unit_mul z)
  | a :: t => by
    show (BPair.ofNat (c a) * z
        + bsum (fun i => BPair.ofNat (c i) * z) t).oneValue
      (BPair.ofNat (c a + ground.famFold Nat.add 0 c t) * z)
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (bsum_scalar c z t)) ?_
    rw [← BPair.right_distrib]
    exact BPair.mul_congr_left
      (BPair.oneValue_symm (BPair.ofNat_add (c a) _))

/-- The count fold's pair read, member by member. -/
theorem ofNat_famFold (g : Nat → Nat) (l : List Nat) :
    (BPair.ofNat (ground.famFold Nat.add 0 g l)).oneValue
      (bsum (fun i => BPair.ofNat (g i)) l) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.mul_ofNat_one _)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (bsum_scalar g (BPair.ofNat 1) l)) ?_
  exact foldB_congr_members _ _ l
    (fun x _ => BPair.mul_ofNat_one _)

/-- The delta family's fold at a key occupied once: the picked
member's own read. -/
theorem bsum_pick (g : Nat → BPair) (l : List Nat) (i : Nat)
    (h : ground.countOf i l = 1) :
    (bsum (fun j => if i = j then g j else BPair.unit) l).oneValue
      (g i) :=
  foldB_pick (fun j => if i = j then g j else BPair.unit) i (g i)
    l h (BPair.oneValue_of_eq (if_pos rfl))
    (fun _ _ hxi => BPair.oneValue_of_eq
      (if_neg (fun he => hxi he.symm)))

/-- The point collapse at the Boolean guard: a fold reading a
stated value at the `==`-guarded key and the unit off it collapses
to the value at a key counted once. -/
theorem foldB_pickBeq (i : Nat) (X : BPair) (l : List Nat)
    (h : countOf i l = 1) :
    (famFold BPair.add BPair.unit
      (fun k => if k == i then X else BPair.unit) l).oneValue X :=
  foldB_pick _ i X l h
    (BPair.oneValue_of_eq (if_pos (eqBeqOf rfl)))
    (fun _ _ hxi => BPair.oneValue_of_eq
      (if_neg (fun hc => hxi (beqEqOf hc))))

/-- Two folds at one comparison per member compare, the carrier's
sum law along the list. -/
theorem bsum_le_of_mem {α : Type} (f g : α → BPair) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a) → bsum f l ≤ bsum g l
  | [], _ => leB_refl _
  | a :: t, h => by
    show f a + bsum f t ≤ g a + bsum g t
    exact leB_add (h a (List.Mem.head t))
      (bsum_le_of_mem f g t (fun x hx => h x (List.Mem.tail a hx)))

/-- Two folds at one comparison per occupied member compare, the
membership read at the count. -/
theorem bsum_le (f g : Nat → BPair) (l : List Nat)
    (h : ∀ i, 0 < ground.countOf i l → f i ≤ g i) :
    bsum f l ≤ bsum g l :=
  bsum_le_of_mem f g l (fun a ha => h a (countOf_pos_of_mem ha))

/-- A fold of reads at or above the sum's unit sits at or above
it, the members read at membership. -/
theorem foldB_nonneg_mem {α : Type} (f : α → BPair) : ∀ l : List α,
    (∀ a ∈ l, BPair.unit ≤ f a) →
    BPair.unit ≤ famFold BPair.add BPair.unit f l
  | [], _ => leB_refl _
  | a :: l, h => by
    show BPair.unit ≤ f a
      + famFold BPair.add BPair.unit f l
    exact unitLeAdd (h a (List.Mem.head l))
      (foldB_nonneg_mem f l (fun x hx => h x (List.Mem.tail a hx)))

/-- A fold of reads at or above the sum's unit sits at or above
it, the members read at their counts. -/
theorem foldB_nonneg {α : Type} [DecidableEq α]
    (f : α → BPair) (l : List α)
    (h : ∀ x, 0 < countOf x l → BPair.unit ≤ f x) :
    BPair.unit ≤ famFold BPair.add BPair.unit f l :=
  foldB_nonneg_mem f l (fun a ha => h a (countOf_pos_of_mem ha))

/-- A fold at the sum's unit whose every member sits at or above it
puts every member at the unit. -/
theorem bsum_unit_members {α : Type} [DecidableEq α] (f : α → BPair) :
    ∀ l : List α,
    (∀ x ∈ l, BPair.unit ≤ f x) →
      (ground.bsum f l).oneValue BPair.unit →
      ∀ x ∈ l, (f x).oneValue BPair.unit
  | [], _, _, _, hx => nomatch hx
  | a :: t, h, hs, x, hx => by
    have hA : BPair.unit ≤ f a := h a (List.Mem.head t)
    have hB : BPair.unit ≤ bsum f t :=
      foldB_nonneg f t (fun z hz =>
        h z (List.Mem.tail a (mem_of_countOf_pos z t hz)))
    have hsum : (f a + bsum f t).oneValue BPair.unit := hs
    have hAu : (f a).oneValue BPair.unit :=
      leB_antisymm (dom_of_split hsum hB) hA
    have hBu : (bsum f t).oneValue BPair.unit :=
      leB_antisymm
        (dom_of_split
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.add_comm (bsum f t) (f a)))
            hsum)
          hA)
        hB
    cases hx with
    | head => exact hAu
    | tail _ hm =>
      exact bsum_unit_members f t
        (fun z hz => h z (List.Mem.tail a hz)) hBu x hm

/-- A fold's two step spellings at a pointwise identity read one
value at every seed. -/
theorem foldl_congr {α β : Type} (f g : β → α → β)
    (h : ∀ acc x, f acc x = g acc x) :
    ∀ (l : List α) (init : β), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | a :: t, init => by
    show List.foldl f (f init a) t = List.foldl g (g init a) t
    rw [h init a]
    exact foldl_congr f g h t (g init a)

/-- The accumulating fold of a family collects to its seed against
the family fold, at every carrier with the displayed sum's laws. -/
theorem foldlFamO {α γ : Type} {add : γ → γ → γ} {unit : γ}
    {ov : γ → γ → Prop} (L : FoldLaws γ add unit ov) (g : α → γ) :
    ∀ (l : List α) (acc : γ),
      ov (l.foldl (fun a x => add a (g x)) acc)
        (add acc (famFold add unit g l))
  | [], acc => L.ovSymm (L.opUnit acc)
  | x :: t, acc => by
    show ov (t.foldl (fun a y => add a (g y)) (add acc (g x)))
      (add acc (add (g x) (famFold add unit g t)))
    exact L.ovTrans (foldlFamO L g t (add acc (g x)))
      (L.opAssoc acc (g x) (famFold add unit g t))

/-- The accumulating fold against its seed, at any fold whose
member joins associate off a right unit. -/
theorem foldlFold {α β : Type} (op : β → β → β) (unit : β)
    (hassoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hrunit : ∀ x, op x unit = x) (g : α → β) :
    ∀ (l : List α) (a : β),
    l.foldl (fun acc x => op acc (g x)) a
      = op a (famFold op unit g l)
  | [], a => (hrunit a).symm
  | x :: t, a => by
    show t.foldl (fun acc y => op acc (g y)) (op a (g x))
      = op a (op (g x) (famFold op unit g t))
    rw [foldlFold op unit hassoc hrunit g t (op a (g x))]
    exact hassoc a (g x) (famFold op unit g t)

/-- The additive left fold as the family fold, the fold-seed
read's instance. -/
theorem foldlSum {α : Type} (g : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc x => acc + g x) a
      = a + ground.famFold Nat.add 0 g l :=
  foldlFold Nat.add 0 Nat.add_assoc Nat.add_zero g l a

/-- The running product collects at the seed against the family's
multiplicative fold. -/
theorem foldlProd {α : Type} (g : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc x => acc * g x) a
      = a * ground.famFold Nat.mul 1 g l :=
  foldlFold Nat.mul 1 mulAssoc Nat.mul_one g l a

/-- The product fold splits over a pointwise product. -/
theorem famFold_mul_split (f g : Nat → Nat) : ∀ l : List Nat,
    famFold Nat.mul 1 (fun x => f x * g x) l
      = famFold Nat.mul 1 f l * famFold Nat.mul 1 g l :=
  famFold_add_ov natMulFoldLaws f g

/-- The nested accumulating product reads the two folds' own. -/
theorem foldl_nest (g : Nat → Nat → Nat) (K : Nat → List Nat) :
    ∀ (L : List Nat) (n : Nat),
      L.foldl (fun acc i => (K i).foldl (fun acc2 j => acc2 * g i j) acc) n
        = n * famFold Nat.mul 1
            (fun i => famFold Nat.mul 1 (g i) (K i)) L
  | [], n => (Nat.mul_one n).symm
  | x :: t, n => by
    show t.foldl (fun acc i =>
        (K i).foldl (fun acc2 j => acc2 * g i j) acc)
        ((K x).foldl (fun acc2 j => acc2 * g x j) n)
      = n * (famFold Nat.mul 1 (g x) (K x)
        * famFold Nat.mul 1
          (fun i => famFold Nat.mul 1 (g i) (K i)) t)
    have hstep : (K x).foldl (fun acc2 j => acc2 * g x j) n
        = n * famFold Nat.mul 1 (g x) (K x) :=
      foldlFold Nat.mul 1 mulAssoc Nat.mul_one (g x) (K x) n
    rw [hstep, foldl_nest g K t (n * famFold Nat.mul 1 (g x) (K x)),
      mulAssoc]


/-- The additive fold hoists its seed: the fold at a stated seed is
the seed joined to the fold at the sum's unit (`foldlSum` at both
seeds). -/
theorem foldlSeed {α : Type} (g : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc x => acc + g x) a
      = a + l.foldl (fun acc x => acc + g x) 0 := by
  rw [foldlSum g l a, foldlSum g l 0]
  rw [Nat.zero_add]

/-! The index range's Boolean fold, a read's own carrier: a
predicate decided at every key of a range folds to one datum, and
the fold reads back key by key.  The range unfolding and the join's
fold split are hand-rolled here (the core `List.range` and
`List.all` lemmas read through `propext`), as is the conjunction's
own kit. -/

/-- The loop's accumulator rides the join. -/
theorem rangeLoop_acc : ∀ (n : Nat) (acc : List Nat),
    List.range.loop n acc = List.range.loop n [] ++ acc
  | 0, _ => rfl
  | n + 1, acc => by
    show List.range.loop n (n :: acc)
      = List.range.loop (n + 1) [] ++ acc
    rw [rangeLoop_acc n (n :: acc),
      show List.range.loop (n + 1) [] = List.range.loop n [n] from rfl,
      rangeLoop_acc n [n], append_assoc]
    rfl

/-- The index range grows at its end. -/
theorem range_succ (n : Nat) :
    List.range (n + 1) = List.range n ++ [n] :=
  rangeLoop_acc n [n]

/-! The reversal kit: the family rotation (`rotAt`), the
range's length and entry reads, the matrix at an entry formula over
two key ranges (`matOf`), the cons reversal with its length, count
and total reads,
the join's reversal with the involution and the map's ride
(`reverse_append`, `reverse_reverse`, `map_reverse`), and the
count family's total (`sumNat`, `def:ground`'s count-carrier fold)
with its raise, lowering, leading-segment and reversal reads — the
core `List.range` and `List.reverse` lemma neighborhoods read
through `propext`, so the kit is hand-rolled off the loop. -/

theorem length_range : ∀ d : Nat, (List.range d).length = d
  | 0 => rfl
  | d + 1 => by
    rw [range_succ d, ground.length_append, length_range d]
    rfl

/-- The range's map reads the range's own length. -/
theorem length_mapRange {α : Type} (f : Nat → α) (n : Nat) :
    ((List.range n).map f).length = n := by
  rw [ground.length_map, ground.length_range]

/-- The key list's mapped entry is the map's own value at the key,
the off-range read the default. -/
theorem getAt_map_range {α : Type} (d0 : α) (f : Nat → α) :
    ∀ (d i : Nat), ground.getAt d0 ((List.range d).map f) i
      = if i < d then f i else d0
  | 0, i => by
    rw [if_neg (Nat.not_lt_zero i)]
    rfl
  | d + 1, i => by
    rw [range_succ d, ground.map_append, ground.getAt_append,
      length_mapRange]
    by_cases hlt : i < d
    · rw [if_pos hlt, getAt_map_range d0 f d i, if_pos hlt,
        if_pos (Nat.lt_succ_of_lt hlt)]
    · rw [if_neg hlt]
      by_cases heq : i = d
      · rw [heq, Nat.sub_self, if_pos (Nat.lt_succ_self d)]
        rfl
      · have hdi : d < i :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt)
            (fun e => heq e.symm)
        rw [if_neg (fun hs : i < d + 1 =>
          heq (Nat.le_antisymm (Nat.le_of_lt_succ hs)
            (Nat.le_of_lt hdi)))]
        cases hk : i - d with
        | zero =>
          exact absurd (hk ▸ subPos hdi) (Nat.lt_irrefl 0)
        | succ k => rfl

/-- The key list's entry is its key, the unit assignment's read. -/
theorem getAt_range (d i : Nat) (h : i < d) :
    ground.getAt 0 (List.range d) i = i := by
  rw [← ground.map_id (List.range d),
    getAt_map_range 0 (fun x => x) d i, if_pos h]

/-- The exchanged assignment's entries: the traded keys against
each further key's own. -/
theorem getAt_adjSwap_range (d k t : Nat) (hk : k + 1 < d) (ht : t < d) :
    getAt 0 (adjSwap k (List.range d)) t
      = if t = k then k + 1 else if t = k + 1 then k else t := by
  rw [getAt_adjSwap 0 k (List.range d)
      (by rw [length_range d]; exact hk) t,
    getAt_range d _ (swapIx_lt (Nat.lt_of_succ_lt hk) hk t ht)]
  rfl

/-- The exchange names its key: two exchanges of the key list agree
only at one key. -/
theorem adjSwap_range_inj (d k b : Nat) (hk : k + 1 < d) (hb : b + 1 < d)
    (he : adjSwap k (List.range d)
      = adjSwap b (List.range d)) : k = b := by
  have hlen : (List.range d).length = d := length_range d
  have hval := congrArg (fun l => getAt 0 l k) he
  have hL : getAt 0 (adjSwap k (List.range d)) k = k + 1 := by
    rw [getAt_adjSwap_fst 0 k (List.range d)
        (by rw [hlen]; exact hk),
      getAt_range d (k + 1) hk]
  by_cases hkb : k = b
  · exact hkb
  · by_cases hk1 : k = b + 1
    · have hR : getAt 0 (adjSwap b (List.range d)) k = b := by
        rw [hk1, getAt_adjSwap_snd 0 b (List.range d)
            (by rw [hlen]; exact hb),
          getAt_range d b (Nat.lt_of_succ_lt hb)]
      have hkb1 : k + 1 = b := hL.symm.trans (hval.trans hR)
      rw [hk1] at hkb1
      exact absurd (addCancelL b
          (show b + 2 = b + 0 by rw [Nat.add_zero]; exact hkb1))
        (by decide +kernel)
    · have hR : getAt 0 (adjSwap b (List.range d)) k = k := by
        rw [getAt_adjSwap_ne 0 b (List.range d) k hkb hk1,
          getAt_range d k (Nat.lt_of_succ_lt hk)]
      exact absurd (hL.symm.trans (hval.trans hR)) (Nat.succ_ne_self k)

theorem range_cons (n : Nat) :
    List.range (n + 1)
      = 0 :: (List.range n).map (fun j => j + 1) := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · show (List.range (n + 1)).length
      = ((List.range n).map (fun j => j + 1)).length + 1
    rw [length_range, length_mapRange]
  · intro i hi
    rw [length_range] at hi
    match i with
    | 0 =>
      rw [getAt_range (n + 1) 0 (Nat.succ_pos n)]
      rfl
    | j + 1 =>
      have hj : j < n := Nat.lt_of_succ_lt_succ hi
      rw [getAt_range (n + 1) (j + 1) hi]
      show j + 1
        = ground.getAt 0 ((List.range n).map (fun j => j + 1)) j
      rw [ground.getAt_map 0 0 (fun j => j + 1) (List.range n) j
          (by rw [length_range]; exact hj),
        getAt_range n j hj]

private theorem reverseAux_acc {α : Type} : ∀ (w acc : List α),
    w.reverseAux acc = w.reverseAux [] ++ acc
  | [], _ => rfl
  | k :: w, acc => by
    show w.reverseAux (k :: acc) = (k :: w).reverseAux [] ++ acc
    rw [reverseAux_acc w (k :: acc),
      show (k :: w).reverseAux [] = w.reverseAux [k] from rfl,
      reverseAux_acc w [k], ground.append_assoc]
    rfl

/-- The cons reversal is the reversed tail joined at the
head. -/
theorem reverse_cons {α : Type} (k : α) (w : List α) :
    (k :: w).reverse = w.reverse ++ [k] :=
  reverseAux_acc w [k]

theorem length_reverse {α : Type} : ∀ w : List α,
    w.reverse.length = w.length
  | [] => rfl
  | k :: w => by
    rw [reverse_cons, ground.length_append, length_reverse w]
    rfl

/-- The reversed family's fold is the family's own, at an exchanging
and regrouping operation with its unit. -/
theorem famFold_rev {α β : Type} (add : β → β → β) (unit : β)
    (hassoc : ∀ x y z, add (add x y) z = add x (add y z))
    (hunit : ∀ x, add unit x = x)
    (hcomm : ∀ x y, add x y = add y x) (f : α → β) :
    ∀ l : List α, famFold add unit f l.reverse = famFold add unit f l
  | [] => rfl
  | x :: t => by
    rw [reverse_cons x t,
      famFold_append add unit hassoc hunit f t.reverse [x],
      famFold_rev add unit hassoc hunit hcomm f t]
    show add (famFold add unit f t) (add (f x) unit)
      = add (f x) (famFold add unit f t)
    rw [hcomm (f x) unit, hunit (f x), hcomm]

theorem countOf_reverse {α : Type} [DecidableEq α] (x : α) :
    ∀ w : List α,
    ground.countOf x w.reverse = ground.countOf x w
  | [] => rfl
  | k :: w => by
    rw [reverse_cons, ground.countOf_append, countOf_reverse x w,
      countOf_cons x k ([] : List α), countOf_cons x k w]
    show ground.countOf x w + ((if x = k then 1 else 0) + 0)
      = (if x = k then 1 else 0) + ground.countOf x w
    rw [Nat.add_comm]
    by_cases hxk : x = k
    · rw [if_pos hxk]
    · rw [if_neg hxk]

/-- The join reverses at the exchanged parts. -/
theorem reverse_append {α : Type} : ∀ l m : List α,
    (l ++ m).reverse = m.reverse ++ l.reverse
  | [], m => (append_nil m.reverse).symm
  | a :: l, m => by
    show (a :: (l ++ m)).reverse = m.reverse ++ (a :: l).reverse
    rw [reverse_cons a (l ++ m), reverse_append l m, reverse_cons a l,
      append_assoc m.reverse l.reverse [a]]

/-- The reversal undoes itself. -/
theorem reverse_reverse {α : Type} : ∀ l : List α,
    l.reverse.reverse = l
  | [] => rfl
  | a :: l => by
    rw [reverse_cons a l, reverse_append l.reverse [a],
      reverse_reverse l]
    rfl

/-- The map rides the reversal. -/
theorem map_reverse {α γ : Type} (f : α → γ) : ∀ l : List α,
    (l.map f).reverse = l.reverse.map f
  | [] => rfl
  | a :: l => by
    show (f a :: l.map f).reverse = (a :: l).reverse.map f
    rw [reverse_cons (f a) (l.map f), reverse_cons a l,
      map_append f l.reverse [a], map_reverse f l]
    rfl

/-- The reversal reads through the zip at matched lengths: the
componentwise walk of the two reversals is the walk's own
reversal. -/
theorem reverse_zipWith {α β γ : Type} (f : α → β → γ) :
    ∀ (x : List α) (y : List β), x.length = y.length →
      (List.zipWith f x y).reverse = List.zipWith f x.reverse y.reverse
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | a :: s, b :: t, h => by
    show (f a b :: List.zipWith f s t).reverse
      = List.zipWith f (a :: s).reverse (b :: t).reverse
    rw [reverse_cons (f a b) (List.zipWith f s t),
      reverse_zipWith f s t (Nat.succ.inj h),
      reverse_cons a s, reverse_cons b t,
      zipWith_append f s.reverse [a] t.reverse [b]
        (by rw [length_reverse, length_reverse, Nat.succ.inj h])]
    rfl

/-- The repeated family is its own reversal. -/
theorem reverse_replicate {α : Type} : ∀ (n : Nat) (a : α),
    (List.replicate n a).reverse = List.replicate n a
  | 0, _ => rfl
  | n + 1, a => by
    show (a :: List.replicate n a).reverse = List.replicate (n + 1) a
    rw [reverse_cons a (List.replicate n a), reverse_replicate n a,
      replicate_snoc a n]

/-- The count family's total: the family fold at the identity
read. -/
def sumNat (l : List Nat) : Nat :=
  famFold Nat.add 0 (fun x => x) l

/-- The edit moves the family's total by the entry's move: the
source entry withdraws and the read's entry joins. -/
theorem sumNat_editAt (f : Nat → Nat) :
    ∀ (i : Nat) (l : List Nat), i < l.length →
      sumNat (editAt f i l) + getAt 0 l i = sumNat l + f (getAt 0 l i)
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, a :: t, _ => by
    show f a + sumNat t + a = a + sumNat t + f a
    exact addSwapEnds (f a) (sumNat t) a
  | i + 1, a :: t, h => by
    show a + sumNat (editAt f i t) + getAt 0 t i
      = a + sumNat t + f (getAt 0 t i)
    rw [Nat.add_assoc a (sumNat (editAt f i t)) (getAt 0 t i),
      sumNat_editAt f i t (Nat.lt_of_succ_lt_succ h),
      Nat.add_assoc]

/-- A one-slot write changes a mapped sum by the written key's
additive gap, at every occupied slot. -/
theorem sumNat_map_set_join {α : Type} (f : α → Nat) (d x : α) (gap : Nat) :
    ∀ (m : List α) (i : Nat), i < m.length → f x + gap = f (getAt d m i) →
      sumNat ((m.set i x).map f) + gap = sumNat (m.map f)
  | [], _, h, _ => absurd h (Nat.not_lt_zero _)
  | a :: t, 0, _, h => by
    change f x + sumNat (t.map f) + gap = f a + sumNat (t.map f)
    rw [Nat.add_right_comm, h]
    rfl
  | a :: t, i + 1, hi, h => by
    change f a + sumNat ((t.set i x).map f) + gap = f a + sumNat (t.map f)
    rw [Nat.add_assoc, sumNat_map_set_join f d x gap t i (Nat.lt_of_succ_lt_succ hi) h]

/-- The gap fold against the total at a dominating bound: the gaps
join their lower members at the counted bound. -/
theorem gapFold_total (x : Nat) : ∀ (t : List Nat),
    (∀ q, q < t.length → getAt 0 t q ≤ x) →
    t.foldl (fun acc y => acc + (x - y)) 0 + sumNat t
      = t.length * x
  | [], _ => by
    show 0 + 0 = 0 * x
    rw [Nat.zero_mul x]
  | y :: t, hdom => by
    have hyx : y ≤ x := hdom 0 (Nat.succ_pos t.length)
    have hih := gapFold_total x t
      (fun q hq => hdom (q + 1) (Nat.succ_lt_succ hq))
    have hs : t.foldl (fun acc z => acc + (x - z)) (0 + (x - y))
        = 0 + (x - y) + t.foldl (fun acc z => acc + (x - z)) 0 :=
      foldlSeed (fun z => x - z) t (0 + (x - y))
    have hxy : x - y + y = x := subAdd hyx
    show t.foldl (fun acc z => acc + (x - z)) (0 + (x - y))
        + (y + sumNat t)
      = (t.length + 1) * x
    rw [hs, Nat.zero_add (x - y), Nat.add_add_add_comm, hxy, hih,
      mulAddR t.length 1 x, Nat.one_mul x,
      Nat.add_comm (t.length * x) x]

/-- The multiplicative fold over a key list at a value map, seeded
at one. -/
def prodOver {α : Type} (g : α → Nat) (K : List α) : Nat :=
  famFold Nat.mul 1 g K

/-- A pointwise bound at the members passes through the product. -/
theorem prodOver_le {α : Type} (F G : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, F x ≤ G x) →
      prodOver F l ≤ prodOver G l
  | [], _ => Nat.le_refl 1
  | a :: t, h =>
    Nat.mul_le_mul (h a (List.Mem.head t))
      (prodOver_le F G t (fun x hx => h x (List.Mem.tail a hx)))

/-- A pointwise-occupied family's product is occupied. -/
theorem prodOver_pos {α : Type} [DecidableEq α] (g : α → Nat) :
    ∀ l : List α, (∀ x, 0 < countOf x l → 0 < g x) →
      0 < prodOver g l
  | [], _ => Nat.le_refl 1
  | a :: t, h => by
    show 0 < g a * prodOver g t
    exact Nat.mul_pos
      (h a (by rw [countOf_head]; exact Nat.succ_pos _))
      (prodOver_pos g t (fun x hx =>
        h x (Nat.lt_of_lt_of_le hx (countOf_cons_le x a t))))

/-- A filter at the product's unit is no filter at all. -/
theorem prodOver_filter {α : Type} (g : α → Nat) (t : α → Bool)
    (h : ∀ v, t v = false → g v = 1) (K : List α) :
    prodOver g (K.filter t) = prodOver g K :=
  famFold_filter_ov natMulFoldLaws g t h K

/-- At a key occupied once in the family, the fold with that key's
factor withdrawn, against the key's own factor, reads the whole
fold (`def:ground`'s displayed product clause). -/
theorem prodOver_pick {α : Type} [DecidableEq α] (g : α → Nat)
    (x₀ : α) (K : List α) (h : countOf x₀ K = 1) :
    prodOver (fun x => if x = x₀ then 1 else g x) K * g x₀
      = prodOver g K := by
  have hpos : 0 < countOf x₀ K := by
    rw [h]
    exact Nat.succ_pos 0
  have hK : prodOver g K
      = g x₀ * prodOver g (eraseFirst x₀ K) :=
    famFold_eraseFirst Nat.mul 1 Nat.mul_comm mulAssoc g K x₀ hpos
  have hI : prodOver (fun x => if x = x₀ then 1 else g x) K
      = (if x₀ = x₀ then 1 else g x₀)
        * prodOver (fun x => if x = x₀ then 1 else g x)
            (eraseFirst x₀ K) :=
    famFold_eraseFirst Nat.mul 1 Nat.mul_comm mulAssoc _ K x₀ hpos
  have hz : countOf x₀ (eraseFirst x₀ K) = 0 := by
    have h2 := countOf_eraseFirst_self K x₀ hpos
    rw [h] at h2
    exact (Nat.succ.inj h2).symm
  have hcongr : prodOver (fun x => if x = x₀ then 1 else g x)
        (eraseFirst x₀ K)
      = prodOver g (eraseFirst x₀ K) :=
    famFold_congr_members Nat.mul 1 _ _ (eraseFirst x₀ K)
      (fun x hx => by
        have hxne : ¬ x = x₀ := fun he => by
          rw [he, hz] at hx
          exact absurd hx (Nat.lt_irrefl 0)
        rw [if_neg hxne])
  rw [hI, if_pos rfl, Nat.one_mul, hcongr,
    Nat.mul_comm (prodOver g (eraseFirst x₀ K)) (g x₀), ← hK]

/-- A constant family's product reads the count alone: two lists
of one length read one product. -/
theorem prodOver_const {α β : Type} (c : Nat) :
    ∀ (l : List α) (m : List β), l.length = m.length →
      prodOver (fun _ => c) l = prodOver (fun _ => c) m
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | _ :: t, _ :: u, h => by
    show c * prodOver (fun _ => c) t = c * prodOver (fun _ => c) u
    rw [prodOver_const c t u (Nat.succ.inj h)]

/-- An occupied constant's product over an occupied key range sits
at or beyond the constant. -/
theorem prodConst_ge (c : Nat) (hc : 1 ≤ c) :
    ∀ n : Nat, 1 ≤ n →
      c ≤ prodOver (fun _ => c) (List.range n)
  | 0, h => absurd h (Nat.not_succ_le_zero 0)
  | n + 1, _ => by
    rw [range_cons n]
    show c ≤ c * prodOver (fun _ => c)
      ((List.range n).map (fun j => j + 1))
    rw [prodOver_const c ((List.range n).map (fun j => j + 1))
      (List.range n) (length_map _ _)]
    have h := Nat.mul_le_mul (Nat.le_refl c)
      (prodOver_pos (fun _ => c) (List.range n) (fun _ _ => hc))
    rw [Nat.mul_one] at h
    exact h

theorem sumNat_append : ∀ u v : List Nat,
    sumNat (u ++ v) = sumNat u + sumNat v
  | [], v => (Nat.zero_add _).symm
  | a :: u, v => by
    show a + sumNat (u ++ v) = a + sumNat u + sumNat v
    rw [sumNat_append u v, Nat.add_assoc]

/-- A pointwise sum's total splits over its two summands. -/
theorem sumNat_map_add {α : Type} (f g : α → Nat) (l : List α) :
    sumNat (l.map (fun x => f x + g x))
      = sumNat (l.map f) + sumNat (l.map g) :=
  (famFold_map Nat.add 0 (fun x => x) (fun x => f x + g x) l).trans
    ((famFold_add_split f g l).trans
      (congr
        (congrArg Nat.add
          (famFold_map Nat.add 0 (fun x => x) f l).symm)
        (famFold_map Nat.add 0 (fun x => x) g l).symm))

/-- The componentwise sum's total is the two totals' own, at
matched widths. -/
theorem sumNat_zipWith_add :
    ∀ u v : List Nat, u.length = v.length →
      sumNat (List.zipWith (fun a b => a + b) u v)
        = sumNat u + sumNat v
  | [], [], _ => rfl
  | [], _ :: _, hl => nomatch hl
  | _ :: _, [], hl => nomatch hl
  | a :: u, b :: v, hl => by
    show a + b + sumNat (List.zipWith (fun a b => a + b) u v)
      = a + sumNat u + (b + sumNat v)
    rw [sumNat_zipWith_add u v (Nat.succ.inj hl),
      Nat.add_assoc a b (sumNat u + sumNat v),
      Nat.add_left_comm b (sumNat u) (sumNat v),
      ← Nat.add_assoc a (sumNat u) (b + sumNat v)]

/-- A raise inside the key list adds one box to the total. -/
theorem sumNat_bumpAt : ∀ (i : Nat) (l : List Nat),
    i < l.length → sumNat (ground.bumpAt i l) = sumNat l + 1
  := fun i l h => by
    refine addCancelR (getAt 0 l i) ?_
    refine (sumNat_editAt (fun x => x + 1) i l h).trans ?_
    rw [Nat.add_comm (getAt 0 l i) 1,
      ← Nat.add_assoc (sumNat l) 1 (getAt 0 l i)]

/-- A lowering at an occupied key withdraws one box from the
total; off an occupied key the truncating subtraction stands
still, so the occupancy is the statement's own binder. -/
theorem sumNat_dipAt : ∀ (j : Nat) (l : List Nat),
    0 < ground.getAt 0 l j →
    sumNat (ground.dipAt j l) + 1 = sumNat l
  := fun j l h => by
    have hlen : j < l.length := by
      match Nat.lt_or_ge j l.length with
      | .inl hl => exact hl
      | .inr hge =>
        rw [getAt_over 0 l j hge] at h
        exact absurd h (Nat.lt_irrefl 0)
    refine addCancelR (getAt 0 l j - 1) ?_
    rw [Nat.add_assoc (sumNat (dipAt j l)) 1 (getAt 0 l j - 1),
      Nat.add_comm 1 (getAt 0 l j - 1), subAdd h]
    exact sumNat_editAt (fun x => x - 1) j l hlen

/-- The family's lead key sits at or below any depth's leading
total joined to that depth's own key. -/
theorem headKey_le : ∀ (nt : List Nat) (j : Nat), j < nt.length →
    getAt 0 nt 0 ≤ sumNat (List.take j nt) + getAt 0 nt j
  | nt, 0, _ => Nat.le_of_eq (Nat.zero_add _).symm
  | [], j + 1, h => absurd h (Nat.not_lt_zero _)
  | n1 :: nt', j + 1, _ => by
    show n1 ≤ (n1 + sumNat (List.take j nt')) + getAt 0 nt' j
    rw [Nat.add_assoc]
    exact Nat.le_add_right n1 _

/-- No key's occupancy exceeds the family's total. -/
theorem getAt_le_sumNat : ∀ (l : List Nat) (i : Nat),
    ground.getAt 0 l i ≤ sumNat l
  | [], _ => Nat.zero_le 0
  | a :: t, 0 => Nat.le_add_right a (sumNat t)
  | a :: t, i + 1 =>
    Nat.le_trans (getAt_le_sumNat t i) (Nat.le_add_left (sumNat t) a)

/-- A member sits at or below the family's total. -/
theorem mem_le_sumNat : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ sumNat l
  | [], _, h => nomatch h
  | a :: t, x, h => by
    match h with
    | List.Mem.head _ => exact Nat.le_add_right _ _
    | List.Mem.tail _ ht =>
      exact Nat.le_trans (mem_le_sumNat t x ht) (Nat.le_add_left _ _)

/-- A constant block's total. -/
theorem sumNat_replicate (c : Nat) : ∀ k : Nat,
    sumNat (List.replicate k c) = k * c
  | 0 => (Nat.zero_mul c).symm
  | k + 1 => by
    show c + sumNat (List.replicate k c) = (k + 1) * c
    rw [
      sumNat_replicate c k,
      mulAddR k 1 c,
      Nat.one_mul c,
      Nat.add_comm c (k * c)]

/-- The unit content's total is its own letter count. -/
theorem sumNat_replicate_one (d : Nat) :
    sumNat (List.replicate d 1) = d := by
  rw [sumNat_replicate 1 d, Nat.mul_one]

/-- The vacant family's total is vacant. -/
theorem sumNat_replicate_zero (n : Nat) :
    sumNat (List.replicate n 0) = 0 := by
  rw [sumNat_replicate 0 n, Nat.mul_zero]

/-- The struck unit family's total is the full width. -/
theorem sumNat_replicate_strike (i e : Nat) (h : i ≤ e) :
    sumNat (List.replicate i 1 ++ 0 :: List.replicate (e - i) 1)
      = e := by
  rw [sumNat_append]
  show sumNat (List.replicate i 1)
      + (0 + sumNat (List.replicate (e - i) 1)) = e
  rw [sumNat_replicate_one i, sumNat_replicate_one (e - i),
    Nat.zero_add]
  exact natAddSubCancel h

/-- The reversal keeps the total. -/
theorem sumNat_reverse : ∀ w : List Nat,
    sumNat w.reverse = sumNat w
  | [] => rfl
  | k :: w => by
    rw [reverse_cons, sumNat_append, sumNat_reverse w]
    show sumNat w + (k + 0) = k + sumNat w
    rw [Nat.add_zero k, Nat.add_comm]

/-- A list's index fold reads its own sum. -/
theorem sumIndex : ∀ cs : List Nat,
    ground.famFold Nat.add 0 (fun k => ground.getAt 0 cs k)
      (List.range cs.length) = sumNat cs
  | [] => rfl
  | c :: t => by
    show ground.famFold Nat.add 0
        (fun k => ground.getAt 0 (c :: t) k)
        (List.range (t.length + 1)) = c + sumNat t
    rw [range_cons t.length]
    show ground.getAt 0 (c :: t) 0 + ground.famFold Nat.add 0
        (fun k => ground.getAt 0 (c :: t) k)
        ((List.range t.length).map (fun j => j + 1))
      = c + sumNat t
    rw [ground.famFold_map Nat.add 0
      (fun k => ground.getAt 0 (c :: t) k) (fun j => j + 1)
      (List.range t.length)]
    show c + ground.famFold Nat.add 0
        (fun x => ground.getAt 0 t x)
        (List.range t.length) = c + sumNat t
    rw [sumIndex t]

/-- The whole list's prefix is the total. -/
theorem prefixAt_full : ∀ (mu : List Nat) (k : Nat),
    mu.length ≤ k → prefixAt k mu = sumNat mu
  | [], k, _ => prefixAt_nil k
  | _ :: _, 0, h => nomatch h
  | a :: t, k + 1, h => by
    show a + prefixAt k t = a + sumNat t
    rw [prefixAt_full t k (Nat.le_of_succ_le_succ h)]

/-- The reversed display's read at the joined places. -/
theorem getAt_reverse {α : Type} (d : α) : ∀ (mu : List α) (t1 t2 : Nat),
    t1 + t2 + 1 = mu.length →
    ground.getAt d mu.reverse t1 = ground.getAt d mu t2
  | [], t1, t2, hj => nomatch hj
  | a :: t, t1, t2, hj => by
    rw [reverse_cons a t]
    match t2 with
    | 0 =>
      have ht1 : t1 = t.length := Nat.succ.inj hj
      rw [ht1, ← length_reverse t]
      exact ground.getAt_append_add d t.reverse [a] 0
    | s + 1 =>
      have hj' : t1 + s + 1 = t.length := Nat.succ.inj hj
      have ht1 : t1 < t.reverse.length := by
        rw [length_reverse, ← hj']
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self t1)
          (Nat.succ_le_succ (Nat.le_add_right t1 s))
      rw [ground.getAt_append d t.reverse [a] t1, if_pos ht1]
      show ground.getAt d t.reverse t1 = ground.getAt d t s
      exact getAt_reverse d t t1 s hj'

/-- The prefix of the reversed display joins its complement's to
the total. -/
theorem prefix_reverse_join :
    ∀ (k1 : Nat) (m : List Nat) (k2 : Nat), k1 + k2 = m.length →
    prefixAt k1 m.reverse + prefixAt k2 m = sumNat m
  | 0, m, k2, h => by
    rw [prefixAt_zero, Nat.zero_add,
      prefixAt_full m k2 (by
        rw [← h, Nat.zero_add]
        exact Nat.le_refl _)]
  | k1 + 1, m, k2, h => by
    have hkj : k1 + k2 + 1 = m.length :=
      (Nat.add_right_comm k1 1 k2).symm.trans h
    have h' : k1 + (k2 + 1) = m.length := hkj
    have hk1 : k1 < m.reverse.length := by
      rw [length_reverse, ← hkj]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k1)
        (Nat.succ_le_succ (Nat.le_add_right k1 k2))
    have hk2 : k2 < m.length := by
      rw [← hkj]
      exact Nat.lt_of_le_of_lt (Nat.le_add_left k2 k1)
        (Nat.lt_succ_self (k1 + k2))
    have hstep := prefix_reverse_join k1 m (k2 + 1) h'
    rw [prefixAt_succ m k2 hk2] at hstep
    rw [prefixAt_succ m.reverse k1 hk1,
      getAt_reverse 0 m k1 k2 hkj,
      Nat.add_assoc,
      Nat.add_comm (ground.getAt 0 m k2) (prefixAt k2 m)]
    exact hstep

theorem xorFalse : ∀ b : Bool, xor b false = b
  | true => rfl
  | false => rfl

theorem xorNot : ∀ b c : Bool, xor b (!c) = !(xor b c)
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

/-- A test refuses its own negation (`Bool.not_eq_self` is
propext- and Quot.sound-bearing; this is the clean spelling). -/
theorem boolNotSelf : ∀ b : Bool, ¬ ((!b) = b)
  | false, h => Bool.noConfusion h
  | true, h => Bool.noConfusion h

/-- A negated test true names the test false (`Bool.not_eq_true`
is propext-bearing; this is the clean spelling). -/
theorem boolFalseOfNot : ∀ {c : Bool}, (!c) = true → c = false
  | false, _ => rfl
  | true, h => Bool.noConfusion h

/-- Two values withheld off one guard sum at the guard: the
guarded sum is the sum of the guarded values. -/
theorem if_add (c : Prop) [Decidable c] (x y : Nat) :
    (if c then x else 0) + (if c then y else 0)
      = if c then x + y else 0 := by
  by_cases h : c
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h]

/-- A list filtered at a read is its places filtered at the read of
the member there, read back at the places. -/
theorem filter_map_range {α : Type} (d : α) (p : α → Bool) :
    ∀ l : List α,
      l.filter p = ((List.range l.length).filter (fun j => p (getAt d l j))).map (getAt d l)
  | [] => rfl
  | a :: t => by
    show (a :: t).filter p
      = ((List.range (t.length + 1)).filter (fun j => p (getAt d (a :: t) j))).map (getAt d (a :: t))
    rw [range_cons, filter_cons p a t]
    show (match p a with
        | true => a :: t.filter p
        | false => t.filter p)
      = ((0 :: (List.range t.length).map (fun j => j + 1)).filter
          (fun j => p (getAt d (a :: t) j))).map (getAt d (a :: t))
    rw [filter_cons (fun j => p (getAt d (a :: t) j)) 0 _,
      filter_map (fun j => j + 1) (fun j => p (getAt d (a :: t) j)) (List.range t.length),
      filter_map_range d p t]
    show (match p a with
        | true => a :: ((List.range t.length).filter (fun j => p (getAt d t j))).map (getAt d t)
        | false => ((List.range t.length).filter (fun j => p (getAt d t j))).map (getAt d t))
      = (match p a with
        | true => 0 :: ((List.range t.length).filter (fun j => p (getAt d t j))).map (fun j => j + 1)
        | false => ((List.range t.length).filter (fun j => p (getAt d t j))).map
            (fun j => j + 1)).map (getAt d (a :: t))
    cases p a with
    | true =>
      show a :: _ = a :: (((List.range t.length).filter (fun j => p (getAt d t j))).map
        (fun j => j + 1)).map (getAt d (a :: t))
      rw [map_map]
      rfl
    | false =>
      show _ = (((List.range t.length).filter (fun j => p (getAt d t j))).map
        (fun j => j + 1)).map (getAt d (a :: t))
      rw [map_map]
      rfl

/-- Nested guards over a withheld value exchange: a value held by
two guards is held by them in either order. -/
theorem if_swap (c e : Prop) [Decidable c] [Decidable e]
    (x : Nat) :
    (if c then (if e then x else 0) else 0)
      = if e then (if c then x else 0) else 0 := by
  by_cases hc : c
  · by_cases he : e
    · rw [if_pos hc, if_pos he, if_pos he, if_pos hc]
    · rw [if_pos hc, if_neg he, if_neg he]
  · by_cases he : e
    · rw [if_neg hc, if_pos he, if_neg hc]
    · rw [if_neg hc, if_neg he]

theorem countOf_range (a : Nat) : ∀ d : Nat,
    ground.countOf a (List.range d) = if a < d then 1 else 0
  | 0 => by
    rw [if_neg (Nat.not_lt_zero a)]
    rfl
  | d + 1 => by
    rw [range_succ d, ground.countOf_append, countOf_range a d,
      countOf_cons a d ([] : List Nat)]
    show (if a < d then 1 else 0)
        + ((if a = d then 1 else 0) + 0)
      = if a < d + 1 then 1 else 0
    by_cases hd : a = d
    · rw [if_neg (fun h : a < d => Nat.lt_irrefl d (by
          rw [hd] at h; exact h)),
        if_pos hd,
        if_pos (show a < d + 1 from by
          rw [hd]; exact Nat.lt_succ_self d)]
    · rw [if_neg hd]
      by_cases hlt : a < d
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · rw [if_neg hlt, if_neg (fun hs : a < d + 1 =>
          match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hs) with
          | .inl he => hd he
          | .inr hl => hlt hl)]

/-- The shift family's count at the closed indicator: a member of
the shifted range is counted once within the window and off it the
count is vacant. -/
theorem countOf_shiftRange (s n : Nat) :
    countOf s ((List.range n).map (fun l => l + 1))
      = if 1 ≤ s ∧ s ≤ n then 1 else 0 := by
  match s with
  | 0 =>
    rw [countOf_map_none (fun l => l + 1) 0 (List.range n)
        (fun v _ hv => Nat.noConfusion hv),
      if_neg (fun hc => Nat.not_succ_le_zero 0 hc.1)]
  | s + 1 =>
    rw [countOf_map_iff (fun l => l + 1) (List.range n) (s + 1) s
        (fun v _ =>
          ⟨fun hx => Nat.succ.inj hx, fun hy => by rw [hy]⟩),
      countOf_range s n]
    by_cases hsn : s < n
    · rw [if_pos hsn, if_pos ⟨Nat.succ_le_succ (Nat.zero_le s),
        Nat.succ_le_of_lt hsn⟩]
    · rw [if_neg hsn,
        if_neg (fun hc => hsn (Nat.lt_of_succ_le hc.2))]

/-- A key inside the range is counted once, the range read at its
occupied side. -/
theorem countOf_range_one {j n : Nat} (h : j < n) :
    ground.countOf j (List.range n) = 1 := by
  rw [countOf_range j n, if_pos h]

/-- A key inside the range is counted positively, the occupied
count's own read. -/
theorem countOf_range_pos {j n : Nat} (h : j < n) :
    0 < ground.countOf j (List.range n) := by
  rw [countOf_range_one h]
  exact Nat.succ_pos 0

/-- A key occupied in a range sits below the range. -/
theorem ltOfCountRange {j n : Nat} (h : 0 < countOf j (List.range n)) : j < n := by
  rw [countOf_range] at h
  cases hlt : decide (j < n) with
  | false =>
    rw [if_neg (of_decide_eq_false hlt)] at h
    exact absurd h (Nat.lt_irrefl 0)
  | true => exact of_decide_eq_true hlt

/-- Two range folds of pairwise equal members are equal. -/
theorem bsum_congr_range (F G : Nat → BPair) (n : Nat)
    (h : ∀ i, i < n → F i = G i) :
    bsum F (List.range n) = bsum G (List.range n) :=
  famFold_congr_members BPair.add BPair.unit F G (List.range n)
    (fun i hc => h i (ltOfCountRange hc))

/-- Two range folds of pairwise one-valued members are one value. -/
theorem bsum_congr_range_ov (F G : Nat → BPair) (n : Nat)
    (h : ∀ i, i < n → (F i).oneValue (G i)) :
    (bsum F (List.range n)).oneValue (bsum G (List.range n)) :=
  famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
    BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) F G
    (List.range n) (fun i hc => h i (ltOfCountRange hc))

/-- A range fold whose summand splits into two reads folds to the two
folds' sum. -/
theorem bsum_split (F B C : Nat → BPair) (n : Nat)
    (h : ∀ x, x < n → (F x).oneValue (B x + C x)) :
    (bsum F (List.range n)).oneValue (bsum B (List.range n) + bsum C (List.range n)) :=
  BPair.oneValue_trans (bsum_congr_range_ov F (fun x => B x + C x) n h) (foldB_add _ _ _)

/-- A key sits in a filtered range exactly at the predicate's read
joined to the range's. -/
theorem containsB_filter (P : Nat → Bool) (n y : Nat) :
    containsB (List.filter P (List.range n)) y
      = (P y && decide (y < n)) := by
  show decide (0 < countOf y (List.filter P (List.range n))) = _
  rw [countOf_filter P y (List.range n), countOf_range y n]
  cases hp : P y with
  | true =>
    rw [if_pos rfl]
    by_cases hyn : y < n
    · rw [if_pos hyn, decide_eq_true hyn]
      rfl
    · rw [if_neg hyn]
      cases hd : decide (y < n) with
      | true => exact absurd (of_decide_eq_true hd) hyn
      | false => rfl
  | false =>
    rw [if_neg (boolNe rfl)]
    rfl

/-- The key range is a distinct list, every count at most one. -/
theorem distinctList_range (n : Nat) :
    ground.distinctList (List.range n) := fun x _ => by
  rw [countOf_range x n]
  cases Nat.lt_or_ge x n with
  | inl h => rw [if_pos h]; exact Nat.le_refl 1
  | inr h =>
    rw [if_neg (fun hc => absurd (Nat.lt_of_lt_of_le hc h)
      (Nat.lt_irrefl x))]
    exact Nat.zero_le 1

/-- A key below the width joins the range family. -/
theorem memRange {n i : Nat} (h : i < n) : i ∈ List.range n :=
  ground.mem_of_countOf_pos i (List.range n) (countOf_range_pos h)

/-- The index family's members are the keys below the count. -/
theorem ltOfMem {n i : Nat}
    (h : 0 < ground.countOf i (List.range n)) : i < n := by
  rw [countOf_range i n] at h
  by_cases hi : i < n
  · exact hi
  · rw [if_neg hi] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- A member of the key range is a key below the count, the
membership's own composition. -/
theorem ltOfMemRange {n i : Nat} (h : i ∈ List.range n) : i < n :=
  ltOfMem (countOf_pos_of_mem h)

/-- Two folds agreeing at every key of a range are one value: the
member congruence at the range carrier's own key binder. -/
theorem famFold_congr_range (F G : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → F i = G i) :
    famFold Nat.add 0 F (List.range n)
      = famFold Nat.add 0 G (List.range n) :=
  famFold_congr_members Nat.add 0 F G (List.range n)
    (fun i hi => h i (ltOfMem hi))

/-- A unit indicator's read is its test. -/
theorem ind_one {c : Prop} [Decidable c]
    (h : (if c then (1 : Nat) else 0) = 1) : c := by
  by_cases hc : c
  · exact hc
  · rw [if_neg hc] at h
    exact absurd h (Nat.noConfusion)

/-- The key-range fold collapses onto one key below the count, the
family reading the sum's unit at every further key. -/
theorem foldB_pickRange (F : Nat → BPair) (i : Nat) (X : BPair)
    (m : Nat) (him : i < m) (hon : (F i).oneValue X)
    (hoff : ∀ k, k < m → ¬ k = i → (F k).oneValue BPair.unit) :
    (famFold BPair.add BPair.unit F (List.range m)).oneValue X :=
  foldB_pick F i X (List.range m) (countOf_range_one him) hon
    (fun x hx hxi => hoff x (ltOfMem hx) hxi)

/-- The key-range fold at a family reading the sum's unit below
the count is that unit. -/
theorem foldB_nullRange (F : Nat → BPair) (m : Nat)
    (hoff : ∀ k, k < m → (F k).oneValue BPair.unit) :
    (famFold BPair.add BPair.unit F (List.range m)).oneValue
      BPair.unit :=
  foldB_null F (List.range m) (fun x hx => hoff x (ltOfMem hx))

/-- A family's rotation at a stated count: the dropped head
rejoined at the tail, the cyclic word's own freedom. -/
def rotAt {α : Type} (k : Nat) (l : List α) : List α :=
  l.drop k ++ l.take k

/-- The rotated list's fold is the list's. -/
theorem any_rotAt {α : Type} (f : α → Bool) (k : Nat) (l : List α) :
    (rotAt k l).any f = l.any f := by
  show (l.drop k ++ l.take k).any f = l.any f
  rw [any_append, Bool.or_comm, ← any_append, List.take_append_drop]

/-- The reversed list's fold is the list's. -/
theorem any_reverse {α : Type} (f : α → Bool) :
    ∀ l : List α, l.reverse.any f = l.any f
  | [] => rfl
  | a :: l => by
    rw [reverse_cons, any_append, any_reverse f l]
    show (l.any f || (f a || false)) = (f a || l.any f)
    rw [Bool.or_false, Bool.or_comm]

/-- The matrix at an entry formula over two stated key ranges: one
row per outer key, the row the inner range's map (`def:elim`'s
occupancy family of entries at row and column keys, total over
stated finite key lists). -/
def matOf {α : Type} (m n : Nat) (f : Nat → Nat → α) :
    List (List α) :=
  (List.range m).map (fun i => (List.range n).map (fun j => f i j))

/-- The row count is the outer range's. -/
theorem matOf_length {α : Type} (m n : Nat) (f : Nat → Nat → α) :
    (matOf m n f).length = m :=
  length_mapRange _ m

/-- A row below the count is its key's inner map. -/
theorem matOf_row {α : Type} (dr : List α) (m n : Nat)
    (f : Nat → Nat → α) (i : Nat) (hi : i < m) :
    ground.getAt dr (matOf m n f) i
      = (List.range n).map (fun j => f i j) := by
  show ground.getAt dr ((List.range m).map
    (fun i => (List.range n).map (fun j => f i j))) i = _
  rw [getAt_map_range dr _ m i, if_pos hi]

/-- A row's width is the inner range's. -/
theorem matOf_rowLength {α : Type} (dr : List α) (m n : Nat)
    (f : Nat → Nat → α) (i : Nat) (hi : i < m) :
    (ground.getAt dr (matOf m n f) i).length = n := by
  rw [matOf_row dr m n f i hi, length_mapRange]

/-- An entry below both counts is the formula's read. -/
theorem matOf_entry {α : Type} (dr : List α) (d0 : α) (m n : Nat)
    (f : Nat → Nat → α) (i j : Nat) (hi : i < m) (hj : j < n) :
    ground.getAt d0 (ground.getAt dr (matOf m n f) i) j
      = f i j := by
  rw [matOf_row dr m n f i hi, getAt_map_range d0 _ n j, if_pos hj]

/-- The entry-formula matrix through an entrywise map is the matrix
at the mapped formula. -/
theorem matOf_map {α β : Type} (m n : Nat) (f : Nat → Nat → α) (g : α → β) :
    (matOf m n f).map (fun r => r.map g) = matOf m n (fun i j => g (f i j)) := by
  show ((List.range m).map (fun i => (List.range n).map (fun j => f i j))).map
      (fun r => r.map g)
    = (List.range m).map (fun i => (List.range n).map (fun j => g (f i j)))
  rw [map_map]
  exact map_congr_all _ _ (fun i => map_map (fun j => f i j) g (List.range n))
    (List.range m)

/-- Two formulas at one read per key pair below the counts build
one matrix. -/
theorem matOf_congr {α : Type} (m n : Nat) (f g : Nat → Nat → α)
    (h : ∀ i j : Nat, i < m → j < n → f i j = g i j) :
    matOf m n f = matOf m n g := by
  refine map_congr_members _ _ (List.range m) (fun i hi => ?_)
  rw [countOf_range i m] at hi
  by_cases him : i < m
  · refine map_congr_members _ _ (List.range n) (fun j hj => ?_)
    rw [countOf_range j n] at hj
    by_cases hjn : j < n
    · exact h i j him hjn
    · rw [if_neg hjn] at hj
      exact absurd hj (Nat.lt_irrefl 0)
  · rw [if_neg him] at hi
    exact absurd hi (Nat.lt_irrefl 0)

/-- The below-count as the entry indicator's fold over the key
range. -/
theorem countBelow_index (a : Nat) : ∀ t : List Nat,
    countBelow a t = famFold Nat.add 0
      (fun k => if getAt 0 t k < a then (1 : Nat) else 0)
      (List.range t.length)
  | [] => rfl
  | b :: t => by
    rw [countBelow_cons]
    show (if b < a then (1 : Nat) else 0) + countBelow a t
      = famFold Nat.add 0
        (fun k => if getAt 0 (b :: t) k < a
          then (1 : Nat) else 0)
        (List.range (t.length + 1))
    rw [range_cons t.length]
    show (if b < a then (1 : Nat) else 0) + countBelow a t
      = Nat.add (if b < a then (1 : Nat) else 0)
        (famFold Nat.add 0
          (fun k => if getAt 0 (b :: t) k < a
            then (1 : Nat) else 0)
          ((List.range t.length).map (fun j => j + 1)))
    rw [famFold_map Nat.add 0
      (fun k => if getAt 0 (b :: t) k < a
        then (1 : Nat) else 0)
      (fun j => j + 1) (List.range t.length)]
    show (if b < a then (1 : Nat) else 0) + countBelow a t
      = (if b < a then (1 : Nat) else 0)
        + famFold Nat.add 0
          (fun k => if getAt 0 t k < a
            then (1 : Nat) else 0)
          (List.range t.length)
    rw [countBelow_index a t]

/-- The below-count collects the member counts over the values'
range. -/
theorem countBelow_sum : ∀ (a : Nat) (l : List Nat),
    countBelow a l
      = famFold Nat.add 0 (fun x => countOf x l) (List.range a)
  | a, [] => by
    exact (famFold_zero
      (fun x => countOf x ([] : List Nat))
      (fun _ => rfl) (List.range a)).symm
  | a, b :: t => by
    rw [countBelow_cons,
      famFold_congr_all Nat.add 0
      (fun x => countOf x (b :: t))
      (fun x => (if x = b then 1 else 0) + countOf x t)
      (fun x => countOf_cons x b t) (List.range a),
      famFold_add_split, countBelow_sum a t,
      famFold_congr_all Nat.add 0
        (fun x => if x = b then 1 else 0)
        (fun x => if b = x then 1 else 0)
        (fun x => by
          by_cases hxb : x = b
          · rw [if_pos hxb, if_pos hxb.symm]
          · rw [if_neg hxb, if_neg (fun h => hxb h.symm)])
        (List.range a),
      ← countOf_fold b (List.range a),
      countOf_range b a]

/-- The entries' counts read through the move, the two places
exchanged. -/
theorem countOf_adjSwap (x : Nat) : ∀ (k : Nat) (m : List Nat),
    ground.countOf x (adjSwap k m) = ground.countOf x m
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, a :: b :: t => by
    show ground.countOf x (b :: a :: t) = ground.countOf x (a :: b :: t)
    rw [countOf_cons x b (a :: t), countOf_cons x a t,
      countOf_cons x a (b :: t), countOf_cons x b t,
      ← Nat.add_assoc, ← Nat.add_assoc,
      Nat.add_comm (if x = b then 1 else 0) (if x = a then 1 else 0)]
  | k + 1, a :: t => by
    show ground.countOf x (a :: adjSwap k t) = ground.countOf x (a :: t)
    rw [countOf_cons, countOf_cons, countOf_adjSwap x k t]

/-- At a distinct family two places read distinct entries. -/
theorem getAt_ne_of_distinct {m : List Nat}
    (hdist : ∀ x, ground.countOf x m ≤ 1) {i j : Nat} (hij : i < j)
    (hj : j < m.length) :
    ground.getAt 0 m i ≠ ground.getAt 0 m j :=
  fun he =>
    absurd (Nat.le_trans (countOf_two_pos 0 m i j
      (Nat.lt_trans hij hj) hj (Nat.ne_of_lt hij) he)
      (hdist _)) (Nat.not_succ_le_self 1)

/-- A family at the vacant total is vacant at every key. -/
theorem getAt_zero_of_sum : ∀ (mu : List Nat),
    sumNat mu = 0 → ∀ i, ground.getAt 0 mu i = 0
  | [], _, _ => rfl
  | n :: t, h, i => by
    have hn : n = 0 := Nat.eq_zero_of_add_eq_zero_right h
    have ht : sumNat t = 0 := Nat.eq_zero_of_add_eq_zero_left h
    match i with
    | 0 => exact hn
    | i + 1 => exact getAt_zero_of_sum t ht i

/-- A family vacant at every key is its length's vacant list. -/
theorem replicate_of_zeros (l : List Nat)
    (h : ∀ p, p < l.length → ground.getAt 0 l p = 0) :
    l = List.replicate l.length 0 :=
  ground.getAt_ext 0 l (List.replicate l.length 0)
    (by rw [ground.length_replicate])
    (fun p hp => by rw [h p hp, ground.getAt_replicate_zero])

/-- An unoccupied family is its length's vacant list. -/
theorem replicate_of_sum_zero (nu : List Nat)
    (h : sumNat nu = 0) : nu = List.replicate nu.length 0 :=
  replicate_of_zeros nu (fun p _ => getAt_zero_of_sum nu h p)

/-- The unit assignment's action reads the list back, the entry
map over the key list. -/
theorem range_map_getAt {γ : Type} (dflt : γ) (d : Nat) (q : List γ)
    (hq : q.length = d) :
    (List.range d).map (ground.getAt dflt q) = q := by
  refine ground.getAt_ext dflt _ _
    (by rw [length_mapRange, hq]) ?_
  intro i hi
  rw [length_mapRange] at hi
  rw [ground.getAt_map 0 dflt _ (List.range d) i
      (by rw [length_range]; exact hi),
    getAt_range d i hi]

/-- The prefix products of a family from a seed, one per key, the
key's read the product of the members before it. -/
def prefixProds {α : Type} (mul : α → α → α) : List α → α → List α
  | [], _ => []
  | a :: t, acc => acc :: prefixProds mul t (mul acc a)

/-- The suffix products of a family to a seed, one per key, the
key's read the product of the members after it, beside the whole
product. -/
def suffixProds {α : Type} (mul : α → α → α) (one : α) : List α → List α × α
  | [] => ([], one)
  | a :: t =>
    let r := suffixProds mul one t
    (r.2 :: r.1, mul a r.2)

/-- The products of every member but one from a seed, one per key,
the key's prefix product against its suffix product, every key's
read at one pass over the family. -/
def othersFrom {α : Type} (mul : α → α → α) (one : α) (l : List α) (acc : α) : List α :=
  List.zipWith mul (prefixProds mul l acc) (suffixProds mul one l).1

/-- The products of every member but one, one per key: the skipping
product at every key at once (`getAt_othersAll`). -/
def othersAll {α : Type} (mul : α → α → α) (one : α) (l : List α) : List α :=
  othersFrom mul one l one

/-- The prefix products read the family's count. -/
theorem length_prefixProds {α : Type} (mul : α → α → α) :
    ∀ (l : List α) (acc : α), (prefixProds mul l acc).length = l.length
  | [], _ => rfl
  | a :: t, acc => by
    show (prefixProds mul t (mul acc a)).length + 1 = t.length + 1
    rw [length_prefixProds mul t]

/-- The suffix products read the family's count. -/
theorem length_suffixProds {α : Type} (mul : α → α → α) (one : α) :
    ∀ l : List α, (suffixProds mul one l).1.length = l.length
  | [] => rfl
  | a :: t => by
    show (suffixProds mul one t).1.length + 1 = t.length + 1
    rw [length_suffixProds mul one t]

/-- The products of every member but one read the family's count. -/
theorem length_othersAll {α : Type} (mul : α → α → α) (one : α) (l : List α) :
    (othersAll mul one l).length = l.length :=
  length_zipWith mul _ _ l.length (length_prefixProds mul l one) (length_suffixProds mul one l)

/-- The whole suffix product joined to a seed is the accumulating
product from the seed, at the product's regrouping with its unit. -/
theorem suffixProds_whole {γ : Type} {mul : γ → γ → γ} {one : γ} {ov : γ → γ → Prop}
    (L : FoldLaws γ mul one ov) :
    ∀ (l : List γ) (acc : γ), ov (mul acc (suffixProds mul one l).2) (l.foldl mul acc)
  | [], acc => L.opUnit acc
  | a :: t, acc => by
    show ov (mul acc (mul a (suffixProds mul one t).2)) (t.foldl mul (mul acc a))
    exact L.ovTrans (L.ovSymm (L.opAssoc acc a _)) (suffixProds_whole L t (mul acc a))

/-- The key's read of the products of every member but one from a
seed is the skipping product over the keys from the seed. -/
theorem getAt_othersFrom {γ : Type} {mul : γ → γ → γ} {one : γ} {ov : γ → γ → Prop}
    (L : FoldLaws γ mul one ov) (d : γ) :
    ∀ (l : List γ) (acc : γ) (i : Nat), i < l.length →
      ov (getAt d (othersFrom mul one l acc) i)
        ((List.range l.length).foldl
          (fun a j => if j = i then a else mul a (getAt d l j)) acc)
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a :: t, acc, 0, _ => by
    have h := foldl_map (getAt d t) mul (List.range t.length) acc
    rw [range_map_getAt d t.length t rfl] at h
    show ov (mul acc (suffixProds mul one t).2)
      ((List.range (t.length + 1)).foldl
        (fun a' j => if j = 0 then a' else mul a' (getAt d (a :: t) j)) acc)
    rw [range_cons]
    show ov (mul acc (suffixProds mul one t).2)
      (((List.range t.length).map (fun j => j + 1)).foldl
        (fun a' j => if j = 0 then a' else mul a' (getAt d (a :: t) j))
        (if 0 = 0 then acc else mul acc a))
    rw [foldl_map, if_pos rfl,
      foldl_congr (fun a' u => if u + 1 = 0 then a' else mul a' (getAt d (a :: t) (u + 1)))
        (fun a' u => mul a' (getAt d t u)) (fun a' u => by
          show (if u + 1 = 0 then a' else mul a' (getAt d t u)) = mul a' (getAt d t u)
          rw [if_neg (fun hh : u + 1 = 0 => Nat.noConfusion hh)]) (List.range t.length) acc,
      ← h]
    exact suffixProds_whole L t acc
  | a :: t, acc, i + 1, hi => by
    have ih := getAt_othersFrom L d t (mul acc a) i (Nat.lt_of_succ_lt_succ hi)
    show ov (getAt d (othersFrom mul one t (mul acc a)) i)
      ((List.range (t.length + 1)).foldl
        (fun a' j => if j = i + 1 then a' else mul a' (getAt d (a :: t) j)) acc)
    rw [range_cons]
    show ov (getAt d (othersFrom mul one t (mul acc a)) i)
      (((List.range t.length).map (fun j => j + 1)).foldl
        (fun a' j => if j = i + 1 then a' else mul a' (getAt d (a :: t) j))
        (if 0 = i + 1 then acc else mul acc a))
    rw [foldl_map, if_neg (fun hh : 0 = i + 1 => Nat.noConfusion hh),
      foldl_congr (fun a' u => if u + 1 = i + 1 then a' else mul a' (getAt d (a :: t) (u + 1)))
        (fun a' u => if u = i then a' else mul a' (getAt d t u)) (fun a' u => by
          show (if u + 1 = i + 1 then a' else mul a' (getAt d t u))
            = (if u = i then a' else mul a' (getAt d t u))
          by_cases hu : u = i
          · have hc : u + 1 = i + 1 := by rw [hu]
            rw [if_pos hc, if_pos hu]
          · rw [if_neg (fun he => hu (Nat.succ.inj he)), if_neg hu])
        (List.range t.length) (mul acc a)]
    exact ih

/-- The key's read of the products of every member but one is the
skipping product over the keys from the unit. -/
theorem getAt_othersAll {γ : Type} {mul : γ → γ → γ} {one : γ} {ov : γ → γ → Prop}
    (L : FoldLaws γ mul one ov) (d : γ) (l : List γ) (i : Nat) (hi : i < l.length) :
    ov (getAt d (othersAll mul one l) i)
      ((List.range l.length).foldl (fun a j => if j = i then a else mul a (getAt d l j)) one) :=
  getAt_othersFrom L d l one i hi

/-- A fold over a list reads as the fold over its key range at the
entry map, the unit assignment's own bridge. -/
theorem famFold_getAt {α β : Type} (add : β → β → β) (unit : β)
    (F : α → β) (d : α) (l : List α) (n : Nat) (h : l.length = n) :
    ground.famFold add unit (fun k => F (ground.getAt d l k))
      (List.range n)
      = ground.famFold add unit F l := by
  refine Eq.trans (ground.famFold_map add unit F (ground.getAt d l)
    (List.range n)).symm ?_
  exact congrArg (ground.famFold add unit F) (range_map_getAt d n l h)

theorem sumMap (f : Nat → Nat) (z : List Nat) :
    sumNat (z.map f) = ground.famFold Nat.add 0 f z :=
  famFold_map Nat.add 0 (fun x => x) f z

/-- Two range folds of pointwise equal members read one count. -/
theorem sumNat_congr_range (f g : Nat → Nat) (n : Nat)
    (h : ∀ j, j < n → f j = g j) :
    sumNat ((List.range n).map f) = sumNat ((List.range n).map g) := by
  rw [sumMap, sumMap]
  exact famFold_congr_members Nat.add 0 f g (List.range n)
    (fun j hc => h j (ltOfCountRange hc))

/-- A key range splits at a stated place, the upper keys the second
range's own shift. -/
theorem range_split (a : Nat) : ∀ b : Nat,
    List.range (a + b)
      = List.range a ++ (List.range b).map (fun c => a + c)
  | 0 => (ground.append_nil (List.range a)).symm
  | b + 1 => by
    show List.range (a + b + 1) = _
    rw [range_succ (a + b), range_split a b, range_succ b,
      ground.map_append, ground.append_assoc]
    rfl

/-- A constant product over a joined key range splits at the
seam. -/
theorem prodConst_split (c a b : Nat) :
    prodOver (fun _ => c) (List.range (a + b))
      = prodOver (fun _ => c) (List.range a)
        * prodOver (fun _ => c) (List.range b) := by
  show famFold Nat.mul 1 (fun _ => c) (List.range (a + b)) = _
  rw [range_split a b,
    famFold_append Nat.mul 1 mulAssoc Nat.one_mul (fun _ => c)
      (List.range a) ((List.range b).map (fun k => a + k))]
  show prodOver (fun _ => c) (List.range a)
      * prodOver (fun _ => c) ((List.range b).map (fun k => a + k))
    = _
  rw [prodOver_const c ((List.range b).map (fun k => a + k))
    (List.range b) (length_map _ _)]

/-- The guarded family above a letter is the count's unit below
that letter's own key. -/
private theorem zeroAbove (a c : Nat) : ∀ m : Nat, m ≤ a →
    ground.famFold Nat.add 0
      (fun b => if a < b then c else 0) (List.range m) = 0
  | 0, _ => rfl
  | m + 1, h => by
    rw [ground.range_succ m,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun b => if a < b then c else 0) (List.range m) [m],
      zeroAbove a c m (Nat.le_of_succ_le h)]
    show Nat.add 0 (Nat.add (if a < m then c else 0) 0) = 0
    rw [if_neg (fun hlt => Nat.lt_irrefl a (Nat.lt_trans hlt h))]

/-- The guarded family above a letter folds to the run beyond it,
one count per key past the letter. -/
theorem aboveRun (a c : Nat) : ∀ g : Nat,
    ground.famFold Nat.add 0 (fun b => if a < b then c else 0)
      (List.range (a + 1 + g)) = c * g
  | 0 => by
    show ground.famFold Nat.add 0 (fun b => if a < b then c else 0)
      (List.range (a + 1)) = 0
    rw [ground.range_succ a,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun b => if a < b then c else 0) (List.range a) [a],
      zeroAbove a c a (Nat.le_refl a)]
    show Nat.add 0 (Nat.add (if a < a then c else 0) 0) = 0
    rw [if_neg (Nat.lt_irrefl a)]
  | g + 1 => by
    show ground.famFold Nat.add 0 (fun b => if a < b then c else 0)
      (List.range (a + 1 + g + 1)) = c * (g + 1)
    rw [ground.range_succ (a + 1 + g),
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun b => if a < b then c else 0) (List.range (a + 1 + g))
        [a + 1 + g],
      aboveRun a c g]
    show Nat.add (c * g)
      (Nat.add (if a < a + 1 + g then c else 0) 0) = c * (g + 1)
    rw [if_pos (show a < a + 1 + g from
      Nat.lt_of_lt_of_le (Nat.lt_succ_self a)
        (Nat.le_add_right (a + 1) g))]
    rfl

theorem endSplit (F : Nat → Nat) :
    ∀ m : Nat, ground.famFold Nat.add 0 F (List.range (m + 1))
      = ground.famFold Nat.add 0 F (List.range m) + F m
  | 0 => by
    rw [range_cons 0]
    show F 0 + 0 = 0 + F 0
    rw [Nat.add_comm (F 0) 0]
  | m + 1 => by
    rw [range_cons (m + 1)]
    show F 0 + ground.famFold Nat.add 0 F
        ((List.range (m + 1)).map (fun j => j + 1))
      = ground.famFold Nat.add 0 F (List.range (m + 1)) + F (m + 1)
    have hm : ground.famFold Nat.add 0 F
        ((List.range (m + 1)).map (fun j => j + 1))
      = ground.famFold Nat.add 0 (fun j => F (j + 1))
        (List.range (m + 1)) :=
      ground.famFold_map Nat.add 0 _ _ _
    rw [hm, endSplit (fun j => F (j + 1)) m, range_cons m]
    show F 0 + (ground.famFold Nat.add 0 (fun j => F (j + 1))
        (List.range m) + F (m + 1))
      = (F 0 + ground.famFold Nat.add 0 F
          ((List.range m).map (fun j => j + 1))) + F (m + 1)
    have hm2 : ground.famFold Nat.add 0 F
        ((List.range m).map (fun j => j + 1))
      = ground.famFold Nat.add 0 (fun j => F (j + 1))
        (List.range m) :=
      ground.famFold_map Nat.add 0 _ _ _
    rw [hm2, ← Nat.add_assoc (F 0)
      (ground.famFold Nat.add 0 (fun j => F (j + 1))
        (List.range m)) (F (m + 1))]

theorem foldExtend (F : Nat → Nat) :
    ∀ (g n : Nat), (∀ l, n ≤ l → F l = 0) →
      ground.famFold Nat.add 0 F (List.range (n + g))
        = ground.famFold Nat.add 0 F (List.range n)
  | 0, _, _ => rfl
  | g + 1, n, h => by
    show ground.famFold Nat.add 0 F (List.range (n + g + 1)) = _
    rw [endSplit F (n + g), h (n + g) (Nat.le_add_right n g),
      foldExtend F g n h]
    rfl

theorem foldExtend' (F : Nat → Nat) (n L : Nat)
    (hnL : n ≤ L) (h0 : ∀ l, n ≤ l → F l = 0) :
    ground.famFold Nat.add 0 F (List.range L)
      = ground.famFold Nat.add 0 F (List.range n) := by
  have hg : n + (L - n) = L := ground.natAddSubCancel hnL
  rw [← hg]
  exact foldExtend F (L - n) n h0

/-- The family fold over a key range splits at the nought key: the
head read joined to the shifted family's fold over the remaining
keys, at any carrier sum. -/
theorem famFold_range_cons {β : Type} (add : β → β → β) (unit : β)
    (F : Nat → β) (m : Nat) :
    ground.famFold add unit F (List.range (m + 1))
      = add (F 0) (ground.famFold add unit
          (fun j => F (j + 1)) (List.range m)) := by
  rw [ground.range_cons m]
  exact congrArg (fun z => add (F 0) z)
    (ground.famFold_map add unit F (fun j => j + 1) (List.range m))

/-- The balance instance at the pair sum. -/
theorem foldB_range_cons (F : Nat → BPair) (m : Nat) :
    ground.famFold BPair.add BPair.unit F (List.range (m + 1))
      = F 0 + ground.famFold BPair.add BPair.unit
          (fun j => F (j + 1)) (List.range m) :=
  famFold_range_cons BPair.add BPair.unit F m

/-- The count instance at the natural sum. -/
theorem sumNat_range_cons (f : Nat → Nat) (m : Nat) :
    sumNat ((List.range (m + 1)).map f)
      = f 0 + sumNat ((List.range m).map (fun j => f (j + 1))) := by
  rw [sumMap, sumMap]
  exact famFold_range_cons Nat.add 0 f m

/-- The balance fold over a key range at its top key: the shorter
range's fold joined to the top key's read. -/
theorem foldB_range_snoc (U : Nat → BPair) (m : Nat) :
    (ground.famFold BPair.add BPair.unit U (List.range (m + 1))).oneValue
      (ground.famFold BPair.add BPair.unit U (List.range m) + U m) := by
  rw [ground.range_succ m]
  refine BPair.oneValue_trans
    (ground.famFold_append_ov ground.bpairFoldLaws U (List.range m) [m]) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit (U m))

/-- A family reading the sum's unit at every key at or beyond a
count leaves its range fold at that count's own range. -/
theorem famFold_range_ext (F : Nat → BPair) (N : Nat)
    (hoff : ∀ j, N ≤ j → (F j).oneValue BPair.unit) : ∀ g : Nat,
    (famFold BPair.add BPair.unit F (List.range (N + g))).oneValue
      (famFold BPair.add BPair.unit F (List.range N))
  | 0 => BPair.oneValue_refl _
  | g + 1 =>
    BPair.oneValue_trans (foldB_range_snoc F (N + g))
      (BPair.oneValue_trans
        (BPair.add_congr (famFold_range_ext F N hoff g)
          (hoff (N + g) (Nat.le_add_right N g)))
        (BPair.add_unit _))

/-- The extension at two stated counts: a family vacant at or
beyond the lower count folds one value over the two ranges. -/
theorem foldRange_le (F : Nat → BPair) (N n : Nat) (hNn : N ≤ n)
    (hoff : ∀ j, N ≤ j → (F j).oneValue BPair.unit) :
    (famFold BPair.add BPair.unit F (List.range n)).oneValue
      (famFold BPair.add BPair.unit F (List.range N)) := by
  obtain ⟨g, hg⟩ := Nat.le.dest hNn
  rw [← hg]
  exact famFold_range_ext F N hoff g

/-- A further first member inside a scaled product of two powers
raises the first power's key. -/
private theorem armFst (c x y : BPair) (t u : Nat) :
    (x * (c * (bpow x t * bpow y u))).oneValue
      (c * (bpow x (t + 1) * bpow y u)) := by
  rw [BPair.mul_left_comm x c (bpow x t * bpow y u),
    ← BPair.mul_assoc x (bpow x t) (bpow y u)]
  exact BPair.mul_congr (BPair.oneValue_refl c)
    (BPair.mul_congr_left
      (BPair.oneValue_symm (BPair.norm_oneValue (x * bpow x t))))

/-- A further second member inside a scaled product of two powers
raises the second power's key. -/
private theorem armSnd (c x y : BPair) (t u : Nat) :
    (y * (c * (bpow x t * bpow y u))).oneValue
      (c * (bpow x t * bpow y (u + 1))) := by
  rw [BPair.mul_left_comm y c (bpow x t * bpow y u),
    BPair.mul_left_comm y (bpow x t) (bpow y u)]
  exact BPair.mul_congr (BPair.oneValue_refl c)
    (BPair.mul_congr (BPair.oneValue_refl (bpow x t))
      (BPair.oneValue_symm (BPair.norm_oneValue (y * bpow y u))))

/-- The binomial theorem at the pair carrier: a sum's power reads
the fold over the keys below the power's own successor of the
Pascal count against the two members' complementary powers. -/
theorem bpow_binom (x y : BPair) : ∀ j : Nat,
    (bpow (x + y) j).oneValue
      (bsum (fun t => BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t))) (List.range (j + 1)))
  | 0 => rfl
  | j + 1 => by
    have hIH := bpow_binom x y j
    have hx : (bsum (fun t => x * (BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t)))) (List.range (j + 1))).oneValue
        (x * bsum (fun t => BPair.ofNat (pasc j t)
          * (bpow x t * bpow y (j - t))) (List.range (j + 1))) :=
      foldB_mul_left x (fun t => BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t))) (List.range (j + 1))
    have hy : (bsum (fun t => y * (BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t)))) (List.range (j + 1))).oneValue
        (y * bsum (fun t => BPair.ofNat (pasc j t)
          * (bpow x t * bpow y (j - t))) (List.range (j + 1))) :=
      foldB_mul_left y (fun t => BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t))) (List.range (j + 1))
    have hxs : (bsum (fun t => x * (BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t)))) (List.range (j + 1))).oneValue
        (bsum (fun t => BPair.ofNat (pasc j t)
          * (bpow x (t + 1) * bpow y (j - t))) (List.range (j + 1))) :=
      foldB_congr_members _ _ (List.range (j + 1))
        (fun t _ => armFst (BPair.ofNat (pasc j t)) x y t (j - t))
    have hys : (bsum (fun t => y * (BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t)))) (List.range (j + 1))).oneValue
        (bsum (fun t => BPair.ofNat (pasc j t)
          * (bpow x t * bpow y (j - t + 1))) (List.range (j + 1))) :=
      foldB_congr_members _ _ (List.range (j + 1))
        (fun t _ => armSnd (BPair.ofNat (pasc j t)) x y t (j - t))
    have hdrop : (bsum (fun t => BPair.ofNat (pasc j (t + 1))
        * (bpow x (t + 1) * bpow y (j - t))) (List.range (j + 1))).oneValue
        (bsum (fun t => BPair.ofNat (pasc j (t + 1))
          * (bpow x (t + 1) * bpow y (j - t))) (List.range j)) := by
      refine BPair.oneValue_trans (foldB_range_snoc _ j)
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _) ?_) (BPair.add_unit _))
      rw [pasc_beyond j (j + 1) (Nat.lt_succ_self j)]
      exact BPair.unit_mul _
    have hmatch : (bsum (fun t => BPair.ofNat (pasc j (t + 1))
        * (bpow x (t + 1) * bpow y (j - t))) (List.range j)).oneValue
        (bsum (fun t => BPair.ofNat (pasc j (t + 1))
          * (bpow x (t + 1) * bpow y (j - (t + 1) + 1))) (List.range j)) := by
      refine foldB_congr_members _ _ (List.range j) ?_
      intro s hs
      rw [subSuccAdd (ltOfMem hs)]
      exact BPair.oneValue_refl _
    have h0 : BPair.ofNat (pasc j 0) * (bpow x 0 * bpow y (j - 0 + 1))
        = BPair.ofNat (pasc (j + 1) 0) * (bpow x 0 * bpow y (j + 1 - 0)) := by
      rw [pascBase j, pascBase (j + 1), Nat.sub_zero j, Nat.sub_zero (j + 1)]
    have hYS : (bsum (fun t => BPair.ofNat (pasc j t)
        * (bpow x t * bpow y (j - t + 1))) (List.range (j + 1))).oneValue
        (BPair.ofNat (pasc (j + 1) 0) * (bpow x 0 * bpow y (j + 1 - 0))
          + bsum (fun t => BPair.ofNat (pasc j (t + 1))
              * (bpow x (t + 1) * bpow y (j - t))) (List.range (j + 1))) := by
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (foldB_range_cons _ j)) ?_
      rw [h0]
      exact BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.oneValue_trans hdrop hmatch))
    have hfold2 : (bsum (fun t => BPair.ofNat (pasc (j + 1) (t + 1))
        * (bpow x (t + 1) * bpow y (j + 1 - (t + 1))))
          (List.range (j + 1))).oneValue
        (bsum (fun t => BPair.ofNat (pasc j t)
            * (bpow x (t + 1) * bpow y (j - t))) (List.range (j + 1))
          + bsum (fun t => BPair.ofNat (pasc j (t + 1))
              * (bpow x (t + 1) * bpow y (j - t))) (List.range (j + 1))) := by
      refine BPair.oneValue_trans
        (foldB_congr_members _ (fun t =>
            BPair.ofNat (pasc j t) * (bpow x (t + 1) * bpow y (j - t))
            + BPair.ofNat (pasc j (t + 1)) * (bpow x (t + 1) * bpow y (j - t)))
          (List.range (j + 1)) ?_)
        (foldB_add
          (fun t => BPair.ofNat (pasc j t) * (bpow x (t + 1) * bpow y (j - t)))
          (fun t => BPair.ofNat (pasc j (t + 1))
            * (bpow x (t + 1) * bpow y (j - t))) (List.range (j + 1)))
      intro t _
      rw [pascStep j t, Nat.succ_sub_succ j t]
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofNat_add (pasc j t) (pasc j (t + 1)))) ?_
      exact BPair.oneValue_of_eq (BPair.right_distrib _ _ _)
    refine BPair.oneValue_trans
      (BPair.norm_oneValue ((x + y) * bpow (x + y) j)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (x + y)) hIH) ?_
    rw [BPair.right_distrib]
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.oneValue_symm hx) hxs)
        (BPair.oneValue_trans (BPair.oneValue_symm hy) hys))
      (BPair.oneValue_symm ?_)
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (foldB_range_cons _ (j + 1))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hfold2) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hYS) ?_)
    exact BPair.oneValue_of_eq (BPair.add_left_comm _ _ _)

/-- The balance fold over a key range at its top key: the shorter
range's fold joined to the top key's read. -/
theorem foldB_range_top : ∀ (F : Nat → BPair) (n : Nat),
    (bsum F (List.range (n + 1))).oneValue (bsum F (List.range n) + F n)
  | F, 0 => by
    show (ground.famFold BPair.add BPair.unit F (List.range (0 + 1))).oneValue (BPair.unit + F 0)
    rw [foldB_range_cons F 0]
    show (F 0 + BPair.unit).oneValue (BPair.unit + F 0)
    rw [BPair.add_comm]; exact BPair.oneValue_refl _
  | F, n + 1 => by
    have hIH := foldB_range_top (fun j => F (j + 1)) n
    show (ground.famFold BPair.add BPair.unit F (List.range (n + 1 + 1))).oneValue
      (ground.famFold BPair.add BPair.unit F (List.range (n + 1)) + F (n + 1))
    rw [foldB_range_cons F (n + 1), foldB_range_cons F n]
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl (F 0)) hIH) ?_
    rw [BPair.add_assoc]; exact BPair.oneValue_refl _

/-- The telescope at a pair summing to one with its partner: the
partner's power joined to the pair's multiple of the partner's
lower powers' fold reads one, `y^i + x Σ_{k<i} y^k ≡ 1` at `x + y ≡ 1`. -/
theorem bpow_telescope (x y : BPair) (h : (x + y).oneValue (BPair.ofPos .one)) :
    ∀ i : Nat, (bpow y i + x * bsum (bpow y) (List.range i)).oneValue (BPair.ofPos .one)
  | 0 => by
    show (BPair.ofPos .one + x * BPair.unit).oneValue (BPair.ofPos .one)
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_unit x)) (BPair.add_unit _)
  | i + 1 => by
    have hIH := bpow_telescope x y h i
    -- the fold at the head: Σ_{k<i+1} y^k = y^0 + Σ_{k<i} y^{k+1}
    have hcons : bsum (bpow y) (List.range (i + 1))
        = bpow y 0 + bsum (fun k => bpow y (k + 1)) (List.range i) :=
      foldB_range_cons (bpow y) i
    have hshift : (bsum (fun k => bpow y (k + 1)) (List.range i)).oneValue
        (y * bsum (bpow y) (List.range i)) := by
      refine BPair.oneValue_trans (famFold_congr_members_ov BPair.oneValue BPair.add
        BPair.unit BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2)
        _ (fun k => y * bpow y k) (List.range i) (fun k _ => bpow_succ_read y k)) ?_
      exact foldB_mul_left y (bpow y) (List.range i)
    show (bpow y (i + 1) + x * bsum (bpow y) (List.range (i + 1))).oneValue (BPair.ofPos .one)
    rw [hcons]
    refine BPair.oneValue_trans (BPair.add_congr (bpow_succ_read y i)
      (BPair.mul_congr (BPair.oneValue_refl x)
        (BPair.add_congr (BPair.oneValue_refl _) hshift))) ?_
    -- y y^i + x (1 + y Σ) ≡ x + y (y^i + x Σ) ≡ x + y ≡ 1
    have h1 : (y * bpow y i + x * (bpow y 0 + y * bsum (bpow y) (List.range i))).oneValue
        (x + y * (bpow y i + x * bsum (bpow y) (List.range i))) := by
      show (y * bpow y i + x * (BPair.ofPos .one + y * bsum (bpow y) (List.range i))).oneValue _
      rw [BPair.left_distrib, BPair.left_distrib]
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.mul_one_read x) (BPair.oneValue_refl _))) ?_
      rw [← BPair.mul_assoc x y, BPair.mul_comm x y, BPair.mul_assoc y x]
      rw [← BPair.add_assoc, BPair.add_comm (y * bpow y i) x, BPair.add_assoc]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans h1 ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl x)
      (BPair.mul_congr (BPair.oneValue_refl y) hIH)) ?_
    exact BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl x) (BPair.mul_one_read y)) h

/-- The unit family's fold over a key range reads the count. -/
theorem bsum_one : ∀ n : Nat,
    (bsum (fun _ : Nat => BPair.ofPos .one) (List.range n)).oneValue (BPair.ofNat n)
  | 0 => BPair.oneValue_refl _
  | n + 1 => by
    refine BPair.oneValue_trans (foldB_range_top (fun _ => BPair.ofPos .one) n) ?_
    refine BPair.oneValue_trans (BPair.add_congr (bsum_one n) (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_symm (BPair.ofNat_succ n)

/-- The telescope folded: the partner's powers' fold joined to the
pair's multiple of the lower folds' fold reads the count,
`Σ_{i<n} y^i + x Σ_{i<n} Σ_{k<i} y^k ≡ n`. -/
theorem bpow_telescope_fold (x y : BPair) (h : (x + y).oneValue (BPair.ofPos .one))
    (n : Nat) :
    (bsum (bpow y) (List.range n)
      + x * bsum (fun i => bsum (bpow y) (List.range i)) (List.range n)).oneValue
      (BPair.ofNat n) := by
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (foldB_mul_left x _ (List.range n)))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (famFold_add_ov bpairFoldLaws (bpow y) (fun i => x * bsum (bpow y) (List.range i))
      (List.range n))) ?_
  refine BPair.oneValue_trans (famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
    BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) _ (fun _ => BPair.ofPos .one)
    (List.range n) (fun i _ => bpow_telescope x y h i)) ?_
  exact bsum_one n

/-- Bernoulli's read at the telescope: the partner's power joined to
the key's multiple of the pair reads one joined to the pair's square
against the lower folds' fold, `y^n + n x ≡ 1 + x² Σ_{i<n} Σ_{k<i} y^k`. -/
theorem bpow_bernoulli (x y : BPair) (h : (x + y).oneValue (BPair.ofPos .one)) (n : Nat) :
    (bpow y n + BPair.ofNat n * x).oneValue
      (BPair.ofPos .one + x * x * bsum (fun i => bsum (bpow y) (List.range i)) (List.range n)) := by
  have hS := bpow_telescope_fold x y h n
  have hT := bpow_telescope x y h n
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.mul_congr (BPair.oneValue_symm hS) (BPair.oneValue_refl x))) ?_
  rw [BPair.right_distrib, ← BPair.add_assoc, BPair.mul_comm (bsum (bpow y) (List.range n)) x,
    BPair.mul_assoc x _ x, BPair.mul_comm _ x, ← BPair.mul_assoc x x]
  exact BPair.add_congr hT (BPair.oneValue_refl _)

/-- The Bernstein bound at the binomial partition: at a pair and its
partner summing to one, the key's Pascal count against the pair's
power and the partner's whole power joined to the gap, the
partition's further summands with the key's summand read against
the partner's key power's telescope, reads one. -/
theorem bernstein_bound (x y : BPair) (h : (x + y).oneValue (BPair.ofPos .one)) (j k : Nat) :
    (BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k))
      + bsum (fun t => if t = j
          then BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y k)
            * (x * bsum (bpow y) (List.range j))
          else BPair.ofNat (pasc (j + k) t) * (bpow x t * bpow y (j + k - t)))
        (List.range (j + k + 1))).oneValue (BPair.ofPos .one) := by
  have hbin := bpow_binom x y (j + k)
  have hone : (bpow (x + y) (j + k)).oneValue (BPair.ofPos .one) :=
    BPair.oneValue_trans (bpow_congr h (j + k)) (bpow_one (j + k))
  -- the indicator fold at the key j reads the withdrawn summand
  have hind : (bsum (fun t => if t = j
      then BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k)) else BPair.unit)
      (List.range (j + k + 1))).oneValue
      (BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k))) :=
    famFold_pick_ov bpairFoldLaws _ j _ (List.range (j + k + 1))
      (by rw [countOf_range j (j + k + 1), if_pos (Nat.lt_succ_of_le (Nat.le_add_right j k))])
      (by rw [if_pos rfl]; exact BPair.oneValue_refl _)
      (fun t _ ht => by rw [if_neg ht]; exact BPair.oneValue_refl _)
  -- the partition's fold splits at the key: gap + indicator
  have hsplit : (bsum (fun t => BPair.ofNat (pasc (j + k) t) * (bpow x t * bpow y (j + k - t)))
      (List.range (j + k + 1))).oneValue
      (bsum (fun t => if t = j
          then BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y k)
            * (x * bsum (bpow y) (List.range j))
          else BPair.ofNat (pasc (j + k) t) * (bpow x t * bpow y (j + k - t)))
        (List.range (j + k + 1))
       + bsum (fun t => if t = j
          then BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k)) else BPair.unit)
        (List.range (j + k + 1))) := by
    refine BPair.oneValue_trans ?_ (famFold_add_ov bpairFoldLaws _ _ (List.range (j + k + 1)))
    refine famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit BPair.oneValue_refl
      (fun h1 h2 => BPair.add_congr h1 h2) _ _ (List.range (j + k + 1)) (fun t _ => ?_)
    by_cases ht : t = j
    · rw [if_pos ht, if_pos ht, ht, addSubSelfL]
      -- C x^j y^k (y^j + x Σ) ≡ C x^j y^k x Σ + C x^j y^{j+k}
      have hT := bpow_telescope x y h j
      have hy : (bpow y (j + k)).oneValue (bpow y k * bpow y j) := by
        rw [Nat.add_comm j k]; exact bpow_add y k j
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl (bpow y k)) hT)
            (BPair.mul_one_read _))))) ?_
      rw [BPair.left_distrib (bpow y k), BPair.left_distrib (bpow x j),
        BPair.left_distrib (BPair.ofNat (pasc (j + k) j)), BPair.add_comm]
      refine BPair.add_congr ?_ ?_
      · rw [BPair.mul_assoc (BPair.ofNat (pasc (j + k) j)) (bpow x j * bpow y k),
          BPair.mul_assoc (bpow x j) (bpow y k)]
        exact BPair.oneValue_refl _
      · exact BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hy))
    · rw [if_neg ht, if_neg ht]
      exact BPair.oneValue_symm (BPair.add_unit _)
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_symm hind) (BPair.oneValue_refl _)) ?_
  rw [BPair.add_comm]
  exact BPair.oneValue_trans (BPair.oneValue_symm hsplit) (BPair.oneValue_trans (BPair.oneValue_symm hbin) hone)

/-- The step quotients ascend along a convex chain: at every key whose
raised key sits below the top, the raised key's member against the
top's own lower key sits at or below the key's member against the top,
the convexity step at the key composed with the read one key up and the
shared positive factor withdrawn. -/
theorem quotients_ascend (b : Nat → BPair) (k : Nat)
    (hpos : ∀ i, i < k → BPair.unit < b i)
    (hconv : ∀ i, i + 1 < k → b (i + 1) * b (i + 1) ≤ b i * b (i + 2)) :
    ∀ i, i + 1 < k → b (i + 1) * b (k - 1) ≤ b i * b k := by
  cases k with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k' =>
    show ∀ i, i + 1 < k' + 1 → b (i + 1) * b k' ≤ b i * b (k' + 1)
    have key : ∀ d i, i + 1 + d = k' →
        b (i + 1) * b k' ≤ b i * b (k' + 1) := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have hk : k' = i + 1 := hi.symm
        have hlt : i + 1 < k' + 1 := by rw [hk]; exact Nat.lt_succ_self (i + 1)
        have hc := hconv i hlt
        rw [hk]
        exact hc
      | succ d ih =>
        intro i hi
        have hik : i + 1 ≤ k' := Nat.le.intro hi
        have h2 : i + 1 + 1 + d = k' := by
          rw [Nat.add_right_comm (i + 1) 1 d]
          exact hi
        have hIH : b (i + 2) * b k' ≤ b (i + 1) * b (k' + 1) := ih (i + 1) h2
        have hc := hconv i (Nat.lt_succ_of_le hik)
        have hp1 : BPair.unit < b (i + 1) :=
          hpos (i + 1) (Nat.lt_succ_of_le hik)
        have hp2 : BPair.unit < b (i + 2) :=
          hpos (i + 2) (Nat.lt_succ_of_le (Nat.le.intro h2))
        have hpk : BPair.unit < b k' := hpos k' (Nat.lt_succ_self k')
        have hi0 : BPair.unit < b i :=
          hpos i (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ i) hik))
        have hmul : b (i + 1) * b (i + 1) * (b (i + 2) * b k')
            ≤ b i * b (i + 2) * (b (i + 1) * b (k' + 1)) :=
          leB_mul_mono (unitLeMul (leB_of_lt hp2) (leB_of_lt hpk))
            (unitLeMul (leB_of_lt hi0) (leB_of_lt hp2)) hc hIH
        rw [BPair.mul_mul_mul_comm (b (i + 1)) (b (i + 1)) (b (i + 2)) (b k'),
          BPair.mul_comm (b i) (b (i + 2)),
          BPair.mul_mul_mul_comm (b (i + 2)) (b i) (b (i + 1)) (b (k' + 1)),
          BPair.mul_comm (b (i + 2)) (b (i + 1))] at hmul
        exact leB_unscale_left (unitLtMul hp1 hp2) hmul
    intro i hi
    obtain ⟨d, hd⟩ := Nat.le.dest (Nat.le_of_lt_succ hi)
    exact key d i hd

/-- The chain's power read: at a convex chain of members beyond the
sum's unit whose head sits at or below a stated clearing, the key's
member raised to the raised key sits at or below the clearing's
multiple of the raised key's member raised to the key: the step
quotients ascend to the last (`quotients_ascend`), so the member is
its head against the product of the quotients, each at or below the
last, one quotient folded in per key. -/
theorem chain_power (b : Nat → BPair) (k' : Nat) (Δ : BPair)
    (hb0 : b 0 ≤ Δ)
    (hpos : ∀ i, i ≤ k' + 1 → BPair.unit < b i)
    (hconv : ∀ i, i + 1 ≤ k' → b (i + 1) * b (i + 1) ≤ b i * b (i + 2)) :
    bpow (b k') (k' + 1) ≤ Δ * bpow (b (k' + 1)) k' := by
  have hasc := quotients_ascend b (k' + 1) (fun i hi => hpos i (Nat.le_of_lt hi))
    (fun i hi => hconv i (Nat.le_of_lt_succ hi))
  have hbk : BPair.unit < b (k' + 1) := hpos (k' + 1) (Nat.le_refl _)
  have hbk' : BPair.unit < b k' := hpos k' (Nat.le_succ k')
  have key : ∀ n, n ≤ k' → b n * bpow (b k') n ≤ b 0 * bpow (b (k' + 1)) n := by
    intro n
    induction n with
    | zero => intro _; exact leB_refl _
    | succ n ih =>
      intro hn
      have h1 : b (n + 1) * b k' ≤ b n * b (k' + 1) := hasc n (Nat.lt_succ_of_le hn)
      have hIH := ih (Nat.le_of_succ_le hn)
      have e1 : (b (n + 1) * bpow (b k') (n + 1)).oneValue
          (b (n + 1) * b k' * bpow (b k') n) := by
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (bpow_succ_read _ n)) ?_
        exact BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm
      have e2 : (b 0 * bpow (b (k' + 1)) (n + 1)).oneValue
          (b 0 * (b (k' + 1) * bpow (b (k' + 1)) n)) :=
        BPair.mul_congr (BPair.oneValue_refl _) (bpow_succ_read _ n)
      refine leB_congr (BPair.oneValue_symm e1) (BPair.oneValue_symm e2) ?_
      refine leB_trans (leB_mulL (unitLeBpow (leB_of_lt hbk') n) h1) ?_
      refine leB_congr (BPair.oneValue_of_eq (BPair.mul_left_comm' _ _ _))
        (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) (leB_mulR (leB_of_lt hbk) hIH)
  refine leB_congr_left (BPair.oneValue_symm (bpow_succ_read _ k')) ?_
  refine leB_trans (key k' (Nat.le_refl k')) ?_
  exact leB_mulL (unitLeBpow (leB_of_lt hbk) k') hb0

/-- One summand of the binomial partition: at two data at or beyond the
sum's unit, the partition's Pascal count against the two powers sits at
or below the joined datum's power, the partition's further summands at
or beyond the sum's unit. -/
theorem binom_member (x y : BPair) (j k : Nat) (hx : BPair.unit ≤ x) (hy : BPair.unit ≤ y) :
    BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y k) ≤ bpow (x + y) (j + k) := by
  have hcount : ground.countOf j (List.range (j + k + 1)) = 1 := by
    rw [countOf_range j (j + k + 1),
      if_pos (Nat.lt_succ_of_le (Nat.le_add_right j k))]
  have hpick : (bsum (fun t => if t = j
      then BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k - j))
      else BPair.unit) (List.range (j + k + 1))).oneValue
      (BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k - j))) :=
    famFold_pick_ov bpairFoldLaws _ j _ (List.range (j + k + 1)) hcount
      (by rw [if_pos rfl]; exact BPair.oneValue_refl _)
      (fun t _ ht => by rw [if_neg ht]; exact BPair.oneValue_refl _)
  have hrest : BPair.unit ≤ bsum (fun t => if t = j then BPair.unit
      else BPair.ofNat (pasc (j + k) t) * (bpow x t * bpow y (j + k - t)))
      (List.range (j + k + 1)) := by
    refine foldB_nonneg _ (List.range (j + k + 1)) (fun t _ => ?_)
    by_cases ht : t = j
    · rw [if_pos ht]
      exact leB_refl _
    · rw [if_neg ht]
      exact unitLeMul (unitLeOfNat _)
        (unitLeMul (unitLeBpow hx t) (unitLeBpow hy (j + k - t)))
  have hsplit : (bsum (fun t => BPair.ofNat (pasc (j + k) t)
        * (bpow x t * bpow y (j + k - t))) (List.range (j + k + 1))).oneValue
      (bsum (fun t => if t = j then BPair.unit
          else BPair.ofNat (pasc (j + k) t) * (bpow x t * bpow y (j + k - t)))
        (List.range (j + k + 1))
       + bsum (fun t => if t = j
          then BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k - j))
          else BPair.unit) (List.range (j + k + 1))) := by
    refine BPair.oneValue_trans ?_
      (famFold_add_ov bpairFoldLaws _ _ (List.range (j + k + 1)))
    refine famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
      BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) _ _
      (List.range (j + k + 1)) (fun t _ => ?_)
    by_cases ht : t = j
    · rw [if_pos ht, if_pos ht, ht]
      exact BPair.oneValue_symm (BPair.unit_add _)
    · rw [if_neg ht, if_neg ht]
      exact BPair.oneValue_symm (BPair.add_unit _)
  have hmem : BPair.ofNat (pasc (j + k) j) * (bpow x j * bpow y (j + k - j))
      ≤ bpow (x + y) (j + k) := by
    refine leB_congr_right (BPair.oneValue_symm (bpow_binom x y (j + k))) ?_
    refine leB_congr_right (BPair.oneValue_symm hsplit) ?_
    refine leB_congr_left (BPair.unit_add _) ?_
    exact leB_add hrest (leB_congr_left hpick (leB_refl _))
  rw [addSubSelfL j k] at hmem
  exact hmem

/-- The power's gap read at the raised key: the power joined to the
gap, the pair's square against the two lower folds with the shift's
power, reads one joined to the raised key's power,
`y^k + ((1 + y^∨)² Σ_{i<k} y^i Σ_{i<j'} y^i + y^{j'}) ≡ 1 + y^{k+j'}`,
the telescope at the pair `1 + y^∨` twice with the two withdrawn
powers pairing off against the joined ones. -/
theorem bpow_gap_read (y : BPair) (k j' : Nat) :
    (bpow y k + ((BPair.ofPos .one + y.swap) * (BPair.ofPos .one + y.swap)
        * bsum (bpow y) (List.range k) * bsum (bpow y) (List.range j')
      + bpow y j')).oneValue (BPair.ofPos .one + bpow y (k + j')) := by
  have hx : ((BPair.ofPos .one + y.swap) + y).oneValue (BPair.ofPos .one) :=
    BPair.add_swap_self _ _
  have hT : ∀ i, ((BPair.ofPos .one + y.swap) * bsum (bpow y) (List.range i)).oneValue
      (BPair.ofPos .one + (bpow y i).swap) := by
    intro i
    have h := bpow_telescope (BPair.ofPos .one + y.swap) y hx i
    refine BPair.oneValue_trans ?_ (BPair.add_congr h (BPair.oneValue_refl (bpow y i).swap))
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_right_comm _ _ _)) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.add_swap_null _) (BPair.oneValue_refl _)) ?_
    exact BPair.unit_add _
  have hprod : ((BPair.ofPos .one + y.swap) * (BPair.ofPos .one + y.swap)
      * bsum (bpow y) (List.range k) * bsum (bpow y) (List.range j')).oneValue
      ((BPair.ofPos .one + (bpow y k).swap) * (BPair.ofPos .one + (bpow y j').swap)) := by
    refine BPair.oneValue_trans (BPair.oneValue_of_eq ?_) (BPair.mul_congr (hT k) (hT j'))
    rw [BPair.mul_assoc _ _ (bsum (bpow y) (List.range j')), BPair.mul_mul_mul_comm]
  have hexp : ((BPair.ofPos .one + (bpow y k).swap) * (BPair.ofPos .one + (bpow y j').swap)).oneValue
      (BPair.ofPos .one + (bpow y j').swap + (bpow y k).swap + bpow y k * bpow y j') := by
    rw [BPair.left_distrib, BPair.right_distrib, BPair.right_distrib, BPair.swap_mul_swap]
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.add_congr (BPair.mul_one_read _) (BPair.mul_one_read _))
      (BPair.add_congr (BPair.ofPos_one_mul _) (BPair.oneValue_refl _))) ?_
    rw [← BPair.add_assoc, BPair.add_right_comm (BPair.ofPos .one)]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.oneValue_trans hprod hexp) (BPair.oneValue_refl _))) ?_
  refine BPair.oneValue_trans ?_
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (bpow_add y k j')))
  have hperm : bpow y k + (BPair.ofPos .one + (bpow y j').swap + (bpow y k).swap
      + bpow y k * bpow y j' + bpow y j')
      = BPair.ofPos .one + bpow y k * bpow y j' + (bpow y k + (bpow y k).swap)
        + (bpow y j' + (bpow y j').swap) := by
    repeat rw [← BPair.add_assoc]
    rw [BPair.add_comm (bpow y k) (BPair.ofPos .one),
      BPair.add_right_comm (BPair.ofPos .one + bpow y k + (bpow y j').swap) ((bpow y k).swap) (bpow y k * bpow y j'),
      BPair.add_right_comm (BPair.ofPos .one + bpow y k) ((bpow y j').swap) (bpow y k * bpow y j'),
      BPair.add_right_comm (BPair.ofPos .one) (bpow y k) (bpow y k * bpow y j'),
      BPair.add_right_comm (BPair.ofPos .one + bpow y k * bpow y j' + bpow y k) ((bpow y j').swap) ((bpow y k).swap),
      BPair.add_right_comm (BPair.ofPos .one + bpow y k * bpow y j' + bpow y k + (bpow y k).swap) ((bpow y j').swap) (bpow y j')]
  rw [hperm]
  refine BPair.oneValue_trans (BPair.add_congr (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_swap_null _)) (BPair.add_swap_null _)) ?_
  exact BPair.oneValue_trans (BPair.add_congr (BPair.add_unit _) (BPair.oneValue_refl _))
    (BPair.add_unit _)

/-- A power sits at or below one joined to the power at the raised
key, the gap read's own gap a positive element at a base at or beyond
the sum's unit: a square against two folds of powers with a further
power. -/
theorem bpow_le_one_add (y : BPair) (k j' : Nat) (hy : BPair.unit ≤ y) :
    bpow y k ≤ BPair.ofPos .one + bpow y (k + j') := by
  refine leB_congr_right (bpow_gap_read y k j') ?_
  refine leB_congr_left (BPair.add_unit _) (leB_add (leB_refl _) ?_)
  refine unitLeAdd (unitLeMul (unitLeMul (unitLeSq _) ?_) ?_) (unitLeBpow hy j')
  · exact foldB_nonneg _ _ (fun i _ => unitLeBpow hy i)
  · exact foldB_nonneg _ _ (fun i _ => unitLeBpow hy i)

/-- The near-scale read, cleared at the scale's pair `[zN : zD]`: a
datum whose scale by the pair's first member's power sits at or below
the raised power's multiple of a weight joined to a remainder itself
at or below that multiple sits, scaled by the second member's power,
at or below twice the power's multiple of the weight, the shared
power withdrawn from both sides. -/
theorem near_scale_read (A B C zN zD : BPair) (k j' : Nat) (hz : BPair.unit < zN)
    (hA : A * bpow zN j' * bpow zD k ≤ bpow zN (k + j') * B + bpow zD (k + j') * C)
    (hC : bpow zD (k + j') * C ≤ bpow zN (k + j') * B) :
    A * bpow zD k ≤ BPair.ofNat 2 * (bpow zN k * B) := by
  have hzj : BPair.unit < bpow zN j' := unitLtBpow hz j'
  have h2 : A * bpow zN j' * bpow zD k ≤ bpow zN (k + j') * B + bpow zN (k + j') * B :=
    leB_trans hA (leB_add (leB_refl _) hC)
  have hpiece : (bpow zN k * B * bpow zN j').oneValue (bpow zN (k + j') * B) := by
    rw [BPair.mul_right_comm (bpow zN k) B (bpow zN j')]
    exact BPair.mul_congr_left (BPair.oneValue_symm (bpow_add zN k j'))
  have hRHS : (BPair.ofNat 2 * (bpow zN k * B) * bpow zN j').oneValue
      (bpow zN (k + j') * B + bpow zN (k + j') * B) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofNat_two_mul (bpow zN k * B))) ?_
    rw [BPair.right_distrib]
    exact BPair.add_congr hpiece hpiece
  exact leB_unscale hzj (leB_congr (BPair.oneValue_of_eq (BPair.mul_right_comm _ _ _))
    (BPair.oneValue_symm hRHS) h2)

/-- The gap read at the chain's last step (`lem:cornerkey`'s
concentration key), cleared: the chain's members at a stated clearing
and the tolerance a pair `[τN : τD]`; at a weight the Bernstein key
prices by the Pascal count of the chain's length at the key against
the tolerance's power, and a weight whose scale by the raised key's
member sits at or beyond the clearing, the key's member sits at or
below its scale by the tolerance joined to the raised key's member,
the display cleared at the tolerance's second member.  The refused
read puts the gap beyond the tolerance, the binomial member at the
partition of the key's member into the gap and the raised key's
member prices the member's power from beneath, and the chain's power
read closes it against the weight's own bound. -/
theorem chain_gap (b : Nat → BPair) (k' e : Nat) (Δ W τN τD : BPair)
    (hb0 : b 0 ≤ Δ)
    (hpos : ∀ i, i ≤ k' + 1 → BPair.unit < b i)
    (hdec : b (k' + 1) ≤ b k')
    (hconv : ∀ i, i + 1 ≤ k' → b (i + 1) * b (i + 1) ≤ b i * b (i + 2))
    (hτN : BPair.unit ≤ τN) (hτD : BPair.unit < τD) (he : e + 1 ≤ k' + 1)
    (hW : Δ ≤ W * b (k' + 1))
    (hkey : W * bpow τD (e + 1) ≤ BPair.ofNat (pasc (k' + 1) (e + 1)) * bpow τN (e + 1)) :
    τD * b k' ≤ τN * b k' + τD * b (k' + 1) := by
  refine leB_of_not_lt (fun hlt => ?_)
  have hbk : BPair.unit < b (k' + 1) := hpos (k' + 1) (Nat.le_refl _)
  have hbk' : BPair.unit < b k' := ltB_trans_le hbk hdec
  have hτB : BPair.unit ≤ τN * b k' := unitLeMul hτN (leB_of_lt hbk')
  have hX0 : BPair.unit ≤ b k' + (b (k' + 1)).swap :=
    leB_unit_add (by rw [BPair.swap_swap]; exact hdec)
  have hXt : τN * b k' < τD * (b k' + (b (k' + 1)).swap) := by
    have h := ltB_add hlt (leB_refl (τD * b (k' + 1)).swap)
    refine BPair.lt_congr ?_ ?_ h
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_swap_null _)) (BPair.add_unit _)
    · rw [BPair.left_distrib, BPair.mul_swap]
      exact BPair.oneValue_refl _
  have hDX : BPair.unit < τD * (b k' + (b (k' + 1)).swap) := leB_ltB_trans hτB hXt
  have hX1 : BPair.unit < b k' + (b (k' + 1)).swap := unitLt_unscale (leB_of_lt hτD) hDX
  obtain ⟨d, hd⟩ := Nat.le.dest he
  have hkd : k' = e + d :=
    Eq.symm (Nat.succ.inj (show (e + d).succ = k'.succ from
      Eq.trans (Nat.add_right_comm e 1 d).symm hd))
  have hbin := binom_member (b k' + (b (k' + 1)).swap) (b (k' + 1)) (e + 1) d hX0
    (leB_of_lt hbk)
  rw [hd] at hbin
  have hcp := chain_power b k' Δ hb0 hpos hconv
  have hup : bpow (b k' + (b (k' + 1)).swap + b (k' + 1)) (k' + 1)
      ≤ Δ * bpow (b (k' + 1)) e * bpow (b (k' + 1)) d := by
    refine leB_congr_left (BPair.oneValue_symm (bpow_congr (BPair.add_swap_self _ _) (k' + 1))) ?_
    refine leB_congr_right ?_ hcp
    rw [hkd, BPair.mul_assoc]
    exact BPair.mul_congr (BPair.oneValue_refl _) (bpow_add _ e d)
  have hd0 : BPair.unit < bpow (b (k' + 1)) d := unitLtBpow hbk d
  have h1 : BPair.ofNat (pasc (k' + 1) (e + 1)) * bpow (b k' + (b (k' + 1)).swap) (e + 1)
      ≤ Δ * bpow (b (k' + 1)) e := by
    refine leB_unscale hd0 ?_
    exact leB_trans (leB_congr_left (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) hbin) hup
  have hpw : bpow (τN * b k') (e + 1) < bpow (τD * (b k' + (b (k' + 1)).swap)) (e + 1) := by
    have h1' : τN * b k' * bpow (τN * b k') e
        ≤ τN * b k' * bpow (τD * (b k' + (b (k' + 1)).swap)) e :=
      leB_mulR hτB (bpow_mono hτB (leB_of_lt hXt) e)
    have h2' : τN * b k' * bpow (τD * (b k' + (b (k' + 1)).swap)) e
        < τD * (b k' + (b (k' + 1)).swap) * bpow (τD * (b k' + (b (k' + 1)).swap)) e :=
      ltB_mulPos hXt (unitLtBpow hDX e)
    exact BPair.lt_congr (BPair.oneValue_symm (bpow_succ_read _ e))
      (BPair.oneValue_symm (bpow_succ_read _ e)) (leB_ltB_trans h1' h2')
  have hpasc : BPair.unit < BPair.ofNat (pasc (k' + 1) (e + 1)) :=
    unitLtNat (pasc_pos (k' + 1) (e + 1) he)
  have hτDe : BPair.unit ≤ bpow τD (e + 1) := unitLeBpow (leB_of_lt hτD) (e + 1)
  have h2 : BPair.ofNat (pasc (k' + 1) (e + 1)) * bpow (τN * b (k' + 1)) (e + 1)
      < bpow τD (e + 1) * (Δ * bpow (b (k' + 1)) e) := by
    refine leB_ltB_trans (leB_mulR (leB_of_lt hpasc)
      (bpow_mono (unitLeMul hτN (leB_of_lt hbk)) (leB_mulR hτN hdec) (e + 1))) ?_
    have h3 : bpow (τN * b k') (e + 1) * BPair.ofNat (pasc (k' + 1) (e + 1))
        < bpow (τD * (b k' + (b (k' + 1)).swap)) (e + 1) * BPair.ofNat (pasc (k' + 1) (e + 1)) :=
      ltB_mulPos hpw hpasc
    refine ltB_trans_le (BPair.lt_congr (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) h3) ?_
    refine leB_congr_left ?_ (leB_mulR hτDe h1)
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (bpow_mul τD _ (e + 1))) ?_
    exact BPair.oneValue_of_eq (by rw [BPair.mul_left_comm])
  have h4 : BPair.ofNat (pasc (k' + 1) (e + 1)) * bpow τN (e + 1) * b (k' + 1)
      < bpow τD (e + 1) * Δ := by
    refine ltB_unscale (unitLeBpow (leB_of_lt hbk) e) ?_
    refine BPair.lt_congr ?_ (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) h2
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (bpow_mul τN (b (k' + 1)) (e + 1))) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.mul_congr (BPair.oneValue_refl _) (bpow_succ_read _ e))) ?_
    exact BPair.oneValue_of_eq (by repeat rw [← BPair.mul_assoc])
  have h5 : bpow τD (e + 1) * Δ
      ≤ BPair.ofNat (pasc (k' + 1) (e + 1)) * bpow τN (e + 1) * b (k' + 1) := by
    refine leB_trans (leB_mulR hτDe hW) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (BPair.mul_left_comm' _ _ _).symm)
      (leB_mulL (leB_of_lt hbk) hkey)
  exact leB_not_lt h5 h4

set_option genInjectivity false in
structure POps (γ : Type) where
  add : γ → γ → γ
  mul : γ → γ → γ
  unit : γ
  one : γ

/-- The count carrier's instance of the entry bundle. -/
def natOps : POps Nat := ⟨Nat.add, Nat.mul, 0, 1⟩

/-- The plain row-against-column fold at a carrier. -/
def dotO {γ : Type} (ops : POps γ) : List γ → List γ → γ
  | [], _ => ops.unit
  | _ :: _, [] => ops.unit
  | a :: s, b :: t => ops.add (ops.mul a b) (dotO ops s t)

/-- The dot fold at matched lists, the entry bundle's count
instance. -/
def dotNat (X Y : List Nat) : Nat :=
  dotO natOps X Y

/-- The unit coefficient list pairs off at the second family's
total, at the matched count. -/
theorem dotOnesL : ∀ (n : Nat) (Y : List Nat), Y.length = n →
    dotNat (List.replicate n 1) Y = sumNat Y
  | 0, [], _ => rfl
  | 0, _ :: _, h => Nat.noConfusion h
  | _ + 1, [], h => Nat.noConfusion h
  | n + 1, b :: Y, h => by
    show 1 * b + dotNat (List.replicate n 1) Y = b + sumNat Y
    rw [Nat.one_mul, dotOnesL n Y (Nat.succ.inj h)]

/-- The coefficient total sits at or below the pairing against a
family occupied at every paired key. -/
theorem sumNat_le_dotNat : ∀ (m Y : List Nat), m.length ≤ Y.length →
    (∀ i, i < m.length → 1 ≤ ground.getAt 0 Y i) →
    ground.sumNat m ≤ ground.dotNat m Y
  | [], _, _, _ => Nat.le_refl 0
  | _ :: _, [], h, _ => absurd h (Nat.not_succ_le_zero _)
  | a :: m, b :: Y, h, hb => by
    show a + ground.sumNat m ≤ a * b + ground.dotNat m Y
    have h1 : a ≤ a * b := by
      have h2 := Nat.mul_le_mul_left a (hb 0 (Nat.succ_pos _))
      rw [Nat.mul_one] at h2
      exact h2
    exact Nat.add_le_add h1
      (sumNat_le_dotNat m Y (Nat.le_of_succ_le_succ h)
        (fun i hi => hb (i + 1) (Nat.succ_lt_succ hi)))

/-- A natural pairing increases when the second list's matched
entries increase, including a first list shorter than either one. -/
theorem dotNat_mono_right : ∀ (m x y : List Nat), x.length = y.length →
    (∀ i, i < x.length → getAt 0 x i ≤ getAt 0 y i) → dotNat m x ≤ dotNat m y
  | [], _, _, _, _ => Nat.le_refl 0
  | _ :: _, [], [], _, _ => Nat.le_refl 0
  | _ :: _, [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, _ :: _, [], h, _ => Nat.noConfusion h
  | a :: m, _ :: x, _ :: y, h, he =>
    Nat.add_le_add (Nat.mul_le_mul_left a (he 0 (Nat.succ_pos _)))
      (dotNat_mono_right m x y (Nat.succ.inj h)
        (fun i hi => he (i + 1) (Nat.succ_lt_succ hi)))

/-- The occupancy family occupied once at each of the first keys:
the units then the vacancies. -/
def onesRows (j g : Nat) : List Nat :=
  List.replicate j 1 ++ List.replicate g 0

/-- The family's width is the two counts' join. -/
theorem length_onesRows (j g : Nat) :
    (onesRows j g).length = j + g := by
  show (List.replicate j 1 ++ List.replicate g 0).length = j + g
  rw [ground.length_append (List.replicate j 1) (List.replicate g 0),
    ground.length_replicate (1 : Nat) j,
    ground.length_replicate (0 : Nat) g]

/-- The family's entry: one below the occupied count, the vacant
read at it and beyond. -/
theorem getAt_onesRows (j g x : Nat) :
    getAt 0 (onesRows j g) x = if x < j then 1 else 0 := by
  show ground.getAt 0 (List.replicate j 1 ++ List.replicate g 0) x
    = if x < j then 1 else 0
  rw [ground.getAt_append 0 (List.replicate j 1)
      (List.replicate g 0) x,
    ground.length_replicate (1 : Nat) j]
  by_cases h : x < j
  · rw [if_pos h, if_pos h, ground.getAt_replicate 0 1 j x h]
  · rw [if_neg h, if_neg h, ground.getAt_replicate_zero g (x - j)]

/-- The unit occupancy family at a stated key: one at the key, the
further keys vacant — the letter's unit content and the one-box
shape's family at its instances. -/
def unitAt (d i : Nat) : List Nat :=
  (List.range d).map (fun j => if j = i then 1 else 0)

theorem length_unitAt (d i : Nat) : (unitAt d i).length = d :=
  length_mapRange _ d

theorem getAt_unitAt (d i k : Nat) :
    ground.getAt 0 (unitAt d i) k
      = if k < d then (if k = i then 1 else 0) else 0 :=
  getAt_map_range 0 (fun j => if j = i then 1 else 0) d k

/-- The unit family at a key inside the width as its list: the
vacancies below the key, the unit, the vacancies beyond. -/
theorem unitAt_replicate (d i : Nat) (hi : i < d) :
    unitAt d i
      = List.replicate i 0 ++ 1 :: List.replicate (d - i - 1) 0 := by
  have hpos : 1 ≤ d - i := subPos hi
  refine getAt_ext 0 _ _ ?_ ?_
  · rw [length_unitAt, length_append, length_replicate]
    show d = i + ((List.replicate (d - i - 1) 0).length + 1)
    rw [length_replicate, subAdd hpos, Nat.add_comm, subAdd (Nat.le_of_lt hi)]
  · intro k hk
    rw [length_unitAt] at hk
    rw [getAt_unitAt, if_pos hk,
      getAt_append 0 (List.replicate i 0) _ k, length_replicate]
    by_cases hki : k < i
    · rw [if_pos hki, if_neg (Nat.ne_of_lt hki), getAt_replicate_zero i k]
    · rw [if_neg hki]
      by_cases he : k = i
      · rw [if_pos he, he, Nat.sub_self]
        rfl
      · rw [if_neg he]
        have hik : i < k := by
          match Nat.lt_or_ge k i with
          | .inl h => exact absurd h hki
          | .inr h =>
            match Nat.le.dest h with
            | ⟨0, h0⟩ => exact absurd h0.symm he
            | ⟨e + 1, h0⟩ =>
              refine Nat.le.intro (k := e) ?_
              rw [Nat.add_right_comm i 1 e]
              exact h0
        have hkp : 1 ≤ k - i := subPos hik
        rw [← subAdd hkp]
        show 0 = getAt 0 (List.replicate (d - i - 1) 0) (k - i - 1)
        exact (getAt_replicate_zero _ _).symm

/-- The unit family at a key inside the width is the vacancy family
raised at that key. -/
theorem unitAt_bumpRep (d i : Nat) (hi : i < d) :
    unitAt d i = bumpAt i (List.replicate d 0) := by
  have hrl : (List.replicate d (0 : Nat)).length = d :=
    length_replicate 0 d
  refine getAt_ext 0 _ _ ?_ ?_
  · rw [length_unitAt, length_bumpAt, hrl]
  · intro k hk
    rw [length_unitAt d i] at hk
    rw [getAt_unitAt d i k, if_pos hk]
    by_cases he : k = i
    · rw [if_pos he, he,
        getAt_bumpAt_self i (List.replicate d 0)
          (by rw [hrl]; exact hi),
        getAt_replicate_zero d i]
    · rw [if_neg he,
        getAt_bumpAt_ne i (List.replicate d 0) k he,
        getAt_replicate_zero d k]

/-- A list reading one at every key is the repeated unit, its
counts the repeated family's. -/
private theorem countOf_ones (t : List Nat)
    (hall : ∀ k, k < t.length → getAt 0 t k = 1) (v : Nat) :
    countOf v t = if v = 1 then t.length else 0 := by
  have ht : t = List.replicate t.length 1 :=
    getAt_ext 0 t _ (length_replicate 1 t.length).symm
      (fun i hi => by rw [hall i hi, getAt_replicate 0 1 t.length i hi])
  rw [congrArg (countOf v) ht]
  by_cases hv : v = 1
  · rw [if_pos hv, hv, countOf_replicate]
  · rw [if_neg hv, countOf_replicate_ne v 1 hv]

/-- One key off one with every further key at one: the counts per
value read the special entry once against the units. -/
private theorem countOf_one_special : ∀ (t : List Nat) (p sv : Nat),
    p < t.length → ¬ sv = 1 → getAt 0 t p = sv →
    (∀ k, k < t.length → ¬ k = p → getAt 0 t k = 1) →
    ∀ v, countOf v t
      = (if v = sv then 1 else 0)
        + (if v = 1 then t.length - 1 else 0)
  | [], p, _, hp, _, _, _, _ => absurd hp (Nat.not_lt_zero p)
  | a :: t, 0, sv, _, hsv, hval, hoff, v => by
    have ha : a = sv := hval
    have ht : ∀ k, k < t.length → getAt 0 t k = 1 :=
      fun k hk => hoff (k + 1) (Nat.succ_lt_succ hk)
        (fun he => Nat.noConfusion he)
    rw [countOf_cons, countOf_ones t ht v, ha]
    show ((if v = sv then 1 else 0) + if v = 1 then t.length else 0)
      = (if v = sv then 1 else 0)
        + if v = 1 then t.length + 1 - 1 else 0
    rw [addSubSelfR t.length 1]
  | a :: t, p + 1, sv, hp, hsv, hval, hoff, v => by
    have ha : a = 1 := hoff 0 (Nat.succ_pos t.length)
      (fun he => Nat.noConfusion he)
    have hp' : p < t.length := Nat.lt_of_succ_lt_succ hp
    have hval' : getAt 0 t p = sv := hval
    have hoff' : ∀ k, k < t.length → ¬ k = p →
        getAt 0 t k = 1 :=
      fun k hk hne => hoff (k + 1) (Nat.succ_lt_succ hk)
        (fun he => hne (Nat.succ.inj he))
    rw [countOf_cons,
      countOf_one_special t p sv hp' hsv hval' hoff' v, ha]
    show (if v = 1 then 1 else 0) + ((if v = sv then 1 else 0)
        + if v = 1 then t.length - 1 else 0)
      = (if v = sv then 1 else 0)
        + if v = 1 then t.length + 1 - 1 else 0
    rw [addSubSelfR t.length 1]
    by_cases hv1 : v = 1
    · have h1 : 1 ≤ t.length := Nat.lt_of_le_of_lt (Nat.zero_le p) hp'
      rw [if_pos hv1, if_neg (fun he => hsv (he.symm.trans hv1)),
        if_pos hv1, if_pos hv1, Nat.zero_add,
        Nat.add_comm 1 (t.length - 1), subAdd h1,
        Nat.zero_add]
    · rw [if_neg hv1, if_neg hv1, if_neg hv1, Nat.add_zero,
        Nat.zero_add]

/-- Two special keys, two and the sum's unit, every further key at
one: the letter-pair content's counts. -/
theorem countOf_pattern2 : ∀ (m : List Nat) (i j : Nat),
    i < m.length → j < m.length → ¬ i = j →
    getAt 0 m i = 2 → getAt 0 m j = 0 →
    (∀ k, k < m.length → ¬ k = i → ¬ k = j →
      getAt 0 m k = 1) →
    countOf 0 m = 1 ∧ countOf 2 m = 1
      ∧ countOf 1 m + 2 = m.length
  | [], i, _, hi, _, _, _, _, _ => absurd hi (Nat.not_lt_zero i)
  | a :: t, 0, 0, _, _, hij, _, _, _ => absurd rfl hij
  | a :: t, 0, j + 1, _, hj, _, h2, h0, h1 => by
    have ha : a = 2 := h2
    have hj' : j < t.length := Nat.lt_of_succ_lt_succ hj
    have hone := countOf_one_special t j 0 hj'
      (fun he => Nat.noConfusion he) h0
      (fun k hk hne => h1 (k + 1) (Nat.succ_lt_succ hk)
        (fun he => Nat.noConfusion he)
        (fun he => hne (Nat.succ.inj he)))
    have h1t : 1 ≤ t.length := Nat.lt_of_le_of_lt (Nat.zero_le j) hj'
    refine ⟨?_, ?_, ?_⟩
    · rw [countOf_cons, ha, if_neg (fun he => Nat.noConfusion he),
        hone 0, if_pos rfl, if_neg (fun he => Nat.noConfusion he),
        Nat.add_zero]
    · rw [countOf_cons, ha, if_pos rfl, hone 2,
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        if_neg (fun he => Nat.noConfusion he), Nat.add_zero]
    · rw [countOf_cons, ha,
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        hone 1, if_neg (fun he => Nat.noConfusion he), Nat.zero_add,
        Nat.zero_add]
      show t.length - 1 + 2 = t.length + 1
      rw [show t.length - 1 + 2 = t.length - 1 + 1 + 1 from rfl,
        subAdd h1t]
  | a :: t, i + 1, 0, hi, _, hij, h2, h0, h1 => by
    have ha : a = 0 := h0
    have hi' : i < t.length := Nat.lt_of_succ_lt_succ hi
    have hone := countOf_one_special t i 2 hi'
      (fun he => Nat.noConfusion (Nat.succ.inj he)) h2
      (fun k hk hne => h1 (k + 1) (Nat.succ_lt_succ hk)
        (fun he => hne (Nat.succ.inj he))
        (fun he => Nat.noConfusion he))
    have h1t : 1 ≤ t.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi'
    refine ⟨?_, ?_, ?_⟩
    · rw [countOf_cons, ha, if_pos rfl, hone 0,
        if_neg (fun he => Nat.noConfusion he),
        if_neg (fun he => Nat.noConfusion he), Nat.add_zero]
    · rw [countOf_cons, ha, if_neg (fun he => Nat.noConfusion he),
        hone 2, if_pos rfl,
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        Nat.add_zero]
    · rw [countOf_cons, ha, if_neg (fun he => Nat.noConfusion he),
        hone 1, if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        Nat.zero_add, Nat.zero_add]
      show t.length - 1 + 2 = t.length + 1
      rw [show t.length - 1 + 2 = t.length - 1 + 1 + 1 from rfl,
        subAdd h1t]
  | a :: t, i + 1, j + 1, hi, hj, hij, h2, h0, h1 => by
    have ha : a = 1 := h1 0 (Nat.succ_pos t.length)
      (fun he => Nat.noConfusion he) (fun he => Nat.noConfusion he)
    obtain ⟨hc0, hc2, hc1⟩ := countOf_pattern2 t i j
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
      (fun he => hij (congrArg Nat.succ he)) h2 h0
      (fun k hk hni hnj => h1 (k + 1) (Nat.succ_lt_succ hk)
        (fun he => hni (Nat.succ.inj he))
        (fun he => hnj (Nat.succ.inj he)))
    refine ⟨?_, ?_, ?_⟩
    · rw [countOf_cons, ha,
        if_neg (fun he => Nat.noConfusion he), hc0, Nat.zero_add]
    · rw [countOf_cons, ha,
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)), hc2,
        Nat.zero_add]
    · rw [countOf_cons, ha, if_pos rfl]
      show 1 + countOf 1 t + 2 = t.length + 1
      rw [Nat.add_comm 1 (countOf 1 t), Nat.add_assoc,
        Nat.add_comm 1 2, ← Nat.add_assoc, hc1]

/-- Two keys' unit families part at the stated key's own read. -/
theorem unitAt_ne (d i j : Nat) (hi : i < d) (hij : ¬ i = j) :
    ¬ unitAt d i = unitAt d j := by
  intro he
  have h1 : ground.getAt 0 (unitAt d i) i
      = ground.getAt 0 (unitAt d j) i := by rw [he]
  rw [getAt_unitAt d i i, getAt_unitAt d j i, if_pos hi, if_pos hi,
    if_pos rfl, if_neg hij] at h1
  exact Nat.noConfusion h1

/-- The unit family at the first key: the one at the head, the
vacant tail. -/
theorem unitAt_zero (n : Nat) :
    unitAt (n + 1) 0 = 1 :: List.replicate n 0 := by
  show (List.range (n + 1)).map (fun j => if j = 0 then 1 else 0)
    = 1 :: List.replicate n 0
  rw [range_cons n]
  show (1 : Nat) :: ((List.range n).map (fun j => j + 1)).map
      (fun j => if j = 0 then 1 else 0) = 1 :: List.replicate n 0
  rw [ground.map_map (fun j => j + 1) (fun j => if j = 0 then 1 else 0)
      (List.range n),
    ground.map_congr_all (fun j => if j + 1 = 0 then 1 else 0)
      (fun _ => 0)
      (fun j => if_neg (fun he : j + 1 = 0 => Nat.noConfusion he))
      (List.range n),
    ground.map_const (0 : Nat) (List.range n), length_range]

/-- The unit family at a successor key: the vacant head, the unit
family one key down. -/
theorem unitAt_succ (n i : Nat) :
    unitAt (n + 1) (i + 1) = 0 :: unitAt n i := by
  show (List.range (n + 1)).map (fun j => if j = i + 1 then 1 else 0)
    = 0 :: (List.range n).map (fun j => if j = i then 1 else 0)
  rw [range_cons n]
  show (if (0 : Nat) = i + 1 then 1 else 0)
      :: ((List.range n).map (fun j => j + 1)).map
        (fun j => if j = i + 1 then 1 else 0)
    = 0 :: (List.range n).map (fun j => if j = i then 1 else 0)
  rw [if_neg (fun he : (0 : Nat) = i + 1 => Nat.noConfusion he),
    ground.map_map (fun j => j + 1)
      (fun j => if j = i + 1 then 1 else 0) (List.range n),
    ground.map_congr_all (fun j => if j + 1 = i + 1 then 1 else 0)
      (fun j => if j = i then 1 else 0)
      (fun j => by
        by_cases hj : j = i
        · rw [if_pos hj, if_pos (congrArg Nat.succ hj)]
        · rw [if_neg hj, if_neg (fun he => hj (Nat.succ.inj he))])
      (List.range n)]

/-- The unit family's total is the one, at a key inside the
width. -/
theorem sumNat_unitAt : ∀ (d i : Nat), i < d →
    sumNat (unitAt d i) = 1
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
    rw [unitAt_zero n]
    show 1 + sumNat (List.replicate n 0) = 1
    rw [sumNat_replicate_zero n]
  | n + 1, i + 1, h => by
    rw [unitAt_succ n i]
    show 0 + sumNat (unitAt n i) = 1
    rw [Nat.zero_add, sumNat_unitAt n i (Nat.lt_of_succ_lt_succ h)]

/-- On matched count lists, an adjacent exchange moves across
the pairing from either list to the other. -/
theorem dotNat_adjSwap : ∀ (k : Nat) (u v : List Nat), u.length = v.length →
    dotNat u (adjSwap k v) = dotNat (adjSwap k u) v
  | 0, [], [], _ => rfl
  | _ + 1, [], [], _ => rfl
  | _, [], _ :: _, h => Nat.noConfusion h
  | _, _ :: _, [], h => Nat.noConfusion h
  | 0, [_], [_], _ => rfl
  | 0, [_], _ :: _ :: _, h => Nat.noConfusion (Nat.succ.inj h)
  | 0, _ :: _ :: _, [_], h => Nat.noConfusion (Nat.succ.inj h)
  | 0, a :: b :: u, c :: d :: v, _ => by
    change a * d + (b * c + dotNat u v) = b * c + (a * d + dotNat u v)
    exact Nat.add_left_comm _ _ _
  | k + 1, a :: u, b :: v, h =>
    congrArg (fun n => a * b + n) (dotNat_adjSwap k u v (Nat.succ.inj h))

/-- The dot's index read: the fold of the entry products over the
key range. -/
theorem dotNat_index : ∀ X Y : List Nat, Y.length = X.length →
    dotNat X Y = ground.famFold Nat.add 0
      (fun i => ground.getAt 0 X i * ground.getAt 0 Y i)
      (List.range X.length)
  | [], [], _ => rfl
  | [], b :: Y, h => Nat.noConfusion h
  | a :: X, [], h => Nat.noConfusion h
  | a :: X, b :: Y, h => by
    show a * b + dotNat X Y
      = ground.famFold Nat.add 0
        (fun i => ground.getAt 0 (a :: X) i
          * ground.getAt 0 (b :: Y) i)
        (List.range (X.length + 1))
    rw [range_cons X.length,
      show ground.famFold Nat.add 0
          (fun i => ground.getAt 0 (a :: X) i
            * ground.getAt 0 (b :: Y) i)
          (0 :: (List.range X.length).map (fun j => j + 1))
        = Nat.add (a * b) (ground.famFold Nat.add 0
            (fun i => ground.getAt 0 (a :: X) i
              * ground.getAt 0 (b :: Y) i)
            ((List.range X.length).map (fun j => j + 1)))
        from rfl,
      ground.famFold_map Nat.add 0
        (fun i => ground.getAt 0 (a :: X) i
          * ground.getAt 0 (b :: Y) i)
        (fun j => j + 1) (List.range X.length)]
    show a * b + dotNat X Y = a * b + ground.famFold Nat.add 0
      (fun i => ground.getAt 0 X i * ground.getAt 0 Y i)
      (List.range X.length)
    rw [dotNat_index X Y (Nat.succ.inj h)]

/-- The conjunction associates. -/
private theorem andAssocB : ∀ a b c : Bool,
    (a && (b && c)) = (a && b && c)
  | true, _, _ => rfl
  | false, _, _ => rfl

/-- A true conjunction is true at both members. -/
theorem andSplitB : ∀ {a b : Bool}, (a && b) = true →
    a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => Bool.noConfusion h
  | false, _, h => Bool.noConfusion h

/-- The keyed pair walk: two lists read together with a running
key, one stated read per position, the walk truncating at the
shorter list. -/
def pairIdxAll (p : Nat → Nat → Nat → Bool) :
    List Nat → List Nat → Nat → Bool
  | a :: ts, b :: hs, k => p k a b && pairIdxAll p ts hs (k + 1)
  | [], _, _ => true
  | _ :: _, [], _ => true

/-- The keyed pair walk reads at every position below both lengths:
the walk's conjunct at the running key against the entries. -/
theorem pairIdxAll_at (p : Nat → Nat → Nat → Bool) :
    ∀ (tl hd : List Nat) (k : Nat),
      pairIdxAll p tl hd k = true →
      ∀ i, i < tl.length → i < hd.length →
        p (k + i) (getAt 0 tl i) (getAt 0 hd i) = true
  | [], _, _, _, i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | _ :: _, [], _, _, i, _, hi => absurd hi (Nat.not_lt_zero i)
  | a :: ts, b :: hs, k, hw, 0, _, _ => by
    have hs2 := andSplitB (show
      (p k a b && pairIdxAll p ts hs (k + 1)) = true from hw)
    rw [Nat.add_zero]
    exact hs2.1
  | a :: ts, b :: hs, k, hw, i + 1, hi, hi' => by
    have hs2 := andSplitB (show
      (p k a b && pairIdxAll p ts hs (k + 1)) = true from hw)
    have hIH := pairIdxAll_at p ts hs (k + 1) hs2.2 i
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')
    have hk : k + 1 + i = k + (i + 1) := by
      rw [Nat.add_assoc k 1 i, Nat.add_comm 1 i]
    rw [hk] at hIH
    exact hIH

/-- Two true tests join true (`Bool.and_eq_true` is
propext-bearing; this is the clean spelling). -/
theorem andIntroB : ∀ {a b : Bool}, a = true → b = true →
    (a && b) = true
  | true, true, _, _ => rfl
  | true, false, _, h => Bool.noConfusion h
  | false, _, h, _ => Bool.noConfusion h

/-- A true fold reads true at every member. -/
theorem all_of_mem {α : Type} (f : α → Bool) :
    ∀ (l : List α), l.all f = true → ∀ x, x ∈ l → f x = true
  | [], _, _, hx => nomatch hx
  | a :: t, h, x, hx => by
    have hsplit : (f a && t.all f) = true := h
    obtain ⟨hfa, hft⟩ := andSplitB hsplit
    match hx with
    | List.Mem.head _ => exact hfa
    | List.Mem.tail _ hxt => exact all_of_mem f t hft x hxt

/-- A fold's members all read the domain from the pointwise read
at the members. -/
theorem all_of_mem_intro {α : Type} (P : α → Bool) :
    ∀ l : List α, (∀ x, x ∈ l → P x = true) → l.all P = true
  | [], _ => rfl
  | a :: t, h => by
    show (P a && t.all P) = true
    rw [h a (List.Mem.head t),
      all_of_mem_intro P t (fun x hx => h x (List.Mem.tail a hx))]
    rfl

/-- A family at every member the refused read filters to the
vacant list. -/
theorem filter_false {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: t, h => by
    rw [filter_cons_false (h a (List.Mem.head t))]
    exact filter_false p t (fun x hx => h x (List.Mem.tail a hx))

/-- A refused occupancy fold reads pointwise: the negated family
holds at every member. -/
theorem all_not_of_any_false {α : Type} (f : α → Bool) :
    ∀ l : List α, l.any f = false →
      l.all (fun x => !(f x)) = true
  | [], _ => rfl
  | a :: t, h => by
    have ha : f a = false := by
      cases hfa : f a with
      | false => rfl
      | true =>
        have h' : (f a || t.any f) = false := h
        rw [hfa] at h'
        exact Bool.noConfusion h'
    have ht : t.any f = false := by
      have h' : (f a || t.any f) = false := h
      rw [ha] at h'
      exact h'
    show (!(f a) && t.all (fun x => !(f x))) = true
    rw [ha, all_not_of_any_false f t ht]
    rfl

/-- The pointwise refusals fold the occupancy read to its
refusal. -/
theorem any_false_of_all_not {α : Type} (f : α → Bool) :
    ∀ l : List α, l.all (fun x => !(f x)) = true →
      l.any f = false
  | [], _ => rfl
  | a :: t, h => by
    have hs := andSplitB h
    show (f a || t.any f) = false
    have ha : f a = false := by
      cases hfa : f a with
      | false => rfl
      | true =>
        have h1 : (!(f a)) = true := hs.1
        rw [hfa] at h1
        exact Bool.noConfusion h1
    rw [ha]
    exact any_false_of_all_not f t hs.2

/-- A true disjunction is true at one member. -/
theorem orSplitB : ∀ {a b : Bool}, (a || b) = true →
    a = true ∨ b = true
  | true, _, _ => Or.inl rfl
  | false, true, _ => Or.inr rfl

/-- A refused disjunction refuses both members. -/
theorem or_false_split : ∀ {a b : Bool}, (a || b) = false →
    a = false ∧ b = false
  | false, false, _ => ⟨rfl, rfl⟩
  | false, true, h => Bool.noConfusion h
  | true, _, h => Bool.noConfusion h

/-- The Boolean fold splits over the join. -/
theorem all_append {α : Type} (f : α → Bool) :
    ∀ u v : List α, (u ++ v).all f = (u.all f && v.all f)
  | [], _ => rfl
  | a :: u, v => by
    show (f a && (u ++ v).all f) = (f a && u.all f && v.all f)
    rw [all_append f u v, andAssocB (f a) (u.all f) (v.all f)]

/-- The fold reads across a flattening: the flattened list's fold
is the member families' folds' own. -/
theorem all_flatMap {α β : Type} (f : α → List β) (P : β → Bool) :
    ∀ l : List α, (l.flatMap f).all P = l.all (fun x => (f x).all P)
  | [] => rfl
  | a :: t => by
    show ((f a ++ t.flatMap f).all P) = ((f a).all P && _)
    rw [all_append P (f a) (t.flatMap f), all_flatMap f P t]

/-- The list fold's pointwise read: a true fold over a list reads
true at the member sitting at every one of its positions. -/
theorem all_getAt {α : Type} {P : α → Bool} (d : α) :
    ∀ l : List α, l.all P = true →
    ∀ k, k < l.length → P (getAt d l k) = true
  | [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | a :: l, h, k, hk => by
    have hs := andSplitB (show (P a && l.all P) = true from h)
    match k with
    | 0 => exact hs.1
    | k + 1 => exact all_getAt d l hs.2 k (Nat.lt_of_succ_lt_succ hk)

/-- The fold's converse: the pointwise reads at every key state the
fold. -/
theorem all_of_getAt {α : Type} (d : α) (P : α → Bool) :
    ∀ l : List α, (∀ k, k < l.length → P (getAt d l k) = true) →
      l.all P = true
  | [], _ => rfl
  | a :: t, h => by
    have h0 : P a = true := h 0 (Nat.succ_pos _)
    show (P a && t.all P) = true
    rw [h0,
      all_of_getAt d P t (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))]
    rfl

/-- The fold at a pointwise-constant read, the key-free intro. -/
theorem all_of_pointwise {α : Type} (P : α → Bool) :
    ∀ l : List α, (∀ x, P x = true) → l.all P = true
  | [], _ => rfl
  | a :: t, h => by
    show (P a && t.all P) = true
    rw [h a, all_of_pointwise P t h]
    rfl

/-- The fold reads across a map: the mapped list's fold is the
composed read's own. -/
theorem all_map {α β : Type} (g : α → β) (P : β → Bool) :
    ∀ l : List α, (l.map g).all P = l.all (fun x => P (g x))
  | [] => rfl
  | a :: t => by
    show (P (g a) && ((t.map g).all P)) = _
    rw [all_map g P t]
    rfl

/-- A read at the zipped pairs from a read at the first list's
members. -/
theorem all_zipWith_left {α β γ : Type} (f : α → β → γ) (P : γ → Bool) (Q : α → Bool)
    (h : ∀ x y, Q x = true → P (f x y) = true) :
    ∀ (u : List α) (v : List β), u.all Q = true → (List.zipWith f u v).all P = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: s, y :: t, hu => by
    obtain ⟨hx, hs⟩ := andSplitB (show (Q x && s.all Q) = true from hu)
    show (P (f x y) && (List.zipWith f s t).all P) = true
    rw [h x y hx, all_zipWith_left f P Q h s t hs]
    rfl

/-- The disjunction's fold over the enumeration reads its witness. -/
theorem orRange_read (f : Nat → Bool) : ∀ n : Nat,
    famFold Bool.or false f (List.range n) = true →
    ∃ i, i < n ∧ f i = true
  | 0, h => Bool.noConfusion h
  | n + 1, h => by
    rw [range_succ n, famFold_append Bool.or false
      (fun a b c => by cases a <;> cases b <;> cases c <;> rfl)
      (fun b => rfl) f] at h
    cases hA : famFold Bool.or false f (List.range n) with
    | true =>
      obtain ⟨i, hi, hfi⟩ := orRange_read f n hA
      exact ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_succ n), hfi⟩
    | false =>
      rw [hA] at h
      cases hf : f n with
      | true => exact ⟨n, Nat.le_refl (n + 1), hf⟩
      | false =>
        rw [show famFold Bool.or false f [n]
            = Bool.or (f n) false from rfl, hf] at h
        exact Bool.noConfusion h

/-- A witness inside the enumeration reads the fold true. -/
theorem orRange_intro (f : Nat → Bool) : ∀ (n i : Nat),
    i < n → f i = true →
    famFold Bool.or false f (List.range n) = true
  | 0, i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | n + 1, i, hi, hf => by
    rw [range_succ n, famFold_append Bool.or false
      (fun a b c => by cases a <;> cases b <;> cases c <;> rfl)
      (fun b => rfl) f]
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [orRange_intro f n i hlt hf]
      rfl
    · have hie : i = n := Nat.le_antisymm
        (Nat.le_of_succ_le_succ hi) hge
      rw [hie] at hf
      rw [show famFold Bool.or false f [n]
          = Bool.or (f n) false from rfl, hf]
      cases famFold Bool.or false f (List.range n) <;> rfl

/-- The range fold's pointwise read: a true fold over the key range
reads true at every key. -/
theorem all_range_read {f : Nat → Bool} : ∀ (n : Nat),
    (List.range n).all f = true → ∀ i, i < n → f i = true
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    rw [range_succ n, all_append f (List.range n) [n]] at h
    have hs := andSplitB h
    match Nat.lt_or_ge i n with
    | Or.inl hlt => exact all_range_read n hs.1 i hlt
    | Or.inr hge =>
      rw [Nat.le_antisymm (Nat.le_of_lt_succ hi) hge]
      exact (andSplitB hs.2).1

/-- The range fold's one-step introduction: a true fold over the
range with the next key true is the fold at the successor. -/
theorem all_range_succ_intro {f : Nat → Bool} (n : Nat)
    (h : (List.range n).all f = true) (hn : f n = true) :
    (List.range (n + 1)).all f = true := by
  rw [range_succ n, all_append f (List.range n) [n]]
  refine andIntroB h ?_
  show (f n && true) = true
  rw [hn]
  rfl

/-- The range fold's block introduction: a true fold over the range
with the next `m` keys true, read at their offsets from the range's
top, is the fold at the sum. -/
theorem all_range_block_intro {f : Nat → Bool} (n : Nat)
    (h : (List.range n).all f = true) :
    ∀ m : Nat, (List.range m).all (fun r => f (n + r)) = true →
      (List.range (n + m)).all f = true
  | 0, _ => h
  | m + 1, hm => by
    rw [range_succ m, all_append (fun r => f (n + r)) (List.range m) [m]] at hm
    have hs := andSplitB hm
    exact all_range_succ_intro (n + m) (all_range_block_intro n h m hs.1)
      (andSplitB hs.2).1

/-- The range fold's introduction: true at every key of the range
is the fold's own true read. -/
theorem all_range_intro {f : Nat → Bool} : ∀ (n : Nat),
    (∀ i, i < n → f i = true) → (List.range n).all f = true
  | 0, _ => rfl
  | n + 1, h =>
    all_range_succ_intro n (all_range_intro n (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      (h n (Nat.lt_succ_self n))

/-! The entry-carrier operations bundle: the displayed operations
of `def:ground` at a general carrier, one bundle per carrier, the
balance pair's instance beside it.  A law bundle reads the
operations at its own carrier equality, one operation bundle
serving every equality the carrier reads at. -/

set_option genInjectivity false in
/-- The entry carrier's operations: the sum and the product with
their units, and the balance partner carrying the sign.  The
carrier's equality is not an operation and is not carried here —
a law bundle reads the operations at its own equality, one
operation bundle serving every equality the carrier reads at. -/
structure DOps (γ : Type) extends POps γ where
  swap : γ → γ

/-- The balance-pair instance of the entry bundle. -/
def bpairOps : DOps BPair :=
  ⟨⟨BPair.add, BPair.mul, BPair.unit, BPair.ofPos .one⟩, BPair.swap⟩

/-- The off-key fold at an entry bundle: the family's images under a
stated map summed with the stated key withdrawn, the walk counting
the key down (`thm:decimation`(ii)'s off-row fold at any carrier,
the seed the sum's unit). -/
def offFoldO {γ : Type} (ops : DOps γ) (mg : γ → γ) : Nat → List γ → γ
  | _, [] => ops.unit
  | 0, _ :: t => famFold ops.add ops.unit mg t
  | i + 1, x :: t => ops.add (mg x) (offFoldO ops mg i t)

/-- The composite pair's instance of the entry bundle, a pair at a
balance-pair first datum `[⟨u:v⟩:c]` at its displayed reads: the
sum at the cross-multiplied first data over the clearings' product
(`BPair.addQ`), the product memberwise, the partner the balance
member's swap at the clearing kept, and the units at the clearing
one. -/
def bpairQOps : DOps (BPair × Pos) :=
  ⟨⟨BPair.addQ, fun p q => (p.1 * q.1, p.2 * q.2),
    (BPair.unit, .one), (BPair.ofPos .one, .one)⟩,
   fun p => (p.1.swap, p.2)⟩

set_option genInjectivity false in
/-- A read at the carrier: the relation with its decision procedure,
`def:ground`'s clause that a read is decidable at every argument.
The carrier towers iterate it at the one-value read, each level's
read the construction at the level below's own. -/
structure DRead (γ : Type) where
  rel : γ → γ → Prop
  dec : ∀ a b, Decidable (rel a b)

instance instGround38 {γ : Type} (R : DRead γ) (a b : γ) : Decidable (R.rel a b) :=
  R.dec a b

/-- The balance-pair instance of the read bundle, the one-value
read with its decision. -/
def bpairRead : DRead BPair :=
  ⟨BPair.oneValue, fun _ _ => inferInstance⟩

/-- Two cleared balance data — a balance datum at its stated
positive clearing — read one value exactly at the cross-multiplied
first data, `def:ground`'s displayed equality at the composite
pair. -/
def qOneValue (p q : BPair × Pos) : Prop :=
  (p.1.scale q.2).oneValue (q.1.scale p.2)

instance instGround39 (p q : BPair × Pos) : Decidable (qOneValue p q) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The composite pair's instance of the read bundle: the cleared
read with its decision. -/
def bpairQRead : DRead (BPair × Pos) :=
  ⟨qOneValue, fun _ _ => inferInstance⟩

/-! The composite pair's arithmetic at the cleared read: the read
is an equivalence, and the cleared join commutes, reassociates,
reads congruently in both summands, exchanges two joins' inner
members, withdraws the vacant datum from either summand and
regroups a seed against three joined pairs. -/

/-- The cleared read is reflexive. -/
theorem qOneValue_refl (p : BPair × Pos) : qOneValue p p :=
  BPair.oneValue_refl _

/-- The cleared read is symmetric. -/
theorem qOneValue_symm {p q : BPair × Pos} (h : qOneValue p q) :
    qOneValue q p :=
  BPair.oneValue_symm h

/-- The cleared read composes, the middle datum's clearing
cancelling. -/
theorem qOneValue_trans {p q r : BPair × Pos} (h1 : qOneValue p q)
    (h2 : qOneValue q r) : qOneValue p r := by
  refine BPair.scale_cancel (w := q.2) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.scale_comm p.1 r.2 q.2)) ?_
  refine BPair.oneValue_trans (BPair.scale_congr r.2 h1) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.scale_comm q.1 p.2 r.2)) ?_
  refine BPair.oneValue_trans (BPair.scale_congr p.2 h2) ?_
  exact BPair.oneValue_of_eq (BPair.scale_comm r.1 q.2 p.2)

/-- Equal cleared data read one value. -/
theorem qOneValue_of_eq {p q : BPair × Pos} (h : p = q) :
    qOneValue p q := by
  rw [h]
  exact qOneValue_refl q

/-- The cleared join commutes. -/
theorem BPair.addQ_comm (p q : BPair × Pos) :
    qOneValue (BPair.addQ p q) (BPair.addQ q p) := by
  show ((p.1.scale q.2 + q.1.scale p.2).scale (q.2 * p.2)).oneValue
    ((q.1.scale p.2 + p.1.scale q.2).scale (p.2 * q.2))
  rw [BPair.add_comm (q.1.scale p.2), ground.mul_comm q.2 p.2]
  exact BPair.oneValue_refl _

/-- The cleared join reassociates. -/
theorem BPair.addQ_assoc (p q r : BPair × Pos) :
    qOneValue (BPair.addQ (BPair.addQ p q) r)
      (BPair.addQ p (BPair.addQ q r)) := by
  refine qOneValue_of_eq ?_
  show ((p.1.scale q.2 + q.1.scale p.2).scale r.2 + r.1.scale (p.2 * q.2),
      p.2 * q.2 * r.2)
    = (p.1.scale (q.2 * r.2) + (q.1.scale r.2 + r.1.scale q.2).scale p.2,
      p.2 * (q.2 * r.2))
  rw [BPair.scale_add, BPair.scale_add, BPair.scale_scale,
    BPair.scale_scale, BPair.scale_scale, BPair.scale_scale,
    ground.mul_comm r.2 p.2, ground.mul_comm q.2 p.2, BPair.add_assoc,
    ground.mul_assoc]

/-- The cleared join reads congruently in both summands. -/
theorem BPair.addQ_congr {p p' q q' : BPair × Pos} (hp : qOneValue p p')
    (hq : qOneValue q q') :
    qOneValue (BPair.addQ p q) (BPair.addQ p' q') := by
  show ((p.1.scale q.2 + q.1.scale p.2).scale (p'.2 * q'.2)).oneValue
    ((p'.1.scale q'.2 + q'.1.scale p'.2).scale (p.2 * q.2))
  rw [BPair.scale_add, BPair.scale_add]
  refine BPair.add_congr ?_ ?_
  · have e1 : (p.1.scale q.2).scale (p'.2 * q'.2)
        = (p.1.scale p'.2).scale (q.2 * q'.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_left_comm q.2 p'.2 q'.2]
    have e2 : (p'.1.scale q'.2).scale (p.2 * q.2)
        = (p'.1.scale p.2).scale (q.2 * q'.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_left_comm q'.2 p.2 q.2, ground.mul_comm q'.2 q.2]
    exact BPair.oneValue_trans (BPair.oneValue_of_eq e1)
      (BPair.oneValue_trans (BPair.scale_congr _ hp)
        (BPair.oneValue_of_eq e2.symm))
  · have e3 : (q.1.scale p.2).scale (p'.2 * q'.2)
        = (q.1.scale q'.2).scale (p.2 * p'.2) := by
      rw [BPair.scale_scale, BPair.scale_scale, ground.mul_comm p'.2 q'.2,
        ground.mul_left_comm p.2 q'.2 p'.2]
    have e4 : (q'.1.scale p'.2).scale (p.2 * q.2)
        = (q'.1.scale q.2).scale (p.2 * p'.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_left_comm p'.2 p.2 q.2, ground.mul_comm p'.2 q.2,
        ground.mul_left_comm p.2 q.2 p'.2]
    exact BPair.oneValue_trans (BPair.oneValue_of_eq e3)
      (BPair.oneValue_trans (BPair.scale_congr _ hq)
        (BPair.oneValue_of_eq e4.symm))

/-- The cleared join exchanges its two middle summands. -/
theorem BPair.addQ_add_comm (a b c d : BPair × Pos) :
    qOneValue (BPair.addQ (BPair.addQ a b) (BPair.addQ c d))
      (BPair.addQ (BPair.addQ a c) (BPair.addQ b d)) := by
  refine qOneValue_trans (BPair.addQ_assoc a b (BPair.addQ c d)) ?_
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl a)
    (qOneValue_trans (qOneValue_symm (BPair.addQ_assoc b c d))
      (qOneValue_trans
        (BPair.addQ_congr (BPair.addQ_comm b c) (qOneValue_refl d))
        (BPair.addQ_assoc c b d)))) ?_
  exact qOneValue_symm (BPair.addQ_assoc a c (BPair.addQ b d))

/-- A cleared datum whose first member reads the sum's unit reads
the vacant datum. -/
theorem qOneValue_unit {p : BPair × Pos} (h : p.1.oneValue BPair.unit) :
    qOneValue p (BPair.unit, Pos.one) := by
  show (p.1.scale Pos.one).oneValue (BPair.unit.scale p.2)
  rw [BPair.scale_one]
  exact BPair.oneValue_trans h (BPair.oneValue_symm (BPair.unit_scale p.2))

/-- The vacant datum withdraws from the join's first summand. -/
theorem BPair.addQ_unitL (p : BPair × Pos) :
    qOneValue (BPair.addQ (BPair.unit, Pos.one) p) p := by
  show ((BPair.unit.scale p.2 + p.1.scale Pos.one).scale p.2).oneValue
    (p.1.scale (Pos.one * p.2))
  rw [BPair.scale_one, ground.one_mul]
  exact BPair.scale_congr p.2
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_scale p.2) (BPair.oneValue_refl p.1))
      (BPair.unit_add p.1))

/-- The vacant datum withdraws from the join's second summand. -/
theorem BPair.addQ_unitR (p : BPair × Pos) :
    qOneValue (BPair.addQ p (BPair.unit, Pos.one)) p :=
  qOneValue_trans (BPair.addQ_comm p (BPair.unit, Pos.one))
    (BPair.addQ_unitL p)

/-- A seed joined to three joined pairs parts as the seed with the
first two pairs' first members, against the last pair's first member
joined to the three second members. -/
theorem BPair.addQ_shuffle (S R0 RT C0 CT D0 DT : BPair × Pos) :
    qOneValue (BPair.addQ S (BPair.addQ (BPair.addQ R0 RT)
          (BPair.addQ (BPair.addQ C0 CT) (BPair.addQ D0 DT))))
      (BPair.addQ (BPair.addQ S (BPair.addQ R0 C0))
        (BPair.addQ D0 (BPair.addQ RT (BPair.addQ CT DT)))) := by
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl S)
    (qOneValue_trans (BPair.addQ_congr (qOneValue_refl (BPair.addQ R0 RT))
        (BPair.addQ_add_comm C0 CT D0 DT))
      (BPair.addQ_add_comm R0 RT (BPair.addQ C0 D0)
        (BPair.addQ CT DT)))) ?_
  refine qOneValue_trans (qOneValue_symm
    (BPair.addQ_assoc S (BPair.addQ R0 (BPair.addQ C0 D0))
      (BPair.addQ RT (BPair.addQ CT DT)))) ?_
  refine qOneValue_trans (BPair.addQ_congr
    (qOneValue_trans
      (BPair.addQ_congr (qOneValue_refl S)
        (qOneValue_symm (BPair.addQ_assoc R0 C0 D0)))
      (qOneValue_symm (BPair.addQ_assoc S (BPair.addQ R0 C0) D0)))
    (qOneValue_refl (BPair.addQ RT (BPair.addQ CT DT)))) ?_
  exact BPair.addQ_assoc (BPair.addQ S (BPair.addQ R0 C0)) D0
    (BPair.addQ RT (BPair.addQ CT DT))

/-! The matched-list read: `def:ground`'s componentwise pairing of
matched lists at a stated entry read — two lists read the relation
exactly where every coordinate pair does and the key lists agree —
with the kit reading the entry relation's laws as hypotheses, each
carrier supplying its own. -/

/-- Two matched lists read an entry relation componentwise, the
members related exactly where every coordinate's are and the key
lists sharing their count. -/
def matchedOV {γ : Type} (R : DRead γ) : List γ → List γ → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | x :: a, y :: b => R.rel x y ∧ matchedOV R a b

def decMatchedOV {γ : Type} (R : DRead γ) :
    ∀ a b : List γ, Decidable (matchedOV R a b)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: a, _ :: b =>
    @instDecidableAnd _ _ (R.dec _ _) (decMatchedOV R a b)

instance instGround40 {γ : Type} (R : DRead γ) (a b : List γ) :
    Decidable (matchedOV R a b) := decMatchedOV R a b

/-- The matched read's own bundle, the tower's iterating step. -/
def matchedRead {γ : Type} (R : DRead γ) : DRead (List γ) :=
  ⟨matchedOV R, decMatchedOV R⟩

/-- Two matched lists share their key count. -/
theorem matched_length {γ : Type} {R : DRead γ} : ∀ {a b : List γ},
    matchedOV R a b → a.length = b.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => congrArg Nat.succ (matched_length h.2)

/-- The matched read at one list, the entry read's own reflexivity
lifted. -/
theorem matched_refl {γ : Type} {R : DRead γ}
    (hr : ∀ x, R.rel x x) : ∀ l : List γ, matchedOV R l l
  | [] => trivial
  | x :: t => ⟨hr x, matched_refl hr t⟩

/-- The matched read exchanges its members where the entry read
does. -/
theorem matched_symm {γ : Type} {R : DRead γ}
    (hs : ∀ {x y : γ}, R.rel x y → R.rel y x) :
    ∀ {a b : List γ}, matchedOV R a b → matchedOV R b a
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => ⟨hs h.1, matched_symm hs h.2⟩

/-- The matched read composes where the entry read does. -/
theorem matched_trans {γ : Type} {R : DRead γ}
    (ht : ∀ {x y z : γ}, R.rel x y → R.rel y z → R.rel x z) :
    ∀ {a b c : List γ}, matchedOV R a b → matchedOV R b c →
    matchedOV R a c
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h2 => h2.elim
  | [], _ :: _, _, h1, _ => h1.elim
  | _ :: _, [], _, h1, _ => h1.elim
  | _ :: _, _ :: _, [], _, h2 => h2.elim
  | _ :: _, _ :: _, _ :: _, h1, h2 =>
    ⟨ht h1.1 h2.1, matched_trans ht h1.2 h2.2⟩

/-- The matched read's key read below the count. -/
theorem matched_entry {γ : Type} {R : DRead γ} (d : γ) :
    ∀ {a b : List γ}, matchedOV R a b →
    ∀ i, i < a.length → R.rel (getAt d a i) (getAt d b i)
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: _, _ :: _, h, i + 1, hi =>
    matched_entry d h.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The matched read's key read at every key, the default's own
read at the keys beyond the count. -/
theorem matched_entryAll {γ : Type} {R : DRead γ} {d : γ}
    (hd : R.rel d d) :
    ∀ {a b : List γ}, matchedOV R a b →
    ∀ i, R.rel (getAt d a i) (getAt d b i)
  | [], [], _, _ => hd
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | _ :: _, _ :: _, h, 0 => h.1
  | _ :: _, _ :: _, h, i + 1 => matched_entryAll hd h.2 i

/-- The count with every below-count key read assembles the matched
read, the converse. -/
theorem matched_ofGetAt {γ : Type} {R : DRead γ} (d : γ) :
    ∀ {a b : List γ}, a.length = b.length →
    (∀ i, i < a.length → R.rel (getAt d a i) (getAt d b i)) →
    matchedOV R a b
  | [], [], _, _ => trivial
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | _ :: _, _ :: _, hl, h =>
    ⟨h 0 (Nat.succ_pos _),
     matched_ofGetAt d (Nat.succ.inj hl)
       (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))⟩

/-- Two pointwise related maps read matched over any index family. -/
theorem matched_map {α γ : Type} {R : DRead γ} (f g : α → γ)
    (h : ∀ x, R.rel (f x) (g x)) : ∀ l : List α,
    matchedOV R (l.map f) (l.map g)
  | [] => trivial
  | x :: t => ⟨h x, matched_map f g h t⟩

/-- The factorial, the product of the naturals from one to the
argument, one at the vacant argument. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n


/-- The factorial is occupied. -/
theorem factorial_pos : ∀ n : Nat, 0 < factorial n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (factorial_pos n)

/-- The factorial's accumulating product over successor keys. -/
theorem factorial_foldl : ∀ n : Nat,
    (List.range n).foldl (fun a k => a * (k + 1)) 1 = factorial n
  | 0 => rfl
  | n + 1 => by
    rw [range_succ, foldl_append]
    change (List.range n).foldl (fun a k => a * (k + 1)) 1 * (n + 1)
      = (n + 1) * factorial n
    rw [factorial_foldl n, Nat.mul_comm]

/-- The factorial at a joined key against the head's: the raised key's
factorial sits at or below the joined key's power at the shift against
the head's factorial, each step's factor at or below the top. -/
theorem factorial_add_le (k : Nat) : ∀ j : Nat, factorial (k + j) ≤ (k + j) ^ j * factorial k
  | 0 => by
    show factorial (k + 0) ≤ (k + 0) ^ 0 * factorial k
    rw [Nat.pow_zero, Nat.one_mul]
    exact Nat.le_refl _
  | j + 1 => by
    show (k + j + 1) * factorial (k + j) ≤ (k + (j + 1)) ^ (j + 1) * factorial k
    rw [← Nat.add_assoc k j 1, Nat.pow_succ, Nat.mul_comm ((k + j + 1) ^ j) (k + j + 1),
      mulAssoc (k + j + 1) ((k + j + 1) ^ j) (factorial k)]
    refine Nat.mul_le_mul_left (k + j + 1) (Nat.le_trans (factorial_add_le k j) ?_)
    exact Nat.mul_le_mul_right (factorial k) (Nat.pow_le_pow_left (Nat.le_succ (k + j)) j)

/-- The falling product at a natural and a key, the product of the
natural's predecessors down over the key's many steps,
`n (n − 1) ⋯ (n − j + 1)`, the sum's unit at a key beyond the natural. -/
def ffall (n : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => (n - j) * ffall n j

/-- A key beyond the natural reads the sum's unit. -/
theorem ffall_beyond (n : Nat) : ∀ j : Nat, n < j → ffall n j = 0
  | 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, h => by
    show (n - j) * ffall n j = 0
    rw [subLe n j (Nat.le_of_lt_succ h), Nat.zero_mul]

/-- The raised natural's raised key reads the natural's successor
against the natural's product at the key. -/
theorem ffall_succ (n : Nat) : ∀ j : Nat, ffall (n + 1) (j + 1) = (n + 1) * ffall n j
  | 0 => rfl
  | j + 1 => by
    show (n + 1 - (j + 1)) * ffall (n + 1) (j + 1) = (n + 1) * ((n - j) * ffall n j)
    rw [Nat.succ_sub_succ, ffall_succ n j, mulLeftComm]

/-- The key's factorial against the Pascal count reads the falling
product, one identity per height and key: the raised height's read at
the definition's step, the raised key's own step joined. -/
theorem factorial_pasc : ∀ n j : Nat, factorial j * pasc n j = ffall n j
  | 0, 0 => rfl
  | 0, j + 1 => by
    show factorial (j + 1) * 0 = (0 - j) * ffall 0 j
    rw [Nat.mul_zero, Nat.zero_sub, Nat.zero_mul]
  | n + 1, 0 => rfl
  | n + 1, j + 1 => by
    show factorial (j + 1) * (pasc n j + pasc n (j + 1)) = ffall (n + 1) (j + 1)
    rw [Nat.mul_add, factorial_pasc n (j + 1), ffall_succ]
    show (j + 1) * factorial j * pasc n j + (n - j) * ffall n j = (n + 1) * ffall n j
    rw [mulAssoc (j + 1) (factorial j) (pasc n j), factorial_pasc n j, ← mulAddR]
    match Nat.lt_or_ge n j with
    | .inl h => rw [ffall_beyond n j h, Nat.mul_zero, Nat.mul_zero]
    | .inr h => rw [Nat.add_right_comm j 1 (n - j), natAddSubCancel h]

/-- The falling product against the withdrawn key's factorial reads the
natural's factorial, `n (n − 1) ⋯ (m + 1) · m! = n!` at the join
`n = k + m`, one raised factor per step. -/
theorem ffall_factorial : ∀ k m : Nat, ffall (k + m) k * factorial m = factorial (k + m)
  | 0, m => by
    show 1 * factorial m = factorial (0 + m)
    rw [Nat.one_mul, Nat.zero_add]
  | k + 1, m => by
    have hx : k + 1 + m = k + (m + 1) := by
      rw [Nat.add_right_comm k 1 m, Nat.add_assoc k m 1]
    show (k + 1 + m - k) * ffall (k + 1 + m) k * factorial m = factorial (k + 1 + m)
    rw [hx, addSubSelfL k (m + 1), Nat.mul_comm (m + 1) (ffall (k + (m + 1)) k), mulAssoc]
    show ffall (k + (m + 1)) k * factorial (m + 1) = factorial (k + (m + 1))
    exact ffall_factorial k (m + 1)

/-- The falling products' comparison at a key at or below two naturals
in order: the lower natural's power against the higher's falling
product sits at or below the higher's power against the lower's, one
termwise read per step, `n (j − i) ≤ j (n − i)`. -/
theorem ffall_pow (n j : Nat) (hj : j ≤ n) :
    ∀ i : Nat, i ≤ j → n ^ i * ffall j i ≤ j ^ i * ffall n i
  | 0, _ => Nat.le_refl _
  | i + 1, hi => by
    show n ^ (i + 1) * ((j - i) * ffall j i) ≤ j ^ (i + 1) * ((n - i) * ffall n i)
    have hij : i ≤ j := Nat.le_of_succ_le hi
    have hterm : n * (j - i) ≤ j * (n - i) := by
      have e1 : n * (j - i) + n * i = n * j := by
        rw [← Nat.mul_add, Nat.add_comm (j - i) i, natAddSubCancel hij]
      have e2 : j * (n - i) + j * i = j * n := by
        rw [← Nat.mul_add, Nat.add_comm (n - i) i, natAddSubCancel (Nat.le_trans hij hj)]
      refine leCancelR (n * i) ?_
      rw [e1, Nat.mul_comm n j, ← e2]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right i hj) _
    have ih := ffall_pow n j hj i hij
    rw [Nat.pow_succ, Nat.pow_succ]
    rw [Nat.mul_comm (n ^ i) n, mulMulMulComm n (n ^ i) (j - i) (ffall j i),
      Nat.mul_comm (j ^ i) j, mulMulMulComm j (j ^ i) (n - i) (ffall n i)]
    exact Nat.mul_le_mul hterm ih

/-- The Pascal count against the key's own power clears the height's
power, `n^j ≤ j^j C(n, j)` at a key at or below the height, the
falling products' comparison at the key against the factorial. -/
theorem pasc_pow (n j : Nat) (hj : j ≤ n) : n ^ j ≤ j ^ j * pasc n j := by
  have h := ffall_pow n j hj j (Nat.le_refl j)
  rw [← factorial_pasc j j, pasc_self j, Nat.mul_one, ← factorial_pasc n j,
    Nat.mul_comm (j ^ j) (factorial j * pasc n j), mulAssoc (factorial j) (pasc n j) (j ^ j),
    Nat.mul_comm (n ^ j) (factorial j)] at h
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans h (Nat.le_of_eq (by
    rw [Nat.mul_comm (pasc n j) (j ^ j)]))) (factorial_pos j)

/-- The Pascal count's fast read: the falling product's quotient at the
key's factorial, the division's read at `factorial_pasc`'s identity, one
product of the key's many steps where the count's own recursion joins
two counts per height. -/
def pascD (n j : Nat) : Nat := ffall n j / factorial j

/-- The fast read is the Pascal count: the factorial's multiple of the
count divides back to the count at the occupied factorial. -/
theorem pascD_eq (n j : Nat) : pascD n j = pasc n j := by
  show ffall n j / factorial j = pasc n j
  rw [← factorial_pasc n j, Nat.mul_comm (factorial j) (pasc n j)]
  exact divMulSelf (pasc n j) (factorial j) (factorial_pos j)

/-- A nonempty list splits at its last member, the prefix at the
tail's length. -/
private theorem snoc_of_cons {α : Type} : ∀ (a : α) (t : List α),
    ∃ l' x, a :: t = l' ++ [x] ∧ l'.length = t.length
  | a, [] => ⟨[], a, rfl, rfl⟩
  | a, b :: t =>
    match snoc_of_cons b t with
    | ⟨l', x, he, hl⟩ =>
      ⟨a :: l', x, congrArg (List.cons a) he, congrArg Nat.succ hl⟩

/-- A list of a successor length splits at its last member, the
prefix at the predecessor length. -/
theorem snoc_split {α : Type} (k : Nat) : ∀ l : List α,
    l.length = k + 1 → ∃ l' x, l = l' ++ [x] ∧ l'.length = k
  | [], h => Nat.noConfusion h
  | a :: t, h =>
    match snoc_of_cons a t with
    | ⟨l', x, he, hl⟩ => ⟨l', x, he, hl.trans (Nat.succ.inj h)⟩

/-- The reversal moves a last member to the head. -/
theorem reverse_snoc {α : Type} (w : List α) (a : α) :
    (w ++ [a]).reverse = a :: w.reverse := by
  rw [reverse_append w [a]]
  rfl

/-- Two lists at one appended member agree exactly at their
prefixes: the append's last member reads off and the prefixes
follow. -/
theorem snoc_inj {α : Type} : ∀ (l l' : List α) (a : α),
    l ++ [a] = l' ++ [a] → l = l'
  | [], [], _, _ => rfl
  | [], b :: t, a, h =>
    have h2 : [] = t ++ [a] := (List.cons.inj h).2
    nomatch ((congrArg List.length h2).trans (length_append t [a]))
  | b :: t, [], a, h =>
    have h2 : t ++ [a] = [] := (List.cons.inj h).2
    nomatch ((congrArg List.length h2).symm.trans (length_append t [a]))
  | b :: t, c :: t', a, h => by
    have h1 := (List.cons.inj h).1
    have h2 := snoc_inj t t' a (List.cons.inj h).2
    rw [h1, h2]

/-- The vacant list is absent from a family of appended lists. -/
theorem countOf_nil_snocMap {α : Type} [DecidableEq α] (a : α) :
    ∀ l : List (List α),
      countOf ([] : List α) (l.map (fun t => t ++ [a])) = 0
  | [] => rfl
  | b :: l => by
    show countOf ([] : List α)
      ((b ++ [a]) :: l.map (fun t => t ++ [a])) = 0
    rw [countOf_cons,
      if_neg (fun hc : ([] : List α) = b ++ [a] =>
        nomatch ((congrArg List.length hc).trans (length_append b [a]))),
      countOf_nil_snocMap a l]

/-- Two appended lists of one value share their last member. -/
private theorem last_of_snoc_eq {α : Type} : ∀ (s c : List α) (a b : α),
    s ++ [a] = c ++ [b] → a = b
  | [], [], _, _, h => (List.cons.inj h).1
  | [], _ :: c, _, b, h =>
    have h2 : [] = c ++ [b] := (List.cons.inj h).2
    nomatch ((congrArg List.length h2).trans (length_append c [b]))
  | _ :: s, [], a, _, h =>
    have h2 : s ++ [a] = [] := (List.cons.inj h).2
    nomatch ((congrArg List.length h2).symm.trans (length_append s [a]))
  | _ :: s, _ :: c, a, b, h => last_of_snoc_eq s c a b (List.cons.inj h).2

/-- A list appended at one member is absent from a family appended
at a different member. -/
theorem countOf_snocMap_ne {α : Type} [DecidableEq α] (s : List α)
    (a b : α) (hab : ¬ b = a) :
    ∀ l : List (List α),
      countOf (s ++ [a]) (l.map (fun t => t ++ [b])) = 0
  | [] => rfl
  | c :: l => by
    show countOf (s ++ [a]) ((c ++ [b]) :: l.map (fun t => t ++ [b])) = 0
    rw [countOf_cons, if_neg (fun hc : s ++ [a] = c ++ [b] => hab ?_),
      countOf_snocMap_ne s a b hab l]
    exact (last_of_snoc_eq s c a b hc).symm

/-- A member's read sits at or below the family's fold. -/
theorem famFold_mem_le {α : Type} (f : α → Nat) :
    ∀ (l : List α) (x : α), x ∈ l →
      f x ≤ famFold Nat.add 0 f l
  | [], _, h => nomatch h
  | a :: t, x, h => by
    show f x ≤ f a + famFold Nat.add 0 f t
    match h with
    | .head _ => exact Nat.le_add_right _ _
    | .tail _ ht =>
      exact Nat.le_trans (famFold_mem_le f t x ht)
        (Nat.le_add_left _ (f a))

/-- Two members' reads at distinct places sit at or below the
family's fold. -/
theorem famFold_two_le {α : Type} (f : α → Nat) (d : α) :
    ∀ (l : List α) (i j : Nat), i < j → j < l.length →
      f (getAt d l i) + f (getAt d l j) ≤ famFold Nat.add 0 f l
  | [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | c :: l, 0, j + 1, _, hj => by
    show f c + f (getAt d l j) ≤ f c + famFold Nat.add 0 f l
    exact Nat.add_le_add_left
      (famFold_mem_le f l _ (mem_getAt d l j (Nat.lt_of_succ_lt_succ hj))) _
  | c :: l, i + 1, j + 1, hij, hj => by
    show f (getAt d l i) + f (getAt d l j) ≤ f c + famFold Nat.add 0 f l
    exact Nat.le_trans (famFold_two_le f d l i j (Nat.lt_of_succ_lt_succ hij)
      (Nat.lt_of_succ_lt_succ hj)) (Nat.le_add_left _ _)
  | _ :: _, _ + 1, 0, hij, _ => absurd hij (Nat.not_lt_zero _)


/-- A pointwise bound passes through the fold. -/
theorem famFold_le {α : Type} (F G : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, F x ≤ G x) →
      famFold Nat.add 0 F l ≤ famFold Nat.add 0 G l
  | [], _ => Nat.le_refl 0
  | a :: t, h => by
    show F a + famFold Nat.add 0 F t
      ≤ G a + famFold Nat.add 0 G t
    exact Nat.add_le_add (h a (List.Mem.head t))
      (famFold_le F G t (fun x hx => h x (List.Mem.tail a hx)))

/-- Two families agreeing at every member of a list fold to one
value over it. -/
theorem famFold_congr_mem {α β : Type} (add : β → β → β) (unit : β)
    (f g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) →
      famFold add unit f l = famFold add unit g l
  | [], _ => rfl
  | a :: t, h => by
    show add (f a) (famFold add unit f t)
      = add (g a) (famFold add unit g t)
    rw [h a (List.Mem.head t),
      famFold_congr_mem add unit f g t (fun x hx => h x (List.Mem.tail a hx))]

/-- The pigeonhole at a distinct host: a distinct family within a
distinct member list is no longer than the list. -/
theorem length_le_of_distinct_mem {α : Type} [DecidableEq α]
    (l D : List α)
    (hdist : ∀ x, ground.countOf x l ≤ 1)
    (hcov : ∀ x ∈ l, x ∈ D) (hD : distinctList D) :
    l.length ≤ D.length := by
  rw [← ground.countOf_partition l D hD hcov]
  refine Nat.le_trans
    (ground.famFold_le _ (fun _ => (1 : Nat)) D
      (fun x _ => hdist x)) ?_
  rw [famFold_length D]
  exact Nat.le_refl D.length

/-- The pigeonhole at the key range: a distinct family within the
alphabet is no longer than the alphabet, the distinct-host read at
the range. -/
theorem length_le_of_distinct (l : List Nat) (n : Nat)
    (hdist : ∀ x, ground.countOf x l ≤ 1)
    (hlt : ∀ x, 0 < ground.countOf x l → x < n) :
    l.length ≤ n := by
  refine Nat.le_trans
    (length_le_of_distinct_mem l (List.range n) hdist
      (fun x hx => memRange (hlt x (countOf_pos_of_mem hx)))
      (distinctList_range n)) ?_
  rw [ground.length_range]
  exact Nat.le_refl n

/-- A self-map of the key range with a left witness has it as a
right witness, the pigeonhole at the range: the images are distinct
and within the range, so every key is an image at the witness's
pre-image. -/
theorem rightInv_of_leftInv (n : Nat) (t s : Nat → Nat)
    (h : ∀ l, l < n → t l < n ∧ s (t l) = l) :
    ∀ l, l < n → s l < n ∧ t (s l) = l := by
  intro l hl
  have hdist : distinctList ((List.range n).map t) := by
    refine distinct_of_getAt_inj 0 _ (fun p q hp hq heq => ?_)
    rw [length_map, length_range] at hp hq
    rw [getAt_map_range 0 t n p, if_pos hp, getAt_map_range 0 t n q, if_pos hq] at heq
    rw [← (h p hp).2, ← (h q hq).2, heq]
  have hmem : l ∈ (List.range n).map t := by
    match Nat.eq_zero_or_pos (countOf l ((List.range n).map t)) with
    | .inr hpos => exact mem_of_countOf_pos l _ hpos
    | .inl hz =>
      have hd2 : ∀ x, countOf x (l :: (List.range n).map t) ≤ 1 := by
        intro x
        rw [countOf_cons]
        by_cases hx : x = l
        · rw [if_pos hx, hx, hz]
          exact Nat.le_refl 1
        · rw [if_neg hx, Nat.zero_add]
          exact distinctList_all hdist x
      have hle := length_le_of_distinct_mem (l :: (List.range n).map t)
        (List.range n) hd2 (fun x hx => ?_) (distinctList_range n)
      · have hle' : n + 1 ≤ n := by
          rw [List.length_cons, length_map, length_range] at hle
          exact hle
        exact absurd hle' (Nat.not_succ_le_self n)
      · cases hx with
        | head => exact memRange hl
        | tail _ hx' =>
          obtain ⟨p, hp, hpx⟩ := mem_map_of t _ x hx'
          rw [← hpx]
          exact memRange (h p (ltOfMemRange hp)).1
  obtain ⟨p, hp, hpl⟩ := mem_map_of t _ l hmem
  have hpn : p < n := ltOfMemRange hp
  rw [← hpl, (h p hpn).2]
  exact ⟨hpn, rfl⟩

/-- A family's entry past the head is the tail family's own. -/
theorem getAt_tail {α : Type} (d : α) :
    ∀ (l : List α) (k : Nat), getAt d l (k + 1) = getAt d l.tail k
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- The first member sits at or below the pair's larger, the
trichotomy's own read at the guarded larger. -/
theorem le_max_left (n m : Nat) : n ≤ Nat.max n m := by
  show n ≤ if n ≤ m then m else n
  by_cases h : n ≤ m
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Nat.le_refl n

/-- The second member sits at or below the pair's larger. -/
theorem le_max_right (n m : Nat) : m ≤ Nat.max n m := by
  show m ≤ if n ≤ m then m else n
  by_cases h : n ≤ m
  · rw [if_pos h]; exact Nat.le_refl m
  · rw [if_neg h]; exact Nat.le_of_not_le h

/-- The larger of two members sits at or below a shared cap. -/
theorem max_le {n m k : Nat} (hn : n ≤ k) (hm : m ≤ k) : Nat.max n m ≤ k := by
  show (if n ≤ m then m else n) ≤ k
  by_cases h : n ≤ m
  · rw [if_pos h]; exact hm
  · rw [if_neg h]; exact hn

/-- A largest-member fold sits at or beyond its seed. -/
theorem foldMax_seed {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat), a ≤ l.foldl (fun b x => Nat.max b (f x)) a
  | [], a => Nat.le_refl a
  | x :: t, a => Nat.le_trans (le_max_left a (f x)) (foldMax_seed f t _)

/-- A largest-member fold sits at or beyond every member's read. -/
theorem foldMax_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat) (x : α), x ∈ l →
      f x ≤ l.foldl (fun b y => Nat.max b (f y)) a
  | [], _, _, h => nomatch h
  | y :: t, a, x, h => by
    cases h with
    | head => exact Nat.le_trans (le_max_right a _) (foldMax_seed f t _)
    | tail _ hm => exact foldMax_mem f t _ x hm

/-- A common upper bound on the seed and all member reads bounds
the maximum fold. -/
theorem foldMax_le {α : Type} (f : α → Nat) (l : List α) (a cap : Nat)
    (ha : a ≤ cap) (hl : ∀ x ∈ l, f x ≤ cap) :
    l.foldl (fun b x => Nat.max b (f x)) a ≤ cap :=
  foldl_invariant (fun b => b ≤ cap) _ l a ha
    (fun x hx _ hb => max_le hb (hl x hx))

/-- A positive strict bound on every member bounds the
maximum fold seeded at the sum's unit. -/
theorem foldMax_lt {α : Type} (f : α → Nat) (l : List α) (cap : Nat)
    (hc : 0 < cap) (hl : ∀ x ∈ l, f x < cap) :
    l.foldl (fun b x => Nat.max b (f x)) 0 < cap := by
  apply foldl_invariant (fun b => b < cap) _ l 0 hc
  intro x hx b hb
  change (if b ≤ f x then f x else b) < cap
  by_cases h : b ≤ f x
  · rw [if_pos h]; exact hl x hx
  · rw [if_neg h]; exact hb

/-- An occupied largest-member fold names an occupied member. -/
theorem foldMax_pos {α : Type} (f : α → Nat) :
    ∀ (l : List α), 0 < l.foldl (fun b x => Nat.max b (f x)) 0 → ∃ x, x ∈ l ∧ 0 < f x
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: t, h => by
    cases Nat.eq_zero_or_pos (f a) with
    | inr hp => exact ⟨a, List.Mem.head t, hp⟩
    | inl hz =>
      have h' : 0 < t.foldl (fun b x => Nat.max b (f x)) 0 := by
        have hh : 0 < t.foldl (fun b x => Nat.max b (f x)) (Nat.max 0 (f a)) := h
        rw [hz] at hh
        exact hh
      obtain ⟨x, hx, hfx⟩ := foldMax_pos f t h'
      exact ⟨x, List.Mem.tail a hx, hfx⟩

/-- A member's count at a grown family splits at the new key. -/
theorem countOf_snoc {α : Type} [DecidableEq α]
    (x j : α) (seen : List α) :
    countOf x (seen ++ [j])
      = countOf x seen + (if x = j then 1 else 0) := by
  rw [countOf_append x seen [j], countOf_cons x j ([] : List α)]
  show countOf x seen + ((if x = j then 1 else 0) + 0) = _
  rw [Nat.add_zero]

/-- A left member joins the joined family. -/
theorem countOf_append_left {α : Type} [DecidableEq α]
    (x : α) {u : List α} (v : List α)
    (h : 0 < countOf x u) :
    0 < countOf x (u ++ v) := by
  rw [countOf_append]
  exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)

/-- A right member joins the joined family. -/
theorem countOf_append_right {α : Type} [DecidableEq α]
    (x : α) (u : List α) {v : List α}
    (h : 0 < countOf x v) :
    0 < countOf x (u ++ v) := by
  rw [countOf_append]
  exact Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)

/-- An occupied join names an occupied side. -/
theorem countOf_append_split {α : Type} [DecidableEq α]
    (x : α) (u v : List α)
    (h : 0 < countOf x (u ++ v)) :
    0 < countOf x u ∨ 0 < countOf x v := by
  rw [countOf_append] at h
  match Nat.eq_zero_or_pos (countOf x u) with
  | .inr hp => exact Or.inl hp
  | .inl hz =>
    rw [hz, Nat.zero_add] at h
    exact Or.inr h

/-- A fresh key keeps the grown family distinct. -/
theorem snoc_distinct {α : Type} [DecidableEq α]
    {j : α} {seen : List α}
    (hsd : ∀ x, countOf x seen ≤ 1)
    (hjf : countOf j seen = 0) :
    ∀ x, countOf x (seen ++ [j]) ≤ 1 := by
  intro x
  rw [countOf_snoc]
  by_cases hxj : x = j
  · rw [if_pos hxj, hxj, hjf]
    exact Nat.le_refl 1
  · rw [if_neg hxj, Nat.add_zero]
    exact hsd x

/-- A bounded key keeps the grown family bounded. -/
theorem snoc_lt {j : Nat} {seen : List Nat} {k : Nat}
    (hsk : ∀ x, 0 < countOf x seen → x < k) (hj : j < k) :
    ∀ x, 0 < countOf x (seen ++ [j]) → x < k := by
  intro x hx
  rw [countOf_snoc] at hx
  by_cases hxj : x = j
  · rw [hxj]
    exact hj
  · rw [if_neg hxj, Nat.add_zero] at hx
    exact hsk x hx

/-- An occupied member keeps its family occupied. -/
theorem length_pos_of_countOf {α : Type} [DecidableEq α]
    {x : α} : ∀ {l : List α}, 0 < countOf x l → 0 < l.length
  | [], h => absurd h (Nat.lt_irrefl 0)
  | _ :: t, _ => Nat.succ_pos t.length

/-- The constant fold reads the scaled length. -/
theorem famFold_const {α : Type} (c : Nat) :
    ∀ l : List α,
      famFold Nat.add 0 (fun _ => c) l = l.length * c
  | [] => (Nat.zero_mul c).symm
  | _ :: t => by
    show c + famFold Nat.add 0 (fun _ => c) t = (t.length + 1) * c
    rw [famFold_const c t, Nat.succ_mul]
    exact Nat.add_comm c (t.length * c)

/-- An option read at a stated function, the vacant option at the
stated unit. -/
def optFold {β γ : Type} (unit : γ) (F : β → γ) : Option β → γ
  | none => unit
  | some y => F y

/-- A keyed value read at the sum's unit off the key. -/
def optVal {β : Type} (F : β → Nat) : Option β → Nat := optFold 0 F

/-- A keyed image's fold is the source family's fold at the keyed
value, the refused keys reading the sum's unit. -/
theorem famFold_filterMap {α β : Type} (f : α → Option β)
    (F : β → Nat) : ∀ l : List α,
      famFold Nat.add 0 F (l.filterMap f)
        = famFold Nat.add 0 (fun x => optVal F (f x)) l
  | [] => rfl
  | x :: t => by
    show famFold Nat.add 0 F
        (match f x with
         | none => t.filterMap f
         | some b => b :: t.filterMap f)
      = optVal F (f x)
        + famFold Nat.add 0 (fun z => optVal F (f z)) t
    cases hf : f x with
    | none =>
      show famFold Nat.add 0 F (t.filterMap f)
        = 0 + famFold Nat.add 0 (fun z => optVal F (f z)) t
      rw [Nat.zero_add]
      exact famFold_filterMap f F t
    | some y =>
      show F y + famFold Nat.add 0 F (t.filterMap f)
        = F y + famFold Nat.add 0 (fun z => optVal F (f z)) t
      rw [famFold_filterMap f F t]

/-- A keyed image's fold reads the source family's fold at the keyed
value with the refused keys at the unit, in every carrier with the
fold laws. -/
theorem famFold_filterMap_ov {α β γ : Type} {ov : γ → γ → Prop} {add : γ → γ → γ}
    {unit : γ} (L : FoldLaws γ add unit ov) (f : α → Option β) (F : β → γ) :
    ∀ l : List α, ov (famFold add unit F (l.filterMap f))
      (famFold add unit (fun x => optFold unit F (f x)) l)
  | [] => L.ovRefl _
  | x :: t => by
    show ov (famFold add unit F
        (match f x with
         | none => t.filterMap f
         | some b => b :: t.filterMap f))
      (add (optFold unit F (f x)) (famFold add unit (fun z => optFold unit F (f z)) t))
    cases hf : f x with
    | none =>
      show ov (famFold add unit F (t.filterMap f))
        (add unit (famFold add unit (fun z => optFold unit F (f z)) t))
      exact L.ovTrans (famFold_filterMap_ov L f F t) (L.ovSymm (L.unitOp _))
    | some y =>
      show ov (add (F y) (famFold add unit F (t.filterMap f)))
        (add (F y) (famFold add unit (fun z => optFold unit F (f z)) t))
      exact L.opCongr (L.ovRefl _) (famFold_filterMap_ov L f F t)

/-- Pointwise equal remainders give equal remainders of the folds. -/
theorem famFold_mod_congr {α : Type} (d : Nat) (f g : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, f x % d = g x % d) →
      famFold Nat.add 0 f l % d = famFold Nat.add 0 g l % d
  | [], _ => rfl
  | a :: l, h => by
    change (f a + famFold Nat.add 0 f l) % d = (g a + famFold Nat.add 0 g l) % d
    rw [← modAdd (f a) (famFold Nat.add 0 f l) d,
      ← modAdd (g a) (famFold Nat.add 0 g l) d, h a (List.Mem.head l),
      famFold_mod_congr d f g l (fun x hx => h x (List.Mem.tail a hx))]

/-- A family at every member the divisor's multiple folds to the
divisor's multiple. -/
theorem foldMod (n : Nat) {α : Type} (f : α → Nat) :
    ∀ l : List α, (∀ x, x ∈ l → f x % n = 0) →
      famFold Nat.add 0 f l % n = 0 := by
  intro l h
  rw [famFold_mod_congr n f (fun _ => 0) l
    (fun x hx => (h x hx).trans (modZeroLeft n).symm),
    famFold_zero (fun _ => 0) (fun _ => rfl), modZeroLeft]

/-- A guarded fold splits at a further read: the members meeting it
and those refusing it. -/
theorem splitGuard {α : Type} (p q : α → Bool) (w : α → Nat)
    (l : List α) :
    famFold Nat.add 0 (fun x => if q x then w x else 0) l
      = famFold Nat.add 0 (fun x => if p x && q x then w x else 0) l
        + famFold Nat.add 0
            (fun x => if !(p x) && q x then w x else 0) l := by
  rw [← famFold_add_split
      (fun x => if p x && q x then w x else 0)
      (fun x => if !(p x) && q x then w x else 0) l]
  refine famFold_congr_all Nat.add 0 _ _ (fun x => ?_) l
  cases hp : p x with
  | true =>
    cases hq : q x with
    | true => exact (Nat.add_zero (w x)).symm
    | false => rfl
  | false =>
    cases hq : q x with
    | true => exact (Nat.zero_add (w x)).symm
    | false => rfl

/-- A guarded fold of a pair splits into the pair's own folds. -/
theorem pairSplit {α : Type} (q : α → Bool) (w w' : α → Nat)
    (l : List α) :
    famFold Nat.add 0 (fun x => if q x then w x + w' x else 0) l
      = famFold Nat.add 0 (fun x => if q x then w x else 0) l
        + famFold Nat.add 0 (fun x => if q x then w' x else 0) l := by
  rw [← famFold_add_split
      (fun x => if q x then w x else 0)
      (fun x => if q x then w' x else 0) l]
  refine famFold_congr_all Nat.add 0 _ _ (fun x => ?_) l
  cases hq : q x with
  | true => rfl
  | false => rfl

/-- A guarded constant fold reads the guard's own count. -/
theorem guardFold_count {α : Type} (p : α → Bool) (w : Nat) :
    ∀ l : List α, famFold Nat.add 0 (fun x => if p x then w else 0) l
      = w * (l.filter p).length
  | [] => by
    show (0 : Nat) = w * 0
    rw [Nat.mul_zero]
  | x :: t => by
    have hIH := guardFold_count p w t
    show (if p x then w else 0)
        + famFold Nat.add 0 (fun y => if p y then w else 0) t
      = w * ((x :: t).filter p).length
    cases hp : p x with
    | true =>
      show w + famFold Nat.add 0 (fun y => if p y then w else 0) t
        = w * ((x :: t).filter p).length
      rw [filter_cons_true hp, hIH]
      show w + w * (t.filter p).length
        = w * ((t.filter p).length + 1)
      rw [Nat.mul_succ w (t.filter p).length,
        Nat.add_comm w (w * (t.filter p).length)]
    | false =>
      show (0 : Nat)
          + famFold Nat.add 0 (fun y => if p y then w else 0) t
        = w * ((x :: t).filter p).length
      rw [filter_cons_false hp, Nat.zero_add, hIH]

/-- A family grown at its end folds its new member on top. -/
theorem famFold_snoc {α : Type} (f : α → Nat) (K : List α) (x : α) :
    famFold Nat.add 0 f (K ++ [x])
      = famFold Nat.add 0 f K + f x := by
  rw [famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add f K [x]]
  show famFold Nat.add 0 f K + (f x + 0) = famFold Nat.add 0 f K + f x
  rw [Nat.add_zero]

/-- A key family vacant at every key below the count folds to the
sum's unit over the range. -/
theorem famFold_rangeZero (h : Nat → Nat) : ∀ L : Nat,
    (∀ x, x < L → h x = 0) →
    famFold Nat.add 0 h (List.range L) = 0 :=
  fun L hz => by
    rw [famFold_congr_members Nat.add 0 h (fun _ => (0 : Nat))
        (List.range L) (fun x hx => hz x (ltOfMem hx)),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (List.range L)]

/-- A key family at one at every key below the count folds to the
count over the range. -/
theorem famFold_rangeOne (h : Nat → Nat) (L : Nat)
    (hone : ∀ x, x < L → h x = 1) :
    famFold Nat.add 0 h (List.range L) = L := by
  rw [famFold_congr_members Nat.add 0 h (fun _ => (1 : Nat))
      (List.range L) (fun x hx => hone x (ltOfMem hx)),
    famFold_length (List.range L), length_range L]

/-- A range fold with a vacant middle window reads its two end
segments: the front's fold joined to the tail's, the middle's terms
at the sum's unit. -/
theorem famFold_splitMid (F : Nat → Nat) (a b c : Nat)
    (hmid : ∀ i, a ≤ i → i < a + b → F i = 0) :
    ground.famFold Nat.add 0 F (List.range (a + b + c))
      = ground.famFold Nat.add 0 F (List.range a)
        + ground.famFold Nat.add 0 (fun i => F (a + b + i))
            (List.range c) := by
  rw [range_split (a + b) c,
    famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
      (List.range (a + b)) ((List.range c).map (fun x => a + b + x)),
    famFold_map Nat.add 0 F (fun x => a + b + x) (List.range c),
    range_split a b,
    famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
      (List.range a) ((List.range b).map (fun x => a + x)),
    famFold_map Nat.add 0 F (fun x => a + x) (List.range b),
    famFold_rangeZero (fun x => F (a + x)) b
      (fun x hx => hmid (a + x) (Nat.le_add_right a x)
        (Nat.add_lt_add_left hx a))]
  show famFold Nat.add 0 F (List.range a) + 0
      + famFold Nat.add 0 (fun i => F (a + b + i)) (List.range c)
    = famFold Nat.add 0 F (List.range a)
      + famFold Nat.add 0 (fun i => F (a + b + i)) (List.range c)
  rw [Nat.add_zero]

/-- A family vacant at every member off one key occupied once folds
to that key's value. -/
theorem famFold_pick_of {α : Type} [DecidableEq α] (F : α → Nat)
    (c : α) (D : List α) (hc : countOf c D = 1)
    (hoff : ∀ y, 0 < countOf y D → ¬ y = c → F y = 0) :
    famFold Nat.add 0 F D = F c := by
  rw [famFold_congr_members Nat.add 0 F
      (fun w => if w = c then F w else 0) D
      (fun y hy => by
        by_cases hyc : y = c
        · rw [if_pos hyc]
        · rw [if_neg hyc, hoff y hy hyc])]
  exact famFold_pick F c D hc

/-- A longer key range folds at or above a shorter one. -/
theorem famFold_range_le (h : Nat → Nat) : ∀ N k : Nat,
    famFold Nat.add 0 h (List.range N)
      ≤ famFold Nat.add 0 h (List.range (N + k))
  | _, 0 => Nat.le_refl _
  | N, k + 1 => by
    rw [show N + (k + 1) = N + k + 1 from (Nat.add_assoc N k 1).symm,
      range_succ (N + k),
      famFold_snoc h (List.range (N + k)) (N + k)]
    exact Nat.le_trans (famFold_range_le h N k) (Nat.le_add_right _ _)

/-- Beyond a vanishing key the range's fold stands still. -/
theorem famFold_range_mono (h : Nat → Nat) (N : Nat)
    (hz : ∀ l, N ≤ l → h l = 0) : ∀ k : Nat,
    famFold Nat.add 0 h (List.range (N + k))
      = famFold Nat.add 0 h (List.range N)
  | 0 => rfl
  | k + 1 => by
    rw [show N + (k + 1) = N + k + 1 from (Nat.add_assoc N k 1).symm,
      range_succ (N + k),
      famFold_snoc h (List.range (N + k)) (N + k),
      hz (N + k) (Nat.le_add_right N k), Nat.add_zero]
    exact famFold_range_mono h N hz k

/-- A key range's fold is dominated by any range reaching the
family's vanishing key: past it the terms read the sum's unit, and
short of it the range's own members are fewer. -/
theorem famFold_range_dom (h : Nat → Nat) (N M : Nat)
    (hz : ∀ l, N ≤ l → h l = 0) :
    famFold Nat.add 0 h (List.range M)
      ≤ famFold Nat.add 0 h (List.range N) := by
  cases Nat.lt_or_ge M N with
  | inl hlt =>
    match Nat.le.dest (Nat.le_of_lt hlt) with
    | ⟨k, hk⟩ =>
      rw [← hk]
      exact famFold_range_le h M k
  | inr hge =>
    match Nat.le.dest hge with
    | ⟨k, hk⟩ =>
      rw [← hk]
      exact Nat.le_of_eq (famFold_range_mono h N hz k)

/-- The one-key collapse over a range: a family guarded at one key
below the count reads that key's value. -/
theorem famFold_pickBeqRange (T w L : Nat) (h : T < L) :
    famFold Nat.add 0 (fun x => if T == x then w else 0)
      (List.range L) = w := by
  rw [famFold_congr_all Nat.add 0
      (fun x => if T == x then w else 0)
      (fun x => w * (if T = x then 1 else 0))
      (fun x => by
        cases hb : (T == x) with
        | true =>
          show w = w * (if T = x then 1 else 0)
          rw [if_pos (beqEqOf hb), Nat.mul_one]
        | false =>
          show (0 : Nat) = w * (if T = x then 1 else 0)
          rw [if_neg (fun he => Bool.noConfusion
              (hb.symm.trans (eqBeqOf he))), Nat.mul_zero])
      (List.range L),
    ← famFold_mul w (fun x => if T = x then 1 else 0)
      (List.range L),
    ← countOf_fold T (List.range L), countOf_range_one h,
    Nat.mul_one]

/-- A raise at a lowered key keeps the family's total. -/
theorem sumNat_move (i j : Nat) (l : List Nat)
    (hi : 0 < getAt 0 l i) (hj : j < l.length) :
    sumNat (bumpAt j (dipAt i l)) = sumNat l := by
  have hjD : j < (dipAt i l).length := by
    rw [length_dipAt]
    exact hj
  exact (sumNat_bumpAt j (dipAt i l) hjD).trans (sumNat_dipAt i l hi)

/-- The raised occupancy at a split-off last member: the key at the
prefix's length reads the member's successor. -/
theorem bumpAt_snoc : ∀ (s : List Nat) (j : Nat),
    bumpAt s.length (s ++ [j]) = s ++ [j + 1]
  | [], _ => rfl
  | x :: t, j => by
    show x :: bumpAt t.length (t ++ [j]) = x :: (t ++ [j + 1])
    rw [bumpAt_snoc t j]

/-- A flattened family's length is the members' length fold. -/
theorem length_flatMap {α β : Type} (f : α → List β) :
    ∀ l : List α, (l.flatMap f).length
      = famFold Nat.add 0 (fun x => (f x).length) l
  | [] => rfl
  | a :: t => by
    show (f a ++ t.flatMap f).length = (f a).length + _
    rw [length_append, length_flatMap f t]

/-- The product lists over a family of domains: one list per
selection of a member from each domain, the first domain's member
at the head — `con:places`' monomial tensors at the factors' lists,
the enumeration blocking at the head factor. -/
def prodLists {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | D :: t => D.flatMap (fun x => (prodLists t).map (fun l => x :: l))

/-- The product lists' count is the domains' length product. -/
theorem length_prodLists {α : Type} :
    ∀ Ds : List (List α), (prodLists Ds).length = prodOver List.length Ds
  | [] => rfl
  | D :: t => by
    show (D.flatMap (fun x => (prodLists t).map (fun l => x :: l))).length
      = D.length * prodOver List.length t
    rw [length_flatMap, ← length_prodLists t,
      famFold_congr_all Nat.add 0 _ (fun _ => (prodLists t).length)
        (fun x => length_map _ _) D,
      famFold_const]

/-- A product list reads one member per domain, at the domains'
count. -/
theorem mem_prodLists_of {α : Type} (d : α) :
    ∀ (Ds : List (List α)) (l : List α), l ∈ prodLists Ds →
      l.length = Ds.length ∧ ∀ i, i < Ds.length → getAt d l i ∈ getAt [] Ds i
  | [], l, h => by
    rw [eq_of_mem_single (show l ∈ [([] : List α)] from h)]
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | D :: t, l, h => by
    obtain ⟨x, hx, hl⟩ := mem_flatMap_of _ D l h
    obtain ⟨m, hm, hml⟩ := mem_map_of _ _ l hl
    obtain ⟨hlen, hall⟩ := mem_prodLists_of d t m hm
    rw [← hml]
    refine ⟨congrArg Nat.succ hlen, fun i hi => ?_⟩
    cases i with
    | zero => exact hx
    | succ j => exact hall j (Nat.lt_of_succ_lt_succ hi)

/-- A list reading one member per domain at the domains' count is
a product list. -/
theorem mem_prodLists_to {α : Type} (d : α) :
    ∀ (Ds : List (List α)) (l : List α), l.length = Ds.length →
      (∀ i, i < Ds.length → getAt d l i ∈ getAt [] Ds i) → l ∈ prodLists Ds
  | [], [], _, _ => List.Mem.head _
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl
  | _ :: t, _ :: m, hl, hall =>
    mem_flatMap_to _ (hall 0 (Nat.succ_pos _))
      (mem_map_to _ (mem_prodLists_to d t m (Nat.succ.inj hl)
        (fun i hi => hall (i + 1) (Nat.succ_lt_succ hi))))

/-- The product lists filtered at a pointwise read are the product
lists of the filtered domains, one list in the domains' order. -/
theorem filter_prodLists {α : Type} (q : α → Bool) :
    ∀ Ds : List (List α),
      (prodLists Ds).filter (fun l => l.all q)
        = prodLists (Ds.map (fun D => D.filter q))
  | [] => rfl
  | D :: t => by
    show (D.flatMap (fun x => (prodLists t).map (fun l => x :: l))).filter
        (fun l => l.all q)
      = (D.filter q).flatMap (fun x =>
          (prodLists (t.map (fun D => D.filter q))).map (fun l => x :: l))
    rw [filter_flatMap, flatMap_filter, ← filter_prodLists q t]
    refine flatMap_congr_all _ _ (fun x => ?_) D
    rw [filter_map]
    cases hq : q x with
    | true =>
      rw [if_pos rfl]
      exact congrArg (List.map (fun l => x :: l))
        (filter_congr _ _ (fun l => by
          show (q x && l.all q) = l.all q
          rw [hq]
          rfl) _)
    | false =>
      rw [if_neg Bool.false_ne_true]
      rw [filter_false _ _ (fun l _ => by
        show (q x && l.all q) = false
        rw [hq]
        rfl)]
      rfl

/-- A grown list's count over the product lists is the head's count
in its domain against the tail's over the further domains'. -/
theorem countOf_prodLists_cons {α : Type} [DecidableEq α] (x : α)
    (l : List α) (D : List α) (t : List (List α)) :
    countOf (x :: l) (prodLists (D :: t))
      = countOf x D * countOf l (prodLists t) := by
  show countOf (x :: l) (D.flatMap (fun y => (prodLists t).map (fun m => y :: m)))
    = _
  rw [countOf_flatMap,
    famFold_off (fun y => countOf (x :: l) ((prodLists t).map (fun m => y :: m)))
      x D (fun y _ hyx => by rw [countOf_consMap, if_neg (fun h => hyx h.symm)]),
    countOf_consMap, if_pos rfl]

/-- The product lists over distinct domains are distinct. -/
theorem distinct_prodLists {α : Type} [DecidableEq α] :
    ∀ Ds : List (List α), (∀ D, D ∈ Ds → distinctList D) →
      distinctList (prodLists Ds)
  | [], _ => fun x hx => by
    rw [eq_of_mem_single (show x ∈ [([] : List α)] from hx)]
    show countOf ([] : List α) [[]] ≤ 1
    rw [countOf_head]
    exact Nat.le_refl 1
  | D :: t, h => fun l hl => by
    obtain ⟨x, hx, hm⟩ := mem_flatMap_of _ D l hl
    obtain ⟨m, hm', hml⟩ := mem_map_of _ _ l hm
    rw [← hml, countOf_prodLists_cons]
    exact Nat.mul_le_mul (h D (List.Mem.head t) x hx)
      (distinct_prodLists t (fun E hE => h E (List.Mem.tail D hE)) m hm')



/-- A list's count in the product lists over distinct domains: one
at one member per domain at the domains' count, the sum's unit
elsewhere. -/
theorem countOf_prodLists {α : Type} [DecidableEq α] (d : α)
    (Ds : List (List α)) (hd : ∀ D, D ∈ Ds → distinctList D)
    (m : List α) :
    countOf m (prodLists Ds)
      = if m.length = Ds.length
          ∧ (∀ i, i < Ds.length → 0 < countOf (getAt d m i) (getAt [] Ds i))
        then 1 else 0 := by
  by_cases h : m.length = Ds.length
      ∧ (∀ i, i < Ds.length → 0 < countOf (getAt d m i) (getAt [] Ds i))
  · rw [if_pos h]
    have hm : m ∈ prodLists Ds :=
      mem_prodLists_to d Ds m h.1 (fun i hi => mem_of_countOf_pos _ _ (h.2 i hi))
    exact Nat.le_antisymm (distinct_prodLists Ds hd m hm) (countOf_pos_of_mem hm)
  · rw [if_neg h]
    cases hc : countOf m (prodLists Ds) with
    | zero => rfl
    | succ k =>
      have hm := mem_prodLists_of d Ds m (mem_of_countOf_pos m _
        (by rw [hc]; exact Nat.succ_pos k))
      exact absurd ⟨hm.1, fun i hi => countOf_pos_of_mem (hm.2 i hi)⟩ h

/-! The position read at an equality read: a member's first key
reading equal in a stated list. -/

/-- Two key pairs one key, the members' equalities joined. -/
def pairBeq (a b : Nat × Nat) : Bool := a.1 == b.1 && a.2 == b.2

/-- Two key triples one key. -/
def tripleBeq (a b : Nat × Nat × Nat) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && a.2.2 == b.2.2

/-- Two key pairs one key are one pair. -/
theorem pairBeq_read (a b : Nat × Nat) (h : pairBeq a b = true) : a = b := by
  have hs := andSplitB (show (a.1 == b.1 && a.2 == b.2) = true from h)
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      have e1 : a1 = b1 := beqEqOf hs.1
      have e2 : a2 = b2 := beqEqOf hs.2
      rw [e1, e2]

/-- A key pair reads one key against itself. -/
theorem pairBeq_refl (a : Nat × Nat) : pairBeq a a = true := by
  show (a.1 == a.1 && a.2 == a.2) = true
  rw [eqBeqOf rfl, eqBeqOf rfl]
  rfl

/-- Two key triples one key are one triple. -/
theorem tripleBeq_read (a b : Nat × Nat × Nat) (h : tripleBeq a b = true) : a = b := by
  have hs := andSplitB (show ((a.1 == b.1 && a.2.1 == b.2.1) && a.2.2 == b.2.2) = true from h)
  have hs' := andSplitB hs.1
  cases a with
  | mk a1 a2 =>
    cases a2 with
    | mk a2 a3 =>
      cases b with
      | mk b1 b2 =>
        cases b2 with
        | mk b2 b3 =>
          have e1 : a1 = b1 := beqEqOf hs'.1
          have e2 : a2 = b2 := beqEqOf hs'.2
          have e3 : a3 = b3 := beqEqOf hs.2
          rw [e1, e2, e3]

/-- A key triple reads one key against itself. -/
theorem tripleBeq_refl (a : Nat × Nat × Nat) : tripleBeq a a = true := by
  show ((a.1 == a.1 && a.2.1 == a.2.1) && a.2.2 == a.2.2) = true
  rw [eqBeqOf rfl, eqBeqOf rfl, eqBeqOf rfl]
  rfl

/-- Two key quadruples one key. -/
def quadBeq (a b : Nat × Nat × Nat × Nat) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && a.2.2.1 == b.2.2.1 && a.2.2.2 == b.2.2.2

/-- Two key quadruples one key are one quadruple. -/
theorem quadBeq_read (a b : Nat × Nat × Nat × Nat) (h : quadBeq a b = true) : a = b := by
  have hs := andSplitB (show (((a.1 == b.1 && a.2.1 == b.2.1) && a.2.2.1 == b.2.2.1)
    && a.2.2.2 == b.2.2.2) = true from h)
  have hs' := andSplitB hs.1
  have hs'' := andSplitB hs'.1
  cases a with
  | mk a1 a2 =>
    cases a2 with
    | mk a2 a3 =>
      cases a3 with
      | mk a3 a4 =>
        cases b with
        | mk b1 b2 =>
          cases b2 with
          | mk b2 b3 =>
            cases b3 with
            | mk b3 b4 =>
              have e1 : a1 = b1 := beqEqOf hs''.1
              have e2 : a2 = b2 := beqEqOf hs''.2
              have e3 : a3 = b3 := beqEqOf hs'.2
              have e4 : a4 = b4 := beqEqOf hs.2
              rw [e1, e2, e3, e4]

/-- A key quadruple reads one key against itself. -/
theorem quadBeq_refl (a : Nat × Nat × Nat × Nat) : quadBeq a a = true := by
  show (((a.1 == a.1 && a.2.1 == a.2.1) && a.2.2.1 == a.2.2.1) && a.2.2.2 == a.2.2.2) = true
  rw [eqBeqOf rfl, eqBeqOf rfl, eqBeqOf rfl, eqBeqOf rfl]
  rfl

/-- The position of a member in a stated list at an equality read,
the list's count off it, the first key reading equal. -/
def posBy {α : Type} (eq : α → α → Bool) (a : α) : List α → Nat
  | [] => 0
  | b :: t => if eq a b then 0 else posBy eq a t + 1

/-- The position at a head reading equal. -/
theorem posBy_cons_hit {α : Type} (eq : α → α → Bool) (a b : α) (t : List α)
    (h : eq a b = true) : posBy eq a (b :: t) = 0 := by
  show (if eq a b then 0 else posBy eq a t + 1) = 0
  rw [if_pos h]

/-- The position past a head reading unequal. -/
theorem posBy_cons_miss {α : Type} (eq : α → α → Bool) (a b : α) (t : List α)
    (h : eq a b = false) : posBy eq a (b :: t) = posBy eq a t + 1 := by
  show (if eq a b then 0 else posBy eq a t + 1) = _
  rw [if_neg (fun h' => Bool.noConfusion (h.symm.trans h'))]

/-- The position sits at or below the count. -/
theorem posBy_le {α : Type} (eq : α → α → Bool) (a : α) :
    ∀ l : List α, posBy eq a l ≤ l.length
  | [] => Nat.le_refl 0
  | b :: t => by
    show (if eq a b then 0 else posBy eq a t + 1) ≤ t.length + 1
    cases eq a b with
    | true => exact Nat.zero_le _
    | false => exact Nat.succ_le_succ (posBy_le eq a t)

/-- At a member met once in the list, the equality read at a key
holds exactly at the position. -/
theorem posBy_once {α : Type} [Inhabited α] (eq : α → α → Bool) (a : α) :
    ∀ l : List α,
      (l.filter (fun b => eq a b)).length = 1 →
      ∀ k, k < l.length →
        (eq a (getAt default l k) = true ↔ posBy eq a l = k)
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | b :: t, h, k, hk => by
    cases hb : eq a b with
    | true =>
      rw [filter_cons_true hb] at h
      have hlen : (t.filter (fun c => eq a c)).length = 0 :=
        Nat.succ.inj h
      have hoff : ∀ c, c ∈ t → eq a c = false := by
        intro c hc
        cases hc' : eq a c with
        | false => rfl
        | true =>
          have hm : c ∈ t.filter (fun c => eq a c) :=
            mem_filter_to _ hc hc'
          rw [nil_of_length_zero _ hlen] at hm
          exact nomatch hm
      show (eq a (getAt default (b :: t) k) = true
        ↔ (if eq a b then 0 else posBy eq a t + 1) = k)
      rw [hb, if_pos rfl]
      cases k with
      | zero => exact ⟨fun _ => rfl, fun _ => hb⟩
      | succ m =>
        show (eq a (getAt default t m) = true ↔ 0 = m + 1)
        have hm : m < t.length := Nat.lt_of_succ_lt_succ hk
        rw [hoff _ (mem_getAt default t m hm)]
        exact ⟨fun h0 => Bool.noConfusion h0, fun h0 => Nat.noConfusion h0⟩
    | false =>
      rw [filter_cons_false hb] at h
      show (eq a (getAt default (b :: t) k) = true
        ↔ (if eq a b then 0 else posBy eq a t + 1) = k)
      rw [hb, if_neg (fun h0 => Bool.noConfusion h0)]
      cases k with
      | zero =>
        show (eq a b = true ↔ posBy eq a t + 1 = 0)
        rw [hb]
        exact ⟨fun h0 => Bool.noConfusion h0, fun h0 => Nat.noConfusion h0⟩
      | succ m =>
        show (eq a (getAt default t m) = true ↔ posBy eq a t + 1 = m + 1)
        have hm : m < t.length := Nat.lt_of_succ_lt_succ hk
        have ih := posBy_once eq a t h m hm
        exact ⟨fun h0 => congrArg Nat.succ (ih.mp h0),
          fun h0 => ih.mpr (Nat.succ.inj h0)⟩

/-- A member met by the read sits at a position below the count. -/
theorem posBy_lt_of_hit {α : Type} (eq : α → α → Bool) (a : α) :
    ∀ l : List α, (∃ b, b ∈ l ∧ eq a b = true) → posBy eq a l < l.length
  | [], ⟨_, hb, _⟩ => nomatch hb
  | b :: t, ⟨c, hc, hac⟩ => by
    cases hab : eq a b with
    | true =>
      rw [posBy_cons_hit eq a b t hab]
      exact Nat.succ_pos _
    | false =>
      rw [posBy_cons_miss eq a b t hab]
      refine Nat.succ_lt_succ (posBy_lt_of_hit eq a t ⟨c, ?_, hac⟩)
      cases hc with
      | head =>
        rw [hac] at hab
        exact Bool.noConfusion hab
      | tail _ h2 => exact h2

/-- The list read at a met member's position reads equal to it. -/
theorem getAt_posBy {α : Type} (d : α) (eq : α → α → Bool) (a : α) :
    ∀ l : List α, (∃ b, b ∈ l ∧ eq a b = true) →
      eq a (getAt d l (posBy eq a l)) = true
  | [], ⟨_, hb, _⟩ => nomatch hb
  | b :: t, ⟨c, hc, hac⟩ => by
    cases hab : eq a b with
    | true =>
      rw [posBy_cons_hit eq a b t hab]
      exact hab
    | false =>
      rw [posBy_cons_miss eq a b t hab]
      show eq a (getAt d t (posBy eq a t)) = true
      refine getAt_posBy d eq a t ⟨c, ?_, hac⟩
      cases hc with
      | head =>
        rw [hac] at hab
        exact Bool.noConfusion hab
      | tail _ h2 => exact h2

/-! The positional keys: a site key's digit at a direction and the
digits' sum, the torus and box windows' coordinate reads. -/

/-- A key's digit at a stated base and direction, the coordinate
read of positional base arithmetic: the key against the direction's
stride `b^e`, the quotient's remainder at the base. -/
def baseDigit (b e s : Nat) : Nat := s / b ^ e % b

/-- A key's digits' sum over the directions below a stated count,
the two-coloring's read. -/
def digitSum (b d s : Nat) : Nat :=
  (List.range d).foldl (fun acc e => acc + baseDigit b e s) 0

/-! The range boxes: the product lists at per-key bounds, each
domain the naturals at or below its bound. -/

/-- The full range boxes at stated per-key bounds: every list
reading each key at or below its bound, once each — the product
lists at the bounds' ranges. -/
def boxAll (b : List Nat) : List (List Nat) :=
  prodLists (b.map (fun x => List.range (x + 1)))

/-- The box's count is the bounds' successor product. -/
theorem boxAll_length (b : List Nat) :
    (boxAll b).length = prodOver (fun x => x + 1) b := by
  show (prodLists _).length = famFold Nat.mul 1 (fun x => x + 1) b
  rw [length_prodLists]
  show famFold Nat.mul 1 List.length (b.map (fun x => List.range (x + 1))) = _
  rw [famFold_map]
  exact famFold_congr_all Nat.mul 1 _ _ (fun x => length_range (x + 1)) b

/-- The range box lists each selection once, the product of the
distinct key ranges. -/
theorem boxAll_distinct (b : List Nat) : distinctList (boxAll b) := by
  refine distinct_prodLists (b.map (fun x => List.range (x + 1))) ?_
  intro D hD
  obtain ⟨x, _, hx⟩ := mem_map_of _ _ D hD
  rw [← hx]
  exact distinctList_range _

/-- A list sits in the box once at the pointwise bound and the
matched length, off it at the vacant count. -/
theorem boxAll_countOf (b m : List Nat) :
    countOf m (boxAll b)
      = if m.length = b.length
          ∧ (∀ i, i < b.length → getAt 0 m i ≤ getAt 0 b i)
        then 1 else 0 := by
  show countOf m (prodLists (b.map (fun x => List.range (x + 1)))) = _
  rw [countOf_prodLists 0 _ (fun D hD => by
    obtain ⟨x, _, hx⟩ := mem_map_of _ _ D hD
    rw [← hx]
    exact distinctList_range _)]
  have hlen : (b.map (fun x => List.range (x + 1))).length = b.length :=
    length_map _ _
  by_cases h : m.length = b.length
      ∧ (∀ i, i < b.length → getAt 0 m i ≤ getAt 0 b i)
  · have hc : m.length = (b.map (fun x => List.range (x + 1))).length
        ∧ (∀ i, i < (b.map (fun x => List.range (x + 1))).length →
          0 < countOf (getAt 0 m i)
            (getAt [] (b.map (fun x => List.range (x + 1))) i)) :=
      ⟨h.1.trans hlen.symm, fun i hi => by
        rw [hlen] at hi
        rw [getAt_map 0 [] _ b i hi, countOf_range,
          if_pos (Nat.lt_succ_of_le (h.2 i hi))]
        exact Nat.succ_pos 0⟩
    rw [if_pos h, if_pos hc]
  · have hc : ¬ (m.length = (b.map (fun x => List.range (x + 1))).length
        ∧ (∀ i, i < (b.map (fun x => List.range (x + 1))).length →
          0 < countOf (getAt 0 m i)
            (getAt [] (b.map (fun x => List.range (x + 1))) i))) :=
      fun h' => h ⟨h'.1.trans hlen, fun i hi => by
        have h2 := h'.2 i (by rw [hlen]; exact hi)
        rw [getAt_map 0 [] _ b i hi, countOf_range] at h2
        by_cases hlt : getAt 0 m i < getAt 0 b i + 1
        · exact Nat.le_of_lt_succ hlt
        · rw [if_neg hlt] at h2
          exact absurd h2 (Nat.lt_irrefl 0)⟩
    rw [if_neg h, if_neg hc]

/-- A coordinate box at all-zero bounds contains exactly its
zero coordinate list, at every width. -/
theorem boxAll_zero (n : Nat) : boxAll (List.replicate n 0) = [List.replicate n 0] := by
  apply single_of_counts
  intro m
  rw [boxAll_countOf]
  by_cases he : m = List.replicate n 0
  · rw [if_pos he, he]
    rw [if_pos ⟨rfl, fun i _ => Nat.le_refl _⟩]
  · rw [if_neg he]
    apply if_neg
    intro h
    apply he
    have hm : m = List.replicate m.length 0 := replicate_of_zeros m (fun i hi => by
      rw [h.1] at hi
      exact Nat.eq_zero_of_le_zero (by
        have hp := h.2 i hi
        rw [getAt_replicate_self] at hp
        exact hp))
    rw [h.1, length_replicate] at hm
    exact hm

/-- A filter confined to a smaller coordinate box reads one list
in either box, with the product enumeration's order preserved. -/
theorem boxAll_filter_eq : ∀ (b B : List Nat), b.length = B.length →
    (∀ i, i < b.length → getAt 0 b i ≤ getAt 0 B i) →
    ∀ P : List Nat → Bool,
      (∀ m, m.length = b.length → P m = true →
        ∀ i, i < b.length → getAt 0 m i ≤ getAt 0 b i) →
      (boxAll B).filter P = (boxAll b).filter P
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => Nat.noConfusion h
  | _ :: _, [], h, _, _, _ => Nat.noConfusion h
  | a :: b, c :: B, hlen, hbound, P, hP => by
    have hlen' : b.length = B.length := Nat.succ.inj hlen
    have htail : ∀ i, i < b.length → getAt 0 b i ≤ getAt 0 B i :=
      fun i hi => hbound (i + 1) (Nat.succ_lt_succ hi)
    have hac : a ≤ c := hbound 0 (Nat.succ_pos _)
    obtain ⟨g, hg⟩ := Nat.le.dest hac
    have hc : c + 1 = (a + 1) + g := by rw [← hg, Nat.add_right_comm]
    have hrest : ∀ k ∈ (List.range g).map (fun j => a + 1 + j),
        ((boxAll B).map (fun m => k :: m)).filter P = [] := by
      intro k hk
      obtain ⟨j, _, hj⟩ := mem_map_of _ _ k hk
      refine filter_false P _ (fun m hm => ?_)
      obtain ⟨tail, htailB, htm⟩ := mem_map_of _ _ m hm
      rw [← htm]
      cases hp : P (k :: tail) with
      | false => rfl
      | true =>
        have hw := (mem_prodLists_of 0 _ tail htailB).1
        change tail.length = (B.map (fun x => List.range (x + 1))).length at hw
        rw [length_map] at hw
        have hka : k ≤ a := hP (k :: tail)
          (congrArg Nat.succ (hw.trans hlen'.symm)) hp 0 (Nat.succ_pos _)
        have hlt : a < k := by
          rw [← hj]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_add_right _ _)
        exact absurd (Nat.lt_of_lt_of_le hlt hka) (Nat.lt_irrefl a)
    change ((List.range (c + 1)).flatMap (fun k => (boxAll B).map (fun m => k :: m))).filter P
      = ((List.range (a + 1)).flatMap (fun k => (boxAll b).map (fun m => k :: m))).filter P
    rw [filter_flatMap, filter_flatMap, hc, range_split, flatMap_append,
      flatMap_nil _ _ hrest, append_nil]
    refine flatMap_congr_all _ _ (fun k => ?_) _
    rw [filter_map, filter_map,
      boxAll_filter_eq b B hlen' htail (fun m => P (k :: m))
        (fun m hm hp i hi => hP (k :: m) (congrArg Nat.succ hm) hp
          (i + 1) (Nat.succ_lt_succ hi))]

/-- Two count families' key-by-key sum, the longer family's tail
riding. -/
def hadd : List Nat → List Nat → List Nat
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: hadd p q

/-! The monomial device: a product mirrors into a count and an
exponent family over a stated datum list, the mirror's value is the
product itself, and two products whose counts and exponent families
agree read one value: the universal product identities' one
decision at `def:ground`'s exchanging and regrouping product, the
families compared by kernel reduction. -/

/-- A power at a summed key is the powers' product. -/
theorem powAdd (x a : Nat) : ∀ b : Nat, x ^ (a + b) = x ^ a * x ^ b
  | 0 => by rw [Nat.add_zero a, Nat.pow_zero x, Nat.mul_one (x ^ a)]
  | b + 1 => by
    rw [← Nat.add_assoc a b 1, Nat.pow_succ x (a + b), powAdd x a b,
      Nat.pow_succ x b, ground.mulAssoc (x ^ a) (x ^ b) x]

/-- A power at the key one is the datum. -/
theorem powOne (x : Nat) : x ^ 1 = x := by
  rw [Nat.pow_succ x 0, Nat.pow_zero x, Nat.one_mul x]

/-- The product's power is the powers' product. -/
theorem mulPow (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero]
  | n + 1 => by
    rw [Nat.pow_succ (a * b) n, Nat.pow_succ a n, Nat.pow_succ b n, mulPow a b n,
      mulMulMulComm]

/-- A power's power is the power at the exponents' product. -/
theorem powPow (a m : Nat) : ∀ n : Nat, (a ^ m) ^ n = a ^ (m * n)
  | 0 => by rw [Nat.pow_zero, Nat.mul_zero, Nat.pow_zero]
  | n + 1 => by rw [Nat.pow_succ (a ^ m) n, powPow a m n, Nat.mul_succ, powAdd]

/-- The halving's power is strict in the exponent. -/
theorem twoPowLt (a b : Nat) (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h
  rw [Nat.pow_succ 2 a, Nat.mul_two] at h1
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.pow_pos (by decide))) h1

/-- The exponent reads back off the halving's powers' order. -/
theorem leOfTwoPowLe (a b : Nat) (h : 2 ^ a ≤ 2 ^ b) : a ≤ b :=
  Nat.le_of_not_lt (fun hlt => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (twoPowLt b a hlt) h))

/-- The powers of four are the halving's doubled powers. -/
theorem fourPow : ∀ i : Nat, 4 ^ i = 2 ^ (2 * i)
  | 0 => by rw [Nat.mul_zero, Nat.pow_zero]
  | i + 1 => by
    rw [Nat.pow_succ 4 i, fourPow i, Nat.mul_succ 2 i, powAdd 2 (2 * i) 2]

/-- The exponent family's product against a stated datum list, from
a stated key. -/
def expVal (env : List Nat) : Nat → List Nat → Nat
  | _, [] => 1
  | i, k :: t => ground.getAt 0 env i ^ k * expVal env (i + 1) t

/-- The one-key exponent family. -/
def monUnit : Nat → List Nat
  | 0 => [1]
  | i + 1 => 0 :: monUnit i

/-- The exponent family's product at joined families is the
products' product. -/
theorem expVal_hadd (env : List Nat) : ∀ (i : Nat) (u v : List Nat),
    expVal env i (hadd u v) = expVal env i u * expVal env i v
  | i, [], v => (Nat.one_mul (expVal env i v)).symm
  | i, a :: u, [] => (Nat.mul_one (expVal env i (a :: u))).symm
  | i, a :: u, b :: v => by
    show ground.getAt 0 env i ^ (a + b) * expVal env (i + 1) (hadd u v)
      = ground.getAt 0 env i ^ a * expVal env (i + 1) u
        * (ground.getAt 0 env i ^ b * expVal env (i + 1) v)
    rw [powAdd (ground.getAt 0 env i) a b, expVal_hadd env (i + 1) u v,
      ground.mulMulMulComm (ground.getAt 0 env i ^ a)
        (ground.getAt 0 env i ^ b) (expVal env (i + 1) u)
        (expVal env (i + 1) v)]

/-- The one-key family's product reads the datum at the shifted
key. -/
theorem expVal_monUnit (env : List Nat) : ∀ (j i : Nat),
    expVal env j (monUnit i) = ground.getAt 0 env (j + i)
  | j, 0 => by
    show ground.getAt 0 env j ^ 1 * 1 = ground.getAt 0 env (j + 0)
    rw [Nat.mul_one, powOne, Nat.add_zero j]
  | j, i + 1 => by
    show ground.getAt 0 env j ^ 0 * expVal env (j + 1) (monUnit i)
      = ground.getAt 0 env (j + (i + 1))
    rw [Nat.pow_zero, Nat.one_mul, expVal_monUnit env (j + 1) i,
      Nat.add_right_comm j 1 i, Nat.add_assoc j i 1]

set_option genInjectivity false in
/-- The mirrored product: the counts, the stated data and the
product. -/
inductive Mon where
  | cst : Nat → Mon
  | var : Nat → Mon
  | mul : Mon → Mon → Mon

/-- The mirror's own value at a stated datum list. -/
def Mon.val (env : List Nat) : Mon → Nat
  | .cst c => c
  | .var i => ground.getAt 0 env i
  | .mul a b => a.val env * b.val env

/-- The mirror's count. -/
def Mon.coef : Mon → Nat
  | .cst c => c
  | .var _ => 1
  | .mul a b => a.coef * b.coef

/-- The mirror's exponent family. -/
def Mon.exps : Mon → List Nat
  | .cst _ => []
  | .var i => monUnit i
  | .mul a b => hadd a.exps b.exps

/-- The mirror's value is its count against its exponent family's
product. -/
theorem Mon.read (env : List Nat) : ∀ m : Mon,
    m.val env = m.coef * expVal env 0 m.exps
  | .cst c => by
    show c = c * 1
    rw [Nat.mul_one c]
  | .var i => by
    show ground.getAt 0 env i = 1 * expVal env 0 (monUnit i)
    rw [Nat.one_mul, expVal_monUnit env 0 i, Nat.zero_add i]
  | .mul a b => by
    show a.val env * b.val env
      = a.coef * b.coef * expVal env 0 (hadd a.exps b.exps)
    rw [Mon.read env a, Mon.read env b, expVal_hadd env 0 a.exps b.exps,
      ground.mulMulMulComm a.coef (expVal env 0 a.exps) b.coef
        (expVal env 0 b.exps)]

/-- Two mirrored products whose counts and exponent families agree
read one value at every datum list. -/
theorem monEq (env : List Nat) (a b : Mon)
    (hc : a.coef = b.coef) (he : a.exps = b.exps) :
    a.val env = b.val env := by
  rw [Mon.read env a, Mon.read env b, hc, he]

/-- A mirrored product's read in the pair carrier: each count at its
one-member site `[c : 1]`, the data at the stated pair list, the
product the carrier's own. -/
def Mon.valB (env : List BPair) : Mon → BPair
  | .cst c => BPair.ofNat c
  | .var i => ground.getAt BPair.unit env i
  | .mul a b => a.valB env * b.valB env

/-- A count product enters the pair carrier at the one-member site
factor by factor, `def:ground`'s product read. -/
theorem Mon.ofNat_val (env : List Nat) : ∀ m : Mon,
    (BPair.ofNat (m.val env)).oneValue (m.valB (env.map BPair.ofNat))
  | .cst c => BPair.oneValue_refl _
  | .var i => by
    show (BPair.ofNat (ground.getAt 0 env i)).oneValue
      (ground.getAt BPair.unit (env.map BPair.ofNat) i)
    rw [getAt_mapT 0 BPair.unit BPair.ofNat rfl env i]
    exact BPair.oneValue_refl _
  | .mul a b =>
    BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (Mon.ofNat_val env a) (Mon.ofNat_val env b))

set_option genInjectivity false in
/-- A count expression: mirrored products joined by the sum and the
product. -/
inductive Pol where
  | mon : Mon → Pol
  | add : Pol → Pol → Pol
  | mul : Pol → Pol → Pol

/-- The expression's own value at a stated datum list. -/
def Pol.val (env : List Nat) : Pol → Nat
  | .mon m => m.val env
  | .add a b => a.val env + b.val env
  | .mul a b => a.val env * b.val env

/-- The expression's read in the pair carrier at a stated pair list. -/
def Pol.valB (env : List BPair) : Pol → BPair
  | .mon m => m.valB env
  | .add a b => a.valB env + b.valB env
  | .mul a b => a.valB env * b.valB env

/-- A count expression enters the pair carrier at the one-member
site, sums to sums and products to products: the count's read at
the data is one value with the carrier's read at the data's
one-member sites. -/
theorem Pol.ofNat_val (env : List Nat) : ∀ p : Pol,
    (BPair.ofNat (p.val env)).oneValue (p.valB (env.map BPair.ofNat))
  | .mon m => Mon.ofNat_val env m
  | .add a b =>
    BPair.oneValue_trans (BPair.ofNat_add _ _)
      (BPair.add_congr (Pol.ofNat_val env a) (Pol.ofNat_val env b))
  | .mul a b =>
    BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (Pol.ofNat_val env a) (Pol.ofNat_val env b))


/-! The polynomial device: a count expression collects to its
collected display, the monomials at sorted exponent families with
their counts joined, and two expressions at one display read one
value at every datum list, of pairs (`polEqB`) or of ground data
entering at their one-member sites (`polEq`): the universal
polynomial identities' one decision at `def:ground`'s sum and product
(two fold orders equal by the ground identities), the displays
compared by kernel reduction, the monomial device's (`monEq`)
extension across the sum. -/

/-- A monomial at its count and exponent family joins a sorted family
list: before the first family beyond it, its count joined at an equal
family, and past a smaller family otherwise. -/
def nfInsert (m : Nat × List Nat) : List (Nat × List Nat) → List (Nat × List Nat)
  | [] => [m]
  | x :: xs =>
    if lexLt m.2 x.2 then m :: x :: xs
    else if m.2 = x.2 then (m.1 + x.1, x.2) :: xs
    else x :: nfInsert m xs

/-- Two normal forms' sum, the first's monomials joined one by one. -/
def nfAdd : List (Nat × List Nat) → List (Nat × List Nat) → List (Nat × List Nat)
  | [], b => b
  | a :: as, b => nfInsert a (nfAdd as b)

/-- A monomial against a normal form, the counts multiplied and the
families joined. -/
def nfScale (m : Nat × List Nat) : List (Nat × List Nat) → List (Nat × List Nat)
  | [] => []
  | x :: xs => nfInsert (m.1 * x.1, hadd m.2 x.2) (nfScale m xs)

/-- Two normal forms' product, the first's monomials against the second. -/
def nfMul : List (Nat × List Nat) → List (Nat × List Nat) → List (Nat × List Nat)
  | [], _ => []
  | a :: as, b => nfAdd (nfScale a b) (nfMul as b)

/-- A count expression's collected display (`def:ground`): the monomials
collected at sorted exponent families with their counts joined, a vacant
count dropped. -/
def Pol.nf : Pol → List (Nat × List Nat)
  | .mon m => if m.coef = 0 then [] else [(m.coef, m.exps)]
  | .add a b => nfAdd a.nf b.nf
  | .mul a b => nfMul a.nf b.nf

/-! The collected display at the pair carrier: the display reads in
the balance carrier at a stated pair list, the counts at their
one-member sites and the data's powers at the carrier's own product,
a formula's read is one value with its display's read there, and two
formulas at one display read one value at every pair list
(`def:ground`'s collected display at the balance-pair carrier, whose
displayed product exchanges, regroups and distributes across the
displayed sum). -/

/-- The exponent family's product in the pair carrier at a stated pair
list, from a stated key. -/
def expValB (env : List BPair) : Nat → List Nat → BPair
  | _, [] => BPair.ofPos .one
  | i, k :: t => bpow (ground.getAt BPair.unit env i) k * expValB env (i + 1) t

/-- The exponent family's product at joined families reads the
products' product. -/
theorem expValB_hadd (env : List BPair) : ∀ (i : Nat) (u v : List Nat),
    (expValB env i (hadd u v)).oneValue (expValB env i u * expValB env i v)
  | _, [], v => BPair.oneValue_symm (BPair.ofPos_one_mul (expValB env _ v))
  | _, a :: u, [] => BPair.oneValue_symm (BPair.mul_one_read (expValB env _ (a :: u)))
  | i, a :: u, b :: v => by
    show (bpow (ground.getAt BPair.unit env i) (a + b)
        * expValB env (i + 1) (hadd u v)).oneValue
      (bpow (ground.getAt BPair.unit env i) a * expValB env (i + 1) u
        * (bpow (ground.getAt BPair.unit env i) b * expValB env (i + 1) v))
    refine BPair.oneValue_trans
      (BPair.mul_congr (bpow_add _ a b) (expValB_hadd env (i + 1) u v)) ?_
    exact BPair.oneValue_of_eq (BPair.mul_mul_mul_comm _ _ _ _)

/-- The one-key family's product reads the datum at the shifted
key. -/
theorem expValB_monUnit (env : List BPair) : ∀ (j i : Nat),
    (expValB env j (monUnit i)).oneValue (ground.getAt BPair.unit env (j + i))
  | j, 0 => by
    show (bpow (ground.getAt BPair.unit env j) 1 * BPair.ofPos .one).oneValue
      (ground.getAt BPair.unit env (j + 0))
    rw [Nat.add_zero j]
    exact BPair.oneValue_trans (BPair.mul_one_read _) (bpow_one_read _)
  | j, i + 1 => by
    show (BPair.ofPos .one * expValB env (j + 1) (monUnit i)).oneValue
      (ground.getAt BPair.unit env (j + (i + 1)))
    have e : j + (i + 1) = j + 1 + i := by
      rw [Nat.add_right_comm j 1 i, Nat.add_assoc j i 1]
    rw [e]
    exact BPair.oneValue_trans (BPair.ofPos_one_mul _) (expValB_monUnit env (j + 1) i)

/-- A mirrored product's pair read is its count's one-member site
against its exponent family's product. -/
theorem Mon.readB (env : List BPair) : ∀ m : Mon,
    (m.valB env).oneValue (BPair.ofNat m.coef * expValB env 0 m.exps)
  | .cst c => by
    show (BPair.ofNat c).oneValue (BPair.ofNat c * BPair.ofPos .one)
    exact BPair.oneValue_symm (BPair.mul_one_read _)
  | .var i => by
    show (ground.getAt BPair.unit env i).oneValue
      (BPair.ofNat 1 * expValB env 0 (monUnit i))
    have h := expValB_monUnit env 0 i
    rw [Nat.zero_add i] at h
    exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_one_mul _) h)
  | .mul a b => by
    show (a.valB env * b.valB env).oneValue
      (BPair.ofNat (a.coef * b.coef) * expValB env 0 (hadd a.exps b.exps))
    refine BPair.oneValue_trans (BPair.mul_congr (Mon.readB env a) (Mon.readB env b)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_mul_mul_comm _ _ _ _)) ?_
    exact BPair.mul_congr (BPair.oneValue_symm (BPair.ofNat_mul _ _))
      (BPair.oneValue_symm (expValB_hadd env 0 a.exps b.exps))

/-- A collected display's read in the pair carrier at a stated pair
list, the counts' one-member sites against the families' products. -/
def nfValB (env : List BPair) : List (Nat × List Nat) → BPair
  | [] => BPair.unit
  | x :: xs => BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs

/-- A joined monomial's pair read adds to the list's. -/
theorem nfValB_insert (env : List BPair) (m : Nat × List Nat) : ∀ l : List (Nat × List Nat),
    (nfValB env (nfInsert m l)).oneValue
      (BPair.ofNat m.1 * expValB env 0 m.2 + nfValB env l)
  | [] => BPair.oneValue_refl _
  | x :: xs => by
    show (nfValB env (if lexLt m.2 x.2 then m :: x :: xs
        else if m.2 = x.2 then (m.1 + x.1, x.2) :: xs else x :: nfInsert m xs)).oneValue
      (BPair.ofNat m.1 * expValB env 0 m.2
        + (BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs))
    cases lexLt m.2 x.2 with
    | true => exact BPair.oneValue_refl _
    | false =>
      show (nfValB env (if m.2 = x.2 then (m.1 + x.1, x.2) :: xs
        else x :: nfInsert m xs)).oneValue _
      match (inferInstance : Decidable (m.2 = x.2)) with
      | isTrue h =>
        rw [if_pos h]
        show (BPair.ofNat (m.1 + x.1) * expValB env 0 x.2 + nfValB env xs).oneValue
          (BPair.ofNat m.1 * expValB env 0 m.2
            + (BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs))
        rw [h]
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.mul_congr_left (BPair.ofNat_add m.1 x.1)) (BPair.oneValue_refl _)) ?_
        exact BPair.oneValue_of_eq (by rw [BPair.right_distrib, BPair.add_assoc])
      | isFalse h =>
        rw [if_neg h]
        show (BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env (nfInsert m xs)).oneValue
          (BPair.ofNat m.1 * expValB env 0 m.2
            + (BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs))
        refine BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _) (nfValB_insert env m xs)) ?_
        exact BPair.oneValue_of_eq (BPair.add_left_comm _ _ _)

/-- The sum's pair read is the reads' sum. -/
theorem nfValB_add (env : List BPair) : ∀ a b : List (Nat × List Nat),
    (nfValB env (nfAdd a b)).oneValue (nfValB env a + nfValB env b)
  | [], b => BPair.oneValue_symm (BPair.unit_add _)
  | x :: xs, b => by
    show (nfValB env (nfInsert x (nfAdd xs b))).oneValue
      (BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs + nfValB env b)
    refine BPair.oneValue_trans (nfValB_insert env x (nfAdd xs b)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (nfValB_add env xs b)) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm

/-- A monomial against a form reads the monomial's pair read against
the form's. -/
theorem nfValB_scale (env : List BPair) (m : Nat × List Nat) : ∀ b : List (Nat × List Nat),
    (nfValB env (nfScale m b)).oneValue
      (BPair.ofNat m.1 * expValB env 0 m.2 * nfValB env b)
  | [] => BPair.oneValue_symm (BPair.mul_unit _)
  | x :: xs => by
    show (nfValB env (nfInsert (m.1 * x.1, hadd m.2 x.2) (nfScale m xs))).oneValue
      (BPair.ofNat m.1 * expValB env 0 m.2
        * (BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs))
    refine BPair.oneValue_trans (nfValB_insert env _ (nfScale m xs)) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.mul_congr (BPair.ofNat_mul m.1 x.1) (expValB_hadd env 0 m.2 x.2))
      (nfValB_scale env m xs)) ?_
    exact BPair.oneValue_of_eq (by
      rw [BPair.mul_mul_mul_comm (BPair.ofNat m.1) (BPair.ofNat x.1)
        (expValB env 0 m.2) (expValB env 0 x.2), ← BPair.left_distrib])

/-- The product's pair read is the reads' product. -/
theorem nfValB_mul (env : List BPair) : ∀ a b : List (Nat × List Nat),
    (nfValB env (nfMul a b)).oneValue (nfValB env a * nfValB env b)
  | [], b => BPair.oneValue_symm (BPair.unit_mul _)
  | x :: xs, b => by
    show (nfValB env (nfAdd (nfScale x b) (nfMul xs b))).oneValue
      ((BPair.ofNat x.1 * expValB env 0 x.2 + nfValB env xs) * nfValB env b)
    refine BPair.oneValue_trans (nfValB_add env _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (nfValB_scale env x b) (nfValB_mul env xs b)) ?_
    exact BPair.oneValue_of_eq (BPair.right_distrib _ _ _).symm

/-- A count expression's pair read is one value with its collected
display's. -/
theorem Pol.valB_nf (env : List BPair) : ∀ p : Pol,
    (p.valB env).oneValue (nfValB env p.nf)
  | .mon m => by
    show (m.valB env).oneValue
      (nfValB env (if m.coef = 0 then [] else [(m.coef, m.exps)]))
    refine BPair.oneValue_trans (Mon.readB env m) ?_
    match (inferInstance : Decidable (m.coef = 0)) with
    | isTrue h =>
      rw [if_pos h, h]
      exact BPair.oneValue_trans (BPair.mul_congr_left BPair.ofNat_zero) (BPair.unit_mul _)
    | isFalse h =>
      rw [if_neg h]
      exact BPair.oneValue_symm (BPair.add_unit _)
  | .add a b => by
    show (a.valB env + b.valB env).oneValue (nfValB env (nfAdd a.nf b.nf))
    exact BPair.oneValue_trans (BPair.add_congr (Pol.valB_nf env a) (Pol.valB_nf env b))
      (BPair.oneValue_symm (nfValB_add env a.nf b.nf))
  | .mul a b => by
    show (a.valB env * b.valB env).oneValue (nfValB env (nfMul a.nf b.nf))
    exact BPair.oneValue_trans (BPair.mul_congr (Pol.valB_nf env a) (Pol.valB_nf env b))
      (BPair.oneValue_symm (nfValB_mul env a.nf b.nf))

/-- Two formulas at one collected display read one value at every pair
list (`def:ground`): the balance carrier's product exchanges and
regroups, the displays compared by kernel reduction. -/
theorem polEqB (env : List BPair) (a b : Pol) (h : a.nf = b.nf) :
    (a.valB env).oneValue (b.valB env) := by
  refine BPair.oneValue_trans (Pol.valB_nf env a) ?_
  rw [h]
  exact BPair.oneValue_symm (Pol.valB_nf env b)

/-- Two formulas at one collected display read one value at every datum
list of ground data (`def:ground`): the data enter the pair carrier at
their one-member sites, the sites' sum and product the data's, and the
pair read's one value reads back at the sites' injectivity. -/
theorem polEq (env : List Nat) (a b : Pol) (h : a.nf = b.nf) : a.val env = b.val env :=
  BPair.ofNat_inj (BPair.oneValue_trans (Pol.ofNat_val env a)
    (BPair.oneValue_trans (polEqB (env.map BPair.ofNat) a b h)
      (BPair.oneValue_symm (Pol.ofNat_val env b))))

/-! The quotient's reads: the uniqueness, the multiple's join, the
count's bound and the iterated quotient. -/

/-- The quotient's uniqueness: a stated reconstruction with its
remainder below the divisor reads the core quotient, the naming
identity's one value. -/
theorem divOf {d q r x : Nat} (hd : 0 < d) (he : d * q + r = x)
    (hr : r < d) : x / d = q := by
  have hn := (natDivRead x d hd).1
  rw [modOf hd he hr] at hn
  exact Nat.eq_of_mul_eq_mul_left hd (addCancelR r (hn.trans he.symm))

/-- A divisor's multiple joins the quotient. -/
theorem divAddMul (x a d : Nat) (hd : 0 < d) :
    (x + a * d) / d = x / d + a := by
  have hn := natDivRead x d hd
  refine divOf hd ?_ hn.2
  rw [Nat.mul_add, Nat.add_right_comm, hn.1, Nat.mul_comm d a]

/-- A quotient sits below a count at a dividend below the count's
multiple of the divisor. -/
theorem divLtOfLtMul {x d n : Nat} (hd : 0 < d) (h : x < d * n) :
    x / d < n := by
  cases Nat.lt_or_ge (x / d) n with
  | inl hlt => exact hlt
  | inr hge =>
    have hn := (natDivRead x d hd).1
    have h1 : d * n ≤ d * (x / d) := Nat.mul_le_mul_left d hge
    have h2 : d * (x / d) ≤ x := Nat.le.intro hn
    exact absurd (Nat.lt_of_lt_of_le h (Nat.le_trans h1 h2)) (Nat.lt_irrefl x)

/-- The quotient at a product of divisors is the iterated
quotient. -/
theorem divDiv (x m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    x / (m * n) = x / m / n := by
  have h1 := natDivRead x m hm
  have h2 := natDivRead (x / m) n hn
  refine divOf (r := m * (x / m % n) + x % m) (Nat.mul_pos hm hn) ?_ ?_
  · have e : m * n * (x / m / n) + (m * (x / m % n) + x % m)
        = m * (n * (x / m / n) + x / m % n) + x % m :=
      polEq [m, n, x / m / n, x / m % n, x % m]
        (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))))
        (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 4)))
        (by decide +kernel)
    rw [e, h2.1, h1.1]
  · have h3 : m * (x / m % n + 1) ≤ m * n :=
      Nat.mul_le_mul_left m (Nat.succ_le_of_lt h2.2)
    rw [Nat.mul_succ] at h3
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h1.2 _) h3

/-! The positional digits: a key's digit at a direction against the
base, the digits' reads at the steps and the prefixes. -/

/-- A digit sits below the base. -/
theorem baseDigit_lt (b e s : Nat) (hb : 0 < b) : baseDigit b e s < b :=
  (natDivRead (s / b ^ e) b hb).2

/-- A higher power's multiple joined keeps a lower digit. -/
theorem baseDigit_add_high (b e c s q : Nat) (hb : 0 < b) (h : e < c) :
    baseDigit b e (s + q * b ^ c) = baseDigit b e s := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  show (s + q * b ^ c) / b ^ e % b = s / b ^ e % b
  rw [← hk, powAdd b (e + 1) k, Nat.pow_succ b e]
  have e1 : s + q * (b ^ e * b * b ^ k) = s + q * b ^ k * b * b ^ e :=
    polEq [s, q, b ^ e, b, b ^ k]
      (Pol.add (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4)))))
      (Pol.add (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 2))))
      (by decide +kernel)
  rw [e1, divAddMul s (q * b ^ k * b) (b ^ e) (Nat.pow_pos hb), modAddMul]

/-- The digit at the stepped key, at a digit below the base's
predecessor. -/
theorem baseDigit_step (b c s : Nat) (hb : 0 < b) (h : baseDigit b c s + 1 < b) :
    baseDigit b c (s + b ^ c) = baseDigit b c s + 1 := by
  show (s + b ^ c) / b ^ c % b = s / b ^ c % b + 1
  have h1 := divAddMul s 1 (b ^ c) (Nat.pow_pos hb)
  rw [Nat.one_mul] at h1
  rw [h1]
  have hn := natDivRead (s / b ^ c) b hb
  refine modOf (q := s / b ^ c / b) hb ?_ h
  rw [← Nat.add_assoc, hn.1]

/-- The remainder at a power sits below the power. -/
theorem modPowLt (b e s : Nat) (hb : 0 < b) : s % b ^ e < b ^ e :=
  (natDivRead s (b ^ e) (Nat.pow_pos hb)).2

/-- A digit beyond a key's reach reads the sum's unit. -/
theorem baseDigit_of_lt (b e s : Nat) (hb : 0 < b) (hs : s < b ^ e) :
    baseDigit b e s = 0 := by
  show s / b ^ e % b = 0
  rw [divOf (q := 0) (Nat.pow_pos hb) (by rw [Nat.mul_zero, Nat.zero_add]) hs, modZeroLeft]

/-- The key's remainder at a direction's successor power splits at
the direction's digit against the lower remainder, and its
quotient there is the direction's quotient at the base. -/
theorem lowSplit (b c s : Nat) (hb : 0 < b) :
    s % b ^ (c + 1) = b ^ c * baseDigit b c s + s % b ^ c
      ∧ s / b ^ (c + 1) = s / b ^ c / b := by
  have h1 := natDivRead s (b ^ c) (Nat.pow_pos hb)
  have h2 := natDivRead (s / b ^ c) b hb
  have hlt : b ^ c * (s / b ^ c % b) + s % b ^ c < b ^ (c + 1) := by
    have h3 : b ^ c * (s / b ^ c % b + 1) ≤ b ^ c * b :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h2.2)
    rw [Nat.mul_succ] at h3
    rw [Nat.pow_succ]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h1.2 _) h3
  have he : b ^ (c + 1) * (s / b ^ c / b) + (b ^ c * (s / b ^ c % b) + s % b ^ c) = s := by
    rw [Nat.pow_succ]
    have e : b ^ c * b * (s / b ^ c / b) + (b ^ c * (s / b ^ c % b) + s % b ^ c)
        = b ^ c * (b * (s / b ^ c / b) + s / b ^ c % b) + s % b ^ c :=
      polEq [b ^ c, b, s / b ^ c / b, s / b ^ c % b, s % b ^ c]
        (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))))
        (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 4)))
        (by decide +kernel)
    rw [e, h2.1, h1.1]
  exact ⟨modOf (Nat.pow_pos hb) he hlt, divOf (Nat.pow_pos hb) he hlt⟩

/-- The stepped remainder stays below the successor power at no
the digit below the base's predecessor. -/
theorem stepLow (b c s : Nat) (hb : 0 < b) (h : baseDigit b c s + 1 < b) :
    s % b ^ (c + 1) + b ^ c < b ^ (c + 1) := by
  rw [(lowSplit b c s hb).1]
  have h1 := natDivRead s (b ^ c) (Nat.pow_pos hb)
  have h3 : b ^ c * (baseDigit b c s + 2) ≤ b ^ c * b := Nat.mul_le_mul_left _ h
  rw [Nat.pow_succ]
  refine Nat.lt_of_lt_of_le ?_ h3
  have e2 : b ^ c * (baseDigit b c s + 2) = b ^ c * baseDigit b c s + b ^ c + b ^ c :=
    polEq [b ^ c, baseDigit b c s]
      (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2))))
      (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0)))
      (by decide +kernel)
  rw [e2, Nat.add_right_comm (b ^ c * baseDigit b c s) (s % b ^ c) (b ^ c)]
  exact Nat.add_lt_add_left h1.2 _

/-- The digit beyond the step's direction, at the stepped digit
below the base's predecessor. -/
theorem baseDigit_step_high (b c e s : Nat) (hb : 0 < b)
    (h : baseDigit b c s + 1 < b) (hce : c < e) :
    baseDigit b e (s + b ^ c) = baseDigit b e s := by
  obtain ⟨k, hk⟩ := Nat.le.dest hce
  have hn := natDivRead s (b ^ (c + 1)) (Nat.pow_pos hb)
  have hq : (s + b ^ c) / b ^ (c + 1) = s / b ^ (c + 1) := by
    refine divOf (Nat.pow_pos hb) ?_ (stepLow b c s hb h)
    rw [← Nat.add_assoc, hn.1]
  show (s + b ^ c) / b ^ e % b = s / b ^ e % b
  rw [← hk, powAdd b (c + 1) k, divDiv _ _ _ (Nat.pow_pos hb) (Nat.pow_pos hb),
    divDiv s _ _ (Nat.pow_pos hb) (Nat.pow_pos hb), hq]

/-- The stepped key stays inside the box at the stepped digit below
the base's predecessor. -/
theorem stepLtPow (b c d s : Nat) (hb : 0 < b) (hs : s < b ^ d) (hcd : c < d)
    (h : baseDigit b c s + 1 < b) : s + b ^ c < b ^ d := by
  obtain ⟨k, hk⟩ := Nat.le.dest hcd
  have hn := natDivRead s (b ^ (c + 1)) (Nat.pow_pos hb)
  have hq : s / b ^ (c + 1) < b ^ k := by
    refine divLtOfLtMul (Nat.pow_pos hb) ?_
    rw [← powAdd, hk]
    exact hs
  have h1 : b ^ (c + 1) * (s / b ^ (c + 1) + 1) ≤ b ^ (c + 1) * b ^ k :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq)
  rw [← powAdd, hk, Nat.mul_succ] at h1
  refine Nat.lt_of_lt_of_le ?_ h1
  conv => lhs; rw [← hn.1]
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left (stepLow b c s hb h) _

/-- The prefix's digits below the cut are the key's own. -/
theorem baseDigit_mod_low (b e i s : Nat) (hb : 0 < b) (hi : i < e) :
    baseDigit b i (s % b ^ e) = baseDigit b i s := by
  have hn := natDivRead s (b ^ e) (Nat.pow_pos hb)
  conv => rhs; rw [← hn.1]
  rw [Nat.mul_comm (b ^ e) (s / b ^ e), Nat.add_comm (s / b ^ e * b ^ e) (s % b ^ e),
    baseDigit_add_high b i e (s % b ^ e) (s / b ^ e) hb hi]

/-- The prefix's digits at or beyond the cut read the sum's unit. -/
theorem baseDigit_mod_high (b e i s : Nat) (hb : 0 < b) (hi : e ≤ i) :
    baseDigit b i (s % b ^ e) = 0 :=
  baseDigit_of_lt b i _ hb
    (Nat.lt_of_lt_of_le (modPowLt b e s hb) (Nat.pow_le_pow_right hb hi))

/-- A split key's lower digits are the low part's. -/
theorem baseDigit_split_low (b e d q r : Nat) (hb : 0 < b) (he : e < d) :
    baseDigit b e (q * b ^ d + r) = baseDigit b e r := by
  rw [Nat.add_comm]
  exact baseDigit_add_high b e d r q hb he

/-- A split key's top digit is the high part. -/
theorem baseDigit_split_top (b d q r : Nat) (hb : 0 < b) (hr : r < b ^ d) (hq : q < b) :
    baseDigit b d (q * b ^ d + r) = q := by
  show (q * b ^ d + r) / b ^ d % b = q
  rw [divOf (q := q) (Nat.pow_pos hb) (by rw [Nat.mul_comm]) hr, modOfLt q b hq]

/-- A split key sits below the successor power. -/
theorem splitLtPow (b d q r : Nat) (hr : r < b ^ d) (hq : q < b) :
    q * b ^ d + r < b ^ (d + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm (b ^ d) b]
  have h1 : (q + 1) * b ^ d ≤ b * b ^ d := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at h1
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) h1

/-- A split key's digits beyond the top read the sum's unit. -/
theorem baseDigit_split_high (b d e q r : Nat) (hb : 0 < b) (hr : r < b ^ d) (hq : q < b)
    (he : d < e) : baseDigit b e (q * b ^ d + r) = 0 :=
  baseDigit_of_lt b e _ hb
    (Nat.lt_of_lt_of_le (splitLtPow b d q r hr hq) (Nat.pow_le_pow_right hb he))

/-- A key whose digit at a direction is occupied steps back along
it: the key less the direction's power steps forward to the key,
its digit there one below the key's and its further digits the
key's own. -/
theorem stepBack (b e s' : Nat) (hb : 0 < b) (hd : 0 < baseDigit b e s') :
    (s' - b ^ e) + b ^ e = s'
    ∧ baseDigit b e (s' - b ^ e) + 1 = baseDigit b e s'
    ∧ ∀ c, ¬ c = e → baseDigit b c (s' - b ^ e) = baseDigit b c s' := by
  have hpe : 0 < b ^ e := Nat.pow_pos hb
  have hpe1 : 0 < b ^ (e + 1) := Nat.pow_pos hb
  obtain ⟨j, hj⟩ := Nat.le.dest hd
  have hdj : baseDigit b e s' = j + 1 := by rw [← hj, Nat.add_comm]
  have hjb : j + 1 < b := by rw [← hdj]; exact baseDigit_lt b e s' hb
  have hs0 : (s' / b ^ (e + 1)) * b ^ (e + 1) + (j * b ^ e + s' % b ^ e) + b ^ e = s' := by
    have h1 := (natDivRead s' (b ^ (e + 1)) hpe1).1
    have h2 := (lowSplit b e s' hb).1
    rw [hdj] at h2
    rw [h2] at h1
    refine Eq.trans ?_ h1
    exact polEq [s' / b ^ (e + 1), b ^ (e + 1), j, b ^ e, s' % b ^ e]
      (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4)))) (Pol.mon (Mon.var 3)))
      (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 0))) (Pol.add (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1)))) (Pol.mon (Mon.var 4))))
      (by decide +kernel)
  have hd0 : baseDigit b e ((s' / b ^ (e + 1)) * b ^ (e + 1) + (j * b ^ e + s' % b ^ e)) = j := by
    rw [baseDigit_split_low b e (e + 1) _ _ hb (Nat.lt_succ_self e),
      baseDigit_split_top b e j _ hb (natDivRead s' (b ^ e) hpe).2 (Nat.lt_of_succ_lt hjb)]
  generalize hs : (s' / b ^ (e + 1)) * b ^ (e + 1) + (j * b ^ e + s' % b ^ e) = s0 at hs0 hd0
  have hd0' : baseDigit b e s0 + 1 < b := by rw [hd0]; exact hjb
  rw [← hs0, addSubSelfR]
  refine ⟨rfl, ?_, ?_⟩
  · rw [baseDigit_step b e s0 hb hd0']
  · intro c hc
    cases Nat.lt_or_ge c e with
    | inl hce =>
      rw [← Nat.one_mul (b ^ e), baseDigit_add_high b c e s0 1 hb hce]
    | inr hce =>
      cases Nat.lt_or_ge e c with
      | inl hec => rw [baseDigit_step_high b e c s0 hb hd0' hec]
      | inr hec => exact absurd (Nat.le_antisymm hec hce) hc

/-! The positional enumeration: the keys below a product split at
the high part, the keys below a power at the top digit. -/

/-- The keys below a product, the high part outer. -/
theorem range_mul (n : Nat) : ∀ b : Nat,
    List.range (b * n)
      = (List.range b).flatMap (fun q => (List.range n).map (fun r => q * n + r))
  | 0 => by
    rw [Nat.zero_mul]
    rfl
  | b + 1 => by
    rw [Nat.succ_mul, range_split (b * n) n, range_mul n b, range_succ b, flatMap_append]
    show _ = _ ++ ((List.range n).map (fun r => b * n + r) ++ [])
    rw [append_nil]

/-- The keys below a power split at the top digit. -/
theorem range_pow_succ (b d : Nat) :
    List.range (b ^ (d + 1))
      = (List.range b).flatMap (fun q => (List.range (b ^ d)).map (fun r => q * b ^ d + r)) := by
  rw [Nat.pow_succ, Nat.mul_comm, range_mul]

/-- Two range reads of pointwise equal members read one value. -/
theorem all_range_congr (f g : Nat → Bool) : ∀ n : Nat, (∀ i, i < n → f i = g i) →
    (List.range n).all f = (List.range n).all g
  | 0, _ => rfl
  | n + 1, h => by
    rw [range_succ n, all_append f, all_append g,
      all_range_congr f g n (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    show ((List.range n).all g && (f n && true)) = ((List.range n).all g && (g n && true))
    rw [h n (Nat.lt_succ_self n)]

/-- A filter at a stated conjunct reads the conjunct's cases: the
filter's count at a held conjunct and the vacant count otherwise. -/
theorem length_filter_and {α : Type} (A : α → Bool) (c : Bool) (l : List α) :
    (l.filter (fun x => A x && c)).length = cond c (l.filter A).length 0 := by
  cases c with
  | true =>
    show (l.filter (fun x => A x && true)).length = (l.filter A).length
    rw [filter_congr _ _ (fun x => Bool.and_true (A x)) l]
  | false =>
    show (l.filter (fun x => A x && false)).length = 0
    rw [filter_false _ l (fun x _ => Bool.and_false (A x))]
    rfl

/-- A guarded range fold at the side's successor reads the fold
below the side. -/
theorem famFold_range_lt (h : Nat → Nat) (L : Nat) :
    famFold Nat.add 0 (fun x => if decide (x < L) = true then h x else 0) (List.range (L + 1))
      = famFold Nat.add 0 h (List.range L) := by
  rw [range_succ L, famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add]
  show famFold Nat.add 0 (fun x => if decide (x < L) = true then h x else 0) (List.range L)
    + ((if decide (L < L) = true then h L else 0) + 0) = famFold Nat.add 0 h (List.range L)
  rw [decide_eq_false (Nat.lt_irrefl L), if_neg (fun hc => Bool.noConfusion hc), Nat.add_zero]
  refine famFold_congr_members Nat.add 0 _ _ (List.range L) (fun x hx => ?_)
  rw [decide_eq_true (ltOfCountRange hx), if_pos rfl]

/-- The box count at constrained directions: the keys below the
box's size whose digits at every direction a stated read selects
sit below the side. -/
def boxCount (b d L : Nat) (P : Nat → Bool) : Nat :=
  ((List.range (b ^ d)).filter (fun s =>
    (List.range d).all (fun e => !P e || decide (baseDigit b e s < L)))).length

/-- The box count reads the side's power at the selected directions'
count against the base's power at the further directions' count. -/
theorem boxCount_read (L : Nat) (P : Nat → Bool) : ∀ d : Nat,
    boxCount (L + 1) d L P
      = L ^ ((List.range d).filter P).length
        * (L + 1) ^ (d - ((List.range d).filter P).length)
  | 0 => rfl
  | d + 1 => by
    have ih := boxCount_read L P d
    have hb : 0 < L + 1 := Nat.succ_pos L
    have hm : ((List.range d).filter P).length ≤ d := by
      have := length_filter_le P (List.range d)
      rw [length_range] at this
      exact this
    show ((List.range ((L + 1) ^ (d + 1))).filter (fun s =>
      (List.range (d + 1)).all (fun e => !P e || decide (baseDigit (L + 1) e s < L)))).length = _
    rw [range_pow_succ, filter_flatMap, length_flatMap]
    have hq : ∀ q, q < L + 1 →
        (((List.range ((L + 1) ^ d)).map (fun r => q * (L + 1) ^ d + r)).filter
          (fun s => (List.range (d + 1)).all
            (fun e => !P e || decide (baseDigit (L + 1) e s < L)))).length
        = cond (!P d || decide (q < L)) (boxCount (L + 1) d L P) 0 := by
      intro q hq
      rw [filter_map, length_map]
      have hc : (List.range ((L + 1) ^ d)).filter (fun r => (List.range (d + 1)).all
            (fun e => !P e || decide (baseDigit (L + 1) e (q * (L + 1) ^ d + r) < L)))
          = (List.range ((L + 1) ^ d)).filter (fun r =>
            (List.range d).all (fun e => !P e || decide (baseDigit (L + 1) e r < L))
              && (!P d || decide (q < L))) :=
        filter_congr_mem _ _ _ (fun r hr => by
          have hr' : r < (L + 1) ^ d := ltOfCountRange hr
          rw [range_succ d, all_append,
            all_range_congr _ (fun e => !P e || decide (baseDigit (L + 1) e r < L)) d
              (fun e he => by rw [baseDigit_split_low _ _ _ _ _ hb he])]
          show ((List.range d).all (fun e => !P e || decide (baseDigit (L + 1) e r < L))
              && ((!P d || decide (baseDigit (L + 1) d (q * (L + 1) ^ d + r) < L)) && true))
            = ((List.range d).all (fun e => !P e || decide (baseDigit (L + 1) e r < L))
              && (!P d || decide (q < L)))
          rw [baseDigit_split_top _ _ _ _ hb hr' hq, Bool.and_true])
      rw [hc, length_filter_and]
      rfl
    rw [famFold_congr_members Nat.add 0 _
      (fun q => cond (!P d || decide (q < L)) (boxCount (L + 1) d L P) 0) (List.range (L + 1))
      (fun q hq' => hq q (ltOfCountRange hq'))]
    cases hPd : P d with
    | false =>
      rw [famFold_congr_members Nat.add 0
        (fun q => cond (!false || decide (q < L)) (boxCount (L + 1) d L P) 0)
        (fun _ => boxCount (L + 1) d L P) (List.range (L + 1))
        (fun q _ => rfl), famFold_const, length_range, ih,
        range_succ d, filter_append, filter_cons_false hPd,
        show List.filter P ([] : List Nat) = [] from rfl, append_nil]
      generalize hmm : ((List.range d).filter P).length = m at hm ⊢
      obtain ⟨k, hk⟩ := Nat.le.dest hm
      rw [← hk, addSubSelfL, Nat.add_assoc m k 1, addSubSelfL, Nat.pow_succ]
      exact polEq [L + 1, L ^ m, (L + 1) ^ k]
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))))
        (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 0))))
        (by decide +kernel)
    | true =>
      rw [famFold_congr_members Nat.add 0
        (fun q => cond (!true || decide (q < L)) (boxCount (L + 1) d L P) 0)
        (fun q => if decide (q < L) = true then boxCount (L + 1) d L P else 0)
        (List.range (L + 1)) (fun q _ => by cases decide (q < L) <;> rfl),
        famFold_range_lt, famFold_const, length_range, ih,
        range_succ d, filter_append, filter_cons_true hPd,
        show List.filter P ([] : List Nat) = [] from rfl, length_append]
      show L * (L ^ ((List.range d).filter P).length * (L + 1) ^ (d - ((List.range d).filter P).length))
        = L ^ (((List.range d).filter P).length + 1)
          * (L + 1) ^ (d + 1 - (((List.range d).filter P).length + 1))
      generalize hmm : ((List.range d).filter P).length = m at hm ⊢
      obtain ⟨k, hk⟩ := Nat.le.dest hm
      rw [Nat.succ_sub_succ, ← hk, addSubSelfL, Nat.pow_succ]
      exact polEq [L, L ^ m, (L + 1) ^ k]
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))))
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2)))
        (by decide +kernel)


/-! The mirror device and the power sums: an expression over two
counts mirrors into a count family, the outer variable's keys the
inner variable's own families (`Mir.keys`), the mirror's value the
expression itself (`Mir.val`), the Horner reads agreeing node by
node (`Mir.read`), so two expressions whose mirrored families reduce
alike read one value (`mirEq`), the universal count identities'
one decision at the sum and the product; the power sums
`powSum k n = Σ_{m=1}^{n} m^k` with their eleven closed reads from the
binomial step at each key (`sumClosed`); and the margin of two
naturals with its square read (`marg`, `margSq_read`). -/

/-- The power sum `S_k(n) = Σ_{m=1}^{n} m^k`, the closed reads'
shared carrier (`def:poly`'s binomial identities close it). -/
def powSum (k n : Nat) : Nat :=
  ground.sumNat ((List.range n).map (fun j => (j + 1) ^ k))


/-- The margin of two naturals, the trichotomy's one value. -/
def marg (a b : Nat) : Nat := (a - b) + (b - a)


/-- The count family's Horner read at a count. -/
def hread : List Nat → Nat → Nat
  | [], _ => 0
  | c :: p, g => c + g * hread p g

/-- Two count families' convolution. -/
private def hmul : List Nat → List Nat → List Nat
  | [], _ => []
  | c :: p, q => hadd (q.map (fun d => c * d)) (0 :: hmul p q)

/-- The Horner read of a key-by-key sum is the reads' sum. -/
theorem hread_add : ∀ (p q : List Nat) (n : Nat),
    hread (hadd p q) n = hread p n + hread q n
  | [], q, n => (Nat.zero_add (hread q n)).symm
  | c :: p, [], n => (Nat.add_zero (hread (c :: p) n)).symm
  | c :: p, d :: q, n => by
    show c + d + n * hread (hadd p q) n
      = c + n * hread p n + (d + n * hread q n)
    rw [hread_add p q n, Nat.left_distrib n (hread p n) (hread q n),
      Nat.add_add_add_comm c d (n * hread p n) (n * hread q n)]

/-- The Horner read of a family's multiple is the read's multiple. -/
theorem hread_scale : ∀ (q : List Nat) (c n : Nat),
    hread (q.map (fun d => c * d)) n = c * hread q n
  | [], c, _ => (Nat.mul_zero c).symm
  | d :: q, c, n => by
    show c * d + n * hread (q.map (fun d => c * d)) n
      = c * (d + n * hread q n)
    rw [hread_scale q c n, Nat.left_distrib c d (n * hread q n),
      ground.mulLeftComm n c (hread q n)]

/-- The Horner read is monotone in the count. -/
theorem hread_mono {K K' : Nat} (h : K ≤ K') :
    ∀ l : List Nat, hread l K ≤ hread l K'
  | [] => Nat.le_refl 0
  | c :: p => Nat.add_le_add_left (Nat.mul_le_mul h (hread_mono h p)) c

/-- The Horner read at a growth past the clearing: at `6 b ≤ K` the
read at `K + b` against the read at `K` sits under seven sixths per
key beyond the head, `6^n hread (c :: p) (K + b) ≤ 7^n hread (c :: p) K`
at `n` the tail's count. -/
theorem hread_grow (K b : Nat) (h : 6 * b ≤ K) :
    ∀ (p : List Nat) (c : Nat),
      6 ^ p.length * hread (c :: p) (K + b) ≤ 7 ^ p.length * hread (c :: p) K
  | [], c => by
    show 6 ^ 0 * (c + (K + b) * 0) ≤ 7 ^ 0 * (c + K * 0)
    exact Nat.le_of_eq (by rw [Nat.mul_zero (K + b), Nat.mul_zero K, Nat.pow_zero])
  | d :: q, c => by
    show 6 ^ (q.length + 1) * (c + (K + b) * hread (d :: q) (K + b))
      ≤ 7 ^ (q.length + 1) * (c + K * hread (d :: q) K)
    have h7 : 6 * (K + b) ≤ 7 * K := by
      have e : 7 * K = 6 * K + K := Nat.succ_mul 6 K
      rw [Nat.mul_add, e]
      exact Nat.add_le_add_left h (6 * K)
    have e1 : 6 ^ (q.length + 1) * (c + (K + b) * hread (d :: q) (K + b))
        = 6 ^ (q.length + 1) * c
          + 6 * (K + b) * (6 ^ q.length * hread (d :: q) (K + b)) := by
      rw [Nat.mul_add, Nat.pow_succ 6 q.length]
      exact congrArg (6 ^ q.length * 6 * c + ·)
        (monEq [6 ^ q.length, K + b, hread (d :: q) (K + b)]
          (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 6)) (Mon.mul (Mon.var 1) (Mon.var 2)))
          (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 1)) (Mon.mul (Mon.var 0) (Mon.var 2)))
          (by decide +kernel) (by decide +kernel))
    have e2 : 7 ^ (q.length + 1) * (c + K * hread (d :: q) K)
        = 7 ^ (q.length + 1) * c + 7 * K * (7 ^ q.length * hread (d :: q) K) := by
      rw [Nat.mul_add, Nat.pow_succ 7 q.length]
      exact congrArg (7 ^ q.length * 7 * c + ·)
        (monEq [7 ^ q.length, K, hread (d :: q) K]
          (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 7)) (Mon.mul (Mon.var 1) (Mon.var 2)))
          (Mon.mul (Mon.mul (Mon.cst 7) (Mon.var 1)) (Mon.mul (Mon.var 0) (Mon.var 2)))
          (by decide +kernel) (by decide +kernel))
    rw [e1, e2]
    exact Nat.add_le_add (Nat.mul_le_mul_right c (Nat.pow_le_pow_left (by decide) _))
      (Nat.mul_le_mul h7 (hread_grow K b h q d))

/-- The Horner read at a linear growth against the count's power of
the read at one step: `hread (c :: p) (K + b t) ≤ t^n hread (c :: p) (K + b)`
at `t` at or beyond one and `n` the tail's count. -/
theorem hread_growLin (K b t : Nat) (ht : 1 ≤ t) :
    ∀ (p : List Nat) (c : Nat),
      hread (c :: p) (K + b * t) ≤ t ^ p.length * hread (c :: p) (K + b)
  | [], c => by
    show c + (K + b * t) * 0 ≤ t ^ 0 * (c + (K + b) * 0)
    exact Nat.le_of_eq (by rw [Nat.mul_zero (K + b * t), Nat.mul_zero (K + b), Nat.pow_zero,
      Nat.one_mul])
  | d :: q, c => by
    show c + (K + b * t) * hread (d :: q) (K + b * t)
      ≤ t ^ (q.length + 1) * (c + (K + b) * hread (d :: q) (K + b))
    have h1 : K + b * t ≤ t * (K + b) := by
      rw [Nat.mul_add, Nat.mul_comm t b]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_left K ht) (b * t)
    have e : t ^ (q.length + 1) * (c + (K + b) * hread (d :: q) (K + b))
        = t ^ (q.length + 1) * c + t * (K + b) * (t ^ q.length * hread (d :: q) (K + b)) := by
      rw [Nat.mul_add, Nat.pow_succ t q.length]
      exact congrArg (t ^ q.length * t * c + ·)
        (monEq [t ^ q.length, t, K + b, hread (d :: q) (K + b)]
          (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 3)))
          (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.mul (Mon.var 0) (Mon.var 3)))
          (by decide +kernel) (by decide +kernel))
    rw [e]
    exact Nat.add_le_add (Nat.le_mul_of_pos_left c (Nat.pow_pos ht))
      (Nat.mul_le_mul h1 (hread_growLin K b t ht q d))

private theorem hread_mul : ∀ (p q : List Nat) (n : Nat),
    hread (hmul p q) n = hread p n * hread q n
  | [], q, n => (Nat.zero_mul (hread q n)).symm
  | c :: p, q, n => by
    show hread (hadd (q.map (fun d => c * d)) (0 :: hmul p q)) n
      = (c + n * hread p n) * hread q n
    rw [hread_add (q.map (fun d => c * d)) (0 :: hmul p q) n,
      hread_scale q c n]
    show c * hread q n + (0 + n * hread (hmul p q) n)
      = (c + n * hread p n) * hread q n
    rw [hread_mul p q n, Nat.zero_add,
      ground.mulAddR c (n * hread p n) (hread q n),
      ground.mulAssoc n (hread p n) (hread q n)]

private theorem hread_cst (c g : Nat) : hread [c] g = c := by
  show c + g * 0 = c
  rw [Nat.mul_zero g, Nat.add_zero c]

private theorem hread_lin (a b g : Nat) : hread [a, b] g = a + g * b := by
  show a + g * (b + g * 0) = a + g * b
  rw [Nat.mul_zero g, Nat.add_zero b]

/-- The two-variable Horner read: the outer variable's keys are the
inner variable's own count families. -/
def h2read : List (List Nat) → Nat → Nat → Nat
  | [], _, _ => 0
  | c :: p, m, g => hread c g + m * h2read p m g

def h2add : List (List Nat) → List (List Nat) → List (List Nat)
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => hadd c d :: h2add p q

private def h2mul : List (List Nat) → List (List Nat) → List (List Nat)
  | [], _ => []
  | c :: p, q => h2add (q.map (fun d => hmul c d)) ([] :: h2mul p q)

private theorem h2read_add : ∀ (p q : List (List Nat)) (m g : Nat),
    h2read (h2add p q) m g = h2read p m g + h2read q m g
  | [], q, m, g => (Nat.zero_add (h2read q m g)).symm
  | c :: p, [], m, g => (Nat.add_zero (h2read (c :: p) m g)).symm
  | c :: p, d :: q, m, g => by
    show hread (hadd c d) g + m * h2read (h2add p q) m g
      = hread c g + m * h2read p m g + (hread d g + m * h2read q m g)
    rw [hread_add c d g, h2read_add p q m g,
      Nat.left_distrib m (h2read p m g) (h2read q m g),
      Nat.add_add_add_comm (hread c g) (hread d g)
        (m * h2read p m g) (m * h2read q m g)]

private theorem h2read_scale : ∀ (q : List (List Nat)) (c : List Nat)
    (m g : Nat),
    h2read (q.map (fun d => hmul c d)) m g = hread c g * h2read q m g
  | [], c, _, g => (Nat.mul_zero (hread c g)).symm
  | d :: q, c, m, g => by
    show hread (hmul c d) g + m * h2read (q.map (fun d => hmul c d)) m g
      = hread c g * (hread d g + m * h2read q m g)
    rw [hread_mul c d g, h2read_scale q c m g,
      Nat.left_distrib (hread c g) (hread d g) (m * h2read q m g),
      ground.mulLeftComm m (hread c g) (h2read q m g)]

private theorem h2read_mul : ∀ (p q : List (List Nat)) (m g : Nat),
    h2read (h2mul p q) m g = h2read p m g * h2read q m g
  | [], q, m, g => (Nat.zero_mul (h2read q m g)).symm
  | c :: p, q, m, g => by
    show h2read (h2add (q.map (fun d => hmul c d)) ([] :: h2mul p q)) m g
      = (hread c g + m * h2read p m g) * h2read q m g
    rw [h2read_add (q.map (fun d => hmul c d)) ([] :: h2mul p q) m g,
      h2read_scale q c m g]
    show hread c g * h2read q m g + (0 + m * h2read (h2mul p q) m g)
      = (hread c g + m * h2read p m g) * h2read q m g
    rw [h2read_mul p q m g, Nat.zero_add,
      ground.mulAddR (hread c g) (m * h2read p m g) (h2read q m g),
      ground.mulAssoc m (h2read p m g) (h2read q m g)]

private def h2pow (p : List (List Nat)) : Nat → List (List Nat)
  | 0 => [[1]]
  | k + 1 => h2mul p (h2pow p k)

private theorem h2read_pow (p : List (List Nat)) (m g : Nat) :
    ∀ k : Nat, h2read (h2pow p k) m g = h2read p m g ^ k
  | 0 => by
    show hread [1] g + m * 0 = h2read p m g ^ 0
    rw [hread_cst 1 g, Nat.mul_zero m, Nat.add_zero 1, Nat.pow_zero]
  | k + 1 => by
    rw [show h2pow p (k + 1) = h2mul p (h2pow p k) from rfl,
      h2read_mul p (h2pow p k) m g, h2read_pow p m g k, Nat.pow_succ,
      Nat.mul_comm (h2read p m g) (h2read p m g ^ k)]

set_option genInjectivity false in
/-- The mirrored expression over two variables: the constants, the
two variables, and the sum, the product and the stated power. -/
inductive Mir where
  | cst : Nat → Mir
  | x : Mir
  | y : Mir
  | add : Mir → Mir → Mir
  | mul : Mir → Mir → Mir
  | pow : Mir → Nat → Mir

/-- The mirror's count families, one key family per outer key. -/
def Mir.keys : Mir → List (List Nat)
  | .cst c => [[c]]
  | .x => [[0], [1]]
  | .y => [[0, 1]]
  | .add a b => h2add a.keys b.keys
  | .mul a b => h2mul a.keys b.keys
  | .pow a k => h2pow a.keys k

/-- The mirror's own value at the two counts. -/
def Mir.val (m g : Nat) : Mir → Nat
  | .cst c => c
  | .x => m
  | .y => g
  | .add a b => a.val m g + b.val m g
  | .mul a b => a.val m g * b.val m g
  | .pow a k => a.val m g ^ k

/-- The mirrored families' Horner read is the expression's value. -/
private theorem Mir.read (m g : Nat) : ∀ e : Mir,
    h2read e.keys m g = e.val m g
  | .cst c => by
    show hread [c] g + m * 0 = c
    rw [hread_cst c g, Nat.mul_zero m, Nat.add_zero c]
  | .x => by
    show hread [0] g + m * (hread [1] g + m * 0) = m
    rw [hread_cst 0 g, hread_cst 1 g, Nat.mul_zero m, Nat.add_zero 1,
      Nat.mul_one m, Nat.zero_add m]
  | .y => by
    show hread [0, 1] g + m * 0 = g
    rw [hread_lin 0 1 g, Nat.mul_zero m, Nat.add_zero (0 + g * 1),
      Nat.mul_one g, Nat.zero_add g]
  | .add a b => by
    show h2read (h2add a.keys b.keys) m g = a.val m g + b.val m g
    rw [h2read_add a.keys b.keys m g, Mir.read m g a, Mir.read m g b]
  | .mul a b => by
    show h2read (h2mul a.keys b.keys) m g = a.val m g * b.val m g
    rw [h2read_mul a.keys b.keys m g, Mir.read m g a, Mir.read m g b]
  | .pow a k => by
    show h2read (h2pow a.keys k) m g = a.val m g ^ k
    rw [h2read_pow a.keys m g k, Mir.read m g a]

/-- The vacant families' padding, the key window the mirrors are
compared inside. -/
def zeroPad : List (List Nat) :=
  List.replicate 32 (List.replicate 16 0)

private theorem hread_zeroRow (g : Nat) :
    ∀ J : Nat, hread (List.replicate J 0) g = 0
  | 0 => rfl
  | J + 1 => by
    show 0 + g * hread (List.replicate J 0) g = 0
    rw [hread_zeroRow g J, Nat.mul_zero g, Nat.add_zero 0]

private theorem h2read_zeroRows (m g : Nat) :
    ∀ K : Nat, h2read (List.replicate K (List.replicate 16 0)) m g = 0
  | 0 => rfl
  | K + 1 => by
    show hread (List.replicate 16 0) g
        + m * h2read (List.replicate K (List.replicate 16 0)) m g = 0
    rw [hread_zeroRow g 16, h2read_zeroRows m g K, Nat.mul_zero m,
      Nat.add_zero 0]

private theorem h2read_zeroPad (m g : Nat) : h2read zeroPad m g = 0 :=
  h2read_zeroRows m g 32

/-- A count family agreeing with a mirror's padded families reads
the mirror's own value. -/
theorem mirRaw (m g : Nat) (K : List (List Nat)) (b : Mir)
    (h : h2add K zeroPad = h2add b.keys zeroPad) :
    h2read K m g = b.val m g := by
  have hK : h2read (h2add K zeroPad) m g = h2read K m g := by
    rw [h2read_add K zeroPad m g, h2read_zeroPad m g, Nat.add_zero]
  have hb : h2read (h2add b.keys zeroPad) m g = b.val m g := by
    rw [h2read_add b.keys zeroPad m g, h2read_zeroPad m g,
      Nat.add_zero, Mir.read m g b]
  rw [← hK, ← hb, h]

/-- Two mirrors whose padded count families agree read one value at
every count pair. -/
theorem mirEq (m g : Nat) (a b : Mir)
    (h : h2add a.keys zeroPad = h2add b.keys zeroPad) :
    a.val m g = b.val m g :=
  (Mir.read m g a).symm.trans (mirRaw m g a.keys b h)

/-- A one-variable count family enters the two-variable read at its
one-count keys. -/
theorem hreadRow : ∀ (L : List Nat) (N : Nat),
    hread L N = h2read (L.map (fun c => [c])) N 0
  | [], _ => rfl
  | c :: t, N => by
    show c + N * hread t N
      = hread [c] 0 + N * h2read (t.map (fun c => [c])) N 0
    rw [hread_cst c 0, hreadRow t N]

/-- The power sum grows at its endpoint by the arriving depth's own
power. -/
private theorem powSum_succ (k n : Nat) :
    powSum k (n + 1) = powSum k n + (n + 1) ^ k := by
  show ground.sumNat (((List.range (n + 1))).map (fun j => (j + 1) ^ k))
    = ground.sumNat ((List.range n).map (fun j => (j + 1) ^ k))
      + (n + 1) ^ k
  rw [ground.range_succ n, ground.map_append, ground.sumNat_append]
  rfl

/-- A count family's total scales through its scalar. -/
theorem sumNat_scale (c : Nat) (f : Nat → Nat)
    (l : List Nat) :
    c * ground.sumNat (l.map f)
      = ground.sumNat (l.map (fun x => c * f x)) := by
  rw [ground.sumMap f l, ground.sumMap (fun x => c * f x) l]
  exact ground.famFold_mul c f l

/-- The closed read's induction at a stated family: the base at the
key nought and one step identity per key settle the cleared read at
every endpoint. -/
theorem sumClosedF (f : Nat → Nat) (a : Nat) (L R : Nat → Nat)
    (hb : a * f 0 + L 0 = R 0)
    (hs : ∀ n : Nat, R (n + 1) + L n = R n + L (n + 1) + a * f (n + 1)) :
    ∀ n : Nat, a * ground.sumNat ((List.range (n + 1)).map f) + L n = R n
  | 0 => by
    show a * ground.sumNat [f 0] + L 0 = R 0
    rw [show ground.sumNat [f 0] = f 0 from rfl]
    exact hb
  | n + 1 => by
    have hstep : ground.sumNat ((List.range (n + 1 + 1)).map f)
        = ground.sumNat ((List.range (n + 1)).map f) + f (n + 1) := by
      rw [ground.range_succ (n + 1), ground.map_append, ground.sumNat_append]
      rfl
    refine ground.addCancelR (L n) ?_
    rw [hstep, Nat.left_distrib a _ (f (n + 1)), hs n,
      Nat.add_right_comm (a * ground.sumNat ((List.range (n + 1)).map f))
        (a * f (n + 1)) (L (n + 1)),
      Nat.add_assoc (a * ground.sumNat ((List.range (n + 1)).map f) + L (n + 1))
        (a * f (n + 1)) (L n),
      Nat.add_comm (a * f (n + 1)) (L n),
      ← Nat.add_assoc (a * ground.sumNat ((List.range (n + 1)).map f) + L (n + 1))
        (L n) (a * f (n + 1)),
      Nat.add_right_comm (a * ground.sumNat ((List.range (n + 1)).map f))
        (L (n + 1)) (L n),
      sumClosedF f a L R hb hs n,
      Nat.add_right_comm (R n) (L (n + 1)) (a * f (n + 1))]

/-- The closed read's induction: the base at the vacant endpoint and
one step identity per depth settle the cleared read at every
endpoint. -/
theorem sumClosed (k a : Nat) (L R : Nat → Nat)
    (hb : L 0 = R 0)
    (hs : ∀ n : Nat, R (n + 1) + L n = R n + L (n + 1) + a * (n + 1) ^ k) :
    ∀ n : Nat, a * powSum k n + L n = R n
  | 0 => by
    show a * 0 + L 0 = R 0
    rw [Nat.mul_zero a, Nat.zero_add]
    exact hb
  | n + 1 =>
    sumClosedF (fun j => (j + 1) ^ k) a (fun j => L (j + 1)) (fun j => R (j + 1))
      (by
        have h := hs 0
        rw [hb] at h
        refine ground.addCancelR (R 0) ?_
        rw [h, Nat.add_comm (R 0) (L (0 + 1)),
          Nat.add_right_comm (L (0 + 1)) (R 0) (a * (0 + 1) ^ k),
          Nat.add_comm (L (0 + 1)) (a * (0 + 1) ^ k)])
      (fun j => hs (j + 1)) n

/-- The power sum's step identity at the key 1. -/
private theorem powStep1 (n : Nat) :
    (n + 1) ^ 2 + (n + 1)
      = n ^ 2 + n + 2 * (n + 1) ^ 1 :=
  mirEq n 0 (Mir.add (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2) (Mir.add
    Mir.x (Mir.cst 1))) (Mir.add (Mir.add (Mir.pow Mir.x 2) Mir.x)
    (Mir.mul (Mir.cst 2) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 1))) (by decide +kernel)

/-- The power sum's step identity at the key 2. -/
private theorem powStep2 (n : Nat) :
    2 * (n + 1) ^ 3 + 3 * (n + 1) ^ 2 + (n + 1)
      = 2 * n ^ 3 + 3 * n ^ 2 + n + 6 * (n + 1) ^ 2 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 3)) (Mir.mul (Mir.cst 3) (Mir.pow (Mir.add Mir.x (Mir.cst
    1)) 2))) (Mir.add Mir.x (Mir.cst 1))) (Mir.add (Mir.add (Mir.add
    (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 3)) (Mir.mul (Mir.cst 3) (Mir.pow
    Mir.x 2))) Mir.x) (Mir.mul (Mir.cst 6) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 2))) (by decide +kernel)

/-- The power sum's step identity at the key 3. -/
private theorem powStep3 (n : Nat) :
    (n + 1) ^ 4 + 2 * (n + 1) ^ 3 + (n + 1) ^ 2
      = n ^ 4 + 2 * n ^ 3 + n ^ 2 + 4 * (n + 1) ^ 3 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 4)
    (Mir.mul (Mir.cst 2) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 3)))
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2)) (Mir.add (Mir.add (Mir.add
    (Mir.pow Mir.x 4) (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 3))) (Mir.pow
    Mir.x 2)) (Mir.mul (Mir.cst 4) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    3))) (by decide +kernel)

/-- The power sum's step identity at the key 4. -/
private theorem powStep4 (n : Nat) :
    6 * (n + 1) ^ 5 + 15 * (n + 1) ^ 4 + 10 * (n + 1) ^ 3 + n
      = 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^ 3 + ((n + 1)) + 30 * (n + 1) ^ 4
        :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 5)) (Mir.mul (Mir.cst 15) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 4))) (Mir.mul (Mir.cst 10) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 3))) Mir.x) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst 15)
    (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 3))) (Mir.add
    Mir.x (Mir.cst 1))) (Mir.mul (Mir.cst 30) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4))) (by decide +kernel)

/-- The power sum's step identity at the key 5. -/
private theorem powStep5 (n : Nat) :
    2 * (n + 1) ^ 6 + 6 * (n + 1) ^ 5 + 5 * (n + 1) ^ 4 + n ^ 2
      = 2 * n ^ 6 + 6 * n ^ 5 + 5 * n ^ 4 + ((n + 1) ^ 2) + 12 * (n + 1) ^
        5 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 6)) (Mir.mul (Mir.cst 6) (Mir.pow (Mir.add
    Mir.x (Mir.cst 1)) 5))) (Mir.mul (Mir.cst 5) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4))) (Mir.pow Mir.x 2)) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 6)
    (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 4))) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 2)) (Mir.mul (Mir.cst 12) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 5))) (by decide +kernel)

/-- The power sum's step identity at the key 6. -/
private theorem powStep6 (n : Nat) :
    6 * (n + 1) ^ 7 + 21 * (n + 1) ^ 6 + 21 * (n + 1) ^ 5 + (n + 1) + 7 *
      n ^ 3
      = 6 * n ^ 7 + 21 * n ^ 6 + 21 * n ^ 5 + n + (7 * (n + 1) ^ 3) + 42 *
        (n + 1) ^ 6 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7)) (Mir.mul (Mir.cst 21)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 6))) (Mir.mul (Mir.cst 21)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 5))) (Mir.add Mir.x (Mir.cst 1)))
    (Mir.mul (Mir.cst 7) (Mir.pow Mir.x 3))) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 21) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x
    5))) Mir.x) (Mir.mul (Mir.cst 7) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    3))) (Mir.mul (Mir.cst 42) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 6)))
    (by decide +kernel)

/-- The power sum's step identity at the key 7. -/
private theorem powStep7 (n : Nat) :
    3 * (n + 1) ^ 8 + 12 * (n + 1) ^ 7 + 14 * (n + 1) ^ 6 + 2 * (n + 1) ^
      2 + 7 * n ^ 4
      = 3 * n ^ 8 + 12 * n ^ 7 + 14 * n ^ 6 + 2 * n ^ 2 + (7 * (n + 1) ^
        4) + 24 * (n + 1) ^ 7 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 3)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8)) (Mir.mul (Mir.cst 12)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7))) (Mir.mul (Mir.cst 14)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 6))) (Mir.mul (Mir.cst 2)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2))) (Mir.mul (Mir.cst 7)
    (Mir.pow Mir.x 4))) (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add
    (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 8)) (Mir.mul (Mir.cst 12) (Mir.pow
    Mir.x 7))) (Mir.mul (Mir.cst 14) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst
    2) (Mir.pow Mir.x 2))) (Mir.mul (Mir.cst 7) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4))) (Mir.mul (Mir.cst 24) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 7))) (by decide +kernel)

/-- The power sum's step identity at the key 8. -/
private theorem powStep8 (n : Nat) :
    10 * (n + 1) ^ 9 + 45 * (n + 1) ^ 8 + 60 * (n + 1) ^ 7 + 20 * (n + 1)
      ^ 3 + (42 * n ^ 5 + 3 * n)
      = 10 * n ^ 9 + 45 * n ^ 8 + 60 * n ^ 7 + 20 * n ^ 3 + (42 * (n + 1)
        ^ 5 + 3 * (n + 1)) + 90 * (n + 1) ^ 8 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 10)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9)) (Mir.mul (Mir.cst 45)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8))) (Mir.mul (Mir.cst 60)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7))) (Mir.mul (Mir.cst 20)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 3))) (Mir.add (Mir.mul (Mir.cst
    42) (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst 3) Mir.x))) (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9))
    (Mir.mul (Mir.cst 45) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 60)
    (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst 20) (Mir.pow Mir.x 3))) (Mir.add
    (Mir.mul (Mir.cst 42) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 5))
    (Mir.mul (Mir.cst 3) (Mir.add Mir.x (Mir.cst 1))))) (Mir.mul (Mir.cst
    90) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8))) (by decide +kernel)

/-- The power sum's step identity at the key 9. -/
private theorem powStep9 (n : Nat) :
    2 * (n + 1) ^ 10 + 10 * (n + 1) ^ 9 + 15 * (n + 1) ^ 8 + 10 * (n + 1)
      ^ 4 + (14 * n ^ 6 + 3 * n ^ 2)
      = 2 * n ^ 10 + 10 * n ^ 9 + 15 * n ^ 8 + 10 * n ^ 4 + (14 * (n + 1)
        ^ 6 + 3 * (n + 1) ^ 2) + 20 * (n + 1) ^ 9 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 10)) (Mir.mul (Mir.cst 10)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9))) (Mir.mul (Mir.cst 15)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8))) (Mir.mul (Mir.cst 10)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 4))) (Mir.add (Mir.mul (Mir.cst
    14) (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 2))))
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2)
    (Mir.pow Mir.x 10)) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9))) (Mir.mul
    (Mir.cst 15) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x
    4))) (Mir.add (Mir.mul (Mir.cst 14) (Mir.pow (Mir.add Mir.x (Mir.cst
    1)) 6)) (Mir.mul (Mir.cst 3) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    2)))) (Mir.mul (Mir.cst 20) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9)))
    (by decide +kernel)

/-- The power sum's step identity at the key 10. -/
private theorem powStep10 (n : Nat) :
    6 * (n + 1) ^ 11 + 33 * (n + 1) ^ 10 + 55 * (n + 1) ^ 9 + 66 * (n + 1)
      ^ 5 + 5 * (n + 1) + (66 * n ^ 7 + 33 * n ^ 3)
      = 6 * n ^ 11 + 33 * n ^ 10 + 55 * n ^ 9 + 66 * n ^ 5 + 5 * n + (66 *
        (n + 1) ^ 7 + 33 * (n + 1) ^ 3) + 66 * (n + 1) ^ 10 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst
    6) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 11)) (Mir.mul (Mir.cst 33)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 10))) (Mir.mul (Mir.cst 55)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9))) (Mir.mul (Mir.cst 66)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 5))) (Mir.mul (Mir.cst 5)
    (Mir.add Mir.x (Mir.cst 1)))) (Mir.add (Mir.mul (Mir.cst 66) (Mir.pow
    Mir.x 7)) (Mir.mul (Mir.cst 33) (Mir.pow Mir.x 3)))) (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow
    Mir.x 11)) (Mir.mul (Mir.cst 33) (Mir.pow Mir.x 10))) (Mir.mul
    (Mir.cst 55) (Mir.pow Mir.x 9))) (Mir.mul (Mir.cst 66) (Mir.pow Mir.x
    5))) (Mir.mul (Mir.cst 5) Mir.x)) (Mir.add (Mir.mul (Mir.cst 66)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7)) (Mir.mul (Mir.cst 33)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 3)))) (Mir.mul (Mir.cst 66)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 10))) (by decide +kernel)

/-- The vacant key's power sum is the endpoint's own count. -/
theorem powSum0_closed : ∀ n : Nat, powSum 0 n = n
  | 0 => rfl
  | n + 1 => by
    rw [powSum_succ 0 n, powSum0_closed n, Nat.pow_zero]

/-- The power sum's closed read at the key 1, cross-added. -/
theorem powSum1_closed (n : Nat) :
    2 * powSum 1 n
      = n ^ 2 + n :=
  sumClosed 1 2 (fun _ => 0) (fun n => n ^ 2 + n) rfl powStep1 n

/-- The power sum's closed read at the key 2, cross-added. -/
theorem powSum2_closed (n : Nat) :
    6 * powSum 2 n
      = 2 * n ^ 3 + 3 * n ^ 2 + n :=
  sumClosed 2 6 (fun _ => 0) (fun n => 2 * n ^ 3 + 3 * n ^ 2 + n) rfl
    powStep2 n

/-- The power sum's closed read at the key 3, cross-added. -/
theorem powSum3_closed (n : Nat) :
    4 * powSum 3 n
      = n ^ 4 + 2 * n ^ 3 + n ^ 2 :=
  sumClosed 3 4 (fun _ => 0) (fun n => n ^ 4 + 2 * n ^ 3 + n ^ 2) rfl
    powStep3 n

/-- The power sum's closed read at the key 4, cross-added. -/
theorem powSum4_closed (n : Nat) :
    30 * powSum 4 n + n
      = 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^ 3 :=
  sumClosed 4 30 (fun n => n) (fun n => 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^
    3) rfl powStep4 n

/-- The power sum's closed read at the key 5, cross-added. -/
theorem powSum5_closed (n : Nat) :
    12 * powSum 5 n + n ^ 2
      = 2 * n ^ 6 + 6 * n ^ 5 + 5 * n ^ 4 :=
  sumClosed 5 12 (fun n => n ^ 2) (fun n => 2 * n ^ 6 + 6 * n ^ 5 + 5 * n
    ^ 4) rfl powStep5 n

/-- The power sum's closed read at the key 6, cross-added. -/
theorem powSum6_closed (n : Nat) :
    42 * powSum 6 n + 7 * n ^ 3
      = 6 * n ^ 7 + 21 * n ^ 6 + 21 * n ^ 5 + n :=
  sumClosed 6 42 (fun n => 7 * n ^ 3) (fun n => 6 * n ^ 7 + 21 * n ^ 6 +
    21 * n ^ 5 + n) rfl powStep6 n

/-- The power sum's closed read at the key 7, cross-added. -/
theorem powSum7_closed (n : Nat) :
    24 * powSum 7 n + 7 * n ^ 4
      = 3 * n ^ 8 + 12 * n ^ 7 + 14 * n ^ 6 + 2 * n ^ 2 :=
  sumClosed 7 24 (fun n => 7 * n ^ 4) (fun n => 3 * n ^ 8 + 12 * n ^ 7 +
    14 * n ^ 6 + 2 * n ^ 2) rfl powStep7 n

/-- The power sum's closed read at the key 8, cross-added. -/
theorem powSum8_closed (n : Nat) :
    90 * powSum 8 n + 42 * n ^ 5 + 3 * n
      = 10 * n ^ 9 + 45 * n ^ 8 + 60 * n ^ 7 + 20 * n ^ 3 :=
  by
  rw [Nat.add_assoc (90 * powSum 8 n) (42 * n ^ 5) (3 * n)]
  exact
    sumClosed 8 90 (fun n => 42 * n ^ 5 + 3 * n) (fun n => 10 * n ^ 9 + 45
      * n ^ 8 + 60 * n ^ 7 + 20 * n ^ 3) rfl powStep8 n

/-- The power sum's closed read at the key 9, cross-added. -/
theorem powSum9_closed (n : Nat) :
    20 * powSum 9 n + 14 * n ^ 6 + 3 * n ^ 2
      = 2 * n ^ 10 + 10 * n ^ 9 + 15 * n ^ 8 + 10 * n ^ 4 :=
  by
  rw [Nat.add_assoc (20 * powSum 9 n) (14 * n ^ 6) (3 * n ^ 2)]
  exact
    sumClosed 9 20 (fun n => 14 * n ^ 6 + 3 * n ^ 2) (fun n => 2 * n ^ 10
      + 10 * n ^ 9 + 15 * n ^ 8 + 10 * n ^ 4) rfl powStep9 n

/-- The power sum's closed read at the key 10, cross-added. -/
theorem powSum10_closed (n : Nat) :
    66 * powSum 10 n + 66 * n ^ 7 + 33 * n ^ 3
      = 6 * n ^ 11 + 33 * n ^ 10 + 55 * n ^ 9 + 66 * n ^ 5 + 5 * n :=
  by
  rw [Nat.add_assoc (66 * powSum 10 n) (66 * n ^ 7) (33 * n ^ 3)]
  exact
    sumClosed 10 66 (fun n => 66 * n ^ 7 + 33 * n ^ 3) (fun n => 6 * n ^
      11 + 33 * n ^ 10 + 55 * n ^ 9 + 66 * n ^ 5 + 5 * n) rfl powStep10 n


/-- A product's square at the factors' squares. -/
theorem mulSq (a b : Nat) :
    (a * b) ^ 2
      = a ^ 2 * b ^ 2 :=
  mirEq a b (Mir.pow (Mir.mul Mir.x Mir.y) 2) (Mir.mul (Mir.pow Mir.x 2)
    (Mir.pow Mir.y 2)) (by decide +kernel)

/-- The doubled product at its two orders. -/
private theorem twoMul (a b : Nat) :
    2 * a * b
      = a * b + b * a :=
  mirEq a b (Mir.mul (Mir.mul (Mir.cst 2) Mir.x) Mir.y) (Mir.add (Mir.mul
    Mir.x Mir.y) (Mir.mul Mir.y Mir.x)) (by decide +kernel)

/-- The gap's square against the shifted pair's crossed product. -/
private theorem margShiftSq (b d : Nat) :
    d ^ 2 + 2 * (b + d) * b
      = (b + d) * (b + d) + b * b :=
  mirEq b d (Mir.add (Mir.pow Mir.y 2) (Mir.mul (Mir.mul (Mir.cst 2)
    (Mir.add Mir.x Mir.y)) Mir.x)) (Mir.add (Mir.mul (Mir.add Mir.x Mir.y)
    (Mir.add Mir.x Mir.y)) (Mir.mul Mir.x Mir.x)) (by decide +kernel)


/-- The margin at a shifted first datum is the shift. -/
theorem margShift (b d : Nat) : marg (b + d) b = d := by
  show b + d - b + (b - (b + d)) = d
  rw [ground.addSubSelfL b d, ground.subLe b (b + d) (Nat.le_add_right b d),
    Nat.add_zero d]

/-- The margin reads one value at either order. -/
theorem margComm (a b : Nat) : marg a b = marg b a :=
  Nat.add_comm (a - b) (b - a)

/-- The margin of a shared factor's two multiples is the factor's
multiple of the margin. -/
theorem marg_mul_left (c a b : Nat) : marg (c * a) (c * b) = c * marg a b := by
  match Nat.le_total b a with
  | Or.inl h =>
    obtain ⟨k, hk⟩ := Nat.le.dest h
    rw [← hk, Nat.mul_add, margShift, margShift]
  | Or.inr h =>
    obtain ⟨k, hk⟩ := Nat.le.dest h
    rw [← hk, Nat.mul_add, margComm, margShift, margComm a, margShift]

/-- The margin's square against the doubled product reads the two
squares, the trichotomy's one identity. -/
theorem margSqNat (a b : Nat) :
    marg a b ^ 2 + 2 * a * b = a * a + b * b := by
  match Nat.le_total b a with
  | Or.inl h =>
    have hd : b + (a - b) = a :=
      (Nat.add_comm b (a - b)).trans (ground.subAdd h)
    have key : marg (b + (a - b)) b ^ 2 + 2 * (b + (a - b)) * b
        = (b + (a - b)) * (b + (a - b)) + b * b := by
      rw [margShift b (a - b)]
      exact margShiftSq b (a - b)
    rw [hd] at key
    exact key
  | Or.inr h =>
    have hd : a + (b - a) = b :=
      (Nat.add_comm a (b - a)).trans (ground.subAdd h)
    have key : marg (a + (b - a)) a ^ 2 + 2 * (a + (b - a)) * a
        = (a + (b - a)) * (a + (b - a)) + a * a := by
      rw [margShift a (b - a)]
      exact margShiftSq a (b - a)
    rw [hd] at key
    rw [margComm a b, ground.mulRightComm 2 a b, Nat.add_comm (a * a) (b *
      b)]
    exact key

/-- The count pair's square: the two squares against the doubled
crossed product. -/
theorem ofCounts_sq (a b : Nat) :
    (BPair.ofCounts a b * BPair.ofCounts a b).oneValue
      (BPair.ofCounts (a * a + b * b) (a * b + b * a)) := by
  refine BPair.oneValue_symm ?_
  show (BPair.ofNat (a * a + b * b)
      + (BPair.ofNat (a * b + b * a)).swap).oneValue
    ((BPair.ofNat a + (BPair.ofNat b).swap)
      * (BPair.ofNat a + (BPair.ofNat b).swap))
  rw [BPair.sq_expand_swap (BPair.ofNat a) (BPair.ofNat b)]
  refine BPair.add_congr ?_ ?_
  · exact BPair.oneValue_trans (BPair.ofNat_add (a * a) (b * b))
      (BPair.add_congr (BPair.ofNat_mul a a) (BPair.ofNat_mul b b))
  · refine BPair.oneValue_trans
      (ground.swap_congr (BPair.ofNat_add (a * b) (b * a))) ?_
    rw [← BPair.swap_add (BPair.ofNat (a * b)) (BPair.ofNat (b * a))]
    exact BPair.add_congr (ground.swap_congr (BPair.ofNat_mul a b))
      (ground.swap_congr
        (BPair.oneValue_trans (BPair.ofNat_mul b a)
          (BPair.oneValue_of_eq
            (BPair.mul_comm (BPair.ofNat b) (BPair.ofNat a)))))

/-- The margin's square is the balance pair's own square read, the
trichotomy's one generic lemma. -/
theorem margSq_read (a b : Nat) :
    (BPair.ofNat (marg a b ^ 2)).oneValue
      (BPair.ofCounts a b * BPair.ofCounts a b) := by
  have h0 : (BPair.ofNat (marg a b ^ 2)).oneValue
      (BPair.ofCounts (marg a b ^ 2) 0) :=
    BPair.oneValue_symm (BPair.add_unit (BPair.ofNat (marg a b ^ 2)))
  refine BPair.oneValue_trans h0 ?_
  refine BPair.oneValue_trans (BPair.ofCounts_crossed ?_)
    (BPair.oneValue_symm (ofCounts_sq a b))
  rw [← twoMul a b, Nat.add_zero (a * a + b * b)]
  exact margSqNat a b

/-- A scalar passes into the fold on the right. -/
theorem foldB_mul_right {α : Type} (c : BPair) (f : α → BPair)
    (l : List α) :
    (ground.famFold BPair.add BPair.unit f l * c).oneValue
      (ground.famFold BPair.add BPair.unit (fun i => f i * c) l) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.mul_comm (ground.famFold BPair.add BPair.unit f l) c)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_mul_left c f l)) ?_
  exact BPair.oneValue_of_eq
    (ground.famFold_congr_all BPair.add BPair.unit _ _
      (fun i => BPair.mul_comm c (f i)) l)

/-- The count fold over the range reversed reads the fold itself:
the reversal is an involution of the range. -/
theorem sumNat_range_rev (f : Nat → Nat) (m : Nat) :
    ground.sumNat ((List.range (m + 1)).map (fun b => f (m - b)))
      = ground.sumNat ((List.range (m + 1)).map f) := by
  have hmem : ∀ x, 0 < countOf x (List.range (m + 1)) → x ≤ m :=
    fun x hx => Nat.le_of_lt_succ (ltOfCountRange hx)
  have hinv : ∀ x, x ≤ m → m - (m - x) = x := by
    intro x hx
    obtain ⟨d, hd⟩ := Nat.le.dest hx
    rw [← hd, ground.addSubSelfL x d, Nat.add_comm x d, ground.addSubSelfL d x]
  have hin : ∀ x, 0 < countOf (m - x) (List.range (m + 1)) := by
    intro x
    rw [countOf_range, if_pos (Nat.lt_succ_of_le (Nat.sub_le m x))]
    exact Nat.succ_pos 0
  rw [ground.sumMap, ground.sumMap]
  exact ground.famFold_bij_ov natFoldLaws.toCommLaws 0
    (fun b => f (m - b)) f (g := fun x => m - x) (h := fun x => m - x)
    (distinctList_range (m + 1)) (fun x hx => hinv x (hmem x hx))
    (fun x hx => hinv x (hmem x hx)) (fun x _ => hin x) (fun x _ => hin x)
    (fun _ _ => rfl)

/-- The margin is one value under a shared summand. -/
theorem marg_add (a b c : Nat) : marg (a + c) (b + c) = marg a b := by
  match Nat.le_total a b with
  | Or.inl h =>
    obtain ⟨d, hd⟩ := Nat.le.dest h
    rw [← hd, Nat.add_right_comm a d c, margComm (a + c) (a + c + d), margShift,
      margComm a (a + d), margShift]
  | Or.inr h =>
    obtain ⟨d, hd⟩ := Nat.le.dest h
    rw [← hd, Nat.add_right_comm b d c, margShift, margShift]

/-- The predicate count at pointwise-equal reads over the members. -/
theorem countBy_congr {p q : Nat → Bool} : ∀ l : List Nat,
    (∀ x, 0 < ground.countOf x l → p x = q x) →
    ground.countBy p l = ground.countBy q l
  | [], _ => rfl
  | a :: t, h => by
    have ha := h a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    have ht := countBy_congr t
      (fun x hx => h x (ground.countOf_cons_pos hx))
    cases hqa : q a with
    | true =>
      rw [ground.countBy_cons_true p t (ha.trans hqa),
        ground.countBy_cons_true q t hqa, ht]
    | false =>
      rw [ground.countBy_cons_false p t (ha.trans hqa),
        ground.countBy_cons_false q t hqa, ht]

/-- Two predicates refusing together count at the join. -/
theorem countBy_or {p q : Nat → Bool} : ∀ l : List Nat,
    (∀ x, 0 < ground.countOf x l → p x = true → q x = false) →
    ground.countBy (fun x => p x || q x) l
      = ground.countBy p l + ground.countBy q l
  | [], _ => rfl
  | a :: t, h => by
    have ht := countBy_or t
      (fun x hx => h x (ground.countOf_cons_pos hx))
    have hmem := h a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    cases hpa : p a with
    | true =>
      rw [ground.countBy_cons_true (fun x => p x || q x) t
          (by rw [hpa]; rfl),
        ground.countBy_cons_true p t hpa,
        ground.countBy_cons_false q t (hmem hpa), ht,
        Nat.add_assoc]
    | false =>
      cases hqa : q a with
      | true =>
        rw [ground.countBy_cons_true (fun x => p x || q x) t
            (by rw [hpa, hqa]; rfl),
          ground.countBy_cons_false p t hpa,
          ground.countBy_cons_true q t hqa, ht,
          Nat.add_left_comm]
      | false =>
        rw [ground.countBy_cons_false (fun x => p x || q x) t
            (by rw [hpa, hqa]; rfl),
          ground.countBy_cons_false p t hpa,
          ground.countBy_cons_false q t hqa, ht]

/-- The predicate and its refusal split the length. -/
theorem countBy_split (p : Nat → Bool) : ∀ l : List Nat,
    ground.countBy p l + ground.countBy (fun x => !(p x)) l
      = l.length
  | [] => rfl
  | a :: t => by
    cases hpa : p a with
    | true =>
      rw [ground.countBy_cons_true p t hpa,
        ground.countBy_cons_false (fun x => !(p x)) t
          (by rw [hpa]; rfl),
        Nat.add_assoc, countBy_split p t,
        show (a :: t).length = t.length + 1 from rfl,
        Nat.add_comm]
    | false =>
      rw [ground.countBy_cons_false p t hpa,
        ground.countBy_cons_true (fun x => !(p x)) t
          (by rw [hpa]; rfl),
        Nat.add_left_comm, countBy_split p t,
        show (a :: t).length = t.length + 1 from rfl,
        Nat.add_comm]

/-- The filter's length is the predicate's count. -/
theorem length_filterBy {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length = ground.countBy p l
  | [] => rfl
  | a :: t => by
    cases hpa : p a with
    | true =>
      rw [ground.filter_cons_true hpa,
        ground.countBy_cons_true p t hpa,
        show (a :: t.filter p).length = (t.filter p).length + 1
          from rfl,
        length_filterBy p t, Nat.add_comm]
    | false =>
      rw [ground.filter_cons_false hpa,
        ground.countBy_cons_false p t hpa, length_filterBy p t]

/-! The direction pairs' and triples' counts, and the filters at
stated keys. -/

/-- A key below a range's successor top, the range joined to its
top. -/
theorem ltSuccOfCountRangeSnoc {k d : Nat} (h : 0 < countOf k (List.range d ++ [d])) :
    k < d + 1 := by
  rw [← range_succ d] at h
  exact ltOfCountRange h

/-- The ordered direction pairs' count at the lower first, the fold
over the directions of the further directions' count. -/
def pairFold (d : Nat) : Nat :=
  famFold Nat.add 0 (fun a =>
    famFold Nat.add 0 (fun k => cond (decide (a < k)) 1 0) (List.range d)) (List.range d)

/-- The ordered direction triples' count at the directions in
order. -/
def tripleFold (d : Nat) : Nat :=
  famFold Nat.add 0 (fun a => famFold Nat.add 0 (fun b =>
    famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0) (List.range d))
      (List.range d)) (List.range d)

/-- The pairs' count grows by the directions' count at one further
direction. -/
theorem pairFold_succ (d : Nat) : pairFold (d + 1) = pairFold d + d := by
  show famFold Nat.add 0 (fun a =>
    famFold Nat.add 0 (fun k => cond (decide (a < k)) 1 0) (List.range (d + 1)))
      (List.range (d + 1)) = _
  rw [range_succ d, famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add]
  have hin : ∀ a, 0 < countOf a (List.range d) →
      famFold Nat.add 0 (fun k => cond (decide (a < k)) 1 0) (List.range d ++ [d])
        = famFold Nat.add 0 (fun k => cond (decide (a < k)) 1 0) (List.range d) + 1 := by
    intro a ha
    rw [famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add]
    show _ + (cond (decide (a < d)) 1 0 + 0) = _ + 1
    rw [decide_eq_true (ltOfCountRange ha)]
    rfl
  have htop : famFold Nat.add 0 (fun k => cond (decide (d < k)) 1 0) (List.range d ++ [d]) = 0 := by
    rw [famFold_congr_members Nat.add 0 _ (fun _ => 0) (List.range d ++ [d]) (fun k hk => by
      rw [decide_eq_false (fun h => Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ (ltSuccOfCountRangeSnoc hk))))]
      rfl), famFold_const, Nat.mul_zero]
  rw [famFold_congr_members Nat.add 0 _
    (fun a => famFold Nat.add 0 (fun k => cond (decide (a < k)) 1 0) (List.range d) + 1)
    (List.range d) hin, famFold_add_split, famFold_const, length_range]
  show pairFold d + d * 1 + (famFold Nat.add 0 (fun k => cond (decide (d < k)) 1 0)
    (List.range d ++ [d]) + 0) = pairFold d + d
  rw [htop, Nat.mul_one]
  rfl

/-- The binomial at the key one is the count. -/
theorem pasc_one : ∀ d : Nat, pasc d 1 = d
  | 0 => rfl
  | d + 1 => by
    show pasc d 0 + pasc d 1 = d + 1
    rw [pasc_one d]
    cases d with
    | zero => exact Nat.add_comm 1 0
    | succ n => exact Nat.add_comm 1 (n + 1)

/-- The ordered pairs' count is the binomial at two. -/
theorem pairFold_eq_pasc : ∀ d : Nat, pairFold d = pasc d 2
  | 0 => rfl
  | d + 1 => by
    rw [pairFold_succ d, pairFold_eq_pasc d]
    show _ = pasc d 1 + pasc d 2
    rw [pasc_one, Nat.add_comm]

/-- Twice the binomial at two joined to the count is the count's
square. -/
theorem pasc_two_read : ∀ d : Nat, 2 * pasc d 2 + d = d * d
  | 0 => rfl
  | d + 1 => by
    show 2 * (pasc d 1 + pasc d 2) + (d + 1) = (d + 1) * (d + 1)
    rw [pasc_one]
    have ih := pasc_two_read d
    have e1 : 2 * (d + pasc d 2) + (d + 1) = (2 * pasc d 2 + d) + (2 * d + 1) :=
      polEq [pasc d 2, d]
        (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 1))))
        (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.cst 1))))
        (by decide +kernel)
    rw [e1, ih]
    exact polEq [pasc d 2, d]
      (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.cst 1))))
      (Pol.mul (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 1))))
      (by decide +kernel)

/-- The triples' count grows by the pairs' count at one further
direction. -/
theorem tripleFold_succ (d : Nat) : tripleFold (d + 1) = tripleFold d + pairFold d := by
  show famFold Nat.add 0 (fun a => famFold Nat.add 0 (fun b =>
    famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0) (List.range (d + 1)))
      (List.range (d + 1))) (List.range (d + 1)) = _
  rw [range_succ d, famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add]
  -- the inner fold at a further top: the pair's read joined
  have hc : ∀ a b, b < d + 1 →
      famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0) (List.range d ++ [d])
        = famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0) (List.range d)
          + cond (decide (a < b) && decide (b < d)) 1 0 := by
    intro a b _
    rw [famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add]
    show _ + (cond (decide (a < b) && decide (b < d)) 1 0 + 0) = _
    rw [Nat.add_zero]
  -- the middle fold at a further top, at a below the top
  have hb : ∀ a, 0 < countOf a (List.range d) →
      famFold Nat.add 0 (fun b =>
        famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0)
          (List.range d ++ [d])) (List.range d ++ [d])
        = famFold Nat.add 0 (fun b =>
            famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0)
              (List.range d)) (List.range d)
          + famFold Nat.add 0 (fun b => cond (decide (a < b)) 1 0) (List.range d) := by
    intro a ha
    rw [famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add]
    have hbd : ∀ b, 0 < countOf b (List.range d) →
        famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0)
          (List.range d ++ [d])
        = famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0)
            (List.range d) + cond (decide (a < b)) 1 0 := by
      intro b hb'
      rw [hc a b (Nat.lt_succ_of_lt (ltOfCountRange hb')), decide_eq_true (ltOfCountRange hb'),
        Bool.and_true]
    rw [famFold_congr_members Nat.add 0 _
      (fun b => famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0)
        (List.range d) + cond (decide (a < b)) 1 0) (List.range d) hbd, famFold_add_split]
    -- the top's own member: b = d, every c at or below d refuses
    show _ + (famFold Nat.add 0 (fun c => cond (decide (a < d) && decide (d < c)) 1 0)
      (List.range d ++ [d]) + 0) = _
    rw [famFold_congr_members Nat.add 0 _ (fun _ => 0) (List.range d ++ [d]) (fun c hc' => by
      rw [decide_eq_false (fun h => Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ (ltSuccOfCountRangeSnoc hc')))), Bool.and_false]
      rfl), famFold_const, Nat.mul_zero]
    rfl
  rw [famFold_congr_members Nat.add 0 _
    (fun a => famFold Nat.add 0 (fun b =>
        famFold Nat.add 0 (fun c => cond (decide (a < b) && decide (b < c)) 1 0)
          (List.range d)) (List.range d)
      + famFold Nat.add 0 (fun b => cond (decide (a < b)) 1 0) (List.range d)) (List.range d) hb,
    famFold_add_split]
  -- the top's own member: a = d, every b at or below d refuses
  show tripleFold d + pairFold d + (famFold Nat.add 0 (fun b =>
    famFold Nat.add 0 (fun c => cond (decide (d < b) && decide (b < c)) 1 0)
      (List.range d ++ [d])) (List.range d ++ [d]) + 0) = _
  rw [famFold_congr_members Nat.add 0 _ (fun _ => 0) (List.range d ++ [d]) (fun b hb' => by
    rw [famFold_congr_members Nat.add 0 _ (fun _ => 0) (List.range d ++ [d]) (fun c _ => by
      rw [decide_eq_false (fun h => Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ (ltSuccOfCountRangeSnoc hb')))), Bool.false_and]
      rfl), famFold_const, Nat.mul_zero]), famFold_const, Nat.mul_zero]
  rfl

/-- The ordered triples' count is the binomial at three. -/
theorem tripleFold_eq_pasc : ∀ d : Nat, tripleFold d = pasc d 3
  | 0 => rfl
  | d + 1 => by
    rw [tripleFold_succ d, tripleFold_eq_pasc d, pairFold_eq_pasc d]
    show _ = pasc d 2 + pasc d 3
    exact Nat.add_comm _ _

/-- Six times the binomial at three joined to three times the
count's square is the count's cube joined to its double. -/
theorem pasc_three_read : ∀ d : Nat, 6 * pasc d 3 + 3 * (d * d) = d * d * d + 2 * d
  | 0 => rfl
  | d + 1 => by
    show 6 * (pasc d 2 + pasc d 3) + 3 * ((d + 1) * (d + 1)) = (d + 1) * (d + 1) * (d + 1) + 2 * (d + 1)
    have ih := pasc_three_read d
    have hp := pasc_two_read d
    refine addCancelR (3 * d) ?_
    have e1 : 6 * (pasc d 2 + pasc d 3) + 3 * ((d + 1) * (d + 1)) + 3 * d
        = 6 * pasc d 3 + 3 * (2 * pasc d 2 + d) + 3 * ((d + 1) * (d + 1)) :=
      polEq [pasc d 3, pasc d 2, d]
        (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1)))))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mon (Mon.var 2))))
        (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))))))
        (by decide +kernel)
    rw [e1, hp]
    have e2 : 6 * pasc d 3 + 3 * (d * d) + 3 * ((d + 1) * (d + 1))
        = (6 * pasc d 3 + 3 * (d * d)) + 3 * ((d + 1) * (d + 1)) := rfl
    rw [e2, ih]
    exact polEq [pasc d 3, pasc d 2, d]
      (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))))))
      (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1)))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1)))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 1))))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mon (Mon.var 2))))
      (by decide +kernel)

/-- A conditional map at a decidable condition reads the filtered
list mapped. -/
theorem filterMap_iteP {α β : Type} (c : α → Prop) [DecidablePred c] (f : α → β) :
    ∀ l : List α, l.filterMap (fun x => if c x then some (f x) else none)
      = (l.filter (fun x => decide (c x))).map f
  | [] => rfl
  | a :: t => by
    rw [List.filterMap_cons]
    by_cases h : c a
    · rw [if_pos h, filter_cons_true (p := fun x => decide (c x)) (decide_eq_true h)]
      show f a :: t.filterMap (fun x => if c x then some (f x) else none)
        = f a :: (t.filter (fun x => decide (c x))).map f
      rw [filterMap_iteP c f t]
    · rw [if_neg h, filter_cons_false (p := fun x => decide (c x)) (decide_eq_false h)]
      exact filterMap_iteP c f t

/-- A refused all-read holds a refusing member. -/
theorem exists_of_all_false {α : Type} (f : α → Bool) :
    ∀ l : List α, l.all f = false → ∃ x, x ∈ l ∧ f x = false
  | [], h => Bool.noConfusion h
  | a :: t, h => by
    cases ha : f a with
    | false => exact ⟨a, List.Mem.head t, ha⟩
    | true =>
      have h' : t.all f = false := by
        have e : (a :: t).all f = (f a && t.all f) := rfl
        rw [e, ha, Bool.true_and] at h
        exact h
      obtain ⟨x, hx, hfx⟩ := exists_of_all_false f t h'
      exact ⟨x, List.Mem.tail a hx, hfx⟩

/-- A range read at the directions a stated list selects is the
list's own read. -/
theorem all_range_pickList (f : Nat → Bool) (E : List Nat) (d : Nat)
    (hE : ∀ e, e ∈ E → e < d) :
    (List.range d).all (fun e' => !(E.any (fun e => e' == e)) || f e') = E.all f := by
  cases hall : E.all f with
  | true =>
    refine all_range_intro d (fun i _ => ?_)
    cases hany : E.any (fun e => i == e) with
    | false => rfl
    | true =>
      obtain ⟨e, he, hie⟩ := mem_of_any _ E hany
      rw [beqEqOf hie, all_of_mem f E hall e he]
      rfl
  | false =>
    obtain ⟨e, he, hfe⟩ := exists_of_all_false f E hall
    cases hr : (List.range d).all (fun e' => !(E.any (fun e => e' == e)) || f e') with
    | false => rfl
    | true =>
      have h := all_range_read d hr e (hE e he)
      rw [any_of_mem (fun e' => e == e') he (eqBeqOf rfl), hfe] at h
      exact Bool.noConfusion h

/-- A filter at two reads held apart counts each read's
filter. -/
theorem length_filter_or {α : Type} (p q : α → Bool) : ∀ l : List α,
    (∀ x, x ∈ l → p x = true → q x = false) →
    (l.filter (fun x => p x || q x)).length = (l.filter p).length + (l.filter q).length
  | [], _ => rfl
  | a :: t, h => by
    have ih := length_filter_or p q t (fun x hx => h x (List.Mem.tail a hx))
    cases hp : p a with
    | true =>
      have hq : q a = false := h a (List.Mem.head t) hp
      rw [filter_cons_true (p := fun x => p x || q x) (show (p a || q a) = true by rw [hp]; rfl),
        filter_cons_true hp, filter_cons_false hq]
      show (t.filter (fun x => p x || q x)).length + 1
        = (t.filter p).length + 1 + (t.filter q).length
      rw [ih, Nat.add_right_comm]
    | false =>
      cases hq : q a with
      | true =>
        rw [filter_cons_true (p := fun x => p x || q x) (show (p a || q a) = true by rw [hp, hq]; rfl),
          filter_cons_false hp, filter_cons_true hq]
        show (t.filter (fun x => p x || q x)).length + 1
          = (t.filter p).length + ((t.filter q).length + 1)
        rw [ih, Nat.add_assoc]
      | false =>
        rw [filter_cons_false (p := fun x => p x || q x) (show (p a || q a) = false by rw [hp, hq]; rfl),
          filter_cons_false hp, filter_cons_false hq]
        exact ih

/-- The keys below a bound at one stated key filter to one. -/
theorem length_filter_beq (e d : Nat) (he : e < d) :
    ((List.range d).filter (fun x => x == e)).length = 1 := by
  rw [length_filterBy]
  have hc : countBy (fun x => x == e) (List.range d) = countOf e (List.range d) :=
    famFold_congr_members Nat.add 0 _ _ (List.range d) (fun x _ => by
      show cond (x == e) 1 0 = cond (decide (e = x)) 1 0
      cases hx : (x == e) with
      | true => rw [decide_eq_true (beqEqOf hx).symm]
      | false =>
        rw [decide_eq_false (fun h => Bool.noConfusion ((eqBeqOf h.symm).symm.trans hx))])
  rw [hc, countOf_range_one he]

/-- The keys below a bound at two stated distinct keys filter to
two. -/
theorem length_filter_beq2 (a k d : Nat) (ha : a < d) (hk : k < d) (hak : a < k) :
    ((List.range d).filter (fun x => x == a || x == k)).length = 2 := by
  rw [length_filter_or _ _ _ (fun x _ hx => by
    rw [beqEqOf hx]
    exact neBeqOf (Nat.ne_of_lt hak)), length_filter_beq a d ha,
    length_filter_beq k d hk]

/-- The keys below a bound at three stated keys in order filter to
three. -/
theorem length_filter_beq3 (a b c d : Nat) (ha : a < d) (hb : b < d) (hc : c < d)
    (hab : a < b) (hbc : b < c) :
    ((List.range d).filter (fun x => x == a || x == b || x == c)).length = 3 := by
  rw [length_filter_or _ _ _ (fun x _ hx => by
    cases orSplitB hx with
    | inl h1 =>
      rw [beqEqOf h1]
      exact neBeqOf (Nat.ne_of_lt (Nat.lt_trans hab hbc))
    | inr h2 =>
      rw [beqEqOf h2]
      exact neBeqOf (Nat.ne_of_lt hbc)), length_filter_beq2 a b d ha hb hab,
    length_filter_beq c d hc]


/-- The vacant predicate counts at the sum's unit. -/
theorem countBy_false : ∀ l : List Nat,
    ground.countBy (fun _ => false) l = 0
  | [] => rfl
  | a :: t => by
    rw [ground.countBy_cons_false (fun _ => false) t rfl,
      countBy_false t]

/-- The key comparison's count is the key's own. -/
theorem countBy_beq (a : Nat) (l : List Nat) :
    ground.countBy (fun j => j == a) l = ground.countOf a l :=
  countBy_congr l (fun x _ => ground.beqSymm x a)

/-- The predicate count adds over a join. -/
theorem countBy_append {α : Type} (p : α → Bool) :
    ∀ u v : List α, ground.countBy p (u ++ v)
      = ground.countBy p u + ground.countBy p v
  | [], v => (Nat.zero_add (ground.countBy p v)).symm
  | a :: u, v => by
    show cond (p a) 1 0 + ground.countBy p (u ++ v)
      = cond (p a) 1 0 + ground.countBy p u + ground.countBy p v
    rw [countBy_append p u v, Nat.add_assoc]

/-- Two mapped families count at one value where the maps agree at
the accepted members. -/
theorem countBy_mapPair {β γ δ : Type} (pb : β → Bool)
    (p : γ → Bool) (q : δ → Bool) (F : β → γ) (G : β → δ)
    (hFG : ∀ b, pb b = true → p (F b) = q (G b)) :
    ∀ lb : List β, (lb.all pb) = true →
      ground.countBy p (lb.map F) = ground.countBy q (lb.map G)
  | [], _ => rfl
  | b :: t, hall => by
    have hs := ground.andSplitB (show (pb b && t.all pb) = true from hall)
    show cond (p (F b)) 1 0 + ground.countBy p (t.map F)
      = cond (q (G b)) 1 0 + ground.countBy q (t.map G)
    rw [hFG b hs.1, countBy_mapPair pb p q F G hFG t hs.2]

/-- Two paired families count at one value where the pair maps agree
at the accepted pairs. -/
theorem countBy_pairMap {α β γ δ : Type} (pa : α → Bool)
    (pb : β → Bool) (p : γ → Bool) (q : δ → Bool)
    (f : α → β → γ) (g : α → β → δ)
    (hfg : ∀ a b, pa a = true → pb b = true → p (f a b) = q (g a b))
    (lb : List β) (hlb : (lb.all pb) = true) :
    ∀ la : List α, (la.all pa) = true →
      ground.countBy p (la.flatMap (fun a => lb.map (f a)))
        = ground.countBy q (la.flatMap (fun a => lb.map (g a)))
  | [], _ => rfl
  | a :: t, hall => by
    have hs := ground.andSplitB (show (pa a && t.all pa) = true from hall)
    show ground.countBy p (lb.map (f a) ++ t.flatMap (fun a => lb.map (f a)))
      = ground.countBy q (lb.map (g a) ++ t.flatMap (fun a => lb.map (g a)))
    rw [countBy_append, countBy_append,
      countBy_mapPair pb p q (f a) (g a)
        (fun b hb => hfg a b hs.1 hb) lb hlb,
      countBy_pairMap pa pb p q f g hfg lb hlb t hs.2]

/-- Two members read true at a count of two or beyond, at distinct
positions. -/
theorem two_of_countBy {α : Type} (d : α) (p : α → Bool) :
    ∀ l : List α, 2 ≤ countBy p l →
      ∃ i j, i < l.length ∧ j < l.length ∧ i ≠ j
        ∧ p (getAt d l i) = true ∧ p (getAt d l j) = true
  | [], h => absurd h (Nat.not_succ_le_zero _)
  | a :: t, h => by
    cases hpa : p a with
    | true =>
      rw [countBy_cons_true p t hpa] at h
      match t, h with
      | [], h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero _)
      | b :: t', h =>
        cases hpb : p b with
        | true =>
          exact ⟨0, 1, Nat.succ_pos _, Nat.succ_lt_succ (Nat.succ_pos _),
            Nat.zero_ne_one, hpa, hpb⟩
        | false =>
          rw [countBy_cons_false p t' hpb, Nat.add_comm] at h
          have h' : 1 ≤ countBy p t' := Nat.le_of_succ_le_succ h
          obtain ⟨j, hj, hpj⟩ := one_of_countBy d p t' h'
          exact ⟨0, j + 2, Nat.succ_pos _, Nat.succ_lt_succ (Nat.succ_lt_succ hj),
            fun h => Nat.noConfusion h, hpa, hpj⟩
    | false =>
      rw [countBy_cons_false p t hpa] at h
      obtain ⟨i, j, hi, hj, hij, hpi, hpj⟩ := two_of_countBy d p t h
      exact ⟨i + 1, j + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hj,
        fun h => hij (Nat.succ.inj h), hpi, hpj⟩
where
  /-- One member reads true at an occupied count. -/
  one_of_countBy (d : α) (p : α → Bool) :
      ∀ l : List α, 1 ≤ countBy p l →
        ∃ i, i < l.length ∧ p (getAt d l i) = true
    | [], h => absurd h (Nat.not_succ_le_zero _)
    | a :: t, h => by
      cases hpa : p a with
      | true => exact ⟨0, Nat.succ_pos _, hpa⟩
      | false =>
        rw [countBy_cons_false p t hpa] at h
        obtain ⟨i, hi, hpi⟩ := one_of_countBy d p t h
        exact ⟨i + 1, Nat.succ_lt_succ hi, hpi⟩

/-- A member reading true occupies the count. -/
theorem countBy_pos_of_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l → p x = true → 0 < countBy p l
  | [], _, h, _ => nomatch h
  | a :: t, x, h, hx => by
    cases h with
    | head =>
      rw [countBy_cons_true p t hx]
      exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
    | tail _ hm =>
      cases hpa : p a with
      | true =>
        rw [countBy_cons_true p t hpa]
        exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
      | false => rw [countBy_cons_false p t hpa]; exact countBy_pos_of_mem p t x hm hx

/-! The keyed families' folds at a key, read through the sort kit: the
collected family and the walk's one-value read each read the family's
fold at every key. -/

/-- A keyed family's fold at one key: the members at the key
joined. -/
def keyFoldB {α : Type} (eq : α → α → Bool) (k : α)
    (l : List (α × BPair)) : BPair :=
  famFold BPair.add BPair.unit (fun p => if eq p.1 k then p.2 else BPair.unit) l

/-- The merge at a joined key reads the two lists' folds at every
key, the merge's fold at the key's guard (`mergeJoin_fold_ov`): at
a key test reading equality and a join one value with the sum. -/
theorem keyFoldB_mergeJoin {α : Type} (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (add : BPair → BPair → BPair)
    (hadd : ∀ x y, (add x y).oneValue (x + y)) (k : α)
    (fuel : Nat) (a b : List (α × BPair)) :
    (keyFoldB eq k (mergeJoin lt eq add fuel a b)).oneValue
      (keyFoldB eq k a + keyFoldB eq k b) :=
  mergeJoin_fold_ov bpairFoldLaws lt eq add
    (fun p => if eq p.1 k then p.2 else BPair.unit) (fun x y he => by
      rw [← hkeq _ _ he]
      show (if eq x.1 k then add x.2 y.2 else BPair.unit).oneValue
        ((if eq x.1 k then x.2 else BPair.unit)
          + (if eq x.1 k then y.2 else BPair.unit))
      cases eq x.1 k with
      | true => exact hadd x.2 y.2
      | false => exact BPair.oneValue_symm (BPair.unit_add _)) fuel a b

/-- A member of the merged join is a member of a factor or the two
factors' members joined at one key. -/
theorem mem_mergeJoin {α β : Type} (lt eq : α → α → Bool) (add : β → β → β) :
    ∀ (fuel : Nat) (a b : List (α × β)) (p : α × β), p ∈ mergeJoin lt eq add fuel a b →
      p ∈ a ∨ p ∈ b ∨ ∃ x y, x ∈ a ∧ y ∈ b ∧ p = (x.1, add x.2 y.2)
  | 0, a, b, p, h => by
    cases mem_append_of a b h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inl h)
  | _ + 1, [], b, p, h => by
    have h' : p ∈ ([] : List (α × β)) ++ b := h
    exact Or.inr (Or.inl h')
  | _ + 1, x :: s, [], p, h => by
    have h' : p ∈ (x :: s) ++ [] := h
    rw [append_nil] at h'
    exact Or.inl h'
  | fuel + 1, x :: s, y :: t, p, h => by
    have h' : p ∈ (if eq x.1 y.1 then (x.1, add x.2 y.2) :: mergeJoin lt eq add fuel s t
        else if lt x.1 y.1 then x :: mergeJoin lt eq add fuel s (y :: t)
        else y :: mergeJoin lt eq add fuel (x :: s) t) := h
    cases he : eq x.1 y.1 with
    | true =>
      rw [he, if_pos rfl] at h'
      cases h' with
      | head => exact Or.inr (Or.inr ⟨x, y, List.Mem.head s, List.Mem.head t, rfl⟩)
      | tail _ hm =>
        cases mem_mergeJoin lt eq add fuel s t p hm with
        | inl hs => exact Or.inl (List.Mem.tail x hs)
        | inr hr =>
          cases hr with
          | inl ht => exact Or.inr (Or.inl (List.Mem.tail y ht))
          | inr hj =>
            obtain ⟨x', y', hx', hy', hp⟩ := hj
            exact Or.inr (Or.inr ⟨x', y', List.Mem.tail x hx', List.Mem.tail y hy', hp⟩)
    | false =>
      rw [he, if_neg (fun hh : false = true => Bool.noConfusion hh)] at h'
      cases hl : lt x.1 y.1 with
      | true =>
        rw [hl, if_pos rfl] at h'
        cases h' with
        | head => exact Or.inl (List.Mem.head s)
        | tail _ hm =>
          cases mem_mergeJoin lt eq add fuel s (y :: t) p hm with
          | inl hs => exact Or.inl (List.Mem.tail x hs)
          | inr hr =>
            cases hr with
            | inl ht => exact Or.inr (Or.inl ht)
            | inr hj =>
              obtain ⟨x', y', hx', hy', hp⟩ := hj
              exact Or.inr (Or.inr ⟨x', y', List.Mem.tail x hx', hy', hp⟩)
      | false =>
        rw [hl, if_neg (fun hh : false = true => Bool.noConfusion hh)] at h'
        cases h' with
        | head => exact Or.inr (Or.inl (List.Mem.head t))
        | tail _ hm =>
          cases mem_mergeJoin lt eq add fuel (x :: s) t p hm with
          | inl hs => exact Or.inl hs
          | inr hr =>
            cases hr with
            | inl ht => exact Or.inr (Or.inl (List.Mem.tail y ht))
            | inr hj =>
              obtain ⟨x', y', hx', hy', hp⟩ := hj
              exact Or.inr (Or.inr ⟨x', y', hx', List.Mem.tail y hy', hp⟩)

/-- Each half's members are the list's own. -/
theorem mem_halvesL {α : Type} : ∀ (l : List α) (x : α),
    (x ∈ (halvesL l).1 → x ∈ l) ∧ (x ∈ (halvesL l).2 → x ∈ l)
  | [], _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | [_], _ => ⟨(fun h => h), (fun h => nomatch h)⟩
  | a :: b :: t, x =>
    ⟨fun h => by
      have h' : x ∈ a :: (halvesL t).1 := h
      cases h' with
      | head => exact List.Mem.head _
      | tail _ h2 => exact List.Mem.tail _ (List.Mem.tail _ ((mem_halvesL t x).1 h2)),
     fun h => by
      have h' : x ∈ b :: (halvesL t).2 := h
      cases h' with
      | head => exact List.Mem.tail _ (List.Mem.head _)
      | tail _ h2 => exact List.Mem.tail _ (List.Mem.tail _ ((mem_halvesL t x).2 h2))⟩

/-- A member of the sorted join reads its key at a member of the
list. -/
theorem mem_sortJoin_key {α β : Type} (lt eq : α → α → Bool) (add : β → β → β) :
    ∀ (fuel : Nat) (l : List (α × β)) (p : α × β), p ∈ sortJoin lt eq add fuel l →
      ∃ q, q ∈ l ∧ q.1 = p.1
  | 0, l, p, h => ⟨p, h, rfl⟩
  | _ + 1, [], _, h => nomatch h
  | _ + 1, [x], p, h => by
    have h' : p ∈ [x] := h
    exact ⟨p, h', rfl⟩
  | fuel + 1, x :: y :: t, p, h => by
    have h' : p ∈ mergeJoin lt eq add
        ((sortJoin lt eq add fuel (halvesL (x :: y :: t)).1).length
          + (sortJoin lt eq add fuel (halvesL (x :: y :: t)).2).length)
        (sortJoin lt eq add fuel (halvesL (x :: y :: t)).1)
        (sortJoin lt eq add fuel (halvesL (x :: y :: t)).2) := h
    cases mem_mergeJoin lt eq add _ _ _ p h' with
    | inl ha =>
      obtain ⟨q, hq, hk⟩ := mem_sortJoin_key lt eq add fuel _ p ha
      exact ⟨q, (mem_halvesL _ q).1 hq, hk⟩
    | inr hb =>
      cases hb with
      | inl hb =>
        obtain ⟨q, hq, hk⟩ := mem_sortJoin_key lt eq add fuel _ p hb
        exact ⟨q, (mem_halvesL _ q).2 hq, hk⟩
      | inr hc =>
        obtain ⟨u, _, hu, _, hp⟩ := hc
        obtain ⟨q, hq, hk⟩ := mem_sortJoin_key lt eq add fuel _ u hu
        refine ⟨q, (mem_halvesL _ q).1 hq, ?_⟩
        rw [hp]
        exact hk

/-- A member of the collection reads its key at a member of the
family. -/
theorem mem_collectBy_key {α : Type} (lt eq : α → α → Bool) (l : List (α × BPair))
    (p : α × BPair) (h : p ∈ collectBy lt eq l) : ∃ q, q ∈ l ∧ q.1 = p.1 := by
  obtain ⟨hm, _⟩ := mem_filter_of _ _ p h
  obtain ⟨r, hr, hrp⟩ := mem_map_of _ _ p hm
  have hk : r.1 = p.1 := by rw [← hrp]
  by_cases ho : keysInOrder lt l = true
  · rw [if_pos ho] at hr
    exact ⟨r, hr, hk⟩
  · rw [if_neg ho] at hr
    obtain ⟨q, hq, hqr⟩ := mem_sortJoin_key lt eq _ _ l r hr
    exact ⟨q, hq, hqr.trans hk⟩

/-- A read at every key of a family holds at every key of its
collection. -/
theorem collectBy_all_keys {α : Type} (lt eq : α → α → Bool) (P : α → Bool)
    (l : List (α × BPair)) (h : l.all (fun p => P p.1) = true) :
    (collectBy lt eq l).all (fun p => P p.1) = true := by
  refine all_of_mem_intro _ _ (fun p hp => ?_)
  obtain ⟨q, hq, hqp⟩ := mem_collectBy_key lt eq l p hp
  rw [← hqp]
  exact all_of_mem _ l h q hq

/-- The members of a family read at canonical representatives with
the unit members withdrawn are canonical and off the unit. -/
theorem mem_normFilter {α : Type} (l : List (α × BPair)) (p : α × BPair)
    (h : p ∈ (l.map (fun q => (q.1, q.2.norm))).filter (fun q => !q.2.isUnitRep)) :
    p.2.norm = p.2 ∧ p.2.isUnitRep = false := by
  obtain ⟨hm, hf⟩ := mem_filter_of _ _ p h
  obtain ⟨q, _, hq⟩ := mem_map_of _ l p hm
  refine ⟨?_, ?_⟩
  · rw [← hq]
    exact BPair.norm_congr (BPair.norm_oneValue q.2)
  · cases hu : p.2.isUnitRep with
    | false => rfl
    | true =>
      rw [hu] at hf
      exact Bool.noConfusion hf

/-- The family with the unit members withdrawn folds to the family's
fold at every key. -/
theorem keyFoldB_unitFilter {α : Type} [DecidableEq α] (eq : α → α → Bool) (k : α)
    (l : List (α × BPair)) :
    (keyFoldB eq k (l.filter (fun p => !p.2.isUnitRep))).oneValue (keyFoldB eq k l) := by
  show (famFold BPair.add BPair.unit (fun p => if eq p.1 k then p.2 else BPair.unit)
    (l.filter (fun p => !p.2.isUnitRep))).oneValue _
  refine famFold_filter_ov bpairFoldLaws _ _ (fun p hp => ?_) _
  have hu : p.2.isUnitRep = true := by
    cases h : p.2.isUnitRep with
    | true => rfl
    | false => rw [h] at hp; exact Bool.noConfusion hp
  rw [BPair.unit_of_isUnitRep hu]
  cases eq p.1 k with
  | true => rfl
  | false => rfl

/-- The family read at canonical representatives with the unit
members withdrawn folds to the family's fold at every key. -/
theorem keyFoldB_normFilter {α : Type} [DecidableEq α] (eq : α → α → Bool) (k : α)
    (l : List (α × BPair)) :
    (keyFoldB eq k ((l.map (fun p => (p.1, p.2.norm))).filter
      (fun p => !p.2.isUnitRep))).oneValue (keyFoldB eq k l) := by
  refine BPair.oneValue_trans (keyFoldB_unitFilter eq k _) ?_
  show (famFold BPair.add BPair.unit (fun p => if eq p.1 k then p.2 else BPair.unit)
    (l.map (fun p => (p.1, p.2.norm)))).oneValue _
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (famFold_map BPair.add BPair.unit _ _ _)) ?_
  refine foldB_congr_members _
    (fun p : α × BPair => if eq p.1 k then p.2 else BPair.unit) _ (fun p _ => ?_)
  show (if eq p.1 k then p.2.norm else BPair.unit).oneValue
    (if eq p.1 k then p.2 else BPair.unit)
  cases eq p.1 k with
  | true => exact BPair.norm_oneValue _
  | false => exact BPair.oneValue_refl _

/-- The collected family reads the family's fold at every key: the
sorted join at the canonical representatives' sum, read at the
representatives with the unit members withdrawn
(`keyFoldB_normFilter`). -/
theorem keyFoldB_collectBy {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (k : α) (l : List (α × BPair)) :
    (keyFoldB eq k (collectBy lt eq l)).oneValue (keyFoldB eq k l) := by
  show (keyFoldB eq k ((((if keysInOrder lt l then l
        else sortJoin lt eq (fun y x => (y + x).norm) l.length l).map
      (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep)))).oneValue _
  refine BPair.oneValue_trans (keyFoldB_normFilter eq k _) ?_
  cases hs : keysInOrder lt l with
  | true =>
    rw [if_pos rfl]
    exact BPair.oneValue_refl _
  | false =>
    rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
    apply sortJoin_fold_ov bpairFoldLaws lt eq (fun y x => (y + x).norm)
      (fun p => if eq p.1 k then p.2 else BPair.unit)
    intro x y he
    rw [← hkeq _ _ he]
    change (if eq x.1 k then (x.2 + y.2).norm else BPair.unit).oneValue
      ((if eq x.1 k then x.2 else BPair.unit)
        + (if eq x.1 k then y.2 else BPair.unit))
    cases eq x.1 k with
    | true => exact BPair.norm_oneValue _
    | false => exact BPair.oneValue_symm (BPair.unit_add _)

/-- A coefficient-linear read has one fold before and after the
collection at canonical coefficients. -/
theorem foldB_collectBy {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (f : α → BPair)
    (l : List (α × BPair)) :
    (bsum (fun p => p.2 * f p.1) (collectBy lt eq l)).oneValue
      (bsum (fun p => p.2 * f p.1) l) := by
  unfold collectBy bsum
  refine BPair.oneValue_trans (famFold_filter_read bpairFoldLaws _ _
    (fun p hp => ?_) _) ?_
  · have hu : p.2.isUnitRep = true := by
      cases h : p.2.isUnitRep with
      | true => rfl
      | false => rw [h] at hp; exact Bool.noConfusion hp
    rw [BPair.unit_of_isUnitRep hu]
    exact BPair.unit_mul _
  · rw [famFold_map]
    refine BPair.oneValue_trans (foldB_congr_members _
      (fun p : α × BPair => p.2 * f p.1) _ (fun p _ =>
        BPair.mul_congr (BPair.norm_oneValue p.2) (BPair.oneValue_refl _))) ?_
    cases hs : keysInOrder lt l with
    | true =>
      rw [if_pos rfl]
      exact BPair.oneValue_refl _
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
      apply sortJoin_fold_ov bpairFoldLaws lt eq (fun y x => (y + x).norm)
        (fun p => p.2 * f p.1)
      intro x y he
      rw [← hkeq _ _ he]
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.norm_oneValue _) (BPair.oneValue_refl _))
        (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))

/-- A keyed list at the unit throughout folds to the unit at every
key. -/
private theorem keyFoldB_units {α : Type} [DecidableEq α] (eq : α → α → Bool) (k : α)
    (a : List (α × BPair))
    (h : a.all (fun p => decide (p.2.oneValue BPair.unit)) = true) :
    (keyFoldB eq k a).oneValue BPair.unit :=
  foldB_null _ a (fun p hp => by
    have := of_decide_eq_true (all_of_mem _ a h p (mem_of_countOf_pos p a hp))
    show (if eq p.1 k then p.2 else BPair.unit).oneValue BPair.unit
    cases eq p.1 k with
    | true => exact this
    | false => exact BPair.oneValue_refl _)

/-- Two keyed lists one value at the walk read one value at every
key's fold: a shared key's two members one value, a key one list
alone occupies at the unit, and the lists at the walk's end at the
unit throughout. -/
private theorem keyFoldB_mergeEqBy {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (k : α) :
    ∀ (fuel : Nat) (a b : List (α × BPair)),
      mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
        (fun x y => decide (x.oneValue y)) fuel a b = true →
      (keyFoldB eq k a).oneValue (keyFoldB eq k b)
  | 0, a, b, h => by
    obtain ⟨ha, hb⟩ := andSplitB h
    exact BPair.oneValue_trans (keyFoldB_units eq k a ha)
      (BPair.oneValue_symm (keyFoldB_units eq k b hb))
  | _ + 1, [], b, h => by
    have h' : (([] : List (α × BPair)).all (fun p => decide (p.2.oneValue BPair.unit))
        && b.all (fun p => decide (p.2.oneValue BPair.unit))) = true := h
    obtain ⟨_, hb⟩ := andSplitB h'
    exact BPair.oneValue_trans (BPair.oneValue_refl _)
      (BPair.oneValue_symm (keyFoldB_units eq k b hb))
  | _ + 1, x :: s, [], h => by
    have h' : ((x :: s).all (fun p => decide (p.2.oneValue BPair.unit))
        && ([] : List (α × BPair)).all (fun p => decide (p.2.oneValue BPair.unit)))
        = true := h
    obtain ⟨ha, _⟩ := andSplitB h'
    exact keyFoldB_units eq k (x :: s) ha
  | fuel + 1, x :: s, y :: t, h => by
    have hun : ∀ (p : α × BPair), p.2.oneValue BPair.unit →
        (if eq p.1 k then p.2 else BPair.unit).oneValue BPair.unit := fun p hp => by
      cases eq p.1 k with
      | true => exact hp
      | false => exact BPair.oneValue_refl _
    cases he : eq x.1 y.1 with
    | true =>
      have h' : (decide (x.2.oneValue y.2)
          && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
            (fun x y => decide (x.oneValue y)) fuel s t) = true := by
        have hh := h
        rw [show mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
            (fun x y => decide (x.oneValue y)) (fuel + 1) (x :: s) (y :: t)
          = (if eq x.1 y.1 then decide (x.2.oneValue y.2)
              && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                (fun x y => decide (x.oneValue y)) fuel s t
            else if lt x.1 y.1 then decide (x.2.oneValue BPair.unit)
              && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                (fun x y => decide (x.oneValue y)) fuel s (y :: t)
            else decide (y.2.oneValue BPair.unit)
              && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                (fun x y => decide (x.oneValue y)) fuel (x :: s) t) from rfl,
          if_pos he] at hh
        exact hh
      obtain ⟨hxy, hr⟩ := andSplitB h'
      have hxy' : x.2.oneValue y.2 := of_decide_eq_true hxy
      have hk : x.1 = y.1 := hkeq _ _ he
      show ((if eq x.1 k then x.2 else BPair.unit) + keyFoldB eq k s).oneValue
        ((if eq y.1 k then y.2 else BPair.unit) + keyFoldB eq k t)
      rw [← hk]
      refine BPair.add_congr ?_ (keyFoldB_mergeEqBy lt eq hkeq k fuel s t hr)
      cases eq x.1 k with
      | true => exact hxy'
      | false => exact BPair.oneValue_refl _
    | false =>
      cases hl : lt x.1 y.1 with
      | true =>
        have h' : (decide (x.2.oneValue BPair.unit)
            && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
              (fun x y => decide (x.oneValue y)) fuel s (y :: t)) = true := by
          have hh := h
          rw [show mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
              (fun x y => decide (x.oneValue y)) (fuel + 1) (x :: s) (y :: t)
            = (if eq x.1 y.1 then decide (x.2.oneValue y.2)
                && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                  (fun x y => decide (x.oneValue y)) fuel s t
              else if lt x.1 y.1 then decide (x.2.oneValue BPair.unit)
                && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                  (fun x y => decide (x.oneValue y)) fuel s (y :: t)
              else decide (y.2.oneValue BPair.unit)
                && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                  (fun x y => decide (x.oneValue y)) fuel (x :: s) t) from rfl,
            he, if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh),
            hl, if_pos rfl] at hh
          exact hh
        obtain ⟨hx, hr⟩ := andSplitB h'
        show ((if eq x.1 k then x.2 else BPair.unit) + keyFoldB eq k s).oneValue
          (keyFoldB eq k (y :: t))
        refine BPair.oneValue_trans
          (BPair.add_congr (hun x (of_decide_eq_true hx)) (BPair.oneValue_refl _)) ?_
        exact BPair.oneValue_trans (BPair.unit_add _)
          (keyFoldB_mergeEqBy lt eq hkeq k fuel s (y :: t) hr)
      | false =>
        have h' : (decide (y.2.oneValue BPair.unit)
            && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
              (fun x y => decide (x.oneValue y)) fuel (x :: s) t) = true := by
          have hh := h
          rw [show mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
              (fun x y => decide (x.oneValue y)) (fuel + 1) (x :: s) (y :: t)
            = (if eq x.1 y.1 then decide (x.2.oneValue y.2)
                && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                  (fun x y => decide (x.oneValue y)) fuel s t
              else if lt x.1 y.1 then decide (x.2.oneValue BPair.unit)
                && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                  (fun x y => decide (x.oneValue y)) fuel s (y :: t)
              else decide (y.2.oneValue BPair.unit)
                && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
                  (fun x y => decide (x.oneValue y)) fuel (x :: s) t) from rfl,
            he, if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh),
            hl, if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)] at hh
          exact hh
        obtain ⟨hy, hr⟩ := andSplitB h'
        show (keyFoldB eq k (x :: s)).oneValue
          ((if eq y.1 k then y.2 else BPair.unit) + keyFoldB eq k t)
        refine BPair.oneValue_trans
          (keyFoldB_mergeEqBy lt eq hkeq k fuel (x :: s) t hr) ?_
        exact BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.add_congr (hun y (of_decide_eq_true hy)) (BPair.oneValue_refl _))
          (BPair.unit_add _))

/-- Two keyed families one value at every key either occupies read
one value at every key's fold. -/
theorem keyFoldB_oneValueBy {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (a b : List (α × BPair))
    (h : oneValueBy lt eq a b = true) (k : α) :
    (keyFoldB eq k a).oneValue (keyFoldB eq k b) :=
  BPair.oneValue_trans (BPair.oneValue_symm (keyFoldB_collectBy lt eq hkeq k a))
    (BPair.oneValue_trans (keyFoldB_mergeEqBy lt eq hkeq k _ _ _ h)
      (keyFoldB_collectBy lt eq hkeq k b))

/-- A keyed list walked against itself at a fuel at or beyond its
count reads one value: a reflexive key test and every member one
value with itself. -/
private theorem mergeEqBy_refl {α : Type} (lt eq : α → α → Bool)
    (hkr : ∀ a, eq a a = true) :
    ∀ (fuel : Nat) (a : List (α × BPair)), a.length ≤ fuel →
      mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
        (fun x y => decide (x.oneValue y)) fuel a a = true
  | 0, [], _ => rfl
  | _ + 1, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | fuel + 1, x :: s, h => by
    show (if eq x.1 x.1 then decide (x.2.oneValue x.2)
        && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
          (fun x y => decide (x.oneValue y)) fuel s s
      else if lt x.1 x.1 then decide (x.2.oneValue BPair.unit)
        && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
          (fun x y => decide (x.oneValue y)) fuel s (x :: s)
      else decide (x.2.oneValue BPair.unit)
        && mergeEqBy lt eq (fun c => decide (c.oneValue BPair.unit))
          (fun x y => decide (x.oneValue y)) fuel (x :: s) s) = true
    rw [if_pos (hkr x.1), decide_eq_true (BPair.oneValue_refl x.2), Bool.true_and]
    exact mergeEqBy_refl lt eq hkr fuel s (Nat.le_of_succ_le_succ h)

/-- A keyed family is one value with itself at every key. -/
theorem oneValueBy_refl {α : Type} (lt eq : α → α → Bool)
    (hkr : ∀ a, eq a a = true) (a : List (α × BPair)) :
    oneValueBy lt eq a a = true :=
  mergeEqBy_refl lt eq hkr _ _ (Nat.le_add_right _ _)

/-! The keyed lists at a strict order: a key below a sorted list's
head sits below every key of the list, a key below every key folds
to the unit, a head below a key folds away at the key, the merge
and the sorted join keep the strict order at the counts' fuel, the
collected family is sorted, two sorted lists at canonical off-unit
values reading one fold at every key are one list, and two sorted
families' walk reads their coordinate fold at the shared keys
(`mergeDot`), a member of the merged join a factor's member or a
join at one key (`mem_mergeJoin`). The order enters at its reads:
the walk and the head's fold at the transitivity and the
irreflexivity with the key test reading equality, the merge's and
the sorted join's order at the trichotomy at the key test and the
order refused besides, and the one-list read at the key test's
reflexivity. -/

/-- A key below every key of a list. -/
def ltAll {α β : Type} (lt : α → α → Bool) (x : α) (l : List (α × β)) : Bool :=
  l.all (fun p => lt x p.1)

/-- A key below a sorted list's head sits below every key of the
list, at a transitive order. -/
theorem ltAll_of_sorted {α β : Type} (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true) (x : α) :
    ∀ (y : α × β) (t : List (α × β)), keysInOrder lt (y :: t) = true →
      lt x y.1 = true → ltAll lt x (y :: t) = true
  | y, [], _, hxy => by
    show (lt x y.1 && true) = true
    rw [hxy]
    rfl
  | y, z :: t, hs, hxy => by
    have hs' : (lt y.1 z.1 && keysInOrder lt (z :: t)) = true := hs
    obtain ⟨hyz, hst⟩ := andSplitB hs'
    show (lt x y.1 && ltAll lt x (z :: t)) = true
    rw [hxy, ltAll_of_sorted lt htrans x z t hst (htrans _ _ _ hxy hyz)]
    rfl

/-- A key below every key of a list folds to the unit there, at a
key test reading equality and an irreflexive order. -/
theorem keyFoldB_of_ltAll {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (hirr : ∀ a, lt a a = false)
    (x : α) (l : List (α × BPair)) (h : ltAll lt x l = true) :
    (keyFoldB eq x l).oneValue BPair.unit :=
  foldB_null _ l (fun p hp => by
    have hx : lt x p.1 = true :=
      all_of_mem _ l h p (mem_of_countOf_pos p l hp)
    show (if eq p.1 x then p.2 else BPair.unit).oneValue BPair.unit
    cases hpx : eq p.1 x with
    | true =>
      rw [hkeq _ _ hpx, hirr x] at hx
      exact Bool.noConfusion hx
    | false => exact BPair.oneValue_refl _)

/-- A sorted list's tail is sorted. -/
theorem sorted_tail {α β : Type} (lt : α → α → Bool) (x : α × β) :
    ∀ t : List (α × β), keysInOrder lt (x :: t) = true → keysInOrder lt t = true
  | [], _ => rfl
  | y :: t, h => (andSplitB (show (lt x.1 y.1 && keysInOrder lt (y :: t)) = true from h)).2

/-- A list sorted past a head below its own head is sorted. -/
theorem sorted_cons {α β : Type} (lt : α → α → Bool) (x : α × β) :
    ∀ t : List (α × β), keysInOrder lt t = true →
      (∀ y r, t = y :: r → lt x.1 y.1 = true) → keysInOrder lt (x :: t) = true
  | [], _, _ => rfl
  | y :: r, ht, hh => by
    show (lt x.1 y.1 && keysInOrder lt (y :: r)) = true
    rw [hh y r rfl, ht]
    rfl

/-- Descending natural-key insertion preserves weak key order,
including distinct entries at an equal key. The unit payload
places the entry list in the keyed-order read. -/
theorem insertKeyDesc_order {α : Type} [DecidableEq α] (key : α → Nat) (x : α) :
    ∀ l : List α,
    keysInOrder (fun a b => decide (key b ≤ key a)) (l.map (fun a => (a, ()))) = true →
    keysInOrder (fun a b => decide (key b ≤ key a))
      ((insertKeyDesc key x l).map (fun a => (a, ()))) = true
  | [], _ => rfl
  | h :: t, hs => by
    let rel := fun a b => decide (key b ≤ key a)
    have ht := sorted_tail rel (h, ()) (t.map (fun a => (a, ()))) hs
    have hall := ltAll_of_sorted rel
      (fun _ _ _ hab hbc => decide_eq_true
        (Nat.le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
      h (h, ()) (t.map (fun a => (a, ()))) hs (decide_eq_true (Nat.le_refl _))
    change keysInOrder rel
      ((if key h < key x then x :: h :: t else h :: insertKeyDesc key x t).map _) = true
    by_cases hc : key h < key x
    · rw [if_pos hc]
      change (decide (key h ≤ key x) && keysInOrder rel ((h :: t).map (fun a => (a, ())))) = true
      rw [decide_eq_true (Nat.le_of_lt hc), hs]
      rfl
    · rw [if_neg hc]
      apply sorted_cons rel (h, ()) _ (insertKeyDesc_order key x t ht)
      intro y r he
      have hy : y ∈ (insertKeyDesc key x t).map (fun a => (a, ())) := by
        rw [he]
        exact List.Mem.head r
      obtain ⟨z, hz, hzy⟩ := mem_map_of _ _ y hy
      have hm : z ∈ x :: t := mem_of_countOf_pos _ _ (by
        rw [← countOf_insertKeyDesc key x z t]
        exact countOf_pos_of_mem hz)
      rw [← hzy]
      cases hm with
      | head => exact decide_eq_true (Nat.le_of_not_lt hc)
      | tail _ hm =>
        exact all_of_mem _ _ hall (z, ())
          (List.Mem.tail (h, ()) (mem_map_to (fun a => (a, ())) hm))

/-- The merge's head is a head of one of its two lists. -/
theorem mergeJoin_head {α β : Type} (lt eq : α → α → Bool) (add : β → β → β) :
    ∀ (fuel : Nat) (a b : List (α × β)) (z : α × β) (r : List (α × β)),
      mergeJoin lt eq add fuel a b = z :: r →
      (∃ s, a = z :: s) ∨ (∃ t, b = z :: t)
      ∨ (∃ y s w t, a = y :: s ∧ b = w :: t ∧ z.1 = y.1)
  | 0, [], b, z, r, h => Or.inr (Or.inl ⟨r, h⟩)
  | 0, x :: s, b, z, r, h => Or.inl ⟨s, by
      have hz : x = z := (List.cons.inj (show x :: (s ++ b) = z :: r from h)).1
      rw [hz]⟩
  | _ + 1, [], b, z, r, h => Or.inr (Or.inl ⟨r, h⟩)
  | _ + 1, x :: s, [], z, r, h => Or.inl ⟨s, by
      have hz : x = z := (List.cons.inj (show x :: (s ++ []) = z :: r from h)).1
      rw [hz]⟩
  | fuel + 1, x :: s, y :: t, z, r, h => by
    have h' : (if eq x.1 y.1 then (x.1, add x.2 y.2) :: mergeJoin lt eq add fuel s t
        else if lt x.1 y.1 then x :: mergeJoin lt eq add fuel s (y :: t)
        else y :: mergeJoin lt eq add fuel (x :: s) t) = z :: r := h
    cases he : eq x.1 y.1 with
    | true =>
      rw [if_pos he] at h'
      refine Or.inr (Or.inr ⟨x, s, y, t, rfl, rfl, ?_⟩)
      rw [← (List.cons.inj h').1]
    | false =>
      rw [he, if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)] at h'
      cases hl : lt x.1 y.1 with
      | true =>
        rw [if_pos hl] at h'
        exact Or.inl ⟨s, by rw [← (List.cons.inj h').1]⟩
      | false =>
        rw [hl, if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)] at h'
        exact Or.inr (Or.inl ⟨t, by rw [← (List.cons.inj h').1]⟩)

/-- The fuel at a leading member withdrawn. -/
private theorem fuelL (a b fuel : Nat) (h : a + 1 + b ≤ fuel + 1) : a + b ≤ fuel := by
  rw [Nat.succ_add] at h
  exact Nat.le_of_succ_le_succ h

/-- The fuel at a trailing member withdrawn. -/
private theorem fuelR (a b fuel : Nat) (h : a + (b + 1) ≤ fuel + 1) : a + b ≤ fuel :=
  Nat.le_of_succ_le_succ h

/-- The merge of two sorted lists at the counts' fuel is sorted: at
a transitive order, the key test reading equality, and the
trichotomy at the key test and the order refused. -/
theorem mergeJoin_sorted {α β : Type} (lt eq : α → α → Bool) (add : β → β → β)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b)
    (htri : ∀ a b, eq a b = false → lt a b = false → lt b a = true) :
    ∀ (fuel : Nat) (a b : List (α × β)), a.length + b.length ≤ fuel →
      keysInOrder lt a = true → keysInOrder lt b = true →
      keysInOrder lt (mergeJoin lt eq add fuel a b) = true
  | 0, [], [], _, _, _ => rfl
  | 0, [], _ :: t, h, _, _ =>
    absurd (Nat.le_trans (Nat.le_add_left (t.length + 1) 0) h) (Nat.not_succ_le_zero _)
  | 0, _ :: s, b, h, _, _ =>
    absurd (Nat.le_trans (Nat.le_add_right (s.length + 1) b.length) h)
      (Nat.not_succ_le_zero _)
  | _ + 1, [], b, _, _, hb => hb
  | _ + 1, x :: s, [], _, ha, _ => by
    show keysInOrder lt ((x :: s) ++ []) = true
    rw [append_nil]
    exact ha
  | fuel + 1, x :: s, y :: t, hf, ha, hb => by
    have hs := sorted_tail lt x s ha
    have ht := sorted_tail lt y t hb
    show keysInOrder lt (if eq x.1 y.1 then (x.1, add x.2 y.2) :: mergeJoin lt eq add fuel s t
      else if lt x.1 y.1 then x :: mergeJoin lt eq add fuel s (y :: t)
      else y :: mergeJoin lt eq add fuel (x :: s) t) = true
    cases he : eq x.1 y.1 with
    | true =>
      rw [if_pos rfl]
      refine sorted_cons lt _ _ (mergeJoin_sorted lt eq add htrans hkeq htri fuel s t
        (Nat.le_trans (Nat.le_succ _) (fuelL _ _ _ hf)) hs ht) ?_
      intro z r hzr
      show lt x.1 z.1 = true
      cases mergeJoin_head lt eq add fuel s t z r hzr with
      | inl hz =>
        obtain ⟨s', hs'⟩ := hz
        rw [hs'] at ha
        exact (andSplitB ha).1
      | inr hz =>
        cases hz with
        | inl hz =>
          obtain ⟨t', ht'⟩ := hz
          rw [ht'] at hb
          rw [hkeq _ _ he]
          exact (andSplitB hb).1
        | inr hz =>
          obtain ⟨y', s', _, _, hs', _, hzy⟩ := hz
          rw [hs'] at ha
          rw [hzy]
          exact (andSplitB ha).1
    | false =>
      rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
      cases hl : lt x.1 y.1 with
      | true =>
        rw [if_pos rfl]
        refine sorted_cons lt _ _ (mergeJoin_sorted lt eq add htrans hkeq htri fuel s (y :: t)
          (fuelL _ _ _ hf) hs hb) ?_
        intro z r hzr
        cases mergeJoin_head lt eq add fuel s (y :: t) z r hzr with
        | inl hz =>
          obtain ⟨s', hs'⟩ := hz
          rw [hs'] at ha
          exact (andSplitB ha).1
        | inr hz =>
          cases hz with
          | inl hz =>
            obtain ⟨t', ht'⟩ := hz
            rw [(List.cons.inj ht').1] at hl
            exact hl
          | inr hz =>
            obtain ⟨y', s', _, _, hs', _, hzy⟩ := hz
            rw [hs'] at ha
            rw [hzy]
            exact (andSplitB ha).1
      | false =>
        rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
        have hyx : lt y.1 x.1 = true := htri _ _ he hl
        refine sorted_cons lt _ _ (mergeJoin_sorted lt eq add htrans hkeq htri fuel (x :: s) t
          (fuelR _ _ _ hf) ha ht) ?_
        intro z r hzr
        cases mergeJoin_head lt eq add fuel (x :: s) t z r hzr with
        | inl hz =>
          obtain ⟨s', hs'⟩ := hz
          rw [(List.cons.inj hs').1] at hyx
          exact hyx
        | inr hz =>
          cases hz with
          | inl hz =>
            obtain ⟨t', ht'⟩ := hz
            rw [ht'] at hb
            exact (andSplitB hb).1
          | inr hz =>
            obtain ⟨y', s', _, _, hs', _, hzy⟩ := hz
            show lt y.1 z.1 = true
            rw [hzy, ← (List.cons.inj hs').1]
            exact hyx

/-- The two halves' counts join to the list's. -/
theorem halvesL_len {α : Type} : ∀ l : List α,
    (halvesL l).1.length + (halvesL l).2.length = l.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: t => by
    show (halvesL t).1.length + 1 + ((halvesL t).2.length + 1) = t.length + 1 + 1
    rw [Nat.succ_add]
    show ((halvesL t).1.length + (halvesL t).2.length + 1).succ = (t.length + 1).succ
    rw [halvesL_len t]

/-- The sorted join at a fuel at or beyond the count is sorted. -/
theorem sortJoin_sorted {α β : Type} (lt eq : α → α → Bool) (add : β → β → β)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b)
    (htri : ∀ a b, eq a b = false → lt a b = false → lt b a = true) :
    ∀ (fuel : Nat) (l : List (α × β)), l.length ≤ fuel →
      keysInOrder lt (sortJoin lt eq add fuel l) = true
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl
  | fuel + 1, x :: y :: t, h => by
    have h1 : (halvesL t).1.length ≤ t.length :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq (halvesL_len t))
    have h2 : (halvesL t).2.length ≤ t.length :=
      Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq (halvesL_len t))
    have hf : t.length + 1 ≤ fuel := Nat.le_of_succ_le_succ h
    show keysInOrder lt (mergeJoin lt eq add
      ((sortJoin lt eq add fuel (x :: (halvesL t).1)).length
        + (sortJoin lt eq add fuel (y :: (halvesL t).2)).length)
      (sortJoin lt eq add fuel (x :: (halvesL t).1))
      (sortJoin lt eq add fuel (y :: (halvesL t).2))) = true
    exact mergeJoin_sorted lt eq add htrans hkeq htri _ _ _ (Nat.le_refl _)
      (sortJoin_sorted lt eq add htrans hkeq htri fuel _
        (Nat.le_trans (Nat.succ_le_succ h1) hf))
      (sortJoin_sorted lt eq add htrans hkeq htri fuel _
        (Nat.le_trans (Nat.succ_le_succ h2) hf))

/-- A sorted list's filter is sorted, at a transitive order. -/
theorem sorted_filter {α β : Type} (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (p : α × β → Bool) :
    ∀ l : List (α × β), keysInOrder lt l = true → keysInOrder lt (l.filter p) = true
  | [], _ => rfl
  | x :: t, h => by
    have ht := sorted_tail lt x t h
    cases hp : p x with
    | true =>
      rw [filter_cons_true hp]
      refine sorted_cons lt x _ (sorted_filter lt htrans p t ht) ?_
      intro z r hzr
      have hz : z ∈ t := (mem_filter_of p t z (by rw [hzr]; exact List.Mem.head r)).1
      cases t with
      | nil => exact absurd hz (fun hh => nomatch hh)
      | cons y t' =>
        exact all_of_mem _ _ (ltAll_of_sorted lt htrans x.1 y t' ht
          (andSplitB h).1) z hz
    | false =>
      rw [filter_cons_false hp]
      exact sorted_filter lt htrans p t ht

/-- A map at the values keeps the order read. -/
theorem sorted_mapVal {α β γ : Type} (lt : α → α → Bool) (f : β → γ) :
    ∀ l : List (α × β),
      keysInOrder lt (l.map (fun p => (p.1, f p.2))) = keysInOrder lt l
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
    show (lt x.1 y.1 && keysInOrder lt ((y :: t).map (fun p => (p.1, f p.2))))
      = (lt x.1 y.1 && keysInOrder lt (y :: t))
    rw [sorted_mapVal lt f (y :: t)]

/-- The collected family is sorted. -/
theorem collectBy_sorted {α : Type} (lt eq : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b)
    (htri : ∀ a b, eq a b = false → lt a b = false → lt b a = true)
    (l : List (α × BPair)) : keysInOrder lt (collectBy lt eq l) = true := by
  show keysInOrder lt ((((if keysInOrder lt l then l
      else sortJoin lt eq (fun y x => (y + x).norm) l.length l).map
    (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep))) = true
  refine sorted_filter lt htrans _ _ ?_
  rw [sorted_mapVal lt BPair.norm]
  cases hs : keysInOrder lt l with
  | true =>
    rw [if_pos rfl]
    exact hs
  | false =>
    rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
    exact sortJoin_sorted lt eq _ htrans hkeq htri l.length l (Nat.le_refl _)

/-- A sorted family at canonical off-unit coefficients is its own
collection: its sort is itself, and the canonical map and the unit
filter fix it. -/
theorem collectBy_of_canon {α : Type} (lt eq : α → α → Bool) (l : List (α × BPair))
    (hs : keysInOrder lt l = true)
    (hc : ∀ p, p ∈ l → p.2.norm = p.2 ∧ p.2.isUnitRep = false) :
    collectBy lt eq l = l := by
  show (((if keysInOrder lt l then l
      else sortJoin lt eq (fun y x => (y + x).norm) l.length l).map
      (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep)) = l
  rw [if_pos hs]
  have hm : l.map (fun p => (p.1, p.2.norm)) = l :=
    map_eq_self_of_mem _ _ (fun p hp => by
      show (p.1, p.2.norm) = p
      rw [(hc p hp).1])
  rw [hm]
  exact filter_all _ _ (fun p hp => by
    show (!p.2.isUnitRep) = true
    rw [(hc p hp).2]
    rfl)

/-- A collected family is its own collection: sorted at canonical
off-unit coefficients (`collectBy_of_canon`). -/
theorem collectBy_idem {α : Type} (lt eq : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b)
    (htri : ∀ a b, eq a b = false → lt a b = false → lt b a = true)
    (l : List (α × BPair)) : collectBy lt eq (collectBy lt eq l) = collectBy lt eq l :=
  collectBy_of_canon lt eq _ (collectBy_sorted lt eq htrans hkeq htri l)
    (fun p hp => mem_normFilter _ p hp)

/-- A sorted list's fold at its head's key is the head's value, at a
reflexive key test reading equality and an irreflexive transitive
order. -/
theorem keyFoldB_head {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b) (hkr : ∀ a, eq a a = true)
    (hirr : ∀ a, lt a a = false) (x : α × BPair) :
    ∀ s : List (α × BPair), keysInOrder lt (x :: s) = true →
      (keyFoldB eq x.1 (x :: s)).oneValue x.2
  | [], _ => by
    show ((if eq x.1 x.1 then x.2 else BPair.unit) + BPair.unit).oneValue x.2
    rw [hkr, if_pos rfl]
    exact BPair.add_unit _
  | y :: s, h => by
    show ((if eq x.1 x.1 then x.2 else BPair.unit) + keyFoldB eq x.1 (y :: s)).oneValue x.2
    rw [hkr, if_pos rfl]
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (keyFoldB_of_ltAll lt eq hkeq hirr x.1 (y :: s)
        (ltAll_of_sorted lt htrans x.1 y s (sorted_tail lt x _ h) (andSplitB h).1))) ?_
    exact BPair.add_unit _

/-- A canonical off-unit value sits off the sum's unit. -/
theorem canon_offUnit {x : BPair} (hn : x.norm = x) (hu : x.isUnitRep = false)
    (h : x.oneValue BPair.unit) : False := by
  have := BPair.isUnitRep_norm_of_unit h
  rw [hn, hu] at this
  exact Bool.noConfusion this

/-- A key's fold off the sum's unit names a member at the key. -/
theorem keyFoldB_mem_of_offUnit {α : Type} (eq : α → α → Bool) (k : α) :
    ∀ l : List (α × BPair), ¬ (keyFoldB eq k l).oneValue BPair.unit →
      ∃ p, p ∈ l ∧ eq p.1 k = true
  | [], h => absurd (BPair.oneValue_refl _) h
  | p :: l, h => by
    cases he : eq p.1 k with
    | true => exact ⟨p, List.Mem.head l, he⟩
    | false =>
      have h' : ¬ (keyFoldB eq k l).oneValue BPair.unit := by
        intro hu
        apply h
        show ((if eq p.1 k then p.2 else BPair.unit) + keyFoldB eq k l).oneValue BPair.unit
        rw [he, if_neg (fun hh : false = true => Bool.noConfusion hh)]
        exact BPair.oneValue_trans (BPair.unit_add _) hu
      obtain ⟨q, hq, hqk⟩ := keyFoldB_mem_of_offUnit eq k l h'
      exact ⟨q, List.Mem.tail p hq, hqk⟩

/-- Two sorted lists at canonical off-unit values reading one fold at
every key are one list: at a transitive irreflexive order with the
key test reading equality and reflexive. -/
theorem sorted_unique {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b)
    (hirr : ∀ a, lt a a = false)
    (hkr : ∀ a, eq a a = true) :
    ∀ (a b : List (α × BPair)), keysInOrder lt a = true → keysInOrder lt b = true →
      (∀ p, p ∈ a → p.2.norm = p.2 ∧ p.2.isUnitRep = false) →
      (∀ p, p ∈ b → p.2.norm = p.2 ∧ p.2.isUnitRep = false) →
      (∀ k, (keyFoldB eq k a).oneValue (keyFoldB eq k b)) → a = b
  | [], [], _, _, _, _, _ => rfl
  | [], y :: t, _, hb, _, hb1, hf => by
    have h1 := hf y.1
    have h2 := keyFoldB_head lt eq htrans hkeq hkr hirr y t hb
    exact absurd (BPair.oneValue_trans (BPair.oneValue_symm h2) (BPair.oneValue_symm h1))
      (canon_offUnit (hb1 y (List.Mem.head t)).1 (hb1 y (List.Mem.head t)).2)
  | x :: s, [], ha, _, ha1, _, hf => by
    have h1 := hf x.1
    have h2 := keyFoldB_head lt eq htrans hkeq hkr hirr x s ha
    exact absurd (BPair.oneValue_trans (BPair.oneValue_symm h2) h1)
      (canon_offUnit (ha1 x (List.Mem.head s)).1 (ha1 x (List.Mem.head s)).2)
  | x :: s, y :: t, ha, hb, ha1, hb1, hf => by
    have hxs := keyFoldB_head lt eq htrans hkeq hkr hirr x s ha
    have hyt := keyFoldB_head lt eq htrans hkeq hkr hirr y t hb
    cases he : eq x.1 y.1 with
    | true =>
      have hxy : x.1 = y.1 := hkeq _ _ he
      have hv : x.2 = y.2 := by
        have h := hf x.1
        rw [hxy] at h
        rw [hxy] at hxs
        have h' : x.2.oneValue y.2 :=
          BPair.oneValue_trans (BPair.oneValue_symm hxs) (BPair.oneValue_trans h hyt)
        rw [← (ha1 x (List.Mem.head s)).1, ← (hb1 y (List.Mem.head t)).1]
        exact BPair.norm_congr h'
      have hst : s = t := by
        refine sorted_unique lt eq htrans hkeq hirr hkr s t
          (sorted_tail lt x s ha) (sorted_tail lt y t hb)
          (fun p hp => ha1 p (List.Mem.tail x hp))
          (fun p hp => hb1 p (List.Mem.tail y hp)) ?_
        intro k
        have h : ((if eq x.1 k then x.2 else BPair.unit) + keyFoldB eq k s).oneValue
          ((if eq y.1 k then y.2 else BPair.unit) + keyFoldB eq k t) := hf k
        rw [hxy, hv] at h
        rw [BPair.add_comm, BPair.add_comm _ (keyFoldB eq k t)] at h
        exact BPair.add_cancel h
      rw [hst]
      show (x.1, x.2) :: t = (y.1, y.2) :: t
      rw [hxy, hv]
    | false =>
      cases hl : lt x.1 y.1 with
      | true =>
        have h := hf x.1
        have hu : (keyFoldB eq x.1 (y :: t)).oneValue BPair.unit :=
          keyFoldB_of_ltAll lt eq hkeq hirr x.1 (y :: t)
            (ltAll_of_sorted lt htrans x.1 y t hb hl)
        exact absurd (BPair.oneValue_trans (BPair.oneValue_symm hxs)
            (BPair.oneValue_trans h hu))
          (canon_offUnit (ha1 x (List.Mem.head s)).1 (ha1 x (List.Mem.head s)).2)
      | false =>
        have h := hf y.1
        have hu : ¬ (keyFoldB eq y.1 s).oneValue BPair.unit := by
          intro hu
          have hunit : (keyFoldB eq y.1 (x :: s)).oneValue BPair.unit := by
            show ((if eq x.1 y.1 then x.2 else BPair.unit)
              + keyFoldB eq y.1 s).oneValue BPair.unit
            rw [he, if_neg (fun hh : false = true => Bool.noConfusion hh)]
            exact BPair.oneValue_trans (BPair.unit_add _) hu
          exact absurd (BPair.oneValue_trans (BPair.oneValue_symm hyt)
              (BPair.oneValue_trans (BPair.oneValue_symm h) hunit))
            (canon_offUnit (hb1 y (List.Mem.head t)).1 (hb1 y (List.Mem.head t)).2)
        have hs : ltAll lt x.1 s = true := by
          cases s with
          | nil => rfl
          | cons z s' =>
            exact ltAll_of_sorted lt htrans x.1 z s' (sorted_tail lt x (z :: s') ha)
              (andSplitB ha).1
        obtain ⟨p, hp, hpk⟩ := keyFoldB_mem_of_offUnit eq y.1 s hu
        have hxp : lt x.1 p.1 = true := all_of_mem _ s hs p hp
        rw [hkeq _ _ hpk] at hxp
        rw [hxp] at hl
        exact Bool.noConfusion hl

/-! The lexicographic order's reads: transitive, irreflexive, and
the trichotomy at the list equality and the order refused. -/

/-- The lexicographic order is transitive. -/
theorem lexLt_trans : ∀ a b c : List Nat,
    lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => Bool.noConfusion h
  | [], _ :: _, [], _, h => Bool.noConfusion h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => Bool.noConfusion h
  | _ :: _, _ :: _, [], _, h => Bool.noConfusion h
  | x :: s, y :: t, z :: u, h1, h2 => by
    show (decide (x < z) || (x == z && lexLt s u)) = true
    have h1' : (decide (x < y) || (x == y && lexLt s t)) = true := h1
    have h2' : (decide (y < z) || (y == z && lexLt t u)) = true := h2
    cases hxy : decide (x < y) with
    | true =>
      have hxy' : x < y := of_decide_eq_true hxy
      cases hyz : decide (y < z) with
      | true =>
        rw [decide_eq_true (Nat.lt_trans hxy' (of_decide_eq_true hyz))]
        rfl
      | false =>
        rw [hyz] at h2'
        have h2'' : (y == z && lexLt t u) = true := h2'
        rw [← beqEqOf (andSplitB h2'').1, decide_eq_true hxy']
        rfl
    | false =>
      rw [hxy] at h1'
      have h1'' : (x == y && lexLt s t) = true := h1'
      obtain ⟨hxy2, hst⟩ := andSplitB h1''
      rw [beqEqOf hxy2]
      cases hyz : decide (y < z) with
      | true => rfl
      | false =>
        rw [hyz] at h2'
        have h2'' : (y == z && lexLt t u) = true := h2'
        obtain ⟨hyz2, htu⟩ := andSplitB h2''
        rw [hyz2, lexLt_trans s t u hst htu]
        rfl

/-- The lexicographic order refuses a list against itself. -/
theorem lexLt_irrefl : ∀ a : List Nat, lexLt a a = false
  | [] => rfl
  | x :: s => by
    show (decide (x < x) || (x == x && lexLt s s)) = false
    rw [decide_eq_false (Nat.lt_irrefl x), lexLt_irrefl s]
    cases x == x with
    | true => rfl
    | false => rfl

/-- Two lists at the equality refused and the order refused read the
order the other way. -/
theorem lexLt_tri : ∀ a b : List Nat,
    (a == b) = false → lexLt a b = false → lexLt b a = true
  | [], [], h, _ => Bool.noConfusion h
  | [], _ :: _, _, h => Bool.noConfusion h
  | _ :: _, [], _, _ => rfl
  | x :: s, y :: t, he, hl => by
    have he' : (x == y && s == t) = false := he
    have hl' : (decide (x < y) || (x == y && lexLt s t)) = false := hl
    show (decide (y < x) || (y == x && lexLt t s)) = true
    cases hxy : x == y with
    | true =>
      have hxy' : x = y := beqEqOf hxy
      subst hxy'
      rw [hxy] at he'
      rw [decide_eq_false (Nat.lt_irrefl x), hxy] at hl'
      have hst : (s == t) = false := he'
      have hst' : lexLt s t = false := hl'
      rw [decide_eq_false (Nat.lt_irrefl x), hxy, lexLt_tri s t hst hst']
      rfl
    | false =>
      rw [hxy] at hl'
      have hxy2 : ¬ x = y := fun h => by
        rw [h, eqBeqOf rfl] at hxy
        exact Bool.noConfusion hxy
      cases hlt : decide (x < y) with
      | true =>
        rw [hlt] at hl'
        exact Bool.noConfusion hl'
      | false =>
        cases Nat.lt_or_ge y x with
        | inl h =>
          rw [decide_eq_true h]
          rfl
        | inr h =>
          have hxy3 : x < y := Nat.lt_of_le_of_ne h hxy2
          rw [decide_eq_true hxy3] at hlt
          exact Bool.noConfusion hlt

/-- A head below a key folds away at the key: the list's fold at the
key is its tail's, at an irreflexive order with the key test reading
equality. -/
theorem keyFoldB_cons_off {α : Type} (lt eq : α → α → Bool)
    (hkeq : ∀ a b, eq a b = true → a = b) (hirr : ∀ a, lt a a = false)
    (k : α) (y : α × BPair) (t : List (α × BPair)) (h : lt y.1 k = true) :
    (keyFoldB eq k (y :: t)).oneValue (keyFoldB eq k t) := by
  show ((if eq y.1 k then y.2 else BPair.unit) + keyFoldB eq k t).oneValue (keyFoldB eq k t)
  cases he : eq y.1 k with
  | true =>
    rw [hkeq _ _ he, hirr k] at h
    exact Bool.noConfusion h
  | false => exact BPair.unit_add _


/-! The keyed folds over the keys below a bound: one occupied key,
the keys off a list, and the squares' fold at distinct keys. -/

/-- A keyed fold at a key off the list's keys reads the sum's
unit. -/
theorem keyFoldB_off (l : Nat) : ∀ w : List (Nat × BPair),
    (∀ f, f ∈ w → (f.1 == l) = false) →
    (keyFoldB (fun a b => a == b) l w).oneValue BPair.unit
  | [], _ => BPair.oneValue_refl _
  | f :: t, h => by
    show ((if f.1 == l then f.2 else BPair.unit) + keyFoldB (fun a b => a == b) l t).oneValue
      BPair.unit
    rw [h f (List.Mem.head t)]
    exact BPair.oneValue_trans (BPair.unit_add _)
      (keyFoldB_off l t (fun g hg => h g (List.Mem.tail f hg)))

/-- A keyed list at distinct keys holds its head's key off every
tail member's. -/
theorem head_key_off {e : Nat × BPair} {t : List (Nat × BPair)}
    (h : distinctList ((e :: t).map Prod.fst)) : ∀ g, g ∈ t → (g.1 == e.1) = false := by
  intro g hg
  refine neBeqOf (fun heq => ?_)
  have hc := h e.1 (mem_map_to Prod.fst (List.Mem.head t))
  rw [show (e :: t).map Prod.fst = e.1 :: t.map Prod.fst from rfl, countOf_head] at hc
  have hp : 0 < countOf e.1 (t.map Prod.fst) := by
    rw [← heq]
    exact countOf_pos_of_mem (mem_map_to Prod.fst hg)
  exact absurd (Nat.le_trans (Nat.succ_le_succ hp) hc) (by decide)

/-- The squares' fold of a keyed list's reads over the keys below a
bound: at distinct keys below the bound, the members' squares'
fold. -/
theorem bsum_keyFold_sq (n : Nat) : ∀ w : List (Nat × BPair),
    (∀ f, f ∈ w → f.1 < n) → distinctList (w.map Prod.fst) →
    (bsum (fun l => keyFoldB (fun a b => a == b) l w * keyFoldB (fun a b => a == b) l w)
      (List.range n)).oneValue (bsum (fun f => f.2 * f.2) w)
  | [], _, _ => by
    refine BPair.oneValue_trans
      (bsum_congr_range_ov _ (fun _ => BPair.unit) n (fun l _ => BPair.unit_mul _)) ?_
    exact famFold_unit_ov bpairFoldLaws (fun _ => BPair.unit) (fun _ => BPair.oneValue_refl _)
      (List.range n)
  | e :: t, hlt, hd => by
    have ih := bsum_keyFold_sq n t (fun f hf => hlt f (List.Mem.tail e hf)) (distinct_tail hd)
    have hoff := head_key_off hd
    have hterm : ∀ l, l < n →
        (keyFoldB (fun a b => a == b) l (e :: t)
          * keyFoldB (fun a b => a == b) l (e :: t)).oneValue
          ((if e.1 == l then e.2 * e.2 else BPair.unit)
            + keyFoldB (fun a b => a == b) l t * keyFoldB (fun a b => a == b) l t) := by
      intro l _
      show (((if e.1 == l then e.2 else BPair.unit) + keyFoldB (fun a b => a == b) l t)
        * ((if e.1 == l then e.2 else BPair.unit) + keyFoldB (fun a b => a == b) l t)).oneValue
        ((if e.1 == l then e.2 * e.2 else BPair.unit)
          + keyFoldB (fun a b => a == b) l t * keyFoldB (fun a b => a == b) l t)
      cases hel : (e.1 == l) with
      | true =>
        have hB : (keyFoldB (fun a b => a == b) l t).oneValue BPair.unit :=
          keyFoldB_off l t (fun g hg => by
            rw [← beqEqOf hel]
            exact hoff g hg)
        refine BPair.oneValue_trans (BPair.mul_congr
          (BPair.add_congr (BPair.oneValue_refl _) hB)
          (BPair.add_congr (BPair.oneValue_refl _) hB)) ?_
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.add_unit _) (BPair.add_unit _)) ?_
        exact BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_congr hB hB))
          (BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_mul _))
            (BPair.add_unit _)))
      | false =>
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.unit_add _) (BPair.unit_add _)) ?_
        exact BPair.oneValue_symm (BPair.unit_add _)
    refine BPair.oneValue_trans (bsum_congr_range_ov _ _ n hterm) ?_
    refine BPair.oneValue_trans (foldB_add _ _ (List.range n)) ?_
    show (bsum (fun l => if e.1 == l then e.2 * e.2 else BPair.unit) (List.range n)
      + bsum (fun l => keyFoldB (fun a b => a == b) l t * keyFoldB (fun a b => a == b) l t)
        (List.range n)).oneValue
      (e.2 * e.2 + bsum (fun f => f.2 * f.2) t)
    refine BPair.add_congr (BPair.oneValue_trans (bsum_congr_range_ov _
      (fun l => if l == e.1 then e.2 * e.2 else BPair.unit) n (fun l _ => by
        rw [beqSymm e.1 l]
        exact BPair.oneValue_refl _))
      (foldB_pickBeq e.1 (e.2 * e.2) (List.range n)
        (countOf_range_one (hlt e (List.Mem.head t))))) ih

/-- A linear contraction over a finite key list reads the keyed
family's own fold when each occupied source key occurs once. -/
theorem foldB_keyFold_linear {α : Type} [DecidableEq α] (eq : α → α → Bool)
    (heq : ∀ a b, eq a b = true → a = b) (hrefl : ∀ a, eq a a = true)
    (keys : List α) (g : α → BPair) : ∀ w : List (α × BPair),
    (∀ p ∈ w, countOf p.1 keys = 1) →
    (bsum (fun k => g k * keyFoldB eq k w) keys).oneValue
      (bsum (fun p => g p.1 * p.2) w)
  | [], _ => foldB_null _ keys (fun _ _ => BPair.mul_unit _)
  | e :: t, hc => by
    have ih := foldB_keyFold_linear eq heq hrefl keys g t
      (fun p hp => hc p (List.Mem.tail e hp))
    have hterm (k : α) :
        (g k * keyFoldB eq k (e :: t)).oneValue
          ((if eq e.1 k then g e.1 * e.2 else BPair.unit) + g k * keyFoldB eq k t) := by
      change (g k * ((if eq e.1 k then e.2 else BPair.unit) + keyFoldB eq k t)).oneValue _
      rw [BPair.left_distrib]
      refine BPair.add_congr ?_ (BPair.oneValue_refl _)
      cases he : eq e.1 k with
      | true => rw [heq _ _ he]; exact BPair.oneValue_refl _
      | false => exact BPair.mul_unit _
    refine BPair.oneValue_trans (foldB_congr_members _ _ keys (fun k _ => hterm k)) ?_
    refine BPair.oneValue_trans (foldB_add _ _ keys) ?_
    change (bsum (fun k => if eq e.1 k then g e.1 * e.2 else BPair.unit) keys
      + bsum (fun k => g k * keyFoldB eq k t) keys).oneValue
      (g e.1 * e.2 + bsum (fun p => g p.1 * p.2) t)
    refine BPair.add_congr ?_ ih
    apply foldB_pick _ e.1 (g e.1 * e.2) keys (hc e (List.Mem.head t))
    · rw [hrefl, if_pos rfl]; exact BPair.oneValue_refl _
    · intro k _ hk
      rw [if_neg (fun h => hk (heq _ _ h).symm)]
      exact BPair.oneValue_refl _

/-- A linear contraction over a key range is the finite-key
contraction at the range's count-one reads. -/
theorem bsum_keyFold_linear (n : Nat) (g : Nat → BPair) (w : List (Nat × BPair))
    (hw : ∀ p ∈ w, p.1 < n) :
    (bsum (fun k => g k * keyFoldB (fun a b => a == b) k w) (List.range n)).oneValue
      (bsum (fun p => g p.1 * p.2) w) :=
  foldB_keyFold_linear (fun a b => a == b) (fun _ _ h => beqEqOf h)
    (fun _ => eqBeqOf rfl) (List.range n) g w
    (fun p hp => countOf_range_one (hw p hp))

/-! The single-key folds over the keys below a bound, and the box's
two-digit reads' factorization at the further directions. -/

/-- A fold over the keys below a bound at a read holding at one key
alone reads that key's member. -/
theorem bsum_range_single_of (P : Nat → Bool) (g : Nat → BPair) (s0 : Nat) : ∀ n : Nat,
    s0 < n → (∀ s, s < n → (P s = true ↔ s = s0)) →
    (bsum (fun s => if P s then g s else BPair.unit) (List.range n)).oneValue (g s0) := by
  intro n hn hP
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s => if s == s0 then g s0 else BPair.unit)
    n (fun s hs => ?_)) (foldB_pickBeq s0 (g s0) (List.range n) (countOf_range_one hn))
  cases hPs : P s with
  | true =>
    have e : s = s0 := (hP s hs).1 hPs
    rw [e, eqBeqOf rfl]
    exact BPair.oneValue_refl _
  | false =>
    cases hb : (s == s0) with
    | true =>
      have e : s = s0 := beqEqOf hb
      rw [e] at hPs
      rw [(hP s0 hn).2 rfl] at hPs
      exact Bool.noConfusion hPs
    | false => exact BPair.oneValue_refl _

/-- A fold over the keys below a bound at a read refused at every key reads
the sum's unit. -/
theorem bsum_range_none (P : Nat → Bool) (g : Nat → BPair) (n : Nat)
    (hP : ∀ s, s < n → P s = false) :
    (bsum (fun s => if P s then g s else BPair.unit) (List.range n)).oneValue BPair.unit := by
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun _ => BPair.unit) n (fun s hs => ?_)) ?_
  · rw [hP s hs]
    exact BPair.oneValue_refl _
  · exact famFold_unit_ov bpairFoldLaws (fun _ => BPair.unit) (fun _ => BPair.oneValue_refl _)
      (List.range n)


/-- A range fold whose members from a stated key on read the unit
reads the fold over the keys below it. -/
theorem bsum_range_prefix (F : Nat → BPair) (k : Nat) : ∀ n : Nat, k ≤ n →
    (∀ i, k ≤ i → i < n → (F i).oneValue BPair.unit) →
    (bsum F (List.range n)).oneValue (bsum F (List.range k))
  | 0, hk, _ => by
    cases k with
    | zero => exact BPair.oneValue_refl _
    | succ k => exact absurd hk (Nat.not_lt_zero k)
  | n + 1, hk, h => by
    cases Nat.lt_or_ge n k with
    | inl hnk =>
      have e : k = n + 1 := Nat.le_antisymm hk hnk
      rw [e]
      exact BPair.oneValue_refl _
    | inr hnk =>
      refine BPair.oneValue_trans (foldB_range_snoc F n) ?_
      refine BPair.oneValue_trans (BPair.add_congr
        (bsum_range_prefix F k n hnk (fun i hi hin => h i hi (Nat.lt_succ_of_lt hin)))
        (h n hnk (Nat.lt_succ_self n))) ?_
      exact BPair.add_unit _

/-- A range fold whose members off one key read the unit collapses
to that key's member. -/
theorem bsum_range_pick (F : Nat → BPair) (k n : Nat) (hk : k < n)
    (h : ∀ i, i < n → ¬ i = k → (F i).oneValue BPair.unit) :
    (bsum F (List.range n)).oneValue (F k) := by
  refine BPair.oneValue_trans (bsum_congr_range_ov F
    (fun i => if i == k then F k else BPair.unit) n (fun i hi => ?_))
    (foldB_pickBeq k (F k) (List.range n) (countOf_range_one hk))
  cases hki : (i == k) with
  | true =>
    rw [beqEqOf hki]
    exact BPair.oneValue_of_eq (if_pos rfl).symm
  | false =>
    refine BPair.oneValue_trans (h i hi (fun e => ?_))
      (BPair.oneValue_of_eq (if_neg (fun hc => Bool.noConfusion hc)).symm)
    rw [e, eqBeqOf rfl] at hki
    exact Bool.noConfusion hki

/-- A guarded unit fold at a key held by at most one member sits at
or below one. -/
theorem bsum_range_le_one (Q : Nat → Bool) (n : Nat)
    (hinj : ∀ s t, s < n → t < n → Q s = true → Q t = true → s = t) :
    bsum (fun s => if Q s then BPair.ofNat 1 else BPair.unit) (List.range n) ≤ BPair.ofNat 1 := by
  cases hany : (List.range n).any Q with
  | true =>
    obtain ⟨s0, hs0, hQ⟩ := mem_of_any Q _ hany
    have hs0n : s0 < n := ltOfMemRange hs0
    refine leB_congr_left (BPair.oneValue_symm (bsum_range_single_of Q (fun _ => BPair.ofNat 1)
      s0 n hs0n (fun s hs => ?_))) (leB_refl _)
    constructor
    · intro h
      exact hinj s s0 hs hs0n h hQ
    · intro h
      rw [h]
      exact hQ
  | false =>
    refine leB_congr_left (BPair.oneValue_symm (bsum_range_none Q (fun _ => BPair.ofNat 1) n
      (fun s hs => ?_))) (unitLeOfNat 1)
    cases hQ : Q s with
    | false => rfl
    | true =>
      rw [any_of_mem Q (memRange hs) hQ] at hany
      exact Bool.noConfusion hany

/-- The keys off a stated key below the count, read at the two
sides: one unit per key on either side of the stated key, the fold
the count's predecessor at a stated weight. -/
theorem bsum_range_sides (e : Nat) (x : BPair) : ∀ d : Nat, e < d →
    (bsum (fun k => (if e < k then x else BPair.unit) + (if k < e then x else BPair.unit))
      (List.range d)).oneValue (bsum (fun _ => x) (List.range (d - 1)))
  | 0, h => absurd h (Nat.not_lt_zero e)
  | d + 1, h => by
    refine BPair.oneValue_trans (foldB_range_snoc _ d) ?_
    show BPair.oneValue (bsum (fun k => (if e < k then x else BPair.unit)
      + (if k < e then x else BPair.unit)) (List.range d)
      + ((if e < d then x else BPair.unit) + (if d < e then x else BPair.unit)))
      (bsum (fun _ => x) (List.range d))
    cases Nat.lt_or_ge e d with
    | inl hed =>
      rw [if_pos hed, if_neg (Nat.not_lt_of_ge (Nat.le_of_lt hed))]
      refine BPair.oneValue_trans (BPair.add_congr (bsum_range_sides e x d hed)
        (BPair.add_unit x)) ?_
      cases d with
      | zero => exact absurd hed (Nat.not_lt_zero e)
      | succ d =>
        show (bsum (fun _ => x) (List.range d) + x).oneValue (bsum (fun _ => x) (List.range (d + 1)))
        exact BPair.oneValue_symm (foldB_range_snoc _ d)
    | inr hed =>
      have hde : e = d := Nat.le_antisymm (Nat.le_of_lt_succ h) hed
      rw [hde, if_neg (Nat.lt_irrefl d)]
      refine BPair.oneValue_trans (BPair.add_congr (bsum_congr_range_ov _ (fun _ => x) d
        (fun k hk => ?_)) (BPair.add_unit _)) (BPair.add_unit _)
      rw [if_neg (Nat.not_lt_of_ge (Nat.le_of_lt hk)), if_pos hk]
      exact BPair.unit_add x

/-- The digit at the unit key of a key below the base is the key. -/
theorem baseDigit_zero (b r : Nat) (hr : r < b) : baseDigit b 0 r = r := by
  show r / b ^ 0 % b = r
  rw [Nat.pow_zero, divOf (q := r) (r := 0) (Nat.succ_pos 0)
    (by rw [Nat.one_mul, Nat.add_zero]) (Nat.succ_pos 0), modOfLt r b hr]

/-- A read of the box's first two digits folds to the further
directions' count against the plane's double fold. -/
theorem bsum_box_two (b : Nat) (hb : 0 < b) (F : Nat → Nat → BPair) : ∀ d : Nat,
    (bsum (fun s => F (baseDigit b 0 s) (baseDigit b 1 s)) (List.range (b ^ (d + 2)))).oneValue
      (BPair.ofNat (b ^ d) * bsum (fun y => bsum (fun x => F x y) (List.range b)) (List.range b))
  | 0 => by
    rw [range_pow_succ b 1]
    refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (List.range b)) ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun q => bsum (fun x => F x q) (List.range b)) b (fun q hq => ?_)) ?_
    · rw [famFold_map BPair.add BPair.unit]
      have hq' : q < b := hq
      refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun r => F r q) (b ^ 1)
        (fun r hr => ?_)) ?_
      · have hr' : r < b ^ 1 := hr
        have hrb : r < b := by
          rw [← powOne b]
          exact hr'
        rw [baseDigit_split_low b 0 1 q r hb Nat.zero_lt_one, baseDigit_zero b r hrb,
          baseDigit_split_top b 1 q r hb hr' hq']
        exact BPair.oneValue_refl _
      · rw [powOne]
        exact BPair.oneValue_refl _
    · rw [Nat.pow_zero]
      exact BPair.oneValue_symm (BPair.ofNat_one_mul _)
  | d + 1 => by
    rw [show b ^ (d + 1 + 2) = b ^ (d + 2 + 1) from rfl, range_pow_succ b (d + 2)]
    refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (List.range b)) ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun _ =>
      bsum (fun s => F (baseDigit b 0 s) (baseDigit b 1 s)) (List.range (b ^ (d + 2)))) b
      (fun q hq => ?_)) ?_
    · rw [famFold_map BPair.add BPair.unit]
      refine bsum_congr_range_ov _ _ (b ^ (d + 2)) (fun r _ => ?_)
      rw [baseDigit_split_low b 0 (d + 2) q r hb (Nat.succ_pos _),
        baseDigit_split_low b 1 (d + 2) q r hb (Nat.succ_lt_succ (Nat.succ_pos _))]
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (foldB_const _ (List.range b)) ?_
      rw [length_range]
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (bsum_box_two b hb F d)) ?_
      rw [← BPair.mul_assoc]
      refine BPair.mul_congr_left ?_
      have e : b ^ (d + 1) = b * b ^ d := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [e]
      exact BPair.oneValue_symm (BPair.ofNat_mul b (b ^ d))



/-- A box read at the first two digits guarded by two direction
reads folds to the further directions' count against the guarded
plane fold, at natural summands. -/
theorem bsum_box_two_ofNat (b : Nat) (hb : 0 < b) (A B : Nat → Bool) (f : Nat → Nat → Nat)
    (g : Nat) :
    (bsum (fun s => if A (baseDigit b 0 s) && B (baseDigit b 1 s)
        then BPair.ofNat (f (baseDigit b 0 s) (baseDigit b 1 s)) else BPair.unit)
      (List.range (b ^ (g + 2)))).oneValue
      (BPair.ofNat (b ^ g * famFold Nat.add 0 (fun y => if B y
        then famFold Nat.add 0 (fun x => if A x then f x y else 0) (List.range b) else 0)
        (List.range b))) := by
  refine BPair.oneValue_trans (bsum_box_two b hb
    (fun x y => if A x && B y then BPair.ofNat (f x y) else BPair.unit) g) ?_
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) ?_)
    (BPair.oneValue_symm (BPair.ofNat_mul _ _))
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun y => BPair.ofNat (if B y
    then famFold Nat.add 0 (fun x => if A x then f x y else 0) (List.range b) else 0)) b
    (fun y _ => ?_)) (BPair.oneValue_symm (ofNat_famFold _ _))
  cases hB : B y with
  | true =>
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun x => BPair.ofNat (if A x then f x y else 0)) b (fun x _ => ?_))
      (BPair.oneValue_symm (ofNat_famFold _ _))
    cases hA : A x with
    | true => exact BPair.oneValue_refl _
    | false => exact BPair.oneValue_symm BPair.ofNat_zero
  | false =>
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun _ => BPair.unit) b
      (fun x _ => by rw [Bool.and_false]; exact BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_trans (famFold_unit_ov bpairFoldLaws (fun _ => BPair.unit)
      (fun _ => BPair.oneValue_refl _) (List.range b)) (BPair.oneValue_symm BPair.ofNat_zero)

/-- Two sorted keyed families' pairing at the walk: at a shared key
the two coefficients' product joined, a key one list alone occupies
walked past, and the lists at the fuel's end the sum's unit
(`mergeWith`). -/
def mergeDot {α : Type} (lt eq : α → α → Bool) :
    Nat → List (α × BPair) → List (α × BPair) → BPair :=
  mergeWith lt eq (fun _ _ => BPair.unit) (fun _ x y r => x * y + r)
    (fun _ r => r) (fun _ r => r)

/-- The pairing walk at a list against itself reads the
coefficient squares once each, at a reflexive key test and
one step per member. -/
theorem mergeDot_self {α : Type} (lt eq : α → α → Bool) (hrefl : ∀ a, eq a a = true) :
    ∀ (fuel : Nat) (l : List (α × BPair)), l.length ≤ fuel →
      mergeDot lt eq fuel l l = bsum (fun p => p.2 * p.2) l
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, [], _ => rfl
  | fuel + 1, p :: l, h => by
    change (if eq p.1 p.1 then p.2 * p.2 + mergeDot lt eq fuel l l
      else if lt p.1 p.1 then mergeDot lt eq fuel l (p :: l)
      else mergeDot lt eq fuel (p :: l) l) = p.2 * p.2 + bsum (fun p => p.2 * p.2) l
    rw [if_pos (hrefl p.1), mergeDot_self lt eq hrefl fuel l (Nat.le_of_succ_le_succ h)]

/-- The fuel at a member withdrawn on both sides. -/
private theorem fuelB (a b fuel : Nat) (h : a + 1 + (b + 1) ≤ fuel + 1) : a + b ≤ fuel := by
  have h' : a + 1 + b ≤ fuel := Nat.le_of_succ_le_succ h
  rw [Nat.succ_add] at h'
  exact Nat.le_of_succ_le h'

/-- The walk reads the coordinate fold: at sorted lists and a fuel
at or beyond the counts, the pairing is the fold over the first
list of each coefficient against the second list's fold at its key,
at a transitive irreflexive order with the key test reading
equality. -/
theorem mergeDot_read {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hkeq : ∀ a b, eq a b = true → a = b)
    (hirr : ∀ a, lt a a = false) :
    ∀ (fuel : Nat) (u v : List (α × BPair)), u.length + v.length ≤ fuel →
      keysInOrder lt u = true → keysInOrder lt v = true →
      (mergeDot lt eq fuel u v).oneValue
        (famFold BPair.add BPair.unit (fun p => p.2 * keyFoldB eq p.1 v) u)
  | 0, [], [], _, _, _ => BPair.oneValue_refl _
  | 0, [], _ :: t, h, _, _ =>
    absurd (Nat.le_trans (Nat.le_add_left (t.length + 1) 0) h) (Nat.not_succ_le_zero _)
  | 0, _ :: s, v, h, _, _ =>
    absurd (Nat.le_trans (Nat.le_add_right (s.length + 1) v.length) h)
      (Nat.not_succ_le_zero _)
  | _ + 1, [], _, _, _, _ => BPair.oneValue_refl _
  | _ + 1, x :: s, [], _, _, _ =>
    BPair.oneValue_symm (foldB_null _ (x :: s) (fun p _ => BPair.mul_unit p.2))
  | fuel + 1, x :: s, y :: t, h, hu, hv => by
    have hu' := sorted_tail lt x s hu
    have hv' := sorted_tail lt y t hv
    have hs : ltAll lt x.1 s = true := by
      cases s with
      | nil => rfl
      | cons z s' => exact ltAll_of_sorted lt htrans x.1 z s' hu' (andSplitB hu).1
    show (if eq x.1 y.1 then x.2 * y.2 + mergeDot lt eq fuel s t
        else if lt x.1 y.1 then mergeDot lt eq fuel s (y :: t)
        else mergeDot lt eq fuel (x :: s) t).oneValue
      (x.2 * keyFoldB eq x.1 (y :: t)
        + famFold BPair.add BPair.unit (fun p => p.2 * keyFoldB eq p.1 (y :: t)) s)
    cases he : eq x.1 y.1 with
    | true =>
      rw [if_pos rfl]
      have hxy := hkeq _ _ he
      have ht : ltAll lt y.1 t = true := by
        cases t with
        | nil => rfl
        | cons z t' => exact ltAll_of_sorted lt htrans y.1 z t' hv' (andSplitB hv).1
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (mergeDot_read lt eq htrans hkeq hirr fuel s t (fuelB _ _ _ h) hu' hv')) ?_
      refine BPair.add_congr ?_ ?_
      · rw [hxy]
        refine BPair.mul_congr (BPair.oneValue_refl _) ?_
        refine BPair.oneValue_symm ?_
        show ((if eq y.1 y.1 then y.2 else BPair.unit) + keyFoldB eq y.1 t).oneValue y.2
        rw [hxy] at he
        rw [he, if_pos rfl]
        refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
          (keyFoldB_of_ltAll lt eq hkeq hirr y.1 t ht)) ?_
        exact BPair.add_unit _
      · refine foldB_congr_members _ _ s (fun p hp => ?_)
        have hxp : lt x.1 p.1 = true := all_of_mem _ s hs p (mem_of_countOf_pos p s hp)
        rw [hxy] at hxp
        exact BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (keyFoldB_cons_off lt eq hkeq hirr p.1 y t hxp))
    | false =>
      rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
      cases hl : lt x.1 y.1 with
      | true =>
        rw [if_pos rfl]
        refine BPair.oneValue_trans (mergeDot_read lt eq htrans hkeq hirr fuel s
          (y :: t) (fuelL _ _ _ h) hu' hv) ?_
        refine BPair.oneValue_symm ?_
        refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (keyFoldB_of_ltAll lt eq hkeq hirr x.1 (y :: t)
              (ltAll_of_sorted lt htrans x.1 y t hv hl)))
          (BPair.mul_unit _)) (BPair.oneValue_refl _)) ?_
        exact BPair.unit_add _
      | false =>
        rw [if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
        refine BPair.oneValue_trans (mergeDot_read lt eq htrans hkeq hirr fuel
          (x :: s) t (fuelR _ _ _ h) hu hv') ?_
        show (x.2 * keyFoldB eq x.1 t
          + famFold BPair.add BPair.unit (fun p => p.2 * keyFoldB eq p.1 t) s).oneValue _
        refine BPair.add_congr ?_ ?_
        · refine BPair.mul_congr (BPair.oneValue_refl _) ?_
          show (keyFoldB eq x.1 t).oneValue
            ((if eq y.1 x.1 then y.2 else BPair.unit) + keyFoldB eq x.1 t)
          cases hyx : eq y.1 x.1 with
          | true =>
            have hyx' : y.1 = x.1 := hkeq _ _ hyx
            rw [hyx'] at hyx he
            rw [hyx] at he
            exact Bool.noConfusion he
          | false => exact BPair.oneValue_symm (BPair.unit_add _)
        · refine foldB_congr_members _ _ s (fun p hp => ?_)
          have hxp : lt x.1 p.1 = true := all_of_mem _ s hs p (mem_of_countOf_pos p s hp)
          refine BPair.mul_congr (BPair.oneValue_refl _) ?_
          show (keyFoldB eq p.1 t).oneValue
            ((if eq y.1 p.1 then y.2 else BPair.unit) + keyFoldB eq p.1 t)
          cases hyp : eq y.1 p.1 with
          | true =>
            rw [← hkeq _ _ hyp] at hxp
            rw [hxp] at hl
            exact Bool.noConfusion hl
          | false => exact BPair.oneValue_symm (BPair.unit_add _)

/-! The move of a segment to a list's tail by adjacent exchanges:
one member past its followers one exchange each, and a segment of
members past the members after it one member at a time, the moved
members last in their order; the key reads at the move, the count
kept, the map passing through, and the exchanges' count. -/

/-- A member moved past the stated count of its followers, one
adjacent exchange per follower. -/
def moveOne {α : Type} : Nat → Nat → List α → List α
  | _, 0, l => l
  | i, q + 1, l => moveOne (i + 1) q (adjSwap i l)

/-- The `k` members from a key moved past the `q` members after them,
one member at a time, each past every member between it and the
segment's end: the leading members kept, the trailing `q` next, the
moved members last in their order. -/
def moveK {α : Type} : Nat → Nat → Nat → List α → List α
  | _, 0, _, l => l
  | p, k + 1, q, l => moveK p k (q + 1) (moveOne p (k + q) l)

/-- The exchanges' count at the move. -/
def moveCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, q => moveCount k (q + 1) + (k + q)

theorem length_moveOne {α : Type} : ∀ (i q : Nat) (l : List α),
    (moveOne i q l).length = l.length
  | _, 0, _ => rfl
  | i, q + 1, l => by
    show (moveOne (i + 1) q (adjSwap i l)).length = l.length
    rw [length_moveOne (i + 1) q, length_adjSwap]

theorem length_moveK {α : Type} : ∀ (p k q : Nat) (l : List α),
    (moveK p k q l).length = l.length
  | _, 0, _, _ => rfl
  | p, k + 1, q, l => by
    show (moveK p k (q + 1) (moveOne p (k + q) l)).length = l.length
    rw [length_moveK p k, length_moveOne]

theorem moveOne_map {α β : Type} (f : α → β) : ∀ (i q : Nat) (l : List α),
    moveOne i q (l.map f) = (moveOne i q l).map f
  | _, 0, _ => rfl
  | i, q + 1, l => by
    show moveOne (i + 1) q (adjSwap i (l.map f)) = (moveOne (i + 1) q (adjSwap i l)).map f
    rw [adjSwap_map, moveOne_map f (i + 1) q]

theorem moveK_map {α β : Type} (f : α → β) : ∀ (p k q : Nat) (l : List α),
    moveK p k q (l.map f) = (moveK p k q l).map f
  | _, 0, _, _ => rfl
  | p, k + 1, q, l => by
    show moveK p k (q + 1) (moveOne p (k + q) (l.map f))
      = (moveK p k (q + 1) (moveOne p (k + q) l)).map f
    rw [moveOne_map, moveK_map f p k]

/-- A successor moved from the trailing summand to the middle one. -/
theorem add_succ_shift (p k q : Nat) : p + k + (q + 1) = p + (k + 1) + q := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_succ, Nat.succ_add]

/-- A successor moved from the outside to the middle summand. -/
theorem add_add_succ (p k q : Nat) : p + (k + q) + 1 = p + (k + 1) + q := by
  rw [Nat.add_assoc p (k + 1) q, Nat.succ_add k q, ← Nat.add_succ]
  rfl

/-- A key below the moved member reads its own. -/
theorem getAt_moveOne_lo {α : Type} (d : α) : ∀ (i q : Nat) (l : List α) (t : Nat),
    t < i → getAt d (moveOne i q l) t = getAt d l t
  | _, 0, _, _, _ => rfl
  | i, q + 1, l, t, ht => by
    show getAt d (moveOne (i + 1) q (adjSwap i l)) t = getAt d l t
    rw [getAt_moveOne_lo d (i + 1) q _ t (Nat.lt_succ_of_lt ht)]
    exact getAt_adjSwap_ne d i l t (Nat.ne_of_lt ht) (Nat.ne_of_lt (Nat.lt_succ_of_lt ht))

/-- A key from the moved member to below its landing reads its
successor. -/
theorem getAt_moveOne_mid {α : Type} (d : α) : ∀ (i q : Nat) (l : List α) (t : Nat),
    t < q → i + q < l.length → getAt d (moveOne i q l) (i + t) = getAt d l (i + t + 1)
  | _, 0, _, t, ht, _ => absurd ht (Nat.not_lt_zero t)
  | i, q + 1, l, 0, _, h => by
    show getAt d (moveOne (i + 1) q (adjSwap i l)) i = getAt d l (i + 1)
    rw [getAt_moveOne_lo d (i + 1) q _ i (Nat.lt_succ_self i)]
    exact getAt_adjSwap_fst d i l
      (Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) q) (by rw [Nat.succ_add]; exact h))
  | i, q + 1, l, t + 1, ht, h => by
    show getAt d (moveOne (i + 1) q (adjSwap i l)) (i + (t + 1)) = getAt d l (i + (t + 1) + 1)
    rw [Nat.add_succ i t, ← Nat.succ_add i t]
    rw [getAt_moveOne_mid d (i + 1) q _ t (Nat.lt_of_succ_lt_succ ht)
      (by rw [length_adjSwap, Nat.succ_add]; exact h)]
    exact getAt_adjSwap_ne d i l (i + 1 + t + 1)
      (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self i)
        (Nat.le_trans (Nat.le_add_right (i + 1) t) (Nat.le_succ _))))
      (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) t) (Nat.lt_succ_self _)))

/-- The landing key reads the moved member. -/
theorem getAt_moveOne_hi {α : Type} (d : α) : ∀ (i q : Nat) (l : List α),
    i + q < l.length → getAt d (moveOne i q l) (i + q) = getAt d l i
  | _, 0, _, _ => rfl
  | i, q + 1, l, h => by
    show getAt d (moveOne (i + 1) q (adjSwap i l)) (i + (q + 1)) = getAt d l i
    rw [Nat.add_succ i q, ← Nat.succ_add i q,
      getAt_moveOne_hi d (i + 1) q _ (by rw [length_adjSwap, Nat.succ_add]; exact h)]
    exact getAt_adjSwap_snd d i l
      (Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) q) (by rw [Nat.succ_add]; exact h))

/-- A key below the segment reads its own at the segment's move. -/
theorem getAt_moveK_lo {α : Type} (d : α) : ∀ (p k q : Nat) (l : List α) (t : Nat),
    t < p → getAt d (moveK p k q l) t = getAt d l t
  | _, 0, _, _, _, _ => rfl
  | p, k + 1, q, l, t, ht => by
    show getAt d (moveK p k (q + 1) (moveOne p (k + q) l)) t = _
    rw [getAt_moveK_lo d p k (q + 1) _ t ht, getAt_moveOne_lo d p (k + q) l t ht]

/-- A key across the trailing members reads its own joined to the
segment's count. -/
theorem getAt_moveK_mid {α : Type} (d : α) : ∀ (p k q : Nat) (l : List α) (t : Nat),
    t < q → p + k + q ≤ l.length →
    getAt d (moveK p k q l) (p + t) = getAt d l (p + k + t)
  | p, 0, _, l, t, _, _ => by
    show getAt d l (p + t) = getAt d l (p + 0 + t)
    rw [Nat.add_zero]
  | p, k + 1, q, l, t, ht, h => by
    show getAt d (moveK p k (q + 1) (moveOne p (k + q) l)) (p + t) = getAt d l (p + (k + 1) + t)
    rw [getAt_moveK_mid d p k (q + 1) _ t (Nat.lt_succ_of_lt ht)
      (by rw [length_moveOne, add_succ_shift]; exact h)]
    rw [Nat.add_assoc p k t,
      getAt_moveOne_mid d p (k + q) l (k + t) (Nat.add_lt_add_left ht k)
        (Nat.lt_of_succ_le (by rw [Nat.succ_eq_add_one, add_add_succ]; exact h)),
      add_add_succ]

/-- A key at the moved members reads its own less the trailing
count. -/
theorem getAt_moveK_hi {α : Type} (d : α) : ∀ (p k q : Nat) (l : List α) (t : Nat),
    t < k → p + k + q ≤ l.length →
    getAt d (moveK p k q l) (p + q + t) = getAt d l (p + t)
  | _, 0, _, _, t, ht, _ => absurd ht (Nat.not_lt_zero t)
  | p, k + 1, q, l, 0, _, h => by
    show getAt d (moveK p k (q + 1) (moveOne p (k + q) l)) (p + q) = getAt d l p
    rw [getAt_moveK_mid d p k (q + 1) _ q (Nat.lt_succ_self q)
        (by rw [length_moveOne, add_succ_shift]; exact h),
      Nat.add_assoc]
    exact getAt_moveOne_hi d p (k + q) l
      (Nat.lt_of_succ_le (by rw [Nat.succ_eq_add_one, add_add_succ]; exact h))
  | p, k + 1, q, l, t + 1, ht, h => by
    show getAt d (moveK p k (q + 1) (moveOne p (k + q) l)) (p + q + (t + 1))
      = getAt d l (p + (t + 1))
    rw [Nat.add_succ (p + q) t, ← Nat.succ_add (p + q) t, Nat.succ_eq_add_one, Nat.add_assoc p q 1,
      getAt_moveK_hi d p k (q + 1) _ t (Nat.lt_of_succ_lt_succ ht)
        (by rw [length_moveOne, add_succ_shift]; exact h),
      getAt_moveOne_mid d p (k + q) l t
        (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt_succ ht) (Nat.le_add_right k q))
        (Nat.lt_of_succ_le (by rw [Nat.succ_eq_add_one, add_add_succ]; exact h)),
      Nat.add_assoc]

/-- A key below the orders' sum sits below the leading order, or
across the middle order, or across the trailing one. -/
theorem idx3 (p k q t : Nat) (ht : t < p + k + q) :
    t < p ∨ (∃ s, s < q ∧ t = p + s) ∨ (∃ s, s < k ∧ t = p + q + s) := by
  rw [Nat.add_assoc, Nat.add_comm k q, ← Nat.add_assoc] at ht
  cases blockIdx (p + q) k t ht with
  | inl h =>
    cases blockIdx p q t h with
    | inl h1 => exact Or.inl h1
    | inr h1 => exact Or.inr (Or.inl h1)
  | inr h => exact Or.inr (Or.inr h)

/-- The key read at the segment's move: a key below the segment its
own, a key across the trailing members its own joined to the
segment's count, a key at the moved members its own less the
trailing count, and a key beyond its own. -/
def mvIx (p k q t : Nat) : Nat :=
  if t < p then t else if t < p + q then t + k
  else if t < p + q + k then t - q else t

/-- The key read below the segment. -/
theorem mvIx_lo (p k q : Nat) {t : Nat} (h : t < p) : mvIx p k q t = t := by
  show (if t < p then t else _) = t
  rw [if_pos h]

/-- The key read across the trailing members. -/
theorem mvIx_mid (p k q : Nat) {t : Nat} (h : t < q) : mvIx p k q (p + t) = p + k + t := by
  show (if p + t < p then p + t else if p + t < p + q then p + t + k else _) = p + k + t
  rw [if_neg (Nat.not_lt_of_le (Nat.le_add_right p t)), if_pos (Nat.add_lt_add_left h p),
    Nat.add_assoc, Nat.add_comm t k, ← Nat.add_assoc]

/-- The key read at the moved members. -/
theorem mvIx_hi (p k q : Nat) {t : Nat} (h : t < k) : mvIx p k q (p + q + t) = p + t := by
  show (if p + q + t < p then p + q + t else if p + q + t < p + q then p + q + t + k
    else if p + q + t < p + q + k then p + q + t - q else p + q + t) = p + t
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans (Nat.le_add_right p q) (Nat.le_add_right _ t))),
    if_neg (Nat.not_lt_of_le (Nat.le_add_right _ t)), if_pos (Nat.add_lt_add_left h _),
    Nat.add_assoc p q t, Nat.add_comm q t, ← Nat.add_assoc, addSubSelfR]

/-- The key read beyond the segment. -/
theorem mvIx_past (p k q : Nat) {t : Nat} (h : p + q + k ≤ t) : mvIx p k q t = t := by
  show (if t < p then t else if t < p + q then t + k else if t < p + q + k then t - q else t) = t
  rw [if_neg (Nat.not_lt_of_le (Nat.le_trans (Nat.le_trans (Nat.le_add_right p q)
      (Nat.le_add_right _ k)) h)),
    if_neg (Nat.not_lt_of_le (Nat.le_trans (Nat.le_add_right _ k) h)),
    if_neg (Nat.not_lt_of_le h)]

/-- The segment's move reads every key of the segment through
`mvIx`. -/
theorem getAt_moveK {α : Type} (d : α) (p k q : Nat) (l : List α) (t : Nat)
    (ht : t < p + k + q) (hl : p + k + q ≤ l.length) :
    getAt d (moveK p k q l) t = getAt d l (mvIx p k q t) := by
  cases idx3 p k q t ht with
  | inl h => rw [getAt_moveK_lo d p k q l t h, mvIx_lo p k q h]
  | inr h =>
    cases h with
    | inl h =>
      obtain ⟨s, hs, rfl⟩ := h
      rw [getAt_moveK_mid d p k q l s hs hl, mvIx_mid p k q hs]
    | inr h =>
      obtain ⟨s, hs, rfl⟩ := h
      rw [getAt_moveK_hi d p k q l s hs hl, mvIx_hi p k q hs]

/-- The key read keeps the segment. -/
theorem mvIx_lt (p k q : Nat) {t : Nat} (h : t < p + k + q) : mvIx p k q t < p + k + q := by
  cases idx3 p k q t h with
  | inl h1 =>
    rw [mvIx_lo p k q h1]
    exact h
  | inr h1 =>
    cases h1 with
    | inl h1 =>
      obtain ⟨s, hs, rfl⟩ := h1
      rw [mvIx_mid p k q hs]
      exact Nat.add_lt_add_left hs _
    | inr h1 =>
      obtain ⟨s, hs, rfl⟩ := h1
      rw [mvIx_hi p k q hs]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hs p) (Nat.le_add_right _ q)

/-- The key read is injective on the segment. -/
theorem mvIx_inj (p k q : Nat) {t s : Nat} (ht : t < p + k + q) (hs : s < p + k + q)
    (h : mvIx p k q t = mvIx p k q s) : t = s := by
  cases idx3 p k q t ht with
  | inl h1 =>
    rw [mvIx_lo p k q h1] at h
    cases idx3 p k q s hs with
    | inl h2 => rw [mvIx_lo p k q h2] at h; exact h
    | inr h2 =>
      cases h2 with
      | inl h2 =>
        obtain ⟨u, hu, rfl⟩ := h2
        rw [mvIx_mid p k q hu] at h
        exact absurd (h ▸ h1) (Nat.not_lt_of_le (Nat.le_trans (Nat.le_add_right p k)
          (Nat.le_add_right _ u)))
      | inr h2 =>
        obtain ⟨u, hu, rfl⟩ := h2
        rw [mvIx_hi p k q hu] at h
        exact absurd (h ▸ h1) (Nat.not_lt_of_le (Nat.le_add_right p u))
  | inr h1 =>
    cases h1 with
    | inl h1 =>
      obtain ⟨u, hu, rfl⟩ := h1
      rw [mvIx_mid p k q hu] at h
      cases idx3 p k q s hs with
      | inl h2 =>
        rw [mvIx_lo p k q h2] at h
        exact absurd (h ▸ h2) (Nat.not_lt_of_le (Nat.le_trans (Nat.le_add_right p k)
          (Nat.le_add_right _ u)))
      | inr h2 =>
        cases h2 with
        | inl h2 =>
          obtain ⟨v, hv, rfl⟩ := h2
          rw [mvIx_mid p k q hv] at h
          rw [addCancelL (p + k) h]
        | inr h2 =>
          obtain ⟨v, hv, rfl⟩ := h2
          rw [mvIx_hi p k q hv] at h
          have h' : k + u = v := addCancelL p (by rw [← Nat.add_assoc]; exact h)
          exact absurd (h' ▸ hv) (Nat.not_lt_of_le (Nat.le_add_right k u))
    | inr h1 =>
      obtain ⟨u, hu, rfl⟩ := h1
      rw [mvIx_hi p k q hu] at h
      cases idx3 p k q s hs with
      | inl h2 =>
        rw [mvIx_lo p k q h2] at h
        exact absurd (h ▸ h2) (Nat.not_lt_of_le (Nat.le_add_right p u))
      | inr h2 =>
        cases h2 with
        | inl h2 =>
          obtain ⟨v, hv, rfl⟩ := h2
          rw [mvIx_mid p k q hv] at h
          have h' : u = k + v := addCancelL p (by rw [← Nat.add_assoc]; exact h)
          exact absurd (h' ▸ hu) (Nat.not_lt_of_le (Nat.le_add_right k v))
        | inr h2 =>
          obtain ⟨v, hv, rfl⟩ := h2
          rw [mvIx_hi p k q hv] at h
          rw [addCancelL p h]

/-! The balance partner iterated, the sign of an exchange count. -/

/-- The balance partner iterated. -/
def BPair.swapN : Nat → BPair → BPair
  | 0, x => x
  | n + 1, x => (BPair.swapN n x).swap

theorem BPair.swapN_swap : ∀ (n : Nat) (x : BPair), BPair.swapN n x.swap = (BPair.swapN n x).swap
  | 0, _ => rfl
  | n + 1, x => by
    show (BPair.swapN n x.swap).swap = (BPair.swapN n x).swap.swap
    rw [BPair.swapN_swap n x]

theorem BPair.swapN_add : ∀ (m n : Nat) (x : BPair),
    BPair.swapN (m + n) x = BPair.swapN m (BPair.swapN n x)
  | 0, n, x => by
    show BPair.swapN (0 + n) x = BPair.swapN n x
    rw [Nat.zero_add]
  | m + 1, n, x => by
    show BPair.swapN (m + 1 + n) x = (BPair.swapN m (BPair.swapN n x)).swap
    rw [Nat.succ_add]
    show (BPair.swapN (m + n) x).swap = _
    rw [BPair.swapN_add m n x]

theorem BPair.swapN_unit : ∀ n : Nat, BPair.swapN n BPair.unit = BPair.unit
  | 0 => rfl
  | n + 1 => by
    show (BPair.swapN n BPair.unit).swap = BPair.unit
    rw [BPair.swapN_unit n]
    rfl

theorem BPair.swapN_mul : ∀ (n : Nat) (x y : BPair),
    BPair.swapN n x * y = BPair.swapN n (x * y)
  | 0, _, _ => rfl
  | n + 1, x, y => by
    show (BPair.swapN n x).swap * y = (BPair.swapN n (x * y)).swap
    rw [BPair.swap_mul, BPair.swapN_mul n x y]

theorem BPair.swapN_congr (n : Nat) {x y : BPair} (h : x.oneValue y) :
    (BPair.swapN n x).oneValue (BPair.swapN n y) := by
  induction n with
  | zero => exact h
  | succ n ih => exact swap_congr ih

theorem BPair.swapN_offUnit (n : Nat) {x : BPair} (h : ¬ x.oneValue BPair.unit) :
    ¬ (BPair.swapN n x).oneValue BPair.unit := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro hh
    exact ih (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.swap_swap _).symm)
      (swap_congr hh))

/-! The equality diagonal and the composed count's fold: at a
positional delta the index family's squares collect from the delta's
double fold, and a double fold whose count is a count joined to the
delta collects the squares joined to the count's own double fold. -/

/-- The equality diagonal as the delta double fold: at a positional
delta the family's squares collect from the double fold. -/
theorem deltaFold (n : Nat) (dl : Nat → Nat → Nat)
    (uu : Nat → BPair)
    (hdl : ∀ i j, i < n → j < n →
      dl i j = if i = j then 1 else 0) :
    (bsum (fun i => uu i * uu i) (List.range n)).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (dl i j) * (uu i * uu j)) (List.range n))
        (List.range n)) := by
  refine foldB_congr_members _ _ (List.range n) (fun i hi => ?_)
  have hin : i < n := ltOfMem hi
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (foldB_congr_members _ (fun j => if i = j then uu i * uu j
      else BPair.unit) (List.range n) (fun j hj => ?_))
    (bsum_pick (fun j => uu i * uu j) (List.range n) i ?_))
  · have hjn : j < n := ltOfMem hj
    rw [hdl i j hin hjn]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij,
        BPair.mul_comm (BPair.ofNat 1) (uu i * uu j)]
      exact BPair.mul_ofNat_one _
    · rw [if_neg hij, if_neg hij]
      exact BPair.unit_mul _
  · rw [countOf_range_one hin]

/-- The two folds merge at the composed count: the family's squares
against a count's double fold collect to the composed count's own
double fold at the count joined to the delta. -/
theorem sumFold (n : Nat) (dl NN CC : Nat → Nat → Nat)
    (uu : Nat → BPair)
    (hdl : ∀ i j, i < n → j < n →
      dl i j = if i = j then 1 else 0)
    (hC : ∀ i j, i < n → j < n → CC i j = NN i j + dl i j) :
    (bsum (fun i => uu i * uu i) (List.range n)
      + bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
          * (uu i * uu j)) (List.range n)) (List.range n)).oneValue
      (bsum (fun i => bsum (fun j => BPair.ofNat (CC i j)
        * (uu i * uu j)) (List.range n)) (List.range n)) := by
  refine BPair.oneValue_trans
    (BPair.add_congr (deltaFold n dl uu hdl) (BPair.oneValue_refl _))
    ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (foldB_add
      (fun i => bsum (fun j => BPair.ofNat (dl i j) * (uu i * uu j))
        (List.range n))
      (fun i => bsum (fun j => BPair.ofNat (NN i j) * (uu i * uu j))
        (List.range n)) (List.range n))) ?_
  refine foldB_congr_members _ _ (List.range n) (fun i hi => ?_)
  have hin : i < n := ltOfMem hi
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (foldB_add (fun j => BPair.ofNat (dl i j) * (uu i * uu j))
      (fun j => BPair.ofNat (NN i j) * (uu i * uu j))
      (List.range n))) ?_
  refine foldB_congr_members _ _ (List.range n) (fun j hj => ?_)
  have hjn : j < n := ltOfMem hj
  show (BPair.ofNat (dl i j) * (uu i * uu j)
      + BPair.ofNat (NN i j) * (uu i * uu j)).oneValue
    (BPair.ofNat (CC i j) * (uu i * uu j))
  rw [← BPair.right_distrib]
  refine BPair.mul_congr_left ?_
  rw [hC i j hin hjn]
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.ofNat_add (NN i j) (dl i j)) ?_)
  exact BPair.oneValue_of_eq (BPair.add_comm _ _)

/-! The guarded reads' kit, the range folds at one key and at two, the
digit steps at a top digit and at a split key beyond its power, and the
fold's growth with its range. -/

/-- A guarded read's memberwise swap at the unit off the guard. -/
theorem ite_swap (c : Bool) (x : BPair) :
    (if c then x else BPair.unit).swap = if c then x.swap else BPair.unit := by
  cases c <;> rfl

/-- A guarded sum splits at the guard, the unit off it. -/
theorem ite_add_unit (c : Bool) (x y : BPair) :
    (if c then x + y else BPair.unit).oneValue
      ((if c then x else BPair.unit) + (if c then y else BPair.unit)) := by
  cases c with
  | true => exact BPair.oneValue_refl _
  | false => exact BPair.oneValue_symm (BPair.add_unit _)

/-- A guarded sum at a proposition splits at the guard, the unit off
it. -/
theorem ite_add_unit_prop (P : Prop) [Decidable P] (x y : BPair) :
    (if P then x + y else BPair.unit).oneValue
      ((if P then x else BPair.unit) + (if P then y else BPair.unit)) := by
  by_cases h : P
  · rw [if_pos h, if_pos h, if_pos h]
    exact BPair.oneValue_refl _
  · rw [if_neg h, if_neg h, if_neg h]
    exact BPair.oneValue_symm (BPair.add_unit _)

/-- A guarded read against a member reads the member under the
guard. -/
theorem ite_mul_unit (P : Prop) [Decidable P] (x y : BPair) :
    ((if P then x else BPair.unit) * y).oneValue (if P then x * y else BPair.unit) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
    exact BPair.oneValue_refl _
  · rw [if_neg h, if_neg h]
    exact BPair.unit_mul y

/-- Two guards nest to their conjunction. -/
theorem ite_ite_and (c e : Bool) (x : BPair) :
    (if c then (if e then x else BPair.unit) else BPair.unit) = if c && e then x else BPair.unit := by
  cases c <;> cases e <;> rfl

/-- A guard implied by its partner absorbs into the conjunction. -/
theorem ite_and_absorb (c e : Bool) (h : e = true → c = true) (x : BPair) :
    (if c && e then x else BPair.unit) = if e then x else BPair.unit := by
  cases he : e with
  | true => rw [h he]; rfl
  | false => rw [Bool.and_false]

/-- A range read at a stated key alone: every occupied guard names the
key, so the fold reads the key's own guarded value. -/
theorem bsum_range_at (P : Nat → Bool) (X : Nat → BPair) (t0 n : Nat) (ht0 : t0 < n)
    (h : ∀ t, t < n → P t = true → t = t0) :
    (bsum (fun t => if P t then X t else BPair.unit) (List.range n)).oneValue
      (if P t0 then X t0 else BPair.unit) := by
  cases hP : P t0 with
  | true =>
    refine bsum_range_single_of P X t0 n ht0 (fun t ht => ⟨h t ht, fun he => by rw [he]; exact hP⟩)
  | false =>
    refine bsum_range_none P X n (fun t ht => ?_)
    cases hPt : P t with
    | true =>
      have he := h t ht hPt
      rw [he] at hPt
      rw [hPt] at hP
      exact Bool.noConfusion hP
    | false => rfl

/-- A range read at two stated keys joined to the fold off them. -/
theorem bsum_range_pick_two (F : Nat → BPair) (a k n : Nat) (ha : a < n) (hk : k < n)
    (hak : ¬ a = k) :
    (bsum F (List.range n)).oneValue
      (F a + (F k + bsum (fun j => if j == a || j == k then BPair.unit else F j) (List.range n))) := by
  refine BPair.oneValue_trans (bsum_congr_range_ov F (fun j =>
    (if j == a then F a else BPair.unit) + ((if j == k then F k else BPair.unit)
      + (if j == a || j == k then BPair.unit else F j))) n (fun j _ => ?_)) ?_
  · cases hja : (j == a) with
    | true =>
      have hjk : (j == k) = false := neBeqOf (fun h => hak ((beqEqOf hja).symm.trans h))
      rw [hjk, ← beqEqOf hja]
      show (F j).oneValue (F j + (BPair.unit + BPair.unit))
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)) (BPair.add_unit _))
    | false =>
      cases hjk : (j == k) with
      | true =>
        rw [← beqEqOf hjk]
        show (F j).oneValue (BPair.unit + (F j + BPair.unit))
        exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.add_unit _))
      | false =>
        show (F j).oneValue (BPair.unit + (BPair.unit + F j))
        exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr (foldB_pickBeq a (F a) _ (countOf_range_one ha)) ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  exact BPair.add_congr (foldB_pickBeq k (F k) _ (countOf_range_one hk)) (BPair.oneValue_refl _)

/-- A range read at three stated keys joined to the fold off them. -/
theorem bsum_range_pick_three (F : Nat → BPair) (a b c n : Nat) (ha : a < n) (hb : b < n)
    (hc : c < n) (hab : ¬ a = b) (hac : ¬ a = c) (hbc : ¬ b = c) :
    (bsum F (List.range n)).oneValue
      (F a + (F b + (F c + bsum (fun j => if (j == a || j == b) || j == c then BPair.unit else F j)
        (List.range n)))) := by
  refine BPair.oneValue_trans (bsum_congr_range_ov F (fun j =>
    (if j == a then F a else BPair.unit) + ((if j == b then F b else BPair.unit)
      + ((if j == c then F c else BPair.unit)
      + (if (j == a || j == b) || j == c then BPair.unit else F j)))) n (fun j _ => ?_)) ?_
  · cases hja : (j == a) with
    | true =>
      have hjb : (j == b) = false := neBeqOf (fun h => hab ((beqEqOf hja).symm.trans h))
      have hjc : (j == c) = false := neBeqOf (fun h => hac ((beqEqOf hja).symm.trans h))
      rw [hjb, hjc, ← beqEqOf hja]
      show (F j).oneValue (F j + (BPair.unit + (BPair.unit + BPair.unit)))
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))) (BPair.add_unit _))
    | false =>
      cases hjb : (j == b) with
      | true =>
        have hjc : (j == c) = false := neBeqOf (fun h => hbc ((beqEqOf hjb).symm.trans h))
        rw [hjc, ← beqEqOf hjb]
        show (F j).oneValue (BPair.unit + (F j + (BPair.unit + BPair.unit)))
        exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)) (BPair.add_unit _)))
      | false =>
        cases hjc : (j == c) with
        | true =>
          rw [← beqEqOf hjc]
          show (F j).oneValue (BPair.unit + (BPair.unit + (F j + BPair.unit)))
          exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
            (BPair.oneValue_trans (BPair.unit_add _) (BPair.add_unit _)))
        | false =>
          show (F j).oneValue (BPair.unit + (BPair.unit + (BPair.unit + F j)))
          exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
            (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _)))
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr (foldB_pickBeq a (F a) _ (countOf_range_one ha)) ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr (foldB_pickBeq b (F b) _ (countOf_range_one hb)) ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  exact BPair.add_congr (foldB_pickBeq c (F c) _ (countOf_range_one hc)) (BPair.oneValue_refl _)

/-- A key at a full digit steps into a carry: the digit reads the
sum's unit at the stepped key. -/
theorem baseDigit_step_top (b c s : Nat) (hb : 0 < b) (h : baseDigit b c s + 1 = b) :
    baseDigit b c (s + b ^ c) = 0 := by
  show (s + b ^ c) / b ^ c % b = 0
  have h1 := divAddMul s 1 (b ^ c) (Nat.pow_pos hb)
  rw [Nat.one_mul] at h1
  rw [h1]
  have hn := natDivRead (s / b ^ c) b hb
  have hd : s / b ^ c % b + 1 = b := h
  refine modOf (q := s / b ^ c / b + 1) hb ?_ hb
  have e : b * (s / b ^ c / b) + b = b * (s / b ^ c / b) + (s / b ^ c % b + 1) := by
    rw [hd]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_zero, e, ← Nat.add_assoc, hn.1]

/-- A guarded read at the true guard reads its member. -/
theorem iteB_true (X : BPair) : (if true then X else BPair.unit) = X := rfl

/-- A guarded read at the false guard reads the unit. -/
theorem iteB_false (X : BPair) : (if false then X else BPair.unit) = BPair.unit := rfl

/-- A guarded read at a guard reading true reads its member. -/
theorem iteB_of_true {c : Bool} (X : BPair) (h : c = true) :
    (if c then X else BPair.unit) = X := by
  rw [h]
  rfl

/-- A guarded read's congruence under a stated guard. -/
theorem ite_congr_prop {A A' : BPair} (P : Prop) [Decidable P] (h : P → A.oneValue A') :
    (if P then A else BPair.unit).oneValue (if P then A' else BPair.unit) := by
  by_cases hP : P
  · rw [if_pos hP, if_pos hP]
    exact h hP
  · rw [if_neg hP, if_neg hP]
    exact BPair.oneValue_refl _

/-- A guarded read of the unit reads the unit at every guard. -/
theorem ite_prop_unit (P : Prop) [Decidable P] :
    (if P then BPair.unit else BPair.unit) = BPair.unit := by
  by_cases h : P
  · rw [if_pos h]
  · rw [if_neg h]

/-- The identity's scaled entry reads the clearing at the diagonal
key and the sum's unit off it, at the comparison's two spellings. -/
theorem delta_scale (D : BPair) (i j : Nat) :
    (if i == j then D else BPair.unit).oneValue
      (D * (if j = i then BPair.ofNat 1 else BPair.unit)) := by
  by_cases hij : i = j
  · rw [if_pos hij.symm, eqBeqOf hij, iteB_true]
    exact BPair.oneValue_symm (BPair.mul_ofNat_one _)
  · rw [if_neg (show ¬ j = i from fun h => hij h.symm), neBeqOf hij, iteB_false]
    exact BPair.oneValue_symm (BPair.mul_unit _)

/-- Two guarded reads multiply under the guards' conjunction. -/
theorem ite_mul_ite_and (c e : Bool) (x y : BPair) :
    ((if c then x else BPair.unit) * (if e then y else BPair.unit)).oneValue
      (if c && e then x * y else BPair.unit) := by
  cases c with
  | true =>
    cases e with
    | true => exact BPair.oneValue_refl _
    | false => exact BPair.mul_unit _
  | false => exact BPair.unit_mul _

/-- The balance partner of one squares to one. -/
theorem swapOne_sq : ((BPair.ofNat 1).swap * (BPair.ofNat 1).swap).oneValue (BPair.ofNat 1) := by
  decide

/-- A refused guard with the unit on its held side reads its else. -/
theorem iteB_false_else (X : BPair) : (if false then BPair.unit else X) = X := rfl

/-- A held guard with the unit on its held side reads the unit. -/
theorem iteB_true_else (X : BPair) : (if true then BPair.unit else X) = BPair.unit := rfl

/-- A fold over a range grows with the range at members at or above
the unit. -/
theorem bsum_range_mono (F : Nat → BPair) (h : ∀ i, BPair.unit ≤ F i) (k : Nat) :
    ∀ g : Nat, bsum F (List.range k) ≤ bsum F (List.range (k + g))
  | 0 => leB_refl _
  | g + 1 =>
    leB_congr_right (BPair.oneValue_symm (foldB_range_snoc F (k + g)))
      (leB_congr_left (BPair.add_unit _) (leB_add (bsum_range_mono F h k g) (h (k + g))))

/-- A guarded comparison at a stated proposition. -/
theorem ite_le_prop (P : Prop) [Decidable P] {x y : BPair} (h : P → x ≤ y) :
    (if P then x else BPair.unit) ≤ (if P then y else BPair.unit) := by
  by_cases hP : P
  · rw [if_pos hP, if_pos hP]
    exact h hP
  · rw [if_neg hP, if_neg hP]
    exact leB_refl _

/-- A split key's digits beyond the split's power read the high
part's digits. -/
theorem baseDigit_split_beyond (b d k q r : Nat) (hb : 0 < b) (hr : r < b ^ d) :
    baseDigit b (d + k) (q * b ^ d + r) = baseDigit b k q := by
  show (q * b ^ d + r) / b ^ (d + k) % b = q / b ^ k % b
  rw [powAdd b d k, divDiv _ _ _ (Nat.pow_pos hb) (Nat.pow_pos hb),
    divOf (Nat.pow_pos hb) (show b ^ d * q + r = q * b ^ d + r by rw [Nat.mul_comm]) hr]

/-- Every bounded digit list has a code below the matching power. -/
theorem baseDigit_exists (b : Nat) (hb : 0 < b) :
    ∀ (d : Nat) (f : Nat → Nat), (∀ i, i < d → f i < b) →
      ∃ n, n < b ^ d ∧ ∀ i, i < d → baseDigit b i n = f i
  | 0, _, _ => ⟨0, Nat.succ_pos 0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | d + 1, f, hf => by
    obtain ⟨n, hn, hd⟩ := baseDigit_exists b hb d f
      (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    refine ⟨f d * b ^ d + n, splitLtPow b d (f d) n hn (hf d (Nat.lt_succ_self d)), ?_⟩
    intro i hi
    cases Nat.lt_or_ge i d with
    | inl hid => rw [baseDigit_split_low b i d (f d) n hb hid, hd i hid]
    | inr hdi =>
      have he : i = d := Nat.le_antisymm (Nat.le_of_lt_succ hi) hdi
      rw [he, baseDigit_split_top b d (f d) n hb hn (hf d (Nat.lt_succ_self d))]

/-- The digits identify a code within its stated power. -/
theorem baseDigit_ext (b : Nat) (hb : 0 < b) :
    ∀ (d n m : Nat), n < b ^ d → m < b ^ d →
      (∀ i, i < d → baseDigit b i n = baseDigit b i m) → n = m
  | 0, n, m, hn, hm, _ =>
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)).trans
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hm)).symm
  | d + 1, n, m, hn, hm, hd => by
    have hn' := (lowSplit b d n hb).1
    have hm' := (lowSplit b d m hb).1
    rw [modOfLt n (b ^ (d + 1)) hn] at hn'
    rw [modOfLt m (b ^ (d + 1)) hm] at hm'
    have hr : n % b ^ d = m % b ^ d := baseDigit_ext b hb d _ _
      (modPowLt b d n hb) (modPowLt b d m hb) (fun i hi => by
        rw [baseDigit_mod_low b d i n hb hi, baseDigit_mod_low b d i m hb hi]
        exact hd i (Nat.lt_succ_of_lt hi))
    rw [hn', hm', hd d (Nat.lt_succ_self d), hr]

/-- A guard at a stated proposition reads as its decided Boolean. -/
theorem ite_decide {α : Type} (P : Prop) [Decidable P] (x y : α) :
    (if decide P = true then x else y) = if P then x else y := by
  by_cases h : P
  · rw [if_pos (decide_eq_true h), if_pos h]
  · rw [if_neg (fun hc => h (of_decide_eq_true hc)), if_neg h]

/-- A refused comparison's read. -/
theorem neOfBeq {a b : Nat} (h : (a == b) = false) : ¬ a = b := fun he => by
  rw [eqBeqOf he] at h
  exact Bool.noConfusion h

/-- The entry read through an erasure: below the struck key its
own, at or above it the successor's. -/
theorem getAt_eraseIdx {α : Type} (d : α) :
    ∀ (l : List α) (j c : Nat),
      ground.getAt d (l.eraseIdx j) c
        = if c < j then ground.getAt d l c
          else ground.getAt d l (c + 1)
  | [], j, c => by
    show ground.getAt d ([] : List α) c
      = if c < j then ground.getAt d ([] : List α) c
        else ground.getAt d ([] : List α) (c + 1)
    by_cases h : c < j
    · rw [if_pos h]
    · rw [if_neg h]
      rfl
  | a :: t, 0, c => by
    show ground.getAt d t c
      = if c < 0 then ground.getAt d (a :: t) c
        else ground.getAt d (a :: t) (c + 1)
    rw [if_neg (Nat.not_lt_zero c)]
    rfl
  | a :: t, j + 1, 0 => by
    show a = if 0 < j + 1 then a else ground.getAt d t 0
    rw [if_pos (Nat.succ_pos j)]
  | a :: t, j + 1, c + 1 => by
    show ground.getAt d (t.eraseIdx j) c
      = if c + 1 < j + 1 then ground.getAt d t c
        else ground.getAt d t (c + 1)
    rw [getAt_eraseIdx d t j c]
    by_cases h : c < j
    · rw [if_pos h, if_pos (Nat.succ_lt_succ h)]
    · rw [if_neg h, if_neg (fun hs => h (Nat.lt_of_succ_lt_succ hs))]

/-- The vacant family's erasure at every key. -/
private theorem eraseIdx_nil {α : Type} : ∀ j : Nat, ([] : List α).eraseIdx j = []
  | 0 => rfl
  | _ + 1 => rfl

/-- The erased rows' entries are entries of the rows: a read at every
entry of a family holds at every entry of the erased family. -/
theorem entries_eraseIdx {γ : Type} (u : γ) (P : γ → Prop)
    (M : List (List γ)) (j : Nat)
    (h : ∀ i k, P (ground.getAt u (ground.getAt [] M i) k)) :
    ∀ i k, P (ground.getAt u
      (ground.getAt [] (M.map (fun l => l.eraseIdx j)) i) k) := by
  intro i k
  rw [ground.getAt_mapT ([] : List γ) ([] : List γ) (fun l => l.eraseIdx j)
      (eraseIdx_nil j) M i,
    getAt_eraseIdx u (ground.getAt [] M i) j k]
  cases Nat.decLt k j with
  | isTrue hk => rw [if_pos hk]; exact h i k
  | isFalse hk => rw [if_neg hk]; exact h i (k + 1)

/-- An erased frame's entries are the frame's own: a read at every
entry of a family holds at every entry of the family with one row
and one column erased. -/
theorem entries_eraseBoth {γ : Type} (u : γ) (P : γ → Prop)
    (M : List (List γ)) (j i : Nat)
    (h : ∀ a b, P (ground.getAt u (ground.getAt [] M a) b)) :
    ∀ a b, P (ground.getAt u (ground.getAt []
      ((M.eraseIdx j).map (fun r => r.eraseIdx i)) a) b) := by
  refine entries_eraseIdx u P (M.eraseIdx j) i (fun a b => ?_)
  rw [getAt_eraseIdx ([] : List γ) M j a]
  cases Nat.decLt a j with
  | isTrue ha => rw [if_pos ha]; exact h a b
  | isFalse ha => rw [if_neg ha]; exact h (a + 1) b

/-- A trace balance isolates its correction at the gap's multiple. -/
theorem BPair.gap_mul_of_rec {Q P G n : BPair}
    (h : (Q * n).oneValue (P * n + G)) : ((Q + P.swap) * n).oneValue G := by
  rw [BPair.right_distrib, BPair.swap_mul]
  refine BPair.oneValue_trans (BPair.add_congr h (BPair.oneValue_refl _)) ?_
  rw [BPair.add_assoc, BPair.add_comm G ((P * n).swap), ← BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr (ground.unitOfOne (BPair.oneValue_refl (P * n))) (BPair.oneValue_refl G))
    (BPair.unit_add G)

/-- A natural trace count is the exact cofactor of its correction
at a positive scalar gap, with zero remainder. -/
theorem BPair.rec_count {Q P G : BPair} (c : Nat) (hlt : P < Q)
    (hrec : (Q * BPair.ofNat c).oneValue (P * BPair.ofNat c + G)) :
    let d := (Q + P.swap).norm.marginN
    let n := G.norm.marginN
    0 < d ∧ n % d = 0 ∧ n / d = c := by
  have hg : BPair.unit < Q + P.swap := by
    apply ground.unitLt_of_swap_lt
    rw [BPair.swap_swap]
    exact hlt
  have hd : (Q + P.swap).norm.marginN = (Q + P.swap).marginN :=
    BPair.marginN_congr (BPair.norm_oneValue _)
  have hv : G.norm.marginN = (Q + P.swap).marginN * c := by
    have hh : G.norm.oneValue (BPair.ofNat ((Q + P.swap).marginN * c)) :=
      BPair.oneValue_trans (BPair.norm_oneValue G)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.gap_mul_of_rec hrec))
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.ofNat_marginN (ground.leB_of_lt hg)) (BPair.oneValue_refl _))
            (BPair.oneValue_symm (BPair.ofNat_mul _ _))))
    exact (BPair.marginN_congr hh).trans (BPair.marginN_ofNat _)
  change 0 < (Q + P.swap).norm.marginN ∧ _
  rw [hd, hv, Nat.mul_comm (Q + P.swap).marginN c]
  exact ⟨BPair.marginN_pos hg, ground.modMulSelf c _, ground.divMulSelf c _ (BPair.marginN_pos hg)⟩

end ground
