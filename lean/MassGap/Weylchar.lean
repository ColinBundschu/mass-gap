import MassGap.Places
/-!
`thm:weylchar` — the alternant layer's carrier: the alternant pair
at an exponent list, the swap-graded fold over the place
permutations at matched-list exponents, enters coefficientwise as
the graded counts `sideCount` at an exponent key, and the repeat
read is `repeat_read` — at two coordinates reading one exponent the
two sides' counts are equal at every key, the repeat's
transposition an odd move fixing every monomial and mapping either
side's family onto the other's, `con:places`' pairing device run
through the enumeration's coherence and the fold clause's
reindexing read; the exchange read is `exchange_read` — at a
permuted exponent list the graded counts exchange along the
permutation's grading, an odd permutation exchanging the members
and an even one fixing them, the grading additive over composition
at the inverse permutation's reindexing.  The keyed table `alternantTable` is the fast
route: one pass over the enumeration accumulating every key's two
counts, `ground.tabRead` its read, and the coherence theorem
`alternantTable_read` ties the fast read to the
definition exactly at every key and side, the units at the keys off the
table among them, so a keyed read prices one pass rather than a
per-key refold of the enumeration; the table's key-distinctness
with the row-level read lands with its consumer, the block tier's
whole-alternant folds, and the one-pass shape's ceiling is the
d = 5 table (the linear key scan prices d = 6 out; a deeper
consumer takes a keyed-structure rework).

The identity's statement tier: the product `a_u · ch_λ` enters
coefficientwise as `prodCount`, the tie fold over the place
permutations — `multAtGap` at `tieGap`, the componentwise gap of
the key against the permuted unit display (`places.display`, the
sorted display at its `con:places` home, `unitDisp` the unit
shape's) — and the theorem's hypotheses enter as the tex proof's
displays, each a decidable read at the occupancy family `L` with
the multiplicity that family's count: the trace recursion
`recRead` (the Casimir trace's string collection,
`q(λ+u)·mult(ν) + 2ΣΣ ν_b·mult(ν^{(l)}) =
q(ν+u)·mult(ν) + 2ΣΣ (ν_a+2l)·mult(ν^{(l)})` at `movedSnd` and
`movedFst` over `moveBy`, read at the family's key list
`recKeys` — the members joined by every pair move's sources),
the reflection symmetry `symRead` (`ch` symmetric at every letter
transposition of a member), and the support with the top line
(`supportRead` at the dominance walk `domGo`/`domBy`, `topRead`).
The identity's read at a key is `identityAt`, one value of the two
balance pairs, decidable at every stated multiplicity.  Proven
here: the key's exchange and
repeat package (`sideCount_swapKey`, `prodCount_swapKey`,
`sideCount_repeatKey`, `prodCount_repeatKey`,
`identityAt_swapKey`, `identityAt_repeatKey` — the reindex at the
places' transposition with the symmetry reading the tie across),
the separation `sq_lt_of_dom` — `q(μ+u) < q(λ+u)` at a
sorted content dominated by the top off it, the conclusion's
eigenvalue gap at the dominance display's prefix gaps against
the weight steps — and the top coefficient `prodCount_top`: at
the support and top clauses the product's coefficient at the top
key reads one on the even side and the count's unit on the odd,
the tie's one contributor the identity permutation, every
further permutation priced off the dominance walk
(`domGo_prefix`, the walk's prefix read) by the permuted
display's prefix cap against the unit display's — the
distinct-family minimum at the withdrawn top value, the prefix
sum `ground.prefixAt` the reasoning read.  The eigen-read opens:
its statement is `eigenAt` — `𝓛₀(a_u ch) = q(λ+u)(a_u ch)`
coefficientwise, the key's and the top display's standard squares
weighing the product's two coefficients to one value — the
recursion's moved folds respell through the telescope family's
members `gFst`/`gSnd` (`G_ab`'s two members at a content), and the
telescope's per-key read is proven (`stepRead`: `⟨x_a : x_b⟩ G_ab
= x_b ⟨D_a ch : D_b ch⟩` at every doubly occupied key, the bumped
spelling, one further move dropping one shift — the pair's folds
at the two bumped contents differing by the dropped move's read,
the edit kit's commuting and fusing entry rewrites beneath it,
the move's own entry reads public at the pair's letters —
`length_moveBy`, `getAt_moveBy_fst`, `getAt_moveBy_snd`,
`getAt_moveBy_ne`, the string tier's own consumption at
`lem:strings`),
and the boundary read is proven (`boundaryRead`: at a key reading
the first letter at the count's unit the moved weights collect to
the second exponent's count, `Σ_{l≥1} 2l·mult(ν^{(l)})
= ν_b Σ_{l≥0} mult(ν^{(l)})`, the one-sided string's palindrome —
the symmetry pairs the shifts at the join `l + l' = ν_b` through
the moved content's reflection `moveSym`, and the paired fold
collects by the pure telescope `palinTele`).  The cofactor tier is
landed: the guarded reads at a key against a display (`gAtGap`,
`dAtGap` — the `G`-members and the Euler read at the tie's
content), the per-key telescope `stepAt` — `⟨x_a : x_b⟩ G_ab
= x_b ⟨D_a ch : D_b ch⟩` at every key against an occupied-second-
letter display, the keyed spelling's whole scope, `stepRead` at a doubly
occupied tie, `boundaryRead` at a first letter reading the count's
unit, and the vacuous reads at an exhausted second letter, over
the tie-move kit (the tie moved along the pair, its bound at the
zeroed first letter, and the moved tie's slack at the second) —
and `cofRead`, the cleared telescope at the cofactor per display:
the shift fold of `x_b ⟨D_a ch : D_b ch⟩`'s guarded reads over the
moved displays collects to the head display's `G`-read against the
far boundary's, `⟨x_a : x_b⟩ Q_ab = V`'s back-substitution with
the interior reads canceling in consecutive pairs.  The perm-fold
assembly's first display is proven (`cofProd`: the product's
graded coefficient against the telescope family `prodG` reads the
cofactor's shift fold `cofFold` at every key — `cofRead` summed
over the place permutations, the far boundaries canceling per
swap coset at the shared zeroed display, the graded sum's
odd-swap read).  The cofactor's
coefficient is data (`cofAt`, the monic letter's division descent,
pinned against the product form's own reads).  The product-rule
read is proven (`prodRule`: the tex's derivative display
`D_i V = Σ_j x_i Q_ij` coefficientwise at the bumped key, the
crossed equation of the letter-weighted graded count with the
cofactor fold `cofSum`, the pairs below the letter at the members
exchanged), transcribing the assembly's four clauses: the display
detection (`arrB` the arrangement test with `permOf` the
complement permutation, `sideCount_arr`/`sideCount_off` the graded
counts' one unit at an arrangement's own permutation, `arr_two`
the line's two arrangements as the pair's value exchange); the
half-line evaluation (`cofAt_split`/`cofAt_line`, the monic
descent opening at the key itself with one head read per letter
beyond and the swapped cofactors strictly moved, over the line
fold's display read, matched-filling balance, and one-sided
concentration); the value's places split at an arrangement
(`placesSplit`: the letter's value with its rising comparisons
`upFold` joins the count with the falling comparisons `downFold`,
the rank read over the places' trichotomy); and the pairing
involution (`partnerAt` on the letter index — the letter's key
value at its second place names the partner line, whose one-sided
hit keeps the upper filling with the receding value at its further
filling, the pairing an involution off its fixed points consumed
through `famFold_reindex`, the grading exchanged at a same-side
partner's transposition and kept across the letter at the swapped
cofactor's memberwise exchange).  The display-1 reorganization per
pair is proven (`cofDProd`: the operator identity `⟨x_a D_a :
x_b D_b⟩ = x_b ⟨D_a : D_b⟩ + ⟨x_a : x_b⟩ D_a` read at the cofactor
against the alternant's clearing — the pair-weighted cofactor fold
`cofDFold` reads the product's `G`-read with the product's Euler
read `prodD`, per display the index shift exchanging the far
boundary for the head display, the far reads canceling per swap
coset at the shared zeroed display, and the telescope fold
converting through `cofProd`).  The eigen-read is closed
(`eigenRead`: the trace recursion with the reflection symmetry
reads `eigenAt` at every key): the product rule convolves over
the key box `places.keyBox` against the letter's guarded Euler read —
the letter-weighted and further-member `A`-counts collapsing one
permutation per bumped display (`convA`/`convB`), the cofactor
fold collapsing onto the letter's moved-display folds `cofEFold`
(`convC`, per shift the point collapse at the edit pair's
preimage `editCollapse`, the box bound clearing the doubled
count) — the letters' folds regroup onto the letter pairs
(`convLetter` per letter, `pairRegroup` the pair regrouping at
the branch split), the convolution theorem `convAll` holds at
every multiplicity with the display-1 identity summed over the
pairs (`cofDAll`), and the Leibniz-square collection
(`leibSplit`, `uSplit`, `recFold`, `gRegroup`, `uCollect` over
the tie fold `tieFold` with the index folds passing through at
`tieFold_fold`) closes the crossed equation (`eigenCross`) at a
matched-length key, the off-length keys reading the count's unit
on both sides through the tie's refusal.  The conclusion is
closed (`identityRead`: under the four hypothesis displays the
identity's read holds at every key): a repeated key reads the
repeat's transposition (`identityAt_repeatKey`), a distinct key
walks to its sorted representative along the ascent measure
(`firstNonDesc` with `ascCount`, the adjacent ascent's swap
dropping the measure by one at `ascCount_swapAdj`, the transport
back through `identityAt_swapKey` at the transposition's
involution), the sorted representative reads the display by
`prodCount_top` against the display's own graded read
(`sideCount_desc_self` at `places.display_desc`) and off it by the two
routes — the eigen-read's crossed cancellation (`crossCancel` at
`eigenRead`) at separated squares, and at equal squares the
per-permutation refusal: a sorted key's occupied tie forces the
unit display entrywise (`unitLe_of_desc`), the gap at the unit
tie (`tieGap_of_le`) weakly descending (`mu_desc`) and dominated
(`mu_dom` over the prefix caps `ground.prefixAt_zipAdd`/`prefixExpo`/
`prefixUnit`/`prefixTri` with the walk's sum and prefix
constructors `domGo_sum`/`domGo_ofPrefix`), so `sq_lt_of_dom`
separates the squares against the equality — with two sorted
keys' graded reads at the count's unit (`sideCount_desc_ne` over
`ground.descUnique` and the count transport) and an off-length
key at the count's unit on both sides.  The block structure tier
discharges the hypotheses at the definitional multiplicity,
`def:blockcount`'s span occupancy.
-/

namespace weylchar
open ground places

/-- The alternant pair's coefficient at an exponent key, one side:
the graded count over the place permutations at the display's
comparison. -/
def sideCount (d : Nat) (beta y : List Nat) (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      if parity p = side then (if expo beta p = y then 1 else 0)
      else 0)
    (perms d)

/-- The alternant pair's keyed table: one pass over the place
permutations at the merging insert, the fast route to the graded
counts. -/
def alternantTable (d : Nat) (beta : List Nat) :
    List (List Nat × Nat × Nat) :=
  (perms d).foldl
    (fun tab p => ground.tabAdd
      (expo beta p, (if parity p then (0 : Nat) else 1),
        (if parity p then (1 : Nat) else 0)) tab) []

/-- The table's coherence: a key's read at a side is the graded
count, the fast route reading the definition exactly. -/
theorem alternantTable_read (d : Nat) (beta y : List Nat)
    (side : Bool) :
    ground.tabRead (fun k => decide (k = y)) side
        (alternantTable d beta)
      = sideCount d beta y side := by
  show ground.tabRead (fun k => decide (k = y)) side
    ((perms d).foldl (fun tab p => ground.tabAdd
      (expo beta p, (if parity p then (0 : Nat) else 1),
        (if parity p then (1 : Nat) else 0)) tab) []) = _
  rw [ground.tabAdd_fold_read]
  show (0 : Nat) + _ = _
  rw [Nat.zero_add]
  refine ground.famFold_congr_all Nat.add 0 _ _ ?_ (perms d)
  intro p
  by_cases he : expo beta p = y
  · rw [decide_eq_true he, if_pos rfl, if_pos he]
    show (if side then (if parity p then (1 : Nat) else 0)
        else (if parity p then (0 : Nat) else 1))
      = (if parity p = side then 1 else 0)
    cases hp : parity p <;> cases side <;> rfl
  · cases hb : decide (expo beta p = y) with
    | true => exact absurd (of_decide_eq_true hb) he
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h), if_neg he]
      by_cases hp : parity p = side
      · rw [if_pos hp]
      · rw [if_neg hp]

/-- The repeat's transposition on a permutation: the two letters'
places exchanged. -/
private def swapAB (a b : Nat) (p : List Nat) : List Nat :=
  swapPair (posOf a p) (posOf b p) p

private theorem swapAB_counts (a b x : Nat) (p : List Nat) :
    ground.countOf x (swapAB a b p) = ground.countOf x p :=
  countOf_swapPair x (posOf a p) (posOf b p) p

private theorem swapAB_length (a b : Nat) (p : List Nat) :
    (swapAB a b p).length = p.length :=
  length_swapPair (posOf a p) (posOf b p) p

private theorem swapAB_member {d a b : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    0 < ground.countOf (swapAB a b p) (perms d) :=
  perm_member_of_counts hp (swapAB_length a b p)
    (fun x => swapAB_counts a b x p)

private theorem swapAB_getAt {d a b : Nat} (hab : a < b) (hbd : b < d)
    {p : List Nat} (hp : 0 < ground.countOf p (perms d)) :
    ground.getAt 0 (swapAB a b p) (posOf a p) = b
      ∧ ground.getAt 0 (swapAB a b p) (posOf b p) = a
      ∧ ∀ t, t ≠ posOf a p → t ≠ posOf b p →
          ground.getAt 0 (swapAB a b p) t = ground.getAt 0 p t := by
  obtain ⟨_, hdist, _, hocc⟩ := perm_member_reads hp
  have hpa : posOf a p < p.length :=
    posOf_lt a p (hocc a (Nat.lt_trans hab hbd))
  have hpb : posOf b p < p.length := posOf_lt b p (hocc b hbd)
  have hga : ground.getAt 0 p (posOf a p) = a :=
    getAt_posOf a p (hocc a (Nat.lt_trans hab hbd))
  have hgb : ground.getAt 0 p (posOf b p) = b :=
    getAt_posOf b p (hocc b hbd)
  have hne : posOf a p ≠ posOf b p := fun e =>
    Nat.ne_of_lt hab (by rw [← hga, ← hgb, e])
  refine ⟨?_, ?_, fun t hta htb => getAt_swapPair_ne p hpa hpb hta htb⟩
  · show ground.getAt 0 (swapPair (posOf a p) (posOf b p) p)
      (posOf a p) = b
    rw [getAt_swapPair_fst p hne hpa hpb, hgb]
  · show ground.getAt 0 (swapPair (posOf a p) (posOf b p) p)
      (posOf b p) = a
    rw [getAt_swapPair_snd p hne hpa hpb, hga]

private theorem swapAB_parity {d a b : Nat} (hab : a < b)
    (hbd : b < d) {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    parity (swapAB a b p) = !(parity p) := by
  obtain ⟨_, hdist, _, hocc⟩ := perm_member_reads hp
  have hpa : posOf a p < p.length :=
    posOf_lt a p (hocc a (Nat.lt_trans hab hbd))
  have hpb : posOf b p < p.length := posOf_lt b p (hocc b hbd)
  have hga : ground.getAt 0 p (posOf a p) = a :=
    getAt_posOf a p (hocc a (Nat.lt_trans hab hbd))
  have hgb : ground.getAt 0 p (posOf b p) = b :=
    getAt_posOf b p (hocc b hbd)
  have hne : posOf a p ≠ posOf b p := fun e =>
    Nat.ne_of_lt hab (by rw [← hga, ← hgb, e])
  exact parity_swapPair p hne hpa hpb hdist

private theorem swapAB_invol {d a b : Nat} (hab : a < b) (hbd : b < d)
    {p : List Nat} (hp : 0 < ground.countOf p (perms d)) :
    swapAB a b (swapAB a b p) = p := by
  obtain ⟨_, hdist, _, hocc⟩ := perm_member_reads hp
  have hpa : posOf a p < p.length :=
    posOf_lt a p (hocc a (Nat.lt_trans hab hbd))
  have hpb : posOf b p < p.length := posOf_lt b p (hocc b hbd)
  obtain ⟨hfst, hsnd, _⟩ := swapAB_getAt hab hbd hp
  have hdist' : ∀ z, ground.countOf z (swapAB a b p) ≤ 1 := fun z => by
    rw [swapAB_counts]
    exact hdist z
  have hpa' : posOf b p < (swapAB a b p).length := by
    rw [swapAB_length]
    exact hpb
  have hpb' : posOf a p < (swapAB a b p).length := by
    rw [swapAB_length]
    exact hpa
  have hposa : posOf a (swapAB a b p) = posOf b p := by
    have h := posOf_getAt hdist' (posOf b p) hpa'
    rw [hsnd] at h
    exact h
  have hposb : posOf b (swapAB a b p) = posOf a p := by
    have h := posOf_getAt hdist' (posOf a p) hpb'
    rw [hfst] at h
    exact h
  show swapPair (posOf a (swapAB a b p)) (posOf b (swapAB a b p))
      (swapAB a b p) = p
  rw [hposa, hposb, swapPair_comm]
  exact swapPair_swapPair (posOf a p) (posOf b p) p

private theorem swapAB_expo {d a b : Nat} (hab : a < b) (hbd : b < d)
    {beta : List Nat}
    (heq : ground.getAt 0 beta a = ground.getAt 0 beta b)
    {p : List Nat} (hp : 0 < ground.countOf p (perms d)) :
    expo beta (swapAB a b p) = expo beta p := by
  obtain ⟨_, _, _, hocc⟩ := perm_member_reads hp
  have hpa : posOf a p < p.length :=
    posOf_lt a p (hocc a (Nat.lt_trans hab hbd))
  have hpb : posOf b p < p.length := posOf_lt b p (hocc b hbd)
  have hga : ground.getAt 0 p (posOf a p) = a :=
    getAt_posOf a p (hocc a (Nat.lt_trans hab hbd))
  have hgb : ground.getAt 0 p (posOf b p) = b :=
    getAt_posOf b p (hocc b hbd)
  obtain ⟨hfst, hsnd, hoth⟩ := swapAB_getAt hab hbd hp
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · show ((swapAB a b p).map (ground.getAt 0 beta)).length
      = (p.map (ground.getAt 0 beta)).length
    rw [ground.length_map, ground.length_map, swapAB_length]
  · intro t ht
    have ht' : t < (swapAB a b p).length := by
      have h := ht
      rw [show (expo beta (swapAB a b p)).length
          = (swapAB a b p).length from ground.length_map _ _] at h
      exact h
    have htp : t < p.length := by
      rw [← swapAB_length a b p]
      exact ht'
    show ground.getAt 0 ((swapAB a b p).map (ground.getAt 0 beta)) t
      = ground.getAt 0 (p.map (ground.getAt 0 beta)) t
    rw [ground.getAt_map 0 0 (ground.getAt 0 beta) _ t ht',
      ground.getAt_map 0 0 (ground.getAt 0 beta) p t htp]
    by_cases hta : t = posOf a p
    · rw [hta, hfst, hga, heq]
    · by_cases htb : t = posOf b p
      · rw [htb, hsnd, hgb, heq]
      · rw [hoth t hta htb]

/-- The repeat read: at two coordinates reading one exponent the
two sides' counts are equal at every key — the repeat's
transposition an odd move fixing every monomial and mapping either
side's family onto the other's. -/
theorem repeat_read (d : Nat) (beta y : List Nat) {a b : Nat}
    (hab : a < b) (hbd : b < d)
    (heq : ground.getAt 0 beta a = ground.getAt 0 beta b) :
    sideCount d beta y true = sideCount d beta y false := by
  show ground.famFold Nat.add 0
      (fun p =>
        if parity p = true then (if expo beta p = y then 1 else 0)
        else 0)
      (perms d)
    = ground.famFold Nat.add 0
      (fun p =>
        if parity p = false then (if expo beta p = y then 1 else 0)
        else 0)
      (perms d)
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun p =>
        if parity p = true then (if expo beta p = y then 1 else 0)
        else 0)
      (l := perms d) (g := swapAB a b) (h := swapAB a b)
      (monomialsAt_distinct _)
      (fun p hp => swapAB_invol hab hbd hp)
      (fun p hp => swapAB_invol hab hbd hp)
      (fun p hp => swapAB_member hp)
      (fun p hp => swapAB_member hp)]
  exact ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => by
      show (if parity (swapAB a b p) = true
          then (if expo beta (swapAB a b p) = y then 1 else 0)
          else 0)
        = (if parity p = false
          then (if expo beta p = y then 1 else 0) else 0)
      rw [swapAB_parity hab hbd hp, swapAB_expo hab hbd heq hp]
      cases hpp : parity p with
      | true =>
        rw [if_neg (fun h : (!true) = true => Bool.noConfusion h),
          if_neg (fun h : true = false => Bool.noConfusion h)]
      | false =>
        rw [if_pos (show (!false) = true from rfl),
          if_pos (show false = false from rfl)])

private theorem xor_shift : ∀ {a b c : Bool},
    xor a b = c ↔ a = xor c b := by
  intro a b c
  cases a <;> cases b <;> cases c <;> exact ⟨fun h => by
      first | rfl | exact absurd h (fun hh => Bool.noConfusion hh),
    fun h => by
      first | rfl | exact absurd h (fun hh => Bool.noConfusion hh)⟩

/-! The identity's statement tier (`thm:weylchar`): the product
`a_u · ch_λ` enters coefficientwise as the tie fold over the place
permutations — the multiplicity at the componentwise gap of the
key against the permuted unit display — and the theorem's
hypotheses enter as the tex's displays, decidable reads at the
occupancy family with the multiplicity that family's count: the
trace recursion (`recRead` over the key list `recKeys`), the
reflection symmetry (`symRead`), and the support with the top line
(`supportRead`, `topRead`), each display's ∀-form over every
content the private spelling the proofs consume.  The identity's
read at a key is `identityAt`, one value of the two balance
pairs. -/

private theorem tieGap_swapPair {i j : Nat} (hne : i ≠ j)
    (y z : List Nat) (hi : i < y.length) (hj : j < y.length)
    (hz : z.length = y.length) :
    tieGap (swapPair i j y) (swapPair i j z)
      = (tieGap y z).map (swapPair i j) := by
  have hzi : i < z.length := by rw [hz]; exact hi
  have hzj : j < z.length := by rw [hz]; exact hj
  cases hyz : tieGap y z with
  | some m =>
    obtain ⟨hml, _, hent⟩ := tieGap_reads y z m hyz
    have hmi : i < m.length := by rw [hml]; exact hi
    have hmj : j < m.length := by rw [hml]; exact hj
    show tieGap (swapPair i j y) (swapPair i j z)
      = some (swapPair i j m)
    refine tieGap_make _ _ _ ?_ ?_ ?_
    · rw [length_swapPair, length_swapPair, hml]
    · rw [length_swapPair, length_swapPair, hz]
    · intro t ht
      rw [length_swapPair] at ht
      by_cases hti : t = i
      · rw [hti, getAt_swapPair_fst m hne hmi hmj,
          getAt_swapPair_fst z hne hzi hzj,
          getAt_swapPair_fst y hne hi hj]
        exact hent j hj
      · by_cases htj : t = j
        · rw [htj, getAt_swapPair_snd m hne hmi hmj,
            getAt_swapPair_snd z hne hzi hzj,
            getAt_swapPair_snd y hne hi hj]
          exact hent i hi
        · rw [getAt_swapPair_ne m hmi hmj hti htj,
            getAt_swapPair_ne z hzi hzj hti htj,
            getAt_swapPair_ne y hi hj hti htj]
          exact hent t ht
  | none =>
    show tieGap (swapPair i j y) (swapPair i j z) = none
    cases hs : tieGap (swapPair i j y) (swapPair i j z) with
    | none => rfl
    | some M =>
      obtain ⟨hMl, _, hent⟩ := tieGap_reads _ _ M hs
      rw [length_swapPair] at hMl
      have hMi : i < M.length := by rw [hMl]; exact hi
      have hMj : j < M.length := by rw [hMl]; exact hj
      have hcon : tieGap y z = some (swapPair i j M) := by
        refine tieGap_make _ _ _ ?_ ?_ ?_
        · rw [length_swapPair, hMl]
        · exact hz
        · intro t ht
          by_cases hti : t = i
          · rw [hti, getAt_swapPair_fst M hne hMi hMj]
            have hj' := hent j (by rw [length_swapPair]; exact hj)
            rw [getAt_swapPair_snd z hne hzi hzj,
              getAt_swapPair_snd y hne hi hj] at hj'
            exact hj'
          · by_cases htj : t = j
            · rw [htj, getAt_swapPair_snd M hne hMi hMj]
              have hi' := hent i (by rw [length_swapPair]; exact hi)
              rw [getAt_swapPair_fst z hne hzi hzj,
                getAt_swapPair_fst y hne hi hj] at hi'
              exact hi'
            · have ht' := hent t (by rw [length_swapPair]; exact ht)
              rw [getAt_swapPair_ne z hzi hzj hti htj,
                getAt_swapPair_ne y hi hj hti htj] at ht'
              rw [getAt_swapPair_ne M hMi hMj hti htj]
              exact ht'
      exact nomatch hyz.symm.trans hcon

/-- The multiplicity at the tie, an occupancy read: the read at
the occupied solution, the count's unit at an absent one. -/
def multAtGap (mult : List Nat → Nat) (y z : List Nat) : Nat :=
  match tieGap y z with
  | some nu => mult nu
  | none => 0

/-- An occupied tie multiplicity names the tie and its own
positive read. -/
theorem multAtGap_pos (mult : List Nat → Nat) (y z : List Nat)
    (hpos : 0 < multAtGap mult y z) :
    ∃ m, ground.tieGap y z = some m ∧ 0 < mult m := by
  cases hg : ground.tieGap y z with
  | none =>
    have hv : multAtGap mult y z = 0 := by
      show (match ground.tieGap y z with
        | some nu => mult nu
        | none => 0) = 0
      rw [hg]
    rw [hv] at hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  | some m =>
    have hv : multAtGap mult y z = mult m := by
      show (match ground.tieGap y z with
        | some nu => mult nu
        | none => 0) = _
      rw [hg]
    rw [hv] at hpos
    exact ⟨m, rfl, hpos⟩

/-- The product's graded coefficient at a key, one side: the fold
over the place permutations of the multiplicity at the tie against
the permuted unit display, `[a_u · ch_λ]_y`'s side count. -/
def prodCount (mult : List Nat → Nat) (d : Nat) (y : List Nat)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      if parity p = side then multAtGap mult y (expo (unitDisp d) p)
      else 0)
    (perms d)

/-- The standard square `q(z) = Σ_i z_i²` (`thm:weylchar`'s `q`). -/
def stdSq (z : List Nat) : Nat := sumNat (z.map (fun a => a * a))

/-- The standard square as the index fold of the entry squares. -/
theorem stdSq_index (z : List Nat) :
    stdSq z = ground.famFold Nat.add 0
      (fun i => getAt 0 z i * getAt 0 z i) (List.range z.length) := by
  show sumNat (z.map (fun a => a * a)) = _
  rw [ground.sumMap (fun a => a * a) z]
  exact (ground.famFold_getAt Nat.add 0 (fun a => a * a) 0 z
    z.length rfl).symm

/-- The letter-pair move at a stated shift: the count at the first
letter raised by the shift, at the second lowered by it, the
further letters kept — `ν^{(l)}` at the pair (`thm:weylchar`'s
recursion display). -/
def moveBy (a b l : Nat) (nu : List Nat) : List Nat :=
  ground.editAt (fun x => x + l) a (ground.editAt (fun x => x - l) b nu)

/-- The pair's moved fold at the second letter's weight, the
telescope family `G_ab`'s second member at a content: over the
shifts `1 ≤ l ≤ ν_b`, the weight `ν_b` against the multiplicity at
the move. -/
def gSnd (mult : List Nat → Nat) (nu : List Nat) (a b : Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun l => ground.getAt 0 nu b * mult (moveBy a b l nu))
    ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1))

/-- The pair's moved fold at the shifted first letter's weight,
`G_ab`'s first member: the weight `ν_a + 2l` against the
multiplicity at the move. -/
def gFst (mult : List Nat → Nat) (nu : List Nat) (a b : Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun l =>
      (ground.getAt 0 nu a + 2 * l) * mult (moveBy a b l nu))
    ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1))

/-- The trace recursion's moved fold at the pairs' second letters'
weights, the recursion display's first side: `G`'s second members
folded over the letter pairs. -/
def movedSnd (mult : List Nat → Nat) (nu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => gSnd mult nu ab.1 ab.2) (pairsOf nu.length)

/-- The moved fold at the shifted first letters' weights, the
display's second side: `G`'s first members folded. -/
def movedFst (mult : List Nat → Nat) (nu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => gFst mult nu ab.1 ab.2) (pairsOf nu.length)

/-- The recursion's key family at an occupancy family: the members
joined by every content one pair move carries onto a member — at
each letter pair the reversed move `ν^{(l)}` at the shifts within
the first letter's count — the recursion display's carrier, the
display's two sides reading the count's unit at every further
key. -/
def recKeys (d : Nat) (L : List (List Nat)) : List (List Nat) :=
  L ++ L.flatMap (fun mu =>
    (pairsOf d).flatMap (fun ab =>
      ((List.range (getAt 0 mu ab.1)).map (fun l => l + 1)).map
        (fun l => moveBy ab.2 ab.1 l mu)))

/-- The recursion display at a stated multiplicity, the ∀-form over
every content. -/
private def recReadE (lam : Shape) (mult : List Nat → Nat) : Prop :=
  ∀ nu : List Nat, nu.length = lam.length →
    stdSq (display lam) * mult nu + 2 * movedSnd mult nu
      = stdSq (List.zipWith (fun a b => a + b) nu
            (unitDisp lam.length)) * mult nu
        + 2 * movedFst mult nu

/-- The trace recursion, `thm:weylchar`'s display at the recursion
family's keys: `q(λ+u)·mult(ν) + 2 Σ_{a<b} Σ_l ν_b·mult(ν^{(l)})
= q(ν+u)·mult(ν) + 2 Σ_{a<b} Σ_l (ν_a+2l)·mult(ν^{(l)})` at the
occupancy family's count, the shifts through the second letter's
count. -/
def recRead (lam : Shape) (L : List (List Nat)) : Prop :=
  ∀ nu ∈ recKeys lam.length L, nu.length = lam.length →
    stdSq (display lam) * countOf nu L
        + 2 * movedSnd (fun chi => countOf chi L) nu
      = stdSq (List.zipWith (fun a b => a + b) nu
            (unitDisp lam.length)) * countOf nu L
        + 2 * movedFst (fun chi => countOf chi L) nu

instance (lam : Shape) (L : List (List Nat)) :
    Decidable (recRead lam L) :=
  inferInstanceAs (Decidable (∀ nu ∈ recKeys lam.length L,
    nu.length = lam.length →
    stdSq (display lam) * countOf nu L
        + 2 * movedSnd (fun chi => countOf chi L) nu
      = stdSq (List.zipWith (fun a b => a + b) nu
            (unitDisp lam.length)) * countOf nu L
        + 2 * movedFst (fun chi => countOf chi L) nu))

/-- The reflection symmetry at a stated multiplicity, the ∀-form
over every content. -/
private def symReadE (d : Nat) (mult : List Nat → Nat) : Prop :=
  ∀ (i j : Nat) (nu : List Nat), i < j → j < d → nu.length = d →
    mult (swapPair i j nu) = mult nu

/-- The reflection symmetry: the occupancy family's count invariant
under every letter transposition at every member, `ch` symmetric
(`lem:strings`' read at the matrix units, `thm:weylchar`'s
hypothesis). -/
def symRead (d : Nat) (L : List (List Nat)) : Prop :=
  ∀ nu ∈ L, ∀ i, i < d → ∀ j, j < d →
    countOf (swapPair i j nu) L = countOf nu L

instance (d : Nat) (L : List (List Nat)) :
    Decidable (symRead d L) :=
  inferInstanceAs (Decidable (∀ nu ∈ L, ∀ i, i < d → ∀ j, j < d →
    countOf (swapPair i j nu) L = countOf nu L))

/-- The dominance order's walk at a carried prefix slack: per key
the first list's entry at or below the slack with the second's, the
kept gap the next slack, and the walk closes at matched lengths
with the final slack the count's unit — every prefix at or below
with the totals equal. -/
def domGo : Nat → List Nat → List Nat → Bool
  | slack, [], [] => Nat.beq slack 0
  | _, [], _ :: _ => false
  | _, _ :: _, [] => false
  | slack, a :: s, b :: t =>
    if a ≤ slack + b then domGo (slack + b - a) s t else false

/-- The dominance order at matched lists, `ν ⪯ μ`: the walk at the
unit slack. -/
def domBy (nu mu : List Nat) : Prop := domGo 0 nu mu = true

instance (nu mu : List Nat) : Decidable (domBy nu mu) :=
  inferInstanceAs (Decidable (_ = _))

/-- The support clause at a stated multiplicity, the ∀-form over
every content. -/
private def supportReadE (lam : Shape) (mult : List Nat → Nat) :
    Prop :=
  ∀ nu : List Nat, nu.length = lam.length → 0 < mult nu →
    domBy nu (rowList lam)

/-- The support clause: every member of the occupancy family sits
at a content dominated by the top, `ν ⪯ λ` (`lem:lowerspan`'s read,
`thm:weylchar`'s hypothesis). -/
def supportRead (lam : Shape) (L : List (List Nat)) : Prop :=
  ∀ nu ∈ L, domBy nu (rowList lam)

instance (lam : Shape) (L : List (List Nat)) :
    Decidable (supportRead lam L) :=
  inferInstanceAs (Decidable (∀ nu ∈ L, domBy nu (rowList lam)))

/-- The top clause at a stated multiplicity, the top content's
value. -/
private def topReadE (lam : Shape) (mult : List Nat → Nat) : Prop :=
  mult (rowList lam) = 1

/-- The top clause: the top content's count one, the block's top
line (`lem:lowerspan`'s read). -/
def topRead (lam : Shape) (L : List (List Nat)) : Prop :=
  countOf (rowList lam) L = 1

instance (lam : Shape) (L : List (List Nat)) :
    Decidable (topRead lam L) :=
  inferInstanceAs (Decidable (_ = _))

/-- The alternant identity's read at a key: the product's graded
coefficient against the shifted alternant's, one value of the two
balance pairs — `[a_u · ch_λ]_y = [a_{λ+u}]_y`, `thm:weylchar`'s
display coefficientwise. -/
def identityAt (mult : List Nat → Nat) (lam : Shape)
    (y : List Nat) : Prop :=
  prodCount mult lam.length y false
      + sideCount lam.length (display lam) y true
    = prodCount mult lam.length y true
      + sideCount lam.length (display lam) y false

instance (mult : List Nat → Nat) (lam : Shape) (y : List Nat) :
    Decidable (identityAt mult lam y) :=
  inferInstanceAs (Decidable (_ = _))

/-- The exchange read: at a permuted exponent list the graded
counts exchange along the permutation's grading — an odd
permutation of the exponents exchanges the members, an even one
fixes them, the grading additive over composition. -/
theorem exchange_read (d : Nat) (beta y q : List Nat)
    (hq : 0 < ground.countOf q (perms d)) (side : Bool) :
    sideCount d (expo beta q) y side
      = sideCount d beta y (xor side (parity q)) := by
  obtain ⟨hqlen, hqdist, hqval, hqocc⟩ := perm_member_reads hq
  have hInv := invPerm_member d hq
  have hInvLen : (invPerm d q).length = d := length_invPerm d q
  have hmem : ∀ {p : List Nat}, 0 < ground.countOf p (perms d) →
      0 < ground.countOf (p.map (ground.getAt 0 (invPerm d q)))
        (perms d) := fun {p} hp => by
    obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
    exact perm_member_of_counts hInv
      (by rw [ground.length_map, hplen, hInvLen])
      (fun x => countOf_comp d x hp hInvLen)
  have hmem' : ∀ {p : List Nat}, 0 < ground.countOf p (perms d) →
      0 < ground.countOf (p.map (ground.getAt 0 q)) (perms d) :=
    fun {p} hp => by
      obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
      exact perm_member_of_counts hq
        (by rw [ground.length_map, hplen, hqlen])
        (fun x => countOf_comp d x hp hqlen)
  have hgh : ∀ p, 0 < ground.countOf p (perms d) →
      (p.map (ground.getAt 0 (invPerm d q))).map (ground.getAt 0 q)
        = p := fun p hp => by
    obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
    rw [ground.map_map, ground.map_congr_members
        (fun x => ground.getAt 0 q (ground.getAt 0 (invPerm d q) x))
        (fun x => x) p (fun v hv => by
          have hvd : v < d := hpval v hv
          rw [getAt_invPerm d q hvd]
          exact getAt_posOf v q (hqocc v hvd)),
      ground.map_id]
  have hhg : ∀ p, 0 < ground.countOf p (perms d) →
      (p.map (ground.getAt 0 q)).map (ground.getAt 0 (invPerm d q))
        = p := fun p hp => by
    obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
    rw [ground.map_map, ground.map_congr_members
        (fun x => ground.getAt 0 (invPerm d q) (ground.getAt 0 q x))
        (fun x => x) p (fun v hv => by
          have hvd : v < d := hpval v hv
          have hqv : ground.getAt 0 q v < d :=
            hqval (ground.getAt 0 q v)
              (countOf_getAt_pos 0 q v (by rw [hqlen]; exact hvd))
          rw [getAt_invPerm d q hqv]
          exact posOf_getAt hqdist v (by rw [hqlen]; exact hvd)),
      ground.map_id]
  show ground.famFold Nat.add 0
      (fun p => if parity p = side then
        (if expo (expo beta q) p = y then 1 else 0) else 0)
      (perms d)
    = ground.famFold Nat.add 0
      (fun p => if parity p = xor side (parity q) then
        (if expo beta p = y then 1 else 0) else 0)
      (perms d)
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun p => if parity p = side then
        (if expo (expo beta q) p = y then 1 else 0) else 0)
      (l := perms d)
      (g := fun p => p.map (ground.getAt 0 (invPerm d q)))
      (h := fun p => p.map (ground.getAt 0 q))
      (monomialsAt_distinct _)
      (fun p hp => hgh p hp)
      (fun p hp => hhg p hp)
      (fun p hp => hmem hp)
      (fun p hp => hmem' hp)]
  exact ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => by
      obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
      have hexpo : expo (expo beta q)
          (p.map (ground.getAt 0 (invPerm d q)))
          = expo beta p := by
        show (p.map (ground.getAt 0 (invPerm d q))).map
            (ground.getAt 0 (expo beta q)) = expo beta p
        have hmemp := hmem hp
        obtain ⟨hplen', _, hpval', _⟩ := perm_member_reads hmemp
        rw [ground.map_congr_members
            (ground.getAt 0 (expo beta q))
            (fun x => ground.getAt 0 beta (ground.getAt 0 q x))
            (p.map (ground.getAt 0 (invPerm d q))) (fun v hv => by
              have hvd : v < d := hpval' v hv
              show ground.getAt 0 (q.map (ground.getAt 0 beta)) v
                = ground.getAt 0 beta (ground.getAt 0 q v)
              exact ground.getAt_map 0 0 (ground.getAt 0 beta) q v
                (by rw [hqlen]; exact hvd)),
          ← ground.map_map (ground.getAt 0 q)
            (ground.getAt 0 beta),
          hgh p hp]
        rfl
      have hpar : parity (p.map (ground.getAt 0 (invPerm d q)))
          = xor (parity p) (parity q) := by
        rw [parity_comp d p (invPerm d q) hp hInv,
          parity_invPerm d hq]
      rw [hexpo, hpar]
      by_cases hc : xor (parity p) (parity q) = side
      · rw [if_pos hc, if_pos (xor_shift.mp hc)]
      · rw [if_neg hc,
          if_neg (fun hc2 : parity p = xor side (parity q) =>
            hc (xor_shift.mpr hc2))])

/-! The key's exchange and repeat reads: transposing two places of
the key exchanges the two graded coefficients — the reindex at the
places' transposition, the multiplicity's symmetry reading the tie
across — so a key at a repeated entry reads equal members on both
coefficients, the identity's read there. -/

private theorem not_shift : ∀ {a b : Bool},
    ((!a) = b) ↔ (a = !b) := by
  intro a b
  cases a <;> cases b <;> exact ⟨fun h => by
      first | rfl | exact absurd h (fun hh => Bool.noConfusion hh),
    fun h => by
      first | rfl | exact absurd h (fun hh => Bool.noConfusion hh)⟩

private theorem swapKey_member {d i j : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    0 < ground.countOf (swapPair i j p) (perms d) :=
  perm_member_of_counts hp (length_swapPair i j p)
    (fun x => countOf_swapPair x i j p)

/-- The graded counts at a transposed key exchange sides: the swap
grading's read through the key. -/
theorem sideCount_swapKey (d : Nat) (beta y : List Nat) {i j : Nat}
    (hij : i < j) (hjd : j < d) (side : Bool) :
    sideCount d beta (swapPair i j y) side
      = sideCount d beta y (!side) := by
  have hne : i ≠ j := Nat.ne_of_lt hij
  have hid : i < d := Nat.lt_trans hij hjd
  show ground.famFold Nat.add 0
      (fun p => if parity p = side then
        (if expo beta p = swapPair i j y then 1 else 0) else 0)
      (perms d)
    = ground.famFold Nat.add 0
      (fun p => if parity p = (!side) then
        (if expo beta p = y then 1 else 0) else 0)
      (perms d)
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun p => if parity p = side then
        (if expo beta p = swapPair i j y then 1 else 0) else 0)
      (l := perms d) (g := swapPair i j) (h := swapPair i j)
      (monomialsAt_distinct _)
      (fun p _ => swapPair_swapPair i j p)
      (fun p _ => swapPair_swapPair i j p)
      (fun p hp => swapKey_member hp)
      (fun p hp => swapKey_member hp)]
  exact ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => by
      obtain ⟨hplen, hpdist, _, _⟩ := perm_member_reads hp
      have hi' : i < p.length := by rw [hplen]; exact hid
      have hj' : j < p.length := by rw [hplen]; exact hjd
      show (if parity (swapPair i j p) = side then
          (if expo beta (swapPair i j p) = swapPair i j y then 1
            else 0) else 0)
        = (if parity p = (!side) then
            (if expo beta p = y then 1 else 0) else 0)
      have hexpo : expo beta (swapPair i j p)
          = swapPair i j (expo beta p) := by
        show (swapPair i j p).map (ground.getAt 0 beta) = _
        rw [← swapPair_map (ground.getAt 0 beta) i j p]
        rfl
      have hinner : (if swapPair i j (expo beta p) = swapPair i j y
          then (1 : Nat) else 0)
          = (if expo beta p = y then (1 : Nat) else 0) := by
        by_cases hey : expo beta p = y
        · rw [if_pos hey, if_pos (by rw [hey])]
        · rw [if_neg hey, if_neg (fun hc => hey
            ((swapPair_swapPair i j (expo beta p)).symm.trans
              ((congrArg (swapPair i j) hc).trans
                (swapPair_swapPair i j y))))]
      rw [hexpo, hinner,
        parity_swapPair p hne hi' hj' hpdist]
      by_cases hc : parity p = !side
      · rw [if_pos hc, if_pos (not_shift.mpr hc)]
      · rw [if_neg hc, if_neg (fun h2 => hc (not_shift.mp h2))])

/-- The product's coefficient at a transposed key exchanges sides,
the multiplicity's symmetry reading the tie across the
transposition. -/
private theorem prodCount_swapKey {d : Nat} (mult : List Nat → Nat)
    (hsym : symReadE d mult) {i j : Nat} (hij : i < j) (hjd : j < d)
    (y : List Nat) (hy : y.length = d) (side : Bool) :
    prodCount mult d (swapPair i j y) side
      = prodCount mult d y (!side) := by
  have hne : i ≠ j := Nat.ne_of_lt hij
  have hid : i < d := Nat.lt_trans hij hjd
  show ground.famFold Nat.add 0
      (fun p => if parity p = side then
        multAtGap mult (swapPair i j y) (expo (unitDisp d) p) else 0)
      (perms d)
    = ground.famFold Nat.add 0
      (fun p => if parity p = (!side) then
        multAtGap mult y (expo (unitDisp d) p) else 0)
      (perms d)
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun p => if parity p = side then
        multAtGap mult (swapPair i j y) (expo (unitDisp d) p) else 0)
      (l := perms d) (g := swapPair i j) (h := swapPair i j)
      (monomialsAt_distinct _)
      (fun p _ => swapPair_swapPair i j p)
      (fun p _ => swapPair_swapPair i j p)
      (fun p hp => swapKey_member hp)
      (fun p hp => swapKey_member hp)]
  exact ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => by
      obtain ⟨hplen, hpdist, _, _⟩ := perm_member_reads hp
      have hi' : i < p.length := by rw [hplen]; exact hid
      have hj' : j < p.length := by rw [hplen]; exact hjd
      show (if parity (swapPair i j p) = side then
          multAtGap mult (swapPair i j y)
            (expo (unitDisp d) (swapPair i j p)) else 0)
        = (if parity p = (!side) then
            multAtGap mult y (expo (unitDisp d) p) else 0)
      have hexpo : expo (unitDisp d) (swapPair i j p)
          = swapPair i j (expo (unitDisp d) p) := by
        show (swapPair i j p).map (ground.getAt 0 (unitDisp d)) = _
        rw [← swapPair_map (ground.getAt 0 (unitDisp d)) i j p]
        rfl
      have hgap : multAtGap mult (swapPair i j y)
          (swapPair i j (expo (unitDisp d) p))
          = multAtGap mult y (expo (unitDisp d) p) := by
        show (match tieGap (swapPair i j y)
            (swapPair i j (expo (unitDisp d) p)) with
          | some nu => mult nu
          | none => 0)
          = (match tieGap y (expo (unitDisp d) p) with
            | some nu => mult nu
            | none => 0)
        rw [tieGap_swapPair hne y (expo (unitDisp d) p)
            (by rw [hy]; exact hid) (by rw [hy]; exact hjd)
            (by show (p.map _).length = y.length
                rw [ground.length_map, hplen, hy])]
        cases hyz : tieGap y (expo (unitDisp d) p) with
        | some nu =>
          show mult (swapPair i j nu) = mult nu
          obtain ⟨hnl, _, _⟩ := tieGap_reads _ _ nu hyz
          exact hsym i j nu hij hjd (by rw [hnl, hy])
        | none => rfl
      rw [hexpo, hgap, parity_swapPair p hne hi' hj' hpdist]
      by_cases hc : parity p = !side
      · rw [if_pos hc, if_pos (not_shift.mpr hc)]
      · rw [if_neg hc, if_neg (fun h2 => hc (not_shift.mp h2))])

/-- The graded counts at a repeated key read equal members, the
repeat's transposition fixing the key while exchanging the
sides. -/
theorem sideCount_repeatKey (d : Nat) (beta y : List Nat)
    {i j : Nat} (hij : i < j) (hjd : j < d) (hy : y.length = d)
    (heq : ground.getAt 0 y i = ground.getAt 0 y j) (side : Bool) :
    sideCount d beta y side = sideCount d beta y (!side) := by
  have hswap : swapPair i j y = y :=
    swapPair_eq_of_getAt_eq y (Nat.ne_of_lt hij)
      (by rw [hy]; exact Nat.lt_trans hij hjd)
      (by rw [hy]; exact hjd) heq
  calc sideCount d beta y side
      = sideCount d beta (swapPair i j y) side := by rw [hswap]
    _ = sideCount d beta y (!side) :=
        sideCount_swapKey d beta y hij hjd side

/-- The product's coefficient at a repeated key reads equal
members. -/
private theorem prodCount_repeatKey {d : Nat} (mult : List Nat → Nat)
    (hsym : symReadE d mult) {i j : Nat} (hij : i < j) (hjd : j < d)
    (y : List Nat) (hy : y.length = d)
    (heq : ground.getAt 0 y i = ground.getAt 0 y j) (side : Bool) :
    prodCount mult d y side = prodCount mult d y (!side) := by
  have hswap : swapPair i j y = y :=
    swapPair_eq_of_getAt_eq y (Nat.ne_of_lt hij)
      (by rw [hy]; exact Nat.lt_trans hij hjd)
      (by rw [hy]; exact hjd) heq
  calc prodCount mult d y side
      = prodCount mult d (swapPair i j y) side := by rw [hswap]
    _ = prodCount mult d y (!side) :=
        prodCount_swapKey mult hsym hij hjd y hy side

/-- The identity's read at a repeated key: both coefficients are
equal-membered, so the crossed sums agree — `thm:weylchar`'s
repeated-exponent clause at the product. -/
private theorem identityAt_repeatKey (mult : List Nat → Nat) (lam : Shape)
    (hsym : symReadE lam.length mult) {i j : Nat} (hij : i < j)
    (hjd : j < lam.length) (y : List Nat)
    (hy : y.length = lam.length)
    (heq : ground.getAt 0 y i = ground.getAt 0 y j) :
    identityAt mult lam y := by
  show prodCount mult lam.length y false
      + sideCount lam.length (display lam) y true
    = prodCount mult lam.length y true
      + sideCount lam.length (display lam) y false
  rw [prodCount_repeatKey mult hsym hij hjd y hy heq false,
    sideCount_repeatKey lam.length (display lam) y hij hjd hy heq
      true]
  rfl

/-- The identity's read transports across a key transposition: the
two sides' reads exchange together. -/
private theorem identityAt_swapKey (mult : List Nat → Nat) (lam : Shape)
    (hsym : symReadE lam.length mult) {i j : Nat} (hij : i < j)
    (hjd : j < lam.length) (y : List Nat)
    (hy : y.length = lam.length) (hid : identityAt mult lam y) :
    identityAt mult lam (swapPair i j y) := by
  show prodCount mult lam.length (swapPair i j y) false
      + sideCount lam.length (display lam) (swapPair i j y) true
    = prodCount mult lam.length (swapPair i j y) true
      + sideCount lam.length (display lam) (swapPair i j y) false
  rw [prodCount_swapKey mult hsym hij hjd y hy false,
    prodCount_swapKey mult hsym hij hjd y hy true,
    sideCount_swapKey lam.length (display lam) y hij hjd true,
    sideCount_swapKey lam.length (display lam) y hij hjd false]
  exact hid.symm

/-! The separation (`thm:weylchar`'s conclusion): at a sorted
content dominated by the top off it, the shifted square sits
strictly below the top's — `q(λ+u) = q(μ+u) + Σ_k δ_k g_k` at the
dominance order's prefix gaps against the weight steps, every
summand two naturals' product and one positive. -/

private theorem subSuccLt : ∀ (d i : Nat), i + 1 ≤ d →
    d - (i + 1) < d - i
  | 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | e + 1, 0, _ => by
    show e + 1 - 1 < e + 1 - 0
    rw [Nat.succ_sub_succ]
    exact Nat.lt_succ_self e
  | e + 1, i + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    exact subSuccLt e i (Nat.le_of_succ_le_succ h)

/-- The unit display's entries, `u_i = d - i`. -/
theorem unitDisp_eq (d : Nat) :
    unitDisp d = (List.range d).map (fun i => d - i) := by
  show List.zipWith (fun l u => l + u)
      (rowList (List.replicate d 0))
      ((List.range (List.replicate d (0 : Nat)).length).map
        (fun i => (List.replicate d (0 : Nat)).length - i))
    = (List.range d).map (fun i => d - i)
  rw [ground.length_replicate 0 d,
    places.rowList_replicate_zero d,
    ground.zipWith_zero_left d ((List.range d).map (fun i => d - i))
      (ground.length_mapRange _ _)]

/-- The unit display's entry read at an interior key. -/
theorem getAt_unitDisp (d i : Nat) (hi : i < d) :
    ground.getAt 0 (unitDisp d) i = d - i := by
  have h := getAt_display (List.replicate d 0) i
    (by rw [ground.length_replicate 0]; exact hi)
  rw [places.rowList_replicate_zero d,
    ground.getAt_replicate_zero d i, ground.length_replicate 0 d, Nat.zero_add] at h
  exact h

/-- The unit display descends strictly. -/
theorem unitDisp_strict (d i : Nat) (hi : i + 1 < d) :
    ground.getAt 0 (unitDisp d) (i + 1)
      < ground.getAt 0 (unitDisp d) i := by
  rw [getAt_unitDisp d (i + 1) hi,
    getAt_unitDisp d i (Nat.lt_of_succ_lt hi)]
  exact subSuccLt d i (Nat.le_of_lt hi)

/-- The display is the row list against the unit display, the
zipped read. -/
theorem display_zip (s : Shape) :
    display s
      = List.zipWith (fun l u => l + u) (rowList s)
          (unitDisp s.length) := by
  show List.zipWith (fun l u => l + u) (rowList s)
      ((List.range s.length).map (fun i => s.length - i)) = _
  rw [unitDisp_eq s.length]

private theorem sqExpand (x y c : Nat) :
    (x + c) * (x + c) + y * (x + y + (c + c))
      = x * x + (y * y + (c * c + (x * y
          + ((x * c + x * c) + (y * c + y * c))))) := by
  rw [ground.mulAddR x c (x + c), Nat.left_distrib x x c,
    Nat.left_distrib c x c, Nat.left_distrib y (x + y) (c + c),
    Nat.left_distrib y x y, Nat.left_distrib y c c,
    Nat.mul_comm c x, Nat.mul_comm y x]
  rw [Nat.add_assoc (x * x) (x * c) (x * c + c * c),
    ← Nat.add_assoc (x * c) (x * c) (c * c)]
  rw [Nat.add_assoc (x * x) ((x * c + x * c) + c * c)
      ((x * y + y * y) + (y * c + y * c))]
  rw [Nat.add_comm (x * y) (y * y),
    Nat.add_assoc (y * y) (x * y) (y * c + y * c),
    Nat.add_left_comm ((x * c + x * c) + c * c) (y * y)
      (x * y + (y * c + y * c))]
  rw [Nat.add_comm (x * c + x * c) (c * c),
    Nat.add_assoc (c * c) (x * c + x * c) (x * y + (y * c + y * c)),
    Nat.add_left_comm (x * c + x * c) (x * y) (y * c + y * c)]

private theorem headSq (a b c : Nat) :
    (a + c) * (a + c) + b * (a + b + (c + c))
      = (b + c) * (b + c) + a * (b + a + (c + c)) := by
  rw [sqExpand a b c, sqExpand b a c, Nat.mul_comm a b,
    Nat.add_left_comm (a * a) (b * b)
      (c * c + (b * a + ((a * c + a * c) + (b * c + b * c)))),
    Nat.add_comm (a * c + a * c) (b * c + b * c)]

private theorem shuffleA (p q r s t : Nat) :
    ((p + q) + r) + (s + t) = (p + t) + ((q + s) + r) := by
  have hL : ((p + q) + r) + (s + t)
      = p + (q + (r + (s + t))) := by
    rw [Nat.add_assoc (p + q) r (s + t), Nat.add_assoc p q _]
  have hR : (p + t) + ((q + s) + r)
      = p + (q + (r + (s + t))) := by
    rw [Nat.add_assoc p t ((q + s) + r),
      Nat.add_left_comm t (q + s) r, Nat.add_assoc q s (t + r),
      Nat.add_comm t r, Nat.add_left_comm s r t]
  rw [hL, hR]

private theorem shuffleB (p u q v r : Nat) :
    (p + u) + ((q + v) + r) = (p + q) + (v + (u + r)) := by
  have hL : (p + u) + ((q + v) + r)
      = p + (u + (q + (v + r))) := by
    rw [Nat.add_assoc p u ((q + v) + r), Nat.add_assoc q v r]
  have hR : (p + q) + (v + (u + r))
      = p + (u + (q + (v + r))) := by
    rw [Nat.add_assoc p q (v + (u + r)),
      Nat.add_left_comm v u r, Nat.add_left_comm q u (v + r)]
  rw [hL, hR]

private theorem shuffleC (P v g s t : Nat) :
    P + (v + ((g + s) + t)) = (P + (g + v)) + (s + t) := by
  have hL : P + (v + ((g + s) + t))
      = P + (g + (v + (s + t))) := by
    rw [Nat.add_assoc g s t, Nat.add_left_comm v g (s + t)]
  have hR : (P + (g + v)) + (s + t)
      = P + (g + (v + (s + t))) := by
    rw [Nat.add_assoc P (g + v) (s + t),
      Nat.add_assoc g v (s + t)]
  rw [hL, hR]

/-- The dominance identity's collected fold, `Σ_{k≥1} δ_k g_k` at
the walked prefix gaps against the weight steps, the recursion in
lockstep with the order's walk. -/
private def sepFold : Nat → List Nat → List Nat → List Nat → Nat
  | _, [], _, _ => 0
  | _, [_], _, _ => 0
  | _, _ :: _ :: _, [], _ => 0
  | _, _ :: _ :: _, [_], _ => 0
  | _, _ :: _ :: _, _ :: _ :: _, [] => 0
  | _, _ :: _ :: _, _ :: _ :: _, [_] => 0
  | slack, b :: b' :: X2, a :: a' :: Y2, c :: c' :: w2 =>
    (slack + a - b) * ((a + b + (c + c)) - (a' + b' + (c' + c')))
      + sepFold (slack + a - b) (b' :: X2) (a' :: Y2) (c' :: w2)

/-- The dominance walk's length tie: the two families run at one
length. -/
theorem domGo_len : ∀ (slack : Nat) (X Y : List Nat),
    domGo slack X Y = true → X.length = Y.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => Bool.noConfusion h
  | _, _ :: _, [], h => Bool.noConfusion h
  | slack, a :: s, b :: t, h => by
    have h' : (if a ≤ slack + b then domGo (slack + b - a) s t
        else false) = true := h
    by_cases hb : a ≤ slack + b
    · rw [if_pos hb] at h'
      show s.length + 1 = t.length + 1
      rw [domGo_len (slack + b - a) s t h']
    · rw [if_neg hb] at h'
      exact Bool.noConfusion h'

private theorem sepFold_eq : ∀ (X Y w : List Nat) (slack : Nat),
    w.length = X.length →
    domGo slack X Y = true →
    (∀ i, i + 1 < X.length →
      ground.getAt 0 X (i + 1) ≤ ground.getAt 0 X i) →
    (∀ i, i + 1 < Y.length →
      ground.getAt 0 Y (i + 1) ≤ ground.getAt 0 Y i) →
    (∀ i, i + 1 < w.length →
      ground.getAt 0 w (i + 1) ≤ ground.getAt 0 w i) →
    stdSq (List.zipWith (fun l u => l + u) Y w)
        + slack * (ground.getAt 0 Y 0 + ground.getAt 0 X 0
            + (ground.getAt 0 w 0 + ground.getAt 0 w 0))
      = stdSq (List.zipWith (fun l u => l + u) X w)
        + sepFold slack X Y w
  | [], [], [], slack, _, hdom, _, _, _ => by
    have hz : slack = 0 := ground.beqEq _ _ hdom
    rw [hz, Nat.zero_mul]
    rfl
  | [], [], _ :: _, _, hw, _, _, _, _ => Nat.noConfusion hw
  | [], _ :: _, _, _, _, hdom, _, _, _ => Bool.noConfusion hdom
  | _ :: _, [], _, _, _, hdom, _, _, _ => Bool.noConfusion hdom
  | [b], a :: t, [], _, hw, _, _, _, _ => Nat.noConfusion hw
  | [b], a :: t, _ :: _ :: _, _, hw, _, _, _, _ =>
    Nat.noConfusion (Nat.succ.inj hw)
  | [b], a :: t, [c], slack, _, hdom, _, _, _ => by
    have h' : (if b ≤ slack + a then domGo (slack + a - b) [] t
        else false) = true := hdom
    by_cases hb : b ≤ slack + a
    · rw [if_pos hb] at h'
      match t, h' with
      | _ :: _, h' => exact Bool.noConfusion h'
      | [], h' =>
        have hz : slack + a - b = 0 := ground.beqEq _ _ h'
        have hba : b = slack + a := by
          have hs := subAdd hb
          rw [hz, Nat.zero_add] at hs
          exact hs
        show (a + c) * (a + c) + slack * (a + b + (c + c))
          = (b + c) * (b + c)
        refine addCancelR (a * (a + b + (c + c))) ?_
        rw [Nat.add_assoc ((a + c) * (a + c))
            (slack * (a + b + (c + c))) (a * (a + b + (c + c))),
          ← ground.mulAddR slack a (a + b + (c + c)),
          ← hba, headSq a b c,
          show b + a + (c + c) = a + b + (c + c) from by
            rw [Nat.add_comm b a]]
    · rw [if_neg hb] at h'
      exact Bool.noConfusion h'
  | b :: b' :: X2, [a], w, slack, _, hdom, _, _, _ => by
    have h' : (if b ≤ slack + a then
        domGo (slack + a - b) (b' :: X2) [] else false) = true :=
      hdom
    by_cases hb : b ≤ slack + a
    · rw [if_pos hb] at h'
      exact Bool.noConfusion h'
    · rw [if_neg hb] at h'
      exact Bool.noConfusion h'
  | _ :: _ :: _, _ :: _ :: _, [], _, hw, _, _, _, _ =>
    Nat.noConfusion hw
  | _ :: _ :: _, _ :: _ :: _, [_], _, hw, _, _, _, _ =>
    Nat.noConfusion (Nat.succ.inj hw)
  | b :: b' :: X2, a :: a' :: Y2, c :: c' :: w2, slack, hw, hdom,
      hsX, hsY, hsw => by
    have h' : (if b ≤ slack + a then
        domGo (slack + a - b) (b' :: X2) (a' :: Y2) else false)
        = true := hdom
    by_cases hb : b ≤ slack + a
    · rw [if_pos hb] at h'
      have hsl : (slack + a - b) + b = slack + a := subAdd hb
      have hIH := sepFold_eq (b' :: X2) (a' :: Y2) (c' :: w2)
        (slack + a - b) (Nat.succ.inj hw) h'
        (fun i hi => hsX (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi => hsY (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi => hsw (i + 1) (Nat.succ_lt_succ hi))
      have hv1 : a' + b' + (c' + c') ≤ a + b + (c + c) := by
        have ha' : a' ≤ a :=
          hsY 0 (Nat.succ_lt_succ (Nat.succ_pos _))
        have hb' : b' ≤ b :=
          hsX 0 (Nat.succ_lt_succ (Nat.succ_pos _))
        have hc' : c' ≤ c :=
          hsw 0 (Nat.succ_lt_succ (Nat.succ_pos _))
        exact Nat.add_le_add (Nat.add_le_add ha' hb')
          (Nat.add_le_add hc' hc')
      have hg : ((a + b + (c + c)) - (a' + b' + (c' + c')))
          + (a' + b' + (c' + c')) = a + b + (c + c) := subAdd hv1
      show (a + c) * (a + c)
          + stdSq (List.zipWith (fun l u => l + u)
              (a' :: Y2) (c' :: w2))
          + slack * (a + b + (c + c))
        = (b + c) * (b + c)
          + stdSq (List.zipWith (fun l u => l + u)
              (b' :: X2) (c' :: w2))
          + ((slack + a - b)
              * ((a + b + (c + c)) - (a' + b' + (c' + c')))
            + sepFold (slack + a - b) (b' :: X2) (a' :: Y2)
                (c' :: w2))
      refine addCancelR
        ((slack + a - b) * (a' + b' + (c' + c'))
          + b * (a + b + (c + c))) ?_
      rw [shuffleA ((a + c) * (a + c))
          (stdSq (List.zipWith (fun l u => l + u)
            (a' :: Y2) (c' :: w2)))
          (slack * (a + b + (c + c)))
          ((slack + a - b) * (a' + b' + (c' + c')))
          (b * (a + b + (c + c)))]
      rw [headSq a b c]
      rw [show ground.getAt 0 (a' :: Y2) 0 + ground.getAt 0
          (b' :: X2) 0 + (ground.getAt 0 (c' :: w2) 0
            + ground.getAt 0 (c' :: w2) 0)
          = a' + b' + (c' + c') from rfl] at hIH
      rw [hIH]
      rw [shuffleB ((b + c) * (b + c)) (a * (b + a + (c + c)))
          (stdSq (List.zipWith (fun l u => l + u)
            (b' :: X2) (c' :: w2)))
          (sepFold (slack + a - b) (b' :: X2) (a' :: Y2)
            (c' :: w2))
          (slack * (a + b + (c + c)))]
      rw [show a * (b + a + (c + c)) + slack * (a + b + (c + c))
          = (slack + a - b) * (a + b + (c + c))
            + b * (a + b + (c + c)) from by
        rw [show b + a + (c + c) = a + b + (c + c) from by
            rw [Nat.add_comm b a],
          ← ground.mulAddR a slack (a + b + (c + c)),
          ← ground.mulAddR (slack + a - b) b (a + b + (c + c)),
          hsl, Nat.add_comm a slack]]
      rw [show (slack + a - b) * (a + b + (c + c))
          = (slack + a - b)
              * ((a + b + (c + c)) - (a' + b' + (c' + c')))
            + (slack + a - b) * (a' + b' + (c' + c')) from by
        rw [← Nat.left_distrib (slack + a - b)
            ((a + b + (c + c)) - (a' + b' + (c' + c')))
            (a' + b' + (c' + c')), hg]]
      rw [shuffleC ((b + c) * (b + c)
          + stdSq (List.zipWith (fun l u => l + u)
            (b' :: X2) (c' :: w2)))
          (sepFold (slack + a - b) (b' :: X2) (a' :: Y2)
            (c' :: w2))
          ((slack + a - b)
            * ((a + b + (c + c)) - (a' + b' + (c' + c'))))
          ((slack + a - b) * (a' + b' + (c' + c')))
          (b * (a + b + (c + c)))]
    · rw [if_neg hb] at h'
      exact Bool.noConfusion h'

private theorem sepFold_pos : ∀ (X Y w : List Nat),
    domGo 0 X Y = true → X ≠ Y →
    (∀ i, i + 1 < X.length →
      ground.getAt 0 X (i + 1) ≤ ground.getAt 0 X i) →
    (∀ i, i + 1 < Y.length →
      ground.getAt 0 Y (i + 1) ≤ ground.getAt 0 Y i) →
    (∀ i, i + 1 < w.length →
      ground.getAt 0 w (i + 1) < ground.getAt 0 w i) →
    w.length = X.length →
    0 < sepFold 0 X Y w
  | [], [], _, _, hne, _, _, _, _ => absurd rfl hne
  | [], _ :: _, _, hdom, _, _, _, _, _ => Bool.noConfusion hdom
  | _ :: _, [], _, hdom, _, _, _, _, _ => Bool.noConfusion hdom
  | b :: s, a :: t, w, hdom, hne, hsX, hsY, hsw, hw => by
    have h' : (if b ≤ 0 + a then domGo (0 + a - b) s t else false)
        = true := hdom
    by_cases hb : b ≤ 0 + a
    · rw [if_pos hb] at h'
      by_cases heq : b = a
      · have hz : 0 + a - b = 0 := by
          rw [heq, Nat.zero_add, Nat.sub_self]
        match s, t, h', hw with
        | [], [], _, _ => exact absurd (by rw [heq]) hne
        | [], _ :: _, h', _ => exact Bool.noConfusion h'
        | _ :: _, [], h', _ => exact Bool.noConfusion h'
        | b' :: s2, a' :: t2, h', hw =>
          match w, hw with
          | [], hw => exact Nat.noConfusion hw
          | [_], hw => exact Nat.noConfusion (Nat.succ.inj hw)
          | c :: c' :: w2, hw =>
            show 0 < (0 + a - b)
                * ((a + b + (c + c)) - (a' + b' + (c' + c')))
              + sepFold (0 + a - b) (b' :: s2) (a' :: t2)
                  (c' :: w2)
            rw [hz, Nat.zero_mul, Nat.zero_add]
            rw [hz] at h'
            exact sepFold_pos (b' :: s2) (a' :: t2) (c' :: w2) h'
              (fun hcon => hne (by rw [heq, hcon]))
              (fun i hi => hsX (i + 1) (Nat.succ_lt_succ hi))
              (fun i hi => hsY (i + 1) (Nat.succ_lt_succ hi))
              (fun i hi => hsw (i + 1) (Nat.succ_lt_succ hi))
              (Nat.succ.inj hw)
      · have hlt : b < a := by
          rw [Nat.zero_add] at hb
          exact Nat.lt_of_le_of_ne hb heq
        have hsp : 0 < 0 + a - b := by
          rw [Nat.zero_add]
          exact subPos hlt
        match s, t, h', hw with
        | [], [], h', _ =>
          have hz := ground.beqEq _ _ h'
          rw [hz] at hsp
          exact absurd hsp (Nat.lt_irrefl 0)
        | [], _ :: _, h', _ => exact Bool.noConfusion h'
        | _ :: _, [], h', _ => exact Bool.noConfusion h'
        | b' :: s2, a' :: t2, h', hw =>
          match w, hw with
          | [], hw => exact Nat.noConfusion hw
          | [_], hw => exact Nat.noConfusion (Nat.succ.inj hw)
          | c :: c' :: w2, hw =>
            show 0 < (0 + a - b)
                * ((a + b + (c + c)) - (a' + b' + (c' + c')))
              + sepFold (0 + a - b) (b' :: s2) (a' :: t2)
                  (c' :: w2)
            have ha' : a' ≤ a :=
              hsY 0 (Nat.succ_lt_succ (Nat.succ_pos _))
            have hb' : b' ≤ b :=
              hsX 0 (Nat.succ_lt_succ (Nat.succ_pos _))
            have hc' : c' < c :=
              hsw 0 (Nat.succ_lt_succ (Nat.succ_pos _))
            have h2c : c' + c' < c + c :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left hc' c')
                (Nat.add_le_add_right (Nat.le_of_lt hc') c)
            have hv : a' + b' + (c' + c') < a + b + (c + c) :=
              Nat.lt_of_le_of_lt
                (Nat.add_le_add_right (Nat.add_le_add ha' hb')
                  (c' + c'))
                (Nat.add_lt_add_left h2c (a + b))
            exact Nat.lt_of_lt_of_le (Nat.mul_pos hsp (subPos hv))
              (Nat.le_add_right _ _)
    · rw [if_neg hb] at h'
      exact Bool.noConfusion h'

/-- The separation: at a sorted content dominated by the top off
it, the shifted square sits strictly below the top's —
`q(μ+u) < q(λ+u)` at `q(λ+u) = q(μ+u) + Σ_k δ_k g_k`, the
dominance order's prefix gaps against the weight steps, some
summand positive (`thm:weylchar`'s conclusion display). -/
theorem sq_lt_of_dom (lam : Shape) (mu : List Nat)
    (hsort : ∀ i, i + 1 < mu.length →
      ground.getAt 0 mu (i + 1) ≤ ground.getAt 0 mu i)
    (hdom : domBy mu (rowList lam)) (hne : mu ≠ rowList lam) :
    stdSq (List.zipWith (fun l u => l + u) mu
        (unitDisp lam.length))
      < stdSq (display lam) := by
  have hlen : mu.length = lam.length := by
    rw [domGo_len 0 mu (rowList lam) hdom, length_rowList]
  have hwlen : (unitDisp lam.length).length = mu.length := by
    rw [length_unitDisp, hlen]
  have hYs : ∀ i, i + 1 < (rowList lam).length →
      ground.getAt 0 (rowList lam) (i + 1)
        ≤ ground.getAt 0 (rowList lam) i := fun i hi =>
    rowList_le lam i (by rw [length_rowList] at hi; exact hi)
  have hws : ∀ i, i + 1 < (unitDisp lam.length).length →
      ground.getAt 0 (unitDisp lam.length) (i + 1)
        ≤ ground.getAt 0 (unitDisp lam.length) i := fun i hi =>
    Nat.le_of_lt (unitDisp_strict lam.length i
      (by rw [length_unitDisp] at hi; exact hi))
  have hwstrict : ∀ i, i + 1 < (unitDisp lam.length).length →
      ground.getAt 0 (unitDisp lam.length) (i + 1)
        < ground.getAt 0 (unitDisp lam.length) i := fun i hi =>
    unitDisp_strict lam.length i
      (by rw [length_unitDisp] at hi; exact hi)
  have heq := sepFold_eq mu (rowList lam) (unitDisp lam.length) 0
    hwlen hdom hsort hYs hws
  have hpos := sepFold_pos mu (rowList lam) (unitDisp lam.length)
    hdom hne hsort hYs hwstrict hwlen
  rw [Nat.zero_mul] at heq
  have heq2 : stdSq (List.zipWith (fun l u => l + u) (rowList lam)
        (unitDisp lam.length))
      = stdSq (List.zipWith (fun l u => l + u) mu
          (unitDisp lam.length))
        + sepFold 0 mu (rowList lam) (unitDisp lam.length) := heq
  rw [display_zip lam, heq2]
  exact Nat.add_lt_add_left hpos _

/-! The top coefficient (`thm:weylchar`'s `c_λ = 1` clause): the
tie's one contributor at the top key is the identity permutation —
`ν ⪯ λ` with `wu ⪯ u` add, the permuted display's prefix cap
against the unit display's forcing `wu = u` alone — read through
the prefix kit and the distinct-family minimum below. -/

private theorem addSwap4' (A x B y : Nat) :
    (A + x) + (B + y) = (A + y) + (x + B) := by
  rw [Nat.add_assoc A x (B + y), Nat.add_assoc A y (x + B),
    Nat.add_left_comm y x B, Nat.add_comm y B]

/-- The dominance walk's prefix read: every prefix of the first
list at or below the slack with the second's. -/
theorem domGo_prefix : ∀ (s : Nat) (X Y : List Nat),
    domGo s X Y = true → ∀ k, prefixAt k X ≤ s + prefixAt k Y
  | _, [], [], _, k => by
    rw [prefixAt_nil k]
    exact Nat.zero_le _
  | _, [], _ :: _, h, _ => Bool.noConfusion h
  | _, _ :: _, [], h, _ => Bool.noConfusion h
  | s, a :: X, b :: Y, h, k => by
    have h' : (if a ≤ s + b then domGo (s + b - a) X Y else false)
        = true := h
    by_cases hab : a ≤ s + b
    · rw [if_pos hab] at h'
      match k with
      | 0 =>
        rw [prefixAt_zero, prefixAt_zero]
        exact Nat.zero_le _
      | k + 1 =>
        show a + prefixAt k X ≤ s + (b + prefixAt k Y)
        have h2 : a + prefixAt k X
            ≤ a + ((s + b - a) + prefixAt k Y) :=
          Nat.add_le_add_left (domGo_prefix (s + b - a) X Y h' k) a
        rw [← Nat.add_assoc, Nat.add_comm a (s + b - a),
          subAdd hab, Nat.add_assoc] at h2
        exact h2
    · rw [if_neg hab] at h'
      exact Bool.noConfusion h'

private theorem tiePrefix : ∀ (y z m : List Nat),
    tieGap y z = some m → ∀ k,
    prefixAt k m + prefixAt k z = prefixAt k y :=
  fun y z m h k => by
    obtain ⟨hml, hzl, hent⟩ := tieGap_reads y z m h
    rw [ground.getAt_ext 0 y (List.zipWith (fun l u => l + u) m z)
        (ground.length_zipWith (fun l u => l + u) m z y.length hml hzl).symm
        (fun i hi => ((ground.getAt_zipWith 0 0 0 (fun l u => l + u) m z i
            (by rw [hml]; exact hi) (by rw [hzl]; exact hi)).trans
          (hent i hi)).symm),
      ground.prefixAt_zipAdd m z (hml.trans hzl.symm) k]

/-! The distinct-family minimum: a distinct list of naturals below
a stated bound sums at or beyond the triangle of its length — the
top value withdrawn per step, the length capped by the bound. -/

private def sumTop : Nat → Nat → Nat
  | _, 0 => 0
  | 0, _ + 1 => 0
  | d + 1, m + 1 => d + sumTop d m

private theorem sumNat_eraseFirst : ∀ (l : List Nat) (x : Nat),
    0 < ground.countOf x l →
    x + sumNat (ground.eraseFirst x l) = sumNat l
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | b :: t, x, h => by
    show x + sumNat (if x = b then t else b :: ground.eraseFirst x t)
      = b + sumNat t
    by_cases hxb : x = b
    · rw [if_pos hxb, hxb]
    · have h' : 0 < ground.countOf x t := by
        rw [← ground.countOf_head_ne hxb t]
        exact h
      rw [if_neg hxb]
      show x + (b + sumNat (ground.eraseFirst x t)) = b + sumNat t
      rw [Nat.add_left_comm, sumNat_eraseFirst t x h']

private theorem boundTight {l : List Nat} {D : Nat}
    (hval : ∀ x, 0 < ground.countOf x l → x < D + 1)
    (hz : ground.countOf D l = 0) :
    ∀ x, 0 < ground.countOf x l → x < D := fun x hx =>
  Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hval x hx)) (fun he => by
    rw [he, hz] at hx
    exact absurd hx (Nat.lt_irrefl 0))

private theorem eraseKit {l : List Nat} {D : Nat}
    (hdist : ∀ x, ground.countOf x l ≤ 1)
    (hval : ∀ x, 0 < ground.countOf x l → x < D + 1)
    (hocc : 0 < ground.countOf D l) :
    (∀ x, ground.countOf x (ground.eraseFirst D l) ≤ 1)
      ∧ (∀ x, 0 < ground.countOf x (ground.eraseFirst D l) →
          x < D) := by
  have hDz : ground.countOf D (ground.eraseFirst D l) = 0 := by
    have h1 := ground.countOf_eraseFirst_self l D hocc
    have h2 := hdist D
    rw [h1] at h2
    exact Nat.le_antisymm (Nat.le_of_succ_le_succ h2) (Nat.zero_le _)
  constructor
  · intro x
    by_cases hx : x = D
    · rw [hx, hDz]
      exact Nat.zero_le 1
    · rw [ground.countOf_eraseFirst_ne l D x hx]
      exact hdist x
  · intro x hx
    by_cases hxD : x = D
    · rw [hxD, hDz] at hx
      exact absurd hx (Nat.lt_irrefl 0)
    · rw [ground.countOf_eraseFirst_ne l D x hxD] at hx
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hval x hx)) hxD

private theorem lenCap : ∀ (D : Nat) (l : List Nat),
    (∀ x, ground.countOf x l ≤ 1) →
    (∀ x, 0 < ground.countOf x l → x < D) → l.length ≤ D
  | 0, l, _, hval => by
    rw [ground.eq_nil_of_countOf l (fun x =>
      match Nat.eq_zero_or_pos (ground.countOf x l) with
      | .inl h => h
      | .inr h => absurd (hval x h) (Nat.not_lt_zero x))]
    exact Nat.le_refl 0
  | D + 1, l, hdist, hval =>
    match Nat.eq_zero_or_pos (ground.countOf D l) with
    | .inl hz =>
      Nat.le_trans (lenCap D l hdist (boundTight hval hz))
        (Nat.le_succ D)
    | .inr hocc => by
      have hkit := eraseKit hdist hval hocc
      rw [← ground.length_eraseFirst D l hocc]
      exact Nat.succ_le_succ
        (lenCap D (ground.eraseFirst D l) hkit.1 hkit.2)

private theorem minSumB : ∀ (D : Nat) (l : List Nat),
    (∀ x, ground.countOf x l ≤ 1) →
    (∀ x, 0 < ground.countOf x l → x < D) →
    sumTop l.length l.length ≤ sumNat l
  | 0, l, _, hval => by
    rw [ground.eq_nil_of_countOf l (fun x =>
      match Nat.eq_zero_or_pos (ground.countOf x l) with
      | .inl h => h
      | .inr h => absurd (hval x h) (Nat.not_lt_zero x))]
    exact Nat.le_refl 0
  | D + 1, l, hdist, hval =>
    match Nat.eq_zero_or_pos (ground.countOf D l) with
    | .inl hz => minSumB D l hdist (boundTight hval hz)
    | .inr hocc => by
      have hkit := eraseKit hdist hval hocc
      rw [← ground.length_eraseFirst D l hocc, ← sumNat_eraseFirst l D hocc]
      show (ground.eraseFirst D l).length
          + sumTop (ground.eraseFirst D l).length
            (ground.eraseFirst D l).length
        ≤ D + sumNat (ground.eraseFirst D l)
      exact Nat.add_le_add
        (lenCap D (ground.eraseFirst D l) hkit.1 hkit.2)
        (minSumB D (ground.eraseFirst D l) hkit.1 hkit.2)

private theorem prefixAt_take : ∀ (k : Nat) (l : List Nat),
    prefixAt k l = sumNat (l.take k)
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | k + 1, a :: t => by
    show a + prefixAt k t = a + sumNat (t.take k)
    rw [prefixAt_take k t]

private theorem prefixExpo {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    ∀ k, k ≤ d →
      prefixAt k (expo (unitDisp d) p) + prefixAt k p = k * d
  | 0, _ => by
    rw [prefixAt_zero, prefixAt_zero, Nat.zero_mul]
  | k + 1, hk => by
    obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
    have hkd : k < d := Nat.lt_of_succ_le hk
    have hkp : k < p.length := by rw [hplen]; exact hkd
    have hkpu : k < (expo (unitDisp d) p).length := by
      show k < (p.map (ground.getAt 0 (unitDisp d))).length
      rw [ground.length_map, hplen]
      exact hkd
    have hpk : ground.getAt 0 p k < d :=
      hpval _ (countOf_getAt_pos 0 p k hkp)
    have hent : ground.getAt 0 (expo (unitDisp d) p) k
        = d - ground.getAt 0 p k := by
      show ground.getAt 0 (p.map (ground.getAt 0 (unitDisp d))) k = _
      rw [ground.getAt_map 0 0 _ p k hkp, getAt_unitDisp d _ hpk]
    rw [prefixAt_succ _ k hkpu, prefixAt_succ p k hkp, hent,
      Nat.add_add_add_comm, prefixExpo hp k (Nat.le_of_succ_le hk),
      subAdd (Nat.le_of_lt hpk), Nat.succ_mul]

private theorem prefixUnit (d : Nat) :
    ∀ k, k ≤ d → prefixAt k (unitDisp d) + sumTop k k = k * d
  | 0, _ => by
    rw [prefixAt_zero, Nat.zero_mul]
    rfl
  | k + 1, hk => by
    have hkd : k < d := Nat.lt_of_succ_le hk
    have hku : k < (unitDisp d).length := by
      rw [length_unitDisp]
      exact hkd
    rw [prefixAt_succ _ k hku, getAt_unitDisp d k hkd]
    show (prefixAt k (unitDisp d) + (d - k)) + (k + sumTop k k)
      = (k + 1) * d
    rw [addSwap4' (prefixAt k (unitDisp d)) (d - k) k (sumTop k k),
      prefixUnit d k (Nat.le_of_succ_le hk),
      subAdd (Nat.le_of_lt hkd), Nat.succ_mul]

private theorem prefixTri {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) (k : Nat) (hk : k ≤ d) :
    sumTop k k ≤ prefixAt k p := by
  obtain ⟨hplen, hpdist, hpval, _⟩ := perm_member_reads hp
  rw [prefixAt_take k p]
  have hlen : (p.take k).length = k :=
    length_take k p (by rw [hplen]; exact hk)
  have hmin := minSumB d (p.take k)
    (fun x => Nat.le_trans (countOf_take x k p) (hpdist x))
    (fun x hx => hpval x
      (Nat.lt_of_lt_of_le hx (countOf_take x k p)))
  rw [hlen] at hmin
  exact hmin

private theorem perm_eq_range {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d))
    (hle : ∀ k, k ≤ d →
      prefixAt k (unitDisp d) ≤ prefixAt k (expo (unitDisp d) p)) :
    p = List.range d := by
  obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
  have hpeq : ∀ k, k ≤ d → prefixAt k p = sumTop k k := fun k hk => by
    have h4 : prefixAt k (unitDisp d) + prefixAt k p
        ≤ prefixAt k (unitDisp d) + sumTop k k := by
      rw [prefixUnit d k hk, ← prefixExpo hp k hk]
      exact Nat.add_le_add_right (hle k hk) _
    exact Nat.le_antisymm (leCancelL _ h4) (prefixTri hp k hk)
  have hpueq : ∀ k, k ≤ d →
      prefixAt k (expo (unitDisp d) p) = prefixAt k (unitDisp d) :=
    fun k hk => by
      refine addCancelR (sumTop k k) ?_
      rw [prefixUnit d k hk, ← hpeq k hk]
      exact prefixExpo hp k hk
  refine ground.getAt_ext 0 p (List.range d)
    (by rw [hplen, length_range]) ?_
  intro j hj
  have hjd : j < d := by rw [← hplen]; exact hj
  rw [getAt_range d j hjd]
  have hjpu : j < (expo (unitDisp d) p).length := by
    show j < (p.map (ground.getAt 0 (unitDisp d))).length
    rw [ground.length_map]
    exact hj
  have hpj : ground.getAt 0 p j < d :=
    hpval _ (countOf_getAt_pos 0 p j hj)
  have hstep : prefixAt j (expo (unitDisp d) p)
        + ground.getAt 0 (expo (unitDisp d) p) j
      = prefixAt j (unitDisp d) + ground.getAt 0 (unitDisp d) j := by
    rw [← prefixAt_succ _ j hjpu,
      ← prefixAt_succ (unitDisp d) j (by rw [length_unitDisp]; exact hjd),
      hpueq (j + 1) (Nat.succ_le_of_lt hjd)]
  rw [hpueq j (Nat.le_of_lt hjd)] at hstep
  have hgeq := addCancelL _ hstep
  have hent : ground.getAt 0 (expo (unitDisp d) p) j
      = d - ground.getAt 0 p j := by
    show ground.getAt 0 (p.map (ground.getAt 0 (unitDisp d))) j = _
    rw [ground.getAt_map 0 0 _ p j hj, getAt_unitDisp d _ hpj]
  rw [hent, getAt_unitDisp d j hjd] at hgeq
  exact ground.subInj (Nat.le_of_lt hpj) (Nat.le_of_lt hjd) hgeq

private theorem multAtGap_off_top {lam : Shape}
    {mult : List Nat → Nat} (hsupp : supportReadE lam mult)
    {p : List Nat}
    (hp : 0 < ground.countOf p (perms lam.length))
    (hne : p ≠ List.range lam.length) :
    multAtGap mult (display lam) (expo (unitDisp lam.length) p)
      = 0 := by
  show (match tieGap (display lam) (expo (unitDisp lam.length) p)
      with
    | some nu => mult nu
    | none => 0) = 0
  cases htie : tieGap (display lam) (expo (unitDisp lam.length) p)
    with
  | none => rfl
  | some nu =>
    show mult nu = 0
    match Nat.eq_zero_or_pos (mult nu) with
    | .inl hz => exact hz
    | .inr hpos =>
      obtain ⟨hnl, _, _⟩ := tieGap_reads _ _ nu htie
      have hnlen : nu.length = lam.length := by
        rw [hnl, length_display]
      have hdom : domBy nu (rowList lam) := hsupp nu hnlen hpos
      have hle : ∀ k, k ≤ lam.length →
          prefixAt k (unitDisp lam.length)
            ≤ prefixAt k (expo (unitDisp lam.length) p) := by
        intro k hk
        have htp := tiePrefix _ _ _ htie k
        have hdz : prefixAt k (display lam)
            = prefixAt k (rowList lam)
              + prefixAt k (unitDisp lam.length) := by
          rw [display_zip lam]
          exact ground.prefixAt_zipAdd _ _
            (by rw [length_rowList, length_unitDisp]) k
        have hdp := domGo_prefix 0 nu (rowList lam) hdom k
        rw [Nat.zero_add] at hdp
        rw [hdz] at htp
        have h6 : prefixAt k (rowList lam)
              + prefixAt k (unitDisp lam.length)
            ≤ prefixAt k (rowList lam)
              + prefixAt k (expo (unitDisp lam.length) p) := by
          rw [← htp]
          exact Nat.add_le_add_right hdp _
        exact leCancelL _ h6
      exact absurd (perm_eq_range hp hle) hne

/-- The top coefficient: at the support and top clauses the
product's coefficient at the top key reads one on the even side
and the count's unit on the odd — the tie's one contributor the
identity permutation, every further permutation priced off the
dominance walk by the permuted display's prefix cap against the
unit display's (`thm:weylchar`'s `c_λ = 1`, the top content on one
line against `wu = u` alone). -/
private theorem prodCount_top (lam : Shape) (mult : List Nat → Nat)
    (hsupp : supportReadE lam mult) (htop : topReadE lam mult) :
    prodCount mult lam.length (display lam) false = 1
      ∧ prodCount mult lam.length (display lam) true = 0 := by
  have htie : tieGap (display lam) (unitDisp lam.length)
      = some (rowList lam) :=
    tieGap_make (display lam) (unitDisp lam.length) (rowList lam)
      (by rw [length_rowList, length_display])
      (by rw [length_unitDisp, length_display])
      (fun i hi => by
        rw [length_display] at hi
        rw [getAt_display lam i hi, getAt_unitDisp lam.length i hi])
  constructor
  · show ground.famFold Nat.add 0
        (fun p => if parity p = false then
          multAtGap mult (display lam)
            (expo (unitDisp lam.length) p) else 0)
        (perms lam.length) = 1
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun p => if List.range lam.length = p then (1 : Nat) else 0)
        (perms lam.length) (fun p hp => by
          by_cases hpr : List.range lam.length = p
          · have hpar : parity p = false := by
              rw [← hpr]
              exact parity_range lam.length
            have hexpo : expo (unitDisp lam.length) p
                = unitDisp lam.length := by
              rw [← hpr]
              exact range_map_getAt 0 lam.length (unitDisp lam.length)
                (length_unitDisp lam.length)
            rw [if_pos hpar, if_pos hpr, hexpo]
            show (match tieGap (display lam) (unitDisp lam.length)
                with
              | some nu => mult nu
              | none => 0) = 1
            rw [htie]
            exact htop
          · rw [if_neg hpr]
            by_cases hpar : parity p = false
            · rw [if_pos hpar]
              exact multAtGap_off_top hsupp hp
                (fun he => hpr he.symm)
            · rw [if_neg hpar]),
      ← countOf_fold (List.range lam.length) (perms lam.length),
      countRangePerms lam.length]
  · show ground.famFold Nat.add 0
        (fun p => if parity p = true then
          multAtGap mult (display lam)
            (expo (unitDisp lam.length) p) else 0)
        (perms lam.length) = 0
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun _ => (0 : Nat)) (perms lam.length) (fun p hp => by
          by_cases hpr : List.range lam.length = p
          · have hpar : parity p = false := by
              rw [← hpr]
              exact parity_range lam.length
            rw [hpar]
            rw [if_neg (fun hc : false = true => Bool.noConfusion hc)]
          · by_cases hpar : parity p = true
            · rw [if_pos hpar]
              exact multAtGap_off_top hsupp hp
                (fun he => hpr he.symm)
            · rw [if_neg hpar]),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
        (perms lam.length)]

/-! The eigen-read's statement and the telescope's per-key read
(`thm:weylchar`'s generating telescope): `⟨x_a : x_b⟩ G_ab
= x_b ⟨D_a ch : D_b ch⟩` coefficientwise — one further move drops
one shift, so the pair's moved folds at the two bumped contents
differ by the dropped move's own read — with the edit kit beneath
it, the entry rewrites at distinct keys commuting and fusing. -/

/-- The eigen-read at a key, `𝓛₀(a_u ch) = q(λ+u)(a_u ch)`
coefficientwise: the standard squares of the key and the top
display weigh the product's two coefficients to one value — the
occupied coefficients sit on the `q`-sphere. -/
def eigenAt (mult : List Nat → Nat) (lam : Shape)
    (y : List Nat) : Prop :=
  stdSq y * prodCount mult lam.length y false
      + stdSq (display lam) * prodCount mult lam.length y true
    = stdSq (display lam) * prodCount mult lam.length y false
      + stdSq y * prodCount mult lam.length y true

instance (mult : List Nat → Nat) (lam : Shape) (y : List Nat) :
    Decidable (eigenAt mult lam y) :=
  inferInstanceAs (Decidable (_ = _))

private theorem bumpAt_editAt : ∀ (k : Nat) (l : List Nat),
    ground.bumpAt k l = ground.editAt (fun x => x + 1) k l :=
  fun _ _ => rfl

private theorem moveBy_zero (a b : Nat) (x : List Nat) :
    moveBy a b 0 x = x := by
  show ground.editAt (fun v => v + 0) a (ground.editAt (fun v => v - 0) b x) = x
  rw [ground.editAt_congr (fun v => v + 0) (fun v => v) (fun _ => rfl) a
      (ground.editAt (fun v => v - 0) b x),
    ground.editAt_congr (fun v => v - 0) (fun v => v) (fun _ => rfl) b x,
    ground.editAt_id, ground.editAt_id]

private theorem moveTarget (a b : Nat) (hab : a ≠ b) (l : Nat)
    (w : List Nat) :
    moveBy a b (l + 1) (ground.bumpAt b w)
      = moveBy a b l (ground.bumpAt a w) := by
  show ground.editAt (fun x => x + (l + 1)) a
      (ground.editAt (fun x => x - (l + 1)) b (ground.bumpAt b w))
    = ground.editAt (fun x => x + l) a
      (ground.editAt (fun x => x - l) b (ground.bumpAt a w))
  rw [bumpAt_editAt b w, bumpAt_editAt a w,
    ground.editAt_fuse (fun x => x - (l + 1)) (fun x => x + 1) b w,
    ground.editAt_congr (fun x => x + 1 - (l + 1)) (fun x => x - l)
      (fun x => Nat.succ_sub_succ x l) b w,
    ground.editAt_comm (fun x => x - l) (fun x => x + 1) b a w
      (fun he => hab he.symm),
    ground.editAt_fuse (fun x => x + l) (fun x => x + 1) a
      (ground.editAt (fun x => x - l) b w),
    ground.editAt_congr (fun x => x + 1 + l) (fun x => x + (l + 1))
      (fun x => by rw [Nat.add_assoc x 1 l, Nat.add_comm 1 l]) a
      (ground.editAt (fun x => x - l) b w)]

private theorem foldShift (F : Nat → Nat) (n : Nat) :
    ground.famFold Nat.add 0 F
        ((List.range (n + 1)).map (fun l => l + 1))
      = F 1 + ground.famFold Nat.add 0 (fun l => F (l + 1))
          ((List.range n).map (fun l => l + 1)) := by
  rw [range_cons n]
  show Nat.add (F (0 + 1)) (ground.famFold Nat.add 0 F
      (((List.range n).map (fun j => j + 1)).map (fun l => l + 1)))
    = F 1 + ground.famFold Nat.add 0 (fun l => F (l + 1))
        ((List.range n).map (fun l => l + 1))
  rw [ground.map_map (fun j => j + 1) (fun l => l + 1)
      (List.range n),
    ground.famFold_map Nat.add 0 F (fun x => x + 1 + 1)
      (List.range n),
    ground.famFold_map Nat.add 0 (fun l => F (l + 1))
      (fun l => l + 1) (List.range n)]
  rfl

private theorem stepCoeff (x y l : Nat) :
    (x + 2 * (l + 1)) + y = (x + 1 + 2 * l) + (y + 1) := by
  rw [Nat.mul_succ 2 l]
  have hL : (x + (2 * l + 2)) + y = (x + 2 * l) + (y + 2) := by
    rw [← Nat.add_assoc x (2 * l) 2,
      Nat.add_assoc (x + 2 * l) 2 y, Nat.add_comm 2 y]
  have hR : (x + 1 + 2 * l) + (y + 1) = (x + 2 * l) + (y + 2) := by
    rw [Nat.add_assoc x 1 (2 * l), Nat.add_comm 1 (2 * l),
      ← Nat.add_assoc x (2 * l) 1,
      Nat.add_assoc (x + 2 * l) 1 (y + 1),
      Nat.add_comm 1 (y + 1)]
  rw [hL, hR]

private theorem headCoeff (x y : Nat) :
    (x + 2 * 1) + y = (y + 1) + (x + 1) := by
  have hL : (x + 2 * 1) + y = (x + y) + 2 := by
    rw [Nat.add_assoc x (2 * 1) y, Nat.add_comm (2 * 1) y,
      ← Nat.add_assoc x y (2 * 1)]
  have hR : (y + 1) + (x + 1) = (x + y) + 2 := by
    rw [Nat.add_assoc y 1 (x + 1), Nat.add_comm 1 (x + 1),
      ← Nat.add_assoc y (x + 1) 1, ← Nat.add_assoc y x 1,
      Nat.add_comm y x, Nat.add_assoc (x + y) 1 1]
  rw [hL, hR]

/-- The telescope's per-key read: at a letter pair over a base
content, the pair's moved folds at the second letter's bump against
the first's differ by the dropped move's read —
`⟨x_a : x_b⟩ G_ab = x_b ⟨D_a ch : D_b ch⟩` at the key, one value of
the balance pairs (`thm:weylchar`'s telescope, one further move
dropping one shift). -/
theorem stepRead (mult : List Nat → Nat) (w : List Nat)
    {a b : Nat} (hab : a < b) (hb : b < w.length) :
    gFst mult (ground.bumpAt b w) a b
        + gSnd mult (ground.bumpAt a w) a b
        + ground.getAt 0 w b * mult (ground.bumpAt a w)
      = gFst mult (ground.bumpAt a w) a b
        + gSnd mult (ground.bumpAt b w) a b
        + (ground.getAt 0 w a + 1) * mult (ground.bumpAt a w) := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have ha : a < w.length := Nat.lt_trans hab hb
  have hva : ground.getAt 0 (ground.bumpAt b w) a
      = ground.getAt 0 w a := by
    exact ground.getAt_bumpAt_ne b w a hne
  have hvb : ground.getAt 0 (ground.bumpAt b w) b
      = ground.getAt 0 w b + 1 := by
    exact ground.getAt_bumpAt_self b w hb
  have hma : ground.getAt 0 (ground.bumpAt a w) a
      = ground.getAt 0 w a + 1 := by
    exact ground.getAt_bumpAt_self a w ha
  have hmb : ground.getAt 0 (ground.bumpAt a w) b
      = ground.getAt 0 w b := by
    exact ground.getAt_bumpAt_ne a w b
      (fun he => hne he.symm)
  have hm1 : moveBy a b 1 (ground.bumpAt b w)
      = ground.bumpAt a w := by
    have h := moveTarget a b hne 0 w
    rw [moveBy_zero] at h
    exact h
  have hgfv : gFst mult (ground.bumpAt b w) a b
      = (ground.getAt 0 w a + 2 * 1) * mult (ground.bumpAt a w)
        + ground.famFold Nat.add 0
          (fun l => (ground.getAt 0 w a + 2 * (l + 1))
            * mult (moveBy a b l (ground.bumpAt a w)))
          ((List.range (ground.getAt 0 w b)).map
            (fun l => l + 1)) := by
    show ground.famFold Nat.add 0
        (fun l => (ground.getAt 0 (ground.bumpAt b w) a + 2 * l)
          * mult (moveBy a b l (ground.bumpAt b w)))
        ((List.range (ground.getAt 0 (ground.bumpAt b w) b)).map
          (fun l => l + 1)) = _
    rw [hva, hvb,
      foldShift (fun l => (ground.getAt 0 w a + 2 * l)
        * mult (moveBy a b l (ground.bumpAt b w)))
        (ground.getAt 0 w b),
      hm1,
      ground.famFold_congr_all Nat.add 0 _
        (fun l => (ground.getAt 0 w a + 2 * (l + 1))
          * mult (moveBy a b l (ground.bumpAt a w)))
        (fun l => by rw [moveTarget a b hne l w]) _]
  have hgsv : gSnd mult (ground.bumpAt b w) a b
      = (ground.getAt 0 w b + 1) * mult (ground.bumpAt a w)
        + ground.famFold Nat.add 0
          (fun l => (ground.getAt 0 w b + 1)
            * mult (moveBy a b l (ground.bumpAt a w)))
          ((List.range (ground.getAt 0 w b)).map
            (fun l => l + 1)) := by
    show ground.famFold Nat.add 0
        (fun l => ground.getAt 0 (ground.bumpAt b w) b
          * mult (moveBy a b l (ground.bumpAt b w)))
        ((List.range (ground.getAt 0 (ground.bumpAt b w) b)).map
          (fun l => l + 1)) = _
    rw [hvb,
      foldShift (fun l => (ground.getAt 0 w b + 1)
        * mult (moveBy a b l (ground.bumpAt b w)))
        (ground.getAt 0 w b),
      hm1,
      ground.famFold_congr_all Nat.add 0 _
        (fun l => (ground.getAt 0 w b + 1)
          * mult (moveBy a b l (ground.bumpAt a w)))
        (fun l => by rw [moveTarget a b hne l w]) _]
  have hgfm : gFst mult (ground.bumpAt a w) a b
      = ground.famFold Nat.add 0
          (fun l => (ground.getAt 0 w a + 1 + 2 * l)
            * mult (moveBy a b l (ground.bumpAt a w)))
          ((List.range (ground.getAt 0 w b)).map
            (fun l => l + 1)) := by
    show ground.famFold Nat.add 0
        (fun l => (ground.getAt 0 (ground.bumpAt a w) a + 2 * l)
          * mult (moveBy a b l (ground.bumpAt a w)))
        ((List.range (ground.getAt 0 (ground.bumpAt a w) b)).map
          (fun l => l + 1)) = _
    rw [hma, hmb]
  have hgsm : gSnd mult (ground.bumpAt a w) a b
      = ground.famFold Nat.add 0
          (fun l => ground.getAt 0 w b
            * mult (moveBy a b l (ground.bumpAt a w)))
          ((List.range (ground.getAt 0 w b)).map
            (fun l => l + 1)) := by
    show ground.famFold Nat.add 0
        (fun l => ground.getAt 0 (ground.bumpAt a w) b
          * mult (moveBy a b l (ground.bumpAt a w)))
        ((List.range (ground.getAt 0 (ground.bumpAt a w) b)).map
          (fun l => l + 1)) = _
    rw [hmb]
  rw [hgfv, hgsv, hgfm, hgsm,
    ground.addExch4 ((ground.getAt 0 w a + 2 * 1) * mult (ground.bumpAt a w))
      (ground.famFold Nat.add 0
        (fun l => (ground.getAt 0 w a + 2 * (l + 1))
          * mult (moveBy a b l (ground.bumpAt a w)))
        ((List.range (ground.getAt 0 w b)).map (fun l => l + 1)))
      (ground.famFold Nat.add 0
        (fun l => ground.getAt 0 w b
          * mult (moveBy a b l (ground.bumpAt a w)))
        ((List.range (ground.getAt 0 w b)).map (fun l => l + 1)))
      (ground.getAt 0 w b * mult (ground.bumpAt a w)),
    ← addJoinHeadOut
      ((ground.getAt 0 w b + 1) * mult (ground.bumpAt a w))
      ((ground.getAt 0 w a + 1) * mult (ground.bumpAt a w))
      (ground.famFold Nat.add 0
        (fun l => (ground.getAt 0 w a + 1 + 2 * l)
          * mult (moveBy a b l (ground.bumpAt a w)))
        ((List.range (ground.getAt 0 w b)).map (fun l => l + 1)))
      (ground.famFold Nat.add 0
        (fun l => (ground.getAt 0 w b + 1)
          * mult (moveBy a b l (ground.bumpAt a w)))
        ((List.range (ground.getAt 0 w b)).map (fun l => l + 1))),
    ← famFold_add_split, ← famFold_add_split,
    ← ground.mulAddR (ground.getAt 0 w a + 2 * 1) (ground.getAt 0 w b)
      (mult (ground.bumpAt a w)),
    ← ground.mulAddR (ground.getAt 0 w b + 1) (ground.getAt 0 w a + 1)
      (mult (ground.bumpAt a w)),
    headCoeff (ground.getAt 0 w a) (ground.getAt 0 w b),
    ground.famFold_congr_all Nat.add 0
      (fun l => (ground.getAt 0 w a + 2 * (l + 1))
          * mult (moveBy a b l (ground.bumpAt a w))
        + ground.getAt 0 w b
          * mult (moveBy a b l (ground.bumpAt a w)))
      (fun l => (ground.getAt 0 w a + 1 + 2 * l)
          * mult (moveBy a b l (ground.bumpAt a w))
        + (ground.getAt 0 w b + 1)
          * mult (moveBy a b l (ground.bumpAt a w)))
      (fun l => by
        rw [← ground.mulAddR (ground.getAt 0 w a + 2 * (l + 1))
            (ground.getAt 0 w b)
            (mult (moveBy a b l (ground.bumpAt a w))),
          ← ground.mulAddR (ground.getAt 0 w a + 1 + 2 * l)
            (ground.getAt 0 w b + 1)
            (mult (moveBy a b l (ground.bumpAt a w))),
          stepCoeff (ground.getAt 0 w a) (ground.getAt 0 w b) l])
      ((List.range (ground.getAt 0 w b)).map (fun l => l + 1))]

/-! The boundary read (`thm:weylchar`'s telescope at a key reading
the first letter at the count's unit): the one-sided string's
palindrome — the symmetry pairs the string's targets, two shifts at
the join `l + l' = ν_b` reading one multiplicity, so the moved
weights collect to the second exponent's count,
`Σ_{l≥1} 2l·mult(ν^{(l)}) = ν_b Σ_{l≥0} mult(ν^{(l)})`. -/

/-- The pair move keeps the content's width: the two letters are
edited in place, no letter joined or dropped. -/
theorem length_moveBy (a b l : Nat) (nu : List Nat) :
    (moveBy a b l nu).length = nu.length := by
  show (ground.editAt (fun x => x + l) a
      (ground.editAt (fun x => x - l) b nu)).length = _
  rw [ground.length_editAt, ground.length_editAt]

/-- The pair move's first letter reads its own count raised by the
shift. -/
theorem getAt_moveBy_fst {a b : Nat} (hne : a ≠ b)
    (l : Nat) (nu : List Nat) (ha : a < nu.length) :
    ground.getAt 0 (moveBy a b l nu) a = ground.getAt 0 nu a + l := by
  show ground.getAt 0 (ground.editAt (fun x => x + l) a
      (ground.editAt (fun x => x - l) b nu)) a = _
  rw [ground.getAt_editAt_self (fun x => x + l) a _
      (by rw [ground.length_editAt]; exact ha),
    ground.getAt_editAt_ne (fun x => x - l) b a nu hne]

/-- The pair move's second letter reads its own count lowered by the
shift, the truncated read at the count's floor. -/
theorem getAt_moveBy_snd (a : Nat) {b : Nat} (hne : a ≠ b)
    (l : Nat) (nu : List Nat) (hb : b < nu.length) :
    ground.getAt 0 (moveBy a b l nu) b = ground.getAt 0 nu b - l := by
  show ground.getAt 0 (ground.editAt (fun x => x + l) a
      (ground.editAt (fun x => x - l) b nu)) b = _
  rw [ground.getAt_editAt_ne (fun x => x + l) a b _
      (fun he => hne he.symm),
    ground.getAt_editAt_self (fun x => x - l) b nu hb]

/-- Every further letter is kept by the pair move. -/
theorem getAt_moveBy_ne (a b l : Nat) (nu : List Nat)
    {t : Nat} (hta : t ≠ a) (htb : t ≠ b) :
    ground.getAt 0 (moveBy a b l nu) t = ground.getAt 0 nu t := by
  show ground.getAt 0 (ground.editAt (fun x => x + l) a
      (ground.editAt (fun x => x - l) b nu)) t = _
  rw [ground.getAt_editAt_ne (fun x => x + l) a t _ hta,
    ground.getAt_editAt_ne (fun x => x - l) b t nu htb]

/-- The reflection of a moved content at a first letter reading the
count's unit: the letters' transposition reads the string's shift
to its join partner, `l + l' = ν_b`. -/
private theorem moveSym {a b : Nat} (hab : a < b) (nu : List Nat)
    (hb : b < nu.length) (hav : ground.getAt 0 nu a = 0)
    {k : Nat} (hk : k ≤ ground.getAt 0 nu b) :
    swapPair a b (moveBy a b k nu)
      = moveBy a b (ground.getAt 0 nu b - k) nu := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have ha : a < nu.length := Nat.lt_trans hab hb
  have hma : a < (moveBy a b k nu).length := by
    rw [length_moveBy]
    exact ha
  have hmb : b < (moveBy a b k nu).length := by
    rw [length_moveBy]
    exact hb
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [length_swapPair, length_moveBy, length_moveBy]
  · intro t ht
    rw [length_swapPair, length_moveBy] at ht
    by_cases hta : t = a
    · rw [hta, getAt_swapPair_fst (moveBy a b k nu) hne hma hmb,
        getAt_moveBy_snd a hne k nu hb,
        getAt_moveBy_fst hne (ground.getAt 0 nu b - k) nu ha, hav,
        Nat.zero_add]
    · by_cases htb : t = b
      · rw [htb, getAt_swapPair_snd (moveBy a b k nu) hne hma hmb,
          getAt_moveBy_fst hne k nu ha, hav, Nat.zero_add,
          getAt_moveBy_snd a hne (ground.getAt 0 nu b - k) nu hb,
          natSubSubCancel _ _ hk]
      · rw [getAt_swapPair_ne (moveBy a b k nu) hma hmb hta htb,
          getAt_moveBy_ne a b k nu hta htb,
          getAt_moveBy_ne a b (ground.getAt 0 nu b - k) nu hta htb]

private theorem predSubSucc {x n : Nat} (hx : x < n) :
    ((n - 1) - x) + 1 = n - x := by
  match n, hx with
  | n + 1, hx =>
    rw [Nat.succ_sub_succ]
    show (n - 0) - x + 1 = n + 1 - x
    match x, hx with
    | 0, _ => rfl
    | x + 1, hx =>
      rw [Nat.succ_sub_succ]
      exact ground.subSuccAdd (Nat.le_of_lt_succ hx)

private theorem shuffleD (f s1 s2 g b : Nat) :
    (f + (s1 + s2)) + (g + b) = g + ((f + s2) + (s1 + b)) := by
  have hL : (f + (s1 + s2)) + (g + b)
      = f + (s1 + (s2 + (g + b))) := by
    rw [Nat.add_assoc f (s1 + s2) (g + b),
      Nat.add_assoc s1 s2 (g + b)]
  have hR : g + ((f + s2) + (s1 + b))
      = f + (s1 + (s2 + (g + b))) := by
    rw [Nat.add_assoc f s2 (s1 + b),
      Nat.add_left_comm g f (s2 + (s1 + b)),
      Nat.add_left_comm g s2 (s1 + b),
      Nat.add_left_comm g s1 b,
      Nat.add_left_comm s2 s1 (g + b)]
  rw [hL, hR]

/-- The palindrome's collected fold, the pure telescope: the
shift-weighted sum against its reflection reads the count's
constant weight, `Σ_j (j+1)F(j+1) + Σ_j (n−j)F(j)
= n·F(0) + Σ_j n·F(j+1)` over the range. -/
private theorem palinTele : ∀ (n : Nat) (F : Nat → Nat),
    ground.famFold Nat.add 0 (fun j => (j + 1) * F (j + 1))
        (List.range n)
      + ground.famFold Nat.add 0 (fun j => (n - j) * F j)
        (List.range n)
    = n * F 0
      + ground.famFold Nat.add 0 (fun j => n * F (j + 1))
        (List.range n)
  | 0, F => by
    show (0 : Nat) + 0 = 0 * F 0 + 0
    rw [Nat.zero_mul]
  | n + 1, F => by
    rw [range_cons n]
    show ((0 + 1) * F (0 + 1)
        + ground.famFold Nat.add 0 (fun j => (j + 1) * F (j + 1))
          ((List.range n).map (fun j => j + 1)))
      + ((n + 1 - 0) * F 0
        + ground.famFold Nat.add 0 (fun j => (n + 1 - j) * F j)
          ((List.range n).map (fun j => j + 1)))
      = (n + 1) * F 0
        + ((n + 1) * F (0 + 1)
          + ground.famFold Nat.add 0 (fun j => (n + 1) * F (j + 1))
            ((List.range n).map (fun j => j + 1)))
    rw [ground.famFold_map Nat.add 0
        (fun j => (j + 1) * F (j + 1)) (fun j => j + 1)
        (List.range n),
      ground.famFold_map Nat.add 0
        (fun j => (n + 1 - j) * F j) (fun j => j + 1)
        (List.range n),
      ground.famFold_map Nat.add 0
        (fun j => (n + 1) * F (j + 1)) (fun j => j + 1)
        (List.range n)]
    have hsplit : ground.famFold Nat.add 0
        (fun j => (j + 1 + 1) * F (j + 1 + 1)) (List.range n)
        = ground.famFold Nat.add 0
            (fun j => (j + 1) * F (j + 1 + 1)) (List.range n)
          + ground.famFold Nat.add 0
            (fun j => F (j + 1 + 1)) (List.range n) := by
      rw [← famFold_add_split (fun j => (j + 1) * F (j + 1 + 1))
          (fun j => F (j + 1 + 1)) (List.range n)]
      exact ground.famFold_congr_all Nat.add 0 _ _ (fun j => by
        rw [ground.mulAddR (j + 1) 1 (F (j + 1 + 1)), Nat.one_mul]) _
    have hsub : ground.famFold Nat.add 0
        (fun j => (n + 1 - (j + 1)) * F (j + 1)) (List.range n)
        = ground.famFold Nat.add 0
            (fun j => (n - j) * F (j + 1)) (List.range n) :=
      ground.famFold_congr_all Nat.add 0 _ _ (fun j => by
        rw [Nat.succ_sub_succ]) _
    have hIH := palinTele n (fun k => F (k + 1))
    have hmerge : ground.famFold Nat.add 0
          (fun j => n * F (j + 1 + 1)) (List.range n)
        + ground.famFold Nat.add 0
          (fun j => F (j + 1 + 1)) (List.range n)
        = ground.famFold Nat.add 0
          (fun j => (n + 1) * F (j + 1 + 1)) (List.range n) := by
      rw [← famFold_add_split (fun j => n * F (j + 1 + 1))
          (fun j => F (j + 1 + 1)) (List.range n)]
      exact ground.famFold_congr_all Nat.add 0 _ _ (fun j => by
        rw [ground.mulAddR n 1 (F (j + 1 + 1)), Nat.one_mul]) _
    have hIH' : ground.famFold Nat.add 0
          (fun j => (j + 1) * F (j + 1 + 1)) (List.range n)
        + ground.famFold Nat.add 0
          (fun j => (n - j) * F (j + 1)) (List.range n)
        = n * F 1
          + ground.famFold Nat.add 0
            (fun j => n * F (j + 1 + 1)) (List.range n) := hIH
    show (1 * F 1
        + ground.famFold Nat.add 0
          (fun j => (j + 1 + 1) * F (j + 1 + 1)) (List.range n))
      + ((n + 1) * F 0
        + ground.famFold Nat.add 0
          (fun j => (n + 1 - (j + 1)) * F (j + 1)) (List.range n))
      = (n + 1) * F 0
        + ((n + 1) * F 1
          + ground.famFold Nat.add 0
            (fun j => (n + 1) * F (j + 1 + 1)) (List.range n))
    rw [hsplit, hsub, Nat.one_mul,
      shuffleD (F 1)
        (ground.famFold Nat.add 0
          (fun j => (j + 1) * F (j + 1 + 1)) (List.range n))
        (ground.famFold Nat.add 0
          (fun j => F (j + 1 + 1)) (List.range n))
        ((n + 1) * F 0)
        (ground.famFold Nat.add 0
          (fun j => (n - j) * F (j + 1)) (List.range n)),
      hIH',
      Nat.add_add_add_comm (F 1)
        (ground.famFold Nat.add 0
          (fun j => F (j + 1 + 1)) (List.range n))
        (n * F 1)
        (ground.famFold Nat.add 0
          (fun j => n * F (j + 1 + 1)) (List.range n)),
      show F 1 + n * F 1 = (n + 1) * F 1 from by
        rw [ground.mulAddR n 1 (F 1), Nat.one_mul, Nat.add_comm],
      Nat.add_comm
        (ground.famFold Nat.add 0
          (fun j => F (j + 1 + 1)) (List.range n))
        (ground.famFold Nat.add 0
          (fun j => n * F (j + 1 + 1)) (List.range n)),
      hmerge]

/-- The boundary read: at a key reading the first letter at the
count's unit, the moved weights collect to the second exponent's
count — `Σ_{l≥1} 2l·mult(ν^{(l)}) = ν_b (mult ν + Σ_{l≥1}
mult(ν^{(l)}))`, the one-sided string's palindrome, the symmetry
pairing the shifts at the join `l + l' = ν_b` (`thm:weylchar`'s
telescope at the boundary keys). -/
theorem boundaryRead (mult : List Nat → Nat) (nu : List Nat)
    {a b : Nat} (hab : a < b) (hb : b < nu.length)
    (hsym : ∀ (i j : Nat) (mu : List Nat), i < j → j < nu.length →
      mu.length = nu.length → mult (swapPair i j mu) = mult mu)
    (hav : ground.getAt 0 nu a = 0) :
    gFst mult nu a b
      = ground.getAt 0 nu b * mult nu + gSnd mult nu a b := by
  have hsymF : ∀ k, k ≤ ground.getAt 0 nu b →
      mult (moveBy a b k nu)
        = mult (moveBy a b (ground.getAt 0 nu b - k) nu) := by
    intro k hk
    have hswap := hsym a b (moveBy a b k nu) hab hb
      (length_moveBy a b k nu)
    rw [moveSym hab nu hb hav hk] at hswap
    exact hswap.symm
  have hmapL : ground.famFold Nat.add 0
      (fun l => (ground.getAt 0 nu a + 2 * l)
        * mult (moveBy a b l nu))
      ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1))
    = ground.famFold Nat.add 0
      (fun j => (j + 1) * mult (moveBy a b (j + 1) nu)
        + (j + 1) * mult (moveBy a b (j + 1) nu))
      (List.range (ground.getAt 0 nu b)) := by
    rw [ground.famFold_map Nat.add 0
      (fun l => (ground.getAt 0 nu a + 2 * l)
        * mult (moveBy a b l nu))
      (fun l => l + 1) (List.range (ground.getAt 0 nu b))]
    exact ground.famFold_congr_all Nat.add 0 _ _ (fun j => by
      show (ground.getAt 0 nu a + 2 * (j + 1))
          * mult (moveBy a b (j + 1) nu)
        = (j + 1) * mult (moveBy a b (j + 1) nu)
          + (j + 1) * mult (moveBy a b (j + 1) nu)
      rw [hav, Nat.zero_add,
        show (2 : Nat) * (j + 1) = (j + 1) + (j + 1) from by
          show ((1 : Nat) + 1) * (j + 1) = (j + 1) + (j + 1)
          rw [ground.mulAddR 1 1 (j + 1), Nat.one_mul],
        ground.mulAddR (j + 1) (j + 1) (mult (moveBy a b (j + 1) nu))]) _
  have hsymStep : ground.famFold Nat.add 0
      (fun j => (j + 1) * mult (moveBy a b (j + 1) nu))
      (List.range (ground.getAt 0 nu b))
    = ground.famFold Nat.add 0
      (fun j => (j + 1)
        * mult (moveBy a b (ground.getAt 0 nu b - (j + 1)) nu))
      (List.range (ground.getAt 0 nu b)) :=
    ground.famFold_congr_members Nat.add 0 _ _ _ (fun j hj => by
      show (j + 1) * mult (moveBy a b (j + 1) nu)
        = (j + 1)
          * mult (moveBy a b (ground.getAt 0 nu b - (j + 1)) nu)
      rw [hsymF (j + 1) (Nat.succ_le_of_lt (ground.ltOfMem hj))])
  have hreindex : ground.famFold Nat.add 0
      (fun j => (j + 1)
        * mult (moveBy a b (ground.getAt 0 nu b - (j + 1)) nu))
      (List.range (ground.getAt 0 nu b))
    = ground.famFold Nat.add 0
      (fun j => (ground.getAt 0 nu b - j)
        * mult (moveBy a b j nu))
      (List.range (ground.getAt 0 nu b)) := by
    rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun j => (j + 1)
        * mult (moveBy a b (ground.getAt 0 nu b - (j + 1)) nu))
      (l := List.range (ground.getAt 0 nu b))
      (g := fun j => (ground.getAt 0 nu b - 1) - j)
      (h := fun j => (ground.getAt 0 nu b - 1) - j)
      (distinctList_range _)
      (fun x hx => ground.natSubSubCancel _ x
        (Nat.le_pred_of_lt (ground.ltOfMem hx)))
      (fun x hx => ground.natSubSubCancel _ x
        (Nat.le_pred_of_lt (ground.ltOfMem hx)))
      (fun x hx => ground.countOf_range_pos (ground.predSubLt (ground.ltOfMem hx)))
      (fun x hx => ground.countOf_range_pos (ground.predSubLt (ground.ltOfMem hx)))]
    exact ground.famFold_congr_members Nat.add 0 _ _ _
      (fun j hj => by
        have hjn : j < ground.getAt 0 nu b := ground.ltOfMem hj
        show ((ground.getAt 0 nu b - 1 - j) + 1)
            * mult (moveBy a b
              (ground.getAt 0 nu b
                - ((ground.getAt 0 nu b - 1 - j) + 1)) nu)
          = (ground.getAt 0 nu b - j) * mult (moveBy a b j nu)
        rw [predSubSucc hjn, natSubSubCancel _ _ (Nat.le_of_lt hjn)])
  calc gFst mult nu a b
      = ground.famFold Nat.add 0
          (fun j => (j + 1) * mult (moveBy a b (j + 1) nu)
            + (j + 1) * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b)) := hmapL
    _ = ground.famFold Nat.add 0
          (fun j => (j + 1) * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b))
        + ground.famFold Nat.add 0
          (fun j => (j + 1) * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b)) :=
        famFold_add_split _ _ (List.range (ground.getAt 0 nu b))
    _ = ground.famFold Nat.add 0
          (fun j => (j + 1) * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b))
        + ground.famFold Nat.add 0
          (fun j => (ground.getAt 0 nu b - j)
            * mult (moveBy a b j nu))
          (List.range (ground.getAt 0 nu b)) :=
        congrArg (fun z => ground.famFold Nat.add 0
          (fun j => (j + 1) * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b)) + z)
          (hsymStep.trans hreindex)
    _ = ground.getAt 0 nu b * mult (moveBy a b 0 nu)
        + ground.famFold Nat.add 0
          (fun j => ground.getAt 0 nu b
            * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b)) :=
        palinTele (ground.getAt 0 nu b)
          (fun k => mult (moveBy a b k nu))
    _ = ground.getAt 0 nu b * mult nu
        + ground.famFold Nat.add 0
          (fun j => ground.getAt 0 nu b
            * mult (moveBy a b (j + 1) nu))
          (List.range (ground.getAt 0 nu b)) := by
        rw [moveBy_zero a b nu]
    _ = ground.getAt 0 nu b * mult nu + gSnd mult nu a b :=
        congrArg (fun z => ground.getAt 0 nu b * mult nu + z)
          (ground.famFold_map Nat.add 0
            (fun l => ground.getAt 0 nu b
              * mult (moveBy a b l nu))
            (fun l => l + 1)
            (List.range (ground.getAt 0 nu b))).symm

/-! The cofactor tier (`thm:weylchar`'s assembly): the cofactor at
`⟨x_a : x_b⟩ Q_ab = V` enters coefficientwise as the division's
back-substitution, the shift fold over the moved displays, and the
cleared telescope at the cofactor reads per display — the guarded
reads at a key against a moved display below, the telescope's
per-key identity `stepAt` over `stepRead` and `boundaryRead`, and
`cofRead`, the shift fold telescoping to the head display's `G`-read
against the far boundary's. -/

/-- The telescope's guarded `G`-read at a key against a display:
the pair's moved fold's member at the tie's content, the count's
unit at an absent tie. -/
def gAtGap (mult : List Nat → Nat) (a b : Nat) (z K : List Nat)
    (side : Bool) : Nat :=
  match tieGap z K with
  | some chi =>
    if side then gSnd mult chi a b else gFst mult chi a b
  | none => 0

/-- The guarded Euler read at a letter: the letter's count against
the multiplicity at the tie's content — `D_c ch`'s coefficient at
the tie, the count's unit at an absent one. -/
def dAtGap (mult : List Nat → Nat) (c : Nat) (z K : List Nat) : Nat :=
  match tieGap z K with
  | some chi => ground.getAt 0 chi c * mult chi
  | none => 0

private theorem gFst_vac (mult : List Nat → Nat) (chi : List Nat)
    (a : Nat) {b : Nat} (hzb : ground.getAt 0 chi b = 0) :
    gFst mult chi a b = 0 := by
  show ground.famFold Nat.add 0
    (fun l =>
      (ground.getAt 0 chi a + 2 * l) * mult (moveBy a b l chi))
    ((List.range (ground.getAt 0 chi b)).map (fun l => l + 1)) = 0
  rw [hzb]
  rfl

private theorem gSnd_vac (mult : List Nat → Nat) (chi : List Nat)
    (a : Nat) {b : Nat} (hzb : ground.getAt 0 chi b = 0) :
    gSnd mult chi a b = 0 := by
  show ground.famFold Nat.add 0
    (fun l => ground.getAt 0 chi b * mult (moveBy a b l chi))
    ((List.range (ground.getAt 0 chi b)).map (fun l => l + 1)) = 0
  rw [hzb]
  rfl

/-- The tie at a dominated display: matched lengths with every
entry at or below name the componentwise gap as the tie's
solution. -/
private theorem tieGap_of_le : ∀ (y z : List Nat),
    z.length = y.length →
    (∀ i, i < y.length →
      ground.getAt 0 z i ≤ ground.getAt 0 y i) →
    tieGap y z = some (List.zipWith (fun a b => a - b) y z) :=
  fun y z h hle =>
    tieGap_make y z (List.zipWith (fun a b => a - b) y z)
      (ground.length_zipWith (fun a b => a - b) y z y.length rfl h) h
      (fun i hi => by
        rw [ground.getAt_zipWith 0 0 0 (fun a b => a - b) y z i hi
          (by rw [h]; exact hi)]
        exact subAdd (hle i hi))

/-- An absent tie names a reversed entry: at matched lengths some
coordinate of the second display exceeds the first's. -/
private theorem tieGap_none : ∀ (y z : List Nat),
    tieGap y z = none → z.length = y.length →
    ∃ i, i < y.length ∧ ground.getAt 0 y i < ground.getAt 0 z i :=
  fun y z h hl => by
    cases hor : ground.famFold Bool.or false
        (fun i => decide (ground.getAt 0 y i < ground.getAt 0 z i))
        (List.range y.length) with
    | true =>
      obtain ⟨i, hi, hfi⟩ := ground.orRange_read _ y.length hor
      exact ⟨i, hi, of_decide_eq_true hfi⟩
    | false =>
      exact nomatch h.symm.trans
        (tieGap_of_le y z hl (fun i hi =>
          Nat.le_of_not_lt (fun hlt => Bool.noConfusion
            ((ground.orRange_intro _ y.length i hi
              (decide_eq_true hlt)).symm.trans hor))))

/-- The tie moves along the pair: at an occupied first letter of
the tie's content, the display moved one step toward the second
letter ties at the content moved back. -/
private theorem tieMoveBy {a b : Nat} (hab : a < b) {z K chi : List Nat}
    (hb : b < K.length) (hlen : K.length = z.length)
    (htie : tieGap z K = some chi)
    (hKb : 1 ≤ ground.getAt 0 K b)
    (hchia : 1 ≤ ground.getAt 0 chi a) :
    tieGap z (moveBy a b 1 K) = some (moveBy b a 1 chi) := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have hne' : b ≠ a := fun he => hne he.symm
  obtain ⟨hchil, hKl, hent⟩ := tieGap_reads z K chi htie
  have ha : a < K.length := Nat.lt_trans hab hb
  have haz : a < z.length := by rw [← hlen]; exact ha
  have hbz : b < z.length := by rw [← hlen]; exact hb
  have hachi : a < chi.length := by rw [hchil, ← hlen]; exact ha
  have hbchi : b < chi.length := by rw [hchil, ← hlen]; exact hb
  refine tieGap_make z (moveBy a b 1 K) (moveBy b a 1 chi) ?_ ?_ ?_
  · rw [length_moveBy, hchil]
  · rw [length_moveBy, hKl]
  · intro i hi
    by_cases hia : i = a
    · rw [hia, getAt_moveBy_snd b hne' 1 chi hachi,
        getAt_moveBy_fst hne 1 K ha]
      have h0 := hent a haz
      rw [show ground.getAt 0 chi a - 1 + (ground.getAt 0 K a + 1)
          = (ground.getAt 0 chi a - 1 + 1) + ground.getAt 0 K a
          from by
            rw [Nat.add_assoc (ground.getAt 0 chi a - 1) 1
                (ground.getAt 0 K a),
              Nat.add_comm 1 (ground.getAt 0 K a),
              ← Nat.add_assoc],
        subAdd hchia]
      exact h0
    · by_cases hib : i = b
      · rw [hib, getAt_moveBy_fst hne' 1 chi hbchi,
          getAt_moveBy_snd a hne 1 K hb]
        have h0 := hent b hbz
        rw [Nat.add_assoc (ground.getAt 0 chi b) 1
            (ground.getAt 0 K b - 1),
          Nat.add_comm 1 (ground.getAt 0 K b - 1), subAdd hKb]
        exact h0
      · rw [getAt_moveBy_ne b a 1 chi hib hia,
          getAt_moveBy_ne a b 1 K hia hib]
        exact hent i hi

/-- At the tie's first letter reading the count's unit, the moved
display ties at no content: the moved first entry exceeds the
join. -/
private theorem tieMove_bound {a b : Nat} (hab : a < b)
    {z K chi : List Nat} (hb : b < K.length)
    (hlen : K.length = z.length) (htie : tieGap z K = some chi)
    (hchia : ground.getAt 0 chi a = 0) :
    tieGap z (moveBy a b 1 K) = none := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  obtain ⟨hchil, hKl, hent⟩ := tieGap_reads z K chi htie
  have ha : a < K.length := Nat.lt_trans hab hb
  have haz : a < z.length := by rw [← hlen]; exact ha
  cases htie' : tieGap z (moveBy a b 1 K) with
  | none => rfl
  | some chi' =>
    obtain ⟨hchil', hKl', hent'⟩ := tieGap_reads z _ chi' htie'
    have h1 := hent' a haz
    rw [getAt_moveBy_fst hne 1 K ha] at h1
    have h0 := hent a haz
    rw [hchia, Nat.zero_add] at h0
    rw [← Nat.add_assoc, h0] at h1
    have hcon : ground.getAt 0 z a
        < ground.getAt 0 chi' a + ground.getAt 0 z a + 1 :=
      Nat.lt_succ_of_le (Nat.le_add_left _ _)
    rw [h1] at hcon
    exact absurd hcon (Nat.lt_irrefl _)

/-- At an absent tie whose moved display ties, the content reads
the second letter at the count's unit: the one slack the move
opened. -/
private theorem tieMove_slack {a b : Nat} (hab : a < b)
    {z K chi' : List Nat} (hb : b < K.length)
    (hlen : K.length = z.length) (htie : tieGap z K = none)
    (hKb : 1 ≤ ground.getAt 0 K b)
    (htie' : tieGap z (moveBy a b 1 K) = some chi') :
    ground.getAt 0 chi' b = 0 := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have ha : a < K.length := Nat.lt_trans hab hb
  obtain ⟨hchil', hKl', hent'⟩ := tieGap_reads z _ chi' htie'
  obtain ⟨i, hi, hlt⟩ := tieGap_none z K htie hlen
  by_cases hia : i = a
  · rw [hia] at hlt
    have h1 := hent' a (by rw [← hlen]; exact ha)
    rw [getAt_moveBy_fst hne 1 K ha, ← Nat.add_assoc] at h1
    have hKz : ground.getAt 0 K a < ground.getAt 0 z a := by
      rw [← h1]
      exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
    exact absurd (Nat.lt_trans hlt hKz) (Nat.lt_irrefl _)
  · by_cases hib : i = b
    · rw [hib] at hlt
      have h1 := hent' b (by rw [← hlen]; exact hb)
      rw [getAt_moveBy_snd a hne 1 K hb] at h1
      have h4 : ground.getAt 0 chi' b + (ground.getAt 0 K b - 1) + 1
          ≤ ground.getAt 0 K b := by
        rw [h1]
        exact hlt
      have h2 : ground.getAt 0 chi' b + ground.getAt 0 K b
          ≤ ground.getAt 0 K b :=
        calc ground.getAt 0 chi' b + ground.getAt 0 K b
            = ground.getAt 0 chi' b
              + ((ground.getAt 0 K b - 1) + 1) := by
              rw [subAdd hKb]
          _ = ground.getAt 0 chi' b + (ground.getAt 0 K b - 1)
              + 1 := (Nat.add_assoc _ _ _).symm
          _ ≤ ground.getAt 0 K b := h4
      have h3 : ground.getAt 0 K b + ground.getAt 0 chi' b
          ≤ ground.getAt 0 K b + 0 := by
        rw [Nat.add_comm (ground.getAt 0 K b)
            (ground.getAt 0 chi' b)]
        exact h2
      exact Nat.eq_zero_of_le_zero (leCancelL (ground.getAt 0 K b) h3)
    · have h1 := hent' i hi
      rw [getAt_moveBy_ne a b 1 K hia hib] at h1
      rw [← h1] at hlt
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt)
        (Nat.lt_irrefl _)

private theorem bumpPred_move {a b : Nat} (hne : a ≠ b)
    {chi : List Nat} (ha : a < chi.length) (hb : b < chi.length) :
    ground.bumpAt b (ground.editAt (fun x => x - 1) a chi)
      = moveBy b a 1 chi := by
  have hne' : b ≠ a := fun he => hne he.symm
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_bumpAt, ground.length_editAt, length_moveBy]
  · intro t ht
    rw [ground.length_bumpAt, ground.length_editAt] at ht
    by_cases htb : t = b
    · rw [htb,
        ground.getAt_bumpAt_self b _
          (by rw [ground.length_editAt]; exact hb),
        ground.getAt_editAt_ne (fun x => x - 1) a b chi hne',
        getAt_moveBy_fst hne' 1 chi hb]
    · by_cases hta : t = a
      · rw [hta,
          ground.getAt_bumpAt_ne b _ a hne,
          ground.getAt_editAt_self (fun x => x - 1) a chi ha,
          getAt_moveBy_snd b hne' 1 chi ha]
      · rw [
          ground.getAt_bumpAt_ne b _ t htb,
          ground.getAt_editAt_ne (fun x => x - 1) a t chi hta,
          getAt_moveBy_ne b a 1 chi htb hta]

/-- The telescope's per-key read: `⟨x_a : x_b⟩ G_ab
= x_b ⟨D_a ch : D_b ch⟩` as guarded reads at the tie against a
display whose second letter is occupied — the keyed spelling's own
scope, the identity at the key `z` against `K - e_b`'s display —
`stepRead` at a doubly occupied tie, the boundary read at a first
letter reading the count's unit, and the vacuous reads at an
exhausted second letter (`thm:weylchar`'s telescope, every
coefficient of the display reached at `K = e_b`). -/
theorem stepAt (mult : List Nat → Nat) {a b : Nat} (hab : a < b)
    (z K : List Nat) (hb : b < K.length)
    (hKb : 1 ≤ ground.getAt 0 K b) (hlen : K.length = z.length)
    (hsym : ∀ (i j : Nat) (nu : List Nat), i < j → j < z.length →
      nu.length = z.length → mult (swapPair i j nu) = mult nu) :
    dAtGap mult a z K + gAtGap mult a b z (moveBy a b 1 K) true
        + gAtGap mult a b z K false
      = dAtGap mult b z K + gAtGap mult a b z (moveBy a b 1 K) false
        + gAtGap mult a b z K true := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  cases htie : tieGap z K with
  | none =>
    have hdA : dAtGap mult a z K = 0 := by
      show (match tieGap z K with
        | some chi => ground.getAt 0 chi a * mult chi
        | none => 0) = 0
      rw [htie]
    have hdB : dAtGap mult b z K = 0 := by
      show (match tieGap z K with
        | some chi => ground.getAt 0 chi b * mult chi
        | none => 0) = 0
      rw [htie]
    have hgKf : gAtGap mult a b z K false = 0 := by
      show (match tieGap z K with
        | some chi =>
          if false then gSnd mult chi a b else gFst mult chi a b
        | none => 0) = 0
      rw [htie]
    have hgKs : gAtGap mult a b z K true = 0 := by
      show (match tieGap z K with
        | some chi =>
          if true then gSnd mult chi a b else gFst mult chi a b
        | none => 0) = 0
      rw [htie]
    cases htie' : tieGap z (moveBy a b 1 K) with
    | none =>
      have hgMf : gAtGap mult a b z (moveBy a b 1 K) false = 0 := by
        show (match tieGap z (moveBy a b 1 K) with
          | some chi =>
            if false then gSnd mult chi a b else gFst mult chi a b
          | none => 0) = 0
        rw [htie']
      have hgMs : gAtGap mult a b z (moveBy a b 1 K) true = 0 := by
        show (match tieGap z (moveBy a b 1 K) with
          | some chi =>
            if true then gSnd mult chi a b else gFst mult chi a b
          | none => 0) = 0
        rw [htie']
      rw [hdA, hdB, hgKf, hgKs, hgMf, hgMs]
    | some chi' =>
      have hb0 := tieMove_slack hab hb hlen htie hKb htie'
      have hgMf : gAtGap mult a b z (moveBy a b 1 K) false = 0 := by
        show (match tieGap z (moveBy a b 1 K) with
          | some chi =>
            if false then gSnd mult chi a b else gFst mult chi a b
          | none => 0) = 0
        rw [htie']
        show gFst mult chi' a b = 0
        exact gFst_vac mult chi' a hb0
      have hgMs : gAtGap mult a b z (moveBy a b 1 K) true = 0 := by
        show (match tieGap z (moveBy a b 1 K) with
          | some chi =>
            if true then gSnd mult chi a b else gFst mult chi a b
          | none => 0) = 0
        rw [htie']
        show gSnd mult chi' a b = 0
        exact gSnd_vac mult chi' a hb0
      rw [hdA, hdB, hgKf, hgKs, hgMf, hgMs]
  | some chi =>
    obtain ⟨hchil, hKl, hent⟩ := tieGap_reads z K chi htie
    have hachi : a < chi.length := by
      rw [hchil, ← hlen]
      exact Nat.lt_trans hab hb
    have hbchi : b < chi.length := by
      rw [hchil, ← hlen]
      exact hb
    have hdA : dAtGap mult a z K
        = ground.getAt 0 chi a * mult chi := by
      show (match tieGap z K with
        | some c => ground.getAt 0 c a * mult c
        | none => 0) = _
      rw [htie]
    have hdB : dAtGap mult b z K
        = ground.getAt 0 chi b * mult chi := by
      show (match tieGap z K with
        | some c => ground.getAt 0 c b * mult c
        | none => 0) = _
      rw [htie]
    have hgKf : gAtGap mult a b z K false = gFst mult chi a b := by
      show (match tieGap z K with
        | some c =>
          if false then gSnd mult c a b else gFst mult c a b
        | none => 0) = _
      rw [htie]
      rfl
    have hgKs : gAtGap mult a b z K true = gSnd mult chi a b := by
      show (match tieGap z K with
        | some c =>
          if true then gSnd mult c a b else gFst mult c a b
        | none => 0) = _
      rw [htie]
      rfl
    cases hca : ground.getAt 0 chi a with
    | zero =>
      have htie' := tieMove_bound hab hb hlen htie hca
      have hgMf : gAtGap mult a b z (moveBy a b 1 K) false = 0 := by
        show (match tieGap z (moveBy a b 1 K) with
          | some c =>
            if false then gSnd mult c a b else gFst mult c a b
          | none => 0) = 0
        rw [htie']
      have hgMs : gAtGap mult a b z (moveBy a b 1 K) true = 0 := by
        show (match tieGap z (moveBy a b 1 K) with
          | some c =>
            if true then gSnd mult c a b else gFst mult c a b
          | none => 0) = 0
        rw [htie']
      rw [hdA, hdB, hgKf, hgKs, hgMf, hgMs, hca, Nat.zero_mul]
      show 0 + 0 + gFst mult chi a b
        = ground.getAt 0 chi b * mult chi + 0 + gSnd mult chi a b
      rw [Nat.zero_add]
      exact boundaryRead mult chi hab hbchi
        (by rw [hchil]; exact hsym) hca
    | succ c =>
      have hchia : 1 ≤ ground.getAt 0 chi a := by
        rw [hca]
        exact Nat.succ_le_succ (Nat.zero_le c)
      have htie' := tieMoveBy hab hb hlen htie hKb hchia
      have hgMf : gAtGap mult a b z (moveBy a b 1 K) false
          = gFst mult (moveBy b a 1 chi) a b := by
        show (match tieGap z (moveBy a b 1 K) with
          | some c =>
            if false then gSnd mult c a b else gFst mult c a b
          | none => 0) = _
        rw [htie']
        rfl
      have hgMs : gAtGap mult a b z (moveBy a b 1 K) true
          = gSnd mult (moveBy b a 1 chi) a b := by
        show (match tieGap z (moveBy a b 1 K) with
          | some c =>
            if true then gSnd mult c a b else gFst mult c a b
          | none => 0) = _
        rw [htie']
        rfl
      have hstep := stepRead mult (ground.editAt (fun x => x - 1) a chi)
        hab (by rw [ground.length_editAt]; exact hbchi)
      have hbp : ground.bumpAt a (ground.editAt (fun x => x - 1) a chi)
          = chi := ground.bumpAt_dipAt_self a chi hchia
      rw [hbp, bumpPred_move hne hachi hbchi,
        ground.getAt_editAt_ne (fun x => x - 1) a b chi
          (fun he => hne he.symm),
        ground.getAt_editAt_self (fun x => x - 1) a chi hachi,
        subAdd hchia] at hstep
      rw [hdA, hdB, hgKf, hgKs, hgMf, hgMs,
        addSwapEnds (ground.getAt 0 chi a * mult chi)
          (gSnd mult (moveBy b a 1 chi) a b) (gFst mult chi a b),
        addSwapEnds (ground.getAt 0 chi b * mult chi)
          (gFst mult (moveBy b a 1 chi) a b) (gSnd mult chi a b),
        Nat.add_comm (gSnd mult chi a b)
          (gFst mult (moveBy b a 1 chi) a b)]
      exact hstep.symm

private theorem teleSum : ∀ (n : Nat) (F : Nat → Nat),
    ground.famFold Nat.add 0 F (List.range n) + F n
      = F 0 + ground.famFold Nat.add 0 (fun l => F (l + 1))
          (List.range n)
  | 0, F => Nat.add_comm 0 (F 0)
  | n + 1, F => by
    rw [range_cons n]
    show (F 0 + ground.famFold Nat.add 0 F
        ((List.range n).map (fun j => j + 1))) + F (n + 1)
      = F 0 + (F 1 + ground.famFold Nat.add 0 (fun l => F (l + 1))
          ((List.range n).map (fun j => j + 1)))
    rw [ground.famFold_map Nat.add 0 F (fun j => j + 1)
        (List.range n),
      ground.famFold_map Nat.add 0 (fun l => F (l + 1))
        (fun j => j + 1) (List.range n)]
    have hIH : ground.famFold Nat.add 0 (fun j => F (j + 1))
          (List.range n) + F (n + 1)
        = F 1 + ground.famFold Nat.add 0 (fun j => F (j + 1 + 1))
            (List.range n) := teleSum n (fun l => F (l + 1))
    show (F 0 + ground.famFold Nat.add 0 (fun j => F (j + 1))
        (List.range n)) + F (n + 1)
      = F 0 + (F 1 + ground.famFold Nat.add 0
          (fun j => F (j + 1 + 1)) (List.range n))
    rw [Nat.add_assoc (F 0)
        (ground.famFold Nat.add 0 (fun j => F (j + 1))
          (List.range n)) (F (n + 1)),
      hIH]

private theorem moveMove {a b : Nat} (hne : a ≠ b) {W : List Nat}
    (ha : a < W.length) (hb : b < W.length) {j : Nat}
    (hj : j + 1 ≤ ground.getAt 0 W a) :
    moveBy a b 1 (moveBy b a (j + 1) W) = moveBy b a j W := by
  have hne' : b ≠ a := fun he => hne he.symm
  have haM : a < (moveBy b a (j + 1) W).length := by
    rw [length_moveBy]
    exact ha
  have hbM : b < (moveBy b a (j + 1) W).length := by
    rw [length_moveBy]
    exact hb
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [length_moveBy, length_moveBy, length_moveBy]
  · intro t ht
    rw [length_moveBy, length_moveBy] at ht
    by_cases hta : t = a
    · rw [hta, getAt_moveBy_fst hne 1 (moveBy b a (j + 1) W) haM,
        getAt_moveBy_snd b hne' (j + 1) W ha,
        getAt_moveBy_snd b hne' j W ha,
        ground.subSuccAdd hj]
    · by_cases htb : t = b
      · rw [htb, getAt_moveBy_snd a hne 1 (moveBy b a (j + 1) W) hbM,
          getAt_moveBy_fst hne' (j + 1) W hb,
          getAt_moveBy_fst hne' j W hb]
        rfl
      · rw [getAt_moveBy_ne a b 1 (moveBy b a (j + 1) W) hta htb,
          getAt_moveBy_ne b a (j + 1) W htb hta,
          getAt_moveBy_ne b a j W htb hta]

private theorem shuffleP1 (x y z u v : Nat) :
    ((x + y) + z) + (u + v) = (x + (y + u)) + (z + v) := by
  have hL : ((x + y) + z) + (u + v) = x + (y + (z + (u + v))) := by
    rw [Nat.add_assoc (x + y) z (u + v), Nat.add_assoc x y (z + (u + v))]
  have hR : (x + (y + u)) + (z + v) = x + (y + (z + (u + v))) := by
    rw [Nat.add_assoc x (y + u) (z + v), Nat.add_assoc y u (z + v),
      Nat.add_left_comm u z v]
  rw [hL, hR]

private theorem shuffleP2 (x p q r s : Nat) :
    (x + (p + q)) + (r + s) = ((x + p) + s) + (q + r) := by
  have hL : (x + (p + q)) + (r + s) = x + (p + (q + (r + s))) := by
    rw [Nat.add_assoc x (p + q) (r + s), Nat.add_assoc p q (r + s)]
  have hR : ((x + p) + s) + (q + r) = x + (p + (q + (r + s))) := by
    rw [Nat.add_assoc (x + p) s (q + r), Nat.add_assoc x p (s + (q + r)),
      Nat.add_left_comm s q r, Nat.add_comm s r]
  rw [hL, hR]

private theorem shuffleP3 (x p q r s : Nat) :
    ((x + p) + q) + (r + s) = ((x + s) + r) + (q + p) := by
  have hL : ((x + p) + q) + (r + s) = x + (p + (q + (r + s))) := by
    rw [Nat.add_assoc (x + p) q (r + s), Nat.add_assoc x p (q + (r + s))]
  have hR : ((x + s) + r) + (q + p) = x + (p + (q + (r + s))) := by
    rw [Nat.add_assoc (x + s) r (q + p), Nat.add_assoc x s (r + (q + p)),
      Nat.add_left_comm s r (q + p), Nat.add_left_comm s q p,
      Nat.add_comm s p, Nat.add_left_comm r q (p + s),
      Nat.add_left_comm r p s, Nat.add_left_comm q p (r + s)]
  rw [hL, hR]

/-- The cleared telescope at the cofactor, per display: the shift
fold of `x_b ⟨D_a ch : D_b ch⟩`'s guarded reads over the moved
displays collects to the head display's `G`-read against the far
boundary's — `⟨x_a : x_b⟩ Q_ab = V`'s back-substitution read
through the per-key telescope `stepAt`, the interior reads
canceling in consecutive pairs (`thm:weylchar`'s `V G_pq
= Q_pq x_q ⟨D_p ch : D_q ch⟩`, one display at a time). -/
theorem cofRead (mult : List Nat → Nat) {a b : Nat} (hab : a < b)
    (z W : List Nat) (hb : b < W.length)
    (hlen : W.length = z.length)
    (hsym : ∀ (i j : Nat) (nu : List Nat), i < j → j < z.length →
      nu.length = z.length → mult (swapPair i j nu) = mult nu) :
    ground.famFold Nat.add 0
        (fun k => dAtGap mult a z (moveBy b a k W))
        ((List.range (ground.getAt 0 W a)).map (fun k => k + 1))
      + gAtGap mult a b z W true
      + gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) false
    = ground.famFold Nat.add 0
        (fun k => dAtGap mult b z (moveBy b a k W))
        ((List.range (ground.getAt 0 W a)).map (fun k => k + 1))
      + gAtGap mult a b z W false
      + gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W)
          true := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have hne' : b ≠ a := fun he => hne he.symm
  have haW : a < W.length := Nat.lt_trans hab hb
  have hmapA : ground.famFold Nat.add 0
      (fun k => dAtGap mult a z (moveBy b a k W))
      ((List.range (ground.getAt 0 W a)).map (fun k => k + 1))
    = ground.famFold Nat.add 0
      (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
      (List.range (ground.getAt 0 W a)) :=
    ground.famFold_map Nat.add 0 _ _ _
  have hmapB : ground.famFold Nat.add 0
      (fun k => dAtGap mult b z (moveBy b a k W))
      ((List.range (ground.getAt 0 W a)).map (fun k => k + 1))
    = ground.famFold Nat.add 0
      (fun j => dAtGap mult b z (moveBy b a (j + 1) W))
      (List.range (ground.getAt 0 W a)) :=
    ground.famFold_map Nat.add 0 _ _ _
  have h1 : ground.famFold Nat.add 0
      (fun j => dAtGap mult a z (moveBy b a (j + 1) W)
        + gAtGap mult a b z (moveBy b a j W) true
        + gAtGap mult a b z (moveBy b a (j + 1) W) false)
      (List.range (ground.getAt 0 W a))
    = ground.famFold Nat.add 0
      (fun j => dAtGap mult b z (moveBy b a (j + 1) W)
        + gAtGap mult a b z (moveBy b a j W) false
        + gAtGap mult a b z (moveBy b a (j + 1) W) true)
      (List.range (ground.getAt 0 W a)) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _
      (fun j hj => ?_)
    have hjn : j < ground.getAt 0 W a := ground.ltOfMem hj
    have hstep := stepAt mult hab z (moveBy b a (j + 1) W)
      (by rw [length_moveBy]; exact hb)
      (by rw [getAt_moveBy_fst hne' (j + 1) W hb]
          exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le j))
            (Nat.le_add_left (j + 1) (ground.getAt 0 W b)))
      (by rw [length_moveBy]; exact hlen) hsym
    rw [moveMove hne haW hb (Nat.succ_le_of_lt hjn)] at hstep
    exact hstep
  have hsplitL : ground.famFold Nat.add 0
      (fun j => dAtGap mult a z (moveBy b a (j + 1) W)
        + gAtGap mult a b z (moveBy b a j W) true
        + gAtGap mult a b z (moveBy b a (j + 1) W) false)
      (List.range (ground.getAt 0 W a))
    = (ground.famFold Nat.add 0
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) true)
        (List.range (ground.getAt 0 W a)))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) false)
        (List.range (ground.getAt 0 W a)) := by
    rw [← famFold_add_split
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
        (fun j => gAtGap mult a b z (moveBy b a j W) true)
        (List.range (ground.getAt 0 W a)),
      ← famFold_add_split
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W)
          + gAtGap mult a b z (moveBy b a j W) true)
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) false)
        (List.range (ground.getAt 0 W a))]
  have hsplitR : ground.famFold Nat.add 0
      (fun j => dAtGap mult b z (moveBy b a (j + 1) W)
        + gAtGap mult a b z (moveBy b a j W) false
        + gAtGap mult a b z (moveBy b a (j + 1) W) true)
      (List.range (ground.getAt 0 W a))
    = (ground.famFold Nat.add 0
        (fun j => dAtGap mult b z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) false)
        (List.range (ground.getAt 0 W a)))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
        (List.range (ground.getAt 0 W a)) := by
    rw [← famFold_add_split
        (fun j => dAtGap mult b z (moveBy b a (j + 1) W))
        (fun j => gAtGap mult a b z (moveBy b a j W) false)
        (List.range (ground.getAt 0 W a)),
      ← famFold_add_split
        (fun j => dAtGap mult b z (moveBy b a (j + 1) W)
          + gAtGap mult a b z (moveBy b a j W) false)
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
        (List.range (ground.getAt 0 W a))]
  have h2 : ground.famFold Nat.add 0
      (fun j => gAtGap mult a b z (moveBy b a j W) false)
      (List.range (ground.getAt 0 W a))
      + gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) false
    = gAtGap mult a b z W false
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) false)
        (List.range (ground.getAt 0 W a)) := by
    have ht : ground.famFold Nat.add 0
        (fun l => gAtGap mult a b z (moveBy b a l W) false)
        (List.range (ground.getAt 0 W a))
        + gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W)
            false
      = gAtGap mult a b z (moveBy b a 0 W) false
        + ground.famFold Nat.add 0
          (fun l => gAtGap mult a b z (moveBy b a (l + 1) W) false)
          (List.range (ground.getAt 0 W a)) :=
      teleSum (ground.getAt 0 W a)
        (fun l => gAtGap mult a b z (moveBy b a l W) false)
    rw [moveBy_zero b a W] at ht
    exact ht
  have h3 : ground.famFold Nat.add 0
      (fun j => gAtGap mult a b z (moveBy b a j W) true)
      (List.range (ground.getAt 0 W a))
      + gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) true
    = gAtGap mult a b z W true
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
        (List.range (ground.getAt 0 W a)) := by
    have ht : ground.famFold Nat.add 0
        (fun l => gAtGap mult a b z (moveBy b a l W) true)
        (List.range (ground.getAt 0 W a))
        + gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W)
            true
      = gAtGap mult a b z (moveBy b a 0 W) true
        + ground.famFold Nat.add 0
          (fun l => gAtGap mult a b z (moveBy b a (l + 1) W) true)
          (List.range (ground.getAt 0 W a)) :=
      teleSum (ground.getAt 0 W a)
        (fun l => gAtGap mult a b z (moveBy b a l W) true)
    rw [moveBy_zero b a W] at ht
    exact ht
  refine addCancelR
    (ground.famFold Nat.add 0
      (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
      (List.range (ground.getAt 0 W a))
    + ground.famFold Nat.add 0
      (fun j => gAtGap mult a b z (moveBy b a j W) false)
      (List.range (ground.getAt 0 W a))) ?_
  have h1' : (ground.famFold Nat.add 0
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) true)
        (List.range (ground.getAt 0 W a)))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) false)
        (List.range (ground.getAt 0 W a))
    = (ground.famFold Nat.add 0
        (fun j => dAtGap mult b z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) false)
        (List.range (ground.getAt 0 W a)))
      + ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
        (List.range (ground.getAt 0 W a)) :=
    (hsplitL.symm.trans h1).trans hsplitR
  rw [hmapA, hmapB,
    shuffleP1
      (ground.famFold Nat.add 0
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a)))
      (gAtGap mult a b z W true)
      (gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) false)
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
        (List.range (ground.getAt 0 W a)))
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) false)
        (List.range (ground.getAt 0 W a))),
    ← h3,
    Nat.add_comm
      (gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) false)
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) false)
        (List.range (ground.getAt 0 W a))),
    h2,
    shuffleP2
      (ground.famFold Nat.add 0
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a)))
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) true)
        (List.range (ground.getAt 0 W a)))
      (gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) true)
      (gAtGap mult a b z W false)
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) false)
        (List.range (ground.getAt 0 W a))),
    h1',
    shuffleP3
      (ground.famFold Nat.add 0
        (fun j => dAtGap mult b z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a)))
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a j W) false)
        (List.range (ground.getAt 0 W a)))
      (ground.famFold Nat.add 0
        (fun j => gAtGap mult a b z (moveBy b a (j + 1) W) true)
        (List.range (ground.getAt 0 W a)))
      (gAtGap mult a b z (moveBy b a (ground.getAt 0 W a) W) true)
      (gAtGap mult a b z W false)]

/-! The perm-fold assembly (`thm:weylchar`'s assembly): the cleared
telescope at the cofactor summed over the place permutations — the
product's graded coefficient against the telescope family reads the
cofactor's shift fold, the far boundaries canceling per swap coset,
the graded sum's odd-swap read at the shared zeroed display. -/

/-- The product's graded coefficient against the telescope family
at a key, one side: `[a_u · G_ab]_z`'s side — the fold over the
place permutations of the guarded `G`-read at the permuted display,
the read's member the side's composition with the permutation's
grading. -/
def prodG (mult : List Nat → Nat) (a b d : Nat) (z : List Nat)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p => gAtGap mult a b z (expo (unitDisp d) p)
      (xor side (parity p)))
    (perms d)

/-- The cofactor's shift fold at a key, one side:
`[Q_ab ⊗ x_b ⟨D_a ch : D_b ch⟩]_z`'s side at the alternant's
clearing — per permutation the guarded Euler reads over the moved
displays, the read letter the side's composition with the
grading. -/
def cofFold (mult : List Nat → Nat) (a b d : Nat) (z : List Nat)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      ground.famFold Nat.add 0
        (fun k => dAtGap mult
          (if xor side (parity p) then b else a) z
          (moveBy b a k (expo (unitDisp d) p)))
        ((List.range
            (ground.getAt 0 (expo (unitDisp d) p) a)).map
          (fun k => k + 1)))
    (perms d)

private theorem farShared {a b : Nat} (hne : a ≠ b) (W : List Nat)
    (ha : a < W.length) (hb : b < W.length) :
    moveBy b a (ground.getAt 0 (swapPair a b W) a) (swapPair a b W)
      = moveBy b a (ground.getAt 0 W a) W := by
  have hne' : b ≠ a := fun he => hne he.symm
  have haS : a < (swapPair a b W).length := by
    rw [length_swapPair]
    exact ha
  have hbS : b < (swapPair a b W).length := by
    rw [length_swapPair]
    exact hb
  have hga : ground.getAt 0 (swapPair a b W) a
      = ground.getAt 0 W b := getAt_swapPair_fst W hne ha hb
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [length_moveBy, length_moveBy, length_swapPair]
  · intro t ht
    rw [length_moveBy, length_swapPair] at ht
    by_cases hta : t = a
    · rw [hta,
        getAt_moveBy_snd b hne' _ (swapPair a b W) haS,
        getAt_moveBy_snd b hne' _ W ha, hga]
      rw [Nat.sub_self (ground.getAt 0 W b),
        Nat.sub_self (ground.getAt 0 W a)]
    · by_cases htb : t = b
      · rw [htb,
          getAt_moveBy_fst hne' _ (swapPair a b W) hbS,
          getAt_moveBy_fst hne' _ W hb, hga,
          getAt_swapPair_snd W hne ha hb,
          Nat.add_comm (ground.getAt 0 W a) (ground.getAt 0 W b)]
      · rw [getAt_moveBy_ne b a _ (swapPair a b W) htb hta,
          getAt_moveBy_ne b a _ W htb hta,
          getAt_swapPair_ne W ha hb hta htb]

private theorem farCancel (mult : List Nat → Nat) {a b d : Nat}
    (hab : a < b) (hbd : b < d) (z : List Nat) :
    ground.famFold Nat.add 0
      (fun p => gAtGap mult a b z
        (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
          (expo (unitDisp d) p))
        (parity p))
      (perms d)
    = ground.famFold Nat.add 0
      (fun p => gAtGap mult a b z
        (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
          (expo (unitDisp d) p))
        (!(parity p)))
      (perms d) := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have had : a < d := Nat.lt_trans hab hbd
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun p => gAtGap mult a b z
      (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
        (expo (unitDisp d) p))
      (parity p))
    (l := perms d) (g := swapPair a b) (h := swapPair a b)
    (monomialsAt_distinct _)
    (fun p _ => swapPair_swapPair a b p)
    (fun p _ => swapPair_swapPair a b p)
    (fun p hp => swapKey_member hp)
    (fun p hp => swapKey_member hp)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  obtain ⟨hplen, hpdist, _, _⟩ := perm_member_reads hp
  have hap : a < p.length := by rw [hplen]; exact had
  have hbp : b < p.length := by rw [hplen]; exact hbd
  have hWlen : (expo (unitDisp d) p).length = p.length := by
    show (p.map (ground.getAt 0 (unitDisp d))).length = p.length
    rw [ground.length_map]
  have hexpo : expo (unitDisp d) (swapPair a b p)
      = swapPair a b (expo (unitDisp d) p) := by
    show (swapPair a b p).map (ground.getAt 0 (unitDisp d)) = _
    rw [← swapPair_map (ground.getAt 0 (unitDisp d)) a b p]
    rfl
  show gAtGap mult a b z
      (moveBy b a
        (ground.getAt 0 (expo (unitDisp d) (swapPair a b p)) a)
        (expo (unitDisp d) (swapPair a b p)))
      (parity (swapPair a b p))
    = gAtGap mult a b z
      (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
        (expo (unitDisp d) p))
      (!(parity p))
  rw [hexpo, parity_swapPair p hne hap hbp hpdist,
    farShared hne (expo (unitDisp d) p)
      (by rw [hWlen]; exact hap) (by rw [hWlen]; exact hbp)]

/-- The cofactor display summed over the permutations,
`a_u G_ab = Q_ab x_b ⟨D_a ch : D_b ch⟩` at the alternant's
clearing: the product's graded coefficient against the telescope
family is the cofactor's shift fold at every key — the per-display
telescope summed, the far boundaries canceling per swap coset at
the shared zeroed display, the graded sum's odd-swap read
(`thm:weylchar`'s `V G_pq = Q_pq x_q ⟨D_p ch : D_q ch⟩`). -/
theorem cofProd (mult : List Nat → Nat) {a b d : Nat}
    (hab : a < b) (hbd : b < d) (z : List Nat)
    (hz : z.length = d)
    (hsym : ∀ (i j : Nat) (nu : List Nat), i < j → j < d →
      nu.length = d → mult (swapPair i j nu) = mult nu) :
    prodG mult a b d z false + cofFold mult a b d z true
      = prodG mult a b d z true + cofFold mult a b d z false := by
  have h1 : ground.famFold Nat.add 0
      (fun p =>
        ground.famFold Nat.add 0
          (fun k => dAtGap mult
            (if xor false (parity p) then b else a) z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
        + gAtGap mult a b z (expo (unitDisp d) p)
            (xor true (parity p))
        + gAtGap mult a b z
            (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
            (parity p))
      (perms d)
    = ground.famFold Nat.add 0
      (fun p =>
        ground.famFold Nat.add 0
          (fun k => dAtGap mult
            (if xor true (parity p) then b else a) z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
        + gAtGap mult a b z (expo (unitDisp d) p)
            (xor false (parity p))
        + gAtGap mult a b z
            (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
            (!(parity p)))
      (perms d) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
      (fun p hp => ?_)
    obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
    have hWlen : (expo (unitDisp d) p).length = d := by
      show (p.map (ground.getAt 0 (unitDisp d))).length = d
      rw [ground.length_map, hplen]
    have hCR := cofRead mult hab z (expo (unitDisp d) p)
      (by rw [hWlen]; exact hbd)
      (by rw [hWlen, hz])
      (by rw [hz]; exact hsym)
    cases hpar : parity p with
    | false =>
      show ground.famFold Nat.add 0
          (fun k => dAtGap mult a z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
        + gAtGap mult a b z (expo (unitDisp d) p) true
        + gAtGap mult a b z
            (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p)) false
        = ground.famFold Nat.add 0
          (fun k => dAtGap mult b z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
        + gAtGap mult a b z (expo (unitDisp d) p) false
        + gAtGap mult a b z
            (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p)) true
      exact hCR
    | true =>
      show ground.famFold Nat.add 0
          (fun k => dAtGap mult b z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
        + gAtGap mult a b z (expo (unitDisp d) p) false
        + gAtGap mult a b z
            (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p)) true
        = ground.famFold Nat.add 0
          (fun k => dAtGap mult a z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
        + gAtGap mult a b z (expo (unitDisp d) p) true
        + gAtGap mult a b z
            (moveBy b a (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p)) false
      exact hCR.symm
  rw [famFold_add_split _ _ (perms d),
    famFold_add_split _ _ (perms d),
    famFold_add_split _ _ (perms d),
    famFold_add_split _ _ (perms d)] at h1
  rw [farCancel mult hab hbd z] at h1
  have h2 := addCancelR _ h1
  show prodG mult a b d z false + cofFold mult a b d z true
    = prodG mult a b d z true + cofFold mult a b d z false
  rw [Nat.add_comm (prodG mult a b d z false)
      (cofFold mult a b d z true),
    Nat.add_comm (prodG mult a b d z true)
      (cofFold mult a b d z false)]
  exact h2.symm

/-- The cofactor's coefficient at a key (`thm:weylchar`'s `Q_ij` at
the alternant's clearing, as data): the division's
back-substitution at the monic first letter — the shift fold of the
graded counts over the moved keys, the second letter's count capping
the range. -/
def cofAt (a b d : Nat) (kappa : List Nat) (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun l => sideCount d (unitDisp d)
      (ground.editAt (fun x => x + (l + 1)) a
        (ground.editAt (fun x => x - l) b kappa)) side)
    (List.range (ground.getAt 0 kappa b + 1))

/-! The product-rule read's display detection (`thm:weylchar`'s
assembly, the derivative display's derivation): an arrangement — a
key reading every unit-display value once — names its permutation
by the complement read, the graded counts at the unit display read
the count's unit off the arrangements and one graded unit at an
arrangement's own permutation, and a pair's moved line through a
key reads its two arrangements alone, the two fillings of the
line's open values at the exchanged grading. -/

/-- The window check on the entries: every member value sits in the
count's window, one and the count its ends. -/
private def entGo (d : Nat) : List Nat → Bool
  | [] => true
  | e :: t => (Nat.ble 1 e && Nat.ble e d) && entGo d t

private theorem entGo_reads {d : Nat} : ∀ {z : List Nat},
    entGo d z = true →
    ∀ v, 0 < ground.countOf v z → 1 ≤ v ∧ v ≤ d
  | [], _, v, hv => absurd hv (Nat.lt_irrefl 0)
  | e :: t, h, v, hv => by
    have h2 := ground.andSplitB (a := Nat.ble 1 e && Nat.ble e d)
      (b := entGo d t) h
    by_cases hve : v = e
    · have h3 := ground.andSplitB h2.1
      rw [hve]
      exact ⟨bleLe h3.1, bleLe h3.2⟩
    · rw [ground.countOf_head_ne hve] at hv
      exact entGo_reads h2.2 v hv

private theorem entGo_make {d : Nat} : ∀ {z : List Nat},
    (∀ v, 0 < ground.countOf v z → 1 ≤ v ∧ v ≤ d) →
    entGo d z = true
  | [], _ => rfl
  | e :: t, h => by
    have he := h e (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _)
    show ((Nat.ble 1 e && Nat.ble e d) && entGo d t) = true
    rw [leBle he.1, leBle he.2,
      entGo_make (fun v hv => h v (ground.countOf_cons_pos hv))]
    rfl

/-- The window fold on the values: every window value read once. -/
private def valsGo (z : List Nat) : Nat → Bool
  | 0 => true
  | v + 1 => Nat.beq (ground.countOf (v + 1) z) 1 && valsGo z v

private theorem valsGo_reads {z : List Nat} : ∀ {n : Nat},
    valsGo z n = true →
    ∀ v, 1 ≤ v → v ≤ n → ground.countOf v z = 1 := by
  intro n
  induction n with
  | zero => exact fun _ v hv hn => nomatch Nat.le_trans hv hn
  | succ n ih =>
    intro h v hv hn
    have h2 := ground.andSplitB (a := Nat.beq (ground.countOf (n + 1) z) 1)
      (b := valsGo z n) h
    match Nat.lt_or_ge v (n + 1) with
    | .inl hlt => exact ih h2.2 v hv (Nat.le_of_lt_succ hlt)
    | .inr hge =>
      rw [Nat.le_antisymm hn hge]
      exact ground.beqEq _ _ h2.1

private theorem valsGo_make {z : List Nat} : ∀ {n : Nat},
    (∀ v, 1 ≤ v → v ≤ n → ground.countOf v z = 1) →
    valsGo z n = true := by
  intro n
  induction n with
  | zero => exact fun _ => rfl
  | succ n ih =>
    intro h
    show (Nat.beq (ground.countOf (n + 1) z) 1 && valsGo z n) = true
    rw [h (n + 1) (Nat.succ_pos n) (Nat.le_refl (n + 1)), ground.beqRefl,
      ih (fun v hv hn => h v hv (Nat.le_succ_of_le hn))]
    rfl

/-- The arrangement test at a count: the length the count, every
entry a window value, and every window value read once — the moved
lines' display recognition (`thm:weylchar`'s assembly, the
arrangements of the derivative display's derivation). -/
def arrB (d : Nat) (z : List Nat) : Bool :=
  Nat.beq z.length d && (entGo d z && valsGo z d)

/-- An arrangement's permutation, the complement read at every
entry: the display's own preimage under the unit display. -/
def permOf (d : Nat) (z : List Nat) : List Nat :=
  z.map (fun v => d - v)

private theorem arr_reads {d : Nat} {z : List Nat}
    (h : arrB d z = true) :
    z.length = d ∧ (∀ v, 0 < ground.countOf v z → 1 ≤ v ∧ v ≤ d)
      ∧ (∀ v, 1 ≤ v → v ≤ d → ground.countOf v z = 1) := by
  have h2 := ground.andSplitB (a := Nat.beq z.length d)
    (b := entGo d z && valsGo z d) h
  have h3 := ground.andSplitB h2.2
  exact ⟨ground.beqEq _ _ h2.1, entGo_reads h3.1, valsGo_reads h3.2⟩

private theorem arr_make {d : Nat} {z : List Nat}
    (hlen : z.length = d)
    (hent : ∀ v, 0 < ground.countOf v z → 1 ≤ v ∧ v ≤ d)
    (hval : ∀ v, 1 ≤ v → v ≤ d → ground.countOf v z = 1) :
    arrB d z = true := by
  show (Nat.beq z.length d && (entGo d z && valsGo z d)) = true
  rw [hlen, ground.beqRefl, entGo_make hent, valsGo_make hval]
  rfl

/-- An arrangement's permutation is a member of the enumeration:
the complement read keeps the counts against the range's. -/
theorem permOf_member {d : Nat} {z : List Nat}
    (h : arrB d z = true) :
    0 < ground.countOf (permOf d z) (perms d) := by
  obtain ⟨hlen, hent, _⟩ := arr_reads h
  have hrange : 0 < ground.countOf (List.range d) (perms d) := by
    rw [countRangePerms d]
    exact Nat.succ_pos 0
  refine perm_member_of_counts hrange ?_ ?_
  · show (z.map (fun v => d - v)).length = (List.range d).length
    rw [ground.length_map, hlen, length_range]
  · intro x
    match Nat.lt_or_ge x d with
    | .inl hxd =>
      have hcnt : ground.countOf x (permOf d z)
          = ground.countOf (d - x) z := by
        refine ground.countOf_map_iff (fun v => d - v) z x (d - x)
          (fun v hv => ?_)
        obtain ⟨hv1, hvd⟩ := hent v hv
        exact ⟨fun hx => by rw [hx, natSubSubCancel _ _ hvd],
          fun hy => by rw [← hy, natSubSubCancel _ _ (Nat.le_of_lt hxd)]⟩
      rw [hcnt, countOf_range x d, if_pos hxd]
      refine (arr_reads h).2.2 (d - x) ?_ (Nat.sub_le d x)
      exact subPos hxd
    | .inr hxd =>
      have hcnt : ground.countOf x (permOf d z) = 0 := by
        refine ground.countOf_map_none (fun v => d - v) x z
          (fun v hv he => ?_)
        obtain ⟨hv1, _⟩ := hent v hv
        have hlt : d - v < d :=
          Nat.sub_lt (Nat.lt_of_lt_of_le hv1 (hent v hv).2) hv1
        rw [← he] at hxd
        exact Nat.lt_irrefl d (Nat.lt_of_le_of_lt hxd hlt)
      rw [hcnt, countOf_range x d,
        if_neg (fun hc =>
          Nat.lt_irrefl d (Nat.lt_of_le_of_lt hxd hc))]

/-- An arrangement is its permutation's display: the complement
read composes with the unit display to the entries back. -/
theorem expo_permOf {d : Nat} {z : List Nat}
    (h : arrB d z = true) :
    expo (unitDisp d) (permOf d z) = z := by
  obtain ⟨hlen, hent, _⟩ := arr_reads h
  have hexplen : (expo (unitDisp d) (permOf d z)).length
      = z.length := by
    show ((z.map (fun v => d - v)).map
        (ground.getAt 0 (unitDisp d))).length = z.length
    rw [ground.length_map, ground.length_map]
  refine ground.getAt_ext 0 _ _ hexplen ?_
  intro k hk
  have hkz : k < z.length := by
    rw [← hexplen]
    exact hk
  have hkm : k < (z.map (fun v => d - v)).length := by
    rw [ground.length_map]
    exact hkz
  obtain ⟨h1, hd⟩ := hent (ground.getAt 0 z k)
    (countOf_getAt_pos 0 z k hkz)
  show ground.getAt 0 ((z.map (fun v => d - v)).map
      (ground.getAt 0 (unitDisp d))) k = ground.getAt 0 z k
  rw [ground.getAt_map 0 0 _ _ k hkm,
    ground.getAt_map 0 0 _ _ k hkz,
    getAt_unitDisp d _ (Nat.sub_lt (Nat.lt_of_lt_of_le h1 hd) h1),
    natSubSubCancel _ _ hd]

/-- A member's display is an arrangement: the recognition closes on
the enumeration's own reads. -/
theorem arrB_expo {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    arrB d (expo (unitDisp d) p) = true := by
  obtain ⟨hplen, hpdist, hpval, hpocc⟩ := perm_member_reads hp
  have hmap : expo (unitDisp d) p = p.map (fun x => d - x) := by
    show p.map (ground.getAt 0 (unitDisp d)) = _
    exact ground.map_congr_members _ _ p (fun x hx =>
      getAt_unitDisp d x (hpval x hx))
  refine arr_make ?_ ?_ ?_
  · rw [hmap, ground.length_map, hplen]
  · intro v hv
    rw [hmap] at hv
    match Nat.eq_zero_or_pos (ground.countOf v
        (p.map (fun x => d - x))) with
    | .inl hz =>
      rw [hz] at hv
      exact absurd hv (Nat.lt_irrefl 0)
    | .inr hpos =>
      have hex : ground.getAt 0 (p.map (fun x => d - x))
          (posOf v (p.map (fun x => d - x))) = v :=
        getAt_posOf v _ hpos
      have hplt : posOf v (p.map (fun x => d - x))
          < (p.map (fun x => d - x)).length :=
        posOf_lt v _ hpos
      have hplp : posOf v (p.map (fun x => d - x)) < p.length := by
        rw [ground.length_map] at hplt
        exact hplt
      rw [ground.getAt_map 0 0 _ _ _ hplp] at hex
      have hval := hpval _ (countOf_getAt_pos 0 p _ hplp)
      constructor
      · rw [← hex]
        exact subPos hval
      · rw [← hex]
        exact Nat.sub_le d _
  · intro v hv1 hvd
    rw [hmap]
    have hcnt : ground.countOf v (p.map (fun x => d - x))
        = ground.countOf (d - v) p := by
      refine ground.countOf_map_iff (fun x => d - x) p v (d - v)
        (fun x hx => ?_)
      have hxd := hpval x hx
      exact ⟨fun hveq => by rw [hveq, natSubSubCancel _ _ (Nat.le_of_lt hxd)],
        fun hy => by rw [← hy, natSubSubCancel _ _ hvd]⟩
    rw [hcnt]
    have hlt : d - v < d := Nat.sub_lt (Nat.lt_of_lt_of_le hv1 hvd)
      hv1
    exact Nat.le_antisymm (hpdist (d - v)) (hpocc (d - v) hlt)

/-- Two members at one display are one member, the display's
entries the complement reads back. -/
private theorem expo_inj {d : Nat} {p q : List Nat}
    (hp : 0 < ground.countOf p (perms d))
    (hq : 0 < ground.countOf q (perms d))
    (he : expo (unitDisp d) p = expo (unitDisp d) q) : p = q := by
  obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
  obtain ⟨hqlen, _, hqval, _⟩ := perm_member_reads hq
  refine ground.getAt_ext 0 p q (by rw [hplen, hqlen]) ?_
  intro k hk
  have hkq : k < q.length := by
    rw [hqlen, ← hplen]
    exact hk
  have hep : ground.getAt 0 (expo (unitDisp d) p) k
      = d - ground.getAt 0 p k := by
    show ground.getAt 0 (p.map (ground.getAt 0 (unitDisp d))) k = _
    rw [ground.getAt_map 0 0 _ p k hk,
      getAt_unitDisp d _ (hpval _ (countOf_getAt_pos 0 p k hk))]
  have heq : ground.getAt 0 (expo (unitDisp d) q) k
      = d - ground.getAt 0 q k := by
    show ground.getAt 0 (q.map (ground.getAt 0 (unitDisp d))) k = _
    rw [ground.getAt_map 0 0 _ q k hkq,
      getAt_unitDisp d _ (hqval _ (countOf_getAt_pos 0 q k hkq))]
  have h2 : d - ground.getAt 0 p k = d - ground.getAt 0 q k := by
    rw [← hep, ← heq, he]
  exact ground.subInj (Nat.le_of_lt (hpval _ (countOf_getAt_pos 0 p k hk)))
    (Nat.le_of_lt (hqval _ (countOf_getAt_pos 0 q k hkq))) h2

/-- The graded counts at an arrangement: one graded unit at the
arrangement's own permutation's side, the count's unit at the
other — one permutation per display. -/
theorem sideCount_arr {d : Nat} {z : List Nat}
    (h : arrB d z = true) (side : Bool) :
    sideCount d (unitDisp d) z side
      = if side = parity (permOf d z) then 1 else 0 := by
  show ground.famFold Nat.add 0
      (fun p => if parity p = side then
        (if expo (unitDisp d) p = z then 1 else 0) else 0)
      (perms d) = _
  rw [ground.famFold_congr_members Nat.add 0 _
    (fun p => if permOf d z = p then
      (if side = parity (permOf d z) then (1 : Nat) else 0) else 0)
    (perms d) (fun p hp => by
      by_cases hpz : permOf d z = p
      · rw [if_pos hpz, ← hpz, expo_permOf h,
          if_pos rfl]
        by_cases hside : parity (permOf d z) = side
        · rw [if_pos hside, if_pos hside.symm]
        · rw [if_neg hside,
            if_neg (fun hc => hside hc.symm)]
      · rw [if_neg hpz]
        by_cases hpar : parity p = side
        · rw [if_pos hpar,
            if_neg (fun hc : expo (unitDisp d) p = z => hpz
              (expo_inj (permOf_member h) hp
                ((expo_permOf h).trans hc.symm)))]
        · rw [if_neg hpar])]
  by_cases hside : side = parity (permOf d z)
  · rw [if_pos hside,
      ← countOf_fold (permOf d z) (perms d)]
    exact Nat.le_antisymm
      (ground.distinctList_all (monomialsAt_distinct _) (permOf d z))
      (permOf_member h)
  · rw [if_neg hside,
      ground.famFold_congr_all Nat.add 0 _ (fun _ => (0 : Nat))
        (fun p => by
          by_cases hpz : permOf d z = p
          · rw [if_pos hpz]
          · rw [if_neg hpz]) (perms d),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d)]

/-- The graded counts off the arrangements read the count's unit:
every display is an arrangement. -/
theorem sideCount_off {d : Nat} {z : List Nat}
    (h : arrB d z = false) (side : Bool) :
    sideCount d (unitDisp d) z side = 0 := by
  show ground.famFold Nat.add 0
      (fun p => if parity p = side then
        (if expo (unitDisp d) p = z then 1 else 0) else 0)
      (perms d) = 0
  rw [ground.famFold_congr_members Nat.add 0 _
    (fun _ => (0 : Nat)) (perms d) (fun p hp => by
      by_cases hpar : parity p = side
      · rw [if_pos hpar,
          if_neg (fun hc : expo (unitDisp d) p = z => by
            rw [← hc] at h
            exact Bool.noConfusion ((arrB_expo hp).symm.trans h))]
      · rw [if_neg hpar]),
    famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d)]

/-- An arrangement's counts are at most one at every value. -/
private theorem arr_counts_le {d : Nat} {z : List Nat}
    (hz : arrB d z = true) :
    ∀ x, ground.countOf x z ≤ 1 := by
  obtain ⟨_, hent, hval⟩ := arr_reads hz
  intro x
  by_cases hx : 1 ≤ x ∧ x ≤ d
  · rw [hval x hx.1 hx.2]
    exact Nat.le_refl 1
  · match Nat.eq_zero_or_pos (ground.countOf x z) with
    | .inl h0 => rw [h0]; exact Nat.le_succ 0
    | .inr hpos => exact absurd ⟨(hent x hpos).1,
        (hent x hpos).2⟩ hx

/-- An arrangement's two places read distinct values, in either
place order. -/
private theorem arr_getAt_ne {d : Nat} {z : List Nat}
    (hz : arrB d z = true) {s t : Nat} (hs : s < d) (ht : t < d)
    (hst : s ≠ t) :
    ground.getAt 0 z s ≠ ground.getAt 0 z t := by
  have hlen := (arr_reads hz).1
  match Nat.lt_or_ge s t with
  | .inl hlt =>
    exact getAt_ne_of_distinct (arr_counts_le hz) hlt
      (by rw [hlen]; exact ht)
  | .inr hge =>
    have hlt : t < s :=
      Nat.lt_of_le_of_ne hge (fun he => hst he.symm)
    exact fun he =>
      getAt_ne_of_distinct (arr_counts_le hz) hlt
        (by rw [hlen]; exact hs) he.symm

/-- The line's two arrangements (`thm:weylchar`'s assembly): two
arrangements agreeing off a place pair are equal or the pair's
value exchange — the two fillings of the line's open values. -/
theorem arr_two {d a b : Nat} (hne : a ≠ b) (ha : a < d)
    (hb : b < d) {z z' : List Nat}
    (hz : arrB d z = true) (hz' : arrB d z' = true)
    (hoff : ∀ t, t < d → t ≠ a → t ≠ b →
      ground.getAt 0 z' t = ground.getAt 0 z t) :
    z' = z ∨ z' = swapPair a b z := by
  obtain ⟨hlen, hent, hval⟩ := arr_reads hz
  obtain ⟨hlen', hent', hval'⟩ := arr_reads hz'
  have haz : a < z.length := by rw [hlen]; exact ha
  have hbz : b < z.length := by rw [hlen]; exact hb
  have haz' : a < z'.length := by rw [hlen']; exact ha
  have hbz' : b < z'.length := by rw [hlen']; exact hb
  have hdist : ∀ {s t : Nat}, s < d → t < d → s ≠ t →
      ground.getAt 0 z' s ≠ ground.getAt 0 z' t :=
    fun hs ht hst => arr_getAt_ne hz' hs ht hst
  -- the value at z'’s place a sits in z at a or at b
  have hplace : ∀ {v : Nat}, 0 < ground.countOf v z' →
      ∀ {s : Nat}, s < d → ground.getAt 0 z' s = v →
      ground.getAt 0 z (posOf v z) = v ∧ posOf v z < d ∧
        (posOf v z ≠ a → posOf v z ≠ b → posOf v z = s) := by
    intro v hv s hs hsv
    obtain ⟨hv1, hvd⟩ := hent' v hv
    have hvz : 0 < ground.countOf v z := by
      rw [hval v hv1 hvd]
      exact Nat.succ_pos 0
    have hget := getAt_posOf v z hvz
    have hlt : posOf v z < z.length := posOf_lt v z hvz
    have hltd : posOf v z < d := by rw [← hlen]; exact hlt
    refine ⟨hget, hltd, fun hpa hpb => ?_⟩
    have hz'p : ground.getAt 0 z' (posOf v z) = v := by
      rw [hoff _ hltd hpa hpb]
      exact hget
    by_cases hps : posOf v z = s
    · exact hps
    · exact absurd (hz'p.trans hsv.symm)
        (hdist hltd hs hps)
  have hva' : 0 < ground.countOf (ground.getAt 0 z' a) z' :=
    countOf_getAt_pos 0 z' a haz'
  have hvb' : 0 < ground.countOf (ground.getAt 0 z' b) z' :=
    countOf_getAt_pos 0 z' b hbz'
  obtain ⟨hgeta, hlta, hposa⟩ := hplace hva' ha rfl
  obtain ⟨hgetb, hltb, hposb⟩ := hplace hvb' hb rfl
  by_cases hpa : posOf (ground.getAt 0 z' a) z = a
  · -- z'’s a-value sits at a in z: agreement, and b follows
    have hzz'a : ground.getAt 0 z a = ground.getAt 0 z' a := by
      rw [hpa] at hgeta
      exact hgeta
    have hbb : ground.getAt 0 z b = ground.getAt 0 z' b := by
      by_cases hpb : posOf (ground.getAt 0 z' b) z = b
      · rw [hpb] at hgetb
        exact hgetb
      · by_cases hpb' : posOf (ground.getAt 0 z' b) z = a
        · have h2 : ground.getAt 0 z a = ground.getAt 0 z' b := by
            rw [hpb'] at hgetb
            exact hgetb
          exact absurd (h2.symm.trans hzz'a)
            (hdist hb ha (fun he => hne he.symm))
        · exact absurd (hposb hpb' hpb) hpb
    refine .inl (ground.getAt_ext 0 z' z (by rw [hlen, hlen']) ?_)
    intro t ht
    have htd : t < d := by rw [← hlen']; exact ht
    by_cases hta : t = a
    · rw [hta, hzz'a]
    · by_cases htb : t = b
      · rw [htb, hbb]
      · exact hoff t htd hta htb
  · -- z'’s a-value sits at b in z: the exchange
    have hpab : posOf (ground.getAt 0 z' a) z = b := by
      by_cases hpb : posOf (ground.getAt 0 z' a) z = b
      · exact hpb
      · exact absurd (hposa hpa hpb) hpa
    have hzb : ground.getAt 0 z b = ground.getAt 0 z' a := by
      rw [hpab] at hgeta
      exact hgeta
    have hza : ground.getAt 0 z a = ground.getAt 0 z' b := by
      by_cases hpb : posOf (ground.getAt 0 z' b) z = a
      · rw [hpb] at hgetb
        exact hgetb
      · by_cases hpb' : posOf (ground.getAt 0 z' b) z = b
        · have h2 : ground.getAt 0 z b = ground.getAt 0 z' b := by
            rw [hpb'] at hgetb
            exact hgetb
          exact absurd ((hzb.symm.trans h2))
            (hdist ha hb hne)
        · exact absurd (hposb hpb hpb') hpb'
  -- close on the swap
    refine .inr (ground.getAt_ext 0 z' (swapPair a b z) ?_ ?_)
    · rw [length_swapPair, hlen, hlen']
    · intro t ht
      have htd : t < d := by rw [← hlen']; exact ht
      by_cases hta : t = a
      · rw [hta, getAt_swapPair_fst z hne haz hbz, ← hzb]
      · by_cases htb : t = b
        · rw [htb, getAt_swapPair_snd z hne haz hbz, ← hza]
        · rw [getAt_swapPair_ne z haz hbz hta htb]
          exact hoff t htd hta htb

/-! The half-line evaluation (`thm:weylchar`'s assembly): the monic
descent opens at the key itself, one head read per variable beyond
the letter with the swapped cofactors moving the letter strictly —
`cofAt`'s fold splits as the head read at the bumped key against
the line fold over the moved keys — and a line fold reads its
arrangements alone: at a display key the swapped display at the
order's read, off the displays the balanced pairs within the fold
or the one-sided hit's own graded unit. -/

private theorem mapRangeDistinct (n : Nat) :
    ground.distinctList ((List.range n).map (fun l => l + 1)) :=
  fun s _ => by
    rw [ground.countOf_shiftRange s n]
    by_cases h : 1 ≤ s ∧ s ≤ n
    · rw [if_pos h]
      exact Nat.le_refl 1
    · rw [if_neg h]
      exact Nat.zero_le 1

private theorem mapRangeMem {s n : Nat}
    (h : 0 < ground.countOf s ((List.range n).map (fun l => l + 1))) :
    1 ≤ s ∧ s ≤ n := by
  rw [ground.countOf_shiftRange s n] at h
  by_cases hc : 1 ≤ s ∧ s ≤ n
  · exact hc
  · rw [if_neg hc] at h
    exact absurd h (Nat.lt_irrefl 0)

private theorem mapRangeOcc {s n : Nat} (h1 : 1 ≤ s) (h2 : s ≤ n) :
    0 < ground.countOf s ((List.range n).map (fun l => l + 1)) := by
  rw [ground.countOf_shiftRange s n, if_pos ⟨h1, h2⟩]
  exact Nat.lt_succ_self 0

/-- The fold concentrates at one member: every further member's
read the count's unit. -/
private theorem foldConc (F : Nat → Nat) :
    ∀ (l : List Nat) (x : Nat), ground.countOf x l = 1 →
      (∀ y, 0 < ground.countOf y l → y ≠ x → F y = 0) →
      ground.famFold Nat.add 0 F l = F x :=
  fun l x hx hz => by
    rw [ground.famFold_congr_members Nat.add 0 F
      (fun w => if w = x then F w else 0) l
      (fun y hy => by
        by_cases hyx : y = x
        · rw [if_pos hyx]
        · rw [if_neg hyx, hz y hy hyx])]
    exact ground.famFold_pick F x l hx

/-- The graded counts at a transposed key in either place order. -/
private theorem sideCount_swapAny (d : Nat) (beta y : List Nat)
    {i j : Nat} (hne : i ≠ j) (hi : i < d) (hj : j < d)
    (side : Bool) :
    sideCount d beta (swapPair i j y) side
      = sideCount d beta y (!side) := by
  match Nat.lt_or_ge i j with
  | .inl hij => exact sideCount_swapKey d beta y hij hj side
  | .inr hge =>
    have hji : j < i := Nat.lt_of_le_of_ne hge
      (fun he => hne he.symm)
    rw [swapPair_comm i j y]
    exact sideCount_swapKey d beta y hji hi side

/-- The arrangement test reads the length and the counts alone. -/
private theorem arrB_congr {d : Nat} {z z' : List Nat}
    (hl : z'.length = z.length)
    (hc : ∀ v, ground.countOf v z' = ground.countOf v z) :
    arrB d z' = arrB d z := by
  cases harr : arrB d z with
  | true =>
    obtain ⟨hlen, hent, hval⟩ := arr_reads harr
    exact arr_make (hl.trans hlen)
      (fun v hv => hent v (by rw [← hc v]; exact hv))
      (fun v h1 h2 => (hc v).trans (hval v h1 h2))
  | false =>
    cases harr' : arrB d z' with
    | true =>
      obtain ⟨hlen', hent', hval'⟩ := arr_reads harr'
      have : arrB d z = true :=
        arr_make (hl.symm.trans hlen')
          (fun v hv => hent' v (by rw [hc v]; exact hv))
          (fun v h1 h2 => (hc v).symm.trans (hval' v h1 h2))
      exact absurd (harr.symm.trans this)
        (fun he => Bool.noConfusion he)
    | false => rfl

private theorem arrB_swapPair (d i j : Nat) (z : List Nat) :
    arrB d (swapPair i j z) = arrB d z :=
  arrB_congr (length_swapPair i j z)
    (fun v => countOf_swapPair v i j z)

/-- The moved key at the co-filling's shift is the moved key's
value exchange: the line's two fillings. -/
private theorem moveBy_swap {up down : Nat} (hne : up ≠ down)
    {kappa : List Nat} (hu : up < kappa.length)
    (hd : down < kappa.length) {s : Nat}
    (hs : ground.getAt 0 kappa up + s ≤ ground.getAt 0 kappa down) :
    moveBy up down
        ((ground.getAt 0 kappa down - s) - ground.getAt 0 kappa up)
        kappa
      = swapPair up down (moveBy up down s kappa) := by
  have hles : ground.getAt 0 kappa up
      ≤ ground.getAt 0 kappa down - s := by
    refine leCancelL s ?_
    rw [Nat.add_comm s (ground.getAt 0 kappa up),
      Nat.add_comm s (ground.getAt 0 kappa down - s),
      subAdd (Nat.le_trans (Nat.le_add_left s _) hs)]
    exact hs
  have hmu : up < (moveBy up down s kappa).length := by
    rw [length_moveBy]
    exact hu
  have hmd : down < (moveBy up down s kappa).length := by
    rw [length_moveBy]
    exact hd
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [length_moveBy, length_swapPair, length_moveBy]
  · intro t ht
    rw [length_moveBy] at ht
    by_cases htu : t = up
    · rw [htu, getAt_moveBy_fst hne _ kappa hu,
        getAt_swapPair_fst _ hne hmu hmd,
        getAt_moveBy_snd up hne s kappa hd,
        Nat.add_comm (ground.getAt 0 kappa up) _,
        subAdd hles]
    · by_cases htd : t = down
      · rw [htd, getAt_moveBy_snd up hne _ kappa hd,
          getAt_swapPair_snd _ hne hmu hmd,
          getAt_moveBy_fst hne s kappa hu,
          ground.subSub (ground.getAt 0 kappa down) s
            (ground.getAt 0 kappa up),
          natSubSubCancel _ _ (by
            rw [Nat.add_comm s (ground.getAt 0 kappa up)]
            exact hs)]
        exact Nat.add_comm s (ground.getAt 0 kappa up)
      · rw [getAt_moveBy_ne up down _ kappa htu htd,
          getAt_swapPair_ne _ hmu hmd htu htd,
          getAt_moveBy_ne up down s kappa htu htd]

/-- The line fold at a place pair: the graded counts at the moved
keys, the shifts through the down place's count — the swapped
cofactor's moved reads at the alternant's clearing. -/
private def lineFold (up down d : Nat) (kappa : List Nat)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun s => sideCount d (unitDisp d) (moveBy up down s kappa) side)
    ((List.range (ground.getAt 0 kappa down)).map (fun s => s + 1))

private theorem cofKey (a b : Nat) (hab : a ≠ b) (l : Nat)
    (w : List Nat) :
    ground.editAt (fun x => x + (l + 1)) a (ground.editAt (fun x => x - l) b w)
      = moveBy a b l (ground.bumpAt a w) := by
  show _ = ground.editAt (fun x => x + l) a
    (ground.editAt (fun x => x - l) b (ground.bumpAt a w))
  rw [bumpAt_editAt a w,
    ground.editAt_comm (fun x => x - l) (fun x => x + 1) b a w
      (fun he => hab he.symm),
    ground.editAt_fuse (fun x => x + l) (fun x => x + 1) a
      (ground.editAt (fun x => x - l) b w),
    ground.editAt_congr (fun x => x + 1 + l) (fun x => x + (l + 1))
      (fun x => by rw [Nat.add_assoc x 1 l, Nat.add_comm 1 l]) a
      (ground.editAt (fun x => x - l) b w)]

/-- The head split (`thm:weylchar`'s assembly, the monic descent
opening at the key itself): the cofactor's coefficient at a pair
beyond the letter reads the bumped key's own graded count against
the line fold at the moved keys. -/
private theorem cofAt_split {a b : Nat} (hab : a ≠ b) (d : Nat)
    (w : List Nat) (side : Bool) :
    cofAt a b d w side
      = sideCount d (unitDisp d) (ground.bumpAt a w) side
        + lineFold a b d (ground.bumpAt a w) side := by
  have hgb : ground.getAt 0 (ground.bumpAt a w) b
      = ground.getAt 0 w b := by
    exact ground.getAt_bumpAt_ne a w b
      (fun he => hab he.symm)
  show ground.famFold Nat.add 0
      (fun l => sideCount d (unitDisp d)
        (ground.editAt (fun x => x + (l + 1)) a
          (ground.editAt (fun x => x - l) b w)) side)
      (List.range (ground.getAt 0 w b + 1)) = _
  rw [← hgb,
    ground.famFold_congr_all Nat.add 0 _
      (fun l => sideCount d (unitDisp d)
        (moveBy a b l (ground.bumpAt a w)) side)
      (fun l => by rw [cofKey a b hab l w]) _,
    range_cons (ground.getAt 0 (ground.bumpAt a w) b)]
  show Nat.add
      (sideCount d (unitDisp d)
        (moveBy a b 0 (ground.bumpAt a w)) side)
      (ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
          (moveBy a b l (ground.bumpAt a w)) side)
        ((List.range (ground.getAt 0 (ground.bumpAt a w) b)).map
          (fun j => j + 1)))
    = _
  rw [moveBy_zero a b (ground.bumpAt a w)]
  rfl

/-- The strictly moved half (`thm:weylchar`'s assembly, the swapped
cofactors moving the letter strictly): the cofactor's coefficient
at a pair below the letter is the line fold whole, the bumped key
off the moved keys. -/
private theorem cofAt_line (b a d : Nat)
    (w : List Nat) (ha : a < w.length) (side : Bool) :
    cofAt b a d w side
      = lineFold b a d (ground.bumpAt a w) side := by
  have hga : ground.getAt 0 (ground.bumpAt a w) a
      = ground.getAt 0 w a + 1 := by
    exact ground.getAt_bumpAt_self a w ha
  show ground.famFold Nat.add 0
      (fun l => sideCount d (unitDisp d)
        (ground.editAt (fun x => x + (l + 1)) b
          (ground.editAt (fun x => x - l) a w)) side)
      (List.range (ground.getAt 0 w a + 1)) = _
  have hkey : ∀ l : Nat,
      ground.editAt (fun x => x + (l + 1)) b (ground.editAt (fun x => x - l) a w)
        = moveBy b a (l + 1) (ground.bumpAt a w) := by
    intro l
    show _ = ground.editAt (fun x => x + (l + 1)) b
      (ground.editAt (fun x => x - (l + 1)) a (ground.bumpAt a w))
    rw [bumpAt_editAt a w,
      ground.editAt_fuse (fun x => x - (l + 1)) (fun x => x + 1) a w,
      ground.editAt_congr (fun x => x + 1 - (l + 1)) (fun x => x - l)
        (fun x => Nat.succ_sub_succ x l) a w]
  rw [ground.famFold_congr_all Nat.add 0 _
      (fun l => sideCount d (unitDisp d)
        (moveBy b a (l + 1) (ground.bumpAt a w)) side)
      (fun l => by rw [hkey l]) _]
  show _ = ground.famFold Nat.add 0
    (fun s => sideCount d (unitDisp d)
      (moveBy b a s (ground.bumpAt a w)) side)
    ((List.range (ground.getAt 0 (ground.bumpAt a w) a)).map
      (fun s => s + 1))
  rw [hga,
    ground.famFold_map Nat.add 0
      (fun s => sideCount d (unitDisp d)
        (moveBy b a s (ground.bumpAt a w)) side)
      (fun s => s + 1) (List.range (ground.getAt 0 w a + 1))]

/-- The line's within-fold pairing device: a hit's shift read to
its co-filling's, the further shifts kept. -/
private def lineInv (up down d : Nat) (kappa : List Nat)
    (s : Nat) : Nat :=
  if arrB d (moveBy up down s kappa) = true
  then ground.getAt 0 kappa down - s - ground.getAt 0 kappa up
  else s

private theorem lineInv_hit {up down d : Nat} {kappa : List Nat}
    {s : Nat} (harr : arrB d (moveBy up down s kappa) = true) :
    lineInv up down d kappa s
      = ground.getAt 0 kappa down - s - ground.getAt 0 kappa up :=
  if_pos harr

private theorem lineInv_miss {up down d : Nat} {kappa : List Nat}
    {s : Nat} (harr : arrB d (moveBy up down s kappa) = false) :
    lineInv up down d kappa s = s :=
  if_neg (fun hc => Bool.noConfusion (harr.symm.trans hc))

/-- The fixed letter's balance (`thm:weylchar`'s assembly, a line
matched at both fillings): at every hit's co-filling among the
moved keys, the line fold reads equal members — the two
arrangements join at the exchanged grading within their own
fold. -/
private theorem lineFold_bal {d up down : Nat} (hne : up ≠ down)
    (hup : up < d) (hdown : down < d) {kappa : List Nat}
    (hlen : kappa.length = d)
    (hall : ∀ s, 1 ≤ s → s ≤ ground.getAt 0 kappa down →
      arrB d (moveBy up down s kappa) = true →
      ground.getAt 0 kappa up + s < ground.getAt 0 kappa down)
    (side : Bool) :
    lineFold up down d kappa side
      = lineFold up down d kappa (!side) := by
  have huk : up < kappa.length := by rw [hlen]; exact hup
  have hdk : down < kappa.length := by rw [hlen]; exact hdown
  have hco : ∀ {s : Nat}, 1 ≤ s →
      s ≤ ground.getAt 0 kappa down →
      arrB d (moveBy up down s kappa) = true →
      (1 ≤ ground.getAt 0 kappa down - s
          - ground.getAt 0 kappa up
        ∧ ground.getAt 0 kappa down - s - ground.getAt 0 kappa up
          ≤ ground.getAt 0 kappa down)
        ∧ moveBy up down
            (ground.getAt 0 kappa down - s
              - ground.getAt 0 kappa up) kappa
          = swapPair up down (moveBy up down s kappa) := by
    intro s h1 h2 harr
    have hstrict := hall s h1 h2 harr
    have hle : ground.getAt 0 kappa up + s
        ≤ ground.getAt 0 kappa down := Nat.le_of_lt hstrict
    refine ⟨⟨?_, Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)⟩,
      moveBy_swap hne huk hdk hle⟩
    rw [ground.subSub (ground.getAt 0 kappa down) s
        (ground.getAt 0 kappa up)]
    refine subPos ?_
    rw [Nat.add_comm s (ground.getAt 0 kappa up)]
    exact hstrict
  have hcoco : ∀ {s : Nat}, 1 ≤ s →
      s ≤ ground.getAt 0 kappa down →
      arrB d (moveBy up down s kappa) = true →
      ground.getAt 0 kappa down
          - (ground.getAt 0 kappa down - s
            - ground.getAt 0 kappa up)
          - ground.getAt 0 kappa up
        = s := by
    intro s h1 h2 harr
    have hle : s + ground.getAt 0 kappa up
        ≤ ground.getAt 0 kappa down := by
      rw [Nat.add_comm s (ground.getAt 0 kappa up)]
      exact Nat.le_of_lt (hall s h1 h2 harr)
    rw [ground.subSub (ground.getAt 0 kappa down) s
        (ground.getAt 0 kappa up),
      natSubSubCancel _ _ hle]
    exact addSubSelfR s (ground.getAt 0 kappa up)
  have hmem : ∀ s, 0 < ground.countOf s
      ((List.range (ground.getAt 0 kappa down)).map
        (fun s => s + 1)) →
      0 < ground.countOf (lineInv up down d kappa s)
        ((List.range (ground.getAt 0 kappa down)).map
          (fun s => s + 1)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := mapRangeMem hs
    cases harr : arrB d (moveBy up down s kappa) with
    | true =>
      rw [lineInv_hit harr]
      obtain ⟨⟨hc1, hc2⟩, _⟩ := hco h1 h2 harr
      exact mapRangeOcc hc1 hc2
    | false =>
      rw [lineInv_miss harr]
      exact hs
  have hinv : ∀ s, 0 < ground.countOf s
      ((List.range (ground.getAt 0 kappa down)).map
        (fun s => s + 1)) →
      lineInv up down d kappa (lineInv up down d kappa s) = s := by
    intro s hs
    obtain ⟨h1, h2⟩ := mapRangeMem hs
    cases harr : arrB d (moveBy up down s kappa) with
    | true =>
      rw [lineInv_hit harr]
      obtain ⟨⟨hc1, hc2⟩, hkey⟩ := hco h1 h2 harr
      have harr' : arrB d (moveBy up down
          (ground.getAt 0 kappa down - s
            - ground.getAt 0 kappa up) kappa) = true := by
        rw [hkey, arrB_swapPair]
        exact harr
      rw [lineInv_hit harr']
      exact hcoco h1 h2 harr
    | false =>
      rw [lineInv_miss harr, lineInv_miss harr]
  show ground.famFold Nat.add 0
      (fun s => sideCount d (unitDisp d) (moveBy up down s kappa)
        side)
      ((List.range (ground.getAt 0 kappa down)).map
        (fun s => s + 1)) = _
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun s => sideCount d (unitDisp d) (moveBy up down s kappa)
      side)
    (l := (List.range (ground.getAt 0 kappa down)).map
      (fun s => s + 1))
    (g := lineInv up down d kappa) (h := lineInv up down d kappa)
    (mapRangeDistinct _) hinv hinv hmem hmem]
  refine ground.famFold_congr_members Nat.add 0 _ _ _
    (fun s hs => ?_)
  obtain ⟨h1, h2⟩ := mapRangeMem hs
  cases harr : arrB d (moveBy up down s kappa) with
  | true =>
    obtain ⟨_, hkey⟩ := hco h1 h2 harr
    show sideCount d (unitDisp d)
        (moveBy up down (lineInv up down d kappa s) kappa) side = _
    rw [lineInv_hit harr, hkey,
      sideCount_swapAny d (unitDisp d) (moveBy up down s kappa)
        hne hup hdown side]
  | false =>
    show sideCount d (unitDisp d)
        (moveBy up down (lineInv up down d kappa s) kappa) side = _
    rw [lineInv_miss harr, sideCount_off harr side,
      sideCount_off harr (!side)]

/-- The one-sided hit's read (`thm:weylchar`'s assembly): at a hit
whose co-filling sits off the moved keys, the line fold
concentrates on the one arrangement, its own graded unit at the
hit's side. -/
private theorem lineFold_single {d up down : Nat} (hne : up ≠ down)
    (hup : up < d) (hdown : down < d) {kappa : List Nat}
    {s0 : Nat} (hs1 : 1 ≤ s0)
    (hs2 : s0 ≤ ground.getAt 0 kappa down)
    (hhit : arrB d (moveBy up down s0 kappa) = true)
    (hone : ground.getAt 0 kappa down
      ≤ ground.getAt 0 kappa up + s0)
    (side : Bool) :
    lineFold up down d kappa side
      = if side = parity (permOf d (moveBy up down s0 kappa))
        then 1 else 0 := by
  obtain ⟨hmlen, _, _⟩ := arr_reads hhit
  have hlen : kappa.length = d := by
    rw [← length_moveBy up down s0 kappa]
    exact hmlen
  have huk : up < kappa.length := by rw [hlen]; exact hup
  have hdk : down < kappa.length := by rw [hlen]; exact hdown
  have hzero : ∀ y, 0 < ground.countOf y
      ((List.range (ground.getAt 0 kappa down)).map
        (fun s => s + 1)) → y ≠ s0 →
      sideCount d (unitDisp d) (moveBy up down y kappa) side
        = 0 := by
    intro y hy hys
    obtain ⟨hy1, hy2⟩ := mapRangeMem hy
    cases harr : arrB d (moveBy up down y kappa) with
    | false => exact sideCount_off harr side
    | true =>
      have hagree : ∀ t, t < d → t ≠ up → t ≠ down →
          ground.getAt 0 (moveBy up down y kappa) t
            = ground.getAt 0 (moveBy up down s0 kappa) t := by
        intro t _ htu htd
        rw [getAt_moveBy_ne up down y kappa htu htd,
          getAt_moveBy_ne up down s0 kappa htu htd]
      match arr_two hne hup hdown hhit harr hagree with
      | .inl heq =>
        have h2 : ground.getAt 0 kappa up + y
            = ground.getAt 0 kappa up + s0 := by
          rw [← getAt_moveBy_fst hne y kappa huk, heq,
            getAt_moveBy_fst hne s0 kappa huk]
        exact absurd (addCancelL _ h2) hys
      | .inr hswap =>
        have hmu : up < (moveBy up down s0 kappa).length := by
          rw [length_moveBy]
          exact huk
        have hmd : down < (moveBy up down s0 kappa).length := by
          rw [length_moveBy]
          exact hdk
        have h2 : ground.getAt 0 kappa up + y
            = ground.getAt 0 kappa down - s0 := by
          rw [← getAt_moveBy_fst hne y kappa huk, hswap,
            getAt_swapPair_fst _ hne hmu hmd,
            getAt_moveBy_snd up hne s0 kappa hdk]
        have h3 : ground.getAt 0 kappa down - s0
            ≤ ground.getAt 0 kappa up := by
          have h4 := Nat.sub_le_sub_right hone s0
          rw [addSubSelfR (ground.getAt 0 kappa up) s0] at h4
          exact h4
        have h5 : ground.getAt 0 kappa up + y
            ≤ ground.getAt 0 kappa up := by
          rw [h2]
          exact h3
        have h6 : ground.getAt 0 kappa up + 1
            ≤ ground.getAt 0 kappa up + y :=
          Nat.add_le_add_left hy1 _
        exact absurd (Nat.le_trans h6 h5)
          (Nat.not_succ_le_self _)
  show ground.famFold Nat.add 0
      (fun s => sideCount d (unitDisp d) (moveBy up down s kappa)
        side)
      ((List.range (ground.getAt 0 kappa down)).map
        (fun s => s + 1)) = _
  rw [foldConc _ _ s0
      (by rw [ground.countOf_shiftRange, if_pos ⟨hs1, hs2⟩]) hzero,
    sideCount_arr hhit side]

/-- The line fold at a display key (`thm:weylchar`'s assembly, the
line's two arrangements at a display): the moved keys read the
swapped display alone, at the order's read of the pair's places —
one graded unit at the exchanged grading where the up place reads
below the down place, the count's unit otherwise. -/
private theorem lineFold_disp {d up down : Nat} (hne : up ≠ down)
    (hup : up < d) (hdown : down < d) {kappa : List Nat}
    (hk : arrB d kappa = true) (side : Bool) :
    lineFold up down d kappa side
      = if ground.getAt 0 kappa up < ground.getAt 0 kappa down then
          (if side = !(parity (permOf d kappa)) then 1 else 0)
        else 0 := by
  obtain ⟨hlen, _, _⟩ := arr_reads hk
  have huk : up < kappa.length := by rw [hlen]; exact hup
  have hdk : down < kappa.length := by rw [hlen]; exact hdown
  have hzero : ∀ s, 0 < ground.countOf s
      ((List.range (ground.getAt 0 kappa down)).map
        (fun s => s + 1)) →
      ¬ (ground.getAt 0 kappa up + s = ground.getAt 0 kappa down) →
      sideCount d (unitDisp d) (moveBy up down s kappa) side
        = 0 := by
    intro s hs hns
    obtain ⟨hs1, hs2⟩ := mapRangeMem hs
    cases harr : arrB d (moveBy up down s kappa) with
    | false => exact sideCount_off harr side
    | true =>
      have hcase := arr_two hne hup hdown hk harr
        (fun t htd htu htdn => getAt_moveBy_ne up down s kappa
          htu htdn)
      match hcase with
      | .inl heq =>
        have h2 : ground.getAt 0 kappa up + s
            = ground.getAt 0 kappa up := by
          rw [← getAt_moveBy_fst hne s kappa huk, heq]
        have h3 : s = 0 :=
          addCancelL (ground.getAt 0 kappa up)
            (h2.trans (Nat.add_zero _).symm)
        rw [h3] at hs1
        exact absurd hs1 (Nat.not_succ_le_zero 0)
      | .inr hswap =>
        have h2 : ground.getAt 0 kappa up + s
            = ground.getAt 0 kappa down := by
          rw [← getAt_moveBy_fst hne s kappa huk, hswap,
            getAt_swapPair_fst kappa hne huk hdk]
        exact absurd h2 hns
  by_cases hlt : ground.getAt 0 kappa up < ground.getAt 0 kappa down
  · rw [if_pos hlt]
    have hgap : ground.getAt 0 kappa up
        + (ground.getAt 0 kappa down - ground.getAt 0 kappa up)
        = ground.getAt 0 kappa down := by
      rw [Nat.add_comm]
      exact subAdd (Nat.le_of_lt hlt)
    have hs1 : 1 ≤ ground.getAt 0 kappa down
        - ground.getAt 0 kappa up := by
      refine subPos hlt
    have hs2 : ground.getAt 0 kappa down - ground.getAt 0 kappa up
        ≤ ground.getAt 0 kappa down := Nat.sub_le _ _
    have hkey : moveBy up down
        (ground.getAt 0 kappa down - ground.getAt 0 kappa up)
        kappa = swapPair up down kappa := by
      have h0 := moveBy_swap hne huk hdk
        (s := 0) (by rw [Nat.add_zero]; exact Nat.le_of_lt hlt)
      rw [moveBy_zero up down kappa] at h0
      have h2 : ground.getAt 0 kappa down - 0
          - ground.getAt 0 kappa up
          = ground.getAt 0 kappa down - ground.getAt 0 kappa up :=
        rfl
      rw [h2] at h0
      exact h0
    have hcount : ground.countOf
        (ground.getAt 0 kappa down - ground.getAt 0 kappa up)
        ((List.range (ground.getAt 0 kappa down)).map
          (fun s => s + 1)) = 1 := by
      rw [ground.countOf_shiftRange, if_pos ⟨hs1, hs2⟩]
    show ground.famFold Nat.add 0 _ _ = _
    rw [foldConc _ _ _ hcount (fun y hy hyne =>
      hzero y hy (fun hc => hyne (by
        have h3 : ground.getAt 0 kappa up + y
            = ground.getAt 0 kappa up
              + (ground.getAt 0 kappa down
                - ground.getAt 0 kappa up) := by
          rw [hgap]
          exact hc
        exact addCancelL (ground.getAt 0 kappa up) h3))),
      hkey,
      sideCount_swapAny d (unitDisp d) kappa hne hup hdown side,
      sideCount_arr hk (!side)]
    by_cases hsp : side = !(parity (permOf d kappa))
    · rw [if_pos hsp, if_pos (not_shift.mp hsp.symm).symm]
    · rw [if_neg hsp,
        if_neg (fun hc => hsp (not_shift.mpr hc.symm).symm)]
  · rw [if_neg hlt]
    show ground.famFold Nat.add 0 _ _ = 0
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun _ => (0 : Nat)) _ (fun s hs =>
          hzero s hs (fun hc => by
            obtain ⟨hs1, _⟩ := mapRangeMem hs
            have h2 : ground.getAt 0 kappa up
                < ground.getAt 0 kappa down := by
              rw [← hc]
              exact Nat.add_lt_add_left hs1 _
            exact hlt h2)),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]

/-! The value's places split (`thm:weylchar`'s assembly, the
displayed identity at an arrangement): the letter's value against
the further places' comparisons — the value's rank read over the
places' trichotomy, the count of the values below the letter's. -/

/-- The place fold reads the value fold: the count of places below
a bound is the fold of the value counts below it. -/
private theorem valueFold (V : Nat) :
    ∀ z : List Nat,
      ground.famFold Nat.add 0
        (fun j => if ground.getAt 0 z j < V then (1 : Nat) else 0)
        (List.range z.length)
      = ground.famFold Nat.add 0
          (fun v => ground.countOf v z) (List.range V) :=
  fun z => (ground.countBelow_index V z).symm.trans
    (ground.countBelow_sum V z)

/-- The rank read at an arrangement: a window value exceeds the
count of the places reading below it by one — the values below the
letter's are the window's own, each at one place. -/
private theorem arr_rank {d : Nat} {kappa : List Nat}
    (hk : arrB d kappa = true) {V : Nat} (hV1 : 1 ≤ V)
    (hVd : V ≤ d) :
    1 + ground.famFold Nat.add 0
        (fun j => if ground.getAt 0 kappa j < V then (1 : Nat)
          else 0)
        (List.range d)
      = V := by
  obtain ⟨hlen, hent, hval⟩ := arr_reads hk
  rw [← hlen, valueFold V kappa]
  match V, hV1, hVd with
  | V' + 1, _, hVd =>
    rw [range_cons V']
    show 1 + Nat.add (ground.countOf 0 kappa)
      (ground.famFold Nat.add 0
        (fun v => ground.countOf v kappa)
        ((List.range V').map (fun v => v + 1))) = V' + 1
    have hzero : ground.countOf 0 kappa = 0 := by
      match Nat.eq_zero_or_pos (ground.countOf 0 kappa) with
      | .inl h0 => exact h0
      | .inr hpos =>
        exact absurd (hent 0 hpos).1 (Nat.not_succ_le_zero 0)
    have hones : ground.famFold Nat.add 0
        (fun v => ground.countOf v kappa)
        ((List.range V').map (fun v => v + 1)) = V' := by
      rw [ground.famFold_map Nat.add 0
          (fun v => ground.countOf v kappa) (fun v => v + 1)
          (List.range V'),
        ground.famFold_congr_members Nat.add 0 _
          (fun _ => (1 : Nat))
          (List.range V') (fun v hv => hval (v + 1)
            (Nat.succ_le_succ (Nat.zero_le v))
            (Nat.le_trans (Nat.succ_le_succ
              (Nat.le_of_lt (ground.ltOfMem hv))) hVd)),
        ground.famFold_length, length_range]
    rw [hzero, hones]
    show 1 + (0 + V') = V' + 1
    rw [Nat.zero_add, Nat.add_comm 1 V']

/-- The further places beyond a letter, counted: the join at the
letter's successor. -/
private theorem rangeSplitGt : ∀ (d i : Nat), i < d →
    (i + 1) + ground.famFold Nat.add 0
        (fun j => if i < j then (1 : Nat) else 0) (List.range d)
      = d
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | n + 1, i, h => by
    rw [range_cons n]
    show (i + 1) + Nat.add (if i < 0 then (1 : Nat) else 0)
      (ground.famFold Nat.add 0
        (fun j => if i < j then (1 : Nat) else 0)
        ((List.range n).map (fun j => j + 1))) = n + 1
    rw [if_neg (Nat.not_lt_zero i),
      ground.famFold_map Nat.add 0
        (fun j => if i < j then (1 : Nat) else 0)
        (fun j => j + 1) (List.range n)]
    match i with
    | 0 =>
      rw [ground.famFold_congr_all Nat.add 0
          (fun j => if 0 < j + 1 then (1 : Nat) else 0)
          (fun _ => (1 : Nat))
          (fun j => if_pos (Nat.succ_pos j)) (List.range n),
        ground.famFold_length, length_range]
      show 1 + (0 + n) = n + 1
      rw [Nat.zero_add, Nat.add_comm 1 n]
    | i' + 1 =>
      have hin : i' < n := Nat.lt_of_succ_lt_succ h
      rw [ground.famFold_congr_all Nat.add 0
          (fun j => if i' + 1 < j + 1 then (1 : Nat) else 0)
          (fun j => if i' < j then (1 : Nat) else 0)
          (fun j => by
            by_cases hij : i' < j
            · rw [if_pos hij, if_pos (Nat.succ_lt_succ hij)]
            · rw [if_neg hij,
                if_neg (fun hc => hij (Nat.lt_of_succ_lt_succ hc))])
          (List.range n)]
      have hIH := rangeSplitGt n i' hin
      show (i' + 1 + 1)
        + (0 + ground.famFold Nat.add 0
            (fun j => if i' < j then (1 : Nat) else 0)
            (List.range n)) = n + 1
      rw [Nat.zero_add, Nat.add_assoc (i' + 1) 1
          (ground.famFold Nat.add 0
            (fun j => if i' < j then (1 : Nat) else 0)
            (List.range n)),
        Nat.add_comm 1 (ground.famFold Nat.add 0
          (fun j => if i' < j then (1 : Nat) else 0)
          (List.range n)),
        ← Nat.add_assoc (i' + 1) (ground.famFold Nat.add 0
          (fun j => if i' < j then (1 : Nat) else 0)
          (List.range n)) 1,
        hIH]

/-- The letter's rising comparisons beyond it, the split's first
count. -/
def upFold (i d : Nat) (kappa : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun j => if i < j then
      (if ground.getAt 0 kappa i < ground.getAt 0 kappa j
        then (1 : Nat) else 0)
      else 0)
    (List.range d)

/-- The letter's falling comparisons below it, the split's second
count. -/
def downFold (i d : Nat) (kappa : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun j => if j < i then
      (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
        then (1 : Nat) else 0)
      else 0)
    (List.range d)

/-- The value's places split (`thm:weylchar`'s assembly display):
at an arrangement, the letter's value with its rising comparisons
beyond the letter joins the count with the falling comparisons
below it — the value's rank read against the places'
trichotomy. -/
theorem placesSplit {d i : Nat} (hid : i < d) {kappa : List Nat}
    (hk : arrB d kappa = true) :
    i + (ground.getAt 0 kappa i + upFold i d kappa)
      = d + downFold i d kappa := by
  obtain ⟨hlen, hent, hval⟩ := arr_reads hk
  have hiv : 1 ≤ ground.getAt 0 kappa i
      ∧ ground.getAt 0 kappa i ≤ d :=
    hent _ (countOf_getAt_pos 0 kappa i (by rw [hlen]; exact hid))
  have hbelow : ground.famFold Nat.add 0
      (fun j => if ground.getAt 0 kappa j < ground.getAt 0 kappa i
        then (1 : Nat) else 0)
      (List.range d)
    = downFold i d kappa
      + ground.famFold Nat.add 0
        (fun j => if i < j then
          (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
            then (1 : Nat) else 0)
          else 0)
        (List.range d) := by
    rw [ground.famFold_congr_all Nat.add 0 _
        (fun j => (if j < i then
            (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
              then (1 : Nat) else 0) else 0)
          + (if i < j then
            (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
              then (1 : Nat) else 0) else 0))
        (fun j => by
          by_cases hji : j < i
          · rw [if_pos hji,
              if_neg (fun hc : i < j => Nat.lt_irrefl i
                (Nat.lt_trans hc hji))]
            exact (Nat.add_zero _).symm
          · by_cases hij : i < j
            · rw [if_pos hij, if_neg hji]
              exact (Nat.zero_add _).symm
            · have hje : j = i := Nat.le_antisymm
                (Nat.le_of_not_lt hij) (Nat.le_of_not_lt hji)
              rw [hje,
                if_neg (Nat.lt_irrefl (ground.getAt 0 kappa i)),
                if_neg (Nat.lt_irrefl i)])
        (List.range d),
      famFold_add_split (fun j => if j < i then
          (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
            then (1 : Nat) else 0) else 0)
        (fun j => if i < j then
          (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
            then (1 : Nat) else 0) else 0)
        (List.range d)]
    rfl
  have hsplit : ground.famFold Nat.add 0
      (fun j => if i < j then (1 : Nat) else 0) (List.range d)
    = ground.famFold Nat.add 0
        (fun j => if i < j then
          (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
            then (1 : Nat) else 0)
          else 0)
        (List.range d)
      + upFold i d kappa := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun j => (if i < j then
            (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
              then (1 : Nat) else 0) else 0)
          + (if i < j then
            (if ground.getAt 0 kappa i < ground.getAt 0 kappa j
              then (1 : Nat) else 0) else 0))
        (List.range d)
        (fun j hj => by
          by_cases hij : i < j
          · rw [if_pos hij, if_pos hij, if_pos hij]
            have hne := arr_getAt_ne hk (ground.ltOfMem hj) hid
              (fun he => Nat.lt_irrefl i (he ▸ hij))
            match Nat.lt_or_ge (ground.getAt 0 kappa j)
              (ground.getAt 0 kappa i) with
            | .inl hlt =>
              rw [if_pos hlt,
                if_neg (fun hc => Nat.lt_irrefl _
                  (Nat.lt_trans hc hlt))]
            | .inr hge =>
              have hlt : ground.getAt 0 kappa i
                  < ground.getAt 0 kappa j :=
                Nat.lt_of_le_of_ne hge (fun he => hne he.symm)
              rw [if_pos hlt,
                if_neg (fun hc => Nat.lt_irrefl _
                  (Nat.lt_trans hc hlt))]
          · rw [if_neg hij, if_neg hij, if_neg hij]),
      famFold_add_split (fun j => if i < j then
          (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
            then (1 : Nat) else 0) else 0)
        (fun j => if i < j then
          (if ground.getAt 0 kappa i < ground.getAt 0 kappa j
            then (1 : Nat) else 0) else 0)
        (List.range d)]
    rfl
  have hshuffle : ∀ (I D L U : Nat),
      I + ((1 + (D + L)) + U) = ((I + 1) + (L + U)) + D := by
    intro I D L U
    rw [Nat.add_assoc 1 (D + L) U, Nat.add_assoc D L U,
      Nat.add_comm D (L + U),
      Nat.add_assoc (I + 1) (L + U) D,
      Nat.add_assoc I 1 ((L + U) + D)]
  have hrank := arr_rank hk hiv.1 hiv.2
  have hcount := rangeSplitGt d i hid
  rw [hbelow] at hrank
  rw [hsplit] at hcount
  rw [← hrank,
    hshuffle i (downFold i d kappa)
      (ground.famFold Nat.add 0
        (fun j => if i < j then
          (if ground.getAt 0 kappa j < ground.getAt 0 kappa i
            then (1 : Nat) else 0) else 0)
        (List.range d))
      (upFold i d kappa),
    hcount]

/-! The pairing involution (`thm:weylchar`'s assembly): at every
further key the lines' reads close in pairs — a line matched at
both fillings joins its two arrangements' reads at the exchanged
grading within its own fold, and at a one-sided hit the pair's
value in the key occupies a second place, whose line keeps the
hit's upper filling with its further filling at the receding value
below the letter's, one one-sided hit per partner line, an
involution off its own fixed points; the two hits' reads enter at
opposite members, the places' transposition exchanging the grading
at partner places on one side of the letter and the swapped
cofactor's memberwise exchange reading the join at places the
letter splits. -/

private theorem andFalse : ∀ {a b : Bool},
    (a && b) = false → a = true → b = false := by
  intro a b h ha
  cases b with
  | false => rfl
  | true =>
    rw [ha] at h
    exact absurd h (fun hh => Bool.noConfusion hh)

/-- The one-sided search along a line: the first shift reading an
arrangement whose co-filling sits off the moved keys. -/
private def oneGo (up down d : Nat) (kappa : List Nat) :
    Nat → Option Nat
  | 0 => none
  | s + 1 =>
    if (arrB d (moveBy up down (s + 1) kappa)
        && Nat.ble (ground.getAt 0 kappa down)
          (ground.getAt 0 kappa up + (s + 1))) = true
    then some (s + 1)
    else oneGo up down d kappa s

/-- The line's one-sided read, the search over the down place's
count. -/
private def oneHit (up down d : Nat) (kappa : List Nat) :
    Option Nat :=
  oneGo up down d kappa (ground.getAt 0 kappa down)

private theorem oneGo_some {up down d : Nat} {kappa : List Nat} :
    ∀ {n s : Nat}, oneGo up down d kappa n = some s →
      1 ≤ s ∧ s ≤ n
        ∧ arrB d (moveBy up down s kappa) = true
        ∧ ground.getAt 0 kappa down ≤ ground.getAt 0 kappa up + s
  | 0, _, h => nomatch h
  | m + 1, s, h => by
    have h' : (if (arrB d (moveBy up down (m + 1) kappa)
          && Nat.ble (ground.getAt 0 kappa down)
            (ground.getAt 0 kappa up + (m + 1))) = true
        then some (m + 1)
        else oneGo up down d kappa m) = some s := h
    by_cases hg : (arrB d (moveBy up down (m + 1) kappa)
        && Nat.ble (ground.getAt 0 kappa down)
          (ground.getAt 0 kappa up + (m + 1))) = true
    · rw [if_pos hg] at h'
      have hs : m + 1 = s := Option.some.inj h'
      obtain ⟨h1, h2⟩ := ground.andSplitB hg
      rw [← hs]
      exact ⟨Nat.succ_le_succ (Nat.zero_le m), Nat.le_refl (m + 1),
        h1, bleLe h2⟩
    · rw [if_neg hg] at h'
      obtain ⟨h1, h2, h3, h4⟩ := oneGo_some h'
      exact ⟨h1, Nat.le_succ_of_le h2, h3, h4⟩

private theorem oneGo_none {up down d : Nat} {kappa : List Nat} :
    ∀ {n : Nat}, oneGo up down d kappa n = none →
      ∀ s, 1 ≤ s → s ≤ n →
        arrB d (moveBy up down s kappa) = true →
        ground.getAt 0 kappa up + s < ground.getAt 0 kappa down
  | 0, _, s, hs1, hs2, _ => nomatch Nat.le_trans hs1 hs2
  | m + 1, h, s, hs1, hs2, harr => by
    have h' : (if (arrB d (moveBy up down (m + 1) kappa)
          && Nat.ble (ground.getAt 0 kappa down)
            (ground.getAt 0 kappa up + (m + 1))) = true
        then some (m + 1)
        else oneGo up down d kappa m) = none := h
    by_cases hg : (arrB d (moveBy up down (m + 1) kappa)
        && Nat.ble (ground.getAt 0 kappa down)
          (ground.getAt 0 kappa up + (m + 1))) = true
    · rw [if_pos hg] at h'
      exact nomatch h'
    · rw [if_neg hg] at h'
      match Nat.lt_or_ge s (m + 1) with
      | .inl hlt =>
        exact oneGo_none h' s hs1 (Nat.le_of_lt_succ hlt) harr
      | .inr hge =>
        have hse : s = m + 1 := Nat.le_antisymm hs2 hge
        refine Nat.gt_of_not_le (fun hle => ?_)
        have hble : Nat.ble (ground.getAt 0 kappa down)
            (ground.getAt 0 kappa up + (m + 1)) = false :=
          andFalse (Bool.eq_false_iff.mpr hg) (by rw [← hse]; exact harr)
        rw [← hse, leBle hle] at hble
        exact Bool.noConfusion hble

/-- The second place of the letter's key value: the search over
the count, the letter and the line's own place skipped. -/
private def sOffGo (i j : Nat) (kappa : List Nat) : Nat → Nat
  | 0 => j
  | t + 1 =>
    if t = i then sOffGo i j kappa t
    else if t = j then sOffGo i j kappa t
    else if ground.getAt 0 kappa t = ground.getAt 0 kappa j
    then t
    else sOffGo i j kappa t

private theorem sOffGo_read {i j : Nat} {kappa : List Nat}
    {t0 : Nat} (ht0i : t0 ≠ i) (ht0j : t0 ≠ j)
    (hv : ground.getAt 0 kappa t0 = ground.getAt 0 kappa j) :
    ∀ {n : Nat}, t0 < n →
      (∀ t, t < n → t ≠ i → t ≠ j →
        ground.getAt 0 kappa t = ground.getAt 0 kappa j →
        t = t0) →
      sOffGo i j kappa n = t0 := by
  intro n
  induction n with
  | zero => exact fun h _ => absurd h (Nat.not_lt_zero t0)
  | succ m ih =>
    intro hlt huniq
    show (if m = i then sOffGo i j kappa m
      else if m = j then sOffGo i j kappa m
      else if ground.getAt 0 kappa m = ground.getAt 0 kappa j
      then m
      else sOffGo i j kappa m) = t0
    have hrec : t0 ≠ m → sOffGo i j kappa m = t0 := fun hne =>
      ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt)
          (fun he => hne he))
        (fun t ht => huniq t (Nat.lt_succ_of_lt ht))
    by_cases hmi : m = i
    · rw [if_pos hmi]
      exact hrec (fun he => ht0i (he.trans hmi))
    · rw [if_neg hmi]
      by_cases hmj : m = j
      · rw [if_pos hmj]
        exact hrec (fun he => ht0j (he.trans hmj))
      · rw [if_neg hmj]
        by_cases hmv : ground.getAt 0 kappa m
            = ground.getAt 0 kappa j
        · rw [if_pos hmv]
          exact huniq m (Nat.lt_succ_self m) hmi hmj hmv
        · rw [if_neg hmv]
          exact hrec (fun he => hmv (he ▸ hv))

/-- The letter pairing (`thm:weylchar`'s assembly involution): a
letter whose line holds a one-sided hit reads to the second place
of its key value, the further letters kept. -/
private def partnerAt (i d : Nat) (kappa : List Nat) (j : Nat) :
    Nat :=
  if i < j then
    match oneHit i j d kappa with
    | some _ => sOffGo i j kappa d
    | none => j
  else if j < i then
    match oneHit j i d kappa with
    | some _ => sOffGo i j kappa d
    | none => j
  else j

/-- Off the displays a one-sided hit's receding value sits
strictly below the up place's key value: the co-filling at the
equality is the key itself. -/
private theorem hit_strict {d up down : Nat} (hne : up ≠ down)
    (hup : up < d) (hdown : down < d) {kappa : List Nat}
    (hoff : arrB d kappa = false) {s : Nat}
    (hs2 : s ≤ ground.getAt 0 kappa down)
    (hhit : arrB d (moveBy up down s kappa) = true)
    (hone : ground.getAt 0 kappa down
      ≤ ground.getAt 0 kappa up + s) :
    ground.getAt 0 (moveBy up down s kappa) down
      < ground.getAt 0 kappa up := by
  have hlenKd : kappa.length = d := by
    rw [← length_moveBy up down s kappa]
    exact (arr_reads hhit).1
  have hupk : up < kappa.length := by rw [hlenKd]; exact hup
  have hdownk : down < kappa.length := by rw [hlenKd]; exact hdown
  have hMd : ground.getAt 0 (moveBy up down s kappa) down
      = ground.getAt 0 kappa down - s :=
    getAt_moveBy_snd up hne s kappa hdownk
  have hle : ground.getAt 0 kappa down - s
      ≤ ground.getAt 0 kappa up := by
    have h4 := Nat.sub_le_sub_right hone s
    rw [addSubSelfR (ground.getAt 0 kappa up) s] at h4
    exact h4
  rw [hMd]
  refine Nat.lt_of_le_of_ne hle (fun heq => ?_)
  have hmu : up < (moveBy up down s kappa).length := by
    rw [length_moveBy]
    exact hupk
  have hmd : down < (moveBy up down s kappa).length := by
    rw [length_moveBy]
    exact hdownk
  have hkey : kappa
      = swapPair up down (moveBy up down s kappa) := by
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [length_swapPair, length_moveBy]
    · intro t ht
      by_cases htu : t = up
      · rw [htu, getAt_swapPair_fst _ hne hmu hmd, hMd, heq]
      · by_cases htd : t = down
        · rw [htd, getAt_swapPair_snd _ hne hmu hmd,
            getAt_moveBy_fst hne s kappa hupk, ← heq,
            subAdd hs2]
        · rw [getAt_swapPair_ne _ hmu hmd htu htd,
            getAt_moveBy_ne up down s kappa htu htd]
  have harrk : arrB d kappa = true := by
    rw [hkey, arrB_swapPair]
    exact hhit
  rw [hoff] at harrk
  exact Bool.noConfusion harrk

/-- A value between a hit's two fillings occupies a further place,
the key's own value at it, and one such place alone. -/
private theorem valuePlace {d up down : Nat} (hup : up < d)
    {kappa : List Nat} {s : Nat}
    (hhit : arrB d (moveBy up down s kappa) = true) {V : Nat}
    (hVlo : ground.getAt 0 (moveBy up down s kappa) down < V)
    (hVhi : V < ground.getAt 0 (moveBy up down s kappa) up) :
    (posOf V (moveBy up down s kappa) < d
      ∧ posOf V (moveBy up down s kappa) ≠ up
      ∧ posOf V (moveBy up down s kappa) ≠ down
      ∧ ground.getAt 0 kappa (posOf V (moveBy up down s kappa))
          = V
      ∧ ground.getAt 0 (moveBy up down s kappa)
          (posOf V (moveBy up down s kappa)) = V)
    ∧ ∀ t, t < d → t ≠ up → t ≠ down →
        ground.getAt 0 kappa t = V →
        t = posOf V (moveBy up down s kappa) := by
  obtain ⟨hmlen, hment, hmval⟩ := arr_reads hhit
  have hupm : up < (moveBy up down s kappa).length := by
    rw [hmlen]
    exact hup
  have hV1 : 1 ≤ V := Nat.lt_of_le_of_lt (Nat.zero_le _) hVlo
  have hVd : V ≤ d := by
    have hupent := hment
      (ground.getAt 0 (moveBy up down s kappa) up)
      (countOf_getAt_pos 0 _ up hupm)
    exact Nat.le_trans (Nat.le_of_lt hVhi) hupent.2
  have hcnt : 0 < ground.countOf V (moveBy up down s kappa) := by
    rw [hmval V hV1 hVd]
    exact Nat.succ_pos 0
  have hplt : posOf V (moveBy up down s kappa)
      < (moveBy up down s kappa).length := posOf_lt V _ hcnt
  have hpltd : posOf V (moveBy up down s kappa) < d := by
    rw [← hmlen]
    exact hplt
  have hget : ground.getAt 0 (moveBy up down s kappa)
      (posOf V (moveBy up down s kappa)) = V :=
    getAt_posOf V _ hcnt
  have hpu : posOf V (moveBy up down s kappa) ≠ up := fun he => by
    rw [he] at hget
    rw [hget] at hVhi
    exact Nat.lt_irrefl V hVhi
  have hpd : posOf V (moveBy up down s kappa) ≠ down :=
    fun he => by
      rw [he] at hget
      rw [hget] at hVlo
      exact Nat.lt_irrefl V hVlo
  have hkread : ground.getAt 0 kappa
      (posOf V (moveBy up down s kappa)) = V := by
    rw [← getAt_moveBy_ne up down s kappa hpu hpd]
    exact hget
  refine ⟨⟨hpltd, hpu, hpd, hkread, hget⟩, ?_⟩
  intro t htd htu htdn hkt
  by_cases hte : t = posOf V (moveBy up down s kappa)
  · exact hte
  · have hMt : ground.getAt 0 (moveBy up down s kappa) t = V := by
      rw [getAt_moveBy_ne up down s kappa htu htdn]
      exact hkt
    exact absurd (hMt.trans hget.symm)
      (arr_getAt_ne hhit htd hpltd hte)

/-- A list agreeing with the key off a pair, at the moved pair
entries, is the moved key. -/
private theorem keyOf {up down : Nat} (hne : up ≠ down)
    {kappa P : List Nat} (hlenP : P.length = kappa.length)
    (hup : up < kappa.length) (hdown : down < kappa.length)
    {s : Nat}
    (hPu : ground.getAt 0 P up = ground.getAt 0 kappa up + s)
    (hPd : ground.getAt 0 P down + s = ground.getAt 0 kappa down)
    (hPoff : ∀ t, t < kappa.length → t ≠ up → t ≠ down →
      ground.getAt 0 P t = ground.getAt 0 kappa t) :
    P = moveBy up down s kappa := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlenP, length_moveBy]
  · intro t ht
    rw [hlenP] at ht
    by_cases htu : t = up
    · rw [htu, getAt_moveBy_fst hne s kappa hup]
      exact hPu
    · by_cases htd : t = down
      · rw [htd, getAt_moveBy_snd up hne s kappa hdown, ← hPd,
          addSubSelfR]
      · rw [getAt_moveBy_ne up down s kappa htu htd]
        exact hPoff t ht htu htd

/-- The partner line's one-sided hit: at the partner places' key
values strictly between the fillings, the arrangement keeping the
upper filling at the up place with the receding value at the down
place is a moved key, one shift, its co-filling off the moved
keys. -/
private theorem partnerHit {d up' down' : Nat} (hne : up' ≠ down')
    (hu : up' < d) (hd : down' < d)
    {kappa P : List Nat} (hlenK : kappa.length = d)
    (harrP : arrB d P = true) {h c : Nat}
    (hsum : ground.getAt 0 kappa up' + ground.getAt 0 kappa down'
      = h + c)
    (hhi1 : ground.getAt 0 kappa up' < h)
    (hhi2 : ground.getAt 0 kappa down' < h)
    (hPu : ground.getAt 0 P up' = h)
    (hPd : ground.getAt 0 P down' = c)
    (hPoff : ∀ t, t < d → t ≠ up' → t ≠ down' →
      ground.getAt 0 P t = ground.getAt 0 kappa t) :
    (1 ≤ h - ground.getAt 0 kappa up'
      ∧ h - ground.getAt 0 kappa up'
        ≤ ground.getAt 0 kappa down')
    ∧ moveBy up' down' (h - ground.getAt 0 kappa up') kappa = P
    ∧ arrB d (moveBy up' down'
        (h - ground.getAt 0 kappa up') kappa) = true
    ∧ ground.getAt 0 kappa down'
      ≤ ground.getAt 0 kappa up'
        + (h - ground.getAt 0 kappa up') := by
  have hup'k : up' < kappa.length := by
    rw [hlenK]
    exact hu
  have hdown'k : down' < kappa.length := by
    rw [hlenK]
    exact hd
  have hs'1 : 1 ≤ h - ground.getAt 0 kappa up' := subPos hhi1
  have hhk : h ≤ ground.getAt 0 kappa up'
      + ground.getAt 0 kappa down' := by
    rw [hsum]
    exact Nat.le_add_right h c
  have hs'le : h - ground.getAt 0 kappa up'
      ≤ ground.getAt 0 kappa down' := by
    have h4 := Nat.sub_le_sub_right hhk (ground.getAt 0 kappa up')
    rw [Nat.add_comm (ground.getAt 0 kappa up')
        (ground.getAt 0 kappa down'),
      addSubSelfR (ground.getAt 0 kappa down')
        (ground.getAt 0 kappa up')] at h4
    exact h4
  have hup's : ground.getAt 0 kappa up'
      + (h - ground.getAt 0 kappa up') = h := by
    rw [Nat.add_comm]
    exact subAdd (Nat.le_of_lt hhi1)
  have hkey : P = moveBy up' down'
      (h - ground.getAt 0 kappa up') kappa := by
    refine keyOf hne ?_ hup'k hdown'k ?_ ?_ ?_
    · rw [(arr_reads harrP).1, hlenK]
    · rw [hPu, hup's]
    · rw [hPd, ground.addSubAssoc (Nat.le_of_lt hhi1) c,
        Nat.add_comm c h, ← hsum,
        Nat.add_comm (ground.getAt 0 kappa up')
          (ground.getAt 0 kappa down'),
        addSubSelfR]
    · intro t ht _htu _htd
      refine hPoff t ?_ _htu _htd
      rw [← hlenK]
      exact ht
  refine ⟨⟨hs'1, hs'le⟩, hkey.symm, ?_, ?_⟩
  · rw [← hkey]
    exact harrP
  · rw [hup's]
    exact Nat.le_of_lt hhi2

private theorem permOf_swapPair (d a b : Nat) (z : List Nat) :
    permOf d (swapPair a b z) = swapPair a b (permOf d z) :=
  (swapPair_map (fun v => d - v) a b z).symm

private theorem parity_permOf_swap {d a b : Nat} (hne : a ≠ b)
    (ha : a < d) (hb : b < d) {z : List Nat}
    (hz : arrB d z = true) :
    parity (permOf d (swapPair a b z))
      = !(parity (permOf d z)) := by
  have hlen : (permOf d z).length = d := by
    show (z.map (fun v => d - v)).length = d
    rw [ground.length_map]
    exact (arr_reads hz).1
  rw [permOf_swapPair d a b z]
  exact parity_swapPair (permOf d z) hne (by rw [hlen]; exact ha)
    (by rw [hlen]; exact hb)
    (perm_member_reads (permOf_member hz)).2.1

/-- A partner line's leaf: at partner places whose key values sit
strictly between a hit's fillings, with the partner arrangement's
entry reads, the line holds its own one-sided hit and its fold
reads the partner arrangement's graded unit. -/
private theorem partnerLeaf {d up' down' : Nat} (hne : up' ≠ down')
    (hu : up' < d) (hd : down' < d) {kappa P : List Nat}
    (hlenK : kappa.length = d) (harrP : arrB d P = true)
    {h c : Nat}
    (hsum : ground.getAt 0 kappa up' + ground.getAt 0 kappa down'
      = h + c)
    (hhi1 : ground.getAt 0 kappa up' < h)
    (hhi2 : ground.getAt 0 kappa down' < h)
    (hPu : ground.getAt 0 P up' = h)
    (hPd : ground.getAt 0 P down' = c)
    (hPoff : ∀ t, t < d → t ≠ up' → t ≠ down' →
      ground.getAt 0 P t = ground.getAt 0 kappa t) :
    oneHit up' down' d kappa ≠ none
    ∧ ∀ sd : Bool,
        lineFold up' down' d kappa sd
          = if sd = parity (permOf d P) then 1 else 0 := by
  obtain ⟨⟨hs'1, hs'2⟩, hPkey, harr', hone'⟩ :=
    partnerHit hne hu hd hlenK harrP hsum hhi1 hhi2 hPu hPd hPoff
  constructor
  · intro hnone
    have hnone' : oneGo up' down' d kappa
        (ground.getAt 0 kappa down') = none := hnone
    have hlt := oneGo_none hnone' _ hs'1 hs'2 harr'
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hone' hlt)
  · intro sd
    rw [lineFold_single hne hu hd hs'1 hs'2 harr' hone' sd, hPkey]

/-- The pairing at a letter beyond the further place
(`thm:weylchar`'s assembly): the letter's key value at its second
place names the partner line, the partner's hit keeps the upper
filling with the receding value at its further filling, the
pairing returns, and the two folds' reads join — the grading
exchanged at a partner on the letter's own side, the memberwise
exchange reading the join across it. -/
private theorem pairedH {d i j tstar : Nat} (hi : i < d)
    (hj : j < d) (htd : tstar < d) (hlt : i < j)
    (hti : tstar ≠ i) (htj : tstar ≠ j) {kappa : List Nat}
    (hoff : arrB d kappa = false) {s : Nat} (hs1 : 1 ≤ s)
    (hs2 : s ≤ ground.getAt 0 kappa j)
    (hhit : arrB d (moveBy i j s kappa) = true)
    (hone : ground.getAt 0 kappa j ≤ ground.getAt 0 kappa i + s)
    (hpM : ground.getAt 0 (moveBy i j s kappa) tstar
      = ground.getAt 0 kappa j) :
    (i < tstar → oneHit i tstar d kappa ≠ none)
    ∧ (tstar < i → oneHit tstar i d kappa ≠ none)
    ∧ sOffGo i tstar kappa d = j
    ∧ ∀ sd : Bool,
        (if i < tstar then lineFold i tstar d kappa sd
        else if tstar < i then lineFold tstar i d kappa (!sd)
        else 0)
        = lineFold i j d kappa (!sd) := by
  have hne_ij : i ≠ j := Nat.ne_of_lt hlt
  have hne_it : i ≠ tstar := fun he => hti he.symm
  have hne_jt : j ≠ tstar := fun he => htj he.symm
  have hlenK : kappa.length = d := by
    rw [← length_moveBy i j s kappa]
    exact (arr_reads hhit).1
  have hik : i < kappa.length := by rw [hlenK]; exact hi
  have hjk : j < kappa.length := by rw [hlenK]; exact hj
  have hMlen : (moveBy i j s kappa).length = d :=
    (arr_reads hhit).1
  have hiM : i < (moveBy i j s kappa).length := by
    rw [hMlen]; exact hi
  have hjM : j < (moveBy i j s kappa).length := by
    rw [hMlen]; exact hj
  have htM : tstar < (moveBy i j s kappa).length := by
    rw [hMlen]; exact htd
  have hcstrict := hit_strict hne_ij hi hj hoff hs2 hhit hone
  have hMu : ground.getAt 0 (moveBy i j s kappa) i
      = ground.getAt 0 kappa i + s :=
    getAt_moveBy_fst hne_ij s kappa hik
  have hMdns : ground.getAt 0 (moveBy i j s kappa) j + s
      = ground.getAt 0 kappa j := by
    rw [getAt_moveBy_snd i hne_ij s kappa hjk]
    exact subAdd hs2
  have hpk : ground.getAt 0 kappa tstar
      = ground.getAt 0 kappa j := by
    rw [← getAt_moveBy_ne i j s kappa hti htj]
    exact hpM
  have hjhi : ground.getAt 0 kappa j
      < ground.getAt 0 (moveBy i j s kappa) i := by
    rw [← hMdns, hMu]
    exact Nat.add_lt_add_right hcstrict s
  have hihi : ground.getAt 0 kappa i
      < ground.getAt 0 (moveBy i j s kappa) i := by
    rw [hMu]
    exact Nat.add_lt_add_left hs1 _
  have hhc : ground.getAt 0 (moveBy i j s kappa) i
      + ground.getAt 0 (moveBy i j s kappa) j
      = ground.getAt 0 kappa i + ground.getAt 0 kappa j := by
    rw [hMu,
      Nat.add_assoc (ground.getAt 0 kappa i) s
        (ground.getAt 0 (moveBy i j s kappa) j),
      Nat.add_comm s (ground.getAt 0 (moveBy i j s kappa) j),
      hMdns]
  have hC4 : sOffGo i tstar kappa d = j := by
    refine sOffGo_read (fun he => hne_ij he.symm) hne_jt
      hpk.symm hj ?_
    intro t htd' hti' htt' hkt
    by_cases htj' : t = j
    · exact htj'
    · have hMt : ground.getAt 0 (moveBy i j s kappa) t
          = ground.getAt 0 kappa j := by
        rw [getAt_moveBy_ne i j s kappa hti' htj', hkt, hpk]
      exact absurd (hMt.trans hpM.symm)
        (arr_getAt_ne hhit htd' htd htt')
  have hRHS : ∀ sd : Bool, lineFold i j d kappa sd
      = if sd = parity (permOf d (moveBy i j s kappa))
        then 1 else 0 :=
    fun sd => lineFold_single hne_ij hi hj hs1 hs2 hhit hone sd
  by_cases hSide : i < tstar
  · -- the same-side partner: the places' transposition, the
    -- grading exchanged
    have harrP : arrB d (swapPair j tstar
        (moveBy i j s kappa)) = true := by
      rw [arrB_swapPair]
      exact hhit
    obtain ⟨hnn, hvals⟩ := partnerLeaf (Nat.ne_of_lt hSide) hi htd
      hlenK harrP
      (h := ground.getAt 0 (moveBy i j s kappa) i)
      (c := ground.getAt 0 (moveBy i j s kappa) j)
      (by rw [hpk]; exact hhc.symm) hihi
      (by rw [hpk]; exact hjhi)
      (getAt_swapPair_ne _ hjM htM hne_ij hne_it)
      (getAt_swapPair_snd _ hne_jt hjM htM)
      (by
        intro t htd' hti' htt'
        by_cases htj' : t = j
        · rw [htj', getAt_swapPair_fst _ hne_jt hjM htM]
          exact hpM
        · rw [getAt_swapPair_ne _ hjM htM htj' htt',
            getAt_moveBy_ne i j s kappa hti' htj'])
    have hparP := parity_permOf_swap hne_jt hj htd hhit
    refine ⟨fun _ => hnn,
      fun hcon => absurd (Nat.lt_trans hSide hcon)
        (Nat.lt_irrefl i),
      hC4, fun sd => ?_⟩
    rw [if_pos hSide, hvals sd, hparP, hRHS (!sd)]
    by_cases hc : sd
        = !(parity (permOf d (moveBy i j s kappa)))
    · rw [if_pos hc, if_pos (not_shift.mpr hc)]
    · rw [if_neg hc, if_neg (fun h2 => hc (not_shift.mp h2))]
  · -- the cross partner: the memberwise exchange, the grading
    -- kept over the pair of transpositions
    have htlt : tstar < i :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_lt hSide) hti
    have harrQ : arrB d (swapPair i tstar
        (moveBy i j s kappa)) = true := by
      rw [arrB_swapPair]
      exact hhit
    have hQlen : (swapPair i tstar
        (moveBy i j s kappa)).length = d := by
      rw [length_swapPair]
      exact hMlen
    have hiQ : i < (swapPair i tstar
        (moveBy i j s kappa)).length := by
      rw [hQlen]; exact hi
    have hjQ : j < (swapPair i tstar
        (moveBy i j s kappa)).length := by
      rw [hQlen]; exact hj
    have harrP : arrB d (swapPair i j (swapPair i tstar
        (moveBy i j s kappa))) = true := by
      rw [arrB_swapPair, arrB_swapPair]
      exact hhit
    obtain ⟨hnn, hvals⟩ := partnerLeaf hti htd hi hlenK harrP
      (h := ground.getAt 0 (moveBy i j s kappa) i)
      (c := ground.getAt 0 (moveBy i j s kappa) j)
      (by rw [hpk, Nat.add_comm (ground.getAt 0 kappa j)
          (ground.getAt 0 kappa i)]
          exact hhc.symm)
      (by rw [hpk]; exact hjhi) hihi
      (by rw [getAt_swapPair_ne _ hiQ hjQ hti htj,
          getAt_swapPair_snd _ hne_it hiM htM])
      (by rw [getAt_swapPair_fst _ hne_ij hiQ hjQ,
          getAt_swapPair_ne _ hiM htM
            (fun he => hne_ij he.symm) hne_jt])
      (by
        intro t htd' htt' hti'
        by_cases htj' : t = j
        · rw [htj', getAt_swapPair_snd _ hne_ij hiQ hjQ,
            getAt_swapPair_fst _ hne_it hiM htM]
          exact hpM
        · rw [getAt_swapPair_ne _ hiQ hjQ hti' htj',
            getAt_swapPair_ne _ hiM htM hti' htt',
            getAt_moveBy_ne i j s kappa hti' htj'])
    have hparP : parity (permOf d (swapPair i j (swapPair i tstar
        (moveBy i j s kappa))))
        = parity (permOf d (moveBy i j s kappa)) := by
      rw [parity_permOf_swap hne_ij hi hj harrQ,
        parity_permOf_swap hne_it hi htd hhit,
        Bool.not_not (parity (permOf d (moveBy i j s kappa)))]
    refine ⟨fun hcon => absurd (Nat.lt_trans hcon htlt)
        (Nat.lt_irrefl i),
      fun _ => hnn, hC4, fun sd => ?_⟩
    rw [if_neg hSide, if_pos htlt, hvals (!sd), hparP, hRHS (!sd)]

/-- The pairing at a letter below the further place, the swapped
cofactor's orientation (`thm:weylchar`'s assembly): the mirror of
the beyond-side pairing at the exchanged fold members. -/
private theorem pairedL {d i j tstar : Nat} (hi : i < d)
    (hj : j < d) (htd : tstar < d) (hlt : j < i)
    (hti : tstar ≠ i) (htj : tstar ≠ j) {kappa : List Nat}
    (hoff : arrB d kappa = false) {s : Nat} (hs1 : 1 ≤ s)
    (hs2 : s ≤ ground.getAt 0 kappa i)
    (hhit : arrB d (moveBy j i s kappa) = true)
    (hone : ground.getAt 0 kappa i ≤ ground.getAt 0 kappa j + s)
    (hpM : ground.getAt 0 (moveBy j i s kappa) tstar
      = ground.getAt 0 kappa j) :
    (i < tstar → oneHit i tstar d kappa ≠ none)
    ∧ (tstar < i → oneHit tstar i d kappa ≠ none)
    ∧ sOffGo i tstar kappa d = j
    ∧ ∀ sd : Bool,
        (if i < tstar then lineFold i tstar d kappa sd
        else if tstar < i then lineFold tstar i d kappa (!sd)
        else 0)
        = lineFold j i d kappa sd := by
  have hne_ji : j ≠ i := Nat.ne_of_lt hlt
  have hne_ij : i ≠ j := fun he => hne_ji he.symm
  have hne_it : i ≠ tstar := fun he => hti he.symm
  have hne_jt : j ≠ tstar := fun he => htj he.symm
  have hlenK : kappa.length = d := by
    rw [← length_moveBy j i s kappa]
    exact (arr_reads hhit).1
  have hik : i < kappa.length := by rw [hlenK]; exact hi
  have hjk : j < kappa.length := by rw [hlenK]; exact hj
  have hMlen : (moveBy j i s kappa).length = d :=
    (arr_reads hhit).1
  have hiM : i < (moveBy j i s kappa).length := by
    rw [hMlen]; exact hi
  have hjM : j < (moveBy j i s kappa).length := by
    rw [hMlen]; exact hj
  have htM : tstar < (moveBy j i s kappa).length := by
    rw [hMlen]; exact htd
  have hcstrict := hit_strict hne_ji hj hi hoff hs2 hhit hone
  have hMu : ground.getAt 0 (moveBy j i s kappa) j
      = ground.getAt 0 kappa j + s :=
    getAt_moveBy_fst hne_ji s kappa hjk
  have hMdns : ground.getAt 0 (moveBy j i s kappa) i + s
      = ground.getAt 0 kappa i := by
    rw [getAt_moveBy_snd j hne_ji s kappa hik]
    exact subAdd hs2
  have hpk : ground.getAt 0 kappa tstar
      = ground.getAt 0 kappa j := by
    rw [← getAt_moveBy_ne j i s kappa htj hti]
    exact hpM
  have hjhi : ground.getAt 0 kappa j
      < ground.getAt 0 (moveBy j i s kappa) j := by
    rw [hMu]
    exact Nat.add_lt_add_left hs1 _
  have hihi : ground.getAt 0 kappa i
      < ground.getAt 0 (moveBy j i s kappa) j := by
    rw [← hMdns, hMu]
    exact Nat.add_lt_add_right hcstrict s
  have hhc : ground.getAt 0 (moveBy j i s kappa) j
      + ground.getAt 0 (moveBy j i s kappa) i
      = ground.getAt 0 kappa j + ground.getAt 0 kappa i := by
    rw [hMu,
      Nat.add_assoc (ground.getAt 0 kappa j) s
        (ground.getAt 0 (moveBy j i s kappa) i),
      Nat.add_comm s (ground.getAt 0 (moveBy j i s kappa) i),
      hMdns]
  have hC4 : sOffGo i tstar kappa d = j := by
    refine sOffGo_read (fun he => hne_ji he) hne_jt
      hpk.symm hj ?_
    intro t htd' hti' htt' hkt
    by_cases htj' : t = j
    · exact htj'
    · have hMt : ground.getAt 0 (moveBy j i s kappa) t
          = ground.getAt 0 kappa j := by
        rw [getAt_moveBy_ne j i s kappa htj' hti', hkt, hpk]
      exact absurd (hMt.trans hpM.symm)
        (arr_getAt_ne hhit htd' htd htt')
  have hRHS : ∀ sd : Bool, lineFold j i d kappa sd
      = if sd = parity (permOf d (moveBy j i s kappa))
        then 1 else 0 :=
    fun sd => lineFold_single hne_ji hj hi hs1 hs2 hhit hone sd
  by_cases hSide : i < tstar
  · -- the cross partner: the memberwise exchange, the grading
    -- kept over the pair of transpositions
    have harrQ : arrB d (swapPair i tstar
        (moveBy j i s kappa)) = true := by
      rw [arrB_swapPair]
      exact hhit
    have hQlen : (swapPair i tstar
        (moveBy j i s kappa)).length = d := by
      rw [length_swapPair]
      exact hMlen
    have hiQ : i < (swapPair i tstar
        (moveBy j i s kappa)).length := by
      rw [hQlen]; exact hi
    have hjQ : j < (swapPair i tstar
        (moveBy j i s kappa)).length := by
      rw [hQlen]; exact hj
    have harrP : arrB d (swapPair i j (swapPair i tstar
        (moveBy j i s kappa))) = true := by
      rw [arrB_swapPair, arrB_swapPair]
      exact hhit
    obtain ⟨hnn, hvals⟩ := partnerLeaf (Nat.ne_of_lt hSide) hi htd
      hlenK harrP
      (h := ground.getAt 0 (moveBy j i s kappa) j)
      (c := ground.getAt 0 (moveBy j i s kappa) i)
      (by rw [hpk, Nat.add_comm (ground.getAt 0 kappa i)
          (ground.getAt 0 kappa j)]
          exact hhc.symm)
      hihi
      (by rw [hpk]; exact hjhi)
      (by rw [getAt_swapPair_fst _ hne_ij hiQ hjQ,
          getAt_swapPair_ne _ hiM htM
            (fun he => hne_ij he.symm) hne_jt])
      (by rw [getAt_swapPair_ne _ hiQ hjQ hti htj,
          getAt_swapPair_snd _ hne_it hiM htM])
      (by
        intro t htd' hti' htt'
        by_cases htj' : t = j
        · rw [htj', getAt_swapPair_snd _ hne_ij hiQ hjQ,
            getAt_swapPair_fst _ hne_it hiM htM]
          exact hpM
        · rw [getAt_swapPair_ne _ hiQ hjQ hti' htj',
            getAt_swapPair_ne _ hiM htM hti' htt',
            getAt_moveBy_ne j i s kappa htj' hti'])
    have hparP : parity (permOf d (swapPair i j (swapPair i tstar
        (moveBy j i s kappa))))
        = parity (permOf d (moveBy j i s kappa)) := by
      rw [parity_permOf_swap hne_ij hi hj harrQ,
        parity_permOf_swap hne_it hi htd hhit,
        Bool.not_not (parity (permOf d (moveBy j i s kappa)))]
    refine ⟨fun _ => hnn,
      fun hcon => absurd (Nat.lt_trans hSide hcon)
        (Nat.lt_irrefl i),
      hC4, fun sd => ?_⟩
    rw [if_pos hSide, hvals sd, hparP, hRHS sd]
  · -- the same-side partner: the places' transposition, the
    -- grading exchanged
    have htlt : tstar < i :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_lt hSide) hti
    have harrP : arrB d (swapPair j tstar
        (moveBy j i s kappa)) = true := by
      rw [arrB_swapPair]
      exact hhit
    obtain ⟨hnn, hvals⟩ := partnerLeaf hti htd hi hlenK harrP
      (h := ground.getAt 0 (moveBy j i s kappa) j)
      (c := ground.getAt 0 (moveBy j i s kappa) i)
      (by rw [hpk]; exact hhc.symm)
      (by rw [hpk]; exact hjhi) hihi
      (getAt_swapPair_snd _ hne_jt hjM htM)
      (by rw [getAt_swapPair_ne _ hjM htM hne_ij hne_it])
      (by
        intro t htd' htt' hti'
        by_cases htj' : t = j
        · rw [htj', getAt_swapPair_fst _ hne_jt hjM htM]
          exact hpM
        · rw [getAt_swapPair_ne _ hjM htM htj' htt',
            getAt_moveBy_ne j i s kappa htj' hti'])
    have hparP := parity_permOf_swap hne_jt hj htd hhit
    refine ⟨fun hcon => absurd (Nat.lt_trans hcon htlt)
        (Nat.lt_irrefl i),
      fun _ => hnn, hC4, fun sd => ?_⟩
    rw [if_neg hSide, if_pos htlt, hvals (!sd), hparP, hRHS sd]
    by_cases hc : sd = parity (permOf d (moveBy j i s kappa))
    · rw [if_pos (congrArg (fun b : Bool => !b) hc), if_pos hc]
    · rw [if_neg (fun h2 => hc (Bool.not_inj h2)), if_neg hc]

/-- The one-sided pairing's whole read (`thm:weylchar`'s assembly
involution at a single letter): the letter's key value occupies a
second place, the partner line holds its own one-sided hit, the
pairing returns, and the two lines' reads enter at opposite
members. -/
private theorem partnerReads {d i j up down : Nat}
    (hi : i < d) (hj : j < d)
    (hor : (i = up ∧ j = down ∧ i < j)
      ∨ (j = up ∧ i = down ∧ j < i))
    {kappa : List Nat} (hoff : arrB d kappa = false) {s : Nat}
    (hs1 : 1 ≤ s) (hs2 : s ≤ ground.getAt 0 kappa down)
    (hhit : arrB d (moveBy up down s kappa) = true)
    (hone : ground.getAt 0 kappa down
      ≤ ground.getAt 0 kappa up + s) :
    (sOffGo i j kappa d < d ∧ sOffGo i j kappa d ≠ i
        ∧ sOffGo i j kappa d ≠ j)
    ∧ (i < sOffGo i j kappa d →
        oneHit i (sOffGo i j kappa d) d kappa ≠ none)
    ∧ (sOffGo i j kappa d < i →
        oneHit (sOffGo i j kappa d) i d kappa ≠ none)
    ∧ sOffGo i (sOffGo i j kappa d) kappa d = j
    ∧ ∀ sd : Bool,
        (if i < sOffGo i j kappa d then
          lineFold i (sOffGo i j kappa d) d kappa sd
        else if sOffGo i j kappa d < i then
          lineFold (sOffGo i j kappa d) i d kappa (!sd)
        else 0)
        = (if i < j then lineFold i j d kappa (!sd)
          else if j < i then lineFold j i d kappa (!(!sd))
          else 0) := by
  cases hor with
  | inl hcase =>
    obtain ⟨hu, hd, hlt⟩ := hcase
    subst hu
    subst hd
    have hne_ij : i ≠ j := Nat.ne_of_lt hlt
    have hlenK : kappa.length = d := by
      rw [← length_moveBy i j s kappa]
      exact (arr_reads hhit).1
    have hik : i < kappa.length := by rw [hlenK]; exact hi
    have hjk : j < kappa.length := by rw [hlenK]; exact hj
    have hcstrict := hit_strict hne_ij hi hj hoff hs2 hhit hone
    have hMu : ground.getAt 0 (moveBy i j s kappa) i
        = ground.getAt 0 kappa i + s :=
      getAt_moveBy_fst hne_ij s kappa hik
    have hMdns : ground.getAt 0 (moveBy i j s kappa) j + s
        = ground.getAt 0 kappa j := by
      rw [getAt_moveBy_snd i hne_ij s kappa hjk]
      exact subAdd hs2
    have hjlo : ground.getAt 0 (moveBy i j s kappa) j
        < ground.getAt 0 kappa j := by
      rw [← hMdns]
      exact Nat.add_lt_add_left hs1 _
    have hjhi : ground.getAt 0 kappa j
        < ground.getAt 0 (moveBy i j s kappa) i := by
      rw [← hMdns, hMu]
      exact Nat.add_lt_add_right hcstrict s
    obtain ⟨⟨hpd, hpu, hpdn, _, hpM⟩, huniq⟩ :=
      valuePlace hi hhit hjlo hjhi
    have hSeq : sOffGo i j kappa d
        = posOf (ground.getAt 0 kappa j) (moveBy i j s kappa) :=
      sOffGo_read hpu hpdn
        (by
          rw [← getAt_moveBy_ne i j s kappa hpu hpdn]
          exact hpM)
        hpd huniq
    rw [hSeq]
    obtain ⟨hA, hB, hC, hD⟩ := pairedH hi hj hpd hlt hpu hpdn
      hoff hs1 hs2 hhit hone hpM
    refine ⟨⟨hpd, hpu, hpdn⟩, hA, hB, hC, fun sd => ?_⟩
    rw [hD sd, if_pos hlt]
  | inr hcase =>
    obtain ⟨hu, hd, hlt⟩ := hcase
    subst hu
    subst hd
    have hne_ji : j ≠ i := Nat.ne_of_lt hlt
    have hlenK : kappa.length = d := by
      rw [← length_moveBy j i s kappa]
      exact (arr_reads hhit).1
    have hik : i < kappa.length := by rw [hlenK]; exact hi
    have hjk : j < kappa.length := by rw [hlenK]; exact hj
    have hcstrict := hit_strict hne_ji hj hi hoff hs2 hhit hone
    have hMu : ground.getAt 0 (moveBy j i s kappa) j
        = ground.getAt 0 kappa j + s :=
      getAt_moveBy_fst hne_ji s kappa hjk
    have hMdns : ground.getAt 0 (moveBy j i s kappa) i + s
        = ground.getAt 0 kappa i := by
      rw [getAt_moveBy_snd j hne_ji s kappa hik]
      exact subAdd hs2
    have hjlo : ground.getAt 0 (moveBy j i s kappa) i
        < ground.getAt 0 kappa j := hcstrict
    have hjhi : ground.getAt 0 kappa j
        < ground.getAt 0 (moveBy j i s kappa) j := by
      rw [hMu]
      exact Nat.add_lt_add_left hs1 _
    obtain ⟨⟨hpd, hpuJ, hpdI, _, hpM⟩, huniq⟩ :=
      valuePlace hj hhit hjlo hjhi
    have hSeq : sOffGo i j kappa d
        = posOf (ground.getAt 0 kappa j) (moveBy j i s kappa) :=
      sOffGo_read hpdI hpuJ
        (by
          rw [← getAt_moveBy_ne j i s kappa hpuJ hpdI]
          exact hpM)
        hpd (fun t ht hti htj hkt => huniq t ht htj hti hkt)
    rw [hSeq]
    obtain ⟨hA, hB, hC, hD⟩ := pairedL hi hj hpd hlt hpdI hpuJ
      hoff hs1 hs2 hhit hone hpM
    refine ⟨⟨hpd, hpdI, hpuJ⟩, hA, hB, hC, fun sd => ?_⟩
    rw [hD sd,
      if_neg (fun hc : i < j =>
        Nat.lt_irrefl i (Nat.lt_trans hc hlt)),
      if_pos hlt, Bool.not_not sd]

/-! The product-rule read (`thm:weylchar`'s assembly): the
derivative display `D_i V = Σ_{j≠i} x_i Q_ij` coefficientwise at
the alternant's clearing — at the bumped key the letter-weighted
coefficient reads the key's own graded count against the cofactor
fold over the further letters, the crossed equation of the two
sides' members. -/

private theorem eqNotOfNe : ∀ {a b : Bool}, ¬ a = b → a = !b := by
  intro a b h
  cases a with
  | false =>
    cases b with
    | false => exact absurd rfl h
    | true => rfl
  | true =>
    cases b with
    | false => rfl
    | true => exact absurd rfl h

private theorem partnerAt_self (i d : Nat) (kappa : List Nat) :
    partnerAt i d kappa i = i := by
  show (if i < i then
      match oneHit i i d kappa with
      | some _ => sOffGo i i kappa d
      | none => i
    else if i < i then
      match oneHit i i d kappa with
      | some _ => sOffGo i i kappa d
      | none => i
    else i) = i
  rw [if_neg (Nat.lt_irrefl i), if_neg (Nat.lt_irrefl i)]

private theorem partnerAt_gt {i j : Nat} (hij : i < j)
    (d : Nat) (kappa : List Nat) :
    partnerAt i d kappa j
      = (match oneHit i j d kappa with
        | some _ => sOffGo i j kappa d
        | none => j) := by
  show (if i < j then
      match oneHit i j d kappa with
      | some _ => sOffGo i j kappa d
      | none => j
    else if j < i then
      match oneHit j i d kappa with
      | some _ => sOffGo i j kappa d
      | none => j
    else j) = _
  rw [if_pos hij]

private theorem partnerAt_lt {i j : Nat} (hji : j < i)
    (d : Nat) (kappa : List Nat) :
    partnerAt i d kappa j
      = (match oneHit j i d kappa with
        | some _ => sOffGo i j kappa d
        | none => j) := by
  show (if i < j then
      match oneHit i j d kappa with
      | some _ => sOffGo i j kappa d
      | none => j
    else if j < i then
      match oneHit j i d kappa with
      | some _ => sOffGo i j kappa d
      | none => j
    else j) = _
  rw [if_neg (fun hc : i < j =>
      Nat.lt_irrefl i (Nat.lt_trans hc hji)),
    if_pos hji]

private theorem partnerAt_gt_none {i j d : Nat}
    {kappa : List Nat} (hij : i < j)
    (h : oneHit i j d kappa = none) :
    partnerAt i d kappa j = j := by
  rw [partnerAt_gt hij d kappa, h]

private theorem partnerAt_gt_some {i j d s0 : Nat}
    {kappa : List Nat} (hij : i < j)
    (h : oneHit i j d kappa = some s0) :
    partnerAt i d kappa j = sOffGo i j kappa d := by
  rw [partnerAt_gt hij d kappa, h]

private theorem partnerAt_lt_none {i j d : Nat}
    {kappa : List Nat} (hji : j < i)
    (h : oneHit j i d kappa = none) :
    partnerAt i d kappa j = j := by
  rw [partnerAt_lt hji d kappa, h]

private theorem partnerAt_lt_some {i j d s0 : Nat}
    {kappa : List Nat} (hji : j < i)
    (h : oneHit j i d kappa = some s0) :
    partnerAt i d kappa j = sOffGo i j kappa d := by
  rw [partnerAt_lt hji d kappa, h]

/-- The cofactor fold at a letter (`thm:weylchar`'s assembly, the
derivative display's cofactor side at the alternant's clearing):
the cofactor coefficients folded over the further letters, the
pairs beyond the letter at the stated side and the pairs below it
at the members exchanged, the swapped cofactor's read. -/
def cofSum (i d : Nat) (w : List Nat) (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun j =>
      if i < j then cofAt i j d w side
      else if j < i then cofAt j i d w (!side)
      else 0)
    (List.range d)

/-- The product-rule read (`thm:weylchar`'s assembly): at the
bumped key the derivative display closes coefficientwise — the
letter-weighted graded count with the further member's own against
the cofactor fold's exchanged reads, the crossed equation over the
two sides.  The bumped spelling reaches every coefficient the
display occupies at the letter, the shift argument the key's own
predecessor there; a key reading the letter at the count's unit
reads the count's unit on both sides of the display outright. -/
theorem prodRule (i d : Nat) (hid : i < d) (w : List Nat)
    (hw : w.length = d) (side : Bool) :
    ground.getAt 0 (ground.bumpAt i w) i
        * sideCount d (unitDisp d) (ground.bumpAt i w) side
      + sideCount d (unitDisp d) (ground.bumpAt i w) (!side)
      + cofSum i d w (!side)
    = ground.getAt 0 (ground.bumpAt i w) i
        * sideCount d (unitDisp d) (ground.bumpAt i w) (!side)
      + sideCount d (unitDisp d) (ground.bumpAt i w) side
      + cofSum i d w side := by
  have hiw : i < w.length := by rw [hw]; exact hid
  have hcof : ∀ tb : Bool, cofSum i d w tb
      = ground.famFold Nat.add 0
        (fun j =>
          if i < j then
            sideCount d (unitDisp d) (ground.bumpAt i w) tb
              + lineFold i j d (ground.bumpAt i w) tb
          else if j < i then
            lineFold j i d (ground.bumpAt i w) (!tb)
          else 0)
        (List.range d) := by
    intro tb
    show ground.famFold Nat.add 0
        (fun j =>
          if i < j then cofAt i j d w tb
          else if j < i then cofAt j i d w (!tb)
          else 0)
        (List.range d) = _
    refine ground.famFold_congr_members Nat.add 0 _ _ _
      (fun j hj => ?_)
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij,
        cofAt_split (Nat.ne_of_lt hij) d w tb]
    · rw [if_neg hij, if_neg hij]
      by_cases hji : j < i
      · rw [if_pos hji, if_pos hji, cofAt_line j i d w hiw (!tb)]
      · rw [if_neg hji, if_neg hji]
  cases harr : arrB d (ground.bumpAt i w) with
  | false =>
    have hmem : ∀ x, 0 < ground.countOf x (List.range d) →
        0 < ground.countOf
          (partnerAt i d (ground.bumpAt i w) x)
          (List.range d) := by
      intro j hj
      have hjd : j < d := ground.ltOfMem hj
      by_cases hje : j = i
      · rw [hje, partnerAt_self]
        exact ground.countOf_range_pos hid
      · by_cases hij : i < j
        · cases honeH : oneHit i j d (ground.bumpAt i w) with
          | none =>
            rw [partnerAt_gt_none hij honeH]
            exact hj
          | some s0 =>
            rw [partnerAt_gt_some hij honeH]
            obtain ⟨hs1, hs2, hhit, hone⟩ :=
              oneGo_some (n := ground.getAt 0
                (ground.bumpAt i w) j) honeH
            obtain ⟨⟨hSd, _, _⟩, _⟩ := partnerReads hid hjd
              (.inl ⟨rfl, rfl, hij⟩) harr hs1 hs2 hhit hone
            exact ground.countOf_range_pos hSd
        · have hji : j < i := Nat.lt_of_le_of_ne
            (Nat.le_of_not_lt hij) hje
          cases honeH : oneHit j i d (ground.bumpAt i w) with
          | none =>
            rw [partnerAt_lt_none hji honeH]
            exact hj
          | some s0 =>
            rw [partnerAt_lt_some hji honeH]
            obtain ⟨hs1, hs2, hhit, hone⟩ :=
              oneGo_some (n := ground.getAt 0
                (ground.bumpAt i w) i) honeH
            obtain ⟨⟨hSd, _, _⟩, _⟩ := partnerReads hid hjd
              (.inr ⟨rfl, rfl, hji⟩) harr hs1 hs2 hhit hone
            exact ground.countOf_range_pos hSd
    have hinv : ∀ x, 0 < ground.countOf x (List.range d) →
        partnerAt i d (ground.bumpAt i w)
          (partnerAt i d (ground.bumpAt i w) x) = x := by
      intro j hj
      have hjd : j < d := ground.ltOfMem hj
      by_cases hje : j = i
      · rw [hje, partnerAt_self, partnerAt_self]
      · by_cases hij : i < j
        · cases honeH : oneHit i j d (ground.bumpAt i w) with
          | none =>
            rw [partnerAt_gt_none hij honeH,
              partnerAt_gt_none hij honeH]
          | some s0 =>
            rw [partnerAt_gt_some hij honeH]
            obtain ⟨hs1, hs2, hhit, hone⟩ :=
              oneGo_some (n := ground.getAt 0
                (ground.bumpAt i w) j) honeH
            obtain ⟨⟨hSd, hSi, _⟩, hA, hB, hC, _⟩ :=
              partnerReads hid hjd (.inl ⟨rfl, rfl, hij⟩) harr
                hs1 hs2 hhit hone
            by_cases hiS : i
                < sOffGo i j (ground.bumpAt i w) d
            · cases honeS : oneHit i
                  (sOffGo i j (ground.bumpAt i w) d) d
                  (ground.bumpAt i w) with
              | none => exact absurd honeS (hA hiS)
              | some s1 =>
                rw [partnerAt_gt_some hiS honeS]
                exact hC
            · have hSi' : sOffGo i j (ground.bumpAt i w) d
                  < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hiS) hSi
              cases honeS : oneHit
                  (sOffGo i j (ground.bumpAt i w) d) i d
                  (ground.bumpAt i w) with
              | none => exact absurd honeS (hB hSi')
              | some s1 =>
                rw [partnerAt_lt_some hSi' honeS]
                exact hC
        · have hji : j < i := Nat.lt_of_le_of_ne
            (Nat.le_of_not_lt hij) hje
          cases honeH : oneHit j i d (ground.bumpAt i w) with
          | none =>
            rw [partnerAt_lt_none hji honeH,
              partnerAt_lt_none hji honeH]
          | some s0 =>
            rw [partnerAt_lt_some hji honeH]
            obtain ⟨hs1, hs2, hhit, hone⟩ :=
              oneGo_some (n := ground.getAt 0
                (ground.bumpAt i w) i) honeH
            obtain ⟨⟨hSd, hSi, _⟩, hA, hB, hC, _⟩ :=
              partnerReads hid hjd (.inr ⟨rfl, rfl, hji⟩) harr
                hs1 hs2 hhit hone
            by_cases hiS : i
                < sOffGo i j (ground.bumpAt i w) d
            · cases honeS : oneHit i
                  (sOffGo i j (ground.bumpAt i w) d) d
                  (ground.bumpAt i w) with
              | none => exact absurd honeS (hA hiS)
              | some s1 =>
                rw [partnerAt_gt_some hiS honeS]
                exact hC
            · have hSi' : sOffGo i j (ground.bumpAt i w) d
                  < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hiS) hSi
              cases honeS : oneHit
                  (sOffGo i j (ground.bumpAt i w) d) i d
                  (ground.bumpAt i w) with
              | none => exact absurd honeS (hB hSi')
              | some s1 =>
                rw [partnerAt_lt_some hSi' honeS]
                exact hC
    have hcs : cofSum i d w (!side) = cofSum i d w side := by
      rw [hcof (!side), hcof side, sideCount_off harr side,
        sideCount_off harr (!side)]
      rw [ground.famFold_reindex Nat.add 0 Nat.add_comm
        Nat.add_assoc
        (fun j =>
          if i < j then
            0 + lineFold i j d (ground.bumpAt i w) side
          else if j < i then
            lineFold j i d (ground.bumpAt i w) (!side)
          else 0)
        (l := List.range d)
        (g := partnerAt i d (ground.bumpAt i w))
        (h := partnerAt i d (ground.bumpAt i w))
        (distinctList_range d) hinv hinv hmem hmem]
      refine ground.famFold_congr_members Nat.add 0 _ _ _
        (fun j hj => ?_)
      have hjd : j < d := ground.ltOfMem hj
      by_cases hje : j = i
      · rw [hje, partnerAt_self, if_neg (Nat.lt_irrefl i),
          if_neg (Nat.lt_irrefl i), if_neg (Nat.lt_irrefl i),
          if_neg (Nat.lt_irrefl i)]
      · by_cases hij : i < j
        · cases honeH : oneHit i j d (ground.bumpAt i w) with
          | none =>
            rw [partnerAt_gt_none hij honeH]
            have hall := oneGo_none (n := ground.getAt 0
              (ground.bumpAt i w) j) honeH
            rw [if_pos hij, if_pos hij, Nat.zero_add,
              Nat.zero_add]
            exact (lineFold_bal (Nat.ne_of_lt hij) hid hjd
              (by rw [ground.length_bumpAt i w, hw])
              hall side).symm
          | some s0 =>
            rw [partnerAt_gt_some hij honeH]
            obtain ⟨hs1, hs2, hhit, hone⟩ :=
              oneGo_some (n := ground.getAt 0
                (ground.bumpAt i w) j) honeH
            obtain ⟨_, _, _, _, hD⟩ :=
              partnerReads hid hjd (.inl ⟨rfl, rfl, hij⟩) harr
                hs1 hs2 hhit hone
            have hD' := hD side
            rw [if_pos hij] at hD'
            rw [if_pos hij, Nat.zero_add]
            by_cases hiS : i
                < sOffGo i j (ground.bumpAt i w) d
            · rw [if_pos hiS] at hD'
              rw [if_pos hiS, Nat.zero_add]
              exact hD'.symm
            · rw [if_neg hiS] at hD'
              rw [if_neg hiS]
              exact hD'.symm
        · have hji : j < i := Nat.lt_of_le_of_ne
            (Nat.le_of_not_lt hij) hje
          cases honeH : oneHit j i d (ground.bumpAt i w) with
          | none =>
            rw [partnerAt_lt_none hji honeH]
            have hall := oneGo_none (n := ground.getAt 0
              (ground.bumpAt i w) i) honeH
            rw [if_neg hij, if_pos hji, if_neg hij, if_pos hji]
            exact (lineFold_bal (Nat.ne_of_lt hji) hjd hid
              (by rw [ground.length_bumpAt i w, hw])
              hall (!side)).symm
          | some s0 =>
            rw [partnerAt_lt_some hji honeH]
            obtain ⟨hs1, hs2, hhit, hone⟩ :=
              oneGo_some (n := ground.getAt 0
                (ground.bumpAt i w) i) honeH
            obtain ⟨_, _, _, _, hD⟩ :=
              partnerReads hid hjd (.inr ⟨rfl, rfl, hji⟩) harr
                hs1 hs2 hhit hone
            have hD' := hD side
            rw [if_neg hij, if_pos hji] at hD'
            rw [if_neg hij, if_pos hji]
            by_cases hiS : i
                < sOffGo i j (ground.bumpAt i w) d
            · rw [if_pos hiS] at hD'
              rw [if_pos hiS, Nat.zero_add]
              exact hD'.symm
            · rw [if_neg hiS] at hD'
              rw [if_neg hiS]
              exact hD'.symm
    rw [sideCount_off harr side, sideCount_off harr (!side), hcs]
  | true =>
    have hfold : ∀ tb : Bool,
        tb = parity (permOf d (ground.bumpAt i w)) →
        cofSum i d w tb
            = ground.famFold Nat.add 0
                (fun j => if i < j then (1 : Nat) else 0)
                (List.range d)
              + downFold i d (ground.bumpAt i w)
          ∧ cofSum i d w (!tb)
            = upFold i d (ground.bumpAt i w) := by
      intro tb htb
      have hA1 : sideCount d (unitDisp d) (ground.bumpAt i w) tb
          = 1 := by
        rw [sideCount_arr harr tb, if_pos htb]
      have hA0 : sideCount d (unitDisp d) (ground.bumpAt i w)
          (!tb) = 0 := by
        rw [sideCount_arr harr (!tb),
          if_neg (fun hc : (!tb)
              = parity (permOf d (ground.bumpAt i w)) => by
            rw [htb] at hc
            exact ground.boolNotSelf _ hc)]
      have hnotb : (!tb)
          = !(parity (permOf d (ground.bumpAt i w))) :=
        congrArg (fun b : Bool => !b) htb
      have htbne : ¬ tb
          = !(parity (permOf d (ground.bumpAt i w))) := by
        rw [htb]
        intro hc
        exact ground.boolNotSelf _ hc.symm
      constructor
      · rw [hcof tb]
        rw [ground.famFold_congr_members Nat.add 0 _
          (fun j => (if i < j then (1 : Nat) else 0)
            + (if j < i then
              (if ground.getAt 0 (ground.bumpAt i w) j
                  < ground.getAt 0 (ground.bumpAt i w) i
                then (1 : Nat) else 0)
              else 0))
          (List.range d) (fun j hj => by
            have hjd : j < d := ground.ltOfMem hj
            by_cases hij : i < j
            · rw [if_pos hij, if_pos hij,
                if_neg (fun hc : j < i =>
                  Nat.lt_irrefl i (Nat.lt_trans hij hc)),
                hA1,
                lineFold_disp (Nat.ne_of_lt hij) hid hjd harr tb,
                if_neg htbne]
              by_cases hk : ground.getAt 0 (ground.bumpAt i w) i
                  < ground.getAt 0 (ground.bumpAt i w) j
              · rw [if_pos hk]
              · rw [if_neg hk]
            · rw [if_neg hij, if_neg hij]
              by_cases hji : j < i
              · rw [if_pos hji, if_pos hji,
                  lineFold_disp (Nat.ne_of_lt hji) hjd hid harr
                    (!tb),
                  if_pos hnotb]
                exact (Nat.zero_add _).symm
              · rw [if_neg hji, if_neg hji]),
          famFold_add_split (fun j => if i < j then (1 : Nat) else 0)
            (fun j => if j < i then
              (if ground.getAt 0 (ground.bumpAt i w) j
                  < ground.getAt 0 (ground.bumpAt i w) i
                then (1 : Nat) else 0)
              else 0)
            (List.range d)]
        rfl
      · rw [hcof (!tb)]
        rw [ground.famFold_congr_members Nat.add 0 _
          (fun j => if i < j then
            (if ground.getAt 0 (ground.bumpAt i w) i
                < ground.getAt 0 (ground.bumpAt i w) j
              then (1 : Nat) else 0)
            else 0)
          (List.range d) (fun j hj => by
            have hjd : j < d := ground.ltOfMem hj
            by_cases hij : i < j
            · rw [if_pos hij, if_pos hij, hA0,
                lineFold_disp (Nat.ne_of_lt hij) hid hjd harr
                  (!tb),
                if_pos hnotb, Nat.zero_add]
            · rw [if_neg hij, if_neg hij]
              by_cases hji : j < i
              · rw [if_pos hji,
                  lineFold_disp (Nat.ne_of_lt hji) hjd hid harr
                    (!(!tb)),
                  Bool.not_not tb, if_neg htbne]
                by_cases hk : ground.getAt 0
                    (ground.bumpAt i w) j
                    < ground.getAt 0 (ground.bumpAt i w) i
                · rw [if_pos hk]
                · rw [if_neg hk]
              · rw [if_neg hji])]
        rfl
    have hkey : ground.getAt 0 (ground.bumpAt i w) i
        + upFold i d (ground.bumpAt i w)
        = 1 + (ground.famFold Nat.add 0
            (fun j => if i < j then (1 : Nat) else 0)
            (List.range d)
          + downFold i d (ground.bumpAt i w)) := by
      have h3 : ((i + 1) + ground.famFold Nat.add 0
            (fun j => if i < j then (1 : Nat) else 0)
            (List.range d))
          + downFold i d (ground.bumpAt i w)
          = i + (1 + (ground.famFold Nat.add 0
              (fun j => if i < j then (1 : Nat) else 0)
              (List.range d)
            + downFold i d (ground.bumpAt i w))) := by
        rw [Nat.add_assoc (i + 1)
            (ground.famFold Nat.add 0
              (fun j => if i < j then (1 : Nat) else 0)
              (List.range d))
            (downFold i d (ground.bumpAt i w)),
          Nat.add_assoc i 1
            (ground.famFold Nat.add 0
              (fun j => if i < j then (1 : Nat) else 0)
              (List.range d)
            + downFold i d (ground.bumpAt i w))]
      exact addCancelL i ((placesSplit hid harr).trans
        ((congrArg
            (fun x => x + downFold i d (ground.bumpAt i w))
            (rangeSplitGt d i hid).symm).trans h3))
    by_cases hsp : side = parity (permOf d (ground.bumpAt i w))
    · obtain ⟨hcsA, hcsB⟩ := hfold side hsp
      have hA1 : sideCount d (unitDisp d) (ground.bumpAt i w)
          side = 1 := by
        rw [sideCount_arr harr side, if_pos hsp]
      have hA0 : sideCount d (unitDisp d) (ground.bumpAt i w)
          (!side) = 0 := by
        rw [sideCount_arr harr (!side),
          if_neg (fun hc : (!side)
              = parity (permOf d (ground.bumpAt i w)) => by
            rw [hsp] at hc
            exact ground.boolNotSelf _ hc)]
      rw [hA1, hA0, hcsA, hcsB, Nat.mul_one, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add]
      exact hkey
    · have hns : side
          = !(parity (permOf d (ground.bumpAt i w))) :=
        eqNotOfNe hsp
      have hnsp : (!side)
          = parity (permOf d (ground.bumpAt i w)) := by
        rw [hns]
        exact Bool.not_not _
      obtain ⟨hcsA, hcsB⟩ := hfold (!side) hnsp
      have hcsB' : cofSum i d w side
          = upFold i d (ground.bumpAt i w) :=
        ((congrArg (fun t => cofSum i d w t)
          (Bool.not_not side)).symm).trans hcsB
      have hA0 : sideCount d (unitDisp d) (ground.bumpAt i w)
          side = 0 := by
        rw [sideCount_arr harr side, if_neg hsp]
      have hA1 : sideCount d (unitDisp d) (ground.bumpAt i w)
          (!side) = 1 := by
        rw [sideCount_arr harr (!side), if_pos hnsp]
      rw [hA1, hA0, hcsA, hcsB', Nat.mul_one, Nat.mul_zero,
        Nat.zero_add 1,
        Nat.add_zero (ground.getAt 0 (ground.bumpAt i w) i)]
      exact hkey.symm

/-! The display-1 reorganization per pair (`thm:weylchar`'s
assembly): the operator identity `⟨x_a D_a : x_b D_b⟩
= x_b ⟨D_a : D_b⟩ + ⟨x_a : x_b⟩ D_a` read at the cofactor against
the alternant's clearing — the cofactor's pair-weighted fold reads
the product's `G`-read with the product's Euler read, per display
the index shift exchanging the far boundary for the head display,
the far reads canceling per swap coset at the shared zeroed
display, and `cofProd` converting the telescope fold to the
`G`-read. -/

/-- The product's Euler coefficient at a key, one side:
`[a_u · D_c ch]_z`'s side — the fold over the place permutations
at the stated grading of the guarded Euler read at the permuted
display (`thm:weylchar`'s `V D_p ch` at the alternant's
clearing). -/
def prodD (mult : List Nat → Nat) (c d : Nat) (z : List Nat)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      if parity p = side then dAtGap mult c z (expo (unitDisp d) p)
      else 0)
    (perms d)

/-- The cofactor's pair-weighted fold at a key, one side:
`[e·Q_ab ⊗ ⟨x_a D_a ch : x_b D_b ch⟩]_z`'s side at the alternant's
clearing — per permutation the guarded Euler reads over the moved
displays at the letter the grading composes: the first member's
range is the index-shifted one, the letter's own shift absorbing
one move so the head display enters and the far boundary drops,
and the second member's is the moved displays themselves
(`thm:weylchar`'s `Q_pq ⟨x_p D_p ch : x_q D_q ch⟩`, the pair's two
`D_i V`-terms collected). -/
def cofDFold (mult : List Nat → Nat) (a b d : Nat) (z : List Nat)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      if xor side (parity p) then
        ground.famFold Nat.add 0
          (fun k => dAtGap mult b z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
      else
        ground.famFold Nat.add 0
          (fun j => dAtGap mult a z
            (moveBy b a j (expo (unitDisp d) p)))
          (List.range (ground.getAt 0 (expo (unitDisp d) p) a)))
    (perms d)

private theorem xorFlip : ∀ s : Bool, xor s (!s) = true
  | false => rfl
  | true => rfl

/-- The per-display index shift, Nat-exact: the first member's fold
from the head display with the far boundary joins the fold over the
moved displays with the head — the range's two ends exchanged
through the pure telescope. -/
private theorem cofDShift (mult : List Nat → Nat) (a b : Nat)
    (z W : List Nat) :
    ground.famFold Nat.add 0
        (fun j => dAtGap mult a z (moveBy b a j W))
        (List.range (ground.getAt 0 W a))
      + dAtGap mult a z (moveBy b a (ground.getAt 0 W a) W)
    = ground.famFold Nat.add 0
        (fun k => dAtGap mult a z (moveBy b a k W))
        ((List.range (ground.getAt 0 W a)).map (fun k => k + 1))
      + dAtGap mult a z W := by
  have hmap : ground.famFold Nat.add 0
      (fun k => dAtGap mult a z (moveBy b a k W))
      ((List.range (ground.getAt 0 W a)).map (fun k => k + 1))
    = ground.famFold Nat.add 0
      (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
      (List.range (ground.getAt 0 W a)) :=
    ground.famFold_map Nat.add 0 _ _ _
  have ht : ground.famFold Nat.add 0
      (fun l => dAtGap mult a z (moveBy b a l W))
      (List.range (ground.getAt 0 W a))
      + dAtGap mult a z (moveBy b a (ground.getAt 0 W a) W)
    = dAtGap mult a z (moveBy b a 0 W)
      + ground.famFold Nat.add 0
        (fun l => dAtGap mult a z (moveBy b a (l + 1) W))
        (List.range (ground.getAt 0 W a)) :=
    teleSum (ground.getAt 0 W a)
      (fun l => dAtGap mult a z (moveBy b a l W))
  rw [moveBy_zero b a W] at ht
  rw [ht, hmap,
    Nat.add_comm (dAtGap mult a z W)
      (ground.famFold Nat.add 0
        (fun j => dAtGap mult a z (moveBy b a (j + 1) W))
        (List.range (ground.getAt 0 W a)))]

/-- The split at a side: the pair-weighted fold with the far
boundary's guarded fold joins the telescope fold with the product's
Euler read — per display the index shift at the first member, the
second member's reads shared outright. -/
private theorem cofDSplit (mult : List Nat → Nat) (a b d : Nat)
    (z : List Nat) (side : Bool) :
    cofDFold mult a b d z side
      + ground.famFold Nat.add 0
        (fun p =>
          if parity p = side then
            dAtGap mult a z
              (moveBy b a
                (ground.getAt 0 (expo (unitDisp d) p) a)
                (expo (unitDisp d) p))
          else 0)
        (perms d)
    = cofFold mult a b d z side + prodD mult a d z side := by
  show ground.famFold Nat.add 0
      (fun p =>
        if xor side (parity p) then
          ground.famFold Nat.add 0
            (fun k => dAtGap mult b z
              (moveBy b a k (expo (unitDisp d) p)))
            ((List.range
                (ground.getAt 0 (expo (unitDisp d) p) a)).map
              (fun k => k + 1))
        else
          ground.famFold Nat.add 0
            (fun j => dAtGap mult a z
              (moveBy b a j (expo (unitDisp d) p)))
            (List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)))
      (perms d)
      + ground.famFold Nat.add 0
        (fun p =>
          if parity p = side then
            dAtGap mult a z
              (moveBy b a
                (ground.getAt 0 (expo (unitDisp d) p) a)
                (expo (unitDisp d) p))
          else 0)
        (perms d)
    = ground.famFold Nat.add 0
      (fun p =>
        ground.famFold Nat.add 0
          (fun k => dAtGap mult
            (if xor side (parity p) then b else a) z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1)))
      (perms d)
      + ground.famFold Nat.add 0
        (fun p =>
          if parity p = side then
            dAtGap mult a z (expo (unitDisp d) p)
          else 0)
        (perms d)
  rw [← famFold_add_split
      (fun p =>
        if xor side (parity p) then
          ground.famFold Nat.add 0
            (fun k => dAtGap mult b z
              (moveBy b a k (expo (unitDisp d) p)))
            ((List.range
                (ground.getAt 0 (expo (unitDisp d) p) a)).map
              (fun k => k + 1))
        else
          ground.famFold Nat.add 0
            (fun j => dAtGap mult a z
              (moveBy b a j (expo (unitDisp d) p)))
            (List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)))
      (fun p =>
        if parity p = side then
          dAtGap mult a z
            (moveBy b a
              (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
        else 0)
      (perms d),
    ← famFold_add_split
      (fun p =>
        ground.famFold Nat.add 0
          (fun k => dAtGap mult
            (if xor side (parity p) then b else a) z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1)))
      (fun p =>
        if parity p = side then
          dAtGap mult a z (expo (unitDisp d) p)
        else 0)
      (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p _ => ?_)
  show (if xor side (parity p) then
        ground.famFold Nat.add 0
          (fun k => dAtGap mult b z
            (moveBy b a k (expo (unitDisp d) p)))
          ((List.range
              (ground.getAt 0 (expo (unitDisp d) p) a)).map
            (fun k => k + 1))
      else
        ground.famFold Nat.add 0
          (fun j => dAtGap mult a z
            (moveBy b a j (expo (unitDisp d) p)))
          (List.range (ground.getAt 0 (expo (unitDisp d) p) a)))
      + (if parity p = side then
          dAtGap mult a z
            (moveBy b a
              (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
        else 0)
    = ground.famFold Nat.add 0
        (fun k => dAtGap mult
          (if xor side (parity p) then b else a) z
          (moveBy b a k (expo (unitDisp d) p)))
        ((List.range
            (ground.getAt 0 (expo (unitDisp d) p) a)).map
          (fun k => k + 1))
      + (if parity p = side then
          dAtGap mult a z (expo (unitDisp d) p)
        else 0)
  by_cases hpar : parity p = side
  · have hx : xor side (parity p) = false := by
      rw [hpar]
      exact Bool.xor_self side
    have hnx : ¬ xor side (parity p) = true :=
      fun hc => Bool.noConfusion (hx.symm.trans hc)
    rw [if_neg hnx, if_neg hnx, if_pos hpar, if_pos hpar]
    exact cofDShift mult a b z (expo (unitDisp d) p)
  · have hp' : parity p = !side := eqNotOfNe hpar
    have hx : xor side (parity p) = true := by
      rw [hp']
      exact xorFlip side
    rw [if_pos hx, if_pos hx, if_neg hpar, if_neg hpar]

/-- The far boundaries cancel per swap coset at the guarded Euler
read: a coset's two members walk to one far display at opposite
gradings — the shared zeroed display's read, the reindex at the
places' transposition. -/
private theorem farCancelD (mult : List Nat → Nat) {a b d : Nat}
    (hab : a < b) (hbd : b < d) (z : List Nat) :
    ground.famFold Nat.add 0
      (fun p =>
        if parity p = false then
          dAtGap mult a z
            (moveBy b a
              (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
        else 0)
      (perms d)
    = ground.famFold Nat.add 0
      (fun p =>
        if parity p = true then
          dAtGap mult a z
            (moveBy b a
              (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
        else 0)
      (perms d) := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have had : a < d := Nat.lt_trans hab hbd
  rw [ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun p =>
      if parity p = false then
        dAtGap mult a z
          (moveBy b a
            (ground.getAt 0 (expo (unitDisp d) p) a)
            (expo (unitDisp d) p))
      else 0)
    (l := perms d) (g := swapPair a b) (h := swapPair a b)
    (monomialsAt_distinct _)
    (fun p _ => swapPair_swapPair a b p)
    (fun p _ => swapPair_swapPair a b p)
    (fun p hp => swapKey_member hp)
    (fun p hp => swapKey_member hp)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  obtain ⟨hplen, hpdist, _, _⟩ := perm_member_reads hp
  have hap : a < p.length := by rw [hplen]; exact had
  have hbp : b < p.length := by rw [hplen]; exact hbd
  have hWlen : (expo (unitDisp d) p).length = p.length := by
    show (p.map (ground.getAt 0 (unitDisp d))).length = p.length
    rw [ground.length_map]
  have hexpo : expo (unitDisp d) (swapPair a b p)
      = swapPair a b (expo (unitDisp d) p) := by
    show (swapPair a b p).map (ground.getAt 0 (unitDisp d)) = _
    rw [← swapPair_map (ground.getAt 0 (unitDisp d)) a b p]
    rfl
  show (if parity (swapPair a b p) = false then
      dAtGap mult a z
        (moveBy b a
          (ground.getAt 0
            (expo (unitDisp d) (swapPair a b p)) a)
          (expo (unitDisp d) (swapPair a b p)))
    else 0)
    = (if parity p = true then
        dAtGap mult a z
          (moveBy b a
            (ground.getAt 0 (expo (unitDisp d) p) a)
            (expo (unitDisp d) p))
      else 0)
  rw [hexpo, parity_swapPair p hne hap hbp hpdist,
    farShared hne (expo (unitDisp d) p)
      (by rw [hWlen]; exact hap) (by rw [hWlen]; exact hbp)]
  cases hpar : parity p with
  | false => rfl
  | true => rfl

private theorem shQ1 (x g p f c : Nat) :
    ((x + g) + p) + (f + c) = (x + f) + ((g + c) + p) := by
  have hL : ((x + g) + p) + (f + c)
      = x + (g + (p + (f + c))) := by
    rw [Nat.add_assoc (x + g) p (f + c),
      Nat.add_assoc x g (p + (f + c))]
  have hR : (x + f) + ((g + c) + p)
      = x + (g + (p + (f + c))) := by
    rw [Nat.add_assoc x f ((g + c) + p), Nat.add_assoc g c p,
      Nat.add_left_comm f g (c + p), ← Nat.add_assoc f c p,
      Nat.add_comm (f + c) p]
  rw [hL, hR]

private theorem shQ2 (v w g c p : Nat) :
    (v + w) + ((g + c) + p) = (g + v) + ((w + p) + c) := by
  have hL : (v + w) + ((g + c) + p)
      = g + (v + (w + (p + c))) := by
    rw [Nat.add_assoc v w ((g + c) + p), Nat.add_assoc g c p,
      Nat.add_left_comm w g (c + p), Nat.add_left_comm v g
        (w + (c + p)), Nat.add_comm c p]
  have hR : (g + v) + ((w + p) + c)
      = g + (v + (w + (p + c))) := by
    rw [Nat.add_assoc g v ((w + p) + c), Nat.add_assoc w p c]
  rw [hL, hR]

private theorem shQ3 (g c p q : Nat) :
    (g + c) + ((p + q) + c) = (c + q) + ((g + c) + p) := by
  have hL : (g + c) + ((p + q) + c)
      = g + (c + (p + (q + c))) := by
    rw [Nat.add_assoc g c ((p + q) + c), Nat.add_assoc p q c]
  have hR : (c + q) + ((g + c) + p)
      = g + (c + (p + (q + c))) := by
    rw [Nat.add_assoc c q ((g + c) + p), Nat.add_assoc g c p,
      Nat.add_left_comm q g (c + p),
      Nat.add_left_comm c g (q + (c + p)),
      Nat.add_comm c p, Nat.add_left_comm q p c]
  rw [hL, hR]

/-- The display-1 read (`thm:weylchar`'s assembly): per pair the
operator identity `⟨x_a D_a : x_b D_b⟩ = x_b ⟨D_a : D_b⟩
+ ⟨x_a : x_b⟩ D_a` reads at the cofactor against the alternant's
clearing, `Q_ab ⟨x_a D_a ch : x_b D_b ch⟩ = a_u G_ab + a_u D_a ch`
coefficientwise — the crossed equation of the pair-weighted
cofactor fold with the product's `G`-read and Euler read, the
per-display index shift exchanging the far boundary for the head,
the far reads canceling per swap coset, and the telescope fold
converting through `cofProd`. -/
theorem cofDProd (mult : List Nat → Nat) {a b d : Nat}
    (hab : a < b) (hbd : b < d) (z : List Nat)
    (hz : z.length = d)
    (hsym : ∀ (i j : Nat) (nu : List Nat), i < j → j < d →
      nu.length = d → mult (swapPair i j nu) = mult nu) :
    cofDFold mult a b d z false + prodG mult a b d z true
        + prodD mult a d z true
      = cofDFold mult a b d z true + prodG mult a b d z false
        + prodD mult a d z false := by
  have hE1 := cofDSplit mult a b d z false
  have hE2 := cofDSplit mult a b d z true
  rw [farCancelD mult hab hbd z] at hE1
  have hE4 := cofProd mult hab hbd z hz hsym
  refine addCancelR
    (ground.famFold Nat.add 0
      (fun p =>
        if parity p = true then
          dAtGap mult a z
            (moveBy b a
              (ground.getAt 0 (expo (unitDisp d) p) a)
              (expo (unitDisp d) p))
        else 0)
      (perms d)
    + cofFold mult a b d z true) ?_
  rw [shQ1 (cofDFold mult a b d z false) (prodG mult a b d z true)
      (prodD mult a d z true)
      (ground.famFold Nat.add 0
        (fun p =>
          if parity p = true then
            dAtGap mult a z
              (moveBy b a
                (ground.getAt 0 (expo (unitDisp d) p) a)
                (expo (unitDisp d) p))
          else 0)
        (perms d))
      (cofFold mult a b d z true),
    hE1,
    shQ2 (cofFold mult a b d z false) (prodD mult a d z false)
      (prodG mult a b d z true) (cofFold mult a b d z true)
      (prodD mult a d z true),
    ← hE4,
    shQ1 (cofDFold mult a b d z true) (prodG mult a b d z false)
      (prodD mult a d z false)
      (ground.famFold Nat.add 0
        (fun p =>
          if parity p = true then
            dAtGap mult a z
              (moveBy b a
                (ground.getAt 0 (expo (unitDisp d) p) a)
                (expo (unitDisp d) p))
          else 0)
        (perms d))
      (cofFold mult a b d z true),
    hE2,
    shQ3 (prodG mult a b d z false) (cofFold mult a b d z true)
      (prodD mult a d z false) (prodD mult a d z true)]

/-! The Leibniz-square collection's kit (`thm:weylchar`'s
assembly): the tie's square split with its invariance at the
permuted displays, over the fold and enumeration reads at their
`ground` and `places` homes. -/

/-- The tie's reconstruction: the key is the entrywise join of the
solution with the display. -/
private theorem tieGap_zip :
    ∀ (y z m : List Nat), tieGap y z = some m →
      y = List.zipWith (fun a b => a + b) m z :=
  fun y z m h => by
    obtain ⟨hml, hzl, hent⟩ := tieGap_reads y z m h
    exact ground.getAt_ext 0 y (List.zipWith (fun a b => a + b) m z)
      (ground.length_zipWith (fun a b => a + b) m z y.length hml hzl).symm
      (fun i hi => ((ground.getAt_zipWith 0 0 0 (fun a b => a + b) m z i
          (by rw [hml]; exact hi) (by rw [hzl]; exact hi)).trans
        (hent i hi)).symm)

private theorem shuffle4 (A X B : Nat) :
    (A + X) + (X + B) = (B + (X + X)) + A := by
  have hL : (A + X) + (X + B) = A + ((X + X) + B) := by
    rw [Nat.add_assoc A X (X + B), ← Nat.add_assoc X X B]
  have hR : (B + (X + X)) + A = A + ((X + X) + B) := by
    rw [Nat.add_comm (B + (X + X)) A, Nat.add_comm B (X + X)]
  rw [hL, hR]

/-- Three seeded sums regroup, the heads collecting against the
tails. -/
private theorem addCross3 (a x b y c z : Nat) :
    a + x + (b + y) + (c + z) = a + b + c + (x + y + z) := by
  rw [Nat.add_add_add_comm a x b y,
    Nat.add_add_add_comm (a + b) (x + y) c z]

private theorem sqScalar (b c : Nat) :
    (c + b) * (c + b) = b * b + 2 * (b * c) + c * c := by
  rw [mulAddR c b (c + b), Nat.left_distrib c c b,
    Nat.left_distrib b c b, Nat.mul_comm c b, Nat.two_mul (b * c)]
  exact shuffle4 (c * c) (b * c) (b * b)

/-- The square's split at the entrywise join: the two parts'
squares with the doubled dot (`thm:weylchar`'s Leibniz square at
the collection). -/
theorem sqSplit :
    ∀ (x y : List Nat), x.length = y.length →
      stdSq (List.zipWith (fun a b => a + b) x y)
        = stdSq x + 2 * ground.dotNat x y + stdSq y
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | c :: x, e :: y, h => by
    show (c + e) * (c + e)
        + stdSq (List.zipWith (fun a b => a + b) x y)
      = c * c + stdSq x
        + 2 * (c * e + ground.dotNat x y) + (e * e + stdSq y)
    rw [sqSplit x y (Nat.succ.inj h), Nat.add_comm c e, sqScalar c e,
      Nat.left_distrib 2 (c * e) (ground.dotNat x y)]
    exact (addCross3 (c * c) (stdSq x) (2 * (c * e))
      (2 * ground.dotNat x y) (e * e) (stdSq y)).symm

private theorem expoRange (d : Nat) :
    expo (unitDisp d) (List.range d) = unitDisp d := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · show ((List.range d).map
        (ground.getAt 0 (unitDisp d))).length
      = (unitDisp d).length
    rw [ground.length_mapRange, length_unitDisp]
  · intro i hi
    have hid : i < d := by
      show i < d
      rw [← length_range d]
      have hl : ((List.range d).map
          (ground.getAt 0 (unitDisp d))).length
          = (List.range d).length := ground.length_map _ _
      rw [← hl]
      exact hi
    show ground.getAt 0 ((List.range d).map
        (ground.getAt 0 (unitDisp d))) i
      = ground.getAt 0 (unitDisp d) i
    rw [ground.getAt_map 0 0 (ground.getAt 0 (unitDisp d))
        (List.range d) i (by rw [length_range]; exact hid),
      getAt_range d i hid]

/-- The standard square at a permuted display: one value at every
permutation, `q` at every arrangement (`thm:weylchar`'s
assembly). -/
private theorem sqPerm {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    stdSq (expo (unitDisp d) p) = stdSq (unitDisp d) := by
  have h1 : stdSq (expo (unitDisp d) p)
      = ground.famFold Nat.add 0
        (fun x => ground.getAt 0 (unitDisp d) x
          * ground.getAt 0 (unitDisp d) x) p := by
    show sumNat ((p.map (ground.getAt 0 (unitDisp d))).map
      (fun a => a * a)) = _
    rw [ground.map_map (ground.getAt 0 (unitDisp d))
      (fun a => a * a) p]
    exact sumMap _ p
  have h2 : stdSq (unitDisp d)
      = ground.famFold Nat.add 0
        (fun x => ground.getAt 0 (unitDisp d) x
          * ground.getAt 0 (unitDisp d) x) (List.range d) := by
    have h3 : stdSq (expo (unitDisp d) (List.range d))
        = ground.famFold Nat.add 0
          (fun x => ground.getAt 0 (unitDisp d) x
            * ground.getAt 0 (unitDisp d) x) (List.range d) := by
      show sumNat (((List.range d).map
        (ground.getAt 0 (unitDisp d))).map (fun a => a * a)) = _
      rw [ground.map_map (ground.getAt 0 (unitDisp d))
        (fun a => a * a) (List.range d)]
      exact sumMap _ (List.range d)
    rw [← h3, expoRange d]
  rw [h1, h2]
  exact ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
    _ p (List.range d) (places.perm_counts_range _ hp)

/-- The tie fold: the guarded read over the place permutations at
a side — every collection fold below an instance at its member
read, the products' coefficients per `def:poly`'s convolution. -/
private def tieFold (d : Nat) (y : List Nat) (side : Bool)
    (F : List Nat → List Nat → Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      if parity p = side then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
    (perms d)

private theorem prodCount_tie (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    prodCount mult d y s = tieFold d y s (fun _ chi => mult chi) :=
  rfl

private theorem tieFold_add (d : Nat) (y : List Nat) (s : Bool)
    (F G : List Nat → List Nat → Nat) :
    tieFold d y s F + tieFold d y s G
      = tieFold d y s (fun W chi => F W chi + G W chi) := by
  show ground.famFold Nat.add 0 _ (perms d)
      + ground.famFold Nat.add 0 _ (perms d)
    = ground.famFold Nat.add 0 _ (perms d)
  rw [← famFold_add_split
    (fun p =>
      if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
    (fun p =>
      if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => G (expo (unitDisp d) p) chi
        | none => 0
      else 0)
    (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p _ => ?_)
  by_cases hpar : parity p = s
  · show (if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
      + (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => G (expo (unitDisp d) p) chi
          | none => 0
        else 0)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => F (expo (unitDisp d) p) chi
              + G (expo (unitDisp d) p) chi
          | none => 0
        else 0)
    rw [if_pos hpar, if_pos hpar, if_pos hpar]
    cases ht : tieGap y (expo (unitDisp d) p) with
    | some chi => rfl
    | none => rfl
  · show (if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
      + (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => G (expo (unitDisp d) p) chi
          | none => 0
        else 0)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => F (expo (unitDisp d) p) chi
              + G (expo (unitDisp d) p) chi
          | none => 0
        else 0)
    rw [if_neg hpar, if_neg hpar, if_neg hpar]

private theorem tieFold_mul (c : Nat) (d : Nat) (y : List Nat)
    (s : Bool) (F : List Nat → List Nat → Nat) :
    c * tieFold d y s F
      = tieFold d y s (fun W chi => c * F W chi) := by
  show c * ground.famFold Nat.add 0 _ (perms d)
    = ground.famFold Nat.add 0 _ (perms d)
  rw [famFold_mul c
    (fun p =>
      if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
    (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p _ => ?_)
  by_cases hpar : parity p = s
  · show c * (if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => c * F (expo (unitDisp d) p) chi
          | none => 0
        else 0)
    rw [if_pos hpar, if_pos hpar]
    cases ht : tieGap y (expo (unitDisp d) p) with
    | some chi => rfl
    | none => exact Nat.mul_zero c
  · show c * (if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => c * F (expo (unitDisp d) p) chi
          | none => 0
        else 0)
    rw [if_neg hpar, if_neg hpar]
    exact Nat.mul_zero c

private theorem tieFold_congr (d : Nat) (y : List Nat) (s : Bool)
    (F G : List Nat → List Nat → Nat)
    (h : ∀ p, 0 < ground.countOf p (perms d) →
      ∀ chi, tieGap y (expo (unitDisp d) p) = some chi →
        F (expo (unitDisp d) p) chi
          = G (expo (unitDisp d) p) chi) :
    tieFold d y s F = tieFold d y s G := by
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  by_cases hpar : parity p = s
  · show (if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => G (expo (unitDisp d) p) chi
          | none => 0
        else 0)
    rw [if_pos hpar, if_pos hpar]
    cases ht : tieGap y (expo (unitDisp d) p) with
    | some chi => exact h p hp chi ht
    | none => rfl
  · show (if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F (expo (unitDisp d) p) chi
        | none => 0
      else 0)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => G (expo (unitDisp d) p) chi
          | none => 0
        else 0)
    rw [if_neg hpar, if_neg hpar]

/-- The Leibniz square's split at the tie (`thm:weylchar`'s
assembly): the key's square against the product's coefficient
opens as the arrangement's one value with the doubled dot and the
content's square, per member. -/
private theorem leibSplit (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    stdSq y * prodCount mult d y s
      = stdSq (unitDisp d) * prodCount mult d y s
        + 2 * tieFold d y s (fun W chi => ground.dotNat W chi * mult chi)
        + tieFold d y s (fun _ chi => stdSq chi * mult chi) := by
  rw [prodCount_tie mult d y s,
    tieFold_mul (stdSq y) d y s (fun _ chi => mult chi),
    tieFold_mul (stdSq (unitDisp d)) d y s (fun _ chi => mult chi),
    tieFold_mul 2 d y s (fun W chi => ground.dotNat W chi * mult chi),
    tieFold_add d y s
      (fun _ chi => stdSq (unitDisp d) * mult chi)
      (fun W chi => 2 * (ground.dotNat W chi * mult chi)),
    tieFold_add d y s
      (fun W chi => stdSq (unitDisp d) * mult chi
        + 2 * (ground.dotNat W chi * mult chi))
      (fun _ chi => stdSq chi * mult chi)]
  refine tieFold_congr d y s _ _ (fun p hp chi ht => ?_)
  obtain ⟨hml, hzl, _⟩ := tieGap_reads y (expo (unitDisp d) p) chi ht
  have hy : stdSq y = stdSq (expo (unitDisp d) p)
      + 2 * ground.dotNat (expo (unitDisp d) p) chi + stdSq chi := by
    rw [tieGap_zip y (expo (unitDisp d) p) chi ht,
      sqSplit chi (expo (unitDisp d) p) (by rw [hml, hzl]),
      places.dotNat_comm chi (expo (unitDisp d) p)]
    exact addSwapEnds (stdSq chi)
      (2 * ground.dotNat (expo (unitDisp d) p) chi)
      (stdSq (expo (unitDisp d) p))
  rw [hy, sqPerm hp,
    mulAddR (stdSq (unitDisp d)
        + 2 * ground.dotNat (expo (unitDisp d) p) chi)
      (stdSq chi) (mult chi),
    mulAddR (stdSq (unitDisp d))
      (2 * ground.dotNat (expo (unitDisp d) p) chi) (mult chi),
    mulAssoc 2 (ground.dotNat (expo (unitDisp d) p) chi) (mult chi)]

/-- The tie's length at a member: the content reads the count. -/
private theorem tieLen {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) {y chi : List Nat}
    (ht : tieGap y (expo (unitDisp d) p) = some chi) :
    chi.length = d := by
  obtain ⟨hml, hzl, _⟩ := tieGap_reads y (expo (unitDisp d) p) chi ht
  obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
  have hel : (expo (unitDisp d) p).length = d := by
    show (p.map (ground.getAt 0 (unitDisp d))).length = d
    rw [ground.length_map, hplen]
  rw [hml, ← hzl, hel]

/-- The unit square's split at the shifted content: `q(nu+u)`
opens per member (`thm:weylchar`'s assembly, the collection's
display). -/
private theorem uSplit (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    tieFold d y s (fun _ chi =>
        stdSq (List.zipWith (fun a b => a + b) chi (unitDisp d))
          * mult chi)
      = tieFold d y s (fun _ chi => stdSq chi * mult chi)
        + 2 * tieFold d y s
          (fun _ chi => ground.dotNat (unitDisp d) chi * mult chi)
        + stdSq (unitDisp d) * prodCount mult d y s := by
  rw [prodCount_tie mult d y s,
    tieFold_mul (stdSq (unitDisp d)) d y s (fun _ chi => mult chi),
    tieFold_mul 2 d y s
      (fun _ chi => ground.dotNat (unitDisp d) chi * mult chi),
    tieFold_add d y s
      (fun _ chi => stdSq chi * mult chi)
      (fun _ chi => 2 * (ground.dotNat (unitDisp d) chi * mult chi)),
    tieFold_add d y s
      (fun _ chi => stdSq chi * mult chi
        + 2 * (ground.dotNat (unitDisp d) chi * mult chi))
      (fun _ chi => stdSq (unitDisp d) * mult chi)]
  refine tieFold_congr d y s _ _ (fun p hp chi ht => ?_)
  have hcl : chi.length = d := tieLen hp ht
  have hz : stdSq (List.zipWith (fun a b => a + b) chi (unitDisp d))
      = stdSq (unitDisp d) + 2 * ground.dotNat (unitDisp d) chi
        + stdSq chi := by
    rw [sqSplit chi (unitDisp d) (by rw [hcl, length_unitDisp]),
      places.dotNat_comm chi (unitDisp d)]
    exact addSwapEnds (stdSq chi)
      (2 * ground.dotNat (unitDisp d) chi) (stdSq (unitDisp d))
  rw [hz,
    mulAddR (stdSq (unitDisp d) + 2 * ground.dotNat (unitDisp d) chi)
      (stdSq chi) (mult chi),
    mulAddR (stdSq (unitDisp d)) (2 * ground.dotNat (unitDisp d) chi)
      (mult chi),
    mulAssoc 2 (ground.dotNat (unitDisp d) chi) (mult chi),
    addSwapEnds (stdSq (unitDisp d) * mult chi)
      (2 * (ground.dotNat (unitDisp d) chi * mult chi))
      (stdSq chi * mult chi)]

/-- The trace recursion folded over the ties (`thm:weylchar`'s
hypothesis display consumed coefficientwise). -/
private theorem recFold (mult : List Nat → Nat) (lam : Shape)
    (hrec : recReadE lam mult) (y : List Nat) (s : Bool) :
    stdSq (display lam) * prodCount mult lam.length y s
        + 2 * tieFold lam.length y s
          (fun _ chi => movedSnd mult chi)
      = tieFold lam.length y s (fun _ chi =>
          stdSq (List.zipWith (fun a b => a + b) chi
            (unitDisp lam.length)) * mult chi)
        + 2 * tieFold lam.length y s
          (fun _ chi => movedFst mult chi) := by
  rw [prodCount_tie mult lam.length y s,
    tieFold_mul (stdSq (display lam)) lam.length y s
      (fun _ chi => mult chi),
    tieFold_mul 2 lam.length y s (fun _ chi => movedSnd mult chi),
    tieFold_mul 2 lam.length y s (fun _ chi => movedFst mult chi),
    tieFold_add lam.length y s
      (fun _ chi => stdSq (display lam) * mult chi)
      (fun _ chi => 2 * movedSnd mult chi),
    tieFold_add lam.length y s
      (fun _ chi =>
        stdSq (List.zipWith (fun a b => a + b) chi
          (unitDisp lam.length)) * mult chi)
      (fun _ chi => 2 * movedFst mult chi)]
  refine tieFold_congr lam.length y s _ _ (fun p hp chi ht => ?_)
  exact hrec chi (tieLen hp ht)

/-- The `G`-folds regroup over the letter pairs: the pairs' graded
product reads collect to the moved folds at the two parities
(`thm:weylchar`'s recursion members at the product). -/
private theorem gRegroup (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 d y s) (pairsOf d)
      = tieFold d y s (fun _ chi => movedFst mult chi)
        + tieFold d y (!s) (fun _ chi => movedSnd mult chi) := by
  show ground.famFold Nat.add 0
      (fun ab => ground.famFold Nat.add 0
        (fun p => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
          (xor s (parity p)))
        (perms d))
      (pairsOf d)
    = tieFold d y s (fun _ chi => movedFst mult chi)
      + tieFold d y (!s) (fun _ chi => movedSnd mult chi)
  rw [famFold_swap
    (fun ab p => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
      (xor s (parity p)))
    (pairsOf d) (perms d)]
  rw [ground.famFold_congr_all Nat.add 0
    (fun p => ground.famFold Nat.add 0
      (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
        (xor s (parity p)))
      (pairsOf d))
    (fun p =>
      (if parity p = s then
        ground.famFold Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            (xor s (parity p)))
          (pairsOf d)
      else 0)
      + (if parity p = (!s) then
          ground.famFold Nat.add 0
            (fun ab => gAtGap mult ab.1 ab.2 y
              (expo (unitDisp d) p) (xor s (parity p)))
            (pairsOf d)
        else 0))
    (fun p => by
      by_cases hpar : parity p = s
      · rw [if_pos hpar,
          if_neg (fun hc : parity p = (!s) => by
            rw [hpar] at hc
            exact ground.boolNotSelf s hc.symm)]
        rfl
      · rw [if_neg hpar, if_pos (eqNotOfNe hpar), Nat.zero_add])
    (perms d)]
  have hfst : ground.famFold Nat.add 0
      (fun p =>
        if parity p = s then
          ground.famFold Nat.add 0
            (fun ab => gAtGap mult ab.1 ab.2 y
              (expo (unitDisp d) p) (xor s (parity p)))
            (pairsOf d)
        else 0)
      (perms d)
    = tieFold d y s (fun _ chi => movedFst mult chi) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
      (fun p hp => ?_)
    by_cases hpar : parity p = s
    · rw [if_pos hpar]
      show ground.famFold Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            (xor s (parity p)))
          (pairsOf d)
        = (if parity p = s then
            match tieGap y (expo (unitDisp d) p) with
            | some chi => movedFst mult chi
            | none => 0
          else 0)
      rw [if_pos hpar, hpar, Bool.xor_self s]
      cases ht : tieGap y (expo (unitDisp d) p) with
      | some chi =>
        have hcl : chi.length = d := tieLen hp ht
        rw [ground.famFold_congr_all Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            false)
          (fun ab => gFst mult chi ab.1 ab.2)
          (fun ab => by
            show (match tieGap y (expo (unitDisp d) p) with
              | some chi' =>
                if false then gSnd mult chi' ab.1 ab.2
                else gFst mult chi' ab.1 ab.2
              | none => 0) = gFst mult chi ab.1 ab.2
            rw [ht]
            rfl)
          (pairsOf d)]
        show ground.famFold Nat.add 0
            (fun ab => gFst mult chi ab.1 ab.2) (pairsOf d)
          = ground.famFold Nat.add 0
            (fun ab => gFst mult chi ab.1 ab.2)
            (pairsOf chi.length)
        rw [hcl]
      | none =>
        rw [ground.famFold_congr_all Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            false)
          (fun _ => (0 : Nat))
          (fun ab => by
            show (match tieGap y (expo (unitDisp d) p) with
              | some chi' =>
                if false then gSnd mult chi' ab.1 ab.2
                else gFst mult chi' ab.1 ab.2
              | none => 0) = 0
            rw [ht])
          (pairsOf d),
          famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]
    · rw [if_neg hpar]
      show (0 : Nat)
        = (if parity p = s then
            match tieGap y (expo (unitDisp d) p) with
            | some chi => movedFst mult chi
            | none => 0
          else 0)
      rw [if_neg hpar]
  have hsnd : ground.famFold Nat.add 0
      (fun p =>
        if parity p = (!s) then
          ground.famFold Nat.add 0
            (fun ab => gAtGap mult ab.1 ab.2 y
              (expo (unitDisp d) p) (xor s (parity p)))
            (pairsOf d)
        else 0)
      (perms d)
    = tieFold d y (!s) (fun _ chi => movedSnd mult chi) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
      (fun p hp => ?_)
    by_cases hpar : parity p = (!s)
    · rw [if_pos hpar]
      show ground.famFold Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            (xor s (parity p)))
          (pairsOf d)
        = (if parity p = (!s) then
            match tieGap y (expo (unitDisp d) p) with
            | some chi => movedSnd mult chi
            | none => 0
          else 0)
      rw [if_pos hpar, hpar, xorFlip s]
      cases ht : tieGap y (expo (unitDisp d) p) with
      | some chi =>
        have hcl : chi.length = d := tieLen hp ht
        rw [ground.famFold_congr_all Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            true)
          (fun ab => gSnd mult chi ab.1 ab.2)
          (fun ab => by
            show (match tieGap y (expo (unitDisp d) p) with
              | some chi' =>
                if true then gSnd mult chi' ab.1 ab.2
                else gFst mult chi' ab.1 ab.2
              | none => 0) = gSnd mult chi ab.1 ab.2
            rw [ht]
            rfl)
          (pairsOf d)]
        show ground.famFold Nat.add 0
            (fun ab => gSnd mult chi ab.1 ab.2) (pairsOf d)
          = ground.famFold Nat.add 0
            (fun ab => gSnd mult chi ab.1 ab.2)
            (pairsOf chi.length)
        rw [hcl]
      | none =>
        rw [ground.famFold_congr_all Nat.add 0
          (fun ab => gAtGap mult ab.1 ab.2 y (expo (unitDisp d) p)
            true)
          (fun _ => (0 : Nat))
          (fun ab => by
            show (match tieGap y (expo (unitDisp d) p) with
              | some chi' =>
                if true then gSnd mult chi' ab.1 ab.2
                else gFst mult chi' ab.1 ab.2
              | none => 0) = 0
            rw [ht])
          (pairsOf d),
          famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]
    · rw [if_neg hpar]
      show (0 : Nat)
        = (if parity p = (!s) then
            match tieGap y (expo (unitDisp d) p) with
            | some chi => movedSnd mult chi
            | none => 0
          else 0)
      rw [if_neg hpar]
  have hjoin : ground.famFold Nat.add 0
      (fun p =>
        (if parity p = s then
          ground.famFold Nat.add 0
            (fun ab => gAtGap mult ab.1 ab.2 y
              (expo (unitDisp d) p) (xor s (parity p)))
            (pairsOf d)
        else 0)
        + (if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun ab => gAtGap mult ab.1 ab.2 y
                (expo (unitDisp d) p) (xor s (parity p)))
              (pairsOf d)
          else 0))
      (perms d)
    = ground.famFold Nat.add 0
        (fun p =>
          if parity p = s then
            ground.famFold Nat.add 0
              (fun ab => gAtGap mult ab.1 ab.2 y
                (expo (unitDisp d) p) (xor s (parity p)))
              (pairsOf d)
          else 0)
        (perms d)
      + ground.famFold Nat.add 0
        (fun p =>
          if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun ab => gAtGap mult ab.1 ab.2 y
                (expo (unitDisp d) p) (xor s (parity p)))
              (pairsOf d)
          else 0)
        (perms d) :=
    famFold_add_split _ _ (perms d)
  rw [hjoin, hfst, hsnd]

/-- The unit weights' collection at a content: the unit display's
dot opens as the content's sum with the pairs' first-letter fold
(`thm:weylchar`'s assembly, the collection
`Σ_{p<q} D_p + Σ_i D_i = Σ_i u_i D_i`). -/
private theorem uDot (d : Nat) (chi : List Nat)
    (hl : chi.length = d) :
    ground.dotNat (unitDisp d) chi
      = sumNat chi + ground.famFold Nat.add 0
        (fun ab => ground.getAt 0 chi ab.1) (pairsOf d) := by
  have h1 : ground.dotNat (unitDisp d) chi
      = ground.famFold Nat.add 0
        (fun i => ground.getAt 0 (unitDisp d) i
          * ground.getAt 0 chi i)
        (List.range d) := by
    have hd := ground.dotNat_index (unitDisp d) chi
      (by rw [length_unitDisp, hl])
    rw [length_unitDisp] at hd
    exact hd
  have h2 : sumNat chi
      = ground.famFold Nat.add 0
        (fun i => ground.getAt 0 chi i) (List.range d) := by
    have hs := (ground.sumIndex chi).symm
    rw [hl] at hs
    exact hs
  have h3 : ground.famFold Nat.add 0
      (fun ab => ground.getAt 0 chi ab.1) (pairsOf d)
    = ground.famFold Nat.add 0
      (fun a => ground.getAt 0 chi a
        * ground.famFold Nat.add 0
          (fun b => if a < b then (1 : Nat) else 0)
          (List.range d))
      (List.range d) := by
    rw [pairsFold (fun ab => ground.getAt 0 chi ab.1) d]
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun a => ?_)
      (List.range d)
    have hin : ground.famFold Nat.add 0
        (fun b => if a < b then ground.getAt 0 chi a else 0)
        (List.range d)
      = ground.famFold Nat.add 0
        (fun b => ground.getAt 0 chi a
          * (if a < b then (1 : Nat) else 0))
        (List.range d) :=
      ground.famFold_congr_all Nat.add 0 _ _
        (fun b => by
          by_cases hab : a < b
          · rw [if_pos hab, if_pos hab, Nat.mul_one]
          · rw [if_neg hab, if_neg hab, Nat.mul_zero])
        (List.range d)
    rw [hin,
      ← famFold_mul (ground.getAt 0 chi a)
        (fun b => if a < b then (1 : Nat) else 0) (List.range d)]
  rw [h1, h2, h3,
    ← famFold_add_split (fun i => ground.getAt 0 chi i)
      (fun a => ground.getAt 0 chi a
        * ground.famFold Nat.add 0
          (fun b => if a < b then (1 : Nat) else 0)
          (List.range d))
      (List.range d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (List.range d)
    (fun a ha => ?_)
  have had : a < d := ground.ltOfMem ha
  have hua : ground.getAt 0 (unitDisp d) a
      = ground.famFold Nat.add 0
        (fun b => if a < b then (1 : Nat) else 0)
        (List.range d) + 1 := by
    refine addCancelR a ?_
    rw [getAt_unitDisp d a had, subAdd (Nat.le_of_lt had)]
    exact (rangeSplitGt d a had).symm.trans
      (addSwapEnds a 1 (ground.famFold Nat.add 0
        (fun b => if a < b then (1 : Nat) else 0)
        (List.range d)))
  rw [hua, mulAddR (ground.famFold Nat.add 0
      (fun b => if a < b then (1 : Nat) else 0)
      (List.range d)) 1 (ground.getAt 0 chi a),
    Nat.one_mul,
    Nat.add_comm (ground.famFold Nat.add 0
        (fun b => if a < b then (1 : Nat) else 0)
        (List.range d) * ground.getAt 0 chi a)
      (ground.getAt 0 chi a),
    Nat.mul_comm (ground.famFold Nat.add 0
        (fun b => if a < b then (1 : Nat) else 0)
        (List.range d))
      (ground.getAt 0 chi a)]

/-- The unit dot's fold collects to the content sum with the
pairs' Euler reads (`thm:weylchar`'s assembly, the collection at
the coefficients). -/
private theorem uCollect (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    tieFold d y s (fun _ chi => ground.dotNat (unitDisp d) chi * mult chi)
      = tieFold d y s (fun _ chi => sumNat chi * mult chi)
        + ground.famFold Nat.add 0
          (fun ab => prodD mult ab.1 d y s) (pairsOf d) := by
  have hpair : ground.famFold Nat.add 0
      (fun ab => prodD mult ab.1 d y s) (pairsOf d)
    = tieFold d y s (fun _ chi =>
        ground.famFold Nat.add 0
          (fun ab => ground.getAt 0 chi ab.1) (pairsOf d)
        * mult chi) := by
    show ground.famFold Nat.add 0
      (fun ab => ground.famFold Nat.add 0
        (fun p => if parity p = s then
            dAtGap mult ab.1 y (expo (unitDisp d) p)
          else 0)
        (perms d))
      (pairsOf d) = _
    rw [famFold_swap
      (fun ab p => if parity p = s then
          dAtGap mult ab.1 y (expo (unitDisp d) p)
        else 0)
      (pairsOf d) (perms d)]
    refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
      (fun p hp => ?_)
    by_cases hpar : parity p = s
    · show ground.famFold Nat.add 0
        (fun ab => if parity p = s then
            dAtGap mult ab.1 y (expo (unitDisp d) p)
          else 0)
        (pairsOf d)
        = (if parity p = s then
            match tieGap y (expo (unitDisp d) p) with
            | some chi =>
              ground.famFold Nat.add 0
                (fun ab => ground.getAt 0 chi ab.1)
                (pairsOf d) * mult chi
            | none => 0
          else 0)
      rw [if_pos hpar,
        ground.famFold_congr_all Nat.add 0
          (fun ab => if parity p = s then
              dAtGap mult ab.1 y (expo (unitDisp d) p)
            else 0)
          (fun ab => dAtGap mult ab.1 y (expo (unitDisp d) p))
          (fun ab => by rw [if_pos hpar]) (pairsOf d)]
      cases ht : tieGap y (expo (unitDisp d) p) with
      | some chi =>
        rw [ground.famFold_congr_all Nat.add 0
          (fun ab => dAtGap mult ab.1 y (expo (unitDisp d) p))
          (fun ab => ground.getAt 0 chi ab.1 * mult chi)
          (fun ab => by
            show (match tieGap y (expo (unitDisp d) p) with
              | some chi' =>
                ground.getAt 0 chi' ab.1 * mult chi'
              | none => 0) = ground.getAt 0 chi ab.1 * mult chi
            rw [ht])
          (pairsOf d),
          famFold_mulR (mult chi)
            (fun ab => ground.getAt 0 chi ab.1) (pairsOf d)]
      | none =>
        rw [ground.famFold_congr_all Nat.add 0
          (fun ab => dAtGap mult ab.1 y (expo (unitDisp d) p))
          (fun _ => (0 : Nat))
          (fun ab => by
            show (match tieGap y (expo (unitDisp d) p) with
              | some chi' =>
                ground.getAt 0 chi' ab.1 * mult chi'
              | none => 0) = 0
            rw [ht])
          (pairsOf d),
          famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]
    · show ground.famFold Nat.add 0
        (fun ab => if parity p = s then
            dAtGap mult ab.1 y (expo (unitDisp d) p)
          else 0)
        (pairsOf d)
        = (if parity p = s then
            match tieGap y (expo (unitDisp d) p) with
            | some chi =>
              ground.famFold Nat.add 0
                (fun ab => ground.getAt 0 chi ab.1)
                (pairsOf d) * mult chi
            | none => 0
          else 0)
      rw [if_neg hpar,
        ground.famFold_congr_all Nat.add 0
          (fun ab => if parity p = s then
              dAtGap mult ab.1 y (expo (unitDisp d) p)
            else 0)
          (fun _ => (0 : Nat))
          (fun ab => by rw [if_neg hpar]) (pairsOf d),
        famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]
  rw [hpair,
    tieFold_add d y s
      (fun _ chi => sumNat chi * mult chi)
      (fun _ chi =>
        ground.famFold Nat.add 0
          (fun ab => ground.getAt 0 chi ab.1) (pairsOf d)
        * mult chi)]
  refine tieFold_congr d y s _ _ (fun p hp chi ht => ?_)
  rw [uDot d chi (tieLen hp ht),
    mulAddR (sumNat chi)
      (ground.famFold Nat.add 0
        (fun ab => ground.getAt 0 chi ab.1) (pairsOf d))
      (mult chi)]

/-- The graded counts at a display with a vacant letter read the
count's unit: every permuted display occupies every letter
(`thm:weylchar`'s assembly, the vacant-letter read). -/
private theorem sideCount_zeroEntry {d j : Nat} (hjd : j < d)
    {K : List Nat} (hK : ground.getAt 0 K j = 0) (t : Bool) :
    sideCount d (unitDisp d) K t = 0 := by
  show ground.famFold Nat.add 0
    (fun p => if parity p = t then
        (if expo (unitDisp d) p = K then 1 else 0)
      else 0)
    (perms d) = 0
  refine (ground.famFold_congr_members Nat.add 0 _
    (fun _ => (0 : Nat)) (perms d) (fun p hp => ?_)).trans
    (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d))
  by_cases hpar : parity p = t
  · rw [if_pos hpar,
      if_neg (fun he : expo (unitDisp d) p = K => by
        obtain ⟨hplen, _, hval, _⟩ := perm_member_reads hp
        have hjp : j < p.length := by rw [hplen]; exact hjd
        have hpj : ground.getAt 0 p j < d :=
          hval _ (countOf_getAt_pos 0 p j hjp)
        have hpos : 0 < ground.getAt 0 (expo (unitDisp d) p) j := by
          show 0 < ground.getAt 0
            (p.map (ground.getAt 0 (unitDisp d))) j
          rw [ground.getAt_map 0 0 _ p j hjp,
            getAt_unitDisp d _ hpj]
          exact subPos hpj
        rw [he, hK] at hpos
        exact absurd hpos (Nat.lt_irrefl 0))]
  · rw [if_neg hpar]

/-- The letter's cofactor-Euler fold at a key, one side:
`[Σ_{j≠i} e·x_i Q_ij ⊗ D_i ch]_y`'s side at the alternant's
clearing — per permutation and further letter the guarded Euler
reads at the letter over the pair's moved displays, the branch
ranges the display detection's own (`thm:weylchar`'s assembly, the
derivative display's letter slice). -/
private def cofEFold (mult : List Nat → Nat) (i d : Nat)
    (y : List Nat) (s : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun p =>
      ground.famFold Nat.add 0
        (fun j =>
          if i < j then
            (if parity p = s then
              ground.famFold Nat.add 0
                (fun l => dAtGap mult i y
                  (moveBy j i l (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) i))
            else 0)
          else if j < i then
            (if parity p = (!s) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult i y
                  (moveBy i j k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0 (expo (unitDisp d) p) j)).map
                  (fun k => k + 1))
            else 0)
          else 0)
        (List.range d))
    (perms d)

/-- A permuted display's entry: the unit value at the letter, at
least one and at most the count. -/
private theorem expoEntry {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) {t : Nat} (ht : t < d) :
    0 < ground.getAt 0 (expo (unitDisp d) p) t
      ∧ ground.getAt 0 (expo (unitDisp d) p) t ≤ d := by
  obtain ⟨hplen, _, hval, _⟩ := perm_member_reads hp
  have htp : t < p.length := by rw [hplen]; exact ht
  have hpt : ground.getAt 0 p t < d :=
    hval _ (countOf_getAt_pos 0 p t htp)
  have hread : ground.getAt 0 (expo (unitDisp d) p) t
      = d - ground.getAt 0 p t := by
    show ground.getAt 0
      (p.map (ground.getAt 0 (unitDisp d))) t = _
    rw [ground.getAt_map 0 0 _ p t htp, getAt_unitDisp d _ hpt]
  rw [hread]
  exact ⟨subPos hpt, Nat.sub_le d (ground.getAt 0 p t)⟩

/-- The `A`-count collapse at the bumped key: the letter-weighted
box fold of the graded count against the guarded Euler read
collects to the tie fold's letter-weighted member (`thm:weylchar`'s
assembly, the derivative display's count side convolved). -/
private theorem convA (mult : List Nat → Nat) (i d : Nat)
    (hid : i < d) (y : List Nat) {B : Nat} (hB : d < B)
    (s : Bool) :
    ground.famFold Nat.add 0
      (fun w => ground.getAt 0 (ground.bumpAt i w) i
        * sideCount d (unitDisp d) (ground.bumpAt i w) s
        * dAtGap mult i y (ground.bumpAt i w))
      (places.keyBox d B)
    = tieFold d y s (fun W chi =>
        ground.getAt 0 W i * (ground.getAt 0 chi i * mult chi)) := by
  show ground.famFold Nat.add 0
    (fun w => ground.getAt 0 (ground.bumpAt i w) i
      * ground.famFold Nat.add 0
        (fun p => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then 1
              else 0)
          else 0)
        (perms d)
      * dAtGap mult i y (ground.bumpAt i w))
    (places.keyBox d B)
    = _
  have hpush : ∀ w : List Nat,
      ground.getAt 0 (ground.bumpAt i w) i
        * ground.famFold Nat.add 0
          (fun p => if parity p = s then
              (if expo (unitDisp d) p = ground.bumpAt i w then 1
                else 0)
            else 0)
          (perms d)
        * dAtGap mult i y (ground.bumpAt i w)
      = ground.famFold Nat.add 0
        (fun p => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then
              ground.getAt 0 (ground.bumpAt i w) i
                * dAtGap mult i y (ground.bumpAt i w)
              else 0)
          else 0)
        (perms d) := by
    intro w
    rw [famFold_mul (ground.getAt 0 (ground.bumpAt i w) i)
      (fun p => if parity p = s then
          (if expo (unitDisp d) p = ground.bumpAt i w then 1
            else 0)
        else 0)
      (perms d),
      ← famFold_mulR (dAtGap mult i y (ground.bumpAt i w))
        (fun p => ground.getAt 0 (ground.bumpAt i w) i
          * (if parity p = s then
              (if expo (unitDisp d) p = ground.bumpAt i w then 1
                else 0)
            else 0))
        (perms d)]
    refine ground.famFold_congr_all Nat.add 0 _ _
      (fun p => ?_) (perms d)
    by_cases hpar : parity p = s
    · rw [if_pos hpar, if_pos hpar]
      by_cases hE : expo (unitDisp d) p = ground.bumpAt i w
      · rw [if_pos hE, if_pos hE, Nat.mul_one]
      · rw [if_neg hE, if_neg hE, Nat.mul_zero, Nat.zero_mul]
    · rw [if_neg hpar, if_neg hpar, Nat.mul_zero, Nat.zero_mul]
  rw [ground.famFold_congr_all Nat.add 0 _ _ hpush (places.keyBox d B),
    famFold_swap
      (fun w p => if parity p = s then
          (if expo (unitDisp d) p = ground.bumpAt i w then
            ground.getAt 0 (ground.bumpAt i w) i
              * dAtGap mult i y (ground.bumpAt i w)
            else 0)
        else 0)
      (places.keyBox d B) (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  by_cases hpar : parity p = s
  · have hpull : ground.famFold Nat.add 0
        (fun w => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then
              ground.getAt 0 (ground.bumpAt i w) i
                * dAtGap mult i y (ground.bumpAt i w)
              else 0)
          else 0)
        (places.keyBox d B)
      = ground.famFold Nat.add 0
        (fun w =>
          if expo (unitDisp d) p = ground.bumpAt i w then
            ground.getAt 0 (ground.bumpAt i w) i
              * dAtGap mult i y (ground.bumpAt i w)
            else 0)
        (places.keyBox d B) :=
      ground.famFold_congr_all Nat.add 0 _ _
        (fun w => by rw [if_pos hpar]) (places.keyBox d B)
    rw [hpull]
    have hEl : (expo (unitDisp d) p).length = d := by
      obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
      show (p.map (ground.getAt 0 (unitDisp d))).length = d
      rw [ground.length_map, hplen]
    have hEi := expoEntry hp hid
    have hcoll := boxPick (d := d) (B := B)
      (fun w => ground.getAt 0 (ground.bumpAt i w) i
        * dAtGap mult i y (ground.bumpAt i w))
      (ground.bumpAt i)
      (expo (unitDisp d) p)
      (ground.editAt (fun x => x - 1) i (expo (unitDisp d) p))
      (by rw [ground.length_editAt, hEl])
      (fun t ht => by
        by_cases hti : t = i
        · rw [hti, ground.getAt_editAt_self (fun x => x - 1) i
            (expo (unitDisp d) p) (by rw [hEl]; exact hid)]
          exact Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.sub_le _ 1) (expoEntry hp hid).2) hB
        · rw [ground.getAt_editAt_ne (fun x => x - 1) i t
            (expo (unitDisp d) p) hti]
          exact Nat.lt_of_le_of_lt (expoEntry hp ht).2 hB)
      (fun w hw hE => by
        have hpb : ground.editAt (fun x => x - 1) i (ground.bumpAt i w)
            = w := ground.dipAt_bumpAt_self i w
        rw [← hpb, ← hE])
      (ground.bumpAt_dipAt_self _ _ hEi.1)
    have hbd : ground.bumpAt i
        (ground.editAt (fun x => x - 1) i (expo (unitDisp d) p))
        = expo (unitDisp d) p :=
      ground.bumpAt_dipAt_self i (expo (unitDisp d) p) hEi.1
    rw [hcoll, hbd]
    show ground.getAt 0 (expo (unitDisp d) p) i
        * dAtGap mult i y (expo (unitDisp d) p)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => ground.getAt 0 (expo (unitDisp d) p) i
              * (ground.getAt 0 chi i * mult chi)
          | none => 0
        else 0)
    rw [if_pos hpar]
    cases ht : tieGap y (expo (unitDisp d) p) with
    | some chi =>
      show ground.getAt 0 (expo (unitDisp d) p) i
          * (match tieGap y (expo (unitDisp d) p) with
            | some chi' => ground.getAt 0 chi' i * mult chi'
            | none => 0)
        = ground.getAt 0 (expo (unitDisp d) p) i
          * (ground.getAt 0 chi i * mult chi)
      rw [ht]
    | none =>
      show ground.getAt 0 (expo (unitDisp d) p) i
          * (match tieGap y (expo (unitDisp d) p) with
            | some chi' => ground.getAt 0 chi' i * mult chi'
            | none => 0)
        = 0
      rw [ht]
      exact Nat.mul_zero _
  · rw [ground.famFold_congr_all Nat.add 0 _
      (fun _ => (0 : Nat))
      (fun w => by rw [if_neg hpar]) (places.keyBox d B),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]
    show (0 : Nat)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => ground.getAt 0 (expo (unitDisp d) p) i
              * (ground.getAt 0 chi i * mult chi)
          | none => 0
        else 0)
    rw [if_neg hpar]

/-- The `A`-count collapse at the bumped key, the unweighted read
(`thm:weylchar`'s assembly, the display's further member
convolved). -/
private theorem convB (mult : List Nat → Nat) (i d : Nat)
    (hid : i < d) (y : List Nat) {B : Nat} (hB : d < B)
    (s : Bool) :
    ground.famFold Nat.add 0
      (fun w => sideCount d (unitDisp d) (ground.bumpAt i w) s
        * dAtGap mult i y (ground.bumpAt i w))
      (places.keyBox d B)
    = tieFold d y s (fun _ chi =>
        ground.getAt 0 chi i * mult chi) := by
  show ground.famFold Nat.add 0
    (fun w => ground.famFold Nat.add 0
        (fun p => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then 1
              else 0)
          else 0)
        (perms d)
      * dAtGap mult i y (ground.bumpAt i w))
    (places.keyBox d B)
    = _
  have hpush : ∀ w : List Nat,
      ground.famFold Nat.add 0
        (fun p => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then 1
              else 0)
          else 0)
        (perms d)
        * dAtGap mult i y (ground.bumpAt i w)
      = ground.famFold Nat.add 0
        (fun p => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then
              dAtGap mult i y (ground.bumpAt i w)
              else 0)
          else 0)
        (perms d) := by
    intro w
    rw [← famFold_mulR (dAtGap mult i y (ground.bumpAt i w))
      (fun p => if parity p = s then
          (if expo (unitDisp d) p = ground.bumpAt i w then 1
            else 0)
        else 0)
      (perms d)]
    refine ground.famFold_congr_all Nat.add 0 _ _
      (fun p => ?_) (perms d)
    by_cases hpar : parity p = s
    · rw [if_pos hpar, if_pos hpar]
      by_cases hE : expo (unitDisp d) p = ground.bumpAt i w
      · rw [if_pos hE, if_pos hE, Nat.one_mul]
      · rw [if_neg hE, if_neg hE, Nat.zero_mul]
    · rw [if_neg hpar, if_neg hpar, Nat.zero_mul]
  rw [ground.famFold_congr_all Nat.add 0 _ _ hpush (places.keyBox d B),
    famFold_swap
      (fun w p => if parity p = s then
          (if expo (unitDisp d) p = ground.bumpAt i w then
            dAtGap mult i y (ground.bumpAt i w)
            else 0)
        else 0)
      (places.keyBox d B) (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  by_cases hpar : parity p = s
  · have hpull : ground.famFold Nat.add 0
        (fun w => if parity p = s then
            (if expo (unitDisp d) p = ground.bumpAt i w then
              dAtGap mult i y (ground.bumpAt i w)
              else 0)
          else 0)
        (places.keyBox d B)
      = ground.famFold Nat.add 0
        (fun w =>
          if expo (unitDisp d) p = ground.bumpAt i w then
            dAtGap mult i y (ground.bumpAt i w)
            else 0)
        (places.keyBox d B) :=
      ground.famFold_congr_all Nat.add 0 _ _
        (fun w => by rw [if_pos hpar]) (places.keyBox d B)
    rw [hpull]
    have hEl : (expo (unitDisp d) p).length = d := by
      obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
      show (p.map (ground.getAt 0 (unitDisp d))).length = d
      rw [ground.length_map, hplen]
    have hEi := expoEntry hp hid
    have hcoll := boxPick (d := d) (B := B)
      (fun w => dAtGap mult i y (ground.bumpAt i w))
      (ground.bumpAt i)
      (expo (unitDisp d) p)
      (ground.editAt (fun x => x - 1) i (expo (unitDisp d) p))
      (by rw [ground.length_editAt, hEl])
      (fun t ht => by
        by_cases hti : t = i
        · rw [hti, ground.getAt_editAt_self (fun x => x - 1) i
            (expo (unitDisp d) p) (by rw [hEl]; exact hid)]
          exact Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.sub_le _ 1) (expoEntry hp hid).2) hB
        · rw [ground.getAt_editAt_ne (fun x => x - 1) i t
            (expo (unitDisp d) p) hti]
          exact Nat.lt_of_le_of_lt (expoEntry hp ht).2 hB)
      (fun w hw hE => by
        have hpb : ground.editAt (fun x => x - 1) i (ground.bumpAt i w)
            = w := ground.dipAt_bumpAt_self i w
        rw [← hpb, ← hE])
      (ground.bumpAt_dipAt_self _ _ hEi.1)
    have hbd : ground.bumpAt i
        (ground.editAt (fun x => x - 1) i (expo (unitDisp d) p))
        = expo (unitDisp d) p :=
      ground.bumpAt_dipAt_self i (expo (unitDisp d) p) hEi.1
    rw [hcoll, hbd]
    show dAtGap mult i y (expo (unitDisp d) p)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => ground.getAt 0 chi i * mult chi
          | none => 0
        else 0)
    rw [if_pos hpar]
    rfl
  · rw [ground.famFold_congr_all Nat.add 0 _
      (fun _ => (0 : Nat))
      (fun w => by rw [if_neg hpar]) (places.keyBox d B),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)]
    show (0 : Nat)
      = (if parity p = s then
          match tieGap y (expo (unitDisp d) p) with
          | some chi => ground.getAt 0 chi i * mult chi
          | none => 0
        else 0)
    rw [if_neg hpar]

private theorem zeroSub : ∀ l : Nat, (0 : Nat) - l = 0
  | 0 => rfl
  | l + 1 => by
    show (0 : Nat) - l - 1 = 0
    rw [zeroSub l]

private theorem editBack {l : Nat} (j : Nat) {w : List Nat}
    (hjl : l ≤ ground.getAt 0 w j) :
    ground.editAt (fun x => x + l) j (ground.editAt (fun x => x - l) j w)
      = w := by
  rw [ground.editAt_fuse (fun x => x + l) (fun x => x - l) j w]
  exact (ground.editAt_congr_entry (fun x => x - l + l) (fun x => x) j w
    (ground.subAdd hjl)).trans (ground.editAt_id j w)

/-- The bumped back-move at the first orientation: the collapsed
display is the pair's moved display (`thm:weylchar`'s assembly,
the cofactor keys against the letter's shift). -/
private theorem bumpEditA {i j l : Nat} (hij : i ≠ j)
    {K : List Nat} (hi : i < K.length) (hj : j < K.length)
    (hval : l + 1 ≤ ground.getAt 0 K i) :
    ground.bumpAt i
      (ground.editAt (fun x => x + l) j
        (ground.editAt (fun x => x - (l + 1)) i K))
      = moveBy j i l K := by
  have hji : j ≠ i := fun he => hij he.symm
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_bumpAt, ground.length_editAt,
      ground.length_editAt, length_moveBy]
  · intro t ht
    rw [ground.length_bumpAt, ground.length_editAt,
      ground.length_editAt] at ht
    by_cases hti : t = i
    · rw [hti,
        ground.getAt_bumpAt_self i _
          (by rw [ground.length_editAt, ground.length_editAt]; exact hi),
        ground.getAt_editAt_ne (fun x => x + l) j i _ hij,
        ground.getAt_editAt_self (fun x => x - (l + 1)) i K hi,
        getAt_moveBy_snd j hji l K hi,
        ground.subSuccAdd hval]
    · by_cases htj : t = j
      · rw [htj,
          ground.getAt_bumpAt_ne i _ j hji,
          ground.getAt_editAt_self (fun x => x + l) j _
            (by rw [ground.length_editAt]; exact hj),
          ground.getAt_editAt_ne (fun x => x - (l + 1)) i j K hji,
          getAt_moveBy_fst hji l K hj]
      · rw [
          ground.getAt_bumpAt_ne i _ t
            (fun he => hti he),
          ground.getAt_editAt_ne (fun x => x + l) j t _
            (fun he => htj he),
          ground.getAt_editAt_ne (fun x => x - (l + 1)) i t K
            (fun he => hti he),
          getAt_moveBy_ne j i l K (fun he => htj he)
            (fun he => hti he)]

/-- The bumped back-move at the second orientation: the collapsed
display at the exchanged letters, the shift's successor. -/
private theorem bumpEditB {i j l : Nat} (hij : i ≠ j)
    {K : List Nat} (hi : i < K.length) (hj : j < K.length) :
    ground.bumpAt i
      (ground.editAt (fun x => x + l) i
        (ground.editAt (fun x => x - (l + 1)) j K))
      = moveBy i j (l + 1) K := by
  have hji : j ≠ i := fun he => hij he.symm
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_bumpAt, ground.length_editAt,
      ground.length_editAt, length_moveBy]
  · intro t ht
    rw [ground.length_bumpAt, ground.length_editAt,
      ground.length_editAt] at ht
    by_cases hti : t = i
    · rw [hti,
        ground.getAt_bumpAt_self i _
          (by rw [ground.length_editAt, ground.length_editAt]; exact hi),
        ground.getAt_editAt_self (fun x => x + l) i _
          (by rw [ground.length_editAt]; exact hi),
        ground.getAt_editAt_ne (fun x => x - (l + 1)) j i K hij,
        getAt_moveBy_fst hij (l + 1) K hi,
        Nat.add_assoc (ground.getAt 0 K i) l 1]
    · by_cases htj : t = j
      · rw [htj,
          ground.getAt_bumpAt_ne i _ j hji,
          ground.getAt_editAt_ne (fun x => x + l) i j _ hji,
          ground.getAt_editAt_self (fun x => x - (l + 1)) j K hj,
          getAt_moveBy_snd i hij (l + 1) K hj]
      · rw [
          ground.getAt_bumpAt_ne i _ t
            (fun he => hti he),
          ground.getAt_editAt_ne (fun x => x + l) i t _
            (fun he => hti he),
          ground.getAt_editAt_ne (fun x => x - (l + 1)) j t K
            (fun he => htj he),
          getAt_moveBy_ne i j (l + 1) K (fun he => hti he)
            (fun he => htj he)]

private theorem posSub : ∀ {m n : Nat}, 0 < n - m → m < n
  | 0, _, h => h
  | m + 1, 0, h => by
    rw [zeroSub (m + 1)] at h
    exact absurd h (Nat.lt_irrefl 0)
  | m + 1, n + 1, h => by
    rw [Nat.succ_sub_succ] at h
    exact Nat.succ_lt_succ (posSub h)

/-- The point collapse at an edit pair's preimage (`thm:weylchar`'s
assembly, the cofactor keys against the letter's shift): the box
fold of a read guarded at a permuted display against the
raised-lowered edit collects to the back-moved key's read, the
validity the raised letter's shift room at the display. -/
private theorem editCollapse {d B : Nat} (h2B : 2 * d ≤ B)
    {a b : Nat} (ha : a < d) (hb : b < d)
    (hab : a ≠ b) (l : Nat) (G : List Nat → Nat) {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    ground.famFold Nat.add 0
      (fun w => if expo (unitDisp d) p
          = ground.editAt (fun x => x + (l + 1)) a
            (ground.editAt (fun x => x - l) b w)
        then G w else 0)
      (places.keyBox d B)
    = if l + 1 ≤ ground.getAt 0 (expo (unitDisp d) p) a then
        G (ground.editAt (fun x => x + l) b
          (ground.editAt (fun x => x - (l + 1)) a
            (expo (unitDisp d) p)))
      else 0 := by
  have hba : b ≠ a := fun he => hab he.symm
  have hEl : (expo (unitDisp d) p).length = d := by
    obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
    show (p.map (ground.getAt 0 (unitDisp d))).length = d
    rw [ground.length_map, hplen]
  have haE : a < (expo (unitDisp d) p).length := by
    rw [hEl]; exact ha
  have hbE : b < (expo (unitDisp d) p).length := by
    rw [hEl]; exact hb
  have hdd : d + d ≤ B := by
    rw [← Nat.two_mul d]
    exact h2B
  have hB : d < B :=
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)
        d)
      hdd
  by_cases hval : l + 1 ≤ ground.getAt 0 (expo (unitDisp d) p) a
  · rw [if_pos hval]
    refine boxPick (d := d) (B := B) G
      (fun w => ground.editAt (fun x => x + (l + 1)) a
        (ground.editAt (fun x => x - l) b w))
      (expo (unitDisp d) p)
      (ground.editAt (fun x => x + l) b
        (ground.editAt (fun x => x - (l + 1)) a (expo (unitDisp d) p)))
      ?_ ?_ ?_ ?_
    · rw [ground.length_editAt, ground.length_editAt, hEl]
    · intro u hu
      by_cases hub : u = b
      · rw [hub, ground.getAt_editAt_self (fun x => x + l) b _
            (by rw [ground.length_editAt]; exact hbE),
          ground.getAt_editAt_ne (fun x => x - (l + 1)) a b _ hba]
        exact Nat.le_trans
          (Nat.add_le_add (expoEntry hp hb).2
            (Nat.le_trans hval (expoEntry hp ha).2))
          hdd
      · by_cases hua : u = a
        · rw [hua, ground.getAt_editAt_ne (fun x => x + l) b a _ hab,
            ground.getAt_editAt_self (fun x => x - (l + 1)) a _ haE]
          exact Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.sub_le _ (l + 1)) (expoEntry hp ha).2)
            hB
        · rw [ground.getAt_editAt_ne (fun x => x + l) b u _ hub,
            ground.getAt_editAt_ne (fun x => x - (l + 1)) a u _ hua]
          exact Nat.lt_of_le_of_lt (expoEntry hp hu).2 hB
    · intro w hw hE
      have hbw : b < w.length := by
        rw [keyBox_len d B w hw]; exact hb
      have hbRead : ground.getAt 0 (expo (unitDisp d) p) b
          = ground.getAt 0 w b - l := by
        rw [hE, ground.getAt_editAt_ne (fun x => x + (l + 1)) a b _ hba,
          ground.getAt_editAt_self (fun x => x - l) b w hbw]
      have hlb : l < ground.getAt 0 w b := posSub (by
        rw [← hbRead]
        exact (expoEntry hp hb).1)
      rw [hE,
        ground.editAt_fuse (fun x => x - (l + 1)) (fun x => x + (l + 1))
          a (ground.editAt (fun x => x - l) b w),
        ground.editAt_congr (fun x => x + (l + 1) - (l + 1))
          (fun x => x) (fun x => addSubSelfR x (l + 1)) a
          (ground.editAt (fun x => x - l) b w),
        ground.editAt_id a (ground.editAt (fun x => x - l) b w),
        editBack b (Nat.le_of_succ_le hlb)]
    · show ground.editAt (fun x => x + (l + 1)) a
          (ground.editAt (fun x => x - l) b
            (ground.editAt (fun x => x + l) b
              (ground.editAt (fun x => x - (l + 1)) a
                (expo (unitDisp d) p))))
        = expo (unitDisp d) p
      rw [ground.editAt_fuse (fun x => x - l) (fun x => x + l) b
          (ground.editAt (fun x => x - (l + 1)) a
            (expo (unitDisp d) p)),
        ground.editAt_congr (fun x => x + l - l) (fun x => x)
          (fun x => addSubSelfR x l) b
          (ground.editAt (fun x => x - (l + 1)) a
            (expo (unitDisp d) p)),
        ground.editAt_id b (ground.editAt (fun x => x - (l + 1)) a
          (expo (unitDisp d) p)),
        editBack a hval]
  · rw [if_neg hval]
    refine boxPickZero G
      (fun w => ground.editAt (fun x => x + (l + 1)) a
        (ground.editAt (fun x => x - l) b w))
      (expo (unitDisp d) p)
      (fun w hw hE => ?_)
    refine hval ?_
    have haw : a < w.length := by
      rw [keyBox_len d B w hw]; exact ha
    rw [hE, ground.getAt_editAt_self (fun x => x + (l + 1)) a _
        (by rw [ground.length_editAt]; exact haw),
      ground.getAt_editAt_ne (fun x => x - l) b a w hab]
    exact Nat.le_add_left (l + 1) (ground.getAt 0 w a)

/-- The cofactor collapse at the raised letter (`thm:weylchar`'s
assembly, the derivative display's cofactor side convolved): the
box fold of the cofactor's coefficient at a pair against the first
letter's guarded Euler read collects to the letter's moved-display
fold at the stated grading, one shift per display unit of the
letter. -/
private theorem convCA (mult : List Nat → Nat) (a b d : Nat)
    (ha : a < d) (hb : b < d) (hab : a ≠ b) (y : List Nat)
    {B : Nat} (h2B : 2 * d ≤ B) (t : Bool) :
    ground.famFold Nat.add 0
      (fun w => cofAt a b d w t
        * dAtGap mult a y (ground.bumpAt a w))
      (places.keyBox d B)
    = ground.famFold Nat.add 0
      (fun p => if parity p = t then
          ground.famFold Nat.add 0
            (fun l => dAtGap mult a y
              (moveBy b a l (expo (unitDisp d) p)))
            (List.range
              (ground.getAt 0 (expo (unitDisp d) p) a))
        else 0)
      (perms d) := by
  have hba : b ≠ a := fun he => hab he.symm
  have hB : d < B :=
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)
        d)
      (by rw [← Nat.two_mul d]; exact h2B)
  have hext : ∀ w : List Nat, 0 < ground.countOf w (places.keyBox d B) →
      cofAt a b d w t * dAtGap mult a y (ground.bumpAt a w)
    = ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult a y (ground.bumpAt a w))
        (List.range B) := by
    intro w hw
    have hbw : b < w.length := by
      rw [keyBox_len d B w hw]; exact hb
    rw [famFold_mulR (dAtGap mult a y (ground.bumpAt a w))
      (fun l => sideCount d (unitDisp d)
        (ground.editAt (fun x => x + (l + 1)) a
          (ground.editAt (fun x => x - l) b w)) t)
      (List.range B)]
    show ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
          (ground.editAt (fun x => x + (l + 1)) a
            (ground.editAt (fun x => x - l) b w)) t)
        (List.range (ground.getAt 0 w b + 1))
        * dAtGap mult a y (ground.bumpAt a w)
      = _
    rw [foldExtend'
      (fun l => sideCount d (unitDisp d)
        (ground.editAt (fun x => x + (l + 1)) a
          (ground.editAt (fun x => x - l) b w)) t)
      (ground.getAt 0 w b + 1) B
      (keyBox_ent d B w hw b hb)
      (fun l hl => sideCount_zeroEntry hb (by
        rw [ground.getAt_editAt_ne (fun x => x + (l + 1)) a b _ hba,
          ground.getAt_editAt_self (fun x => x - l) b w hbw]
        exact (ground.subLe _ _) (Nat.le_of_succ_le hl)) t)]
  rw [ground.famFold_congr_members Nat.add 0
      (fun w => cofAt a b d w t
        * dAtGap mult a y (ground.bumpAt a w))
      (fun w => ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult a y (ground.bumpAt a w))
        (List.range B))
      (places.keyBox d B) hext,
    famFold_swap
      (fun w l => sideCount d (unitDisp d)
          (ground.editAt (fun x => x + (l + 1)) a
            (ground.editAt (fun x => x - l) b w)) t
        * dAtGap mult a y (ground.bumpAt a w))
      (places.keyBox d B) (List.range B)]
  have hcoll : ∀ l : Nat,
      ground.famFold Nat.add 0
        (fun w => sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult a y (ground.bumpAt a w))
        (places.keyBox d B)
    = ground.famFold Nat.add 0
        (fun p => if parity p = t then
            (if l + 1 ≤ ground.getAt 0 (expo (unitDisp d) p) a
              then dAtGap mult a y
                (moveBy b a l (expo (unitDisp d) p))
              else 0)
          else 0)
        (perms d) := by
    intro l
    have hpush : ∀ w : List Nat,
        sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult a y (ground.bumpAt a w)
      = ground.famFold Nat.add 0
          (fun p => if parity p = t then
              (if expo (unitDisp d) p
                  = ground.editAt (fun x => x + (l + 1)) a
                    (ground.editAt (fun x => x - l) b w)
                then dAtGap mult a y (ground.bumpAt a w)
                else 0)
            else 0)
          (perms d) := by
      intro w
      show ground.famFold Nat.add 0
          (fun p => if parity p = t then
              (if expo (unitDisp d) p
                  = ground.editAt (fun x => x + (l + 1)) a
                    (ground.editAt (fun x => x - l) b w)
                then (1 : Nat) else 0)
            else 0)
          (perms d)
          * dAtGap mult a y (ground.bumpAt a w)
        = _
      rw [← famFold_mulR (dAtGap mult a y (ground.bumpAt a w))
        (fun p => if parity p = t then
            (if expo (unitDisp d) p
                = ground.editAt (fun x => x + (l + 1)) a
                  (ground.editAt (fun x => x - l) b w)
              then (1 : Nat) else 0)
          else 0)
        (perms d)]
      refine ground.famFold_congr_all Nat.add 0 _ _
        (fun p => ?_) (perms d)
      by_cases hpar : parity p = t
      · rw [if_pos hpar, if_pos hpar]
        by_cases hE : expo (unitDisp d) p
            = ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)
        · rw [if_pos hE, if_pos hE, Nat.one_mul]
        · rw [if_neg hE, if_neg hE, Nat.zero_mul]
      · rw [if_neg hpar, if_neg hpar, Nat.zero_mul]
    rw [ground.famFold_congr_all Nat.add 0 _ _ hpush
        (places.keyBox d B),
      famFold_swap
        (fun w p => if parity p = t then
            (if expo (unitDisp d) p
                = ground.editAt (fun x => x + (l + 1)) a
                  (ground.editAt (fun x => x - l) b w)
              then dAtGap mult a y (ground.bumpAt a w)
              else 0)
          else 0)
        (places.keyBox d B) (perms d)]
    refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
      (fun p hp => ?_)
    have hEl : (expo (unitDisp d) p).length = d := by
      obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
      show (p.map (ground.getAt 0 (unitDisp d))).length = d
      rw [ground.length_map, hplen]
    by_cases hpar : parity p = t
    · rw [if_pos hpar,
        ground.famFold_congr_all Nat.add 0 _
          (fun w => if expo (unitDisp d) p
              = ground.editAt (fun x => x + (l + 1)) a
                (ground.editAt (fun x => x - l) b w)
            then dAtGap mult a y (ground.bumpAt a w)
            else 0)
          (fun w => by rw [if_pos hpar]) (places.keyBox d B),
        editCollapse h2B ha hb hab l
          (fun w => dAtGap mult a y (ground.bumpAt a w)) hp]
      by_cases hval : l + 1
          ≤ ground.getAt 0 (expo (unitDisp d) p) a
      · rw [if_pos hval, if_pos hval,
          bumpEditA hab (by rw [hEl]; exact ha)
            (by rw [hEl]; exact hb) hval]
      · rw [if_neg hval, if_neg hval]
    · rw [if_neg hpar,
        ground.famFold_congr_all Nat.add 0 _
          (fun _ => (0 : Nat))
          (fun w => by rw [if_neg hpar]) (places.keyBox d B),
        famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (places.keyBox d B)]
  rw [ground.famFold_congr_all Nat.add 0 _ _ hcoll
      (List.range B),
    famFold_swap
      (fun l p => if parity p = t then
          (if l + 1 ≤ ground.getAt 0 (expo (unitDisp d) p) a
            then dAtGap mult a y
              (moveBy b a l (expo (unitDisp d) p))
            else 0)
        else 0)
      (List.range B) (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  by_cases hpar : parity p = t
  · rw [if_pos hpar,
      ground.famFold_congr_all Nat.add 0 _
        (fun l => if l + 1
            ≤ ground.getAt 0 (expo (unitDisp d) p) a
          then dAtGap mult a y
            (moveBy b a l (expo (unitDisp d) p))
          else 0)
        (fun l => by rw [if_pos hpar]) (List.range B),
      foldExtend'
        (fun l => if l + 1
            ≤ ground.getAt 0 (expo (unitDisp d) p) a
          then dAtGap mult a y
            (moveBy b a l (expo (unitDisp d) p))
          else 0)
        (ground.getAt 0 (expo (unitDisp d) p) a) B
        (Nat.le_trans (expoEntry hp ha).2
          (Nat.le_of_succ_le hB))
        (fun l hl => if_neg (fun hc =>
          absurd (Nat.le_trans hc hl) (Nat.lt_irrefl l)))]
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range (ground.getAt 0 (expo (unitDisp d) p) a))
      (fun l hl => ?_)
    rw [countOf_range l
      (ground.getAt 0 (expo (unitDisp d) p) a)] at hl
    by_cases hlc : l < ground.getAt 0 (expo (unitDisp d) p) a
    · rw [if_pos (show l + 1
        ≤ ground.getAt 0 (expo (unitDisp d) p) a from hlc)]
    · rw [if_neg hlc] at hl
      exact absurd hl (Nat.lt_irrefl 0)
  · rw [if_neg hpar,
      ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat))
        (fun l => by rw [if_neg hpar]) (List.range B),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (List.range B)]

/-- The cofactor collapse at the lowered letter (`thm:weylchar`'s
assembly, the swapped cofactor's read convolved): the box fold of
the cofactor's coefficient at a pair against the second letter's
guarded Euler read collects to the letter's moved-display fold at
the stated grading, the shifts the mapped successors. -/
private theorem convCB (mult : List Nat → Nat) (a b d : Nat)
    (ha : a < d) (hb : b < d) (hab : a ≠ b) (y : List Nat)
    {B : Nat} (h2B : 2 * d ≤ B) (t : Bool) :
    ground.famFold Nat.add 0
      (fun w => cofAt a b d w t
        * dAtGap mult b y (ground.bumpAt b w))
      (places.keyBox d B)
    = ground.famFold Nat.add 0
      (fun p => if parity p = t then
          ground.famFold Nat.add 0
            (fun k => dAtGap mult b y
              (moveBy b a k (expo (unitDisp d) p)))
            ((List.range
                (ground.getAt 0 (expo (unitDisp d) p) a)).map
              (fun k => k + 1))
        else 0)
      (perms d) := by
  have hba : b ≠ a := fun he => hab he.symm
  have hB : d < B :=
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)
        d)
      (by rw [← Nat.two_mul d]; exact h2B)
  have hext : ∀ w : List Nat, 0 < ground.countOf w (places.keyBox d B) →
      cofAt a b d w t * dAtGap mult b y (ground.bumpAt b w)
    = ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult b y (ground.bumpAt b w))
        (List.range B) := by
    intro w hw
    have hbw : b < w.length := by
      rw [keyBox_len d B w hw]; exact hb
    rw [famFold_mulR (dAtGap mult b y (ground.bumpAt b w))
      (fun l => sideCount d (unitDisp d)
        (ground.editAt (fun x => x + (l + 1)) a
          (ground.editAt (fun x => x - l) b w)) t)
      (List.range B)]
    show ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
          (ground.editAt (fun x => x + (l + 1)) a
            (ground.editAt (fun x => x - l) b w)) t)
        (List.range (ground.getAt 0 w b + 1))
        * dAtGap mult b y (ground.bumpAt b w)
      = _
    rw [foldExtend'
      (fun l => sideCount d (unitDisp d)
        (ground.editAt (fun x => x + (l + 1)) a
          (ground.editAt (fun x => x - l) b w)) t)
      (ground.getAt 0 w b + 1) B
      (keyBox_ent d B w hw b hb)
      (fun l hl => sideCount_zeroEntry hb (by
        rw [ground.getAt_editAt_ne (fun x => x + (l + 1)) a b _ hba,
          ground.getAt_editAt_self (fun x => x - l) b w hbw]
        exact (ground.subLe _ _) (Nat.le_of_succ_le hl)) t)]
  rw [ground.famFold_congr_members Nat.add 0
      (fun w => cofAt a b d w t
        * dAtGap mult b y (ground.bumpAt b w))
      (fun w => ground.famFold Nat.add 0
        (fun l => sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult b y (ground.bumpAt b w))
        (List.range B))
      (places.keyBox d B) hext,
    famFold_swap
      (fun w l => sideCount d (unitDisp d)
          (ground.editAt (fun x => x + (l + 1)) a
            (ground.editAt (fun x => x - l) b w)) t
        * dAtGap mult b y (ground.bumpAt b w))
      (places.keyBox d B) (List.range B)]
  have hcoll : ∀ l : Nat,
      ground.famFold Nat.add 0
        (fun w => sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult b y (ground.bumpAt b w))
        (places.keyBox d B)
    = ground.famFold Nat.add 0
        (fun p => if parity p = t then
            (if l + 1 ≤ ground.getAt 0 (expo (unitDisp d) p) a
              then dAtGap mult b y
                (moveBy b a (l + 1) (expo (unitDisp d) p))
              else 0)
          else 0)
        (perms d) := by
    intro l
    have hpush : ∀ w : List Nat,
        sideCount d (unitDisp d)
            (ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)) t
          * dAtGap mult b y (ground.bumpAt b w)
      = ground.famFold Nat.add 0
          (fun p => if parity p = t then
              (if expo (unitDisp d) p
                  = ground.editAt (fun x => x + (l + 1)) a
                    (ground.editAt (fun x => x - l) b w)
                then dAtGap mult b y (ground.bumpAt b w)
                else 0)
            else 0)
          (perms d) := by
      intro w
      show ground.famFold Nat.add 0
          (fun p => if parity p = t then
              (if expo (unitDisp d) p
                  = ground.editAt (fun x => x + (l + 1)) a
                    (ground.editAt (fun x => x - l) b w)
                then (1 : Nat) else 0)
            else 0)
          (perms d)
          * dAtGap mult b y (ground.bumpAt b w)
        = _
      rw [← famFold_mulR (dAtGap mult b y (ground.bumpAt b w))
        (fun p => if parity p = t then
            (if expo (unitDisp d) p
                = ground.editAt (fun x => x + (l + 1)) a
                  (ground.editAt (fun x => x - l) b w)
              then (1 : Nat) else 0)
          else 0)
        (perms d)]
      refine ground.famFold_congr_all Nat.add 0 _ _
        (fun p => ?_) (perms d)
      by_cases hpar : parity p = t
      · rw [if_pos hpar, if_pos hpar]
        by_cases hE : expo (unitDisp d) p
            = ground.editAt (fun x => x + (l + 1)) a
              (ground.editAt (fun x => x - l) b w)
        · rw [if_pos hE, if_pos hE, Nat.one_mul]
        · rw [if_neg hE, if_neg hE, Nat.zero_mul]
      · rw [if_neg hpar, if_neg hpar, Nat.zero_mul]
    rw [ground.famFold_congr_all Nat.add 0 _ _ hpush
        (places.keyBox d B),
      famFold_swap
        (fun w p => if parity p = t then
            (if expo (unitDisp d) p
                = ground.editAt (fun x => x + (l + 1)) a
                  (ground.editAt (fun x => x - l) b w)
              then dAtGap mult b y (ground.bumpAt b w)
              else 0)
          else 0)
        (places.keyBox d B) (perms d)]
    refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
      (fun p hp => ?_)
    have hEl : (expo (unitDisp d) p).length = d := by
      obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
      show (p.map (ground.getAt 0 (unitDisp d))).length = d
      rw [ground.length_map, hplen]
    by_cases hpar : parity p = t
    · rw [if_pos hpar,
        ground.famFold_congr_all Nat.add 0 _
          (fun w => if expo (unitDisp d) p
              = ground.editAt (fun x => x + (l + 1)) a
                (ground.editAt (fun x => x - l) b w)
            then dAtGap mult b y (ground.bumpAt b w)
            else 0)
          (fun w => by rw [if_pos hpar]) (places.keyBox d B),
        editCollapse h2B ha hb hab l
          (fun w => dAtGap mult b y (ground.bumpAt b w)) hp]
      by_cases hval : l + 1
          ≤ ground.getAt 0 (expo (unitDisp d) p) a
      · rw [if_pos hval, if_pos hval,
          bumpEditB hba (by rw [hEl]; exact hb)
            (by rw [hEl]; exact ha)]
      · rw [if_neg hval, if_neg hval]
    · rw [if_neg hpar,
        ground.famFold_congr_all Nat.add 0 _
          (fun _ => (0 : Nat))
          (fun w => by rw [if_neg hpar]) (places.keyBox d B),
        famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (places.keyBox d B)]
  rw [ground.famFold_congr_all Nat.add 0 _ _ hcoll
      (List.range B),
    famFold_swap
      (fun l p => if parity p = t then
          (if l + 1 ≤ ground.getAt 0 (expo (unitDisp d) p) a
            then dAtGap mult b y
              (moveBy b a (l + 1) (expo (unitDisp d) p))
            else 0)
        else 0)
      (List.range B) (perms d)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (perms d)
    (fun p hp => ?_)
  by_cases hpar : parity p = t
  · rw [if_pos hpar,
      ground.famFold_map Nat.add 0
        (fun k => dAtGap mult b y
          (moveBy b a k (expo (unitDisp d) p)))
        (fun k => k + 1)
        (List.range (ground.getAt 0 (expo (unitDisp d) p) a)),
      ground.famFold_congr_all Nat.add 0 _
        (fun l => if l + 1
            ≤ ground.getAt 0 (expo (unitDisp d) p) a
          then dAtGap mult b y
            (moveBy b a (l + 1) (expo (unitDisp d) p))
          else 0)
        (fun l => by rw [if_pos hpar]) (List.range B),
      foldExtend'
        (fun l => if l + 1
            ≤ ground.getAt 0 (expo (unitDisp d) p) a
          then dAtGap mult b y
            (moveBy b a (l + 1) (expo (unitDisp d) p))
          else 0)
        (ground.getAt 0 (expo (unitDisp d) p) a) B
        (Nat.le_trans (expoEntry hp ha).2
          (Nat.le_of_succ_le hB))
        (fun l hl => if_neg (fun hc =>
          absurd (Nat.le_trans hc hl) (Nat.lt_irrefl l)))]
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range (ground.getAt 0 (expo (unitDisp d) p) a))
      (fun l hl => ?_)
    rw [countOf_range l
      (ground.getAt 0 (expo (unitDisp d) p) a)] at hl
    by_cases hlc : l < ground.getAt 0 (expo (unitDisp d) p) a
    · rw [if_pos (show l + 1
        ≤ ground.getAt 0 (expo (unitDisp d) p) a from hlc)]
    · rw [if_neg hlc] at hl
      exact absurd hl (Nat.lt_irrefl 0)
  · rw [if_neg hpar,
      ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat))
        (fun l => by rw [if_neg hpar]) (List.range B),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (List.range B)]

/-- The cofactor-side convolution at the letter (`thm:weylchar`'s
assembly, the derivative display convolved over the key box): the
box fold of the cofactor fold against the letter's guarded Euler
read collects to the letter's cofactor-Euler fold, the pairs
beyond the letter at the raised-letter collapse and the pairs
below it at the lowered-letter one. -/
private theorem convC (mult : List Nat → Nat) (i d : Nat)
    (hid : i < d) (y : List Nat) {B : Nat}
    (h2B : 2 * d ≤ B) (s : Bool) :
    ground.famFold Nat.add 0
      (fun w => cofSum i d w s
        * dAtGap mult i y (ground.bumpAt i w))
      (places.keyBox d B)
    = cofEFold mult i d y s := by
  have hsplit : ∀ w : List Nat,
      cofSum i d w s * dAtGap mult i y (ground.bumpAt i w)
    = ground.famFold Nat.add 0
        (fun j =>
          (if i < j then cofAt i j d w s
            else if j < i then cofAt j i d w (!s)
            else 0)
          * dAtGap mult i y (ground.bumpAt i w))
        (List.range d) := by
    intro w
    show ground.famFold Nat.add 0
        (fun j =>
          if i < j then cofAt i j d w s
          else if j < i then cofAt j i d w (!s)
          else 0)
        (List.range d)
        * dAtGap mult i y (ground.bumpAt i w)
      = _
    rw [← famFold_mulR (dAtGap mult i y (ground.bumpAt i w))
      (fun j =>
        if i < j then cofAt i j d w s
        else if j < i then cofAt j i d w (!s)
        else 0)
      (List.range d)]
  have hswap : cofEFold mult i d y s
    = ground.famFold Nat.add 0
      (fun j => ground.famFold Nat.add 0
        (fun p =>
          if i < j then
            (if parity p = s then
              ground.famFold Nat.add 0
                (fun l => dAtGap mult i y
                  (moveBy j i l (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) i))
            else 0)
          else if j < i then
            (if parity p = (!s) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult i y
                  (moveBy i j k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) j)).map
                  (fun k => k + 1))
            else 0)
          else 0)
        (perms d))
      (List.range d) :=
    famFold_swap
      (fun p j =>
        if i < j then
          (if parity p = s then
            ground.famFold Nat.add 0
              (fun l => dAtGap mult i y
                (moveBy j i l (expo (unitDisp d) p)))
              (List.range
                (ground.getAt 0 (expo (unitDisp d) p) i))
          else 0)
        else if j < i then
          (if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun k => dAtGap mult i y
                (moveBy i j k (expo (unitDisp d) p)))
              ((List.range
                  (ground.getAt 0
                    (expo (unitDisp d) p) j)).map
                (fun k => k + 1))
          else 0)
        else 0)
      (perms d) (List.range d)
  rw [ground.famFold_congr_all Nat.add 0 _ _ hsplit
      (places.keyBox d B),
    famFold_swap
      (fun w j =>
        (if i < j then cofAt i j d w s
          else if j < i then cofAt j i d w (!s)
          else 0)
        * dAtGap mult i y (ground.bumpAt i w))
      (places.keyBox d B) (List.range d),
    hswap]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range d) (fun j hj => ?_)
  have hjd : j < d := by
    rw [countOf_range j d] at hj
    by_cases hjd : j < d
    · exact hjd
    · rw [if_neg hjd] at hj
      exact absurd hj (Nat.lt_irrefl 0)
  by_cases hij : i < j
  · rw [ground.famFold_congr_all Nat.add 0 _
        (fun w => cofAt i j d w s
          * dAtGap mult i y (ground.bumpAt i w))
        (fun w => by rw [if_pos hij]) (places.keyBox d B),
      ground.famFold_congr_all Nat.add 0 _
        (fun p => if parity p = s then
            ground.famFold Nat.add 0
              (fun l => dAtGap mult i y
                (moveBy j i l (expo (unitDisp d) p)))
              (List.range
                (ground.getAt 0 (expo (unitDisp d) p) i))
          else 0)
        (fun p => by rw [if_pos hij]) (perms d)]
    exact convCA mult i j d hid hjd (Nat.ne_of_lt hij) y
      h2B s
  · by_cases hji : j < i
    · rw [ground.famFold_congr_all Nat.add 0 _
          (fun w => cofAt j i d w (!s)
            * dAtGap mult i y (ground.bumpAt i w))
          (fun w => by rw [if_neg hij, if_pos hji])
          (places.keyBox d B),
        ground.famFold_congr_all Nat.add 0 _
          (fun p => if parity p = (!s) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult i y
                  (moveBy i j k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) j)).map
                  (fun k => k + 1))
            else 0)
          (fun p => by rw [if_neg hij, if_pos hji]) (perms d)]
      exact convCB mult j i d hjd hid (Nat.ne_of_lt hji) y
        h2B (!s)
    · rw [ground.famFold_congr_all Nat.add 0 _
          (fun _ => (0 : Nat))
          (fun w => by
            rw [if_neg hij, if_neg hji, Nat.zero_mul])
          (places.keyBox d B),
        ground.famFold_congr_all Nat.add 0 _
          (fun _ => (0 : Nat))
          (fun p => by rw [if_neg hij, if_neg hji]) (perms d),
        famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (places.keyBox d B),
        famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (perms d)]

/-- The letter's convolution (`thm:weylchar`'s assembly, the
derivative display convolved at one letter): the crossed equation
of the letter-weighted tie folds with the letter's cofactor-Euler
fold — the product rule's box fold against the letter's guarded
Euler read, each side's three members the collapses' reads. -/
private theorem convLetter (mult : List Nat → Nat) (i d : Nat)
    (hid : i < d) (y : List Nat) (s : Bool) :
    tieFold d y s (fun W chi =>
        ground.getAt 0 W i * (ground.getAt 0 chi i * mult chi))
      + tieFold d y (!s) (fun _ chi =>
        ground.getAt 0 chi i * mult chi)
      + cofEFold mult i d y (!s)
    = tieFold d y (!s) (fun W chi =>
        ground.getAt 0 W i * (ground.getAt 0 chi i * mult chi))
      + tieFold d y s (fun _ chi =>
        ground.getAt 0 chi i * mult chi)
      + cofEFold mult i d y s := by
  have hdd : d ≤ 2 * d := by
    rw [Nat.two_mul d]
    exact Nat.le_add_right d d
  have hB : d < 2 * d + 1 := Nat.succ_le_succ hdd
  have h2B : 2 * d ≤ 2 * d + 1 := Nat.le_add_right (2 * d) 1
  rw [← convA mult i d hid y hB s,
    ← convA mult i d hid y hB (!s),
    ← convB mult i d hid y hB s,
    ← convB mult i d hid y hB (!s),
    ← convC mult i d hid y h2B s,
    ← convC mult i d hid y h2B (!s),
    ← famFold_add_split, ← famFold_add_split,
    ← famFold_add_split, ← famFold_add_split]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (places.keyBox d (2 * d + 1)) (fun w hw => ?_)
  rw [← mulAddR, ← mulAddR, ← mulAddR, ← mulAddR]
  exact congrArg
    (fun x => x * dAtGap mult i y (ground.bumpAt i w))
    (prodRule i d hid w (keyBox_len d (2 * d + 1) w hw) s)

private theorem ifSplit3 {c1 c2 : Prop} [Decidable c1]
    [Decidable c2] (h : c1 → c2 → False) (X Y : Nat) :
    (if c1 then X else if c2 then Y else 0)
      = (if c1 then X else 0) + (if c2 then Y else 0) := by
  by_cases h1 : c1
  · rw [if_pos h1, if_pos h1, if_neg (fun h2 => h h1 h2)]
    rfl
  · rw [if_neg h1, if_neg h1, Nat.zero_add]

private theorem ifPairJoin (c : Prop) [Decidable c] (u v w : Nat)
    (h : u + v = w) :
    (if c then u else 0) + (if c then v else 0)
      = if c then w else 0 :=
  (ground.if_add c u v).trans
    (congrArg (fun z => if c then z else 0) h)

private theorem gradeJoin : ∀ (q s : Bool) (X Y : Nat),
    (if q = s then X else 0) + (if q = (!s) then Y else 0)
      = if xor s q then Y else X
  | false, false, _, _ => rfl
  | false, true, _, Y => Nat.zero_add Y
  | true, false, _, Y => Nat.zero_add Y
  | true, true, _, _ => rfl

/-- The letters' cofactor-Euler folds regroup onto the letter
pairs (`thm:weylchar`'s assembly, the pair's two `D_i V`-terms
collected): the letter fold of the cofactor-Euler folds is the
pair fold of the cofactor's pair-weighted folds, a pair's two
letters the raised and lowered members at the composed grading. -/
private theorem pairRegroup (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    ground.famFold Nat.add 0
      (fun i => cofEFold mult i d y s) (List.range d)
    = ground.famFold Nat.add 0
      (fun ab => cofDFold mult ab.1 ab.2 d y s)
      (pairsOf d) := by
  refine Eq.trans ?_
    (pairsFold (fun ab => cofDFold mult ab.1 ab.2 d y s) d).symm
  have hR : ground.famFold Nat.add 0
      (fun a => ground.famFold Nat.add 0
        (fun b => if a < b then
            cofDFold mult (a, b).1 (a, b).2 d y s
          else 0)
        (List.range d))
      (List.range d)
    = ground.famFold Nat.add 0
      (fun p => ground.famFold Nat.add 0
        (fun a => ground.famFold Nat.add 0
          (fun b => if a < b then
              (if xor s (parity p) then
                ground.famFold Nat.add 0
                  (fun k => dAtGap mult b y
                    (moveBy b a k (expo (unitDisp d) p)))
                  ((List.range
                      (ground.getAt 0
                        (expo (unitDisp d) p) a)).map
                    (fun k => k + 1))
              else
                ground.famFold Nat.add 0
                  (fun j => dAtGap mult a y
                    (moveBy b a j (expo (unitDisp d) p)))
                  (List.range
                    (ground.getAt 0 (expo (unitDisp d) p) a)))
            else 0)
          (List.range d))
        (List.range d))
      (perms d) := by
    refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
      (fun a => ground.famFold Nat.add 0
        (fun p => ground.famFold Nat.add 0
          (fun b => if a < b then
              (if xor s (parity p) then
                ground.famFold Nat.add 0
                  (fun k => dAtGap mult b y
                    (moveBy b a k (expo (unitDisp d) p)))
                  ((List.range
                      (ground.getAt 0
                        (expo (unitDisp d) p) a)).map
                    (fun k => k + 1))
              else
                ground.famFold Nat.add 0
                  (fun j => dAtGap mult a y
                    (moveBy b a j (expo (unitDisp d) p)))
                  (List.range
                    (ground.getAt 0 (expo (unitDisp d) p) a)))
            else 0)
          (List.range d))
        (perms d))
      (fun a => ?_) (List.range d))
      (famFold_swap
        (fun a p => ground.famFold Nat.add 0
          (fun b => if a < b then
              (if xor s (parity p) then
                ground.famFold Nat.add 0
                  (fun k => dAtGap mult b y
                    (moveBy b a k (expo (unitDisp d) p)))
                  ((List.range
                      (ground.getAt 0
                        (expo (unitDisp d) p) a)).map
                    (fun k => k + 1))
              else
                ground.famFold Nat.add 0
                  (fun j => dAtGap mult a y
                    (moveBy b a j (expo (unitDisp d) p)))
                  (List.range
                    (ground.getAt 0 (expo (unitDisp d) p) a)))
            else 0)
          (List.range d))
        (List.range d) (perms d))
    refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
      (fun b => ground.famFold Nat.add 0
        (fun p => if a < b then
            (if xor s (parity p) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult b y
                  (moveBy b a k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) a)).map
                  (fun k => k + 1))
            else
              ground.famFold Nat.add 0
                (fun j => dAtGap mult a y
                  (moveBy b a j (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) a)))
          else 0)
        (perms d))
      (fun b => ?_) (List.range d))
      (famFold_swap
        (fun b p => if a < b then
            (if xor s (parity p) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult b y
                  (moveBy b a k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) a)).map
                  (fun k => k + 1))
            else
              ground.famFold Nat.add 0
                (fun j => dAtGap mult a y
                  (moveBy b a j (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) a)))
          else 0)
        (List.range d) (perms d))
    show (if a < b then cofDFold mult a b d y s else 0) = _
    by_cases hab : a < b
    · rw [if_pos hab]
      exact ground.famFold_congr_all Nat.add 0
        (fun p =>
          if xor s (parity p) then
            ground.famFold Nat.add 0
              (fun k => dAtGap mult b y
                (moveBy b a k (expo (unitDisp d) p)))
              ((List.range
                  (ground.getAt 0
                    (expo (unitDisp d) p) a)).map
                (fun k => k + 1))
          else
            ground.famFold Nat.add 0
              (fun j => dAtGap mult a y
                (moveBy b a j (expo (unitDisp d) p)))
              (List.range
                (ground.getAt 0 (expo (unitDisp d) p) a)))
        (fun p => if a < b then
            (if xor s (parity p) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult b y
                  (moveBy b a k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) a)).map
                  (fun k => k + 1))
            else
              ground.famFold Nat.add 0
                (fun j => dAtGap mult a y
                  (moveBy b a j (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) a)))
          else 0)
        (fun p => (if_pos hab).symm) (perms d)
    · rw [if_neg hab]
      exact ((ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat))
        (fun p => if_neg hab) (perms d)).trans
        (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (perms d))).symm
  rw [hR]
  show ground.famFold Nat.add 0
      (fun i => ground.famFold Nat.add 0
        (fun p => ground.famFold Nat.add 0
          (fun j =>
            if i < j then
              (if parity p = s then
                ground.famFold Nat.add 0
                  (fun l => dAtGap mult i y
                    (moveBy j i l (expo (unitDisp d) p)))
                  (List.range
                    (ground.getAt 0 (expo (unitDisp d) p) i))
              else 0)
            else if j < i then
              (if parity p = (!s) then
                ground.famFold Nat.add 0
                  (fun k => dAtGap mult i y
                    (moveBy i j k (expo (unitDisp d) p)))
                  ((List.range
                      (ground.getAt 0
                        (expo (unitDisp d) p) j)).map
                    (fun k => k + 1))
              else 0)
            else 0)
          (List.range d))
        (perms d))
      (List.range d)
    = _
  rw [famFold_swap
    (fun i p => ground.famFold Nat.add 0
      (fun j =>
        if i < j then
          (if parity p = s then
            ground.famFold Nat.add 0
              (fun l => dAtGap mult i y
                (moveBy j i l (expo (unitDisp d) p)))
              (List.range
                (ground.getAt 0 (expo (unitDisp d) p) i))
          else 0)
        else if j < i then
          (if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun k => dAtGap mult i y
                (moveBy i j k (expo (unitDisp d) p)))
              ((List.range
                  (ground.getAt 0
                    (expo (unitDisp d) p) j)).map
                (fun k => k + 1))
          else 0)
        else 0)
      (List.range d))
    (List.range d) (perms d)]
  refine ground.famFold_congr_all Nat.add 0 _ _
    (fun p => ?_) (perms d)
  rw [ground.famFold_congr_all Nat.add 0 _
      (fun i => ground.famFold Nat.add 0
        (fun j =>
          if i < j then
            (if parity p = s then
              ground.famFold Nat.add 0
                (fun l => dAtGap mult i y
                  (moveBy j i l (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) i))
            else 0)
          else 0)
        (List.range d)
        + ground.famFold Nat.add 0
          (fun j =>
            if j < i then
              (if parity p = (!s) then
                ground.famFold Nat.add 0
                  (fun k => dAtGap mult i y
                    (moveBy i j k (expo (unitDisp d) p)))
                  ((List.range
                      (ground.getAt 0
                        (expo (unitDisp d) p) j)).map
                    (fun k => k + 1))
              else 0)
            else 0)
          (List.range d))
      (fun i => ?_) (List.range d),
    famFold_add_split
      (fun i => ground.famFold Nat.add 0
        (fun j =>
          if i < j then
            (if parity p = s then
              ground.famFold Nat.add 0
                (fun l => dAtGap mult i y
                  (moveBy j i l (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) i))
            else 0)
          else 0)
        (List.range d))
      (fun i => ground.famFold Nat.add 0
        (fun j =>
          if j < i then
            (if parity p = (!s) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult i y
                  (moveBy i j k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) j)).map
                  (fun k => k + 1))
            else 0)
          else 0)
        (List.range d))
      (List.range d),
    famFold_swap
      (fun i j =>
        if j < i then
          (if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun k => dAtGap mult i y
                (moveBy i j k (expo (unitDisp d) p)))
              ((List.range
                  (ground.getAt 0
                    (expo (unitDisp d) p) j)).map
                (fun k => k + 1))
          else 0)
        else 0)
      (List.range d) (List.range d),
    ← famFold_add_split
      (fun a => ground.famFold Nat.add 0
        (fun j =>
          if a < j then
            (if parity p = s then
              ground.famFold Nat.add 0
                (fun l => dAtGap mult a y
                  (moveBy j a l (expo (unitDisp d) p)))
                (List.range
                  (ground.getAt 0 (expo (unitDisp d) p) a))
            else 0)
          else 0)
        (List.range d))
      (fun a => ground.famFold Nat.add 0
        (fun i =>
          if a < i then
            (if parity p = (!s) then
              ground.famFold Nat.add 0
                (fun k => dAtGap mult i y
                  (moveBy i a k (expo (unitDisp d) p)))
                ((List.range
                    (ground.getAt 0
                      (expo (unitDisp d) p) a)).map
                  (fun k => k + 1))
            else 0)
          else 0)
        (List.range d))
      (List.range d)]
  · refine ground.famFold_congr_all Nat.add 0 _ _
      (fun a => ?_) (List.range d)
    rw [← famFold_add_split
      (fun j =>
        if a < j then
          (if parity p = s then
            ground.famFold Nat.add 0
              (fun l => dAtGap mult a y
                (moveBy j a l (expo (unitDisp d) p)))
              (List.range
                (ground.getAt 0 (expo (unitDisp d) p) a))
          else 0)
        else 0)
      (fun i =>
        if a < i then
          (if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun k => dAtGap mult i y
                (moveBy i a k (expo (unitDisp d) p)))
              ((List.range
                  (ground.getAt 0
                    (expo (unitDisp d) p) a)).map
                (fun k => k + 1))
          else 0)
        else 0)
      (List.range d)]
    refine ground.famFold_congr_all Nat.add 0 _ _
      (fun b => ?_) (List.range d)
    exact ifPairJoin (a < b) _ _ _
      (gradeJoin (parity p) s _ _)
  · rw [← famFold_add_split
      (fun j =>
        if i < j then
          (if parity p = s then
            ground.famFold Nat.add 0
              (fun l => dAtGap mult i y
                (moveBy j i l (expo (unitDisp d) p)))
              (List.range
                (ground.getAt 0 (expo (unitDisp d) p) i))
          else 0)
        else 0)
      (fun j =>
        if j < i then
          (if parity p = (!s) then
            ground.famFold Nat.add 0
              (fun k => dAtGap mult i y
                (moveBy i j k (expo (unitDisp d) p)))
              ((List.range
                  (ground.getAt 0
                    (expo (unitDisp d) p) j)).map
                (fun k => k + 1))
          else 0)
        else 0)
      (List.range d)]
    refine ground.famFold_congr_all Nat.add 0 _ _
      (fun j => ?_) (List.range d)
    exact ifSplit3
      (fun h1 h2 => Nat.lt_irrefl i (Nat.lt_trans h1 h2)) _ _

/-- An index fold of tie folds is the tie fold of the index folds:
the guarded reads share one tie per permutation, so the family
fold passes through the guard and the tie's match. -/
private theorem tieFold_fold {α : Type} (d : Nat) (y : List Nat)
    (s : Bool) (F : α → List Nat → List Nat → Nat) (L : List α) :
    ground.famFold Nat.add 0
      (fun i => tieFold d y s (F i)) L
    = tieFold d y s (fun W chi =>
        ground.famFold Nat.add 0 (fun i => F i W chi) L) := by
  show ground.famFold Nat.add 0
      (fun i => ground.famFold Nat.add 0
        (fun p =>
          if parity p = s then
            match tieGap y (expo (unitDisp d) p) with
            | some chi => F i (expo (unitDisp d) p) chi
            | none => 0
          else 0)
        (perms d))
      L
    = _
  rw [famFold_swap
    (fun i p =>
      if parity p = s then
        match tieGap y (expo (unitDisp d) p) with
        | some chi => F i (expo (unitDisp d) p) chi
        | none => 0
      else 0)
    L (perms d)]
  refine ground.famFold_congr_all Nat.add 0 _ _
    (fun p => ?_) (perms d)
  by_cases hpar : parity p = s
  · rw [if_pos hpar,
      ground.famFold_congr_all Nat.add 0 _
        (fun i =>
          match tieGap y (expo (unitDisp d) p) with
          | some chi => F i (expo (unitDisp d) p) chi
          | none => 0)
        (fun i => by rw [if_pos hpar]) L]
    cases tieGap y (expo (unitDisp d) p) with
    | some chi => rfl
    | none =>
      exact (ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat)) (fun i => rfl) L).trans
        (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) L)
  · rw [if_neg hpar,
      ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat))
        (fun i => by rw [if_neg hpar]) L,
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) L]

/-- The product's graded coefficient reads its multiplicity
pointwise. -/
theorem prodCount_congr (m1 m2 : List Nat → Nat)
    (h : ∀ mu, m1 mu = m2 mu) (d : Nat) (y : List Nat)
    (side : Bool) :
    prodCount m1 d y side = prodCount m2 d y side := by
  rw [prodCount_tie m1 d y side, prodCount_tie m2 d y side]
  exact tieFold_congr d y side _ _ (fun _ _ chi _ => h chi)

/-- A scaled multiplicity scales the product's graded
coefficient. -/
theorem prodCount_scale (w : Nat) (mult : List Nat → Nat)
    (d : Nat) (y : List Nat) (side : Bool) :
    prodCount (fun mu => w * mult mu) d y side
      = w * prodCount mult d y side := by
  rw [prodCount_tie _ d y side, prodCount_tie mult d y side]
  exact (tieFold_mul w d y side (fun _ chi => mult chi)).symm

/-- The product's graded coefficient is additive in its
multiplicity: a multiplicity read as a fold over a family splits
the coefficient into the family members' own coefficients. -/
theorem prodCount_famFold {α : Type}
    (F : α → List Nat → Nat) (L : List α) (d : Nat)
    (y : List Nat) (side : Bool) :
    prodCount
        (fun mu => ground.famFold Nat.add 0 (fun x => F x mu) L)
        d y side
      = ground.famFold Nat.add 0
          (fun x => prodCount (F x) d y side) L :=
  (tieFold_fold d y side (fun x _ chi => F x chi) L).symm

/-- The convolution theorem (`thm:weylchar`'s assembly, the
derivative display convolved over every letter): the crossed
equation of the letter-weighted tie fold and the content-sum tie
fold with the cofactor's pair-weighted folds, at every
multiplicity. -/
private theorem convAll (mult : List Nat → Nat) (d : Nat)
    (y : List Nat) (s : Bool) :
    tieFold d y s (fun W chi => ground.dotNat W chi * mult chi)
      + tieFold d y (!s) (fun _ chi => sumNat chi * mult chi)
      + ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 d y (!s))
        (pairsOf d)
    = tieFold d y (!s) (fun W chi => ground.dotNat W chi * mult chi)
      + tieFold d y s (fun _ chi => sumNat chi * mult chi)
      + ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 d y s)
        (pairsOf d) := by
  have hW : ∀ t : Bool,
      tieFold d y t (fun W chi => ground.dotNat W chi * mult chi)
    = ground.famFold Nat.add 0
        (fun i => tieFold d y t (fun W chi =>
          ground.getAt 0 W i
            * (ground.getAt 0 chi i * mult chi)))
        (List.range d) := by
    intro t
    rw [tieFold_fold d y t
      (fun i W chi => ground.getAt 0 W i
        * (ground.getAt 0 chi i * mult chi))
      (List.range d)]
    refine tieFold_congr d y t _ _ (fun p hp chi ht => ?_)
    have hEl : (expo (unitDisp d) p).length = d := by
      obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
      show (p.map (ground.getAt 0 (unitDisp d))).length = d
      rw [ground.length_map, hplen]
    rw [ground.dotNat_index (expo (unitDisp d) p) chi
        (by rw [hEl, tieLen hp ht]),
      hEl,
      ← famFold_mulR (mult chi)
        (fun i => ground.getAt 0 (expo (unitDisp d) p) i
          * ground.getAt 0 chi i)
        (List.range d)]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun i => mulAssoc
        (ground.getAt 0 (expo (unitDisp d) p) i)
        (ground.getAt 0 chi i) (mult chi)) (List.range d)
  have hN : ∀ t : Bool,
      tieFold d y t (fun _ chi => sumNat chi * mult chi)
    = ground.famFold Nat.add 0
        (fun i => tieFold d y t (fun _ chi =>
          ground.getAt 0 chi i * mult chi))
        (List.range d) := by
    intro t
    rw [tieFold_fold d y t
      (fun i _ chi => ground.getAt 0 chi i * mult chi)
      (List.range d)]
    refine tieFold_congr d y t _ _ (fun p hp chi ht => ?_)
    rw [← ground.sumIndex chi, tieLen hp ht,
      ← famFold_mulR (mult chi)
        (fun i => ground.getAt 0 chi i) (List.range d)]
  rw [hW s, hW (!s), hN s, hN (!s),
    ← pairRegroup mult d y s, ← pairRegroup mult d y (!s),
    ← famFold_add_split, ← famFold_add_split,
    ← famFold_add_split, ← famFold_add_split]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range d) (fun i hi => ?_)
  have hid : i < d := by
    rw [countOf_range i d] at hi
    by_cases hid : i < d
    · exact hid
    · rw [if_neg hid] at hi
      exact absurd hi (Nat.lt_irrefl 0)
  exact convLetter mult i d hid y s

/-- The cofactor identity summed over the letter pairs
(`thm:weylchar`'s assembly, the pairs' display-1 reads
collected): the crossed equation of the pair-weighted, product
and Euler folds over the letter pairs, at the symmetry. -/
private theorem cofDAll (mult : List Nat → Nat) (d : Nat)
    (z : List Nat) (hz : z.length = d) (hsym : symReadE d mult)
    (s : Bool) :
    ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 d z s)
        (pairsOf d)
      + ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 d z (!s))
        (pairsOf d)
      + ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 d z (!s)) (pairsOf d)
    = ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 d z (!s))
        (pairsOf d)
      + ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 d z s) (pairsOf d)
      + ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 d z s) (pairsOf d) := by
  rw [pairsFold (fun ab => cofDFold mult ab.1 ab.2 d z s) d,
    pairsFold (fun ab => cofDFold mult ab.1 ab.2 d z (!s)) d,
    pairsFold (fun ab => prodG mult ab.1 ab.2 d z s) d,
    pairsFold (fun ab => prodG mult ab.1 ab.2 d z (!s)) d,
    pairsFold (fun ab => prodD mult ab.1 d z s) d,
    pairsFold (fun ab => prodD mult ab.1 d z (!s)) d,
    ← famFold_add_split, ← famFold_add_split,
    ← famFold_add_split, ← famFold_add_split]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range d) (fun a _ => ?_)
  rw [← famFold_add_split, ← famFold_add_split,
    ← famFold_add_split, ← famFold_add_split]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range d) (fun b hb => ?_)
  have hbd : b < d := by
    rw [countOf_range b d] at hb
    by_cases hbd : b < d
    · exact hbd
    · rw [if_neg hbd] at hb
      exact absurd hb (Nat.lt_irrefl 0)
  by_cases hab : a < b
  · rw [if_pos hab, if_pos hab, if_pos hab, if_pos hab,
      if_pos hab, if_pos hab]
    show cofDFold mult a b d z s + prodG mult a b d z (!s)
        + prodD mult a d z (!s)
      = cofDFold mult a b d z (!s) + prodG mult a b d z s
        + prodD mult a d z s
    cases s with
    | false => exact cofDProd mult hab hbd z hz hsym
    | true => exact (cofDProd mult hab hbd z hz hsym).symm
  · rw [if_neg hab, if_neg hab, if_neg hab, if_neg hab,
      if_neg hab, if_neg hab]

private theorem shE (x c' c g p : Nat) :
    (x + c') + ((c + g) + p) = ((x + p) + g) + (c' + c) := by
  have hL : (x + c') + ((c + g) + p)
      = x + (c' + (c + (g + p))) := by
    rw [Nat.add_assoc x c' ((c + g) + p),
      Nat.add_assoc c g p]
  have hR : ((x + p) + g) + (c' + c)
      = x + (c' + (c + (g + p))) := by
    rw [Nat.add_assoc (x + p) g (c' + c),
      Nat.add_assoc x p (g + (c' + c)),
      Nat.add_left_comm g c' c,
      Nat.add_left_comm p c' (g + c),
      Nat.add_left_comm p g c,
      Nat.add_comm p c,
      Nat.add_left_comm g c p]
  rw [hL, hR]

private theorem shM (c c' p p' w n h g : Nat) :
    (((c' + (n + h)) + p') + ((p + w) + c)) + g
      = ((c + c') + (p + p')) + (((w + n) + h) + g) := by
  have hL : (((c' + (n + h)) + p') + ((p + w) + c)) + g
      = c + (c' + (p + (p' + (w + (n + (h + g)))))) := by
    rw [Nat.add_assoc ((c' + (n + h)) + p') ((p + w) + c) g,
      Nat.add_assoc (c' + (n + h)) p' (((p + w) + c) + g),
      Nat.add_assoc c' (n + h) (p' + (((p + w) + c) + g)),
      Nat.add_assoc (p + w) c g,
      Nat.add_assoc p w (c + g),
      Nat.add_assoc n h (p' + (p + (w + (c + g)))),
      Nat.add_left_comm w c g,
      Nat.add_left_comm p c (w + g),
      Nat.add_left_comm p' c (p + (w + g)),
      Nat.add_left_comm h c (p' + (p + (w + g))),
      Nat.add_left_comm n c (h + (p' + (p + (w + g)))),
      Nat.add_left_comm c' c (n + (h + (p' + (p + (w + g))))),
      Nat.add_left_comm p' p (w + g),
      Nat.add_left_comm h p (p' + (w + g)),
      Nat.add_left_comm n p (h + (p' + (w + g))),
      Nat.add_left_comm h p' (w + g),
      Nat.add_left_comm n p' (h + (w + g)),
      Nat.add_left_comm h w g,
      Nat.add_left_comm n w (h + g)]
  have hR : ((c + c') + (p + p')) + (((w + n) + h) + g)
      = c + (c' + (p + (p' + (w + (n + (h + g)))))) := by
    rw [Nat.add_assoc (c + c') (p + p') (((w + n) + h) + g),
      Nat.add_assoc c c' ((p + p') + (((w + n) + h) + g)),
      Nat.add_assoc p p' (((w + n) + h) + g),
      Nat.add_assoc (w + n) h g,
      Nat.add_assoc w n (h + g)]
  rw [hL, hR]

/-- The eigen-read's crossed equation at a matched-length key
(`thm:weylchar`'s assembly closed): the key's square against the
product's coefficient crosses with the top display's — the
Leibniz split against the folded trace recursion, the convolution
and the display-1 identity closing the collection. -/
private theorem eigenCross (mult : List Nat → Nat) (lam : Shape)
    (hrec : recReadE lam mult)
    (hsym : symReadE lam.length mult)
    (y : List Nat) (hy : y.length = lam.length) (s : Bool) :
    stdSq y * prodCount mult lam.length y s
        + stdSq (display lam) * prodCount mult lam.length y (!s)
      = stdSq (display lam) * prodCount mult lam.length y s
        + stdSq y * prodCount mult lam.length y (!s) := by
  have haug : ∀ t : Bool,
      (stdSq y * prodCount mult lam.length y t
        + stdSq (display lam) * prodCount mult lam.length y (!t))
      + (2 * tieFold lam.length y (!t)
          (fun _ chi => movedSnd mult chi)
        + 2 * tieFold lam.length y t
          (fun _ chi => movedSnd mult chi))
    = (((tieFold lam.length y (!t)
            (fun _ chi => stdSq chi * mult chi)
          + (2 * tieFold lam.length y (!t)
              (fun _ chi => sumNat chi * mult chi)
            + 2 * ground.famFold Nat.add 0
              (fun ab => prodD mult ab.1 lam.length y (!t))
              (pairsOf lam.length)))
        + stdSq (unitDisp lam.length)
          * prodCount mult lam.length y (!t))
      + ((stdSq (unitDisp lam.length)
            * prodCount mult lam.length y t
          + 2 * tieFold lam.length y t
            (fun W chi => ground.dotNat W chi * mult chi))
        + tieFold lam.length y t
          (fun _ chi => stdSq chi * mult chi)))
      + 2 * ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y (!t))
        (pairsOf lam.length) := by
    intro t
    have h2 := recFold mult lam hrec y (!t)
    rw [uSplit mult lam.length y (!t),
      uCollect mult lam.length y (!t),
      Nat.left_distrib 2
        (tieFold lam.length y (!t)
          (fun _ chi => sumNat chi * mult chi))
        (ground.famFold Nat.add 0
          (fun ab => prodD mult ab.1 lam.length y (!t))
          (pairsOf lam.length))] at h2
    have h4 := gRegroup mult lam.length y (!t)
    rw [Bool.not_not t] at h4
    rw [← addJoinHeadFront
        (stdSq (display lam) * prodCount mult lam.length y (!t))
        (2 * tieFold lam.length y (!t)
          (fun _ chi => movedSnd mult chi))
        (stdSq y * prodCount mult lam.length y t)
        (2 * tieFold lam.length y t
          (fun _ chi => movedSnd mult chi)),
      h2, leibSplit mult lam.length y t,
      Nat.add_add_add_comm
        ((tieFold lam.length y (!t)
            (fun _ chi => stdSq chi * mult chi)
          + (2 * tieFold lam.length y (!t)
              (fun _ chi => sumNat chi * mult chi)
            + 2 * ground.famFold Nat.add 0
              (fun ab => prodD mult ab.1 lam.length y (!t))
              (pairsOf lam.length)))
          + stdSq (unitDisp lam.length)
            * prodCount mult lam.length y (!t))
        (2 * tieFold lam.length y (!t)
          (fun _ chi => movedFst mult chi))
        ((stdSq (unitDisp lam.length)
            * prodCount mult lam.length y t
          + 2 * tieFold lam.length y t
            (fun W chi => ground.dotNat W chi * mult chi))
          + tieFold lam.length y t
            (fun _ chi => stdSq chi * mult chi))
        (2 * tieFold lam.length y t
          (fun _ chi => movedSnd mult chi)),
      ← Nat.left_distrib 2
        (tieFold lam.length y (!t)
          (fun _ chi => movedFst mult chi))
        (tieFold lam.length y t
          (fun _ chi => movedSnd mult chi)),
      ← h4]
  refine addCancelR
    (2 * tieFold lam.length y (!s)
        (fun _ chi => movedSnd mult chi)
      + 2 * tieFold lam.length y s
        (fun _ chi => movedSnd mult chi))
    ?_
  have hLe := haug s
  have hRe := haug (!s)
  rw [Bool.not_not s] at hRe
  rw [Nat.add_comm
      (stdSq y * prodCount mult lam.length y (!s))
      (stdSq (display lam) * prodCount mult lam.length y s),
    Nat.add_comm
      (2 * tieFold lam.length y s
        (fun _ chi => movedSnd mult chi))
      (2 * tieFold lam.length y (!s)
        (fun _ chi => movedSnd mult chi))] at hRe
  rw [hLe, hRe]
  have h6 := convAll mult lam.length y s
  have h7 := cofDAll mult lam.length y hy hsym s
  have hsum : (tieFold lam.length y s
        (fun W chi => ground.dotNat W chi * mult chi)
      + tieFold lam.length y (!s)
        (fun _ chi => sumNat chi * mult chi)
      + ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length))
      + (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length)
      + ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length)
      + ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y (!s))
        (pairsOf lam.length))
    = (tieFold lam.length y (!s)
        (fun W chi => ground.dotNat W chi * mult chi)
      + tieFold lam.length y s
        (fun _ chi => sumNat chi * mult chi)
      + ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length))
      + (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length)
      + ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length)
      + ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y s)
        (pairsOf lam.length)) := by
    rw [h6, h7]
  rw [shE (tieFold lam.length y s
        (fun W chi => ground.dotNat W chi * mult chi)
      + tieFold lam.length y (!s)
        (fun _ chi => sumNat chi * mult chi))
      (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y (!s))
        (pairsOf lam.length)),
    shE (tieFold lam.length y (!s)
        (fun W chi => ground.dotNat W chi * mult chi)
      + tieFold lam.length y s
        (fun _ chi => sumNat chi * mult chi))
      (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y s)
        (pairsOf lam.length)),
    Nat.add_comm
      (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length))] at hsum
  have hstar := addCancelR
    (ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length)
      + ground.famFold Nat.add 0
        (fun ab => cofDFold mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length))
    hsum
  have hstar2 := congrArg (fun x => 2 * x) hstar
  rw [Nat.left_distrib 2
      ((tieFold lam.length y s
          (fun W chi => ground.dotNat W chi * mult chi)
        + tieFold lam.length y (!s)
          (fun _ chi => sumNat chi * mult chi))
        + ground.famFold Nat.add 0
          (fun ab => prodD mult ab.1 lam.length y (!s))
          (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length)),
    Nat.left_distrib 2
      (tieFold lam.length y s
          (fun W chi => ground.dotNat W chi * mult chi)
        + tieFold lam.length y (!s)
          (fun _ chi => sumNat chi * mult chi))
      (ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y (!s))
        (pairsOf lam.length)),
    Nat.left_distrib 2
      (tieFold lam.length y s
        (fun W chi => ground.dotNat W chi * mult chi))
      (tieFold lam.length y (!s)
        (fun _ chi => sumNat chi * mult chi)),
    Nat.left_distrib 2
      ((tieFold lam.length y (!s)
          (fun W chi => ground.dotNat W chi * mult chi)
        + tieFold lam.length y s
          (fun _ chi => sumNat chi * mult chi))
        + ground.famFold Nat.add 0
          (fun ab => prodD mult ab.1 lam.length y s)
          (pairsOf lam.length))
      (ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length)),
    Nat.left_distrib 2
      (tieFold lam.length y (!s)
          (fun W chi => ground.dotNat W chi * mult chi)
        + tieFold lam.length y s
          (fun _ chi => sumNat chi * mult chi))
      (ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y s)
        (pairsOf lam.length)),
    Nat.left_distrib 2
      (tieFold lam.length y (!s)
        (fun W chi => ground.dotNat W chi * mult chi))
      (tieFold lam.length y s
        (fun _ chi => sumNat chi * mult chi))] at hstar2
  rw [shM (tieFold lam.length y s
        (fun _ chi => stdSq chi * mult chi))
      (tieFold lam.length y (!s)
        (fun _ chi => stdSq chi * mult chi))
      (stdSq (unitDisp lam.length)
        * prodCount mult lam.length y s)
      (stdSq (unitDisp lam.length)
        * prodCount mult lam.length y (!s))
      (2 * tieFold lam.length y s
        (fun W chi => ground.dotNat W chi * mult chi))
      (2 * tieFold lam.length y (!s)
        (fun _ chi => sumNat chi * mult chi))
      (2 * ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y (!s))
        (pairsOf lam.length))
      (2 * ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y (!s))
        (pairsOf lam.length)),
    shM (tieFold lam.length y (!s)
        (fun _ chi => stdSq chi * mult chi))
      (tieFold lam.length y s
        (fun _ chi => stdSq chi * mult chi))
      (stdSq (unitDisp lam.length)
        * prodCount mult lam.length y (!s))
      (stdSq (unitDisp lam.length)
        * prodCount mult lam.length y s)
      (2 * tieFold lam.length y (!s)
        (fun W chi => ground.dotNat W chi * mult chi))
      (2 * tieFold lam.length y s
        (fun _ chi => sumNat chi * mult chi))
      (2 * ground.famFold Nat.add 0
        (fun ab => prodD mult ab.1 lam.length y s)
        (pairsOf lam.length))
      (2 * ground.famFold Nat.add 0
        (fun ab => prodG mult ab.1 ab.2 lam.length y s)
        (pairsOf lam.length)),
    Nat.add_comm
      (tieFold lam.length y (!s)
        (fun _ chi => stdSq chi * mult chi))
      (tieFold lam.length y s
        (fun _ chi => stdSq chi * mult chi)),
    Nat.add_comm
      (stdSq (unitDisp lam.length)
        * prodCount mult lam.length y (!s))
      (stdSq (unitDisp lam.length)
        * prodCount mult lam.length y s),
    hstar2]

/-! The conclusion's kit (`thm:weylchar`'s conclusion): the
off-length reads, the crossed cancellation, and the sorted key's
gap against the unit display — the tie at the unit display with
its weak descent, the dominance walk's sum and prefix
constructors, and the display bridge. -/

/-- The alternant's graded count at an off-length key: the count's
unit on both sides, the permuted display's own length the
refusal. -/
private theorem sideCount_offLen {d : Nat} (beta : List Nat)
    {y : List Nat} (hy : ¬ y.length = d) (t : Bool) :
    sideCount d beta y t = 0 := by
  show ground.famFold Nat.add 0
    (fun p => if parity p = t then
        (if expo beta p = y then 1 else 0)
      else 0)
    (perms d) = 0
  refine (ground.famFold_congr_members Nat.add 0 _
    (fun _ => (0 : Nat)) (perms d) (fun p hp => ?_)).trans
    (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d))
  by_cases hpar : parity p = t
  · rw [if_pos hpar,
      if_neg (fun he : expo beta p = y => by
        obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
        have hEl : (expo beta p).length = d := by
          show (p.map (ground.getAt 0 beta)).length = d
          rw [ground.length_map, hplen]
        exact absurd ((congrArg List.length he).symm.trans hEl)
          hy)]
  · rw [if_neg hpar]

/-- The product's graded coefficient at refused ties: every
occupied tie's multiplicity at the count's unit reads the fold
there, both sides. -/
private theorem prodCount_zeroTies {d : Nat}
    (mult : List Nat → Nat) (y : List Nat)
    (h : ∀ p, 0 < ground.countOf p (perms d) →
      ∀ chi, tieGap y (expo (unitDisp d) p) = some chi →
        mult chi = 0)
    (t : Bool) : prodCount mult d y t = 0 := by
  show ground.famFold Nat.add 0
    (fun p =>
      if parity p = t then
        multAtGap mult y (expo (unitDisp d) p)
      else 0)
    (perms d) = 0
  refine (ground.famFold_congr_members Nat.add 0 _
    (fun _ => (0 : Nat)) (perms d)
    (fun p hp => ?_)).trans
    (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d))
  by_cases hpar : parity p = t
  · rw [if_pos hpar]
    cases ht : tieGap y (expo (unitDisp d) p) with
    | some chi =>
      show (match tieGap y (expo (unitDisp d) p) with
        | some nu => mult nu
        | none => 0) = 0
      rw [ht]
      exact h p hp chi ht
    | none =>
      show (match tieGap y (expo (unitDisp d) p) with
        | some nu => mult nu
        | none => 0) = 0
      rw [ht]
  · rw [if_neg hpar]

/-- The product's graded coefficient at an off-length key: the
count's unit on both sides, the tie refusing at every permuted
display's own length. -/
private theorem prodCount_offLen {d : Nat} (mult : List Nat → Nat)
    {y : List Nat} (hy : ¬ y.length = d) (t : Bool) :
    prodCount mult d y t = 0 :=
  prodCount_zeroTies mult y
    (fun p hp chi ht => by
      obtain ⟨_, hzl, _⟩ :=
        tieGap_reads y (expo (unitDisp d) p) chi ht
      have hEl : (expo (unitDisp d) p).length = d := by
        obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
        show (p.map (ground.getAt 0 (unitDisp d))).length = d
        rw [ground.length_map, hplen]
      exact absurd (hzl.symm.trans hEl) hy)
    t

/-- The crossed cancellation: at two distinct weights the crossed
equation forces its two carried members equal, the gap's own
product cancelling. -/
private theorem crossCancel {a b x z : Nat} (hne : ¬ a = b)
    (h : a * x + b * z = b * x + a * z) : x = z := by
  have hnlt : ∀ g u v : Nat, 0 < g → g * u = g * v →
      ¬ u < v := by
    intro g u v hg hguv huv
    have hz : g * u + 0 = g * u + g * (v - u) := by
      show g * u = g * u + g * (v - u)
      rw [← Nat.mul_add, natAddSubCancel (Nat.le_of_succ_le huv)]
      exact hguv
    exact absurd (addCancelL (g * u) hz)
      (Nat.ne_of_lt (Nat.mul_pos hg (subPos huv)))
  have hcan : ∀ g u v : Nat, 0 < g → g * u = g * v → u = v := by
    intro g u v hg hguv
    cases Nat.lt_or_ge u v with
    | inl hlt => exact absurd hlt (hnlt g u v hg hguv)
    | inr hge =>
      cases Nat.lt_or_ge v u with
      | inl hlt => exact absurd hlt (hnlt g v u hg hguv.symm)
      | inr hge' => exact Nat.le_antisymm hge' hge
  cases Nat.lt_or_ge a b with
  | inl hab =>
    have hb : a + (b - a) = b :=
      natAddSubCancel (Nat.le_of_succ_le hab)
    rw [← hb, mulAddR a (b - a) z, mulAddR a (b - a) x] at h
    have h2 : (a * x + a * z) + (b - a) * z
        = (a * x + a * z) + (b - a) * x := by
      rw [Nat.add_assoc (a * x) (a * z) ((b - a) * z),
        Nat.add_assoc (a * x) (a * z) ((b - a) * x),
        Nat.add_comm (a * z) ((b - a) * x),
        ← Nat.add_assoc (a * x) ((b - a) * x) (a * z)]
      exact h
    exact (hcan (b - a) z x (subPos hab)
      (addCancelL (a * x + a * z) h2)).symm
  | inr hge =>
    cases Nat.lt_or_ge b a with
    | inl hba =>
      have ha : b + (a - b) = a :=
        natAddSubCancel (Nat.le_of_succ_le hba)
      rw [← ha, mulAddR b (a - b) x, mulAddR b (a - b) z] at h
      have h2 : (b * x + b * z) + (a - b) * x
          = (b * x + b * z) + (a - b) * z := by
        rw [Nat.add_assoc (b * x) (b * z) ((a - b) * x),
          Nat.add_comm (b * z) ((a - b) * x),
          ← Nat.add_assoc (b * x) ((a - b) * x) (b * z),
          Nat.add_assoc (b * x) (b * z) ((a - b) * z)]
        exact h
      exact hcan (a - b) x z (subPos hba)
        (addCancelL (b * x + b * z) h2)
    | inr hge' => exact absurd (Nat.le_antisymm hge' hge) hne

/-- A strictly descending occupied key dominates the unit display
entrywise: the value at a place at least the places beyond it with
one apiece. -/
private theorem unitLe_of_desc {d : Nat} {y : List Nat}
    (hy : y.length = d)
    (hdesc : ∀ i, i + 1 < d →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i)
    (hpos : ∀ i, i < d → 0 < ground.getAt 0 y i) :
    ∀ i, i < d → ground.getAt 0 (unitDisp d) i
      ≤ ground.getAt 0 y i := by
  subst hy
  have key : ∀ g i, i + g + 1 = y.length →
      y.length - i ≤ ground.getAt 0 y i := by
    intro g
    induction g with
    | zero =>
      intro i hi
      have hi' : i + 1 = y.length := hi
      have hd : y.length - i = 1 := by
        rw [← hi', Nat.add_comm i 1]
        exact addSubSelfR 1 i
      rw [hd]
      exact hpos i (by rw [← hi']; exact Nat.lt_succ_self i)
    | succ g ih =>
      intro i hi
      have hj : (i + 1) + g + 1 = y.length := by
        rw [Nat.add_assoc i 1 g, Nat.add_comm 1 g]
        exact hi
      have hlt : i + 1 < y.length := by
        rw [← hj]
        exact Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) g)
          (Nat.lt_succ_self _)
      have hstep : y.length - (i + 1) + 1 ≤ ground.getAt 0 y i :=
        Nat.le_trans (Nat.succ_le_succ (ih (i + 1) hj))
          (hdesc i hlt)
      rw [← ground.subSuccAdd (Nat.le_of_succ_le hlt)]
      exact hstep
  intro i hi
  rw [getAt_unitDisp y.length i hi]
  have hjoin : i + (y.length - (i + 1)) + 1 = y.length := by
    rw [Nat.add_assoc i (y.length - (i + 1)) 1,
      Nat.add_comm (y.length - (i + 1)) 1,
      ← Nat.add_assoc i 1 (y.length - (i + 1))]
    exact natAddSubCancel hi
  exact key (y.length - (i + 1)) i hjoin

/-- The tie's gap at the unit display descends weakly: a strictly
descending key's gap against the unit display is a content. -/
private theorem mu_desc {d : Nat} {y mu : List Nat}
    (hy : y.length = d)
    (hdesc : ∀ i, i + 1 < d →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i)
    (htu : tieGap y (unitDisp d) = some mu) :
    ∀ i, i + 1 < d →
      ground.getAt 0 mu (i + 1) ≤ ground.getAt 0 mu i := by
  obtain ⟨_, _, hent⟩ := tieGap_reads y (unitDisp d) mu htu
  have sh : ∀ A B C : Nat, A + B < C + (B + 1) →
      (B + 1) + A ≤ (B + 1) + C := by
    intro A B C hABC
    rw [Nat.add_comm (B + 1) A, Nat.add_comm (B + 1) C,
      ← Nat.add_assoc A B 1]
    exact hABC
  intro i hid
  have hiy : i < y.length := by
    rw [hy]
    exact Nat.lt_of_succ_lt hid
  have hi1y : i + 1 < y.length := by
    rw [hy]
    exact hid
  have hu : ground.getAt 0 (unitDisp d) i
      = ground.getAt 0 (unitDisp d) (i + 1) + 1 := by
    rw [getAt_unitDisp d i (Nat.lt_of_succ_lt hid),
      getAt_unitDisp d (i + 1) hid]
    exact (ground.subSuccAdd (Nat.le_of_succ_le hid)).symm
  have h0 := hdesc i hid
  rw [← hent i hiy, ← hent (i + 1) hi1y, hu] at h0
  exact leCancelL _ (sh _ _ _ h0)

/-- The dominance walk's total: the first family's whole prefix
joins the carried slack with the second's, the walk's own
orientation. -/
theorem domGo_sum : ∀ (s : Nat) (X Y : List Nat),
    domGo s X Y = true →
    prefixAt X.length X = s + prefixAt Y.length Y
  | s, [], [], h => by
    rw [ground.beqEq _ _ h]
    rfl
  | _, [], _ :: _, h => Bool.noConfusion h
  | _, _ :: _, [], h => Bool.noConfusion h
  | s, a :: X, b :: Y, h => by
    have h' : (if a ≤ s + b then domGo (s + b - a) X Y else false)
        = true := h
    by_cases hab : a ≤ s + b
    · rw [if_pos hab] at h'
      have hrec := domGo_sum (s + b - a) X Y h'
      show a + prefixAt X.length X
        = s + (b + prefixAt Y.length Y)
      rw [hrec, ← Nat.add_assoc a (s + b - a) (prefixAt Y.length Y),
        natAddSubCancel hab,
        Nat.add_assoc s b (prefixAt Y.length Y)]
    · rw [if_neg hab] at h'
      exact Bool.noConfusion h'

/-- The dominance walk's constructor: matched lengths with every
prefix at or below the slack's join and the totals joining name
the walk. -/
theorem domGo_ofPrefix : ∀ (s : Nat) (X Y : List Nat),
    X.length = Y.length →
    (∀ k, prefixAt k X ≤ s + prefixAt k Y) →
    prefixAt X.length X = s + prefixAt Y.length Y →
    domGo s X Y = true
  | s, [], [], _, _, htot => by
    have hs : 0 = s := htot
    show Nat.beq s 0 = true
    rw [← hs]
    rfl
  | _, [], _ :: _, hl, _, _ => Nat.noConfusion hl
  | _, _ :: _, [], hl, _, _ => Nat.noConfusion hl
  | s, a :: X, b :: Y, hl, hpre, htot => by
    have hab : a ≤ s + b := by
      have h1 := hpre 1
      rw [prefixAt_one (a :: X), prefixAt_one (b :: Y)] at h1
      exact h1
    show (if a ≤ s + b then domGo (s + b - a) X Y else false)
      = true
    rw [if_pos hab]
    refine domGo_ofPrefix (s + b - a) X Y (Nat.succ.inj hl)
      (fun k => ?_) ?_
    · have h2 := hpre (k + 1)
      have h3 : a + prefixAt k X
          ≤ a + ((s + b - a) + prefixAt k Y) := by
        rw [← Nat.add_assoc a (s + b - a) (prefixAt k Y),
          natAddSubCancel hab, Nat.add_assoc s b (prefixAt k Y)]
        exact h2
      exact leCancelL a h3
    · have h4 : a + prefixAt X.length X
          = a + ((s + b - a) + prefixAt Y.length Y) := by
        rw [← Nat.add_assoc a (s + b - a) (prefixAt Y.length Y),
          natAddSubCancel hab,
          Nat.add_assoc s b (prefixAt Y.length Y)]
        exact htot
      exact addCancelL a h4

/-- The dominance order's antisymmetry: two walks in both
directions read equal prefixes at every key, and the entries
follow at the joined reads. -/
theorem domBy_antisymm (X Y : List Nat)
    (hxy : domBy X Y) (hyx : domBy Y X) : X = Y := by
  have hlen : X.length = Y.length := domGo_len 0 X Y hxy
  have hpre : ∀ k, prefixAt k X = prefixAt k Y := by
    intro k
    have h1 := domGo_prefix 0 X Y hxy k
    have h2 := domGo_prefix 0 Y X hyx k
    rw [Nat.zero_add] at h1
    rw [Nat.zero_add] at h2
    exact Nat.le_antisymm h1 h2
  refine ground.getAt_ext 0 X Y hlen ?_
  intro i hi
  have hs : prefixAt i X + ground.getAt 0 X i
      = prefixAt i Y + ground.getAt 0 Y i := by
    rw [← prefixAt_succ X i hi,
      ← prefixAt_succ Y i (by rw [← hlen]; exact hi), hpre (i + 1)]
  rw [hpre i] at hs
  exact ground.addCancelL (prefixAt i Y) hs

/-- The dominance order flips at the reversals: the two lists'
totals tie, and at every key a prefix of the second's reversal
joins that list's complementary prefix to the shared total, so the
complementary reads exchange the comparison. -/
theorem domBy_reverse (X Y : List Nat) (h : domBy X Y) :
    domBy Y.reverse X.reverse := by
  have hl : X.length = Y.length := domGo_len 0 X Y h
  have hs : prefixAt X.length X = 0 + prefixAt Y.length Y :=
    domGo_sum 0 X Y h
  have hsum : sumNat X = sumNat Y := by
    rw [← ground.prefixAt_full X X.length (Nat.le_refl _),
      ← ground.prefixAt_full Y Y.length (Nat.le_refl _), hs,
      Nat.zero_add]
  have hfull : ∀ m : List Nat,
      prefixAt m.reverse.length m.reverse = sumNat m := by
    intro m
    rw [ground.length_reverse]
    have hj := ground.prefix_reverse_join m.length m 0
      (Nat.add_zero m.length)
    rw [prefixAt_zero m, Nat.add_zero] at hj
    exact hj
  refine domGo_ofPrefix 0 Y.reverse X.reverse
    (by rw [ground.length_reverse, ground.length_reverse, hl])
    (fun k => ?_) ?_
  · rw [Nat.zero_add]
    match Nat.lt_or_ge k (Y.length + 1) with
    | .inl hk =>
      have hkd : k ≤ Y.length := Nat.le_of_lt_succ hk
      obtain ⟨g, hg⟩ := Nat.le.dest hkd
      have hB := ground.prefix_reverse_join k Y g hg
      have hgX : k + g = X.length := by
        rw [hl]
        exact hg
      have hA := ground.prefix_reverse_join k X g hgX
      have hQle : prefixAt g X ≤ prefixAt g Y := by
        have h1 := domGo_prefix 0 X Y h g
        rw [Nat.zero_add] at h1
        exact h1
      obtain ⟨w, hw⟩ := Nat.le.dest hQle
      have hA2 : prefixAt k Y.reverse + (prefixAt g X + w)
          = sumNat Y := by
        rw [hw]
        exact hB
      have h5 : prefixAt g X + (prefixAt k Y.reverse + w)
          = sumNat Y := by
        rw [Nat.add_left_comm]
        exact hA2
      have h7 : sumNat Y = prefixAt g X + prefixAt k X.reverse := by
        rw [Nat.add_comm (prefixAt g X) (prefixAt k X.reverse),
          ← hsum]
        exact hA.symm
      exact Nat.le.intro
        (ground.addCancelL (prefixAt g X) (h5.trans h7))
    | .inr hk =>
      have hd : Y.length ≤ k := Nat.le_of_succ_le hk
      rw [ground.prefixAt_full Y.reverse k
          (by rw [ground.length_reverse]; exact hd),
        ground.prefixAt_full X.reverse k
          (by rw [ground.length_reverse, hl]; exact hd),
        ground.sumNat_reverse Y, ground.sumNat_reverse X, hsum]
      exact Nat.le_refl _
  · rw [Nat.zero_add, hfull Y, hfull X]
    exact hsum.symm

/-- The permuted unit display's sum: one value at every
permutation, the unit display's own. -/
private theorem sumExpo {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (perms d)) :
    sumNat (expo (unitDisp d) p) = sumNat (unitDisp d) := by
  have h1 : sumNat (expo (unitDisp d) p)
      = ground.famFold Nat.add 0
        (ground.getAt 0 (unitDisp d)) p := by
    show sumNat (p.map (ground.getAt 0 (unitDisp d))) = _
    exact sumMap _ p
  have h2 : sumNat (unitDisp d)
      = ground.famFold Nat.add 0
        (ground.getAt 0 (unitDisp d)) (List.range d) := by
    have h3 : sumNat (expo (unitDisp d) (List.range d))
        = ground.famFold Nat.add 0
          (ground.getAt 0 (unitDisp d)) (List.range d) := by
      show sumNat ((List.range d).map
        (ground.getAt 0 (unitDisp d))) = _
      exact sumMap _ (List.range d)
    rw [← h3, expoRange d]
  rw [h1, h2]
  exact ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
    _ p (List.range d) (places.perm_counts_range _ hp)

/-- The display bridge: a key whose gap against the unit display
is the top line is the top display itself. -/
private theorem display_of_muRow {lam : Shape} {y mu : List Nat}
    (hy : y.length = lam.length)
    (htu : tieGap y (unitDisp lam.length) = some mu)
    (hmu : mu = rowList lam) :
    y = display lam := by
  obtain ⟨_, _, hent⟩ :=
    tieGap_reads y (unitDisp lam.length) mu htu
  refine ground.getAt_ext 0 _ _ (by rw [hy, length_display]) ?_
  intro i hi
  have hil : i < lam.length := by
    rw [← hy]
    exact hi
  rw [getAt_display lam i hil, ← hent i hi, hmu,
    getAt_unitDisp lam.length i hil]

/-! The sorted key's graded reads and the walk's measure
(`thm:weylchar`'s conclusion): a strictly descending key reads its
own display once on the even side, two distinct sorted keys read
the count's unit, and the adjacent ascent's swap drops the
inversion measure by exactly one. -/

/-- The alternant's graded count at a strictly descending key
against its own display: the identity permutation the one
contributor, the even side reading one and the odd the count's
unit. -/
theorem sideCount_desc_self {d : Nat} {z : List Nat}
    (hz : z.length = d)
    (hdesc : ∀ i, i + 1 < d →
      ground.getAt 0 z (i + 1) < ground.getAt 0 z i) :
    sideCount d z z false = 1 ∧ sideCount d z z true = 0 := by
  have hdl : ∀ i, i + 1 < z.length →
      ground.getAt 0 z (i + 1) < ground.getAt 0 z i :=
    fun i hi => hdesc i (by rw [← hz]; exact hi)
  have hkey : ∀ p, 0 < ground.countOf p (perms d) →
      expo z p = z → p = List.range d := by
    intro p hp hg
    obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
    refine ground.getAt_ext 0 p (List.range d)
      (by rw [hplen, length_range]) ?_
    intro j hj
    have hjd : j < d := by rw [← hplen]; exact hj
    rw [getAt_range d j hjd]
    have h1 : ground.getAt 0 (expo z p) j
        = ground.getAt 0 z (ground.getAt 0 p j) :=
      ground.getAt_map 0 0 (ground.getAt 0 z) p j hj
    rw [hg] at h1
    have hbnd : ground.getAt 0 p j < z.length := by
      rw [hz]
      exact hpval _ (countOf_getAt_pos 0 p j hj)
    exact desc_inj hdl (ground.getAt 0 p j) j hbnd
      (by rw [hz]; exact hjd) h1.symm
  constructor
  · show ground.famFold Nat.add 0
        (fun p => if parity p = false then
            (if expo z p = z then 1 else 0)
          else 0)
        (perms d) = 1
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun p => if List.range d = p then (1 : Nat) else 0)
        (perms d) (fun p hp => by
          by_cases hpr : List.range d = p
          · have hpar : parity p = false := by
              rw [← hpr]
              exact parity_range d
            have hexp : expo z p = z := by
              rw [← hpr]
              exact ground.range_map_getAt 0 d z hz
            rw [if_pos hpar, if_pos hexp, if_pos hpr]
          · rw [if_neg hpr]
            by_cases hpar : parity p = false
            · rw [if_pos hpar,
                if_neg (fun he : expo z p = z =>
                  hpr (hkey p hp he).symm)]
            · rw [if_neg hpar]),
      ← countOf_fold (List.range d) (perms d),
      countRangePerms d]
  · show ground.famFold Nat.add 0
        (fun p => if parity p = true then
            (if expo z p = z then 1 else 0)
          else 0)
        (perms d) = 0
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun _ => (0 : Nat)) (perms d) (fun p hp => by
          by_cases hpar : parity p = true
          · rw [if_pos hpar,
              if_neg (fun he : expo z p = z => by
                rw [hkey p hp he, parity_range d] at hpar
                exact Bool.noConfusion hpar)]
          · rw [if_neg hpar]),
      famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d)]

/-- The alternant's graded count at two distinct strictly
descending keys: the count's unit on both sides, the sorted
spelling's uniqueness the refusal. -/
theorem sideCount_desc_ne {d : Nat} {z y : List Nat}
    (hz : z.length = d) (hy : y.length = d)
    (hdz : ∀ i, i + 1 < d →
      ground.getAt 0 z (i + 1) < ground.getAt 0 z i)
    (hdy : ∀ i, i + 1 < d →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i)
    (hne : ¬ y = z) (t : Bool) :
    sideCount d z y t = 0 := by
  have hdzl : ∀ i, i + 1 < z.length →
      ground.getAt 0 z (i + 1) < ground.getAt 0 z i :=
    fun i hi => hdz i (by rw [← hz]; exact hi)
  have hdyl : ∀ i, i + 1 < y.length →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i :=
    fun i hi => hdy i (by rw [← hy]; exact hi)
  show ground.famFold Nat.add 0
    (fun p => if parity p = t then
        (if expo z p = y then 1 else 0)
      else 0)
    (perms d) = 0
  refine (ground.famFold_congr_members Nat.add 0 _
    (fun _ => (0 : Nat)) (perms d) (fun p hp => ?_)).trans
    (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) (perms d))
  by_cases hpar : parity p = t
  · have hno : ¬ expo z p = y := by
      intro he
      have hcv : ∀ v, ground.countOf v y = ground.countOf v z := by
        intro v
        rw [← he]
        exact places.countOf_comp d v hp hz
      exact hne
        (descUnique y z (by rw [hy, hz]) hdyl hdzl hcv)
    rw [if_pos hpar, if_neg hno]
  · rw [if_neg hpar]

/-- The ascent count: the pairs at the earlier entry below the
later, the walk's measure. -/
private def ascCount : List Nat → Nat
  | [] => 0
  | a :: t => ground.countAbove a t + ascCount t

/-- The count beyond a value as its indicator's fold over the
family. -/
private theorem countAbove_fold (c : Nat) : ∀ l : List Nat,
    ground.countAbove c l
      = ground.famFold Nat.add 0 (fun b => if c < b then 1 else 0) l
  | [] => rfl
  | b :: t =>
    (ground.countAbove_cons c b t).trans
      (congrArg (fun x => (if c < b then 1 else 0) + x)
        (countAbove_fold c t))

/-- The count beyond a value is kept by an adjacent exchange: the
entries are the family's own. -/
private theorem countAbove_swapAdj (c : Nat) :
    ∀ (i : Nat) (t : List Nat),
    ground.countAbove c (places.swapPair i (i + 1) t)
      = ground.countAbove c t := by
  intro i t
  rw [countAbove_fold c (places.swapPair i (i + 1) t),
    countAbove_fold c t]
  exact ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun b => if c < b then 1 else 0)
    (places.swapPair i (i + 1) t) t
    (fun x => places.countOf_swapPair x i (i + 1) t)

/-- The walk's step: exchanging an adjacent ascent drops the
ascent count by exactly one. -/
private theorem ascCount_swapAdj : ∀ (t : List Nat) (i : Nat),
    i + 1 < t.length →
    ground.getAt 0 t i < ground.getAt 0 t (i + 1) →
    ascCount (places.swapPair i (i + 1) t) + 1 = ascCount t
  | [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | [_], i, hi, _ =>
    absurd (Nat.le_of_succ_le_succ hi) (Nat.not_succ_le_zero i)
  | a :: b :: u, 0, _, hlt => by
    have hab : a < b := hlt
    have hba : ¬ b < a :=
      fun h => Nat.lt_irrefl a (Nat.lt_trans hab h)
    rw [places.swapPair_adjacent 0 (a :: b :: u)]
    show ground.countAbove b (a :: u)
        + (ground.countAbove a u + ascCount u) + 1
      = ground.countAbove a (b :: u)
        + (ground.countAbove b u + ascCount u)
    rw [ground.countAbove_cons, ground.countAbove_cons,
      if_neg hba, if_pos hab, Nat.zero_add,
      Nat.add_comm (ground.countAbove b u
        + (ground.countAbove a u + ascCount u)) 1,
      Nat.add_assoc 1 (ground.countAbove a u)
        (ground.countAbove b u + ascCount u),
      Nat.add_left_comm (ground.countAbove b u)
        (ground.countAbove a u) (ascCount u)]
  | a :: u, i + 1, hi, hlt => by
    have hiu : i + 1 < u.length := Nat.lt_of_succ_lt_succ hi
    have hlt' : ground.getAt 0 u i < ground.getAt 0 u (i + 1) :=
      hlt
    rw [places.swapPair_adjacent (i + 1) (a :: u)]
    show ground.countAbove a (ground.adjSwap i u)
        + ascCount (ground.adjSwap i u) + 1
      = ground.countAbove a u + ascCount u
    rw [← places.swapPair_adjacent i u, countAbove_swapAdj a i u,
      Nat.add_assoc (ground.countAbove a u)
        (ascCount (places.swapPair i (i + 1) u)) 1,
      ascCount_swapAdj u i hiu hlt']

/-- The first non-descent's search from a stated position. -/
private def ndGo : Nat → List Nat → Option Nat
  | _, [] => none
  | _, [_] => none
  | k, a :: b :: t =>
    if a ≤ b then some k else ndGo (k + 1) (b :: t)

/-- The first position whose successor does not descend, the
walk's branch datum. -/
private def firstNonDesc (y : List Nat) : Option Nat := ndGo 0 y

/-- An exhausted search names the family strictly descending. -/
private theorem ndGo_none : ∀ (k : Nat) (y : List Nat),
    ndGo k y = none →
    ∀ i, i + 1 < y.length →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | _, [_], _ => fun i hi =>
    absurd (Nat.le_of_succ_le_succ hi) (Nat.not_succ_le_zero i)
  | k, a :: b :: t, h => by
    have h' : (if a ≤ b then some k else ndGo (k + 1) (b :: t))
        = none := h
    have hab : ¬ a ≤ b := by
      intro hle
      rw [if_pos hle] at h'
      exact nomatch h'
    have hrec : ndGo (k + 1) (b :: t) = none := by
      rw [if_neg hab] at h'
      exact h'
    intro i hi
    cases i with
    | zero => exact Nat.gt_of_not_le hab
    | succ j =>
      exact ndGo_none (k + 1) (b :: t) hrec j
        (Nat.lt_of_succ_lt_succ hi)

/-- The search's value is at or beyond its stated position. -/
private theorem ndGo_ge : ∀ (k : Nat) (y : List Nat) (m : Nat),
    ndGo k y = some m → k ≤ m
  | _, [], _, h => nomatch h
  | _, [_], _, h => nomatch h
  | k, a :: b :: t, m, h => by
    have h' : (if a ≤ b then some k else ndGo (k + 1) (b :: t))
        = some m := h
    by_cases hab : a ≤ b
    · rw [if_pos hab] at h'
      exact Nat.le_of_eq (Option.some.inj h')
    · rw [if_neg hab] at h'
      exact Nat.le_trans (Nat.le_succ k)
        (ndGo_ge (k + 1) (b :: t) m h')

/-- A found position sits inside the family with its successor at
or above it, the non-descent's own read. -/
private theorem ndGo_some : ∀ (k : Nat) (y : List Nat) (i : Nat),
    ndGo k y = some (k + i) →
    i + 1 < y.length ∧
      ground.getAt 0 y i ≤ ground.getAt 0 y (i + 1)
  | _, [], _, h => nomatch h
  | _, [_], _, h => nomatch h
  | k, a :: b :: t, i, h => by
    have h' : (if a ≤ b then some k else ndGo (k + 1) (b :: t))
        = some (k + i) := h
    by_cases hab : a ≤ b
    · rw [if_pos hab] at h'
      have h0 : k + 0 = k + i := by
        rw [Nat.add_zero]
        exact Option.some.inj h'
      rw [← addCancelL k h0]
      exact ⟨Nat.succ_lt_succ (Nat.succ_pos t.length), hab⟩
    · rw [if_neg hab] at h'
      cases i with
      | zero =>
        have hge := ndGo_ge (k + 1) (b :: t) (k + 0) h'
        rw [Nat.add_zero] at hge
        exact absurd hge (Nat.not_succ_le_self k)
      | succ j =>
        have harr : k + (j + 1) = k + 1 + j := by
          rw [Nat.add_assoc k 1 j, Nat.add_comm 1 j]
        rw [harr] at h'
        obtain ⟨hlen, hle⟩ := ndGo_some (k + 1) (b :: t) j h'
        exact ⟨Nat.succ_lt_succ hlen, hle⟩

/-- The eigen-read (`thm:weylchar`'s assembly): the trace
recursion and the reflection symmetry close the eigen equation at
every key — a matched-length key by the crossed collection, an
off-length key reading the count's unit on both sides through the
tie's refusal. -/
private theorem eigenRead (mult : List Nat → Nat) (lam : Shape)
    (hrec : recReadE lam mult) (hsym : symReadE lam.length mult)
    (y : List Nat) : eigenAt mult lam y := by
  by_cases hy : y.length = lam.length
  · exact eigenCross mult lam hrec hsym y hy false
  · show stdSq y * prodCount mult lam.length y false
        + stdSq (display lam)
          * prodCount mult lam.length y true
      = stdSq (display lam)
          * prodCount mult lam.length y false
        + stdSq y * prodCount mult lam.length y true
    rw [prodCount_offLen mult hy false, prodCount_offLen mult hy true,
    Nat.mul_zero, Nat.mul_zero]

/-! The conclusion's assembly (`thm:weylchar`'s conclusion): the
walk to the sorted representative over the ascent measure, the
sorted key's two routes — the crossed cancellation at separated
squares and the per-permutation refusal at equal ones — and the
identity's read closed at every key. -/

/-- An adjacent ascent occupies the ascent count. -/
private theorem ascCount_pos_of_asc :
    ∀ (y : List Nat) (i : Nat), i + 1 < y.length →
      ground.getAt 0 y i < ground.getAt 0 y (i + 1) →
      0 < ascCount y
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | [_], i, hi, _ =>
    absurd (Nat.le_of_succ_le_succ hi) (Nat.not_succ_le_zero i)
  | a :: b :: u, 0, _, hasc => by
    show 0 < ground.countAbove a (b :: u) + ascCount (b :: u)
    have hab : a < b := hasc
    rw [ground.countAbove_cons, if_pos hab]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 0)
      (Nat.le_trans (Nat.le_add_right 1 (ground.countAbove a u))
        (Nat.le_add_right (1 + ground.countAbove a u) (ascCount (b :: u))))
  | a :: b :: u, i + 1, hi, hasc => by
    show 0 < ground.countAbove a (b :: u) + ascCount (b :: u)
    exact Nat.lt_of_lt_of_le
      (ascCount_pos_of_asc (b :: u) i
        (Nat.lt_of_succ_lt_succ hi) hasc)
      (Nat.le_add_left (ascCount (b :: u)) (ground.countAbove a (b :: u)))

/-- The sorted key's gap at the unit display is dominated by the
rows (`thm:weylchar`'s conclusion, the support display's prefix
read): the occupied tie's content dominated by the support clause,
the permuted display's prefixes cleared by the sorted display's,
and the walk reconstructed from the prefix caps with the matched
totals. -/
private theorem mu_dom {lam : Shape} (mult : List Nat → Nat)
    (hsupp : supportReadE lam mult) {y : List Nat}
    (hy : y.length = lam.length) {p : List Nat}
    (hp : 0 < ground.countOf p (perms lam.length))
    {chi : List Nat}
    (ht : tieGap y (expo (unitDisp lam.length) p) = some chi)
    (hchi : 0 < mult chi) {mu : List Nat}
    (htu : tieGap y (unitDisp lam.length) = some mu) :
    domBy mu (rowList lam) := by
  obtain ⟨hcl, hel, _⟩ :=
    tieGap_reads y (expo (unitDisp lam.length) p) chi ht
  obtain ⟨hml, hul, _⟩ :=
    tieGap_reads y (unitDisp lam.length) mu htu
  have hdomchi : domBy chi (rowList lam) :=
    hsupp chi (hcl.trans hy) hchi
  have hpre1 : ∀ k, prefixAt k y
      = prefixAt k chi
        + prefixAt k (expo (unitDisp lam.length) p) := by
    intro k
    rw [tieGap_zip y (expo (unitDisp lam.length) p) chi ht]
    exact ground.prefixAt_zipAdd chi (expo (unitDisp lam.length) p)
      (hcl.trans hel.symm) k
  have hpre2 : ∀ k, prefixAt k y
      = prefixAt k mu + prefixAt k (unitDisp lam.length) := by
    intro k
    rw [tieGap_zip y (unitDisp lam.length) mu htu]
    exact ground.prefixAt_zipAdd mu (unitDisp lam.length)
      (hml.trans hul.symm) k
  have hexl : (expo (unitDisp lam.length) p).length
      = lam.length := hel.trans hy
  have hcap : ∀ k,
      prefixAt k (expo (unitDisp lam.length) p)
        ≤ prefixAt k (unitDisp lam.length) := by
    intro k
    by_cases hk : k ≤ lam.length
    · have he := prefixExpo hp k hk
      have hu := prefixUnit lam.length k hk
      have htri := prefixTri hp k hk
      have h6 : prefixAt k (expo (unitDisp lam.length) p)
          + prefixAt k p
        ≤ prefixAt k (unitDisp lam.length) + prefixAt k p := by
        rw [show prefixAt k (expo (unitDisp lam.length) p)
              + prefixAt k p
            = prefixAt k (unitDisp lam.length) + sumTop k k from
          he.trans hu.symm]
        exact Nat.add_le_add_left htri _
      have h7 : prefixAt k p
          + prefixAt k (expo (unitDisp lam.length) p)
        ≤ prefixAt k p
          + prefixAt k (unitDisp lam.length) := by
        rw [Nat.add_comm (prefixAt k p)
            (prefixAt k (expo (unitDisp lam.length) p)),
          Nat.add_comm (prefixAt k p)
            (prefixAt k (unitDisp lam.length))]
        exact h6
      exact leCancelL (prefixAt k p) h7
    · have hdk : lam.length ≤ k := Nat.le_of_lt (Nat.gt_of_not_le hk)
      rw [prefixAt_full (expo (unitDisp lam.length) p) k
          (by rw [hexl]; exact hdk),
        prefixAt_full (unitDisp lam.length) k
          (by rw [length_unitDisp]; exact hdk),
        sumExpo hp]
      exact Nat.le_refl _
  have hchiR : ∀ k,
      prefixAt k chi ≤ prefixAt k (rowList lam) := by
    intro k
    have h := domGo_prefix 0 chi (rowList lam) hdomchi k
    rw [Nat.zero_add] at h
    exact h
  have hpre : ∀ k,
      prefixAt k mu ≤ 0 + prefixAt k (rowList lam) := by
    intro k
    rw [Nat.zero_add]
    have hA : prefixAt k mu + prefixAt k (unitDisp lam.length)
        = prefixAt k chi
          + prefixAt k (expo (unitDisp lam.length) p) :=
      (hpre2 k).symm.trans (hpre1 k)
    have hB : prefixAt k chi
        + prefixAt k (expo (unitDisp lam.length) p)
      ≤ prefixAt k (rowList lam)
        + prefixAt k (unitDisp lam.length) :=
      Nat.add_le_add (hchiR k) (hcap k)
    rw [← hA] at hB
    have hD : prefixAt k (unitDisp lam.length) + prefixAt k mu
        ≤ prefixAt k (unitDisp lam.length)
          + prefixAt k (rowList lam) := by
      rw [Nat.add_comm (prefixAt k (unitDisp lam.length))
          (prefixAt k mu),
        Nat.add_comm (prefixAt k (unitDisp lam.length))
          (prefixAt k (rowList lam))]
      exact hB
    exact leCancelL _ hD
  have hsumChi : sumNat chi = sumNat (rowList lam) := by
    have h := domGo_sum 0 chi (rowList lam) hdomchi
    rw [Nat.zero_add, prefixAt_full chi _ (Nat.le_refl _),
      prefixAt_full (rowList lam) _ (Nat.le_refl _)] at h
    exact h
  have htot : prefixAt mu.length mu
      = 0 + prefixAt (rowList lam).length (rowList lam) := by
    rw [Nat.zero_add, prefixAt_full mu _ (Nat.le_refl _),
      prefixAt_full (rowList lam) _ (Nat.le_refl _)]
    have h1 := hpre1 y.length
    have h2 := hpre2 y.length
    rw [prefixAt_full y _ (Nat.le_refl _),
      prefixAt_full chi y.length (Nat.le_of_eq hcl),
      prefixAt_full (expo (unitDisp lam.length) p) y.length
        (Nat.le_of_eq hel)] at h1
    rw [prefixAt_full y _ (Nat.le_refl _),
      prefixAt_full mu y.length (Nat.le_of_eq hml),
      prefixAt_full (unitDisp lam.length) y.length
        (Nat.le_of_eq hul)] at h2
    have h3 : sumNat mu + sumNat (unitDisp lam.length)
        = sumNat (rowList lam)
          + sumNat (unitDisp lam.length) := by
      rw [h2.symm.trans h1, hsumChi, sumExpo hp]
    have h4 : sumNat (unitDisp lam.length) + sumNat mu
        = sumNat (unitDisp lam.length)
          + sumNat (rowList lam) := by
      rw [Nat.add_comm (sumNat (unitDisp lam.length))
          (sumNat mu),
        Nat.add_comm (sumNat (unitDisp lam.length))
          (sumNat (rowList lam))]
      exact h3
    exact addCancelL _ h4
  exact domGo_ofPrefix 0 mu (rowList lam)
    (by rw [hml.trans hy, length_rowList]) hpre htot

/-- The identity's read at a strictly descending key
(`thm:weylchar`'s conclusion at the orbit's representative): the
display by the top coefficient against the display's own graded
read, and off the display the eigen-read's crossed cancellation
at separated squares with the per-permutation refusal through the
dominance separation at equal ones. -/
private theorem identity_sorted (mult : List Nat → Nat)
    (lam : Shape) (hrec : recReadE lam mult)
    (hsym : symReadE lam.length mult)
    (hsupp : supportReadE lam mult) (htop : topReadE lam mult)
    (y : List Nat) (hy : y.length = lam.length)
    (hdesc : ∀ i, i + 1 < y.length →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i) :
    identityAt mult lam y := by
  have hdescd : ∀ i, i + 1 < lam.length →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i :=
    fun i hi => hdesc i (by rw [hy]; exact hi)
  by_cases hyd : y = display lam
  · show prodCount mult lam.length y false
        + sideCount lam.length (display lam) y true
      = prodCount mult lam.length y true
        + sideCount lam.length (display lam) y false
    obtain ⟨hP0, hP1⟩ := prodCount_top lam mult hsupp htop
    obtain ⟨hS0, hS1⟩ := sideCount_desc_self
      (length_display lam) (places.display_desc lam)
    rw [hyd, hP0, hP1, hS0, hS1]
  · show prodCount mult lam.length y false
        + sideCount lam.length (display lam) y true
      = prodCount mult lam.length y true
        + sideCount lam.length (display lam) y false
    rw [sideCount_desc_ne (length_display lam) hy
        (places.display_desc lam) hdescd hyd true,
      sideCount_desc_ne (length_display lam) hy
        (places.display_desc lam) hdescd hyd false]
    have hPP : prodCount mult lam.length y false
        = prodCount mult lam.length y true := by
      by_cases hq : stdSq y = stdSq (display lam)
      · have hz : ∀ t : Bool,
            prodCount mult lam.length y t = 0 := by
          intro t
          show ground.famFold Nat.add 0
            (fun p => if parity p = t then
                multAtGap mult y (expo (unitDisp lam.length) p)
              else 0)
            (perms lam.length) = 0
          refine (ground.famFold_congr_members Nat.add 0 _
            (fun _ => (0 : Nat)) (perms lam.length)
            (fun p hp => ?_)).trans
            (famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
              (perms lam.length))
          by_cases hpar : parity p = t
          · rw [if_pos hpar]
            cases ht : tieGap y (expo (unitDisp lam.length) p)
              with
            | none =>
              show (match
                  tieGap y (expo (unitDisp lam.length) p) with
                | some nu => mult nu
                | none => 0) = 0
              rw [ht]
            | some chi =>
              show (match
                  tieGap y (expo (unitDisp lam.length) p) with
                | some nu => mult nu
                | none => 0) = 0
              rw [ht]
              cases hm : mult chi with
              | zero => exact hm
              | succ m' =>
                have hchi : 0 < mult chi := by
                  rw [hm]
                  exact Nat.succ_pos m'
                obtain ⟨hcl, hel, hent⟩ := tieGap_reads y
                  (expo (unitDisp lam.length) p) chi ht
                have hpos : ∀ i, i < lam.length →
                    0 < ground.getAt 0 y i := by
                  intro i hi
                  have hiy : i < y.length := by
                    rw [hy]
                    exact hi
                  refine Nat.lt_of_lt_of_le
                    (expoEntry hp hi).1 ?_
                  rw [← hent i hiy]
                  exact Nat.le_add_left _ _
                have hge := unitLe_of_desc hy hdescd hpos
                have hgeY : ∀ i, i < y.length →
                    ground.getAt 0 (unitDisp lam.length) i
                      ≤ ground.getAt 0 y i :=
                  fun i hi => hge i (by rw [← hy]; exact hi)
                have htu := tieGap_of_le y
                  (unitDisp lam.length)
                  (by rw [length_unitDisp, hy]) hgeY
                obtain ⟨hml, _, _⟩ := tieGap_reads y
                  (unitDisp lam.length) _ htu
                have hmud := mu_desc hy hdescd htu
                have hdom := mu_dom mult hsupp hy hp ht hchi
                  htu
                have hnemu : ¬ List.zipWith (fun a b => a - b)
                    y (unitDisp lam.length) = rowList lam :=
                  fun hmu => hyd (display_of_muRow hy htu hmu)
                have hsort : ∀ i, i + 1
                    < (List.zipWith (fun a b => a - b) y
                        (unitDisp lam.length)).length →
                    ground.getAt 0 (List.zipWith
                        (fun a b => a - b) y
                        (unitDisp lam.length)) (i + 1)
                      ≤ ground.getAt 0 (List.zipWith
                        (fun a b => a - b) y
                        (unitDisp lam.length)) i :=
                  fun i hi => hmud i
                    (by rw [← hy, ← hml]; exact hi)
                have hlt := sq_lt_of_dom lam _ hsort hdom
                  hnemu
                rw [← tieGap_zip y (unitDisp lam.length) _
                    htu, hq] at hlt
                exact absurd hlt (Nat.lt_irrefl _)
          · rw [if_neg hpar]
        rw [hz false, hz true]
      · exact crossCancel hq (eigenRead mult lam hrec hsym y)
    rw [hPP]

/-- The walk to the sorted representative (`thm:weylchar`'s
conclusion, the exchanges' own walk): a repeated adjacent pair
reads the repeat's transposition, an adjacent ascent's exchange
drops the ascent count by one with the transport back through the
transposition's involution, and the descent's end reads the
sorted case. -/
private theorem identity_walk (mult : List Nat → Nat)
    (lam : Shape) (hrec : recReadE lam mult)
    (hsym : symReadE lam.length mult)
    (hsupp : supportReadE lam mult) (htop : topReadE lam mult) :
    ∀ (n : Nat) (y : List Nat), y.length = lam.length →
      ascCount y ≤ n → identityAt mult lam y
  | 0, y, hy, hinv => by
    cases hnd : firstNonDesc y with
    | none =>
      exact identity_sorted mult lam hrec hsym hsupp htop y hy
        (ndGo_none 0 y hnd)
    | some i =>
      have hnd' : ndGo 0 y = some (0 + i) := by
        rw [Nat.zero_add]
        exact hnd
      obtain ⟨hi1, hle⟩ := ndGo_some 0 y i hnd'
      have hi1d : i + 1 < lam.length := by
        rw [← hy]
        exact hi1
      by_cases heq : ground.getAt 0 y i
          = ground.getAt 0 y (i + 1)
      · exact identityAt_repeatKey mult lam hsym
          (Nat.lt_succ_self i) hi1d y hy heq
      · exact absurd
          (Nat.lt_of_lt_of_le
            (ascCount_pos_of_asc y i hi1 (Nat.lt_of_le_of_ne hle heq))
            hinv)
          (Nat.lt_irrefl 0)
  | n' + 1, y, hy, hinv => by
    cases hnd : firstNonDesc y with
    | none =>
      exact identity_sorted mult lam hrec hsym hsupp htop y hy
        (ndGo_none 0 y hnd)
    | some i =>
      have hnd' : ndGo 0 y = some (0 + i) := by
        rw [Nat.zero_add]
        exact hnd
      obtain ⟨hi1, hle⟩ := ndGo_some 0 y i hnd'
      have hi1d : i + 1 < lam.length := by
        rw [← hy]
        exact hi1
      by_cases heq : ground.getAt 0 y i
          = ground.getAt 0 y (i + 1)
      · exact identityAt_repeatKey mult lam hsym
          (Nat.lt_succ_self i) hi1d y hy heq
      · have hasc : ground.getAt 0 y i
            < ground.getAt 0 y (i + 1) := Nat.lt_of_le_of_ne hle heq
        have hy' : (places.swapPair i (i + 1) y).length
            = lam.length := by
          rw [places.length_swapPair i (i + 1) y]
          exact hy
        have hinv' : ascCount (places.swapPair i (i + 1) y)
            ≤ n' := by
          refine Nat.le_of_succ_le_succ ?_
          show ascCount (places.swapPair i (i + 1) y) + 1
            ≤ n' + 1
          rw [ascCount_swapAdj y i hi1 hasc]
          exact hinv
        have h2 := identityAt_swapKey mult lam hsym
          (Nat.lt_succ_self i) hi1d
          (places.swapPair i (i + 1) y) hy'
          (identity_walk mult lam hrec hsym hsupp htop n'
            (places.swapPair i (i + 1) y) hy' hinv')
        rw [places.swapPair_swapPair i (i + 1) y] at h2
        exact h2

/-! The occupancy family's reads at the displays: the family's
clauses carry to every content, an unoccupied content's count the
fold's unit — the pair move's exact inverse putting a moved
content's source inside the recursion's key family, so a key off
the family reads both sides at the count's unit. -/

private theorem memApp {α : Type} {x : α} :
    ∀ {u : List α}, x ∈ u → ∀ v : List α, x ∈ u ++ v
  | _ :: t, .head _, v => List.Mem.head (t ++ v)
  | b :: _, .tail _ h, v => List.Mem.tail b (memApp h v)

private theorem memAppR {α : Type} {x : α} {v : List α}
    (h : x ∈ v) : ∀ u : List α, x ∈ u ++ v
  | [] => h
  | a :: t => List.Mem.tail a (memAppR h t)

private theorem memFlat {α β : Type} (f : α → List β) {x : β} :
    ∀ {l : List α} {a : α}, a ∈ l → x ∈ f a → x ∈ l.flatMap f
  | _ :: t, _, .head _, hx => memApp hx (List.flatMap f t)
  | b :: _, _, .tail _ h, hx => memAppR (memFlat f h hx) (f b)

private theorem memEq {α : Type} {x y : α} {l : List α}
    (h : x = y) (hx : x ∈ l) : y ∈ l := h ▸ hx

/-- The pair move's exact inverse: the reversed move at the same
shift returns the content, the raised letter lowered back and the
lowered letter's shift restored within its count. -/
theorem moveBy_moveBy {a b : Nat} (hne : a ≠ b) (l : Nat)
    (nu : List Nat) (ha : a < nu.length) (hb : b < nu.length)
    (hl : l ≤ ground.getAt 0 nu b) :
    moveBy b a l (moveBy a b l nu) = nu := by
  have hma : a < (moveBy a b l nu).length := by
    rw [length_moveBy]
    exact ha
  have hmb : b < (moveBy a b l nu).length := by
    rw [length_moveBy]
    exact hb
  have hen : b ≠ a := fun he => hne he.symm
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [length_moveBy, length_moveBy]
  · intro t _
    by_cases hta : t = a
    · rw [hta, getAt_moveBy_snd b hen l _ hma,
        getAt_moveBy_fst hne l nu ha, addSubSelfR]
    · by_cases htb : t = b
      · rw [htb, getAt_moveBy_fst hen l _ hmb,
          getAt_moveBy_snd a hne l nu hb, subAdd hl]
      · rw [getAt_moveBy_ne b a l _ htb hta,
          getAt_moveBy_ne a b l nu hta htb]

/-- A moved content off the occupancy family: at a key outside the
recursion's family every pair move's target is unoccupied, the
move's source the key itself through the exact inverse. -/
private theorem count_key_zero {d : Nat} {L : List (List Nat)}
    {nu : List Nat}
    (hz : ground.countOf nu (recKeys d L) = 0)
    {a b : Nat} (hab : a < b) (hbn : b < nu.length)
    (hnd : nu.length = d) {l : Nat}
    (hl : l < ground.getAt 0 nu b) :
    ground.countOf (moveBy a b (l + 1) nu) L = 0 := by
  match Nat.eq_zero_or_pos
      (ground.countOf (moveBy a b (l + 1) nu) L) with
  | .inl h0 => exact h0
  | .inr hp =>
    have hne : a ≠ b := Nat.ne_of_lt hab
    have han : a < nu.length := Nat.lt_trans hab hbn
    have hmu : moveBy a b (l + 1) nu ∈ L :=
      ground.mem_of_countOf_pos _ L hp
    have hpair : (a, b) ∈ pairsOf d :=
      ground.mem_of_countOf_pos _ _
        (places.pairs_complete d hab (hnd ▸ hbn))
    have hlt : l < ground.getAt 0 (moveBy a b (l + 1) nu) a := by
      rw [getAt_moveBy_fst hne (l + 1) nu han]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self l)
        (Nat.le_add_left (l + 1) _)
    have heq : moveBy b a (l + 1) (moveBy a b (l + 1) nu) = nu :=
      moveBy_moveBy hne (l + 1) nu han hbn hl
    have hin : moveBy b a (l + 1) (moveBy a b (l + 1) nu)
        ∈ ((List.range
              (ground.getAt 0 (moveBy a b (l + 1) nu) a)).map
            (fun k => k + 1)).map
          (fun k => moveBy b a k (moveBy a b (l + 1) nu)) :=
      ground.mem_map_to _ (ground.mem_map_to _ (ground.memRange hlt))
    have harm : nu ∈ (pairsOf d).flatMap (fun ab =>
        ((List.range
            (ground.getAt 0 (moveBy a b (l + 1) nu) ab.1)).map
          (fun k => k + 1)).map
          (fun k => moveBy ab.2 ab.1 k (moveBy a b (l + 1) nu))) := by
      exact memFlat _ hpair (memEq heq hin)
    have hnu : nu ∈ recKeys d L := by
      show nu ∈ L ++ L.flatMap (fun mu =>
        (pairsOf d).flatMap (fun ab =>
          ((List.range (ground.getAt 0 mu ab.1)).map
            (fun l => l + 1)).map
            (fun l => moveBy ab.2 ab.1 l mu)))
      exact memAppR (memFlat _ hmu harm) L
    have hc := ground.countOf_pos_of_mem hnu
    rw [hz] at hc
    exact absurd hc (Nat.lt_irrefl 0)

/-- The second-letter fold at an unoccupied pair's moves: every
shift's target off the family, the fold the count's unit. -/
private theorem gSnd_zero {L : List (List Nat)} {nu : List Nat}
    {a b : Nat}
    (h : ∀ l, l < ground.getAt 0 nu b →
      ground.countOf (moveBy a b (l + 1) nu) L = 0) :
    gSnd (fun chi => ground.countOf chi L) nu a b = 0 := by
  show ground.famFold Nat.add 0
      (fun l => ground.getAt 0 nu b
        * ground.countOf (moveBy a b l nu) L)
      ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1))
    = 0
  rw [ground.famFold_map]
  refine (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0) _
    (fun l hl => ?_)).trans (ground.famFold_zero _ (fun _ => rfl) _)
  rw [h l (ground.ltOfMem hl), Nat.mul_zero]

/-- The first-letter fold at an unoccupied pair's moves, the
shifted weight against the absent multiplicity. -/
private theorem gFst_zero {L : List (List Nat)} {nu : List Nat}
    {a b : Nat}
    (h : ∀ l, l < ground.getAt 0 nu b →
      ground.countOf (moveBy a b (l + 1) nu) L = 0) :
    gFst (fun chi => ground.countOf chi L) nu a b = 0 := by
  show ground.famFold Nat.add 0
      (fun l => (ground.getAt 0 nu a + 2 * l)
        * ground.countOf (moveBy a b l nu) L)
      ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1))
    = 0
  rw [ground.famFold_map]
  refine (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0) _
    (fun l hl => ?_)).trans (ground.famFold_zero _ (fun _ => rfl) _)
  rw [h l (ground.ltOfMem hl), Nat.mul_zero]

/-- The moved folds at a key off the recursion's family: the pair
fold at the letters' double fold, every ordered pair's moves
unoccupied. -/
private theorem movedSnd_zero {L : List (List Nat)}
    {nu : List Nat}
    (h : ∀ a b, a < b → b < nu.length → ∀ l,
      l < ground.getAt 0 nu b →
      ground.countOf (moveBy a b (l + 1) nu) L = 0) :
    movedSnd (fun chi => ground.countOf chi L) nu = 0 := by
  show ground.famFold Nat.add 0
      (fun ab =>
        gSnd (fun chi => ground.countOf chi L) nu ab.1 ab.2)
      (pairsOf nu.length)
    = 0
  rw [places.pairsFold]
  refine (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0) _
    (fun a _ => ?_)).trans (ground.famFold_zero _ (fun _ => rfl) _)
  refine (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0) _
    (fun b hb => ?_)).trans (ground.famFold_zero _ (fun _ => rfl) _)
  by_cases hab : a < b
  · rw [if_pos hab]
    exact gSnd_zero (h a b hab (ground.ltOfMem hb))
  · rw [if_neg hab]

/-- The shifted-weight fold at a key off the recursion's family. -/
private theorem movedFst_zero {L : List (List Nat)}
    {nu : List Nat}
    (h : ∀ a b, a < b → b < nu.length → ∀ l,
      l < ground.getAt 0 nu b →
      ground.countOf (moveBy a b (l + 1) nu) L = 0) :
    movedFst (fun chi => ground.countOf chi L) nu = 0 := by
  show ground.famFold Nat.add 0
      (fun ab =>
        gFst (fun chi => ground.countOf chi L) nu ab.1 ab.2)
      (pairsOf nu.length)
    = 0
  rw [places.pairsFold]
  refine (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0) _
    (fun a _ => ?_)).trans (ground.famFold_zero _ (fun _ => rfl) _)
  refine (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0) _
    (fun b hb => ?_)).trans (ground.famFold_zero _ (fun _ => rfl) _)
  by_cases hab : a < b
  · rw [if_pos hab]
    exact gFst_zero (h a b hab (ground.ltOfMem hb))
  · rw [if_neg hab]

/-- The symmetry at every content: a member reads the family's
clause, a member's transposed source reads it back through the
transposition's involution, and off the family both counts are the
fold's unit. -/
private theorem symRead_all (d : Nat) (L : List (List Nat))
    (h : symRead d L) :
    symReadE d (fun chi => ground.countOf chi L) := by
  intro i j nu hij hjd _
  show ground.countOf (swapPair i j nu) L = ground.countOf nu L
  have hid : i < d := Nat.lt_trans hij hjd
  match Nat.eq_zero_or_pos (ground.countOf nu L) with
  | .inr hp =>
    exact h nu (ground.mem_of_countOf_pos nu L hp) i hid j hjd
  | .inl h0 =>
    match Nat.eq_zero_or_pos
        (ground.countOf (swapPair i j nu) L) with
    | .inl h1 => rw [h0, h1]
    | .inr hp =>
      have hs := h (swapPair i j nu)
        (ground.mem_of_countOf_pos _ L hp) i hid j hjd
      rw [swapPair_swapPair] at hs
      exact hs.symm

/-- The support at every content: an occupied content is a
member. -/
private theorem supportRead_all (lam : Shape) (L : List (List Nat))
    (h : supportRead lam L) :
    supportReadE lam (fun chi => ground.countOf chi L) :=
  fun nu _ hp => h nu (ground.mem_of_countOf_pos nu L hp)

/-- The recursion at every content: a key of the family reads the
family's clause, and off it the key's count and both moved folds
are the fold's unit. -/
private theorem recRead_all (lam : Shape) (L : List (List Nat))
    (h : recRead lam L) :
    recReadE lam (fun chi => ground.countOf chi L) := by
  intro nu hnu
  match Nat.eq_zero_or_pos
      (ground.countOf nu (recKeys lam.length L)) with
  | .inr hp =>
    exact h nu (ground.mem_of_countOf_pos nu _ hp) hnu
  | .inl hz =>
    show stdSq (display lam) * ground.countOf nu L
        + 2 * movedSnd (fun chi => ground.countOf chi L) nu
      = stdSq (List.zipWith (fun a b => a + b) nu
            (unitDisp lam.length)) * ground.countOf nu L
        + 2 * movedFst (fun chi => ground.countOf chi L) nu
    have hkey : ∀ a b, a < b → b < nu.length → ∀ l,
        l < ground.getAt 0 nu b →
        ground.countOf (moveBy a b (l + 1) nu) L = 0 :=
      fun a b hab hbn l hl => count_key_zero hz hab hbn hnu hl
    rw [movedSnd_zero hkey, movedFst_zero hkey,
      (ground.addZeroN
        ((ground.countOf_append _ _ _).symm.trans hz)).1]
    rfl

/-- The identity's read at every key (`thm:weylchar`'s
conclusion): under the four hypothesis displays at the occupancy
family the product's graded coefficient reads the shifted
alternant's at every key — a repeated key at the repeat's
transposition, a distinct key transported to its sorted
representative along the ascent walk, the sorted representative at
the top by the support and top clauses and off it by the
eigen-read's crossed cancellation at separated squares or the
per-permutation refusal through the dominance separation at equal
ones, and an off-length key reading the count's unit on both
sides. -/
theorem identityRead (lam : Shape) (L : List (List Nat))
    (hrec : recRead lam L) (hsym : symRead lam.length L)
    (hsupp : supportRead lam L) (htop : topRead lam L)
    (y : List Nat) :
    identityAt (fun chi => countOf chi L) lam y := by
  by_cases hy : y.length = lam.length
  · exact identity_walk (fun chi => countOf chi L) lam
      (recRead_all lam L hrec) (symRead_all lam.length L hsym)
      (supportRead_all lam L hsupp) htop
      (ascCount y) y hy (Nat.le_refl _)
  · show prodCount (fun chi => countOf chi L) lam.length y false
        + sideCount lam.length (display lam) y true
      = prodCount (fun chi => countOf chi L) lam.length y true
        + sideCount lam.length (display lam) y false
    rw [prodCount_offLen (fun chi => countOf chi L) hy false,
      prodCount_offLen (fun chi => countOf chi L) hy true,
      sideCount_offLen (display lam) hy true,
      sideCount_offLen (display lam) hy false]

end weylchar
