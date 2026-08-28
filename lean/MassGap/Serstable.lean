import MassGap.Casfloor
import MassGap.Row
/-!
`lem:serstable`(i) — the leading families' members in the classical
series.  A leading family is a coordinate word `W = [W_1, …, W_a]`,
weakly descending, and its member at a cleared rank `ℓ ≥ a + 2` is
the content whose sorted coordinates are `(W, 0, …, 0)`.  In the
coroot presentation the member is the list of consecutive gaps of
the padded word (`member`), series-uniform at the cleared rank, and
its simple-fold display `e μ = Σ_k b_k α_k` carries the word's
leading sums at key one (`foldB`), their doubles with the word's
total at the last key at key two (`foldC`), or with the total at
the last two keys (`foldD`); the coroot identities
`Σ_k b_k α_k(α_j^∨) = e μ(α_j^∨)` hold at every simple key
(`corootRead_B`, `corootRead_C`, `corootRead_D`), the reads at the
interior keys the leading sums' telescoping against the word's
gaps and the reads at the last keys vacant beyond the word.  The
Casimir is the displayed value `ĉ₂(μ) = [casNum : casDen]`: the
numerator is the word's square fold with the word against the root
fold's key reads (`casNumB`, `casNumC`, `casNumD`, the key reads
`2(ℓ − i − 1) + 1`, `2(ℓ − i)` and `2(ℓ − i − 1)`), the denominator
the adjoint Casimir's clearing (`casDenB`, `casDenC`, `casDenD`),
and the evaluations are `casRead_B`, `casRead_C`, `casRead_D`.  The
root fold's key reads are closed forms in the rank —
`(k+1)(2ℓ − k − 1)` at `B`, `(k+1)(2ℓ − k)` at `C` and
`(k+1)(2ℓ − k − 2)` at `D` — the positive families' columns counted
over the coordinate pairs; the member's coroot list vanishes beyond
the word, so the Casimir's fold truncates to the word's own keys,
where the leading sums and the root fold's reads telescope against
the gaps by the Abel step.  The dimension clause closes the same
member at `cor:weyldim`'s gap product: the concrete gap at a
positive fold `f` against a coroot list `v` is
`Σ_k f_k · lenNums_k · v_k` (`gapAt`, the halved products cleared
at `2 lenDen`), the raised member is the padded word's gaps each
carrying one (`memberRho`), and the cross-multiplied identity
`dimNum · G(ρ) = dimDen · G(member + ρ)` holds at every series
(`dimGap_B`, `dimGap_C`, `dimGap_D`) — the numerators and
denominators the word-against-word difference and sum factors with
the short or long factors and the two word-against-tail
telescopes.  The proof is one master read per series: the gap
product at the raised member is the numerator against a rank-only
tail, the tail-against-tail factors reading the same on both
sides, so the denominator is the numerator's own value at the
vacant word of the same length and the identity is the two
instances' exchange.  The form's own read closes the gap
(`gapAt_dotB`): the pairing of a positive member's coroot vector
against a coroot list is the concrete gap at the fundamentals'
scale, the Cartan-transposed fold associated across the Gram's
defining read to the diagonal at `scale · lenNums`.

`lem:serstable`(ii) closes the adjoint rows at the same members.
The row runs at `cor:steinberg`'s member ties over the member's
Weyl list at the `θ` contents; the member enters as the key
`memberV` and the shifted key is its `ρ`-raise
`pnorm (vecAdd (memberV W l) (rhoV t))`, the padded word's gaps each
carrying one, and the row's value is the `letterFold` — the
identity's read at the target's own content joined against one
signed read per simple letter at the raised content, the raise the
key's coroot multiple of the letter's own root.  The alignment's
fold runs at an abstract member vector (`letterFoldAt`) with the
leading member its first instance: the abstract member's length, its
shifted key's coordinate read against a raised member vector and
that vector's positivity are the member's whole entry into the
tier.  Beside it stands the fold's value function `letterFoldVal`,
the same fold at `row.thetaCount`: under the θ content list's
characterization the two are one value (`letterFoldAt_val`), so the
fold reads the table, the shifted keys and the moved content
alone.  The two convolution counts read it at every dominant
target (`rowValues_B`, `rowValues_C`, `rowValues_D`): a tie's
element sits at the shifted key's withdrawal of a natural simple
fold, the kept square reads that fold against its doubled pairing
with the key, the tie collects the square against the target's own
shifted key, and the contents' cap with the target's dominance
prices the fold's length-weighted height at two — the residue walk
then closing at the identity and the simple letters, a two-keyed
fold carrying two coroot pairs at two on distinct keys and refused
at the simple's own row.  The diagonal's evaluation is the
vacuum's (`letterFold_vac_B`, `letterFold_vac_C`,
`letterFold_vac_D`): at the vacant target the fold reads the
member's vacant-key count, the word's own occupied coroot support
read back.  The diagonal display closes the tower read at the
members themselves (`diagRead_B`, `diagRead_C`, `diagRead_D`): at
the member's own display the even count is the vacuum content's
multiplicity, the coordinate count, and the odd count the letter
fold there, so the display's cancellation reads the member's
channel count against the word's vacant-key count, the two joining
at the rank — the tex's "the diagonal is the occupied support, the
word's distinct-value count", the vacant word the same statement at
the tower's foot.  The off-diagonal evaluations close the row's
enumeration.  An occupied target off the vacant content counts at
most once (`rowOffOne_B`, `rowOffOne_C`, `rowOffOne_D`): the
family holds the content once, so the member display's count joins
the letter fold to one.  And the target is a leading word at the
reach grown by at most two (`rowConfined_B`, `rowConfined_C`,
`rowConfined_D`): the coroot presentation clears the grown reach,
every further key reading its displayed pair at coordinates past
the reach — a coroot content's column family is vacant beyond its
window's top, and an occupied entry at or beyond the word's
two-clearance hands the window's edge a lower-side companion at a
key beyond the word, refusing the target's dominance.  At `D` the
last key alone sits off that read: its pair is the two tail
coordinates' sum, so it reads the grown reach's own coordinate,
occupied at the whole-growth target at the rank one beyond the
boundary and vacant at every rank clearing the reach by four, the
theorem's last-key clause.

The polynomial tier states clause (i) as its own reads: one
polynomial pair per family in the rank.  The Casimir's numerator is
`casPolyB`, `casPolyC`, `casPolyD` — the word's square fold cleared
of the key-weighted fold at the constant, the word's doubled total
at the rank's key — and `casPolyB_eval`, `casPolyC_eval`,
`casPolyD_eval` state the agreement with the displayed numerator at
every rank at or beyond the word's length, where the root fold's key
reads join their key-weighted partners at the doubled rank.  The
dimension's pair is `dimPolyNumX` against `dimPolyDenX`: the
word-against-word difference factors enter as the rank-free
constant, the word sums and the short or long factors as single
linear factors, and the two word-against-tail telescopes as one
linear factor per box of the word, the tail's own key count carried
on the opposite member; `dimPolyB_eval`, `dimPolyC_eval`,
`dimPolyD_eval` state the cross-multiplied agreement with the
displayed pair `dimNumX`, `dimDenX` at every rank clearing the
word's reach, the shared factorial representatives absorbed by the
cross multiplication.  The bridge is the rising products'
rectangle — `rise c (g + w) = rise c g · rise (c+g) w
= rise c w · rise (c+w) g`, the window of the word's boxes over the
tail's keys read either way round — once at each telescope.  Clause
(iii) reads the rank as a cell coordinate through these pairs:
`lem:genericlift`'s settled-side theorems fix each divisor's side
beyond its own radius, so the divisors' rank roots read against the
compared families' reach clearances, one symbolic count at every
cleared rank with the below-clearance ranks read directly.  The
`B` column kit stands public at that read: the Cartan entries
`cartB` with their square `cartB_eq`, the window and sum entries
`fDiff`, `fSumB` at their value reads, the neighbour fold `nbB`,
the column's count-pair read `colB` and the range-presented fold's
`colValue`, the positive list's case read `foldsB_cases` — a fold
at a key is one of the three families' range maps, reading the
column at every key — and the interior magnitude-two
characterization: at a key with two keys above it inside the rank
the doubled entry exceeds its two neighbours' sum by two exactly at
the narrow window `fDiff (m + 1) (m + 2)` (`fDiff_two`,
`fSumB_two`, `fShort_two`) and never falls two below it
(`colB_notNegTwo`), the narrow window's own column vacant off its
three keys (`fDiff_narrow_off`).  Off the four boundary keys the
window and sum columns are vacant outright (`fDiff_off`,
`fSumB_off`), a positive fold's normalized coroot vector reads its
column values entrywise (`posCorootV_entry`), and the run letters
vanish: at an interior letter with the moved content vacant on its
three keys and occupied at a witness off them, the raised content
reads the vacant θ count (`runVanishB`), clause (iii)'s symbolic
count at the alignment's interior.  The `C` column kit stands
public at the same read — the Cartan entries `cartC` with their
square `cartC_eq` and the long last edge's own reads (`cartCd`,
`cartCdn2`, `cartCdn1`, `cartCup`, `cartCoff`), the sum and long
entries `fSumC`, `fLong` at their value reads, the neighbour fold
`nbC`, the column's count-pair read `colC`, the positive list's
case read `foldsC_cases` at the rank's successor presentation, the
interior magnitude-two characterizations (`fSumC_two_refuse`,
`fSumC_negTwo_refuse`, `fDiff_negTwo_refuse`, `fLong_two_head`,
`fLong_negTwo`), the vacant columns off the narrow window's three
keys, the long family's two poles and the sum family's four
boundary keys (`fDiffC_narrow_off`, `fLong_off`, `fSumC_off`) and
the run letters' vanishing (`runVanishC`) — the long family the
one column reading plus two at its head and minus two one key
below it, a dipole at two poles the witness kills at either sign —
with the columns' magnitude cap (`colC_magLe`, every column within
two of its neighbour fold) and the coroot vectors' entrywise column
reads (`posCorootV_entryC`).  The `D` column kit stands public at
the fork geometry: the Cartan entries `cartD` with their square
`cartD_eq` and the fork's own reads (`cartDd`, `cartDup`,
`cartDdn`, `cartDforkT`, `cartDoff`), the neighbour
fold `nbD` at its four arms (`nbD_eq`) — the last tip reading the
key two below it (`pv2D`), the tip beside it and the chain the key
one below (`pvD`), and the fork key its three joined keys — and
the sum family's two classes at the last-coordinate branch: the
generic member `fSumD` one on the window, two on the run to the
fork and one at each tip (`fSumD_eq`), the last-coordinate member
`fSumDt` one on the window through the fork key, vacant at the sub
tip and one at the last tip, each entry read per arm
(`fSumD_lo`, `fSumD_mid`, `fSumD_two`, `fSumD_end`, `fSumDt_gap`,
`fSumDt_top`) with the caps `fSumD_le2` and `fSumDt_le1`.  The
positive list's case read `foldsD_cases` at the rank's second
successor presentation names the three families; at an interior
key neither sum column sits two above its neighbours' sum, nor
two below it (`fSumD_two_refuse`, `fSumD_negTwo_refuse`,
`fSumDt_two_refuse`, `fSumDt_negTwo_refuse`), so an interior
plus-two read pins the narrow window (`narrowOfTwoD`) and a
minus-two read refuses outright (`colD_notNegTwo`), the narrow window's
own column is vacant off its three keys (`fDiffD_narrow_off`),
every column sits within two of its neighbour fold (`colD_magLe`),
a positive fold's normalized coroot vector and its balance partner
read the column values entrywise (`posCorootV_entryD`,
`negCorootV_entryD`), and the run letters vanish: at a chain
letter with the moved content vacant at the letter's own key and
occupied at a witness off its three keys, the raised content reads
the vacant θ count (`runVanishD`).
-/

namespace serstable
open ground gentable

/-! ## The leading family's member and its simple folds -/

/-- The leading family's member at the cleared rank, the coroot
presentation: the padded word's consecutive gaps. -/
def member (W : List Nat) (l : Nat) : List Nat :=
  (List.range l).map (fun i =>
    ground.getAt 0 W i - ground.getAt 0 W (i + 1))

/-- The `B` simple fold: the word's leading sums. -/
def foldB (W : List Nat) (l : Nat) : List Nat :=
  (List.range l).map (fun k => ground.sumNat (List.take (k + 1) W))

/-- The `C` simple fold: the doubled leading sums with the word's
total at the last key. -/
def foldC (W : List Nat) (l : Nat) : List Nat :=
  (List.range l).map (fun k =>
    if l ≤ k + 1 then ground.sumNat W
    else 2 * ground.sumNat (List.take (k + 1) W))

/-- The `D` simple fold: the doubled leading sums with the word's
total at the last two keys. -/
def foldD (W : List Nat) (l : Nat) : List Nat :=
  (List.range l).map (fun k =>
    if l ≤ k + 2 then ground.sumNat W
    else 2 * ground.sumNat (List.take (k + 1) W))

/-- The `B` member's cleared-fold datum at key one. -/
def endB (W : List Nat) (l : Nat) : casfloor.EndFold :=
  ⟨foldB W l, 1, member W l⟩
/-- The `C` member's cleared-fold datum at key two. -/
def endC (W : List Nat) (l : Nat) : casfloor.EndFold :=
  ⟨foldC W l, 2, member W l⟩
/-- The `D` member's cleared-fold datum at key two. -/
def endD (W : List Nat) (l : Nat) : casfloor.EndFold :=
  ⟨foldD W l, 2, member W l⟩

/-- The `B` Casimir's numerator: the word's square fold with the
word against the root fold's key reads. -/
def casNumB (W : List Nat) (l : Nat) : Nat :=
  c2hat.sumSq W + ground.dotNat W
    ((List.range W.length).map (fun i => 2 * (l - (i + 1)) + 1))
/-- The `C` Casimir's numerator. -/
def casNumC (W : List Nat) (l : Nat) : Nat :=
  c2hat.sumSq W + ground.dotNat W
    ((List.range W.length).map (fun i => 2 * (l - i)))
/-- The `D` Casimir's numerator. -/
def casNumD (W : List Nat) (l : Nat) : Nat :=
  c2hat.sumSq W + ground.dotNat W
    ((List.range W.length).map (fun i => 2 * (l - (i + 1))))

/-- The `B` Casimir's denominator, the adjoint Casimir's
clearing. -/
def casDenB (l : Nat) : Nat := 2 * (2 * l - 1)
/-- The `C` Casimir's denominator. -/
def casDenC (l : Nat) : Nat := 4 * (l + 1)
/-- The `D` Casimir's denominator. -/
def casDenD (l : Nat) : Nat := 4 * (l - 1)

/-! ## The column kit: a fold against a Cartan column -/

private theorem bsumCongr (f g : Nat → BPair)
    (h : ∀ x, (f x).oneValue (g x)) : ∀ L : List Nat,
    (ground.famFold BPair.add BPair.unit f L).oneValue
      (ground.famFold BPair.add BPair.unit g L)
  | [] => BPair.oneValue_refl _
  | a :: t => BPair.add_congr (h a) (bsumCongr f g h t)

/-- A count pair reads a count exactly at the cleared
difference. -/
private theorem countsRead (a b c : Nat) (h : a = c + b) :
    (BPair.ofCounts a b).oneValue (BPair.ofNat c) := by
  have key := BPair.ofCounts_add c 0 b b
  rw [Nat.zero_add b] at key
  rw [h]
  refine BPair.oneValue_trans key ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.ofCounts_unit.mpr rfl)) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.add_unit (BPair.ofNat c)

private theorem countsPos (c : Nat) :
    (BPair.ofCounts c 0).oneValue (BPair.ofNat c) :=
  BPair.add_unit (BPair.ofNat c)

private theorem countsNeg (c : Nat) :
    (BPair.ofCounts 0 c).oneValue ((BPair.ofNat c).swap) :=
  BPair.unit_add ((BPair.ofNat c).swap)

private theorem cellTwo (c : Nat) :
    (BPair.ofNat c * BPair.ofNat 2).oneValue
      (BPair.ofCounts (2 * c) 0) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofNat_mul c 2)) ?_
  rw [Nat.mul_comm c 2]
  exact BPair.oneValue_symm (countsPos (2 * c))

private theorem cellOneNeg (c : Nat) :
    (BPair.ofNat c * (BPair.ofNat 1).swap).oneValue
      (BPair.ofCounts 0 c) := by
  refine BPair.oneValue_trans
    (ground.swap_congr (BPair.mul_ofNat_one (BPair.ofNat c))) ?_
  exact BPair.oneValue_symm (countsNeg c)

private theorem cellTwoNeg (c : Nat) :
    (BPair.ofNat c * (BPair.ofNat 2).swap).oneValue
      (BPair.ofCounts 0 (2 * c)) := by
  refine BPair.oneValue_trans
    (ground.swap_congr (BPair.oneValue_symm (BPair.ofNat_mul c 2))) ?_
  rw [Nat.mul_comm c 2]
  exact BPair.oneValue_symm (countsNeg (2 * c))

private theorem cellOneNegZ (c : Nat) :
    (BPair.ofNat c * (BPair.ofNat 1).swap).oneValue
      (BPair.ofCounts 0 (0 + c)) := by
  rw [Nat.zero_add]
  exact cellOneNeg c

private theorem cellNull (c : Nat) :
    (BPair.ofNat c * BPair.unit).oneValue (BPair.ofCounts 0 0) :=
  BPair.oneValue_trans (BPair.mul_unit (BPair.ofNat c))
    (BPair.oneValue_symm BPair.ofCounts_zero)

/-- The column read at a range-presented table: the fold against a
Cartan column collects the two count families' folds. -/
private theorem colValue (t : Table) (C : Nat → Nat → BPair)
    (l j : Nat) (F P N : Nat → Nat)
    (hcart : t.cartan = ground.matOf l l (fun i j => C i j))
    (hj : j < l)
    (hcell : ∀ k, (BPair.ofNat (F k) * C k j).oneValue
      (BPair.ofCounts (P k) (N k))) :
    (corootAt t ((List.range l).map F) j).oneValue
      (BPair.ofCounts (ground.famFold Nat.add 0 P (List.range l))
        (ground.famFold Nat.add 0 N (List.range l))) := by
  have hfun : (List.range l).map (fun k => BPair.ofNat (F k)
      * getAt BPair.unit ((List.range l).map (C k)) j)
      = (List.range l).map (fun k => BPair.ofNat (F k) * C k j) :=
    ground.map_congr_all _ _ (fun k => by
      rw [ground.getAt_map_range BPair.unit (C k) l j, if_pos hj])
      (List.range l)
  show (BPair.sum (List.zipWith
    (fun c row => BPair.ofNat c * getAt BPair.unit row j)
    ((List.range l).map F) t.cartan)).oneValue _
  rw [hcart,
    show List.zipWith
          (fun c row => BPair.ofNat c * getAt BPair.unit row j)
          ((List.range l).map F) (ground.matOf l l (fun i j => C i j))
        = (List.range l).map (fun k => BPair.ofNat (F k)
            * getAt BPair.unit ((List.range l).map (C k)) j) from
      ground.zipWith_map_map
        (fun c row => BPair.ofNat c * getAt BPair.unit row j) F
        (fun i => (List.range l).map (C i)) (List.range l),
    hfun]
  refine BPair.oneValue_trans
    (BPair.sum_map (fun k => BPair.ofNat (F k) * C k j)
      (List.range l)) ?_
  refine BPair.oneValue_trans (bsumCongr _ _ hcell (List.range l)) ?_
  exact BPair.oneValue_symm (ground.foldB_ofCounts P N (List.range l))

/-! ## Range folds of guarded count families -/

/-- The one-key family's fold over a key range: the key's value
inside the range, the vacant fold beyond it. -/
private theorem pickR (T w L : Nat) :
    ground.famFold Nat.add 0 (fun x => if T == x then w else 0)
      (List.range L) = if T < L then w else 0 := by
  by_cases hT : T < L
  · rw [if_pos hT]
    exact ground.famFold_pickBeqRange T w L hT
  · rw [if_neg hT]
    refine ground.famFold_rangeZero _ L (fun x hx => ?_)
    exact if_neg (fun he : (T == x) = true =>
      hT (ground.beqEqOf he ▸ hx))

/-! ## Boolean and order helpers -/

private theorem andT (b : Bool) : (b && true) = b := by cases b <;> rfl
private theorem andF (b : Bool) : (b && false) = false := by
  cases b <;> rfl
private theorem orT (b : Bool) : (b || true) = true := by cases b <;> rfl
private theorem orF (b : Bool) : (b || false) = b := by cases b <;> rfl

private theorem neAdd (a d : Nat) : ¬ a = a + (d + 1) := Nat.ne_of_lt (ground.ltAddSucc a d)

/-! ## The `B` Cartan column entries -/

/-- The `B` Cartan entry at a row and a column, the chain with the
doubled edge into the short last key. -/
def cartB (l i j : Nat) : BPair :=
  if j == i then BPair.ofNat 2
  else if j == i + 1 then
    (if i + 2 == l then (BPair.ofNat 2).swap else (BPair.ofNat 1).swap)
  else if j + 1 == i then (BPair.ofNat 1).swap
  else BPair.unit

private theorem cartB_cell (l i j : Nat) :
    (if j == i then BPair.ofNat 2
      else if (i + 2 == l && j == i + 1) then (BPair.ofNat 2).swap
      else if (j + 1 == i || j == i + 1) then (BPair.ofNat 1).swap
      else BPair.unit) = cartB l i j := by
  show _ = (if (j == i) = true then _ else _)
  cases h1 : (j == i) with
  | true => rfl
  | false =>
    cases h2 : (j == i + 1) with
    | true =>
      rw [andT, orT]
      rfl
    | false =>
      rw [andF, orF]
      rfl

/-- The `B` table's Cartan list is the entry function's square. -/
theorem cartB_eq (l : Nat) :
    (sertables.tableB l).cartan
      = ground.matOf l l (fun i j => cartB l i j) :=
  ground.map_congr_all _ _ (fun i =>
    ground.map_congr_all _ _ (fun j => cartB_cell l i j) (List.range l))
    (List.range l)

/-- The `B` Cartan's diagonal entry is two. -/
theorem cartBd (l i : Nat) : cartB l i i = BPair.ofNat 2 := by
  show (if (i == i) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : i = i)]
  rfl

/-- The `B` Cartan's entry one key up, off the short last edge, is
the swapped one. -/
theorem cartBup1 (l i : Nat) (h : ¬ i + 2 = l) :
    cartB l i (i + 1) = (BPair.ofNat 1).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => neAdd i 0 he.symm),
    ground.eqBeqOf (rfl : i + 1 = i + 1), ground.neBeqOf h]
  rfl

/-- The `B` Cartan's entry one key up at the short last edge is the
swapped two. -/
private theorem cartBup2 (l i : Nat) (h : i + 2 = l) :
    cartB l i (i + 1) = (BPair.ofNat 2).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => neAdd i 0 he.symm),
    ground.eqBeqOf (rfl : i + 1 = i + 1), ground.eqBeqOf h]
  rfl

/-- The `B` Cartan's entry one key down is the swapped one. -/
theorem cartBdn (l i : Nat) :
    cartB l (i + 1) i = (BPair.ofNat 1).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (neAdd i 0), ground.neBeqOf (neAdd i 1),
    ground.eqBeqOf (rfl : i + 1 = i + 1)]
  rfl

/-- The `B` Cartan's entry off the diagonal and its two chain
neighbours is vacant. -/
theorem cartBoff (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ j = i + 1)
    (h3 : ¬ j + 1 = i) : cartB l i j = BPair.unit := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1, ground.neBeqOf h2, ground.neBeqOf h3]
  rfl

/-! ## The `B` column reads -/

private theorem colB0c (l : Nat) (h0 : 0 < l) (F : Nat → Nat) :
    (corootAt (sertables.tableB l) ((List.range l).map F) 0).oneValue
      (BPair.ofCounts (2 * F 0) (if 1 < l then F 1 else 0)) := by
  refine BPair.oneValue_trans
    (colValue (sertables.tableB l) (cartB l) l 0 F
      (fun k => if 0 == k then 2 * F 0 else 0)
      (fun k => if 1 == k then F 1 else 0)
      (cartB_eq l) h0 ?_) ?_
  · intro k
    match k with
    | 0 =>
      rw [cartBd l 0]
      exact cellTwo (F 0)
    | 1 =>
      rw [cartBdn l 0]
      exact cellOneNeg (F 1)
    | m + 2 =>
      rw [cartBoff l (m + 2) 0 (fun he => Nat.noConfusion he)
        (fun he => Nat.noConfusion he)
        (fun he => Nat.noConfusion (Nat.succ.inj he))]
      exact cellNull (F (m + 2))
  · rw [pickR 0 (2 * F 0) l, pickR 1 (F 1) l, if_pos h0]
    exact BPair.oneValue_refl _

private theorem colB0 (l : Nat) (hl : 1 < l) (F : Nat → Nat) (v : Nat)
    (h : 2 * F 0 = v + F 1) :
    (corootAt (sertables.tableB l) ((List.range l).map F) 0).oneValue
      (BPair.ofNat v) :=
  BPair.oneValue_trans
    (colB0c l (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_of_lt hl)) F)
    (countsRead (2 * F 0) (if 1 < l then F 1 else 0) v
      (by rw [if_pos hl]; exact h))

private theorem colBmidc (l m : Nat) (hm : m + 2 < l) (F : Nat → Nat) :
    (corootAt (sertables.tableB l) ((List.range l).map F)
      (m + 1)).oneValue
      (BPair.ofCounts (2 * F (m + 1)) (F m + F (m + 2))) := by
  have hj : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm
  have hml : m < l := Nat.lt_trans (Nat.lt_succ_self m) hj
  refine BPair.oneValue_trans
    (colValue (sertables.tableB l) (cartB l) l (m + 1) F
      (fun k => if m + 1 == k then 2 * F (m + 1) else 0)
      (fun k => (if m == k then F m else 0)
        + (if m + 2 == k then F (m + 2) else 0))
      (cartB_eq l) hj ?_) ?_
  · intro k
    by_cases e1 : k = m
    · rw [e1, cartBup1 l m (Nat.ne_of_lt hm),
        ground.neBeqOf (fun he : m + 1 = m => neAdd m 0 he.symm),
        ground.eqBeqOf (rfl : m = m),
        ground.neBeqOf (fun he : m + 2 = m => neAdd m 1 he.symm)]
      exact cellOneNeg (F m)
    · by_cases e2 : k = m + 1
      · rw [e2, cartBd l (m + 1), ground.eqBeqOf (rfl : m + 1 = m + 1),
          ground.neBeqOf (neAdd m 0),
          ground.neBeqOf (fun he : m + 2 = m + 1 =>
            neAdd m 0 (Nat.succ.inj he).symm)]
        exact cellTwo (F (m + 1))
      · by_cases e3 : k = m + 2
        · rw [e3, cartBdn l (m + 1),
            ground.neBeqOf (fun he : m + 1 = m + 2 => neAdd m 0
              (Nat.succ.inj he)),
            ground.neBeqOf (neAdd m 1),
            ground.eqBeqOf (rfl : m + 2 = m + 2)]
          exact cellOneNegZ (F (m + 2))
        · rw [cartBoff l k (m + 1) (fun he => e2 he.symm)
            (fun he => e1 (Nat.succ.inj he).symm)
            (fun he => e3 he.symm),
            ground.neBeqOf (fun he => e2 he.symm),
            ground.neBeqOf (fun he => e1 he.symm),
            ground.neBeqOf (fun he => e3 he.symm)]
          exact cellNull (F k)
  · rw [pickR (m + 1) (2 * F (m + 1)) l,
      ground.famFold_add_split (fun k => if m == k then F m else 0)
        (fun k => if m + 2 == k then F (m + 2) else 0) (List.range l),
      pickR m (F m) l, pickR (m + 2) (F (m + 2)) l,
      if_pos hj, if_pos hml, if_pos hm]
    exact BPair.oneValue_refl _

private theorem colBmid (l m : Nat) (hm : m + 2 < l) (F : Nat → Nat)
    (v : Nat) (h : 2 * F (m + 1) = v + (F m + F (m + 2))) :
    (corootAt (sertables.tableB l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colBmidc l m hm F)
    (countsRead (2 * F (m + 1)) (F m + F (m + 2)) v h)

private theorem colBtopc (l m : Nat) (hm : m + 2 = l) (F : Nat → Nat) :
    (corootAt (sertables.tableB l) ((List.range l).map F)
      (m + 1)).oneValue
      (BPair.ofCounts (2 * F (m + 1)) (2 * F m)) := by
  have hj : m + 1 < l := hm ▸ Nat.lt_succ_self (m + 1)
  have hml : m < l := Nat.lt_trans (Nat.lt_succ_self m) hj
  have hno : ¬ m + 2 < l := hm ▸ Nat.lt_irrefl (m + 2)
  refine BPair.oneValue_trans
    (colValue (sertables.tableB l) (cartB l) l (m + 1) F
      (fun k => if m + 1 == k then 2 * F (m + 1) else 0)
      (fun k => (if m == k then 2 * F m else 0)
        + (if m + 2 == k then F (m + 2) else 0))
      (cartB_eq l) hj ?_) ?_
  · intro k
    by_cases e1 : k = m
    · rw [e1, cartBup2 l m hm,
        ground.neBeqOf (fun he : m + 1 = m => neAdd m 0 he.symm),
        ground.eqBeqOf (rfl : m = m),
        ground.neBeqOf (fun he : m + 2 = m => neAdd m 1 he.symm)]
      exact cellTwoNeg (F m)
    · by_cases e2 : k = m + 1
      · rw [e2, cartBd l (m + 1), ground.eqBeqOf (rfl : m + 1 = m + 1),
          ground.neBeqOf (neAdd m 0),
          ground.neBeqOf (fun he : m + 2 = m + 1 =>
            neAdd m 0 (Nat.succ.inj he).symm)]
        exact cellTwo (F (m + 1))
      · by_cases e3 : k = m + 2
        · rw [e3, cartBdn l (m + 1),
            ground.neBeqOf (fun he : m + 1 = m + 2 => neAdd m 0
              (Nat.succ.inj he)),
            ground.neBeqOf (neAdd m 1),
            ground.eqBeqOf (rfl : m + 2 = m + 2)]
          exact cellOneNegZ (F (m + 2))
        · rw [cartBoff l k (m + 1) (fun he => e2 he.symm)
            (fun he => e1 (Nat.succ.inj he).symm)
            (fun he => e3 he.symm),
            ground.neBeqOf (fun he => e2 he.symm),
            ground.neBeqOf (fun he => e1 he.symm),
            ground.neBeqOf (fun he => e3 he.symm)]
          exact cellNull (F k)
  · rw [pickR (m + 1) (2 * F (m + 1)) l,
      ground.famFold_add_split (fun k => if m == k then 2 * F m else 0)
        (fun k => if m + 2 == k then F (m + 2) else 0) (List.range l),
      pickR m (2 * F m) l, pickR (m + 2) (F (m + 2)) l,
      if_pos hj, if_pos hml, if_neg hno]
    exact BPair.oneValue_refl _

private theorem colBtop (l m : Nat) (hm : m + 2 = l) (F : Nat → Nat)
    (v : Nat) (h : 2 * F (m + 1) = v + 2 * F m) :
    (corootAt (sertables.tableB l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colBtopc l m hm F)
    (countsRead (2 * F (m + 1)) (2 * F m) v h)

/-! ## The word's leading sums -/

/-- The leading sum grows by the word's own entry. -/
private theorem takeStep : ∀ (W : List Nat) (k : Nat),
    ground.sumNat (List.take (k + 1) W)
      = ground.sumNat (List.take k W) + ground.getAt 0 W k
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | a :: t, 0 => by
    show a + ground.sumNat (List.take 0 t) = 0 + a
    rw [Nat.zero_add]
    rfl
  | a :: t, k + 1 => by
    show a + ground.sumNat (List.take (k + 1) t)
      = a + ground.sumNat (List.take k t) + ground.getAt 0 t k
    rw [takeStep t k, Nat.add_assoc]

/-- The word's first leading sum is its first entry. -/
private theorem takeOne (W : List Nat) :
    ground.sumNat (List.take 1 W) = ground.getAt 0 W 0 := by
  rw [takeStep W 0]
  exact Nat.zero_add _

/-- The member's entry at a key inside the rank, the padded word's
gap there. -/
theorem memberEntry (W : List Nat) (l j : Nat) (hj : j < l) :
    ground.getAt 0 (member W l) j
      = ground.getAt 0 W j - ground.getAt 0 W (j + 1) := by
  show ground.getAt 0 ((List.range l).map (fun i =>
    ground.getAt 0 W i - ground.getAt 0 W (i + 1))) j = _
  rw [ground.getAt_map_range 0 _ l j, if_pos hj]

private theorem succAdd : ∀ (a c : Nat), a + (c + 1) = a + 1 + c
  | _, 0 => rfl
  | a, c + 1 => congrArg (· + 1) (succAdd a c)

/-! ## The `B` coroot identities -/

private theorem addSwap (a b c d : Nat) :
    a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), Nat.add_left_comm b c d,
    ← Nat.add_assoc a c (b + d)]

private theorem arithB0 (A C D : Nat) (h : D + C = A) :
    2 * A = D + (A + C) := by
  rw [← h, Nat.two_mul (D + C), addSwap D C D C, Nat.add_assoc D C C,
    Nat.add_assoc D D (C + C)]

private theorem arithBmid (A B C D : Nat) (h : D + C = B) :
    2 * (A + B) = D + (A + (A + B + C)) := by
  rw [← h, Nat.two_mul (A + (D + C)),
    addSwap A (D + C) A (D + C),
    Nat.add_assoc A (D + C) C,
    ← Nat.add_assoc A A (D + C + C),
    Nat.add_left_comm D (A + A) (D + C + C),
    Nat.add_assoc D C (D + C), Nat.add_left_comm C D C,
    Nat.add_assoc D C C]

/-- The `B` series' coroot identities at the leading family's
member: the display's fold reads the member's coroot list. -/
theorem corootRead_B : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    casfloor.corootRead (sertables.tableB l) (endB W l) := by
  intro W l hs hl
  have hsa := ground.sortedAll W hs
  have hl2 : 1 < l :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
      (Nat.le_trans (Nat.le_add_left 2 W.length) hl)
  show ((List.range l).all (fun j => decide
    ((corootAt (sertables.tableB l) (foldB W l) j).oneValue
      (BPair.ofNat (1 * ground.getAt 0 (member W l) j))))) = true
  refine ground.all_range_intro l (fun j hj => decide_eq_true ?_)
  rw [Nat.one_mul, memberEntry W l j hj]
  cases j with
  | zero =>
    refine colB0 l hl2 (fun k => ground.sumNat (List.take (k + 1) W))
      (ground.getAt 0 W 0 - ground.getAt 0 W 1) ?_
    show 2 * ground.sumNat (List.take 1 W)
      = (ground.getAt 0 W 0 - ground.getAt 0 W 1)
        + ground.sumNat (List.take 2 W)
    rw [takeStep W 1, takeOne W]
    exact arithB0 (ground.getAt 0 W 0) (ground.getAt 0 W 1)
      (ground.getAt 0 W 0 - ground.getAt 0 W 1) (ground.subAdd (hsa 0))
  | succ m =>
    by_cases htop : m + 2 = l
    · have hlen : W.length ≤ m :=
        ground.leCancelR 2 (htop ▸ hl)
      have hz1 : ground.getAt 0 W (m + 1) = 0 :=
        ground.getAt_over 0 W (m + 1) (Nat.le_trans hlen (Nat.le_succ m))
      have hz2 : ground.getAt 0 W (m + 2) = 0 :=
        ground.getAt_over 0 W (m + 2) (Nat.le_trans hlen
          (Nat.le_trans (Nat.le_succ m) (Nat.le_succ (m + 1))))
      refine colBtop l m htop
        (fun k => ground.sumNat (List.take (k + 1) W)) _ ?_
      show 2 * ground.sumNat (List.take (m + 2) W)
        = (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
          + 2 * ground.sumNat (List.take (m + 1) W)
      rw [takeStep W (m + 1), hz1, hz2]
      exact (Nat.zero_add _).symm
    · have hmid : m + 2 < l :=
        Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) htop
      refine colBmid l m hmid
        (fun k => ground.sumNat (List.take (k + 1) W)) _ ?_
      show 2 * ground.sumNat (List.take (m + 2) W)
        = (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
          + (ground.sumNat (List.take (m + 1) W)
            + ground.sumNat (List.take (m + 3) W))
      rw [takeStep W (m + 2), takeStep W (m + 1)]
      exact arithBmid (ground.sumNat (List.take (m + 1) W))
        (ground.getAt 0 W (m + 1)) (ground.getAt 0 W (m + 2))
        (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
        (ground.subAdd (hsa (m + 1)))

/-! ## The `C` Cartan column entries -/

/-- The `C` Cartan entry at a row and a column, the chain with the
doubled edge out of the long last key. -/
def cartC (l i j : Nat) : BPair :=
  if j == i then BPair.ofNat 2
  else if i + 1 == l && j + 2 == l then (BPair.ofNat 2).swap
  else if j + 1 == i || j == i + 1 then (BPair.ofNat 1).swap
  else BPair.unit

/-- The `C` table's Cartan list is the entry function's square. -/
theorem cartC_eq (l : Nat) :
    (sertables.tableC l).cartan
      = ground.matOf l l (fun i j => cartC l i j) :=
  rfl

/-- The `C` Cartan's diagonal entry is two. -/
theorem cartCd (l i : Nat) : cartC l i i = BPair.ofNat 2 := by
  show (if (i == i) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : i = i)]
  rfl

/-- The `C` Cartan's entry one key down at the long last edge is
the swapped two. -/
private theorem cartCdn2 (l i : Nat) (h : i + 2 = l) :
    cartC l (i + 1) i = (BPair.ofNat 2).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (neAdd i 0),
    ground.eqBeqOf (show i + 1 + 1 = l from h)]
  rfl

/-- The `C` Cartan's entry one key down, off the long last edge, is
the swapped one. -/
theorem cartCdn1 (l i : Nat) (h : ¬ i + 2 = l) :
    cartC l (i + 1) i = (BPair.ofNat 1).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (neAdd i 0),
    ground.neBeqOf (show ¬ i + 1 + 1 = l from h),
    ground.eqBeqOf (rfl : i + 1 = i + 1)]
  rfl

/-- The `C` Cartan's entry one key up is the swapped one. -/
theorem cartCup (l i : Nat) :
    cartC l i (i + 1) = (BPair.ofNat 1).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => neAdd i 0 he.symm)]
  cases hb : (i + 1 == l) with
  | true =>
    rw [ground.neBeqOf (fun he : i + 1 + 2 = l =>
        neAdd (i + 1) 1 (he.trans (ground.beqEqOf hb).symm).symm),
      ground.eqBeqOf (rfl : i + 1 = i + 1), orT]
    rfl
  | false =>
    rw [ground.eqBeqOf (rfl : i + 1 = i + 1), orT]
    rfl

/-- The `C` Cartan's entry off the diagonal and its two chain
neighbours is vacant. -/
theorem cartCoff (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ j + 1 = i)
    (h3 : ¬ j = i + 1) : cartC l i j = BPair.unit := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1]
  cases hb : (i + 1 == l) with
  | true =>
    rw [ground.neBeqOf (fun he : j + 2 = l =>
        h2 (Nat.succ.inj (he.trans (ground.beqEqOf hb).symm))),
      ground.neBeqOf h2, ground.neBeqOf h3]
    rfl
  | false =>
    rw [ground.neBeqOf h2, ground.neBeqOf h3]
    rfl

/-! ## The `C` column reads -/

private theorem colC0dc (l : Nat) (h0 : 0 < l) (hne : ¬ 0 + 2 = l)
    (F : Nat → Nat) :
    (corootAt (sertables.tableC l) ((List.range l).map F) 0).oneValue
      (BPair.ofCounts (2 * F 0) (if 1 < l then F 1 else 0)) := by
  refine BPair.oneValue_trans
    (colValue (sertables.tableC l) (cartC l) l 0 F
      (fun k => if 0 == k then 2 * F 0 else 0)
      (fun k => if 1 == k then F 1 else 0)
      (cartC_eq l) h0 ?_) ?_
  · intro k
    match k with
    | 0 =>
      rw [cartCd l 0]
      exact cellTwo (F 0)
    | 1 =>
      rw [cartCdn1 l 0 hne]
      exact cellOneNeg (F 1)
    | m + 2 =>
      rw [cartCoff l (m + 2) 0 (fun he => Nat.noConfusion he)
        (fun he => Nat.noConfusion (Nat.succ.inj he))
        (fun he => Nat.noConfusion he)]
      exact cellNull (F (m + 2))
  · rw [pickR 0 (2 * F 0) l, pickR 1 (F 1) l, if_pos h0]
    exact BPair.oneValue_refl _

private theorem colC0d (l : Nat) (hl : 2 < l) (F : Nat → Nat) (v : Nat)
    (h : 2 * F 0 = v + F 1) :
    (corootAt (sertables.tableC l) ((List.range l).map F) 0).oneValue
      (BPair.ofNat v) :=
  BPair.oneValue_trans
    (colC0dc l (Nat.lt_trans (Nat.lt_succ_self 0)
        (Nat.lt_trans (Nat.lt_succ_self 1) hl))
      (Nat.ne_of_lt hl) F)
    (countsRead (2 * F 0) (if 1 < l then F 1 else 0) v
      (by rw [if_pos (Nat.lt_trans (Nat.lt_succ_self 1) hl)]; exact h))

private theorem colC0ec (l : Nat) (he : 2 = l) (F : Nat → Nat) :
    (corootAt (sertables.tableC l) ((List.range l).map F) 0).oneValue
      (BPair.ofCounts (2 * F 0) (2 * F 1)) := by
  have h1 : 1 < l := he ▸ Nat.lt_succ_self 1
  have h0 : 0 < l := Nat.lt_trans (Nat.lt_succ_self 0) h1
  refine BPair.oneValue_trans
    (colValue (sertables.tableC l) (cartC l) l 0 F
      (fun k => if 0 == k then 2 * F 0 else 0)
      (fun k => if 1 == k then 2 * F 1 else 0)
      (cartC_eq l) h0 ?_) ?_
  · intro k
    match k with
    | 0 =>
      rw [cartCd l 0]
      exact cellTwo (F 0)
    | 1 =>
      rw [cartCdn2 l 0 (show 0 + 2 = l from he)]
      exact cellTwoNeg (F 1)
    | m + 2 =>
      rw [cartCoff l (m + 2) 0 (fun hx => Nat.noConfusion hx)
        (fun hx => Nat.noConfusion (Nat.succ.inj hx))
        (fun hx => Nat.noConfusion hx)]
      exact cellNull (F (m + 2))
  · rw [pickR 0 (2 * F 0) l, pickR 1 (2 * F 1) l, if_pos h0, if_pos h1]
    exact BPair.oneValue_refl _

private theorem colC0e (l : Nat) (he : 2 = l) (F : Nat → Nat) (v : Nat)
    (h : 2 * F 0 = v + 2 * F 1) :
    (corootAt (sertables.tableC l) ((List.range l).map F) 0).oneValue
      (BPair.ofNat v) :=
  BPair.oneValue_trans (colC0ec l he F)
    (countsRead (2 * F 0) (2 * F 1) v h)

private theorem colCgenc (l m : Nat) (hj : m + 1 < l) (F : Nat → Nat)
    (w n : Nat) (hup : cartC l (m + 2) (m + 1) = (BPair.ofNat w).swap)
    (hw : ∀ c : Nat, (BPair.ofNat c * (BPair.ofNat w).swap).oneValue
      (BPair.ofCounts 0 (0 + w * c)))
    (hfold : ground.famFold Nat.add 0
        (fun k => (if m == k then F m else 0)
          + (if m + 2 == k then w * F (m + 2) else 0)) (List.range l)
      = n) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofCounts (2 * F (m + 1)) n) := by
  refine BPair.oneValue_trans
    (colValue (sertables.tableC l) (cartC l) l (m + 1) F
      (fun k => if m + 1 == k then 2 * F (m + 1) else 0)
      (fun k => (if m == k then F m else 0)
        + (if m + 2 == k then w * F (m + 2) else 0))
      (cartC_eq l) hj ?_) ?_
  · intro k
    by_cases e1 : k = m
    · rw [e1, cartCup l m,
        ground.neBeqOf (fun hx : m + 1 = m => neAdd m 0 hx.symm),
        ground.eqBeqOf (rfl : m = m),
        ground.neBeqOf (fun hx : m + 2 = m => neAdd m 1 hx.symm)]
      exact cellOneNeg (F m)
    · by_cases e2 : k = m + 1
      · rw [e2, cartCd l (m + 1),
          ground.eqBeqOf (rfl : m + 1 = m + 1),
          ground.neBeqOf (neAdd m 0),
          ground.neBeqOf (fun hx : m + 2 = m + 1 =>
            neAdd m 0 (Nat.succ.inj hx).symm)]
        exact cellTwo (F (m + 1))
      · by_cases e3 : k = m + 2
        · rw [e3, hup,
            ground.neBeqOf (fun hx : m + 1 = m + 2 =>
              neAdd m 0 (Nat.succ.inj hx)),
            ground.neBeqOf (neAdd m 1),
            ground.eqBeqOf (rfl : m + 2 = m + 2)]
          exact hw (F (m + 2))
        · rw [cartCoff l k (m + 1) (fun hx => e2 hx.symm)
            (fun hx => e3 hx.symm)
            (fun hx => e1 (Nat.succ.inj hx).symm),
            ground.neBeqOf (fun hx => e2 hx.symm),
            ground.neBeqOf (fun hx => e1 hx.symm),
            ground.neBeqOf (fun hx => e3 hx.symm)]
          exact cellNull (F k)
  · rw [pickR (m + 1) (2 * F (m + 1)) l, hfold, if_pos hj]
    exact BPair.oneValue_refl _

private theorem cfold (l m : Nat) (F : Nat → Nat) (w : Nat)
    (hm : m < l) :
    ground.famFold Nat.add 0
      (fun k => (if m == k then F m else 0)
        + (if m + 2 == k then w * F (m + 2) else 0)) (List.range l)
    = F m + (if m + 2 < l then w * F (m + 2) else 0) := by
  rw [ground.famFold_add_split (fun k => if m == k then F m else 0)
      (fun k => if m + 2 == k then w * F (m + 2) else 0) (List.range l),
    pickR m (F m) l, pickR (m + 2) (w * F (m + 2)) l, if_pos hm]

private theorem colCmdc (l m : Nat) (hm : m + 3 < l) (F : Nat → Nat) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue
      (BPair.ofCounts (2 * F (m + 1)) (F m + F (m + 2))) := by
  have h2 : m + 2 < l := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm
  have h1 : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) h2
  have h0 : m < l := Nat.lt_trans (Nat.lt_succ_self m) h1
  refine colCgenc l m h1 F 1 (F m + F (m + 2))
    (cartCdn1 l (m + 1) (show ¬ m + 1 + 2 = l from Nat.ne_of_lt hm))
    (fun c => by rw [Nat.zero_add, Nat.one_mul]; exact cellOneNeg c) ?_
  rw [cfold l m F 1 h0, if_pos h2, Nat.one_mul]

private theorem colCmd (l m : Nat) (hm : m + 3 < l) (F : Nat → Nat)
    (v : Nat) (h : 2 * F (m + 1) = v + (F m + 1 * F (m + 2))) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colCmdc l m hm F)
    (countsRead (2 * F (m + 1)) (F m + F (m + 2)) v
      (by rw [Nat.one_mul] at h; exact h))

private theorem colCmec (l m : Nat) (he : m + 3 = l) (F : Nat → Nat) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue
      (BPair.ofCounts (2 * F (m + 1)) (F m + 2 * F (m + 2))) := by
  have h2 : m + 2 < l := he ▸ Nat.lt_succ_self (m + 2)
  have h1 : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) h2
  have h0 : m < l := Nat.lt_trans (Nat.lt_succ_self m) h1
  refine colCgenc l m h1 F 2 (F m + 2 * F (m + 2))
    (cartCdn2 l (m + 1) (show m + 1 + 2 = l from he))
    (fun c => by rw [Nat.zero_add]; exact cellTwoNeg c) ?_
  rw [cfold l m F 2 h0, if_pos h2]

private theorem colCme (l m : Nat) (he : m + 3 = l) (F : Nat → Nat)
    (v : Nat) (h : 2 * F (m + 1) = v + (F m + 2 * F (m + 2))) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colCmec l m he F)
    (countsRead (2 * F (m + 1)) (F m + 2 * F (m + 2)) v h)

private theorem colCtopc (l m : Nat) (ht : m + 2 = l) (F : Nat → Nat) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofCounts (2 * F (m + 1)) (F m)) := by
  have h1 : m + 1 < l := ht ▸ Nat.lt_succ_self (m + 1)
  have h0 : m < l := Nat.lt_trans (Nat.lt_succ_self m) h1
  have hno : ¬ m + 2 < l := ht ▸ Nat.lt_irrefl (m + 2)
  refine colCgenc l m h1 F 1 (F m)
    (cartCdn1 l (m + 1)
      (show ¬ m + 1 + 2 = l from fun hx => neAdd (m + 2) 0 (ht.trans hx.symm)))
    (fun c => by rw [Nat.zero_add, Nat.one_mul]; exact cellOneNeg c) ?_
  rw [cfold l m F 1 h0, if_neg hno, Nat.add_zero]

private theorem colCtop (l m : Nat) (ht : m + 2 = l) (F : Nat → Nat)
    (v : Nat) (h : 2 * F (m + 1) = v + (F m + 0)) :
    (corootAt (sertables.tableC l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colCtopc l m ht F)
    (countsRead (2 * F (m + 1)) (F m) v h)

/-! ## The word's full leading sum -/

private theorem sumFull (W : List Nat) (k : Nat) (h : W.length ≤ k + 1) :
    ground.sumNat (List.take (k + 1) W) = ground.sumNat W :=
  congrArg ground.sumNat (ground.take_of_le W (k + 1) h)

private theorem sumHead (W : List Nat) (h : W.length ≤ 1) :
    ground.sumNat W = ground.getAt 0 W 0 :=
  (sumFull W 0 h).symm.trans (takeOne W)

private theorem subZero (x : Nat) : x - 0 = x := rfl

private theorem arithD3 (A B : Nat) : 2 * (A + B) = B + (A + (A + B)) := by
  rw [Nat.two_mul (A + B), ← Nat.add_assoc B A (A + B), Nat.add_comm B A]

private theorem dfold2 (l a b wa wb : Nat) :
    ground.famFold Nat.add 0
      (fun k => (if a == k then wa else 0) + (if b == k then wb else 0))
      (List.range l)
    = (if a < l then wa else 0) + (if b < l then wb else 0) := by
  rw [ground.famFold_add_split (fun k => if a == k then wa else 0)
      (fun k => if b == k then wb else 0) (List.range l),
    pickR a wa l, pickR b wb l]

private theorem dfold3 (l a b c wa wb wc : Nat) :
    ground.famFold Nat.add 0
      (fun k => (if a == k then wa else 0)
        + ((if b == k then wb else 0) + (if c == k then wc else 0)))
      (List.range l)
    = (if a < l then wa else 0)
      + ((if b < l then wb else 0) + (if c < l then wc else 0)) := by
  rw [ground.famFold_add_split (fun k => if a == k then wa else 0)
      (fun k => (if b == k then wb else 0) + (if c == k then wc else 0))
      (List.range l),
    dfold2 l b c wb wc, pickR a wa l]

private theorem sumNilOf : ∀ (W : List Nat), W.length ≤ 0 →
    ground.sumNat W = 0
  | [], _ => rfl
  | _ :: _, h => absurd h (Nat.not_succ_le_zero _)

/-- The `C` series' coroot identities at the leading family's
member. -/
theorem corootRead_C : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    casfloor.corootRead (sertables.tableC l) (endC W l) := by
  intro W l hs hl
  have hsa := ground.sortedAll W hs
  show ((List.range l).all (fun j => decide
    ((corootAt (sertables.tableC l) (foldC W l) j).oneValue
      (BPair.ofNat (2 * ground.getAt 0 (member W l) j))))) = true
  refine ground.all_range_intro l (fun j hj => decide_eq_true ?_)
  rw [memberEntry W l j hj]
  cases j with
  | zero =>
    by_cases hl2 : 2 = l
    · have hlen : W.length ≤ 0 :=
        ground.leCancelR 2 (show W.length + 2 ≤ 0 + 2 from
          Nat.le_trans hl (Nat.le_of_eq hl2.symm))
      refine colC0e l hl2
        (fun k => if l ≤ k + 1 then ground.sumNat W
          else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_
      rw [if_neg (show ¬ l ≤ 0 + 1 from fun hc =>
          Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
              (Nat.le_of_eq hl2)))),
        if_pos (show l ≤ 1 + 1 from Nat.le_of_eq hl2.symm),
        ground.take_of_le W (0 + 1) (Nat.le_trans hlen (Nat.zero_le 1)),
        sumNilOf W hlen, ground.getAt_over 0 W 0 hlen,
        ground.getAt_over 0 W 1 (Nat.le_trans hlen (Nat.zero_le 1))]
    · have hl3 : 2 < l :=
        Nat.lt_of_le_of_ne (Nat.le_trans (Nat.le_add_left 2 W.length) hl)
          hl2
      have h1l : 1 < l := Nat.lt_trans (Nat.lt_succ_self 1) hl3
      refine colC0d l hl3
        (fun k => if l ≤ k + 1 then ground.sumNat W
          else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_
      rw [if_neg (show ¬ l ≤ 0 + 1 from fun hc =>
          Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc h1l)),
        if_neg (show ¬ l ≤ 1 + 1 from fun hc =>
          Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hl3)),
        takeStep W 1, takeOne W,
        ← Nat.left_distrib 2 (ground.getAt 0 W 0 - ground.getAt 0 W 1)
          (ground.getAt 0 W 0 + ground.getAt 0 W 1),
        ← arithB0 (ground.getAt 0 W 0) (ground.getAt 0 W 1)
          (ground.getAt 0 W 0 - ground.getAt 0 W 1) (ground.subAdd (hsa 0))]
  | succ m =>
    have hm2 : m + 2 ≤ l := Nat.succ_le_of_lt hj
    by_cases htop : m + 2 = l
    · have hlen : W.length ≤ m :=
        ground.leCancelR 2 (show W.length + 2 ≤ m + 2 from
          Nat.le_trans hl (Nat.le_of_eq htop.symm))
      refine colCtop l m htop
        (fun k => if l ≤ k + 1 then ground.sumNat W
          else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_
      rw [if_pos (show l ≤ m + 1 + 1 from Nat.le_of_eq htop.symm),
        if_neg (show ¬ l ≤ m + 1 from fun hc =>
          Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hj)),
        sumFull W m (Nat.le_trans hlen (Nat.le_succ m)),
        ground.getAt_over 0 W (m + 1) (Nat.le_trans hlen (Nat.le_succ m)),
        ground.getAt_over 0 W (m + 2) (Nat.le_trans hlen
          (Nat.le_trans (Nat.le_succ m) (Nat.le_succ (m + 1)))),
        show (0 : Nat) - 0 = 0 from rfl, Nat.mul_zero, Nat.zero_add]
      rfl
    · have hB : m + 2 < l := Nat.lt_of_le_of_ne hm2 htop
      by_cases hme : m + 3 = l
      · have hlen : W.length ≤ m + 1 :=
          ground.leCancelR 2 (show W.length + 2 ≤ m + 1 + 2 from
            Nat.le_trans hl (Nat.le_of_eq hme.symm))
        refine colCme l m hme
          (fun k => if l ≤ k + 1 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_
        rw [if_neg (show ¬ l ≤ m + 1 + 1 from fun hc =>
            Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hB)),
          if_neg (show ¬ l ≤ m + 1 from fun hc =>
            Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hj)),
          if_pos (show l ≤ m + 2 + 1 from Nat.le_of_eq hme.symm),
          sumFull W (m + 1) (Nat.le_trans hlen (Nat.le_succ (m + 1))),
          sumFull W m hlen,
          ground.getAt_over 0 W (m + 1) hlen,
          ground.getAt_over 0 W (m + 2) (Nat.le_trans hlen (Nat.le_succ (m + 1))),
          show (0 : Nat) - 0 = 0 from rfl, Nat.mul_zero, Nat.zero_add,
          Nat.two_mul (2 * ground.sumNat W)]
      · have hC : m + 3 < l :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hB) hme
        refine colCmd l m hC
          (fun k => if l ≤ k + 1 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_
        rw [if_neg (show ¬ l ≤ m + 1 + 1 from fun hc =>
            Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hB)),
          if_neg (show ¬ l ≤ m + 1 from fun hc =>
            Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hj)),
          if_neg (show ¬ l ≤ m + 2 + 1 from fun hc =>
            Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hC)),
          takeStep W (m + 2), takeStep W (m + 1), Nat.one_mul,
          ← Nat.left_distrib 2 (ground.sumNat (List.take (m + 1) W))
            (ground.sumNat (List.take (m + 1) W)
              + ground.getAt 0 W (m + 1) + ground.getAt 0 W (m + 2)),
          ← Nat.left_distrib 2
            (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
            (ground.sumNat (List.take (m + 1) W)
              + (ground.sumNat (List.take (m + 1) W)
                + ground.getAt 0 W (m + 1) + ground.getAt 0 W (m + 2))),
          ← arithBmid (ground.sumNat (List.take (m + 1) W))
            (ground.getAt 0 W (m + 1)) (ground.getAt 0 W (m + 2))
            (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
            (ground.subAdd (hsa (m + 1)))]

/-! ## The `D` Cartan column entries -/

/-- The `D` Cartan entry at a row and a column, the fork joining
the last two keys to the key before them. -/
def cartD (l i j : Nat) : BPair :=
  if j == i then BPair.ofNat 2
  else if i + 1 == l then
    (if j + 3 == l then (BPair.ofNat 1).swap else BPair.unit)
  else if j + 1 == l then
    (if i + 3 == l then (BPair.ofNat 1).swap else BPair.unit)
  else if j + 1 == i || j == i + 1 then (BPair.ofNat 1).swap
  else BPair.unit

/-- The `D` table's Cartan list is the entry function's square. -/
theorem cartD_eq (l : Nat) :
    (sertables.tableD l).cartan
      = ground.matOf l l (fun i j => cartD l i j) :=
  rfl

/-- The `D` Cartan's diagonal entry is two. -/
theorem cartDd (l i : Nat) : cartD l i i = BPair.ofNat 2 := by
  show (if (i == i) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : i = i)]
  rfl

/-- The `D` Cartan's entry one key up, along the chain below the
fork, is the swapped one. -/
theorem cartDup (l i : Nat) (h2 : ¬ i + 1 = l)
    (h3 : ¬ i + 2 = l) : cartD l i (i + 1) = (BPair.ofNat 1).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => neAdd i 0 he.symm),
    ground.neBeqOf h2, ground.neBeqOf (show ¬ i + 1 + 1 = l from h3),
    ground.eqBeqOf (rfl : i + 1 = i + 1), orT]
  rfl

/-- The `D` Cartan's entry one key down, along the chain below the
fork, is the swapped one. -/
theorem cartDdn (l i : Nat) (h2 : ¬ i + 2 = l)
    (h3 : ¬ i + 1 = l) : cartD l (i + 1) i = (BPair.ofNat 1).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (neAdd i 0),
    ground.neBeqOf (show ¬ i + 1 + 1 = l from h2), ground.neBeqOf h3,
    ground.eqBeqOf (rfl : i + 1 = i + 1)]
  rfl

/-- The `D` Cartan's entry at the last key against the key three
below the rank is the swapped one. -/
private theorem cartDfork (l i j : Nat) (h1 : ¬ j = i) (h2 : i + 1 = l)
    (h3 : j + 3 = l) : cartD l i j = (BPair.ofNat 1).swap := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1, ground.eqBeqOf h2, ground.eqBeqOf h3]
  rfl

/-- The `D` Cartan's entry at the key three below the rank against
the last key is the swapped one. -/
theorem cartDforkT (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ i + 1 = l)
    (h3 : j + 1 = l) (h4 : i + 3 = l) :
    cartD l i j = (BPair.ofNat 1).swap := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1, ground.neBeqOf h2, ground.eqBeqOf h3,
    ground.eqBeqOf h4]
  rfl

/-- The `D` Cartan's entry off the diagonal, off the fork's two
edges and off the chain's two neighbours is vacant. -/
theorem cartDoff (l i j : Nat) (h1 : ¬ j = i)
    (h2 : i + 1 = l → ¬ j + 3 = l)
    (h3 : ¬ i + 1 = l → j + 1 = l → ¬ i + 3 = l)
    (h4 : ¬ i + 1 = l → ¬ j + 1 = l → ¬ j + 1 = i)
    (h5 : ¬ i + 1 = l → ¬ j + 1 = l → ¬ j = i + 1) :
    cartD l i j = BPair.unit := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1]
  cases hb : (i + 1 == l) with
  | true =>
    rw [ground.neBeqOf (h2 (ground.beqEqOf hb))]
    rfl
  | false =>
    have hbn : ¬ i + 1 = l := fun he =>
      Bool.noConfusion (hb.symm.trans (ground.eqBeqOf he))
    cases hc : (j + 1 == l) with
    | true =>
      rw [ground.neBeqOf (h3 hbn (ground.beqEqOf hc))]
      rfl
    | false =>
      have hcn : ¬ j + 1 = l := fun he =>
        Bool.noConfusion (hc.symm.trans (ground.eqBeqOf he))
      rw [ground.neBeqOf (h4 hbn hcn), ground.neBeqOf (h5 hbn hcn)]
      rfl

/-! ## The `D` column reads -/

private theorem colDsimplec (l j : Nat) (hj : j < l) (F : Nat → Nat)
    (hoff : ∀ k, ¬ k = j → cartD l k j = BPair.unit) :
    (corootAt (sertables.tableD l) ((List.range l).map F) j).oneValue
      (BPair.ofCounts (2 * F j) 0) := by
  refine BPair.oneValue_trans
    (colValue (sertables.tableD l) (cartD l) l j F
      (fun k => if j == k then 2 * F j else 0) (fun _ => 0)
      (cartD_eq l) hj ?_) ?_
  · intro k
    by_cases e : k = j
    · rw [e, cartDd l j, ground.eqBeqOf (rfl : j = j)]
      exact cellTwo (F j)
    · rw [hoff k e, ground.neBeqOf (fun he => e he.symm)]
      exact cellNull (F k)
  · rw [pickR j (2 * F j) l, if_pos hj,
      ground.famFold_rangeZero (fun _ => 0) l (fun _ _ => rfl)]
    exact BPair.oneValue_refl _

private theorem colDsimple (l j : Nat) (hj : j < l) (F : Nat → Nat)
    (v : Nat) (hoff : ∀ k, ¬ k = j → cartD l k j = BPair.unit)
    (h : 2 * F j = v + 0) :
    (corootAt (sertables.tableD l) ((List.range l).map F) j).oneValue
      (BPair.ofNat v) :=
  BPair.oneValue_trans (colDsimplec l j hj F hoff)
    (countsRead (2 * F j) 0 v h)

private theorem colDzeroc (l : Nat) (h1 : 1 < l) (F : Nat → Nat)
    (c1 c2 : Nat)
    (hE1 : ∀ c : Nat, (BPair.ofNat c * cartD l 1 0).oneValue
      (BPair.ofCounts 0 (c1 * c)))
    (hE2 : ∀ c : Nat, (BPair.ofNat c * cartD l 2 0).oneValue
      (BPair.ofCounts 0 (0 + c2 * c)))
    (hoff : ∀ q : Nat, cartD l (q + 3) 0 = BPair.unit) :
    (corootAt (sertables.tableD l) ((List.range l).map F) 0).oneValue
      (BPair.ofCounts (2 * F 0) ((if 1 < l then c1 * F 1 else 0)
        + (if 2 < l then c2 * F 2 else 0))) := by
  have h0 : 0 < l := Nat.lt_trans (Nat.lt_succ_self 0) h1
  refine BPair.oneValue_trans
    (colValue (sertables.tableD l) (cartD l) l 0 F
      (fun k => if 0 == k then 2 * F 0 else 0)
      (fun k => (if 1 == k then c1 * F 1 else 0)
        + (if 2 == k then c2 * F 2 else 0))
      (cartD_eq l) h0 ?_) ?_
  · intro k
    match k with
    | 0 =>
      rw [cartDd l 0]
      exact cellTwo (F 0)
    | 1 => exact hE1 (F 1)
    | 2 => exact hE2 (F 2)
    | q + 3 =>
      rw [hoff q]
      exact cellNull (F (q + 3))
  · rw [pickR 0 (2 * F 0) l, if_pos h0, dfold2 l 1 2 (c1 * F 1) (c2 * F 2)]
    exact BPair.oneValue_refl _

private theorem colDzero (l : Nat) (h1 : 1 < l) (F : Nat → Nat)
    (c1 c2 v : Nat)
    (hE1 : ∀ c : Nat, (BPair.ofNat c * cartD l 1 0).oneValue
      (BPair.ofCounts 0 (c1 * c)))
    (hE2 : ∀ c : Nat, (BPair.ofNat c * cartD l 2 0).oneValue
      (BPair.ofCounts 0 (0 + c2 * c)))
    (hoff : ∀ q : Nat, cartD l (q + 3) 0 = BPair.unit)
    (h : 2 * F 0 = v + ((if 1 < l then c1 * F 1 else 0)
      + (if 2 < l then c2 * F 2 else 0))) :
    (corootAt (sertables.tableD l) ((List.range l).map F) 0).oneValue
      (BPair.ofNat v) :=
  BPair.oneValue_trans (colDzeroc l h1 F c1 c2 hE1 hE2 hoff)
    (countsRead (2 * F 0) _ v h)

private theorem colDmidc (l m : Nat) (hj2 : m + 2 < l) (F : Nat → Nat)
    (c1 c2 : Nat)
    (hE1 : ∀ c : Nat, (BPair.ofNat c * cartD l (m + 2) (m + 1)).oneValue
      (BPair.ofCounts 0 (0 + c1 * c)))
    (hE2 : ∀ c : Nat, (BPair.ofNat c * cartD l (m + 3) (m + 1)).oneValue
      (BPair.ofCounts 0 (0 + (0 + c2 * c)))) :
    (corootAt (sertables.tableD l) ((List.range l).map F)
      (m + 1)).oneValue
      (BPair.ofCounts (2 * F (m + 1)) ((if m < l then F m else 0)
        + ((if m + 2 < l then c1 * F (m + 2) else 0)
          + (if m + 3 < l then c2 * F (m + 3) else 0)))) := by
  have hj : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hj2
  refine BPair.oneValue_trans
    (colValue (sertables.tableD l) (cartD l) l (m + 1) F
      (fun k => if m + 1 == k then 2 * F (m + 1) else 0)
      (fun k => (if m == k then F m else 0)
        + ((if m + 2 == k then c1 * F (m + 2) else 0)
          + (if m + 3 == k then c2 * F (m + 3) else 0)))
      (cartD_eq l) hj ?_) ?_
  · intro k
    by_cases e1 : k = m
    · rw [e1, cartDup l m
        (fun he => Nat.lt_irrefl (m + 1) (Nat.lt_trans
          (Nat.lt_succ_self (m + 1))
          (Nat.lt_of_lt_of_le hj2 (Nat.le_of_eq he.symm))))
        (fun he => Nat.lt_irrefl l (he ▸ hj2)),
        ground.neBeqOf (fun hx : m + 1 = m => neAdd m 0 hx.symm),
        ground.eqBeqOf (rfl : m = m),
        ground.neBeqOf (fun hx : m + 2 = m => neAdd m 1 hx.symm),
        ground.neBeqOf (fun hx : m + 3 = m => neAdd m 2 hx.symm)]
      exact cellOneNeg (F m)
    · by_cases e2 : k = m + 1
      · rw [e2, cartDd l (m + 1), ground.eqBeqOf (rfl : m + 1 = m + 1),
          ground.neBeqOf (neAdd m 0),
          ground.neBeqOf (fun hx : m + 2 = m + 1 =>
            neAdd m 0 (Nat.succ.inj hx).symm),
          ground.neBeqOf (fun hx : m + 3 = m + 1 =>
            neAdd m 1 (Nat.succ.inj hx).symm)]
        exact cellTwo (F (m + 1))
      · by_cases e3 : k = m + 2
        · rw [e3, ground.neBeqOf (fun hx : m + 1 = m + 2 =>
              neAdd m 0 (Nat.succ.inj hx)),
            ground.neBeqOf (neAdd m 1),
            ground.eqBeqOf (rfl : m + 2 = m + 2),
            ground.neBeqOf (fun hx : m + 3 = m + 2 =>
              neAdd m 0 (Nat.succ.inj (Nat.succ.inj hx)).symm)]
          exact hE1 (F (m + 2))
        · by_cases e4 : k = m + 3
          · rw [e4, ground.neBeqOf (fun hx : m + 1 = m + 3 =>
                neAdd m 1 (Nat.succ.inj hx)),
              ground.neBeqOf (neAdd m 2),
              ground.neBeqOf (fun hx : m + 2 = m + 3 =>
                neAdd m 0 (Nat.succ.inj (Nat.succ.inj hx))),
              ground.eqBeqOf (rfl : m + 3 = m + 3)]
            exact hE2 (F (m + 3))
          · rw [cartDoff l k (m + 1) (fun hx => e2 hx.symm)
              (fun hk hx => e4 (Nat.succ.inj (hk.trans hx.symm)))
              (fun _ hx => absurd (show m + 2 = l from hx)
                (fun he => Nat.lt_irrefl l (he ▸ hj2)))
              (fun _ _ hx => e3 hx.symm)
              (fun _ _ hx => e1 (Nat.succ.inj hx).symm),
              ground.neBeqOf (fun hx => e2 hx.symm),
              ground.neBeqOf (fun hx => e1 hx.symm),
              ground.neBeqOf (fun hx => e3 hx.symm),
              ground.neBeqOf (fun hx => e4 hx.symm)]
            exact cellNull (F k)
  · rw [pickR (m + 1) (2 * F (m + 1)) l, if_pos hj,
      dfold3 l m (m + 2) (m + 3) (F m) (c1 * F (m + 2)) (c2 * F (m + 3))]
    exact BPair.oneValue_refl _

private theorem colDmid (l m : Nat) (hj2 : m + 2 < l) (F : Nat → Nat)
    (c1 c2 v : Nat)
    (hE1 : ∀ c : Nat, (BPair.ofNat c * cartD l (m + 2) (m + 1)).oneValue
      (BPair.ofCounts 0 (0 + c1 * c)))
    (hE2 : ∀ c : Nat, (BPair.ofNat c * cartD l (m + 3) (m + 1)).oneValue
      (BPair.ofCounts 0 (0 + (0 + c2 * c))))
    (h : 2 * F (m + 1) = v + ((if m < l then F m else 0)
      + ((if m + 2 < l then c1 * F (m + 2) else 0)
        + (if m + 3 < l then c2 * F (m + 3) else 0)))) :
    (corootAt (sertables.tableD l) ((List.range l).map F)
      (m + 1)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colDmidc l m hj2 F c1 c2 hE1 hE2)
    (countsRead (2 * F (m + 1)) _ v h)

private theorem colDtopc (l m : Nat) (ht : m + 3 = l) (F : Nat → Nat) :
    (corootAt (sertables.tableD l) ((List.range l).map F)
      (m + 2)).oneValue
      (BPair.ofCounts (2 * F (m + 2)) (if m < l then F m else 0)) := by
  have hj : m + 2 < l := ht ▸ Nat.lt_succ_self (m + 2)
  have hne : ¬ m + 2 + 1 = l → False := fun hc => hc ht
  refine BPair.oneValue_trans
    (colValue (sertables.tableD l) (cartD l) l (m + 2) F
      (fun k => if m + 2 == k then 2 * F (m + 2) else 0)
      (fun k => if m == k then F m else 0)
      (cartD_eq l) hj ?_) ?_
  · intro k
    by_cases e1 : k = m
    · rw [e1, cartDforkT l m (m + 2) (fun hx => neAdd m 1 hx.symm)
        (fun hx => neAdd (m + 1) 1 (hx.trans ht.symm)) ht ht,
        ground.neBeqOf (fun hx : m + 2 = m => neAdd m 1 hx.symm),
        ground.eqBeqOf (rfl : m = m)]
      exact cellOneNeg (F m)
    · by_cases e2 : k = m + 2
      · rw [e2, cartDd l (m + 2), ground.eqBeqOf (rfl : m + 2 = m + 2),
          ground.neBeqOf (neAdd m 1)]
        exact cellTwo (F (m + 2))
      · rw [cartDoff l k (m + 2) (fun hx => e2 hx.symm)
          (fun hk => absurd (Nat.succ.inj (hk.trans ht.symm)) e2)
          (fun _ hx => fun hc => e1 (Nat.succ.inj (Nat.succ.inj
            (Nat.succ.inj (hc.trans ht.symm)))))
          (fun _ hc => absurd (show m + 2 + 1 = l from ht) hc)
          (fun _ hc => absurd (show m + 2 + 1 = l from ht) hc),
          ground.neBeqOf (fun hx => e2 hx.symm),
          ground.neBeqOf (fun hx => e1 hx.symm)]
        exact cellNull (F k)
  · rw [pickR (m + 2) (2 * F (m + 2)) l, if_pos hj, pickR m (F m) l]
    exact BPair.oneValue_refl _

private theorem colDtop (l m : Nat) (ht : m + 3 = l) (F : Nat → Nat)
    (v : Nat) (h : 2 * F (m + 2) = v + (if m < l then F m else 0)) :
    (corootAt (sertables.tableD l) ((List.range l).map F)
      (m + 2)).oneValue (BPair.ofNat v) :=
  BPair.oneValue_trans (colDtopc l m ht F)
    (countsRead (2 * F (m + 2)) _ v h)

/-- The `D` series' coroot identities at the leading family's
member. -/
theorem corootRead_D : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    casfloor.corootRead (sertables.tableD l) (endD W l) := by
  intro W l hs hl
  have hsa := ground.sortedAll W hs
  show ((List.range l).all (fun j => decide
    ((corootAt (sertables.tableD l) (foldD W l) j).oneValue
      (BPair.ofNat (2 * ground.getAt 0 (member W l) j))))) = true
  refine ground.all_range_intro l (fun j hj => decide_eq_true ?_)
  rw [memberEntry W l j hj]
  cases j with
  | zero =>
    by_cases hl2 : 2 = l
    · have hlen : W.length ≤ 0 := ground.leCancelR 2
        (show W.length + 2 ≤ 0 + 2 from
          Nat.le_trans hl (Nat.le_of_eq hl2.symm))
      refine colDsimple l 0 (hl2 ▸ Nat.zero_lt_succ 1)
        (fun k => if l ≤ k + 2 then ground.sumNat W
          else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_ ?_
      · intro k hk
        exact cartDoff l k 0 (fun hx => hk hx.symm)
          (fun _ hx => absurd ((show (3 : Nat) = l from hx).trans hl2.symm)
            (by decide +kernel))
          (fun _ hx _ => absurd
            ((show (1 : Nat) = l from hx).trans hl2.symm) (by decide +kernel))
          (fun hb _ hx => hb (show k + 1 = l from by
            rw [← show (1 : Nat) = k from hx]; exact hl2))
          (fun _ _ hx => Nat.noConfusion hx)
      · show 2 * (if l ≤ 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take 1 W))
          = 2 * (ground.getAt 0 W 0 - ground.getAt 0 W 1) + 0
        rw [if_pos (Nat.le_of_eq hl2.symm), sumNilOf W hlen,
          ground.getAt_over 0 W 0 hlen,
          ground.getAt_over 0 W 1 (Nat.le_trans hlen (Nat.zero_le 1))]
    · have hl3 : 2 < l :=
        Nat.lt_of_le_of_ne (Nat.le_trans (Nat.le_add_left 2 W.length) hl)
          hl2
      have h1l : 1 < l := Nat.lt_trans (Nat.lt_succ_self 1) hl3
      have hne1 : ¬ (1 : Nat) = l := Nat.ne_of_lt h1l
      have hne2 : ¬ (2 : Nat) = l := hl2
      by_cases he3 : (3 : Nat) = l
      · have hlen : W.length ≤ 1 := ground.leCancelR 2
          (show W.length + 2 ≤ 1 + 2 from
            Nat.le_trans hl (Nat.le_of_eq he3.symm))
        refine colDzero l h1l
          (fun k => if l ≤ k + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) 1 1 _
          (fun c => by
            rw [cartDdn l 0 (show ¬ 0 + 2 = l from hne2)
              (show ¬ 0 + 1 = l from hne1), Nat.one_mul]
            exact cellOneNeg c)
          (fun c => by
            rw [cartDfork l 2 0 (by decide +kernel)
              (show 2 + 1 = l from he3) (show 0 + 3 = l from he3),
              Nat.zero_add, Nat.one_mul]
            exact cellOneNeg c)
          (fun q => cartDoff l (q + 3) 0 (fun hx => Nat.noConfusion hx)
            (fun hk _ => absurd (hk.trans he3.symm)
              (fun hc => Nat.noConfusion (Nat.succ.inj
                (Nat.succ.inj (Nat.succ.inj hc)))))
            (fun _ hx _ => absurd
              ((show (1 : Nat) = l from hx).trans he3.symm) (by decide +kernel))
            (fun _ _ hx => Nat.noConfusion (Nat.succ.inj hx))
            (fun _ _ hx => Nat.noConfusion hx)) ?_
        show 2 * (if l ≤ 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take 1 W))
          = 2 * (ground.getAt 0 W 0 - ground.getAt 0 W 1)
            + ((if 1 < l then 1 * (if l ≤ 3 then ground.sumNat W
                  else 2 * ground.sumNat (List.take 2 W)) else 0)
              + (if 2 < l then 1 * (if l ≤ 4 then ground.sumNat W
                  else 2 * ground.sumNat (List.take 3 W)) else 0))
        rw [if_neg (fun hc => Nat.lt_irrefl l
            (Nat.lt_of_le_of_lt hc hl3)),
          if_pos h1l, if_pos (Nat.le_of_eq he3.symm), if_pos hl3,
          if_pos (Nat.le_trans (Nat.le_of_eq he3.symm) (Nat.le_succ 3)),
          takeOne W, sumHead W hlen, ground.getAt_over 0 W 1 hlen, subZero,
          Nat.one_mul,
          ← Nat.two_mul (ground.getAt 0 W 0),
          Nat.two_mul (2 * ground.getAt 0 W 0)]
      · have hl4 : 3 < l :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hl3) he3
        refine colDzero l h1l
          (fun k => if l ≤ k + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) 1 0 _
          (fun c => by
            rw [cartDdn l 0 (show ¬ 0 + 2 = l from hne2)
              (show ¬ 0 + 1 = l from hne1), Nat.one_mul]
            exact cellOneNeg c)
          (fun c => by
            rw [cartDoff l 2 0 (by decide +kernel)
              (fun _ hx => absurd (show (3 : Nat) = l from hx) (Nat.ne_of_lt hl4))
              (fun _ hx _ => absurd (show (1 : Nat) = l from hx) hne1)
              (fun _ _ hx => Nat.noConfusion (Nat.succ.inj hx))
              (fun _ _ hx => Nat.noConfusion hx), Nat.zero_mul]
            exact cellNull c)
          (fun q => cartDoff l (q + 3) 0 (fun hx => Nat.noConfusion hx)
            (fun _ hx => absurd (show (3 : Nat) = l from hx) (Nat.ne_of_lt hl4))
            (fun _ hx _ => absurd (show (1 : Nat) = l from hx) hne1)
            (fun _ _ hx => Nat.noConfusion (Nat.succ.inj hx))
            (fun _ _ hx => Nat.noConfusion hx)) ?_
        show 2 * (if l ≤ 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take 1 W))
          = 2 * (ground.getAt 0 W 0 - ground.getAt 0 W 1)
            + ((if 1 < l then 1 * (if l ≤ 3 then ground.sumNat W
                  else 2 * ground.sumNat (List.take 2 W)) else 0)
              + (if 2 < l then 0 * (if l ≤ 4 then ground.sumNat W
                  else 2 * ground.sumNat (List.take 3 W)) else 0))
        rw [if_neg (fun hc => Nat.lt_irrefl l
            (Nat.lt_of_le_of_lt hc hl3)),
          if_pos h1l,
          if_neg (fun hc => Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hl4)),
          if_pos hl3, Nat.zero_mul, Nat.add_zero, Nat.one_mul,
          takeStep W 1, takeOne W,
          ← Nat.left_distrib 2 (ground.getAt 0 W 0 - ground.getAt 0 W 1)
            (ground.getAt 0 W 0 + ground.getAt 0 W 1),
          ← arithB0 (ground.getAt 0 W 0) (ground.getAt 0 W 1)
            (ground.getAt 0 W 0 - ground.getAt 0 W 1) (ground.subAdd (hsa 0))]
  | succ m =>
    by_cases htop : m + 2 = l
    · cases m with
      | zero =>
        have hlen : W.length ≤ 0 := ground.leCancelR 2
          (show W.length + 2 ≤ 0 + 2 from
            Nat.le_trans hl (Nat.le_of_eq htop.symm))
        refine colDsimple l 1 hj
          (fun k => if l ≤ k + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_ ?_
        · intro k hk
          exact cartDoff l k 1 (fun hx => hk hx.symm)
            (fun _ hx => absurd
              ((show (4 : Nat) = l from hx).trans htop.symm) (by decide +kernel))
            (fun _ _ hx => absurd (hx.trans htop.symm)
              (fun hc => Nat.noConfusion (Nat.succ.inj
                (Nat.succ.inj hc))))
            (fun _ hb _ => absurd (show 1 + 1 = l from htop) hb)
            (fun _ hb _ => absurd (show 1 + 1 = l from htop) hb)
        · show 2 * (if l ≤ 1 + 2 then ground.sumNat W
              else 2 * ground.sumNat (List.take 2 W))
            = 2 * (ground.getAt 0 W 1 - ground.getAt 0 W 2) + 0
          rw [if_pos (Nat.le_trans (Nat.le_of_eq htop.symm)
              (Nat.le_succ 2)),
            sumNilOf W hlen, ground.getAt_over 0 W 1 (Nat.le_trans hlen
              (Nat.zero_le 1)),
            ground.getAt_over 0 W 2 (Nat.le_trans hlen (Nat.zero_le 2))]
      | succ q =>
        have ht : q + 3 = l := htop
        have hlen : W.length ≤ q + 1 := ground.leCancelR 2
          (show W.length + 2 ≤ q + 1 + 2 from
            Nat.le_trans hl (Nat.le_of_eq ht.symm))
        refine colDtop l q ht
          (fun k => if l ≤ k + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) _ ?_
        show 2 * (if l ≤ q + 2 + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (q + 3) W))
          = 2 * (ground.getAt 0 W (q + 2) - ground.getAt 0 W (q + 3))
            + (if q < l then (if l ≤ q + 2 then ground.sumNat W
                else 2 * ground.sumNat (List.take (q + 1) W)) else 0)
        rw [if_pos (Nat.le_trans (Nat.le_of_eq ht.symm)
            (Nat.le_succ (q + 3))),
          if_pos (ht ▸ ground.ltAddSucc q 2),
          if_neg (fun hc => Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc
            (ht ▸ Nat.lt_succ_self (q + 2)))),
          sumFull W q hlen,
          ground.getAt_over 0 W (q + 2) (Nat.le_trans hlen (Nat.le_succ (q + 1))),
          ground.getAt_over 0 W (q + 3) (Nat.le_trans hlen
            (Nat.le_trans (Nat.le_succ (q + 1)) (Nat.le_succ (q + 2)))),
          show (0 : Nat) - 0 = 0 from rfl, Nat.mul_zero, Nat.zero_add]
    · have hj2 : m + 2 < l := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) htop
      by_cases he3 : m + 3 = l
      · have hlen : W.length ≤ m + 1 := ground.leCancelR 2
          (show W.length + 2 ≤ m + 1 + 2 from
            Nat.le_trans hl (Nat.le_of_eq he3.symm))
        refine colDmid l m hj2
          (fun k => if l ≤ k + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (k + 1) W)) 0 0 _
          (fun c => by
            rw [cartDoff l (m + 2) (m + 1) (neAdd (m + 1) 0)
              (fun _ hx => (neAdd (m + 3) 0
                (hx.trans he3.symm).symm))
              (fun hb _ => absurd (show m + 2 + 1 = l from he3) hb)
              (fun hb _ => absurd (show m + 2 + 1 = l from he3) hb)
              (fun hb _ => absurd (show m + 2 + 1 = l from he3) hb),
              Nat.zero_mul]
            exact cellNull c)
          (fun c => by
            rw [cartDoff l (m + 3) (m + 1) (neAdd (m + 1) 1)
              (fun hk _ => absurd (hk.trans he3.symm).symm
                (neAdd (m + 3) 0))
              (fun _ hx => absurd (hx.trans he3.symm) (neAdd (m + 2) 0))
              (fun _ _ => neAdd (m + 2) 0)
              (fun _ _ => neAdd (m + 1) 2), Nat.zero_mul]
            exact cellNull c) ?_
        show 2 * (if l ≤ m + 1 + 2 then ground.sumNat W
            else 2 * ground.sumNat (List.take (m + 2) W))
          = 2 * (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
            + ((if m < l then (if l ≤ m + 2 then ground.sumNat W
                  else 2 * ground.sumNat (List.take (m + 1) W)) else 0)
              + ((if m + 2 < l then 0 * (if l ≤ m + 2 + 2
                    then ground.sumNat W
                    else 2 * ground.sumNat (List.take (m + 3) W))
                  else 0)
                + (if m + 3 < l then 0 * (if l ≤ m + 3 + 2
                      then ground.sumNat W
                      else 2 * ground.sumNat (List.take (m + 4) W))
                  else 0)))
        rw [if_pos (Nat.le_of_eq he3.symm),
          if_pos (Nat.lt_trans (Nat.lt_succ_self m) hj),
          if_neg (fun hc => Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hj2)),
          if_pos hj2,
          if_neg (fun hc => Nat.lt_irrefl (m + 3)
            (Nat.lt_of_lt_of_le hc (Nat.le_of_eq he3.symm))),
          Nat.zero_mul, sumFull W m hlen,
          ground.getAt_over 0 W (m + 1) hlen,
          ground.getAt_over 0 W (m + 2) (Nat.le_trans hlen (Nat.le_succ (m + 1))),
          show (0 : Nat) - 0 = 0 from rfl, Nat.mul_zero, Nat.zero_add]
        rfl
      · have hj3 : m + 3 < l :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj2) he3
        have hne3 : ¬ m + 1 + 2 = l := Nat.ne_of_lt hj3
        have hne2 : ¬ m + 1 + 1 = l := Nat.ne_of_lt hj2
        have hle3 : ¬ l ≤ m + 1 + 2 := fun hc =>
          Nat.lt_irrefl l (Nat.lt_of_le_of_lt hc hj3)
        by_cases he4 : m + 4 = l
        · have hlen : W.length ≤ m + 2 := ground.leCancelR 2
            (show W.length + 2 ≤ m + 2 + 2 from
              Nat.le_trans hl (Nat.le_of_eq he4.symm))
          refine colDmid l m hj2
            (fun k => if l ≤ k + 2 then ground.sumNat W
              else 2 * ground.sumNat (List.take (k + 1) W)) 1 1 _
            (fun c => by
              rw [cartDdn l (m + 1) hne3 hne2, Nat.zero_add, Nat.one_mul]
              exact cellOneNeg c)
            (fun c => by
              rw [cartDfork l (m + 3) (m + 1) (neAdd (m + 1) 1)
                (show m + 3 + 1 = l from he4)
                (show m + 1 + 3 = l from he4),
                Nat.zero_add, Nat.zero_add, Nat.one_mul]
              exact cellOneNeg c) ?_
          show 2 * (if l ≤ m + 1 + 2 then ground.sumNat W
              else 2 * ground.sumNat (List.take (m + 2) W))
            = 2 * (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
              + ((if m < l then (if l ≤ m + 2 then ground.sumNat W
                    else 2 * ground.sumNat (List.take (m + 1) W)) else 0)
                + ((if m + 2 < l then 1 * (if l ≤ m + 2 + 2
                      then ground.sumNat W
                      else 2 * ground.sumNat (List.take (m + 3) W))
                    else 0)
                  + (if m + 3 < l then 1 * (if l ≤ m + 3 + 2
                        then ground.sumNat W
                        else 2 * ground.sumNat (List.take (m + 4) W))
                    else 0)))
          rw [if_neg hle3,
            if_pos (Nat.lt_trans (Nat.lt_succ_self m) hj),
            if_neg (fun hc => Nat.lt_irrefl l
              (Nat.lt_of_le_of_lt hc hj2)),
            if_pos hj2, if_pos (Nat.le_of_eq he4.symm),
            if_pos hj3,
            if_pos (Nat.le_trans (Nat.le_of_eq he4.symm)
              (Nat.le_succ (m + 4))),
            ground.getAt_over 0 W (m + 2) hlen, subZero, Nat.one_mul,
            ← sumFull W (m + 1) hlen, takeStep W (m + 1),
            ← Nat.two_mul (ground.sumNat (List.take (m + 1) W)
              + ground.getAt 0 W (m + 1)),
            ← Nat.left_distrib 2 (ground.sumNat (List.take (m + 1) W))
              (ground.sumNat (List.take (m + 1) W)
                + ground.getAt 0 W (m + 1)),
            ← Nat.left_distrib 2 (ground.getAt 0 W (m + 1))
              (ground.sumNat (List.take (m + 1) W)
                + (ground.sumNat (List.take (m + 1) W)
                  + ground.getAt 0 W (m + 1))),
            ← arithD3 (ground.sumNat (List.take (m + 1) W))
              (ground.getAt 0 W (m + 1))]
        · have hj4 : m + 4 < l :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj3) he4
          refine colDmid l m hj2
            (fun k => if l ≤ k + 2 then ground.sumNat W
              else 2 * ground.sumNat (List.take (k + 1) W)) 1 0 _
            (fun c => by
              rw [cartDdn l (m + 1) hne3 hne2, Nat.zero_add, Nat.one_mul]
              exact cellOneNeg c)
            (fun c => by
              rw [cartDoff l (m + 3) (m + 1) (neAdd (m + 1) 1)
                (fun hk => absurd (show m + 4 = l from hk) (Nat.ne_of_lt hj4))
                (fun _ hx => absurd (show m + 2 = l from hx) (Nat.ne_of_lt hj2))
                (fun _ _ => neAdd (m + 2) 0)
                (fun _ _ => neAdd (m + 1) 2), Nat.zero_mul]
              exact cellNull c) ?_
          show 2 * (if l ≤ m + 1 + 2 then ground.sumNat W
              else 2 * ground.sumNat (List.take (m + 2) W))
            = 2 * (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
              + ((if m < l then (if l ≤ m + 2 then ground.sumNat W
                    else 2 * ground.sumNat (List.take (m + 1) W)) else 0)
                + ((if m + 2 < l then 1 * (if l ≤ m + 2 + 2
                      then ground.sumNat W
                      else 2 * ground.sumNat (List.take (m + 3) W))
                    else 0)
                  + (if m + 3 < l then 0 * (if l ≤ m + 3 + 2
                        then ground.sumNat W
                        else 2 * ground.sumNat (List.take (m + 4) W))
                    else 0)))
          rw [if_neg hle3,
            if_pos (Nat.lt_trans (Nat.lt_succ_self m) hj),
            if_neg (fun hc => Nat.lt_irrefl l
              (Nat.lt_of_le_of_lt hc hj2)),
            if_pos hj2,
            if_neg (fun hc => Nat.lt_irrefl l
              (Nat.lt_of_le_of_lt hc hj4)),
            if_pos hj3, Nat.zero_mul, Nat.one_mul,
            Nat.add_zero (2 * ground.sumNat (List.take (m + 3) W)),
            takeStep W (m + 2), takeStep W (m + 1),
            ← Nat.left_distrib 2 (ground.sumNat (List.take (m + 1) W))
              (ground.sumNat (List.take (m + 1) W)
                + ground.getAt 0 W (m + 1) + ground.getAt 0 W (m + 2)),
            ← Nat.left_distrib 2
              (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
              (ground.sumNat (List.take (m + 1) W)
                + (ground.sumNat (List.take (m + 1) W)
                  + ground.getAt 0 W (m + 1)
                  + ground.getAt 0 W (m + 2))),
            ← arithBmid (ground.sumNat (List.take (m + 1) W))
              (ground.getAt 0 W (m + 1)) (ground.getAt 0 W (m + 2))
              (ground.getAt 0 W (m + 1) - ground.getAt 0 W (m + 2))
              (ground.subAdd (hsa (m + 1)))]

/-! ## The range-fold kit -/

private theorem foldRangeSplit (f : Nat → Nat) (m : Nat) : ∀ n : Nat,
    ground.famFold Nat.add 0 f (List.range (m + n))
      = ground.famFold Nat.add 0 f (List.range m)
        + ground.famFold Nat.add 0 (fun e => f (m + e)) (List.range n)
  | 0 => (Nat.add_zero _).symm
  | n + 1 => by
    rw [show m + (n + 1) = m + n + 1 from rfl,
      ground.range_succ (m + n),
      ground.famFold_snoc f (List.range (m + n)) (m + n),
      foldRangeSplit f m n, ground.range_succ n,
      ground.famFold_snoc (fun e => f (m + e)) (List.range n) n,
      Nat.add_assoc]

private theorem foldConst (c : Nat) : ∀ n : Nat,
    ground.famFold Nat.add 0 (fun _ => c) (List.range n) = c * n :=
  fun n => by
    rw [ground.famFold_const c (List.range n), ground.length_range n,
      Nat.mul_comm n c]

private theorem foldId : ∀ n : Nat,
    2 * ground.famFold Nat.add 0 (fun d => d) (List.range (n + 1))
      = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    rw [ground.range_succ (n + 1),
      ground.famFold_snoc (fun d => d) (List.range (n + 1)) (n + 1),
      Nat.left_distrib, foldId n, ← ground.mulAddR n 2 (n + 1),
      Nat.mul_comm (n + 2) (n + 1)]

/-- The count of the keys at or below a bound inside a range. -/
private theorem cntLe (k : Nat) : ∀ d : Nat, k < d →
    ground.famFold Nat.add 0 (fun j => if j ≤ k then 1 else 0)
      (List.range d) = k + 1 := by
  intro d hk
  match Nat.le.dest hk with
  | ⟨e, he⟩ =>
    rw [← he, foldRangeSplit _ (k + 1) e,
      ground.famFold_congr_range (fun j => if j ≤ k then 1 else 0) (fun _ => 1)
        (k + 1) (fun x hx => if_pos (Nat.le_of_lt_succ hx)),
      foldConst 1 (k + 1),
      ground.famFold_congr_range (fun e' => if k + 1 + e' ≤ k then 1 else 0)
        (fun _ => 0) e (fun x _ => if_neg (fun hc =>
          Nat.lt_irrefl k (Nat.lt_of_lt_of_le (ground.ltAddSucc k 0)
            (Nat.le_trans (Nat.le_add_right (k + 1) x) hc)))),
      foldConst 0 e, Nat.one_mul, Nat.zero_mul, Nat.add_zero]


private theorem cntGt (k c : Nat) : ∀ r : Nat,
    ground.famFold Nat.add 0 (fun d => if k < d then c else 0)
      (List.range r) = c * (r - (k + 1)) := by
  intro r
  by_cases hr : k + 1 ≤ r
  · match Nat.le.dest hr with
    | ⟨e, he⟩ =>
      rw [← he, foldRangeSplit _ (k + 1) e,
        ground.famFold_congr_range (fun d => if k < d then c else 0) (fun _ => 0)
          (k + 1) (fun x hx => if_neg (fun hc =>
            Nat.lt_irrefl k (Nat.lt_of_lt_of_le hc
              (Nat.le_of_lt_succ hx)))),
        foldConst 0 (k + 1),
        ground.famFold_congr_range (fun e' => if k < k + 1 + e' then c else 0)
          (fun _ => c) e (fun x _ => if_pos
            (Nat.lt_of_lt_of_le (ground.ltAddSucc k 0)
              (Nat.le_add_right (k + 1) x))),
        foldConst c e, Nat.zero_mul, Nat.zero_add,
        show k + 1 + e - (k + 1) = e from by
          rw [Nat.add_comm (k + 1) e, ground.addSubSelfR e (k + 1)]]
  · rw [ground.famFold_congr_range (fun d => if k < d then c else 0) (fun _ => 0) r
        (fun x hx => if_neg (fun hc => hr (Nat.le_trans hc
          (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hx))))),
      foldConst 0 r, Nat.zero_mul,
      ground.subLe r (k + 1) (Nat.le_of_not_le hr), Nat.mul_zero]

/-- The weighted count of the keys at or below a bound. -/
private theorem sumLe (k : Nat) : ∀ r : Nat, k < r →
    2 * ground.famFold Nat.add 0 (fun d => if d ≤ k then d else 0)
      (List.range r) = k * (k + 1) := by
  intro r hk
  match Nat.le.dest hk with
  | ⟨e, he⟩ =>
    rw [← he, foldRangeSplit _ (k + 1) e,
      ground.famFold_congr_range (fun d => if d ≤ k then d else 0) (fun d => d)
        (k + 1) (fun x hx => if_pos (Nat.le_of_lt_succ hx)),
      ground.famFold_congr_range (fun e' => if k + 1 + e' ≤ k then k + 1 + e' else 0)
        (fun _ => 0) e (fun x _ => if_neg (fun hc =>
          Nat.lt_irrefl k (Nat.lt_of_lt_of_le (ground.ltAddSucc k 0)
            (Nat.le_trans (Nat.le_add_right (k + 1) x) hc)))),
      foldConst 0 e, Nat.zero_mul, Nat.add_zero, foldId k]

/-! ## The root fold's columnwise reads -/

private theorem zipLen : ∀ (k : Nat) (a b : List Nat),
    k < a.length → k < b.length →
    k < (List.zipWith (fun x y => x + y) a b).length
  | _, [], _, ha, _ => absurd ha (Nat.not_lt_zero _)
  | _, _ :: _, [], _, hb => absurd hb (Nat.not_lt_zero _)
  | 0, _ :: _, _ :: _, _, _ => Nat.zero_lt_succ _
  | k + 1, _ :: s, _ :: t, ha, hb =>
    Nat.succ_lt_succ (zipLen k s t (Nat.lt_of_succ_lt_succ ha)
      (Nat.lt_of_succ_lt_succ hb))

private theorem mapFoldLen (k : Nat) {α : Type} (G : α → List Nat)
    (hG : ∀ x, k < (G x).length) :
    ∀ (P : List α) (acc : List Nat), k < acc.length →
    k < ((P.map G).foldl
      (fun a f => List.zipWith (fun x y => x + y) a f) acc).length
  | [], _, h => h
  | x :: P, acc, h =>
    mapFoldLen k G hG P _ (zipLen k acc (G x) h (hG x))

private theorem mapFoldAt (k : Nat) {α : Type} (G : α → List Nat)
    (hG : ∀ x, k < (G x).length) :
    ∀ (P : List α) (acc : List Nat), k < acc.length →
    ground.getAt 0 ((P.map G).foldl
        (fun a f => List.zipWith (fun x y => x + y) a f) acc) k
      = ground.getAt 0 acc k
        + ground.famFold Nat.add 0
            (fun x => ground.getAt 0 (G x) k) P
  | [], _, _ => (Nat.add_zero _).symm
  | x :: P, acc, h => by
    show ground.getAt 0 ((P.map G).foldl
      (fun a f => List.zipWith (fun x y => x + y) a f)
      (List.zipWith (fun x y => x + y) acc (G x))) k = _
    rw [mapFoldAt k G hG P _ (zipLen k acc (G x) h (hG x)),
      ground.getAt_zipWith 0 0 0 (fun x y => x + y) acc (G x) k h (hG x),
      Nat.add_assoc]
    rfl

/-! ## The list-fold and dot reads -/

private theorem dotIndex : ∀ (X Y : List Nat),
    ground.dotNat X Y
      = ground.famFold Nat.add 0
          (fun i => ground.getAt 0 X i * ground.getAt 0 Y i)
          (List.range X.length)
  | [], _ => rfl
  | a :: s, [] => by
    show (0 : Nat) = ground.famFold Nat.add 0
      (fun i => ground.getAt 0 (a :: s) i
        * ground.getAt 0 ([] : List Nat) i) (List.range (s.length + 1))
    rw [ground.famFold_congr_range
      (fun i => ground.getAt 0 (a :: s) i * ground.getAt 0 ([] : List Nat) i)
      (fun _ => 0) (s.length + 1) (fun x _ => by
        show ground.getAt 0 (a :: s) x * ground.getAt 0 ([] : List Nat) x = 0
        rw [ground.getAt_over 0 ([] : List Nat) x (Nat.zero_le x),
          Nat.mul_zero]),
      foldConst 0 (s.length + 1), Nat.zero_mul]
  | a :: s, b :: t => by
    show a * b + ground.dotNat s t = ground.famFold Nat.add 0
      (fun i => ground.getAt 0 (a :: s) i * ground.getAt 0 (b :: t) i)
      (List.range (s.length + 1))
    rw [ground.famFold_range_cons Nat.add 0 (fun i => ground.getAt 0 (a :: s) i
        * ground.getAt 0 (b :: t) i) s.length,
      dotIndex s t]
    rfl

/-! ## The occupancy windows of the root families -/

private theorem iteB {α : Type} (P : Prop) [Decidable P] (x y : α) :
    (if decide P = true then x else y) = if P then x else y := by
  by_cases h : P
  · rw [if_pos (decide_eq_true h), if_pos h]
  · rw [if_neg (fun hc => h (of_decide_eq_true hc)), if_neg h]

private theorem indValIn (a b k : Nat) (h : k < b) :
    (if a ≤ k && k < b then (1 : Nat) else 0) = if a ≤ k then 1 else 0 := by
  show (if (decide (a ≤ k) && decide (k < b)) = true then (1 : Nat) else 0)
    = _
  rw [decide_eq_true h, andT, iteB (a ≤ k) (1 : Nat) 0]

private theorem indValOut (a b k : Nat) (h : ¬ k < b) :
    (if a ≤ k && k < b then (1 : Nat) else 0) = 0 := by
  show (if (decide (a ≤ k) && decide (k < b)) = true then (1 : Nat) else 0)
    = _
  rw [decide_eq_false h, andF]
  rfl

private theorem indValLo (a b k : Nat) (h : ¬ a ≤ k) :
    (if a ≤ k && k < b then (1 : Nat) else 0) = 0 := by
  show (if (decide (a ≤ k) && decide (k < b)) = true then (1 : Nat) else 0)
    = _
  rw [decide_eq_false h]
  rfl

/-! ## The pair-family counts at a key -/

/-- The difference family's count at a key. -/
private theorem diffCount (l k : Nat) :
    ground.famFold Nat.add 0
      (fun p => if p.1 ≤ k && k < p.2 then (1 : Nat) else 0)
      (places.pairsOf l) = (k + 1) * (l - (k + 1)) := by
  rw [places.pairsFold_free _ l,
    ground.famFold_congr_range _ (fun d => if k < d then k + 1 else 0) l (fun d _ => by
      by_cases hd : k < d
      · rw [if_pos hd,
          ground.famFold_congr_range _ (fun j => if j ≤ k then (1 : Nat) else 0) d
            (fun j _ => indValIn j d k hd),
          cntLe k d hd]
      · rw [if_neg hd,
          ground.famFold_congr_range _ (fun _ => (0 : Nat)) d
            (fun j _ => indValOut j d k hd),
          foldConst 0 d, Nat.zero_mul]),
    cntGt k (k + 1) l]

/-- The upper-window family's doubled count at a key. -/
private theorem topCnt (l k : Nat) (hk : k < l) :
    ground.famFold Nat.add 0
      (fun p => if p.2 ≤ k then (1 : Nat) else 0) (places.pairsOf l)
    + ground.famFold Nat.add 0
      (fun p => if p.2 ≤ k then (1 : Nat) else 0) (places.pairsOf l)
      = k * (k + 1) := by
  have hone : ground.famFold Nat.add 0
      (fun p => if p.2 ≤ k then (1 : Nat) else 0) (places.pairsOf l)
      = ground.famFold Nat.add 0
        (fun d => if d ≤ k then d else 0) (List.range l) := by
    rw [places.pairsFold_free _ l]
    refine ground.famFold_congr_range _ (fun d => if d ≤ k then d else 0) l
      (fun d _ => ?_)
    by_cases hd : d ≤ k
    · rw [if_pos hd,
        ground.famFold_congr_range _ (fun _ => (1 : Nat)) d
          (fun _ _ => if_pos hd),
        foldConst 1 d, Nat.one_mul]
    · rw [if_neg hd,
        ground.famFold_congr_range _ (fun _ => (0 : Nat)) d
          (fun _ _ => if_neg hd),
        foldConst 0 d, Nat.zero_mul]
  rw [hone, ← Nat.two_mul, sumLe k l hk]

/-! ## The root families' entries and widths -/

private theorem zipLen2 (u v : List Nat) (n : Nat) (hu : u.length = n)
    (hv : v.length = n) :
    (List.zipWith (fun x y => x + y) u v).length = n :=
  ground.length_zipWith (fun x y => x + y) u v n hu hv

private theorem zipAt2 (u v : List Nat) (k n : Nat) (hu : u.length = n)
    (hv : v.length = n) (hk : k < n) :
    ground.getAt 0 (List.zipWith (fun x y => x + y) u v) k
      = ground.getAt 0 u k + ground.getAt 0 v k :=
  ground.getAt_zipWith 0 0 0 (fun x y => x + y) u v k
    (by rw [hu]; exact hk) (by rw [hv]; exact hk)

private theorem diffLen (l a b : Nat) :
    (sertables.diffFold l a b).length = l := sertables.ind_len l a b

private theorem diffAt (l a b k : Nat) (hk : k < l) :
    ground.getAt 0 (sertables.diffFold l a b) k
      = if a ≤ k && k < b then 1 else 0 := sertables.ind_at l a b k hk

private theorem sumBLen (l a b : Nat) :
    (sertables.sumFoldB l a b).length = l :=
  zipLen2 (sertables.ind l a b)
    (List.zipWith (fun x y => x + y) (sertables.ind l b l) (sertables.ind l b l)) l
    (sertables.ind_len l a b)
    (zipLen2 (sertables.ind l b l) (sertables.ind l b l) l (sertables.ind_len l b l) (sertables.ind_len l b l))

private theorem sumBAt (l a b k : Nat) (hk : k < l) :
    ground.getAt 0 (sertables.sumFoldB l a b) k
      = (if a ≤ k && k < b then 1 else 0)
        + ((if b ≤ k && k < l then 1 else 0)
          + (if b ≤ k && k < l then 1 else 0)) := by
  show ground.getAt 0 (List.zipWith (fun x y => x + y) (sertables.ind l a b)
    (List.zipWith (fun x y => x + y) (sertables.ind l b l) (sertables.ind l b l))) k = _
  rw [zipAt2 (sertables.ind l a b)
      (List.zipWith (fun x y => x + y) (sertables.ind l b l) (sertables.ind l b l)) k l
      (sertables.ind_len l a b)
      (zipLen2 (sertables.ind l b l) (sertables.ind l b l) l (sertables.ind_len l b l) (sertables.ind_len l b l))
      hk,
    zipAt2 (sertables.ind l b l) (sertables.ind l b l) k l (sertables.ind_len l b l) (sertables.ind_len l b l) hk,
    sertables.ind_at l a b k hk, sertables.ind_at l b l k hk]

private theorem shortLen (l a : Nat) :
    (sertables.shortFold l a).length = l := sertables.ind_len l a l

private theorem shortAt (l a k : Nat) (hk : k < l) :
    ground.getAt 0 (sertables.shortFold l a) k
      = if a ≤ k && k < l then 1 else 0 := sertables.ind_at l a l k hk

private theorem sumCLen (l a b : Nat) :
    (sertables.sumFoldC l a b).length = l :=
  zipLen2 (sertables.ind l a b) _ l (sertables.ind_len l a b)
    (zipLen2 _ (sertables.ind l (l - 1) l) l
      (zipLen2 (sertables.ind l b (l - 1)) (sertables.ind l b (l - 1)) l
        (sertables.ind_len l b (l - 1)) (sertables.ind_len l b (l - 1)))
      (sertables.ind_len l (l - 1) l))

private theorem sumCAt (l a b k : Nat) (hk : k < l) :
    ground.getAt 0 (sertables.sumFoldC l a b) k
      = (if a ≤ k && k < b then 1 else 0)
        + (((if b ≤ k && k < l - 1 then 1 else 0)
            + (if b ≤ k && k < l - 1 then 1 else 0))
          + (if l - 1 ≤ k && k < l then 1 else 0)) := by
  show ground.getAt 0 (List.zipWith (fun x y => x + y) (sertables.ind l a b)
    (List.zipWith (fun x y => x + y)
      (List.zipWith (fun x y => x + y) (sertables.ind l b (l - 1)) (sertables.ind l b (l - 1)))
      (sertables.ind l (l - 1) l))) k = _
  rw [zipAt2 (sertables.ind l a b) _ k l (sertables.ind_len l a b)
      (zipLen2 _ (sertables.ind l (l - 1) l) l
        (zipLen2 (sertables.ind l b (l - 1)) (sertables.ind l b (l - 1)) l
          (sertables.ind_len l b (l - 1)) (sertables.ind_len l b (l - 1)))
        (sertables.ind_len l (l - 1) l)) hk,
    zipAt2 _ (sertables.ind l (l - 1) l) k l
      (zipLen2 (sertables.ind l b (l - 1)) (sertables.ind l b (l - 1)) l
        (sertables.ind_len l b (l - 1)) (sertables.ind_len l b (l - 1)))
      (sertables.ind_len l (l - 1) l) hk,
    zipAt2 (sertables.ind l b (l - 1)) (sertables.ind l b (l - 1)) k l
      (sertables.ind_len l b (l - 1)) (sertables.ind_len l b (l - 1)) hk,
    sertables.ind_at l a b k hk, sertables.ind_at l b (l - 1) k hk, sertables.ind_at l (l - 1) l k hk]

private theorem longLen (l a : Nat) :
    (sertables.longFold l a).length = l :=
  zipLen2 _ (sertables.ind l (l - 1) l) l
    (zipLen2 (sertables.ind l a (l - 1)) (sertables.ind l a (l - 1)) l
      (sertables.ind_len l a (l - 1)) (sertables.ind_len l a (l - 1)))
    (sertables.ind_len l (l - 1) l)

private theorem longAt (l a k : Nat) (hk : k < l) :
    ground.getAt 0 (sertables.longFold l a) k
      = ((if a ≤ k && k < l - 1 then 1 else 0)
          + (if a ≤ k && k < l - 1 then 1 else 0))
        + (if l - 1 ≤ k && k < l then 1 else 0) := by
  show ground.getAt 0 (List.zipWith (fun x y => x + y)
    (List.zipWith (fun x y => x + y) (sertables.ind l a (l - 1)) (sertables.ind l a (l - 1)))
    (sertables.ind l (l - 1) l)) k = _
  rw [zipAt2 _ (sertables.ind l (l - 1) l) k l
      (zipLen2 (sertables.ind l a (l - 1)) (sertables.ind l a (l - 1)) l
        (sertables.ind_len l a (l - 1)) (sertables.ind_len l a (l - 1)))
      (sertables.ind_len l (l - 1) l) hk,
    zipAt2 (sertables.ind l a (l - 1)) (sertables.ind l a (l - 1)) k l
      (sertables.ind_len l a (l - 1)) (sertables.ind_len l a (l - 1)) hk,
    sertables.ind_at l a (l - 1) k hk, sertables.ind_at l (l - 1) l k hk]

private theorem sumDLen (l a b : Nat) :
    (sertables.sumFoldD l a b).length = l := by
  show List.length (if (b + 1 == l) = true then
      List.zipWith (fun x y => x + y) (sertables.ind l a (l - 2)) (sertables.ind l (l - 1) l)
    else
      List.zipWith (fun x y => x + y) (sertables.ind l a b)
        (List.zipWith (fun x y => x + y)
          (List.zipWith (fun x y => x + y) (sertables.ind l b (l - 2))
            (sertables.ind l b (l - 2)))
          (sertables.ind l (l - 2) l))) = l
  cases hb : (b + 1 == l) with
  | true =>
    exact zipLen2 (sertables.ind l a (l - 2)) (sertables.ind l (l - 1) l) l
      (sertables.ind_len l a (l - 2)) (sertables.ind_len l (l - 1) l)
  | false =>
    exact zipLen2 (sertables.ind l a b) _ l (sertables.ind_len l a b)
      (zipLen2 _ (sertables.ind l (l - 2) l) l
        (zipLen2 (sertables.ind l b (l - 2)) (sertables.ind l b (l - 2)) l
          (sertables.ind_len l b (l - 2)) (sertables.ind_len l b (l - 2)))
        (sertables.ind_len l (l - 2) l))

private theorem sumDAtTop (l a b k : Nat) (hk : k < l) (hb : b + 1 = l) :
    ground.getAt 0 (sertables.sumFoldD l a b) k
      = (if a ≤ k && k < l - 2 then 1 else 0)
        + (if l - 1 ≤ k && k < l then 1 else 0) := by
  show ground.getAt 0 (if (b + 1 == l) = true then _ else _) k = _
  rw [ground.eqBeqOf hb]
  show ground.getAt 0 (List.zipWith (fun x y => x + y)
    (sertables.ind l a (l - 2)) (sertables.ind l (l - 1) l)) k = _
  rw [zipAt2 (sertables.ind l a (l - 2)) (sertables.ind l (l - 1) l) k l
      (sertables.ind_len l a (l - 2)) (sertables.ind_len l (l - 1) l) hk,
    sertables.ind_at l a (l - 2) k hk, sertables.ind_at l (l - 1) l k hk]

private theorem sumDAtGen (l a b k : Nat) (hk : k < l) (hb : ¬ b + 1 = l) :
    ground.getAt 0 (sertables.sumFoldD l a b) k
      = (if a ≤ k && k < b then 1 else 0)
        + (((if b ≤ k && k < l - 2 then 1 else 0)
            + (if b ≤ k && k < l - 2 then 1 else 0))
          + (if l - 2 ≤ k && k < l then 1 else 0)) := by
  show ground.getAt 0 (if (b + 1 == l) = true then _ else _) k = _
  rw [ground.neBeqOf hb]
  show ground.getAt 0 (List.zipWith (fun x y => x + y) (sertables.ind l a b)
    (List.zipWith (fun x y => x + y)
      (List.zipWith (fun x y => x + y) (sertables.ind l b (l - 2)) (sertables.ind l b (l - 2)))
      (sertables.ind l (l - 2) l))) k = _
  rw [zipAt2 (sertables.ind l a b) _ k l (sertables.ind_len l a b)
      (zipLen2 _ (sertables.ind l (l - 2) l) l
        (zipLen2 (sertables.ind l b (l - 2)) (sertables.ind l b (l - 2)) l
          (sertables.ind_len l b (l - 2)) (sertables.ind_len l b (l - 2)))
        (sertables.ind_len l (l - 2) l)) hk,
    zipAt2 _ (sertables.ind l (l - 2) l) k l
      (zipLen2 (sertables.ind l b (l - 2)) (sertables.ind l b (l - 2)) l
        (sertables.ind_len l b (l - 2)) (sertables.ind_len l b (l - 2)))
      (sertables.ind_len l (l - 2) l) hk,
    zipAt2 (sertables.ind l b (l - 2)) (sertables.ind l b (l - 2)) k l
      (sertables.ind_len l b (l - 2)) (sertables.ind_len l b (l - 2)) hk,
    sertables.ind_at l a b k hk, sertables.ind_at l b (l - 2) k hk, sertables.ind_at l (l - 2) l k hk]

/-! ## The root fold's key reads -/

private theorem rhoBAt (l k : Nat) (hk : k < l) :
    ground.getAt 0 (casfloor.rhoFold (sertables.tableB l)) k
      = 0 + (k + 1) * (l - (k + 1))
        + ((k + 1) * (l - (k + 1)) + k * (k + 1)) + (k + 1) := by
  have h0 : k < (List.replicate l 0).length := by
    rw [ground.length_replicate]; exact hk
  have hG1 : ∀ p : Nat × Nat, k < (sertables.diffFold l p.1 p.2).length :=
    fun p => by rw [diffLen]; exact hk
  have hG2 : ∀ p : Nat × Nat, k < (sertables.sumFoldB l p.1 p.2).length :=
    fun p => by rw [sumBLen]; exact hk
  have hG3 : ∀ a : Nat, k < (sertables.shortFold l a).length :=
    fun a => by rw [shortLen]; exact hk
  have hacc1 := mapFoldLen k (fun p : Nat × Nat =>
    sertables.diffFold l p.1 p.2) hG1 (places.pairsOf l)
    (List.replicate l 0) h0
  have hacc2 := mapFoldLen k (fun p : Nat × Nat =>
    sertables.sumFoldB l p.1 p.2) hG2 (places.pairsOf l) _ hacc1
  show ground.getAt 0 ((sertables.foldsB l).foldl
    (fun a f => List.zipWith (fun x y => x + y) a f)
    (List.replicate l 0)) k = _
  rw [show sertables.foldsB l
      = ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
        ++ ((places.pairsOf l).map (fun p => sertables.sumFoldB l p.1 p.2)))
          ++ ((List.range l).map (sertables.shortFold l)) from rfl,
    ground.foldl_append (fun a f => List.zipWith (fun x y => x + y) a f)
      ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
        ++ (places.pairsOf l).map (fun p => sertables.sumFoldB l p.1 p.2))
      _ _,
    ground.foldl_append (fun a f => List.zipWith (fun x y => x + y) a f)
      ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)) _ _,
    mapFoldAt k (sertables.shortFold l) hG3 (List.range l) _ hacc2,
    mapFoldAt k (fun p : Nat × Nat => sertables.sumFoldB l p.1 p.2) hG2
      (places.pairsOf l) _ hacc1,
    mapFoldAt k (fun p : Nat × Nat => sertables.diffFold l p.1 p.2) hG1
      (places.pairsOf l) _ h0,
    ground.getAt_replicate_zero l k,
    ground.famFold_congr_all Nat.add 0
      (fun p : Nat × Nat => ground.getAt 0 (sertables.diffFold l p.1 p.2) k)
      (fun p => if p.1 ≤ k && k < p.2 then 1 else 0)
      (fun p => diffAt l p.1 p.2 k hk) (places.pairsOf l),
    diffCount l k,
    ground.famFold_congr_all Nat.add 0
      (fun p : Nat × Nat => ground.getAt 0 (sertables.sumFoldB l p.1 p.2) k)
      (fun p => (if p.1 ≤ k && k < p.2 then 1 else 0)
        + ((if p.2 ≤ k then 1 else 0) + (if p.2 ≤ k then 1 else 0)))
      (fun p => by
        rw [sumBAt l p.1 p.2 k hk, indValIn p.2 l k hk])
      (places.pairsOf l),
    ground.famFold_add_split
      (fun p : Nat × Nat => if p.1 ≤ k && k < p.2 then 1 else 0)
      (fun p => (if p.2 ≤ k then 1 else 0) + (if p.2 ≤ k then 1 else 0))
      (places.pairsOf l),
    diffCount l k,
    ground.famFold_add_split
      (fun p : Nat × Nat => if p.2 ≤ k then (1 : Nat) else 0)
      (fun p => if p.2 ≤ k then (1 : Nat) else 0) (places.pairsOf l),
    topCnt l k hk,
    ground.famFold_congr_all Nat.add 0
      (fun a => ground.getAt 0 (sertables.shortFold l a) k)
      (fun a => if a ≤ k then 1 else 0)
      (fun a => by rw [shortAt l a k hk, indValIn a l k hk])
      (List.range l),
    cntLe k l hk]

private theorem foldZero {α : Type} : ∀ L : List α,
    ground.famFold Nat.add 0 (fun _ => (0 : Nat)) L = 0 :=
  fun L => (ground.famFold_const 0 L).trans (Nat.mul_zero L.length)

private theorem subOneGe : ∀ (a l : Nat), a + 1 ≤ l → a ≤ l - 1
  | _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _, _ + 1, h => Nat.le_of_succ_le_succ h

private theorem subTwoGe : ∀ (a l : Nat), a + 2 ≤ l → a ≤ l - 2
  | _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _, 1, h => absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero _)
  | _, _ + 2, h => Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h)

private theorem rhoCAt (l k : Nat) (hk3 : k + 3 ≤ l) :
    ground.getAt 0 (casfloor.rhoFold (sertables.tableC l)) k
      = 0 + (k + 1) * (l - (k + 1))
        + ((k + 1) * (l - (k + 1)) + (k * (k + 1) + 0))
        + ((k + 1) + (k + 1) + 0) := by
  have hk : k < l := Nat.lt_of_lt_of_le (ground.ltAddSucc k 2) hk3
  have hk1 : k < l - 1 :=
    subOneGe (k + 1) l (Nat.le_trans
      (show k + 1 + 1 ≤ k + 3 from Nat.le_succ (k + 2)) hk3)
  have hlo : ¬ l - 1 ≤ k := fun hc => Nat.lt_irrefl k
    (Nat.lt_of_lt_of_le hk1 hc)
  have h0 : k < (List.replicate l 0).length := by
    rw [ground.length_replicate]; exact hk
  have hG1 : ∀ p : Nat × Nat, k < (sertables.diffFold l p.1 p.2).length :=
    fun p => by rw [diffLen]; exact hk
  have hG2 : ∀ p : Nat × Nat, k < (sertables.sumFoldC l p.1 p.2).length :=
    fun p => by rw [sumCLen]; exact hk
  have hG3 : ∀ a : Nat, k < (sertables.longFold l a).length :=
    fun a => by rw [longLen]; exact hk
  have hacc1 := mapFoldLen k (fun p : Nat × Nat =>
    sertables.diffFold l p.1 p.2) hG1 (places.pairsOf l)
    (List.replicate l 0) h0
  have hacc2 := mapFoldLen k (fun p : Nat × Nat =>
    sertables.sumFoldC l p.1 p.2) hG2 (places.pairsOf l) _ hacc1
  show ground.getAt 0 ((sertables.foldsC l).foldl
    (fun a f => List.zipWith (fun x y => x + y) a f)
    (List.replicate l 0)) k = _
  rw [show sertables.foldsC l
      = ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
        ++ ((places.pairsOf l).map (fun p => sertables.sumFoldC l p.1 p.2)))
          ++ ((List.range l).map (sertables.longFold l)) from rfl,
    ground.foldl_append (fun a f => List.zipWith (fun x y => x + y) a f)
      ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
        ++ (places.pairsOf l).map (fun p => sertables.sumFoldC l p.1 p.2))
      _ _,
    ground.foldl_append (fun a f => List.zipWith (fun x y => x + y) a f)
      ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)) _ _,
    mapFoldAt k (sertables.longFold l) hG3 (List.range l) _ hacc2,
    mapFoldAt k (fun p : Nat × Nat => sertables.sumFoldC l p.1 p.2) hG2
      (places.pairsOf l) _ hacc1,
    mapFoldAt k (fun p : Nat × Nat => sertables.diffFold l p.1 p.2) hG1
      (places.pairsOf l) _ h0,
    ground.getAt_replicate_zero l k,
    ground.famFold_congr_all Nat.add 0
      (fun p : Nat × Nat => ground.getAt 0 (sertables.diffFold l p.1 p.2) k)
      (fun p => if p.1 ≤ k && k < p.2 then 1 else 0)
      (fun p => diffAt l p.1 p.2 k hk) (places.pairsOf l),
    diffCount l k,
    ground.famFold_congr_all Nat.add 0
      (fun p : Nat × Nat => ground.getAt 0 (sertables.sumFoldC l p.1 p.2) k)
      (fun p => (if p.1 ≤ k && k < p.2 then 1 else 0)
        + (((if p.2 ≤ k then 1 else 0) + (if p.2 ≤ k then 1 else 0)) + 0))
      (fun p => by
        rw [sumCAt l p.1 p.2 k hk, indValIn p.2 (l - 1) k hk1,
          indValLo (l - 1) l k hlo])
      (places.pairsOf l),
    ground.famFold_add_split
      (fun p : Nat × Nat => if p.1 ≤ k && k < p.2 then 1 else 0)
      (fun p => ((if p.2 ≤ k then 1 else 0) + (if p.2 ≤ k then 1 else 0)) + 0)
      (places.pairsOf l),
    diffCount l k,
    ground.famFold_add_split
      (fun p : Nat × Nat => (if p.2 ≤ k then (1 : Nat) else 0)
        + (if p.2 ≤ k then (1 : Nat) else 0))
      (fun _ => (0 : Nat)) (places.pairsOf l),
    ground.famFold_add_split
      (fun p : Nat × Nat => if p.2 ≤ k then (1 : Nat) else 0)
      (fun p => if p.2 ≤ k then (1 : Nat) else 0) (places.pairsOf l),
    topCnt l k hk, foldZero (places.pairsOf l),
    ground.famFold_congr_all Nat.add 0
      (fun a => ground.getAt 0 (sertables.longFold l a) k)
      (fun a => ((if a ≤ k then 1 else 0) + (if a ≤ k then 1 else 0)) + 0)
      (fun a => by
        rw [longAt l a k hk, indValIn a (l - 1) k hk1,
          indValLo (l - 1) l k hlo])
      (List.range l),
    ground.famFold_add_split
      (fun a => (if a ≤ k then (1 : Nat) else 0)
        + (if a ≤ k then (1 : Nat) else 0))
      (fun _ => (0 : Nat)) (List.range l),
    ground.famFold_add_split
      (fun a => if a ≤ k then (1 : Nat) else 0)
      (fun a => if a ≤ k then (1 : Nat) else 0) (List.range l),
    cntLe k l hk, foldZero (List.range l)]

private theorem rhoDAt (l m k : Nat) (hm : m + 1 = l) (hk3 : k + 3 ≤ l) :
    ground.getAt 0 (casfloor.rhoFold (sertables.tableD l)) k
      = 0 + (k + 1) * (l - (k + 1))
        + (((k + 1) * (m - (k + 1)) + (k * (k + 1) + 0))
          + ((k + 1) + 0)) := by
  have hk : k < l := Nat.lt_of_lt_of_le (ground.ltAddSucc k 2) hk3
  have hk2 : k < l - 2 := subTwoGe (k + 1) l hk3
  have hlo2 : ¬ l - 2 ≤ k := fun hc =>
    Nat.lt_irrefl k (Nat.lt_of_lt_of_le hk2 hc)
  have hl1 : l - 1 = m := by
    rw [← hm]
    rfl
  have hkm : k < m := by
    rw [← hm] at hk3
    exact Nat.le_trans (Nat.le_succ (k + 1))
      (Nat.le_of_succ_le_succ (show k + 2 + 1 ≤ m + 1 from hk3))
  have hlo1 : ¬ l - 1 ≤ k := by
    rw [hl1]
    exact fun hc => Nat.lt_irrefl k (Nat.lt_of_lt_of_le hkm hc)
  have hF2 : ground.famFold Nat.add 0
      (fun p : Nat × Nat => ground.getAt 0 (sertables.sumFoldD l p.1 p.2) k)
      (places.pairsOf l)
      = ((k + 1) * (m - (k + 1)) + (k * (k + 1) + 0))
        + ((k + 1) + 0) := by
    rw [places.pairsFold_free _ l,
      show List.range l = List.range (m + 1) from
        congrArg List.range hm.symm,
      ground.range_succ m,
      ground.famFold_snoc (fun d => ground.famFold Nat.add 0
        (fun j => ground.getAt 0 (sertables.sumFoldD l j d) k)
        (List.range d)) (List.range m) m,
      ground.famFold_congr_range _ (fun d => ground.famFold Nat.add 0
          (fun j => (if j ≤ k && k < d then 1 else 0)
            + (((if d ≤ k then 1 else 0) + (if d ≤ k then 1 else 0)) + 0))
          (List.range d)) m
        (fun d hd => ground.famFold_congr_range _ _ d (fun j _ => by
          rw [sumDAtGen l j d k hk (fun hc =>
              Nat.lt_irrefl l (Nat.lt_of_lt_of_le
                (hc ▸ Nat.succ_lt_succ hd) (Nat.le_of_eq hm))),
            indValIn d (l - 2) k hk2, indValLo (l - 2) l k hlo2])),
      ← places.pairsFold_free (fun p : Nat × Nat =>
        (if p.1 ≤ k && k < p.2 then 1 else 0)
          + (((if p.2 ≤ k then 1 else 0) + (if p.2 ≤ k then 1 else 0)) + 0))
        m,
      ground.famFold_add_split
        (fun p : Nat × Nat => if p.1 ≤ k && k < p.2 then 1 else 0)
        (fun p => ((if p.2 ≤ k then 1 else 0)
          + (if p.2 ≤ k then 1 else 0)) + 0) (places.pairsOf m),
      diffCount m k,
      ground.famFold_add_split
        (fun p : Nat × Nat => (if p.2 ≤ k then (1 : Nat) else 0)
          + (if p.2 ≤ k then (1 : Nat) else 0))
        (fun _ => (0 : Nat)) (places.pairsOf m),
      ground.famFold_add_split
        (fun p : Nat × Nat => if p.2 ≤ k then (1 : Nat) else 0)
        (fun p => if p.2 ≤ k then (1 : Nat) else 0) (places.pairsOf m),
      topCnt m k hkm, foldZero (places.pairsOf m),
      ground.famFold_congr_range _ (fun j => (if j ≤ k then (1 : Nat) else 0) + 0) m
        (fun j _ => by
          rw [sumDAtTop l j m k hk hm, indValIn j (l - 2) k hk2,
            indValLo (l - 1) l k hlo1]),
      ground.famFold_add_split (fun j => if j ≤ k then (1 : Nat) else 0)
        (fun _ => (0 : Nat)) (List.range m),
      cntLe k m hkm, foldZero (List.range m)]
  have h0 : k < (List.replicate l 0).length := by
    rw [ground.length_replicate]; exact hk
  have hG1 : ∀ p : Nat × Nat, k < (sertables.diffFold l p.1 p.2).length :=
    fun p => by rw [diffLen]; exact hk
  have hG2 : ∀ p : Nat × Nat, k < (sertables.sumFoldD l p.1 p.2).length :=
    fun p => by rw [sumDLen]; exact hk
  have hacc1 := mapFoldLen k (fun p : Nat × Nat =>
    sertables.diffFold l p.1 p.2) hG1 (places.pairsOf l)
    (List.replicate l 0) h0
  show ground.getAt 0 ((sertables.foldsD l).foldl
    (fun a f => List.zipWith (fun x y => x + y) a f)
    (List.replicate l 0)) k = _
  rw [show sertables.foldsD l
      = (places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
        ++ ((places.pairsOf l).map (fun p => sertables.sumFoldD l p.1 p.2))
      from rfl,
    ground.foldl_append (fun a f => List.zipWith (fun x y => x + y) a f)
      ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)) _ _,
    mapFoldAt k (fun p : Nat × Nat => sertables.sumFoldD l p.1 p.2) hG2
      (places.pairsOf l) _ hacc1,
    mapFoldAt k (fun p : Nat × Nat => sertables.diffFold l p.1 p.2) hG1
      (places.pairsOf l) _ h0,
    ground.getAt_replicate_zero l k,
    ground.famFold_congr_all Nat.add 0
      (fun p : Nat × Nat => ground.getAt 0 (sertables.diffFold l p.1 p.2) k)
      (fun p => if p.1 ≤ k && k < p.2 then 1 else 0)
      (fun p => diffAt l p.1 p.2 k hk) (places.pairsOf l),
    diffCount l k, hF2]

/-! ## The members' length folds and residues -/

private theorem resB (m : Nat) :
    gentable.residue (sertables.tableB (m + 2)) = 2 * m + 2 := by
  have hval : ground.dotNat (sertables.sumFoldB (m + 2) 0 1)
      (sertables.tableB (m + 2)).lenNums = (2 * m + 2) * 2 := by
    rw [dotIndex, sumBLen,
      ground.famFold_range_cons Nat.add 0 (fun i => ground.getAt 0 (sertables.sumFoldB (m + 2) 0 1) i
        * ground.getAt 0 (sertables.tableB (m + 2)).lenNums i) (m + 1),
      ground.range_succ m,
      ground.famFold_snoc (fun i =>
        ground.getAt 0 (sertables.sumFoldB (m + 2) 0 1) (i + 1)
          * ground.getAt 0 (sertables.tableB (m + 2)).lenNums (i + 1))
        (List.range m) m,
      ground.famFold_congr_range _ (fun _ => (4 : Nat)) m (fun i hi => by
        rw [sumBAt (m + 2) 0 1 (i + 1) (Nat.succ_lt_succ
            (Nat.lt_trans hi (Nat.lt_succ_self m))),
          sertables.lensB_at (m + 2) (i + 1) (Nat.succ_lt_succ
            (Nat.lt_trans hi (Nat.lt_succ_self m))),
          indValOut 0 1 (i + 1) (fun hc =>
            Nat.not_succ_le_zero i (Nat.le_of_succ_le_succ hc)),
          indValIn 1 (m + 2) (i + 1) (Nat.succ_lt_succ
            (Nat.lt_trans hi (Nat.lt_succ_self m))),
          if_pos (Nat.le_add_left 1 i),
          ground.neBeqOf (fun hc : i + 1 + 1 = m + 2 =>
            Nat.lt_irrefl i (Nat.succ.inj (Nat.succ.inj hc) ▸ hi))]
        rfl),
      foldConst 4 m,
      sumBAt (m + 2) 0 1 0 (Nat.zero_lt_succ _),
      sertables.lensB_at (m + 2) 0 (Nat.zero_lt_succ _),
      sumBAt (m + 2) 0 1 (m + 1) (Nat.lt_succ_self (m + 1)),
      sertables.lensB_at (m + 2) (m + 1) (Nat.lt_succ_self (m + 1)),
      indValIn 0 1 0 (Nat.zero_lt_succ 0),
      indValLo 1 (m + 2) 0 (fun hc =>
        Nat.not_succ_le_zero 0 hc),
      indValOut 0 1 (m + 1) (fun hc =>
        Nat.not_succ_le_zero m (Nat.le_of_succ_le_succ hc)),
      indValIn 1 (m + 2) (m + 1) (Nat.lt_succ_self (m + 1)),
      if_pos (Nat.le_refl 0), if_pos (Nat.le_add_left 1 m),
      ground.neBeqOf (fun hc : 0 + 1 = m + 2 =>
        Nat.noConfusion (Nat.succ.inj hc)),
      ground.eqBeqOf (rfl : m + 1 + 1 = m + 2)]
    show 1 * 2 + (4 * m + 2 * 1) = (2 * m + 2) * 2
    rw [ground.mulAddR (2 * m) 2 2, ground.mulAssoc 2 m 2,
      Nat.mul_comm m 2, ← ground.mulAssoc 2 2 m,
      Nat.add_comm 2 (4 * m + 2), Nat.add_assoc (4 * m) 2 2]
  show ground.dotNat (sertables.sumFoldB (m + 2) 0 1)
    (sertables.tableB (m + 2)).lenNums / (2 * 1) = _
  rw [hval]
  exact ground.divMulSelf (2 * m + 2) 2 (Nat.zero_lt_succ 1)

private theorem resC (m : Nat) :
    gentable.residue (sertables.tableC (m + 2)) = m + 2 := by
  have hval : ground.dotNat (sertables.longFold (m + 2) 0)
      (sertables.tableC (m + 2)).lenNums = (m + 2) * 2 := by
    rw [dotIndex, longLen, ground.range_succ (m + 1),
      ground.famFold_snoc (fun i =>
        ground.getAt 0 (sertables.longFold (m + 2) 0) i
          * ground.getAt 0 (sertables.tableC (m + 2)).lenNums i)
        (List.range (m + 1)) (m + 1),
      ground.famFold_congr_range _ (fun _ => (2 : Nat)) (m + 1) (fun i hi => by
        rw [longAt (m + 2) 0 i
            (Nat.lt_trans hi (Nat.lt_succ_self (m + 1))),
          sertables.lensC_at (m + 2) i (Nat.lt_trans hi (Nat.lt_succ_self (m + 1))),
          indValIn 0 (m + 2 - 1) i (show i < m + 2 - 1 from hi),
          indValLo (m + 2 - 1) (m + 2) i
            (show ¬ m + 2 - 1 ≤ i from fun hc =>
              Nat.lt_irrefl i (Nat.lt_of_lt_of_le
                (show i < m + 1 from hi) hc)),
          if_pos (Nat.zero_le i),
          ground.neBeqOf (fun hc : i + 1 = m + 2 =>
            Nat.lt_irrefl i (Nat.succ.inj hc ▸ hi))]
        rfl),
      foldConst 2 (m + 1),
      longAt (m + 2) 0 (m + 1) (Nat.lt_succ_self (m + 1)),
      sertables.lensC_at (m + 2) (m + 1) (Nat.lt_succ_self (m + 1)),
      indValOut 0 (m + 2 - 1) (m + 1)
        (show ¬ m + 1 < m + 2 - 1 from Nat.lt_irrefl (m + 1)),
      indValIn (m + 2 - 1) (m + 2) (m + 1) (Nat.lt_succ_self (m + 1)),
      if_pos (show m + 2 - 1 ≤ m + 1 from Nat.le_refl (m + 1)),
      ground.eqBeqOf (rfl : m + 1 + 1 = m + 2)]
    show 2 * (m + 1) + (0 + 0 + 1) * 2 = (m + 2) * 2
    rw [ground.mulAddR m 2 2, Nat.mul_comm 2 (m + 1), ground.mulAddR m 1 2]
  show ground.dotNat (sertables.longFold (m + 2) 0)
    (sertables.tableC (m + 2)).lenNums / (2 * 1) = _
  rw [hval]
  exact ground.divMulSelf (m + 2) 2 (Nat.zero_lt_succ 1)

private theorem resD (m : Nat) :
    gentable.residue (sertables.tableD (m + 3)) = 2 * m + 3 := by
  have hb : ¬ 1 + 1 = m + 3 := fun hc =>
    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))
  have hval : ground.dotNat (sertables.sumFoldD (m + 3) 0 1)
      (sertables.tableD (m + 3)).lenNums = (2 * m + 3) * 2 := by
    rw [dotIndex, sumDLen,
      ground.famFold_range_cons Nat.add 0 (fun i => ground.getAt 0 (sertables.sumFoldD (m + 3) 0 1) i
        * ground.getAt 0 (sertables.tableD (m + 3)).lenNums i) (m + 2),
      ground.range_succ (m + 1),
      ground.famFold_snoc (fun i =>
        ground.getAt 0 (sertables.sumFoldD (m + 3) 0 1) (i + 1)
          * ground.getAt 0 (sertables.tableD (m + 3)).lenNums (i + 1))
        (List.range (m + 1)) (m + 1),
      ground.range_succ m,
      ground.famFold_snoc (fun i =>
        ground.getAt 0 (sertables.sumFoldD (m + 3) 0 1) (i + 1)
          * ground.getAt 0 (sertables.tableD (m + 3)).lenNums (i + 1))
        (List.range m) m,
      ground.famFold_congr_range _ (fun _ => (4 : Nat)) m (fun i hi => by
        rw [sumDAtGen (m + 3) 0 1 (i + 1)
            (Nat.succ_lt_succ (Nat.lt_trans hi
              (Nat.lt_trans (Nat.lt_succ_self m)
                (Nat.lt_succ_self (m + 1)))))
            hb,
          sertables.lensD_at (m + 3) (i + 1)
            (Nat.succ_lt_succ (Nat.lt_trans hi
              (Nat.lt_trans (Nat.lt_succ_self m)
                (Nat.lt_succ_self (m + 1))))),
          indValOut 0 1 (i + 1) (fun hc =>
            Nat.not_succ_le_zero i (Nat.le_of_succ_le_succ hc)),
          indValIn 1 (m + 3 - 2) (i + 1)
            (show i + 1 < m + 1 from Nat.succ_lt_succ hi),
          indValLo (m + 3 - 2) (m + 3) (i + 1)
            (show ¬ m + 1 ≤ i + 1 from fun hc =>
              Nat.lt_irrefl i (Nat.lt_of_lt_of_le hi
                (Nat.le_of_succ_le_succ hc))),
          if_pos (Nat.le_add_left 1 i)]),
      foldConst 4 m,
      sumDAtGen (m + 3) 0 1 0 (Nat.zero_lt_succ _) hb,
      sertables.lensD_at (m + 3) 0 (Nat.zero_lt_succ _),
      sumDAtGen (m + 3) 0 1 (m + 1)
        (Nat.lt_trans (Nat.lt_succ_self (m + 1))
          (Nat.lt_succ_self (m + 2))) hb,
      sertables.lensD_at (m + 3) (m + 1)
        (Nat.lt_trans (Nat.lt_succ_self (m + 1))
          (Nat.lt_succ_self (m + 2))),
      sumDAtGen (m + 3) 0 1 (m + 2) (Nat.lt_succ_self (m + 2)) hb,
      sertables.lensD_at (m + 3) (m + 2) (Nat.lt_succ_self (m + 2)),
      indValIn 0 1 0 (Nat.zero_lt_succ 0),
      indValLo 1 (m + 3 - 2) 0 (fun hc => Nat.not_succ_le_zero 0 hc),
      indValLo (m + 3 - 2) (m + 3) 0
        (show ¬ m + 1 ≤ 0 from fun hc => Nat.not_succ_le_zero m hc),
      indValOut 0 1 (m + 1) (fun hc =>
        Nat.not_succ_le_zero m (Nat.le_of_succ_le_succ hc)),
      indValOut 1 (m + 3 - 2) (m + 1)
        (show ¬ m + 1 < m + 1 from Nat.lt_irrefl (m + 1)),
      indValIn (m + 3 - 2) (m + 3) (m + 1)
        (show m + 1 < m + 3 from Nat.lt_trans (Nat.lt_succ_self (m + 1))
          (Nat.lt_succ_self (m + 2))),
      indValOut 0 1 (m + 2) (fun hc =>
        Nat.not_succ_le_zero (m + 1) (Nat.le_of_succ_le_succ hc)),
      indValOut 1 (m + 3 - 2) (m + 2)
        (show ¬ m + 2 < m + 1 from fun hc =>
          Nat.lt_irrefl (m + 1) (Nat.lt_trans (Nat.lt_succ_self (m + 1)) hc)),
      indValIn (m + 3 - 2) (m + 3) (m + 2) (Nat.lt_succ_self (m + 2)),
      if_pos (Nat.le_refl 0),
      if_pos (show m + 3 - 2 ≤ m + 1 from Nat.le_refl (m + 1)),
      if_pos (show m + 3 - 2 ≤ m + 2 from Nat.le_succ (m + 1))]
    show 1 * 2 + (4 * m + 1 * 2 + 1 * 2) = (2 * m + 3) * 2
    rw [ground.mulAddR (2 * m) 3 2, ground.mulAssoc 2 m 2,
      Nat.mul_comm m 2, ← ground.mulAssoc 2 2 m,
      Nat.add_comm 2 (4 * m + 2 + 2),
      Nat.add_assoc (4 * m + 2) 2 2, Nat.add_assoc (4 * m) 2 4]
  show ground.dotNat (sertables.sumFoldD (m + 3) 0 1)
    (sertables.tableD (m + 3)).lenNums / (2 * 1) = _
  rw [hval]
  exact ground.divMulSelf (2 * m + 3) 2 (Nat.zero_lt_succ 1)

/-! ## The root fold's closed forms -/

private theorem hSB (k D l : Nat) (hD : D + (k + 1) = l) :
    2 * l - (k + 1) = D + D + (k + 1) := by
  rw [← hD, Nat.two_mul (D + (k + 1)), addSwap D (k + 1) D (k + 1),
    ← Nat.add_assoc (D + D) (k + 1) (k + 1),
    ground.addSubSelfR (D + D + (k + 1)) (k + 1)]

private theorem hSC (k D l : Nat) (hD : D + (k + 1) = l) :
    2 * l - k = D + D + (k + 1 + 1) := by
  rw [← hD, Nat.two_mul (D + (k + 1)), addSwap D (k + 1) D (k + 1),
    ← Nat.add_assoc (k + 1) k 1, Nat.add_right_comm (k + 1) k 1,
    ← Nat.add_assoc (D + D) (k + 1 + 1) k, ground.addSubSelfR (D + D + (k + 1 + 1)) k]

private theorem hSD (k D l : Nat) (hD : D + (k + 1) = l) :
    2 * l - (k + 1 + 1) = D + D + k := by
  rw [← hD, Nat.two_mul (D + (k + 1)), addSwap D (k + 1) D (k + 1),
    show k + 1 + (k + 1) = k + (k + 1 + 1) from by
      rw [Nat.add_comm (k + 1) (k + 1), Nat.add_assoc k 1 (k + 1),
        Nat.add_comm 1 (k + 1)],
    ← Nat.add_assoc (D + D) k (k + 1 + 1),
    ground.addSubSelfR (D + D + k) (k + 1 + 1)]

private theorem polyB (k D : Nat) :
    0 + (k + 1) * D + ((k + 1) * D + k * (k + 1)) + (k + 1)
      = (k + 1) * (D + D + (k + 1)) := by
  rw [Nat.left_distrib (k + 1) (D + D) (k + 1),
    Nat.left_distrib (k + 1) D D,
    ground.mulAddR k 1 (k + 1), Nat.one_mul, Nat.zero_add,
    ← Nat.add_assoc ((k + 1) * D) ((k + 1) * D) (k * (k + 1)),
    Nat.add_assoc ((k + 1) * D + (k + 1) * D) (k * (k + 1)) (k + 1)]

private theorem polyC (k D : Nat) :
    0 + (k + 1) * D + ((k + 1) * D + (k * (k + 1) + 0))
        + ((k + 1) + (k + 1) + 0)
      = (k + 1) * (D + D + (k + 1 + 1)) := by
  rw [Nat.left_distrib (k + 1) (D + D) (k + 1 + 1),
    Nat.left_distrib (k + 1) D D,
    Nat.left_distrib (k + 1) (k + 1) 1, Nat.mul_one,
    ground.mulAddR k 1 (k + 1), Nat.one_mul, Nat.zero_add,
    Nat.add_zero (k * (k + 1)), Nat.add_zero (k + 1 + (k + 1)),
    ← Nat.add_assoc ((k + 1) * D) ((k + 1) * D) (k * (k + 1)),
    Nat.add_assoc ((k + 1) * D + (k + 1) * D) (k * (k + 1)) (k + 1 + (k + 1)),
    Nat.add_assoc (k * (k + 1)) (k + 1) (k + 1)]

private theorem polyD (k D Dm : Nat) :
    0 + (k + 1) * D + (((k + 1) * Dm + (k * (k + 1) + 0)) + ((k + 1) + 0))
      = (k + 1) * (D + Dm + (k + 1)) := by
  rw [Nat.left_distrib (k + 1) (D + Dm) (k + 1),
    Nat.left_distrib (k + 1) D Dm,
    ground.mulAddR k 1 (k + 1), Nat.one_mul, Nat.zero_add,
    Nat.add_zero (k * (k + 1)), Nat.add_zero (k + 1),
    Nat.add_assoc ((k + 1) * Dm) (k * (k + 1)) (k + 1),
    ← Nat.add_assoc ((k + 1) * D) ((k + 1) * Dm) (k * (k + 1) + (k + 1))]

private theorem addDfix (Dm k : Nat) :
    (Dm + 1) + (Dm + 1) + k = (Dm + 1) + Dm + (k + 1) := by
  rw [← Nat.add_assoc (Dm + 1) Dm 1, Nat.add_assoc (Dm + 1 + Dm) 1 k,
    Nat.add_comm 1 k]

private theorem subStep (k l : Nat) (h : k + 2 ≤ l) :
    l - (k + 1) = (l - (k + 1 + 1)) + 1 := by
  have hD2 : (l - (k + 1 + 1)) + (k + 1 + 1) = l :=
    ground.subAdd (show k + 1 + 1 ≤ l from h)
  rw [← hD2, ground.addSubSelfR (l - (k + 1 + 1)) (k + 1 + 1),
    succAdd (l - (k + 1 + 1)) (k + 1),
    ground.addSubSelfR (l - (k + 1 + 1) + 1) (k + 1)]

private theorem rhoBc (l k : Nat) (hk2 : k + 2 ≤ l) :
    ground.getAt 0 (casfloor.rhoFold (sertables.tableB l)) k
      = (k + 1) * (2 * l - (k + 1)) := by
  have hk : k < l := Nat.lt_of_lt_of_le (ground.ltAddSucc k 1) hk2
  have hD : (l - (k + 1)) + (k + 1) = l := ground.subAdd hk
  rw [rhoBAt l k hk, hSB k (l - (k + 1)) l hD]
  exact polyB k (l - (k + 1))

private theorem rhoCc (l k : Nat) (hk3 : k + 3 ≤ l) :
    ground.getAt 0 (casfloor.rhoFold (sertables.tableC l)) k
      = (k + 1) * (2 * l - k) := by
  have hk : k < l := Nat.lt_of_lt_of_le (ground.ltAddSucc k 2) hk3
  have hD : (l - (k + 1)) + (k + 1) = l := ground.subAdd hk
  rw [rhoCAt l k hk3, hSC k (l - (k + 1)) l hD]
  exact polyC k (l - (k + 1))

private theorem rhoDc (l m k : Nat) (hm : m + 1 = l) (hk3 : k + 3 ≤ l) :
    ground.getAt 0 (casfloor.rhoFold (sertables.tableD l)) k
      = (k + 1) * (2 * l - (k + 1 + 1)) := by
  have hk : k < l := Nat.lt_of_lt_of_le (ground.ltAddSucc k 2) hk3
  have hD : (l - (k + 1)) + (k + 1) = l := ground.subAdd hk
  have hkm : k + 1 ≤ m := by
    rw [← hm] at hk3
    exact Nat.le_of_succ_le_succ
      (Nat.le_trans (Nat.le_succ (k + 2)) hk3)
  have hDm : (m - (k + 1)) + (k + 1) = m := ground.subAdd hkm
  have hDl : ((m - (k + 1)) + 1) + (k + 1) = l := by
    rw [Nat.add_right_comm (m - (k + 1)) 1 (k + 1), hDm, hm]
  have hsub : l - (k + 1) = (m - (k + 1)) + 1 := by
    rw [← hDl, ground.addSubSelfR ((m - (k + 1)) + 1) (k + 1)]
  rw [rhoDAt l m k hm hk3, hsub,
    hSD k (l - (k + 1)) l hD, hsub,
    addDfix (m - (k + 1)) k]
  exact polyD k ((m - (k + 1)) + 1) (m - (k + 1))

/-! ## The Abel summation and the Casimir count -/

private def prevH (H : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => H k

private theorem telescope (W : List Nat) (H U : Nat → Nat)
    (hsa : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) :
    ∀ n : Nat, (∀ k, k < n → H k = prevH H k + U k) →
    ground.famFold Nat.add 0
        (fun k => H k
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range n)
      + prevH H n * ground.getAt 0 W n
      = ground.famFold Nat.add 0
        (fun i => ground.getAt 0 W i * U i) (List.range n)
  | 0, _ => by
    show (0 : Nat) + 0 * ground.getAt 0 W 0 = 0
    rw [Nat.zero_mul]
  | n + 1, hU => by
    rw [ground.range_succ n,
      ground.famFold_snoc (fun k => H k
        * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range n) n,
      ground.famFold_snoc (fun i => ground.getAt 0 W i * U i)
        (List.range n) n,
      show prevH H (n + 1) = H n from rfl,
      Nat.add_assoc (ground.famFold Nat.add 0 (fun k => H k
        * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))) (List.range n))
        (H n * (ground.getAt 0 W n - ground.getAt 0 W (n + 1)))
        (H n * ground.getAt 0 W (n + 1)),
      ← Nat.left_distrib (H n)
        (ground.getAt 0 W n - ground.getAt 0 W (n + 1))
        (ground.getAt 0 W (n + 1)),
      ground.subAdd (hsa n), hU n (Nat.lt_succ_self n),
      ground.mulAddR (prevH H n) (U n) (ground.getAt 0 W n),
      ← Nat.add_assoc (ground.famFold Nat.add 0 (fun k => H k
        * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))) (List.range n))
        (prevH H n * ground.getAt 0 W n)
        (U n * ground.getAt 0 W n),
      telescope W H U hsa n (fun k hk => hU k (Nat.lt_succ_of_lt hk)),
      Nat.mul_comm (U n) (ground.getAt 0 W n)]

theorem memberLen (W : List Nat) (l : Nat) :
    (member W l).length = l :=
  ground.length_mapRange _ l

private theorem memberZero (W : List Nat) (l x : Nat)
    (h : W.length ≤ x) : ground.getAt 0 (member W l) x = 0 := by
  by_cases hx : x < l
  · rw [memberEntry W l x hx, ground.getAt_over 0 W x h,
      ground.getAt_over 0 W (x + 1) (Nat.le_trans h (Nat.le_succ x))]
  · exact ground.getAt_over 0 (member W l) x
      (by rw [memberLen]; exact Nat.le_of_not_lt hx)

private theorem c2NumFold (t : gentable.Table) (E : casfloor.EndFold)
    (l key : Nat) (f cor : List Nat)
    (hr : t.rank = l) (hf : E.fold = f) (hk : E.key = key)
    (hc : E.coroot = cor) :
    casfloor.c2Num t E = ground.famFold Nat.add 0
      (fun k => (ground.getAt 0 f k
          + key * ground.getAt 0 (casfloor.rhoFold t) k)
        * ground.getAt 0 cor k * ground.getAt 0 t.lenNums k)
      (List.range l) := by
  rw [← hr, ← hf, ← hk, ← hc]
  show (List.range t.rank).foldl (fun acc k =>
    acc + (ground.getAt 0 E.fold k
        + E.key * ground.getAt 0 (casfloor.rhoFold t) k)
      * ground.getAt 0 E.coroot k * ground.getAt 0 t.lenNums k) 0 = _
  rw [ground.foldlSum _ (List.range t.rank) 0, Nat.zero_add]

private theorem dotMapRange (W : List Nat) (f : Nat → Nat) :
    ground.dotNat W ((List.range W.length).map f)
      = ground.famFold Nat.add 0
        (fun i => ground.getAt 0 W i * f i) (List.range W.length) := by
  rw [dotIndex]
  exact ground.famFold_congr_range _ _ W.length (fun i hi => by
    rw [ground.getAt_map_range 0 f W.length i, if_pos hi])

private theorem sumSqDot : ∀ W : List Nat,
    c2hat.sumSq W = ground.dotNat W W
  | [] => rfl
  | a :: t => by
    show a * a + c2hat.sumSq t = a * a + ground.dotNat t t
    rw [sumSqDot t]

private theorem hUgen (j X c : Nat) (hXc : X = (j + 1) + c) :
    (j + 1 + 1) * X = (j + 1) * (X + 1) + c := by
  rw [Nat.left_distrib (j + 1) X 1, Nat.mul_one,
    Nat.add_assoc ((j + 1) * X) (j + 1) c, ← hXc,
    ground.mulAddR (j + 1) 1 X, Nat.one_mul]

private theorem addB1 (j D : Nat) :
    (D + 1) + (D + 1) + (j + 1) = (D + D + (j + 1 + 1)) + 1 := by
  rw [addSwap D 1 D 1, Nat.add_assoc (D + D) (1 + 1) (j + 1),
    Nat.add_assoc (D + D) (j + 1 + 1) 1,
    Nat.add_comm (1 + 1) (j + 1)]

private theorem addB2 (j D : Nat) :
    D + D + (j + 1 + 1) = (j + 1) + (2 * D + 1) := by
  rw [Nat.two_mul D, ← Nat.add_assoc (j + 1) (D + D) 1,
    Nat.add_comm (j + 1) (D + D), Nat.add_assoc (D + D) (j + 1) 1]

private theorem addC1 (j D : Nat) :
    (D + 1) + (D + 1) + (j + 1 + 1) = (D + D + (j + 1 + 1 + 1)) + 1 := by
  rw [addSwap D 1 D 1, Nat.add_assoc (D + D) (1 + 1) (j + 1 + 1),
    Nat.add_assoc (D + D) (j + 1 + 1 + 1) 1,
    Nat.add_comm (1 + 1) (j + 1 + 1)]

private theorem addC2 (j D : Nat) :
    D + D + (j + 1 + 1 + 1) = (j + 1) + 2 * (D + 1) := by
  rw [Nat.left_distrib 2 D 1, Nat.two_mul D, Nat.mul_one,
    ← Nat.add_assoc (j + 1) (D + D) 2,
    Nat.add_comm (j + 1) (D + D), Nat.add_assoc (D + D) (j + 1) 2]

private theorem addD1 (j D : Nat) :
    (D + 1) + (D + 1) + j = (D + D + (j + 1)) + 1 := by
  rw [addSwap D 1 D 1, Nat.add_assoc (D + D) (1 + 1) j,
    Nat.add_assoc (D + D) (j + 1) 1, Nat.add_comm (1 + 1) j]

private theorem addD2 (j D : Nat) :
    D + D + (j + 1) = (j + 1) + 2 * D := by
  rw [Nat.two_mul D, Nat.add_comm (j + 1) (D + D)]

private theorem teleAt (W : List Nat) (H U : Nat → Nat)
    (hsa : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i)
    (hU : ∀ k, k < W.length → H k = prevH H k + U k) :
    ground.famFold Nat.add 0
        (fun k => H k
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range W.length)
      = ground.famFold Nat.add 0
        (fun i => ground.getAt 0 W i * U i) (List.range W.length) := by
  have h := telescope W H U hsa W.length hU
  rw [ground.getAt_over 0 W W.length (Nat.le_refl _), Nat.mul_zero,
    Nat.add_zero] at h
  exact h

private theorem foldBAt (W : List Nat) (l k : Nat) (hk : k < l) :
    ground.getAt 0 (foldB W l) k = ground.sumNat (List.take (k + 1) W) := by
  show ground.getAt 0 ((List.range l).map
    (fun x => ground.sumNat (List.take (x + 1) W))) k = _
  rw [ground.getAt_map_range 0 _ l k, if_pos hk]

private theorem takeSumStep (W : List Nat) : ∀ k : Nat,
    ground.sumNat (List.take (k + 1) W)
      = prevH (fun x => ground.sumNat (List.take (x + 1) W)) k
        + ground.getAt 0 W k
  | 0 => takeStep W 0
  | j + 1 => takeStep W (j + 1)

private theorem subOf (X b c : Nat) (h : X = c + b) : X - b = c := by
  rw [h, ground.addSubSelfR c b]

private theorem hSBg (c D l : Nat) (hD : D + c = l) :
    2 * l - c = D + D + c := by
  rw [← hD, Nat.two_mul (D + c), addSwap D c D c,
    ← Nat.add_assoc (D + D) c c, ground.addSubSelfR (D + D + c) c]

private theorem hSD0 (D l : Nat) (hD : D + 1 = l) : 2 * l - 2 = D + D :=
  subOf (2 * l) 2 (D + D) (by
    rw [← hD, Nat.two_mul (D + 1), addSwap D 1 D 1])

private theorem hUB (l : Nat) : ∀ k : Nat, k + 3 ≤ l →
    (k + 1) * (2 * l - (k + 1))
      = prevH (fun x => (x + 1) * (2 * l - (x + 1))) k
        + (2 * (l - (k + 1)) + 1)
  | 0, h => by
    have hD : (l - 1) + 1 = l :=
      ground.subAdd (Nat.le_trans (Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2)) h)
    show 1 * (2 * l - 1) = 0 + (2 * (l - 1) + 1)
    rw [hSBg 1 (l - 1) l hD, Nat.zero_add, Nat.two_mul (l - 1), Nat.one_mul]
  | j + 1, h => by
    have h2 : j + 1 + 1 ≤ l :=
      Nat.le_trans (Nat.le_trans (Nat.le_succ (j + 2)) (Nat.le_succ (j + 3))) h
    have h1 : j + 1 ≤ l := Nat.le_trans (Nat.le_succ (j + 1)) h2
    have hD : (l - (j + 1 + 1)) + (j + 1 + 1) = l := ground.subAdd h2
    have hD' : (l - (j + 1)) + (j + 1) = l := ground.subAdd h1
    show (j + 1 + 1) * (2 * l - (j + 1 + 1))
      = (j + 1) * (2 * l - (j + 1)) + (2 * (l - (j + 1 + 1)) + 1)
    rw [hSBg (j + 1 + 1) (l - (j + 1 + 1)) l hD,
      hSBg (j + 1) (l - (j + 1)) l hD',
      subStep j l h2, addB1 j (l - (j + 1 + 1))]
    exact hUgen j ((l - (j + 1 + 1)) + (l - (j + 1 + 1)) + (j + 1 + 1))
      (2 * (l - (j + 1 + 1)) + 1) (addB2 j (l - (j + 1 + 1)))

private theorem hUC (l : Nat) : ∀ k : Nat, k + 3 ≤ l →
    (k + 1) * (2 * l - k)
      = prevH (fun x => (x + 1) * (2 * l - x)) k + 2 * (l - k)
  | 0, _ => by
    show 1 * (2 * l) = 0 + 2 * l
    rw [Nat.zero_add, Nat.one_mul]
  | j + 1, h => by
    have h2 : j + 1 + 1 ≤ l :=
      Nat.le_trans (Nat.le_trans (Nat.le_succ (j + 2)) (Nat.le_succ (j + 3))) h
    have h1 : j + 1 ≤ l := Nat.le_trans (Nat.le_succ (j + 1)) h2
    have hD : (l - (j + 1 + 1)) + (j + 1 + 1) = l := ground.subAdd h2
    have hD' : (l - (j + 1)) + (j + 1) = l := ground.subAdd h1
    show (j + 1 + 1) * (2 * l - (j + 1))
      = (j + 1) * (2 * l - j) + 2 * (l - (j + 1))
    rw [hSC (j + 1) (l - (j + 1 + 1)) l hD, hSC j (l - (j + 1)) l hD',
      subStep j l h2, addC1 j (l - (j + 1 + 1))]
    exact hUgen j
      ((l - (j + 1 + 1)) + (l - (j + 1 + 1)) + (j + 1 + 1 + 1))
      (2 * ((l - (j + 1 + 1)) + 1)) (addC2 j (l - (j + 1 + 1)))

private theorem hUD (l : Nat) : ∀ k : Nat, k + 3 ≤ l →
    (k + 1) * (2 * l - (k + 1 + 1))
      = prevH (fun x => (x + 1) * (2 * l - (x + 1 + 1))) k
        + 2 * (l - (k + 1))
  | 0, h => by
    have hD : (l - 1) + 1 = l :=
      ground.subAdd (Nat.le_trans (Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2)) h)
    show 1 * (2 * l - 2) = 0 + 2 * (l - 1)
    rw [hSD0 (l - 1) l hD, Nat.zero_add, Nat.two_mul (l - 1), Nat.one_mul]
  | j + 1, h => by
    have h2 : j + 1 + 1 ≤ l :=
      Nat.le_trans (Nat.le_trans (Nat.le_succ (j + 2)) (Nat.le_succ (j + 3))) h
    have h1 : j + 1 ≤ l := Nat.le_trans (Nat.le_succ (j + 1)) h2
    have hD : (l - (j + 1 + 1)) + (j + 1 + 1) = l := ground.subAdd h2
    have hD' : (l - (j + 1)) + (j + 1) = l := ground.subAdd h1
    show (j + 1 + 1) * (2 * l - (j + 1 + 1 + 1))
      = (j + 1) * (2 * l - (j + 1 + 1)) + 2 * (l - (j + 1 + 1))
    rw [hSD (j + 1) (l - (j + 1 + 1)) l hD, hSD j (l - (j + 1)) l hD',
      subStep j l h2, addD1 j (l - (j + 1 + 1))]
    exact hUgen j ((l - (j + 1 + 1)) + (l - (j + 1 + 1)) + (j + 1))
      (2 * (l - (j + 1 + 1))) (addD2 j (l - (j + 1 + 1)))

private theorem hinB (m : Nat) : 2 * (2 * m + 2) + 2 = (2 * m + 3) * 2 := by
  rw [ground.mulAddR (2 * m) 3 2, Nat.left_distrib 2 (2 * m) 2,
    Nat.add_assoc (2 * (2 * m)) (2 * 2) 2, Nat.mul_comm 2 (2 * m)]

private theorem c2DenB (l : Nat) (hl : 2 ≤ l) (E : casfloor.EndFold)
    (hkey : E.key = 1) :
    casfloor.c2Den (sertables.tableB l) E = casDenB l * 2 := by
  match Nat.le.dest hl with
  | ⟨m, hm⟩ =>
    have hm' : m + 2 = l := (Nat.add_comm m 2).trans hm
    rw [← hm']
    show 2 * 1 * E.key
        * (2 * gentable.residue (sertables.tableB (m + 2)) + 2)
      = 2 * (2 * (m + 2) - 1) * 2
    rw [hkey, resB m,
      subOf (2 * (m + 2)) 1 (2 * m + 3) (by
        rw [Nat.left_distrib 2 m 2, Nat.add_assoc (2 * m) 3 1])]
    show 2 * (2 * (2 * m + 2) + 2) = 2 * (2 * m + 3) * 2
    rw [hinB m, ground.mulAssoc 2 (2 * m + 3) 2]

/-- The `B` series' Casimir value at the leading family's member. -/
theorem casRead_B : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    casfloor.c2Read (sertables.tableB l) (endB W l)
      (casNumB W l) (casDenB l) := by
  intro W l hs hl
  have hsa := ground.sortedAll W hs
  have hal : W.length ≤ l := Nat.le_trans (Nat.le_add_right W.length 2) hl
  have hl2 : 2 ≤ l := Nat.le_trans (Nat.le_add_left 2 W.length) hl
  have hk3 : ∀ k, k < W.length → k + 3 ≤ l := fun k hk =>
    Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ hk)) hl
  have hk2 : ∀ k, k < W.length → k + 2 ≤ l := fun k hk =>
    Nat.le_trans (Nat.le_succ (k + 2)) (hk3 k hk)
  have hkl : ∀ k, k < W.length → k < l := fun k hk =>
    Nat.lt_of_lt_of_le (ground.ltAddSucc k 1) (hk2 k hk)
  have hnum : casfloor.c2Num (sertables.tableB l) (endB W l)
      = casNumB W l * 2 := by
    rw [c2NumFold (sertables.tableB l) (endB W l) l 1 (foldB W l)
        (member W l) rfl rfl rfl rfl,
      ground.foldExtend' _ W.length l hal (fun x hx => by
        rw [memberZero W l x hx, Nat.mul_zero, Nat.zero_mul]),
      ground.famFold_congr_range _ (fun k =>
        (ground.sumNat (List.take (k + 1) W)
            + (k + 1) * (2 * l - (k + 1)))
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)) * 2)
        W.length (fun k hk => by
          rw [foldBAt W l k (hkl k hk), Nat.one_mul,
            rhoBc l k (hk2 k hk), memberEntry W l k (hkl k hk),
            sertables.lensB_at l k (hkl k hk),
            ground.neBeqOf (fun hc : k + 1 = l =>
              Nat.lt_irrefl (k + 1)
                (Nat.le_trans (hk2 k hk) (Nat.le_of_eq hc.symm)))]
          rfl),
      ground.famFold_mulR 2 (fun k =>
        (ground.sumNat (List.take (k + 1) W)
            + (k + 1) * (2 * l - (k + 1)))
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range W.length),
      ground.famFold_congr_range _ (fun k =>
        ground.sumNat (List.take (k + 1) W)
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))
          + (k + 1) * (2 * l - (k + 1))
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        W.length (fun k _ => ground.mulAddR _ _ _),
      ground.famFold_add_split
        (fun k => ground.sumNat (List.take (k + 1) W)
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (fun k => (k + 1) * (2 * l - (k + 1))
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range W.length),
      teleAt W (fun x => ground.sumNat (List.take (x + 1) W))
        (fun x => ground.getAt 0 W x) hsa (fun k _ => takeSumStep W k),
      teleAt W (fun x => (x + 1) * (2 * l - (x + 1)))
        (fun x => 2 * (l - (x + 1)) + 1) hsa
        (fun k hk => hUB l k (hk3 k hk)),
      ← dotIndex W W, ← sumSqDot W,
      ← dotMapRange W (fun i => 2 * (l - (i + 1)) + 1)]
    rfl
  show casDenB l * casfloor.c2Num (sertables.tableB l) (endB W l)
    = casNumB W l * casfloor.c2Den (sertables.tableB l) (endB W l)
  rw [hnum, c2DenB l hl2 (endB W l) rfl]
  exact ground.mulLeftComm (casDenB l) (casNumB W l) 2

private theorem foldCAt (W : List Nat) (l k : Nat) (hk : k < l)
    (h : ¬ l ≤ k + 1) :
    ground.getAt 0 (foldC W l) k
      = 2 * ground.sumNat (List.take (k + 1) W) := by
  show ground.getAt 0 ((List.range l).map (fun x =>
    if l ≤ x + 1 then ground.sumNat W
    else 2 * ground.sumNat (List.take (x + 1) W))) k = _
  rw [ground.getAt_map_range 0 _ l k, if_pos hk, if_neg h]

private theorem foldDAt (W : List Nat) (l k : Nat) (hk : k < l)
    (h : ¬ l ≤ k + 2) :
    ground.getAt 0 (foldD W l) k
      = 2 * ground.sumNat (List.take (k + 1) W) := by
  show ground.getAt 0 ((List.range l).map (fun x =>
    if l ≤ x + 2 then ground.sumNat W
    else 2 * ground.sumNat (List.take (x + 1) W))) k = _
  rw [ground.getAt_map_range 0 _ l k, if_pos hk, if_neg h]

private theorem hinC (m : Nat) : 2 * (m + 2) + 2 = (m + 3) * 2 := by
  rw [ground.mulAddR m 3 2, Nat.left_distrib 2 m 2,
    Nat.add_assoc (2 * m) (2 * 2) 2, Nat.mul_comm 2 m]

private theorem hinD (m : Nat) : 2 * (2 * m + 3) + 2 = (m + 2) * 4 := by
  rw [ground.mulAddR m 2 4, Nat.left_distrib 2 (2 * m) 3,
    Nat.add_assoc (2 * (2 * m)) (2 * 3) 2, ← ground.mulAssoc 2 2 m,
    Nat.mul_comm 4 m]

private theorem c2DenC (l : Nat) (hl : 2 ≤ l) (E : casfloor.EndFold)
    (hkey : E.key = 2) :
    casfloor.c2Den (sertables.tableC l) E = casDenC l * 2 := by
  match Nat.le.dest hl with
  | ⟨m, hm⟩ =>
    have hm' : m + 2 = l := (Nat.add_comm m 2).trans hm
    rw [← hm']
    show 2 * 1 * E.key
        * (2 * gentable.residue (sertables.tableC (m + 2)) + 2)
      = 4 * (m + 2 + 1) * 2
    rw [hkey, resC m]
    show 4 * (2 * (m + 2) + 2) = 4 * (m + 3) * 2
    rw [hinC m, ground.mulAssoc 4 (m + 3) 2]

private theorem c2DenD (l : Nat) (hl : 3 ≤ l) (E : casfloor.EndFold)
    (hkey : E.key = 2) :
    casfloor.c2Den (sertables.tableD l) E = casDenD l * 4 := by
  match Nat.le.dest hl with
  | ⟨m, hm⟩ =>
    have hm' : m + 3 = l := (Nat.add_comm m 3).trans hm
    rw [← hm']
    show 2 * 1 * E.key
        * (2 * gentable.residue (sertables.tableD (m + 3)) + 2)
      = 4 * (m + 3 - 1) * 4
    rw [hkey, resD m]
    show 4 * (2 * (2 * m + 3) + 2) = 4 * (m + 2) * 4
    rw [hinD m, ground.mulAssoc 4 (m + 2) 4]

private theorem nilOf : ∀ (W : List Nat), W.length ≤ 0 → W = []
  | [], _ => rfl
  | _ :: _, h => absurd h (Nat.not_succ_le_zero _)

/-- The `C` series' Casimir value at the leading family's member. -/
theorem casRead_C : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    casfloor.c2Read (sertables.tableC l) (endC W l)
      (casNumC W l) (casDenC l) := by
  intro W l hs hl
  have hsa := ground.sortedAll W hs
  have hal : W.length ≤ l := Nat.le_trans (Nat.le_add_right W.length 2) hl
  have hl2 : 2 ≤ l := Nat.le_trans (Nat.le_add_left 2 W.length) hl
  have hk3 : ∀ k, k < W.length → k + 3 ≤ l := fun k hk =>
    Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ hk)) hl
  have hk2 : ∀ k, k < W.length → k + 2 ≤ l := fun k hk =>
    Nat.le_trans (Nat.le_succ (k + 2)) (hk3 k hk)
  have hkl : ∀ k, k < W.length → k < l := fun k hk =>
    Nat.lt_of_lt_of_le (ground.ltAddSucc k 1) (hk2 k hk)
  have hne : ∀ k, k < W.length → ¬ l ≤ k + 1 := fun k hk hc =>
    Nat.lt_irrefl (k + 1) (Nat.le_trans (hk2 k hk) hc)
  have hnum : casfloor.c2Num (sertables.tableC l) (endC W l)
      = casNumC W l * 2 := by
    rw [c2NumFold (sertables.tableC l) (endC W l) l 2 (foldC W l)
        (member W l) rfl rfl rfl rfl,
      ground.foldExtend' _ W.length l hal (fun x hx => by
        rw [memberZero W l x hx, Nat.mul_zero, Nat.zero_mul]),
      ground.famFold_congr_range _ (fun k =>
        (ground.sumNat (List.take (k + 1) W)
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))
          + (k + 1) * (2 * l - k)
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))) * 2)
        W.length (fun k hk => by
          rw [foldCAt W l k (hkl k hk) (hne k hk),
            rhoCc l k (hk3 k hk), memberEntry W l k (hkl k hk),
            sertables.lensC_at l k (hkl k hk),
            ground.neBeqOf (fun hc : k + 1 = l =>
              Nat.lt_irrefl (k + 1)
                (Nat.le_trans (hk2 k hk) (Nat.le_of_eq hc.symm)))]
          show (2 * ground.sumNat (List.take (k + 1) W)
                + 2 * ((k + 1) * (2 * l - k)))
              * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)) * 1
            = (ground.sumNat (List.take (k + 1) W)
                * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))
              + (k + 1) * (2 * l - k)
                * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))) * 2
          rw [Nat.mul_one,
            ← Nat.left_distrib 2 (ground.sumNat (List.take (k + 1) W))
              ((k + 1) * (2 * l - k)),
            ground.mulAssoc 2 (ground.sumNat (List.take (k + 1) W)
              + (k + 1) * (2 * l - k))
              (ground.getAt 0 W k - ground.getAt 0 W (k + 1)),
            Nat.mul_comm 2 ((ground.sumNat (List.take (k + 1) W)
              + (k + 1) * (2 * l - k))
              * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))),
            ground.mulAddR (ground.sumNat (List.take (k + 1) W))
              ((k + 1) * (2 * l - k))
              (ground.getAt 0 W k - ground.getAt 0 W (k + 1))]),
      ground.famFold_mulR 2 (fun k =>
        ground.sumNat (List.take (k + 1) W)
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))
          + (k + 1) * (2 * l - k)
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range W.length),
      ground.famFold_add_split
        (fun k => ground.sumNat (List.take (k + 1) W)
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (fun k => (k + 1) * (2 * l - k)
          * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
        (List.range W.length),
      teleAt W (fun x => ground.sumNat (List.take (x + 1) W))
        (fun x => ground.getAt 0 W x) hsa (fun k _ => takeSumStep W k),
      teleAt W (fun x => (x + 1) * (2 * l - x))
        (fun x => 2 * (l - x)) hsa (fun k hk => hUC l k (hk3 k hk)),
      ← dotIndex W W, ← sumSqDot W,
      ← dotMapRange W (fun i => 2 * (l - i))]
    rfl
  show casDenC l * casfloor.c2Num (sertables.tableC l) (endC W l)
    = casNumC W l * casfloor.c2Den (sertables.tableC l) (endC W l)
  rw [hnum, c2DenC l hl2 (endC W l) rfl]
  exact ground.mulLeftComm (casDenC l) (casNumC W l) 2

/-- The `D` series' Casimir value at the leading family's member. -/
theorem casRead_D : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    casfloor.c2Read (sertables.tableD l) (endD W l)
      (casNumD W l) (casDenD l) := by
  intro W l hs hl
  have hsa := ground.sortedAll W hs
  have hal : W.length ≤ l := Nat.le_trans (Nat.le_add_right W.length 2) hl
  have hl2 : 2 ≤ l := Nat.le_trans (Nat.le_add_left 2 W.length) hl
  have hk3 : ∀ k, k < W.length → k + 3 ≤ l := fun k hk =>
    Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ hk)) hl
  have hk2 : ∀ k, k < W.length → k + 2 ≤ l := fun k hk =>
    Nat.le_trans (Nat.le_succ (k + 2)) (hk3 k hk)
  have hkl : ∀ k, k < W.length → k < l := fun k hk =>
    Nat.lt_of_lt_of_le (ground.ltAddSucc k 1) (hk2 k hk)
  have hne : ∀ k, k < W.length → ¬ l ≤ k + 2 := fun k hk hc =>
    Nat.lt_irrefl (k + 2) (Nat.le_trans (hk3 k hk) hc)
  match Nat.le.dest (show 1 ≤ l from
      Nat.le_trans (Nat.le_succ 1) hl2) with
  | ⟨m, hm0⟩ =>
    have hm : m + 1 = l := (Nat.add_comm m 1).trans hm0
    have hnum : casfloor.c2Num (sertables.tableD l) (endD W l)
        = casNumD W l * 4 := by
      rw [c2NumFold (sertables.tableD l) (endD W l) l 2 (foldD W l)
          (member W l) rfl rfl rfl rfl,
        ground.foldExtend' _ W.length l hal (fun x hx => by
          rw [memberZero W l x hx, Nat.mul_zero, Nat.zero_mul]),
        ground.famFold_congr_range _ (fun k =>
          (ground.sumNat (List.take (k + 1) W)
              * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))
            + (k + 1) * (2 * l - (k + 1 + 1))
              * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))) * 4)
          W.length (fun k hk => by
            rw [foldDAt W l k (hkl k hk) (hne k hk),
              rhoDc l m k hm (hk3 k hk), memberEntry W l k (hkl k hk),
              sertables.lensD_at l k (hkl k hk),
              ← Nat.left_distrib 2 (ground.sumNat (List.take (k + 1) W))
                ((k + 1) * (2 * l - (k + 1 + 1))),
              ground.mulAssoc 2 (ground.sumNat (List.take (k + 1) W)
                + (k + 1) * (2 * l - (k + 1 + 1)))
                (ground.getAt 0 W k - ground.getAt 0 W (k + 1)),
              Nat.mul_comm 2 ((ground.sumNat (List.take (k + 1) W)
                + (k + 1) * (2 * l - (k + 1 + 1)))
                * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))),
              ground.mulAssoc ((ground.sumNat (List.take (k + 1) W)
                + (k + 1) * (2 * l - (k + 1 + 1)))
                * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))) 2 2,
              ground.mulAddR (ground.sumNat (List.take (k + 1) W))
                ((k + 1) * (2 * l - (k + 1 + 1)))
                (ground.getAt 0 W k - ground.getAt 0 W (k + 1))]),
        ground.famFold_mulR 4 (fun k =>
          ground.sumNat (List.take (k + 1) W)
              * (ground.getAt 0 W k - ground.getAt 0 W (k + 1))
            + (k + 1) * (2 * l - (k + 1 + 1))
              * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
          (List.range W.length),
        ground.famFold_add_split
          (fun k => ground.sumNat (List.take (k + 1) W)
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
          (fun k => (k + 1) * (2 * l - (k + 1 + 1))
            * (ground.getAt 0 W k - ground.getAt 0 W (k + 1)))
          (List.range W.length),
        teleAt W (fun x => ground.sumNat (List.take (x + 1) W))
          (fun x => ground.getAt 0 W x) hsa (fun k _ => takeSumStep W k),
        teleAt W (fun x => (x + 1) * (2 * l - (x + 1 + 1)))
          (fun x => 2 * (l - (x + 1))) hsa
          (fun k hk => hUD l k (hk3 k hk)),
        ← dotIndex W W, ← sumSqDot W,
        ← dotMapRange W (fun i => 2 * (l - (i + 1)))]
      rfl
    by_cases h3 : 3 ≤ l
    · show casDenD l * casfloor.c2Num (sertables.tableD l) (endD W l)
        = casNumD W l * casfloor.c2Den (sertables.tableD l) (endD W l)
      rw [hnum, c2DenD l h3 (endD W l) rfl]
      exact ground.mulLeftComm (casDenD l) (casNumD W l) 4
    · have hW : W.length ≤ 0 := ground.leCancelR 2
        (show W.length + 2 ≤ 0 + 2 from
          Nat.le_trans hl (Nat.le_of_not_lt h3))
      have hcas : casNumD W l = 0 := by
        rw [nilOf W hW]
        rfl
      show casDenD l * casfloor.c2Num (sertables.tableD l) (endD W l)
        = casNumD W l * casfloor.c2Den (sertables.tableD l) (endD W l)
      rw [hnum, hcas, Nat.zero_mul, Nat.zero_mul, Nat.mul_zero]

/-! ## The polynomial tier: the rank's own coefficient reads

`lem:serstable`(i) states the Casimir as one polynomial pair per
family: the numerator is the word's square fold cleared of the
key-weighted fold, the rank's coefficient the word's doubled
total, and the denominator the adjoint clearing's own constant.
The evaluation is the Horner read at the balance pairs, so the
agreement is a gap of counts — the coefficient's own members
against the argument's scale — and the bridges `casPolyB_eval`,
`casPolyC_eval`, `casPolyD_eval` state it at every rank at or
beyond the word's length, where the root fold's key reads
`2(ℓ − i − 1) + 1`, `2(ℓ − i)` and `2(ℓ − i − 1)` join their
key-weighted partners at the doubled rank. -/

/-! The word's key folds against the rank: the two key-weighted
reads join at the doubled rank, the word's own total the fold. -/

/-- A constant weight over the word's keys folds to the word's
total against it. -/
private theorem foldWConst (W : List Nat) (c : Nat) :
    ground.famFold Nat.add 0 (fun i => ground.getAt 0 W i * c)
      (List.range W.length) = ground.sumNat W * c := by
  rw [ground.famFold_getAt Nat.add 0 (fun x => x * c) 0 W W.length rfl,
    ground.famFold_mulR c (fun x => x) W]
  rfl

/-- Two key families joining at a constant fold the word's total
against it. -/
private theorem casJoin (W : List Nat) (f g : Nat → Nat) (c : Nat)
    (h : ∀ i, i < W.length → f i + g i = c) :
    ground.dotNat W ((List.range W.length).map f)
      + ground.dotNat W ((List.range W.length).map g)
      = ground.sumNat W * c := by
  rw [dotMapRange W f, dotMapRange W g,
    ← ground.famFold_add_split (fun i => ground.getAt 0 W i * f i)
      (fun i => ground.getAt 0 W i * g i) (List.range W.length),
    ground.famFold_congr_range (fun i => ground.getAt 0 W i * f i
        + ground.getAt 0 W i * g i)
      (fun i => ground.getAt 0 W i * c) W.length (fun i hi => by
        rw [← Nat.left_distrib (ground.getAt 0 W i) (f i) (g i), h i hi]),
    foldWConst W c]

/-- The rank's own scale of the word's doubled total. -/
private theorem rankScale (S l : Nat) : S * (2 * l) = l * (2 * S) := by
  rw [← ground.mulAssoc S 2 l, ← ground.mulAssoc l 2 S,
    Nat.mul_comm S 2, Nat.mul_comm l 2, ground.mulAssoc 2 S l,
    ground.mulAssoc 2 l S, Nat.mul_comm S l]

/-- The two key reads' join at a cleared key: the `B` pair. -/
private theorem keyJoinB (l i : Nat) (h : i + 1 ≤ l) :
    (2 * i + 1) + (2 * (l - (i + 1)) + 1) = 2 * l := by
  match Nat.le.dest h with
  | ⟨m, hm⟩ =>
    have hsub : l - (i + 1) = m := by
      rw [← hm]
      exact ground.addSubSelfL (i + 1) m
    rw [hsub, ← hm, Nat.left_distrib 2 (i + 1) m,
      Nat.left_distrib 2 i 1, Nat.mul_one,
      ← Nat.add_assoc (2 * i + 1) (2 * m) 1,
      Nat.add_right_comm (2 * i) 1 (2 * m),
      Nat.add_right_comm (2 * i) 2 (2 * m),
      Nat.add_assoc (2 * i + 2 * m) 1 1]

/-- The two key reads' join at a cleared key: the `C` pair. -/
private theorem keyJoinC (l i : Nat) (h : i ≤ l) :
    2 * i + 2 * (l - i) = 2 * l := by
  match Nat.le.dest h with
  | ⟨m, hm⟩ =>
    have hsub : l - i = m := by
      rw [← hm]
      exact ground.addSubSelfL i m
    rw [hsub, ← hm, Nat.left_distrib 2 i m]

/-- The two key reads' join at a cleared key: the `D` pair. -/
private theorem keyJoinD (l i : Nat) (h : i + 1 ≤ l) :
    2 * (i + 1) + 2 * (l - (i + 1)) = 2 * l := by
  match Nat.le.dest h with
  | ⟨m, hm⟩ =>
    have hsub : l - (i + 1) = m := by
      rw [← hm]
      exact ground.addSubSelfL (i + 1) m
    rw [hsub, ← hm, Nat.left_distrib 2 (i + 1) m]

/-- The `B` Casimir's numerator as a polynomial in the rank: the
word's square fold cleared of the key-weighted fold, the rank's
coefficient the word's doubled total. -/
def casPolyB (W : List Nat) : poly.Poly :=
  [⟨ground.posOfSucc (c2hat.sumSq W),
    ground.posOfSucc (ground.dotNat W
      ((List.range W.length).map (fun i => 2 * i + 1)))⟩,
   ground.BPair.ofNat (2 * ground.sumNat W)]

/-- The `C` Casimir's numerator as a polynomial in the rank. -/
def casPolyC (W : List Nat) : poly.Poly :=
  [⟨ground.posOfSucc (c2hat.sumSq W),
    ground.posOfSucc (2 * ground.dotNat W
      ((List.range W.length).map (fun i => i)))⟩,
   ground.BPair.ofNat (2 * ground.sumNat W)]

/-- The `D` Casimir's numerator as a polynomial in the rank. -/
def casPolyD (W : List Nat) : poly.Poly :=
  [⟨ground.posOfSucc (c2hat.sumSq W),
    ground.posOfSucc (2 * ground.dotNat W
      ((List.range W.length).map (fun i => i + 1)))⟩,
   ground.BPair.ofNat (2 * ground.sumNat W)]

/-- The doubled key fold reads the doubled family. -/
private theorem dotDouble (W : List Nat) (f g : Nat → Nat)
    (h : ∀ i, g i = 2 * f i) :
    2 * ground.dotNat W ((List.range W.length).map f)
      = ground.dotNat W ((List.range W.length).map g) := by
  rw [dotMapRange W f, dotMapRange W g,
    ground.famFold_congr_range (fun i => ground.getAt 0 W i * g i)
      (fun i => ground.getAt 0 W i * f i * 2) W.length (fun i _ => by
        rw [h i, ground.mulLeftComm (ground.getAt 0 W i) 2 (f i),
          Nat.mul_comm 2 (ground.getAt 0 W i * f i)]),
    ground.famFold_mulR 2 (fun i => ground.getAt 0 W i * f i)
      (List.range W.length),
    Nat.mul_comm 2 (ground.famFold Nat.add 0
      (fun i => ground.getAt 0 W i * f i) (List.range W.length))]

/-- `lem:serstable`(i)'s Casimir polynomial at the `B` series: at
every rank at or beyond the word's length the polynomial's value
is the displayed numerator. -/
theorem casPolyB_eval : ∀ (W : List Nat) (l : Nat),
    W.length ≤ l →
    (poly.eval (casPolyB W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (casNumB W l)) := by
  intro W l hal
  refine poly.linRead (c2hat.sumSq W)
    (ground.dotNat W ((List.range W.length).map (fun i => 2 * i + 1)))
    (2 * ground.sumNat W) (casNumB W l) l ?_
  show ground.dotNat W ((List.range W.length).map (fun i => 2 * i + 1))
      + (c2hat.sumSq W + ground.dotNat W ((List.range W.length).map
          (fun i => 2 * (l - (i + 1)) + 1)))
    = c2hat.sumSq W + l * (2 * ground.sumNat W)
  rw [Nat.add_left_comm,
    casJoin W (fun i => 2 * i + 1) (fun i => 2 * (l - (i + 1)) + 1)
      (2 * l) (fun i hi => keyJoinB l i (Nat.le_trans hi hal)),
    rankScale (ground.sumNat W) l]

/-- `lem:serstable`(i)'s Casimir polynomial at the `C` series. -/
theorem casPolyC_eval : ∀ (W : List Nat) (l : Nat),
    W.length ≤ l →
    (poly.eval (casPolyC W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (casNumC W l)) := by
  intro W l hal
  refine poly.linRead (c2hat.sumSq W)
    (2 * ground.dotNat W ((List.range W.length).map (fun i => i)))
    (2 * ground.sumNat W) (casNumC W l) l ?_
  show 2 * ground.dotNat W ((List.range W.length).map (fun i => i))
      + (c2hat.sumSq W + ground.dotNat W ((List.range W.length).map
          (fun i => 2 * (l - i))))
    = c2hat.sumSq W + l * (2 * ground.sumNat W)
  rw [dotDouble W (fun i => i) (fun i => 2 * i) (fun _ => rfl),
    Nat.add_left_comm,
    casJoin W (fun i => 2 * i) (fun i => 2 * (l - i))
      (2 * l) (fun i hi => keyJoinC l i
        (Nat.le_trans (Nat.le_of_lt hi) hal)),
    rankScale (ground.sumNat W) l]

/-- `lem:serstable`(i)'s Casimir polynomial at the `D` series. -/
theorem casPolyD_eval : ∀ (W : List Nat) (l : Nat),
    W.length ≤ l →
    (poly.eval (casPolyD W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (casNumD W l)) := by
  intro W l hal
  refine poly.linRead (c2hat.sumSq W)
    (2 * ground.dotNat W ((List.range W.length).map (fun i => i + 1)))
    (2 * ground.sumNat W) (casNumD W l) l ?_
  show 2 * ground.dotNat W ((List.range W.length).map (fun i => i + 1))
      + (c2hat.sumSq W + ground.dotNat W ((List.range W.length).map
          (fun i => 2 * (l - (i + 1)))))
    = c2hat.sumSq W + l * (2 * ground.sumNat W)
  rw [dotDouble W (fun i => i + 1) (fun i => 2 * (i + 1)) (fun _ => rfl),
    Nat.add_left_comm,
    casJoin W (fun i => 2 * (i + 1)) (fun i => 2 * (l - (i + 1)))
      (2 * l) (fun i hi => keyJoinD l i (Nat.le_trans hi hal)),
    rankScale (ground.sumNat W) l]

/-! ## The dimension tier: the member's gap product

`cor:weyldim`'s gap product at the leading family's member.  The
concrete gap at a positive fold `f` against a coroot list `v` is
`Σ_k f_k · lenNums_k · v_k`, the halved products cleared at
`2 lenDen`; the member's dimension is the gap product at
`member + ρ` against the gap product at `ρ`, and the four factor
classes close the cross-multiplied identity — the tail factors
read one on both sides, the word-against-word difference factors
are rank-free, the word sums and the short or long factors are
single linear reads in the rank, and the word-against-tail factors
telescope over the position gaps. -/

/-- The member raised by `ρ`, the coroot presentation: the padded
word's consecutive gaps each raised by one. -/
def memberRho (W : List Nat) (l : Nat) : List Nat :=
  (member W l).map (· + 1)

/-- The concrete gap at a positive fold against a coroot list. -/
def gapAt (t : gentable.Table) (v : List Nat) (j : Nat) : Nat :=
  ground.dotNat (ground.getAt [] t.posFolds j)
    (List.zipWith Nat.mul t.lenNums v)

/-- The `B` member's dimension numerator: the word-against-word
difference and sum factors, the short factors, and the two
word-against-tail telescopes. -/
def dimNumB (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - 1 - p.1 - p.2))) 1
  let sh := (List.range a).foldl (fun acc i =>
    acc * (2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))) 1
  let t1 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (ground.getAt 0 W i + (a - i + k))) 1) 1
  let t2 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (ground.getAt 0 W i + (l - i + k))) 1) 1
  dif * sm * sh * t1 * t2

/-- The `B` member's dimension denominator, the numerator's reads
at the vacant word. -/
def dimDenB (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (2 * l - 1 - p.1 - p.2)) 1
  let sh := (List.range a).foldl (fun acc i => acc * (2 * l - 1 - 2 * i)) 1
  let t1 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (a - i + k)) 1) 1
  let t2 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (l - i + k)) 1) 1
  dif * sm * sh * t1 * t2

/-- The `C` member's dimension numerator. -/
def dimNumC (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - p.1 - p.2))) 1
  let lg := (List.range a).foldl (fun acc i =>
    acc * (ground.getAt 0 W i + (l - i))) 1
  let t1 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (ground.getAt 0 W i + (a - i + k))) 1) 1
  let t2 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (ground.getAt 0 W i + (l - i + 1 + k))) 1) 1
  dif * sm * lg * t1 * t2

/-- The `C` member's dimension denominator. -/
def dimDenC (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (2 * l - p.1 - p.2)) 1
  let lg := (List.range a).foldl (fun acc i => acc * (l - i)) 1
  let t1 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (a - i + k)) 1) 1
  let t2 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (l - i + 1 + k)) 1) 1
  dif * sm * lg * t1 * t2

/-- The `D` member's dimension numerator. -/
def dimNumD (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - 2 - p.1 - p.2))) 1
  let t1 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (ground.getAt 0 W i + (a - i + k))) 1) 1
  let t2 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (ground.getAt 0 W i + (l - i - 1 + k))) 1) 1
  dif * sm * t1 * t2

/-- The `D` member's dimension denominator. -/
def dimDenD (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (2 * l - 2 - p.1 - p.2)) 1
  let t1 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (a - i + k)) 1) 1
  let t2 := (List.range a).foldl (fun acc i =>
    acc * (List.range (l - a)).foldl (fun acc2 k =>
      acc2 * (l - i - 1 + k)) 1) 1
  dif * sm * t1 * t2

/-! ## The multiplicative fold kit -/

private theorem mulSnoc {α : Type} (f : α → Nat) (K : List α) (x : α) :
    ground.famFold Nat.mul 1 f (K ++ [x])
      = ground.famFold Nat.mul 1 f K * f x := by
  rw [ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul f K [x]]
  show ground.famFold Nat.mul 1 f K * (f x * 1) = _
  rw [Nat.mul_one]

private theorem mulOnes {α : Type} : ∀ L : List α,
    ground.famFold Nat.mul 1 (fun _ => (1 : Nat)) L = 1
  | [] => rfl
  | _ :: t => by
    show 1 * ground.famFold Nat.mul 1 (fun _ => (1 : Nat)) t = 1
    rw [mulOnes t]

private theorem mulRangeCongr (f g : Nat → Nat) (L : Nat)
    (hx : ∀ x, x < L → f x = g x) :
    ground.famFold Nat.mul 1 f (List.range L)
      = ground.famFold Nat.mul 1 g (List.range L) :=
  ground.famFold_congr_members Nat.mul 1 f g (List.range L)
    (fun x hp => hx x (ground.ltOfMem hp))

private theorem mulRangeSplit (f : Nat → Nat) (m : Nat) : ∀ n : Nat,
    ground.famFold Nat.mul 1 f (List.range (m + n))
      = ground.famFold Nat.mul 1 f (List.range m)
        * ground.famFold Nat.mul 1 (fun e => f (m + e)) (List.range n)
  | 0 => (Nat.mul_one _).symm
  | n + 1 => by
    rw [show m + (n + 1) = m + n + 1 from rfl,
      ground.range_succ (m + n),
      mulSnoc f (List.range (m + n)) (m + n),
      mulRangeSplit f m n, ground.range_succ n,
      mulSnoc (fun e => f (m + e)) (List.range n) n,
      ground.mulAssoc]

private theorem mulPair {α : Type} (f g : α → Nat) : ∀ L : List α,
    ground.famFold Nat.mul 1 (fun x => f x * g x) L
      = ground.famFold Nat.mul 1 f L * ground.famFold Nat.mul 1 g L
  | [] => rfl
  | a :: t => by
    show f a * g a * ground.famFold Nat.mul 1 (fun x => f x * g x) t
      = f a * ground.famFold Nat.mul 1 f t
        * (g a * ground.famFold Nat.mul 1 g t)
    rw [mulPair f g t, ground.mulMulMulComm]

private theorem mulPairsFold (F : Nat × Nat → Nat) : ∀ L : Nat,
    ground.famFold Nat.mul 1 F (places.pairsOf L)
      = ground.famFold Nat.mul 1
          (fun d => ground.famFold Nat.mul 1 (fun j => F (j, d))
            (List.range d)) (List.range L)
  | 0 => rfl
  | L + 1 => by
    rw [show places.pairsOf (L + 1)
        = places.pairsOf L ++ (List.range L).map (fun j => (j, L)) from rfl,
      ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul F
        (places.pairsOf L) ((List.range L).map (fun j => (j, L))),
      ground.famFold_map Nat.mul 1 F (fun j => (j, L)) (List.range L),
      mulPairsFold F L, ground.range_succ L,
      mulSnoc (fun d => ground.famFold Nat.mul 1
        (fun j => F (j, d)) (List.range d)) (List.range L) L]
    rfl

private theorem mulShift (g : Nat → Nat) : ∀ n : Nat,
    ground.famFold Nat.mul 1 g (List.range (n + 1))
      = g 0 * ground.famFold Nat.mul 1 (fun i => g (i + 1)) (List.range n)
  | 0 => by
    show g 0 * 1 = g 0 * 1
    rfl
  | n + 1 => by
    rw [ground.range_succ (n + 1), mulSnoc g (List.range (n + 1)) (n + 1),
      mulShift g n, ground.range_succ n,
      mulSnoc (fun i => g (i + 1)) (List.range n) n, ground.mulAssoc]

private theorem mulSwap (F : Nat → Nat → Nat) (n : Nat) : ∀ m : Nat,
    ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun j => F i j) (List.range n))
        (List.range m)
      = ground.famFold Nat.mul 1
        (fun j => ground.famFold Nat.mul 1 (fun i => F i j) (List.range m))
        (List.range n)
  | 0 => (mulOnes (List.range n)).symm
  | m + 1 => by
    have hR : ground.famFold Nat.mul 1
        (fun j => ground.famFold Nat.mul 1 (fun i => F i j)
          (List.range (m + 1))) (List.range n)
      = ground.famFold Nat.mul 1
        (fun j => ground.famFold Nat.mul 1 (fun i => F i j)
          (List.range m) * F m j) (List.range n) :=
      mulRangeCongr _ _ n (fun j _ => by
        rw [ground.range_succ m, mulSnoc (fun i => F i j) (List.range m) m])
    rw [hR, mulPair (fun j => ground.famFold Nat.mul 1 (fun i => F i j)
        (List.range m)) (fun j => F m j) (List.range n),
      ← mulSwap F n m, ground.range_succ m,
      mulSnoc (fun i => ground.famFold Nat.mul 1 (fun j => F i j)
        (List.range n)) (List.range m) m]

private theorem mulRev (g : Nat → Nat) : ∀ n : Nat,
    ground.famFold Nat.mul 1 g (List.range n)
      = ground.famFold Nat.mul 1 (fun k => g (n - 1 - k)) (List.range n)
  | 0 => rfl
  | n + 1 => by
    rw [mulShift (fun k => g (n + 1 - 1 - k)) n,
      mulRangeCongr (fun i => g (n + 1 - 1 - (i + 1)))
        (fun k => g (n - 1 - k)) n (fun x _ => by
          show g (n - (x + 1)) = g (n - 1 - x)
          rw [ground.subSub n 1 x, Nat.add_comm 1 x]),
      ← mulRev g n, ground.range_succ n, mulSnoc g (List.range n) n]
    exact Nat.mul_comm _ _

private theorem foldlFam {α : Type} (F : α → Nat) (L : List α) :
    L.foldl (fun a x => a * F x) 1 = ground.famFold Nat.mul 1 F L := by
  rw [ground.foldlProd F L 1, Nat.one_mul]

/-! ## The pair family's split at the word boundary -/

private theorem pairsSplit (F : Nat → Nat → Nat) (a n : Nat) :
    ground.famFold Nat.mul 1 (fun p => F p.1 p.2) (places.pairsOf (a + n))
      = ground.famFold Nat.mul 1 (fun p => F p.1 p.2) (places.pairsOf a)
        * (ground.famFold Nat.mul 1
            (fun i => ground.famFold Nat.mul 1 (fun e => F i (a + e))
              (List.range n)) (List.range a)
          * ground.famFold Nat.mul 1
            (fun e => ground.famFold Nat.mul 1 (fun j => F (a + j) (a + e))
              (List.range e)) (List.range n)) := by
  rw [mulPairsFold (fun p => F p.1 p.2) (a + n),
    mulPairsFold (fun p => F p.1 p.2) a,
    mulRangeSplit
      (fun d => ground.famFold Nat.mul 1 (fun j => F j d) (List.range d))
      a n,
    mulRangeCongr
      (fun e => ground.famFold Nat.mul 1 (fun j => F j (a + e))
        (List.range (a + e)))
      (fun e => ground.famFold Nat.mul 1 (fun j => F j (a + e))
          (List.range a)
        * ground.famFold Nat.mul 1 (fun j => F (a + j) (a + e))
          (List.range e)) n
      (fun e _ => mulRangeSplit (fun j => F j (a + e)) a e),
    mulPair
      (fun e => ground.famFold Nat.mul 1 (fun j => F j (a + e))
        (List.range a))
      (fun e => ground.famFold Nat.mul 1 (fun j => F (a + j) (a + e))
        (List.range e)) (List.range n),
    mulSwap (fun i e => F i (a + e)) n a]

/-! ## The window sums of a weight family -/

/-- The occupancy window's weighted sum: the weights inside the
window, nothing outside it. -/
private theorem windowSum (wt : Nat → Nat) (a s r : Nat) :
    ground.famFold Nat.add 0
      (fun k => (if a ≤ k && k < a + s then 1 else 0) * wt k)
      (List.range (a + (s + r)))
      = ground.famFold Nat.add 0 (fun e => wt (a + e)) (List.range s) := by
  rw [foldRangeSplit
      (fun k => (if a ≤ k && k < a + s then 1 else 0) * wt k) a (s + r),
    ground.famFold_congr_range
      (fun k => (if a ≤ k && k < a + s then 1 else 0) * wt k)
      (fun _ => (0 : Nat)) a (fun x hx => by
        rw [indValLo a (a + s) x (fun hc =>
          Nat.lt_irrefl x (Nat.lt_of_lt_of_le hx hc)), Nat.zero_mul]),
    foldZero (List.range a), Nat.zero_add,
    foldRangeSplit
      (fun e => (if a ≤ a + e && a + e < a + s then 1 else 0) * wt (a + e))
      s r,
    ground.famFold_congr_range
      (fun e => (if a ≤ a + e && a + e < a + s then 1 else 0) * wt (a + e))
      (fun e => wt (a + e)) s (fun x hx => by
        rw [show (if a ≤ a + x && a + x < a + s then (1 : Nat) else 0) = 1 from
          if_pos (by
            rw [decide_eq_true (Nat.le_add_right a x),
              decide_eq_true (Nat.add_lt_add_left hx a)]
            rfl), Nat.one_mul]),
    ground.famFold_congr_range
      (fun e => (if a ≤ a + (s + e) && a + (s + e) < a + s then 1 else 0)
        * wt (a + (s + e)))
      (fun _ => (0 : Nat)) r (fun x _ => by
        rw [indValOut a (a + s) (a + (s + x)) (fun hc =>
          Nat.lt_irrefl (a + s) (Nat.lt_of_le_of_lt
            (Nat.add_le_add_left (Nat.le_add_right s x) a) hc)),
          Nat.zero_mul]),
    foldZero (List.range r), Nat.add_zero]

/-! ## The clearing and linear-form kit -/

/-- Two successive clearings at a joined pair. -/
private theorem sub2 (X i j c : Nat) (h : X = i + j + c) : X - i - j = c :=
  subOf (X - i) j c (subOf X i (c + j)
    (by rw [h, Nat.add_comm (c + j) i, Nat.add_comm c j,
      ← Nat.add_assoc i j c]))

/-- A unit clearing ahead of the pair. -/
private theorem sub1c (X i j c : Nat) (h : X = i + j + (c + 1)) :
    X - 1 - i - j = c :=
  sub2 (X - 1) i j c (subOf X 1 (i + j + c)
    (by rw [h, Nat.add_assoc (i + j) c 1]))

/-- A doubled clearing ahead of the pair. -/
private theorem sub2c (X i j c : Nat) (h : X = i + j + (c + 2)) :
    X - 2 - i - j = c :=
  sub2 (X - 2) i j c (subOf X 2 (i + j + c)
    (by rw [h, Nat.add_assoc (i + j) c 2]))

/-- A unit clearing ahead of a single key. -/
private theorem sub1b (X b c : Nat) (h : X = b + (c + 1)) : X - 1 - b = c :=
  subOf (X - 1) b c (subOf X 1 (c + b)
    (by rw [h, Nat.add_comm c b, Nat.add_assoc b c 1]))

private theorem sumBform2 (i s r l : Nat) (hl : i + s + (r + 1) = l) :
    2 * l = i + (i + s) + (s + (2 * r + 1) + 1) := by
  rw [← hl, Nat.left_distrib 2 (i + s) (r + 1), Nat.two_mul (i + s),
    Nat.left_distrib 2 r 1, Nat.mul_one,
    ← Nat.add_assoc (i + s) i s, Nat.add_comm (i + s) i,
    Nat.add_assoc (i + (i + s)) s (2 * r + 2),
    ← Nat.add_assoc s (2 * r + 1) 1]

private theorem sumDform2 (i s r l : Nat) (hl : i + s + (r + 2) = l) :
    2 * l = i + (i + s) + (s + (2 * r + 2) + 2) := by
  rw [← hl, Nat.left_distrib 2 (i + s) (r + 2), Nat.two_mul (i + s),
    Nat.left_distrib 2 r 2,
    ← Nat.add_assoc (i + s) i s, Nat.add_comm (i + s) i,
    Nat.add_assoc (i + (i + s)) s (2 * r + 2 * 2),
    ← Nat.add_assoc s (2 * r + 2) 2]

private theorem arithSumB (P Wj Wi s r Q : Nat) (h : P + Wj = Wi)
    (hQ : s + (2 * r + 1) = Q) :
    2 * (P + s) + (2 * (Wj + r) + 1 + (2 * (Wj + r) + 1))
      = 2 * (Wi + Wj + Q) := by
  rw [← h, ← hQ, ← Nat.two_mul (2 * (Wj + r) + 1),
    ← Nat.left_distrib 2 (P + s) (2 * (Wj + r) + 1),
    Nat.left_distrib 2 Wj r, Nat.two_mul Wj,
    addSwap P s (Wj + Wj + 2 * r) 1,
    ← Nat.add_assoc P (Wj + Wj) (2 * r), ← Nat.add_assoc P Wj Wj,
    Nat.add_assoc (P + Wj + Wj) (2 * r) (s + 1),
    Nat.add_left_comm (2 * r) s 1]

private theorem arithSumC (P Wj Wi s r Q : Nat) (h : P + Wj = Wi)
    (hQ : s + (2 * r + 2) = Q) :
    P + s + (Wj + r + (Wj + r) + 2) = Wi + Wj + Q := by
  rw [← h, ← hQ, addSwap Wj r Wj r, ← Nat.two_mul r,
    addSwap P s (Wj + Wj + 2 * r) 2,
    ← Nat.add_assoc P (Wj + Wj) (2 * r), ← Nat.add_assoc P Wj Wj,
    Nat.add_assoc (P + Wj + Wj) (2 * r) (s + 2),
    Nat.add_left_comm (2 * r) s 2]

private theorem arithSumDg (P Wj Wi s r Q : Nat) (h : P + Wj = Wi)
    (hQ : s + (2 * r + 2) = Q) :
    2 * (P + s) + (2 * (Wj + r) + 2 * (Wj + r) + 4)
      = 2 * (Wi + Wj + Q) := by
  rw [← h, ← hQ, ← Nat.two_mul (2 * (Wj + r)),
    show (4 : Nat) = 2 * 2 from rfl,
    ← Nat.left_distrib 2 (2 * (Wj + r)) 2,
    ← Nat.left_distrib 2 (P + s) (2 * (Wj + r) + 2),
    Nat.left_distrib 2 Wj r, Nat.two_mul Wj,
    addSwap P s (Wj + Wj + 2 * r) 2,
    ← Nat.add_assoc P (Wj + Wj) (2 * r), ← Nat.add_assoc P Wj Wj,
    Nat.add_assoc (P + Wj + Wj) (2 * r) (s + 2),
    Nat.add_left_comm (2 * r) s 2]

private theorem shBform (i r l : Nat) (hl : i + (r + 1) = l) :
    2 * l = 2 * i + (2 * r + 1 + 1) := by
  rw [← hl, Nat.left_distrib 2 i (r + 1), Nat.left_distrib 2 r 1,
    Nat.mul_one, ← Nat.add_assoc (2 * i) (2 * r) 2]

private theorem lgCform (i r l : Nat) (hl : i + (r + 1) = l) : l - i = r + 1 :=
  subOf l i (r + 1) (by rw [← hl, Nat.add_comm i (r + 1)])

private theorem arithShB (X r : Nat) : 2 * (X + r) + 1 = 2 * X + (2 * r + 1) := by
  rw [Nat.left_distrib 2 X r, Nat.add_assoc (2 * X) (2 * r) 1]

private theorem arithLgC (X r : Nat) :
    X + r + (X + r) + 2 = 2 * (X + (r + 1)) := by
  rw [addSwap X r X r, ← Nat.two_mul X, ← Nat.two_mul r,
    Nat.left_distrib 2 X (r + 1), Nat.left_distrib 2 r 1, Nat.mul_one,
    Nat.add_assoc (2 * X) (2 * r) 2]

private theorem arithSumDt (X q : Nat) : 2 * (X + q) + 2 = 2 * (X + 0 + (q + 1)) := by
  rw [Nat.add_zero X, Nat.left_distrib 2 X (q + 1),
    Nat.left_distrib 2 q 1, Nat.mul_one, Nat.left_distrib 2 X q,
    Nat.add_assoc (2 * X) (2 * q) 2]

private theorem mixDif (a i e : Nat) (h : i ≤ a) : a + e - i = a - i + e :=
  subOf (a + e) i (a - i + e) (by
    rw [Nat.add_assoc (a - i) e i, Nat.add_comm e i,
      ← Nat.add_assoc (a - i) i e, ground.subAdd h])

private theorem sumDtform (i q j l : Nat) (hl : i + (q + 2) = l) (hj : j + 1 = l) :
    2 * l = i + j + (q + 1 + 2) := by
  have hji : j = i + (q + 1) := Nat.succ.inj
    (show j + 1 = i + (q + 1) + 1 by
      rw [hj, ← hl, Nat.add_assoc i (q + 1) 1])
  rw [hji, ← hl, show q + 2 = q + 1 + 1 from rfl,
    Nat.two_mul (i + (q + 1 + 1)),
    ← Nat.add_assoc (i + (q + 1 + 1)) i (q + 1 + 1),
    Nat.add_comm (i + (q + 1 + 1)) i,
    ← Nat.add_assoc i (q + 1) 1,
    ← Nat.add_assoc i (i + (q + 1)) 1,
    Nat.add_assoc (i + (i + (q + 1))) 1 (q + 1 + 1),
    Nat.add_comm 1 (q + 1 + 1)]

private theorem mixFormB (l a i n k c : Nat) (hn : a + n = l) (hc : c + (k + 1) = n)
    (hi : i ≤ l) : 2 * l = i + (a + c) + (l - i + k + 1) := by
  have h1 : i + (l - i) = l := ground.natAddSubCancel hi
  have h2 : a + (c + (k + 1)) = l := by rw [hc, hn]
  rw [Nat.two_mul l]
  conv => lhs; lhs; rw [← h1]
  conv => lhs; rhs; rw [← h2]
  rw [addSwap i (l - i) a (c + (k + 1)),
    Nat.add_left_comm (l - i) c (k + 1),
    ← Nat.add_assoc (i + a) c (l - i + (k + 1)),
    Nat.add_assoc i a c, ← Nat.add_assoc (l - i) k 1]

private theorem mixFormC (l a i n k c : Nat) (hn : a + n = l) (hc : c + (k + 1) = n)
    (hi : i ≤ l) : 2 * l = i + (a + c) + (l - i + 1 + k) := by
  rw [mixFormB l a i n k c hn hc hi, Nat.add_assoc (l - i) k 1,
    Nat.add_comm k 1, ← Nat.add_assoc (l - i) 1 k]

private theorem mixFormD (l a i n k c : Nat) (hn : a + n = l) (hc : c + (k + 1) = n)
    (hi : i + 1 ≤ l) : 2 * l = i + (a + c) + (l - i - 1 + k + 2) := by
  have h1 : i + 1 + (l - (i + 1)) = l := ground.natAddSubCancel hi
  have h2 : a + (c + (k + 1)) = l := by rw [hc, hn]
  rw [ground.subSub l i 1, Nat.two_mul l]
  conv => lhs; lhs; rw [← h1]
  conv => lhs; rhs; rw [← h2]
  rw [Nat.add_assoc i 1 (l - (i + 1)),
    addSwap i (1 + (l - (i + 1))) a (c + (k + 1)),
    Nat.add_left_comm (1 + (l - (i + 1))) c (k + 1),
    ← Nat.add_assoc (i + a) c (1 + (l - (i + 1)) + (k + 1)),
    Nat.add_assoc i a c,
    Nat.add_comm 1 (l - (i + 1)),
    addSwap (l - (i + 1)) 1 k 1]


/-! ## The member's window telescope -/

private theorem subChain (x y z : Nat) (h1 : y ≤ x) (h2 : z ≤ y) :
    x - y + (y - z) = x - z :=
  (subOf x z (x - y + (y - z)) (by
    rw [Nat.add_assoc (x - y) (y - z) z, ground.subAdd h2,
      ground.subAdd h1])).symm

/-- The raised member's window sum telescopes to the word's gap
across the window joined to the window's own width. -/
private theorem gapWindow (W v : List Nat) (l : Nat)
    (hs : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (a : Nat) : ∀ s : Nat, a + s ≤ l →
    ground.famFold Nat.add 0 (fun e => ground.getAt 0 v (a + e))
      (List.range s)
      = ground.getAt 0 W a - ground.getAt 0 W (a + s) + s
  | 0, _ => by
    show (0 : Nat) = ground.getAt 0 W a - ground.getAt 0 W (a + 0) + 0
    rw [Nat.add_zero a, Nat.sub_self]
  | s + 1, hle => by
    rw [ground.range_succ s,
      ground.famFold_snoc (fun e => ground.getAt 0 v (a + e))
        (List.range s) s,
      gapWindow W v l hs hv a s (Nat.le_trans (Nat.le_succ (a + s)) hle),
      hv (a + s) (Nat.lt_of_lt_of_le (Nat.lt_succ_self (a + s)) hle),
      addSwap (ground.getAt 0 W a - ground.getAt 0 W (a + s)) s
        (ground.getAt 0 W (a + s) - ground.getAt 0 W (a + s + 1)) 1,
      subChain (ground.getAt 0 W a) (ground.getAt 0 W (a + s))
        (ground.getAt 0 W (a + s + 1)) (ground.descChain W hs a s) (hs (a + s))]
    rfl

/-- A positive fold's gap against a coroot list, the weighted key
fold. -/
private theorem gapWeight (lens v f : List Nat) (l : Nat)
    (hlen : lens.length = l) (hv : v.length = l) (hf : f.length = l) :
    ground.dotNat f (List.zipWith Nat.mul lens v)
      = ground.famFold Nat.add 0
        (fun k => ground.getAt 0 f k
          * (ground.getAt 0 lens k * ground.getAt 0 v k))
        (List.range l) := by
  rw [dotIndex, hf]
  exact ground.famFold_congr_range _ _ l (fun k hk => by
    rw [ground.getAt_zipWith 0 0 0 Nat.mul lens v k
      (by rw [hlen]; exact hk) (by rw [hv]; exact hk)]
    rfl)

/-- The occupancy window's weighted fold at a stated rank. -/
private theorem indWindow (wt : Nat → Nat) (l a s r : Nat)
    (hl : a + s + r = l) :
    ground.famFold Nat.add 0
      (fun k => (if a ≤ k && k < a + s then 1 else 0) * wt k) (List.range l)
      = ground.famFold Nat.add 0 (fun e => wt (a + e)) (List.range s) := by
  rw [← hl, Nat.add_assoc a s r]
  exact windowSum wt a s r

private theorem lensBLen (l : Nat) :
    (sertables.tableB l).lenNums.length = l :=
  ground.length_mapRange _ l

private theorem lensCLen (l : Nat) :
    (sertables.tableC l).lenNums.length = l :=
  ground.length_mapRange _ l

private theorem lensDLen (l : Nat) :
    (sertables.tableD l).lenNums.length = l := by
  show (List.replicate l 2).length = l
  exact ground.length_replicate 2 l

private theorem lensBOff (l k : Nat) (hk : k < l) (hne : ¬ k + 1 = l) :
    ground.getAt 0 (sertables.tableB l).lenNums k = 2 := by
  rw [sertables.lensB_at l k hk, ground.neBeqOf hne]
  rfl

private theorem lensBEnd (l k : Nat) (hk : k < l) (he : k + 1 = l) :
    ground.getAt 0 (sertables.tableB l).lenNums k = 1 := by
  rw [sertables.lensB_at l k hk, ground.eqBeqOf he]
  rfl

private theorem lensCOff (l k : Nat) (hk : k < l) (hne : ¬ k + 1 = l) :
    ground.getAt 0 (sertables.tableC l).lenNums k = 1 := by
  rw [sertables.lensC_at l k hk, ground.neBeqOf hne]
  rfl

private theorem lensCEnd (l k : Nat) (hk : k < l) (he : k + 1 = l) :
    ground.getAt 0 (sertables.tableC l).lenNums k = 2 := by
  rw [sertables.lensC_at l k hk, ground.eqBeqOf he]
  rfl

/-- A `B` window below the short key: the doubled telescope. -/
private theorem winB (W v : List Nat) (l i s t : Nat)
    (hs : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hl : i + s + (t + 1) = l) :
    ground.famFold Nat.add 0
      (fun e => ground.getAt 0 (sertables.tableB l).lenNums (i + e)
        * ground.getAt 0 v (i + e)) (List.range s)
      = 2 * (ground.getAt 0 W i - ground.getAt 0 W (i + s) + s) := by
  have hisl : i + s < l := by
    rw [← hl]
    exact ground.ltAddSucc (i + s) t
  rw [ground.famFold_congr_range
      (fun e => ground.getAt 0 (sertables.tableB l).lenNums (i + e)
        * ground.getAt 0 v (i + e))
      (fun e => 2 * ground.getAt 0 v (i + e)) s
      (fun e he => by
        rw [lensBOff l (i + e)
          (Nat.lt_trans (Nat.add_lt_add_left he i) hisl)
          (Nat.ne_of_lt (Nat.lt_of_le_of_lt
            (Nat.succ_le_of_lt (Nat.add_lt_add_left he i)) hisl))]),
    ← ground.famFold_mul 2 (fun e => ground.getAt 0 v (i + e))
      (List.range s),
    gapWindow W v l hs hv i s (Nat.le_of_lt hisl)]

/-- The `B` window through the short key. -/
private theorem winBtop (W v : List Nat) (l i s : Nat)
    (hs : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hl : i + s + 1 = l) (hz : ground.getAt 0 W (i + s) = 0) :
    ground.famFold Nat.add 0
      (fun e => ground.getAt 0 (sertables.tableB l).lenNums (i + e)
        * ground.getAt 0 v (i + e)) (List.range (s + 1))
      = 2 * (ground.getAt 0 W i + s) + 1 := by
  have hisl : i + s < l := by
    rw [← hl]
    exact Nat.lt_succ_self (i + s)
  rw [ground.range_succ s,
    ground.famFold_snoc
      (fun e => ground.getAt 0 (sertables.tableB l).lenNums (i + e)
        * ground.getAt 0 v (i + e)) (List.range s) s,
    winB W v l i s 0 hs hv hl,
    lensBEnd l (i + s) hisl hl, hv (i + s) hisl,
    hz, Nat.sub_zero, Nat.zero_sub, Nat.zero_add, Nat.one_mul]

/-- A `C` window below the long key. -/
private theorem winC (W v : List Nat) (l i s t : Nat)
    (hs : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hl : i + s + (t + 1) = l) :
    ground.famFold Nat.add 0
      (fun e => ground.getAt 0 (sertables.tableC l).lenNums (i + e)
        * ground.getAt 0 v (i + e)) (List.range s)
      = ground.getAt 0 W i - ground.getAt 0 W (i + s) + s := by
  have hisl : i + s < l := by
    rw [← hl]
    exact ground.ltAddSucc (i + s) t
  rw [ground.famFold_congr_range
      (fun e => ground.getAt 0 (sertables.tableC l).lenNums (i + e)
        * ground.getAt 0 v (i + e))
      (fun e => ground.getAt 0 v (i + e)) s
      (fun e he => by
        rw [lensCOff l (i + e)
          (Nat.lt_trans (Nat.add_lt_add_left he i) hisl)
          (Nat.ne_of_lt (Nat.lt_of_le_of_lt
            (Nat.succ_le_of_lt (Nat.add_lt_add_left he i)) hisl)),
          Nat.one_mul]),
    gapWindow W v l hs hv i s (Nat.le_of_lt hisl)]

/-- A `D` window: every key doubled. -/
private theorem winD (W v : List Nat) (l i s : Nat)
    (hs : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hle : i + s ≤ l) :
    ground.famFold Nat.add 0
      (fun e => ground.getAt 0 (sertables.tableD l).lenNums (i + e)
        * ground.getAt 0 v (i + e)) (List.range s)
      = 2 * (ground.getAt 0 W i - ground.getAt 0 W (i + s) + s) := by
  rw [ground.famFold_congr_range
      (fun e => ground.getAt 0 (sertables.tableD l).lenNums (i + e)
        * ground.getAt 0 v (i + e))
      (fun e => 2 * ground.getAt 0 v (i + e)) s
      (fun e he => by
        rw [sertables.lensD_at l (i + e) (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left he i) hle)]),
    ← ground.famFold_mul 2 (fun e => ground.getAt 0 v (i + e))
      (List.range s),
    gapWindow W v l hs hv i s hle]

/-- The occupancy window at a named upper key. -/
private theorem indWindowAt (wt : Nat → Nat) (l a s r b : Nat)
    (hl : a + s + r = l) (hb : a + s = b) :
    ground.famFold Nat.add 0
      (fun k => (if a ≤ k && k < b then 1 else 0) * wt k) (List.range l)
      = ground.famFold Nat.add 0 (fun e => wt (a + e)) (List.range s) := by
  rw [← hb]
  exact indWindow wt l a s r hl

/-! ## The `B` families' gaps in closed form -/

/-- The `B` difference family's gap at a coordinate pair. -/
private theorem gapDifB (W v : List Nat) (l i s t : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + s + (t + 1) = l) :
    ground.dotNat (sertables.diffFold l i (i + s))
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)
      = 2 * (ground.getAt 0 W i - ground.getAt 0 W (i + s) + s) := by
  rw [gapWeight (sertables.tableB l).lenNums v
      (sertables.diffFold l i (i + s)) l (lensBLen l) hvl
      (diffLen l i (i + s)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + s then 1 else 0)
        * (ground.getAt 0 (sertables.tableB l).lenNums k
          * ground.getAt 0 v k)) l
      (fun k hk => by rw [diffAt l i (i + s) k hk]),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableB l).lenNums k
      * ground.getAt 0 v k) l i s (t + 1) (i + s) hl rfl,
    winB W v l i s t hsa hv hl]

/-- The `B` sum family's gap at a coordinate pair. -/
private theorem gapSumB (W v : List Nat) (l i s r : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + s + (r + 1) = l)
    (hz : ground.getAt 0 W (i + s + r) = 0) :
    ground.dotNat (sertables.sumFoldB l i (i + s))
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)
      = 2 * (ground.getAt 0 W i + ground.getAt 0 W (i + s)
          + (2 * l - 1 - i - (i + s))) := by
  rw [gapWeight (sertables.tableB l).lenNums v
      (sertables.sumFoldB l i (i + s)) l (lensBLen l) hvl
      (sumBLen l i (i + s)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + s then 1 else 0)
          * (ground.getAt 0 (sertables.tableB l).lenNums k
            * ground.getAt 0 v k)
        + ((if i + s ≤ k && k < l then 1 else 0)
            * (ground.getAt 0 (sertables.tableB l).lenNums k
              * ground.getAt 0 v k)
          + (if i + s ≤ k && k < l then 1 else 0)
            * (ground.getAt 0 (sertables.tableB l).lenNums k
              * ground.getAt 0 v k))) l
      (fun k hk => by
        rw [sumBAt l i (i + s) k hk, ground.mulAddR, ground.mulAddR]),
    ground.famFold_add_split _ _ (List.range l),
    ground.famFold_add_split _ _ (List.range l),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableB l).lenNums k
      * ground.getAt 0 v k) l i s (r + 1) (i + s) hl rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableB l).lenNums k
      * ground.getAt 0 v k) l (i + s) (r + 1) 0 l
      (by rw [Nat.add_zero]; exact hl) hl,
    winB W v l i s r hsa hv hl,
    winBtop W v l (i + s) r hsa hv hl hz]
  exact arithSumB (ground.getAt 0 W i - ground.getAt 0 W (i + s))
    (ground.getAt 0 W (i + s)) (ground.getAt 0 W i) s r
    (2 * l - 1 - i - (i + s))
    (ground.subAdd (ground.descChain W hsa i s))
    (sub1c (2 * l) i (i + s) (s + (2 * r + 1)) (sumBform2 i s r l hl)).symm

/-- The `B` short family's gap at a coordinate key. -/
private theorem gapShB (W v : List Nat) (l i r : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + r + 1 = l)
    (hz : ground.getAt 0 W (i + r) = 0) :
    ground.dotNat (sertables.shortFold l i)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)
      = 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i) := by
  rw [gapWeight (sertables.tableB l).lenNums v (sertables.shortFold l i) l
      (lensBLen l) hvl (shortLen l i),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < l then 1 else 0)
        * (ground.getAt 0 (sertables.tableB l).lenNums k
          * ground.getAt 0 v k)) l
      (fun k hk => by rw [shortAt l i k hk]),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableB l).lenNums k
      * ground.getAt 0 v k) l i (r + 1) 0 l
      (by rw [Nat.add_zero]; exact hl) hl,
    winBtop W v l i r hsa hv hl hz,
    arithShB (ground.getAt 0 W i) r]
  have hq : 2 * l - 1 - 2 * i = 2 * r + 1 :=
    sub1b (2 * l) (2 * i) (2 * r + 1) (shBform i r l hl)
  rw [hq]

/-! ## The gap product's regroupings -/

private theorem prodPermB (A B C D E F G H I J : Nat) :
    A * (B * (C * D)) * (E * (F * (G * H))) * (I * J)
      = B * F * I * C * G * (A * D * E * H * J) := by
  have hL : A * (B * (C * D)) * (E * (F * (G * H))) * (I * J)
      = A * (B * (C * (D * (E * (F * (G * (H * (I * J)))))))) := by
    rw [ground.mulAssoc (A * (B * (C * D))) (E * (F * (G * H))) (I * J),
      ground.mulAssoc A (B * (C * D)) ((E * (F * (G * H))) * (I * J)),
      ground.mulAssoc B (C * D) ((E * (F * (G * H))) * (I * J)),
      ground.mulAssoc C D ((E * (F * (G * H))) * (I * J)),
      ground.mulAssoc E (F * (G * H)) (I * J),
      ground.mulAssoc F (G * H) (I * J),
      ground.mulAssoc G H (I * J)]
  have hR : B * F * I * C * G * (A * D * E * H * J)
      = A * (B * (C * (D * (E * (F * (G * (H * (I * J)))))))) := by
    rw [ground.mulAssoc (B * F * I * C) G (A * D * E * H * J),
      ground.mulAssoc (B * F * I) C (G * (A * D * E * H * J)),
      ground.mulAssoc (B * F) I (C * (G * (A * D * E * H * J))),
      ground.mulAssoc B F (I * (C * (G * (A * D * E * H * J)))),
      ground.mulAssoc (A * D * E) H J,
      ground.mulAssoc (A * D) E (H * J),
      ground.mulAssoc A D (E * (H * J)),
      ground.mulLeftComm G A (D * (E * (H * J))),
      ground.mulLeftComm C A (G * (D * (E * (H * J)))),
      ground.mulLeftComm I A (C * (G * (D * (E * (H * J))))),
      ground.mulLeftComm F A (I * (C * (G * (D * (E * (H * J)))))),
      ground.mulLeftComm B A (F * (I * (C * (G * (D * (E * (H * J))))))),
      ground.mulLeftComm I C (G * (D * (E * (H * J)))),
      ground.mulLeftComm F C (I * (G * (D * (E * (H * J))))),
      ground.mulLeftComm G D (E * (H * J)),
      ground.mulLeftComm I D (G * (E * (H * J))),
      ground.mulLeftComm F D (I * (G * (E * (H * J)))),
      ground.mulLeftComm G E (H * J),
      ground.mulLeftComm I E (G * (H * J)),
      ground.mulLeftComm F E (I * (G * (H * J))),
      ground.mulLeftComm I G (H * J),
      ground.mulLeftComm I H J]
  rw [hL, hR]

private theorem prodPermC (A B C D E F G H I : Nat) :
    A * (B * C) * (D * (E * F)) * (G * (H * I))
      = A * D * H * B * E * (C * F * G * I) := by
  have hL : A * (B * C) * (D * (E * F)) * (G * (H * I))
      = A * (B * (C * (D * (E * (F * (G * (H * I))))))) := by
    rw [ground.mulAssoc (A * (B * C)) (D * (E * F)) (G * (H * I)),
      ground.mulAssoc A (B * C) ((D * (E * F)) * (G * (H * I))),
      ground.mulAssoc B C ((D * (E * F)) * (G * (H * I))),
      ground.mulAssoc D (E * F) (G * (H * I)),
      ground.mulAssoc E F (G * (H * I))]
  have hR : A * D * H * B * E * (C * F * G * I)
      = A * (B * (C * (D * (E * (F * (G * (H * I))))))) := by
    rw [ground.mulAssoc (A * D * H * B) E (C * F * G * I),
      ground.mulAssoc (A * D * H) B (E * (C * F * G * I)),
      ground.mulAssoc (A * D) H (B * (E * (C * F * G * I))),
      ground.mulAssoc A D (H * (B * (E * (C * F * G * I)))),
      ground.mulAssoc (C * F) G I, ground.mulAssoc C F (G * I),
      ground.mulLeftComm H B (E * (C * (F * (G * I)))),
      ground.mulLeftComm D B (H * (E * (C * (F * (G * I))))),
      ground.mulLeftComm E C (F * (G * I)),
      ground.mulLeftComm H C (E * (F * (G * I))),
      ground.mulLeftComm D C (H * (E * (F * (G * I)))),
      ground.mulLeftComm H E (F * (G * I)),
      ground.mulLeftComm H F (G * I),
      ground.mulLeftComm H G I]
  rw [hL, hR]

private theorem prodPermD (A B C D E F G H : Nat) :
    A * (B * (C * D)) * (E * (F * (G * H)))
      = B * F * C * G * (A * D * E * H) := by
  have hL : A * (B * (C * D)) * (E * (F * (G * H)))
      = A * (B * (C * (D * (E * (F * (G * H)))))) := by
    rw [ground.mulAssoc A (B * (C * D)) (E * (F * (G * H))),
      ground.mulAssoc B (C * D) (E * (F * (G * H))),
      ground.mulAssoc C D (E * (F * (G * H)))]
  have hR : B * F * C * G * (A * D * E * H)
      = A * (B * (C * (D * (E * (F * (G * H)))))) := by
    rw [ground.mulAssoc (B * F * C) G (A * D * E * H),
      ground.mulAssoc (B * F) C (G * (A * D * E * H)),
      ground.mulAssoc B F (C * (G * (A * D * E * H))),
      ground.mulAssoc (A * D) E H, ground.mulAssoc A D (E * H),
      ground.mulLeftComm G A (D * (E * H)),
      ground.mulLeftComm C A (G * (D * (E * H))),
      ground.mulLeftComm F A (C * (G * (D * (E * H)))),
      ground.mulLeftComm B A (F * (C * (G * (D * (E * H))))),
      ground.mulLeftComm F C (G * (D * (E * H))),
      ground.mulLeftComm G D (E * H),
      ground.mulLeftComm F D (G * (E * H)),
      ground.mulLeftComm G E H,
      ground.mulLeftComm F E (G * H)]
  rw [hL, hR]


/-! ## The positive blocks' products -/

/-- A pair family's block at a constant leading factor. -/
private theorem pairBlock (F : Nat × Nat → Nat) (G : Nat → Nat → Nat)
    (c l : Nat) (h : ∀ j d, j < d → d < l → F (j, d) = c * G j d) :
    ground.famFold Nat.mul 1 F (places.pairsOf l)
      = ground.famFold Nat.mul 1 (fun _ => c) (places.pairsOf l)
        * ground.famFold Nat.mul 1 (fun p => G p.1 p.2)
          (places.pairsOf l) := by
  rw [mulPairsFold F l, mulPairsFold (fun _ => c) l,
    mulPairsFold (fun p => G p.1 p.2) l,
    mulRangeCongr _
      (fun d => ground.famFold Nat.mul 1 (fun j => c * G j d)
        (List.range d)) l
      (fun d hd => mulRangeCongr _ _ d (fun j hj => h j d hj hd)),
    mulRangeCongr
      (fun d => ground.famFold Nat.mul 1 (fun j => c * G j d)
        (List.range d))
      (fun d => ground.famFold Nat.mul 1 (fun _ => c) (List.range d)
        * ground.famFold Nat.mul 1 (fun j => G j d) (List.range d)) l
      (fun d _ => mulPair (fun _ => c) (fun j => G j d) (List.range d)),
    mulPair _ _ (List.range l)]

/-- A pair family's block at a unit leading factor. -/
private theorem pairBlockOne (F : Nat × Nat → Nat) (G : Nat → Nat → Nat)
    (l : Nat) (h : ∀ j d, j < d → d < l → F (j, d) = G j d) :
    ground.famFold Nat.mul 1 F (places.pairsOf l)
      = ground.famFold Nat.mul 1 (fun p => G p.1 p.2)
        (places.pairsOf l) := by
  rw [mulPairsFold F l, mulPairsFold (fun p => G p.1 p.2) l]
  exact mulRangeCongr _ _ l
    (fun d hd => mulRangeCongr _ _ d (fun j hj => h j d hj hd))

/-- A key family's block at a constant leading factor. -/
private theorem rangeBlock (F G : Nat → Nat) (c l : Nat)
    (h : ∀ i, i < l → F i = c * G i) :
    ground.famFold Nat.mul 1 F (List.range l)
      = ground.famFold Nat.mul 1 (fun _ => c) (List.range l)
        * ground.famFold Nat.mul 1 G (List.range l) := by
  rw [mulRangeCongr F (fun i => c * G i) l h,
    mulPair (fun _ => c) G (List.range l)]

private theorem foldlFam2 (g : Nat → Nat → Nat) (a n : Nat) :
    (List.range a).foldl (fun acc i =>
        acc * (List.range n).foldl (fun acc2 k => acc2 * g i k) 1) 1
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (g i) (List.range n))
        (List.range a) := by
  rw [foldlFam (fun i => (List.range n).foldl (fun acc2 k => acc2 * g i k) 1)
    (List.range a)]
  exact mulRangeCongr _ _ a (fun i _ => foldlFam (g i) (List.range n))

/-! ## The `B` gaps at strict coordinate keys -/

private theorem gapDifB' (W v : List Nat) (l i j : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hij : i < j) (hjl : j < l) :
    ground.dotNat (sertables.diffFold l i j)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)
      = 2 * (ground.getAt 0 W i - ground.getAt 0 W j + (j - i)) := by
  match Nat.le.dest (Nat.le_of_lt hij), Nat.le.dest hjl with
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
    have hl : i + s + (t + 1) = l := by
      rw [hs, succAdd j t]
      exact ht
    rw [← hs, gapDifB W v l i s t hsa hv hvl hl, ground.addSubSelfL i s]

private theorem gapSumB' (W v : List Nat) (l i j : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l)
    (hij : i < j) (hjl : j < l) :
    ground.dotNat (sertables.sumFoldB l i j)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)
      = 2 * (ground.getAt 0 W i + ground.getAt 0 W j
          + (2 * l - 1 - i - j)) := by
  match Nat.le.dest (Nat.le_of_lt hij), Nat.le.dest hjl with
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
    have hl : i + s + (t + 1) = l := by
      rw [hs, succAdd j t]
      exact ht
    have hjt1 : j + t + 1 = l := by
      rw [← ht]
      exact succAdd j t
    have hcl2 : W.length + 2 ≤ j + t + 1 := by
      rw [hjt1]
      exact hcl
    have hz : ground.getAt 0 W (i + s + t) = 0 := by
      rw [hs]
      exact ground.getAt_over 0 W (j + t) (Nat.le_of_succ_le
        (Nat.le_of_succ_le_succ hcl2))
    rw [← hs, gapSumB W v l i s t hsa hv hvl hl hz]

private theorem gapShB' (W v : List Nat) (l i : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l) (hil : i < l) :
    ground.dotNat (sertables.shortFold l i)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)
      = 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i) := by
  match Nat.le.dest hil with
  | ⟨t, ht⟩ =>
    have hl : i + t + 1 = l := by
      rw [← ht]
      exact succAdd i t
    have hcl2 : W.length + 2 ≤ i + t + 1 := by
      rw [hl]
      exact hcl
    have hz : ground.getAt 0 W (i + t) = 0 :=
      ground.getAt_over 0 W (i + t) (Nat.le_of_succ_le
        (Nat.le_of_succ_le_succ hcl2))
    exact gapShB W v l i t hsa hv hvl hl hz

/-- The reversed key of a range rejoins its own width. -/
private theorem revIdx (n k : Nat) (hk : k < n) : n - 1 - k + (k + 1) = n := by
  rw [ground.subSub n 1 k, Nat.add_comm 1 k]
  exact ground.subAdd hk

private theorem dimNumB_fam (W : List Nat) (l : Nat) :
    ground.famFold Nat.mul 1
        (fun p => ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))
        (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun p => ground.getAt 0 W p.1 + ground.getAt 0 W p.2
          + (2 * l - 1 - p.1 - p.2)) (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun i => 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))
        (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (W.length - i + k))
          (List.range (l - W.length))) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (l - i + k))
          (List.range (l - W.length))) (List.range W.length)
      = dimNumB W l := by
  rw [← foldlFam (fun p => ground.getAt 0 W p.1 - ground.getAt 0 W p.2
      + (p.2 - p.1)) (places.pairsOf W.length),
    ← foldlFam (fun p => ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - 1 - p.1 - p.2)) (places.pairsOf W.length),
    ← foldlFam (fun i => 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))
      (List.range W.length),
    ← foldlFam2 (fun i k => ground.getAt 0 W i + (W.length - i + k))
      W.length (l - W.length),
    ← foldlFam2 (fun i k => ground.getAt 0 W i + (l - i + k))
      W.length (l - W.length)]
  rfl

/-- The `B` gap product's rank-only factors. -/
private def tailB (l a : Nat) : Nat :=
  ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
    * ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => a + e - (a + j)) (List.range e)) (List.range (l - a))
    * ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
    * ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => 2 * l - 1 - (a + j) - (a + e)) (List.range e))
      (List.range (l - a))
    * ground.famFold Nat.mul 1
      (fun e => 2 * l - 1 - 2 * (a + e)) (List.range (l - a))

private theorem tailB_eq (l a : Nat) : tailB l a
    = ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
      * ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => a + e - (a + j)) (List.range e)) (List.range (l - a))
      * ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
      * ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => 2 * l - 1 - (a + j) - (a + e)) (List.range e))
        (List.range (l - a))
      * ground.famFold Nat.mul 1
        (fun e => 2 * l - 1 - 2 * (a + e)) (List.range (l - a)) := rfl

/-- The `B` member's gap product at the raised coroot list: the
dimension numerator against the rank-only tail. -/
private theorem gapProdB (W v : List Nat) (l : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l) :
    ground.famFold Nat.mul 1 (gapAt (sertables.tableB l) v)
        (List.range (sertables.tableB l).posFolds.length)
      = dimNumB W l * tailB l W.length := by
  have hal : W.length ≤ l :=
    Nat.le_trans (Nat.le_add_right W.length 2) hcl
  match Nat.le.dest hal with
  | ⟨n, hn⟩ =>
  have hna : l - W.length = n := by
    rw [← hn]
    exact ground.addSubSelfL W.length n
  have hzero : ∀ x, ground.getAt 0 W (W.length + x) = 0 :=
    fun x => ground.getAt_over 0 W (W.length + x) (Nat.le_add_right W.length x)
  have hDsp := pairsSplit
    (fun x y => ground.getAt 0 W x - ground.getAt 0 W y + (y - x))
    W.length n
  rw [hn] at hDsp
  have hSsp := pairsSplit
    (fun x y => ground.getAt 0 W x + ground.getAt 0 W y
      + (2 * l - 1 - x - y)) W.length n
  rw [hn] at hSsp
  have hShsp := mulRangeSplit
    (fun i => 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i)) W.length n
  rw [hn] at hShsp
  have hDmix : ground.famFold Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun e => ground.getAt 0 W i - ground.getAt 0 W (W.length + e)
          + (W.length + e - i)) (List.range n)) (List.range W.length)
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (W.length - i + k))
          (List.range n)) (List.range W.length) :=
    mulRangeCongr _ _ W.length (fun i hi =>
      mulRangeCongr _ _ n (fun e _ => by
        rw [hzero e, Nat.sub_zero,
          mixDif W.length i e (Nat.le_of_lt hi)]))
  have hDtail : ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => ground.getAt 0 W (W.length + j)
          - ground.getAt 0 W (W.length + e)
          + (W.length + e - (W.length + j))) (List.range e)) (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => W.length + e - (W.length + j)) (List.range e))
        (List.range n) :=
    mulRangeCongr _ _ n (fun e _ =>
      mulRangeCongr _ _ e (fun j _ => by
        rw [hzero j, hzero e, Nat.zero_sub, Nat.zero_add]))
  have hSmix : ground.famFold Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun e => ground.getAt 0 W i + ground.getAt 0 W (W.length + e)
          + (2 * l - 1 - i - (W.length + e))) (List.range n))
      (List.range W.length)
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (l - i + k)) (List.range n))
        (List.range W.length) :=
    mulRangeCongr _ _ W.length (fun i hi => by
      rw [mulRev (fun e => ground.getAt 0 W i
        + ground.getAt 0 W (W.length + e)
        + (2 * l - 1 - i - (W.length + e))) n]
      exact mulRangeCongr _ _ n (fun k hk => by
        rw [hzero (n - 1 - k), Nat.add_zero,
          sub1c (2 * l) i (W.length + (n - 1 - k)) (l - i + k)
            (mixFormB l W.length i n k (n - 1 - k) hn (revIdx n k hk)
              (Nat.le_trans (Nat.le_of_lt hi) hal))]))
  have hStail : ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => ground.getAt 0 W (W.length + j)
          + ground.getAt 0 W (W.length + e)
          + (2 * l - 1 - (W.length + j) - (W.length + e))) (List.range e))
      (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => 2 * l - 1 - (W.length + j) - (W.length + e))
          (List.range e)) (List.range n) :=
    mulRangeCongr _ _ n (fun e _ =>
      mulRangeCongr _ _ e (fun j _ => by
        rw [hzero j, hzero e, Nat.zero_add]))
  have hShtail : ground.famFold Nat.mul 1
      (fun e => 2 * ground.getAt 0 W (W.length + e)
        + (2 * l - 1 - 2 * (W.length + e))) (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => 2 * l - 1 - 2 * (W.length + e)) (List.range n) :=
    mulRangeCongr _ _ n (fun e _ => by
      rw [hzero e, Nat.mul_zero, Nat.zero_add])
  refine Eq.trans (ground.famFold_getAt Nat.mul 1
    (fun fd => ground.dotNat fd
      (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
    ([] : List Nat) (sertables.tableB l).posFolds
    (sertables.tableB l).posFolds.length rfl) ?_
  rw [show (sertables.tableB l).posFolds
      = ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
          ++ (places.pairsOf l).map (fun p => sertables.sumFoldB l p.1 p.2))
        ++ (List.range l).map (sertables.shortFold l) from rfl,
    ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)) _
      ((List.range l).map (sertables.shortFold l)),
    ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v)) _
      ((places.pairsOf l).map (fun p => sertables.sumFoldB l p.1 p.2)),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
      (fun p => sertables.diffFold l p.1 p.2) (places.pairsOf l),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
      (fun p => sertables.sumFoldB l p.1 p.2) (places.pairsOf l),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
      (sertables.shortFold l) (List.range l),
    pairBlock (fun p => ground.dotNat (sertables.diffFold l p.1 p.2)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
      (fun x y => ground.getAt 0 W x - ground.getAt 0 W y + (y - x))
      2 l (fun j d hj hd => gapDifB' W v l j d hsa hv hvl hj hd),
    pairBlock (fun p => ground.dotNat (sertables.sumFoldB l p.1 p.2)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
      (fun x y => ground.getAt 0 W x + ground.getAt 0 W y
        + (2 * l - 1 - x - y)) 2 l
      (fun j d hj hd => gapSumB' W v l j d hsa hv hvl hcl hj hd),
    mulRangeCongr (fun i => ground.dotNat (sertables.shortFold l i)
        (List.zipWith Nat.mul (sertables.tableB l).lenNums v))
      (fun i => 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i)) l
      (fun i hi => gapShB' W v l i hsa hv hvl hcl hi),
    hDsp, hSsp, hShsp, hDmix, hDtail, hSmix, hStail, hShtail,
    ← dimNumB_fam W l, tailB_eq l W.length, hna]
  exact prodPermB _ _ _ _ _ _ _ _ _ _

private theorem memberRhoLen (W : List Nat) (l : Nat) :
    (memberRho W l).length = l := by
  show ((member W l).map (· + 1)).length = l
  rw [ground.length_map, memberLen]

theorem memberRhoAt (W : List Nat) (l k : Nat) (hk : k < l) :
    ground.getAt 0 (memberRho W l) k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1 := by
  show ground.getAt 0 ((member W l).map (· + 1)) k = _
  rw [ground.getAt_map 0 0 (· + 1) (member W l) k
    (by rw [memberLen]; exact hk), memberEntry W l k hk]

/-- The leading member's shifted key reads one across the run
beyond the word's reach. -/
theorem memberRho_run (W : List Nat) (l i : Nat)
    (hWi : W.length ≤ i) (hi : i < l) :
    ground.getAt 0 (memberRho W l) i = 1 := by
  rw [memberRhoAt W l i hi, ground.getAt_over 0 W i hWi, Nat.zero_sub]

private theorem dimDenB_fam (W : List Nat) (l : Nat) :
    ground.famFold Nat.mul 1 (fun p => p.2 - p.1) (places.pairsOf W.length)
      * ground.famFold Nat.mul 1 (fun p => 2 * l - 1 - p.1 - p.2)
        (places.pairsOf W.length)
      * ground.famFold Nat.mul 1 (fun i => 2 * l - 1 - 2 * i)
        (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun k => W.length - i + k)
          (List.range (l - W.length))) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun k => l - i + k)
          (List.range (l - W.length))) (List.range W.length)
      = dimDenB W l := by
  rw [← foldlFam (fun p => p.2 - p.1) (places.pairsOf W.length),
    ← foldlFam (fun p => 2 * l - 1 - p.1 - p.2) (places.pairsOf W.length),
    ← foldlFam (fun i => 2 * l - 1 - 2 * i) (List.range W.length),
    ← foldlFam2 (fun i k => W.length - i + k) W.length (l - W.length),
    ← foldlFam2 (fun i k => l - i + k) W.length (l - W.length)]
  rfl

/-- The `B` denominator is the numerator's read at the vacant word
of the same length. -/
private theorem dimDenB_eq (W Z : List Nat) (l : Nat)
    (hlen : Z.length = W.length) (hz : ∀ i, ground.getAt 0 Z i = 0) :
    dimNumB Z l = dimDenB W l := by
  rw [← dimNumB_fam Z l, ← dimDenB_fam W l, hlen,
    ground.famFold_congr_all Nat.mul 1
      (fun p => ground.getAt 0 Z p.1 - ground.getAt 0 Z p.2 + (p.2 - p.1))
      (fun p => p.2 - p.1)
      (fun p => by rw [hz p.1, hz p.2, Nat.zero_sub, Nat.zero_add])
      (places.pairsOf W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun p => ground.getAt 0 Z p.1 + ground.getAt 0 Z p.2
        + (2 * l - 1 - p.1 - p.2))
      (fun p => 2 * l - 1 - p.1 - p.2)
      (fun p => by rw [hz p.1, hz p.2, Nat.zero_add])
      (places.pairsOf W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => 2 * ground.getAt 0 Z i + (2 * l - 1 - 2 * i))
      (fun i => 2 * l - 1 - 2 * i)
      (fun i => by rw [hz i, Nat.mul_zero, Nat.zero_add])
      (List.range W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => ground.getAt 0 Z i + (W.length - i + k))
        (List.range (l - W.length)))
      (fun i => ground.famFold Nat.mul 1 (fun k => W.length - i + k)
        (List.range (l - W.length)))
      (fun i => ground.famFold_congr_all Nat.mul 1 _ _
        (fun k => by rw [hz i, Nat.zero_add]) (List.range (l - W.length)))
      (List.range W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => ground.getAt 0 Z i + (l - i + k))
        (List.range (l - W.length)))
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i + k)
        (List.range (l - W.length)))
      (fun i => ground.famFold_congr_all Nat.mul 1 _ _
        (fun k => by rw [hz i, Nat.zero_add]) (List.range (l - W.length)))
      (List.range W.length)]

/-- `lem:serstable`(i)'s dimension clause at the `B` series: the
member's dimension is `cor:weyldim`'s gap product, the
cross-multiplied identity at the displayed numerator and
denominator. -/
theorem dimGap_B : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    dimNumB W l * ground.famFold Nat.mul 1
        (gapAt (sertables.tableB l) (List.replicate l 1))
        (List.range (sertables.tableB l).posFolds.length)
      = dimDenB W l * ground.famFold Nat.mul 1
          (gapAt (sertables.tableB l) (memberRho W l))
          (List.range (sertables.tableB l).posFolds.length) := by
  intro W l hs hcl
  have hsa := ground.sortedAll W hs
  have hm := gapProdB W (memberRho W l) l hsa
    (fun k hk => memberRhoAt W l k hk)
    (memberRhoLen W l) hcl
  have hzl : (List.replicate W.length (0 : Nat)).length = W.length :=
    ground.length_replicate 0 W.length
  have h1 := gapProdB (List.replicate W.length 0) (List.replicate l 1) l
    (fun x => by
      rw [ground.getAt_replicate_zero, ground.getAt_replicate_zero]
      exact Nat.le_refl 0)
    (fun k hk => by
      rw [ground.getAt_replicate 0 1 l k hk,
        ground.getAt_replicate_zero, ground.getAt_replicate_zero])
    (ground.length_replicate 1 l) (by rw [hzl]; exact hcl)
  rw [hzl] at h1
  rw [hm, h1, dimDenB_eq W (List.replicate W.length 0) l hzl
    (fun i => ground.getAt_replicate_zero W.length i)]
  exact ground.mulLeftComm (dimNumB W l) (dimDenB W l) (tailB l W.length)

/-! ## The `C` families' gaps in closed form -/

/-- The `C` window at the long key alone. -/
private theorem winCend (W v : List Nat) (l m : Nat)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hl : m + 1 = l) (hz : ground.getAt 0 W m = 0) :
    ground.famFold Nat.add 0
      (fun e => ground.getAt 0 (sertables.tableC l).lenNums (m + e)
        * ground.getAt 0 v (m + e)) (List.range 1) = 2 := by
  have hml : m < l := by
    rw [← hl]
    exact Nat.lt_succ_self m
  show ground.getAt 0 (sertables.tableC l).lenNums (m + 0)
    * ground.getAt 0 v (m + 0) + 0 = 2
  rw [Nat.add_zero m, Nat.add_zero, lensCEnd l m hml hl, hv m hml, hz,
    Nat.zero_sub, Nat.zero_add, Nat.mul_one]

/-- The `C` difference family's gap at a coordinate pair. -/
private theorem gapDifC (W v : List Nat) (l i s t : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + s + (t + 1) = l) :
    ground.dotNat (sertables.diffFold l i (i + s))
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)
      = ground.getAt 0 W i - ground.getAt 0 W (i + s) + s := by
  rw [gapWeight (sertables.tableC l).lenNums v
      (sertables.diffFold l i (i + s)) l (lensCLen l) hvl
      (diffLen l i (i + s)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + s then 1 else 0)
        * (ground.getAt 0 (sertables.tableC l).lenNums k
          * ground.getAt 0 v k)) l
      (fun k hk => by rw [diffAt l i (i + s) k hk]),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableC l).lenNums k
      * ground.getAt 0 v k) l i s (t + 1) (i + s) hl rfl,
    winC W v l i s t hsa hv hl]

/-- The `C` sum family's gap at a coordinate pair. -/
private theorem gapSumC (W v : List Nat) (l i s r : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + s + (r + 1) = l)
    (hz : ground.getAt 0 W (i + s + r) = 0) :
    ground.dotNat (sertables.sumFoldC l i (i + s))
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)
      = ground.getAt 0 W i + ground.getAt 0 W (i + s)
          + (2 * l - i - (i + s)) := by
  have hl1 : l - 1 = i + s + r := subOf l 1 (i + s + r) hl.symm
  rw [gapWeight (sertables.tableC l).lenNums v
      (sertables.sumFoldC l i (i + s)) l (lensCLen l) hvl
      (sumCLen l i (i + s)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + s then 1 else 0)
          * (ground.getAt 0 (sertables.tableC l).lenNums k
            * ground.getAt 0 v k)
        + (((if i + s ≤ k && k < i + s + r then 1 else 0)
              * (ground.getAt 0 (sertables.tableC l).lenNums k
                * ground.getAt 0 v k)
            + (if i + s ≤ k && k < i + s + r then 1 else 0)
              * (ground.getAt 0 (sertables.tableC l).lenNums k
                * ground.getAt 0 v k))
          + (if i + s + r ≤ k && k < l then 1 else 0)
            * (ground.getAt 0 (sertables.tableC l).lenNums k
              * ground.getAt 0 v k))) l
      (fun k hk => by
        rw [sumCAt l i (i + s) k hk, hl1, ground.mulAddR, ground.mulAddR,
          ground.mulAddR]),
    ground.famFold_add_split _ _ (List.range l),
    ground.famFold_add_split _ _ (List.range l),
    ground.famFold_add_split _ _ (List.range l),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableC l).lenNums k
      * ground.getAt 0 v k) l i s (r + 1) (i + s) hl rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableC l).lenNums k
      * ground.getAt 0 v k) l (i + s) r 1 (i + s + r) hl rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableC l).lenNums k
      * ground.getAt 0 v k) l (i + s + r) 1 0 l
      (by rw [Nat.add_zero]; exact hl) hl,
    winC W v l i s r hsa hv hl,
    winC W v l (i + s) r 0 hsa hv hl,
    winCend W v l (i + s + r) hv hl hz, hz, Nat.sub_zero]
  exact arithSumC (ground.getAt 0 W i - ground.getAt 0 W (i + s))
    (ground.getAt 0 W (i + s)) (ground.getAt 0 W i) s r
    (2 * l - i - (i + s))
    (ground.subAdd (ground.descChain W hsa i s))
    (sub2 (2 * l) i (i + s) (s + (2 * r + 2)) (sumBform2 i s r l hl)).symm

/-- The `C` long family's gap at a coordinate key. -/
private theorem gapLgC (W v : List Nat) (l i r : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + r + 1 = l)
    (hz : ground.getAt 0 W (i + r) = 0) :
    ground.dotNat (sertables.longFold l i)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)
      = 2 * (ground.getAt 0 W i + (l - i)) := by
  have hl1 : l - 1 = i + r := subOf l 1 (i + r) hl.symm
  rw [gapWeight (sertables.tableC l).lenNums v (sertables.longFold l i) l
      (lensCLen l) hvl (longLen l i),
    ground.famFold_congr_range _
      (fun k => ((if i ≤ k && k < i + r then 1 else 0)
            * (ground.getAt 0 (sertables.tableC l).lenNums k
              * ground.getAt 0 v k)
          + (if i ≤ k && k < i + r then 1 else 0)
            * (ground.getAt 0 (sertables.tableC l).lenNums k
              * ground.getAt 0 v k))
        + (if i + r ≤ k && k < l then 1 else 0)
          * (ground.getAt 0 (sertables.tableC l).lenNums k
            * ground.getAt 0 v k)) l
      (fun k hk => by
        rw [longAt l i k hk, hl1, ground.mulAddR, ground.mulAddR]),
    ground.famFold_add_split _ _ (List.range l),
    ground.famFold_add_split _ _ (List.range l),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableC l).lenNums k
      * ground.getAt 0 v k) l i r 1 (i + r) hl rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableC l).lenNums k
      * ground.getAt 0 v k) l (i + r) 1 0 l
      (by rw [Nat.add_zero]; exact hl) hl,
    winC W v l i r 0 hsa hv hl,
    winCend W v l (i + r) hv hl hz, hz, Nat.sub_zero,
    lgCform i r l hl]
  exact arithLgC (ground.getAt 0 W i) r

/-! ## The `C` gaps at strict coordinate keys -/

private theorem gapDifC' (W v : List Nat) (l i j : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hij : i < j) (hjl : j < l) :
    ground.dotNat (sertables.diffFold l i j)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)
      = ground.getAt 0 W i - ground.getAt 0 W j + (j - i) := by
  match Nat.le.dest (Nat.le_of_lt hij), Nat.le.dest hjl with
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
    have hl : i + s + (t + 1) = l := by
      rw [hs, succAdd j t]
      exact ht
    rw [← hs, gapDifC W v l i s t hsa hv hvl hl, ground.addSubSelfL i s]

private theorem gapSumC' (W v : List Nat) (l i j : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l)
    (hij : i < j) (hjl : j < l) :
    ground.dotNat (sertables.sumFoldC l i j)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)
      = ground.getAt 0 W i + ground.getAt 0 W j + (2 * l - i - j) := by
  match Nat.le.dest (Nat.le_of_lt hij), Nat.le.dest hjl with
  | ⟨s, hs⟩, ⟨t, ht⟩ =>
    have hl : i + s + (t + 1) = l := by
      rw [hs, succAdd j t]
      exact ht
    have hjt1 : j + t + 1 = l := by
      rw [← ht]
      exact succAdd j t
    have hcl2 : W.length + 2 ≤ j + t + 1 := by
      rw [hjt1]
      exact hcl
    have hz : ground.getAt 0 W (i + s + t) = 0 := by
      rw [hs]
      exact ground.getAt_over 0 W (j + t) (Nat.le_of_succ_le
        (Nat.le_of_succ_le_succ hcl2))
    rw [← hs, gapSumC W v l i s t hsa hv hvl hl hz]

private theorem gapLgC' (W v : List Nat) (l i : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l) (hil : i < l) :
    ground.dotNat (sertables.longFold l i)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)
      = 2 * (ground.getAt 0 W i + (l - i)) := by
  match Nat.le.dest hil with
  | ⟨t, ht⟩ =>
    have hl : i + t + 1 = l := by
      rw [← ht]
      exact succAdd i t
    have hcl2 : W.length + 2 ≤ i + t + 1 := by
      rw [hl]
      exact hcl
    have hz : ground.getAt 0 W (i + t) = 0 :=
      ground.getAt_over 0 W (i + t) (Nat.le_of_succ_le
        (Nat.le_of_succ_le_succ hcl2))
    exact gapLgC W v l i t hsa hv hvl hl hz

private theorem dimNumC_fam (W : List Nat) (l : Nat) :
    ground.famFold Nat.mul 1
        (fun p => ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))
        (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun p => ground.getAt 0 W p.1 + ground.getAt 0 W p.2
          + (2 * l - p.1 - p.2)) (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.getAt 0 W i + (l - i)) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (W.length - i + k))
          (List.range (l - W.length))) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (l - i + 1 + k))
          (List.range (l - W.length))) (List.range W.length)
      = dimNumC W l := by
  rw [← foldlFam (fun p => ground.getAt 0 W p.1 - ground.getAt 0 W p.2
      + (p.2 - p.1)) (places.pairsOf W.length),
    ← foldlFam (fun p => ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - p.1 - p.2)) (places.pairsOf W.length),
    ← foldlFam (fun i => ground.getAt 0 W i + (l - i)) (List.range W.length),
    ← foldlFam2 (fun i k => ground.getAt 0 W i + (W.length - i + k))
      W.length (l - W.length),
    ← foldlFam2 (fun i k => ground.getAt 0 W i + (l - i + 1 + k))
      W.length (l - W.length)]
  rfl

private theorem dimDenC_fam (W : List Nat) (l : Nat) :
    ground.famFold Nat.mul 1 (fun p => p.2 - p.1) (places.pairsOf W.length)
      * ground.famFold Nat.mul 1 (fun p => 2 * l - p.1 - p.2)
        (places.pairsOf W.length)
      * ground.famFold Nat.mul 1 (fun i => l - i) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun k => W.length - i + k)
          (List.range (l - W.length))) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun k => l - i + 1 + k)
          (List.range (l - W.length))) (List.range W.length)
      = dimDenC W l := by
  rw [← foldlFam (fun p => p.2 - p.1) (places.pairsOf W.length),
    ← foldlFam (fun p => 2 * l - p.1 - p.2) (places.pairsOf W.length),
    ← foldlFam (fun i => l - i) (List.range W.length),
    ← foldlFam2 (fun i k => W.length - i + k) W.length (l - W.length),
    ← foldlFam2 (fun i k => l - i + 1 + k) W.length (l - W.length)]
  rfl

/-- The `C` gap product's rank-only factors. -/
private def tailC (l a : Nat) : Nat :=
  ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => a + e - (a + j)) (List.range e)) (List.range (l - a))
    * ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => 2 * l - (a + j) - (a + e)) (List.range e))
      (List.range (l - a))
    * ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (List.range l)
    * ground.famFold Nat.mul 1 (fun e => l - (a + e)) (List.range (l - a))

private theorem tailC_eq (l a : Nat) : tailC l a
    = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => a + e - (a + j)) (List.range e)) (List.range (l - a))
      * ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => 2 * l - (a + j) - (a + e)) (List.range e))
        (List.range (l - a))
      * ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (List.range l)
      * ground.famFold Nat.mul 1 (fun e => l - (a + e))
        (List.range (l - a)) := rfl

private theorem gapProdC (W v : List Nat) (l : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l) :
    ground.famFold Nat.mul 1 (gapAt (sertables.tableC l) v)
        (List.range (sertables.tableC l).posFolds.length)
      = dimNumC W l * tailC l W.length := by
  have hal : W.length ≤ l :=
    Nat.le_trans (Nat.le_add_right W.length 2) hcl
  match Nat.le.dest hal with
  | ⟨n, hn⟩ =>
  have hna : l - W.length = n := by
    rw [← hn]
    exact ground.addSubSelfL W.length n
  have hzero : ∀ x, ground.getAt 0 W (W.length + x) = 0 :=
    fun x => ground.getAt_over 0 W (W.length + x) (Nat.le_add_right W.length x)
  have hDsp := pairsSplit
    (fun x y => ground.getAt 0 W x - ground.getAt 0 W y + (y - x))
    W.length n
  rw [hn] at hDsp
  have hSsp := pairsSplit
    (fun x y => ground.getAt 0 W x + ground.getAt 0 W y
      + (2 * l - x - y)) W.length n
  rw [hn] at hSsp
  have hLsp := mulRangeSplit
    (fun i => ground.getAt 0 W i + (l - i)) W.length n
  rw [hn] at hLsp
  have hDmix : ground.famFold Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun e => ground.getAt 0 W i - ground.getAt 0 W (W.length + e)
          + (W.length + e - i)) (List.range n)) (List.range W.length)
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (W.length - i + k))
          (List.range n)) (List.range W.length) :=
    mulRangeCongr _ _ W.length (fun i hi =>
      mulRangeCongr _ _ n (fun e _ => by
        rw [hzero e, Nat.sub_zero,
          mixDif W.length i e (Nat.le_of_lt hi)]))
  have hDtail : ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => ground.getAt 0 W (W.length + j)
          - ground.getAt 0 W (W.length + e)
          + (W.length + e - (W.length + j))) (List.range e)) (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => W.length + e - (W.length + j)) (List.range e))
        (List.range n) :=
    mulRangeCongr _ _ n (fun e _ =>
      mulRangeCongr _ _ e (fun j _ => by
        rw [hzero j, hzero e, Nat.zero_sub, Nat.zero_add]))
  have hSmix : ground.famFold Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun e => ground.getAt 0 W i + ground.getAt 0 W (W.length + e)
          + (2 * l - i - (W.length + e))) (List.range n))
      (List.range W.length)
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (l - i + 1 + k)) (List.range n))
        (List.range W.length) :=
    mulRangeCongr _ _ W.length (fun i hi => by
      rw [mulRev (fun e => ground.getAt 0 W i
        + ground.getAt 0 W (W.length + e)
        + (2 * l - i - (W.length + e))) n]
      exact mulRangeCongr _ _ n (fun k hk => by
        rw [hzero (n - 1 - k), Nat.add_zero,
          sub2 (2 * l) i (W.length + (n - 1 - k)) (l - i + 1 + k)
            (mixFormC l W.length i n k (n - 1 - k) hn (revIdx n k hk)
              (Nat.le_trans (Nat.le_of_lt hi) hal))]))
  have hStail : ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => ground.getAt 0 W (W.length + j)
          + ground.getAt 0 W (W.length + e)
          + (2 * l - (W.length + j) - (W.length + e))) (List.range e))
      (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => 2 * l - (W.length + j) - (W.length + e))
          (List.range e)) (List.range n) :=
    mulRangeCongr _ _ n (fun e _ =>
      mulRangeCongr _ _ e (fun j _ => by
        rw [hzero j, hzero e, Nat.zero_add]))
  have hLtail : ground.famFold Nat.mul 1
      (fun e => ground.getAt 0 W (W.length + e) + (l - (W.length + e)))
      (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => l - (W.length + e)) (List.range n) :=
    mulRangeCongr _ _ n (fun e _ => by
      rw [hzero e, Nat.zero_add])
  refine Eq.trans (ground.famFold_getAt Nat.mul 1
    (fun fd => ground.dotNat fd
      (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
    ([] : List Nat) (sertables.tableC l).posFolds
    (sertables.tableC l).posFolds.length rfl) ?_
  rw [show (sertables.tableC l).posFolds
      = ((places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
          ++ (places.pairsOf l).map (fun p => sertables.sumFoldC l p.1 p.2))
        ++ (List.range l).map (sertables.longFold l) from rfl,
    ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)) _
      ((List.range l).map (sertables.longFold l)),
    ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v)) _
      ((places.pairsOf l).map (fun p => sertables.sumFoldC l p.1 p.2)),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
      (fun p => sertables.diffFold l p.1 p.2) (places.pairsOf l),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
      (fun p => sertables.sumFoldC l p.1 p.2) (places.pairsOf l),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
      (sertables.longFold l) (List.range l),
    pairBlockOne (fun p => ground.dotNat (sertables.diffFold l p.1 p.2)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
      (fun x y => ground.getAt 0 W x - ground.getAt 0 W y + (y - x))
      l (fun j d hj hd => gapDifC' W v l j d hsa hv hvl hj hd),
    pairBlockOne (fun p => ground.dotNat (sertables.sumFoldC l p.1 p.2)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
      (fun x y => ground.getAt 0 W x + ground.getAt 0 W y
        + (2 * l - x - y))
      l (fun j d hj hd => gapSumC' W v l j d hsa hv hvl hcl hj hd),
    rangeBlock (fun i => ground.dotNat (sertables.longFold l i)
        (List.zipWith Nat.mul (sertables.tableC l).lenNums v))
      (fun i => ground.getAt 0 W i + (l - i)) 2 l
      (fun i hi => gapLgC' W v l i hsa hv hvl hcl hi),
    hDsp, hSsp, hLsp, hDmix, hDtail, hSmix, hStail, hLtail,
    ← dimNumC_fam W l, tailC_eq l W.length, hna]
  exact prodPermC _ _ _ _ _ _ _ _ _

private theorem dimDenC_eq (W Z : List Nat) (l : Nat)
    (hlen : Z.length = W.length) (hz : ∀ i, ground.getAt 0 Z i = 0) :
    dimNumC Z l = dimDenC W l := by
  rw [← dimNumC_fam Z l, ← dimDenC_fam W l, hlen,
    ground.famFold_congr_all Nat.mul 1
      (fun p => ground.getAt 0 Z p.1 - ground.getAt 0 Z p.2 + (p.2 - p.1))
      (fun p => p.2 - p.1)
      (fun p => by rw [hz p.1, hz p.2, Nat.zero_sub, Nat.zero_add])
      (places.pairsOf W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun p => ground.getAt 0 Z p.1 + ground.getAt 0 Z p.2
        + (2 * l - p.1 - p.2))
      (fun p => 2 * l - p.1 - p.2)
      (fun p => by rw [hz p.1, hz p.2, Nat.zero_add])
      (places.pairsOf W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.getAt 0 Z i + (l - i)) (fun i => l - i)
      (fun i => by rw [hz i, Nat.zero_add]) (List.range W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => ground.getAt 0 Z i + (W.length - i + k))
        (List.range (l - W.length)))
      (fun i => ground.famFold Nat.mul 1 (fun k => W.length - i + k)
        (List.range (l - W.length)))
      (fun i => ground.famFold_congr_all Nat.mul 1 _ _
        (fun k => by rw [hz i, Nat.zero_add]) (List.range (l - W.length)))
      (List.range W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => ground.getAt 0 Z i + (l - i + 1 + k))
        (List.range (l - W.length)))
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i + 1 + k)
        (List.range (l - W.length)))
      (fun i => ground.famFold_congr_all Nat.mul 1 _ _
        (fun k => by rw [hz i, Nat.zero_add]) (List.range (l - W.length)))
      (List.range W.length)]

/-- `lem:serstable`(i)'s dimension clause at the `C` series. -/
theorem dimGap_C : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    dimNumC W l * ground.famFold Nat.mul 1
        (gapAt (sertables.tableC l) (List.replicate l 1))
        (List.range (sertables.tableC l).posFolds.length)
      = dimDenC W l * ground.famFold Nat.mul 1
          (gapAt (sertables.tableC l) (memberRho W l))
          (List.range (sertables.tableC l).posFolds.length) := by
  intro W l hs hcl
  have hsa := ground.sortedAll W hs
  have hm := gapProdC W (memberRho W l) l hsa
    (fun k hk => memberRhoAt W l k hk) (memberRhoLen W l) hcl
  have hzl : (List.replicate W.length (0 : Nat)).length = W.length :=
    ground.length_replicate 0 W.length
  have h1 := gapProdC (List.replicate W.length 0) (List.replicate l 1) l
    (fun x => by
      rw [ground.getAt_replicate_zero, ground.getAt_replicate_zero]
      exact Nat.le_refl 0)
    (fun k hk => by
      rw [ground.getAt_replicate 0 1 l k hk,
        ground.getAt_replicate_zero, ground.getAt_replicate_zero])
    (ground.length_replicate 1 l) (by rw [hzl]; exact hcl)
  rw [hzl] at h1
  rw [hm, h1, dimDenC_eq W (List.replicate W.length 0) l hzl
    (fun i => ground.getAt_replicate_zero W.length i)]
  exact ground.mulLeftComm (dimNumC W l) (dimDenC W l) (tailC l W.length)

/-! ## The `D` families' gaps in closed form -/

/-- The `D` difference family's gap at a coordinate pair. -/
private theorem gapDifD (W v : List Nat) (l i s t : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + s + t = l) :
    ground.dotNat (sertables.diffFold l i (i + s))
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v)
      = 2 * (ground.getAt 0 W i - ground.getAt 0 W (i + s) + s) := by
  have hle : i + s ≤ l := by
    rw [← hl]
    exact Nat.le_add_right (i + s) t
  rw [gapWeight (sertables.tableD l).lenNums v
      (sertables.diffFold l i (i + s)) l (lensDLen l) hvl
      (diffLen l i (i + s)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + s then 1 else 0)
        * (ground.getAt 0 (sertables.tableD l).lenNums k
          * ground.getAt 0 v k)) l
      (fun k hk => by rw [diffAt l i (i + s) k hk]),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableD l).lenNums k
      * ground.getAt 0 v k) l i s t (i + s) hl rfl,
    winD W v l i s hsa hv hle]

/-- The `D` sum family's gap at a generic coordinate pair. -/
private theorem gapSumDg (W v : List Nat) (l i s r : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + s + (r + 2) = l)
    (hz : ground.getAt 0 W (i + s + r) = 0)
    (hne : ¬ i + s + 1 = l) :
    ground.dotNat (sertables.sumFoldD l i (i + s))
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v)
      = 2 * (ground.getAt 0 W i + ground.getAt 0 W (i + s)
          + (2 * l - 2 - i - (i + s))) := by
  have hl2 : l - 2 = i + s + r := subOf l 2 (i + s + r) hl.symm
  have hle1 : i + s ≤ l := by
    rw [← hl]
    exact Nat.le_add_right (i + s) (r + 2)
  have heq : i + s + r + 2 = l := by
    rw [← hl]
    exact Nat.add_assoc (i + s) r 2
  have hle2 : i + s + r ≤ l := by
    rw [← heq]
    exact Nat.le_add_right (i + s + r) 2
  have hle3 : i + s + r + 2 ≤ l := Nat.le_of_eq heq
  rw [gapWeight (sertables.tableD l).lenNums v
      (sertables.sumFoldD l i (i + s)) l (lensDLen l) hvl
      (sumDLen l i (i + s)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + s then 1 else 0)
          * (ground.getAt 0 (sertables.tableD l).lenNums k
            * ground.getAt 0 v k)
        + (((if i + s ≤ k && k < i + s + r then 1 else 0)
              * (ground.getAt 0 (sertables.tableD l).lenNums k
                * ground.getAt 0 v k)
            + (if i + s ≤ k && k < i + s + r then 1 else 0)
              * (ground.getAt 0 (sertables.tableD l).lenNums k
                * ground.getAt 0 v k))
          + (if i + s + r ≤ k && k < l then 1 else 0)
            * (ground.getAt 0 (sertables.tableD l).lenNums k
              * ground.getAt 0 v k))) l
      (fun k hk => by
        rw [sumDAtGen l i (i + s) k hk hne, hl2, ground.mulAddR,
          ground.mulAddR, ground.mulAddR]),
    ground.famFold_add_split _ _ (List.range l),
    ground.famFold_add_split _ _ (List.range l),
    ground.famFold_add_split _ _ (List.range l),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableD l).lenNums k
      * ground.getAt 0 v k) l i s (r + 2) (i + s) hl rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableD l).lenNums k
      * ground.getAt 0 v k) l (i + s) r 2 (i + s + r)
      (by rw [Nat.add_assoc (i + s) r 2]; exact hl) rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableD l).lenNums k
      * ground.getAt 0 v k) l (i + s + r) 2 0 l
      (by rw [Nat.add_zero]; exact heq) heq,
    winD W v l i s hsa hv hle1,
    winD W v l (i + s) r hsa hv hle2,
    winD W v l (i + s + r) 2 hsa hv hle3,
    hz, Nat.sub_zero, Nat.zero_sub, Nat.zero_add]
  exact arithSumDg (ground.getAt 0 W i - ground.getAt 0 W (i + s))
    (ground.getAt 0 W (i + s)) (ground.getAt 0 W i) s r
    (2 * l - 2 - i - (i + s))
    (ground.subAdd (ground.descChain W hsa i s))
    (sub2c (2 * l) i (i + s) (s + (2 * r + 2))
      (sumDform2 i s r l hl)).symm

/-- The `D` sum family's gap at the last coordinate. -/
private theorem gapSumDt (W v : List Nat) (l i q : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hl : i + (q + 2) = l)
    (hz : ground.getAt 0 W (i + q) = 0)
    (hz1 : ground.getAt 0 W (i + q + 1) = 0) :
    ground.dotNat (sertables.sumFoldD l i (i + q + 1))
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v)
      = 2 * (ground.getAt 0 W i + ground.getAt 0 W (i + q + 1)
          + (2 * l - 2 - i - (i + q + 1))) := by
  have hb : i + q + 1 + 1 = l := hl
  have hl2 : l - 2 = i + q := subOf l 2 (i + q) hl.symm
  have hl1 : l - 1 = i + q + 1 := subOf l 1 (i + q + 1) hb.symm
  have heqt : i + q + 2 = l := by
    rw [← hl]
    exact Nat.add_assoc i q 2
  have hle1 : i + q ≤ l := by
    rw [← heqt]
    exact Nat.le_add_right (i + q) 2
  have hle2 : i + q + 1 + 1 ≤ l := Nat.le_of_eq hb
  rw [gapWeight (sertables.tableD l).lenNums v
      (sertables.sumFoldD l i (i + q + 1)) l (lensDLen l) hvl
      (sumDLen l i (i + q + 1)),
    ground.famFold_congr_range _
      (fun k => (if i ≤ k && k < i + q then 1 else 0)
          * (ground.getAt 0 (sertables.tableD l).lenNums k
            * ground.getAt 0 v k)
        + (if i + q + 1 ≤ k && k < l then 1 else 0)
          * (ground.getAt 0 (sertables.tableD l).lenNums k
            * ground.getAt 0 v k)) l
      (fun k hk => by
        rw [sumDAtTop l i (i + q + 1) k hk hb, hl2, hl1, ground.mulAddR]),
    ground.famFold_add_split _ _ (List.range l),
    indWindowAt (fun k => ground.getAt 0 (sertables.tableD l).lenNums k
      * ground.getAt 0 v k) l i q 2 (i + q) heqt rfl,
    indWindowAt (fun k => ground.getAt 0 (sertables.tableD l).lenNums k
      * ground.getAt 0 v k) l (i + q + 1) 1 0 l
      (by rw [Nat.add_zero]; exact hb) hb,
    winD W v l i q hsa hv hle1,
    winD W v l (i + q + 1) 1 hsa hv hle2,
    hz, Nat.sub_zero, hz1, Nat.zero_sub, Nat.zero_add,
    sub2c (2 * l) i (i + q + 1) (q + 1)
      (sumDtform i q (i + q + 1) l hl hb)]
  exact arithSumDt (ground.getAt 0 W i) q

/-! ## The `D` gaps at strict coordinate keys -/

private theorem gapDifD' (W v : List Nat) (l i j : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hij : i < j) (hjl : j < l) :
    ground.dotNat (sertables.diffFold l i j)
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v)
      = 2 * (ground.getAt 0 W i - ground.getAt 0 W j + (j - i)) := by
  match Nat.le.dest hij, Nat.le.dest hjl with
  | ⟨q, hq⟩, ⟨t, ht⟩ =>
    have hjq : i + (q + 1) = j := (succAdd i q).trans hq
    have hl : i + (q + 1) + (t + 1) = l := by
      rw [hjq, succAdd j t]
      exact ht
    rw [← hjq, gapDifD W v l i (q + 1) (t + 1) hsa hv hvl hl,
      ground.addSubSelfL i (q + 1)]

private theorem gapSumD' (W v : List Nat) (l i j : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l)
    (hij : i < j) (hjl : j < l) :
    ground.dotNat (sertables.sumFoldD l i j)
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v)
      = 2 * (ground.getAt 0 W i + ground.getAt 0 W j
          + (2 * l - 2 - i - j)) := by
  match Nat.le.dest hij with
  | ⟨q, hq⟩ =>
    have hjq : i + (q + 1) = j := (succAdd i q).trans hq
    have hjq' : i + q + 1 = j := hjq
    by_cases hb : j + 1 = l
    · have hl : i + (q + 2) = l := by
        rw [← hb, ← hjq']
        rfl
      have heqt : i + q + 2 = l := by
        rw [← hl]
        exact Nat.add_assoc i q 2
      have hcl2 : W.length + 2 ≤ i + q + 2 := by
        rw [heqt]
        exact hcl
      have haq : W.length ≤ i + q :=
        Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hcl2)
      rw [← hjq', gapSumDt W v l i q hsa hv hvl hl
        (ground.getAt_over 0 W (i + q) haq)
        (ground.getAt_over 0 W (i + q + 1) (Nat.le_succ_of_le haq))]
    · have hlt : j + 1 < l := Nat.lt_of_le_of_ne hjl hb
      match Nat.le.dest hlt with
      | ⟨r, hr⟩ =>
        have hl : i + (q + 1) + (r + 2) = l := by
          rw [hjq, Nat.add_comm r 2, ← Nat.add_assoc j 2 r]
          exact hr
        have hjr2 : j + r + 2 = l := by
          rw [Nat.add_assoc j r 2, Nat.add_comm r 2,
            ← Nat.add_assoc j 2 r]
          exact hr
        have hcl2 : W.length + 2 ≤ j + r + 2 := by
          rw [hjr2]
          exact hcl
        have hz : ground.getAt 0 W (i + (q + 1) + r) = 0 := by
          rw [hjq]
          exact ground.getAt_over 0 W (j + r)
            (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hcl2))
        have hne : ¬ i + (q + 1) + 1 = l := by
          rw [hjq]
          exact hb
        rw [← hjq, gapSumDg W v l i (q + 1) r hsa hv hvl hl hz hne]

private theorem dimNumD_fam (W : List Nat) (l : Nat) :
    ground.famFold Nat.mul 1
        (fun p => ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))
        (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun p => ground.getAt 0 W p.1 + ground.getAt 0 W p.2
          + (2 * l - 2 - p.1 - p.2)) (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (W.length - i + k))
          (List.range (l - W.length))) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (l - i - 1 + k))
          (List.range (l - W.length))) (List.range W.length)
      = dimNumD W l := by
  rw [← foldlFam (fun p => ground.getAt 0 W p.1 - ground.getAt 0 W p.2
      + (p.2 - p.1)) (places.pairsOf W.length),
    ← foldlFam (fun p => ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - 2 - p.1 - p.2)) (places.pairsOf W.length),
    ← foldlFam2 (fun i k => ground.getAt 0 W i + (W.length - i + k))
      W.length (l - W.length),
    ← foldlFam2 (fun i k => ground.getAt 0 W i + (l - i - 1 + k))
      W.length (l - W.length)]
  rfl

private theorem dimDenD_fam (W : List Nat) (l : Nat) :
    ground.famFold Nat.mul 1 (fun p => p.2 - p.1) (places.pairsOf W.length)
      * ground.famFold Nat.mul 1 (fun p => 2 * l - 2 - p.1 - p.2)
        (places.pairsOf W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun k => W.length - i + k)
          (List.range (l - W.length))) (List.range W.length)
      * ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1 (fun k => l - i - 1 + k)
          (List.range (l - W.length))) (List.range W.length)
      = dimDenD W l := by
  rw [← foldlFam (fun p => p.2 - p.1) (places.pairsOf W.length),
    ← foldlFam (fun p => 2 * l - 2 - p.1 - p.2) (places.pairsOf W.length),
    ← foldlFam2 (fun i k => W.length - i + k) W.length (l - W.length),
    ← foldlFam2 (fun i k => l - i - 1 + k) W.length (l - W.length)]
  rfl

/-- The `D` gap product's rank-only factors. -/
private def tailD (l a : Nat) : Nat :=
  ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
    * ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => a + e - (a + j)) (List.range e)) (List.range (l - a))
    * ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
    * ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => 2 * l - 2 - (a + j) - (a + e)) (List.range e))
      (List.range (l - a))

private theorem tailD_eq (l a : Nat) : tailD l a
    = ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
      * ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => a + e - (a + j)) (List.range e)) (List.range (l - a))
      * ground.famFold Nat.mul 1 (fun _ => (2 : Nat)) (places.pairsOf l)
      * ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => 2 * l - 2 - (a + j) - (a + e)) (List.range e))
        (List.range (l - a)) := rfl

private theorem gapProdD (W v : List Nat) (l : Nat)
    (hsa : ∀ x, ground.getAt 0 W (x + 1) ≤ ground.getAt 0 W x)
    (hv : ∀ k, k < l → ground.getAt 0 v k
      = ground.getAt 0 W k - ground.getAt 0 W (k + 1) + 1)
    (hvl : v.length = l) (hcl : W.length + 2 ≤ l) :
    ground.famFold Nat.mul 1 (gapAt (sertables.tableD l) v)
        (List.range (sertables.tableD l).posFolds.length)
      = dimNumD W l * tailD l W.length := by
  have hal : W.length ≤ l :=
    Nat.le_trans (Nat.le_add_right W.length 2) hcl
  match Nat.le.dest hal with
  | ⟨n, hn⟩ =>
  have hna : l - W.length = n := by
    rw [← hn]
    exact ground.addSubSelfL W.length n
  have hzero : ∀ x, ground.getAt 0 W (W.length + x) = 0 :=
    fun x => ground.getAt_over 0 W (W.length + x) (Nat.le_add_right W.length x)
  have hDsp := pairsSplit
    (fun x y => ground.getAt 0 W x - ground.getAt 0 W y + (y - x))
    W.length n
  rw [hn] at hDsp
  have hSsp := pairsSplit
    (fun x y => ground.getAt 0 W x + ground.getAt 0 W y
      + (2 * l - 2 - x - y)) W.length n
  rw [hn] at hSsp
  have hDmix : ground.famFold Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun e => ground.getAt 0 W i - ground.getAt 0 W (W.length + e)
          + (W.length + e - i)) (List.range n)) (List.range W.length)
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (W.length - i + k))
          (List.range n)) (List.range W.length) :=
    mulRangeCongr _ _ W.length (fun i hi =>
      mulRangeCongr _ _ n (fun e _ => by
        rw [hzero e, Nat.sub_zero,
          mixDif W.length i e (Nat.le_of_lt hi)]))
  have hDtail : ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => ground.getAt 0 W (W.length + j)
          - ground.getAt 0 W (W.length + e)
          + (W.length + e - (W.length + j))) (List.range e)) (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => W.length + e - (W.length + j)) (List.range e))
        (List.range n) :=
    mulRangeCongr _ _ n (fun e _ =>
      mulRangeCongr _ _ e (fun j _ => by
        rw [hzero j, hzero e, Nat.zero_sub, Nat.zero_add]))
  have hSmix : ground.famFold Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun e => ground.getAt 0 W i + ground.getAt 0 W (W.length + e)
          + (2 * l - 2 - i - (W.length + e))) (List.range n))
      (List.range W.length)
      = ground.famFold Nat.mul 1
        (fun i => ground.famFold Nat.mul 1
          (fun k => ground.getAt 0 W i + (l - i - 1 + k)) (List.range n))
        (List.range W.length) :=
    mulRangeCongr _ _ W.length (fun i hi => by
      rw [mulRev (fun e => ground.getAt 0 W i
        + ground.getAt 0 W (W.length + e)
        + (2 * l - 2 - i - (W.length + e))) n]
      exact mulRangeCongr _ _ n (fun k hk => by
        rw [hzero (n - 1 - k), Nat.add_zero,
          sub2c (2 * l) i (W.length + (n - 1 - k)) (l - i - 1 + k)
            (mixFormD l W.length i n k (n - 1 - k) hn (revIdx n k hk)
              (Nat.le_trans hi hal))]))
  have hStail : ground.famFold Nat.mul 1
      (fun e => ground.famFold Nat.mul 1
        (fun j => ground.getAt 0 W (W.length + j)
          + ground.getAt 0 W (W.length + e)
          + (2 * l - 2 - (W.length + j) - (W.length + e))) (List.range e))
      (List.range n)
      = ground.famFold Nat.mul 1
        (fun e => ground.famFold Nat.mul 1
          (fun j => 2 * l - 2 - (W.length + j) - (W.length + e))
          (List.range e)) (List.range n) :=
    mulRangeCongr _ _ n (fun e _ =>
      mulRangeCongr _ _ e (fun j _ => by
        rw [hzero j, hzero e, Nat.zero_add]))
  refine Eq.trans (ground.famFold_getAt Nat.mul 1
    (fun fd => ground.dotNat fd
      (List.zipWith Nat.mul (sertables.tableD l).lenNums v))
    ([] : List Nat) (sertables.tableD l).posFolds
    (sertables.tableD l).posFolds.length rfl) ?_
  rw [show (sertables.tableD l).posFolds
      = (places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2)
        ++ (places.pairsOf l).map (fun p => sertables.sumFoldD l p.1 p.2)
      from rfl,
    ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v)) _
      ((places.pairsOf l).map (fun p => sertables.sumFoldD l p.1 p.2)),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v))
      (fun p => sertables.diffFold l p.1 p.2) (places.pairsOf l),
    ground.famFold_map Nat.mul 1
      (fun fd => ground.dotNat fd
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v))
      (fun p => sertables.sumFoldD l p.1 p.2) (places.pairsOf l),
    pairBlock (fun p => ground.dotNat (sertables.diffFold l p.1 p.2)
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v))
      (fun x y => ground.getAt 0 W x - ground.getAt 0 W y + (y - x))
      2 l (fun j d hj hd => gapDifD' W v l j d hsa hv hvl hj hd),
    pairBlock (fun p => ground.dotNat (sertables.sumFoldD l p.1 p.2)
        (List.zipWith Nat.mul (sertables.tableD l).lenNums v))
      (fun x y => ground.getAt 0 W x + ground.getAt 0 W y
        + (2 * l - 2 - x - y)) 2 l
      (fun j d hj hd => gapSumD' W v l j d hsa hv hvl hcl hj hd),
    hDsp, hSsp, hDmix, hDtail, hSmix, hStail,
    ← dimNumD_fam W l, tailD_eq l W.length, hna]
  exact prodPermD _ _ _ _ _ _ _ _

private theorem dimDenD_eq (W Z : List Nat) (l : Nat)
    (hlen : Z.length = W.length) (hz : ∀ i, ground.getAt 0 Z i = 0) :
    dimNumD Z l = dimDenD W l := by
  rw [← dimNumD_fam Z l, ← dimDenD_fam W l, hlen,
    ground.famFold_congr_all Nat.mul 1
      (fun p => ground.getAt 0 Z p.1 - ground.getAt 0 Z p.2 + (p.2 - p.1))
      (fun p => p.2 - p.1)
      (fun p => by rw [hz p.1, hz p.2, Nat.zero_sub, Nat.zero_add])
      (places.pairsOf W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun p => ground.getAt 0 Z p.1 + ground.getAt 0 Z p.2
        + (2 * l - 2 - p.1 - p.2))
      (fun p => 2 * l - 2 - p.1 - p.2)
      (fun p => by rw [hz p.1, hz p.2, Nat.zero_add])
      (places.pairsOf W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => ground.getAt 0 Z i + (W.length - i + k))
        (List.range (l - W.length)))
      (fun i => ground.famFold Nat.mul 1 (fun k => W.length - i + k)
        (List.range (l - W.length)))
      (fun i => ground.famFold_congr_all Nat.mul 1 _ _
        (fun k => by rw [hz i, Nat.zero_add]) (List.range (l - W.length)))
      (List.range W.length),
    ground.famFold_congr_all Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => ground.getAt 0 Z i + (l - i - 1 + k))
        (List.range (l - W.length)))
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i - 1 + k)
        (List.range (l - W.length)))
      (fun i => ground.famFold_congr_all Nat.mul 1 _ _
        (fun k => by rw [hz i, Nat.zero_add]) (List.range (l - W.length)))
      (List.range W.length)]

/-- `lem:serstable`(i)'s dimension clause at the `D` series. -/
theorem dimGap_D : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    dimNumD W l * ground.famFold Nat.mul 1
        (gapAt (sertables.tableD l) (List.replicate l 1))
        (List.range (sertables.tableD l).posFolds.length)
      = dimDenD W l * ground.famFold Nat.mul 1
          (gapAt (sertables.tableD l) (memberRho W l))
          (List.range (sertables.tableD l).posFolds.length) := by
  intro W l hs hcl
  have hsa := ground.sortedAll W hs
  have hm := gapProdD W (memberRho W l) l hsa
    (fun k hk => memberRhoAt W l k hk) (memberRhoLen W l) hcl
  have hzl : (List.replicate W.length (0 : Nat)).length = W.length :=
    ground.length_replicate 0 W.length
  have h1 := gapProdD (List.replicate W.length 0) (List.replicate l 1) l
    (fun x => by
      rw [ground.getAt_replicate_zero, ground.getAt_replicate_zero]
      exact Nat.le_refl 0)
    (fun k hk => by
      rw [ground.getAt_replicate 0 1 l k hk,
        ground.getAt_replicate_zero, ground.getAt_replicate_zero])
    (ground.length_replicate 1 l) (by rw [hzl]; exact hcl)
  rw [hzl] at h1
  rw [hm, h1, dimDenD_eq W (List.replicate W.length 0) l hzl
    (fun i => ground.getAt_replicate_zero W.length i)]
  exact ground.mulLeftComm (dimNumD W l) (dimDenD W l) (tailD l W.length)

/-! ## The dimension tier's polynomial pair

`lem:serstable`(i)'s second read: the dimension is one polynomial
pair in the rank.  The gap product's four classes enter as their
own factors — the word-against-word difference factors rank-free
(the pair's own constant), the word sums and the short or long
factors single linear reads, and the two word-against-tail
telescopes the binomial pairs, one linear factor per box of the
word rather than one per tail key, the tail's own count carried on
the opposite member.  `dimPolyNumX` and `dimPolyDenX` are those
factors' convolution folds, seeded at the rank-free constants, and
`dimPolyX_eval` states the cross-multiplied agreement against the
displayed pair `dimNumX`, `dimDenX` at every rank clearing the
word's reach.  The bridge is the rising products' rectangle: the
window of `W_i` boxes over the tail's keys reads either way round,
`rise c (g + w) = rise c g · rise (c+g) w = rise c w · rise (c+w) g`,
once at each telescope. -/

/-- The rising product as the key range's own fold. -/
private theorem riseFam : ∀ (n c : Nat),
    ground.famFold Nat.mul 1 (fun k => c + k) (List.range n) = ground.rise c n
  | 0, _ => rfl
  | n + 1, c => by
    rw [ground.range_cons n,
      show ground.famFold Nat.mul 1 (fun k => c + k)
          (0 :: (List.range n).map (fun j => j + 1))
        = Nat.mul (c + 0) (ground.famFold Nat.mul 1 (fun k => c + k)
            ((List.range n).map (fun j => j + 1))) from rfl,
      ground.famFold_map Nat.mul 1 (fun k => c + k) (fun j => j + 1)
        (List.range n),
      ground.famFold_congr_members Nat.mul 1 (fun j => c + (j + 1))
        (fun j => c + 1 + j) (List.range n) (fun j _ => by
          rw [Nat.add_assoc c 1 j, Nat.add_comm 1 j]),
      riseFam n (c + 1), Nat.add_zero c]
    rfl

/-- An accumulating product over a key range whose factors read a
rising window is that window's own product. -/
private theorem foldRise (F : Nat → Nat) (c n : Nat)
    (h : ∀ k, F k = c + k) :
    (List.range n).foldl (fun acc k => acc * F k) 1 = ground.rise c n := by
  have h1 : (List.range n).foldl (fun acc k => acc * F k) 1
      = 1 * ground.famFold Nat.mul 1 F (List.range n) :=
    ground.foldlFold Nat.mul 1 ground.mulAssoc Nat.mul_one F
      (List.range n) 1
  rw [h1, Nat.one_mul,
    ground.famFold_congr_members Nat.mul 1 F (fun k => c + k)
      (List.range n) (fun k _ => h k)]
  exact riseFam n c

/-- Four paired folds over one key range agree at their pointwise
products. -/
private theorem famFold_quad (f1 f2 f3 f4 g1 g2 g3 g4 : Nat → Nat)
    (n : Nat) (h : ∀ i, i < n →
      f1 i * f2 i * f3 i * f4 i = g1 i * g2 i * g3 i * g4 i) :
    ground.famFold Nat.mul 1 f1 (List.range n)
        * ground.famFold Nat.mul 1 f2 (List.range n)
        * ground.famFold Nat.mul 1 f3 (List.range n)
        * ground.famFold Nat.mul 1 f4 (List.range n)
      = ground.famFold Nat.mul 1 g1 (List.range n)
        * ground.famFold Nat.mul 1 g2 (List.range n)
        * ground.famFold Nat.mul 1 g3 (List.range n)
        * ground.famFold Nat.mul 1 g4 (List.range n) := by
  rw [← ground.famFold_mul_split f1 f2 (List.range n),
    ← ground.famFold_mul_split (fun x => f1 x * f2 x) f3 (List.range n),
    ← ground.famFold_mul_split (fun x => f1 x * f2 x * f3 x) f4
      (List.range n),
    ← ground.famFold_mul_split g1 g2 (List.range n),
    ← ground.famFold_mul_split (fun x => g1 x * g2 x) g3 (List.range n),
    ← ground.famFold_mul_split (fun x => g1 x * g2 x * g3 x) g4
      (List.range n)]
  refine ground.famFold_congr_members Nat.mul 1 _ _ (List.range n) ?_
  intro i hi
  exact h i (ground.ltOfMem hi)

/-! The factors' own gaps: each linear factor's value against the
rank's scale, and the products' regrouping at the two telescope
pairs. -/

/-- The rank-free gap's join: a stated clearance moves the
subtraction across the sum. -/
private theorem linGap (S u v : Nat) (h : u ≤ v) :
    u + (S + (v - u)) = S + v := by
  rw [Nat.add_left_comm u S (v - u), ground.natAddSubCancel h]

/-- The doubled rank as its own sum. -/
private theorem twoL (l : Nat) : l * 2 = l + l := by
  rw [Nat.mul_comm l 2, Nat.two_mul l]

/-- The four keys' regrouping at a joined pair. -/
private theorem gapTwo (i a p q k : Nat) :
    i + a + (p + q + k) = k + (i + p + (a + q)) := by
  rw [← Nat.add_assoc (i + a) (p + q) k,
    Nat.add_add_add_comm i a p q,
    Nat.add_comm (i + p + (a + q)) k]

/-- The word-sum factor's gap at a stated series offset. -/
private theorem smGapN (X l i j s : Nat) (h : s + i + j ≤ 2 * l) :
    (s + i + j) + (X + (2 * l - s - i - j)) = X + l * 2 := by
  rw [ground.subSub (2 * l - s) i j, ground.subSub (2 * l) s (i + j),
    ← Nat.add_assoc s i j, linGap X (s + i + j) (2 * l) h,
    Nat.mul_comm l 2]

/-- The word-sum factor's gap at the unit display. -/
private theorem smGapD (l i j s : Nat) (h : s + i + j ≤ 2 * l) :
    (s + i + j) + (2 * l - s - i - j) = 0 + l * 2 := by
  rw [Nat.zero_add, ground.subSub (2 * l - s) i j,
    ground.subSub (2 * l) s (i + j), ← Nat.add_assoc s i j,
    ground.natAddSubCancel h, Nat.mul_comm l 2]

/-- The word-sum factor's gap at the vacant offset. -/
private theorem smGapN0 (X l i j : Nat) (h : i + j ≤ 2 * l) :
    (i + j) + (X + (2 * l - i - j)) = X + l * 2 := by
  rw [ground.subSub (2 * l) i j, linGap X (i + j) (2 * l) h,
    Nat.mul_comm l 2]

/-- The word-sum factor's gap at the vacant offset, unit display. -/
private theorem smGapD0 (l i j : Nat) (h : i + j ≤ 2 * l) :
    (i + j) + (2 * l - i - j) = 0 + l * 2 := by
  rw [Nat.zero_add, ground.subSub (2 * l) i j,
    ground.natAddSubCancel h, Nat.mul_comm l 2]

/-- The short factor's gap. -/
private theorem shGapN (X l i : Nat) (h : 2 * i + 1 ≤ 2 * l) :
    (2 * i + 1) + (X + (2 * l - 1 - 2 * i)) = X + l * 2 := by
  rw [ground.subSub (2 * l) 1 (2 * i), Nat.add_comm 1 (2 * i),
    linGap X (2 * i + 1) (2 * l) h, Nat.mul_comm l 2]

/-- The short factor's gap at the unit display. -/
private theorem shGapD (l i : Nat) (h : 2 * i + 1 ≤ 2 * l) :
    (2 * i + 1) + (2 * l - 1 - 2 * i) = 0 + l * 2 := by
  rw [Nat.zero_add, ground.subSub (2 * l) 1 (2 * i),
    Nat.add_comm 1 (2 * i), ground.natAddSubCancel h,
    Nat.mul_comm l 2]

/-- The long factor's gap. -/
private theorem lgGapN (X l i : Nat) (h : i ≤ l) :
    i + (X + (l - i)) = X + l * 1 := by
  rw [linGap X i l h, Nat.mul_one l]

/-- The long factor's gap at the unit display. -/
private theorem lgGapD (l i : Nat) (h : i ≤ l) :
    i + (l - i) = 0 + l * 1 := by
  rw [Nat.zero_add, Nat.mul_one l, ground.natAddSubCancel h]

/-- A telescope factor's gap at a single rank. -/
private theorem riseGap1 (l i k : Nat) (h : i ≤ l) :
    i + (l - i + k) = k + l * 1 := by
  rw [← Nat.add_assoc i (l - i) k, ground.natAddSubCancel h,
    Nat.mul_one l, Nat.add_comm l k]

/-- A telescope factor's gap at a single rank, raised by one. -/
private theorem riseGap1u (l i k : Nat) (h : i ≤ l) :
    i + (l - i + 1 + k) = (k + 1) + l * 1 := by
  rw [← Nat.add_assoc i (l - i + 1) k, ← Nat.add_assoc i (l - i) 1,
    ground.natAddSubCancel h, Nat.mul_one l,
    Nat.add_right_comm l 1 k, Nat.add_right_comm k 1 l,
    Nat.add_comm l k]

/-- The sum telescope's gap at the doubled rank. -/
private theorem riseGap2 (l a i k : Nat) (hi : i ≤ l) (ha : a ≤ l) :
    (i + a) + (l - i + (l - a) + k) = k + l * 2 := by
  rw [gapTwo i a (l - i) (l - a) k, ground.natAddSubCancel hi,
    ground.natAddSubCancel ha, twoL l]

/-- The sum telescope's gap at the doubled rank, raised by one. -/
private theorem riseGap2u (l a i k : Nat) (hi : i ≤ l) (ha : a ≤ l) :
    (i + a) + (l - i + 1 + (l - a) + k) = (k + 1) + l * 2 := by
  rw [gapTwo i a (l - i + 1) (l - a) k, ← Nat.add_assoc i (l - i) 1,
    ground.natAddSubCancel hi, ground.natAddSubCancel ha, twoL l,
    Nat.add_assoc k 1 (l + l), Nat.add_comm l 1, Nat.add_assoc 1 l l]

/-- The sum telescope's gap at the doubled rank, lowered by one. -/
private theorem riseGap2d (l a i k : Nat) (hi : i + 1 ≤ l) (ha : a ≤ l) :
    (i + a + 1) + (l - (i + 1) + (l - a) + k) = k + l * 2 := by
  rw [Nat.add_right_comm i a 1,
    gapTwo (i + 1) a (l - (i + 1)) (l - a) k,
    ground.natAddSubCancel hi, ground.natAddSubCancel ha, twoL l]

/-- A telescope factor's gap at a single rank, lowered by one. -/
private theorem riseGap1D (l i k : Nat) (h : i + 1 ≤ l) :
    (i + 1) + (l - i - 1 + k) = k + l * 1 := by
  rw [ground.subSub l i 1]
  exact riseGap1 l (i + 1) k h

/-- The sum telescope's gap at the lowered rank's spelling. -/
private theorem riseGap2D (l a i k : Nat) (hi : i + 1 ≤ l) (ha : a ≤ l) :
    (i + a + 1) + (l - i - 1 + (l - a) + k) = k + l * 2 := by
  rw [ground.subSub l i 1]
  exact riseGap2d l a i k hi ha

/-- The two blocks' regrouping at the numerator's side. -/
private theorem numShuffle (p s h u1 u2 pd sd hd v1 v2 : Nat) :
    p * s * h * u1 * u2 * (pd * sd * hd * v1 * v2)
      = pd * sd * hd * p * s * h * (u1 * u2 * v1 * v2) := by
  rw [ground.mulAssoc (p * s * h) u1 u2,
    ground.mulAssoc (pd * sd * hd) v1 v2,
    ground.mulMulMulComm (p * s * h) (u1 * u2) (pd * sd * hd) (v1 * v2),
    Nat.mul_comm (p * s * h) (pd * sd * hd),
    ← ground.mulAssoc (pd * sd * hd) (p * s) h,
    ← ground.mulAssoc (pd * sd * hd) p s,
    ← ground.mulAssoc (u1 * u2) v1 v2]

/-- The two blocks' regrouping at the denominator's side. -/
private theorem denShuffle (p s h pd cc sd hd a2 w1 w2 : Nat) :
    pd * cc * sd * hd * a2 * (p * s * h * w1 * w2)
      = pd * sd * hd * p * s * h * (cc * a2 * w1 * w2) := by
  rw [ground.mulRightComm pd cc sd, ground.mulRightComm (pd * sd) cc hd,
    ground.mulAssoc (pd * sd * hd) cc a2,
    ground.mulAssoc (p * s * h) w1 w2,
    ground.mulMulMulComm (pd * sd * hd) (cc * a2) (p * s * h) (w1 * w2),
    ← ground.mulAssoc (pd * sd * hd) (p * s) h,
    ← ground.mulAssoc (pd * sd * hd) p s,
    ← ground.mulAssoc (cc * a2) w1 w2]

/-- The two blocks' regrouping where no middle factor stands. -/
private theorem numShuffleD (p s u1 u2 pd sd v1 v2 : Nat) :
    p * s * u1 * u2 * (pd * sd * v1 * v2)
      = pd * sd * p * s * (u1 * u2 * v1 * v2) := by
  rw [ground.mulAssoc (p * s) u1 u2,
    ground.mulAssoc (pd * sd) v1 v2,
    ground.mulMulMulComm (p * s) (u1 * u2) (pd * sd) (v1 * v2),
    Nat.mul_comm (p * s) (pd * sd),
    ← ground.mulAssoc (pd * sd) p s,
    ← ground.mulAssoc (u1 * u2) v1 v2]

/-- The denominator's regrouping where no middle factor stands. -/
private theorem denShuffleD (p s pd cc sd a2 w1 w2 : Nat) :
    pd * cc * sd * a2 * (p * s * w1 * w2)
      = pd * sd * p * s * (cc * a2 * w1 * w2) := by
  rw [ground.mulRightComm pd cc sd,
    ground.mulAssoc (pd * sd) cc a2,
    ground.mulAssoc (p * s) w1 w2,
    ground.mulMulMulComm (pd * sd) (cc * a2) (p * s) (w1 * w2),
    ← ground.mulAssoc (pd * sd) p s,
    ← ground.mulAssoc (cc * a2) w1 w2]

/-- The two telescopes' rectangles at one key. -/
private theorem quadKey (c1 c2 g w : Nat) :
    ground.rise (c1 + g) w * ground.rise (c2 + g) w
        * ground.rise c1 g * ground.rise c2 g
      = ground.rise c1 w * ground.rise c2 w
        * ground.rise (c1 + w) g * ground.rise (c2 + w) g := by
  rw [ground.mulAssoc (ground.rise (c1 + g) w * ground.rise (c2 + g) w)
      (ground.rise c1 g) (ground.rise c2 g),
    ground.mulMulMulComm (ground.rise (c1 + g) w) (ground.rise (c2 + g) w)
      (ground.rise c1 g) (ground.rise c2 g),
    ground.rise_rect c1 g w, ground.rise_rect c2 g w,
    ground.mulMulMulComm (ground.rise c1 w) (ground.rise (c1 + w) g)
      (ground.rise c2 w) (ground.rise (c2 + w) g),
    ← ground.mulAssoc (ground.rise c1 w * ground.rise c2 w)
      (ground.rise (c1 + w) g) (ground.rise (c2 + w) g)]



/-- The `B` dimension numerator as a polynomial in the rank. -/
def dimPolyNumB (W : List Nat) : poly.Poly :=
  let a := W.length
  let base : poly.Poly := [ground.BPair.ofNat
    ((places.pairsOf a).foldl (fun acc p =>
      acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
        + (p.2 - p.1))) 1)]
  let sm := (places.pairsOf a).foldl (fun acc p => poly.mul acc
    [⟨ground.posOfSucc (ground.getAt 0 W p.1 + ground.getAt 0 W p.2),
      ground.posOfSucc (1 + p.1 + p.2)⟩,
     ground.BPair.ofNat 2]) base
  let sh := (List.range a).foldl (fun acc i => poly.mul acc
    [⟨ground.posOfSucc (2 * ground.getAt 0 W i),
      ground.posOfSucc (2 * i + 1)⟩,
     ground.BPair.ofNat 2]) sm
  let t1 := (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
       ground.BPair.ofNat 1]) acc) sh
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc (i + a)⟩,
       ground.BPair.ofNat 2]) acc) t1

/-- The `B` dimension denominator as a polynomial in the rank. -/
def dimPolyDenB (W : List Nat) : poly.Poly :=
  let a := W.length
  let base : poly.Poly := [ground.BPair.ofNat
    ((places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
      * (List.range a).foldl (fun acc i =>
          acc * (List.range (ground.getAt 0 W i)).foldl
            (fun acc2 k => acc2 * (a - i + k)) 1) 1)]
  let sm := (places.pairsOf a).foldl (fun acc p => poly.mul acc
    [⟨ground.posOfSucc 0, ground.posOfSucc (1 + p.1 + p.2)⟩,
     ground.BPair.ofNat 2]) base
  let sh := (List.range a).foldl (fun acc i => poly.mul acc
    [⟨ground.posOfSucc 0, ground.posOfSucc (2 * i + 1)⟩,
     ground.BPair.ofNat 2]) sm
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
       ground.BPair.ofNat 1]) acc) sh

/-- The `C` dimension numerator as a polynomial in the rank. -/
def dimPolyNumC (W : List Nat) : poly.Poly :=
  let a := W.length
  let base : poly.Poly := [ground.BPair.ofNat
    ((places.pairsOf a).foldl (fun acc p =>
      acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
        + (p.2 - p.1))) 1)]
  let sm := (places.pairsOf a).foldl (fun acc p => poly.mul acc
    [⟨ground.posOfSucc (ground.getAt 0 W p.1 + ground.getAt 0 W p.2),
      ground.posOfSucc (p.1 + p.2)⟩,
     ground.BPair.ofNat 2]) base
  let lg := (List.range a).foldl (fun acc i => poly.mul acc
    [⟨ground.posOfSucc (ground.getAt 0 W i), ground.posOfSucc i⟩,
     ground.BPair.ofNat 1]) sm
  let t1 := (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
       ground.BPair.ofNat 1]) acc) lg
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc (k + 1), ground.posOfSucc (i + a)⟩,
       ground.BPair.ofNat 2]) acc) t1

/-- The `C` dimension denominator as a polynomial in the rank. -/
def dimPolyDenC (W : List Nat) : poly.Poly :=
  let a := W.length
  let base : poly.Poly := [ground.BPair.ofNat
    ((places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
      * (List.range a).foldl (fun acc i =>
          acc * (List.range (ground.getAt 0 W i)).foldl
            (fun acc2 k => acc2 * (a - i + k)) 1) 1)]
  let sm := (places.pairsOf a).foldl (fun acc p => poly.mul acc
    [⟨ground.posOfSucc 0, ground.posOfSucc (p.1 + p.2)⟩,
     ground.BPair.ofNat 2]) base
  let lg := (List.range a).foldl (fun acc i => poly.mul acc
    [⟨ground.posOfSucc 0, ground.posOfSucc i⟩,
     ground.BPair.ofNat 1]) sm
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc (k + 1), ground.posOfSucc i⟩,
       ground.BPair.ofNat 1]) acc) lg

/-- The `D` dimension numerator as a polynomial in the rank. -/
def dimPolyNumD (W : List Nat) : poly.Poly :=
  let a := W.length
  let base : poly.Poly := [ground.BPair.ofNat
    ((places.pairsOf a).foldl (fun acc p =>
      acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
        + (p.2 - p.1))) 1)]
  let sm := (places.pairsOf a).foldl (fun acc p => poly.mul acc
    [⟨ground.posOfSucc (ground.getAt 0 W p.1 + ground.getAt 0 W p.2),
      ground.posOfSucc (2 + p.1 + p.2)⟩,
     ground.BPair.ofNat 2]) base
  let t1 := (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
       ground.BPair.ofNat 1]) acc) sm
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc (i + a + 1)⟩,
       ground.BPair.ofNat 2]) acc) t1

/-- The `D` dimension denominator as a polynomial in the rank. -/
def dimPolyDenD (W : List Nat) : poly.Poly :=
  let a := W.length
  let base : poly.Poly := [ground.BPair.ofNat
    ((places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
      * (List.range a).foldl (fun acc i =>
          acc * (List.range (ground.getAt 0 W i)).foldl
            (fun acc2 k => acc2 * (a - i + k)) 1) 1)]
  let sm := (places.pairsOf a).foldl (fun acc p => poly.mul acc
    [⟨ground.posOfSucc 0, ground.posOfSucc (2 + p.1 + p.2)⟩,
     ground.BPair.ofNat 2]) base
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
      [⟨ground.posOfSucc k, ground.posOfSucc (i + 1)⟩,
       ground.BPair.ofNat 1]) acc) sm

/-- The pair keys' clearance at the doubled rank. -/
private theorem pairBound (l i j : Nat) (hij : i < j) (hjl : j ≤ l) :
    1 + i + j ≤ 2 * l := by
  have h1 : 1 + i ≤ j := by
    rw [Nat.add_comm 1 i]
    exact hij
  rw [Nat.two_mul l]
  exact Nat.le_trans (Nat.add_le_add_right h1 j) (Nat.add_le_add hjl hjl)

/-- The pair keys' clearance at the vacant offset. -/
private theorem pairBound0 (l i j : Nat) (hil : i ≤ l) (hjl : j ≤ l) :
    i + j ≤ 2 * l := by
  rw [Nat.two_mul l]
  exact Nat.add_le_add hil hjl

/-- The pair keys' clearance at the doubled offset. -/
private theorem pairBound2 (l i j : Nat) (hij : i < j) (hjl : j + 1 ≤ l) :
    2 + i + j ≤ 2 * l := by
  have h1 : 2 + i ≤ 1 + j := by
    rw [show (2 : Nat) + i = 1 + (1 + i) from by
      rw [← Nat.add_assoc 1 1 i]]
    exact Nat.add_le_add_left (by rw [Nat.add_comm 1 i]; exact hij) 1
  rw [Nat.two_mul l]
  refine Nat.le_trans (Nat.add_le_add_right h1 j) ?_
  exact Nat.add_le_add (by rw [Nat.add_comm 1 j]; exact hjl)
    (Nat.le_trans (Nat.le_succ j) hjl)

/-- The short factor's key clearance. -/
private theorem shBound (l i : Nat) (h : i + 1 ≤ l) :
    2 * i + 1 ≤ 2 * l := by
  rw [Nat.two_mul l, Nat.two_mul i, Nat.add_right_comm i i 1]
  exact Nat.add_le_add h (Nat.le_trans (Nat.le_succ i) h)

/-- The `B` numerator polynomial's value at a rank. -/
private def numValB (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - 1 - p.1 - p.2))) dif
  let sh := (List.range a).foldl (fun acc i =>
    acc * (2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))) sm
  let t1 := (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + k)) acc) sh
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + (l - a) + k)) acc) t1

/-- The `B` denominator polynomial's value at a rank. -/
private def denValB (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let base := (places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
    * (List.range a).foldl (fun acc i =>
        acc * (List.range (ground.getAt 0 W i)).foldl
          (fun acc2 k => acc2 * (a - i + k)) 1) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (2 * l - 1 - p.1 - p.2)) base
  let sh := (List.range a).foldl (fun acc i =>
    acc * (2 * l - 1 - 2 * i)) sm
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + k)) acc) sh

/-- The `B` numerator polynomial's evaluation at a cleared rank. -/
private theorem numReadB (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    (poly.eval (dimPolyNumB W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (numValB W l)) := by
  have hbase := poly.constRead ((places.pairsOf W.length).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
      + (p.2 - p.1))) 1) l
  have hsm := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (p : Nat × Nat) => poly.mul acc
      [⟨ground.posOfSucc (ground.getAt 0 W p.1 + ground.getAt 0 W p.2),
        ground.posOfSucc (1 + p.1 + p.2)⟩,
       ground.BPair.ofNat 2])
    (fun (n : Nat) (p : Nat × Nat) => n *
      (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
        + (2 * l - 1 - p.1 - p.2)))
    (fun p => p.1 < p.2 ∧ p.2 < W.length)
    (fun acc n p hp hacc => poly.eval_mulStep
      (poly.linRead (ground.getAt 0 W p.1 + ground.getAt 0 W p.2)
        (1 + p.1 + p.2) 2
        (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
          + (2 * l - 1 - p.1 - p.2)) l
        (smGapN (ground.getAt 0 W p.1 + ground.getAt 0 W p.2) l
          p.1 p.2 1 (pairBound l p.1 p.2 hp.1
            (Nat.le_trans (Nat.le_of_lt hp.2) hal))))
      acc n hacc)
    (places.pairsOf W.length)
    (fun p hp => places.pairs_mem W.length p
      (ground.countOf_pos_of_mem hp))
    _ _ hbase
  have hsh := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) => poly.mul acc
      [⟨ground.posOfSucc (2 * ground.getAt 0 W i),
        ground.posOfSucc (2 * i + 1)⟩,
       ground.BPair.ofNat 2])
    (fun (n i : Nat) => n * (2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i)))
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_mulStep
      (poly.linRead (2 * ground.getAt 0 W i) (2 * i + 1) 2
        (2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i)) l
        (shGapN (2 * ground.getAt 0 W i) l i
          (shBound l i (Nat.le_trans hi hal))))
      acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsm
  have ht1 := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1])
      (fun (n2 k : Nat) => n2 * (l - i + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k i 1 (l - i + k) l
          (riseGap1 l i k (Nat.le_trans (Nat.le_of_lt hi) hal)))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsh
  exact poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc (i + W.length)⟩,
         ground.BPair.ofNat 2]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + (l - W.length) + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc (i + W.length)⟩,
         ground.BPair.ofNat 2])
      (fun (n2 k : Nat) => n2 * (l - i + (l - W.length) + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k (i + W.length) 2 (l - i + (l - W.length) + k) l
          (riseGap2 l W.length i k
            (Nat.le_trans (Nat.le_of_lt hi) hal) hal))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ ht1

/-- The `B` denominator polynomial's evaluation at a cleared rank. -/
private theorem denReadB (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    (poly.eval (dimPolyDenB W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (denValB W l)) := by
  have hbase := poly.constRead
    ((places.pairsOf W.length).foldl (fun acc p => acc * (p.2 - p.1)) 1
      * (List.range W.length).foldl (fun acc i =>
          acc * (List.range (ground.getAt 0 W i)).foldl
            (fun acc2 k => acc2 * (W.length - i + k)) 1) 1) l
  have hsm := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (p : Nat × Nat) => poly.mul acc
      [⟨ground.posOfSucc 0, ground.posOfSucc (1 + p.1 + p.2)⟩,
       ground.BPair.ofNat 2])
    (fun (n : Nat) (p : Nat × Nat) => n * (2 * l - 1 - p.1 - p.2))
    (fun p => p.1 < p.2 ∧ p.2 < W.length)
    (fun acc n p hp hacc => poly.eval_mulStep
      (poly.linRead 0 (1 + p.1 + p.2) 2 (2 * l - 1 - p.1 - p.2) l
        (smGapD l p.1 p.2 1 (pairBound l p.1 p.2 hp.1
          (Nat.le_trans (Nat.le_of_lt hp.2) hal))))
      acc n hacc)
    (places.pairsOf W.length)
    (fun p hp => places.pairs_mem W.length p
      (ground.countOf_pos_of_mem hp))
    _ _ hbase
  have hsh := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) => poly.mul acc
      [⟨ground.posOfSucc 0, ground.posOfSucc (2 * i + 1)⟩,
       ground.BPair.ofNat 2])
    (fun (n i : Nat) => n * (2 * l - 1 - 2 * i))
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_mulStep
      (poly.linRead 0 (2 * i + 1) 2 (2 * l - 1 - 2 * i) l
        (shGapD l i (shBound l i (Nat.le_trans hi hal))))
      acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsm
  exact poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1])
      (fun (n2 k : Nat) => n2 * (l - i + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k i 1 (l - i + k) l
          (riseGap1 l i k (Nat.le_trans (Nat.le_of_lt hi) hal)))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsh

/-- The `B` dimension pair's displayed reads in flat form. -/
private theorem dimNumB_flat (W : List Nat) (l : Nat) :
    dimNumB W l
      = (places.pairsOf W.length).foldl (fun acc p =>
          acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
            + (p.2 - p.1))) 1
        * (places.pairsOf W.length).foldl (fun acc p =>
            acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
              + (2 * l - 1 - p.1 - p.2))) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (ground.getAt 0 W i + (l - i + k))) 1) 1 := rfl

/-- The `B` dimension denominator in flat form. -/
private theorem dimDenB_flat (W : List Nat) (l : Nat) :
    dimDenB W l
      = (places.pairsOf W.length).foldl (fun acc p =>
          acc * (p.2 - p.1)) 1
        * (places.pairsOf W.length).foldl (fun acc p =>
            acc * (2 * l - 1 - p.1 - p.2)) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (2 * l - 1 - 2 * i)) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (W.length - i + k)) 1) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (l - i + k)) 1) 1 := rfl

/-- The `B` pair's cross-multiplied identity at a cleared rank. -/
private theorem crossB (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    numValB W l * dimDenB W l = denValB W l * dimNumB W l := by
  show ((List.range W.length).foldl (fun acc i =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
        acc2 * (l - i + (l - W.length) + k)) acc)
    ((List.range W.length).foldl (fun acc i =>
        (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
          acc2 * (l - i + k)) acc)
      ((List.range W.length).foldl (fun acc i =>
          acc * (2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i)))
        ((places.pairsOf W.length).foldl (fun acc p =>
            acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
              + (2 * l - 1 - p.1 - p.2)))
          ((places.pairsOf W.length).foldl (fun acc p =>
              acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
                + (p.2 - p.1))) 1))))) * dimDenB W l
    = ((List.range W.length).foldl (fun acc i =>
        (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
          acc2 * (l - i + k)) acc)
      ((List.range W.length).foldl (fun acc i =>
          acc * (2 * l - 1 - 2 * i))
        ((places.pairsOf W.length).foldl (fun acc p =>
            acc * (2 * l - 1 - p.1 - p.2))
          ((places.pairsOf W.length).foldl (fun acc p =>
              acc * (p.2 - p.1)) 1
            * (List.range W.length).foldl (fun acc i =>
                acc * (List.range (ground.getAt 0 W i)).foldl
                  (fun acc2 k => acc2 * (W.length - i + k)) 1) 1))))
      * dimNumB W l
  rw [dimNumB_flat W l, dimDenB_flat W l,
    foldlFam (fun p : Nat × Nat => ground.getAt 0 W p.1
      - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => p.2 - p.1)
      (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => ground.getAt 0 W p.1
      + ground.getAt 0 W p.2 + (2 * l - 1 - p.1 - p.2))
      (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => 2 * l - 1 - p.1 - p.2)
      (places.pairsOf W.length),
    foldlFam (fun i => 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))
      (List.range W.length),
    foldlFam (fun i => 2 * l - 1 - 2 * i) (List.range W.length),
    foldlFam (fun i => (List.range (ground.getAt 0 W i)).foldl
      (fun acc2 k => acc2 * (W.length - i + k)) 1) (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1)
      (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (ground.getAt 0 W i + (l - i + k))) 1)
      (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (W.length - i + k)) 1) (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (l - i + k)) 1) (List.range W.length),
    ground.foldlProd (fun p : Nat × Nat => ground.getAt 0 W p.1
      + ground.getAt 0 W p.2 + (2 * l - 1 - p.1 - p.2))
      (places.pairsOf W.length),
    ground.foldlProd (fun i => 2 * ground.getAt 0 W i + (2 * l - 1 - 2 * i))
      (List.range W.length),
    ground.foldlProd (fun p : Nat × Nat => 2 * l - 1 - p.1 - p.2)
      (places.pairsOf W.length),
    ground.foldlProd (fun i => 2 * l - 1 - 2 * i) (List.range W.length),
    ground.foldl_nest (fun i k => l - i + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.foldl_nest (fun i k => l - i + (l - W.length) + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.foldl_nest (fun i k => l - i + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i) (l - i)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => l - i + (l - W.length) + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i + (l - W.length)) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i) (l - i + (l - W.length))),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (ground.getAt 0 W i)).foldl
        (fun acc2 k => acc2 * (W.length - i + k)) 1)
      (fun i => ground.rise (W.length - i) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => foldRise (fun k => W.length - i + k) (W.length - i)
        (ground.getAt 0 W i) (fun _ => rfl)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1)
      (fun i => ground.rise (ground.getAt 0 W i + (W.length - i))
        (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise
        (fun k => ground.getAt 0 W i + (W.length - i + k))
        (ground.getAt 0 W i + (W.length - i)) (l - W.length)
        (fun k => (Nat.add_assoc (ground.getAt 0 W i)
          (W.length - i) k).symm)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (ground.getAt 0 W i + (l - i + k))) 1)
      (fun i => ground.rise (ground.getAt 0 W i + (l - i)) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise
        (fun k => ground.getAt 0 W i + (l - i + k))
        (ground.getAt 0 W i + (l - i)) (l - W.length)
        (fun k => (Nat.add_assoc (ground.getAt 0 W i) (l - i) k).symm)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (W.length - i + k)) 1)
      (fun i => ground.rise (W.length - i) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise (fun k => W.length - i + k) (W.length - i)
        (l - W.length) (fun _ => rfl)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (l - i + k)) 1)
      (fun i => ground.rise (l - i) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise (fun k => l - i + k) (l - i) (l - W.length)
        (fun _ => rfl))]
  rw [numShuffle
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        + ground.getAt 0 W p.2 + (2 * l - 1 - p.1 - p.2))
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => 2 * ground.getAt 0 W i
        + (2 * l - 1 - 2 * i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i + (l - W.length))
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => p.2 - p.1)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => 2 * l - 1 - p.1 - p.2)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => 2 * l - 1 - 2 * i)
        (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (W.length - i)
        (l - W.length)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i) (l - W.length))
        (List.range W.length)),
    denShuffle
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        + ground.getAt 0 W p.2 + (2 * l - 1 - p.1 - p.2))
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => 2 * ground.getAt 0 W i
        + (2 * l - 1 - 2 * i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => p.2 - p.1)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (W.length - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => 2 * l - 1 - p.1 - p.2)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => 2 * l - 1 - 2 * i)
        (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (ground.getAt 0 W i
        + (W.length - i)) (l - W.length)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (ground.getAt 0 W i
        + (l - i)) (l - W.length)) (List.range W.length))]
  exact congrArg _ (famFold_quad
    (fun i => ground.rise (l - i) (ground.getAt 0 W i))
    (fun i => ground.rise (l - i + (l - W.length)) (ground.getAt 0 W i))
    (fun i => ground.rise (W.length - i) (l - W.length))
    (fun i => ground.rise (l - i) (l - W.length))
    (fun i => ground.rise (W.length - i) (ground.getAt 0 W i))
    (fun i => ground.rise (l - i) (ground.getAt 0 W i))
    (fun i => ground.rise (ground.getAt 0 W i + (W.length - i)) (l - W.length))
    (fun i => ground.rise (ground.getAt 0 W i + (l - i)) (l - W.length))
    W.length (fun i hi => by
      rw [← ground.subJoin (Nat.le_of_lt hi) hal,
        Nat.add_comm (l - W.length) (W.length - i),
        Nat.add_comm (ground.getAt 0 W i) (W.length - i),
        Nat.add_comm (ground.getAt 0 W i)
          (W.length - i + (l - W.length))]
      exact quadKey (W.length - i) (W.length - i + (l - W.length))
        (l - W.length) (ground.getAt 0 W i)))

/-- `lem:serstable`(i)'s dimension polynomial pair at the `B`
series: at every rank clearing the word's reach the polynomial
pair's cross-multiplied read is the displayed pair's. -/
theorem dimPolyB_eval : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    (poly.eval (dimPolyNumB W) (ground.BPair.ofNat l)
        * ground.BPair.ofNat (dimDenB W l)).oneValue
      (poly.eval (dimPolyDenB W) (ground.BPair.ofNat l)
        * ground.BPair.ofNat (dimNumB W l)) := by
  intro W l _ hl
  have hal : W.length ≤ l :=
    Nat.le_trans (Nat.le_add_right W.length 2) hl
  refine ground.BPair.oneValue_trans
    (ground.BPair.mul_congr (numReadB W l hal)
      (ground.BPair.oneValue_refl (ground.BPair.ofNat (dimDenB W l)))) ?_
  refine ground.BPair.oneValue_trans
    (ground.BPair.oneValue_symm
      (ground.BPair.ofNat_mul (numValB W l) (dimDenB W l))) ?_
  rw [crossB W l hal]
  refine ground.BPair.oneValue_trans
    (ground.BPair.ofNat_mul (denValB W l) (dimNumB W l)) ?_
  exact ground.BPair.mul_congr
    (ground.BPair.oneValue_symm (denReadB W l hal))
    (ground.BPair.oneValue_refl (ground.BPair.ofNat (dimNumB W l)))

/-- The `C` numerator polynomial's value at a rank. -/
private def numValC (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - p.1 - p.2))) dif
  let lg := (List.range a).foldl (fun acc i =>
    acc * (ground.getAt 0 W i + (l - i))) sm
  let t1 := (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + k)) acc) lg
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + 1 + (l - a) + k)) acc) t1

/-- The `C` denominator polynomial's value at a rank. -/
private def denValC (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let base := (places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
    * (List.range a).foldl (fun acc i =>
        acc * (List.range (ground.getAt 0 W i)).foldl
          (fun acc2 k => acc2 * (a - i + k)) 1) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (2 * l - p.1 - p.2)) base
  let lg := (List.range a).foldl (fun acc i => acc * (l - i)) sm
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + 1 + k)) acc) lg

/-- The `C` numerator polynomial's evaluation at a cleared rank. -/
private theorem numReadC (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    (poly.eval (dimPolyNumC W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (numValC W l)) := by
  have hbase := poly.constRead ((places.pairsOf W.length).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
      + (p.2 - p.1))) 1) l
  have hsm := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (p : Nat × Nat) => poly.mul acc
      [⟨ground.posOfSucc (ground.getAt 0 W p.1 + ground.getAt 0 W p.2),
        ground.posOfSucc (p.1 + p.2)⟩,
       ground.BPair.ofNat 2])
    (fun (n : Nat) (p : Nat × Nat) => n *
      (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
        + (2 * l - p.1 - p.2)))
    (fun p => p.1 < p.2 ∧ p.2 < W.length)
    (fun acc n p hp hacc => poly.eval_mulStep
      (poly.linRead (ground.getAt 0 W p.1 + ground.getAt 0 W p.2)
        (p.1 + p.2) 2
        (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
          + (2 * l - p.1 - p.2)) l
        (smGapN0 (ground.getAt 0 W p.1 + ground.getAt 0 W p.2) l
          p.1 p.2 (pairBound0 l p.1 p.2
            (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans hp.1 hp.2)) hal)
            (Nat.le_trans (Nat.le_of_lt hp.2) hal))))
      acc n hacc)
    (places.pairsOf W.length)
    (fun p hp => places.pairs_mem W.length p
      (ground.countOf_pos_of_mem hp))
    _ _ hbase
  have hlg := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) => poly.mul acc
      [⟨ground.posOfSucc (ground.getAt 0 W i), ground.posOfSucc i⟩,
       ground.BPair.ofNat 1])
    (fun (n i : Nat) => n * (ground.getAt 0 W i + (l - i)))
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_mulStep
      (poly.linRead (ground.getAt 0 W i) i 1
        (ground.getAt 0 W i + (l - i)) l
        (lgGapN (ground.getAt 0 W i) l i
          (Nat.le_trans (Nat.le_of_lt hi) hal)))
      acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsm
  have ht1 := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1])
      (fun (n2 k : Nat) => n2 * (l - i + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k i 1 (l - i + k) l
          (riseGap1 l i k (Nat.le_trans (Nat.le_of_lt hi) hal)))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hlg
  exact poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc (k + 1), ground.posOfSucc (i + W.length)⟩,
         ground.BPair.ofNat 2]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + 1 + (l - W.length) + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc (k + 1), ground.posOfSucc (i + W.length)⟩,
         ground.BPair.ofNat 2])
      (fun (n2 k : Nat) => n2 * (l - i + 1 + (l - W.length) + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead (k + 1) (i + W.length) 2
          (l - i + 1 + (l - W.length) + k) l
          (riseGap2u l W.length i k
            (Nat.le_trans (Nat.le_of_lt hi) hal) hal))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ ht1

/-- The `C` denominator polynomial's evaluation at a cleared rank. -/
private theorem denReadC (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    (poly.eval (dimPolyDenC W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (denValC W l)) := by
  have hbase := poly.constRead
    ((places.pairsOf W.length).foldl (fun acc p => acc * (p.2 - p.1)) 1
      * (List.range W.length).foldl (fun acc i =>
          acc * (List.range (ground.getAt 0 W i)).foldl
            (fun acc2 k => acc2 * (W.length - i + k)) 1) 1) l
  have hsm := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (p : Nat × Nat) => poly.mul acc
      [⟨ground.posOfSucc 0, ground.posOfSucc (p.1 + p.2)⟩,
       ground.BPair.ofNat 2])
    (fun (n : Nat) (p : Nat × Nat) => n * (2 * l - p.1 - p.2))
    (fun p => p.1 < p.2 ∧ p.2 < W.length)
    (fun acc n p hp hacc => poly.eval_mulStep
      (poly.linRead 0 (p.1 + p.2) 2 (2 * l - p.1 - p.2) l
        (smGapD0 l p.1 p.2 (pairBound0 l p.1 p.2
          (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans hp.1 hp.2)) hal)
          (Nat.le_trans (Nat.le_of_lt hp.2) hal))))
      acc n hacc)
    (places.pairsOf W.length)
    (fun p hp => places.pairs_mem W.length p
      (ground.countOf_pos_of_mem hp))
    _ _ hbase
  have hlg := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) => poly.mul acc
      [⟨ground.posOfSucc 0, ground.posOfSucc i⟩,
       ground.BPair.ofNat 1])
    (fun (n i : Nat) => n * (l - i))
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_mulStep
      (poly.linRead 0 i 1 (l - i) l
        (lgGapD l i (Nat.le_trans (Nat.le_of_lt hi) hal)))
      acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsm
  exact poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc (k + 1), ground.posOfSucc i⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + 1 + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc (k + 1), ground.posOfSucc i⟩,
         ground.BPair.ofNat 1])
      (fun (n2 k : Nat) => n2 * (l - i + 1 + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead (k + 1) i 1 (l - i + 1 + k) l
          (riseGap1u l i k (Nat.le_trans (Nat.le_of_lt hi) hal)))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hlg

/-- The `C` dimension numerator in flat form. -/
private theorem dimNumC_flat (W : List Nat) (l : Nat) :
    dimNumC W l
      = (places.pairsOf W.length).foldl (fun acc p =>
          acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
            + (p.2 - p.1))) 1
        * (places.pairsOf W.length).foldl (fun acc p =>
            acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
              + (2 * l - p.1 - p.2))) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (ground.getAt 0 W i + (l - i))) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (ground.getAt 0 W i + (l - i + 1 + k))) 1) 1 := rfl

/-- The `C` dimension denominator in flat form. -/
private theorem dimDenC_flat (W : List Nat) (l : Nat) :
    dimDenC W l
      = (places.pairsOf W.length).foldl (fun acc p =>
          acc * (p.2 - p.1)) 1
        * (places.pairsOf W.length).foldl (fun acc p =>
            acc * (2 * l - p.1 - p.2)) 1
        * (List.range W.length).foldl (fun acc i => acc * (l - i)) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (W.length - i + k)) 1) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (l - i + 1 + k)) 1) 1 := rfl

/-- The `C` pair's cross-multiplied identity at a cleared rank. -/
private theorem crossC (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    numValC W l * dimDenC W l = denValC W l * dimNumC W l := by
  show ((List.range W.length).foldl (fun acc i =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
        acc2 * (l - i + 1 + (l - W.length) + k)) acc)
    ((List.range W.length).foldl (fun acc i =>
        (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
          acc2 * (l - i + k)) acc)
      ((List.range W.length).foldl (fun acc i =>
          acc * (ground.getAt 0 W i + (l - i)))
        ((places.pairsOf W.length).foldl (fun acc p =>
            acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
              + (2 * l - p.1 - p.2)))
          ((places.pairsOf W.length).foldl (fun acc p =>
              acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
                + (p.2 - p.1))) 1))))) * dimDenC W l
    = ((List.range W.length).foldl (fun acc i =>
        (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
          acc2 * (l - i + 1 + k)) acc)
      ((List.range W.length).foldl (fun acc i => acc * (l - i))
        ((places.pairsOf W.length).foldl (fun acc p =>
            acc * (2 * l - p.1 - p.2))
          ((places.pairsOf W.length).foldl (fun acc p =>
              acc * (p.2 - p.1)) 1
            * (List.range W.length).foldl (fun acc i =>
                acc * (List.range (ground.getAt 0 W i)).foldl
                  (fun acc2 k => acc2 * (W.length - i + k)) 1) 1))))
      * dimNumC W l
  rw [dimNumC_flat W l, dimDenC_flat W l,
    foldlFam (fun p : Nat × Nat => ground.getAt 0 W p.1
      - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => p.2 - p.1)
      (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => ground.getAt 0 W p.1
      + ground.getAt 0 W p.2 + (2 * l - p.1 - p.2))
      (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => 2 * l - p.1 - p.2)
      (places.pairsOf W.length),
    foldlFam (fun i => ground.getAt 0 W i + (l - i))
      (List.range W.length),
    foldlFam (fun i => l - i) (List.range W.length),
    foldlFam (fun i => (List.range (ground.getAt 0 W i)).foldl
      (fun acc2 k => acc2 * (W.length - i + k)) 1) (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1)
      (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (ground.getAt 0 W i + (l - i + 1 + k))) 1)
      (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (W.length - i + k)) 1) (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (l - i + 1 + k)) 1) (List.range W.length),
    ground.foldlProd (fun p : Nat × Nat => ground.getAt 0 W p.1
      + ground.getAt 0 W p.2 + (2 * l - p.1 - p.2))
      (places.pairsOf W.length),
    ground.foldlProd (fun i => ground.getAt 0 W i + (l - i))
      (List.range W.length),
    ground.foldlProd (fun p : Nat × Nat => 2 * l - p.1 - p.2)
      (places.pairsOf W.length),
    ground.foldlProd (fun i => l - i) (List.range W.length),
    ground.foldl_nest (fun i k => l - i + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.foldl_nest (fun i k => l - i + 1 + (l - W.length) + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.foldl_nest (fun i k => l - i + 1 + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i) (l - i)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => l - i + 1 + (l - W.length) + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i + 1 + (l - W.length)) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i)
        (l - i + 1 + (l - W.length))),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i + 1 + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i + 1) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i) (l - i + 1)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (ground.getAt 0 W i)).foldl
        (fun acc2 k => acc2 * (W.length - i + k)) 1)
      (fun i => ground.rise (W.length - i) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => foldRise (fun k => W.length - i + k) (W.length - i)
        (ground.getAt 0 W i) (fun _ => rfl)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1)
      (fun i => ground.rise (ground.getAt 0 W i + (W.length - i))
        (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise
        (fun k => ground.getAt 0 W i + (W.length - i + k))
        (ground.getAt 0 W i + (W.length - i)) (l - W.length)
        (fun k => (Nat.add_assoc (ground.getAt 0 W i)
          (W.length - i) k).symm)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (ground.getAt 0 W i + (l - i + 1 + k))) 1)
      (fun i => ground.rise (ground.getAt 0 W i + (l - i + 1)) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise
        (fun k => ground.getAt 0 W i + (l - i + 1 + k))
        (ground.getAt 0 W i + (l - i + 1)) (l - W.length)
        (fun k => (Nat.add_assoc (ground.getAt 0 W i)
          (l - i + 1) k).symm)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (W.length - i + k)) 1)
      (fun i => ground.rise (W.length - i) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise (fun k => W.length - i + k) (W.length - i)
        (l - W.length) (fun _ => rfl)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (l - i + 1 + k)) 1)
      (fun i => ground.rise (l - i + 1) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise (fun k => l - i + 1 + k) (l - i + 1)
        (l - W.length) (fun _ => rfl))]
  rw [numShuffle
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        + ground.getAt 0 W p.2 + (2 * l - p.1 - p.2))
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.getAt 0 W i + (l - i))
        (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i =>
        ground.rise (l - i + 1 + (l - W.length)) (ground.getAt 0 W i))
        (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => p.2 - p.1)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => 2 * l - p.1 - p.2)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => l - i) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (W.length - i)
        (l - W.length)) (List.range W.length))
      (ground.famFold Nat.mul 1
        (fun i => ground.rise (l - i + 1) (l - W.length))
        (List.range W.length)),
    denShuffle
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        + ground.getAt 0 W p.2 + (2 * l - p.1 - p.2))
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.getAt 0 W i + (l - i))
        (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => p.2 - p.1)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (W.length - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => 2 * l - p.1 - p.2)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => l - i) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i + 1)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (ground.getAt 0 W i
        + (W.length - i)) (l - W.length)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (ground.getAt 0 W i
        + (l - i + 1)) (l - W.length)) (List.range W.length))]
  exact congrArg _ (famFold_quad
    (fun i => ground.rise (l - i) (ground.getAt 0 W i))
    (fun i => ground.rise (l - i + 1 + (l - W.length)) (ground.getAt 0 W i))
    (fun i => ground.rise (W.length - i) (l - W.length))
    (fun i => ground.rise (l - i + 1) (l - W.length))
    (fun i => ground.rise (W.length - i) (ground.getAt 0 W i))
    (fun i => ground.rise (l - i + 1) (ground.getAt 0 W i))
    (fun i => ground.rise (ground.getAt 0 W i + (W.length - i)) (l - W.length))
    (fun i => ground.rise (ground.getAt 0 W i + (l - i + 1)) (l - W.length))
    W.length (fun i hi => by
      rw [← ground.subJoin (Nat.le_of_lt hi) hal,
        Nat.add_comm (l - W.length) (W.length - i),
        Nat.add_comm (ground.getAt 0 W i) (W.length - i),
        Nat.add_comm (ground.getAt 0 W i)
          (W.length - i + (l - W.length) + 1)]
      exact quadKey (W.length - i) (W.length - i + (l - W.length) + 1)
        (l - W.length) (ground.getAt 0 W i)))

/-- `lem:serstable`(i)'s dimension polynomial pair at the `C`
series. -/
theorem dimPolyC_eval : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    (poly.eval (dimPolyNumC W) (ground.BPair.ofNat l)
        * ground.BPair.ofNat (dimDenC W l)).oneValue
      (poly.eval (dimPolyDenC W) (ground.BPair.ofNat l)
        * ground.BPair.ofNat (dimNumC W l)) := by
  intro W l _ hl
  have hal : W.length ≤ l :=
    Nat.le_trans (Nat.le_add_right W.length 2) hl
  refine ground.BPair.oneValue_trans
    (ground.BPair.mul_congr (numReadC W l hal)
      (ground.BPair.oneValue_refl (ground.BPair.ofNat (dimDenC W l)))) ?_
  refine ground.BPair.oneValue_trans
    (ground.BPair.oneValue_symm
      (ground.BPair.ofNat_mul (numValC W l) (dimDenC W l))) ?_
  rw [crossC W l hal]
  refine ground.BPair.oneValue_trans
    (ground.BPair.ofNat_mul (denValC W l) (dimNumC W l)) ?_
  exact ground.BPair.mul_congr
    (ground.BPair.oneValue_symm (denReadC W l hal))
    (ground.BPair.oneValue_refl (ground.BPair.ofNat (dimNumC W l)))

/-- The `D` numerator polynomial's value at a rank. -/
private def numValD (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let dif := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2 + (p.2 - p.1))) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
      + (2 * l - 2 - p.1 - p.2))) dif
  let t1 := (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i + k)) acc) sm
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i - 1 + (l - a) + k)) acc) t1

/-- The `D` denominator polynomial's value at a rank. -/
private def denValD (W : List Nat) (l : Nat) : Nat :=
  let a := W.length
  let base := (places.pairsOf a).foldl (fun acc p => acc * (p.2 - p.1)) 1
    * (List.range a).foldl (fun acc i =>
        acc * (List.range (ground.getAt 0 W i)).foldl
          (fun acc2 k => acc2 * (a - i + k)) 1) 1
  let sm := (places.pairsOf a).foldl (fun acc p =>
    acc * (2 * l - 2 - p.1 - p.2)) base
  (List.range a).foldl (fun acc i =>
    (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
      acc2 * (l - i - 1 + k)) acc) sm

/-- The `D` numerator polynomial's evaluation at a cleared rank. -/
private theorem numReadD (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    (poly.eval (dimPolyNumD W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (numValD W l)) := by
  have hbase := poly.constRead ((places.pairsOf W.length).foldl (fun acc p =>
    acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
      + (p.2 - p.1))) 1) l
  have hsm := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (p : Nat × Nat) => poly.mul acc
      [⟨ground.posOfSucc (ground.getAt 0 W p.1 + ground.getAt 0 W p.2),
        ground.posOfSucc (2 + p.1 + p.2)⟩,
       ground.BPair.ofNat 2])
    (fun (n : Nat) (p : Nat × Nat) => n *
      (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
        + (2 * l - 2 - p.1 - p.2)))
    (fun p => p.1 < p.2 ∧ p.2 < W.length)
    (fun acc n p hp hacc => poly.eval_mulStep
      (poly.linRead (ground.getAt 0 W p.1 + ground.getAt 0 W p.2)
        (2 + p.1 + p.2) 2
        (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
          + (2 * l - 2 - p.1 - p.2)) l
        (smGapN (ground.getAt 0 W p.1 + ground.getAt 0 W p.2) l
          p.1 p.2 2 (pairBound2 l p.1 p.2 hp.1
            (Nat.le_trans hp.2 hal))))
      acc n hacc)
    (places.pairsOf W.length)
    (fun p hp => places.pairs_mem W.length p
      (ground.countOf_pos_of_mem hp))
    _ _ hbase
  have ht1 := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc i⟩,
         ground.BPair.ofNat 1])
      (fun (n2 k : Nat) => n2 * (l - i + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k i 1 (l - i + k) l
          (riseGap1 l i k (Nat.le_trans (Nat.le_of_lt hi) hal)))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsm
  exact poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc (i + W.length + 1)⟩,
         ground.BPair.ofNat 2]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i - 1 + (l - W.length) + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc (i + W.length + 1)⟩,
         ground.BPair.ofNat 2])
      (fun (n2 k : Nat) => n2 * (l - i - 1 + (l - W.length) + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k (i + W.length + 1) 2
          (l - i - 1 + (l - W.length) + k) l
          (riseGap2D l W.length i k (Nat.le_trans hi hal) hal))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ ht1

/-- The `D` denominator polynomial's evaluation at a cleared rank. -/
private theorem denReadD (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    (poly.eval (dimPolyDenD W) (ground.BPair.ofNat l)).oneValue
      (ground.BPair.ofNat (denValD W l)) := by
  have hbase := poly.constRead
    ((places.pairsOf W.length).foldl (fun acc p => acc * (p.2 - p.1)) 1
      * (List.range W.length).foldl (fun acc i =>
          acc * (List.range (ground.getAt 0 W i)).foldl
            (fun acc2 k => acc2 * (W.length - i + k)) 1) 1) l
  have hsm := poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (p : Nat × Nat) => poly.mul acc
      [⟨ground.posOfSucc 0, ground.posOfSucc (2 + p.1 + p.2)⟩,
       ground.BPair.ofNat 2])
    (fun (n : Nat) (p : Nat × Nat) => n * (2 * l - 2 - p.1 - p.2))
    (fun p => p.1 < p.2 ∧ p.2 < W.length)
    (fun acc n p hp hacc => poly.eval_mulStep
      (poly.linRead 0 (2 + p.1 + p.2) 2 (2 * l - 2 - p.1 - p.2) l
        (smGapD l p.1 p.2 2 (pairBound2 l p.1 p.2 hp.1
          (Nat.le_trans hp.2 hal))))
      acc n hacc)
    (places.pairsOf W.length)
    (fun p hp => places.pairs_mem W.length p
      (ground.countOf_pos_of_mem hp))
    _ _ hbase
  exact poly.eval_fold (ground.BPair.ofNat l)
    (fun (acc : poly.Poly) (i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc (i + 1)⟩,
         ground.BPair.ofNat 1]) acc)
    (fun (n i : Nat) =>
      (List.range (ground.getAt 0 W i)).foldl (fun n2 k =>
        n2 * (l - i - 1 + k)) n)
    (fun i => i < W.length)
    (fun acc n i hi hacc => poly.eval_fold (ground.BPair.ofNat l)
      (fun (acc2 : poly.Poly) (k : Nat) => poly.mul acc2
        [⟨ground.posOfSucc k, ground.posOfSucc (i + 1)⟩,
         ground.BPair.ofNat 1])
      (fun (n2 k : Nat) => n2 * (l - i - 1 + k))
      (fun _ => True)
      (fun acc2 n2 k _ h2 => poly.eval_mulStep
        (poly.linRead k (i + 1) 1 (l - i - 1 + k) l
          (riseGap1D l i k (Nat.le_trans hi hal)))
        acc2 n2 h2)
      (List.range (ground.getAt 0 W i)) (fun _ _ => trivial) acc n hacc)
    (List.range W.length)
    (fun x hx => ground.ltOfMemRange hx) _ _ hsm

/-- The `D` dimension numerator in flat form. -/
private theorem dimNumD_flat (W : List Nat) (l : Nat) :
    dimNumD W l
      = (places.pairsOf W.length).foldl (fun acc p =>
          acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
            + (p.2 - p.1))) 1
        * (places.pairsOf W.length).foldl (fun acc p =>
            acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
              + (2 * l - 2 - p.1 - p.2))) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (ground.getAt 0 W i + (l - i - 1 + k))) 1) 1 := rfl

/-- The `D` dimension denominator in flat form. -/
private theorem dimDenD_flat (W : List Nat) (l : Nat) :
    dimDenD W l
      = (places.pairsOf W.length).foldl (fun acc p =>
          acc * (p.2 - p.1)) 1
        * (places.pairsOf W.length).foldl (fun acc p =>
            acc * (2 * l - 2 - p.1 - p.2)) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (W.length - i + k)) 1) 1
        * (List.range W.length).foldl (fun acc i =>
            acc * (List.range (l - W.length)).foldl (fun acc2 k =>
              acc2 * (l - i - 1 + k)) 1) 1 := rfl

/-- The `D` pair's cross-multiplied identity at a cleared rank. -/
private theorem crossD (W : List Nat) (l : Nat) (hal : W.length ≤ l) :
    numValD W l * dimDenD W l = denValD W l * dimNumD W l := by
  show ((List.range W.length).foldl (fun acc i =>
      (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
        acc2 * (l - i - 1 + (l - W.length) + k)) acc)
    ((List.range W.length).foldl (fun acc i =>
        (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
          acc2 * (l - i + k)) acc)
      ((places.pairsOf W.length).foldl (fun acc p =>
          acc * (ground.getAt 0 W p.1 + ground.getAt 0 W p.2
            + (2 * l - 2 - p.1 - p.2)))
        ((places.pairsOf W.length).foldl (fun acc p =>
            acc * (ground.getAt 0 W p.1 - ground.getAt 0 W p.2
              + (p.2 - p.1))) 1)))) * dimDenD W l
    = ((List.range W.length).foldl (fun acc i =>
        (List.range (ground.getAt 0 W i)).foldl (fun acc2 k =>
          acc2 * (l - i - 1 + k)) acc)
      ((places.pairsOf W.length).foldl (fun acc p =>
          acc * (2 * l - 2 - p.1 - p.2))
        ((places.pairsOf W.length).foldl (fun acc p =>
            acc * (p.2 - p.1)) 1
          * (List.range W.length).foldl (fun acc i =>
              acc * (List.range (ground.getAt 0 W i)).foldl
                (fun acc2 k => acc2 * (W.length - i + k)) 1) 1)))
      * dimNumD W l
  rw [dimNumD_flat W l, dimDenD_flat W l,
    foldlFam (fun p : Nat × Nat => ground.getAt 0 W p.1
      - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => p.2 - p.1)
      (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => ground.getAt 0 W p.1
      + ground.getAt 0 W p.2 + (2 * l - 2 - p.1 - p.2))
      (places.pairsOf W.length),
    foldlFam (fun p : Nat × Nat => 2 * l - 2 - p.1 - p.2)
      (places.pairsOf W.length),
    foldlFam (fun i => (List.range (ground.getAt 0 W i)).foldl
      (fun acc2 k => acc2 * (W.length - i + k)) 1) (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1)
      (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (ground.getAt 0 W i + (l - i - 1 + k))) 1)
      (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (W.length - i + k)) 1) (List.range W.length),
    foldlFam (fun i => (List.range (l - W.length)).foldl
      (fun acc2 k => acc2 * (l - i - 1 + k)) 1) (List.range W.length),
    ground.foldlProd (fun p : Nat × Nat => ground.getAt 0 W p.1
      + ground.getAt 0 W p.2 + (2 * l - 2 - p.1 - p.2))
      (places.pairsOf W.length),
    ground.foldlProd (fun p : Nat × Nat => 2 * l - 2 - p.1 - p.2)
      (places.pairsOf W.length),
    ground.foldl_nest (fun i k => l - i + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.foldl_nest (fun i k => l - i - 1 + (l - W.length) + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.foldl_nest (fun i k => l - i - 1 + k)
      (fun i => List.range (ground.getAt 0 W i)) (List.range W.length),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i) (l - i)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1
        (fun k => l - i - 1 + (l - W.length) + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i - 1 + (l - W.length)) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i)
        (l - i - 1 + (l - W.length))),
    ground.famFold_congr_members Nat.mul 1
      (fun i => ground.famFold Nat.mul 1 (fun k => l - i - 1 + k)
        (List.range (ground.getAt 0 W i)))
      (fun i => ground.rise (l - i - 1) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => riseFam (ground.getAt 0 W i) (l - i - 1)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (ground.getAt 0 W i)).foldl
        (fun acc2 k => acc2 * (W.length - i + k)) 1)
      (fun i => ground.rise (W.length - i) (ground.getAt 0 W i))
      (List.range W.length)
      (fun i _ => foldRise (fun k => W.length - i + k) (W.length - i)
        (ground.getAt 0 W i) (fun _ => rfl)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (ground.getAt 0 W i + (W.length - i + k))) 1)
      (fun i => ground.rise (ground.getAt 0 W i + (W.length - i))
        (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise
        (fun k => ground.getAt 0 W i + (W.length - i + k))
        (ground.getAt 0 W i + (W.length - i)) (l - W.length)
        (fun k => (Nat.add_assoc (ground.getAt 0 W i)
          (W.length - i) k).symm)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (ground.getAt 0 W i + (l - i - 1 + k))) 1)
      (fun i => ground.rise (ground.getAt 0 W i + (l - i - 1)) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise
        (fun k => ground.getAt 0 W i + (l - i - 1 + k))
        (ground.getAt 0 W i + (l - i - 1)) (l - W.length)
        (fun k => (Nat.add_assoc (ground.getAt 0 W i)
          (l - i - 1) k).symm)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (W.length - i + k)) 1)
      (fun i => ground.rise (W.length - i) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise (fun k => W.length - i + k) (W.length - i)
        (l - W.length) (fun _ => rfl)),
    ground.famFold_congr_members Nat.mul 1
      (fun i => (List.range (l - W.length)).foldl
        (fun acc2 k => acc2 * (l - i - 1 + k)) 1)
      (fun i => ground.rise (l - i - 1) (l - W.length))
      (List.range W.length)
      (fun i _ => foldRise (fun k => l - i - 1 + k) (l - i - 1)
        (l - W.length) (fun _ => rfl))]
  rw [numShuffleD
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        + ground.getAt 0 W p.2 + (2 * l - 2 - p.1 - p.2))
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i =>
        ground.rise (l - i - 1 + (l - W.length)) (ground.getAt 0 W i))
        (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => p.2 - p.1)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat =>
        2 * l - 2 - p.1 - p.2) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (W.length - i)
        (l - W.length)) (List.range W.length))
      (ground.famFold Nat.mul 1
        (fun i => ground.rise (l - i - 1) (l - W.length))
        (List.range W.length)),
    denShuffleD
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        - ground.getAt 0 W p.2 + (p.2 - p.1)) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => ground.getAt 0 W p.1
        + ground.getAt 0 W p.2 + (2 * l - 2 - p.1 - p.2))
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat => p.2 - p.1)
        (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (W.length - i)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun p : Nat × Nat =>
        2 * l - 2 - p.1 - p.2) (places.pairsOf W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (l - i - 1)
        (ground.getAt 0 W i)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (ground.getAt 0 W i
        + (W.length - i)) (l - W.length)) (List.range W.length))
      (ground.famFold Nat.mul 1 (fun i => ground.rise (ground.getAt 0 W i
        + (l - i - 1)) (l - W.length)) (List.range W.length))]
  exact congrArg _ (famFold_quad
    (fun i => ground.rise (l - i) (ground.getAt 0 W i))
    (fun i => ground.rise (l - i - 1 + (l - W.length)) (ground.getAt 0 W i))
    (fun i => ground.rise (W.length - i) (l - W.length))
    (fun i => ground.rise (l - i - 1) (l - W.length))
    (fun i => ground.rise (W.length - i) (ground.getAt 0 W i))
    (fun i => ground.rise (l - i - 1) (ground.getAt 0 W i))
    (fun i => ground.rise (ground.getAt 0 W i + (W.length - i)) (l - W.length))
    (fun i => ground.rise (ground.getAt 0 W i + (l - i - 1)) (l - W.length))
    W.length (fun i hi => by
      rw [← ground.subJoin (Nat.le_of_lt hi) hal,
        Nat.add_comm (l - W.length) (W.length - i),
        Nat.add_comm (ground.getAt 0 W i) (W.length - i),
        Nat.add_comm (ground.getAt 0 W i)
          (W.length - i + (l - W.length) - 1)]
      exact quadKey (W.length - i) (W.length - i + (l - W.length) - 1)
        (l - W.length) (ground.getAt 0 W i)))

/-- `lem:serstable`(i)'s dimension polynomial pair at the `D`
series. -/
theorem dimPolyD_eval : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    (poly.eval (dimPolyNumD W) (ground.BPair.ofNat l)
        * ground.BPair.ofNat (dimDenD W l)).oneValue
      (poly.eval (dimPolyDenD W) (ground.BPair.ofNat l)
        * ground.BPair.ofNat (dimNumD W l)) := by
  intro W l _ hl
  have hal : W.length ≤ l :=
    Nat.le_trans (Nat.le_add_right W.length 2) hl
  refine ground.BPair.oneValue_trans
    (ground.BPair.mul_congr (numReadD W l hal)
      (ground.BPair.oneValue_refl (ground.BPair.ofNat (dimDenD W l)))) ?_
  refine ground.BPair.oneValue_trans
    (ground.BPair.oneValue_symm
      (ground.BPair.ofNat_mul (numValD W l) (dimDenD W l))) ?_
  rw [crossD W l hal]
  refine ground.BPair.oneValue_trans
    (ground.BPair.ofNat_mul (denValD W l) (dimNumD W l)) ?_
  exact ground.BPair.mul_congr
    (ground.BPair.oneValue_symm (denReadD W l hal))
    (ground.BPair.oneValue_refl (ground.BPair.ofNat (dimNumD W l)))

/-! ## The pairing tier: the gap as the form's own read

The clause's pairing reads are the standing publics — Elim's keyed
row pairing, its scale and unit passes, its joined-operand split and
its zipped fold's split, and Assembly's Cartan row count, diagonal
read and simple fold pairing — so that `lem:serstable`(i)'s gap
clause closes at one spelling of each. -/

private theorem zipLenR {α β γ : Type} (g : α → β → γ) :
    ∀ (a : List α) (b : List β), (List.zipWith g a b).length ≤ b.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | _ :: s, _ :: t => Nat.succ_le_succ (zipLenR g s t)

/-- The zipped fold's read at a stated weight list: the pairing
collects the coefficients against the weights. -/
private theorem zipSumRead (G : List BPair) :
    ∀ (f : List Nat) (rows : List (List BPair)) (ws : List Nat),
    rows.length = ws.length →
    (∀ l, l < rows.length →
      (elim.dotP (ground.getAt [] rows l) G).oneValue
        (BPair.ofNat (ground.getAt 0 ws l))) →
    (BPair.sum (List.zipWith
      (fun c row => BPair.ofNat c * elim.dotP row G) f rows)).oneValue
      (BPair.ofNat (ground.dotNat f ws))
  | [], _, _, _, _ => BPair.oneValue_refl _
  | _ :: _, [], [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, _ :: _, [], hl, _ => Nat.noConfusion hl
  | c :: f, row :: rows, w :: ws, hl, h => by
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat c))
          (h 0 (Nat.succ_pos _)))
        (zipSumRead G f rows ws (Nat.succ.inj hl)
          (fun l hl' => h (l + 1) (Nat.succ_lt_succ hl')))) ?_
    exact BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.ofNat_add (c * w) (ground.dotNat f ws))
        (BPair.add_congr (BPair.ofNat_mul c w) (BPair.oneValue_refl _)))

/-- `lem:serstable`(i)'s gap clause: the form's pairing of a
positive member's coroot vector against a coroot list reads the
concrete gap at the fundamentals' scale. -/
theorem gapAt_dotB : ∀ (t : gentable.Table) (F : sertables.FundData),
    sertables.fundShape t F → sertables.gramRead t F →
    ∀ j, j < t.posFolds.length → ∀ v : List Nat, v.length = t.rank →
    (sertables.dotB F (sertables.posCorootV t j)
        (v.map ground.BPair.ofNat)).oneValue
      (ground.BPair.ofNat (F.scale * gapAt t v j)) := by
  intro t F hshape hgram j _ v hv
  have hyl : (v.map BPair.ofNat).length = t.rank := by
    rw [ground.length_map, hv]
  have hG : (elim.matVec F.gram (v.map BPair.ofNat)).length = t.rank :=
    (elim.matVec_length F.gram _).trans hshape.1
  have hcl : t.cartan.length = t.rank := assembly.cartanLen t F hgram
  have hEnt : ∀ i, ground.getAt 0
      ((List.range t.cartan.length).map (fun l =>
        F.scale * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) l)) i
      = F.scale
        * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) i := by
    intro i
    by_cases hi : i < t.cartan.length
    · rw [ground.getAt_map 0 0 _ (List.range t.cartan.length) i
        (by rw [ground.length_range]; exact hi),
        ground.getAt_range t.cartan.length i hi]
    · rw [ground.getAt_over 0 _ i
        (by rw [ground.length_mapRange]
            exact Nat.le_of_not_lt hi),
        ground.getAt_over 0 (List.zipWith Nat.mul t.lenNums v) i
          (Nat.le_trans (Nat.le_trans (zipLenR Nat.mul t.lenNums v)
            (Nat.le_of_eq (hv.trans hcl.symm))) (Nat.le_of_not_lt hi)),
        Nat.mul_zero]
  have hws : ∀ l, l < t.cartan.length →
      (elim.dotP (getAt [] t.cartan l)
          (elim.matVec F.gram (v.map BPair.ofNat))).oneValue
        (BPair.ofNat (ground.getAt 0
          ((List.range t.cartan.length).map (fun l' =>
            F.scale
              * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) l')) l)) := by
    intro l hlr
    rw [hEnt l]
    refine BPair.oneValue_trans
      (assembly.diagRow t F hshape hgram (v.map BPair.ofNat) hyl l hlr) ?_
    rw [ground.getAt_map 0 BPair.unit BPair.ofNat v l
      (by rw [hv, ← hcl]; exact hlr)]
    refine BPair.oneValue_symm (BPair.oneValue_trans ?_
      (BPair.ofNat_mul (F.scale * ground.getAt 0 t.lenNums l)
        (ground.getAt 0 v l)))
    refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
    by_cases hll : l < t.lenNums.length
    · rw [ground.getAt_zipWith 0 0 0 Nat.mul t.lenNums v l hll
        (by rw [hv, ← hcl]; exact hlr)]
      exact (ground.mulAssoc F.scale (ground.getAt 0 t.lenNums l)
        (ground.getAt 0 v l)).symm
    · rw [ground.getAt_over 0 (List.zipWith Nat.mul t.lenNums v) l
        (Nat.le_trans (ground.length_zipWith_le Nat.mul t.lenNums v)
          (Nat.le_of_not_lt hll)),
        ground.getAt_over 0 t.lenNums l (Nat.le_of_not_lt hll),
        Nat.mul_zero]
      exact (Nat.zero_mul (ground.getAt 0 v l)).symm
  have hnat : ground.dotNat (getAt [] t.posFolds j)
      ((List.range t.cartan.length).map (fun l =>
        F.scale * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) l))
      = F.scale * gapAt t v j := by
    show _ = F.scale * ground.dotNat (getAt [] t.posFolds j)
      (List.zipWith Nat.mul t.lenNums v)
    rw [dotIndex, dotIndex,
      ground.famFold_congr_range
        (fun i => ground.getAt 0 (getAt [] t.posFolds j) i
          * ground.getAt 0 ((List.range t.cartan.length).map (fun l =>
              F.scale
                * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) l)) i)
        (fun i => F.scale * (ground.getAt 0 (getAt [] t.posFolds j) i
          * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) i))
        (getAt [] t.posFolds j).length
        (fun i _ => by
          rw [hEnt i]
          exact ground.mulLeftComm _ F.scale _),
      ← ground.famFold_mul F.scale _ (List.range _)]
  rw [← hnat]
  refine BPair.oneValue_trans
    (elim.dotP_zipSum t.rank (elim.matVec F.gram (v.map BPair.ofNat)) hG
      (getAt [] t.posFolds j) t.cartan) ?_
  exact zipSumRead (elim.matVec F.gram (v.map BPair.ofNat))
    (getAt [] t.posFolds j) t.cartan
    ((List.range t.cartan.length).map (fun l =>
      F.scale * ground.getAt 0 (List.zipWith Nat.mul t.lenNums v) l))
    (ground.length_mapRange _ _).symm hws

/-! ## The row tier: the pairing at a key off the naturals

`lem:serstable`(ii)'s tie analysis reads the form against keys that
carry both sides — the contents' own coroot vectors, the withdrawn
folds — so the gap clause's Gram reduction is re-run at a key off
the naturals: the Cartan-transposed fold associates across the
Gram's defining read exactly as before, the weights the scaled
lengths at the key's own entries, and the naturals' restriction
sits only in `zipSumRead`'s ofNat-valued weights.  The positive
member's own square is that read at the member's coroot vector,
`con:gentable`'s cleared form fold `formNum` at the member's fold
against itself. -/

/-- The zipped fold's read at a weight family off the naturals: the
pairing collects the coefficients against the weights, `zipSumRead`
at a family the naturals do not carry. -/
private theorem zipSumReadB (G : List BPair) :
    ∀ (f : List Nat) (rows : List (List BPair)) (ws : List BPair),
    rows.length = ws.length →
    (∀ l, l < rows.length →
      (elim.dotP (ground.getAt [] rows l) G).oneValue
        (ground.getAt BPair.unit ws l)) →
    (BPair.sum (List.zipWith
      (fun c row => BPair.ofNat c * elim.dotP row G) f rows)).oneValue
      (BPair.sum (List.zipWith
        (fun c w => BPair.ofNat c * w) f ws))
  | [], _, _, _, _ => BPair.oneValue_refl _
  | _ :: _, [], [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, _ :: _, [], hl, _ => Nat.noConfusion hl
  | c :: f, row :: rows, w :: ws, hl, h => by
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat c))
          (h 0 (Nat.succ_pos _)))
        (zipSumReadB G f rows ws (Nat.succ.inj hl)
          (fun l hl' => h (l + 1) (Nat.succ_lt_succ hl'))))
      (BPair.oneValue_symm (BPair.sum_cons _ _))

/-- The gap clause's Gram reduction at a key off the naturals: the
form's pairing of a positive member's coroot vector against a
stated key of the rank's order reads the fold against the scaled
lengths at the key's own entries (`gapAt_dotB`'s route at an
arbitrary key list of the rank's order). -/
private theorem dotB_posCorootV (t : gentable.Table)
    (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (j : Nat) (x : List BPair) (hx : x.length = t.rank) :
    (sertables.dotB F (sertables.posCorootV t j) x).oneValue
      (BPair.sum (List.zipWith (fun c w => BPair.ofNat c * w)
        (ground.getAt [] t.posFolds j)
        ((List.range t.cartan.length).map (fun l =>
          BPair.ofNat (F.scale * ground.getAt 0 t.lenNums l)
            * ground.getAt BPair.unit x l)))) := by
  have hG : (elim.matVec F.gram x).length = t.rank :=
    (elim.matVec_length F.gram _).trans hshape.1
  have hws : ∀ l, l < t.cartan.length →
      (elim.dotP (ground.getAt [] t.cartan l)
          (elim.matVec F.gram x)).oneValue
        (ground.getAt BPair.unit ((List.range t.cartan.length).map
          (fun l' => BPair.ofNat (F.scale * ground.getAt 0 t.lenNums l')
            * ground.getAt BPair.unit x l')) l) := by
    intro l hlr
    rw [ground.getAt_map 0 BPair.unit _ (List.range t.cartan.length) l
        (by rw [ground.length_range]; exact hlr),
      ground.getAt_range t.cartan.length l hlr]
    exact assembly.diagRow t F hshape hgram x hx l hlr
  refine BPair.oneValue_trans
    (elim.dotP_zipSum t.rank (elim.matVec F.gram x) hG
      (ground.getAt [] t.posFolds j) t.cartan) ?_
  exact zipSumReadB (elim.matVec F.gram x)
    (ground.getAt [] t.posFolds j) t.cartan
    ((List.range t.cartan.length).map (fun l =>
      BPair.ofNat (F.scale * ground.getAt 0 t.lenNums l)
        * ground.getAt BPair.unit x l))
    (ground.length_mapRange _ _).symm hws

/-! ## The row tier: the member's keys and the letter fold

`lem:serstable`(ii) runs the row at the member ties
`ν_w + w(λ+ρ) = c+ρ` over the member's Weyl list at the `θ`
contents.  The member enters as a key — `memberV` the coroot
presentation carried onto the balance pairs, its `ρ`-raise the
shifted key `pnorm (vecAdd (memberV W l) (rhoV t))`, the padded
word's gaps each carrying one — and the row's value is the
`letterFold`: the identity's read at the target's own content joined
against one read per simple letter at the raised content, the raise
the key's coroot multiple of the letter's own root.  The tier runs
at an abstract member vector, `letterFoldAt` the fold there and the
leading member its instance.

The vacuum's evaluation closes the diagonal's odd fold.  At the
vacant target a letter's tie content is `memberRho_i α_i`, and a
multiple of a simple beyond one sits off every series' root list:
its square is the raise's own square against the letter's scaled
length while its `ρ`-dot is the raise once, so the square passes
the doubled dot exactly when the raise clears one — the `ρ`-length
read's cap refusing it — and a balance partner is refused by the
`ρ`-dot's own positivity.  So the fold reads one at each unit
coroot pair and nothing elsewhere: the member's vacant-key count. -/

/-- The leading family's member as a key, the coroot presentation
carried onto the balance pairs. -/
def memberV (W : List Nat) (l : Nat) : List ground.BPair :=
  (member W l).map ground.BPair.ofNat

/-- The letter fold at an abstract raised member
(`lem:serstable`(ii)): one read per simple letter at the raised
content, the raise the key's coroot multiple of the letter's own
root, the raise read off the raised member's own entry. -/
def letterFoldAt (t : gentable.Table) (ρv : List Nat)
    (nu0 : List ground.BPair) (L : List (List ground.BPair)) : Nat :=
  ground.famFold Nat.add 0 (fun i =>
    ground.countOf (poly.pnorm (elim.vecAdd nu0
      (elim.vecScale (ground.BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i)))) L)
    (List.range t.rank)

/-- The letter fold at the leading family's member
(`lem:serstable`(ii)), the abstract fold at the raised member. -/
def letterFold (t : gentable.Table) (W : List Nat) (l : Nat)
    (nu0 : List ground.BPair) (L : List (List ground.BPair)) : Nat :=
  letterFoldAt t (memberRho W l) nu0 L

/-- The letter fold's value under the θ list's characterization:
the fold at the count function. -/
def letterFoldVal (t : gentable.Table) (ρv : List Nat)
    (nu0 : List ground.BPair) : Nat :=
  ground.famFold Nat.add 0 (fun i =>
    row.thetaCount t (poly.pnorm (elim.vecAdd nu0
      (elim.vecScale (ground.BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i)))))
    (List.range t.rank)

/-- The letter fold reads its value function: under the θ content
list's characterization the fold is a function of the table, the
shifted-key reads and the moved content alone. -/
theorem letterFoldAt_val (t : gentable.Table) (ρv : List Nat)
    (nu0 : List ground.BPair) (L : List (List ground.BPair))
    (h : row.thetaFamRead t L) :
    letterFoldAt t ρv nu0 L = letterFoldVal t ρv nu0 :=
  ground.famFold_congr_all Nat.add 0 _ _
    (fun _ => row.countOf_theta t L h _) (List.range t.rank)

/-- The reflecting Cartan row's pairing: the row against the Gram's
action reads the scaled length at the key's own entry,
`assembly.dotB_simple` at the raw stored row (the simple's
position carries its one-key fold, so the positive member's
coroot vector reads the row entrywise). -/
private theorem dotB_row (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hsp : sertables.simplePosRead t F)
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (z : List BPair) (hz : z.length = t.rank) :
    (sertables.dotB F (ground.getAt [] t.cartan i) z).oneValue
      (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
        * ground.getAt BPair.unit z i) := by
  have hone : poly.oneValue
      (sertables.posCorootV t (ground.getAt 0 F.simplePos i))
      (ground.getAt [] t.cartan i) := by
    refine poly.oneValue_of_entries _ _
      ((sertables.posCorootV_length t _).trans hcl.symm) (fun j hj => ?_)
    have hjr : j < t.rank := by
      rw [sertables.posCorootV_length] at hj
      exact hj
    show (ground.getAt BPair.unit ((List.range t.rank).map
      (gentable.corootAt t (ground.getAt [] t.posFolds
        (ground.getAt 0 F.simplePos i)))) j).oneValue _
    rw [ground.getAt_map_range BPair.unit _ t.rank j, if_pos hjr,
      hsp i hi]
    exact gentable.corootAt_oneHot t i j hi
  exact BPair.oneValue_trans
    (sertables.dotB_congrL F _ _ z (poly.oneValue_symm hone))
    (assembly.dotB_simple t F hshape hgram hsp hi z hz)

/-- The raise's own growth: beyond the unit the raised content's
square passes its doubled `ρ`-dot. -/
private theorem sqGrow {c s : Nat} (hc : 2 ≤ c) (hs : 0 < s) :
    c * s + c * s < c * c * s * 2 := by
  obtain ⟨d, hd⟩ := Nat.le.dest hc
  have hcd : c = d + 2 := by
    rw [← hd, Nat.add_comm 2 d]
  subst hcd
  have hstep : (d + 2) * s < (d + 1) * (d + 2) * s + (d + 2) * s :=
    Nat.lt_add_of_pos_left
      (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos (d + 1))) hs)
  have hexp : (d + 2) * (d + 2) * s = (d + 1) * (d + 2) * s + (d + 2) * s := by
    rw [Nat.succ_mul (d + 1) (d + 2), ground.mulAddR]
  have hinner : (d + 2) * s < (d + 2) * (d + 2) * s := by
    rw [hexp]
    exact hstep
  have hpair : (d + 2) * s + (d + 2) * s
      < (d + 2) * (d + 2) * s + (d + 2) * (d + 2) * s :=
    Nat.add_lt_add hinner hinner
  rw [← Nat.mul_two ((d + 2) * (d + 2) * s)] at hpair
  exact hpair

/-- The four-fold natural product carried onto the balance pairs. -/
private theorem ofNat4 (a b c d : Nat) :
    (BPair.ofNat a * (BPair.ofNat b
      * (BPair.ofNat c * BPair.ofNat d))).oneValue
      (BPair.ofNat (a * (b * (c * d)))) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans (BPair.ofNat_mul a (b * (c * d)))
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.ofNat_mul b (c * d))
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.ofNat_mul c d)))))

/-- The raised content's square in the natural key's own shape. -/
private theorem sqShape (c s : Nat) : c * (s * (c * 2)) = c * c * s * 2 := by
  rw [← ground.mulAssoc s c 2, ← ground.mulAssoc c (s * c) 2,
    Nat.mul_comm s c, ← ground.mulAssoc c c s]

/-- The simple's coroot vector reads its stored Cartan row: the
keyed row at the stored row's own order is that row, so
`assembly.simpleRow`'s representative reading transports to the raw
spelling. -/
private theorem simpleRowOne (t : gentable.Table) (F : sertables.FundData)
    (hsp : sertables.simplePosRead t F) {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank) :
    poly.oneValue (sertables.posCorootV t (ground.getAt 0 F.simplePos i))
      (ground.getAt [] t.cartan i) := by
  have hrow : assembly.cartRowV t i = ground.getAt [] t.cartan i :=
    ground.range_map_getAt BPair.unit t.rank _ hcl
  refine poly.oneValue_trans
    (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
  rw [assembly.simpleRow t F hsp hi, hrow]
  exact poly.pnorm_oneValue _

/-- The letter's raised content at the vacant target: the `θ`
content list holds it once at the unit coroot pair and never
beyond.  The raise's `ρ`-dot is the raise against the letter's own
scaled length and its square that dot at the raise's double, so a
raise beyond one carries the square past the doubled dot — refused
by the `ρ`-length read — while the vacant content and the balance
partners are refused by the dot's own positivity. -/
private theorem vacContent (t : gentable.Table) (F : sertables.FundData)
    (L : List (List BPair))
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F) (hfam : row.thetaFamRead t L)
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (hdg : (ground.getAt BPair.unit (ground.getAt [] t.cartan i) i).oneValue
      (BPair.ofNat 2))
    (c : Nat) (hc : 1 ≤ c) :
    ground.countOf (poly.pnorm (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i))) L = if c = 1 then 1 else 0 := by
  have hXl : (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i)).length = t.rank :=
    (elim.length_vecScale _ _).trans hcl
  have hs : 0 < F.scale * ground.getAt 0 t.lenNums i :=
    Nat.mul_pos hshape.2.2.1
      (memberchar.lenNums_pos t F hshape hsp hrd hgram hi)
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hrhoi : ground.getAt BPair.unit (sertables.rhoV t) i = BPair.ofNat 1 :=
    ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi
  -- the raised content's ρ-dot
  have hdR : (sertables.dotB F (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i)) (sertables.rhoV t)).oneValue
      (BPair.ofNat (c * (F.scale * ground.getAt 0 t.lenNums i))) := by
    have h2 := dotB_row t F hshape hgram hsp hi hcl (sertables.rhoV t) hrl
    rw [hrhoi] at h2
    refine BPair.oneValue_trans
      (elim.dotP_scaleL (BPair.ofNat c) (ground.getAt [] t.cartan i)
        (elim.matVec F.gram (sertables.rhoV t))) ?_
    refine BPair.oneValue_trans (BPair.mul_congr
      (BPair.oneValue_refl (BPair.ofNat c))
      (BPair.oneValue_trans h2 (BPair.mul_ofNat_one _))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_mul c _)
  -- the raised content's square
  have hdS : (sertables.dotB F (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i))
      (elim.vecScale (BPair.ofNat c)
        (ground.getAt [] t.cartan i))).oneValue
      (BPair.ofNat (c * c * (F.scale * ground.getAt 0 t.lenNums i) * 2)) := by
    have h4 := dotB_row t F hshape hgram hsp hi hcl
      (elim.vecScale (BPair.ofNat c) (ground.getAt [] t.cartan i)) hXl
    rw [elim.getAt_vecScale (BPair.ofNat c) (ground.getAt [] t.cartan i) i
      (by rw [hcl]; exact hi)] at h4
    refine BPair.oneValue_trans
      (elim.dotP_scaleL (BPair.ofNat c) (ground.getAt [] t.cartan i)
        (elim.matVec F.gram (elim.vecScale (BPair.ofNat c)
          (ground.getAt [] t.cartan i)))) ?_
    refine BPair.oneValue_trans (BPair.mul_congr
      (BPair.oneValue_refl (BPair.ofNat c))
      (BPair.oneValue_trans h4 (BPair.mul_congr
        (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _) hdg)))) ?_
    refine BPair.oneValue_trans (ofNat4 c _ c 2) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat (sqShape c _))
  by_cases hc1 : c = 1
  · subst hc1
    rw [if_pos rfl]
    have hone : poly.oneValue (elim.vecScale (BPair.ofNat 1)
        (ground.getAt [] t.cartan i)) (ground.getAt [] t.cartan i) := by
      refine poly.oneValue_of_entries _ _ (hXl.trans hcl.symm) (fun k hk => ?_)
      have hkr : k < t.rank := by rw [hXl] at hk; exact hk
      rw [elim.getAt_vecScale (BPair.ofNat 1) (ground.getAt [] t.cartan i) k
        (by rw [hcl]; exact hkr)]
      exact BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.mul_ofNat_one _)
    have hpn : poly.pnorm (elim.vecScale (BPair.ofNat 1)
        (ground.getAt [] t.cartan i))
        = poly.pnorm (ground.getAt [] t.cartan i) :=
      poly.pnorm_congr _ _ (hXl.trans hcl.symm) hone
    have hpn2 : poly.pnorm (sertables.posCorootV t
        (ground.getAt 0 F.simplePos i))
        = poly.pnorm (ground.getAt [] t.cartan i) :=
      poly.pnorm_congr _ _
        ((sertables.posCorootV_length t _).trans hcl.symm)
        (simpleRowOne t F hsp hi hcl)
    rw [hpn, ← hpn2]
    exact (hfam.2.1 (ground.getAt 0 F.simplePos i)
      (assembly.simplePos_lt t F hshape hi)).1
  · rw [if_neg hc1]
    have hc2 : 2 ≤ c := Nat.lt_of_le_of_ne hc (fun h => hc1 h.symm)
    match Nat.eq_zero_or_pos (ground.countOf (poly.pnorm
        (elim.vecScale (BPair.ofNat c)
          (ground.getAt [] t.cartan i))) L) with
    | Or.inl h => exact h
    | Or.inr hpos =>
      exfalso
      have hmem := ground.mem_of_countOf_pos _ L hpos
      have hcsPos : 0 < c * (F.scale * ground.getAt 0 t.lenNums i) :=
        Nat.mul_pos (Nat.lt_of_lt_of_le (by decide +kernel) hc2) hs
      obtain ⟨k, hk⟩ := Nat.le.dest hcsPos
      have hcsk : c * (F.scale * ground.getAt 0 t.lenNums i) = k + 1 := by
        rw [← hk, Nat.add_comm]
      have hlt : BPair.unit < sertables.dotB F
          (elim.vecScale (BPair.ofNat c) (ground.getAt [] t.cartan i))
          (sertables.rhoV t) := by
        refine BPair.lt_congr (BPair.oneValue_refl BPair.unit)
          (BPair.oneValue_symm ?_) (ground.unitLtOfNat k)
        rw [← hcsk]
        exact hdR
      match hfam.2.2 _ hmem with
      | Or.inl he =>
        have hu : (sertables.dotB F (elim.vecScale (BPair.ofNat c)
            (ground.getAt [] t.cartan i)) (sertables.rhoV t)).oneValue
            BPair.unit := by
          refine BPair.oneValue_trans
            (sertables.dotB_congrL F _ _ (sertables.rhoV t)
              (poly.oneValue_symm (poly.pnorm_oneValue _))) ?_
          rw [he]
          exact elim.dotP_replL t.rank (elim.matVec F.gram (sertables.rhoV t))
        exact absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit) hu hlt)
          (by decide +kernel)
      | Or.inr ⟨j, hj1, hcase⟩ =>
        have hj : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj1
        match hcase with
        | Or.inl hpb =>
          have hXrho : (sertables.dotB F (elim.vecScale (BPair.ofNat c)
              (ground.getAt [] t.cartan i)) (sertables.rhoV t)).oneValue
              (sertables.dotB F (sertables.posCorootV t j)
                (sertables.rhoV t)) := by
            refine BPair.oneValue_trans
              (sertables.dotB_congrL F _ _ (sertables.rhoV t)
                (poly.oneValue_symm (poly.pnorm_oneValue _))) ?_
            rw [hpb]
            exact sertables.dotB_congrL F _ _ (sertables.rhoV t)
              (poly.pnorm_oneValue _)
          have hXsq : (sertables.dotB F (elim.vecScale (BPair.ofNat c)
              (ground.getAt [] t.cartan i))
              (elim.vecScale (BPair.ofNat c)
                (ground.getAt [] t.cartan i))).oneValue
              (sertables.dotB F (sertables.posCorootV t j)
                (sertables.posCorootV t j)) := by
            refine BPair.oneValue_trans
              (sertables.dotB_congrL F _ _ _
                (poly.oneValue_symm (poly.pnorm_oneValue _))) ?_
            refine BPair.oneValue_trans
              (sertables.dotB_congrR F _ _ _
                (poly.oneValue_symm (poly.pnorm_oneValue _))) ?_
            rw [hpb]
            refine BPair.oneValue_trans
              (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _)) ?_
            exact sertables.dotB_congrR F _ _ _ (poly.pnorm_oneValue _)
          refine Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (sqGrow hc2 hs)
            (ground.leB_ofNat_cancel (a := c * c
                * (F.scale * ground.getAt 0 t.lenNums i) * 2)
              (b := c * (F.scale * ground.getAt 0 t.lenNums i)
                + c * (F.scale * ground.getAt 0 t.lenNums i)) ?_))
          refine ground.leB_congr
            (BPair.oneValue_trans (BPair.oneValue_symm hXsq) hdS)
            (BPair.oneValue_trans
              (BPair.add_congr
                (BPair.oneValue_trans (BPair.oneValue_symm hXrho) hdR)
                (BPair.oneValue_trans (BPair.oneValue_symm hXrho) hdR))
              (BPair.oneValue_symm (BPair.ofNat_add _ _)))
            (hrho j hj).2.1
        | Or.inr hnb =>
          have hXrho : (sertables.dotB F (elim.vecScale (BPair.ofNat c)
              (ground.getAt [] t.cartan i)) (sertables.rhoV t)).oneValue
              (sertables.dotB F (sertables.posCorootV t j)
                (sertables.rhoV t)).swap := by
            refine BPair.oneValue_trans
              (sertables.dotB_congrL F _ _ (sertables.rhoV t)
                (poly.oneValue_symm (poly.pnorm_oneValue _))) ?_
            rw [hnb]
            refine BPair.oneValue_trans
              (sertables.dotB_congrL F _ _ (sertables.rhoV t)
                (poly.pnorm_oneValue _)) ?_
            exact BPair.oneValue_of_eq
              (elim.dotP_swap_left (sertables.posCorootV t j)
                (elim.matVec F.gram (sertables.rhoV t)))
          have hsw : BPair.unit < (sertables.dotB F
              (sertables.posCorootV t j) (sertables.rhoV t)).swap :=
            BPair.lt_congr (BPair.oneValue_refl BPair.unit) hXrho hlt
          have hjoin : BPair.unit < sertables.dotB F
              (sertables.posCorootV t j) (sertables.rhoV t)
              + (sertables.dotB F (sertables.posCorootV t j)
                (sertables.rhoV t)).swap :=
            ground.unitLtAdd (hrd j hj) (ground.leB_of_lt hsw)
          exact absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
            (ground.unitOfOne (BPair.oneValue_refl _)) hjoin) (by decide +kernel)

/-- The raised member's entry: the word's gap at its own successor. -/
private theorem memberRhoStep (W : List Nat) (l k : Nat) (hk : k < l) :
    ground.getAt 0 (memberRho W l) k
      = ground.getAt 0 (member W l) k + 1 := by
  show ground.getAt 0 ((member W l).map (· + 1)) k = _
  exact ground.getAt_map 0 0 (· + 1) (member W l) k
    (by rw [memberLen]; exact hk)

/-- The raised member's entry is occupied. -/
private theorem memberRhoPos (W : List Nat) (l k : Nat) (hk : k < l) :
    1 ≤ ground.getAt 0 (memberRho W l) k := by
  rw [memberRhoStep W l k hk]
  exact Nat.succ_le_succ (Nat.zero_le _)

/-- The leading member's key sits at the rank's order. -/
private theorem memberVLen (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) : (memberV W l).length = t.rank := by
  show ((member W l).map BPair.ofNat).length = t.rank
  rw [ground.length_map, memberLen, hrk]

/-- The raised member's unit-key count is the member's vacant-key
count: the raise is the entrywise successor, so a unit entry there
is a vacant entry here. -/
private theorem memberRhoCount (W : List Nat) (l : Nat) :
    ground.countOf 1 (memberRho W l) = ground.countOf 0 (member W l) := by
  show ground.countOf 1 ((member W l).map (· + 1)) = _
  rw [ground.countOf_map_famFold 1 (· + 1) (member W l),
    ground.countOf_fold 0 (member W l)]
  refine ground.famFold_congr_members Nat.add 0 _ _ (member W l)
    (fun x _ => ?_)
  by_cases h : (0 : Nat) = x
  · rw [if_pos h,
      if_pos (show (1 : Nat) = x + 1 from congrArg (fun z => z + 1) h)]
  · rw [if_neg h,
      if_neg (fun hb : (1 : Nat) = x + 1 => h (Nat.succ.inj hb))]

/-- `lem:serstable`(ii)'s diagonal evaluation at an abstract member,
series-uniform: at the vacant target the letter fold reads the
raised member's unit-key count, the member's own occupied coroot
support read back. -/
private theorem letterFold_vacuum (t : gentable.Table)
    (F : sertables.FundData) (L : List (List BPair))
    (ρv : List Nat) (hρl : ρv.length = t.rank)
    (hpos : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 ρv k)
    (hcl : ∀ i, i < t.rank →
      (ground.getAt [] t.cartan i).length = t.rank)
    (hdg : ∀ i, i < t.rank →
      (ground.getAt BPair.unit (ground.getAt [] t.cartan i) i).oneValue
        (BPair.ofNat 2))
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F) (hfam : row.thetaFamRead t L) :
    letterFoldAt t ρv (List.replicate t.rank BPair.unit) L
      = ground.countOf 1 ρv := by
  have hstep : ∀ i, i < t.rank →
      ground.countOf (poly.pnorm (elim.vecAdd
        (List.replicate t.rank BPair.unit)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
          (ground.getAt [] t.cartan i)))) L
        = if 1 = ground.getAt 0 ρv i then 1 else 0 := by
    intro i hi
    have hcli := hcl i hi
    have hXl : (elim.vecScale
        (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i)).length = t.rank :=
      (elim.length_vecScale _ _).trans hcli
    have hrepl : (List.replicate t.rank BPair.unit).length = t.rank :=
      ground.length_replicate BPair.unit t.rank
    have hsum : (elim.vecAdd (List.replicate t.rank BPair.unit)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
          (ground.getAt [] t.cartan i))).length = t.rank :=
      elim.length_vecAdd _ _ t.rank hrepl hXl
    have hred : poly.pnorm (elim.vecAdd
        (List.replicate t.rank BPair.unit)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
          (ground.getAt [] t.cartan i)))
        = poly.pnorm (elim.vecScale
            (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i)) :=
      poly.pnorm_congr _ _ (hsum.trans hXl.symm)
        (elim.vecAdd_null_left _ _ (hrepl.trans hXl.symm)
          (poly.unitTail_replicate t.rank))
    rw [hred, vacContent t F L hshape hgram hsp hrd hrho hfam hi hcli
      (hdg i hi) _ (hpos i hi)]
    by_cases hz : ground.getAt 0 ρv i = 1
    · rw [if_pos hz, if_pos hz.symm]
    · rw [if_neg hz, if_neg (fun hb => hz hb.symm)]
  show ground.famFold Nat.add 0 _ (List.range t.rank) = _
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun i => if 1 = ground.getAt 0 ρv i then 1 else 0)
    (List.range t.rank) (fun i hi => hstep i (ground.ltOfMem hi))) ?_
  rw [ground.countOf_fold 1 ρv]
  exact ground.famFold_getAt Nat.add 0
    (fun x => if 1 = x then 1 else 0) 0 ρv t.rank hρl

/-! The series' Cartan rows at the reflecting key: each row sits at
the rank's order and carries the coroot pair two on its own key. -/

/-- The `B` rows' own coroot pair, the stored Cartan row's
diagonal two. -/
theorem cartanBDiag (l i : Nat) (hi : i < l) :
    (ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanB l) i) i).oneValue
      (BPair.ofNat 2) := by
  unfold sertables.cartanB
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i i hi hi,
    if_pos (ground.eqBeqOf rfl)]
  exact BPair.oneValue_refl _

/-- The `C` rows' own coroot pair, the stored Cartan row's
diagonal two. -/
private theorem cartanCDiag (l i : Nat) (hi : i < l) :
    (ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanC l) i) i).oneValue
      (BPair.ofNat 2) := by
  unfold sertables.cartanC
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i i hi hi,
    if_pos (ground.eqBeqOf rfl)]
  exact BPair.oneValue_refl _

/-- The `D` rows' own coroot pair, the stored Cartan row's
diagonal two. -/
theorem cartanDDiag (l i : Nat) (hi : i < l) :
    (ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanD l) i) i).oneValue
      (BPair.ofNat 2) := by
  unfold sertables.cartanD
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i i hi hi,
    if_pos (ground.eqBeqOf rfl)]
  exact BPair.oneValue_refl _

/-- `lem:serstable`(ii)'s diagonal evaluation at the `B` series: at
the vacant target the letter fold reads the member's vacant-key
count (the diagonal's odd fold at the key's unit coroot pairs). -/
theorem letterFold_vac_B : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (L : List (List BPair)),
    sertables.fundShape (sertables.tableB l) F →
    sertables.gramRead (sertables.tableB l) F →
    sertables.simplePosRead (sertables.tableB l) F →
    sertables.rhoDotRead (sertables.tableB l) F →
    row.rhoLenRead (sertables.tableB l) F →
    row.thetaFamRead (sertables.tableB l) L →
    letterFold (sertables.tableB l) W l
        (List.replicate l ground.BPair.unit) L
      = ground.countOf 0 (member W l) := by
  intro W l F L hshape hgram hsp hrd hrho hfam
  exact Eq.trans (letterFold_vacuum (sertables.tableB l) F L
    (memberRho W l) (memberRhoLen W l)
    (fun k hk => memberRhoPos W l k hk)
    (fun i hi => ground.matOf_rowLength ([] : List BPair) l l _ i hi)
    (fun i hi => cartanBDiag l i hi)
    hshape hgram hsp hrd hrho hfam) (memberRhoCount W l)

/-- `lem:serstable`(ii)'s diagonal evaluation at the `C` series. -/
theorem letterFold_vac_C : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (L : List (List BPair)),
    sertables.fundShape (sertables.tableC l) F →
    sertables.gramRead (sertables.tableC l) F →
    sertables.simplePosRead (sertables.tableC l) F →
    sertables.rhoDotRead (sertables.tableC l) F →
    row.rhoLenRead (sertables.tableC l) F →
    row.thetaFamRead (sertables.tableC l) L →
    letterFold (sertables.tableC l) W l
        (List.replicate l ground.BPair.unit) L
      = ground.countOf 0 (member W l) := by
  intro W l F L hshape hgram hsp hrd hrho hfam
  exact Eq.trans (letterFold_vacuum (sertables.tableC l) F L
    (memberRho W l) (memberRhoLen W l)
    (fun k hk => memberRhoPos W l k hk)
    (fun i hi => ground.matOf_rowLength ([] : List BPair) l l _ i hi)
    (fun i hi => cartanCDiag l i hi)
    hshape hgram hsp hrd hrho hfam) (memberRhoCount W l)

/-- `lem:serstable`(ii)'s diagonal evaluation at the `D` series. -/
theorem letterFold_vac_D : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (L : List (List BPair)),
    sertables.fundShape (sertables.tableD l) F →
    sertables.gramRead (sertables.tableD l) F →
    sertables.simplePosRead (sertables.tableD l) F →
    sertables.rhoDotRead (sertables.tableD l) F →
    row.rhoLenRead (sertables.tableD l) F →
    row.thetaFamRead (sertables.tableD l) L →
    letterFold (sertables.tableD l) W l
        (List.replicate l ground.BPair.unit) L
      = ground.countOf 0 (member W l) := by
  intro W l F L hshape hgram hsp hrd hrho hfam
  exact Eq.trans (letterFold_vacuum (sertables.tableD l) F L
    (memberRho W l) (memberRhoLen W l)
    (fun k hk => memberRhoPos W l k hk)
    (fun i hi => ground.matOf_rowLength ([] : List BPair) l l _ i hi)
    (fun i hi => cartanDDiag l i hi)
    hshape hgram hsp hrd hrho hfam) (memberRhoCount W l)

/-! ## The row tier's tie walk: the target's own key

`lem:serstable`(ii)'s row runs at a target `c + ρ = κ + ν₀`, the
member's shifted key `κ` raised by the target's content `ν₀`.  A tie
`(v, s)` of the graded image list against a content `ν` of the `θ`
list reads `v` at `κ`'s own withdrawal of a natural simple fold (the
support read at `κ`), so the tie's content is `ν₀` joined to that
fold; the kept square reads the fold's own square at its doubled
pairing with `κ`; and the tie collects the square against the
target's shifted key, twice the fold's pairing there the two
contents' square gap.  The target's dominance puts every shifted
coroot pair at or beyond one, so the contents' cap prices the fold's
length-weighted height at two, and the residue walk closes: the
vacant fold is the identity's tie, a one-keyed fold reads the key's
own coroot multiple, and a two-keyed fold carries two coroot pairs
at two on distinct keys — refused at the simple's own row. -/

/-- The same read off a stated key: beyond that key the family
either reads nought or names a second occupied key. -/
private theorem findNZoff (c : List Nat) (i0 : Nat) : ∀ n : Nat,
    (∀ i, i < n → ¬ i = i0 → ground.getAt 0 c i = 0)
      ∨ ∃ i, i < n ∧ ¬ i = i0 ∧ ¬ ground.getAt 0 c i = 0
  | 0 => Or.inl (fun i hi _ => absurd hi (Nat.not_lt_zero i))
  | n + 1 => by
    match findNZoff c i0 n with
    | Or.inr ⟨i, hi, hne, h⟩ =>
      exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hne, h⟩
    | Or.inl hall =>
      by_cases hn : n = i0
      · refine Or.inl (fun i hi hne => ?_)
        match Nat.lt_or_ge i n with
        | Or.inl hin => exact hall i hin hne
        | Or.inr hin =>
          have hie : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hin
          exact absurd (hie.trans hn) hne
      · by_cases h : ground.getAt 0 c n = 0
        · refine Or.inl (fun i hi hne => ?_)
          match Nat.lt_or_ge i n with
          | Or.inl hin => exact hall i hin hne
          | Or.inr hin =>
            rw [Nat.le_antisymm (Nat.le_of_lt_succ hi) hin]
            exact h
        · exact Or.inr ⟨n, Nat.lt_succ_self n, hn, h⟩

/-- One key peels off a range fold: the fold reads the key's own
value joined to the fold of the family the key is cleared from. -/
private theorem foldPeel (h : Nat → Nat) (i : Nat) : ∀ n : Nat, i < n →
    ground.famFold Nat.add 0 h (List.range n)
      = h i + ground.famFold Nat.add 0
          (fun k => if k == i then 0 else h k) (List.range n)
  | 0, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, hi => by
    rw [ground.range_succ n, ground.famFold_snoc h (List.range n) n,
      ground.famFold_snoc _ (List.range n) n]
    match Nat.lt_or_ge i n with
    | Or.inl hin =>
      rw [foldPeel h i n hin,
        if_neg (fun hb : (n == i) = true =>
          Nat.lt_irrefl i (ground.beqEqOf hb ▸ hin)),
        Nat.add_assoc]
    | Or.inr hge =>
      have hie : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
      rw [hie, if_pos (ground.eqBeqOf rfl), Nat.add_zero,
        ground.famFold_congr_members Nat.add 0
          (fun k => if k == n then 0 else h k) h (List.range n)
          (fun k hk => if_neg (fun hb : (k == n) = true => by
            have hkn : k < n := ground.ltOfMem hk
            rw [ground.beqEqOf hb] at hkn
            exact Nat.lt_irrefl n hkn)),
        Nat.add_comm (h n) _]

/-- A range fold sits at or above any one of its members. -/
private theorem foldMemLe (h : Nat → Nat) (i n : Nat) (hi : i < n) :
    h i ≤ ground.famFold Nat.add 0 h (List.range n) := by
  rw [foldPeel h i n hi]
  exact Nat.le_add_right _ _

/-- A range fold sits at or above two of its members joined. -/
private theorem foldPairLe (h : Nat → Nat) (i j n : Nat)
    (hi : i < n) (hj : j < n) (hij : ¬ j = i) :
    h i + h j ≤ ground.famFold Nat.add 0 h (List.range n) := by
  rw [foldPeel h i n hi]
  refine Nat.add_le_add_left ?_ (h i)
  have hstep := foldMemLe (fun k => if k == i then 0 else h k) j n hj
  rw [if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
    at hstep
  exact hstep

/-- A range fold sits at or above three of its members joined. -/
private theorem foldTripLe (h : Nat → Nat) (i j k n : Nat)
    (hi : i < n) (hj : j < n) (hk : k < n)
    (hij : ¬ j = i) (hki : ¬ k = i) (hkj : ¬ k = j) :
    h i + h j + h k ≤ ground.famFold Nat.add 0 h (List.range n) := by
  rw [foldPeel h i n hi, Nat.add_assoc]
  refine Nat.add_le_add_left ?_ (h i)
  have hstep := foldPairLe (fun m => if m == i then 0 else h m) j k n
    hj hk hkj
  rw [if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb)),
    if_neg (fun hb : (k == i) = true => hki (ground.beqEqOf hb))]
    at hstep
  exact hstep

/-- The scaled simple row's pairing: the scale against the row's
own scaled length at the key's coordinate. -/
private theorem dotB_scaleRow (t : gentable.Table)
    (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hsp : sertables.simplePosRead t F)
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (c : BPair) (z : List BPair) (hz : z.length = t.rank) :
    (sertables.dotB F
        (elim.vecScale c (ground.getAt [] t.cartan i)) z).oneValue
      (c * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
        * ground.getAt BPair.unit z i)) := by
  refine BPair.oneValue_trans
    (elim.dotP_scaleL c (ground.getAt [] t.cartan i)
      (elim.matVec F.gram z)) ?_
  exact BPair.mul_congr (BPair.oneValue_refl c)
    (dotB_row t F hshape hgram hsp hi hcl z hz)

/-- The member's shifted key sits at the rank's order. -/
private theorem kapLen (t : gentable.Table) (μ : List BPair)
    (hμl : μ.length = t.rank) :
    (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))).length
      = t.rank := by
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  rw [poly.pnorm_length, elim.length_vecAdd _ _ t.rank hμl hrl]

/-- The member's shifted key at a coordinate: the raised member's
own entry (`lem:serstable`(ii)'s shifted key at the word's values
against the `ρ` run). -/
private theorem kapAt (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) {i : Nat} (hi : i < t.rank) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) (sertables.rhoV t)))
      i).oneValue
      (BPair.ofNat (ground.getAt 0 (memberRho W l) i)) := by
  have hil : i < l := by rw [← hrk]; exact hi
  have hml : (memberV W l).length = t.rank := memberVLen t W l hrk
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hA : (elim.vecAdd (memberV W l) (sertables.rhoV t)).length
      = t.rank := elim.length_vecAdd _ _ t.rank hml hrl
  show (ground.getAt BPair.unit
    ((elim.vecAdd (memberV W l) (sertables.rhoV t)).map BPair.norm)
      i).oneValue _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ i
      (by rw [hA]; exact hi),
    elim.getAt_vecAdd _ _ i (by rw [hml]; exact hi)
      (by rw [hrl]; exact hi),
    show ground.getAt BPair.unit (sertables.rhoV t) i = BPair.ofNat 1 from
      ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi,
    show ground.getAt BPair.unit (memberV W l) i
        = BPair.ofNat (ground.getAt 0 (member W l) i) from
      ground.getAt_map 0 BPair.unit BPair.ofNat (member W l) i
        (by rw [memberLen]; exact hil),
    memberRhoStep W l i hil]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_symm (BPair.ofNat_succ _))

/-- The letter's pairing at the shifted target: the key's own coroot
multiple against the letter's scaled length at the target's
coordinate (`lem:serstable`(ii)'s pivot, the fold's pairing at the
target's own shifted key). -/
private def letterDot (t : gentable.Table) (F : sertables.FundData)
    (μ : List BPair) (ρv : List Nat) (i : Nat)
    (nu0 : List BPair) : BPair :=
  BPair.ofNat (ground.getAt 0 ρv i)
    * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
      * ground.getAt BPair.unit (elim.vecAdd nu0
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) i)

/-- The letter's raised content at a target: its square is the
target content's joined to twice the letter's pairing at the shifted
target (`lem:serstable`(ii)'s pivot at the letter's own fold, the
raise the key's coroot multiple). -/
private theorem letterSq (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F)
    (μ : List BPair) (ρv : List Nat) (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (hdg : (ground.getAt BPair.unit
      (ground.getAt [] t.cartan i) i).oneValue (BPair.ofNat 2))
    (nu0 : List BPair) (hn0 : nu0.length = t.rank) :
    (sertables.dotB F
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i))))
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i))))).oneValue
      (sertables.dotB F nu0 nu0
        + (letterDot t F μ ρv i nu0 + letterDot t F μ ρv i nu0)) := by
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hXl : (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
      (ground.getAt [] t.cartan i)).length = t.rank :=
    (elim.length_vecScale _ _).trans hcl
  have hKi := hkap i hi
  have hXi : ground.getAt BPair.unit
      (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i)) i
      = BPair.ofNat (ground.getAt 0 ρv i)
        * ground.getAt BPair.unit (ground.getAt [] t.cartan i) i :=
    elim.getAt_vecScale _ _ i (by rw [hcl]; exact hi)
  have hdouble : (ground.getAt BPair.unit
      (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i)) i).oneValue
      (ground.getAt BPair.unit
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i
        + ground.getAt BPair.unit
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i) := by
    rw [hXi]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hdg) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_mul
        (ground.getAt 0 ρv i) 2)) ?_
    rw [Nat.mul_two]
    exact BPair.oneValue_trans
      (BPair.ofNat_add _ _)
      (BPair.add_congr (BPair.oneValue_symm hKi)
        (BPair.oneValue_symm hKi))
  have hP : (sertables.dotB F nu0
      (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i))).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)
        * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
          * ground.getAt BPair.unit nu0 i)) :=
    BPair.oneValue_trans
      (assembly.dotB_swap t F hshape hgsym nu0 _ hn0 hXl)
      (dotB_scaleRow t F hshape hgram hsp hi hcl _ nu0 hn0)
  have hQ : (sertables.dotB F
      (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i))
      (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i))).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)
          * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
            * ground.getAt BPair.unit
              (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i)
        + BPair.ofNat (ground.getAt 0 ρv i)
          * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
            * ground.getAt BPair.unit
              (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i)) := by
    refine BPair.oneValue_trans
      (dotB_scaleRow t F hshape hgram hsp hi hcl _ _ hXl) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.mul_congr (BPair.oneValue_refl _) hdouble)) ?_
    rw [BPair.left_distrib, BPair.left_distrib]
    exact BPair.oneValue_refl _
  have hLD : (letterDot t F μ ρv i nu0).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)
          * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
            * ground.getAt BPair.unit nu0 i)
        + BPair.ofNat (ground.getAt 0 ρv i)
          * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
            * ground.getAt BPair.unit
              (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i)) := by
    show (BPair.ofNat (ground.getAt 0 ρv i)
      * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
        * ground.getAt BPair.unit (elim.vecAdd nu0
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) i)).oneValue _
    rw [elim.getAt_vecAdd nu0 _ i (by rw [hn0]; exact hi)
        (by rw [hkl]; exact hi),
      BPair.left_distrib, BPair.left_distrib]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans
    (memberchar.dotB_sq_split t F hshape hgsym nu0 _ hn0 hXl) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr hP hP))
    hQ) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)) ?_
  exact BPair.add_congr (BPair.oneValue_symm hLD)
    (BPair.oneValue_symm hLD)

/-- The `θ` content's square: the unit content reads the sum's unit
and every further content sits strictly above it (`prop:row`'s
`ρ`-length read at the positive members, the balance partner's
square its member's own). -/
private theorem contentSq (t : gentable.Table) (F : sertables.FundData)
    (hrho : row.rhoLenRead t F) (L : List (List BPair))
    (hfam : row.thetaFamRead t L) (nu : List BPair) (hmem : nu ∈ L) :
    (nu = List.replicate t.rank BPair.unit
      ∧ (sertables.dotB F nu nu).oneValue BPair.unit)
    ∨ BPair.unit < sertables.dotB F nu nu := by
  match hfam.2.2 nu hmem with
  | Or.inl he =>
    refine Or.inl ⟨he, ?_⟩
    rw [he]
    exact elim.dotP_replL t.rank
      (elim.matVec F.gram (List.replicate t.rank BPair.unit))
  | Or.inr ⟨j, hj1, hcase⟩ =>
    have hj : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj1
    refine Or.inr ?_
    match hcase with
    | Or.inl hpb =>
      have heq : (sertables.dotB F nu nu).oneValue
          (sertables.dotB F (sertables.posCorootV t j)
            (sertables.posCorootV t j)) := by
        rw [hpb]
        exact BPair.oneValue_trans
          (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
          (sertables.dotB_congrR F _ _ _ (poly.pnorm_oneValue _))
      exact BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm heq) (hrho j hj).1
    | Or.inr hnb =>
      have heq : (sertables.dotB F nu nu).oneValue
          (sertables.dotB F (sertables.posCorootV t j)
            (sertables.posCorootV t j)) := by
        rw [hnb]
        refine BPair.oneValue_trans
          (BPair.oneValue_trans
            (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
            (sertables.dotB_congrR F _ _ _ (poly.pnorm_oneValue _))) ?_
        exact BPair.oneValue_of_eq (sertables.dotB_negSq F (sertables.posCorootV t j))
      exact BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm heq) (hrho j hj).1

/-- A `θ` content's square sits at or above the sum's unit. -/
private theorem contentNonneg (t : gentable.Table)
    (F : sertables.FundData)
    (hrho : row.rhoLenRead t F) (L : List (List BPair))
    (hfam : row.thetaFamRead t L) (nu : List BPair) (hmem : nu ∈ L) :
    BPair.unit ≤ sertables.dotB F nu nu := by
  match contentSq t F hrho L hfam nu hmem with
  | Or.inl h =>
    exact ground.leB_congr_right (BPair.oneValue_symm h.2)
      (ground.leB_refl BPair.unit)
  | Or.inr hlt =>
    exact ground.leB_of_lt hlt

/-- A `θ` content at the vacant square is the unit content. -/
private theorem contentVac (t : gentable.Table) (F : sertables.FundData)
    (hrho : row.rhoLenRead t F) (L : List (List BPair))
    (hfam : row.thetaFamRead t L) (nu : List BPair) (hmem : nu ∈ L)
    (hu : (sertables.dotB F nu nu).oneValue BPair.unit) :
    nu = List.replicate t.rank BPair.unit := by
  match contentSq t F hrho L hfam nu hmem with
  | Or.inl h =>
    exact h.1
  | Or.inr hlt =>
    exact absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit) hu hlt)
      (by decide +kernel)

/-- The shifted target's coroot pairs sit at or beyond one: the
target's dominance raised by the `ρ` run. -/
private theorem shiftedDom (t : gentable.Table) (μ : List BPair)
    (hμl : μ.length = t.rank)
    (nu0 : List BPair) (hn0 : nu0.length = t.rank)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    {i : Nat} (hi : i < t.rank) :
    BPair.ofNat 1 ≤ ground.getAt BPair.unit (elim.vecAdd nu0
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) i := by
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hdi : BPair.unit ≤ ground.getAt BPair.unit μ i
      + ground.getAt BPair.unit nu0 i := by
    refine ground.leB_congr_right ?_ (hdomin i hi)
    show (ground.getAt BPair.unit
      ((elim.vecAdd μ nu0).map BPair.norm) i).oneValue _
    rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ i
        (by rw [elim.length_vecAdd _ _ t.rank hμl hn0]; exact hi),
      elim.getAt_vecAdd _ _ i (by rw [hμl]; exact hi)
        (by rw [hn0]; exact hi)]
    exact BPair.norm_oneValue _
  have hki : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      i).oneValue
      (ground.getAt BPair.unit μ i + BPair.ofNat 1) := by
    show (ground.getAt BPair.unit
      ((elim.vecAdd μ (sertables.rhoV t)).map BPair.norm) i).oneValue _
    rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ i
        (by rw [elim.length_vecAdd _ _ t.rank hμl hrl]; exact hi),
      elim.getAt_vecAdd _ _ i (by rw [hμl]; exact hi)
        (by rw [hrl]; exact hi),
      show ground.getAt BPair.unit (sertables.rhoV t) i
          = BPair.ofNat 1 from
        ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi]
    exact BPair.norm_oneValue _
  rw [elim.getAt_vecAdd nu0 _ i (by rw [hn0]; exact hi)
    (by rw [hkl]; exact hi)]
  refine ground.leB_congr (BPair.unit_add (BPair.ofNat 1))
    (BPair.oneValue_symm ?_)
    (ground.leB_add hdi (ground.leB_refl (BPair.ofNat 1)))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) hki) ?_
  rw [← BPair.add_assoc]
  exact BPair.add_congr
    (BPair.oneValue_of_eq (BPair.add_comm _ _)) (BPair.oneValue_refl _)

/-- The letter's raise clears one at a dominant target: beyond one
the raised content's square passes the contents' cap, the target's
shifted coroot pair at the raise itself once the target content's
square reads the sum's unit (`lem:serstable`(ii)'s residue walk at
the one-keyed fold). -/
private theorem letterOne (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F)
    (L : List (List BPair)) (hfam : row.thetaFamRead t L)
    (μ : List BPair) (ρv : List Nat) (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    (hpos : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 ρv k)
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (hdg : (ground.getAt BPair.unit
      (ground.getAt [] t.cartan i) i).oneValue (BPair.ofNat 2))
    (nu0 : List BPair) (hn0 : nu0.length = t.rank) (hn0mem : nu0 ∈ L)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    (hcap : sertables.dotB F
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i))))
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i))))
      ≤ BPair.ofNat (4 * F.scale)) :
    ground.getAt 0 ρv i = 1 := by
  by_cases hone : ground.getAt 0 ρv i = 1
  · exact hone
  · exfalso
    have hcc2 : 2 ≤ ground.getAt 0 ρv i :=
      Nat.lt_of_le_of_ne (hpos i hi) (fun h => hone h.symm)
    have hs1 : 1 ≤ F.scale := hshape.2.2.1
    have hln1 : 1 ≤ ground.getAt 0 t.lenNums i :=
      memberchar.lenNums_pos t F hshape hsp hrd hgram hi
    have hms : F.scale ≤ F.scale * ground.getAt 0 t.lenNums i := by
      have h := Nat.mul_le_mul (Nat.le_refl F.scale) hln1
      rw [Nat.mul_one] at h
      exact h
    have hsq := letterSq t F hshape hgram hgsym hsp μ ρv hμl hkap hi
      hcl hdg nu0 hn0
    have hyi := shiftedDom t μ hμl nu0 hn0 hdomin hi
    have hkl : (poly.pnorm (elim.vecAdd μ
        (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
    have hbase : (BPair.ofNat (ground.getAt 0 ρv i
        * (F.scale * ground.getAt 0 t.lenNums i))).oneValue
        (BPair.ofNat (ground.getAt 0 ρv i)
          * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
            * BPair.ofNat 1)) :=
      BPair.oneValue_trans (BPair.ofNat_mul _ _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (BPair.mul_ofNat_one _)))
    have hLD1 : BPair.ofNat (ground.getAt 0 ρv i
        * (F.scale * ground.getAt 0 t.lenNums i))
        ≤ letterDot t F μ ρv i nu0 :=
      ground.leB_congr_left (BPair.oneValue_symm hbase)
        (ground.leB_mulR (ground.unitLeOfNat _)
          (ground.leB_mulR (ground.unitLeOfNat _) hyi))
    have h2s : 2 * F.scale ≤ ground.getAt 0 ρv i
        * (F.scale * ground.getAt 0 t.lenNums i) :=
      Nat.mul_le_mul hcc2 hms
    have hLD2 : BPair.ofNat (2 * F.scale) ≤ letterDot t F μ ρv i nu0 :=
      ground.leB_trans (ground.leB_ofNat h2s) hLD1
    have hA : BPair.unit ≤ sertables.dotB F nu0 nu0 :=
      contentNonneg t F hrho L hfam nu0 hn0mem
    have h4 : (BPair.ofNat (4 * F.scale)).oneValue
        (BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale)) := by
      have hn : 4 * F.scale = 2 * F.scale + 2 * F.scale := by
        rw [← ground.mulAddR 2 2 F.scale]
      rw [hn]
      exact BPair.ofNat_add _ _
    have hcap' : sertables.dotB F nu0 nu0
        + (letterDot t F μ ρv i nu0 + letterDot t F μ ρv i nu0)
        ≤ BPair.ofNat (4 * F.scale) :=
      ground.leB_congr_left hsq hcap
    have hchain : sertables.dotB F nu0 nu0
        + (BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale))
        ≤ BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale) :=
      ground.leB_congr_right h4
        (ground.leB_trans
          (ground.leB_add (ground.leB_refl _)
            (ground.leB_add hLD2 hLD2)) hcap')
    have hAu : (sertables.dotB F nu0 nu0).oneValue BPair.unit := by
      have hcm : BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale)
            + sertables.dotB F nu0 nu0
          ≤ BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale)
            + BPair.unit :=
        ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
          (BPair.oneValue_symm (BPair.add_unit _)) hchain
      exact ground.leB_antisymm (ground.leB_cancelL hcm) hA
    have hnu0 : nu0 = List.replicate t.rank BPair.unit :=
      contentVac t F hrho L hfam nu0 hn0mem hAu
    have hYcc : (ground.getAt BPair.unit (elim.vecAdd nu0
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) i).oneValue
        (BPair.ofNat (ground.getAt 0 ρv i)) := by
      rw [elim.getAt_vecAdd nu0 _ i (by rw [hn0]; exact hi)
          (by rw [hkl]; exact hi), hnu0,
        ground.getAt_replicate BPair.unit BPair.unit t.rank i hi]
      exact BPair.oneValue_trans (BPair.unit_add _) (hkap i hi)
    have hbig : 4 * F.scale ≤ ground.getAt 0 ρv i
        * (F.scale * ground.getAt 0 t.lenNums i
          * ground.getAt 0 ρv i) := by
      have hn : 4 * F.scale = 2 * (F.scale * 2) := by
        rw [Nat.mul_comm F.scale 2, ← ground.mulAssoc 2 2 F.scale]
      rw [hn]
      exact Nat.mul_le_mul hcc2 (Nat.mul_le_mul hms hcc2)
    have hLDe : (BPair.ofNat (ground.getAt 0 ρv i
        * (F.scale * ground.getAt 0 t.lenNums i
          * ground.getAt 0 ρv i))).oneValue
        (letterDot t F μ ρv i nu0) := by
      refine BPair.oneValue_trans (BPair.ofNat_mul _ _) ?_
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofNat_mul _ _)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm hYcc))
    have hLD3 : BPair.ofNat (4 * F.scale) ≤ letterDot t F μ ρv i nu0 :=
      ground.leB_congr_right hLDe (ground.leB_ofNat hbig)
    have hfin : BPair.ofNat (4 * F.scale + 4 * F.scale)
        ≤ BPair.ofNat (4 * F.scale) := by
      refine ground.leB_congr_left (BPair.oneValue_symm
        (BPair.ofNat_add _ _)) ?_
      refine ground.leB_trans ?_ hcap'
      exact ground.leB_congr_left (BPair.unit_add _)
        (ground.leB_add hA (ground.leB_add hLD3 hLD3))
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
      (Nat.lt_add_of_pos_right
        (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_trans hs1 (Nat.le_mul_of_pos_left F.scale
            (Nat.succ_pos 3)))))
      (ground.leB_ofNat_cancel hfin))

/-- The tie's support fold (`lem:serstable`(ii)'s tie analysis): a
graded member sitting at the shifted target's withdrawal of a `θ`
content reads the member's key at the shifted key's own withdrawal
of a natural simple fold, names the content as the target content
joined to that fold, and carries the kept square as the fold's own
square at its doubled pairing with the shifted key. -/
private theorem tieFold (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgsym : sertables.gramSymRead F)
    (Wl : List (List BPair × Bool)) (wits : List (List Nat))
    (kap y nu0 nu : List BPair)
    (hkl : kap.length = t.rank) (hkn : poly.pnorm kap = kap)
    (hyl : y.length = t.rank) (hyn : poly.pnorm y = y)
    (hyv : poly.oneValue y (elim.vecAdd kap nu0))
    (hn0 : nu0.length = t.rank)
    (hnul : nu.length = t.rank) (s : Bool)
    (hwsh : sertables.wShapeRead t Wl)
    (hdom : assembly.wDomAt t Wl wits kap)
    (hksq : row.sqAtRead F Wl kap)
    (hmem : (poly.pnorm (elim.vecAdd y (poly.neg nu)), s) ∈ Wl) :
    ∃ c : List Nat,
      (assembly.cartanFold t c).length = t.rank
      ∧ poly.pnorm (elim.vecAdd kap
          (poly.neg (assembly.cartanFold t c)))
        = poly.pnorm (elim.vecAdd y (poly.neg nu))
      ∧ poly.oneValue nu (elim.vecAdd nu0 (assembly.cartanFold t c))
      ∧ (sertables.dotB F (assembly.cartanFold t c)
          (assembly.cartanFold t c)).oneValue
          (sertables.dotB F (assembly.cartanFold t c) kap
            + sertables.dotB F (assembly.cartanFold t c) kap) := by
  obtain ⟨hvl, hvn⟩ := hwsh _ hmem
  obtain ⟨k, hk, hgk⟩ := ground.getAt_of_mem ([], false) hmem
  have hkeyk := hdom.2 k hk
  rw [hgk] at hkeyk
  have hcf : (assembly.cartanFold t (ground.getAt [] wits k)).length
      = t.rank :=
    assembly.cartanFold_frame t _ (ground.getAt [] wits k) kap hkl hkeyk
  have hsolve : poly.pnorm (elim.vecAdd kap
      (poly.neg (assembly.cartanFold t (ground.getAt [] wits k))))
      = poly.pnorm (elim.vecAdd y (poly.neg nu)) :=
    assembly.addKey_solve t.rank kap _ _ hkl hkn hcf hvl hvn hkeyk
  have hjoin : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd y (poly.neg nu))) nu) = y :=
    assembly.addKey_join t.rank y nu _ hyl hyn hnul hvl hvn rfl
  have hkone : poly.oneValue kap (elim.vecAdd
      (poly.pnorm (elim.vecAdd y (poly.neg nu)))
      (assembly.cartanFold t (ground.getAt [] wits k))) := by
    have h := poly.pnorm_oneValue (elim.vecAdd
      (poly.pnorm (elim.vecAdd y (poly.neg nu)))
      (assembly.cartanFold t (ground.getAt [] wits k)))
    rw [hkeyk] at h
    exact h
  have hjone : poly.oneValue y (elim.vecAdd
      (poly.pnorm (elim.vecAdd y (poly.neg nu))) nu) := by
    have h := poly.pnorm_oneValue (elim.vecAdd
      (poly.pnorm (elim.vecAdd y (poly.neg nu))) nu)
    rw [hjoin] at h
    exact h
  refine ⟨ground.getAt [] wits k, hcf, hsolve, ?_, ?_⟩
  · refine poly.oneValue_of_entries _ _
      (hnul.trans (elim.length_vecAdd nu0 _ t.rank hn0 hcf).symm)
      (fun j hj => ?_)
    have hjr : j < t.rank := by rw [hnul] at hj; exact hj
    have e1 := poly.oneValue_getAt j hjone
    have e2 := poly.oneValue_getAt j hyv
    have e3 := poly.oneValue_getAt j hkone
    rw [elim.getAt_vecAdd _ nu j (by rw [hvl]; exact hjr)
      (by rw [hnul]; exact hjr)] at e1
    rw [elim.getAt_vecAdd kap nu0 j (by rw [hkl]; exact hjr)
      (by rw [hn0]; exact hjr)] at e2
    rw [elim.getAt_vecAdd _ _ j (by rw [hvl]; exact hjr)
      (by rw [hcf]; exact hjr)] at e3
    rw [elim.getAt_vecAdd nu0 _ j (by rw [hn0]; exact hjr)
      (by rw [hcf]; exact hjr)]
    refine BPair.add_cancel
      (c := ground.getAt BPair.unit
        (poly.pnorm (elim.vecAdd y (poly.neg nu))) j) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm e1) ?_
    refine BPair.oneValue_trans e2 ?_
    refine BPair.oneValue_trans
      (BPair.add_congr e3 (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.add_assoc, BPair.add_comm
        (ground.getAt BPair.unit
          (assembly.cartanFold t (ground.getAt [] wits k)) j)
        (ground.getAt BPair.unit nu0 j),
      BPair.add_comm (ground.getAt BPair.unit
        (poly.pnorm (elim.vecAdd y (poly.neg nu))) j)]
  · have hsqv := hksq _ hmem
    have hsplit := memberchar.dotB_sq_split t F hshape hgsym _
      (assembly.cartanFold t (ground.getAt [] wits k)) hvl hcf
    rw [hkeyk] at hsplit
    have hzero : (sertables.dotB F
          (poly.pnorm (elim.vecAdd y (poly.neg nu)))
          (assembly.cartanFold t (ground.getAt [] wits k))
        + sertables.dotB F (poly.pnorm (elim.vecAdd y (poly.neg nu)))
          (assembly.cartanFold t (ground.getAt [] wits k))
        + sertables.dotB F
          (assembly.cartanFold t (ground.getAt [] wits k))
          (assembly.cartanFold t (ground.getAt [] wits k))).oneValue
        BPair.unit := by
      refine BPair.add_cancel (c := sertables.dotB F kap kap) ?_
      refine BPair.oneValue_trans ?_
        (BPair.oneValue_symm (BPair.unit_add _))
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
      refine BPair.oneValue_trans ?_ (BPair.oneValue_symm hsplit)
      rw [← BPair.add_assoc]
      exact BPair.add_congr
        (BPair.add_congr (BPair.oneValue_symm hsqv)
          (BPair.oneValue_refl _)) (BPair.oneValue_refl _)
    have hdk : (sertables.dotB F
        (assembly.cartanFold t (ground.getAt [] wits k)) kap).oneValue
        (sertables.dotB F (poly.pnorm (elim.vecAdd y (poly.neg nu)))
          (assembly.cartanFold t (ground.getAt [] wits k))
          + sertables.dotB F
            (assembly.cartanFold t (ground.getAt [] wits k))
            (assembly.cartanFold t (ground.getAt [] wits k))) := by
      refine BPair.oneValue_trans
        (sertables.dotB_congrR F _ _ _ hkone) ?_
      refine BPair.oneValue_trans
        (sertables.dotB_addR t F hshape _ _ _ hcf hvl hcf) ?_
      exact BPair.add_congr
        (assembly.dotB_swap t F hshape hgsym _ _ hcf hvl)
        (BPair.oneValue_refl _)
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr hdk hdk) ?_)
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
    exact BPair.oneValue_trans
      (BPair.add_congr hzero (BPair.oneValue_refl _))
      (BPair.unit_add _)

/-- The tie's pivot (`lem:serstable`(ii)): the tie's content square
is the target content's joined to twice the support fold's pairing
at the target's own shifted key. -/
private theorem tiePivot (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgsym : sertables.gramSymRead F)
    (kap nu0 nu : List BPair) (hkl : kap.length = t.rank)
    (hn0 : nu0.length = t.rank)
    (hnul : nu.length = t.rank) (hnun : poly.pnorm nu = nu)
    (c : List Nat) (hcf : (assembly.cartanFold t c).length = t.rank)
    (hnuc : poly.oneValue nu (elim.vecAdd nu0 (assembly.cartanFold t c)))
    (hSQ : (sertables.dotB F (assembly.cartanFold t c)
        (assembly.cartanFold t c)).oneValue
        (sertables.dotB F (assembly.cartanFold t c) kap
          + sertables.dotB F (assembly.cartanFold t c) kap)) :
    (sertables.dotB F nu nu).oneValue
      (sertables.dotB F nu0 nu0
        + (sertables.dotB F (assembly.cartanFold t c)
              (elim.vecAdd nu0 kap)
          + sertables.dotB F (assembly.cartanFold t c)
              (elim.vecAdd nu0 kap))) := by
  have hnueq : nu = poly.pnorm (elim.vecAdd nu0
      (assembly.cartanFold t c)) :=
    hnun.symm.trans (poly.pnorm_congr nu _
      (hnul.trans (elim.length_vecAdd nu0 _ t.rank hn0 hcf).symm) hnuc)
  have hD : (sertables.dotB F (assembly.cartanFold t c)
      (elim.vecAdd nu0 kap)).oneValue
      (sertables.dotB F (assembly.cartanFold t c) nu0
        + sertables.dotB F (assembly.cartanFold t c) kap) :=
    sertables.dotB_addR t F hshape _ nu0 kap hcf hn0 hkl
  rw [hnueq]
  refine BPair.oneValue_trans
    (memberchar.dotB_sq_split t F hshape hgsym nu0 _ hn0 hcf) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr
        (assembly.dotB_swap t F hshape hgsym nu0 _ hn0 hcf)
        (assembly.dotB_swap t F hshape hgsym nu0 _ hn0 hcf)))
    hSQ) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)) ?_
  exact BPair.add_congr (BPair.oneValue_symm hD)
    (BPair.oneValue_symm hD)

/-- The support fold's length-weighted height sits at two: the tie's
pivot prices the fold's pairing at the shifted target, whose coroot
pairs the target's dominance puts at or beyond one, against the
contents' own cap (`lem:serstable`(ii)'s caps). -/
private theorem foldHeight (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (μ : List BPair) (hμl : μ.length = t.rank)
    (nu0 nu : List BPair) (hn0 : nu0.length = t.rank)
    (hnul : nu.length = t.rank) (hnun : poly.pnorm nu = nu)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    (hA : BPair.unit ≤ sertables.dotB F nu0 nu0)
    (hcapnu : sertables.dotB F nu nu ≤ BPair.ofNat (4 * F.scale))
    (c : List Nat) (hcf : (assembly.cartanFold t c).length = t.rank)
    (hnuc : poly.oneValue nu (elim.vecAdd nu0 (assembly.cartanFold t c)))
    (hSQ : (sertables.dotB F (assembly.cartanFold t c)
        (assembly.cartanFold t c)).oneValue
        (sertables.dotB F (assembly.cartanFold t c)
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          + sertables.dotB F (assembly.cartanFold t c)
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))) :
    ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k))
        (List.range t.rank) ≤ 2 * F.scale := by
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hyl : (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t)))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hn0 hkl
  have hpiv := tiePivot t F hshape hgsym _ nu0 nu hkl hn0 hnul hnun c hcf
    hnuc hSQ
  have hDf := assembly.dotB_cartanFold t F hshape hgram c hcf _ hyl
  have hlow : ground.bsum (fun k => BPair.ofNat (ground.getAt 0 c k
        * (F.scale * ground.getAt 0 t.lenNums k))) (List.range t.rank)
      ≤ sertables.dotB F (assembly.cartanFold t c)
        (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ
          (sertables.rhoV t)))) := by
    refine ground.leB_congr_right (BPair.oneValue_symm hDf) ?_
    refine ground.bsum_le _ _ (List.range t.rank) (fun k hk => ?_)
    have hkr : k < t.rank := ground.ltOfMem hk
    refine ground.leB_congr_left (BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.ofNat_mul _ _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (BPair.mul_ofNat_one _))))) ?_
    exact ground.leB_mulR (ground.unitLeOfNat _)
      (ground.leB_mulR (ground.unitLeOfNat _)
        (shiftedDom t μ hμl nu0 hn0 hdomin hkr))
  have hGle : BPair.ofNat (ground.famFold Nat.add 0
      (fun k => ground.getAt 0 c k
        * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank))
      ≤ sertables.dotB F (assembly.cartanFold t c)
        (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) :=
    ground.leB_congr_left (BPair.oneValue_symm
      (ground.ofNat_famFold _ (List.range t.rank))) hlow
  have hsum : BPair.ofNat (ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank)
      + ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank))
      ≤ BPair.ofNat (4 * F.scale) := by
    refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.ofNat_add _ _)) ?_
    refine ground.leB_trans ?_ (ground.leB_congr_left hpiv hcapnu)
    exact ground.leB_congr_left (BPair.unit_add _)
      (ground.leB_add hA (ground.leB_add hGle hGle))
  have hnat : ground.famFold Nat.add 0
      (fun k => ground.getAt 0 c k
        * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank)
      + ground.famFold Nat.add 0
      (fun k => ground.getAt 0 c k
        * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank)
      ≤ 4 * F.scale :=
    ground.leB_ofNat_cancel hsum
  refine Nat.le_of_not_lt (fun hlt => ?_)
  have hdb : 2 * F.scale + 2 * F.scale
      < ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank)
      + ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k)) (List.range t.rank) :=
    Nat.add_lt_add hlt hlt
  rw [← ground.mulAddR 2 2 F.scale] at hdb
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hdb hnat)

/-- A fold occupied at two keys reads their two values joined. -/
private theorem bsumPickTwo (f : Nat → BPair) (i j : Nat)
    (hij : ¬ j = i) (l : List Nat)
    (hi : ground.countOf i l = 1) (hj : ground.countOf j l = 1)
    (hoff : ∀ x, 0 < ground.countOf x l → ¬ x = i → ¬ x = j →
      (f x).oneValue BPair.unit) :
    (ground.famFold BPair.add BPair.unit f l).oneValue (f i + f j) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members f
      (fun k => (if k == i then f i else BPair.unit)
        + (if k == j then f j else BPair.unit)) l (fun x hx => ?_)) ?_
  · by_cases hxi : x = i
    · rw [hxi, if_pos (ground.eqBeqOf rfl),
        if_neg (fun hb : (i == j) = true =>
          hij (ground.beqEqOf hb).symm)]
      exact BPair.oneValue_symm (BPair.add_unit _)
    · by_cases hxj : x = j
      · rw [hxj, if_pos (ground.eqBeqOf rfl),
          if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
        exact BPair.oneValue_symm (BPair.unit_add _)
      · rw [if_neg (fun hb : (x == i) = true => hxi (ground.beqEqOf hb)),
          if_neg (fun hb : (x == j) = true => hxj (ground.beqEqOf hb))]
        exact BPair.oneValue_trans (hoff x hx hxi hxj)
          (BPair.oneValue_symm (BPair.add_unit BPair.unit))
  · exact BPair.oneValue_trans
      (ground.foldB_add _ _ l)
      (BPair.add_congr
        (ground.foldB_pickBeq i (f i) l hi)
        (ground.foldB_pickBeq j (f j) l hj))

/-- A fold occupied at one key alone reads the key's scaled row. -/
private theorem cartanFoldOne (t : gentable.Table) (c : List Nat)
    (hcf : (assembly.cartanFold t c).length = t.rank)
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (hoth : ∀ k, k < t.rank → ¬ k = i → ground.getAt 0 c k = 0) :
    poly.oneValue (assembly.cartanFold t c)
      (elim.vecScale (BPair.ofNat (ground.getAt 0 c i))
        (ground.getAt [] t.cartan i)) := by
  refine poly.oneValue_of_entries _ _
    (hcf.trans ((elim.length_vecScale _ _).trans hcl).symm)
    (fun q hq => ?_)
  have hqr : q < t.rank := by rw [hcf] at hq; exact hq
  rw [elim.getAt_vecScale _ _ q (by rw [hcl]; exact hqr)]
  refine BPair.oneValue_trans (assembly.cartanFold_getAt t c hqr hcf) ?_
  refine ground.foldB_pickRange _ i _ t.rank hi
    (BPair.oneValue_refl _) (fun x hx hxi => ?_)
  rw [hoth x hx hxi]
  exact BPair.unit_mul _

/-- The one-keyed fold's square equation pins the count at the
shifted key's own coroot pair (`lem:serstable`(ii)'s residue walk:
the square equation names the letter's raise). -/
private theorem oneKeyPin (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (μ : List BPair) (ρv : List Nat) (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    {i : Nat} (hi : i < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (hdg : (ground.getAt BPair.unit
      (ground.getAt [] t.cartan i) i).oneValue (BPair.ofNat 2))
    (c : List Nat) (hcf : (assembly.cartanFold t c).length = t.rank)
    (hoth : ∀ k, k < t.rank → ¬ k = i → ground.getAt 0 c k = 0)
    (hci : 1 ≤ ground.getAt 0 c i)
    (hSQ : (sertables.dotB F (assembly.cartanFold t c)
        (assembly.cartanFold t c)).oneValue
        (sertables.dotB F (assembly.cartanFold t c)
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          + sertables.dotB F (assembly.cartanFold t c)
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))) :
    ground.getAt 0 c i = ground.getAt 0 ρv i := by
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hXl : (elim.vecScale (BPair.ofNat (ground.getAt 0 c i))
      (ground.getAt [] t.cartan i)).length = t.rank :=
    (elim.length_vecScale _ _).trans hcl
  have hone := cartanFoldOne t c hcf hi hcl hoth
  have hsq2 : (sertables.dotB F (assembly.cartanFold t c)
      (assembly.cartanFold t c)).oneValue
      (BPair.ofNat (ground.getAt 0 c i
        * (F.scale * ground.getAt 0 t.lenNums i
          * (ground.getAt 0 c i * 2)))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_trans (sertables.dotB_congrL F _ _ _ hone)
        (sertables.dotB_congrR F _ _ _ hone)) ?_
    refine BPair.oneValue_trans
      (dotB_scaleRow t F hshape hgram hsp hi hcl _ _ hXl) ?_
    rw [elim.getAt_vecScale _ _ i (by rw [hcl]; exact hi)]
    refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.ofNat_mul _ _)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans (BPair.ofNat_mul _ _)
              (BPair.mul_congr (BPair.oneValue_refl _)
                (BPair.oneValue_symm hdg)))))))
  have hdk : (sertables.dotB F (assembly.cartanFold t c)
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))).oneValue
      (BPair.ofNat (ground.getAt 0 c i
        * (F.scale * ground.getAt 0 t.lenNums i
          * ground.getAt 0 ρv i))) := by
    refine BPair.oneValue_trans (sertables.dotB_congrL F _ _ _ hone) ?_
    refine BPair.oneValue_trans
      (dotB_scaleRow t F hshape hgram hsp hi hcl _ _ hkl) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.ofNat_mul _ _)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_symm (hkap i hi))))))
  have heq : ground.getAt 0 c i
      * (F.scale * ground.getAt 0 t.lenNums i
        * (ground.getAt 0 c i * 2))
      = ground.getAt 0 c i
        * (F.scale * ground.getAt 0 t.lenNums i
          * ground.getAt 0 ρv i)
      + ground.getAt 0 c i
        * (F.scale * ground.getAt 0 t.lenNums i
          * ground.getAt 0 ρv i) :=
    ground.BPair.ofNat_inj (BPair.oneValue_trans (BPair.oneValue_symm hsq2)
      (BPair.oneValue_trans hSQ
        (BPair.oneValue_trans (BPair.add_congr hdk hdk)
          (BPair.oneValue_symm (BPair.ofNat_add _ _)))))
  have hmpos : 0 < F.scale * ground.getAt 0 t.lenNums i :=
    Nat.mul_pos hshape.2.2.1
      (memberchar.lenNums_pos t F hshape hsp hrd hgram hi)
  have hstep : F.scale * ground.getAt 0 t.lenNums i
      * (ground.getAt 0 c i * 2)
      = F.scale * ground.getAt 0 t.lenNums i
        * (ground.getAt 0 ρv i * 2) := by
    refine Nat.eq_of_mul_eq_mul_left
      (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hci) ?_
    rw [heq, ← ground.mulAssoc (F.scale * ground.getAt 0 t.lenNums i)
        (ground.getAt 0 ρv i) 2,
      Nat.mul_two (F.scale * ground.getAt 0 t.lenNums i
        * ground.getAt 0 ρv i),
      Nat.left_distrib]
  have hfin : ground.getAt 0 c i * 2
      = ground.getAt 0 ρv i * 2 :=
    Nat.eq_of_mul_eq_mul_left hmpos hstep
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos 1) hfin

/-- A unit product of occupied counts reads its two factors at
one. -/
private theorem unitFactors {c s ln : Nat} (hs : 1 ≤ s) (hc : 1 ≤ c)
    (hl : 1 ≤ ln) (h : c * (s * ln) = s) : c = 1 ∧ ln = 1 := by
  have h1 : s * 1 ≤ s * ln := Nat.mul_le_mul (Nat.le_refl s) hl
  rw [Nat.mul_one] at h1
  have h2 : 1 * (s * ln) ≤ c * (s * ln) :=
    Nat.mul_le_mul hc (Nat.le_refl _)
  rw [Nat.one_mul] at h2
  have h3 : s * ln = s :=
    Nat.le_antisymm (Nat.le_trans h2 (Nat.le_of_eq h)) h1
  refine ⟨?_, ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right
      (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hs) ?_
    rw [Nat.one_mul]
    rw [h3] at h
    exact h
  · refine Nat.eq_of_mul_eq_mul_left
      (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hs) ?_
    rw [h3, Nat.mul_one]

/-- The two-keyed fold at the height cap: both counts and both
lengths read one and every further key is vacant
(`lem:serstable`(ii)'s residue walk at the two-keyed fold). -/
private theorem twoKeyData (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F)
    (hln : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 t.lenNums k)
    (c : List Nat) {i j : Nat} (hi : i < t.rank) (hj : j < t.rank)
    (hij : ¬ j = i)
    (hci : 1 ≤ ground.getAt 0 c i) (hcj : 1 ≤ ground.getAt 0 c j)
    (hG : ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k))
        (List.range t.rank) ≤ 2 * F.scale) :
    ground.getAt 0 c i = 1 ∧ ground.getAt 0 c j = 1
      ∧ ground.getAt 0 t.lenNums i = 1 ∧ ground.getAt 0 t.lenNums j = 1
      ∧ ∀ k, k < t.rank → ¬ k = i → ¬ k = j →
          ground.getAt 0 c k = 0 := by
  have hs1 : 1 ≤ F.scale := hshape.2.2.1
  have key : ∀ q, q < t.rank → 1 ≤ ground.getAt 0 c q →
      F.scale ≤ ground.getAt 0 c q
        * (F.scale * ground.getAt 0 t.lenNums q) := by
    intro q hq hcq
    have h1 : F.scale * 1 ≤ F.scale * ground.getAt 0 t.lenNums q :=
      Nat.mul_le_mul (Nat.le_refl _) (hln q hq)
    rw [Nat.mul_one] at h1
    have h2 : 1 * (F.scale * ground.getAt 0 t.lenNums q)
        ≤ ground.getAt 0 c q * (F.scale * ground.getAt 0 t.lenNums q) :=
      Nat.mul_le_mul hcq (Nat.le_refl _)
    rw [Nat.one_mul] at h2
    exact Nat.le_trans h1 h2
  have hG2 : ground.famFold Nat.add 0
      (fun k => ground.getAt 0 c k
        * (F.scale * ground.getAt 0 t.lenNums k))
      (List.range t.rank) ≤ F.scale + F.scale := by
    rw [← Nat.two_mul]
    exact hG
  have hpair := Nat.le_trans
    (foldPairLe (fun k => ground.getAt 0 c k
      * (F.scale * ground.getAt 0 t.lenNums k)) i j t.rank hi hj hij) hG2
  have hIle : ground.getAt 0 c i * (F.scale * ground.getAt 0 t.lenNums i)
      ≤ F.scale :=
    ground.leCancelR F.scale
      (Nat.le_trans (Nat.add_le_add_left (key j hj hcj) _) hpair)
  have hJle : ground.getAt 0 c j * (F.scale * ground.getAt 0 t.lenNums j)
      ≤ F.scale :=
    ground.leCancelL F.scale
      (Nat.le_trans (Nat.add_le_add_right (key i hi hci) _) hpair)
  have hIe := unitFactors hs1 hci (hln i hi)
    (Nat.le_antisymm hIle (key i hi hci))
  have hJe := unitFactors hs1 hcj (hln j hj)
    (Nat.le_antisymm hJle (key j hj hcj))
  refine ⟨hIe.1, hJe.1, hIe.2, hJe.2, fun k hk hki hkj => ?_⟩
  have hsum : ground.getAt 0 c i * (F.scale * ground.getAt 0 t.lenNums i)
      + ground.getAt 0 c j * (F.scale * ground.getAt 0 t.lenNums j)
      = F.scale + F.scale := by
    rw [hIe.1, hIe.2, hJe.1, hJe.2, Nat.one_mul, Nat.mul_one]
  have htrip := Nat.le_trans
    (foldTripLe (fun q => ground.getAt 0 c q
      * (F.scale * ground.getAt 0 t.lenNums q)) i j k t.rank hi hj hk
      hij hki hkj) hG2
  rw [hsum] at htrip
  have hzero : ground.getAt 0 c k
      * (F.scale * ground.getAt 0 t.lenNums k) = 0 :=
    Nat.le_antisymm
      (ground.leCancelL (F.scale + F.scale)
        (Nat.le_trans htrip (Nat.le_of_eq (Nat.add_zero _).symm)))
      (Nat.zero_le _)
  match Nat.eq_zero_or_pos (ground.getAt 0 c k) with
  | Or.inl h => exact h
  | Or.inr h =>
    have hpos : 0 < ground.getAt 0 c k
        * (F.scale * ground.getAt 0 t.lenNums k) :=
      Nat.mul_pos h (Nat.mul_pos hshape.2.2.1 (hln k hk))
    rw [hzero] at hpos
    exact absurd hpos (Nat.lt_irrefl 0)

/-- The two-keyed fold is refused (`lem:serstable`(ii)'s residue
walk): at the height cap both keys carry unit counts and unit
lengths, the target content's square is then the sum's unit and the
tie's content reads the fold itself, whose `ρ`-dot names it a simple
of the doubled length — a key off both, where the fold's own coroot
pair reads at or below the unit against the simple's two. -/
private theorem twoKeyRefute (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F)
    (L : List (List BPair)) (hfam : row.thetaFamRead t L)
    (μ : List BPair) (hμl : μ.length = t.rank)
    (hcl : ∀ q, q < t.rank →
      (ground.getAt [] t.cartan q).length = t.rank)
    (hdg : ∀ q, q < t.rank → (ground.getAt BPair.unit
      (ground.getAt [] t.cartan q) q).oneValue (BPair.ofNat 2))
    (hoff : ∀ p q, p < t.rank → q < t.rank → ¬ q = p →
      ground.getAt BPair.unit (ground.getAt [] t.cartan p) q
        ≤ BPair.unit)
    (nu0 nu : List BPair) (hn0 : nu0.length = t.rank)
    (hn0mem : nu0 ∈ L)
    (hnul : nu.length = t.rank) (hnun : poly.pnorm nu = nu)
    (hnumem : nu ∈ L)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    (hcapnu : sertables.dotB F nu nu ≤ BPair.ofNat (4 * F.scale))
    (c : List Nat) (hcf : (assembly.cartanFold t c).length = t.rank)
    (hnuc : poly.oneValue nu (elim.vecAdd nu0 (assembly.cartanFold t c)))
    (hSQ : (sertables.dotB F (assembly.cartanFold t c)
        (assembly.cartanFold t c)).oneValue
        (sertables.dotB F (assembly.cartanFold t c)
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          + sertables.dotB F (assembly.cartanFold t c)
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))))
    {i j : Nat} (hi : i < t.rank) (hj : j < t.rank) (hij : ¬ j = i)
    (hci : 1 ≤ ground.getAt 0 c i) (hcj : 1 ≤ ground.getAt 0 c j)
    (hG : ground.famFold Nat.add 0
        (fun k => ground.getAt 0 c k
          * (F.scale * ground.getAt 0 t.lenNums k))
        (List.range t.rank) ≤ 2 * F.scale) : False := by
  have hln : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 t.lenNums k :=
    fun k hk => memberchar.lenNums_pos t F hshape hsp hrd hgram hk
  have hs1 : 1 ≤ F.scale := hshape.2.2.1
  obtain ⟨hc1, hc2, hl1, hl2, hoth⟩ :=
    twoKeyData t F hshape hln c hi hj hij hci hcj hG
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hyl : (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t)))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hn0 hkl
  have hpickC : ∀ g : Nat → BPair,
      (ground.bsum (fun x => BPair.ofNat (ground.getAt 0 c x) * g x)
        (List.range t.rank)).oneValue
        (BPair.ofNat (ground.getAt 0 c i) * g i
          + BPair.ofNat (ground.getAt 0 c j) * g j) := fun g =>
    bsumPickTwo _ i j hij (List.range t.rank)
      (ground.countOf_range_one hi) (ground.countOf_range_one hj)
      (fun x hx hxi hxj => by
        rw [hoth x (ground.ltOfMem hx) hxi hxj]
        exact BPair.unit_mul _)
  have hdotTwo : ∀ z : List BPair, z.length = t.rank →
      (sertables.dotB F (assembly.cartanFold t c) z).oneValue
        (BPair.ofNat F.scale * ground.getAt BPair.unit z i
          + BPair.ofNat F.scale * ground.getAt BPair.unit z j) := by
    intro z hz
    refine BPair.oneValue_trans
      (assembly.dotB_cartanFold t F hshape hgram c hcf z hz) ?_
    refine BPair.oneValue_trans (hpickC _) ?_
    rw [hc1, hl1, hc2, hl2, Nat.mul_one]
    exact BPair.add_congr (BPair.ofNat_one_mul _)
      (BPair.ofNat_one_mul _)
  have hdEntry : ∀ q, q < t.rank →
      (ground.getAt BPair.unit (assembly.cartanFold t c) q).oneValue
        (ground.getAt BPair.unit (ground.getAt [] t.cartan i) q
          + ground.getAt BPair.unit (ground.getAt [] t.cartan j) q) := by
    intro q hq
    refine BPair.oneValue_trans (assembly.cartanFold_getAt t c hq hcf) ?_
    refine BPair.oneValue_trans (hpickC _) ?_
    rw [hc1, hc2]
    exact BPair.add_congr (BPair.ofNat_one_mul _)
      (BPair.ofNat_one_mul _)
  have hD0 : (BPair.ofNat (2 * F.scale)).oneValue
      (BPair.ofNat F.scale + BPair.ofNat F.scale) := by
    rw [Nat.two_mul]
    exact BPair.ofNat_add _ _
  have hDlow : BPair.ofNat (2 * F.scale)
      ≤ sertables.dotB F (assembly.cartanFold t c)
        (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ
          (sertables.rhoV t)))) := by
    refine ground.leB_congr_left (BPair.oneValue_symm hD0)
      (ground.leB_congr_right (BPair.oneValue_symm (hdotTwo _ hyl)) ?_)
    refine ground.leB_add ?_ ?_
    · exact ground.leB_congr_left (BPair.mul_ofNat_one _)
        (ground.leB_mulR (ground.unitLeOfNat _)
          (shiftedDom t μ hμl nu0 hn0 hdomin hi))
    · exact ground.leB_congr_left (BPair.mul_ofNat_one _)
        (ground.leB_mulR (ground.unitLeOfNat _)
          (shiftedDom t μ hμl nu0 hn0 hdomin hj))
  have hpiv := tiePivot t F hshape hgsym _ nu0 nu hkl hn0 hnul hnun c hcf
    hnuc hSQ
  have h4 : (BPair.ofNat (4 * F.scale)).oneValue
      (BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale)) := by
    have hn : 4 * F.scale = 2 * F.scale + 2 * F.scale := by
      rw [← ground.mulAddR 2 2 F.scale]
    rw [hn]
    exact BPair.ofNat_add _ _
  have hA : BPair.unit ≤ sertables.dotB F nu0 nu0 :=
    contentNonneg t F hrho L hfam nu0 hn0mem
  have hcap' : sertables.dotB F nu0 nu0
      + (sertables.dotB F (assembly.cartanFold t c)
          (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
        + sertables.dotB F (assembly.cartanFold t c)
          (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))))
      ≤ BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale) :=
    ground.leB_congr_right h4 (ground.leB_congr_left hpiv hcapnu)
  have hAu : (sertables.dotB F nu0 nu0).oneValue BPair.unit := by
    have hcm : BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale)
          + sertables.dotB F nu0 nu0
        ≤ BPair.ofNat (2 * F.scale) + BPair.ofNat (2 * F.scale)
          + BPair.unit :=
      ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.oneValue_symm (BPair.add_unit _))
        (ground.leB_trans
          (ground.leB_add (ground.leB_refl _)
            (ground.leB_add hDlow hDlow)) hcap')
    exact ground.leB_antisymm (ground.leB_cancelL hcm) hA
  have hDup : sertables.dotB F (assembly.cartanFold t c)
      (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
      ≤ BPair.ofNat (2 * F.scale) := by
    refine ground.leB_cancelL (x := BPair.ofNat (2 * F.scale)) ?_
    refine ground.leB_trans (ground.leB_add hDlow (ground.leB_refl _)) ?_
    refine ground.leB_trans ?_ hcap'
    exact ground.leB_congr_left (BPair.unit_add _)
      (ground.leB_add hA (ground.leB_refl _))
  have hDeq : (sertables.dotB F (assembly.cartanFold t c)
      (elim.vecAdd nu0 (poly.pnorm (elim.vecAdd μ
        (sertables.rhoV t))))).oneValue (BPair.ofNat (2 * F.scale)) :=
    ground.leB_antisymm hDup hDlow
  have hnu0e : nu0 = List.replicate t.rank BPair.unit :=
    contentVac t F hrho L hfam nu0 hn0mem hAu
  have hnud : poly.oneValue nu (assembly.cartanFold t c) := by
    refine poly.oneValue_trans hnuc ?_
    rw [hnu0e]
    exact elim.vecAdd_null_left _ _
      ((ground.length_replicate BPair.unit t.rank).trans hcf.symm)
      (poly.unitTail_replicate t.rank)
  have hsqnu : (sertables.dotB F nu nu).oneValue
      (BPair.ofNat (4 * F.scale)) := by
    refine BPair.oneValue_trans hpiv ?_
    refine BPair.oneValue_trans
      (BPair.add_congr hAu (BPair.add_congr hDeq hDeq)) ?_
    exact BPair.oneValue_trans (BPair.unit_add _)
      (BPair.oneValue_symm h4)
  have hrhoNu : (sertables.dotB F nu (sertables.rhoV t)).oneValue
      (BPair.ofNat (2 * F.scale)) := by
    refine BPair.oneValue_trans
      (sertables.dotB_congrL F _ _ _ hnud) ?_
    refine BPair.oneValue_trans (hdotTwo _ hrl) ?_
    rw [show ground.getAt BPair.unit (sertables.rhoV t) i = BPair.ofNat 1
        from ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi,
      show ground.getAt BPair.unit (sertables.rhoV t) j = BPair.ofNat 1
        from ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank j hj]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_ofNat_one _) (BPair.mul_ofNat_one _))
      (BPair.oneValue_symm hD0)
  match hfam.2.2 nu hnumem with
  | Or.inl he =>
    refine BPair.ofNat_off_unit (4 * F.scale)
      (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
        (Nat.le_trans hs1 (Nat.le_mul_of_pos_left F.scale
          (Nat.succ_pos 3)))) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm hsqnu) ?_
    rw [he]
    exact elim.dotP_replL t.rank
      (elim.matVec F.gram (List.replicate t.rank BPair.unit))
  | Or.inr ⟨j0, hj01, hcase⟩ =>
    have hj0 : j0 < t.posFolds.length := Nat.lt_of_succ_lt_succ hj01
    match hcase with
    | Or.inr hnb =>
      have hsw : (sertables.dotB F nu (sertables.rhoV t)).oneValue
          (sertables.dotB F (sertables.posCorootV t j0)
            (sertables.rhoV t)).swap := by
        rw [hnb]
        refine BPair.oneValue_trans
          (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _)) ?_
        exact BPair.oneValue_of_eq
          (elim.dotP_swap_left (sertables.posCorootV t j0)
            (elim.matVec F.gram (sertables.rhoV t)))
      have hlt : (sertables.dotB F (sertables.posCorootV t j0)
          (sertables.rhoV t)).swap < BPair.unit :=
        ground.ltB_swap (hrd j0 hj0)
      have hpos : BPair.unit < BPair.ofNat (2 * F.scale) := by
        obtain ⟨d, hd⟩ := Nat.le.dest
          (Nat.le_trans hs1 (Nat.le_mul_of_pos_left F.scale
            (Nat.succ_pos 1)))
        rw [← hd, Nat.add_comm]
        exact ground.unitLtOfNat d
      have hltU : sertables.dotB F nu (sertables.rhoV t) < BPair.unit :=
        BPair.lt_congr (BPair.oneValue_symm hsw)
          (BPair.oneValue_refl _) hlt
      have hgtU : BPair.unit < sertables.dotB F nu (sertables.rhoV t) :=
        BPair.lt_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm hrhoNu) hpos
      exact ground.leB_not_lt (ground.leB_of_lt hgtU) hltU
    | Or.inl hpb =>
      have hnb : poly.oneValue nu (sertables.posCorootV t j0) := by
        rw [hpb]
        exact poly.pnorm_oneValue _
      have hsqB : (sertables.dotB F (sertables.posCorootV t j0)
          (sertables.posCorootV t j0)).oneValue
          (BPair.ofNat (4 * F.scale)) :=
        BPair.oneValue_trans
          (BPair.oneValue_trans
            (sertables.dotB_congrL F _ _ _ (poly.oneValue_symm hnb))
            (sertables.dotB_congrR F _ _ _ (poly.oneValue_symm hnb)))
          hsqnu
      have hrhoB : (sertables.dotB F (sertables.posCorootV t j0)
          (sertables.rhoV t)).oneValue (BPair.ofNat (2 * F.scale)) :=
        BPair.oneValue_trans
          (sertables.dotB_congrL F _ _ _ (poly.oneValue_symm hnb))
          hrhoNu
      obtain ⟨i0, hi01, hi0e⟩ := (hrho j0 hj0).2.2
        (BPair.oneValue_trans (BPair.add_congr hrhoB hrhoB)
          (BPair.oneValue_trans (BPair.oneValue_symm h4)
            (BPair.oneValue_symm hsqB)))
      have hi0 : i0 < t.rank := Nat.lt_of_succ_lt_succ hi01
      have hrow : poly.oneValue nu (ground.getAt [] t.cartan i0) := by
        refine poly.oneValue_trans hnb ?_
        rw [hi0e]
        exact simpleRowOne t F hsp hi0 (hcl i0 hi0)
      have hlen2 : (sertables.dotB F (ground.getAt [] t.cartan i0)
          (sertables.rhoV t)).oneValue
          (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i0)) := by
        refine BPair.oneValue_trans
          (dotB_row t F hshape hgram hsp hi0 (hcl i0 hi0) _ hrl) ?_
        rw [show ground.getAt BPair.unit (sertables.rhoV t) i0
            = BPair.ofNat 1 from
          ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i0 hi0]
        exact BPair.mul_ofNat_one _
      have hlnEq : F.scale * ground.getAt 0 t.lenNums i0 = F.scale * 2 :=
        ground.BPair.ofNat_inj (BPair.oneValue_trans (BPair.oneValue_symm hlen2)
          (BPair.oneValue_trans
            (sertables.dotB_congrL F _ _ _ (poly.oneValue_symm hrow))
            (BPair.oneValue_trans hrhoNu
              (BPair.oneValue_of_eq
                (congrArg BPair.ofNat (Nat.mul_comm 2 F.scale))))))
      have hln2 : ground.getAt 0 t.lenNums i0 = 2 :=
        Nat.eq_of_mul_eq_mul_left
          (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hs1) hlnEq
      have hne1 : ¬ i0 = i := by
        intro he
        rw [he, hl1] at hln2
        exact Nat.noConfusion hln2 (fun h => Nat.noConfusion h)
      have hne2 : ¬ i0 = j := by
        intro he
        rw [he, hl2] at hln2
        exact Nat.noConfusion hln2 (fun h => Nat.noConfusion h)
      have hdiag : (ground.getAt BPair.unit
          (assembly.cartanFold t c) i0).oneValue (BPair.ofNat 2) :=
        BPair.oneValue_trans
          (BPair.oneValue_symm (poly.oneValue_getAt i0 hnud))
          (BPair.oneValue_trans (poly.oneValue_getAt i0 hrow)
            (hdg i0 hi0))
      refine absurd ?_ (by decide +kernel : ¬ (BPair.ofNat 2 ≤ BPair.unit))
      refine ground.leB_congr_left hdiag ?_
      refine ground.leB_congr_left (BPair.oneValue_symm (hdEntry i0 hi0))
        ?_
      refine ground.leB_congr_right (BPair.add_unit BPair.unit) ?_
      exact ground.leB_add
        (hoff i i0 hi hi0 (fun he => hne1 he))
        (hoff j i0 hj hi0 (fun he => hne2 he))

/-- `lem:serstable`(ii)'s residue walk: a tie of the graded image
list against a `θ` content at the raised target is the identity's —
the content the target's own, the member the shifted key — or a
simple letter's, the content the target's raised by the key's coroot
multiple of the letter's root at the raise one and the member the
letter's image of the shifted key. -/
private theorem tieWalk (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F)
    (Wl : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (hmsh : memberchar.mShapeRead t L)
    (hfam : row.thetaFamRead t L)
    (μ : List BPair) (ρv : List Nat) (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    (hpos : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 ρv k)
    (hcl : ∀ q, q < t.rank →
      (ground.getAt [] t.cartan q).length = t.rank)
    (hdg : ∀ q, q < t.rank → (ground.getAt BPair.unit
      (ground.getAt [] t.cartan q) q).oneValue (BPair.ofNat 2))
    (hoff : ∀ p q, p < t.rank → q < t.rank → ¬ q = p →
      ground.getAt BPair.unit (ground.getAt [] t.cartan p) q
        ≤ BPair.unit)
    (hwsh : sertables.wShapeRead t Wl)
    (hdom : assembly.wDomAt t Wl wits
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
    (hksq : row.sqAtRead F Wl
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
    (nu0 : List BPair) (hn0mem : nu0 ∈ L)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    (hcapL : ∀ z ∈ L, sertables.dotB F z z ≤ BPair.ofNat (4 * F.scale))
    (nu : List BPair) (hnumem : nu ∈ L) (s : Bool)
    (hmem : (poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
        nu0)) (poly.neg nu)), s) ∈ Wl) :
    (nu = nu0
      ∧ poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
            nu0)) (poly.neg nu))
        = poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
    ∨ ∃ i, i < t.rank
        ∧ ground.getAt 0 ρv i = 1
        ∧ nu = poly.pnorm (elim.vecAdd nu0
            (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
              (ground.getAt [] t.cartan i)))
        ∧ poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
              nu0)) (poly.neg nu))
          = sertables.reflAt t i
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) := by
  obtain ⟨hn0, hn0n⟩ := hmsh nu0 hn0mem
  obtain ⟨hnul, hnun⟩ := hmsh nu hnumem
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hkn : poly.pnorm (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      = poly.pnorm (elim.vecAdd μ (sertables.rhoV t)) :=
    poly.pnorm_pnorm _
  have hyl : (poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      nu0)).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd _ _ t.rank hkl hn0)
  obtain ⟨c, hcf, hsolve, hnuc, hSQ⟩ := tieFold t F hshape hgsym Wl wits
    _ _ nu0 nu hkl hkn hyl (poly.pnorm_pnorm _)
    (poly.pnorm_oneValue _) hn0 hnul s hwsh hdom hksq hmem
  have hcapnu := hcapL nu hnumem
  have hA := contentNonneg t F hrho L hfam nu0 hn0mem
  have hG := foldHeight t F hshape hgram hgsym μ hμl nu0 nu hn0 hnul
    hnun hdomin hA hcapnu c hcf hnuc hSQ
  match ground.getAt_vac_or_occ c t.rank with
  | Or.inl hall =>
    refine Or.inl ⟨?_, ?_⟩
    · have hnull := assembly.cartanFold_null t c hcf hall
      refine hnun.symm.trans ((poly.pnorm_congr nu nu0
        (hnul.trans hn0.symm) ?_).trans hn0n)
      refine poly.oneValue_trans hnuc ?_
      refine poly.oneValue_trans
        (elim.polyOne_vecAdd nu0 nu0 _ _ (poly.oneValue_refl nu0)
          hnull rfl
          (hcf.trans (ground.length_replicate BPair.unit t.rank).symm)) ?_
      exact elim.vecAdd_null_right nu0 _
        (hn0.trans (ground.length_replicate BPair.unit t.rank).symm)
        (poly.unitTail_replicate t.rank)
    · refine hsolve.symm.trans ?_
      have hnull := assembly.cartanFold_null t c hcf hall
      have hneg : poly.oneValue (poly.neg (assembly.cartanFold t c))
          (List.replicate t.rank BPair.unit) := by
        refine poly.oneValue_trans (poly.swapMap_oneValue hnull) ?_
        show poly.oneValue (poly.neg (List.replicate t.rank BPair.unit))
          (List.replicate t.rank BPair.unit)
        rw [poly.neg_repl t.rank]
        exact poly.oneValue_refl _
      have hnl : (poly.neg (assembly.cartanFold t c)).length = t.rank :=
        (ground.length_map BPair.swap _).trans hcf
      refine Eq.trans (poly.pnorm_congr _ _ ?_ ?_) hkn
      · rw [elim.length_vecAdd _ _ t.rank hkl hnl, hkl]
      · refine poly.oneValue_trans
          (elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _) hneg rfl
            (hnl.trans
              (ground.length_replicate BPair.unit t.rank).symm)) ?_
        exact elim.vecAdd_null_right _ _
          (hkl.trans (ground.length_replicate BPair.unit t.rank).symm)
          (poly.unitTail_replicate t.rank)
  | Or.inr ⟨i, hi, hci0⟩ =>
    have hci : 1 ≤ ground.getAt 0 c i := Nat.pos_of_ne_zero hci0
    match findNZoff c i t.rank with
    | Or.inr ⟨j, hj, hji, hcj0⟩ =>
      exact absurd (twoKeyRefute t F hshape hgram hgsym hsp hrd hrho L
        hfam μ hμl hcl hdg hoff nu0 nu hn0 hn0mem hnul hnun hnumem
        hdomin hcapnu c hcf hnuc hSQ hi hj hji hci
        (Nat.pos_of_ne_zero hcj0) hG) (fun h => h)
    | Or.inl hoth =>
      have hpin := oneKeyPin t F hshape hgram hsp hrd μ ρv hμl hkap hi
        (hcl i hi) (hdg i hi) c hcf hoth hci hSQ
      have hone := cartanFoldOne t c hcf hi (hcl i hi) hoth
      rw [hpin] at hone
      have hXl : (elim.vecScale
          (BPair.ofNat (ground.getAt 0 ρv i))
          (ground.getAt [] t.cartan i)).length = t.rank :=
        (elim.length_vecScale _ _).trans (hcl i hi)
      have hnuE : nu = poly.pnorm (elim.vecAdd nu0
          (elim.vecScale
            (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i))) := by
        refine hnun.symm.trans (poly.pnorm_congr nu _
          (hnul.trans (elim.length_vecAdd _ _ t.rank hn0 hXl).symm) ?_)
        refine poly.oneValue_trans hnuc ?_
        exact elim.polyOne_vecAdd nu0 nu0 _ _ (poly.oneValue_refl nu0)
          hone rfl (hcf.trans hXl.symm)
      have hmr1 : ground.getAt 0 ρv i = 1 := by
        refine letterOne t F hshape hgram hgsym hsp hrd hrho L hfam μ ρv
          hμl hkap hpos hi (hcl i hi) (hdg i hi) nu0 hn0 hn0mem
          hdomin ?_
        rw [← hnuE]
        exact hcapnu
      refine Or.inr ⟨i, hi, hmr1, hnuE, ?_⟩
      refine hsolve.symm.trans ?_
      have hki : (ground.getAt BPair.unit
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          i).oneValue (BPair.ofNat 1) := by
        refine BPair.oneValue_trans (hkap i hi) ?_
        rw [hmr1]
        exact BPair.oneValue_refl _
      rw [assembly.reflAt_shift t i hi _ hkl hki]
      have hnl : (poly.neg (assembly.cartanFold t c)).length = t.rank :=
        (ground.length_map BPair.swap _).trans hcf
      have hcr : (poly.neg (assembly.cartRowV t i)).length = t.rank :=
        (ground.length_map BPair.swap _).trans (assembly.cartRowV_length t i)
      refine poly.pnorm_congr _ _ ?_ ?_
      · rw [elim.length_vecAdd _ _ t.rank hkl hnl,
          elim.length_vecAdd _ _ t.rank hkl hcr]
      · refine elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _) ?_ rfl
          (hnl.trans hcr.symm)
        refine poly.swapMap_oneValue ?_
        refine poly.oneValue_trans hone ?_
        refine poly.oneValue_of_entries _ _
          (hXl.trans (assembly.cartRowV_length t i).symm) (fun q hq => ?_)
        have hqr : q < t.rank := by rw [hXl] at hq; exact hq
        rw [elim.getAt_vecScale _ _ q (by rw [hcl i hi]; exact hqr),
          assembly.cartRowV_getAt t i q hqr, hmr1]
        exact BPair.ofNat_one_mul _

/-- The letter's image at a coordinate: the key's own entry
withdrawn by the letter's Cartan row, read at a key whose own
coordinate is the natural one. -/
private theorem reflEntry (t : gentable.Table) {i : Nat} (hi : i < t.rank)
    (v : List BPair) (hvl : v.length = t.rank)
    (hvi : (ground.getAt BPair.unit v i).oneValue (BPair.ofNat 1))
    {q : Nat} (hq : q < t.rank) :
    (ground.getAt BPair.unit (sertables.reflAt t i v) q).oneValue
      (ground.getAt BPair.unit v q
        + (ground.getAt BPair.unit
            (ground.getAt [] t.cartan i) q).swap) := by
  have hcr : (poly.neg (assembly.cartRowV t i)).length = t.rank :=
    (ground.length_map BPair.swap _).trans (assembly.cartRowV_length t i)
  rw [assembly.reflAt_shift t i hi v hvl hvi]
  refine BPair.oneValue_trans
    (poly.oneValue_getAt q (poly.pnorm_oneValue _)) ?_
  rw [elim.getAt_vecAdd _ _ q (by rw [hvl]; exact hq)
      (by rw [hcr]; exact hq),
    show ground.getAt BPair.unit (poly.neg (assembly.cartRowV t i)) q
      = (ground.getAt BPair.unit (assembly.cartRowV t i) q).swap
      from ground.getAt_map BPair.unit BPair.unit BPair.swap _ q
        (by rw [assembly.cartRowV_length t i]; exact hq),
    assembly.cartRowV_getAt t i q hq]
  exact BPair.oneValue_refl _

/-- A datum at or below the sum's unit reads its swap at or above
it. -/
private theorem leSwapUnit {x : BPair} (h : x ≤ BPair.unit) :
    BPair.unit ≤ x.swap := by
  show Pos.one + x.fst ≤ x.snd + Pos.one
  have h' : x.fst + Pos.one ≤ Pos.one + x.snd := h
  rw [ground.add_comm Pos.one x.fst, ground.add_comm x.snd Pos.one]
  exact h'

/-- The letters' images part: two letters at unit coroot pairs
sending the shifted key to one image are the same letter, the
image's own coordinate reading below the sum's unit at its letter
and at or above it at every other (`lem:serstable`(ii): the letters'
images are distinct at the strict dominance). -/
private theorem reflDistinct (t : gentable.Table)
    (μ : List BPair) (ρv : List Nat) (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    (hdg : ∀ p, p < t.rank → (ground.getAt BPair.unit
      (ground.getAt [] t.cartan p) p).oneValue (BPair.ofNat 2))
    (hoff : ∀ p q, p < t.rank → q < t.rank → ¬ q = p →
      ground.getAt BPair.unit (ground.getAt [] t.cartan p) q
        ≤ BPair.unit)
    {i q : Nat} (hi : i < t.rank) (hq : q < t.rank) (hiq : ¬ i = q)
    (hmri : ground.getAt 0 ρv i = 1)
    (hmrq : ground.getAt 0 ρv q = 1)
    (he : sertables.reflAt t q
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      = sertables.reflAt t i
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) :
    False := by
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hki : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      i).oneValue (BPair.ofNat 1) := by
    refine BPair.oneValue_trans (hkap i hi) ?_
    rw [hmri]
    exact BPair.oneValue_refl _
  have hkq : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      q).oneValue (BPair.ofNat 1) := by
    refine BPair.oneValue_trans (hkap q hq) ?_
    rw [hmrq]
    exact BPair.oneValue_refl _
  have hAi : (ground.getAt BPair.unit (sertables.reflAt t i
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
      i).oneValue (BPair.ofNat 1 + (BPair.ofNat 2).swap) :=
    BPair.oneValue_trans (reflEntry t hi _ hkl hki hi)
      (BPair.add_congr hki (ground.swap_congr (hdg i hi)))
  have hAq : BPair.unit ≤ ground.getAt BPair.unit (sertables.reflAt t q
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) i := by
    refine ground.leB_congr_right
      (BPair.oneValue_symm (reflEntry t hq _ hkl hkq hi)) ?_
    refine ground.unitLeAdd ?_ (leSwapUnit (hoff q i hq hi hiq))
    exact ground.leB_congr_right (BPair.oneValue_symm hki)
      (ground.unitLeOfNat 1)
  rw [he] at hAq
  exact absurd (ground.leB_congr_right hAi hAq)
    (by decide +kernel : ¬ (BPair.unit ≤ BPair.ofNat 1 + (BPair.ofNat 2).swap))

/-- The letter's own tie: at a dominant target a letter content
sitting in the `θ` list carries the raise one, and the shifted
target's withdrawal of it is the letter's image of the shifted key
(`lem:serstable`(ii)'s letter reads at the run). -/
private theorem letterKey (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F)
    (L : List (List BPair)) (hmsh : memberchar.mShapeRead t L)
    (hfam : row.thetaFamRead t L)
    (μ : List BPair) (ρv : List Nat) (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    (hpos : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 ρv k)
    (hcl : ∀ q, q < t.rank →
      (ground.getAt [] t.cartan q).length = t.rank)
    (hdg : ∀ q, q < t.rank → (ground.getAt BPair.unit
      (ground.getAt [] t.cartan q) q).oneValue (BPair.ofNat 2))
    (nu0 : List BPair) (hn0mem : nu0 ∈ L)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    (hcapL : ∀ z ∈ L, sertables.dotB F z z ≤ BPair.ofNat (4 * F.scale))
    {i : Nat} (hi : i < t.rank)
    (hmemL : poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat (ground.getAt 0 ρv i))
          (ground.getAt [] t.cartan i))) ∈ L) :
    ground.getAt 0 ρv i = 1
    ∧ poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          nu0))
        (poly.neg (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale
            (BPair.ofNat (ground.getAt 0 ρv i))
            (ground.getAt [] t.cartan i))))))
      = sertables.reflAt t i
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) := by
  obtain ⟨hn0, hn0n⟩ := hmsh nu0 hn0mem
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hXl : (elim.vecScale
      (BPair.ofNat (ground.getAt 0 ρv i))
      (ground.getAt [] t.cartan i)).length = t.rank :=
    (elim.length_vecScale _ _).trans (hcl i hi)
  have hnul : (poly.pnorm (elim.vecAdd nu0
      (elim.vecScale
        (BPair.ofNat (ground.getAt 0 ρv i))
        (ground.getAt [] t.cartan i)))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd _ _ t.rank hn0 hXl)
  have hmr1 : ground.getAt 0 ρv i = 1 :=
    letterOne t F hshape hgram hgsym hsp hrd hrho L hfam μ ρv hμl hkap
      hpos hi (hcl i hi) (hdg i hi) nu0 hn0 hn0mem hdomin
      (hcapL _ hmemL)
  have hki : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      i).oneValue (BPair.ofNat 1) := by
    refine BPair.oneValue_trans (hkap i hi) ?_
    rw [hmr1]
    exact BPair.oneValue_refl _
  have hyl : (poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      nu0)).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd _ _ t.rank hkl hn0)
  have hcr : (poly.neg (assembly.cartRowV t i)).length = t.rank :=
    (ground.length_map BPair.swap _).trans (assembly.cartRowV_length t i)
  have hrl : (sertables.reflAt t i
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))).length = t.rank := by
    rw [assembly.reflAt_shift t i hi _ hkl hki, poly.pnorm_length,
      elim.length_vecAdd _ _ t.rank hkl hcr]
  refine ⟨hmr1, ?_⟩
  refine assembly.addKey_solve t.rank _ _ _ hyl (poly.pnorm_pnorm _)
    hnul hrl (assembly.reflAt_norm t i _) ?_
  refine Eq.trans (poly.pnorm_congr _ _ ?_ ?_) rfl
  · rw [elim.length_vecAdd _ _ t.rank hrl hnul,
      elim.length_vecAdd _ _ t.rank hkl hn0]
  · refine poly.oneValue_of_entries _ _ ?_ (fun q hq => ?_)
    · rw [elim.length_vecAdd _ _ t.rank hrl hnul,
        elim.length_vecAdd _ _ t.rank hkl hn0]
    · have hqr : q < t.rank := by
        rw [elim.length_vecAdd _ _ t.rank hrl hnul] at hq
        exact hq
      have hA : (ground.getAt BPair.unit (sertables.reflAt t i
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))) q).oneValue
          (ground.getAt BPair.unit
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) q
            + (ground.getAt BPair.unit
                (ground.getAt [] t.cartan i) q).swap) := by
        exact reflEntry t hi _ hkl hki hqr
      have hB : (ground.getAt BPair.unit
          (poly.pnorm (elim.vecAdd nu0
            (elim.vecScale
              (BPair.ofNat (ground.getAt 0 ρv i))
              (ground.getAt [] t.cartan i)))) q).oneValue
          (ground.getAt BPair.unit nu0 q
            + ground.getAt BPair.unit
                (ground.getAt [] t.cartan i) q) := by
        refine BPair.oneValue_trans
          (poly.oneValue_getAt q (poly.pnorm_oneValue _)) ?_
        rw [elim.getAt_vecAdd _ _ q (by rw [hn0]; exact hqr)
            (by rw [hXl]; exact hqr),
          elim.getAt_vecScale _ _ q (by rw [hcl i hi]; exact hqr), hmr1]
        exact BPair.add_congr (BPair.oneValue_refl _)
          (BPair.ofNat_one_mul _)
      rw [elim.getAt_vecAdd _ _ q (by rw [hrl]; exact hqr)
          (by rw [hnul]; exact hqr),
        elim.getAt_vecAdd _ _ q (by rw [hkl]; exact hqr)
          (by rw [hn0]; exact hqr)]
      refine BPair.oneValue_trans (BPair.add_congr hA hB) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.add_comm _ _))
            (ground.unitOfOne (BPair.oneValue_refl
              (ground.getAt BPair.unit
                (ground.getAt [] t.cartan i) q))))) ?_
      exact BPair.add_unit _


/-- The letter's image at the odd grading reads the key's even
count, and at the even grading the key's odd count
(`thm:assembly`'s transport at the graded image list). -/
private theorem countReflT (t : gentable.Table)
    (Wl : List (List BPair × Bool))
    (hclose : assembly.wCloseRead t Wl)
    (hsqr : sertables.reflSquareRead t) {i : Nat} (hi : i < t.rank)
    (v : List BPair) (hvl : v.length = t.rank)
    (hvn : poly.pnorm v = v) :
    ground.countOf (sertables.reflAt t i v, true) Wl
      = ground.countOf (v, false) Wl :=
  assembly.wCount_refl t Wl hclose hsqr i hi v hvl hvn true

/-- The even grading's transport. -/
private theorem countReflF (t : gentable.Table)
    (Wl : List (List BPair × Bool))
    (hclose : assembly.wCloseRead t Wl)
    (hsqr : sertables.reflSquareRead t) {i : Nat} (hi : i < t.rank)
    (v : List BPair) (hvl : v.length = t.rank)
    (hvn : poly.pnorm v = v) :
    ground.countOf (sertables.reflAt t i v, false) Wl
      = ground.countOf (v, true) Wl :=
  assembly.wCount_refl t Wl hclose hsqr i hi v hvl hvn false

/-- `lem:serstable`(ii)'s row values at an abstract member vector,
series-uniform: at a dominant target the two convolution counts of
the graded image list against the `θ` content list read the target
content's own multiplicity on the even side and the letter fold on
the odd — the identity's tie alone at the even grading, one signed
read per simple letter at the raised content on the odd — the
leading members the displayed instances. -/
theorem rowValuesAt (t : gentable.Table) (F : sertables.FundData)
    (Wl : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (μ : List BPair) (ρv : List Nat)
    (nu0 : List BPair)
    (hμl : μ.length = t.rank)
    (hkap : ∀ i, i < t.rank → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i)))
    (hpos : ∀ k, k < t.rank → 1 ≤ ground.getAt 0 ρv k)
    (hcl : ∀ q, q < t.rank →
      (ground.getAt [] t.cartan q).length = t.rank)
    (hdg : ∀ q, q < t.rank → (ground.getAt BPair.unit
      (ground.getAt [] t.cartan q) q).oneValue (BPair.ofNat 2))
    (hoff : ∀ p q, p < t.rank → q < t.rank → ¬ q = p →
      ground.getAt BPair.unit (ground.getAt [] t.cartan p) q
        ≤ BPair.unit)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F)
    (hsqr : sertables.reflSquareRead t)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hrho : row.rhoLenRead t F)
    (hwsh : sertables.wShapeRead t Wl)
    (hclose : assembly.wCloseRead t Wl)
    (hdom : assembly.wDomAt t Wl wits
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
    (htop : assembly.wTopAt Wl
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
    (hksq : row.sqAtRead F Wl
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))))
    (hmsh : memberchar.mShapeRead t L) (hfam : row.thetaFamRead t L)
    (hn0pos : 0 < ground.countOf nu0 L)
    (hdomin : ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd μ nu0)) k)
    (hcapL : ∀ z ∈ L, sertables.dotB F z z ≤ BPair.ofNat (4 * F.scale)) :
    memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          nu0)) false
      = ground.countOf nu0 L
    ∧ memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          nu0)) true
      = letterFoldAt t ρv nu0 L := by
  have hn0mem := ground.mem_of_countOf_pos nu0 L hn0pos
  obtain ⟨hn0, hn0n⟩ := hmsh nu0 hn0mem
  have hkl : (poly.pnorm (elim.vecAdd μ
      (sertables.rhoV t))).length = t.rank := kapLen t μ hμl
  have hkn : poly.pnorm (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      = poly.pnorm (elim.vecAdd μ (sertables.rhoV t)) :=
    poly.pnorm_pnorm _
  have hyl : (poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
      nu0)).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd _ _ t.rank hkl hn0)
  have hyn : poly.pnorm (poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd μ (sertables.rhoV t))) nu0))
      = poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
        nu0) := poly.pnorm_pnorm _
  have hkapkey : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
        nu0)) (poly.neg nu0))
      = poly.pnorm (elim.vecAdd μ (sertables.rhoV t)) :=
    assembly.addKey_solve t.rank _ nu0 _ hyl hyn hn0 hkl hkn rfl
  have heven : ∀ nu, nu ∈ L →
      ground.countOf (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          nu0)) (poly.neg nu)), false) Wl
      = if nu0 = nu then 1 else 0 := by
    intro nu hnumem
    by_cases hz : nu0 = nu
    · rw [if_pos hz, ← hz, hkapkey]
      exact htop.1
    · rw [if_neg hz]
      match Nat.eq_zero_or_pos (ground.countOf (poly.pnorm
          (elim.vecAdd (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
            nu0)) (poly.neg nu)), false) Wl) with
      | Or.inl h => exact h
      | Or.inr hposW =>
        exfalso
        have hmemW := ground.mem_of_countOf_pos _ Wl hposW
        match tieWalk t F hshape hgram hgsym hsp hrd hrho Wl wits L hmsh
            hfam μ ρv hμl hkap hpos hcl hdg hoff hwsh hdom hksq nu0
            hn0mem hdomin hcapL nu hnumem false hmemW with
        | Or.inl h => exact hz h.1.symm
        | Or.inr ⟨i, hi, _, _, hveq⟩ =>
          rw [hveq, countReflF t Wl hclose hsqr hi _ hkl hkn,
            htop.2] at hposW
          exact absurd hposW (Nat.lt_irrefl 0)
  have hodd : ∀ nu, nu ∈ L →
      ground.countOf (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          nu0)) (poly.neg nu)), true) Wl
      = ground.famFold Nat.add 0 (fun i =>
          if poly.pnorm (elim.vecAdd nu0
            (elim.vecScale
              (BPair.ofNat (ground.getAt 0 ρv i))
              (ground.getAt [] t.cartan i))) = nu then 1 else 0)
          (List.range t.rank) := by
    intro nu hnumem
    match Nat.eq_zero_or_pos (ground.countOf (poly.pnorm
        (elim.vecAdd (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd μ (sertables.rhoV t)))
          nu0)) (poly.neg nu)), true) Wl) with
    | Or.inr hposW =>
      have hmemW := ground.mem_of_countOf_pos _ Wl hposW
      match tieWalk t F hshape hgram hgsym hsp hrd hrho Wl wits L hmsh
          hfam μ ρv hμl hkap hpos hcl hdg hoff hwsh hdom hksq nu0
          hn0mem hdomin hcapL nu hnumem true hmemW with
      | Or.inl h =>
        exfalso
        rw [h.2, htop.2] at hposW
        exact absurd hposW (Nat.lt_irrefl 0)
      | Or.inr ⟨i, hi, hmr, hnuE, hveq⟩ =>
        rw [hveq, countReflT t Wl hclose hsqr hi _ hkl hkn, htop.1]
        refine Eq.symm (Eq.trans
          (ground.famFold_congr_members Nat.add 0 _
            (fun q => if i = q then 1 else 0) (List.range t.rank)
            (fun q hq => ?_)) ?_)
        · have hqr : q < t.rank := ground.ltOfMem hq
          by_cases hiq : i = q
          · rw [if_pos hiq, ← hiq, if_pos hnuE.symm]
          · rw [if_neg hiq]
            by_cases hE : poly.pnorm (elim.vecAdd nu0
                (elim.vecScale
                  (BPair.ofNat (ground.getAt 0 ρv q))
                  (ground.getAt [] t.cartan q))) = nu
            · exfalso
              obtain ⟨hmrq, hveq2⟩ := letterKey t F hshape hgram hgsym
                hsp hrd hrho L hmsh hfam μ ρv hμl hkap hpos hcl hdg nu0
                hn0mem hdomin hcapL hqr (by rw [hE]; exact hnumem)
              rw [hE, hveq] at hveq2
              exact reflDistinct t μ ρv hμl hkap hdg hoff hi hqr hiq
                hmr hmrq hveq2.symm
            · rw [if_neg hE]
        · rw [← ground.countOf_fold i (List.range t.rank),
            ground.countOf_range i t.rank, if_pos hi]
    | Or.inl h0 =>
      rw [h0]
      refine Eq.symm (Eq.trans (ground.famFold_congr_members Nat.add 0 _
        (fun _ => 0) (List.range t.rank) (fun q hq => ?_))
        (ground.famFold_zero (fun _ : Nat => (0 : Nat)) (fun _ => rfl)
          (List.range t.rank)))
      have hqr : q < t.rank := ground.ltOfMem hq
      by_cases hE : poly.pnorm (elim.vecAdd nu0
          (elim.vecScale
            (BPair.ofNat (ground.getAt 0 ρv q))
            (ground.getAt [] t.cartan q))) = nu
      · exfalso
        obtain ⟨hmrq, hveq2⟩ := letterKey t F hshape hgram hgsym hsp hrd
          hrho L hmsh hfam μ ρv hμl hkap hpos hcl hdg nu0 hn0mem hdomin
          hcapL hqr (by rw [hE]; exact hnumem)
        rw [hE] at hveq2
        rw [hveq2, countReflT t Wl hclose hsqr hqr _ hkl hkn,
          htop.1] at h0
        exact Nat.noConfusion h0
      · rw [if_neg hE]
  refine ⟨?_, ?_⟩
  · rw [memberchar.convCount_wFold t Wl L hwsh hmsh _ hyl hyn false]
    refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
      (fun nu => if nu0 = nu then 1 else 0) L
      (fun nu hnu => heven nu (ground.mem_of_countOf_pos nu L hnu))) ?_
    exact (ground.countOf_fold nu0 L).symm
  · rw [memberchar.convCount_wFold t Wl L hwsh hmsh _ hyl hyn true]
    refine Eq.trans (ground.famFold_congr_members Nat.add 0 _ _ L
      (fun nu hnu => hodd nu (ground.mem_of_countOf_pos nu L hnu))) ?_
    rw [ground.famFold_swap (fun (nu : List BPair) (i : Nat) =>
      if poly.pnorm (elim.vecAdd nu0
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 ρv i))
          (ground.getAt [] t.cartan i))) = nu then 1 else 0)
      L (List.range t.rank)]
    show ground.famFold Nat.add 0 _ (List.range t.rank)
      = letterFoldAt t ρv nu0 L
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range t.rank) (fun i _ => ?_)
    exact (ground.countOf_fold _ L).symm

/-! ## The content cap: the fold families' own squares

`lem:serstable`(ii) reads the tie analysis against the `θ` content
list's squares, and `con:sertables`' displayed lengths cap them:
a positive member's cleared form square `formNum t f f` sits at or
below four at every series' fold family, so the cap is a derived
read at the tables and never a hypothesis.

The reads run at the count pair.  A fold's coroot value at a key is
the doubled entry against the neighbouring entries' fold — the
column kit's own count-pair reads `colB`/`colC`/`colD` — so the
form's term at the key is that pair scaled by the entry and the
key's length (`cellScale`), and the family's terms collect at the
fold's own ends: the interior keys' contributions cancel between
the two counts, and what survives is the displayed pair.
-/

/-- The scaled count pair: an entry and a key's length scale a
coroot pair's two counts. -/
private theorem cellScale (c p n m : Nat) :
    (BPair.ofNat c * BPair.ofCounts p n * BPair.ofNat m).oneValue
      (BPair.ofCounts (c * p * m) (c * n * m)) := by
  show (BPair.ofNat c * (BPair.ofNat p + (BPair.ofNat n).swap)
      * BPair.ofNat m).oneValue _
  rw [BPair.left_distrib, BPair.right_distrib, BPair.mul_swap,
    BPair.swap_mul]
  refine BPair.add_congr ?_ ?_
  · exact BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.ofNat_mul (c * p) m)
        (BPair.mul_congr_left (BPair.ofNat_mul c p)))
  · exact ground.swap_congr (BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.ofNat_mul (c * n) m)
        (BPair.mul_congr_left (BPair.ofNat_mul c n))))

/-- The occupancy window's entry at a key, the fold families' one
constructor read as a function. -/
def fDiff (a b k : Nat) : Nat :=
  if a ≤ k && k < b then 1 else 0

/-- The window's entry inside the window is one. -/
theorem fDiff_in (a b k : Nat) (h1 : a ≤ k) (h2 : k < b) :
    fDiff a b k = 1 := by
  show (if (decide (a ≤ k) && decide (k < b)) = true then (1 : Nat)
    else 0) = 1
  rw [decide_eq_true h1, decide_eq_true h2]
  rfl

/-- The window's entry below the window is vacant. -/
theorem fDiff_lo (a b k : Nat) (h : ¬ a ≤ k) :
    fDiff a b k = 0 := by
  show (if (decide (a ≤ k) && decide (k < b)) = true then (1 : Nat)
    else 0) = 0
  rw [decide_eq_false h]
  rfl

/-- The window's entry at or above the window's top is vacant. -/
theorem fDiff_hi (a b k : Nat) (h : ¬ k < b) :
    fDiff a b k = 0 := by
  show (if (decide (a ≤ k) && decide (k < b)) = true then (1 : Nat)
    else 0) = 0
  rw [decide_eq_false h, andF]
  rfl


/-- A window entry sits at or below one. -/
theorem fDiff_le1 (a b k : Nat) : fDiff a b k ≤ 1 := by
  by_cases h1 : a ≤ k
  · by_cases h2 : k < b
    · rw [fDiff_in a b k h1 h2]
      exact Nat.le_refl 1
    · rw [fDiff_hi a b k h2]
      exact Nat.zero_le 1
  · rw [fDiff_lo a b k h1]
    exact Nat.zero_le 1

/-- The difference family is the window entry's range map. -/
private theorem fDiff_eq (l a b : Nat) :
    sertables.diffFold l a b = (List.range l).map (fDiff a b) := rfl

/-- The form's cap off the count-pair reads: the terms' two counts
fold to the displayed pair, and the pair's cleared count is the
cap. -/
private theorem formCap (t : gentable.Table) (l : Nat) (hrk : t.rank = l)
    (F nb Ln A N : Nat → Nat) (C : Nat)
    (hcol : ∀ j, j < l →
      (corootAt t ((List.range l).map F) j).oneValue
        (BPair.ofCounts (2 * F j) (nb j)))
    (hlen : ∀ j, j < l → ground.getAt 0 t.lenNums j = Ln j)
    (hnat : ∀ j, j < l →
      F j * (2 * F j) * Ln j + N j = A j + F j * nb j * Ln j)
    (hsum : ground.famFold Nat.add 0 A (List.range l)
      = C + ground.famFold Nat.add 0 N (List.range l))
    (hC : C ≤ 4) :
    gentable.formNum t ((List.range l).map F) ((List.range l).map F)
      ≤ BPair.ofNat 4 := by
  have hread : (gentable.formNum t ((List.range l).map F)
      ((List.range l).map F)).oneValue (BPair.ofNat C) := by
    show (BPair.sum ((List.range t.rank).map (fun j =>
      BPair.ofNat (ground.getAt 0 ((List.range l).map F) j)
        * corootAt t ((List.range l).map F) j
        * BPair.ofNat (ground.getAt 0 t.lenNums j)))).oneValue _
    rw [hrk]
    refine BPair.oneValue_trans (BPair.sum_map _ (List.range l)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun j => BPair.ofCounts (A j) (N j)) (List.range l)
        (fun j hj => ?_)) ?_
    · have hjl : j < l := ground.ltOfMem hj
      rw [ground.getAt_map_range 0 F l j, if_pos hjl, hlen j hjl]
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr (BPair.oneValue_refl _) (hcol j hjl))
          (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans
        (cellScale (F j) (2 * F j) (nb j) (Ln j)) ?_
      exact BPair.ofCounts_crossed (hnat j hjl)
    · refine BPair.oneValue_trans
        (BPair.oneValue_symm (ground.foldB_ofCounts A N (List.range l))) ?_
      exact countsRead _ _ C hsum
  exact ground.leB_congr_left (BPair.oneValue_symm hread) (ground.leB_ofNat hC)

/-! ### The `B` series' fold families -/

/-- The `B` key's length. -/
private def lnB (l k : Nat) : Nat := if k + 1 == l then 1 else 2

/-- The `B` column's neighbour fold at a key: the chain's two
neighbours, the last key's edge doubled. -/
def nbB (l : Nat) (F : Nat → Nat) : Nat → Nat
  | 0 => if 1 < l then F 1 else 0
  | m + 1 => if m + 2 == l then 2 * F m else F m + F (m + 2)

/-- The `B` neighbour fold at the first key is the second key's
entry inside the rank. -/
theorem nbB_zero (l : Nat) (F : Nat → Nat) :
    nbB l F 0 = if 1 < l then F 1 else 0 := rfl

/-- The `B` neighbour fold past the first key: the doubled lower
neighbour at the short last edge, the two neighbours' sum
elsewhere. -/
theorem nbB_succ (l : Nat) (F : Nat → Nat) (m : Nat) :
    nbB l F (m + 1)
      = if m + 2 == l then 2 * F m else F m + F (m + 2) := rfl

/-- The `B` column's count-pair read at every key. -/
private theorem colB (l : Nat) (F : Nat → Nat) : ∀ j, j < l →
    (corootAt (sertables.tableB l) ((List.range l).map F) j).oneValue
      (BPair.ofCounts (2 * F j) (nbB l F j))
  | 0, hj => colB0c l hj F
  | m + 1, hj => by
    rw [nbB_succ]
    by_cases ht : m + 2 = l
    · rw [if_pos (ground.eqBeqOf ht)]
      exact colBtopc l m ht F
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      exact colBmidc l m
        (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht) F

private theorem lnB_read (l : Nat) : ∀ j, j < l →
    ground.getAt 0 (sertables.tableB l).lenNums j = lnB l j :=
  fun j hj => sertables.lensB_at l j hj

/-- The vacant entry's term identity: an unoccupied key carries no
count on either side. -/
private theorem natVac (x y : Nat) :
    (0 : Nat) * (2 * 0) * x + 0 = (0 + 0) + 0 * y * x := by
  rw [Nat.zero_mul (2 * 0), Nat.zero_mul y, Nat.zero_mul x]

/-- The `B` difference family's term identity at every key: the two
counts part at the window's own ends. -/
private theorem natDiffB (l a c : Nat) (hac : a ≤ c) (hcl : c + 1 < l) :
    ∀ j, j < l →
      fDiff a (c + 1) j * (2 * fDiff a (c + 1) j) * lnB l j + 0
        = ((if a == j then 2 else 0) + (if c == j then 2 else 0))
          + fDiff a (c + 1) j * nbB l (fDiff a (c + 1)) j * lnB l j
  | 0, _ => by
    have h1l : 1 < l :=
      Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le c)) hcl
    match Nat.lt_or_ge 0 a with
    | .inr hle =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hle
      have hln : lnB l 0 = 2 :=
        if_neg (fun hb => Nat.ne_of_lt h1l (ground.beqEqOf hb))
      rw [fDiff_in a (c + 1) 0 hle (Nat.succ_pos c), hln, nbB_zero,
        if_pos h1l, ground.eqBeqOf ha]
      match Nat.eq_zero_or_pos c with
      | .inl hc0 =>
        rw [ground.eqBeqOf hc0,
          fDiff_hi a (c + 1) 1 (fun hx =>
            Nat.lt_irrefl 1 (by rw [hc0] at hx; exact hx))]
        rfl
      | .inr hcp =>
        rw [ground.neBeqOf (fun hx : c = 0 =>
            Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hcp
              (Nat.le_of_eq hx))),
          fDiff_in a (c + 1) 1 (ha ▸ Nat.zero_le 1)
            (Nat.succ_lt_succ hcp)]
        rfl
    | .inl hlt =>
      rw [fDiff_lo a (c + 1) 0 (fun hx =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt hx)),
        ground.neBeqOf (fun hx : a = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt
            (Nat.le_of_eq hx))),
        ground.neBeqOf (fun hx : c = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt
            (Nat.le_trans hac (Nat.le_of_eq hx))))]
      exact natVac _ _
  | m + 1, _ => by
    match Nat.lt_or_ge (m + 1) (c + 1) with
    | .inl hhi =>
      have hjc : m + 1 ≤ c := Nat.le_of_lt_succ hhi
      have hjl : ¬ m + 1 + 1 = l :=
        Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_succ hjc) hcl)
      match Nat.lt_or_ge (m + 1) a with
      | .inl hlt =>
        rw [fDiff_lo a (c + 1) (m + 1) (fun hx =>
            Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt hx)),
          ground.neBeqOf (fun hx : a = m + 1 =>
            Nat.lt_irrefl (m + 1)
              (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
          ground.neBeqOf (fun hx : c = m + 1 =>
            Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt
              (Nat.le_trans hac (Nat.le_of_eq hx))))]
        exact natVac _ _
      | .inr hlo =>
        rw [fDiff_in a (c + 1) (m + 1) hlo hhi,
          show lnB l (m + 1) = 2 from
            if_neg (fun hb => hjl (ground.beqEqOf hb)),
          nbB_succ, if_neg (fun hb => hjl (ground.beqEqOf hb))]
        match Nat.lt_or_ge m a with
        | .inr hma =>
          rw [ground.neBeqOf (fun hx : a = m + 1 =>
              Nat.not_succ_le_self m
                (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
            fDiff_in a (c + 1) m hma
              (Nat.lt_trans (Nat.lt_succ_self m) hhi)]
          match Nat.lt_or_ge (m + 1) c with
          | .inl hmc =>
            rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl c (hx ▸ hmc)),
              fDiff_in a (c + 1) (m + 2)
                (Nat.le_trans hma (Nat.le_succ_of_le (Nat.le_succ m)))
                (Nat.succ_lt_succ hmc)]
            rfl
          | .inr hcm =>
            have hce : c = m + 1 := Nat.le_antisymm hcm hjc
            rw [ground.eqBeqOf hce,
              fDiff_hi a (c + 1) (m + 2) (fun hx =>
                Nat.lt_irrefl (m + 2) (by rw [hce] at hx; exact hx))]
            rfl
        | .inl hma =>
          have hae : a = m + 1 :=
            Nat.le_antisymm hlo (Nat.succ_le_of_lt hma)
          rw [ground.eqBeqOf hae,
            fDiff_lo a (c + 1) m (fun hx =>
              Nat.lt_irrefl m (Nat.lt_of_lt_of_le hma hx))]
          match Nat.lt_or_ge (m + 1) c with
          | .inl hmc =>
            rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl c (hx ▸ hmc)),
              fDiff_in a (c + 1) (m + 2)
                (Nat.le_trans hlo (Nat.le_succ (m + 1)))
                (Nat.succ_lt_succ hmc)]
            rfl
          | .inr hcm =>
            have hce : c = m + 1 := Nat.le_antisymm hcm hjc
            rw [ground.eqBeqOf hce,
              fDiff_hi a (c + 1) (m + 2) (fun hx =>
                Nat.lt_irrefl (m + 2) (by rw [hce] at hx; exact hx))]
            rfl
    | .inr hge =>
      rw [fDiff_hi a (c + 1) (m + 1) (fun hx =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hx hge)),
        ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_eq hx.symm) hac)
              (Nat.lt_succ_self c)) hge)),
        ground.neBeqOf (fun hx : c = m + 1 =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le
            (Nat.lt_succ_of_le (Nat.le_of_eq hx.symm)) hge))]
      exact natVac _ _

/-- The `B` difference family's square: the long root's cleared
form at four. -/
private theorem capDiffB (l a b : Nat) (hab : a < b) (hbl : b < l) :
    gentable.formNum (sertables.tableB l) (sertables.diffFold l a b)
        (sertables.diffFold l a b) ≤ BPair.ofNat 4 := by
  match b, hab, hbl with
  | c + 1, hab, hbl =>
    have hac : a ≤ c := Nat.le_of_lt_succ hab
    have hal : a < l := Nat.lt_of_le_of_lt hac
      (Nat.lt_trans (Nat.lt_succ_self c) hbl)
    have hcl : c < l := Nat.lt_trans (Nat.lt_succ_self c) hbl
    rw [fDiff_eq l a (c + 1)]
    refine formCap (sertables.tableB l) l rfl (fDiff a (c + 1))
      (nbB l (fDiff a (c + 1))) (lnB l)
      (fun k => (if a == k then 2 else 0) + (if c == k then 2 else 0))
      (fun _ => 0) 4 (colB l (fDiff a (c + 1))) (lnB_read l)
      (natDiffB l a c hac hbl) ?_ (Nat.le_refl 4)
    rw [dfold2 l a c 2 2, if_pos hal, if_pos hcl,
      ground.famFold_rangeZero (fun _ => 0) l (fun _ _ => rfl)]

/-- The `B` short family's term identity at every key. -/
private theorem natShortB (l a : Nat) :
    ∀ j, j < l →
      fDiff a l j * (2 * fDiff a l j) * lnB l j + 0
        = (if a == j then 2 else 0)
          + fDiff a l j * nbB l (fDiff a l) j * lnB l j
  | 0, hj => by
    match Nat.lt_or_ge 0 a with
    | .inl hlt =>
      rw [fDiff_lo a l 0 (fun hx =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt hx)),
        ground.neBeqOf (fun hx : a = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx)))]
      exact natVac _ _
    | .inr hle =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hle
      rw [fDiff_in a l 0 hle hj, ground.eqBeqOf ha, nbB_zero]
      match Nat.lt_or_ge 1 l with
      | .inl h1l =>
        rw [if_pos h1l,
          show lnB l 0 = 2 from
            if_neg (fun hb => Nat.ne_of_lt h1l (ground.beqEqOf hb)),
          fDiff_in a l 1 (ha ▸ Nat.zero_le 1) h1l]
        rfl
      | .inr hle1 =>
        have hl1 : (0 : Nat) + 1 = l := Nat.le_antisymm hj hle1
        rw [if_neg (fun hc : 1 < l => Nat.lt_irrefl 1
            (Nat.lt_of_lt_of_le hc hle1)),
          show lnB l 0 = 1 from if_pos (ground.eqBeqOf hl1)]
        rfl
  | m + 1, hj => by
    match Nat.lt_or_ge (m + 1) a with
    | .inl hlt =>
      rw [fDiff_lo a l (m + 1) (fun hx =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt hx)),
        ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.lt_irrefl (m + 1)
            (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx)))]
      exact natVac _ _
    | .inr hlo =>
      rw [fDiff_in a l (m + 1) hlo hj, nbB_succ]
      match Nat.lt_or_ge m a with
      | .inl hma =>
        have hae : a = m + 1 :=
          Nat.le_antisymm hlo (Nat.succ_le_of_lt hma)
        rw [ground.eqBeqOf hae,
          fDiff_lo a l m (fun hx =>
            Nat.lt_irrefl m (Nat.lt_of_lt_of_le hma hx))]
        by_cases ht : m + 2 = l
        · rw [if_pos (ground.eqBeqOf ht),
            show lnB l (m + 1) = 1 from if_pos (ground.eqBeqOf ht)]
          rfl
        · have ht2 : m + 2 < l :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht
          rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
            show lnB l (m + 1) = 2 from
              if_neg (fun hb => ht (ground.beqEqOf hb)),
            fDiff_in a l (m + 2)
              (Nat.le_trans hlo (Nat.le_succ (m + 1))) ht2]
          rfl
      | .inr hma =>
        rw [ground.neBeqOf (fun hx : a = m + 1 =>
            Nat.not_succ_le_self m
              (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
          fDiff_in a l m hma (Nat.lt_trans (Nat.lt_succ_self m) hj)]
        by_cases ht : m + 2 = l
        · rw [if_pos (ground.eqBeqOf ht),
            show lnB l (m + 1) = 1 from if_pos (ground.eqBeqOf ht)]
          rfl
        · have ht2 : m + 2 < l :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht
          rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
            show lnB l (m + 1) = 2 from
              if_neg (fun hb => ht (ground.beqEqOf hb)),
            fDiff_in a l (m + 2)
              (Nat.le_trans hlo (Nat.le_succ (m + 1))) ht2]
          rfl

/-- The `B` short family's square: the short root's cleared form at
two. -/
private theorem capShortB (l a : Nat) (hal : a < l) :
    gentable.formNum (sertables.tableB l) (sertables.shortFold l a)
        (sertables.shortFold l a) ≤ BPair.ofNat 4 := by
  rw [show sertables.shortFold l a = (List.range l).map (fDiff a l)
      from rfl]
  refine formCap (sertables.tableB l) l rfl (fDiff a l)
    (nbB l (fDiff a l)) (lnB l)
    (fun k => if a == k then 2 else 0)
    (fun _ => 0) 2 (colB l (fDiff a l)) (lnB_read l)
    (natShortB l a) ?_ (by decide +kernel)
  rw [pickR a 2 l, if_pos hal,
    ground.famFold_rangeZero (fun _ => 0) l (fun _ _ => rfl)]

/-- The `B` sum family's entry at a key. -/
def fSumB (l a b k : Nat) : Nat :=
  fDiff a b k + (fDiff b l k + fDiff b l k)

/-- The `B` sum family is its entry function's range map. -/
theorem fSumB_eq (l a b : Nat) :
    sertables.sumFoldB l a b = (List.range l).map (fSumB l a b) := by
  show List.zipWith (fun x y => x + y) (sertables.ind l a b)
      (List.zipWith (fun x y => x + y) (sertables.ind l b l)
        (sertables.ind l b l))
    = (List.range l).map (fSumB l a b)
  rw [show sertables.ind l b l = (List.range l).map (fDiff b l) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff b l) (fDiff b l) (List.range l),
    show sertables.ind l a b = (List.range l).map (fDiff a b) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff a b)
      (fun k => fDiff b l k + fDiff b l k) (List.range l)]
  rfl

/-- The `B` sum family's entry below both windows is vacant. -/
theorem fSumB_lo (l a b k : Nat) (h1 : ¬ a ≤ k) (h2 : ¬ b ≤ k) :
    fSumB l a b k = 0 := by
  show fDiff a b k + (fDiff b l k + fDiff b l k) = 0
  rw [fDiff_lo a b k h1, fDiff_lo b l k h2]

/-- The `B` sum family's entry inside the narrow window is one. -/
theorem fSumB_mid (l a b k : Nat) (h1 : a ≤ k) (h2 : k < b) :
    fSumB l a b k = 1 := by
  show fDiff a b k + (fDiff b l k + fDiff b l k) = 1
  rw [fDiff_in a b k h1 h2, fDiff_lo b l k (fun hc =>
    Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hc))]

/-- The `B` sum family's entry at or above the pair's top, inside
the rank, is two. -/
theorem fSumB_hi (l a b k : Nat) (h1 : b ≤ k) (h2 : k < l) :
    fSumB l a b k = 2 := by
  show fDiff a b k + (fDiff b l k + fDiff b l k) = 2
  rw [fDiff_hi a b k (fun hc =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le hc h1)),
    fDiff_in b l k h1 h2]

/-- The `B` sum family's term identity at every key. -/
private theorem natSumB (l a c : Nat) (hac : a ≤ c) (hcl : c + 1 < l) :
    ∀ j, j < l →
      fSumB l a (c + 1) j * (2 * fSumB l a (c + 1) j) * lnB l j
          + (if c == j then 2 else 0)
        = ((if a == j then 2 else 0) + (if c + 1 == j then 4 else 0))
          + fSumB l a (c + 1) j * nbB l (fSumB l a (c + 1)) j * lnB l j
  | 0, _ => by
    have h1l : 1 < l :=
      Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le c)) hcl
    have hln : lnB l 0 = 2 :=
      if_neg (fun hb => Nat.ne_of_lt h1l (ground.beqEqOf hb))
    match Nat.lt_or_ge 0 a with
    | .inl hlt =>
      rw [fSumB_lo l a (c + 1) 0 (fun hx =>
            Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt hx))
          (fun hx => Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le
            (Nat.succ_pos c) hx)),
        ground.neBeqOf (fun hx : a = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
        ground.neBeqOf (fun hx : c = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt
            (Nat.le_trans hac (Nat.le_of_eq hx)))),
        ground.neBeqOf (fun hx : c + 1 = 0 => Nat.noConfusion hx)]
      exact natVac _ _
    | .inr hle =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hle
      rw [fSumB_mid l a (c + 1) 0 hle (Nat.succ_pos c), hln, nbB_zero,
        if_pos h1l, ground.eqBeqOf ha,
        ground.neBeqOf (fun hx : c + 1 = 0 => Nat.noConfusion hx)]
      match Nat.eq_zero_or_pos c with
      | .inl hc0 =>
        rw [ground.eqBeqOf hc0,
          fSumB_hi l a (c + 1) 1 (Nat.le_of_eq (congrArg (· + 1) hc0))
            h1l]
        rfl
      | .inr hcp =>
        rw [ground.neBeqOf (fun hx : c = 0 =>
            Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hcp (Nat.le_of_eq hx))),
          fSumB_mid l a (c + 1) 1 (ha ▸ Nat.zero_le 1)
            (Nat.succ_lt_succ hcp)]
        rfl
  | m + 1, hj => by
    match Nat.lt_or_ge (m + 1) (c + 1) with
    | .inl hhi =>
      have hjc : m + 1 ≤ c := Nat.le_of_lt_succ hhi
      have hjl : ¬ m + 1 + 1 = l :=
        Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_succ hjc) hcl)
      have hln : lnB l (m + 1) = 2 :=
        if_neg (fun hb => hjl (ground.beqEqOf hb))
      have hbne : ¬ c + 1 = m + 1 := fun hx =>
        Nat.not_succ_le_self m
          (Nat.le_trans hjc (Nat.le_of_eq (Nat.succ.inj hx)))
      match Nat.lt_or_ge (m + 1) a with
      | .inl hlt =>
        rw [fSumB_lo l a (c + 1) (m + 1) (fun hx =>
              Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt hx))
            (fun hx => Nat.lt_irrefl (m + 1)
              (Nat.lt_of_lt_of_le hhi hx)),
          ground.neBeqOf (fun hx : a = m + 1 =>
            Nat.lt_irrefl (m + 1)
              (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
          ground.neBeqOf (fun hx : c = m + 1 =>
            Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt
              (Nat.le_trans hac (Nat.le_of_eq hx)))),
          ground.neBeqOf hbne]
        exact natVac _ _
      | .inr hlo =>
        rw [fSumB_mid l a (c + 1) (m + 1) hlo hhi, hln, nbB_succ,
          if_neg (fun hb => hjl (ground.beqEqOf hb)),
          ground.neBeqOf hbne]
        have hmb : ¬ c + 1 ≤ m := fun hx =>
          Nat.not_succ_le_self m
            (Nat.le_trans (Nat.le_trans hjc (Nat.le_succ c)) hx)
        match Nat.lt_or_ge m a with
        | .inl hma =>
          have hae : a = m + 1 :=
            Nat.le_antisymm hlo (Nat.succ_le_of_lt hma)
          rw [ground.eqBeqOf hae,
            fSumB_lo l a (c + 1) m (fun hx =>
              Nat.lt_irrefl m (Nat.lt_of_lt_of_le hma hx)) hmb]
          match Nat.lt_or_ge (m + 1) c with
          | .inl hmc =>
            rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                  (Nat.le_of_eq hx))),
              fSumB_mid l a (c + 1) (m + 2)
                (Nat.le_trans hlo (Nat.le_succ (m + 1)))
                (Nat.succ_lt_succ hmc)]
            rfl
          | .inr hcm =>
            have hce : c = m + 1 := Nat.le_antisymm hcm hjc
            rw [ground.eqBeqOf hce,
              fSumB_hi l a (c + 1) (m + 2)
                (Nat.le_of_eq (congrArg (· + 1) hce))
                (by rw [hce] at hcl; exact hcl)]
            rfl
        | .inr hma =>
          rw [ground.neBeqOf (fun hx : a = m + 1 =>
              Nat.not_succ_le_self m
                (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
            fSumB_mid l a (c + 1) m hma
              (Nat.lt_trans (Nat.lt_succ_self m) hhi)]
          match Nat.lt_or_ge (m + 1) c with
          | .inl hmc =>
            rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                  (Nat.le_of_eq hx))),
              fSumB_mid l a (c + 1) (m + 2)
                (Nat.le_trans hlo (Nat.le_succ (m + 1)))
                (Nat.succ_lt_succ hmc)]
            rfl
          | .inr hcm =>
            have hce : c = m + 1 := Nat.le_antisymm hcm hjc
            rw [ground.eqBeqOf hce,
              fSumB_hi l a (c + 1) (m + 2)
                (Nat.le_of_eq (congrArg (· + 1) hce))
                (by rw [hce] at hcl; exact hcl)]
            rfl
    | .inr hge =>
      have hcm : c ≤ m := Nat.le_of_succ_le_succ hge
      rw [fSumB_hi l a (c + 1) (m + 1) hge hj, nbB_succ,
        ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.not_succ_le_self m (Nat.le_trans
            (Nat.le_trans (Nat.le_of_eq hx.symm) hac) hcm)),
        ground.neBeqOf (fun hx : c = m + 1 =>
          Nat.not_succ_le_self m
            (Nat.le_trans (Nat.le_of_eq hx.symm) hcm))]
      match Nat.lt_or_ge c m with
      | .inr hmc =>
        have hce : c = m := Nat.le_antisymm hcm hmc
        rw [ground.eqBeqOf (congrArg (· + 1) hce),
          fSumB_mid l a (c + 1) m (hce ▸ hac) (Nat.lt_succ_of_le hmc)]
        by_cases ht : m + 2 = l
        · rw [if_pos (ground.eqBeqOf ht),
            show lnB l (m + 1) = 1 from if_pos (ground.eqBeqOf ht)]
          rfl
        · have ht2 : m + 2 < l :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht
          rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
            show lnB l (m + 1) = 2 from
              if_neg (fun hb => ht (ground.beqEqOf hb)),
            fSumB_hi l a (c + 1) (m + 2)
              (Nat.le_trans hge (Nat.le_succ (m + 1))) ht2]
          rfl
      | .inl hlt =>
        rw [ground.neBeqOf (fun hx : c + 1 = m + 1 =>
            Nat.lt_irrefl c (Nat.lt_of_lt_of_le hlt
              (Nat.le_of_eq (Nat.succ.inj hx).symm))),
          fSumB_hi l a (c + 1) m hlt
            (Nat.lt_trans (Nat.lt_succ_self m) hj)]
        by_cases ht : m + 2 = l
        · rw [if_pos (ground.eqBeqOf ht),
            show lnB l (m + 1) = 1 from if_pos (ground.eqBeqOf ht)]
          rfl
        · have ht2 : m + 2 < l :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht
          rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
            show lnB l (m + 1) = 2 from
              if_neg (fun hb => ht (ground.beqEqOf hb)),
            fSumB_hi l a (c + 1) (m + 2)
              (Nat.le_trans hge (Nat.le_succ (m + 1))) ht2]
          rfl

/-- The `B` sum family's square: the long root's cleared form at
four. -/
private theorem capSumB (l a b : Nat) (hab : a < b) (hbl : b < l) :
    gentable.formNum (sertables.tableB l) (sertables.sumFoldB l a b)
        (sertables.sumFoldB l a b) ≤ BPair.ofNat 4 := by
  match b, hab, hbl with
  | c + 1, hab, hbl =>
    have hac : a ≤ c := Nat.le_of_lt_succ hab
    have hal : a < l := Nat.lt_of_le_of_lt hac
      (Nat.lt_trans (Nat.lt_succ_self c) hbl)
    have hcl : c < l := Nat.lt_trans (Nat.lt_succ_self c) hbl
    rw [fSumB_eq l a (c + 1)]
    refine formCap (sertables.tableB l) l rfl (fSumB l a (c + 1))
      (nbB l (fSumB l a (c + 1))) (lnB l)
      (fun k => (if a == k then 2 else 0) + (if c + 1 == k then 4 else 0))
      (fun k => if c == k then 2 else 0) 4
      (colB l (fSumB l a (c + 1))) (lnB_read l)
      (natSumB l a c hac hbl) ?_ (Nat.le_refl 4)
    rw [dfold2 l a (c + 1) 2 4, if_pos hal, if_pos hbl,
      pickR c 2 l, if_pos hcl]

/-! ### The `C` series' fold families -/

/-- The `C` key's length. -/
private def lnC (l k : Nat) : Nat := if k + 1 == l then 2 else 1

/-- The `C` column's neighbour fold at a key: the chain's two
neighbours, the edge out of the long last key doubled. -/
def nbC (l : Nat) (F : Nat → Nat) : Nat → Nat
  | 0 => if 2 == l then 2 * F 1 else if 1 < l then F 1 else 0
  | m + 1 =>
    if m + 2 == l then F m
    else if m + 3 == l then F m + 2 * F (m + 2)
    else F m + F (m + 2)

/-- The `C` neighbour fold at the first key: the second key's entry
doubled at the rank two, that entry alone inside a longer rank, and
the vacant count at the rank one. -/
theorem nbC_zero (l : Nat) (F : Nat → Nat) :
    nbC l F 0 = if 2 == l then 2 * F 1 else if 1 < l then F 1 else 0 :=
  rfl

/-- The `C` neighbour fold past the first key: the lower neighbour
alone at the last key, the doubled upper neighbour beside the lower
one at the key below it, the two neighbours' sum elsewhere. -/
theorem nbC_succ (l : Nat) (F : Nat → Nat) (m : Nat) :
    nbC l F (m + 1)
      = if m + 2 == l then F m
        else if m + 3 == l then F m + 2 * F (m + 2)
        else F m + F (m + 2) := rfl

/-- The `C` column's count-pair read at every key. -/
private theorem colC (l : Nat) (F : Nat → Nat) : ∀ j, j < l →
    (corootAt (sertables.tableC l) ((List.range l).map F) j).oneValue
      (BPair.ofCounts (2 * F j) (nbC l F j))
  | 0, hj => by
    rw [nbC_zero]
    by_cases he : 2 = l
    · rw [if_pos (ground.eqBeqOf he)]
      exact colC0ec l he F
    · rw [if_neg (fun hb => he (ground.beqEqOf hb))]
      exact colC0dc l hj he F
  | m + 1, hj => by
    rw [nbC_succ]
    by_cases ht : m + 2 = l
    · rw [if_pos (ground.eqBeqOf ht)]
      exact colCtopc l m ht F
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      have h2 : m + 2 < l := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht
      by_cases he3 : m + 3 = l
      · rw [if_pos (ground.eqBeqOf he3)]
        exact colCmec l m he3 F
      · rw [if_neg (fun hb => he3 (ground.beqEqOf hb))]
        exact colCmdc l m
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h2) he3) F

private theorem lnC_read (l : Nat) : ∀ j, j < l →
    ground.getAt 0 (sertables.tableC l).lenNums j = lnC l j :=
  fun j hj => sertables.lensC_at l j hj

/-- The `C` difference family's term identity at every key. -/
private theorem natDiffC (l a c : Nat) (hac : a ≤ c) (hcl : c + 1 < l) :
    ∀ j, j < l →
      fDiff a (c + 1) j * (2 * fDiff a (c + 1) j) * lnC l j + 0
        = ((if a == j then 1 else 0) + (if c == j then 1 else 0))
          + fDiff a (c + 1) j * nbC l (fDiff a (c + 1)) j * lnC l j
  | 0, _ => by
    have h1l : 1 < l :=
      Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le c)) hcl
    match Nat.lt_or_ge 0 a with
    | .inl hlt =>
      rw [fDiff_lo a (c + 1) 0 (fun hx =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt hx)),
        ground.neBeqOf (fun hx : a = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
        ground.neBeqOf (fun hx : c = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt
            (Nat.le_trans hac (Nat.le_of_eq hx))))]
      exact natVac _ _
    | .inr hle =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hle
      have hln : lnC l 0 = 1 :=
        if_neg (fun hb => Nat.ne_of_lt h1l (ground.beqEqOf hb))
      rw [fDiff_in a (c + 1) 0 hle (Nat.succ_pos c), hln, nbC_zero,
        ground.eqBeqOf ha]
      by_cases he2 : 2 = l
      · have hc2 : c + 1 < 2 := by rw [← he2] at hcl; exact hcl
        have hc0 : c = 0 := Nat.eq_zero_of_le_zero
          (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ hc2))
        rw [if_pos (ground.eqBeqOf he2), ground.eqBeqOf hc0,
          fDiff_hi a (c + 1) 1 (fun hx =>
            Nat.lt_irrefl 1 (by rw [hc0] at hx; exact hx))]
        rfl
      · rw [if_neg (fun hb => he2 (ground.beqEqOf hb)), if_pos h1l]
        match Nat.eq_zero_or_pos c with
        | .inl hc0 =>
          rw [ground.eqBeqOf hc0,
            fDiff_hi a (c + 1) 1 (fun hx =>
              Nat.lt_irrefl 1 (by rw [hc0] at hx; exact hx))]
          rfl
        | .inr hcp =>
          rw [ground.neBeqOf (fun hx : c = 0 =>
              Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hcp (Nat.le_of_eq hx))),
            fDiff_in a (c + 1) 1 (ha ▸ Nat.zero_le 1)
              (Nat.succ_lt_succ hcp)]
          rfl
  | m + 1, hj => by
    match Nat.lt_or_ge (m + 1) (c + 1) with
    | .inl hhi =>
      have hjc : m + 1 ≤ c := Nat.le_of_lt_succ hhi
      have hjl : ¬ m + 1 + 1 = l :=
        Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_succ hjc) hcl)
      have hln : lnC l (m + 1) = 1 :=
        if_neg (fun hb => hjl (ground.beqEqOf hb))
      match Nat.lt_or_ge (m + 1) a with
      | .inl hlt =>
        rw [fDiff_lo a (c + 1) (m + 1) (fun hx =>
            Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt hx)),
          ground.neBeqOf (fun hx : a = m + 1 =>
            Nat.lt_irrefl (m + 1)
              (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
          ground.neBeqOf (fun hx : c = m + 1 =>
            Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt
              (Nat.le_trans hac (Nat.le_of_eq hx))))]
        exact natVac _ _
      | .inr hlo =>
        rw [fDiff_in a (c + 1) (m + 1) hlo hhi, hln, nbC_succ,
          if_neg (fun hb => hjl (ground.beqEqOf hb))]
        by_cases he3 : m + 3 = l
        · have hc3 : c + 1 < m + 3 := by rw [← he3] at hcl; exact hcl
          have hce : c = m + 1 := Nat.le_antisymm
            (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hc3)) hjc
          rw [if_pos (ground.eqBeqOf he3), ground.eqBeqOf hce,
            fDiff_hi a (c + 1) (m + 2) (fun hx =>
              Nat.lt_irrefl (m + 2) (by rw [hce] at hx; exact hx))]
          match Nat.lt_or_ge m a with
          | .inl hma =>
            rw [ground.eqBeqOf (Nat.le_antisymm hlo
                (Nat.succ_le_of_lt hma)),
              fDiff_lo a (c + 1) m (fun hx =>
                Nat.lt_irrefl m (Nat.lt_of_lt_of_le hma hx))]
            rfl
          | .inr hma =>
            rw [ground.neBeqOf (fun hx : a = m + 1 =>
                Nat.not_succ_le_self m
                  (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
              fDiff_in a (c + 1) m hma
                (Nat.lt_trans (Nat.lt_succ_self m) hhi)]
            rfl
        · rw [if_neg (fun hb => he3 (ground.beqEqOf hb))]
          match Nat.lt_or_ge m a with
          | .inl hma =>
            rw [ground.eqBeqOf (Nat.le_antisymm hlo
                (Nat.succ_le_of_lt hma)),
              fDiff_lo a (c + 1) m (fun hx =>
                Nat.lt_irrefl m (Nat.lt_of_lt_of_le hma hx))]
            match Nat.lt_or_ge (m + 1) c with
            | .inl hmc =>
              rw [ground.neBeqOf (fun hx : c = m + 1 =>
                  Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                    (Nat.le_of_eq hx))),
                fDiff_in a (c + 1) (m + 2)
                  (Nat.le_trans hlo (Nat.le_succ (m + 1)))
                  (Nat.succ_lt_succ hmc)]
              rfl
            | .inr hcm =>
              have hce : c = m + 1 := Nat.le_antisymm hcm hjc
              rw [ground.eqBeqOf hce,
                fDiff_hi a (c + 1) (m + 2) (fun hx =>
                  Nat.lt_irrefl (m + 2) (by rw [hce] at hx; exact hx))]
              rfl
          | .inr hma =>
            rw [ground.neBeqOf (fun hx : a = m + 1 =>
                Nat.not_succ_le_self m
                  (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
              fDiff_in a (c + 1) m hma
                (Nat.lt_trans (Nat.lt_succ_self m) hhi)]
            match Nat.lt_or_ge (m + 1) c with
            | .inl hmc =>
              rw [ground.neBeqOf (fun hx : c = m + 1 =>
                  Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                    (Nat.le_of_eq hx))),
                fDiff_in a (c + 1) (m + 2)
                  (Nat.le_trans hlo (Nat.le_succ (m + 1)))
                  (Nat.succ_lt_succ hmc)]
              rfl
            | .inr hcm =>
              have hce : c = m + 1 := Nat.le_antisymm hcm hjc
              rw [ground.eqBeqOf hce,
                fDiff_hi a (c + 1) (m + 2) (fun hx =>
                  Nat.lt_irrefl (m + 2) (by rw [hce] at hx; exact hx))]
              rfl
    | .inr hge =>
      rw [fDiff_hi a (c + 1) (m + 1) (fun hx =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hx hge)),
        ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_eq hx.symm) hac)
              (Nat.lt_succ_self c)) hge)),
        ground.neBeqOf (fun hx : c = m + 1 =>
          Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le
            (Nat.lt_succ_of_le (Nat.le_of_eq hx.symm)) hge))]
      exact natVac _ _

/-- The `C` difference family's square: the short root's cleared
form at two. -/
private theorem capDiffC (l a b : Nat) (hab : a < b) (hbl : b < l) :
    gentable.formNum (sertables.tableC l) (sertables.diffFold l a b)
        (sertables.diffFold l a b) ≤ BPair.ofNat 4 := by
  match b, hab, hbl with
  | c + 1, hab, hbl =>
    have hac : a ≤ c := Nat.le_of_lt_succ hab
    have hal : a < l := Nat.lt_of_le_of_lt hac
      (Nat.lt_trans (Nat.lt_succ_self c) hbl)
    have hcl : c < l := Nat.lt_trans (Nat.lt_succ_self c) hbl
    rw [fDiff_eq l a (c + 1)]
    refine formCap (sertables.tableC l) l rfl (fDiff a (c + 1))
      (nbC l (fDiff a (c + 1))) (lnC l)
      (fun k => (if a == k then 1 else 0) + (if c == k then 1 else 0))
      (fun _ => 0) 2 (colC l (fDiff a (c + 1))) (lnC_read l)
      (natDiffC l a c hac hbl) ?_ (by decide +kernel)
    rw [dfold2 l a c 1 1, if_pos hal, if_pos hcl,
      ground.famFold_rangeZero (fun _ => 0) l (fun _ _ => rfl)]

/-- The `C` sum family's entry at a key. -/
def fSumC (d a b k : Nat) : Nat :=
  fDiff a b k + ((fDiff b d k + fDiff b d k) + fDiff d (d + 1) k)

/-- The `C` sum family is its entry function's range map. -/
theorem fSumC_eq (d a b : Nat) :
    sertables.sumFoldC (d + 1) a b
      = (List.range (d + 1)).map (fSumC d a b) := by
  show List.zipWith (fun x y => x + y) (sertables.ind (d + 1) a b)
      (List.zipWith (fun x y => x + y)
        (List.zipWith (fun x y => x + y) (sertables.ind (d + 1) b d)
          (sertables.ind (d + 1) b d))
        (sertables.ind (d + 1) d (d + 1)))
    = (List.range (d + 1)).map (fSumC d a b)
  rw [show sertables.ind (d + 1) b d
        = (List.range (d + 1)).map (fDiff b d) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff b d) (fDiff b d)
      (List.range (d + 1)),
    show sertables.ind (d + 1) d (d + 1)
        = (List.range (d + 1)).map (fDiff d (d + 1)) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fun k => fDiff b d k + fDiff b d k)
      (fDiff d (d + 1)) (List.range (d + 1)),
    show sertables.ind (d + 1) a b
        = (List.range (d + 1)).map (fDiff a b) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff a b)
      (fun k => fDiff b d k + fDiff b d k + fDiff d (d + 1) k)
      (List.range (d + 1))]
  rfl

/-- The `C` sum family's entry below the pair is vacant. -/
theorem fSumC_lo (d a b k : Nat) (h1 : k < a) (h2 : a < b)
    (h3 : b ≤ d) : fSumC d a b k = 0 := by
  show fDiff a b k + ((fDiff b d k + fDiff b d k)
    + fDiff d (d + 1) k) = 0
  rw [fDiff_lo a b k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h1 hx)),
    fDiff_lo b d k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_trans h1 h2) hx)),
    fDiff_lo d (d + 1) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le
        (Nat.lt_trans h1 h2) h3) hx))]

/-- The `C` sum family's entry inside the pair's window is one. -/
theorem fSumC_mid (d a b k : Nat) (h1 : a ≤ k) (h2 : k < b)
    (h3 : b ≤ d) : fSumC d a b k = 1 := by
  show fDiff a b k + ((fDiff b d k + fDiff b d k)
    + fDiff d (d + 1) k) = 1
  rw [fDiff_in a b k h1 h2,
    fDiff_lo b d k (fun hx => Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hx)),
    fDiff_lo d (d + 1) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h2 h3) hx))]

/-- The `C` sum family's entry at or above the pair's top, below the
last key, is two. -/
theorem fSumC_two (d a b k : Nat) (h1 : b ≤ k) (h2 : k < d) :
    fSumC d a b k = 2 := by
  show fDiff a b k + ((fDiff b d k + fDiff b d k)
    + fDiff d (d + 1) k) = 2
  rw [fDiff_hi a b k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le hx h1)),
    fDiff_in b d k h1 h2,
    fDiff_lo d (d + 1) k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hx))]

/-- The `C` sum family's entry at the last key is one. -/
theorem fSumC_end (d a b k : Nat) (h : b ≤ d) (hk : d = k) :
    fSumC d a b k = 1 := by
  subst hk
  show fDiff a b d + ((fDiff b d d + fDiff b d d)
    + fDiff d (d + 1) d) = 1
  rw [fDiff_hi a b d (fun hx =>
      Nat.lt_irrefl d (Nat.lt_of_lt_of_le hx h)),
    fDiff_hi b d d (Nat.lt_irrefl d),
    fDiff_in d (d + 1) d (Nat.le_refl d) (Nat.lt_succ_self d)]

/-- The `C` sum family's term identity at every key. -/
private theorem natSumC (d a c : Nat) (hac : a ≤ c) (hcd : c + 1 ≤ d) :
    ∀ j, j < d + 1 →
      fSumC d a (c + 1) j * (2 * fSumC d a (c + 1) j) * lnC (d + 1) j
          + (if c == j then 1 else 0)
        = ((if a == j then 1 else 0) + (if c + 1 == j then 2 else 0))
          + fSumC d a (c + 1) j
              * nbC (d + 1) (fSumC d a (c + 1)) j * lnC (d + 1) j
  | 0, _ => by
    have hd0 : 0 < d := Nat.lt_of_lt_of_le (Nat.succ_pos c) hcd
    have hln : lnC (d + 1) 0 = 1 :=
      if_neg (fun hb => absurd (Nat.succ.inj (ground.beqEqOf hb))
        (Nat.ne_of_lt hd0))
    match Nat.lt_or_ge 0 a with
    | .inl hlt =>
      rw [fSumC_lo d a (c + 1) 0 hlt (Nat.lt_succ_of_le hac) hcd,
        ground.neBeqOf (fun hx : a = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
        ground.neBeqOf (fun hx : c = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt
            (Nat.le_trans hac (Nat.le_of_eq hx)))),
        ground.neBeqOf (fun hx : c + 1 = 0 => Nat.noConfusion hx)]
      exact natVac _ _
    | .inr hle =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hle
      rw [fSumC_mid d a (c + 1) 0 hle (Nat.succ_pos c) hcd, hln,
        nbC_zero, ground.eqBeqOf ha,
        ground.neBeqOf (fun hx : c + 1 = 0 => Nat.noConfusion hx)]
      by_cases he2 : 2 = d + 1
      · have hd1 : d = 1 := (Nat.succ.inj he2).symm
        have hc0 : c = 0 := Nat.eq_zero_of_le_zero
          (Nat.le_of_succ_le_succ (by rw [hd1] at hcd; exact hcd))
        rw [if_pos (ground.eqBeqOf he2), ground.eqBeqOf hc0,
          fSumC_end d a (c + 1) 1 hcd hd1]
        rfl
      · rw [if_neg (fun hb => he2 (ground.beqEqOf hb)),
          if_pos (Nat.succ_lt_succ hd0)]
        match Nat.eq_zero_or_pos c with
        | .inl hc0 =>
          have hd2 : 1 < d := Nat.lt_of_le_of_ne hd0
            (fun hx => he2 (congrArg (· + 1) hx))
          rw [ground.eqBeqOf hc0,
            fSumC_two d a (c + 1) 1
              (Nat.le_of_eq (congrArg (· + 1) hc0)) hd2]
          rfl
        | .inr hcp =>
          rw [ground.neBeqOf (fun hx : c = 0 =>
              Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hcp (Nat.le_of_eq hx))),
            fSumC_mid d a (c + 1) 1 (ha ▸ Nat.zero_le 1)
              (Nat.succ_lt_succ hcp) hcd]
          rfl
  | m + 1, hj => by
    have hjd : m + 1 ≤ d := Nat.le_of_lt_succ hj
    match Nat.lt_or_ge (m + 1) (c + 1) with
    | .inl hhi =>
      have hjc : m + 1 ≤ c := Nat.le_of_lt_succ hhi
      have hmd : m + 1 < d := Nat.lt_of_le_of_lt hjc
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hcd)
      have hjl : ¬ m + 1 + 1 = d + 1 := fun hx =>
        absurd (Nat.succ.inj hx) (Nat.ne_of_lt hmd)
      have hln : lnC (d + 1) (m + 1) = 1 :=
        if_neg (fun hb => hjl (ground.beqEqOf hb))
      have hbne : ¬ c + 1 = m + 1 := fun hx =>
        Nat.not_succ_le_self m
          (Nat.le_trans hjc (Nat.le_of_eq (Nat.succ.inj hx)))
      match Nat.lt_or_ge (m + 1) a with
      | .inl hlt =>
        rw [fSumC_lo d a (c + 1) (m + 1) hlt
            (Nat.lt_succ_of_le hac) hcd,
          ground.neBeqOf (fun hx : a = m + 1 =>
            Nat.lt_irrefl (m + 1)
              (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
          ground.neBeqOf (fun hx : c = m + 1 =>
            Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hlt
              (Nat.le_trans hac (Nat.le_of_eq hx)))),
          ground.neBeqOf hbne]
        exact natVac _ _
      | .inr hlo =>
        rw [fSumC_mid d a (c + 1) (m + 1) hlo hhi hcd, hln, nbC_succ,
          if_neg (fun hb => hjl (ground.beqEqOf hb)),
          ground.neBeqOf hbne]
        by_cases he3 : m + 3 = d + 1
        · have hmd2 : m + 2 = d := Nat.succ.inj he3
          have hce : c = m + 1 := Nat.le_antisymm
            (Nat.le_of_succ_le_succ (by rw [← hmd2] at hcd; exact hcd))
            hjc
          rw [if_pos (ground.eqBeqOf he3), ground.eqBeqOf hce,
            fSumC_end d a (c + 1) (m + 2) hcd hmd2.symm]
          match Nat.lt_or_ge m a with
          | .inl hma =>
            rw [ground.eqBeqOf (Nat.le_antisymm hlo
                (Nat.succ_le_of_lt hma)),
              fSumC_lo d a (c + 1) m hma (Nat.lt_succ_of_le hac) hcd]
            rfl
          | .inr hma =>
            rw [ground.neBeqOf (fun hx : a = m + 1 =>
                Nat.not_succ_le_self m
                  (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
              fSumC_mid d a (c + 1) m hma
                (Nat.lt_trans (Nat.lt_succ_self m) hhi) hcd]
            rfl
        · rw [if_neg (fun hb => he3 (ground.beqEqOf hb))]
          have hfm2 : fSumC d a (c + 1) (m + 2)
              = if c == m + 1 then 2 else 1 := by
            match Nat.lt_or_ge (m + 1) c with
            | .inl hmc =>
              rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                  (Nat.le_of_eq hx)))]
              exact fSumC_mid d a (c + 1) (m + 2)
                (Nat.le_trans hlo (Nat.le_succ (m + 1)))
                (Nat.succ_lt_succ hmc) hcd
            | .inr hcm =>
              have hce : c = m + 1 := Nat.le_antisymm hcm hjc
              rw [ground.eqBeqOf hce]
              exact fSumC_two d a (c + 1) (m + 2)
                (Nat.le_of_eq (congrArg (· + 1) hce))
                (Nat.lt_of_le_of_ne
                  (Nat.le_trans
                    (Nat.le_of_eq (congrArg (· + 1) hce).symm) hcd)
                  (fun hx => he3 (congrArg (· + 1) hx)))
          rw [hfm2]
          match Nat.lt_or_ge m a with
          | .inl hma =>
            rw [ground.eqBeqOf (Nat.le_antisymm hlo
                (Nat.succ_le_of_lt hma)),
              fSumC_lo d a (c + 1) m hma (Nat.lt_succ_of_le hac) hcd]
            match Nat.lt_or_ge (m + 1) c with
            | .inl hmc =>
              rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                  (Nat.le_of_eq hx)))]
              rfl
            | .inr hcm =>
              rw [ground.eqBeqOf (Nat.le_antisymm hcm hjc)]
              rfl
          | .inr hma =>
            rw [ground.neBeqOf (fun hx : a = m + 1 =>
                Nat.not_succ_le_self m
                  (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
              fSumC_mid d a (c + 1) m hma
                (Nat.lt_trans (Nat.lt_succ_self m) hhi) hcd]
            match Nat.lt_or_ge (m + 1) c with
            | .inl hmc =>
              rw [ground.neBeqOf (fun hx : c = m + 1 =>
                Nat.lt_irrefl (m + 1) (Nat.lt_of_lt_of_le hmc
                  (Nat.le_of_eq hx)))]
              rfl
            | .inr hcm =>
              rw [ground.eqBeqOf (Nat.le_antisymm hcm hjc)]
              rfl
    | .inr hge =>
      have hcm : c ≤ m := Nat.le_of_succ_le_succ hge
      rw [ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.not_succ_le_self m (Nat.le_trans
            (Nat.le_trans (Nat.le_of_eq hx.symm) hac) hcm)),
        ground.neBeqOf (fun hx : c = m + 1 =>
          Nat.not_succ_le_self m
            (Nat.le_trans (Nat.le_of_eq hx.symm) hcm))]
      by_cases hend : m + 1 = d
      · have hg1 : (m + 1 + 1 == d + 1) = true :=
          ground.eqBeqOf (congrArg (· + 1) hend)
        have hg2 : (m + 2 == d + 1) = true :=
          ground.eqBeqOf (congrArg (· + 1) hend)
        rw [fSumC_end d a (c + 1) (m + 1) hcd hend.symm,
          show lnC (d + 1) (m + 1) = 2 from if_pos hg1,
          nbC_succ, if_pos hg2]
        match Nat.lt_or_ge c m with
        | .inl hlt =>
          rw [ground.neBeqOf (fun hx : c + 1 = m + 1 =>
              Nat.lt_irrefl c (Nat.lt_of_lt_of_le hlt
                (Nat.le_of_eq (Nat.succ.inj hx).symm))),
            fSumC_two d a (c + 1) m hlt
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self m)
                (Nat.le_of_eq hend))]
          rfl
        | .inr hmc =>
          have hce : c = m := Nat.le_antisymm hcm hmc
          rw [ground.eqBeqOf (congrArg (· + 1) hce),
            fSumC_mid d a (c + 1) m (by rw [hce] at hac; exact hac)
              (Nat.lt_succ_of_le hmc) hcd]
          rfl
      · have hmd : m + 1 < d := Nat.lt_of_le_of_ne hjd hend
        have hjl : ¬ m + 1 + 1 = d + 1 := fun hx =>
          hend (Nat.succ.inj hx)
        rw [fSumC_two d a (c + 1) (m + 1) hge hmd,
          show lnC (d + 1) (m + 1) = 1 from
            if_neg (fun hb => hjl (ground.beqEqOf hb)),
          nbC_succ, if_neg (fun hb => hjl (ground.beqEqOf hb))]
        have hfm : fSumC d a (c + 1) m = if c + 1 == m + 1 then 1 else 2 := by
          match Nat.lt_or_ge c m with
          | .inl hlt =>
            rw [ground.neBeqOf (fun hx : c + 1 = m + 1 =>
              Nat.lt_irrefl c (Nat.lt_of_lt_of_le hlt
                (Nat.le_of_eq (Nat.succ.inj hx).symm)))]
            exact fSumC_two d a (c + 1) m hlt
              (Nat.lt_trans (Nat.lt_succ_self m) hmd)
          | .inr hmc =>
            have hce : c = m := Nat.le_antisymm hcm hmc
            rw [ground.eqBeqOf (congrArg (· + 1) hce)]
            exact fSumC_mid d a (c + 1) m
              (by rw [hce] at hac; exact hac)
              (Nat.lt_succ_of_le hmc) hcd
        by_cases he3 : m + 3 = d + 1
        · have hmd2 : m + 2 = d := Nat.succ.inj he3
          rw [if_pos (ground.eqBeqOf he3),
            fSumC_end d a (c + 1) (m + 2) hcd hmd2.symm, hfm]
          match Nat.lt_or_ge c m with
          | .inl hlt =>
            rw [ground.neBeqOf (fun hx : c + 1 = m + 1 =>
              Nat.lt_irrefl c (Nat.lt_of_lt_of_le hlt
                (Nat.le_of_eq (Nat.succ.inj hx).symm)))]
            rfl
          | .inr hmc =>
            rw [ground.eqBeqOf (congrArg (· + 1)
              (Nat.le_antisymm hcm hmc))]
            rfl
        · rw [if_neg (fun hb => he3 (ground.beqEqOf hb)),
            fSumC_two d a (c + 1) (m + 2)
              (Nat.le_trans hge (Nat.le_succ (m + 1)))
              (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hmd)
                (fun hx => he3 (congrArg (· + 1) hx))), hfm]
          match Nat.lt_or_ge c m with
          | .inl hlt =>
            rw [ground.neBeqOf (fun hx : c + 1 = m + 1 =>
              Nat.lt_irrefl c (Nat.lt_of_lt_of_le hlt
                (Nat.le_of_eq (Nat.succ.inj hx).symm)))]
            rfl
          | .inr hmc =>
            rw [ground.eqBeqOf (congrArg (· + 1)
              (Nat.le_antisymm hcm hmc))]
            rfl

/-- The `C` sum family's square: the short root's cleared form at
two. -/
private theorem capSumC (l a b : Nat) (hab : a < b) (hbl : b < l) :
    gentable.formNum (sertables.tableC l) (sertables.sumFoldC l a b)
        (sertables.sumFoldC l a b) ≤ BPair.ofNat 4 := by
  match l, hbl with
  | d + 1, hbl =>
    match b, hab, hbl with
    | c + 1, hab, hbl =>
      have hac : a ≤ c := Nat.le_of_lt_succ hab
      have hcd : c + 1 ≤ d := Nat.le_of_lt_succ hbl
      have hal : a < d + 1 := Nat.lt_succ_of_le
        (Nat.le_trans hac (Nat.le_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_succ_self c) hcd)))
      have hbd : c + 1 < d + 1 := Nat.lt_succ_of_le hcd
      have hcl : c < d + 1 := Nat.lt_trans (Nat.lt_succ_self c) hbd
      rw [fSumC_eq d a (c + 1)]
      refine formCap (sertables.tableC (d + 1)) (d + 1) rfl
        (fSumC d a (c + 1)) (nbC (d + 1) (fSumC d a (c + 1)))
        (lnC (d + 1))
        (fun k => (if a == k then 1 else 0)
          + (if c + 1 == k then 2 else 0))
        (fun k => if c == k then 1 else 0) 2
        (colC (d + 1) (fSumC d a (c + 1))) (lnC_read (d + 1))
        (natSumC d a c hac hcd) ?_ (by decide +kernel)
      rw [dfold2 (d + 1) a (c + 1) 1 2, if_pos hal, if_pos hbd,
        pickR c 1 (d + 1), if_pos hcl]

/-- The `C` long family's entry at a key. -/
def fLong (d a k : Nat) : Nat :=
  (fDiff a d k + fDiff a d k) + fDiff d (d + 1) k

/-- The `C` long family is its entry function's range map. -/
theorem fLong_eq (d a : Nat) :
    sertables.longFold (d + 1) a
      = (List.range (d + 1)).map (fLong d a) := by
  show List.zipWith (fun x y => x + y)
      (List.zipWith (fun x y => x + y) (sertables.ind (d + 1) a d)
        (sertables.ind (d + 1) a d))
      (sertables.ind (d + 1) d (d + 1))
    = (List.range (d + 1)).map (fLong d a)
  rw [show sertables.ind (d + 1) a d
        = (List.range (d + 1)).map (fDiff a d) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff a d) (fDiff a d)
      (List.range (d + 1)),
    show sertables.ind (d + 1) d (d + 1)
        = (List.range (d + 1)).map (fDiff d (d + 1)) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fun k => fDiff a d k + fDiff a d k)
      (fDiff d (d + 1)) (List.range (d + 1))]
  rfl

/-- The `C` long family's entry below its coordinate is vacant. -/
theorem fLong_lo (d a k : Nat) (h1 : k < a) (h2 : a ≤ d) :
    fLong d a k = 0 := by
  show (fDiff a d k + fDiff a d k) + fDiff d (d + 1) k = 0
  rw [fDiff_lo a d k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h1 hx)),
    fDiff_lo d (d + 1) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h2) hx))]

/-- The `C` long family's entry at or above its coordinate, below
the last key, is two. -/
theorem fLong_two (d a k : Nat) (h1 : a ≤ k) (h2 : k < d) :
    fLong d a k = 2 := by
  show (fDiff a d k + fDiff a d k) + fDiff d (d + 1) k = 2
  rw [fDiff_in a d k h1 h2,
    fDiff_lo d (d + 1) k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hx))]

/-- The `C` long family's entry at the last key is one. -/
theorem fLong_end (d a k : Nat) (hk : d = k) :
    fLong d a k = 1 := by
  subst hk
  show (fDiff a d d + fDiff a d d) + fDiff d (d + 1) d = 1
  rw [fDiff_hi a d d (Nat.lt_irrefl d),
    fDiff_in d (d + 1) d (Nat.le_refl d) (Nat.lt_succ_self d)]

/-- The `C` long family's term identity at every key. -/
private theorem natLongC (d a : Nat) (had : a ≤ d) :
    ∀ j, j < d + 1 →
      fLong d a j * (2 * fLong d a j) * lnC (d + 1) j + 0
        = (if a == j then 4 else 0)
          + fLong d a j * nbC (d + 1) (fLong d a) j * lnC (d + 1) j
  | 0, _ => by
    match Nat.lt_or_ge 0 a with
    | .inl hlt =>
      rw [fLong_lo d a 0 hlt had,
        ground.neBeqOf (fun hx : a = 0 =>
          Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx)))]
      exact natVac _ _
    | .inr hle =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hle
      rw [ground.eqBeqOf ha, nbC_zero]
      match Nat.eq_zero_or_pos d with
      | .inl hd0 =>
        have h1 : (0 + 1 == d + 1) = true :=
          ground.eqBeqOf (congrArg (· + 1) hd0.symm)
        rw [fLong_end d a 0 hd0, show lnC (d + 1) 0 = 2 from if_pos h1,
          if_neg (fun hb : (2 == d + 1) = true =>
            Nat.noConfusion (Nat.succ.inj
              ((ground.beqEqOf hb).trans (congrArg (· + 1) hd0)))),
          if_neg (fun hx : 1 < d + 1 =>
            Nat.lt_irrefl 0 (by rw [hd0] at hx
                                exact Nat.lt_of_succ_lt_succ hx))]
        rfl
      | .inr hdp =>
        have hln : lnC (d + 1) 0 = 1 :=
          if_neg (fun hb => absurd (Nat.succ.inj (ground.beqEqOf hb))
            (Nat.ne_of_lt hdp))
        rw [fLong_two d a 0 hle hdp, hln]
        by_cases he2 : 2 = d + 1
        · have hd1 : d = 1 := (Nat.succ.inj he2).symm
          rw [if_pos (ground.eqBeqOf he2), fLong_end d a 1 hd1]
          rfl
        · have hd2 : 1 < d := Nat.lt_of_le_of_ne hdp
            (fun hx => he2 (congrArg (· + 1) hx))
          rw [if_neg (fun hb => he2 (ground.beqEqOf hb)),
            if_pos (Nat.succ_lt_succ hdp),
            fLong_two d a 1 (ha ▸ Nat.zero_le 1) hd2]
          rfl
  | m + 1, hj => by
    have hjd : m + 1 ≤ d := Nat.le_of_lt_succ hj
    match Nat.lt_or_ge (m + 1) a with
    | .inl hlt =>
      rw [fLong_lo d a (m + 1) hlt had,
        ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.lt_irrefl (m + 1)
            (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx)))]
      exact natVac _ _
    | .inr hlo =>
      have hfm : fLong d a m = if a == m + 1 then 0 else 2 := by
        match Nat.lt_or_ge m a with
        | .inl hma =>
          rw [ground.eqBeqOf (Nat.le_antisymm hlo (Nat.succ_le_of_lt hma))]
          exact fLong_lo d a m hma had
        | .inr hma =>
          rw [ground.neBeqOf (fun hx : a = m + 1 =>
            Nat.not_succ_le_self m
              (Nat.le_trans (Nat.le_of_eq hx.symm) hma))]
          exact fLong_two d a m hma
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hjd)
      by_cases hend : m + 1 = d
      · have hg1 : (m + 1 + 1 == d + 1) = true :=
          ground.eqBeqOf (congrArg (· + 1) hend)
        have hg2 : (m + 2 == d + 1) = true :=
          ground.eqBeqOf (congrArg (· + 1) hend)
        rw [fLong_end d a (m + 1) hend.symm,
          show lnC (d + 1) (m + 1) = 2 from if_pos hg1,
          nbC_succ, if_pos hg2, hfm]
        by_cases hae : a = m + 1
        · rw [ground.eqBeqOf hae]
          rfl
        · rw [ground.neBeqOf hae]
          rfl
      · have hmd : m + 1 < d := Nat.lt_of_le_of_ne hjd hend
        have hjl : ¬ m + 1 + 1 = d + 1 := fun hx =>
          hend (Nat.succ.inj hx)
        rw [fLong_two d a (m + 1) hlo hmd,
          show lnC (d + 1) (m + 1) = 1 from
            if_neg (fun hb => hjl (ground.beqEqOf hb)),
          nbC_succ, if_neg (fun hb => hjl (ground.beqEqOf hb))]
        by_cases he3 : m + 3 = d + 1
        · rw [if_pos (ground.eqBeqOf he3),
            fLong_end d a (m + 2) (Nat.succ.inj he3).symm, hfm]
          by_cases hae : a = m + 1
          · rw [ground.eqBeqOf hae]
            rfl
          · rw [ground.neBeqOf hae]
            rfl
        · rw [if_neg (fun hb => he3 (ground.beqEqOf hb)),
            fLong_two d a (m + 2)
              (Nat.le_trans hlo (Nat.le_succ (m + 1)))
              (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hmd)
                (fun hx => he3 (congrArg (· + 1) hx))), hfm]
          by_cases hae : a = m + 1
          · rw [ground.eqBeqOf hae]
            rfl
          · rw [ground.neBeqOf hae]
            rfl

/-- The `C` long family's square: the long root's cleared form at
four. -/
private theorem capLongC (l a : Nat) (hal : a < l) :
    gentable.formNum (sertables.tableC l) (sertables.longFold l a)
        (sertables.longFold l a) ≤ BPair.ofNat 4 := by
  match l, hal with
  | d + 1, hal =>
    have had : a ≤ d := Nat.le_of_lt_succ hal
    rw [fLong_eq d a]
    refine formCap (sertables.tableC (d + 1)) (d + 1) rfl (fLong d a)
      (nbC (d + 1) (fLong d a)) (lnC (d + 1))
      (fun k => if a == k then 4 else 0) (fun _ => 0) 4
      (colC (d + 1) (fLong d a)) (lnC_read (d + 1))
      (natLongC d a had) ?_ (Nat.le_refl 4)
    rw [pickR a 4 (d + 1), if_pos hal,
      ground.famFold_rangeZero (fun _ => 0) (d + 1) (fun _ _ => rfl)]

/-! ### The `D` series' fold families -/

/-- The entry one key below, the vacant read at the first key. -/
def pvD (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => F m

/-- The entry two keys below, vacant at the first two keys. -/
def pv2D (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | k + 2 => F k

/-- The entry one key below reads vacant at the first key. -/
theorem pvD_zero (F : Nat → Nat) : pvD F 0 = 0 := rfl

/-- The entry one key below at a successor key is the entry at the
key's own predecessor. -/
theorem pvD_succ (F : Nat → Nat) (m : Nat) :
    pvD F (m + 1) = F m := rfl

/-- The entry two keys below at a second successor key is the entry
two keys down. -/
theorem pv2D_succ2 (F : Nat → Nat) (k : Nat) :
    pv2D F (k + 2) = F k := rfl

/-- The `D` column's neighbour fold at a key: the chain's two
neighbours away from the fork, the fork key's three, and the two
tips each joined to the key three below the rank. -/
def nbD (l : Nat) (F : Nat → Nat) (j : Nat) : Nat :=
  if j + 1 == l then pv2D F j
  else if j + 2 == l then pvD F j
  else if j + 3 == l then pvD F j + F (j + 1) + F (j + 2)
  else pvD F j + F (j + 1)

/-- The `D` neighbour fold's four arms at a key: the two tips, the
fork key and the chain. -/
theorem nbD_eq (l : Nat) (F : Nat → Nat) (j : Nat) :
    nbD l F j
      = if j + 1 == l then pv2D F j
        else if j + 2 == l then pvD F j
        else if j + 3 == l then pvD F j + F (j + 1) + F (j + 2)
        else pvD F j + F (j + 1) := rfl

/-- The `D` column's count-pair read at every key. -/
private theorem colD (l : Nat) (h1l : 1 < l) (F : Nat → Nat) :
    ∀ j, j < l →
    (corootAt (sertables.tableD l) ((List.range l).map F) j).oneValue
      (BPair.ofCounts (2 * F j) (nbD l F j))
  | 0, hj => by
    have hne1 : ¬ (1 : Nat) = l := Nat.ne_of_lt h1l
    rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb))]
    by_cases he2 : (2 : Nat) = l
    · rw [if_pos (ground.eqBeqOf he2)]
      refine colDsimplec l 0 hj F (fun k hk => ?_)
      exact cartDoff l k 0 (fun hx => hk hx.symm)
        (fun _ hx => absurd ((show (3 : Nat) = l from hx).trans he2.symm)
          (by decide +kernel))
        (fun _ hx _ => absurd
          ((show (1 : Nat) = l from hx).trans he2.symm) (by decide +kernel))
        (fun hb _ hx => hb (show k + 1 = l from by
          rw [← show (1 : Nat) = k from hx]; exact he2))
        (fun _ _ hx => Nat.noConfusion hx)
    · rw [if_neg (fun hb => he2 (ground.beqEqOf hb))]
      by_cases he3 : (3 : Nat) = l
      · rw [if_pos (ground.eqBeqOf he3)]
        have h2l : 2 < l := he3 ▸ Nat.lt_succ_self 2
        refine BPair.oneValue_trans
          (colDzeroc l h1l F 1 1
            (fun c => by
              rw [cartDdn l 0 (show ¬ 0 + 2 = l from he2)
                (show ¬ 0 + 1 = l from hne1), Nat.one_mul]
              exact cellOneNeg c)
            (fun c => by
              rw [cartDfork l 2 0 (by decide +kernel)
                (show 2 + 1 = l from he3) (show 0 + 3 = l from he3),
                Nat.zero_add, Nat.one_mul]
              exact cellOneNeg c)
            (fun q => cartDoff l (q + 3) 0 (fun hx => Nat.noConfusion hx)
              (fun hk _ => absurd (hk.trans he3.symm)
                (fun hc => Nat.noConfusion (Nat.succ.inj
                  (Nat.succ.inj (Nat.succ.inj hc)))))
              (fun _ hx _ => absurd
                ((show (1 : Nat) = l from hx).trans he3.symm) (by decide +kernel))
              (fun _ _ hx => Nat.noConfusion (Nat.succ.inj hx))
              (fun _ _ hx => Nat.noConfusion hx)))
          (BPair.oneValue_of_eq (congrArg (BPair.ofCounts (2 * F 0)) ?_))
        rw [if_pos h1l, if_pos h2l, Nat.one_mul, Nat.one_mul, pvD_zero,
          Nat.zero_add]
      · rw [if_neg (fun hb => he3 (ground.beqEqOf hb))]
        have h3l : 3 < l := Nat.lt_of_le_of_ne
          (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1l he2)) he3
        have h2l : 2 < l := Nat.lt_trans (Nat.lt_succ_self 2) h3l
        refine BPair.oneValue_trans
          (colDzeroc l h1l F 1 0
            (fun c => by
              rw [cartDdn l 0 (show ¬ 0 + 2 = l from he2)
                (show ¬ 0 + 1 = l from hne1), Nat.one_mul]
              exact cellOneNeg c)
            (fun c => by
              rw [cartDoff l 2 0 (by decide +kernel)
                (fun _ hx => absurd (show (3 : Nat) = l from hx)
                  (Nat.ne_of_lt h3l))
                (fun _ hx _ => absurd (show (1 : Nat) = l from hx) hne1)
                (fun _ _ hx => Nat.noConfusion (Nat.succ.inj hx))
                (fun _ _ hx => Nat.noConfusion hx), Nat.zero_mul]
              exact cellNull c)
            (fun q => cartDoff l (q + 3) 0 (fun hx => Nat.noConfusion hx)
              (fun _ hx => absurd (show (3 : Nat) = l from hx)
                (Nat.ne_of_lt h3l))
              (fun _ hx _ => absurd (show (1 : Nat) = l from hx) hne1)
              (fun _ _ hx => Nat.noConfusion (Nat.succ.inj hx))
              (fun _ _ hx => Nat.noConfusion hx)))
          (BPair.oneValue_of_eq (congrArg (BPair.ofCounts (2 * F 0)) ?_))
        rw [if_pos h1l, if_pos h2l, Nat.one_mul, Nat.zero_mul,
          Nat.add_zero, pvD_zero, Nat.zero_add]
  | m + 1, hj => by
    rw [nbD_eq]
    by_cases ht : m + 1 + 1 = l
    · rw [if_pos (ground.eqBeqOf ht)]
      match m, ht, hj with
      | 0, ht, hj =>
        refine colDsimplec l 1 hj F (fun k hk => ?_)
        exact cartDoff l k 1 (fun hx => hk hx.symm)
          (fun _ hx => absurd
            ((show (4 : Nat) = l from hx).trans ht.symm) (by decide +kernel))
          (fun _ _ hx => absurd (hx.trans ht.symm)
            (fun hc => Nat.noConfusion (Nat.succ.inj
              (Nat.succ.inj hc))))
          (fun _ hb _ => absurd (show 1 + 1 = l from ht) hb)
          (fun _ hb _ => absurd (show 1 + 1 = l from ht) hb)
      | q + 1, ht, hj =>
        refine BPair.oneValue_trans (colDtopc l q ht F)
          (BPair.oneValue_of_eq
            (congrArg (BPair.ofCounts (2 * F (q + 2))) ?_))
        rw [if_pos (Nat.lt_trans (Nat.lt_succ_self q)
          (Nat.lt_trans (Nat.lt_succ_self (q + 1)) hj))]
        exact (pv2D_succ2 F q).symm
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      have hj2 : m + 2 < l := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj) ht
      have hml : m < l := Nat.lt_trans (Nat.lt_succ_self m) hj
      by_cases he3 : m + 1 + 2 = l
      · rw [if_pos (ground.eqBeqOf he3)]
        have he3' : m + 3 = l := he3
        refine BPair.oneValue_trans
          (colDmidc l m hj2 F 0 0
            (fun c => by
              rw [cartDoff l (m + 2) (m + 1) (neAdd (m + 1) 0)
                (fun _ hx => (neAdd (m + 3) 0 (hx.trans he3'.symm).symm))
                (fun hb _ => absurd (show m + 2 + 1 = l from he3') hb)
                (fun hb _ => absurd (show m + 2 + 1 = l from he3') hb)
                (fun hb _ => absurd (show m + 2 + 1 = l from he3') hb),
                Nat.zero_mul]
              exact cellNull c)
            (fun c => by
              rw [cartDoff l (m + 3) (m + 1) (neAdd (m + 1) 1)
                (fun hk _ => absurd (hk.trans he3'.symm).symm
                  (neAdd (m + 3) 0))
                (fun _ hx => absurd (hx.trans he3'.symm) (neAdd (m + 2) 0))
                (fun _ _ => neAdd (m + 2) 0)
                (fun _ _ => neAdd (m + 1) 2), Nat.zero_mul]
              exact cellNull c))
          (BPair.oneValue_of_eq
            (congrArg (BPair.ofCounts (2 * F (m + 1))) ?_))
        rw [if_pos hml, if_pos hj2,
          if_neg (fun hc => Nat.lt_irrefl l
            (Nat.lt_of_le_of_lt (Nat.le_of_eq he3'.symm) hc)),
          Nat.zero_mul, Nat.add_zero, Nat.add_zero, pvD_succ]
      · rw [if_neg (fun hb => he3 (ground.beqEqOf hb))]
        have hj3 : m + 3 < l :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj2) he3
        have hne3 : ¬ m + 1 + 2 = l := he3
        have hne2 : ¬ m + 1 + 1 = l := ht
        by_cases he4 : m + 1 + 3 = l
        · rw [if_pos (ground.eqBeqOf he4)]
          have he4' : m + 4 = l := he4
          refine BPair.oneValue_trans
            (colDmidc l m hj2 F 1 1
              (fun c => by
                rw [cartDdn l (m + 1) hne3 hne2, Nat.zero_add,
                  Nat.one_mul]
                exact cellOneNeg c)
              (fun c => by
                rw [cartDfork l (m + 3) (m + 1) (neAdd (m + 1) 1)
                  (show m + 3 + 1 = l from he4')
                  (show m + 1 + 3 = l from he4'),
                  Nat.zero_add, Nat.zero_add, Nat.one_mul]
                exact cellOneNeg c))
            (BPair.oneValue_of_eq
              (congrArg (BPair.ofCounts (2 * F (m + 1))) ?_))
          rw [if_pos hml, if_pos hj2, if_pos hj3, Nat.one_mul,
            Nat.one_mul, pvD_succ, Nat.add_assoc]
        · rw [if_neg (fun hb => he4 (ground.beqEqOf hb))]
          have hj4 : m + 4 < l :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hj3) he4
          refine BPair.oneValue_trans
            (colDmidc l m hj2 F 1 0
              (fun c => by
                rw [cartDdn l (m + 1) hne3 hne2, Nat.zero_add,
                  Nat.one_mul]
                exact cellOneNeg c)
              (fun c => by
                rw [cartDoff l (m + 3) (m + 1) (neAdd (m + 1) 1)
                  (fun hk => absurd (show m + 4 = l from hk)
                    (Nat.ne_of_lt hj4))
                  (fun _ hx => absurd (show m + 2 = l from hx)
                    (Nat.ne_of_lt hj2))
                  (fun _ _ => neAdd (m + 2) 0)
                  (fun _ _ => neAdd (m + 1) 2), Nat.zero_mul]
                exact cellNull c))
            (BPair.oneValue_of_eq
              (congrArg (BPair.ofCounts (2 * F (m + 1))) ?_))
          rw [if_pos hml, if_pos hj2, if_pos hj3, Nat.one_mul,
            Nat.zero_mul, Nat.add_zero, pvD_succ]

/-- The window's entry one key below at an occupied key: vacant at
the window's own first key and occupied beyond it. -/
private theorem pvDiffD (a c : Nat) : ∀ j, a ≤ j → j ≤ c →
    pvD (fDiff a (c + 1)) j = if a == j then 0 else 1
  | 0, hlo, _ => by
    rw [ground.eqBeqOf (Nat.eq_zero_of_le_zero hlo)]
    rfl
  | m + 1, hlo, hhi => by
    rw [pvD_succ]
    match Nat.lt_or_ge m a with
    | .inl hma =>
      rw [ground.eqBeqOf (Nat.le_antisymm hlo (Nat.succ_le_of_lt hma)),
        fDiff_lo a (c + 1) m (fun hx =>
          Nat.lt_irrefl m (Nat.lt_of_lt_of_le hma hx))]
      rfl
    | .inr hma =>
      rw [ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.not_succ_le_self m
            (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
        fDiff_in a (c + 1) m hma
          (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ m) hhi))]
      rfl

/-- The `D` difference family's neighbour fold inside the window:
the key below against the window's own end. -/
private theorem nbDiffD (l a c : Nat) (hcl : c + 1 < l) :
    ∀ j, a ≤ j → j ≤ c →
      nbD l (fDiff a (c + 1)) j
        = pvD (fDiff a (c + 1)) j + (if c == j then 0 else 1) := by
  intro j hlo hhi
  have hjl : ¬ j + 1 = l :=
    Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_succ hhi) hcl)
  rw [nbD_eq, if_neg (fun hb => hjl (ground.beqEqOf hb))]
  by_cases h2 : j + 2 = l
  · have hce : c = j := Nat.le_antisymm
      (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ
        (by rw [← h2] at hcl; exact hcl))) hhi
    rw [if_pos (ground.eqBeqOf h2), ground.eqBeqOf hce]
    rfl
  · rw [if_neg (fun hb => h2 (ground.beqEqOf hb))]
    have hfj : fDiff a (c + 1) (j + 1) = if c == j then 0 else 1 := by
      match Nat.lt_or_ge j c with
      | .inl hjc =>
        rw [ground.neBeqOf (fun hx : c = j =>
            Nat.lt_irrefl j (Nat.lt_of_lt_of_le hjc (Nat.le_of_eq hx)))]
        exact fDiff_in a (c + 1) (j + 1)
          (Nat.le_trans hlo (Nat.le_succ j)) (Nat.succ_lt_succ hjc)
      | .inr hcj =>
        have hce : c = j := Nat.le_antisymm hcj hhi
        rw [ground.eqBeqOf hce]
        exact fDiff_hi a (c + 1) (j + 1) (fun hx =>
          Nat.lt_irrefl (j + 1) (by rw [hce] at hx; exact hx))
    by_cases h3 : j + 3 = l
    · have hcj : c ≤ j + 1 := Nat.le_of_succ_le_succ
        (Nat.le_of_lt_succ (by rw [← h3] at hcl; exact hcl))
      rw [if_pos (ground.eqBeqOf h3), hfj,
        fDiff_hi a (c + 1) (j + 2) (fun hx =>
          Nat.lt_irrefl (j + 2)
            (Nat.lt_of_lt_of_le hx (Nat.succ_le_succ hcj)))]
      rfl
    · rw [if_neg (fun hb => h3 (ground.beqEqOf hb)), hfj]

/-- The `D` difference family's term identity at every key. -/
private theorem natDiffD (l a c : Nat) (hac : a ≤ c) (hcl : c + 1 < l) :
    ∀ j, j < l →
      fDiff a (c + 1) j * (2 * fDiff a (c + 1) j) * 2 + 0
        = ((if a == j then 2 else 0) + (if c == j then 2 else 0))
          + fDiff a (c + 1) j * nbD l (fDiff a (c + 1)) j * 2 := by
  intro j _
  match Nat.lt_or_ge j a with
  | .inl hlt =>
    rw [fDiff_lo a (c + 1) j (fun hx =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt hx)),
      ground.neBeqOf (fun hx : a = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
      ground.neBeqOf (fun hx : c = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans hac (Nat.le_of_eq hx))))]
    exact natVac _ _
  | .inr hlo =>
    match Nat.lt_or_ge c j with
    | .inl hcj =>
      rw [fDiff_hi a (c + 1) j (fun hx =>
          Nat.lt_irrefl c (Nat.lt_of_lt_of_le hcj
            (Nat.le_of_lt_succ hx))),
        ground.neBeqOf (fun hx : a = j =>
          Nat.lt_irrefl j (Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_of_eq hx.symm) hac) hcj)),
        ground.neBeqOf (fun hx : c = j =>
          Nat.lt_irrefl c (Nat.lt_of_lt_of_le hcj (Nat.le_of_eq hx.symm)))]
      exact natVac _ _
    | .inr hhi =>
      rw [fDiff_in a (c + 1) j hlo (Nat.lt_succ_of_le hhi),
        nbDiffD l a c hcl j hlo hhi, pvDiffD a c j hlo hhi]
      by_cases hae : a = j
      · rw [ground.eqBeqOf hae]
        by_cases hce : c = j
        · rw [ground.eqBeqOf hce]
          rfl
        · rw [ground.neBeqOf hce]
          rfl
      · rw [ground.neBeqOf hae]
        by_cases hce : c = j
        · rw [ground.eqBeqOf hce]
          rfl
        · rw [ground.neBeqOf hce]
          rfl

/-- The `D` difference family's square: the root's cleared form at
four. -/
private theorem capDiffD (l a b : Nat) (hab : a < b) (hbl : b < l) :
    gentable.formNum (sertables.tableD l) (sertables.diffFold l a b)
        (sertables.diffFold l a b) ≤ BPair.ofNat 4 := by
  match b, hab, hbl with
  | c + 1, hab, hbl =>
    have hac : a ≤ c := Nat.le_of_lt_succ hab
    have hcl : c < l := Nat.lt_trans (Nat.lt_succ_self c) hbl
    have hal : a < l := Nat.lt_of_le_of_lt hac hcl
    have h1l : 1 < l := Nat.lt_of_le_of_lt
      (Nat.succ_le_succ (Nat.zero_le c)) hbl
    rw [fDiff_eq l a (c + 1)]
    refine formCap (sertables.tableD l) l rfl (fDiff a (c + 1))
      (nbD l (fDiff a (c + 1))) (fun _ => 2)
      (fun k => (if a == k then 2 else 0) + (if c == k then 2 else 0))
      (fun _ => 0) 4 (colD l h1l (fDiff a (c + 1))) (sertables.lensD_at l)
      (natDiffD l a c hac hbl) ?_ (Nat.le_refl 4)
    rw [dfold2 l a c 2 2, if_pos hal, if_pos hcl,
      ground.famFold_rangeZero (fun _ => 0) l (fun _ _ => rfl)]

/-- The `D` sum family's entry at a key, the generic shape. -/
def fSumD (e a b k : Nat) : Nat :=
  fDiff a b k + ((fDiff b e k + fDiff b e k) + fDiff e (e + 2) k)

/-- The `D` sum family's generic member is its entry's range map. -/
theorem fSumD_eq (e a b : Nat) (hb : ¬ b + 1 = e + 2) :
    sertables.sumFoldD (e + 2) a b
      = (List.range (e + 2)).map (fSumD e a b) := by
  show (if (b + 1 == e + 2) = true then _ else _) = _
  rw [ground.neBeqOf hb]
  show List.zipWith (fun x y => x + y) (sertables.ind (e + 2) a b)
      (List.zipWith (fun x y => x + y)
        (List.zipWith (fun x y => x + y) (sertables.ind (e + 2) b e)
          (sertables.ind (e + 2) b e))
        (sertables.ind (e + 2) e (e + 2)))
    = (List.range (e + 2)).map (fSumD e a b)
  rw [show sertables.ind (e + 2) b e
        = (List.range (e + 2)).map (fDiff b e) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff b e) (fDiff b e)
      (List.range (e + 2)),
    show sertables.ind (e + 2) e (e + 2)
        = (List.range (e + 2)).map (fDiff e (e + 2)) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fun k => fDiff b e k + fDiff b e k)
      (fDiff e (e + 2)) (List.range (e + 2)),
    show sertables.ind (e + 2) a b
        = (List.range (e + 2)).map (fDiff a b) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff a b)
      (fun k => fDiff b e k + fDiff b e k + fDiff e (e + 2) k)
      (List.range (e + 2))]
  rfl

theorem fSumD_lo (e a b k : Nat) (h1 : k < a) (h2 : a < b)
    (h3 : b ≤ e) : fSumD e a b k = 0 := by
  show fDiff a b k + ((fDiff b e k + fDiff b e k)
    + fDiff e (e + 2) k) = 0
  rw [fDiff_lo a b k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h1 hx)),
    fDiff_lo b e k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_trans h1 h2) hx)),
    fDiff_lo e (e + 2) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le
        (Nat.lt_trans h1 h2) h3) hx))]

theorem fSumD_mid (e a b k : Nat) (h1 : a ≤ k) (h2 : k < b)
    (h3 : b ≤ e) : fSumD e a b k = 1 := by
  show fDiff a b k + ((fDiff b e k + fDiff b e k)
    + fDiff e (e + 2) k) = 1
  rw [fDiff_in a b k h1 h2,
    fDiff_lo b e k (fun hx => Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hx)),
    fDiff_lo e (e + 2) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h2 h3) hx))]

theorem fSumD_two (e a b k : Nat) (h1 : b ≤ k) (h2 : k < e) :
    fSumD e a b k = 2 := by
  show fDiff a b k + ((fDiff b e k + fDiff b e k)
    + fDiff e (e + 2) k) = 2
  rw [fDiff_hi a b k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le hx h1)),
    fDiff_in b e k h1 h2,
    fDiff_lo e (e + 2) k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hx))]

theorem fSumD_end (e a b k : Nat) (h1 : b ≤ e) (h2 : e ≤ k)
    (h3 : k < e + 2) : fSumD e a b k = 1 := by
  show fDiff a b k + ((fDiff b e k + fDiff b e k)
    + fDiff e (e + 2) k) = 1
  rw [fDiff_hi a b k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le hx (Nat.le_trans h1 h2))),
    fDiff_hi b e k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le hx h2)),
    fDiff_in e (e + 2) k h2 h3]


/-- The `D` sum family's generic entry sits at or below two. -/
theorem fSumD_le2 (e a b k : Nat) (hbe : b ≤ e) : fSumD e a b k ≤ 2 := by
  show fDiff a b k + ((fDiff b e k + fDiff b e k)
    + fDiff e (e + 2) k) ≤ 2
  by_cases h1 : k < b
  · rw [fDiff_lo b e k (fun hc =>
        Nat.lt_irrefl k (Nat.lt_of_lt_of_le h1 hc)),
      fDiff_lo e (e + 2) k (fun hc => Nat.lt_irrefl k
        (Nat.lt_of_lt_of_le h1 (Nat.le_trans hbe hc))),
      Nat.add_zero]
    exact Nat.le_trans (fDiff_le1 a b k) (by decide +kernel)
  · rw [fDiff_hi a b k h1, Nat.zero_add]
    by_cases h2 : k < e
    · rw [fDiff_lo e (e + 2) k (fun hc =>
          Nat.lt_irrefl k (Nat.lt_of_lt_of_le h2 hc)), Nat.add_zero]
      exact Nat.add_le_add (fDiff_le1 b e k) (fDiff_le1 b e k)
    · rw [fDiff_hi b e k h2, Nat.zero_add]
      exact Nat.le_trans (fDiff_le1 e (e + 2) k) (by decide +kernel)

/-- The `D` sum family's neighbour fold inside the one-window. -/
private theorem nbSumD (e a c : Nat) (hce : c + 1 ≤ e) :
    ∀ j, a ≤ j → j ≤ c →
      nbD (e + 2) (fSumD e a (c + 1)) j
        = pvD (fSumD e a (c + 1)) j + (if c == j then 2 else 1) := by
  intro j hlo hhi
  have hje : j < e := Nat.lt_of_le_of_lt hhi
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hce)
  have hj1 : ¬ j + 1 = e + 2 := fun hx =>
    Nat.lt_irrefl e (Nat.lt_trans (Nat.lt_succ_self e)
      (by rw [Nat.succ.inj hx] at hje; exact hje))
  have hj2 : ¬ j + 2 = e + 2 := fun hx =>
    Nat.lt_irrefl e
      (by rw [Nat.succ.inj (Nat.succ.inj hx)] at hje; exact hje)
  rw [nbD_eq, if_neg (fun hb => hj1 (ground.beqEqOf hb)),
    if_neg (fun hb => hj2 (ground.beqEqOf hb))]
  by_cases h3 : j + 3 = e + 2
  · have hje1 : j + 1 = e := Nat.succ.inj (Nat.succ.inj h3)
    have hce2 : c = j := Nat.le_antisymm
      (Nat.le_of_succ_le_succ (by rw [← hje1] at hce; exact hce)) hhi
    rw [if_pos (ground.eqBeqOf h3), ground.eqBeqOf hce2,
      fSumD_end e a (c + 1) (j + 1) hce (Nat.le_of_eq hje1.symm)
        (by rw [hje1]
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self e)
              (Nat.le_succ (e + 1))),
      fSumD_end e a (c + 1) (j + 2) hce
        (Nat.le_trans (Nat.le_of_eq hje1.symm) (Nat.le_succ (j + 1)))
        (by rw [← hje1]; exact Nat.lt_succ_self (j + 2))]
    rfl
  · rw [if_neg (fun hb => h3 (ground.beqEqOf hb))]
    match Nat.lt_or_ge j c with
    | .inl hjc =>
      rw [ground.neBeqOf (fun hx : c = j =>
          Nat.lt_irrefl j (Nat.lt_of_lt_of_le hjc (Nat.le_of_eq hx))),
        fSumD_mid e a (c + 1) (j + 1)
          (Nat.le_trans hlo (Nat.le_succ j))
          (Nat.succ_lt_succ hjc) hce]
      rfl
    | .inr hcj =>
      have hce2 : c = j := Nat.le_antisymm hcj hhi
      have hbe : c + 1 < e := Nat.lt_of_le_of_ne hce
        (fun hx => h3 (by rw [← hx, hce2]))
      rw [ground.eqBeqOf hce2,
        fSumD_two e a (c + 1) (j + 1)
          (Nat.le_of_eq (congrArg (· + 1) hce2))
          (by rw [← hce2]; exact hbe)]
      rfl

/-- The window's entry one key below at an occupied key of the `D`
sum family. -/
private theorem pvSumD (e a c : Nat) (hac : a ≤ c) (hce : c + 1 ≤ e) :
    ∀ j, a ≤ j → j ≤ c →
      pvD (fSumD e a (c + 1)) j = if a == j then 0 else 1
  | 0, hlo, _ => by
    rw [ground.eqBeqOf (Nat.eq_zero_of_le_zero hlo)]
    rfl
  | m + 1, hlo, hhi => by
    rw [pvD_succ]
    match Nat.lt_or_ge m a with
    | .inl hma =>
      rw [ground.eqBeqOf (Nat.le_antisymm hlo (Nat.succ_le_of_lt hma)),
        fSumD_lo e a (c + 1) m hma (Nat.lt_succ_of_le hac) hce]
      rfl
    | .inr hma =>
      rw [ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.not_succ_le_self m
            (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
        fSumD_mid e a (c + 1) m hma
          (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ m) hhi)) hce]
      rfl

/-- The `D` sum family's entry one key below, inside the doubled
window. -/
private theorem pvSumDmid (e a c : Nat) (hac : a ≤ c) (hce : c + 1 ≤ e) :
    ∀ j, c + 1 ≤ j → j < e →
      pvD (fSumD e a (c + 1)) j = if c + 1 == j then 1 else 2
  | 0, hlo, _ => absurd hlo (Nat.not_succ_le_zero c)
  | m + 1, hlo, hhi => by
    rw [pvD_succ]
    by_cases hjb : c + 1 = m + 1
    · have hcm : c = m := Nat.succ.inj hjb
      rw [if_pos (ground.eqBeqOf hjb)]
      exact fSumD_mid e a (c + 1) m (by rw [← hcm]; exact hac)
        (by rw [← hcm]; exact Nat.lt_succ_self c) hce
    · rw [if_neg (fun hb => hjb (ground.beqEqOf hb))]
      exact fSumD_two e a (c + 1) m
        (Nat.le_of_succ_le_succ (Nat.lt_of_le_of_ne hlo hjb))
        (Nat.lt_trans (Nat.lt_succ_self m) hhi)

/-- The `D` sum family's entries below the last two keys. -/
private theorem pvSumDend (e a c : Nat) (hac : a ≤ c) :
    ∀ e', e = e' → c + 1 ≤ e' →
      pvD (fSumD e a (c + 1)) e' = if c + 1 == e' then 1 else 2
  | 0, _, hce => absurd hce (Nat.not_succ_le_zero c)
  | f + 1, hef, hce => by
    rw [pvD_succ]
    by_cases hjb : c + 1 = f + 1
    · have hcm : c = f := Nat.succ.inj hjb
      rw [if_pos (ground.eqBeqOf hjb)]
      exact fSumD_mid e a (c + 1) f (by rw [← hcm]; exact hac)
        (by rw [← hcm]; exact Nat.lt_succ_self c) (by rw [hef]; exact hce)
    · rw [if_neg (fun hb => hjb (ground.beqEqOf hb))]
      exact fSumD_two e a (c + 1) f
        (Nat.le_of_succ_le_succ (Nat.lt_of_le_of_ne hce hjb))
        (by rw [hef]; exact Nat.lt_succ_self f)

private theorem pv2SumDend (e a c : Nat) (hac : a ≤ c) :
    ∀ e', e = e' → c + 1 ≤ e' →
      pv2D (fSumD e a (c + 1)) (e' + 1) = if c + 1 == e' then 1 else 2
  | 0, _, hce => absurd hce (Nat.not_succ_le_zero c)
  | f + 1, hef, hce => by
    rw [pv2D_succ2]
    by_cases hjb : c + 1 = f + 1
    · have hcm : c = f := Nat.succ.inj hjb
      rw [if_pos (ground.eqBeqOf hjb)]
      exact fSumD_mid e a (c + 1) f (by rw [← hcm]; exact hac)
        (by rw [← hcm]; exact Nat.lt_succ_self c) (by rw [hef]; exact hce)
    · rw [if_neg (fun hb => hjb (ground.beqEqOf hb))]
      exact fSumD_two e a (c + 1) f
        (Nat.le_of_succ_le_succ (Nat.lt_of_le_of_ne hce hjb))
        (by rw [hef]; exact Nat.lt_succ_self f)

/-- The `D` sum family's neighbour fold inside the doubled
window. -/
private theorem nbSumDmid (e a c : Nat) (hce : c + 1 ≤ e) :
    ∀ j, c + 1 ≤ j → j < e →
      nbD (e + 2) (fSumD e a (c + 1)) j
        = pvD (fSumD e a (c + 1)) j + 2 := by
  intro j hlo hhi
  have h1 : ¬ j + 1 = e + 2 := Nat.ne_of_lt
    (Nat.lt_trans (Nat.succ_lt_succ hhi) (Nat.lt_succ_self (e + 1)))
  have h2 : ¬ j + 2 = e + 2 := fun hx =>
    Nat.lt_irrefl e
      (by rw [Nat.succ.inj (Nat.succ.inj hx)] at hhi; exact hhi)
  rw [nbD_eq, if_neg (fun hb => h1 (ground.beqEqOf hb)),
    if_neg (fun hb => h2 (ground.beqEqOf hb))]
  by_cases h3 : j + 3 = e + 2
  · have hje1 : j + 1 = e := Nat.succ.inj (Nat.succ.inj h3)
    rw [if_pos (ground.eqBeqOf h3),
      fSumD_end e a (c + 1) (j + 1) hce (Nat.le_of_eq hje1.symm)
        (by rw [hje1]
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self e)
              (Nat.le_succ (e + 1))),
      fSumD_end e a (c + 1) (j + 2) hce
        (Nat.le_trans (Nat.le_of_eq hje1.symm) (Nat.le_succ (j + 1)))
        (by rw [← hje1]; exact Nat.lt_succ_self (j + 2))]
  · rw [if_neg (fun hb => h3 (ground.beqEqOf hb)),
      fSumD_two e a (c + 1) (j + 1)
        (Nat.le_trans hlo (Nat.le_succ j))
        (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hhi)
          (fun hx => h3 (congrArg (· + 1) (congrArg (· + 1) hx))))]

/-- The `D` sum family's term identity at every key, the generic
shape. -/
private theorem natSumDg (e a c q : Nat) (hac : a ≤ c) (hce : c + 1 ≤ e)
    (hq : q = if c + 1 == e then e + 1 else c + 1) :
    ∀ j, j < e + 2 →
      fSumD e a (c + 1) j * (2 * fSumD e a (c + 1) j) * 2
          + (if c == j then 2 else 0)
        = ((if a == j then 2 else 0)
            + ((if c + 1 == j then 2 else 0) + (if q == j then 2 else 0)))
          + fSumD e a (c + 1) j
              * nbD (e + 2) (fSumD e a (c + 1)) j * 2 := by
  have hqge : c + 1 ≤ q := by
    rw [hq]
    by_cases hbe : c + 1 = e
    · rw [if_pos (ground.eqBeqOf hbe)]
      exact Nat.le_trans (Nat.le_of_eq hbe) (Nat.le_succ e)
    · rw [if_neg (fun hb => hbe (ground.beqEqOf hb))]
      exact Nat.le_refl (c + 1)
  intro j hj
  match Nat.lt_or_ge j a with
  | .inl hlt =>
    rw [fSumD_lo e a (c + 1) j hlt (Nat.lt_succ_of_le hac) hce,
      ground.neBeqOf (fun hx : a = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hx))),
      ground.neBeqOf (fun hx : c = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans hac (Nat.le_of_eq hx)))),
      ground.neBeqOf (fun hx : c + 1 = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans (Nat.le_succ_of_le hac) (Nat.le_of_eq hx)))),
      ground.neBeqOf (fun hx : q = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans (Nat.le_succ_of_le hac)
            (Nat.le_trans hqge (Nat.le_of_eq hx)))))]
    exact natVac _ _
  | .inr hlo =>
    match Nat.lt_or_ge c j with
    | .inr hjc =>
      have hqne : ¬ q = j := fun hx =>
        Nat.not_succ_le_self c (Nat.le_trans
          (Nat.le_trans hqge (Nat.le_of_eq hx)) hjc)
      rw [fSumD_mid e a (c + 1) j hlo (Nat.lt_succ_of_le hjc) hce,
        nbSumD e a c hce j hlo hjc, pvSumD e a c hac hce j hlo hjc,
        ground.neBeqOf (fun hx : c + 1 = j =>
          Nat.not_succ_le_self c
            (Nat.le_trans (Nat.le_of_eq hx) hjc)),
        ground.neBeqOf hqne]
      by_cases hae : a = j
      · rw [ground.eqBeqOf hae]
        by_cases hce2 : c = j
        · rw [ground.eqBeqOf hce2]
          rfl
        · rw [ground.neBeqOf hce2]
          rfl
      · rw [ground.neBeqOf hae]
        by_cases hce2 : c = j
        · rw [ground.eqBeqOf hce2]
          rfl
        · rw [ground.neBeqOf hce2]
          rfl
    | .inl hcj =>
      have hcj1 : c + 1 ≤ j := hcj
      have hane : ¬ a = j := fun hx =>
        Nat.lt_irrefl j (Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.le_of_eq hx.symm) hac) hcj)
      have hcne : ¬ c = j := fun hx =>
        Nat.lt_irrefl j (Nat.lt_of_le_of_lt (Nat.le_of_eq hx.symm) hcj)
      match Nat.lt_or_ge j e with
      | .inl hje =>
        have hbe : ¬ c + 1 = e := fun hx =>
          Nat.lt_irrefl e (Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_of_eq hx.symm) hcj1) hje)
        have hqv : q = c + 1 := by
          rw [hq, if_neg (fun hb => hbe (ground.beqEqOf hb))]
        rw [fSumD_two e a (c + 1) j hcj1 hje,
          nbSumDmid e a c hce j hcj1 hje,
          pvSumDmid e a c hac hce j hcj1 hje,
          ground.neBeqOf hane, ground.neBeqOf hcne, hqv]
        by_cases hjb : c + 1 = j
        · rw [ground.eqBeqOf hjb]
          rfl
        · rw [ground.neBeqOf hjb]
          rfl
      | .inr hej =>
        match Nat.lt_or_ge j (e + 1) with
        | .inl hje1 =>
          have hje : j = e := Nat.le_antisymm (Nat.le_of_lt_succ hje1) hej
          have h2 : (j + 2 == e + 2) = true :=
            ground.eqBeqOf (congrArg (fun x => x + 2) hje)
          have h1 : ¬ j + 1 = e + 2 := fun hx =>
            Nat.ne_of_lt (Nat.lt_succ_self e)
              (Nat.succ.inj (by rw [hje] at hx; exact hx))
          rw [fSumD_end e a (c + 1) j hce hej hj, nbD_eq,
            if_neg (fun hb => h1 (ground.beqEqOf hb)), if_pos h2,
            pvSumDend e a c hac j hje.symm (by rw [hje]; exact hce),
            ground.neBeqOf hane, ground.neBeqOf hcne, hje]
          by_cases hbe : c + 1 = e
          · have hqv : q = e + 1 := by
              rw [hq, if_pos (ground.eqBeqOf hbe)]
            rw [hqv, ground.eqBeqOf hbe,
              ground.neBeqOf (fun hx : e + 1 = e =>
                Nat.not_succ_le_self e (Nat.le_of_eq hx))]
            rfl
          · have hqv : q = c + 1 := by
              rw [hq, if_neg (fun hb => hbe (ground.beqEqOf hb))]
            rw [hqv, ground.neBeqOf hbe]
            rfl
        | .inr hje1 =>
          have hje : j = e + 1 :=
            Nat.le_antisymm (Nat.le_of_lt_succ hj) hje1
          have h1 : (j + 1 == e + 2) = true :=
            ground.eqBeqOf (congrArg (fun x => x + 1) hje)
          rw [fSumD_end e a (c + 1) j hce
              (Nat.le_trans (Nat.le_succ e) (Nat.le_of_eq hje.symm)) hj,
            nbD_eq, if_pos h1, ground.neBeqOf hane,
            ground.neBeqOf hcne, hje,
            pv2SumDend e a c hac e rfl hce]
          by_cases hbe : c + 1 = e
          · have hqv : q = e + 1 := by
              rw [hq, if_pos (ground.eqBeqOf hbe)]
            rw [hqv, ground.eqBeqOf hbe,
              ground.eqBeqOf (rfl : e + 1 = e + 1),
              ground.neBeqOf (fun hx : c + 1 = e + 1 =>
                Nat.not_succ_le_self e
                  (Nat.le_trans (Nat.le_of_eq hx.symm)
                    (Nat.le_of_eq hbe)))]
            rfl
          · have hqv : q = c + 1 := by
              rw [hq, if_neg (fun hb => hbe (ground.beqEqOf hb))]
            rw [hqv, ground.neBeqOf hbe,
              ground.neBeqOf (fun hx : c + 1 = e + 1 =>
                Nat.not_succ_le_self c
                  (Nat.le_trans hce
                    (Nat.le_of_eq (Nat.succ.inj hx).symm)))]
            rfl

/-- The `D` sum family's square at the generic shape. -/
private theorem capSumDg (l a b : Nat) (hab : a < b) (hbl : b < l)
    (hbe : ¬ b + 1 = l) :
    gentable.formNum (sertables.tableD l) (sertables.sumFoldD l a b)
        (sertables.sumFoldD l a b) ≤ BPair.ofNat 4 := by
  match l, hbl, hbe with
  | 0, hbl, _ => exact absurd hbl (Nat.not_lt_zero b)
  | 1, hbl, _ =>
    exact absurd (Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ hbl))
      (Nat.not_lt_zero a)
  | e + 2, hbl, hbe =>
    match b, hab, hbl, hbe with
    | 0, hab, _, _ => exact absurd hab (Nat.not_lt_zero a)
    | c + 1, hab, hbl, hbe =>
      have hac : a ≤ c := Nat.le_of_lt_succ hab
      have hce : c + 1 ≤ e := Nat.le_of_lt_succ
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hbl)
          (fun hx => hbe (congrArg (· + 1) hx)))
      have hal : a < e + 2 := Nat.lt_of_le_of_lt hac
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans hce (Nat.le_succ_of_le (Nat.le_succ e))))
      have hbl2 : c + 1 < e + 2 := Nat.lt_succ_of_le
        (Nat.le_succ_of_le hce)
      have hcl : c < e + 2 := Nat.lt_trans (Nat.lt_succ_self c) hbl2
      have hql : (if c + 1 == e then e + 1 else c + 1) < e + 2 := by
        by_cases hb : c + 1 = e
        · rw [if_pos (ground.eqBeqOf hb)]
          exact Nat.lt_succ_self (e + 1)
        · rw [if_neg (fun hx => hb (ground.beqEqOf hx))]
          exact hbl2
      have h1l : 1 < e + 2 := Nat.succ_lt_succ (Nat.succ_pos e)
      rw [fSumD_eq e a (c + 1) hbe]
      refine formCap (sertables.tableD (e + 2)) (e + 2) rfl
        (fSumD e a (c + 1)) (nbD (e + 2) (fSumD e a (c + 1)))
        (fun _ => 2)
        (fun k => (if a == k then 2 else 0)
          + ((if c + 1 == k then 2 else 0)
            + (if (if c + 1 == e then e + 1 else c + 1) == k
              then 2 else 0)))
        (fun k => if c == k then 2 else 0) 4
        (colD (e + 2) h1l (fSumD e a (c + 1))) (sertables.lensD_at (e + 2))
        (natSumDg e a c _ hac hce rfl) ?_ (Nat.le_refl 4)
      rw [dfold3 (e + 2) a (c + 1)
          (if c + 1 == e then e + 1 else c + 1) 2 2 2,
        if_pos hal, if_pos hbl2, if_pos hql, pickR c 2 (e + 2),
        if_pos hcl]

/-- The `D` sum family's entry at a key, the last-coordinate
shape. -/
def fSumDt (e a k : Nat) : Nat :=
  fDiff a e k + fDiff (e + 1) (e + 2) k

/-- The `D` sum family's last-coordinate member is its entry's range
map. -/
private theorem fSumDt_eq (e a : Nat) :
    sertables.sumFoldD (e + 2) a (e + 1)
      = (List.range (e + 2)).map (fSumDt e a) := by
  show (if (e + 1 + 1 == e + 2) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : e + 1 + 1 = e + 2)]
  show List.zipWith (fun x y => x + y) (sertables.ind (e + 2) a e)
      (sertables.ind (e + 2) (e + 1) (e + 2))
    = (List.range (e + 2)).map (fSumDt e a)
  rw [show sertables.ind (e + 2) a e
        = (List.range (e + 2)).map (fDiff a e) from rfl,
    show sertables.ind (e + 2) (e + 1) (e + 2)
        = (List.range (e + 2)).map (fDiff (e + 1) (e + 2)) from rfl,
    ground.zipWith_map_map (fun x y => x + y) (fDiff a e) (fDiff (e + 1) (e + 2))
      (List.range (e + 2))]
  rfl

private theorem fSumDt_lo (e a k : Nat) (h1 : k < a) (h2 : a ≤ e) :
    fSumDt e a k = 0 := by
  show fDiff a e k + fDiff (e + 1) (e + 2) k = 0
  rw [fDiff_lo a e k (fun hx =>
      Nat.lt_irrefl k (Nat.lt_of_lt_of_le h1 hx)),
    fDiff_lo (e + 1) (e + 2) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1
        (Nat.le_succ_of_le h2)) hx))]

private theorem fSumDt_mid (e a k : Nat) (h1 : a ≤ k) (h2 : k < e) :
    fSumDt e a k = 1 := by
  show fDiff a e k + fDiff (e + 1) (e + 2) k = 1
  rw [fDiff_in a e k h1 h2,
    fDiff_lo (e + 1) (e + 2) k (fun hx => Nat.lt_irrefl k
      (Nat.lt_of_lt_of_le (Nat.lt_trans h2 (Nat.lt_succ_self e)) hx))]

theorem fSumDt_gap (e a k : Nat) (hk : k = e) :
    fSumDt e a k = 0 := by
  show fDiff a e k + fDiff (e + 1) (e + 2) k = 0
  rw [fDiff_hi a e k (fun hx =>
      Nat.lt_irrefl e (by rw [hk] at hx; exact hx)),
    fDiff_lo (e + 1) (e + 2) k (fun hx =>
      Nat.not_succ_le_self e (by rw [hk] at hx; exact hx))]

theorem fSumDt_top (e a k : Nat) (hk : k = e + 1) :
    fSumDt e a k = 1 := by
  show fDiff a e k + fDiff (e + 1) (e + 2) k = 1
  rw [fDiff_hi a e k (fun hx =>
      Nat.lt_irrefl e (Nat.lt_trans (Nat.lt_succ_self e)
        (by rw [hk] at hx; exact hx))),
    fDiff_in (e + 1) (e + 2) k (Nat.le_of_eq hk.symm)
      (by rw [hk]; exact Nat.lt_succ_self (e + 1))]


/-- The `D` last-coordinate entry sits at or below one. -/
theorem fSumDt_le1 (e a k : Nat) : fSumDt e a k ≤ 1 := by
  show fDiff a e k + fDiff (e + 1) (e + 2) k ≤ 1
  by_cases h1 : k < e
  · rw [fDiff_lo (e + 1) (e + 2) k (fun hc => Nat.lt_irrefl k
        (Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.le_succ e) hc))),
      Nat.add_zero]
    exact fDiff_le1 a e k
  · rw [fDiff_hi a e k h1, Nat.zero_add]
    exact fDiff_le1 (e + 1) (e + 2) k

/-- The last-coordinate family's entry one key below, inside the
window. -/
private theorem pvSumDt (e a : Nat) : ∀ j, a ≤ j → j < e →
    pvD (fSumDt e a) j = if a == j then 0 else 1
  | 0, hlo, _ => by
    rw [ground.eqBeqOf (Nat.eq_zero_of_le_zero hlo)]
    rfl
  | m + 1, hlo, hhi => by
    rw [pvD_succ]
    match Nat.lt_or_ge m a with
    | .inl hma =>
      rw [ground.eqBeqOf (Nat.le_antisymm hlo (Nat.succ_le_of_lt hma)),
        fSumDt_lo e a m hma (Nat.le_of_lt (Nat.lt_of_le_of_lt hlo hhi))]
      rfl
    | .inr hma =>
      rw [ground.neBeqOf (fun hx : a = m + 1 =>
          Nat.not_succ_le_self m
            (Nat.le_trans (Nat.le_of_eq hx.symm) hma)),
        fSumDt_mid e a m hma (Nat.lt_trans (Nat.lt_succ_self m) hhi)]
      rfl

/-- The last-coordinate family's entry two keys below the last
key. -/
private theorem pv2SumDt (e a : Nat) (hae : a ≤ e) :
    ∀ e', e = e' → pv2D (fSumDt e a) (e' + 1) = if a == e' then 0 else 1
  | 0, hef => by
    have ha0 : a = 0 := by rw [hef] at hae; exact Nat.eq_zero_of_le_zero hae
    rw [ground.eqBeqOf ha0]
    rfl
  | f + 1, hef => by
    rw [pv2D_succ2]
    match Nat.lt_or_ge f a with
    | .inl hfa =>
      rw [ground.eqBeqOf (Nat.le_antisymm
          (Nat.le_trans hae (Nat.le_of_eq hef)) (Nat.succ_le_of_lt hfa)),
        fSumDt_lo e a f hfa hae]
      rfl
    | .inr hfa =>
      rw [ground.neBeqOf (fun hx : a = f + 1 =>
          Nat.not_succ_le_self f
            (Nat.le_trans (Nat.le_of_eq hx.symm) hfa)),
        fSumDt_mid e a f hfa
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self f)
            (Nat.le_of_eq hef.symm))]
      rfl

/-- The last-coordinate family's neighbour fold inside the
window. -/
private theorem nbSumDt (e a : Nat) : ∀ j, a ≤ j → j < e →
    nbD (e + 2) (fSumDt e a) j = pvD (fSumDt e a) j + 1 := by
  intro j hlo hhi
  have h1 : ¬ j + 1 = e + 2 := Nat.ne_of_lt
    (Nat.lt_trans (Nat.succ_lt_succ hhi) (Nat.lt_succ_self (e + 1)))
  have h2 : ¬ j + 2 = e + 2 := fun hx =>
    Nat.lt_irrefl e
      (by rw [Nat.succ.inj (Nat.succ.inj hx)] at hhi; exact hhi)
  rw [nbD_eq, if_neg (fun hb => h1 (ground.beqEqOf hb)),
    if_neg (fun hb => h2 (ground.beqEqOf hb))]
  by_cases h3 : j + 3 = e + 2
  · have hje1 : j + 1 = e := Nat.succ.inj (Nat.succ.inj h3)
    rw [if_pos (ground.eqBeqOf h3), fSumDt_gap e a (j + 1) hje1,
      fSumDt_top e a (j + 2) (by rw [← hje1])]
  · rw [if_neg (fun hb => h3 (ground.beqEqOf hb)),
      fSumDt_mid e a (j + 1) (Nat.le_trans hlo (Nat.le_succ j))
        (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hhi)
          (fun hx => h3 (congrArg (· + 1) (congrArg (· + 1) hx))))]

/-- The `D` sum family's term identity at every key, the
last-coordinate shape. -/
private theorem natSumDt (e a p : Nat) (hae : a ≤ e)
    (hp : p = if a == e then e + 1 else a) :
    ∀ j, j < e + 2 →
      fSumDt e a j * (2 * fSumDt e a j) * 2 + 0
        = ((if p == j then 2 else 0) + (if e + 1 == j then 2 else 0))
          + fSumDt e a j * nbD (e + 2) (fSumDt e a) j * 2 := by
  have hpge : a ≤ p := by
    rw [hp]
    by_cases hae2 : a = e
    · rw [if_pos (ground.eqBeqOf hae2)]
      exact Nat.le_trans hae (Nat.le_succ e)
    · rw [if_neg (fun hb => hae2 (ground.beqEqOf hb))]
      exact Nat.le_refl a
  intro j hj
  match Nat.lt_or_ge j a with
  | .inl hlt =>
    rw [fSumDt_lo e a j hlt hae,
      ground.neBeqOf (fun hx : p = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans hpge (Nat.le_of_eq hx)))),
      ground.neBeqOf (fun hx : e + 1 = j =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt
          (Nat.le_trans (Nat.le_trans hae
            (Nat.le_succ e)) (Nat.le_of_eq hx))))]
    exact natVac _ _
  | .inr hlo =>
    match Nat.lt_or_ge j e with
    | .inl hje =>
      have hane : ¬ a = e := fun hx =>
        Nat.lt_irrefl j (Nat.lt_of_lt_of_le hje
          (Nat.le_trans (Nat.le_of_eq hx.symm) hlo))
      have hpv : p = a := by
        rw [hp, if_neg (fun hb => hane (ground.beqEqOf hb))]
      rw [fSumDt_mid e a j hlo hje, nbSumDt e a j hlo hje,
        pvSumDt e a j hlo hje, hpv,
        ground.neBeqOf (fun hx : e + 1 = j =>
          Nat.lt_irrefl j (Nat.lt_of_lt_of_le hje
            (Nat.le_trans (Nat.le_succ e) (Nat.le_of_eq hx))))]
      by_cases hae2 : a = j
      · rw [ground.eqBeqOf hae2]
        rfl
      · rw [ground.neBeqOf hae2]
        rfl
    | .inr hej =>
      match Nat.lt_or_ge j (e + 1) with
      | .inl hje1 =>
        have hje : j = e := Nat.le_antisymm (Nat.le_of_lt_succ hje1) hej
        rw [fSumDt_gap e a j hje,
          ground.neBeqOf (fun hx : p = j => by
            rw [hp] at hx
            by_cases hae2 : a = e
            · rw [if_pos (ground.eqBeqOf hae2)] at hx
              exact Nat.not_succ_le_self e
                (Nat.le_of_eq (hx.trans hje))
            · rw [if_neg (fun hb => hae2 (ground.beqEqOf hb))] at hx
              exact hae2 (hx.trans hje)),
          ground.neBeqOf (fun hx : e + 1 = j =>
            Nat.not_succ_le_self e
              (Nat.le_of_eq (hx.trans hje)))]
        exact natVac _ _
      | .inr hje1 =>
        have hje : j = e + 1 :=
          Nat.le_antisymm (Nat.le_of_lt_succ hj) hje1
        have h1 : (j + 1 == e + 2) = true :=
          ground.eqBeqOf (congrArg (fun x => x + 1) hje)
        rw [fSumDt_top e a j hje, nbD_eq, if_pos h1, hje,
          pv2SumDt e a hae e rfl,
          ground.eqBeqOf (rfl : e + 1 = e + 1), hp]
        by_cases hae2 : a = e
        · rw [if_pos (ground.eqBeqOf hae2), ground.eqBeqOf hae2,
            ground.eqBeqOf (rfl : e + 1 = e + 1)]
          rfl
        · rw [if_neg (fun hb => hae2 (ground.beqEqOf hb)),
            ground.neBeqOf hae2,
            ground.neBeqOf (fun hx : a = e + 1 =>
              Nat.not_succ_le_self e
                (Nat.le_trans (Nat.le_of_eq hx.symm) hae))]
          rfl

/-- The `D` sum family's square at the last-coordinate shape. -/
private theorem capSumDt (l a b : Nat) (hab : a < b) (hbl : b < l)
    (hbe : b + 1 = l) :
    gentable.formNum (sertables.tableD l) (sertables.sumFoldD l a b)
        (sertables.sumFoldD l a b) ≤ BPair.ofNat 4 := by
  match b, hab, hbl, hbe with
  | 0, hab, _, _ => exact absurd hab (Nat.not_lt_zero a)
  | e + 1, hab, hbl, hbe =>
    have hae : a ≤ e := Nat.le_of_lt_succ hab
    have hl : l = e + 2 := hbe.symm
    subst hl
    have hpl : (if a == e then e + 1 else a) < e + 2 := by
      by_cases hx : a = e
      · rw [if_pos (ground.eqBeqOf hx)]
        exact Nat.lt_succ_self (e + 1)
      · rw [if_neg (fun hb => hx (ground.beqEqOf hb))]
        exact Nat.lt_of_le_of_lt hae
          (Nat.lt_trans (Nat.lt_succ_self e) (Nat.lt_succ_self (e + 1)))
    have h1l : 1 < e + 2 := Nat.succ_lt_succ (Nat.succ_pos e)
    rw [fSumDt_eq e a]
    refine formCap (sertables.tableD (e + 2)) (e + 2) rfl (fSumDt e a)
      (nbD (e + 2) (fSumDt e a)) (fun _ => 2)
      (fun k => (if (if a == e then e + 1 else a) == k then 2 else 0)
        + (if e + 1 == k then 2 else 0))
      (fun _ => 0) 4 (colD (e + 2) h1l (fSumDt e a)) (sertables.lensD_at (e + 2))
      (natSumDt e a _ hae rfl) ?_ (Nat.le_refl 4)
    rw [dfold2 (e + 2) (if a == e then e + 1 else a) (e + 1) 2 2,
      if_pos hpl, if_pos (Nat.lt_succ_self (e + 1)),
      ground.famFold_rangeZero (fun _ => 0) (e + 2) (fun _ _ => rfl)]

/-! ### The positive lists' members and the content cap -/

/-- The `B` positive list's members: the two pair families and the
short family, each at its own parameters. -/
private theorem foldsB_data (l : Nat) : ∀ j,
    j < (sertables.tableB l).posFolds.length →
    (ground.getAt [] (sertables.tableB l).posFolds j).length = l
      ∧ gentable.formNum (sertables.tableB l)
          (ground.getAt [] (sertables.tableB l).posFolds j)
          (ground.getAt [] (sertables.tableB l).posFolds j)
        ≤ BPair.ofNat 4 := by
  intro j hj
  have hmem : ground.getAt [] (sertables.tableB l).posFolds j
      ∈ sertables.foldsB l :=
    ground.mem_getAt [] (sertables.tableB l).posFolds j hj
  match ground.mem_append_of _ _ hmem with
  | .inl h1 =>
    match ground.mem_append_of _ _ h1 with
    | .inl h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        rw [← he]
        exact ⟨diffLen l p.1 p.2, capDiffB l p.1 p.2 hpr.1 hpr.2⟩
    | .inr h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        rw [← he]
        exact ⟨sumBLen l p.1 p.2, capSumB l p.1 p.2 hpr.1 hpr.2⟩
  | .inr h1 =>
    match ground.mem_map_of _ (List.range l) _ h1 with
    | ⟨a, ha, he⟩ =>
      have hal : a < l := ground.ltOfMemRange ha
      rw [← he]
      exact ⟨shortLen l a, capShortB l a hal⟩

/-- The `C` positive list's members. -/
private theorem foldsC_data (l : Nat) : ∀ j,
    j < (sertables.tableC l).posFolds.length →
    (ground.getAt [] (sertables.tableC l).posFolds j).length = l
      ∧ gentable.formNum (sertables.tableC l)
          (ground.getAt [] (sertables.tableC l).posFolds j)
          (ground.getAt [] (sertables.tableC l).posFolds j)
        ≤ BPair.ofNat 4 := by
  intro j hj
  have hmem : ground.getAt [] (sertables.tableC l).posFolds j
      ∈ sertables.foldsC l :=
    ground.mem_getAt [] (sertables.tableC l).posFolds j hj
  match ground.mem_append_of _ _ hmem with
  | .inl h1 =>
    match ground.mem_append_of _ _ h1 with
    | .inl h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        rw [← he]
        exact ⟨diffLen l p.1 p.2, capDiffC l p.1 p.2 hpr.1 hpr.2⟩
    | .inr h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        rw [← he]
        exact ⟨sumCLen l p.1 p.2, capSumC l p.1 p.2 hpr.1 hpr.2⟩
  | .inr h1 =>
    match ground.mem_map_of _ (List.range l) _ h1 with
    | ⟨a, ha, he⟩ =>
      have hal : a < l := ground.ltOfMemRange ha
      rw [← he]
      exact ⟨longLen l a, capLongC l a hal⟩

/-- The `D` positive list's members. -/
private theorem foldsD_data (l : Nat) : ∀ j,
    j < (sertables.tableD l).posFolds.length →
    (ground.getAt [] (sertables.tableD l).posFolds j).length = l
      ∧ gentable.formNum (sertables.tableD l)
          (ground.getAt [] (sertables.tableD l).posFolds j)
          (ground.getAt [] (sertables.tableD l).posFolds j)
        ≤ BPair.ofNat 4 := by
  intro j hj
  have hmem : ground.getAt [] (sertables.tableD l).posFolds j
      ∈ sertables.foldsD l :=
    ground.mem_getAt [] (sertables.tableD l).posFolds j hj
  match ground.mem_append_of _ _ hmem with
  | .inl h1 =>
    match ground.mem_map_of _ (places.pairsOf l) _ h1 with
    | ⟨p, hp, he⟩ =>
      have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      rw [← he]
      exact ⟨diffLen l p.1 p.2, capDiffD l p.1 p.2 hpr.1 hpr.2⟩
  | .inr h1 =>
    match ground.mem_map_of _ (places.pairsOf l) _ h1 with
    | ⟨p, hp, he⟩ =>
      have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      rw [← he]
      refine ⟨sumDLen l p.1 p.2, ?_⟩
      by_cases hb : p.2 + 1 = l
      · exact capSumDt l p.1 p.2 hpr.1 hpr.2 hb
      · exact capSumDg l p.1 p.2 hpr.1 hpr.2 hb

/-- The zipped fold against a weight family is the pairing at the
counted coefficients. -/
private theorem zipSum_dotP : ∀ (f : List Nat) (ws : List BPair),
    (BPair.sum (List.zipWith (fun c w => BPair.ofNat c * w) f ws)).oneValue
      (elim.dotP (f.map BPair.ofNat) ws)
  | [], _ => BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | c :: f, w :: ws => by
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    exact BPair.add_congr (BPair.oneValue_refl _) (zipSum_dotP f ws)

/-- The four factors' rearrangement at the scaled term. -/
private theorem mul4rearr (a b c d : BPair) :
    a * (b * c * d) = b * (a * d * c) := by
  rw [BPair.mul_assoc b c d, ← BPair.mul_assoc a b (c * d),
    BPair.mul_comm a b, BPair.mul_assoc b a (c * d),
    BPair.mul_comm c d, ← BPair.mul_assoc a d c]

/-- A positive member's own square at the cleared form: the scale
against `con:gentable`'s cleared form fold at the member's fold. -/
private theorem dotB_posSq (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (j : Nat) (hf : (ground.getAt [] t.posFolds j).length = t.rank) :
    (sertables.dotB F (sertables.posCorootV t j)
        (sertables.posCorootV t j)).oneValue
      (BPair.ofNat F.scale
        * gentable.formNum t (ground.getAt [] t.posFolds j)
            (ground.getAt [] t.posFolds j)) := by
  have hcl : t.cartan.length = t.rank := assembly.cartanLen t F hgram
  have hxl : (sertables.posCorootV t j).length = t.rank :=
    sertables.posCorootV_length t j
  refine BPair.oneValue_trans
    (dotB_posCorootV t F hshape hgram j (sertables.posCorootV t j) hxl) ?_
  refine BPair.oneValue_trans
    (zipSum_dotP (ground.getAt [] t.posFolds j) _) ?_
  rw [elim.dotP_fold t.rank _ _
      (by rw [ground.length_map, hf])
      (by rw [ground.length_mapRange, hcl])]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun i => BPair.ofNat F.scale
        * (BPair.ofNat (ground.getAt 0 (ground.getAt [] t.posFolds j) i)
            * gentable.corootAt t (ground.getAt [] t.posFolds j) i
            * BPair.ofNat (ground.getAt 0 t.lenNums i)))
      (List.range t.rank) (fun i hi => ?_)) ?_
  · have hir : i < t.rank := ground.ltOfMem hi
    rw [ground.getAt_map 0 BPair.unit BPair.ofNat
        (ground.getAt [] t.posFolds j) i (by rw [hf]; exact hir),
      ground.getAt_map 0 BPair.unit _ (List.range t.cartan.length) i
        (by rw [ground.length_range, hcl]; exact hir),
      ground.getAt_range t.cartan.length i (by rw [hcl]; exact hir),
      show sertables.posCorootV t j
          = (List.range t.rank).map
            (gentable.corootAt t (ground.getAt [] t.posFolds j)) from rfl,
      ground.getAt_map_range BPair.unit _ t.rank i, if_pos hir,
      ← mul4rearr (BPair.ofNat
        (ground.getAt 0 (ground.getAt [] t.posFolds j) i))
        (BPair.ofNat F.scale)
        (BPair.ofNat (ground.getAt 0 t.lenNums i))
        (gentable.corootAt t (ground.getAt [] t.posFolds j) i)]
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.mul_congr_left
        (BPair.ofNat_mul F.scale (ground.getAt 0 t.lenNums i)))
  · refine BPair.oneValue_trans
      (ground.foldB_mul_left (BPair.ofNat F.scale) _ (List.range t.rank)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.sum_map _ (List.range t.rank)))

/-- `lem:serstable`(ii)'s content cap at a table whose positive
list's members carry the displayed cap: every `θ` content's square
sits at or below four scales. -/
private theorem contentCapGen (t : gentable.Table)
    (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (L : List (List BPair)) (hfam : row.thetaFamRead t L)
    (hdata : ∀ j, j < t.posFolds.length →
      (ground.getAt [] t.posFolds j).length = t.rank
        ∧ gentable.formNum t (ground.getAt [] t.posFolds j)
            (ground.getAt [] t.posFolds j) ≤ BPair.ofNat 4)
    (nu : List BPair) (hmem : nu ∈ L) :
    sertables.dotB F nu nu ≤ BPair.ofNat (4 * F.scale) := by
  have hscale : (BPair.ofNat F.scale * BPair.ofNat 4).oneValue
      (BPair.ofNat (4 * F.scale)) := by
    rw [Nat.mul_comm 4 F.scale]
    exact BPair.oneValue_symm (BPair.ofNat_mul F.scale 4)
  match hfam.2.2 nu hmem with
  | Or.inl he =>
    have hu : (sertables.dotB F nu nu).oneValue BPair.unit := by
      rw [he]
      exact elim.dotP_replL t.rank
        (elim.matVec F.gram (List.replicate t.rank BPair.unit))
    exact ground.leB_congr_left (BPair.oneValue_symm hu)
      (ground.unitLeOfNat (4 * F.scale))
  | Or.inr ⟨j, hj1, hcase⟩ =>
    have hj : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj1
    have hsq : (sertables.dotB F nu nu).oneValue
        (sertables.dotB F (sertables.posCorootV t j)
          (sertables.posCorootV t j)) := by
      match hcase with
      | Or.inl hpb =>
        rw [hpb]
        exact BPair.oneValue_trans
          (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
          (sertables.dotB_congrR F _ _ _ (poly.pnorm_oneValue _))
      | Or.inr hnb =>
        rw [hnb]
        refine BPair.oneValue_trans
          (BPair.oneValue_trans
            (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
            (sertables.dotB_congrR F _ _ _ (poly.pnorm_oneValue _))) ?_
        exact BPair.oneValue_of_eq
          (sertables.dotB_negSq F (sertables.posCorootV t j))
    refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.oneValue_trans hsq
        (dotB_posSq t F hshape hgram j (hdata j hj).1))) ?_
    exact ground.leB_congr_right hscale
      (ground.leB_mulR (ground.unitLeOfNat F.scale) (hdata j hj).2)

/-- `lem:serstable`(ii)'s content cap at the `B` series: the tex's
displayed lengths cap every `θ` content's square. -/
theorem contentCap_B : ∀ (l : Nat) (F : sertables.FundData)
    (L : List (List BPair)),
    sertables.fundShape (sertables.tableB l) F →
    sertables.gramRead (sertables.tableB l) F →
    row.thetaFamRead (sertables.tableB l) L →
    ∀ z ∈ L, sertables.dotB F z z ≤ BPair.ofNat (4 * F.scale) :=
  fun l F L hshape hgram hfam z hz =>
    contentCapGen (sertables.tableB l) F hshape hgram L hfam
      (foldsB_data l) z hz

/-- `lem:serstable`(ii)'s content cap at the `C` series. -/
theorem contentCap_C : ∀ (l : Nat) (F : sertables.FundData)
    (L : List (List BPair)),
    sertables.fundShape (sertables.tableC l) F →
    sertables.gramRead (sertables.tableC l) F →
    row.thetaFamRead (sertables.tableC l) L →
    ∀ z ∈ L, sertables.dotB F z z ≤ BPair.ofNat (4 * F.scale) :=
  fun l F L hshape hgram hfam z hz =>
    contentCapGen (sertables.tableC l) F hshape hgram L hfam
      (foldsC_data l) z hz

/-- `lem:serstable`(ii)'s content cap at the `D` series. -/
theorem contentCap_D : ∀ (l : Nat) (F : sertables.FundData)
    (L : List (List BPair)),
    sertables.fundShape (sertables.tableD l) F →
    sertables.gramRead (sertables.tableD l) F →
    row.thetaFamRead (sertables.tableD l) L →
    ∀ z ∈ L, sertables.dotB F z z ≤ BPair.ofNat (4 * F.scale) :=
  fun l F L hshape hgram hfam z hz =>
    contentCapGen (sertables.tableD l) F hshape hgram L hfam
      (foldsD_data l) z hz

/-- The `B` rows off their own key: every further coroot pair of
the stored Cartan row sits at or below the sum's unit. -/
theorem cartanBOff (l i j : Nat) (hi : i < l) (hj : j < l)
    (hij : ¬ j = i) :
    ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanB l) i) j ≤ BPair.unit := by
  unfold sertables.cartanB
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i j hi hj,
    if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
  by_cases h1 : (i + 2 == l && j == i + 1) = true
  · rw [if_pos h1]
    decide +kernel
  · rw [if_neg h1]
    by_cases h2 : (j + 1 == i || j == i + 1) = true
    · rw [if_pos h2]
      decide +kernel
    · rw [if_neg h2]
      exact ground.leB_refl _

/-- The `C` rows off their own key: every further coroot pair of
the stored Cartan row sits at or below the sum's unit. -/
private theorem cartanCOff (l i j : Nat) (hi : i < l) (hj : j < l)
    (hij : ¬ j = i) :
    ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanC l) i) j ≤ BPair.unit := by
  unfold sertables.cartanC
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i j hi hj,
    if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
  by_cases h1 : (i + 1 == l && j + 2 == l) = true
  · rw [if_pos h1]
    decide +kernel
  · rw [if_neg h1]
    by_cases h2 : (j + 1 == i || j == i + 1) = true
    · rw [if_pos h2]
      decide +kernel
    · rw [if_neg h2]
      exact ground.leB_refl _

/-- The `D` rows off their own key: every further coroot pair of
the stored Cartan row sits at or below the sum's unit. -/
theorem cartanDOff (l i j : Nat) (hi : i < l) (hj : j < l)
    (hij : ¬ j = i) :
    ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanD l) i) j ≤ BPair.unit := by
  unfold sertables.cartanD
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i j hi hj,
    if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
  by_cases h1 : (i + 1 == l) = true
  · rw [if_pos h1]
    by_cases h2 : (j + 3 == l) = true
    · rw [if_pos h2]
      decide +kernel
    · rw [if_neg h2]
      exact ground.leB_refl _
  · rw [if_neg h1]
    by_cases h2 : (j + 1 == l) = true
    · rw [if_pos h2]
      by_cases h3 : (i + 3 == l) = true
      · rw [if_pos h3]
        decide +kernel
      · rw [if_neg h3]
        exact ground.leB_refl _
    · rw [if_neg h2]
      by_cases h3 : (j + 1 == i || j == i + 1) = true
      · rw [if_pos h3]
        decide +kernel
      · rw [if_neg h3]
        exact ground.leB_refl _

/-- `lem:serstable`(ii)'s row values at the `B` series: at a
dominant target the even count is the target content's own
multiplicity and the odd count the letter fold. -/
theorem rowValues_B : ∀ (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (mv : List BPair) (ρv : List Nat) (nu0 : List BPair),
    mv.length = l →
    (∀ i, i < l → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd mv
        (sertables.rhoV (sertables.tableB l)))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i))) →
    (∀ k, k < l → 1 ≤ ground.getAt 0 ρv k) →
    sertables.fundShape (sertables.tableB l) F →
    sertables.gramRead (sertables.tableB l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableB l) →
    sertables.simplePosRead (sertables.tableB l) F →
    sertables.rhoDotRead (sertables.tableB l) F →
    row.rhoLenRead (sertables.tableB l) F →
    sertables.wShapeRead (sertables.tableB l) Wl →
    assembly.wCloseRead (sertables.tableB l) Wl →
    assembly.wDomAt (sertables.tableB l) Wl wits
      (poly.pnorm (elim.vecAdd mv
        (sertables.rhoV (sertables.tableB l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd mv
      (sertables.rhoV (sertables.tableB l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd mv
      (sertables.rhoV (sertables.tableB l)))) →
    memberchar.mShapeRead (sertables.tableB l) L →
    row.thetaFamRead (sertables.tableB l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd mv nu0)) k) →
    memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd mv
            (sertables.rhoV (sertables.tableB l)))) nu0)) false
      = ground.countOf nu0 L
    ∧ memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd mv
            (sertables.rhoV (sertables.tableB l)))) nu0)) true
      = letterFoldAt (sertables.tableB l) ρv nu0 L := by
  intro l F Wl wits L mv ρv nu0 hml hkap hpos hshape hgram hgsym hsqr
    hsp hrd hrho hwsh hclose hdom htop hksq hmsh hfam hn0pos hdomin
  exact rowValuesAt (sertables.tableB l) F Wl wits L mv ρv nu0
    hml hkap hpos
    (fun q hq => ground.matOf_rowLength ([] : List BPair) l l _ q hq)
    (fun q hq => cartanBDiag l q hq)
    (fun p q hp hq hqp => cartanBOff l p q hp hq hqp)
    hshape hgram hgsym hsqr hsp hrd hrho hwsh hclose hdom htop hksq
    hmsh hfam hn0pos hdomin
    (contentCap_B l F L hshape hgram hfam)

/-- `lem:serstable`(ii)'s row values at the `C` series. -/
theorem rowValues_C : ∀ (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (mv : List BPair) (ρv : List Nat) (nu0 : List BPair),
    mv.length = l →
    (∀ i, i < l → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd mv
        (sertables.rhoV (sertables.tableC l)))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i))) →
    (∀ k, k < l → 1 ≤ ground.getAt 0 ρv k) →
    sertables.fundShape (sertables.tableC l) F →
    sertables.gramRead (sertables.tableC l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableC l) →
    sertables.simplePosRead (sertables.tableC l) F →
    sertables.rhoDotRead (sertables.tableC l) F →
    row.rhoLenRead (sertables.tableC l) F →
    sertables.wShapeRead (sertables.tableC l) Wl →
    assembly.wCloseRead (sertables.tableC l) Wl →
    assembly.wDomAt (sertables.tableC l) Wl wits
      (poly.pnorm (elim.vecAdd mv
        (sertables.rhoV (sertables.tableC l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd mv
      (sertables.rhoV (sertables.tableC l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd mv
      (sertables.rhoV (sertables.tableC l)))) →
    memberchar.mShapeRead (sertables.tableC l) L →
    row.thetaFamRead (sertables.tableC l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd mv nu0)) k) →
    memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd mv
            (sertables.rhoV (sertables.tableC l)))) nu0)) false
      = ground.countOf nu0 L
    ∧ memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd mv
            (sertables.rhoV (sertables.tableC l)))) nu0)) true
      = letterFoldAt (sertables.tableC l) ρv nu0 L := by
  intro l F Wl wits L mv ρv nu0 hml hkap hpos hshape hgram hgsym hsqr
    hsp hrd hrho hwsh hclose hdom htop hksq hmsh hfam hn0pos hdomin
  exact rowValuesAt (sertables.tableC l) F Wl wits L mv ρv nu0
    hml hkap hpos
    (fun q hq => ground.matOf_rowLength ([] : List BPair) l l _ q hq)
    (fun q hq => cartanCDiag l q hq)
    (fun p q hp hq hqp => cartanCOff l p q hp hq hqp)
    hshape hgram hgsym hsqr hsp hrd hrho hwsh hclose hdom htop hksq
    hmsh hfam hn0pos hdomin
    (contentCap_C l F L hshape hgram hfam)

/-- `lem:serstable`(ii)'s row values at the `D` series. -/
theorem rowValues_D : ∀ (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (mv : List BPair) (ρv : List Nat) (nu0 : List BPair),
    mv.length = l →
    (∀ i, i < l → (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd mv
        (sertables.rhoV (sertables.tableD l)))) i).oneValue
      (BPair.ofNat (ground.getAt 0 ρv i))) →
    (∀ k, k < l → 1 ≤ ground.getAt 0 ρv k) →
    sertables.fundShape (sertables.tableD l) F →
    sertables.gramRead (sertables.tableD l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableD l) →
    sertables.simplePosRead (sertables.tableD l) F →
    sertables.rhoDotRead (sertables.tableD l) F →
    row.rhoLenRead (sertables.tableD l) F →
    sertables.wShapeRead (sertables.tableD l) Wl →
    assembly.wCloseRead (sertables.tableD l) Wl →
    assembly.wDomAt (sertables.tableD l) Wl wits
      (poly.pnorm (elim.vecAdd mv
        (sertables.rhoV (sertables.tableD l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd mv
      (sertables.rhoV (sertables.tableD l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd mv
      (sertables.rhoV (sertables.tableD l)))) →
    memberchar.mShapeRead (sertables.tableD l) L →
    row.thetaFamRead (sertables.tableD l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd mv nu0)) k) →
    memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd mv
            (sertables.rhoV (sertables.tableD l)))) nu0)) false
      = ground.countOf nu0 L
    ∧ memberchar.convCount Wl L
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd mv
            (sertables.rhoV (sertables.tableD l)))) nu0)) true
      = letterFoldAt (sertables.tableD l) ρv nu0 L := by
  intro l F Wl wits L mv ρv nu0 hml hkap hpos hshape hgram hgsym hsqr
    hsp hrd hrho hwsh hclose hdom htop hksq hmsh hfam hn0pos hdomin
  exact rowValuesAt (sertables.tableD l) F Wl wits L mv ρv nu0
    hml hkap hpos
    (fun q hq => ground.matOf_rowLength ([] : List BPair) l l _ q hq)
    (fun q hq => cartanDDiag l q hq)
    (fun p q hp hq hqp => cartanDOff l p q hp hq hqp)
    hshape hgram hgsym hsqr hsp hrd hrho hwsh hclose hdom htop hksq
    hmsh hfam hn0pos hdomin
    (contentCap_D l F L hshape hgram hfam)


/-! ## The diagonal display: the member's own count

`lem:serstable`(ii)'s diagonal: at the member's own display the
row's two counts are the vacuum content's multiplicity on the even
side and the letter fold on the odd, so the display's cancellation
reads the diagonal count against the word's vacant-key count, the
rank their join — the tex's "the diagonal is the occupied support,
the word's distinct-value count", the vacuum's Kronecker defect the
same statement at the vacant word. -/

/-- The member's scaled display against the vacuum content: the
`ρ`-raise of the scaled member reads the raised member's own
representative at the vacant content. -/
private theorem scaleKey (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) :
    poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecScale (BPair.ofNat 1) (memberV W l)))
        (sertables.rhoV t))
      = poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l) (sertables.rhoV t)))
          (List.replicate l BPair.unit)) := by
  have hml : (memberV W l).length = t.rank := memberVLen t W l hrk
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hsl : (elim.vecScale (BPair.ofNat 1) (memberV W l)).length
      = t.rank := by
    rw [elim.length_vecScale]
    exact hml
  have hA : (elim.vecAdd (memberV W l) (sertables.rhoV t)).length
      = t.rank := elim.length_vecAdd _ _ t.rank hml hrl
  have hrep : (List.replicate l BPair.unit).length = t.rank := by
    rw [ground.length_replicate, hrk]
  have e1 : poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecScale (BPair.ofNat 1) (memberV W l)))
        (sertables.rhoV t))
      = poly.pnorm (elim.vecAdd
          (elim.vecScale (BPair.ofNat 1) (memberV W l))
          (sertables.rhoV t)) :=
    elim.pnorm_vecAdd_left _ _ (by rw [hsl, hrl])
  have e2 : poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l) (sertables.rhoV t)))
        (List.replicate l BPair.unit))
      = poly.pnorm (elim.vecAdd
          (elim.vecAdd (memberV W l) (sertables.rhoV t))
          (List.replicate l BPair.unit)) :=
    elim.pnorm_vecAdd_left _ _ (by rw [hA, hrep])
  have e3 : poly.pnorm (elim.vecAdd
        (elim.vecScale (BPair.ofNat 1) (memberV W l))
        (sertables.rhoV t))
      = poly.pnorm (elim.vecAdd
          (elim.vecAdd (memberV W l) (sertables.rhoV t))
          (List.replicate l BPair.unit)) := by
    refine poly.pnorm_congr _ _ ?_ (poly.oneValue_of_entries _ _ ?_ ?_)
    · rw [elim.length_vecAdd _ _ t.rank hsl hrl,
        elim.length_vecAdd _ _ t.rank hA hrep]
    · rw [elim.length_vecAdd _ _ t.rank hsl hrl,
        elim.length_vecAdd _ _ t.rank hA hrep]
    · intro i hi
      rw [elim.length_vecAdd _ _ t.rank hsl hrl] at hi
      rw [elim.getAt_vecAdd _ _ i (by rw [hsl]; exact hi)
          (by rw [hrl]; exact hi),
        elim.getAt_vecScale (BPair.ofNat 1) (memberV W l) i
          (by rw [hml]; exact hi),
        elim.getAt_vecAdd _ _ i (by rw [hA]; exact hi)
          (by rw [hrep]; exact hi),
        elim.getAt_vecAdd _ _ i (by rw [hml]; exact hi)
          (by rw [hrl]; exact hi),
        ground.getAt_replicate BPair.unit BPair.unit l i
          (show i < l by rw [← hrk]; exact hi)]
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.ofNat_one_mul _) (BPair.oneValue_refl _))
        (BPair.oneValue_symm (BPair.add_unit _))
  exact e1.trans (e3.trans e2.symm)

/-- `lem:serstable`(ii)'s diagonal display at the `B` series: the
member's own channel count joins the word's vacant-key count to the
rank. -/
theorem diagRead_B : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (cVs : List (List BPair)),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    sertables.fundShape (sertables.tableB l) F →
    sertables.gramRead (sertables.tableB l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableB l) →
    sertables.simplePosRead (sertables.tableB l) F →
    sertables.rhoDotRead (sertables.tableB l) F →
    row.rhoLenRead (sertables.tableB l) F →
    sertables.wShapeRead (sertables.tableB l) Wl →
    assembly.wCloseRead (sertables.tableB l) Wl →
    assembly.wDomAt (sertables.tableB l) Wl wits
      (poly.pnorm (elim.vecAdd (memberV W l)
        (sertables.rhoV (sertables.tableB l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableB l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableB l)))) →
    memberchar.mShapeRead (sertables.tableB l) L →
    row.thetaFamRead (sertables.tableB l) L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l)
        (List.replicate l BPair.unit))) k) →
    steinberg.memberAt (sertables.tableB l) Wl L cVs
      (poly.pnorm (elim.vecScale (BPair.ofNat 1) (memberV W l))) →
    ground.countOf (poly.pnorm (elim.vecScale (BPair.ofNat 1)
        (memberV W l))) cVs
      + ground.countOf 0 (member W l) = l := by
  intro W l F Wl wits L cVs hs hl hshape hgram hgsym hsqr hsp hrd hrho
    hwsh hclose hdom htop hksq hmsh hfam hdomin hmem
  have hcount : ground.countOf (List.replicate l BPair.unit) L = l :=
    hfam.1
  have hpos : 0 < ground.countOf (List.replicate l BPair.unit) L := by
    rw [hcount]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 1)
      (Nat.le_trans (Nat.le_add_left 2 W.length) hl)
  obtain ⟨hfalse, htrue⟩ := rowValues_B l F Wl wits L
    (memberV W l) (memberRho W l) (List.replicate l BPair.unit)
    (memberVLen (sertables.tableB l) W l rfl)
    (fun i hi => kapAt (sertables.tableB l) W l rfl hi)
    (fun k hk => memberRhoPos W l k hk)
    hshape hgram hgsym hsqr hsp hrd
    hrho hwsh hclose hdom htop hksq hmsh hfam hpos hdomin
  have hvac : letterFoldAt (sertables.tableB l) (memberRho W l)
      (List.replicate l ground.BPair.unit) L
      = ground.countOf 0 (member W l) :=
    letterFold_vac_B W l F L hshape hgram hsp hrd hrho hfam
  have hmem' : ground.countOf (poly.pnorm (elim.vecScale
        (BPair.ofNat 1) (memberV W l))) cVs
      + memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l)
            (sertables.rhoV (sertables.tableB l))))
          (List.replicate l BPair.unit))) true
    = memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l)
          (sertables.rhoV (sertables.tableB l))))
        (List.replicate l BPair.unit))) false := by
    rw [← scaleKey (sertables.tableB l) W l rfl]
    exact hmem
  rw [hfalse, htrue, hvac, hcount] at hmem'
  exact hmem'

/-- `lem:serstable`(ii)'s diagonal display at the `C` series. -/
theorem diagRead_C : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (cVs : List (List BPair)),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    sertables.fundShape (sertables.tableC l) F →
    sertables.gramRead (sertables.tableC l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableC l) →
    sertables.simplePosRead (sertables.tableC l) F →
    sertables.rhoDotRead (sertables.tableC l) F →
    row.rhoLenRead (sertables.tableC l) F →
    sertables.wShapeRead (sertables.tableC l) Wl →
    assembly.wCloseRead (sertables.tableC l) Wl →
    assembly.wDomAt (sertables.tableC l) Wl wits
      (poly.pnorm (elim.vecAdd (memberV W l)
        (sertables.rhoV (sertables.tableC l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableC l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableC l)))) →
    memberchar.mShapeRead (sertables.tableC l) L →
    row.thetaFamRead (sertables.tableC l) L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l)
        (List.replicate l BPair.unit))) k) →
    steinberg.memberAt (sertables.tableC l) Wl L cVs
      (poly.pnorm (elim.vecScale (BPair.ofNat 1) (memberV W l))) →
    ground.countOf (poly.pnorm (elim.vecScale (BPair.ofNat 1)
        (memberV W l))) cVs
      + ground.countOf 0 (member W l) = l := by
  intro W l F Wl wits L cVs hs hl hshape hgram hgsym hsqr hsp hrd hrho
    hwsh hclose hdom htop hksq hmsh hfam hdomin hmem
  have hcount : ground.countOf (List.replicate l BPair.unit) L = l :=
    hfam.1
  have hpos : 0 < ground.countOf (List.replicate l BPair.unit) L := by
    rw [hcount]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 1)
      (Nat.le_trans (Nat.le_add_left 2 W.length) hl)
  obtain ⟨hfalse, htrue⟩ := rowValues_C l F Wl wits L
    (memberV W l) (memberRho W l) (List.replicate l BPair.unit)
    (memberVLen (sertables.tableC l) W l rfl)
    (fun i hi => kapAt (sertables.tableC l) W l rfl hi)
    (fun k hk => memberRhoPos W l k hk)
    hshape hgram hgsym hsqr hsp hrd
    hrho hwsh hclose hdom htop hksq hmsh hfam hpos hdomin
  have hvac : letterFoldAt (sertables.tableC l) (memberRho W l)
      (List.replicate l ground.BPair.unit) L
      = ground.countOf 0 (member W l) :=
    letterFold_vac_C W l F L hshape hgram hsp hrd hrho hfam
  have hmem' : ground.countOf (poly.pnorm (elim.vecScale
        (BPair.ofNat 1) (memberV W l))) cVs
      + memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l)
            (sertables.rhoV (sertables.tableC l))))
          (List.replicate l BPair.unit))) true
    = memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l)
          (sertables.rhoV (sertables.tableC l))))
        (List.replicate l BPair.unit))) false := by
    rw [← scaleKey (sertables.tableC l) W l rfl]
    exact hmem
  rw [hfalse, htrue, hvac, hcount] at hmem'
  exact hmem'

/-- `lem:serstable`(ii)'s diagonal display at the `D` series. -/
theorem diagRead_D : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (cVs : List (List BPair)),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    sertables.fundShape (sertables.tableD l) F →
    sertables.gramRead (sertables.tableD l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableD l) →
    sertables.simplePosRead (sertables.tableD l) F →
    sertables.rhoDotRead (sertables.tableD l) F →
    row.rhoLenRead (sertables.tableD l) F →
    sertables.wShapeRead (sertables.tableD l) Wl →
    assembly.wCloseRead (sertables.tableD l) Wl →
    assembly.wDomAt (sertables.tableD l) Wl wits
      (poly.pnorm (elim.vecAdd (memberV W l)
        (sertables.rhoV (sertables.tableD l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableD l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableD l)))) →
    memberchar.mShapeRead (sertables.tableD l) L →
    row.thetaFamRead (sertables.tableD l) L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l)
        (List.replicate l BPair.unit))) k) →
    steinberg.memberAt (sertables.tableD l) Wl L cVs
      (poly.pnorm (elim.vecScale (BPair.ofNat 1) (memberV W l))) →
    ground.countOf (poly.pnorm (elim.vecScale (BPair.ofNat 1)
        (memberV W l))) cVs
      + ground.countOf 0 (member W l) = l := by
  intro W l F Wl wits L cVs hs hl hshape hgram hgsym hsqr hsp hrd hrho
    hwsh hclose hdom htop hksq hmsh hfam hdomin hmem
  have hcount : ground.countOf (List.replicate l BPair.unit) L = l :=
    hfam.1
  have hpos : 0 < ground.countOf (List.replicate l BPair.unit) L := by
    rw [hcount]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 1)
      (Nat.le_trans (Nat.le_add_left 2 W.length) hl)
  obtain ⟨hfalse, htrue⟩ := rowValues_D l F Wl wits L
    (memberV W l) (memberRho W l) (List.replicate l BPair.unit)
    (memberVLen (sertables.tableD l) W l rfl)
    (fun i hi => kapAt (sertables.tableD l) W l rfl hi)
    (fun k hk => memberRhoPos W l k hk)
    hshape hgram hgsym hsqr hsp hrd
    hrho hwsh hclose hdom htop hksq hmsh hfam hpos hdomin
  have hvac : letterFoldAt (sertables.tableD l) (memberRho W l)
      (List.replicate l ground.BPair.unit) L
      = ground.countOf 0 (member W l) :=
    letterFold_vac_D W l F L hshape hgram hsp hrd hrho hfam
  have hmem' : ground.countOf (poly.pnorm (elim.vecScale
        (BPair.ofNat 1) (memberV W l))) cVs
      + memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l)
            (sertables.rhoV (sertables.tableD l))))
          (List.replicate l BPair.unit))) true
    = memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l)
          (sertables.rhoV (sertables.tableD l))))
        (List.replicate l BPair.unit))) false := by
    rw [← scaleKey (sertables.tableD l) W l rfl]
    exact hmem
  rw [hfalse, htrue, hvac, hcount] at hmem'
  exact hmem'


/-- The off-diagonal shuffle: the target's shifted display is the
shifted key at the content joined on, the two normed spellings one
list at the summands' exchange and regrouping. -/
private theorem offKey (t : gentable.Table) (W : List Nat) (l : Nat)
    (nu0 : List BPair) (hrk : t.rank = l)
    (hn : nu0.length = t.rank) :
    poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l) nu0))
        (sertables.rhoV t))
      = poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l) (sertables.rhoV t)))
          nu0) := by
  have hml : (memberV W l).length = t.rank := by
    show ((member W l).map BPair.ofNat).length = t.rank
    rw [ground.length_map, memberLen, hrk]
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have e1 : poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l) nu0))
        (sertables.rhoV t))
      = poly.pnorm (elim.vecAdd
          (elim.vecAdd (memberV W l) nu0) (sertables.rhoV t)) :=
    elim.pnorm_vecAdd_left _ _ (by
      rw [elim.length_vecAdd _ _ t.rank hml hn, hrl])
  have e2 : poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l) (sertables.rhoV t)))
        nu0)
      = poly.pnorm (elim.vecAdd
          (elim.vecAdd (memberV W l) (sertables.rhoV t)) nu0) :=
    elim.pnorm_vecAdd_left _ _ (by
      rw [elim.length_vecAdd _ _ t.rank hml hrl, hn])
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [elim.vecAdd_assoc, elim.vecAdd_comm nu0 (sertables.rhoV t),
    ← elim.vecAdd_assoc]


/-! ## The confinement kit: the dominance refutation and the
target's entry reads -/

/-- A pair below the unit: the swapped occupied read against the
sum's unit. -/
private theorem negLtUnit (m : Nat) :
    (BPair.ofNat (m + 1)).swap < BPair.unit := by
  show (BPair.ofNat (m + 1)).swap.fst + BPair.unit.snd
    < BPair.unit.fst + (BPair.ofNat (m + 1)).swap.snd
  show Pos.one + Pos.one < Pos.one + (posOfSucc m + Pos.one)
  rw [ground.add_comm (posOfSucc m) Pos.one, ← ground.add_assoc]
  exact ground.posLtSelfAdd (Pos.one + Pos.one) (posOfSucc m)

/-- The dominance refutation: an entry at the lower-side count pair
refuses the at-or-beyond-unit read. -/
private theorem domRefuse {x : BPair} (p m : Nat)
    (h : x.oneValue (BPair.ofCounts p (p + (m + 1))))
    (hle : BPair.unit ≤ x) : False := by
  have hx : ((BPair.ofNat (m + 1)).swap).oneValue x :=
    BPair.oneValue_symm (BPair.oneValue_trans h
      (BPair.oneValue_trans
        (BPair.ofCounts_crossed (by rw [Nat.zero_add]))
        (countsNeg (m + 1))))
  exact ground.leB_not_lt hle
    (BPair.lt_congr hx (BPair.oneValue_refl BPair.unit) (negLtUnit m))

/-- The count pair's swap exchanges the counts. -/
private theorem swapCounts (p q : Nat) :
    ((BPair.ofCounts p q).swap).oneValue (BPair.ofCounts q p) := by
  rw [ground.BPair.ofCounts_swap p q]
  exact BPair.oneValue_refl _

/-- The target's entry at a key beyond the word: the member's
vacant entry withdraws and the entry is the content's own. -/
private theorem targetAt (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) (nu0 : List BPair) (hn0 : nu0.length = t.rank)
    (y : Nat) (hy : y < l) (hWy : W.length ≤ y) :
    (ground.getAt BPair.unit
        (poly.pnorm (elim.vecAdd (memberV W l) nu0)) y).oneValue
      (ground.getAt BPair.unit nu0 y) := by
  have hyr : y < t.rank := by rw [hrk]; exact hy
  have hml : (memberV W l).length = t.rank := by
    show ((member W l).map BPair.ofNat).length = t.rank
    rw [ground.length_map, memberLen, hrk]
  show (ground.getAt BPair.unit
    ((elim.vecAdd (memberV W l) nu0).map BPair.norm) y).oneValue _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ y
      (by rw [elim.length_vecAdd _ _ t.rank hml hn0]; exact hyr),
    elim.getAt_vecAdd _ _ y (by rw [hml]; exact hyr)
      (by rw [hn0]; exact hyr)]
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  have hmi : ground.getAt BPair.unit (memberV W l) y
      = BPair.ofNat (ground.getAt 0 (member W l) y) :=
    ground.getAt_map 0 BPair.unit BPair.ofNat (member W l) y
      (by rw [memberLen]; exact hy)
  rw [hmi, memberZero W l y hWy]
  exact BPair.unit_add _

/-- The target's vacancy at a key beyond the word: a content entry
at the sum's unit reads the target's own entry there. -/
private theorem targetVac (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) (nu0 : List BPair) (hn0 : nu0.length = t.rank)
    (x : Nat) (hx : x < l) (hWx : W.length ≤ x)
    (hval : (ground.getAt BPair.unit nu0 x).oneValue BPair.unit) :
    ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) x = BPair.unit := by
  have hxr : x < t.rank := by rw [hrk]; exact hx
  have hml : (memberV W l).length = t.rank := by
    show ((member W l).map BPair.ofNat).length = t.rank
    rw [ground.length_map, memberLen, hrk]
  show ground.getAt BPair.unit
    ((elim.vecAdd (memberV W l) nu0).map BPair.norm) x = BPair.unit
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ x
      (by rw [elim.length_vecAdd _ _ t.rank hml hn0]; exact hxr),
    elim.getAt_vecAdd _ _ x (by rw [hml]; exact hxr)
      (by rw [hn0]; exact hxr)]
  have hmi : ground.getAt BPair.unit (memberV W l) x
      = BPair.ofNat (ground.getAt 0 (member W l) x) :=
    ground.getAt_map 0 BPair.unit BPair.ofNat (member W l) x
      (by rw [memberLen]; exact hx)
  rw [hmi, memberZero W l x hWx]
  have hn : (BPair.ofNat 0 + ground.getAt BPair.unit nu0 x).oneValue
      BPair.unit :=
    BPair.oneValue_trans (BPair.unit_add _) hval
  rw [BPair.norm_congr hn]
  rfl

/-- A coroot content's entry: the fold's column read at the
canonical representative. -/
private theorem nuAtP (t : gentable.Table) (j y : Nat)
    (hy : y < t.rank) :
    ground.getAt BPair.unit
        (poly.pnorm (sertables.posCorootV t j)) y
      = BPair.norm
          (corootAt t (getAt [] t.posFolds j) y) := by
  show ground.getAt BPair.unit
    ((sertables.posCorootV t j).map BPair.norm) y = _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ y
      (by rw [sertables.posCorootV_length]; exact hy)]
  show BPair.norm (ground.getAt BPair.unit
    ((List.range t.rank).map
      (gentable.corootAt t (getAt [] t.posFolds j))) y) = _
  rw [ground.getAt_map_range BPair.unit _ t.rank y, if_pos hy]

/-- A coroot content's balance partner's entry: the column read's
memberwise swap at the representative. -/
private theorem nuAtN (t : gentable.Table) (j y : Nat)
    (hy : y < t.rank) :
    ground.getAt BPair.unit
        (poly.pnorm (poly.neg (sertables.posCorootV t j))) y
      = BPair.norm
          ((corootAt t (getAt [] t.posFolds j) y).swap) := by
  show ground.getAt BPair.unit
    (((sertables.posCorootV t j).map BPair.swap).map BPair.norm) y = _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ y
      (by rw [ground.length_map, sertables.posCorootV_length]; exact hy),
    ground.getAt_map BPair.unit BPair.unit BPair.swap _ y
      (by rw [sertables.posCorootV_length]; exact hy)]
  show BPair.norm (ground.getAt BPair.unit
    ((List.range t.rank).map
      (gentable.corootAt t (getAt [] t.posFolds j))) y).swap = _
  rw [ground.getAt_map_range BPair.unit _ t.rank y, if_pos hy]



/-! ## The `B` confinement: each family's occupied columns sit at
its window with a lower-side and an upper-side companion beside
every occupied key -/

/-- The difference family's column at a key: vacant beyond the
window's top, and at or below it the window's top edge reads the
two companions. -/
private theorem confDiffB (l a b x : Nat) (hab : a < b) (hbl : b < l)
    (hx2 : 2 ≤ x) (hxl : x < l) :
    2 * fDiff a b x = nbB l (fDiff a b) x
    ∨ ((∃ y m1, x ≤ y + 2 ∧ y < l
          ∧ 2 * fDiff a b y + (m1 + 1) = nbB l (fDiff a b) y)
        ∧ (∃ y m2, x ≤ y + 2 ∧ y < l
          ∧ nbB l (fDiff a b) y + (m2 + 1) = 2 * fDiff a b y)) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 :=
    ⟨b - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a) hab)).symm⟩
  have hac : a ≤ c := Nat.le_of_succ_le_succ hab
  match Nat.lt_or_ge (c + 1) x with
  | .inl hbx =>
    refine Or.inl ?_
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
      ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        hx2)).symm⟩
    have hbm : c + 1 ≤ m := Nat.le_of_succ_le_succ hbx
    rw [nbB_succ,
      fDiff_hi a (c + 1) (m + 1)
        (Nat.not_lt_of_ge (Nat.le_succ_of_le hbm)),
      fDiff_hi a (c + 1) m (Nat.not_lt_of_ge hbm)]
    by_cases hml : m + 2 = l
    · rw [if_pos (ground.eqBeqOf hml)]
    · rw [if_neg (fun hb => hml (ground.beqEqOf hb)),
        fDiff_hi a (c + 1) (m + 2)
          (Nat.not_lt_of_ge (Nat.le_succ_of_le
            (Nat.le_succ_of_le hbm)))]
  | .inr hxb =>
    refine Or.inr ⟨?_, ?_⟩
    · by_cases hcl : c + 2 = l
      · refine ⟨c + 1, 1,
          Nat.le_trans hxb (Nat.le_add_right (c + 1) 2), hbl, ?_⟩
        rw [nbB_succ, if_pos (ground.eqBeqOf hcl),
          fDiff_hi a (c + 1) (c + 1) (Nat.lt_irrefl (c + 1)),
          fDiff_in a (c + 1) c hac (Nat.lt_succ_self c)]
      · refine ⟨c + 1, 0,
          Nat.le_trans hxb (Nat.le_add_right (c + 1) 2), hbl, ?_⟩
        rw [nbB_succ, if_neg (fun hb => hcl (ground.beqEqOf hb)),
          fDiff_hi a (c + 1) (c + 1) (Nat.lt_irrefl (c + 1)),
          fDiff_in a (c + 1) c hac (Nat.lt_succ_self c),
          fDiff_hi a (c + 1) (c + 2)
            (Nat.not_lt_of_ge (Nat.le_succ (c + 1)))]
    · have hc1 : 1 ≤ c := Nat.le_of_succ_le_succ (Nat.le_trans hx2 hxb)
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 :=
        ⟨c - 1, (ground.subAdd hc1).symm⟩
      have hyl : d + 1 < l :=
        Nat.lt_trans (Nat.lt_succ_self (d + 1)) hbl
      have hy2 : x ≤ d + 1 + 2 :=
        Nat.le_trans hxb (Nat.le_succ (d + 2))
      have hne : ¬ d + 2 = l := Nat.ne_of_lt hbl
      by_cases had : a ≤ d
      · refine ⟨d + 1, 0, hy2, hyl, ?_⟩
        rw [nbB_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
          fDiff_in a (d + 2) d had
            (Nat.lt_trans (Nat.lt_succ_self d) (Nat.lt_succ_self (d + 1))),
          fDiff_hi a (d + 2) (d + 2) (Nat.lt_irrefl (d + 2)),
          fDiff_in a (d + 2) (d + 1) (Nat.le_succ_of_le had)
            (Nat.lt_succ_self (d + 1))]
      · refine ⟨d + 1, 1, hy2, hyl, ?_⟩
        rw [nbB_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
          fDiff_lo a (d + 2) d had,
          fDiff_hi a (d + 2) (d + 2) (Nat.lt_irrefl (d + 2)),
          fDiff_in a (d + 2) (d + 1) hac (Nat.lt_succ_self (d + 1))]


/-- The `B` sum family's column at a key: vacant beyond the one
window's top, the window's two edges holding the companions. -/
private theorem confSumB (l a b x : Nat) (hab : a < b) (hbl : b < l)
    (hx2 : 2 ≤ x) (hxl : x < l) :
    2 * fSumB l a b x = nbB l (fSumB l a b) x
    ∨ ((∃ y m1, x ≤ y + 2 ∧ y < l
          ∧ 2 * fSumB l a b y + (m1 + 1) = nbB l (fSumB l a b) y)
        ∧ (∃ y m2, x ≤ y + 2 ∧ y < l
          ∧ nbB l (fSumB l a b) y + (m2 + 1) = 2 * fSumB l a b y)) := by
  match Nat.lt_or_ge b x with
  | .inl hbx =>
    refine Or.inl ?_
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
      ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        hx2)).symm⟩
    have hbm : b ≤ m := Nat.le_of_succ_le_succ hbx
    rw [nbB_succ,
      fSumB_hi l a b (m + 1) (Nat.le_succ_of_le hbm) hxl,
      fSumB_hi l a b m hbm
        (Nat.lt_trans (Nat.lt_succ_self m) hxl)]
    by_cases hml : m + 2 = l
    · rw [if_pos (ground.eqBeqOf hml)]
    · rw [if_neg (fun hb => hml (ground.beqEqOf hb)),
        fSumB_hi l a b (m + 2)
          (Nat.le_succ_of_le (Nat.le_succ_of_le hbm))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hxl) hml)]
  | .inr hxb =>
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 :=
      ⟨b - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
        hab)).symm⟩
    have hac : a ≤ c := Nat.le_of_succ_le_succ hab
    refine Or.inr ⟨?_, ?_⟩
    · by_cases hb1 : a = c
      · -- the one-key window: the lower companion sits below it
        have ha1 : 1 ≤ a := by
          rw [hb1]
          exact Nat.le_of_succ_le_succ (Nat.le_trans hx2 hxb)
        obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 :=
          ⟨a - 1, (ground.subAdd ha1).symm⟩
        have hyl : d < l :=
          Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self d) hab) hbl
        have hy2 : x ≤ d + 2 := by
          rw [show d + 2 = d + 1 + 1 from rfl, hb1]
          exact hxb
        have hmd : fSumB l (d + 1) (c + 1) (d + 1) = 1 :=
          fSumB_mid l (d + 1) (c + 1) (d + 1) (Nat.le_refl (d + 1))
            (by rw [← hb1]; exact Nat.lt_succ_self (d + 1))
        match d, hyl, hy2 with
        | 0, hyl, hy2 =>
          refine ⟨0, 0, hy2, hyl, ?_⟩
          rw [nbB_zero, if_pos (Nat.lt_trans hab hbl),
            fSumB_lo l 1 (c + 1) 0
              (Nat.not_le_of_lt (Nat.lt_succ_self 0))
              (Nat.not_le_of_lt (Nat.lt_of_lt_of_le
                (Nat.lt_succ_self 0) (Nat.le_of_lt hab))),
            hmd]
        | d' + 1, hyl, hy2 =>
          refine ⟨d' + 1, 0, hy2, hyl, ?_⟩
          have hne : ¬ d' + 2 = l := by
            rw [hb1]
            exact Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self c) hbl)
          rw [nbB_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
            fSumB_lo l (d' + 2) (c + 1) (d' + 1)
              (Nat.not_le_of_lt (Nat.lt_succ_self (d' + 1)))
              (Nat.not_le_of_lt (Nat.lt_of_lt_of_le
                (Nat.lt_succ_self (d' + 1)) (Nat.le_of_lt hab))),
            fSumB_lo l (d' + 2) (c + 1) d'
              (Nat.not_le_of_lt (Nat.lt_trans (Nat.lt_succ_self d')
                (Nat.lt_succ_self (d' + 1))))
              (Nat.not_le_of_lt (Nat.lt_of_lt_of_le
                (Nat.lt_trans (Nat.lt_succ_self d')
                  (Nat.lt_succ_self (d' + 1))) (Nat.le_of_lt hab))),
            hmd]
      · -- the window beyond one key: the lower companion at the
        -- window's top key
        have hd1 : a < c := Nat.lt_of_le_of_ne hac hb1
        obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 :=
          ⟨c - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
            hd1)).symm⟩
        have had : a ≤ d := Nat.le_of_succ_le_succ hd1
        have hyl : d + 1 < l :=
          Nat.lt_trans (Nat.lt_succ_self (d + 1)) hbl
        have hy2 : x ≤ d + 1 + 2 :=
          Nat.le_trans hxb (Nat.le_succ (d + 2))
        refine ⟨d + 1, 0, hy2, hyl, ?_⟩
        have hne : ¬ d + 2 = l := Nat.ne_of_lt hbl
        rw [nbB_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
          fSumB_mid l a (d + 2) d had
            (Nat.lt_trans (Nat.lt_succ_self d)
              (Nat.lt_succ_self (d + 1))),
          fSumB_hi l a (d + 2) (d + 2) (Nat.le_refl (d + 2)) hbl,
          fSumB_mid l a (d + 2) (d + 1) (Nat.le_succ_of_le had)
            (Nat.lt_succ_self (d + 1))]
    · -- the upper companion at the window's beyond-key
      have hy2 : x ≤ c + 1 + 2 :=
        Nat.le_trans hxb (Nat.le_add_right (c + 1) 2)
      by_cases hcl : c + 2 = l
      · refine ⟨c + 1, 1, hy2, hbl, ?_⟩
        rw [nbB_succ, if_pos (ground.eqBeqOf hcl),
          fSumB_mid l a (c + 1) c hac (Nat.lt_succ_self c),
          fSumB_hi l a (c + 1) (c + 1) (Nat.le_refl (c + 1)) hbl]
      · refine ⟨c + 1, 0, hy2, hbl, ?_⟩
        have hc2l : c + 2 < l :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hbl) hcl
        rw [nbB_succ, if_neg (fun hb => hcl (ground.beqEqOf hb)),
          fSumB_mid l a (c + 1) c hac (Nat.lt_succ_self c),
          fSumB_hi l a (c + 1) (c + 1) (Nat.le_refl (c + 1)) hbl,
          fSumB_hi l a (c + 1) (c + 2)
            (Nat.le_succ_of_le (Nat.le_refl (c + 1))) hc2l]

/-- The `B` short family's column at a key: vacant beyond the
window's first key, whose two sides hold the companions. -/
private theorem confShortB (l a x : Nat) (hal : a < l)
    (hx2 : 2 ≤ x) (hxl : x < l) :
    2 * fDiff a l x = nbB l (fDiff a l) x
    ∨ ((∃ y m1, x ≤ y + 2 ∧ y < l
          ∧ 2 * fDiff a l y + (m1 + 1) = nbB l (fDiff a l) y)
        ∧ (∃ y m2, x ≤ y + 2 ∧ y < l
          ∧ nbB l (fDiff a l) y + (m2 + 1) = 2 * fDiff a l y)) := by
  match Nat.lt_or_ge a x with
  | .inl hax =>
    refine Or.inl ?_
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
      ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        hx2)).symm⟩
    have ham : a ≤ m := Nat.le_of_succ_le_succ hax
    rw [nbB_succ,
      fDiff_in a l (m + 1) (Nat.le_succ_of_le ham) hxl,
      fDiff_in a l m ham (Nat.lt_trans (Nat.lt_succ_self m) hxl)]
    by_cases hml : m + 2 = l
    · rw [if_pos (ground.eqBeqOf hml)]
    · rw [if_neg (fun hb => hml (ground.beqEqOf hb)),
        fDiff_in a l (m + 2)
          (Nat.le_succ_of_le (Nat.le_succ_of_le ham))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hxl) hml)]
  | .inr hxa =>
    have ha2 : 2 ≤ a := Nat.le_trans hx2 hxa
    obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 :=
      ⟨a - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        ha2)).symm⟩
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 :=
      ⟨d - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
        (Nat.le_of_succ_le_succ ha2))).symm⟩
    refine Or.inr ⟨?_, ?_⟩
    · -- the lower companion below the window
      refine ⟨e + 1, 0,
        Nat.le_trans hxa (Nat.le_succ (e + 2)),
        Nat.lt_trans (Nat.lt_succ_self (e + 1)) hal, ?_⟩
      have hne : ¬ e + 2 = l := Nat.ne_of_lt hal
      rw [nbB_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
        fDiff_lo (e + 2) l (e + 1)
          (Nat.not_le_of_lt (Nat.lt_succ_self (e + 1))),
        fDiff_lo (e + 2) l e
          (Nat.not_le_of_lt (Nat.lt_trans (Nat.lt_succ_self e)
            (Nat.lt_succ_self (e + 1)))),
        fDiff_in (e + 2) l (e + 2) (Nat.le_refl (e + 2)) hal]
    · -- the upper companion at the window's first key
      refine ⟨e + 2, ?_⟩
      by_cases hal1 : e + 3 = l
      · refine ⟨1, Nat.le_trans hxa (Nat.le_add_right (e + 2) 2),
          hal, ?_⟩
        rw [nbB_succ, if_pos (ground.eqBeqOf hal1),
          fDiff_lo (e + 2) l (e + 1)
            (Nat.not_le_of_lt (Nat.lt_succ_self (e + 1))),
          fDiff_in (e + 2) l (e + 2) (Nat.le_refl (e + 2)) hal]
      · refine ⟨0, Nat.le_trans hxa (Nat.le_add_right (e + 2) 2),
          hal, ?_⟩
        have h3l : e + 3 < l :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hal) hal1
        rw [nbB_succ, if_neg (fun hb => hal1 (ground.beqEqOf hb)),
          fDiff_lo (e + 2) l (e + 1)
            (Nat.not_le_of_lt (Nat.lt_succ_self (e + 1))),
          fDiff_in (e + 2) l (e + 2) (Nat.le_refl (e + 2)) hal,
          fDiff_in (e + 2) l (e + 3)
            (Nat.le_succ_of_le (Nat.le_refl (e + 2))) h3l]


/-- Two keys within one of a middle key bound that key's doubled
read against their sum, either way, by two. -/
private theorem magPairB (x u v : Nat) (h1 : x ≤ u + 1) (h2 : x ≤ v + 1)
    (h3 : u ≤ x + 1) (h4 : v ≤ x + 1) :
    2 * x ≤ u + v + 2 ∧ u + v ≤ 2 * x + 2 := by
  have hp : ∀ p q : Nat, p + 1 + (q + 1) = p + q + 2 := fun p q => by
    rw [← Nat.add_assoc (p + 1) q 1, Nat.add_right_comm p 1 q]
  refine ⟨?_, ?_⟩
  · rw [Nat.two_mul]
    exact Nat.le_trans (Nat.add_le_add h1 h2) (Nat.le_of_eq (hp u v))
  · rw [Nat.two_mul]
    exact Nat.le_trans (Nat.add_le_add h3 h4) (Nat.le_of_eq (hp x x))

/-- A family capped at two, at or below one at the first key and
varying by at most one along consecutive keys, sits within two of
its `B` neighbour fold at every key. -/
private theorem magCoreB (l : Nat) (F : Nat → Nat) (k : Nat) (hk : k < l)
    (h0 : F 0 ≤ 1) (hcap : ∀ i, i < l → F i ≤ 2)
    (hstep : ∀ i, i + 1 < l → F i ≤ F (i + 1) + 1 ∧ F (i + 1) ≤ F i + 1) :
    2 * F k ≤ nbB l F k + 2 ∧ nbB l F k ≤ 2 * F k + 2 := by
  match k with
  | 0 =>
    rw [nbB_zero]
    have h2 : 2 * F 0 ≤ 2 := by
      rw [Nat.two_mul]
      exact Nat.add_le_add h0 h0
    by_cases h1 : 1 < l
    · rw [if_pos h1]
      exact ⟨Nat.le_trans h2 (Nat.le_add_left 2 (F 1)),
        Nat.le_trans (hcap 1 h1) (Nat.le_add_left 2 (2 * F 0))⟩
    · rw [if_neg h1]
      exact ⟨Nat.le_trans h2 (Nat.le_add_left 2 0), Nat.zero_le _⟩
  | m + 1 =>
    rw [nbB_succ]
    have hm := hstep m hk
    by_cases ht : m + 2 = l
    · rw [if_pos (ground.eqBeqOf ht), Nat.two_mul (F m)]
      exact magPairB (F (m + 1)) (F m) (F m) hm.2 hm.2 hm.1 hm.1
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      have hm2 := hstep (m + 1)
        (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)
      exact magPairB (F (m + 1)) (F m) (F (m + 2)) hm.2 hm2.1 hm.1 hm2.2

/-- Every `B` family's column sits within two of its neighbour
fold, at every key. -/
theorem colB_magLe (F : Nat → Nat) (k l : Nat) (hk : k < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ a b, a < b ∧ b < l ∧ F = fSumB l a b)
      ∨ (∃ a, a < l ∧ F = fDiff a l)) :
    2 * F k ≤ nbB l F k + 2 ∧ nbB l F k ≤ 2 * F k + 2 := by
  have hdiff : ∀ a b : Nat,
      2 * fDiff a b k ≤ nbB l (fDiff a b) k + 2
        ∧ nbB l (fDiff a b) k ≤ 2 * fDiff a b k + 2 := by
    intro a b
    have hone : ∀ i, fDiff a b i ≤ 1 := fun i => by
      by_cases h1 : a ≤ i
      · by_cases h2 : i < b
        · exact Nat.le_of_eq (fDiff_in a b i h1 h2)
        · rw [fDiff_hi a b i h2]
          exact Nat.zero_le 1
      · rw [fDiff_lo a b i h1]
        exact Nat.zero_le 1
    exact magCoreB l (fDiff a b) k hk (hone 0)
      (fun i _ => Nat.le_trans (hone i) (Nat.le_succ 1))
      (fun i _ => ⟨Nat.le_trans (hone i)
          (Nat.succ_le_succ (Nat.zero_le _)),
        Nat.le_trans (hone (i + 1))
          (Nat.succ_le_succ (Nat.zero_le _))⟩)
  match hcase with
  | .inl h =>
    obtain ⟨a, b, _, _, rfl⟩ := h
    exact hdiff a b
  | .inr (.inr h) =>
    obtain ⟨a, _, rfl⟩ := h
    exact hdiff a l
  | .inr (.inl h) =>
    obtain ⟨a, b, hab, hbl, rfl⟩ := h
    have hsub1 : ∀ i, ¬ b ≤ i → fSumB l a b i ≤ 1 := fun i hbi => by
      by_cases hai : a ≤ i
      · exact Nat.le_of_eq
          (fSumB_mid l a b i hai (Nat.lt_of_not_le hbi))
      · rw [fSumB_lo l a b i hai hbi]
        exact Nat.zero_le 1
    have hcap2 : ∀ i, i < l → fSumB l a b i ≤ 2 := fun i hil => by
      by_cases hbi : b ≤ i
      · exact Nat.le_of_eq (fSumB_hi l a b i hbi hil)
      · exact Nat.le_trans (hsub1 i hbi) (Nat.le_succ 1)
    refine magCoreB l (fSumB l a b) k hk
      (hsub1 0 (Nat.not_le_of_lt
        (Nat.lt_of_le_of_lt (Nat.zero_le a) hab))) hcap2
      (fun i hil => ?_)
    by_cases hbi : b ≤ i
    · rw [fSumB_hi l a b i hbi
          (Nat.lt_trans (Nat.lt_succ_self i) hil),
        fSumB_hi l a b (i + 1) (Nat.le_succ_of_le hbi) hil]
      exact ⟨Nat.le_succ 2, Nat.le_succ 2⟩
    · refine ⟨Nat.le_trans (hsub1 i hbi)
        (Nat.succ_le_succ (Nat.zero_le _)), ?_⟩
      by_cases hai : a ≤ i
      · rw [fSumB_mid l a b i hai (Nat.lt_of_not_le hbi)]
        exact hcap2 (i + 1) hil
      · rw [fSumB_lo l a b i hai hbi]
        refine hsub1 (i + 1) (fun hb1 => ?_)
        exact absurd (Nat.le_trans hb1
            (Nat.succ_le_of_lt (Nat.lt_of_not_le hai)))
          (Nat.not_le_of_lt hab)

/-- The companion's key clears the word: the key-distance read at
the stated word bound. -/
private theorem confAdapt (w x l : Nat) (F nb : Nat → Nat)
    (hwx : w + 2 ≤ x)
    (h : 2 * F x = nb x
      ∨ ((∃ y m1, x ≤ y + 2 ∧ y < l
            ∧ 2 * F y + (m1 + 1) = nb y)
          ∧ (∃ y m2, x ≤ y + 2 ∧ y < l
            ∧ nb y + (m2 + 1) = 2 * F y))) :
    2 * F x = nb x
    ∨ ((∃ y m1, w ≤ y ∧ y < l ∧ 2 * F y + (m1 + 1) = nb y)
        ∧ (∃ y m2, w ≤ y ∧ y < l ∧ nb y + (m2 + 1) = 2 * F y)) := by
  match h with
  | .inl hv => exact Or.inl hv
  | .inr hc =>
    obtain ⟨y, m1, hy2, hyl, heq⟩ := hc.1
    obtain ⟨y2, m2, hy22, hy2l, heq2⟩ := hc.2
    exact Or.inr
      ⟨⟨y, m1, ground.leCancelR 2 (Nat.le_trans hwx hy2), hyl, heq⟩,
        ⟨y2, m2, ground.leCancelR 2 (Nat.le_trans hwx hy22), hy2l,
          heq2⟩⟩

/-- The confinement's shared read: at a coroot content whose column
family is vacant at the key or holds the two companions, the
dominant target's entry at the key is vacant — a companion's
lower-side read refuses the dominance at its own key. -/
private theorem confCore (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) (nu0 : List BPair)
    (hn0 : nu0.length = t.rank)
    (j : Nat) (F : Nat → Nat) (nb : Nat → Nat)
    (hfe : getAt [] t.posFolds j = (List.range l).map F)
    (hcol : ∀ k, k < l →
      (corootAt t ((List.range l).map F) k).oneValue
        (BPair.ofCounts (2 * F k) (nb k)))
    (hdir : nu0 = poly.pnorm (sertables.posCorootV t j)
      ∨ nu0 = poly.pnorm (poly.neg (sertables.posCorootV t j)))
    (hdomin : ∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k)
    (x : Nat) (hwx : W.length + 2 ≤ x) (hxl : x < l)
    (hsplit : 2 * F x = nb x
      ∨ ((∃ y m1, W.length ≤ y ∧ y < l
            ∧ 2 * F y + (m1 + 1) = nb y)
          ∧ (∃ y m2, W.length ≤ y ∧ y < l
            ∧ nb y + (m2 + 1) = 2 * F y))) :
    ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) x
      = BPair.unit := by
  have hWx : W.length ≤ x :=
    Nat.le_trans (Nat.le_add_right W.length 2) hwx
  match hsplit with
  | .inl hvac =>
    refine targetVac t W l hrk nu0 hn0 x hxl hWx ?_
    match hdir with
    | .inl hP =>
      rw [hP, nuAtP t j x (by rw [hrk]; exact hxl), hfe]
      refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
      refine BPair.oneValue_trans (hcol x hxl) ?_
      rw [hvac]
      exact BPair.ofCounts_unit.mpr rfl
    | .inr hN =>
      rw [hN, nuAtN t j x (by rw [hrk]; exact hxl), hfe]
      refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
      refine BPair.oneValue_trans (ground.swap_congr (hcol x hxl)) ?_
      refine BPair.oneValue_trans (swapCounts (2 * F x) (nb x)) ?_
      rw [hvac]
      exact BPair.ofCounts_unit.mpr rfl
  | .inr hcomp =>
    match hdir with
    | .inl hP =>
      obtain ⟨y, m1, hWy, hyl, heq⟩ := hcomp.1
      have hdy := ground.leB_congr_right
        (targetAt t W l hrk nu0 hn0 y hyl hWy) (hdomin y hyl)
      refine absurd hdy (fun hle => domRefuse (2 * F y) m1 ?_ hle)
      have hey : ground.getAt BPair.unit nu0 y
          = BPair.norm (corootAt t ((List.range l).map F) y) := by
        rw [hP, nuAtP t j y (by rw [hrk]; exact hyl), hfe]
      rw [hey, heq]
      exact BPair.oneValue_trans (BPair.norm_oneValue _)
        (hcol y hyl)
    | .inr hN =>
      obtain ⟨y, m2, hWy, hyl, heq⟩ := hcomp.2
      have hdy := ground.leB_congr_right
        (targetAt t W l hrk nu0 hn0 y hyl hWy) (hdomin y hyl)
      refine absurd hdy (fun hle => domRefuse (nb y) m2 ?_ hle)
      have hey : ground.getAt BPair.unit nu0 y
          = BPair.norm ((corootAt t
              ((List.range l).map F) y).swap) := by
        rw [hN, nuAtN t j y (by rw [hrk]; exact hyl), hfe]
      rw [hey, heq]
      refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
      exact BPair.oneValue_trans (ground.swap_congr (hcol y hyl))
        (swapCounts (2 * F y) (nb y))

/-- `lem:serstable`(ii)'s target confinement at the `B` series: an
occupied dominant target's entries are vacant at every key at or
beyond the word's reach grown by two — the reach clause of the
off-diagonal enumeration. -/
theorem rowConfined_B : ∀ (W : List Nat) (l : Nat)
    (L : List (List BPair)) (nu0 : List BPair) (x : Nat),
    memberchar.mShapeRead (sertables.tableB l) L →
    row.thetaFamRead (sertables.tableB l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k) →
    W.length + 2 ≤ x → x < l →
    ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) x
      = BPair.unit := by
  intro W l L nu0 x hmsh hfam hpos hdomin hwx hxl
  have hnu : nu0 ∈ L := ground.mem_of_countOf_pos nu0 L hpos
  have hn0 : nu0.length = (sertables.tableB l).rank :=
    (hmsh nu0 hnu).1
  have hWx : W.length ≤ x :=
    Nat.le_trans (Nat.le_add_right W.length 2) hwx
  have hx2 : 2 ≤ x := Nat.le_trans (Nat.le_add_left 2 W.length) hwx
  match hfam.2.2 nu0 hnu with
  | .inl hu =>
    refine targetVac (sertables.tableB l) W l rfl nu0 hn0 x hxl
      hWx ?_
    rw [hu, ground.getAt_replicate BPair.unit BPair.unit
      (sertables.tableB l).rank x hxl]
    exact BPair.oneValue_refl BPair.unit
  | .inr hex =>
    obtain ⟨j, hj, hor⟩ := hex
    have hjl : j < (sertables.tableB l).posFolds.length :=
      Nat.lt_of_succ_lt_succ hj
    have hmem : getAt [] (sertables.tableB l).posFolds j
        ∈ sertables.foldsB l :=
      ground.mem_getAt [] _ j hjl
    match ground.mem_append_of _ _ hmem with
    | .inl h1 =>
      match ground.mem_append_of _ _ h1 with
      | .inl h2 =>
        match ground.mem_map_of _ (places.pairsOf l) _ h2 with
        | ⟨p, hp, he⟩ =>
          have hpr := places.pairs_mem l p
            (ground.countOf_pos_of_mem hp)
          refine confCore (sertables.tableB l) W l rfl nu0 hn0 j
            (fDiff p.1 p.2) (nbB l (fDiff p.1 p.2))
            (by rw [← he]; rfl)
            (colB l (fDiff p.1 p.2)) hor hdomin x hwx hxl ?_
          exact confAdapt W.length x l _ _ hwx
            (confDiffB l p.1 p.2 x hpr.1 hpr.2 hx2 hxl)
      | .inr h2 =>
        match ground.mem_map_of _ (places.pairsOf l) _ h2 with
        | ⟨p, hp, he⟩ =>
          have hpr := places.pairs_mem l p
            (ground.countOf_pos_of_mem hp)
          refine confCore (sertables.tableB l) W l rfl nu0 hn0 j
            (fSumB l p.1 p.2) (nbB l (fSumB l p.1 p.2))
            (by rw [← he]; exact fSumB_eq l p.1 p.2)
            (colB l (fSumB l p.1 p.2)) hor hdomin x hwx hxl ?_
          exact confAdapt W.length x l _ _ hwx
            (confSumB l p.1 p.2 x hpr.1 hpr.2 hx2 hxl)
    | .inr h1 =>
      match ground.mem_map_of _ (List.range l) _ h1 with
      | ⟨a, ha, he⟩ =>
        have hal : a < l :=
          ground.ltOfMemRange ha
        refine confCore (sertables.tableB l) W l rfl nu0 hn0 j
          (fDiff a l) (nbB l (fDiff a l))
          (by rw [← he]; rfl)
          (colB l (fDiff a l)) hor hdomin x hwx hxl ?_
        exact confAdapt W.length x l _ _ hwx
          (confShortB l a x hal hx2 hxl)



/-! ## The `C` confinement: the three families at the `C` column
guards -/

/-- The `C` difference family's column at a key. -/
private theorem confDiffC (l a b x : Nat) (hab : a < b) (hbl : b < l)
    (hx2 : 2 ≤ x) (hxl : x < l) :
    2 * fDiff a b x = nbC l (fDiff a b) x
    ∨ ((∃ y m1, x ≤ y + 2 ∧ y < l
          ∧ 2 * fDiff a b y + (m1 + 1) = nbC l (fDiff a b) y)
        ∧ (∃ y m2, x ≤ y + 2 ∧ y < l
          ∧ nbC l (fDiff a b) y + (m2 + 1) = 2 * fDiff a b y)) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 :=
    ⟨b - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
      hab)).symm⟩
  have hac : a ≤ c := Nat.le_of_succ_le_succ hab
  match Nat.lt_or_ge (c + 1) x with
  | .inl hbx =>
    refine Or.inl ?_
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
      ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        hx2)).symm⟩
    have hbm : c + 1 ≤ m := Nat.le_of_succ_le_succ hbx
    rw [nbC_succ,
      fDiff_hi a (c + 1) (m + 1)
        (Nat.not_lt_of_ge (Nat.le_succ_of_le hbm)),
      fDiff_hi a (c + 1) m (Nat.not_lt_of_ge hbm)]
    by_cases hml : m + 2 = l
    · rw [if_pos (ground.eqBeqOf hml)]
    · rw [if_neg (fun hb => hml (ground.beqEqOf hb))]
      by_cases hml3 : m + 3 = l
      · rw [if_pos (ground.eqBeqOf hml3),
          fDiff_hi a (c + 1) (m + 2)
            (Nat.not_lt_of_ge (Nat.le_succ_of_le
              (Nat.le_succ_of_le hbm)))]
      · rw [if_neg (fun hb => hml3 (ground.beqEqOf hb)),
          fDiff_hi a (c + 1) (m + 2)
            (Nat.not_lt_of_ge (Nat.le_succ_of_le
              (Nat.le_succ_of_le hbm)))]
  | .inr hxb =>
    refine Or.inr ⟨?_, ?_⟩
    · -- the lower companion at the window's top successor
      refine ⟨c + 1, 0,
        Nat.le_trans hxb (Nat.le_add_right (c + 1) 2), hbl, ?_⟩
      have hfc : fDiff a (c + 1) c = 1 :=
        fDiff_in a (c + 1) c hac (Nat.lt_succ_self c)
      have hfc1 : fDiff a (c + 1) (c + 1) = 0 :=
        fDiff_hi a (c + 1) (c + 1) (Nat.lt_irrefl (c + 1))
      rw [nbC_succ]
      by_cases h1 : c + 2 = l
      · rw [if_pos (ground.eqBeqOf h1), hfc, hfc1]
      · rw [if_neg (fun hb => h1 (ground.beqEqOf hb))]
        by_cases h2 : c + 3 = l
        · rw [if_pos (ground.eqBeqOf h2), hfc, hfc1,
            fDiff_hi a (c + 1) (c + 2)
              (Nat.not_lt_of_ge (Nat.le_succ (c + 1)))]
        · rw [if_neg (fun hb => h2 (ground.beqEqOf hb)), hfc, hfc1,
            fDiff_hi a (c + 1) (c + 2)
              (Nat.not_lt_of_ge (Nat.le_succ (c + 1)))]
    · -- the upper companion at the window's top key
      have hc1 : 1 ≤ c := Nat.le_of_succ_le_succ (Nat.le_trans hx2 hxb)
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 :=
        ⟨c - 1, (ground.subAdd hc1).symm⟩
      have hyl : d + 1 < l :=
        Nat.lt_trans (Nat.lt_succ_self (d + 1)) hbl
      have hy2 : x ≤ d + 1 + 2 :=
        Nat.le_trans hxb (Nat.le_succ (d + 2))
      have hne : ¬ d + 2 = l := Nat.ne_of_lt hbl
      have hfd1 : fDiff a (d + 2) (d + 1) = 1 :=
        fDiff_in a (d + 2) (d + 1) hac (Nat.lt_succ_self (d + 1))
      have hfd2 : fDiff a (d + 2) (d + 2) = 0 :=
        fDiff_hi a (d + 2) (d + 2) (Nat.lt_irrefl (d + 2))
      by_cases h3 : d + 3 = l
      · by_cases had : a ≤ d
        · refine ⟨d + 1, 0, hy2, hyl, ?_⟩
          rw [nbC_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf h3),
            fDiff_in a (d + 2) d had
              (Nat.lt_trans (Nat.lt_succ_self d)
                (Nat.lt_succ_self (d + 1))),
            hfd1, hfd2]
        · refine ⟨d + 1, 1, hy2, hyl, ?_⟩
          rw [nbC_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf h3),
            fDiff_lo a (d + 2) d had, hfd1, hfd2]
      · by_cases had : a ≤ d
        · refine ⟨d + 1, 0, hy2, hyl, ?_⟩
          rw [nbC_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
            if_neg (fun hb => h3 (ground.beqEqOf hb)),
            fDiff_in a (d + 2) d had
              (Nat.lt_trans (Nat.lt_succ_self d)
                (Nat.lt_succ_self (d + 1))),
            hfd1, hfd2]
        · refine ⟨d + 1, 1, hy2, hyl, ?_⟩
          rw [nbC_succ, if_neg (fun hb => hne (ground.beqEqOf hb)),
            if_neg (fun hb => h3 (ground.beqEqOf hb)),
            fDiff_lo a (d + 2) d had, hfd1, hfd2]



/-- The `C` sum family's column at a key, the fold at the rank's
successor presentation. -/
private theorem confSumC (d a b x : Nat) (hab : a < b) (hbd : b ≤ d)
    (hx2 : 2 ≤ x) (hxl : x < d + 1) :
    2 * fSumC d a b x = nbC (d + 1) (fSumC d a b) x
    ∨ ((∃ y m1, x ≤ y + 2 ∧ y < d + 1
          ∧ 2 * fSumC d a b y + (m1 + 1)
            = nbC (d + 1) (fSumC d a b) y)
        ∧ (∃ y m2, x ≤ y + 2 ∧ y < d + 1
          ∧ nbC (d + 1) (fSumC d a b) y + (m2 + 1)
            = 2 * fSumC d a b y)) := by
  match Nat.lt_or_ge b x with
  | .inl hbx =>
    refine Or.inl ?_
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
      ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        hx2)).symm⟩
    have hbm : b ≤ m := Nat.le_of_succ_le_succ hbx
    rw [nbC_succ]
    by_cases hxd : m + 2 = d + 1
    · have hdm : d = m + 1 := (Nat.succ.inj hxd).symm
      rw [if_pos (ground.eqBeqOf hxd),
        fSumC_end d a b (m + 1) hbd hdm,
        fSumC_two d a b m hbm (by rw [hdm]; exact Nat.lt_succ_self m)]
    · have hmd : m + 1 < d := Nat.lt_of_le_of_ne
        (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hxl))
        (fun he => hxd (congrArg Nat.succ he))
      rw [if_neg (fun hb => hxd (ground.beqEqOf hb)),
        fSumC_two d a b (m + 1) (Nat.le_succ_of_le hbm) hmd,
        fSumC_two d a b m hbm
          (Nat.lt_trans (Nat.lt_succ_self m) hmd)]
      by_cases hxd1 : m + 3 = d + 1
      · have hdm : d = m + 2 := (Nat.succ.inj hxd1).symm
        rw [if_pos (ground.eqBeqOf hxd1),
          fSumC_end d a b (m + 2) hbd hdm]
      · have hm2d : m + 2 < d := Nat.lt_of_le_of_ne
          (Nat.succ_le_of_lt hmd)
          (fun he => hxd1 (congrArg Nat.succ he))
        rw [if_neg (fun hb => hxd1 (ground.beqEqOf hb)),
          fSumC_two d a b (m + 2)
            (Nat.le_succ_of_le (Nat.le_succ_of_le hbm)) hm2d]
  | .inr hxb =>
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 :=
      ⟨b - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
        hab)).symm⟩
    have hac : a ≤ c := Nat.le_of_succ_le_succ hab
    have hbl : c + 1 < d + 1 := Nat.lt_succ_of_le hbd
    refine Or.inr ⟨?_, ?_⟩
    · by_cases hb1 : a = c
      · -- the one-key window: the lower companion below it
        have ha1 : 1 ≤ a := by
          rw [hb1]
          exact Nat.le_of_succ_le_succ (Nat.le_trans hx2 hxb)
        obtain ⟨e, rfl⟩ : ∃ e, a = e + 1 :=
          ⟨a - 1, (ground.subAdd ha1).symm⟩
        have hyl : e < d + 1 :=
          Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self e) hab) hbl
        have hy2 : x ≤ e + 2 := by
          rw [show e + 2 = e + 1 + 1 from rfl, hb1]
          exact hxb
        match e, hb1, hyl, hy2 with
        | 0, hb1, hyl, hy2 =>
          refine ⟨0, 0, hy2, hyl, ?_⟩
          have hd2 : (2 : Nat) ≤ d := by
            rw [show (2 : Nat) = 0 + 1 + 1 from rfl, hb1]
            exact hbd
          have hd1 : ¬ (2 : Nat) = d + 1 := fun he => by
            have hdd : d = 1 := Nat.succ.inj he.symm
            rw [hdd] at hd2
            exact Nat.not_succ_le_self 1 hd2
          rw [nbC_zero, if_neg (fun hb => hd1 (ground.beqEqOf hb)),
            if_pos (Nat.lt_trans hab hbl),
            fSumC_lo d (0 + 1) (c + 1) 0 (Nat.lt_succ_self 0) hab hbd,
            fSumC_mid d (0 + 1) (c + 1) 1 (Nat.le_refl 1) hab hbd]
        | e' + 1, hb1, hyl, hy2 =>
          refine ⟨e' + 1, 0, hy2, hyl, ?_⟩
          have hc2 : e' + 2 = c := hb1
          have hg1 : ¬ e' + 2 = d + 1 := fun he => by
            have hcd1 : c = d + 1 := hc2.symm.trans he
            rw [hcd1] at hbl
            exact Nat.lt_irrefl (d + 1)
              (Nat.lt_trans (Nat.lt_succ_self (d + 1)) hbl)
          have hg2 : ¬ e' + 3 = d + 1 := fun he => by
            have hdd : d = c := (Nat.succ.inj he.symm).trans hc2
            rw [hdd] at hbd
            exact Nat.not_succ_le_self c hbd
          rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb)),
            if_neg (fun hb => hg2 (ground.beqEqOf hb)),
            fSumC_lo d (e' + 1 + 1) (c + 1) (e' + 1)
              (Nat.lt_succ_self (e' + 1)) hab hbd,
            fSumC_lo d (e' + 1 + 1) (c + 1) e'
              (Nat.lt_trans (Nat.lt_succ_self e')
                (Nat.lt_succ_self (e' + 1))) hab hbd,
            fSumC_mid d (e' + 1 + 1) (c + 1) (e' + 2)
              (Nat.le_refl (e' + 2))
              (by rw [hc2]; exact Nat.lt_succ_self c) hbd]
      · -- the window beyond one key: the lower companion at the
        -- window's top key
        have hd1 : a < c := Nat.lt_of_le_of_ne hac hb1
        obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 :=
          ⟨c - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
            hd1)).symm⟩
        have hae : a ≤ e := Nat.le_of_succ_le_succ hd1
        have hyl : e + 1 < d + 1 :=
          Nat.lt_trans (Nat.lt_succ_self (e + 1)) hbl
        have hy2 : x ≤ e + 1 + 2 :=
          Nat.le_trans hxb (Nat.le_succ (e + 2))
        refine ⟨e + 1, 0, hy2, hyl, ?_⟩
        have hg1 : ¬ e + 2 = d + 1 := Nat.ne_of_lt hbl
        have hmide : fSumC d a (e + 2) e = 1 :=
          fSumC_mid d a (e + 2) e hae
            (Nat.lt_trans (Nat.lt_succ_self e)
              (Nat.lt_succ_self (e + 1))) hbd
        have hmid1 : fSumC d a (e + 2) (e + 1) = 1 :=
          fSumC_mid d a (e + 2) (e + 1) (Nat.le_succ_of_le hae)
            (Nat.lt_succ_self (e + 1)) hbd
        by_cases hg2 : e + 3 = d + 1
        · have hdm : d = e + 2 := (Nat.succ.inj hg2).symm
          rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf hg2), hmide,
            fSumC_end d a (e + 2) (e + 2) hbd hdm, hmid1]
        · have h2d : e + 2 < d := Nat.lt_of_le_of_ne
            (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hbl))
            (fun he => hg2 (congrArg Nat.succ he))
          rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb)),
            if_neg (fun hb => hg2 (ground.beqEqOf hb)), hmide,
            fSumC_two d a (e + 2) (e + 2) (Nat.le_refl (e + 2)) h2d,
            hmid1]
    · -- the upper companion at the window's beyond-key
      have hy2 : x ≤ c + 1 + 2 :=
        Nat.le_trans hxb (Nat.le_add_right (c + 1) 2)
      have hmidc : fSumC d a (c + 1) c = 1 :=
        fSumC_mid d a (c + 1) c hac (Nat.lt_succ_self c) hbd
      by_cases hbd1 : c + 1 = d
      · -- the window's top at the last key
        refine ⟨c + 1, 0, hy2, hbl, ?_⟩
        have hg1 : c + 2 = d + 1 := congrArg Nat.succ hbd1
        rw [nbC_succ, if_pos (ground.eqBeqOf hg1),
          fSumC_end d a (c + 1) (c + 1) hbd hbd1.symm, hmidc]
      · have hcd : c + 1 < d := Nat.lt_of_le_of_ne hbd hbd1
        refine ⟨c + 1, 0, hy2, hbl, ?_⟩
        have hg1 : ¬ c + 2 = d + 1 := fun he =>
          hbd1 (Nat.succ.inj he)
        have htwo : fSumC d a (c + 1) (c + 1) = 2 :=
          fSumC_two d a (c + 1) (c + 1) (Nat.le_refl (c + 1)) hcd
        by_cases hg2 : c + 3 = d + 1
        · have hdm : d = c + 2 := (Nat.succ.inj hg2).symm
          rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf hg2), hmidc,
            fSumC_end d a (c + 1) (c + 2) hbd hdm, htwo]
        · have h2d : c + 2 < d := Nat.lt_of_le_of_ne
            (Nat.succ_le_of_lt hcd)
            (fun he => hg2 (congrArg Nat.succ he))
          rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb)),
            if_neg (fun hb => hg2 (ground.beqEqOf hb)), hmidc,
            fSumC_two d a (c + 1) (c + 2)
              (Nat.le_succ_of_le (Nat.le_refl (c + 1))) h2d, htwo]



/-- The `C` long family's column at a key, the fold at the rank's
successor presentation. -/
private theorem confLongC (d a x : Nat) (had : a ≤ d)
    (hx2 : 2 ≤ x) (hxl : x < d + 1) :
    2 * fLong d a x = nbC (d + 1) (fLong d a) x
    ∨ ((∃ y m1, x ≤ y + 2 ∧ y < d + 1
          ∧ 2 * fLong d a y + (m1 + 1)
            = nbC (d + 1) (fLong d a) y)
        ∧ (∃ y m2, x ≤ y + 2 ∧ y < d + 1
          ∧ nbC (d + 1) (fLong d a) y + (m2 + 1)
            = 2 * fLong d a y)) := by
  match Nat.lt_or_ge a x with
  | .inl hax =>
    refine Or.inl ?_
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
      ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        hx2)).symm⟩
    have ham : a ≤ m := Nat.le_of_succ_le_succ hax
    rw [nbC_succ]
    by_cases hxd : m + 2 = d + 1
    · have hdm : d = m + 1 := (Nat.succ.inj hxd).symm
      rw [if_pos (ground.eqBeqOf hxd), fLong_end d a (m + 1) hdm,
        fLong_two d a m ham (by rw [hdm]; exact Nat.lt_succ_self m)]
    · have hmd : m + 1 < d := Nat.lt_of_le_of_ne
        (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt hxl))
        (fun he => hxd (congrArg Nat.succ he))
      rw [if_neg (fun hb => hxd (ground.beqEqOf hb)),
        fLong_two d a (m + 1) (Nat.le_succ_of_le ham) hmd,
        fLong_two d a m ham (Nat.lt_trans (Nat.lt_succ_self m) hmd)]
      by_cases hxd1 : m + 3 = d + 1
      · have hdm : d = m + 2 := (Nat.succ.inj hxd1).symm
        rw [if_pos (ground.eqBeqOf hxd1),
          fLong_end d a (m + 2) hdm]
      · have hm2d : m + 2 < d := Nat.lt_of_le_of_ne
          (Nat.succ_le_of_lt hmd)
          (fun he => hxd1 (congrArg Nat.succ he))
        rw [if_neg (fun hb => hxd1 (ground.beqEqOf hb)),
          fLong_two d a (m + 2)
            (Nat.le_succ_of_le (Nat.le_succ_of_le ham)) hm2d]
  | .inr hxa =>
    have ha2 : 2 ≤ a := Nat.le_trans hx2 hxa
    obtain ⟨e, rfl⟩ : ∃ e, a = e + 2 := by
      refine ⟨a - 2, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 :=
        ⟨a - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          ha2)).symm⟩
      obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
        ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_of_succ_le_succ ha2))).symm⟩
      rfl
    have hlo1 : fLong d (e + 2) (e + 1) = 0 :=
      fLong_lo d (e + 2) (e + 1) (Nat.lt_succ_self (e + 1)) had
    have hloe : fLong d (e + 2) e = 0 :=
      fLong_lo d (e + 2) e (Nat.lt_trans (Nat.lt_succ_self e)
        (Nat.lt_succ_self (e + 1))) had
    refine Or.inr ⟨?_, ?_⟩
    · -- the lower companion below the window
      refine ⟨e + 1, 1,
        Nat.le_trans hxa (Nat.le_succ (e + 2)),
        Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ (e + 1))
          had), ?_⟩
      have hg1 : ¬ e + 2 = d + 1 := fun he =>
        Nat.lt_irrefl d (Nat.lt_of_lt_of_le
          (by rw [← Nat.succ.inj he]; exact Nat.lt_succ_self (e + 1))
          had)
      rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb))]
      by_cases hg2 : e + 3 = d + 1
      · have hdm : d = e + 2 := (Nat.succ.inj hg2).symm
        rw [if_pos (ground.eqBeqOf hg2), hloe, hlo1,
          fLong_end d (e + 2) (e + 2) hdm]
      · have h2d : e + 2 < d := Nat.lt_of_le_of_ne had
          (fun he => hg2 (congrArg Nat.succ he))
        rw [if_neg (fun hb => hg2 (ground.beqEqOf hb)), hloe, hlo1,
          fLong_two d (e + 2) (e + 2) (Nat.le_refl (e + 2)) h2d]
    · -- the upper companion at the window's first key
      refine ⟨e + 2, 1,
        Nat.le_trans hxa (Nat.le_add_right (e + 2) 2),
        Nat.lt_succ_of_le had, ?_⟩
      by_cases hg1 : e + 3 = d + 1
      · have hdm : d = e + 2 := (Nat.succ.inj hg1).symm
        rw [nbC_succ, if_pos (ground.eqBeqOf hg1), hlo1,
          fLong_end d (e + 2) (e + 2) hdm]
      · have h2d : e + 2 < d := Nat.lt_of_le_of_ne had
          (fun he => hg1 (congrArg Nat.succ he))
        rw [nbC_succ, if_neg (fun hb => hg1 (ground.beqEqOf hb))]
        by_cases hg2 : e + 4 = d + 1
        · have hdm : d = e + 3 := (Nat.succ.inj hg2).symm
          rw [if_pos (ground.eqBeqOf hg2), hlo1,
            fLong_end d (e + 2) (e + 3) hdm,
            fLong_two d (e + 2) (e + 2) (Nat.le_refl (e + 2)) h2d]
        · have h3d : e + 3 < d := Nat.lt_of_le_of_ne
            (Nat.succ_le_of_lt h2d)
            (fun he => hg2 (congrArg Nat.succ he))
          rw [if_neg (fun hb => hg2 (ground.beqEqOf hb)), hlo1,
            fLong_two d (e + 2) (e + 3)
              (Nat.le_succ (e + 2)) h3d,
            fLong_two d (e + 2) (e + 2) (Nat.le_refl (e + 2)) h2d]



/-- `lem:serstable`(ii)'s target confinement at the `C` series. -/
theorem rowConfined_C : ∀ (W : List Nat) (l : Nat)
    (L : List (List BPair)) (nu0 : List BPair) (x : Nat),
    memberchar.mShapeRead (sertables.tableC l) L →
    row.thetaFamRead (sertables.tableC l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k) →
    W.length + 2 ≤ x → x < l →
    ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) x
      = BPair.unit := by
  intro W l L nu0 x hmsh hfam hpos hdomin hwx hxl
  have hnu : nu0 ∈ L := ground.mem_of_countOf_pos nu0 L hpos
  have hn0 : nu0.length = (sertables.tableC l).rank :=
    (hmsh nu0 hnu).1
  have hWx : W.length ≤ x :=
    Nat.le_trans (Nat.le_add_right W.length 2) hwx
  have hx2 : 2 ≤ x := Nat.le_trans (Nat.le_add_left 2 W.length) hwx
  match hfam.2.2 nu0 hnu with
  | .inl hu =>
    refine targetVac (sertables.tableC l) W l rfl nu0 hn0 x hxl
      hWx ?_
    rw [hu, ground.getAt_replicate BPair.unit BPair.unit
      (sertables.tableC l).rank x hxl]
    exact BPair.oneValue_refl BPair.unit
  | .inr hex =>
    obtain ⟨j, hj, hor⟩ := hex
    have hjl : j < (sertables.tableC l).posFolds.length :=
      Nat.lt_of_succ_lt_succ hj
    have hmem : getAt [] (sertables.tableC l).posFolds j
        ∈ sertables.foldsC l :=
      ground.mem_getAt [] _ j hjl
    obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 :=
      ⟨l - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
        (Nat.le_of_lt (Nat.lt_of_le_of_lt hx2 hxl)))).symm⟩
    match ground.mem_append_of _ _ hmem with
    | .inl h1 =>
      match ground.mem_append_of _ _ h1 with
      | .inl h2 =>
        match ground.mem_map_of _ (places.pairsOf (d + 1)) _ h2 with
        | ⟨p, hp, he⟩ =>
          have hpr := places.pairs_mem (d + 1) p
            (ground.countOf_pos_of_mem hp)
          refine confCore (sertables.tableC (d + 1)) W (d + 1) rfl
            nu0 hn0 j (fDiff p.1 p.2) (nbC (d + 1) (fDiff p.1 p.2))
            (by rw [← he]; rfl)
            (colC (d + 1) (fDiff p.1 p.2)) hor hdomin x hwx hxl ?_
          exact confAdapt W.length x (d + 1) _ _ hwx
            (confDiffC (d + 1) p.1 p.2 x hpr.1 hpr.2 hx2 hxl)
      | .inr h2 =>
        match ground.mem_map_of _ (places.pairsOf (d + 1)) _ h2 with
        | ⟨p, hp, he⟩ =>
          have hpr := places.pairs_mem (d + 1) p
            (ground.countOf_pos_of_mem hp)
          refine confCore (sertables.tableC (d + 1)) W (d + 1) rfl
            nu0 hn0 j (fSumC d p.1 p.2)
            (nbC (d + 1) (fSumC d p.1 p.2))
            (by rw [← he]; exact fSumC_eq d p.1 p.2)
            (colC (d + 1) (fSumC d p.1 p.2)) hor hdomin x hwx
            hxl ?_
          exact confAdapt W.length x (d + 1) _ _ hwx
            (confSumC d p.1 p.2 x hpr.1
              (Nat.le_of_succ_le_succ hpr.2) hx2 hxl)
    | .inr h1 =>
      match ground.mem_map_of _ (List.range (d + 1)) _ h1 with
      | ⟨a, ha, he⟩ =>
        have hal : a < d + 1 :=
          ground.ltOfMemRange ha
        refine confCore (sertables.tableC (d + 1)) W (d + 1) rfl
          nu0 hn0 j (fLong d a) (nbC (d + 1) (fLong d a))
          (by rw [← he]; exact fLong_eq d a)
          (colC (d + 1) (fLong d a)) hor hdomin x hwx hxl ?_
        exact confAdapt W.length x (d + 1) _ _ hwx
          (confLongC d a x (Nat.le_of_succ_le_succ hal) hx2 hxl)



/-! ## The `D` confinement: the two families at the `D` column
guards, the fork's last key at the word's four-clearance -/

/-- The `D` difference family's column at a key: the fork's last
key reads the window's own neighbour, so the last key joins at the
word's four-clearance. -/
private theorem confDiffD (e a b w x : Nat) (hab : a < b)
    (hbl : b < e + 2) (hwx : w + 2 ≤ x) (hxl : x < e + 2)
    (hlast : x = e + 1 → w + 4 ≤ e + 2) :
    2 * fDiff a b x = nbD (e + 2) (fDiff a b) x
    ∨ ((∃ y m1, w ≤ y ∧ y < e + 2
          ∧ 2 * fDiff a b y + (m1 + 1)
            = nbD (e + 2) (fDiff a b) y)
        ∧ (∃ y m2, w ≤ y ∧ y < e + 2
          ∧ nbD (e + 2) (fDiff a b) y + (m2 + 1)
            = 2 * fDiff a b y)) := by
  have hx2 : 2 ≤ x := Nat.le_trans (Nat.le_add_left 2 w) hwx
  by_cases hxe : x = e + 1
  · -- the last key at the four-clearance
    have hw4 : w + 4 ≤ e + 2 := hlast hxe
    have he2 : 2 ≤ e :=
      ground.leCancelR 2 (Nat.le_trans (Nat.le_add_left 4 w) hw4)
    obtain ⟨g, rfl⟩ : ∃ g, e = g + 2 := by
      refine ⟨e - 2, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, e = u + 1 :=
        ⟨e - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          he2)).symm⟩
      obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
        ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_of_succ_le_succ he2))).symm⟩
      rfl
    subst hxe
    have hwg : w ≤ g :=
      ground.leCancelR 4 (show w + 4 ≤ g + 4 from hw4)
    have hple : pv2D (fDiff a b) (g + 2 + 1) = fDiff a b (g + 1) :=
      rfl
    have hbhi : ¬ g + 2 + 1 < b :=
      Nat.not_lt_of_ge (Nat.le_of_succ_le_succ hbl)
    by_cases hocc : a ≤ g + 1 ∧ g + 1 < b
    · refine Or.inr ⟨⟨g + 2 + 1, 0,
        Nat.le_trans hwg (Nat.le_add_right g 3),
        Nat.lt_succ_self (g + 3), ?_⟩, ?_⟩
      · rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hple,
          fDiff_hi a b (g + 2 + 1) hbhi,
          fDiff_in a b (g + 1) hocc.1 hocc.2]
      · by_cases hb1 : b = g + 3
        · refine ⟨g + 2, 0, Nat.le_trans hwg (Nat.le_add_right g 2),
            Nat.lt_trans (Nat.lt_succ_self (g + 2))
              (Nat.lt_succ_self (g + 3)), ?_⟩
          have hp : pvD (fDiff a b) (g + 2) = fDiff a b (g + 1) :=
            rfl
          rw [nbD_eq,
            if_neg (fun hb =>
              (Nat.ne_of_lt (Nat.lt_succ_self (g + 3)))
                (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf rfl), hp,
            fDiff_in a b (g + 1) hocc.1 hocc.2,
            fDiff_in a b (g + 2) (Nat.le_succ_of_le hocc.1)
              (by rw [hb1]; exact Nat.lt_succ_self (g + 2))]
        · have hb2 : b = g + 2 := Nat.le_antisymm
            (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne
              (Nat.le_of_lt_succ hbl) hb1))
            (Nat.succ_le_of_lt hocc.2)
          subst hb2
          have hyl : g + 1 < g + 2 + 2 :=
            Nat.lt_trans (Nat.lt_succ_self (g + 1))
              (Nat.lt_trans (Nat.lt_succ_self (g + 2))
                (Nat.lt_succ_self (g + 3)))
          have hne1 : ¬ g + 1 + 1 = g + 2 + 2 :=
            Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (g + 2))
              (Nat.lt_succ_self (g + 3)))
          have hne2 : ¬ g + 1 + 2 = g + 2 + 2 :=
            Nat.ne_of_lt (Nat.lt_succ_self (g + 3))
          by_cases hag : a ≤ g
          · refine ⟨g + 1, 0,
              Nat.le_trans hwg (Nat.le_add_right g 1), hyl, ?_⟩
            rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
              if_neg (fun hb => hne2 (ground.beqEqOf hb)),
              if_pos (ground.eqBeqOf rfl), pvD_succ,
              fDiff_hi a (g + 2) (g + 1 + 1)
                (Nat.lt_irrefl (g + 2)),
              fDiff_hi a (g + 2) (g + 1 + 2)
                (Nat.not_lt_of_ge (Nat.le_succ (g + 2))),
              fDiff_in a (g + 2) (g + 1) hocc.1 hocc.2,
              fDiff_in a (g + 2) g hag
                (Nat.lt_trans (Nat.lt_succ_self g)
                  (Nat.lt_succ_self (g + 1)))]
          · refine ⟨g + 1, 1,
              Nat.le_trans hwg (Nat.le_add_right g 1), hyl, ?_⟩
            rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
              if_neg (fun hb => hne2 (ground.beqEqOf hb)),
              if_pos (ground.eqBeqOf rfl), pvD_succ,
              fDiff_hi a (g + 2) (g + 1 + 1)
                (Nat.lt_irrefl (g + 2)),
              fDiff_hi a (g + 2) (g + 1 + 2)
                (Nat.not_lt_of_ge (Nat.le_succ (g + 2))),
              fDiff_in a (g + 2) (g + 1) hocc.1 hocc.2,
              fDiff_lo a (g + 2) g hag]
    · refine Or.inl ?_
      rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hple,
        fDiff_hi a b (g + 2 + 1) hbhi]
      by_cases ha1 : a ≤ g + 1
      · rw [fDiff_hi a b (g + 1) (fun hc => hocc ⟨ha1, hc⟩)]
      · rw [fDiff_lo a b (g + 1) ha1]
  · -- the interior keys
    have hxee : x < e + 1 :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hxl) hxe
    match Nat.lt_or_ge b x with
    | .inl hbx =>
      refine Or.inl ?_
      obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
        ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          hx2)).symm⟩
      have hbm : b ≤ m := Nat.le_of_succ_le_succ hbx
      rw [nbD_eq,
        if_neg (fun hb =>
          (Nat.ne_of_lt (Nat.succ_lt_succ hxee))
            (ground.beqEqOf hb)),
        fDiff_hi a b (m + 1) (Nat.not_lt_of_ge
          (Nat.le_succ_of_le hbm))]
      by_cases hg2 : m + 1 + 2 = e + 2
      · rw [if_pos (ground.eqBeqOf hg2), pvD_succ,
          fDiff_hi a b m (Nat.not_lt_of_ge hbm)]
      · rw [if_neg (fun hb => hg2 (ground.beqEqOf hb))]
        by_cases hg3 : m + 1 + 3 = e + 2
        · rw [if_pos (ground.eqBeqOf hg3), pvD_succ,
            fDiff_hi a b m (Nat.not_lt_of_ge hbm),
            fDiff_hi a b (m + 1 + 1) (Nat.not_lt_of_ge
              (Nat.le_succ_of_le (Nat.le_succ_of_le hbm))),
            fDiff_hi a b (m + 1 + 2) (Nat.not_lt_of_ge
              (Nat.le_succ_of_le (Nat.le_succ_of_le
                (Nat.le_succ_of_le hbm))))]
        · rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)), pvD_succ,
            fDiff_hi a b m (Nat.not_lt_of_ge hbm),
            fDiff_hi a b (m + 1 + 1) (Nat.not_lt_of_ge
              (Nat.le_succ_of_le (Nat.le_succ_of_le hbm)))]
    | .inr hxb =>
      by_cases hbe1 : b = e + 1
      · have hel : 1 ≤ e := Nat.le_of_succ_le_succ
          (Nat.le_trans hx2 (Nat.le_trans hxb (Nat.le_of_eq hbe1)))
        obtain ⟨g, rfl⟩ : ∃ g, e = g + 1 :=
          ⟨e - 1, (ground.subAdd hel).symm⟩
        subst hbe1
        have hwg : w ≤ g :=
          ground.leCancelR 2 (Nat.le_trans hwx hxb)
        by_cases hae : a = g + 1
        · -- the one-key window at the fork's first key
          subst hae
          refine Or.inr ⟨⟨g, 0, hwg,
            Nat.lt_trans (Nat.lt_succ_self g)
              (Nat.lt_trans (Nat.lt_succ_self (g + 1))
                (Nat.lt_succ_self (g + 2))), ?_⟩,
            ⟨g + 1, 1, Nat.le_succ_of_le hwg,
              Nat.lt_trans (Nat.lt_succ_self (g + 1))
                (Nat.lt_succ_self (g + 2)), ?_⟩⟩
          · rw [nbD_eq,
              if_neg (fun hb =>
                (Nat.ne_of_lt (Nat.lt_trans
                  (Nat.lt_succ_self (g + 1))
                  (Nat.lt_succ_self (g + 2)))) (ground.beqEqOf hb)),
              if_neg (fun hb =>
                (Nat.ne_of_lt (Nat.lt_succ_self (g + 2)))
                  (ground.beqEqOf hb)),
              if_pos (ground.eqBeqOf rfl),
              fDiff_in (g + 1) (g + 1 + 1) (g + 1)
                (Nat.le_refl (g + 1)) (Nat.lt_succ_self (g + 1)),
              fDiff_hi (g + 1) (g + 1 + 1) (g + 2)
                (Nat.lt_irrefl (g + 2)),
              fDiff_lo (g + 1) (g + 1 + 1) g
                (Nat.not_le_of_lt (Nat.lt_succ_self g))]
            match g with
            | 0 => rfl
            | h + 1 =>
              rw [pvD_succ,
                fDiff_lo (h + 1 + 1) (h + 1 + 1 + 1) h
                  (Nat.not_le_of_lt (Nat.lt_trans
                    (Nat.lt_succ_self h)
                    (Nat.lt_succ_self (h + 1))))]
          · rw [nbD_eq,
              if_neg (fun hb =>
                (Nat.ne_of_lt (Nat.lt_succ_self (g + 2)))
                  (ground.beqEqOf hb)),
              if_pos (ground.eqBeqOf rfl), pvD_succ,
              fDiff_lo (g + 1) (g + 1 + 1) g
                (Nat.not_le_of_lt (Nat.lt_succ_self g)),
              fDiff_in (g + 1) (g + 1 + 1) (g + 1)
                (Nat.le_refl (g + 1)) (Nat.lt_succ_self (g + 1))]
        · -- the window into the fork at an interior first key
          have hag : a ≤ g := Nat.le_of_lt_succ
            (Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ hab) hae)
          refine Or.inr ⟨⟨g + 2, 0,
            Nat.le_succ_of_le (Nat.le_succ_of_le hwg),
            Nat.lt_succ_self (g + 2), ?_⟩,
            ⟨g + 1, 0, Nat.le_succ_of_le hwg,
              Nat.lt_trans (Nat.lt_succ_self (g + 1))
                (Nat.lt_succ_self (g + 2)), ?_⟩⟩
          · have hp : pv2D (fDiff a (g + 1 + 1)) (g + 2)
                = fDiff a (g + 1 + 1) g := rfl
            rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hp,
              fDiff_in a (g + 1 + 1) g hag
                (Nat.lt_trans (Nat.lt_succ_self g)
                  (Nat.lt_succ_self (g + 1))),
              fDiff_hi a (g + 1 + 1) (g + 2)
                (Nat.lt_irrefl (g + 2))]
          · rw [nbD_eq,
              if_neg (fun hb =>
                (Nat.ne_of_lt (Nat.lt_succ_self (g + 2)))
                  (ground.beqEqOf hb)),
              if_pos (ground.eqBeqOf rfl), pvD_succ,
              fDiff_in a (g + 1 + 1) g hag
                (Nat.lt_trans (Nat.lt_succ_self g)
                  (Nat.lt_succ_self (g + 1))),
              fDiff_in a (g + 1 + 1) (g + 1)
                (Nat.le_succ_of_le hag) (Nat.lt_succ_self (g + 1))]
      · -- the window below the fork: the top edge's companions
        have hb2 : 2 ≤ b := Nat.le_trans hx2 hxb
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 :=
          ⟨b - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
            hb2)).symm⟩
        obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 :=
          ⟨c - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
            (Nat.le_of_succ_le_succ hb2))).symm⟩
        have hwc : w ≤ d + 1 :=
          ground.leCancelR 2 (Nat.le_trans hwx
            (Nat.le_succ_of_le hxb))
        have hwb : w ≤ d + 1 + 1 := Nat.le_succ_of_le hwc
        have hfc : fDiff a (d + 1 + 1) (d + 1) = 1 :=
          fDiff_in a (d + 1 + 1) (d + 1)
            (Nat.le_of_succ_le_succ hab) (Nat.lt_succ_self (d + 1))
        have hfc1 : fDiff a (d + 1 + 1) (d + 1 + 1) = 0 :=
          fDiff_hi a (d + 1 + 1) (d + 1 + 1)
            (Nat.lt_irrefl (d + 2))
        have hylb : d + 1 < e + 2 :=
          Nat.lt_trans (Nat.lt_succ_self (d + 1)) hbl
        refine Or.inr ⟨⟨d + 1 + 1, 0, hwb, hbl, ?_⟩, ?_⟩
        · rw [nbD_eq,
            if_neg (fun hb => hbe1
              (Nat.succ.inj (ground.beqEqOf hb)))]
          by_cases hg2 : d + 1 + 1 + 2 = e + 2
          · rw [if_pos (ground.eqBeqOf hg2), pvD_succ, hfc1, hfc]
          · rw [if_neg (fun hb => hg2 (ground.beqEqOf hb))]
            by_cases hg3 : d + 1 + 1 + 3 = e + 2
            · rw [if_pos (ground.eqBeqOf hg3), pvD_succ, hfc1, hfc,
                fDiff_hi a (d + 1 + 1) (d + 1 + 1 + 1)
                  (Nat.not_lt_of_ge (Nat.le_succ (d + 2))),
                fDiff_hi a (d + 1 + 1) (d + 1 + 1 + 2)
                  (Nat.not_lt_of_ge (Nat.le_succ_of_le
                    (Nat.le_succ (d + 2))))]
            · rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)),
                pvD_succ, hfc1, hfc,
                fDiff_hi a (d + 1 + 1) (d + 1 + 1 + 1)
                  (Nat.not_lt_of_ge (Nat.le_succ (d + 2)))]
        · have hg1 : ¬ d + 1 + 1 = e + 2 := Nat.ne_of_lt hbl
          have hg2 : ¬ d + 1 + 2 = e + 2 := fun he =>
            hbe1 (Nat.succ.inj he)
          by_cases hg3 : d + 1 + 3 = e + 2
          · by_cases had : a ≤ d
            · refine ⟨d + 1, 0, hwc, hylb, ?_⟩
              rw [nbD_eq,
                if_neg (fun hb => hg1 (ground.beqEqOf hb)),
                if_neg (fun hb => hg2 (ground.beqEqOf hb)),
                if_pos (ground.eqBeqOf hg3), pvD_succ, hfc, hfc1,
                fDiff_hi a (d + 1 + 1) (d + 1 + 2)
                  (Nat.not_lt_of_ge (Nat.le_succ (d + 2))),
                fDiff_in a (d + 1 + 1) d had
                  (Nat.lt_trans (Nat.lt_succ_self d)
                    (Nat.lt_succ_self (d + 1)))]
            · refine ⟨d + 1, 1, hwc, hylb, ?_⟩
              rw [nbD_eq,
                if_neg (fun hb => hg1 (ground.beqEqOf hb)),
                if_neg (fun hb => hg2 (ground.beqEqOf hb)),
                if_pos (ground.eqBeqOf hg3), pvD_succ, hfc, hfc1,
                fDiff_hi a (d + 1 + 1) (d + 1 + 2)
                  (Nat.not_lt_of_ge (Nat.le_succ (d + 2))),
                fDiff_lo a (d + 1 + 1) d had]
          · by_cases had : a ≤ d
            · refine ⟨d + 1, 0, hwc, hylb, ?_⟩
              rw [nbD_eq,
                if_neg (fun hb => hg1 (ground.beqEqOf hb)),
                if_neg (fun hb => hg2 (ground.beqEqOf hb)),
                if_neg (fun hb => hg3 (ground.beqEqOf hb)),
                pvD_succ, hfc, hfc1,
                fDiff_in a (d + 1 + 1) d had
                  (Nat.lt_trans (Nat.lt_succ_self d)
                    (Nat.lt_succ_self (d + 1)))]
            · refine ⟨d + 1, 1, hwc, hylb, ?_⟩
              rw [nbD_eq,
                if_neg (fun hb => hg1 (ground.beqEqOf hb)),
                if_neg (fun hb => hg2 (ground.beqEqOf hb)),
                if_neg (fun hb => hg3 (ground.beqEqOf hb)),
                pvD_succ, hfc, hfc1,
                fDiff_lo a (d + 1 + 1) d had]


/-- The `D` sum family's generic column at a key. -/
private theorem confSumD (e a b w x : Nat) (hab : a < b)
    (hbe : b ≤ e) (hwx : w + 2 ≤ x) (hxl : x < e + 2)
    (hlast : x = e + 1 → w + 4 ≤ e + 2) :
    2 * fSumD e a b x = nbD (e + 2) (fSumD e a b) x
    ∨ ((∃ y m1, w ≤ y ∧ y < e + 2
          ∧ 2 * fSumD e a b y + (m1 + 1)
            = nbD (e + 2) (fSumD e a b) y)
        ∧ (∃ y m2, w ≤ y ∧ y < e + 2
          ∧ nbD (e + 2) (fSumD e a b) y + (m2 + 1)
            = 2 * fSumD e a b y)) := by
  have hx2 : 2 ≤ x := Nat.le_trans (Nat.le_add_left 2 w) hwx
  by_cases hxe : x = e + 1
  · -- the last key at the four-clearance
    have hw4 : w + 4 ≤ e + 2 := hlast hxe
    have he2 : 2 ≤ e :=
      ground.leCancelR 2 (Nat.le_trans (Nat.le_add_left 4 w) hw4)
    obtain ⟨g, rfl⟩ : ∃ g, e = g + 2 := by
      refine ⟨e - 2, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, e = u + 1 :=
        ⟨e - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          he2)).symm⟩
      obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
        ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_of_succ_le_succ he2))).symm⟩
      rfl
    subst hxe
    have hwg : w ≤ g :=
      ground.leCancelR 4 (show w + 4 ≤ g + 4 from hw4)
    have hple : pv2D (fSumD (g + 2) a b) (g + 2 + 1)
        = fSumD (g + 2) a b (g + 1) := rfl
    have hend3 : fSumD (g + 2) a b (g + 2 + 1) = 1 :=
      fSumD_end (g + 2) a b (g + 3) hbe
        (Nat.le_succ (g + 2)) (Nat.lt_succ_self (g + 3))
    by_cases hbg : b = g + 2
    · -- the window's top at the tip: the last key is occupied
      subst hbg
      refine Or.inr ⟨?_, ⟨g + 2 + 1, 0,
        Nat.le_trans hwg (Nat.le_add_right g 3),
        Nat.lt_succ_self (g + 3), ?_⟩⟩
      · have hmid1 : fSumD (g + 2) a (g + 2) (g + 1) = 1 :=
          fSumD_mid (g + 2) a (g + 2) (g + 1)
            (Nat.le_of_succ_le_succ hab)
            (Nat.lt_succ_self (g + 1)) hbe
        have hend1 : fSumD (g + 2) a (g + 2) (g + 1 + 1) = 1 :=
          fSumD_end (g + 2) a (g + 2) (g + 1 + 1) hbe
            (Nat.le_refl (g + 2))
            (Nat.lt_trans (Nat.lt_succ_self (g + 2))
              (Nat.lt_succ_self (g + 3)))
        have hend2 : fSumD (g + 2) a (g + 2) (g + 1 + 2) = 1 :=
          fSumD_end (g + 2) a (g + 2) (g + 1 + 2) hbe
            (Nat.le_succ (g + 2)) (Nat.lt_succ_self (g + 3))
        have hne1 : ¬ g + 1 + 1 = g + 2 + 2 :=
          Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (g + 2))
            (Nat.lt_succ_self (g + 3)))
        have hne2 : ¬ g + 1 + 2 = g + 2 + 2 :=
          Nat.ne_of_lt (Nat.lt_succ_self (g + 3))
        by_cases hag : a ≤ g
        · refine ⟨g + 1, 0,
            Nat.le_trans hwg (Nat.le_add_right g 1),
            Nat.lt_trans (Nat.lt_succ_self (g + 1))
              (Nat.lt_trans (Nat.lt_succ_self (g + 2))
                (Nat.lt_succ_self (g + 3))), ?_⟩
          rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
            if_neg (fun hb => hne2 (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf rfl), pvD_succ, hmid1, hend1,
            hend2,
            fSumD_mid (g + 2) a (g + 2) g hag
              (Nat.lt_trans (Nat.lt_succ_self g)
                (Nat.lt_succ_self (g + 1))) hbe]
        · have hag1 : a = g + 1 := Nat.le_antisymm
            (Nat.le_of_succ_le_succ hab)
            (Nat.succ_le_of_lt (Nat.lt_of_not_le hag))
          subst hag1
          refine ⟨g, 0, hwg,
            Nat.lt_trans (Nat.lt_succ_self g)
              (Nat.lt_trans (Nat.lt_succ_self (g + 1))
                (Nat.lt_trans (Nat.lt_succ_self (g + 2))
                  (Nat.lt_succ_self (g + 3)))), ?_⟩
          have hglo : fSumD (g + 2) (g + 1) (g + 2) g = 0 :=
            fSumD_lo (g + 2) (g + 1) (g + 2) g
              (Nat.lt_succ_self g) hab hbe
          have hne0a : ¬ g + 1 = g + 2 + 2 :=
            Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (g + 1))
              (Nat.lt_trans (Nat.lt_succ_self (g + 2))
                (Nat.lt_succ_self (g + 3))))
          have hne0b : ¬ g + 2 = g + 2 + 2 :=
            Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (g + 2))
              (Nat.lt_succ_self (g + 3)))
          have hne0c : ¬ g + 3 = g + 2 + 2 :=
            Nat.ne_of_lt (Nat.lt_succ_self (g + 3))
          rw [nbD_eq, if_neg (fun hb => hne0a (ground.beqEqOf hb)),
            if_neg (fun hb => hne0b (ground.beqEqOf hb)),
            if_neg (fun hb => hne0c (ground.beqEqOf hb)),
            fSumD_mid (g + 2) (g + 1) (g + 2) (g + 1)
              (Nat.le_refl (g + 1)) (Nat.lt_succ_self (g + 1)) hbe,
            hglo]
          match g, hglo with
          | 0, _ => rfl
          | h + 1, _ =>
            rw [pvD_succ,
              fSumD_lo (h + 1 + 2) (h + 1 + 1) (h + 1 + 2) h
                (Nat.lt_trans (Nat.lt_succ_self h)
                  (Nat.lt_succ_self (h + 1))) hab hbe]
      · rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hple, hend3,
          fSumD_mid (g + 2) a (g + 2) (g + 1)
            (Nat.le_of_succ_le_succ hab)
            (Nat.lt_succ_self (g + 1)) hbe]
    · -- the window's top below the tip: the last key is vacant
      have hbg1 : b ≤ g + 1 := Nat.le_of_lt_succ
        (Nat.lt_of_le_of_ne hbe hbg)
      refine Or.inl ?_
      rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hple, hend3,
        fSumD_two (g + 2) a b (g + 1) hbg1
          (Nat.lt_succ_self (g + 1))]
  · -- the interior keys
    have hxee : x < e + 1 :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hxl) hxe
    match Nat.lt_or_ge b x with
    | .inl hbx =>
      refine Or.inl ?_
      obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
        ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          hx2)).symm⟩
      have hbm : b ≤ m := Nat.le_of_succ_le_succ hbx
      rw [nbD_eq,
        if_neg (fun hb =>
          (Nat.ne_of_lt (Nat.succ_lt_succ hxee))
            (ground.beqEqOf hb))]
      by_cases hg2 : m + 1 + 2 = e + 2
      · have hme : m + 1 = e := Nat.succ.inj (Nat.succ.inj hg2)
        rw [if_pos (ground.eqBeqOf hg2), pvD_succ,
          fSumD_end e a b (m + 1) hbe (Nat.le_of_eq hme.symm)
            hxl,
          fSumD_two e a b m hbm
            (by rw [← hme]; exact Nat.lt_succ_self m)]
      · have hme : m + 1 < e := by
          match Nat.lt_or_ge (m + 1) e with
          | .inl h => exact h
          | .inr h =>
            exact absurd (Nat.le_antisymm
              (Nat.le_of_lt_succ hxee) h)
              (fun he => hg2 (congrArg (fun z => z + 1)
                (congrArg Nat.succ he)))
        rw [if_neg (fun hb => hg2 (ground.beqEqOf hb))]
        by_cases hg3 : m + 1 + 3 = e + 2
        · have hme2 : m + 1 + 1 = e := Nat.succ.inj
            (Nat.succ.inj hg3)
          rw [if_pos (ground.eqBeqOf hg3), pvD_succ,
            fSumD_two e a b (m + 1) (Nat.le_succ_of_le hbm) hme,
            fSumD_two e a b m hbm
              (Nat.lt_trans (Nat.lt_succ_self m) hme),
            fSumD_end e a b (m + 1 + 1) hbe
              (Nat.le_of_eq hme2.symm)
              (Nat.succ_lt_succ hxee),
            fSumD_end e a b (m + 1 + 2) hbe
              (by rw [← hme2]; exact Nat.le_succ (m + 2))
              (by rw [← hme2]; exact Nat.lt_succ_self (m + 3))]
        · have hme2 : m + 1 + 1 < e := by
            match Nat.lt_or_ge (m + 1 + 1) e with
            | .inl h => exact h
            | .inr h =>
              exact absurd (Nat.le_antisymm (Nat.succ_le_of_lt hme)
                h)
                (fun he => hg3 (congrArg (fun z => z + 1)
                  (congrArg Nat.succ he)))
          rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)), pvD_succ,
            fSumD_two e a b (m + 1) (Nat.le_succ_of_le hbm) hme,
            fSumD_two e a b m hbm
              (Nat.lt_trans (Nat.lt_succ_self m) hme),
            fSumD_two e a b (m + 1 + 1)
              (Nat.le_succ_of_le (Nat.le_succ_of_le hbm)) hme2]
    | .inr hxb =>
      have hwb2 : w + 2 ≤ b := Nat.le_trans hwx hxb
      have hb2 : 2 ≤ b := Nat.le_trans hx2 hxb
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 :=
        ⟨b - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          hb2)).symm⟩
      have hac : a ≤ c := Nat.le_of_succ_le_succ hab
      have hwc : w ≤ c := ground.leCancelR 2
        (show w + 2 ≤ c + 2 from Nat.le_succ_of_le hwb2)
      refine Or.inr ⟨?_, ?_⟩
      · -- the lower companion
        by_cases hb1 : a = c
        · -- the one-key window: the companion below it
          have ha1 : 1 ≤ a := by
            rw [hb1]
            exact Nat.le_of_succ_le_succ (Nat.le_trans hx2 hxb)
          obtain ⟨f, rfl⟩ : ∃ f, a = f + 1 :=
            ⟨a - 1, (ground.subAdd ha1).symm⟩
          have hfc : f + 1 = c := hb1
          refine ⟨f, 0, ground.leCancelR 2
              (by rw [show f + 2 = f + 1 + 1 from rfl, hfc]
                  exact hwb2),
            Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_succ f)
                (Nat.le_trans (Nat.le_of_eq hfc)
                  (Nat.le_trans (Nat.le_succ c) hbe)))
              (Nat.lt_trans (Nat.lt_succ_self e)
                (Nat.lt_succ_self (e + 1))), ?_⟩
          have hglo : fSumD e (f + 1) (c + 1) f = 0 :=
            fSumD_lo e (f + 1) (c + 1) f (Nat.lt_succ_self f)
              hab hbe
          have hgmid : fSumD e (f + 1) (c + 1) (f + 1) = 1 :=
            fSumD_mid e (f + 1) (c + 1) (f + 1)
              (Nat.le_refl (f + 1))
              (by rw [hfc]; exact Nat.lt_succ_self c) hbe
          have hne1 : ¬ f + 1 = e + 2 := Nat.ne_of_lt
            (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_of_eq hfc)
                (Nat.le_trans (Nat.le_succ c) hbe))
              (Nat.lt_trans (Nat.lt_succ_self e)
                (Nat.lt_succ_self (e + 1))))
          have hne2 : ¬ f + 2 = e + 2 := fun he => by
            have hfe : f = e := Nat.succ.inj (Nat.succ.inj he)
            rw [hfe] at hfc
            refine absurd hbe (Nat.not_le_of_lt ?_)
            rw [← hfc]
            exact Nat.lt_trans (Nat.lt_succ_self e)
              (Nat.lt_succ_self (e + 1))
          have hne3 : ¬ f + 3 = e + 2 := fun he => by
            have hfe : f + 1 = e := Nat.succ.inj (Nat.succ.inj he)
            have hce : c = e := hfc.symm.trans hfe
            rw [hce] at hbe
            exact Nat.not_succ_le_self e hbe
          rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
            if_neg (fun hb => hne2 (ground.beqEqOf hb)),
            if_neg (fun hb => hne3 (ground.beqEqOf hb)), hglo,
            hgmid]
          match f, hglo with
          | 0, _ => rfl
          | h + 1, _ =>
            rw [pvD_succ,
              fSumD_lo e (h + 1 + 1) (c + 1) h
                (Nat.lt_trans (Nat.lt_succ_self h)
                  (Nat.lt_succ_self (h + 1))) hab hbe]
        · -- the window's top key holds the companion
          have hd1 : a < c := Nat.lt_of_le_of_ne hac hb1
          obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 :=
            ⟨c - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
              hd1)).symm⟩
          have had : a ≤ d := Nat.le_of_succ_le_succ hd1
          refine ⟨d + 1, 0, hwc,
            Nat.lt_of_lt_of_le (Nat.lt_succ_self (d + 1))
              (Nat.le_trans hbe (Nat.le_add_right e 2)), ?_⟩
          have hmidd : fSumD e a (d + 2) d = 1 :=
            fSumD_mid e a (d + 2) d had
              (Nat.lt_trans (Nat.lt_succ_self d)
                (Nat.lt_succ_self (d + 1))) hbe
          have hmidd1 : fSumD e a (d + 2) (d + 1) = 1 :=
            fSumD_mid e a (d + 2) (d + 1) (Nat.le_succ_of_le had)
              (Nat.lt_succ_self (d + 1)) hbe
          have hne1 : ¬ d + 1 + 1 = e + 2 := fun he =>
            absurd hbe (by
              rw [show d + 2 = d + 1 + 1 from rfl,
                Nat.succ.inj (Nat.succ.inj he)]
              exact Nat.not_le_of_lt (Nat.lt_trans
                (Nat.lt_succ_self e) (Nat.lt_succ_self (e + 1))))
          have hne2 : ¬ d + 1 + 2 = e + 2 := fun he => by
            have hde : d + 1 = e := Nat.succ.inj (Nat.succ.inj he)
            exact absurd hbe (by
              rw [show d + 2 = d + 1 + 1 from rfl, hde]
              exact Nat.not_le_of_lt (Nat.lt_succ_self e))
          rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
            if_neg (fun hb => hne2 (ground.beqEqOf hb))]
          by_cases hg3 : d + 1 + 3 = e + 2
          · have hde : d + 2 = e := Nat.succ.inj (Nat.succ.inj hg3)
            rw [if_pos (ground.eqBeqOf hg3), pvD_succ, hmidd,
              hmidd1,
              fSumD_end e a (d + 2) (d + 1 + 1) hbe
                (Nat.le_of_eq hde.symm)
                (by rw [hde]
                    exact Nat.lt_trans (Nat.lt_succ_self e)
                      (Nat.lt_succ_self (e + 1))),
              fSumD_end e a (d + 2) (d + 1 + 2) hbe
                (by rw [← hde]; exact Nat.le_succ (d + 2))
                (by rw [← hde]; exact Nat.lt_succ_self (d + 3))]
          · have hde : d + 2 < e := by
              match Nat.lt_or_ge (d + 2) e with
              | .inl h => exact h
              | .inr h =>
                exact absurd (Nat.le_antisymm hbe h)
                  (fun he => hg3 (congrArg (fun z => z + 1)
                    (congrArg Nat.succ he)))
            rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)),
              pvD_succ, hmidd, hmidd1,
              fSumD_two e a (d + 2) (d + 1 + 1)
                (Nat.le_refl (d + 2)) hde]
      · -- the upper companion at the window's beyond-key
        by_cases hbg : c + 1 = e
        · -- the window's top at the tip's neighbour
          refine ⟨c + 1, 0, Nat.le_succ_of_le hwc,
            Nat.lt_of_le_of_lt hbe
              (Nat.lt_trans (Nat.lt_succ_self e)
                (Nat.lt_succ_self (e + 1))), ?_⟩
          have hne1 : ¬ c + 1 + 1 = e + 2 := fun he =>
            absurd (Nat.succ.inj (Nat.succ.inj he) : c = e)
              (fun hc => (Nat.ne_of_lt (Nat.lt_succ_self c))
                (hc.trans hbg.symm))
          rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf (congrArg (fun z => z + 2) hbg)),
            pvD_succ,
            fSumD_mid e a (c + 1) c hac (Nat.lt_succ_self c) hbe,
            fSumD_end e a (c + 1) (c + 1) hbe
              (Nat.le_of_eq hbg.symm)
              (Nat.lt_of_le_of_lt hbe
                (Nat.lt_trans (Nat.lt_succ_self e)
                  (Nat.lt_succ_self (e + 1))))]
        · have hce : c + 1 < e := Nat.lt_of_le_of_ne hbe hbg
          refine ⟨c + 1, 0, Nat.le_succ_of_le hwc,
            Nat.lt_trans (Nat.lt_succ_of_le hbe)
              (Nat.lt_succ_self (e + 1)), ?_⟩
          have hne1 : ¬ c + 1 + 1 = e + 2 := fun he =>
            absurd (Nat.succ.inj (Nat.succ.inj he) : c = e)
              (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self c) hce))
          have hne2 : ¬ c + 1 + 2 = e + 2 := fun he =>
            absurd (Nat.succ.inj (Nat.succ.inj he) : c + 1 = e)
              hbg
          rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
            if_neg (fun hb => hne2 (ground.beqEqOf hb))]
          by_cases hg3 : c + 1 + 3 = e + 2
          · have hde : c + 2 = e := Nat.succ.inj (Nat.succ.inj hg3)
            rw [if_pos (ground.eqBeqOf hg3), pvD_succ,
              fSumD_mid e a (c + 1) c hac (Nat.lt_succ_self c) hbe,
              fSumD_two e a (c + 1) (c + 1) (Nat.le_refl (c + 1))
                hce,
              fSumD_end e a (c + 1) (c + 1 + 1) hbe
                (Nat.le_of_eq hde.symm)
                (by rw [show c + 1 + 1 = c + 2 from rfl, hde]
                    exact Nat.lt_trans (Nat.lt_succ_self e)
                      (Nat.lt_succ_self (e + 1))),
              fSumD_end e a (c + 1) (c + 1 + 2) hbe
                (by rw [← hde]; exact Nat.le_succ (c + 2))
                (by rw [← hde]; exact Nat.lt_succ_self (c + 3))]
          · have hde : c + 2 < e := by
              match Nat.lt_or_ge (c + 2) e with
              | .inl h => exact h
              | .inr h =>
                exact absurd (Nat.le_antisymm (Nat.succ_le_of_lt hce)
                  h)
                  (fun he => hg3 (congrArg (fun z => z + 1)
                    (congrArg Nat.succ he)))
            rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)),
              pvD_succ,
              fSumD_mid e a (c + 1) c hac (Nat.lt_succ_self c) hbe,
              fSumD_two e a (c + 1) (c + 1) (Nat.le_refl (c + 1))
                hce,
              fSumD_two e a (c + 1) (c + 1 + 1)
                (Nat.le_succ (c + 1)) hde]



/-- The `D` sum family's last-pair column at a key: the boundary
arm's fold at the vacant tip neighbour. -/
private theorem confSumDt (e a w x : Nat) (hae : a ≤ e)
    (hwx : w + 2 ≤ x) (hxl : x < e + 2)
    (hlast : x = e + 1 → w + 4 ≤ e + 2) :
    2 * fSumDt e a x = nbD (e + 2) (fSumDt e a) x
    ∨ ((∃ y m1, w ≤ y ∧ y < e + 2
          ∧ 2 * fSumDt e a y + (m1 + 1)
            = nbD (e + 2) (fSumDt e a) y)
        ∧ (∃ y m2, w ≤ y ∧ y < e + 2
          ∧ nbD (e + 2) (fSumDt e a) y + (m2 + 1)
            = 2 * fSumDt e a y)) := by
  have hx2 : 2 ≤ x := Nat.le_trans (Nat.le_add_left 2 w) hwx
  by_cases hxe : x = e + 1
  · -- the last key at the four-clearance
    have hw4 : w + 4 ≤ e + 2 := hlast hxe
    have he2 : 2 ≤ e :=
      ground.leCancelR 2 (Nat.le_trans (Nat.le_add_left 4 w) hw4)
    obtain ⟨g, rfl⟩ : ∃ g, e = g + 2 := by
      refine ⟨e - 2, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, e = u + 1 :=
        ⟨e - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          he2)).symm⟩
      obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
        ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_of_succ_le_succ he2))).symm⟩
      rfl
    subst hxe
    have hwg : w ≤ g :=
      ground.leCancelR 4 (show w + 4 ≤ g + 4 from hw4)
    have hple : pv2D (fSumDt (g + 2) a) (g + 2 + 1)
        = fSumDt (g + 2) a (g + 1) := rfl
    have htop : fSumDt (g + 2) a (g + 2 + 1) = 1 :=
      fSumDt_top (g + 2) a (g + 3) rfl
    by_cases hag : a ≤ g + 1
    · refine Or.inr ⟨⟨g + 2, 0,
        Nat.le_trans hwg (Nat.le_add_right g 2),
        Nat.lt_trans (Nat.lt_succ_self (g + 2))
          (Nat.lt_succ_self (g + 3)), ?_⟩,
        ⟨g + 2 + 1, 0, Nat.le_trans hwg (Nat.le_add_right g 3),
          Nat.lt_succ_self (g + 3), ?_⟩⟩
      · have hp : pvD (fSumDt (g + 2) a) (g + 2)
            = fSumDt (g + 2) a (g + 1) := rfl
        rw [nbD_eq,
          if_neg (fun hb =>
            (Nat.ne_of_lt (Nat.lt_succ_self (g + 3)))
              (ground.beqEqOf hb)),
          if_pos (ground.eqBeqOf rfl), hp,
          fSumDt_mid (g + 2) a (g + 1) hag
            (Nat.lt_succ_self (g + 1)),
          fSumDt_gap (g + 2) a (g + 2) rfl]
      · rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hple, htop,
          fSumDt_mid (g + 2) a (g + 1) hag
            (Nat.lt_succ_self (g + 1))]
    · have hag2 : a = g + 2 := Nat.le_antisymm hae
        (Nat.succ_le_of_lt (Nat.lt_of_not_le hag))
      subst hag2
      refine Or.inr ⟨⟨g + 1, 0,
        Nat.le_trans hwg (Nat.le_add_right g 1),
        Nat.lt_trans (Nat.lt_succ_self (g + 1))
          (Nat.lt_trans (Nat.lt_succ_self (g + 2))
            (Nat.lt_succ_self (g + 3))), ?_⟩,
        ⟨g + 2 + 1, 1, Nat.le_trans hwg (Nat.le_add_right g 3),
          Nat.lt_succ_self (g + 3), ?_⟩⟩
      · have hlo1 : fSumDt (g + 2) (g + 2) (g + 1) = 0 :=
          fSumDt_lo (g + 2) (g + 2) (g + 1)
            (Nat.lt_succ_self (g + 1)) hae
        rw [nbD_eq,
          if_neg (fun hb =>
            (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (g + 2))
              (Nat.lt_succ_self (g + 3)))) (ground.beqEqOf hb)),
          if_neg (fun hb =>
            (Nat.ne_of_lt (Nat.lt_succ_self (g + 3)))
              (ground.beqEqOf hb)),
          if_pos (ground.eqBeqOf rfl), pvD_succ, hlo1,
          fSumDt_gap (g + 2) (g + 2) (g + 1 + 1) rfl,
          fSumDt_top (g + 2) (g + 2) (g + 1 + 2) rfl,
          fSumDt_lo (g + 2) (g + 2) g
            (Nat.lt_trans (Nat.lt_succ_self g)
              (Nat.lt_succ_self (g + 1))) hae]
      · rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hple, htop,
          fSumDt_lo (g + 2) (g + 2) (g + 1)
            (Nat.lt_succ_self (g + 1)) hae]
  · -- the interior keys
    have hxee : x < e + 1 :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hxl) hxe
    match Nat.lt_or_ge a x with
    | .inl hax =>
      by_cases hxee2 : x = e
      · -- the vacant tip neighbour's own key: the two companions
        subst hxee2
        obtain ⟨f, rfl⟩ : ∃ f, x = f + 1 :=
          ⟨x - 1, (ground.subAdd (Nat.lt_of_le_of_lt (Nat.zero_le a)
            hax)).symm⟩
        have hwf : w ≤ f + 1 := Nat.le_succ_of_le
          (ground.leCancelR 2 (Nat.le_succ_of_le hwx))
        have hmf : fSumDt (f + 1) a f = 1 :=
          fSumDt_mid (f + 1) a f (Nat.le_of_succ_le_succ hax)
            (Nat.lt_succ_self f)
        refine Or.inr ⟨⟨f + 1, 0, hwf,
          Nat.lt_trans (Nat.lt_succ_self (f + 1))
            (Nat.lt_succ_self (f + 2)), ?_⟩,
          ⟨f + 1 + 1, 0, Nat.le_succ_of_le hwf,
            Nat.lt_succ_self (f + 2), ?_⟩⟩
        · rw [nbD_eq,
            if_neg (fun hb =>
              (Nat.ne_of_lt (Nat.lt_succ_self (f + 2)))
                (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf rfl), pvD_succ, hmf,
            fSumDt_gap (f + 1) a (f + 1) rfl]
        · have hp : pv2D (fSumDt (f + 1) a) (f + 1 + 1)
              = fSumDt (f + 1) a f := rfl
          rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hp, hmf,
            fSumDt_top (f + 1) a (f + 1 + 1) rfl]
      · -- the interior of the one-window: vacant
        refine Or.inl ?_
        have hxe' : x < e :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hxee) hxee2
        obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
          ⟨x - 1, (ground.subAdd (Nat.lt_of_lt_of_le
            (Nat.succ_pos 1) hx2)).symm⟩
        have ham : a ≤ m := Nat.le_of_succ_le_succ hax
        have hmm : fSumDt e a m = 1 :=
          fSumDt_mid e a m ham
            (Nat.lt_trans (Nat.lt_succ_self m) hxe')
        have hmm1 : fSumDt e a (m + 1) = 1 :=
          fSumDt_mid e a (m + 1) (Nat.le_succ_of_le ham) hxe'
        rw [nbD_eq,
          if_neg (fun hb =>
            (Nat.ne_of_lt (Nat.succ_lt_succ hxee))
              (ground.beqEqOf hb)),
          if_neg (fun hb =>
            (Nat.ne_of_lt (Nat.succ_lt_succ (Nat.succ_lt_succ
              hxe'))) (ground.beqEqOf hb))]
        by_cases hg3 : m + 1 + 3 = e + 2
        · have hme : m + 2 = e := Nat.succ.inj (Nat.succ.inj hg3)
          rw [if_pos (ground.eqBeqOf hg3), pvD_succ, hmm, hmm1,
            fSumDt_gap e a (m + 1 + 1) hme,
            fSumDt_top e a (m + 1 + 2)
              (congrArg Nat.succ hme)]
        · have hme : m + 2 < e := Nat.lt_of_le_of_ne
            (Nat.succ_le_of_lt hxe')
            (fun he => hg3 (congrArg (fun z => z + 1)
              (congrArg Nat.succ he)))
          rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)), pvD_succ,
            hmm, hmm1,
            fSumDt_mid e a (m + 1 + 1)
              (Nat.le_succ_of_le (Nat.le_succ_of_le ham)) hme]
    | .inr hxa =>
      have ha2 : 2 ≤ a := Nat.le_trans hx2 hxa
      by_cases hae2 : a = e
      · -- the window at the tip's neighbour alone
        subst hae2
        obtain ⟨g, rfl⟩ : ∃ g, a = g + 2 := by
          refine ⟨a - 2, ?_⟩
          obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 :=
            ⟨a - 1, (ground.subAdd (Nat.lt_of_lt_of_le
              (Nat.succ_pos 1) ha2)).symm⟩
          obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
            ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le
              (Nat.succ_pos 0)
              (Nat.le_of_succ_le_succ ha2))).symm⟩
          rfl
        have hwg : w ≤ g := ground.leCancelR 2
          (show w + 2 ≤ g + 2 from Nat.le_trans hwx hxa)
        have hlo1 : fSumDt (g + 2) (g + 2) (g + 1) = 0 :=
          fSumDt_lo (g + 2) (g + 2) (g + 1)
            (Nat.lt_succ_self (g + 1)) hae
        refine Or.inr ⟨⟨g + 1, 0, Nat.le_succ_of_le hwg,
          Nat.lt_trans (Nat.lt_succ_self (g + 1))
            (Nat.lt_trans (Nat.lt_succ_self (g + 2))
              (Nat.lt_succ_self (g + 3))), ?_⟩,
          ⟨g + 2 + 1, 1, Nat.le_trans hwg (Nat.le_add_right g 3),
            Nat.lt_succ_self (g + 3), ?_⟩⟩
        · rw [nbD_eq,
            if_neg (fun hb =>
              (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (g + 2))
                (Nat.lt_succ_self (g + 3)))) (ground.beqEqOf hb)),
            if_neg (fun hb =>
              (Nat.ne_of_lt (Nat.lt_succ_self (g + 3)))
                (ground.beqEqOf hb)),
            if_pos (ground.eqBeqOf rfl), pvD_succ, hlo1,
            fSumDt_gap (g + 2) (g + 2) (g + 1 + 1) rfl,
            fSumDt_top (g + 2) (g + 2) (g + 1 + 2) rfl,
            fSumDt_lo (g + 2) (g + 2) g
              (Nat.lt_trans (Nat.lt_succ_self g)
                (Nat.lt_succ_self (g + 1))) hae]
        · have hp : pv2D (fSumDt (g + 2) (g + 2)) (g + 2 + 1)
              = fSumDt (g + 2) (g + 2) (g + 1) := rfl
          rw [nbD_eq, if_pos (ground.eqBeqOf rfl), hp, hlo1,
            fSumDt_top (g + 2) (g + 2) (g + 2 + 1) rfl]
      · -- the window below the tip's neighbour
        have hae3 : a < e := Nat.lt_of_le_of_ne hae hae2
        obtain ⟨f, rfl⟩ : ∃ f, a = f + 2 := by
          refine ⟨a - 2, ?_⟩
          obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 :=
            ⟨a - 1, (ground.subAdd (Nat.lt_of_lt_of_le
              (Nat.succ_pos 1) ha2)).symm⟩
          obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
            ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le
              (Nat.succ_pos 0)
              (Nat.le_of_succ_le_succ ha2))).symm⟩
          rfl
        have hwf : w ≤ f + 1 := Nat.le_of_succ_le_succ
          (ground.leCancelR 1
            (show w + 1 + 1 ≤ f + 2 + 1 from
              Nat.le_succ_of_le (Nat.le_trans hwx hxa)))
        have hlof : fSumDt e (f + 2) (f + 1) = 0 :=
          fSumDt_lo e (f + 2) (f + 1)
            (Nat.lt_succ_self (f + 1)) hae
        have hmida : fSumDt e (f + 2) (f + 2) = 1 :=
          fSumDt_mid e (f + 2) (f + 2) (Nat.le_refl (f + 2)) hae3
        have hne1 : ¬ f + 1 + 1 = e + 2 := Nat.ne_of_lt
          (Nat.lt_trans (Nat.succ_lt_succ (Nat.lt_of_lt_of_le
            (Nat.lt_succ_self (f + 1)) (Nat.le_of_lt hae3)))
            (Nat.lt_succ_self (e + 1)))
        have hne2 : ¬ f + 1 + 2 = e + 2 := fun he =>
          absurd (Nat.succ.inj (Nat.succ.inj he) : f + 1 = e)
            (Nat.ne_of_lt (Nat.lt_of_lt_of_le
              (Nat.lt_succ_self (f + 1)) (Nat.le_of_lt hae3)))
        have hne3 : ¬ f + 1 + 3 = e + 2 := fun he =>
          hae2 (Nat.succ.inj (Nat.succ.inj he) :
            f + 1 + 1 = e)
        refine Or.inr ⟨⟨f + 1, 0, hwf,
          Nat.lt_trans (Nat.lt_of_lt_of_le
            (Nat.lt_succ_self (f + 1)) (Nat.le_of_lt hae3))
            (Nat.lt_trans (Nat.lt_succ_self e)
              (Nat.lt_succ_self (e + 1))), ?_⟩, ?_⟩
        · rw [nbD_eq, if_neg (fun hb => hne1 (ground.beqEqOf hb)),
            if_neg (fun hb => hne2 (ground.beqEqOf hb)),
            if_neg (fun hb => hne3 (ground.beqEqOf hb)), pvD_succ,
            hlof, hmida,
            fSumDt_lo e (f + 2) f
              (Nat.lt_trans (Nat.lt_succ_self f)
                (Nat.lt_succ_self (f + 1))) hae]
        · have hne1' : ¬ f + 2 + 1 = e + 2 := fun he =>
            (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (f + 1))
              hae3)) (Nat.succ.inj (Nat.succ.inj he))
          have hne2' : ¬ f + 2 + 2 = e + 2 := fun he =>
            hae2 (Nat.succ.inj (Nat.succ.inj he))
          have hyl : f + 2 < e + 2 := Nat.lt_trans hae3
            (Nat.lt_trans (Nat.lt_succ_self e)
              (Nat.lt_succ_self (e + 1)))
          refine ⟨f + 2, 0, Nat.le_succ_of_le hwf, hyl, ?_⟩
          rw [nbD_eq, if_neg (fun hb => hne1' (ground.beqEqOf hb)),
            if_neg (fun hb => hne2' (ground.beqEqOf hb))]
          by_cases hg3 : f + 2 + 3 = e + 2
          · have hme : f + 3 = e := Nat.succ.inj (Nat.succ.inj hg3)
            rw [if_pos (ground.eqBeqOf hg3), pvD_succ, hlof, hmida,
              fSumDt_gap e (f + 2) (f + 2 + 1) hme,
              fSumDt_top e (f + 2) (f + 2 + 2)
                (congrArg Nat.succ hme)]
          · have hme : f + 3 < e := Nat.lt_of_le_of_ne
              (Nat.succ_le_of_lt hae3)
              (fun he => hg3 (congrArg (fun z => z + 1)
                (congrArg Nat.succ he)))
            rw [if_neg (fun hb => hg3 (ground.beqEqOf hb)),
              pvD_succ, hlof, hmida,
              fSumDt_mid e (f + 2) (f + 2 + 1)
                (Nat.le_succ (f + 2)) hme]





/-- `lem:serstable`(ii)'s target confinement at the `D` series: the
interior keys at the word's two-clearance, the fork's last key
joining at the four-clearance — the boundary-adjacent rank's sum
pair the last key's own occupancy. -/
theorem rowConfined_D : ∀ (W : List Nat) (l : Nat)
    (L : List (List BPair)) (nu0 : List BPair) (x : Nat),
    memberchar.mShapeRead (sertables.tableD l) L →
    row.thetaFamRead (sertables.tableD l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k) →
    W.length + 2 ≤ x → x < l →
    (x + 1 = l → W.length + 4 ≤ l) →
    ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) x
      = BPair.unit := by
  intro W l L nu0 x hmsh hfam hpos hdomin hwx hxl hguard
  have hnu : nu0 ∈ L := ground.mem_of_countOf_pos nu0 L hpos
  have hn0 : nu0.length = (sertables.tableD l).rank :=
    (hmsh nu0 hnu).1
  have hWx : W.length ≤ x :=
    Nat.le_trans (Nat.le_add_right W.length 2) hwx
  have hx2 : 2 ≤ x := Nat.le_trans (Nat.le_add_left 2 W.length) hwx
  match hfam.2.2 nu0 hnu with
  | .inl hu =>
    refine targetVac (sertables.tableD l) W l rfl nu0 hn0 x hxl
      hWx ?_
    rw [hu, ground.getAt_replicate BPair.unit BPair.unit
      (sertables.tableD l).rank x hxl]
    exact BPair.oneValue_refl BPair.unit
  | .inr hex =>
    obtain ⟨j, hj, hor⟩ := hex
    have hjl : j < (sertables.tableD l).posFolds.length :=
      Nat.lt_of_succ_lt_succ hj
    have hmem : getAt [] (sertables.tableD l).posFolds j
        ∈ sertables.foldsD l :=
      ground.mem_getAt [] _ j hjl
    obtain ⟨e, rfl⟩ : ∃ e, l = e + 2 := by
      refine ⟨l - 2, ?_⟩
      have hl3 : 2 ≤ l :=
        Nat.le_of_lt (Nat.lt_of_le_of_lt hx2 hxl)
      obtain ⟨u, rfl⟩ : ∃ u, l = u + 1 :=
        ⟨l - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 1)
          hl3)).symm⟩
      obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 :=
        ⟨u - 1, (ground.subAdd (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
          (Nat.le_of_succ_le_succ hl3))).symm⟩
      rfl
    have h1l : 1 < e + 2 :=
      Nat.succ_lt_succ (Nat.succ_pos e)
    have hlast : x = e + 1 → W.length + 4 ≤ e + 2 := fun hx =>
      hguard (congrArg Nat.succ hx)
    match ground.mem_append_of _ _ hmem with
    | .inl h1 =>
      match ground.mem_map_of _ (places.pairsOf (e + 2)) _ h1 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem (e + 2) p
          (ground.countOf_pos_of_mem hp)
        refine confCore (sertables.tableD (e + 2)) W (e + 2) rfl
          nu0 hn0 j (fDiff p.1 p.2)
          (nbD (e + 2) (fDiff p.1 p.2))
          (by rw [← he]; rfl)
          (colD (e + 2) h1l (fDiff p.1 p.2)) hor hdomin x hwx
          hxl ?_
        exact confDiffD e p.1 p.2 W.length x hpr.1 hpr.2 hwx hxl
          hlast
    | .inr h1 =>
      match ground.mem_map_of _ (places.pairsOf (e + 2)) _ h1 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem (e + 2) p
          (ground.countOf_pos_of_mem hp)
        by_cases hb1 : p.2 + 1 = e + 2
        · have hb2 : p.2 = e + 1 := Nat.succ.inj hb1
          refine confCore (sertables.tableD (e + 2)) W (e + 2) rfl
            nu0 hn0 j (fSumDt e p.1) (nbD (e + 2) (fSumDt e p.1))
            (by rw [← he, hb2]; exact fSumDt_eq e p.1)
            (colD (e + 2) h1l (fSumDt e p.1)) hor hdomin x hwx
            hxl ?_
          exact confSumDt e p.1 W.length x
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hpr.1
              (Nat.le_of_eq hb2)))
            hwx hxl hlast
        · have hb2 : p.2 ≤ e := Nat.le_of_lt_succ
            (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hpr.2)
              (fun hc => hb1 (congrArg Nat.succ hc)))
          refine confCore (sertables.tableD (e + 2)) W (e + 2) rfl
            nu0 hn0 j (fSumD e p.1 p.2)
            (nbD (e + 2) (fSumD e p.1 p.2))
            (by rw [← he]; exact fSumD_eq e p.1 p.2 hb1)
            (colD (e + 2) h1l (fSumD e p.1 p.2)) hor hdomin x hwx
            hxl ?_
          exact confSumD e p.1 p.2 W.length x hpr.1 hb2 hwx hxl
            hlast


/-- `lem:serstable`(ii)'s off-diagonal read at the `B` series: at an
occupied content off the vacant one, the member display's target
count sits at or below one, the family's one occurrence against the
letter fold. -/
theorem rowOffOne_B : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (cVs : List (List BPair)) (nu0 : List BPair),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    sertables.fundShape (sertables.tableB l) F →
    sertables.gramRead (sertables.tableB l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableB l) →
    sertables.simplePosRead (sertables.tableB l) F →
    sertables.rhoDotRead (sertables.tableB l) F →
    row.rhoLenRead (sertables.tableB l) F →
    sertables.wShapeRead (sertables.tableB l) Wl →
    assembly.wCloseRead (sertables.tableB l) Wl →
    assembly.wDomAt (sertables.tableB l) Wl wits
      (poly.pnorm (elim.vecAdd (memberV W l)
        (sertables.rhoV (sertables.tableB l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableB l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableB l)))) →
    memberchar.mShapeRead (sertables.tableB l) L →
    row.thetaFamRead (sertables.tableB l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k) →
    ¬ nu0 = List.replicate l BPair.unit →
    steinberg.memberAt (sertables.tableB l) Wl L cVs
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) →
    ground.countOf (poly.pnorm (elim.vecAdd (memberV W l) nu0)) cVs
      ≤ 1 := by
  intro W l F Wl wits L cVs nu0 hs hl hshape hgram hgsym hsqr hsp hrd
    hrho hwsh hclose hdom htop hksq hmsh hfam hn0pos hdomin hoff hmem
  have hnu : nu0 ∈ L := ground.mem_of_countOf_pos nu0 L hn0pos
  have hone : ground.countOf nu0 L = 1 := by
    match hfam.2.2 nu0 hnu with
    | .inl hu => exact absurd hu hoff
    | .inr hex =>
      obtain ⟨j, hj, hor⟩ := hex
      have hjlt : j < (sertables.tableB l).posFolds.length :=
        Nat.lt_of_succ_lt_succ hj
      match hor with
      | .inl h1 =>
        rw [h1]
        exact (hfam.2.1 j hjlt).1
      | .inr h2 =>
        rw [h2]
        exact (hfam.2.1 j hjlt).2
  obtain ⟨hfalse, htrue⟩ := rowValues_B l F Wl wits L
    (memberV W l) (memberRho W l) nu0
    (memberVLen (sertables.tableB l) W l rfl)
    (fun i hi => kapAt (sertables.tableB l) W l rfl hi)
    (fun k hk => memberRhoPos W l k hk)
    hshape hgram hgsym hsqr hsp hrd hrho hwsh hclose hdom htop hksq
    hmsh hfam hn0pos hdomin
  have hlen : nu0.length = (sertables.tableB l).rank :=
    (hmsh nu0 hnu).1
  have hmem2 : ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
        nu0)) cVs
      + memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l)
            (sertables.rhoV (sertables.tableB l)))) nu0)) true
    = memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l)
          (sertables.rhoV (sertables.tableB l)))) nu0)) false := by
    rw [← offKey (sertables.tableB l) W l nu0 rfl hlen]
    exact hmem
  rw [hfalse, htrue, hone] at hmem2
  have hle : ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
        nu0)) cVs
      ≤ ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
          nu0)) cVs
        + letterFoldAt (sertables.tableB l) (memberRho W l) nu0 L :=
    Nat.le_add_right _ _
  rw [hmem2] at hle
  exact hle


/-- `lem:serstable`(ii)'s off-diagonal read at the `C` series: at an
occupied content off the vacant one, the member display's target
count sits at or below one, the family's one occurrence against the
letter fold. -/
theorem rowOffOne_C : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (cVs : List (List BPair)) (nu0 : List BPair),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    sertables.fundShape (sertables.tableC l) F →
    sertables.gramRead (sertables.tableC l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableC l) →
    sertables.simplePosRead (sertables.tableC l) F →
    sertables.rhoDotRead (sertables.tableC l) F →
    row.rhoLenRead (sertables.tableC l) F →
    sertables.wShapeRead (sertables.tableC l) Wl →
    assembly.wCloseRead (sertables.tableC l) Wl →
    assembly.wDomAt (sertables.tableC l) Wl wits
      (poly.pnorm (elim.vecAdd (memberV W l)
        (sertables.rhoV (sertables.tableC l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableC l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableC l)))) →
    memberchar.mShapeRead (sertables.tableC l) L →
    row.thetaFamRead (sertables.tableC l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k) →
    ¬ nu0 = List.replicate l BPair.unit →
    steinberg.memberAt (sertables.tableC l) Wl L cVs
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) →
    ground.countOf (poly.pnorm (elim.vecAdd (memberV W l) nu0)) cVs
      ≤ 1 := by
  intro W l F Wl wits L cVs nu0 hs hl hshape hgram hgsym hsqr hsp hrd
    hrho hwsh hclose hdom htop hksq hmsh hfam hn0pos hdomin hoff hmem
  have hnu : nu0 ∈ L := ground.mem_of_countOf_pos nu0 L hn0pos
  have hone : ground.countOf nu0 L = 1 := by
    match hfam.2.2 nu0 hnu with
    | .inl hu => exact absurd hu hoff
    | .inr hex =>
      obtain ⟨j, hj, hor⟩ := hex
      have hjlt : j < (sertables.tableC l).posFolds.length :=
        Nat.lt_of_succ_lt_succ hj
      match hor with
      | .inl h1 =>
        rw [h1]
        exact (hfam.2.1 j hjlt).1
      | .inr h2 =>
        rw [h2]
        exact (hfam.2.1 j hjlt).2
  obtain ⟨hfalse, htrue⟩ := rowValues_C l F Wl wits L
    (memberV W l) (memberRho W l) nu0
    (memberVLen (sertables.tableC l) W l rfl)
    (fun i hi => kapAt (sertables.tableC l) W l rfl hi)
    (fun k hk => memberRhoPos W l k hk)
    hshape hgram hgsym hsqr hsp hrd hrho hwsh hclose hdom htop hksq
    hmsh hfam hn0pos hdomin
  have hlen : nu0.length = (sertables.tableC l).rank :=
    (hmsh nu0 hnu).1
  have hmem2 : ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
        nu0)) cVs
      + memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l)
            (sertables.rhoV (sertables.tableC l)))) nu0)) true
    = memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l)
          (sertables.rhoV (sertables.tableC l)))) nu0)) false := by
    rw [← offKey (sertables.tableC l) W l nu0 rfl hlen]
    exact hmem
  rw [hfalse, htrue, hone] at hmem2
  have hle : ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
        nu0)) cVs
      ≤ ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
          nu0)) cVs
        + letterFoldAt (sertables.tableC l) (memberRho W l) nu0 L :=
    Nat.le_add_right _ _
  rw [hmem2] at hle
  exact hle


/-- `lem:serstable`(ii)'s off-diagonal read at the `D` series: at an
occupied content off the vacant one, the member display's target
count sits at or below one, the family's one occurrence against the
letter fold. -/
theorem rowOffOne_D : ∀ (W : List Nat) (l : Nat)
    (F : sertables.FundData) (Wl : List (List BPair × Bool))
    (wits : List (List Nat)) (L : List (List BPair))
    (cVs : List (List BPair)) (nu0 : List BPair),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length + 2 ≤ l →
    sertables.fundShape (sertables.tableD l) F →
    sertables.gramRead (sertables.tableD l) F →
    sertables.gramSymRead F →
    sertables.reflSquareRead (sertables.tableD l) →
    sertables.simplePosRead (sertables.tableD l) F →
    sertables.rhoDotRead (sertables.tableD l) F →
    row.rhoLenRead (sertables.tableD l) F →
    sertables.wShapeRead (sertables.tableD l) Wl →
    assembly.wCloseRead (sertables.tableD l) Wl →
    assembly.wDomAt (sertables.tableD l) Wl wits
      (poly.pnorm (elim.vecAdd (memberV W l)
        (sertables.rhoV (sertables.tableD l)))) →
    assembly.wTopAt Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableD l)))) →
    row.sqAtRead F Wl (poly.pnorm (elim.vecAdd (memberV W l)
      (sertables.rhoV (sertables.tableD l)))) →
    memberchar.mShapeRead (sertables.tableD l) L →
    row.thetaFamRead (sertables.tableD l) L →
    0 < ground.countOf nu0 L →
    (∀ k, k < l → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) k) →
    ¬ nu0 = List.replicate l BPair.unit →
    steinberg.memberAt (sertables.tableD l) Wl L cVs
      (poly.pnorm (elim.vecAdd (memberV W l) nu0)) →
    ground.countOf (poly.pnorm (elim.vecAdd (memberV W l) nu0)) cVs
      ≤ 1 := by
  intro W l F Wl wits L cVs nu0 hs hl hshape hgram hgsym hsqr hsp hrd
    hrho hwsh hclose hdom htop hksq hmsh hfam hn0pos hdomin hoff hmem
  have hnu : nu0 ∈ L := ground.mem_of_countOf_pos nu0 L hn0pos
  have hone : ground.countOf nu0 L = 1 := by
    match hfam.2.2 nu0 hnu with
    | .inl hu => exact absurd hu hoff
    | .inr hex =>
      obtain ⟨j, hj, hor⟩ := hex
      have hjlt : j < (sertables.tableD l).posFolds.length :=
        Nat.lt_of_succ_lt_succ hj
      match hor with
      | .inl h1 =>
        rw [h1]
        exact (hfam.2.1 j hjlt).1
      | .inr h2 =>
        rw [h2]
        exact (hfam.2.1 j hjlt).2
  obtain ⟨hfalse, htrue⟩ := rowValues_D l F Wl wits L
    (memberV W l) (memberRho W l) nu0
    (memberVLen (sertables.tableD l) W l rfl)
    (fun i hi => kapAt (sertables.tableD l) W l rfl hi)
    (fun k hk => memberRhoPos W l k hk)
    hshape hgram hgsym hsqr hsp hrd hrho hwsh hclose hdom htop hksq
    hmsh hfam hn0pos hdomin
  have hlen : nu0.length = (sertables.tableD l).rank :=
    (hmsh nu0 hnu).1
  have hmem2 : ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
        nu0)) cVs
      + memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV W l)
            (sertables.rhoV (sertables.tableD l)))) nu0)) true
    = memberchar.convCount Wl L (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (memberV W l)
          (sertables.rhoV (sertables.tableD l)))) nu0)) false := by
    rw [← offKey (sertables.tableD l) W l nu0 rfl hlen]
    exact hmem
  rw [hfalse, htrue, hone] at hmem2
  have hle : ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
        nu0)) cVs
      ≤ ground.countOf (poly.pnorm (elim.vecAdd (memberV W l)
          nu0)) cVs
        + letterFoldAt (sertables.tableD l) (memberRho W l) nu0 L :=
    Nat.le_add_right _ _
  rw [hmem2] at hle
  exact hle


/-! ## The `B` column kit's public tier: the fold list's case read
and the interior magnitude-two characterization -/

/-- The `B` positive list's case read at a key: the fold there is a
range map, its entry function reads the `B` column's count pair at
every key, and it is one of the three families — the difference or
the sum family at a coordinate pair, the short family at a
coordinate. -/
theorem foldsB_cases (l j : Nat)
    (hj : j < (sertables.foldsB l).length) :
    ∃ F : Nat → Nat,
      ground.getAt [] (sertables.foldsB l) j = (List.range l).map F
      ∧ ((∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
         ∨ (∃ a b, a < b ∧ b < l ∧ F = fSumB l a b)
         ∨ (∃ a, a < l ∧ F = fDiff a l)) := by
  have hmem : ground.getAt [] (sertables.foldsB l) j
      ∈ sertables.foldsB l :=
    ground.mem_getAt [] _ j hj
  match ground.mem_append_of _ _ hmem with
  | .inl h1 =>
    match ground.mem_append_of _ _ h1 with
    | .inl h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        exact ⟨fDiff p.1 p.2, by rw [← he]; rfl,
          Or.inl ⟨p.1, p.2, hpr.1, hpr.2, rfl⟩⟩
    | .inr h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        exact ⟨fSumB l p.1 p.2, by rw [← he]; exact fSumB_eq l p.1 p.2,
          Or.inr (Or.inl ⟨p.1, p.2, hpr.1, hpr.2, rfl⟩)⟩
  | .inr h1 =>
    match ground.mem_map_of _ (List.range l) _ h1 with
    | ⟨a, ha, he⟩ =>
      have hal : a < l := ground.ltOfMemRange ha
      exact ⟨fDiff a l, by rw [← he]; rfl,
        Or.inr (Or.inr ⟨a, hal, rfl⟩)⟩

/-- A value at or below one is no value grown by two. -/
private theorem ltTwo {x y : Nat} (hx : x ≤ 1) : ¬ x = y + 2 := by
  intro he
  rw [he] at hx
  exact Nat.not_succ_le_zero y (Nat.le_of_succ_le_succ hx)

/-- The plus-two pin: a value at or below one whose double is two
further values' sum grown by two is one at both of them vacant. -/
private theorem twoPin {A B C : Nat} (hA : A ≤ 1)
    (h : 2 * A = B + C + 2) : A = 1 ∧ B = 0 ∧ C = 0 := by
  match ground.leOneCases hA with
  | .inl h0 =>
    rw [h0] at h
    exact absurd h (ltTwo (Nat.zero_le 1))
  | .inr h1 =>
    rw [h1] at h
    have hz : (0 : Nat) = B + C := Nat.succ.inj (Nat.succ.inj h)
    exact ⟨h1, Nat.eq_zero_of_add_eq_zero_right hz.symm,
      Nat.eq_zero_of_add_eq_zero_left hz.symm⟩

/-- The minus-two pin: two values at or below one whose sum is a
third's double grown by two are both one at the third vacant. -/
private theorem negPin {A B C : Nat} (hA : A ≤ 1) (hC : C ≤ 1)
    (h : A + C = 2 * B + 2) : A = 1 ∧ C = 1 ∧ B = 0 := by
  match ground.leOneCases hA, ground.leOneCases hC with
  | .inl h0, .inl h1 =>
    rw [h0, h1] at h
    exact absurd h (ltTwo (Nat.zero_le 1))
  | .inl h0, .inr h1 =>
    rw [h0, h1] at h
    exact absurd h (ltTwo (Nat.le_refl 1))
  | .inr h0, .inl h1 =>
    rw [h0, h1] at h
    exact absurd h (ltTwo (Nat.le_refl 1))
  | .inr h0, .inr h1 =>
    rw [h0, h1] at h
    exact ⟨h0, h1, ground.twoMulZero (Nat.succ.inj (Nat.succ.inj h.symm))⟩

/-- The window family's plus-two read at a key and its two
neighbours: the doubled middle entry is the neighbours' sum grown
by two exactly at the window one key wide above the key. -/
private theorem diffTwo (a b m : Nat) :
    2 * fDiff a b (m + 1) = fDiff a b m + fDiff a b (m + 2) + 2
      ↔ (a = m + 1 ∧ b = m + 2) := by
  constructor
  · intro h
    obtain ⟨hy, hx, hz⟩ := twoPin (fDiff_le1 a b (m + 1)) h
    have h1 : a ≤ m + 1 := by
      by_cases hc : a ≤ m + 1
      · exact hc
      · rw [fDiff_lo a b (m + 1) hc] at hy
        exact Nat.noConfusion hy
    have h2 : m + 1 < b := by
      by_cases hc : m + 1 < b
      · exact hc
      · rw [fDiff_hi a b (m + 1) hc] at hy
        exact Nat.noConfusion hy
    have h3 : ¬ a ≤ m := by
      intro hc
      rw [fDiff_in a b m hc (Nat.lt_trans (Nat.lt_succ_self m) h2)] at hx
      exact Nat.noConfusion hx
    have h4 : ¬ m + 2 < b := by
      intro hc
      rw [fDiff_in a b (m + 2) (Nat.le_trans h1 (Nat.le_succ (m + 1))) hc]
        at hz
      exact Nat.noConfusion hz
    exact ⟨Nat.le_antisymm h1 (Nat.lt_of_not_le h3),
      Nat.le_antisymm (Nat.le_of_not_lt h4) (Nat.succ_le_of_lt h2)⟩
  · intro hab
    rw [hab.1, hab.2,
      fDiff_in (m + 1) (m + 2) (m + 1) (Nat.le_refl (m + 1))
        (Nat.lt_succ_self (m + 1)),
      fDiff_lo (m + 1) (m + 2) m (Nat.not_succ_le_self m),
      fDiff_hi (m + 1) (m + 2) (m + 2) (Nat.lt_irrefl (m + 2))]

/-- The window family's two neighbouring entries never sum to its
doubled middle entry grown by two. -/
private theorem diffNeg (a b m : Nat) :
    ¬ fDiff a b m + fDiff a b (m + 2) = 2 * fDiff a b (m + 1) + 2 := by
  intro h
  obtain ⟨h1, h2, h0⟩ :=
    negPin (fDiff_le1 a b m) (fDiff_le1 a b (m + 2)) h
  have ham : a ≤ m := by
    by_cases hc : a ≤ m
    · exact hc
    · rw [fDiff_lo a b m hc] at h1
      exact Nat.noConfusion h1
  have hb2 : m + 2 < b := by
    by_cases hc : m + 2 < b
    · exact hc
    · rw [fDiff_hi a b (m + 2) hc] at h2
      exact Nat.noConfusion h2
  rw [fDiff_in a b (m + 1) (Nat.le_trans ham (Nat.le_succ m))
    (Nat.lt_trans (Nat.lt_succ_self (m + 1)) hb2)] at h0
  exact Nat.noConfusion h0

/-- The `B` sum family's three consecutive entries inside the rank:
the eight patterns weakly rising by at most one a key, capped at
two. -/
private theorem sumTriple (l a b m : Nat) (hab : a < b) (hml : m + 2 < l) :
    (fSumB l a b m = 0 ∧ fSumB l a b (m + 1) = 0
        ∧ fSumB l a b (m + 2) = 0)
      ∨ (fSumB l a b m = 0 ∧ fSumB l a b (m + 1) = 0
          ∧ fSumB l a b (m + 2) = 1)
      ∨ (fSumB l a b m = 0 ∧ fSumB l a b (m + 1) = 1
          ∧ fSumB l a b (m + 2) = 1)
      ∨ (fSumB l a b m = 0 ∧ fSumB l a b (m + 1) = 1
          ∧ fSumB l a b (m + 2) = 2)
      ∨ (fSumB l a b m = 1 ∧ fSumB l a b (m + 1) = 1
          ∧ fSumB l a b (m + 2) = 1)
      ∨ (fSumB l a b m = 1 ∧ fSumB l a b (m + 1) = 1
          ∧ fSumB l a b (m + 2) = 2)
      ∨ (fSumB l a b m = 1 ∧ fSumB l a b (m + 1) = 2
          ∧ fSumB l a b (m + 2) = 2)
      ∨ (fSumB l a b m = 2 ∧ fSumB l a b (m + 1) = 2
          ∧ fSumB l a b (m + 2) = 2) := by
  have hm1 : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
  have hm0 : m < l := Nat.lt_trans (Nat.lt_succ_self m) hm1
  have hnb : ∀ k, ¬ a ≤ k → ¬ b ≤ k :=
    fun k hlo hc => hlo (Nat.le_trans (Nat.le_of_lt hab) hc)
  by_cases g0 : a ≤ m
  · by_cases g1 : b ≤ m
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨fSumB_hi l a b m g1 hm0,
          fSumB_hi l a b (m + 1) (Nat.le_trans g1 (Nat.le_succ m)) hm1,
          fSumB_hi l a b (m + 2)
            (Nat.le_trans g1 (Nat.le_add_right m 2)) hml⟩))))))
    · by_cases g2 : b ≤ m + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨fSumB_mid l a b m g0 (Nat.lt_of_not_le g1),
            fSumB_hi l a b (m + 1) g2 hm1,
            fSumB_hi l a b (m + 2)
              (Nat.le_trans g2 (Nat.le_succ (m + 1))) hml⟩))))))
      · by_cases g3 : b ≤ m + 2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨fSumB_mid l a b m g0 (Nat.lt_of_not_le g1),
              fSumB_mid l a b (m + 1) (Nat.le_trans g0 (Nat.le_succ m))
                (Nat.lt_of_not_le g2),
              fSumB_hi l a b (m + 2) g3 hml⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨fSumB_mid l a b m g0 (Nat.lt_of_not_le g1),
              fSumB_mid l a b (m + 1) (Nat.le_trans g0 (Nat.le_succ m))
                (Nat.lt_of_not_le g2),
              fSumB_mid l a b (m + 2)
                (Nat.le_trans g0 (Nat.le_add_right m 2))
                (Nat.lt_of_not_le g3)⟩))))
  · have hx0 : fSumB l a b m = 0 := fSumB_lo l a b m g0 (hnb m g0)
    by_cases g1 : a ≤ m + 1
    · have hbm1 : ¬ b ≤ m + 1 := fun hc =>
        Nat.lt_irrefl a (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hab hc) (Nat.lt_of_not_le g0))
      by_cases g3 : b ≤ m + 2
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hx0, fSumB_mid l a b (m + 1) g1 (Nat.lt_of_not_le hbm1),
            fSumB_hi l a b (m + 2) g3 hml⟩)))
      · exact Or.inr (Or.inr (Or.inl
          ⟨hx0, fSumB_mid l a b (m + 1) g1 (Nat.lt_of_not_le hbm1),
            fSumB_mid l a b (m + 2) (Nat.le_trans g1 (Nat.le_succ (m + 1)))
              (Nat.lt_of_not_le g3)⟩))
    · have hy0 : fSumB l a b (m + 1) = 0 :=
        fSumB_lo l a b (m + 1) g1 (hnb (m + 1) g1)
      by_cases g2 : a ≤ m + 2
      · exact Or.inr (Or.inl
          ⟨hx0, hy0, fSumB_mid l a b (m + 2) g2
            (Nat.lt_of_le_of_lt (Nat.lt_of_not_le g1) hab)⟩)
      · exact Or.inl ⟨hx0, hy0,
          fSumB_lo l a b (m + 2) g2 (hnb (m + 2) g2)⟩

/-- The `B` sum family's two neighbouring entries never sum to its
doubled middle entry grown by two. -/
private theorem sumNeg (l a b m : Nat) (hab : a < b) (hml : m + 2 < l) :
    ¬ fSumB l a b m + fSumB l a b (m + 2)
      = 2 * fSumB l a b (m + 1) + 2 := by
  intro h
  match sumTriple l a b m hab hml with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
  | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩)))))) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

set_option linter.unusedVariables false in
/-- At an interior key the diff family's column reads plus two
exactly at the narrow window.  The pair's order and the rank
binders are the frame the interior key states the read at; the
proof consumes none of them. -/
theorem fDiff_two (a b m l : Nat) (hab : a < b) (hbl : b < l)
    (hml : m + 2 < l) :
    2 * fDiff a b (m + 1) = fDiff a b m + fDiff a b (m + 2) + 2
      ↔ (a = m + 1 ∧ b = m + 2) :=
  diffTwo a b m

set_option linter.unusedVariables false in
/-- At an interior key the `B` sum family's column sits below plus
two.  The pair's top binder is the frame the read is stated at; the
proof consumes it nowhere. -/
theorem fSumB_two (a b m l : Nat) (hab : a < b) (hbl : b < l)
    (hml : m + 2 < l) :
    ¬ 2 * fSumB l a b (m + 1)
      = fSumB l a b m + fSumB l a b (m + 2) + 2 := by
  intro h
  match sumTriple l a b m hab hml with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
  | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩)))))) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

set_option linter.unusedVariables false in
/-- At an interior key the short family's column sits below plus
two.  The coordinate's own bound is the frame the read is stated
at; the proof consumes it nowhere. -/
theorem fShort_two (a m l : Nat) (hal : a < l) (hml : m + 2 < l) :
    ¬ 2 * fDiff a l (m + 1) = fDiff a l m + fDiff a l (m + 2) + 2 := by
  intro h
  have h2 : l = m + 2 := ((diffTwo a l m).mp h).2
  rw [h2] at hml
  exact Nat.lt_irrefl (m + 2) hml

/-- At an interior key every `B` family's column sits above minus
two. -/
theorem colB_notNegTwo (F : Nat → Nat) (m l : Nat)
    (hml : m + 2 < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ a b, a < b ∧ b < l ∧ F = fSumB l a b)
      ∨ (∃ a, a < l ∧ F = fDiff a l)) :
    ¬ F m + F (m + 2) = 2 * F (m + 1) + 2 := by
  intro h
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    rw [hF] at h
    exact diffNeg a b m h
  | .inr (.inl ⟨a, b, hab, _, hF⟩) =>
    rw [hF] at h
    exact sumNeg l a b m hab hml h
  | .inr (.inr ⟨a, _, hF⟩) =>
    rw [hF] at h
    exact diffNeg a l m h

set_option linter.unusedVariables false in
/-- The narrow diff family's column vector is vacant off its three
keys.  The interior binder is the frame the read is stated at; the
proof consumes it nowhere. -/
theorem fDiff_narrow_off (m l k : Nat) (hml : m + 2 < l)
    (hk : k < l) (h0 : ¬ k = m) (h1 : ¬ k = m + 1) (h2 : ¬ k = m + 2) :
    2 * fDiff (m + 1) (m + 2) k = nbB l (fDiff (m + 1) (m + 2)) k := by
  have hG : ∀ j, ¬ j = m + 1 → fDiff (m + 1) (m + 2) j = 0 := by
    intro j hj
    by_cases hle : m + 1 ≤ j
    · exact fDiff_hi (m + 1) (m + 2) j (fun hc =>
        hj (Nat.le_antisymm (Nat.le_of_lt_succ hc) hle))
    · exact fDiff_lo (m + 1) (m + 2) j hle
  rw [hG k h1, Nat.mul_zero]
  cases k with
  | zero =>
    rw [nbB_zero]
    by_cases hl : 1 < l
    · rw [if_pos hl, hG 1 (fun hc => h0 (Nat.succ.inj hc))]
    · rw [if_neg hl]
  | succ p =>
    rw [nbB_succ]
    by_cases ht : p + 2 = l
    · rw [if_pos (ground.eqBeqOf ht),
        hG p (fun hc => h2 (congrArg (· + 1) hc)), Nat.mul_zero]
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
        hG p (fun hc => h2 (congrArg (· + 1) hc)),
        hG (p + 2) (fun hc => h0 (Nat.succ.inj hc))]

/-! ## The run letters' vanishing: the raised content at an
interior letter sits off the θ list -/


/-- The window's entry is unchanged one key up off the window's two
edges. -/
private theorem fDiffShift (a b k : Nat) (h1 : ¬ k + 1 = a)
    (h2 : ¬ k + 1 = b) : fDiff a b (k + 1) = fDiff a b k := by
  by_cases hlo : a ≤ k
  · by_cases hhi : k < b
    · rw [fDiff_in a b (k + 1) (Nat.le_succ_of_le hlo)
        (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hhi) h2),
        fDiff_in a b k hlo hhi]
    · rw [fDiff_hi a b (k + 1) (fun hc => hhi (Nat.lt_of_succ_lt hc)),
        fDiff_hi a b k hhi]
  · rw [fDiff_lo a b (k + 1) (fun hc =>
      hlo (Nat.le_of_succ_le_succ (Nat.lt_of_le_of_ne hc
        (fun he => h1 he.symm)))),
      fDiff_lo a b k hlo]

set_option linter.unusedVariables false in
/-- The diff window's column is vacant off its four boundary
keys.  The key's own rank bound is the frame the read is stated at;
the proof consumes it nowhere. -/
theorem fDiff_off (a b k l : Nat) (hk : k < l)
    (h1 : ¬ k + 1 = a) (h2 : ¬ k = a)
    (h3 : ¬ k + 1 = b) (h4 : ¬ k = b) :
    2 * fDiff a b k = nbB l (fDiff a b) k := by
  cases k with
  | zero =>
    have hna : ¬ a ≤ 1 := by
      intro hc
      cases a with
      | zero => exact h2 rfl
      | succ p =>
        cases p with
        | zero => exact h1 rfl
        | succ q =>
          exact absurd (Nat.le_of_succ_le_succ hc) (Nat.not_succ_le_zero q)
    rw [fDiff_lo a b 0 (fun hc =>
        h2 (Nat.le_antisymm hc (Nat.zero_le a)).symm),
      Nat.mul_zero, nbB_zero]
    by_cases hl : 1 < l
    · rw [if_pos hl, fDiff_lo a b 1 hna]
    · rw [if_neg hl]
  | succ p =>
    rw [nbB_succ]
    by_cases ht : p + 2 = l
    · rw [if_pos (ground.eqBeqOf ht), fDiffShift a b p h2 h4]
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
        fDiffShift a b (p + 1) h1 h3, fDiffShift a b p h2 h4,
        Nat.two_mul]

/-- The `B` sum entry is unchanged one key up off the pair's edges
and the rank's own top. -/
private theorem fSumBShift (l a b k : Nat) (h1 : ¬ k + 1 = a)
    (h2 : ¬ k + 1 = b) (h3 : ¬ k + 1 = l) :
    fSumB l a b (k + 1) = fSumB l a b k := by
  show fDiff a b (k + 1) + (fDiff b l (k + 1) + fDiff b l (k + 1))
    = fDiff a b k + (fDiff b l k + fDiff b l k)
  rw [fDiffShift a b k h1 h2, fDiffShift b l k h2 h3]

/-- The B sum window's column is vacant off its four boundary
keys. -/
theorem fSumB_off (a b k l : Nat) (hk : k < l) (hbl : b < l)
    (h1 : ¬ k + 1 = a) (h2 : ¬ k = a)
    (h3 : ¬ k + 1 = b) (h4 : ¬ k = b) :
    2 * fSumB l a b k = nbB l (fSumB l a b) k := by
  cases k with
  | zero =>
    have hna : ¬ a ≤ 1 := by
      intro hc
      cases a with
      | zero => exact h2 rfl
      | succ p =>
        cases p with
        | zero => exact h1 rfl
        | succ q =>
          exact absurd (Nat.le_of_succ_le_succ hc) (Nat.not_succ_le_zero q)
    have hnb : ¬ b ≤ 1 := by
      intro hc
      cases b with
      | zero => exact h4 rfl
      | succ p =>
        cases p with
        | zero => exact h3 rfl
        | succ q =>
          exact absurd (Nat.le_of_succ_le_succ hc) (Nat.not_succ_le_zero q)
    rw [fSumB_lo l a b 0 (fun hc =>
          h2 (Nat.le_antisymm hc (Nat.zero_le a)).symm)
        (fun hc => h4 (Nat.le_antisymm hc (Nat.zero_le b)).symm),
      Nat.mul_zero, nbB_zero]
    by_cases hl : 1 < l
    · rw [if_pos hl, fSumB_lo l a b 1 hna hnb]
    · rw [if_neg hl]
  | succ p =>
    rw [nbB_succ]
    by_cases ht : p + 2 = l
    · rw [if_pos (ground.eqBeqOf ht)]
      have hbl2 : b < p + 2 := by rw [ht]; exact hbl
      have hb1 : b ≤ p + 1 := Nat.le_of_lt_succ hbl2
      have hbp : b ≤ p :=
        Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hb1 (fun he => h4 he.symm))
      have hEq : fSumB l a b (p + 1) = fSumB l a b p := by
        show fDiff a b (p + 1) + (fDiff b l (p + 1) + fDiff b l (p + 1))
          = fDiff a b p + (fDiff b l p + fDiff b l p)
        rw [fDiffShift a b p h2 h4,
          fDiff_in b l (p + 1) hb1 (by rw [← ht]; exact Nat.lt_succ_self (p + 1)),
          fDiff_in b l p hbp (by
            rw [← ht]
            exact Nat.lt_trans (Nat.lt_succ_self p) (Nat.lt_succ_self (p + 1)))]
      rw [hEq]
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
        fSumBShift l a b (p + 1) h1 h3 ht,
        fSumBShift l a b p h2 h4 (Nat.ne_of_lt hk),
        Nat.two_mul]

/-- A positive fold's normalized coroot vector reads its column
values entrywise. -/
theorem posCorootV_entry (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsB l) j
      = (List.range l).map F) :
    (ground.getAt ground.BPair.unit
      (poly.pnorm (sertables.posCorootV (sertables.tableB l) j))
      k).oneValue
      (ground.BPair.ofCounts (2 * F k) (nbB l F k)) := by
  have hkr : k < (sertables.tableB l).rank := hk
  have hf : ground.getAt [] (sertables.tableB l).posFolds j
      = (List.range l).map F := hfe
  rw [nuAtP (sertables.tableB l) j k hkr, hf]
  exact BPair.oneValue_trans (BPair.norm_oneValue _) (colB l F k hk)

/-! ### The count-pair reads and the θ count's vacant arm -/

/-- A `B` positive fold's balance partner reads the column values'
swap entrywise. -/
theorem negCorootV_entry (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsB l) j
      = (List.range l).map F) :
    (ground.getAt ground.BPair.unit
      (poly.pnorm (poly.neg
        (sertables.posCorootV (sertables.tableB l) j)))
      k).oneValue (ground.BPair.ofCounts (nbB l F k) (2 * F k)) := by
  have hkr : k < (sertables.tableB l).rank := hk
  have hf : ground.getAt [] (sertables.tableB l).posFolds j
      = (List.range l).map F := hfe
  rw [nuAtN (sertables.tableB l) j k hkr, hf,
    ← ground.BPair.ofCounts_swap (2 * F k) (nbB l F k)]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (ground.swap_congr (colB l F k hk))

/-- The two count reads as a count pair. -/
private theorem ofNatTwoCounts :
    (BPair.ofCounts 2 0).oneValue (BPair.ofNat 2) := by
  decide +kernel

/-- A count pair at the two reads its first count two above its
second. -/
private theorem countsTwo {p n : Nat}
    (h : (BPair.ofCounts p n).oneValue (BPair.ofNat 2)) : p = n + 2 := by
  have hc : p + 0 = 2 + n :=
    ground.BPair.ofCounts_cross (BPair.oneValue_trans h
      (BPair.oneValue_symm ofNatTwoCounts))
  rw [Nat.add_zero] at hc
  rw [hc]
  exact Nat.add_comm 2 n

/-- The θ count's vacant read: a content off the unit content and
off the positive list's two limbs. -/
private theorem thetaCountZero (t : gentable.Table) (x : List BPair)
    (h1 : ¬ x = List.replicate t.rank BPair.unit)
    (h2 : ¬ ∃ j, j + 1 < t.posFolds.length + 1
      ∧ (x = poly.pnorm (sertables.posCorootV t j)
         ∨ x = poly.pnorm (poly.neg (sertables.posCorootV t j)))) :
    row.thetaCount t x = 0 := by
  show (if x = List.replicate t.rank BPair.unit then t.rank
      else if ∃ j, j + 1 < t.posFolds.length + 1
          ∧ (x = poly.pnorm (sertables.posCorootV t j)
             ∨ x = poly.pnorm (poly.neg (sertables.posCorootV t j)))
        then 1 else 0) = 0
  rw [if_neg h1, if_neg h2]

/-- A raised content's entry at any table: the moved content's own
against the scaled Cartan row's, read before the entry's
identification. -/
theorem raisedAt (t : gentable.Table) (nu0 : List BPair)
    (hlen : nu0.length = t.rank) (c i : Nat)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank)
    (y : Nat) (hy : y < t.rank) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat c)
          (ground.getAt [] t.cartan i)))) y).oneValue
      (ground.getAt BPair.unit nu0 y
        + BPair.ofNat c * ground.getAt BPair.unit
            (ground.getAt [] t.cartan i) y) := by
  have hsl : (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i)).length = t.rank := by
    rw [elim.length_vecScale]
    exact hcl
  show (ground.getAt BPair.unit
    ((elim.vecAdd nu0 (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i))).map BPair.norm) y).oneValue _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ y
      (by rw [elim.length_vecAdd _ _ t.rank hlen hsl]; exact hy),
    elim.getAt_vecAdd _ _ y (by rw [hlen]; exact hy)
      (by rw [hsl]; exact hy),
    elim.getAt_vecScale _ _ y (by rw [hcl]; exact hy)]
  exact BPair.norm_oneValue _

/-- The raised entry at a table whose Cartan list is a stated
entry function's square, the scale one absorbed: the moved
content's own entry joined to the letter's Cartan value. -/
private theorem raisedEntryG (t : gentable.Table)
    (cart : Nat → Nat → BPair)
    (hcart : t.cartan = ground.matOf t.rank t.rank cart)
    (nu0 : List BPair) (hlen : nu0.length = t.rank)
    (i : Nat) (hil : i < t.rank) (y : Nat) (hy : y < t.rank) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] t.cartan i)))) y).oneValue
      (ground.getAt BPair.unit nu0 y + cart i y) := by
  have hcl : (ground.getAt [] t.cartan i).length = t.rank := by
    rw [hcart]
    exact ground.matOf_rowLength [] t.rank t.rank cart i hil
  have hcent : ground.getAt BPair.unit
      (ground.getAt [] t.cartan i) y = cart i y := by
    rw [hcart]
    exact ground.matOf_entry [] BPair.unit t.rank t.rank cart i y hil hy
  refine BPair.oneValue_trans (raisedAt t nu0 hlen 1 i hcl y hy) ?_
  rw [hcent]
  exact BPair.add_congr (BPair.oneValue_refl _)
    (BPair.ofNat_one_mul (cart i y))

private theorem raisedEntry (l m : Nat) (nu0 : List BPair)
    (hlen : nu0.length = l) (hm1l : m + 1 < l) (y : Nat) (hy : y < l) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableB l).cartan (m + 1)))))
      y).oneValue
      (ground.getAt BPair.unit nu0 y + cartB l (m + 1) y) :=
  raisedEntryG (sertables.tableB l) (fun i j => cartB l i j)
    (cartB_eq l) nu0 hlen (m + 1) hm1l y hy


/-- An interior plus-two column read at a `B` family pins the
narrow window: the doubled entry exceeding the neighbour fold by
two at a chain letter forces the one-key difference window at the
letter, the sum and short families refusing the read outright. -/
theorem narrowOfTwoB (l m : Nat) (F : Nat → Nat) (hml : m + 2 < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ a b, a < b ∧ b < l ∧ F = fSumB l a b)
      ∨ (∃ a, a < l ∧ F = fDiff a l))
    (hnat : 2 * F (m + 1) = F m + F (m + 2) + 2) :
    F = fDiff (m + 1) (m + 2) := by
  match hcase with
  | .inl ⟨a, b, hab, hbl, hF⟩ =>
    have hab2 :=
      (fDiff_two a b m l hab hbl hml).mp (by rw [← hF]; exact hnat)
    rw [hF, hab2.1, hab2.2]
  | .inr (.inl ⟨a, b, hab, hbl, hF⟩) =>
    rw [hF] at hnat
    exact absurd hnat (fSumB_two a b m l hab hbl hml)
  | .inr (.inr ⟨a, hal, hF⟩) =>
    rw [hF] at hnat
    exact absurd hnat (fShort_two a m l hal hml)

/-- The run letters vanish: at an interior letter with the moved
content vacant at the letter's own key and occupied at a witness
off its three keys, the raised content reads the vacant count. -/
theorem runVanishB (l m : Nat) (nu0 : List ground.BPair)
    (hml : m + 2 < l) (hlen : nu0.length = l)
    (hv1 : (ground.getAt ground.BPair.unit nu0 (m + 1)).oneValue
      ground.BPair.unit)
    (w : Nat) (hw : w < l) (hwoff : w < m ∨ m + 2 < w)
    (hocc : ¬ (ground.getAt ground.BPair.unit nu0 w).oneValue
      ground.BPair.unit) :
    row.thetaCount (sertables.tableB l)
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (ground.BPair.ofNat 1)
          (ground.getAt [] (sertables.tableB l).cartan (m + 1)))))
      = 0 := by
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
  have hwne : ¬ w = m ∧ ¬ w = m + 1 ∧ ¬ w = m + 2 := by
    match hwoff with
    | .inl h =>
      exact ⟨Nat.ne_of_lt h,
        Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_succ m)),
        Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right m 2))⟩
    | .inr h =>
      exact ⟨fun he => absurd h
          (by rw [he]; exact Nat.not_lt_of_ge (Nat.le_add_right m 2)),
        fun he => absurd h
          (by rw [he]; exact Nat.not_lt_of_ge (Nat.le_succ (m + 1))),
        fun he => absurd h (by rw [he]; exact Nat.lt_irrefl (m + 2))⟩
  have hx1 : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableB l).cartan (m + 1)))))
      (m + 1)).oneValue (BPair.ofNat 2) := by
    refine BPair.oneValue_trans (raisedEntry l m nu0 hlen hm1l (m + 1) hm1l) ?_
    rw [cartBd l (m + 1)]
    exact BPair.oneValue_trans
      (BPair.add_congr hv1 (BPair.oneValue_refl _)) (BPair.unit_add _)
  have hxw : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableB l).cartan (m + 1)))))
      w).oneValue (ground.getAt BPair.unit nu0 w) := by
    refine BPair.oneValue_trans (raisedEntry l m nu0 hlen hm1l w hw) ?_
    rw [cartBoff l (m + 1) w hwne.2.1 hwne.2.2
      (fun he => hwne.1 (Nat.succ.inj he))]
    exact BPair.add_unit _
  refine thetaCountZero (sertables.tableB l) _ ?_ ?_
  · intro he
    have hg : ground.getAt BPair.unit
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat 1)
            (ground.getAt [] (sertables.tableB l).cartan (m + 1)))))
        (m + 1) = BPair.unit := by
      rw [he]
      exact ground.getAt_replicate BPair.unit BPair.unit
        (sertables.tableB l).rank (m + 1) hm1l
    rw [hg] at hx1
    exact BPair.ofNat_off_unit 2 (Nat.succ_pos 1) (BPair.oneValue_symm hx1)
  · intro hex
    obtain ⟨j, hj, hor⟩ := hex
    have hjl : j < (sertables.foldsB l).length := Nat.lt_of_succ_lt_succ hj
    obtain ⟨F, hfe, hcase⟩ := foldsB_cases l j hjl
    have hmne : ¬ m + 2 = l := Nat.ne_of_lt hml
    match hor with
    | .inl he =>
      rw [he] at hx1 hxw
      have hnat : 2 * F (m + 1) = nbB l F (m + 1) + 2 :=
        countsTwo (BPair.oneValue_trans
          (BPair.oneValue_symm (posCorootV_entry l j (m + 1) F hm1l hfe)) hx1)
      rw [nbB_succ, if_neg (fun hb => hmne (ground.beqEqOf hb))] at hnat
      have hFn : F = fDiff (m + 1) (m + 2) :=
        narrowOfTwoB l m F hml hcase hnat
      refine hocc (BPair.oneValue_trans (BPair.oneValue_symm hxw)
        (BPair.oneValue_trans (posCorootV_entry l j w F hw hfe)
          (BPair.ofCounts_unit.mpr ?_)))
      rw [hFn]
      exact fDiff_narrow_off m l w hml hw hwne.1 hwne.2.1 hwne.2.2
    | .inr he =>
      rw [he] at hx1
      have hnv : (ground.getAt BPair.unit
          (poly.pnorm (poly.neg
            (sertables.posCorootV (sertables.tableB l) j)))
          (m + 1)).oneValue
          (BPair.ofCounts (nbB l F (m + 1)) (2 * F (m + 1))) := by
        have hf : ground.getAt [] (sertables.tableB l).posFolds j
            = (List.range l).map F := hfe
        rw [nuAtN (sertables.tableB l) j (m + 1) hm1l, hf,
          ← ground.BPair.ofCounts_swap (2 * F (m + 1)) (nbB l F (m + 1))]
        exact BPair.oneValue_trans (BPair.norm_oneValue _)
          (ground.swap_congr (colB l F (m + 1) hm1l))
      have hnat : nbB l F (m + 1) = 2 * F (m + 1) + 2 :=
        countsTwo (BPair.oneValue_trans (BPair.oneValue_symm hnv) hx1)
      rw [nbB_succ, if_neg (fun hb => hmne (ground.beqEqOf hb))] at hnat
      exact colB_notNegTwo F m l hml hcase hnat


/-! ## The `C` column kit's public tier: the fold list's case read,
the interior magnitude-two characterizations and the run letters'
vanishing -/

/-- The `C` positive list's case read at a key: the fold there is a
range map, its entry function reads the `C` column's count pair at
every key, and it is one of the three families — the difference
family at a coordinate pair, the sum family at a coordinate pair,
the long family at a coordinate, the last two at the rank's
successor presentation. -/
theorem foldsC_cases (l j : Nat)
    (hj : j < (sertables.foldsC l).length) :
    ∃ F : Nat → Nat,
      ground.getAt [] (sertables.foldsC l) j = (List.range l).map F
      ∧ ((∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
         ∨ (∃ d a b, l = d + 1 ∧ a < b ∧ b < l ∧ F = fSumC d a b)
         ∨ (∃ d a, l = d + 1 ∧ a < l ∧ F = fLong d a)) := by
  have hmem : ground.getAt [] (sertables.foldsC l) j
      ∈ sertables.foldsC l :=
    ground.mem_getAt [] _ j hj
  match ground.mem_append_of _ _ hmem with
  | .inl h1 =>
    match ground.mem_append_of _ _ h1 with
    | .inl h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        exact ⟨fDiff p.1 p.2, by rw [← he]; rfl,
          Or.inl ⟨p.1, p.2, hpr.1, hpr.2, rfl⟩⟩
    | .inr h2 =>
      match ground.mem_map_of _ (places.pairsOf l) _ h2 with
      | ⟨p, hp, he⟩ =>
        have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
        obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 :=
          ⟨l - 1, (ground.subAdd
            (Nat.lt_of_le_of_lt (Nat.zero_le p.2) hpr.2)).symm⟩
        exact ⟨fSumC d p.1 p.2,
          by rw [← he]; exact fSumC_eq d p.1 p.2,
          Or.inr (Or.inl ⟨d, p.1, p.2, rfl, hpr.1, hpr.2, rfl⟩)⟩
  | .inr h1 =>
    match ground.mem_map_of _ (List.range l) _ h1 with
    | ⟨a, ha, he⟩ =>
      have hal : a < l := ground.ltOfMemRange ha
      obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 :=
        ⟨l - 1, (ground.subAdd
          (Nat.lt_of_le_of_lt (Nat.zero_le a) hal)).symm⟩
      exact ⟨fLong d a, by rw [← he]; exact fLong_eq d a,
        Or.inr (Or.inr ⟨d, a, rfl, hal, rfl⟩)⟩

/-- The `C` sum family's three consecutive entries below the last
key: the eight patterns weakly rising by at most one a key, capped
at two. -/
private theorem sumTripleC (d a b m : Nat) (hab : a < b) (hbd : b ≤ d)
    (hint : m + 3 ≤ d) :
    (fSumC d a b m = 0 ∧ fSumC d a b (m + 1) = 0
        ∧ fSumC d a b (m + 2) = 0)
      ∨ (fSumC d a b m = 0 ∧ fSumC d a b (m + 1) = 0
          ∧ fSumC d a b (m + 2) = 1)
      ∨ (fSumC d a b m = 0 ∧ fSumC d a b (m + 1) = 1
          ∧ fSumC d a b (m + 2) = 1)
      ∨ (fSumC d a b m = 0 ∧ fSumC d a b (m + 1) = 1
          ∧ fSumC d a b (m + 2) = 2)
      ∨ (fSumC d a b m = 1 ∧ fSumC d a b (m + 1) = 1
          ∧ fSumC d a b (m + 2) = 1)
      ∨ (fSumC d a b m = 1 ∧ fSumC d a b (m + 1) = 1
          ∧ fSumC d a b (m + 2) = 2)
      ∨ (fSumC d a b m = 1 ∧ fSumC d a b (m + 1) = 2
          ∧ fSumC d a b (m + 2) = 2)
      ∨ (fSumC d a b m = 2 ∧ fSumC d a b (m + 1) = 2
          ∧ fSumC d a b (m + 2) = 2) := by
  have hm2 : m + 2 < d := hint
  have hm1 : m + 1 < d := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2
  have hm0 : m < d := Nat.lt_trans (Nat.lt_succ_self m) hm1
  by_cases g0 : a ≤ m
  · by_cases g1 : b ≤ m
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨fSumC_two d a b m g1 hm0,
          fSumC_two d a b (m + 1) (Nat.le_trans g1 (Nat.le_succ m)) hm1,
          fSumC_two d a b (m + 2)
            (Nat.le_trans g1 (Nat.le_add_right m 2)) hm2⟩))))))
    · by_cases g2 : b ≤ m + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨fSumC_mid d a b m g0 (Nat.lt_of_not_le g1) hbd,
            fSumC_two d a b (m + 1) g2 hm1,
            fSumC_two d a b (m + 2)
              (Nat.le_trans g2 (Nat.le_succ (m + 1))) hm2⟩))))))
      · by_cases g3 : b ≤ m + 2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨fSumC_mid d a b m g0 (Nat.lt_of_not_le g1) hbd,
              fSumC_mid d a b (m + 1) (Nat.le_trans g0 (Nat.le_succ m))
                (Nat.lt_of_not_le g2) hbd,
              fSumC_two d a b (m + 2) g3 hm2⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨fSumC_mid d a b m g0 (Nat.lt_of_not_le g1) hbd,
              fSumC_mid d a b (m + 1) (Nat.le_trans g0 (Nat.le_succ m))
                (Nat.lt_of_not_le g2) hbd,
              fSumC_mid d a b (m + 2)
                (Nat.le_trans g0 (Nat.le_add_right m 2))
                (Nat.lt_of_not_le g3) hbd⟩))))
  · have hx0 : fSumC d a b m = 0 :=
      fSumC_lo d a b m (Nat.lt_of_not_le g0) hab hbd
    by_cases g1 : a ≤ m + 1
    · have hbm1 : ¬ b ≤ m + 1 := fun hc =>
        Nat.lt_irrefl a (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hab hc) (Nat.lt_of_not_le g0))
      by_cases g3 : b ≤ m + 2
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hx0, fSumC_mid d a b (m + 1) g1 (Nat.lt_of_not_le hbm1) hbd,
            fSumC_two d a b (m + 2) g3 hm2⟩)))
      · exact Or.inr (Or.inr (Or.inl
          ⟨hx0, fSumC_mid d a b (m + 1) g1 (Nat.lt_of_not_le hbm1) hbd,
            fSumC_mid d a b (m + 2)
              (Nat.le_trans g1 (Nat.le_succ (m + 1)))
              (Nat.lt_of_not_le g3) hbd⟩))
    · have hy0 : fSumC d a b (m + 1) = 0 :=
        fSumC_lo d a b (m + 1) (Nat.lt_of_not_le g1) hab hbd
      by_cases g2 : a ≤ m + 2
      · exact Or.inr (Or.inl
          ⟨hx0, hy0, fSumC_mid d a b (m + 2) g2
            (Nat.lt_of_le_of_lt (Nat.lt_of_not_le g1) hab) hbd⟩)
      · exact Or.inl ⟨hx0, hy0,
          fSumC_lo d a b (m + 2) (Nat.lt_of_not_le g2) hab hbd⟩

/-- At an interior key the `C` sum family's column sits below plus
two. -/
theorem fSumC_two_refuse (d a b m : Nat) (hab : a < b)
    (hbd : b ≤ d) (hint : m + 3 ≤ d) :
    ¬ 2 * fSumC d a b (m + 1)
      = fSumC d a b m + fSumC d a b (m + 2) + 2 := by
  intro h
  match sumTripleC d a b m hab hbd hint with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
  | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩)))))) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

/-- At an interior key the `C` sum family's column sits above minus
two. -/
theorem fSumC_negTwo_refuse (d a b m : Nat) (hab : a < b)
    (hbd : b ≤ d) (hint : m + 3 ≤ d) :
    ¬ fSumC d a b m + fSumC d a b (m + 2)
      = 2 * fSumC d a b (m + 1) + 2 := by
  intro h
  match sumTripleC d a b m hab hbd hint with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
  | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩)))))) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

set_option linter.unusedVariables false in
/-- At an interior key the diff family's column sits above minus
two.  The pair's order is the frame the read is stated at; the
proof consumes it nowhere. -/
theorem fDiff_negTwo_refuse (a b m : Nat) (hab : a < b) :
    ¬ fDiff a b m + fDiff a b (m + 2) = 2 * fDiff a b (m + 1) + 2 :=
  diffNeg a b m

/-- The `C` long family's three consecutive entries at or below the
last key: the four positions of the family's coordinate against the
last key's own read. -/
private theorem longTripleC (d a m : Nat) (had : a ≤ d)
    (hint : m + 2 ≤ d) :
    (fLong d a m = 2 ∧ fLong d a (m + 1) = 2 ∧ fLong d a (m + 2) = 2)
      ∨ (fLong d a m = 2 ∧ fLong d a (m + 1) = 2
          ∧ fLong d a (m + 2) = 1)
      ∨ (fLong d a m = 0 ∧ fLong d a (m + 1) = 2
          ∧ fLong d a (m + 2) = 2 ∧ a = m + 1 ∧ m + 2 < d)
      ∨ (fLong d a m = 0 ∧ fLong d a (m + 1) = 2
          ∧ fLong d a (m + 2) = 1)
      ∨ (fLong d a m = 0 ∧ fLong d a (m + 1) = 0
          ∧ fLong d a (m + 2) = 2 ∧ a = m + 2 ∧ m + 2 < d)
      ∨ (fLong d a m = 0 ∧ fLong d a (m + 1) = 0
          ∧ fLong d a (m + 2) = 1)
      ∨ (fLong d a m = 0 ∧ fLong d a (m + 1) = 0
          ∧ fLong d a (m + 2) = 0) := by
  by_cases hmd : m + 2 = d
  · have hend : fLong d a (m + 2) = 1 := fLong_end d a (m + 2) hmd.symm
    have hm1 : m + 1 < d := by
      rw [← hmd]
      exact Nat.lt_succ_self (m + 1)
    have hm0 : m < d := Nat.lt_trans (Nat.lt_succ_self m) hm1
    by_cases ham : a ≤ m
    · exact Or.inr (Or.inl ⟨fLong_two d a m ham hm0,
        fLong_two d a (m + 1) (Nat.le_trans ham (Nat.le_succ m)) hm1,
        hend⟩)
    · have hlo : fLong d a m = 0 :=
        fLong_lo d a m (Nat.lt_of_not_le ham) had
      by_cases ham1 : a ≤ m + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hlo, fLong_two d a (m + 1) ham1 hm1, hend⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hlo, fLong_lo d a (m + 1) (Nat.lt_of_not_le ham1) had,
            hend⟩)))))
  · have hm2 : m + 2 < d := Nat.lt_of_le_of_ne hint hmd
    have hm1 : m + 1 < d := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2
    have hm0 : m < d := Nat.lt_trans (Nat.lt_succ_self m) hm1
    by_cases ham : a ≤ m
    · exact Or.inl ⟨fLong_two d a m ham hm0,
        fLong_two d a (m + 1) (Nat.le_trans ham (Nat.le_succ m)) hm1,
        fLong_two d a (m + 2)
          (Nat.le_trans ham (Nat.le_add_right m 2)) hm2⟩
    · have hlo : fLong d a m = 0 :=
        fLong_lo d a m (Nat.lt_of_not_le ham) had
      by_cases ham1 : a ≤ m + 1
      · exact Or.inr (Or.inr (Or.inl
          ⟨hlo, fLong_two d a (m + 1) ham1 hm1,
            fLong_two d a (m + 2)
              (Nat.le_trans ham1 (Nat.le_succ (m + 1))) hm2,
            Nat.le_antisymm ham1 (Nat.lt_of_not_le ham), hm2⟩))
      · have hlo1 : fLong d a (m + 1) = 0 :=
          fLong_lo d a (m + 1) (Nat.lt_of_not_le ham1) had
        by_cases ham2 : a ≤ m + 2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hlo, hlo1, fLong_two d a (m + 2) ham2 hm2,
              Nat.le_antisymm ham2 (Nat.lt_of_not_le ham1), hm2⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hlo, hlo1,
              fLong_lo d a (m + 2) (Nat.lt_of_not_le ham2) had⟩)))))

/-- At an interior key the long family's column reads plus two
exactly at its head. -/
theorem fLong_two_head (d a m : Nat) (had : a ≤ d)
    (hint : m + 3 ≤ d + 1) :
    (2 * fLong d a (m + 1) = fLong d a m + fLong d a (m + 2) + 2)
      ↔ (a = m + 1 ∧ m + 2 < d) := by
  constructor
  · intro h
    match longTripleC d a m had (Nat.le_of_succ_le_succ hint) with
    | .inl ⟨e0, e1, e2⟩
    | .inr (.inl ⟨e0, e1, e2⟩)
    | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
    | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
    | .inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩))))) =>
      rw [e0, e1, e2] at h
      exact absurd h (by decide +kernel)
    | .inr (.inr (.inl ⟨_, _, _, ha, hd⟩)) => exact ⟨ha, hd⟩
    | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2, _, _⟩)))) =>
      rw [e0, e1, e2] at h
      exact absurd h (by decide +kernel)
  · intro hae
    have hm1d : m + 1 < d :=
      Nat.lt_trans (Nat.lt_succ_self (m + 1)) hae.2
    have e1 : fLong d a (m + 1) = 2 := by
      rw [hae.1]
      exact fLong_two d (m + 1) (m + 1) (Nat.le_refl (m + 1)) hm1d
    have e0 : fLong d a m = 0 := by
      rw [hae.1]
      exact fLong_lo d (m + 1) m (Nat.lt_succ_self m) (Nat.le_of_lt hm1d)
    have e2 : fLong d a (m + 2) = 2 := by
      rw [hae.1]
      exact fLong_two d (m + 1) (m + 2) (Nat.le_succ (m + 1)) hae.2
    rw [e0, e1, e2]

/-- At an interior key the long family's column reads minus two
exactly one key below its head. -/
theorem fLong_negTwo (d a m : Nat) (had : a ≤ d)
    (hint : m + 3 ≤ d + 1) :
    (fLong d a m + fLong d a (m + 2) = 2 * fLong d a (m + 1) + 2)
      ↔ (a = m + 2 ∧ m + 2 < d) := by
  constructor
  · intro h
    match longTripleC d a m had (Nat.le_of_succ_le_succ hint) with
    | .inl ⟨e0, e1, e2⟩
    | .inr (.inl ⟨e0, e1, e2⟩)
    | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
    | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
    | .inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩))))) =>
      rw [e0, e1, e2] at h
      exact absurd h (by decide +kernel)
    | .inr (.inr (.inl ⟨e0, e1, e2, _, _⟩)) =>
      rw [e0, e1, e2] at h
      exact absurd h (by decide +kernel)
    | .inr (.inr (.inr (.inr (.inl ⟨_, _, _, ha, hd⟩)))) => exact ⟨ha, hd⟩
  · intro hae
    have hm1d : m + 1 < d :=
      Nat.lt_trans (Nat.lt_succ_self (m + 1)) hae.2
    have e2 : fLong d a (m + 2) = 2 := by
      rw [hae.1]
      exact fLong_two d (m + 2) (m + 2) (Nat.le_refl (m + 2)) hae.2
    have e1 : fLong d a (m + 1) = 0 := by
      rw [hae.1]
      exact fLong_lo d (m + 2) (m + 1) (Nat.lt_succ_self (m + 1))
        (Nat.le_of_lt hae.2)
    have e0 : fLong d a m = 0 := by
      rw [hae.1]
      exact fLong_lo d (m + 2) m
        (Nat.lt_trans (Nat.lt_succ_self m) (Nat.lt_succ_self (m + 1)))
        (Nat.le_of_lt hae.2)
    rw [e0, e1, e2]

set_option linter.unusedVariables false in
/-- The narrow diff window's column is vacant off its three keys,
at the `C` neighbour fold.  The key's own rank bound is the frame
the read is stated at; the proof consumes it nowhere. -/
theorem fDiffC_narrow_off (m l k : Nat) (hml : m + 3 < l)
    (hk : k < l) (h0 : ¬ k = m) (h1 : ¬ k = m + 1)
    (h2 : ¬ k = m + 2) :
    2 * fDiff (m + 1) (m + 2) k = nbC l (fDiff (m + 1) (m + 2)) k := by
  have h4l : 4 ≤ l := Nat.le_trans (Nat.le_add_left 4 m) hml
  have hG : ∀ j, ¬ j = m + 1 → fDiff (m + 1) (m + 2) j = 0 := by
    intro j hj
    by_cases hle : m + 1 ≤ j
    · exact fDiff_hi (m + 1) (m + 2) j (fun hc =>
        hj (Nat.le_antisymm (Nat.le_of_lt_succ hc) hle))
    · exact fDiff_lo (m + 1) (m + 2) j hle
  rw [hG k h1, Nat.mul_zero]
  cases k with
  | zero =>
    have h2l : ¬ (2 : Nat) = l := fun he => by
      rw [← he] at h4l
      exact absurd h4l (by decide +kernel)
    have h1l : (1 : Nat) < l :=
      Nat.lt_of_lt_of_le (show (1 : Nat) < 4 by decide +kernel) h4l
    rw [nbC_zero, if_neg (fun hb => h2l (ground.beqEqOf hb)),
      if_pos h1l, hG 1 (fun hc => h0 (Nat.succ.inj hc))]
  | succ p =>
    rw [nbC_succ]
    by_cases ht : p + 2 = l
    · rw [if_pos (ground.eqBeqOf ht),
        hG p (fun hc => h2 (congrArg (· + 1) hc))]
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      by_cases ht3 : p + 3 = l
      · rw [if_pos (ground.eqBeqOf ht3),
          hG p (fun hc => h2 (congrArg (· + 1) hc)),
          hG (p + 2) (fun hc => h0 (Nat.succ.inj hc))]
      · rw [if_neg (fun hb => ht3 (ground.beqEqOf hb)),
          hG p (fun hc => h2 (congrArg (· + 1) hc)),
          hG (p + 2) (fun hc => h0 (Nat.succ.inj hc))]

/-- The long family's column is vacant off its two pole keys. -/
theorem fLong_off (d a k : Nat) (had : a ≤ d) (hk : k < d + 1)
    (h1 : ¬ k + 1 = a) (h2 : ¬ k = a) :
    2 * fLong d a k = nbC (d + 1) (fLong d a) k := by
  cases k with
  | zero =>
    have hna : ¬ a ≤ 1 := by
      intro hc
      cases a with
      | zero => exact h2 rfl
      | succ u =>
        cases u with
        | zero => exact h1 rfl
        | succ q =>
          exact absurd (Nat.le_of_succ_le_succ hc)
            (Nat.not_succ_le_zero q)
    have h2a : 2 ≤ a := Nat.lt_of_not_le hna
    have hd2 : 2 ≤ d := Nat.le_trans h2a had
    have hne : ¬ 2 = d + 1 := fun he => by
      rw [← Nat.succ.inj he] at hd2
      exact Nat.not_succ_le_self 1 hd2
    have h1d : (1 : Nat) < d + 1 :=
      show 1 < d + 1 from Nat.succ_le_succ (Nat.le_trans (Nat.le_succ 1) hd2)
    rw [fLong_lo d a 0 (Nat.le_trans (Nat.le_succ 1) h2a) had,
      Nat.mul_zero, nbC_zero,
      if_neg (fun hb => hne (ground.beqEqOf hb)),
      if_pos h1d, fLong_lo d a 1 h2a had]
  | succ p =>
    rw [nbC_succ]
    by_cases ht : p + 2 = d + 1
    · have hd : d = p + 1 := (Nat.succ.inj ht).symm
      have hap : a ≤ p := by
        have hlt : a < d :=
          Nat.lt_of_le_of_ne had (fun he => h2 (he.trans hd).symm)
        rw [hd] at hlt
        exact Nat.le_of_lt_succ hlt
      rw [if_pos (ground.eqBeqOf ht), fLong_end d a (p + 1) hd,
        fLong_two d a p hap (by rw [hd]; exact Nat.lt_succ_self p)]
    · by_cases ht3 : p + 3 = d + 1
      · have hd : d = p + 2 := (Nat.succ.inj ht3).symm
        have hap : a ≤ p := by
          have hle2 : a ≤ p + 2 := by
            rw [← hd]
            exact had
          have hle1 : a ≤ p + 1 :=
            Nat.le_of_lt_succ
              (Nat.lt_of_le_of_ne hle2 (fun he => h1 he.symm))
          exact Nat.le_of_lt_succ
            (Nat.lt_of_le_of_ne hle1 (fun he => h2 he.symm))
        rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
          if_pos (ground.eqBeqOf ht3),
          fLong_two d a (p + 1) (Nat.le_succ_of_le hap)
            (by rw [hd]; exact Nat.lt_succ_self (p + 1)),
          fLong_two d a p hap
            (by
              rw [hd]
              exact Nat.lt_trans (Nat.lt_succ_self p)
                (Nat.lt_succ_self (p + 1))),
          fLong_end d a (p + 2) hd]
      · have hp1d : p + 1 < d :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk)
            (fun he => ht (congrArg Nat.succ he))
        have hp2d : p + 2 < d :=
          Nat.lt_of_le_of_ne hp1d (fun he => ht3 (congrArg Nat.succ he))
        have hpd : p < d := Nat.lt_trans (Nat.lt_succ_self p) hp1d
        rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
          if_neg (fun hb => ht3 (ground.beqEqOf hb))]
        by_cases hap : a ≤ p + 1
        · have hap0 : a ≤ p :=
            Nat.le_of_lt_succ
              (Nat.lt_of_le_of_ne hap (fun he => h2 he.symm))
          rw [fLong_two d a (p + 1) hap hp1d,
            fLong_two d a p hap0 hpd,
            fLong_two d a (p + 2) (Nat.le_succ_of_le hap) hp2d]
        · have hlt1 : p + 1 < a := Nat.lt_of_not_le hap
          have hlt2 : p + 2 < a := Nat.lt_of_le_of_ne hlt1 h1
          rw [fLong_lo d a (p + 1) hlt1 had,
            fLong_lo d a p (Nat.lt_trans (Nat.lt_succ_self p) hlt1) had,
            fLong_lo d a (p + 2) hlt2 had]

/-- The `C` sum family's column is vacant off its four boundary
keys. -/
theorem fSumC_off (d a b k : Nat) (hab : a < b) (hbd : b ≤ d)
    (hk : k < d + 1)
    (h1 : ¬ k + 1 = a) (h2 : ¬ k = a)
    (h3 : ¬ k + 1 = b) (h4 : ¬ k = b) :
    2 * fSumC d a b k = nbC (d + 1) (fSumC d a b) k := by
  cases k with
  | zero =>
    have hna : ¬ a ≤ 1 := by
      intro hc
      cases a with
      | zero => exact h2 rfl
      | succ u =>
        cases u with
        | zero => exact h1 rfl
        | succ q =>
          exact absurd (Nat.le_of_succ_le_succ hc)
            (Nat.not_succ_le_zero q)
    have h2a : 2 ≤ a := Nat.lt_of_not_le hna
    have h3b : 3 ≤ b := Nat.lt_of_le_of_lt h2a hab
    have hd3 : 3 ≤ d := Nat.le_trans h3b hbd
    have hne : ¬ 2 = d + 1 := fun he => by
      rw [← Nat.succ.inj he] at hd3
      exact absurd hd3 (by decide +kernel)
    have h1d : (1 : Nat) < d + 1 :=
      show 1 < d + 1 from Nat.succ_le_succ
        (Nat.le_trans (Nat.le_succ_of_le (Nat.le_succ 1)) hd3)
    rw [fSumC_lo d a b 0 (Nat.le_trans (Nat.le_succ 1) h2a) hab hbd,
      Nat.mul_zero, nbC_zero,
      if_neg (fun hb => hne (ground.beqEqOf hb)),
      if_pos h1d, fSumC_lo d a b 1 h2a hab hbd]
  | succ p =>
    rw [nbC_succ]
    by_cases ht : p + 2 = d + 1
    · have hd : d = p + 1 := (Nat.succ.inj ht).symm
      have hbp : b ≤ p := by
        have hlt : b < d :=
          Nat.lt_of_le_of_ne hbd (fun he => h4 (he.trans hd).symm)
        rw [hd] at hlt
        exact Nat.le_of_lt_succ hlt
      rw [if_pos (ground.eqBeqOf ht), fSumC_end d a b (p + 1) hbd hd,
        fSumC_two d a b p hbp (by rw [hd]; exact Nat.lt_succ_self p)]
    · by_cases ht3 : p + 3 = d + 1
      · have hd : d = p + 2 := (Nat.succ.inj ht3).symm
        have hbp : b ≤ p := by
          have hle2 : b ≤ p + 2 := by
            rw [← hd]
            exact hbd
          have hle1 : b ≤ p + 1 :=
            Nat.le_of_lt_succ
              (Nat.lt_of_le_of_ne hle2 (fun he => h3 he.symm))
          exact Nat.le_of_lt_succ
            (Nat.lt_of_le_of_ne hle1 (fun he => h4 he.symm))
        rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
          if_pos (ground.eqBeqOf ht3),
          fSumC_two d a b (p + 1) (Nat.le_succ_of_le hbp)
            (by rw [hd]; exact Nat.lt_succ_self (p + 1)),
          fSumC_two d a b p hbp
            (by
              rw [hd]
              exact Nat.lt_trans (Nat.lt_succ_self p)
                (Nat.lt_succ_self (p + 1))),
          fSumC_end d a b (p + 2) hbd hd]
      · have hp1d : p + 1 < d :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk)
            (fun he => ht (congrArg Nat.succ he))
        have hp2d : p + 2 < d :=
          Nat.lt_of_le_of_ne hp1d (fun he => ht3 (congrArg Nat.succ he))
        have hpd : p < d := Nat.lt_trans (Nat.lt_succ_self p) hp1d
        rw [if_neg (fun hb => ht (ground.beqEqOf hb)),
          if_neg (fun hb => ht3 (ground.beqEqOf hb))]
        by_cases hbp : b ≤ p
        · rw [fSumC_two d a b (p + 1) (Nat.le_succ_of_le hbp) hp1d,
            fSumC_two d a b p hbp hpd,
            fSumC_two d a b (p + 2)
              (Nat.le_trans hbp (Nat.le_add_right p 2)) hp2d]
        · have hb1 : p + 1 < b :=
            Nat.lt_of_le_of_ne (Nat.lt_of_not_le hbp) h4
          have hb2 : p + 2 < b := Nat.lt_of_le_of_ne hb1 h3
          by_cases hap : a ≤ p
          · rw [fSumC_mid d a b (p + 1) (Nat.le_succ_of_le hap) hb1 hbd,
              fSumC_mid d a b p hap (Nat.lt_of_not_le hbp) hbd,
              fSumC_mid d a b (p + 2)
                (Nat.le_trans hap (Nat.le_add_right p 2)) hb2 hbd]
          · have ha1 : p + 1 < a :=
              Nat.lt_of_le_of_ne (Nat.lt_of_not_le hap) h2
            have ha2 : p + 2 < a := Nat.lt_of_le_of_ne ha1 h1
            rw [fSumC_lo d a b (p + 1) ha1 hab hbd,
              fSumC_lo d a b p
                (Nat.lt_trans (Nat.lt_succ_self p) ha1) hab hbd,
              fSumC_lo d a b (p + 2) ha2 hab hbd]

/-- The raised content's entry at the `C` table: the content's own
against the Cartan row's. -/
private theorem raisedEntryC (l m : Nat) (nu0 : List BPair)
    (hlen : nu0.length = l) (hm1l : m + 1 < l) (y : Nat) (hy : y < l) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableC l).cartan (m + 1)))))
      y).oneValue
      (ground.getAt BPair.unit nu0 y + cartC l (m + 1) y) :=
  raisedEntryG (sertables.tableC l) (fun i j => cartC l i j)
    (cartC_eq l) nu0 hlen (m + 1) hm1l y hy

/-- The `C` positive list's coroot vectors read their column
values entrywise: the fold's coroot read at a key is the count
pair of the doubled entry against the neighbour fold. -/
theorem posCorootV_entryC (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsC l) j
      = (List.range l).map F) :
    (ground.getAt BPair.unit
      (poly.pnorm (sertables.posCorootV (sertables.tableC l) j))
      k).oneValue (BPair.ofCounts (2 * F k) (nbC l F k)) := by
  have hkr : k < (sertables.tableC l).rank := hk
  have hf : ground.getAt [] (sertables.tableC l).posFolds j
      = (List.range l).map F := hfe
  rw [nuAtP (sertables.tableC l) j k hkr, hf]
  exact BPair.oneValue_trans (BPair.norm_oneValue _) (colC l F k hk)

/-- A `C` positive fold's balance partner reads the column values'
swap entrywise. -/
theorem negCorootV_entryC (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsC l) j
      = (List.range l).map F) :
    (ground.getAt BPair.unit
      (poly.pnorm (poly.neg
        (sertables.posCorootV (sertables.tableC l) j)))
      k).oneValue (BPair.ofCounts (nbC l F k) (2 * F k)) := by
  have hkr : k < (sertables.tableC l).rank := hk
  have hf : ground.getAt [] (sertables.tableC l).posFolds j
      = (List.range l).map F := hfe
  rw [nuAtN (sertables.tableC l) j k hkr, hf,
    ← ground.BPair.ofCounts_swap (2 * F k) (nbC l F k)]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (ground.swap_congr (colC l F k hk))

/-- An interior plus-two column read at a `C` family splits two
ways: the one-key difference window at the letter, or the long
family's dipole with the letter its coordinate, the sum family
refusing the read outright. -/
theorem twoSplitC (l m : Nat) (F : Nat → Nat) (hml : m + 3 < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ d a b, l = d + 1 ∧ a < b ∧ b < l ∧ F = fSumC d a b)
      ∨ (∃ d a, l = d + 1 ∧ a < l ∧ F = fLong d a))
    (hnat : 2 * F (m + 1) = F m + F (m + 2) + 2) :
    F = fDiff (m + 1) (m + 2)
    ∨ ∃ d, l = d + 1 ∧ F = fLong d (m + 1) := by
  match hcase with
  | .inl ⟨a, b, hab, hbl, hF⟩ =>
    have hm2l : m + 2 < l := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hml
    have hab2 :=
      (fDiff_two a b m l hab hbl hm2l).mp (by rw [← hF]; exact hnat)
    exact Or.inl (by rw [hF, hab2.1, hab2.2])
  | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
    subst hld
    rw [hF] at hnat
    exact absurd hnat (fSumC_two_refuse d a b m hab
      (Nat.le_of_lt_succ hbl) (Nat.le_of_lt_succ hml))
  | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
    subst hld
    have had : a ≤ d := Nat.le_of_lt_succ hal
    have hhead := (fLong_two_head d a m had (Nat.le_of_lt hml)).mp
      (by rw [← hF]; exact hnat)
    exact Or.inr ⟨d, rfl, by rw [hF, hhead.1]⟩

/-- An interior minus-two column read at a `C` family is the long
family's dipole with the letter's successor its coordinate: the
difference and sum families refuse the read outright. -/
theorem negTwoLongC (l m : Nat) (F : Nat → Nat) (hml : m + 3 < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ d a b, l = d + 1 ∧ a < b ∧ b < l ∧ F = fSumC d a b)
      ∨ (∃ d a, l = d + 1 ∧ a < l ∧ F = fLong d a))
    (hnat : F m + F (m + 2) = 2 * F (m + 1) + 2) :
    ∃ d, l = d + 1 ∧ F = fLong d (m + 2) := by
  match hcase with
  | .inl ⟨a, b, hab, _, hF⟩ =>
    rw [hF] at hnat
    exact absurd hnat (fDiff_negTwo_refuse a b m hab)
  | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
    subst hld
    rw [hF] at hnat
    exact absurd hnat (fSumC_negTwo_refuse d a b m hab
      (Nat.le_of_lt_succ hbl) (Nat.le_of_lt_succ hml))
  | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
    subst hld
    have had : a ≤ d := Nat.le_of_lt_succ hal
    have hpole := (fLong_negTwo d a m had (Nat.le_of_lt hml)).mp
      (by rw [← hF]; exact hnat)
    exact ⟨d, rfl, by rw [hF, hpole.1]⟩

/-- The `C` run letters vanish: at an interior letter with the moved
content vacant at the letter's own key and occupied at a witness
off its three keys, the raised content reads the vacant count. -/
theorem runVanishC (l m : Nat) (nu0 : List ground.BPair)
    (hml : m + 3 < l) (hlen : nu0.length = l)
    (hv1 : (ground.getAt ground.BPair.unit nu0 (m + 1)).oneValue
      ground.BPair.unit)
    (w : Nat) (hw : w < l) (hwoff : w < m ∨ m + 2 < w)
    (hocc : ¬ (ground.getAt ground.BPair.unit nu0 w).oneValue
      ground.BPair.unit) :
    row.thetaCount (sertables.tableC l)
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (ground.BPair.ofNat 1)
          (ground.getAt [] (sertables.tableC l).cartan (m + 1)))))
      = 0 := by
  have hm2l : m + 2 < l := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hml
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
  have hwne : ¬ w = m ∧ ¬ w = m + 1 ∧ ¬ w = m + 2 := by
    match hwoff with
    | .inl h =>
      exact ⟨Nat.ne_of_lt h,
        Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_succ m)),
        Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right m 2))⟩
    | .inr h =>
      exact ⟨fun he => absurd h
          (by rw [he]; exact Nat.not_lt_of_ge (Nat.le_add_right m 2)),
        fun he => absurd h
          (by rw [he]; exact Nat.not_lt_of_ge (Nat.le_succ (m + 1))),
        fun he => absurd h (by rw [he]; exact Nat.lt_irrefl (m + 2))⟩
  have hx1 : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableC l).cartan (m + 1)))))
      (m + 1)).oneValue (BPair.ofNat 2) := by
    refine BPair.oneValue_trans
      (raisedEntryC l m nu0 hlen hm1l (m + 1) hm1l) ?_
    rw [cartCd l (m + 1)]
    exact BPair.oneValue_trans
      (BPair.add_congr hv1 (BPair.oneValue_refl _)) (BPair.unit_add _)
  have hxw : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableC l).cartan (m + 1)))))
      w).oneValue (ground.getAt BPair.unit nu0 w) := by
    refine BPair.oneValue_trans (raisedEntryC l m nu0 hlen hm1l w hw) ?_
    rw [cartCoff l (m + 1) w hwne.2.1
      (fun he => hwne.1 (Nat.succ.inj he)) hwne.2.2]
    exact BPair.add_unit _
  refine thetaCountZero (sertables.tableC l) _ ?_ ?_
  · intro he
    have hg : ground.getAt BPair.unit
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat 1)
            (ground.getAt [] (sertables.tableC l).cartan (m + 1)))))
        (m + 1) = BPair.unit := by
      rw [he]
      exact ground.getAt_replicate BPair.unit BPair.unit
        (sertables.tableC l).rank (m + 1) hm1l
    rw [hg] at hx1
    exact BPair.ofNat_off_unit 2 (Nat.succ_pos 1) (BPair.oneValue_symm hx1)
  · intro hex
    obtain ⟨j, hj, hor⟩ := hex
    have hjl : j < (sertables.foldsC l).length := Nat.lt_of_succ_lt_succ hj
    obtain ⟨F, hfe, hcase⟩ := foldsC_cases l j hjl
    have hmne2 : ¬ m + 2 = l := Nat.ne_of_lt hm2l
    have hmne3 : ¬ m + 3 = l := Nat.ne_of_lt hml
    match hor with
    | .inl he =>
      rw [he] at hx1 hxw
      have hnat : 2 * F (m + 1) = nbC l F (m + 1) + 2 :=
        countsTwo (BPair.oneValue_trans
          (BPair.oneValue_symm
            (posCorootV_entryC l j (m + 1) F hm1l hfe)) hx1)
      rw [nbC_succ, if_neg (fun hb => hmne2 (ground.beqEqOf hb)),
        if_neg (fun hb => hmne3 (ground.beqEqOf hb))] at hnat
      match twoSplitC l m F hml hcase hnat with
      | .inl hFn =>
        refine hocc (BPair.oneValue_trans (BPair.oneValue_symm hxw)
          (BPair.oneValue_trans (posCorootV_entryC l j w F hw hfe)
            (BPair.ofCounts_unit.mpr ?_)))
        rw [hFn]
        exact fDiffC_narrow_off m l w hml hw hwne.1 hwne.2.1 hwne.2.2
      | .inr ⟨d, hld, hFn⟩ =>
        subst hld
        have hm1d : m + 1 ≤ d := Nat.le_trans
          (Nat.le_add_right (m + 1) 2) (Nat.le_of_succ_le_succ hml)
        refine hocc (BPair.oneValue_trans (BPair.oneValue_symm hxw)
          (BPair.oneValue_trans (posCorootV_entryC (d + 1) j w F hw hfe)
            (BPair.ofCounts_unit.mpr ?_)))
        rw [hFn]
        exact fLong_off d (m + 1) w hm1d hw
          (fun he2 => hwne.1 (Nat.succ.inj he2))
          (fun he2 => hwne.2.1 he2)
    | .inr he =>
      rw [he] at hx1 hxw
      have hnat : nbC l F (m + 1) = 2 * F (m + 1) + 2 :=
        countsTwo (BPair.oneValue_trans
          (BPair.oneValue_symm
            (negCorootV_entryC l j (m + 1) F hm1l hfe)) hx1)
      rw [nbC_succ, if_neg (fun hb => hmne2 (ground.beqEqOf hb)),
        if_neg (fun hb => hmne3 (ground.beqEqOf hb))] at hnat
      obtain ⟨d, hld, hFn⟩ := negTwoLongC l m F hml hcase hnat
      subst hld
      have hm2d : m + 2 ≤ d := Nat.le_trans
        (Nat.le_add_right (m + 2) 1) (Nat.le_of_succ_le_succ hml)
      refine hocc (BPair.oneValue_trans (BPair.oneValue_symm hxw)
        (BPair.oneValue_trans (negCorootV_entryC (d + 1) j w F hw hfe)
          (BPair.ofCounts_unit.mpr ?_)))
      rw [hFn]
      exact (fLong_off d (m + 2) w hm2d hw
        (fun he2 => hwne.2.1 (Nat.succ.inj he2))
        (fun he2 => hwne.2.2 he2)).symm

/-! ### The `C` columns' magnitude cap -/

/-- The `C` difference column sits within two of its neighbour
fold: the window's entries stay at or below one and the last key's
read is vacant. -/
private theorem magDiffC (l a b k : Nat) (hbl : b < l) (hk : k < l) :
    2 * fDiff a b k ≤ nbC l (fDiff a b) k + 2
      ∧ nbC l (fDiff a b) k ≤ 2 * fDiff a b k + 2 := by
  have hone : ∀ i, fDiff a b i ≤ 1 := fun i => by
    by_cases h1 : a ≤ i
    · by_cases h2 : i < b
      · exact Nat.le_of_eq (fDiff_in a b i h1 h2)
      · rw [fDiff_hi a b i h2]
        exact Nat.zero_le 1
    · rw [fDiff_lo a b i h1]
      exact Nat.zero_le 1
  have hlow : 2 * fDiff a b k ≤ nbC l (fDiff a b) k + 2 :=
    Nat.le_trans (Nat.mul_le_mul_left 2 (hone k))
      (Nat.le_add_left 2 (nbC l (fDiff a b) k))
  refine ⟨hlow, ?_⟩
  match k with
  | 0 =>
    rw [nbC_zero]
    by_cases h2l : 2 = l
    · rw [if_pos (ground.eqBeqOf h2l)]
      exact Nat.le_trans (Nat.mul_le_mul_left 2 (hone 1))
        (Nat.le_add_left 2 (2 * fDiff a b 0))
    · rw [if_neg (fun hb => h2l (ground.beqEqOf hb))]
      by_cases h1l : 1 < l
      · rw [if_pos h1l]
        exact Nat.le_trans (hone 1)
          (Nat.le_trans (by decide +kernel)
            (Nat.le_add_left 2 (2 * fDiff a b 0)))
      · rw [if_neg h1l]
        exact Nat.zero_le _
  | m + 1 =>
    rw [nbC_succ]
    by_cases ht : m + 2 = l
    · rw [if_pos (ground.eqBeqOf ht)]
      exact Nat.le_trans (hone m)
        (Nat.le_trans (by decide +kernel)
          (Nat.le_add_left 2 (2 * fDiff a b (m + 1))))
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      by_cases hs : m + 3 = l
      · rw [if_pos (ground.eqBeqOf hs)]
        have hz : fDiff a b (m + 2) = 0 :=
          fDiff_hi a b (m + 2) (fun hc =>
            Nat.not_succ_le_self (m + 2)
              (Nat.le_trans (Nat.succ_le_of_lt hc)
                (by rw [← hs] at hbl; exact Nat.le_of_lt_succ hbl)))
        rw [hz, Nat.mul_zero, Nat.add_zero]
        exact Nat.le_trans (hone m)
          (Nat.le_trans (by decide +kernel)
            (Nat.le_add_left 2 (2 * fDiff a b (m + 1))))
      · rw [if_neg (fun hb => hs (ground.beqEqOf hb))]
        exact Nat.le_trans (Nat.add_le_add (hone m) (hone (m + 2)))
          (Nat.le_add_left 2 (2 * fDiff a b (m + 1)))

/-- The `C` sum column sits within two of its neighbour fold: the
window's steps move by one and the last key reads one. -/
private theorem magSumC (d a b k : Nat) (hab : a < b) (hbd : b < d + 1)
    (hk : k < d + 1) :
    2 * fSumC d a b k ≤ nbC (d + 1) (fSumC d a b) k + 2
      ∧ nbC (d + 1) (fSumC d a b) k ≤ 2 * fSumC d a b k + 2 := by
  have hbd' : b ≤ d := Nat.le_of_lt_succ hbd
  have hcap : ∀ i, i < d → fSumC d a b i ≤ 2 := fun i hid => by
    by_cases hbi : b ≤ i
    · rw [fSumC_two d a b i hbi hid]
      exact Nat.le_refl 2
    · by_cases hai : a ≤ i
      · rw [fSumC_mid d a b i hai (Nat.lt_of_not_le hbi) hbd']
        exact by decide +kernel
      · rw [fSumC_lo d a b i (Nat.lt_of_not_le hai) hab hbd']
        exact Nat.zero_le 2
  have hstep : ∀ i, i + 1 < d + 1 →
      fSumC d a b i ≤ fSumC d a b (i + 1) + 1
        ∧ fSumC d a b (i + 1) ≤ fSumC d a b i + 1 := fun i hi => by
    have hid : i < d := Nat.lt_of_succ_lt_succ hi
    have hv1 : fSumC d a b (i + 1) = 2 ∨ fSumC d a b (i + 1) = 1
        ∨ fSumC d a b (i + 1) = 0 := by
      by_cases h1d : i + 1 < d
      · by_cases hb1 : b ≤ i + 1
        · exact Or.inl (fSumC_two d a b (i + 1) hb1 h1d)
        · by_cases ha1 : a ≤ i + 1
          · exact Or.inr (Or.inl (fSumC_mid d a b (i + 1) ha1
              (Nat.lt_of_not_le hb1) hbd'))
          · exact Or.inr (Or.inr (fSumC_lo d a b (i + 1)
              (Nat.lt_of_not_le ha1) hab hbd'))
      · exact Or.inr (Or.inl (fSumC_end d a b (i + 1) hbd'
          (Nat.le_antisymm (Nat.le_of_not_lt h1d)
            (Nat.succ_le_of_lt hid))))
    by_cases hbi : b ≤ i
    · rw [fSumC_two d a b i hbi hid]
      have hb1 : b ≤ i + 1 := Nat.le_trans hbi (Nat.le_succ i)
      match hv1 with
      | .inl hv => rw [hv]; exact ⟨by decide +kernel, by decide +kernel⟩
      | .inr (.inl hv) =>
        rw [hv]; exact ⟨by decide +kernel, by decide +kernel⟩
      | .inr (.inr hv) =>
        exact absurd hv (by
          by_cases h1d : i + 1 < d
          · rw [fSumC_two d a b (i + 1) hb1 h1d]
            exact fun hc => absurd hc (by decide +kernel)
          · rw [fSumC_end d a b (i + 1) hbd'
              (Nat.le_antisymm (Nat.le_of_not_lt h1d)
                (Nat.succ_le_of_lt hid))]
            exact fun hc => absurd hc (by decide +kernel))
    · by_cases hai : a ≤ i
      · rw [fSumC_mid d a b i hai (Nat.lt_of_not_le hbi) hbd']
        match hv1 with
        | .inl hv => rw [hv]; exact ⟨by decide +kernel, by decide +kernel⟩
        | .inr (.inl hv) =>
          rw [hv]; exact ⟨by decide +kernel, by decide +kernel⟩
        | .inr (.inr hv) =>
          exact absurd hv (by
            have ha1 : a ≤ i + 1 := Nat.le_trans hai (Nat.le_succ i)
            by_cases h1d : i + 1 < d
            · by_cases hb1 : b ≤ i + 1
              · rw [fSumC_two d a b (i + 1) hb1 h1d]
                exact fun hc => absurd hc (by decide +kernel)
              · rw [fSumC_mid d a b (i + 1) ha1
                  (Nat.lt_of_not_le hb1) hbd']
                exact fun hc => absurd hc (by decide +kernel)
            · rw [fSumC_end d a b (i + 1) hbd'
                (Nat.le_antisymm (Nat.le_of_not_lt h1d)
                  (Nat.succ_le_of_lt hid))]
              exact fun hc => absurd hc (by decide +kernel))
      · rw [fSumC_lo d a b i (Nat.lt_of_not_le hai) hab hbd']
        match hv1 with
        | .inl hv =>
          exact absurd hv (by
            by_cases hb1 : b ≤ i + 1
            · exact absurd (Nat.le_trans hab hb1) (fun hc =>
                hai (Nat.le_of_succ_le_succ (Nat.le_trans hc
                  (Nat.le_refl (i + 1)))))
            · by_cases h1d : i + 1 < d
              · by_cases ha1 : a ≤ i + 1
                · rw [fSumC_mid d a b (i + 1) ha1
                    (Nat.lt_of_not_le hb1) hbd']
                  exact fun hc => absurd hc (by decide +kernel)
                · rw [fSumC_lo d a b (i + 1)
                    (Nat.lt_of_not_le ha1) hab hbd']
                  exact fun hc => absurd hc (by decide +kernel)
              · rw [fSumC_end d a b (i + 1) hbd'
                  (Nat.le_antisymm (Nat.le_of_not_lt h1d)
                    (Nat.succ_le_of_lt hid))]
                exact fun hc => absurd hc (by decide +kernel))
        | .inr (.inl hv) =>
          rw [hv]; exact ⟨by decide +kernel, by decide +kernel⟩
        | .inr (.inr hv) =>
          rw [hv]; exact ⟨by decide +kernel, by decide +kernel⟩
  match k with
  | 0 =>
    rw [nbC_zero]
    have h0le : fSumC d a b 0 ≤ 1 := by
      by_cases h0a : a = 0
      · rw [fSumC_mid d a b 0 (by rw [h0a]; exact Nat.le_refl 0)
          (by rw [← h0a]; exact hab) hbd']
        exact Nat.le_refl 1
      · rw [fSumC_lo d a b 0 (Nat.pos_of_ne_zero h0a) hab hbd']
        exact Nat.zero_le 1
    by_cases h2l : 2 = d + 1
    · rw [if_pos (ground.eqBeqOf h2l)]
      have h1e : fSumC d a b 1 = 1 :=
        fSumC_end d a b 1 hbd' (Nat.succ.inj h2l.symm)
      rw [h1e]
      exact ⟨Nat.le_trans (Nat.mul_le_mul_left 2 h0le)
          (by decide +kernel),
        Nat.le_trans (by decide +kernel)
          (Nat.le_add_left 2 (2 * fSumC d a b 0))⟩
    · rw [if_neg (fun hb => h2l (ground.beqEqOf hb))]
      have h1l : 1 < d + 1 := by
        match d with
        | 0 => exact absurd (Nat.lt_of_lt_of_le hab
            (Nat.le_of_lt_succ hbd)) (Nat.not_lt_zero a)
        | e + 1 => exact Nat.succ_lt_succ (Nat.zero_lt_succ e)
      rw [if_pos h1l]
      have h1v : fSumC d a b 1 ≤ 2 := by
        by_cases h1d : 1 < d
        · exact hcap 1 h1d
        · rw [fSumC_end d a b 1 hbd'
            (Nat.le_antisymm (Nat.le_of_not_lt h1d)
            (Nat.succ_le_of_lt (Nat.lt_of_succ_lt_succ h1l)))]
          exact by decide +kernel
      exact ⟨Nat.le_trans (Nat.mul_le_mul_left 2 h0le)
          (Nat.le_trans (by decide +kernel)
            (Nat.le_add_left 2 (fSumC d a b 1))),
        Nat.le_trans h1v (Nat.le_add_left 2 (2 * fSumC d a b 0))⟩
  | m + 1 =>
    rw [nbC_succ]
    by_cases ht : m + 2 = d + 1
    · rw [if_pos (ground.eqBeqOf ht)]
      have hme : fSumC d a b (m + 1) = 1 :=
        fSumC_end d a b (m + 1) hbd' (Nat.succ.inj ht).symm
      have hmd : m < d := by
        rw [← Nat.succ.inj ht]
        exact Nat.lt_succ_self m
      rw [hme]
      exact ⟨Nat.le_trans (by decide +kernel)
          (Nat.le_add_left 2 (fSumC d a b m)),
        Nat.le_trans (hcap m hmd) (by decide +kernel)⟩
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      by_cases hs : m + 3 = d + 1
      · rw [if_pos (ground.eqBeqOf hs)]
        have hm2d : m + 2 = d := Nat.succ.inj hs
        have hm1d : m + 1 < d := by
          rw [← hm2d]
          exact Nat.lt_succ_self (m + 1)
        have hmd : m < d := Nat.lt_trans (Nat.lt_succ_self m) hm1d
        have h2e : fSumC d a b (m + 2) = 1 :=
          fSumC_end d a b (m + 2) hbd' hm2d.symm
        rw [h2e]
        refine ⟨?_, ?_⟩
        · have h1v : fSumC d a b (m + 1) ≤ 2 := hcap (m + 1) hm1d
          exact Nat.le_trans
            (Nat.le_trans (Nat.mul_le_mul_left 2 h1v)
              (by decide +kernel))
            (Nat.le_add_left 4 (fSumC d a b m))
        · have hup : fSumC d a b m ≤ 2 * fSumC d a b (m + 1) := by
            by_cases hbm : b ≤ m
            · rw [fSumC_two d a b m hbm hmd,
                fSumC_two d a b (m + 1)
                  (Nat.le_trans hbm (Nat.le_succ m)) hm1d]
              exact by decide +kernel
            · by_cases ham : a ≤ m
              · rw [fSumC_mid d a b m ham (Nat.lt_of_not_le hbm) hbd']
                have h1v : 1 ≤ fSumC d a b (m + 1) := by
                  by_cases hb1 : b ≤ m + 1
                  · rw [fSumC_two d a b (m + 1) hb1 hm1d]
                    exact by decide +kernel
                  · rw [fSumC_mid d a b (m + 1)
                      (Nat.le_trans ham (Nat.le_succ m))
                      (Nat.lt_of_not_le hb1) hbd']
                    exact Nat.le_refl 1
                exact Nat.le_trans (by decide +kernel)
                  (Nat.mul_le_mul_left 2 h1v)
              · rw [fSumC_lo d a b m (Nat.lt_of_not_le ham) hab hbd']
                exact Nat.zero_le _
          exact Nat.add_le_add hup (Nat.le_refl 2)
      · rw [if_neg (fun hb => hs (ground.beqEqOf hb))]
        have hm2 : m + 2 < d + 1 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht
        have s1 := hstep m hk
        have s2 := hstep (m + 1) hm2
        exact magPairB (fSumC d a b (m + 1)) (fSumC d a b m)
          (fSumC d a b (m + 2)) s1.2 s2.1 s1.1 s2.2

/-- The `C` long column sits within two of its neighbour fold: the
head dipole's poles read the cap exactly and every further key
sits inside it. -/
private theorem magLongC (d a k : Nat) (had : a < d + 1)
    (hk : k < d + 1) :
    2 * fLong d a k ≤ nbC (d + 1) (fLong d a) k + 2
      ∧ nbC (d + 1) (fLong d a) k ≤ 2 * fLong d a k + 2 := by
  have had' : a ≤ d := Nat.le_of_lt_succ had
  have hin : ∀ i, i < d → a ≤ i → fLong d a i = 2 := fun i h1 h2 =>
    fLong_two d a i h2 h1
  have hout : ∀ i, i < a → fLong d a i = 0 := fun i h1 =>
    fLong_lo d a i h1 had'
  match k with
  | 0 =>
    rw [nbC_zero]
    by_cases h2l : 2 = d + 1
    · rw [if_pos (ground.eqBeqOf h2l)]
      have hd1 : d = 1 := Nat.succ.inj h2l.symm
      have h1e : fLong d a 1 = 1 := fLong_end d a 1 hd1
      rw [h1e]
      by_cases h0a : a ≤ 0
      · rw [hin 0 (by rw [hd1]; exact Nat.zero_lt_succ 0) h0a]
        exact ⟨by decide +kernel, by decide +kernel⟩
      · rw [hout 0 (Nat.lt_of_not_le h0a)]
        exact ⟨by decide +kernel, by decide +kernel⟩
    · rw [if_neg (fun hb => h2l (ground.beqEqOf hb))]
      by_cases h1l : 1 < d + 1
      · rw [if_pos h1l]
        by_cases hd1 : 1 < d
        · by_cases h1a : a ≤ 1
          · rw [hin 1 hd1 h1a]
            by_cases h0a : a ≤ 0
            · rw [hin 0 (Nat.lt_trans (Nat.zero_lt_succ 0) hd1) h0a]
              exact ⟨by decide +kernel, by decide +kernel⟩
            · rw [hout 0 (Nat.lt_of_not_le h0a)]
              exact ⟨by decide +kernel, by decide +kernel⟩
          · rw [hout 1 (Nat.lt_of_not_le h1a),
              hout 0 (Nat.lt_trans (Nat.zero_lt_succ 0)
                (Nat.lt_of_not_le h1a))]
            exact ⟨by decide +kernel, by decide +kernel⟩
        · have hde : d = 1 :=
            Nat.le_antisymm (Nat.le_of_not_lt hd1)
              (Nat.succ_le_of_lt (Nat.lt_of_succ_lt_succ h1l))
          exact absurd hde (fun hc => h2l (by rw [hc]))
      · rw [if_neg h1l]
        have hd0 : d = 0 := Nat.le_antisymm
          (Nat.le_of_succ_le_succ (Nat.le_of_not_lt h1l))
          (Nat.zero_le d)
        rw [fLong_end d a 0 hd0]
        exact ⟨by decide +kernel, by decide +kernel⟩
  | m + 1 =>
    rw [nbC_succ]
    by_cases ht : m + 2 = d + 1
    · rw [if_pos (ground.eqBeqOf ht)]
      have hmd : m + 1 = d := Nat.succ.inj ht
      have hme : fLong d a (m + 1) = 1 := fLong_end d a (m + 1) hmd.symm
      rw [hme]
      by_cases hma : a ≤ m
      · rw [hin m (by rw [← hmd]; exact Nat.lt_succ_self m) hma]
        exact ⟨by decide +kernel, by decide +kernel⟩
      · rw [hout m (Nat.lt_of_not_le hma)]
        exact ⟨by decide +kernel, by decide +kernel⟩
    · rw [if_neg (fun hb => ht (ground.beqEqOf hb))]
      by_cases hs : m + 3 = d + 1
      · rw [if_pos (ground.eqBeqOf hs)]
        have hm2d : m + 2 = d := Nat.succ.inj hs
        have hm1d : m + 1 < d := by
          rw [← hm2d]
          exact Nat.lt_succ_self (m + 1)
        have hmd : m < d := Nat.lt_trans (Nat.lt_succ_self m) hm1d
        have h2e : fLong d a (m + 2) = 1 :=
          fLong_end d a (m + 2) hm2d.symm
        rw [h2e]
        by_cases hma : a ≤ m
        · rw [hin m hmd hma,
            hin (m + 1) hm1d (Nat.le_trans hma (Nat.le_succ m))]
          exact ⟨by decide +kernel, by decide +kernel⟩
        · rw [hout m (Nat.lt_of_not_le hma)]
          by_cases h1a : a ≤ m + 1
          · rw [hin (m + 1) hm1d h1a]
            exact ⟨by decide +kernel, by decide +kernel⟩
          · rw [hout (m + 1) (Nat.lt_of_not_le h1a)]
            exact ⟨by decide +kernel, by decide +kernel⟩
      · rw [if_neg (fun hb => hs (ground.beqEqOf hb))]
        have hm2 : m + 2 < d + 1 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht
        have hm3 : m + 3 < d + 1 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm2) hs
        have hm2d : m + 2 < d := Nat.lt_of_succ_lt_succ hm3
        have hm1d : m + 1 < d :=
          Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2d
        have hmd : m < d := Nat.lt_trans (Nat.lt_succ_self m) hm1d
        by_cases hma : a ≤ m
        · rw [hin m hmd hma,
            hin (m + 1) hm1d (Nat.le_trans hma (Nat.le_succ m)),
            hin (m + 2) hm2d (Nat.le_trans hma
              (Nat.le_trans (Nat.le_succ m) (Nat.le_succ (m + 1))))]
          exact ⟨by decide +kernel, by decide +kernel⟩
        · rw [hout m (Nat.lt_of_not_le hma)]
          by_cases h1a : a ≤ m + 1
          · rw [hin (m + 1) hm1d h1a,
              hin (m + 2) hm2d (Nat.le_trans h1a (Nat.le_succ (m + 1)))]
            exact ⟨by decide +kernel, by decide +kernel⟩
          · rw [hout (m + 1) (Nat.lt_of_not_le h1a)]
            by_cases h2a : a ≤ m + 2
            · rw [hin (m + 2) hm2d h2a]
              exact ⟨by decide +kernel, by decide +kernel⟩
            · rw [hout (m + 2) (Nat.lt_of_not_le h2a)]
              exact ⟨by decide +kernel, by decide +kernel⟩

/-- Every `C` family's column sits within two of its neighbour
fold, at every key. -/
theorem colC_magLe (F : Nat → Nat) (k l : Nat) (hk : k < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ d a b, l = d + 1 ∧ a < b ∧ b < l ∧ F = fSumC d a b)
      ∨ (∃ d a, l = d + 1 ∧ a < l ∧ F = fLong d a)) :
    2 * F k ≤ nbC l F k + 2 ∧ nbC l F k ≤ 2 * F k + 2 := by
  match hcase with
  | .inl ⟨a, b, _, hbl, hF⟩ =>
    rw [hF]
    exact magDiffC l a b k hbl hk
  | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
    rw [hF, hld]
    rw [hld] at hbl hk
    exact magSumC d a b k hab hbl hk
  | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
    rw [hF, hld]
    rw [hld] at hal hk
    exact magLongC d a k hal hk

/-! ## The `D` column kit's public tier: the fold list's case read,
the interior magnitude-two characterizations, the run letters'
vanishing and the columns' magnitude cap -/

/-- The `D` positive list's case read at a key: the fold there is a
range map, its entry function reads the `D` column's count pair at
every key, and it is one of the three families — the difference
family at a coordinate pair, the sum family's generic member at a
coordinate pair below the fork, the last-coordinate member at a
coordinate, the last two at the rank's second successor
presentation. -/
theorem foldsD_cases (l j : Nat)
    (hj : j < (sertables.foldsD l).length) :
    ∃ F : Nat → Nat,
      ground.getAt [] (sertables.foldsD l) j = (List.range l).map F
      ∧ ((∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
         ∨ (∃ e a b, l = e + 2 ∧ a < b ∧ b ≤ e ∧ F = fSumD e a b)
         ∨ (∃ e a, l = e + 2 ∧ a ≤ e ∧ F = fSumDt e a)) := by
  have hmem : ground.getAt [] (sertables.foldsD l) j
      ∈ sertables.foldsD l :=
    ground.mem_getAt [] _ j hj
  match ground.mem_append_of _ _ hmem with
  | .inl h1 =>
    match ground.mem_map_of _ (places.pairsOf l) _ h1 with
    | ⟨p, hp, he⟩ =>
      have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      exact ⟨fDiff p.1 p.2, by rw [← he]; rfl,
        Or.inl ⟨p.1, p.2, hpr.1, hpr.2, rfl⟩⟩
  | .inr h1 =>
    match ground.mem_map_of _ (places.pairsOf l) _ h1 with
    | ⟨p, hp, he⟩ =>
      have hpr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      have h1p2 : 1 ≤ p.2 := Nat.lt_of_le_of_lt (Nat.zero_le p.1) hpr.1
      by_cases hbt : p.2 + 1 = l
      · obtain ⟨e, hpe⟩ : ∃ e, p.2 = e + 1 :=
          ⟨p.2 - 1, (ground.subAdd h1p2).symm⟩
        obtain rfl : l = e + 2 := by rw [← hbt, hpe]
        have hz : sertables.sumFoldD (e + 2) p.1 p.2
            = (List.range (e + 2)).map (fSumDt e p.1) := by
          rw [hpe]
          exact fSumDt_eq e p.1
        have hae : p.1 ≤ e := by
          have hlt : p.1 < e + 1 := by rw [← hpe]; exact hpr.1
          exact Nat.le_of_lt_succ hlt
        exact ⟨fSumDt e p.1, by rw [← he]; exact hz,
          Or.inr (Or.inr ⟨e, p.1, rfl, hae, rfl⟩)⟩
      · obtain ⟨e, he2⟩ : ∃ e, 2 + e = l :=
          Nat.le.dest (Nat.le_trans (Nat.succ_le_succ h1p2) hpr.2)
        obtain rfl : l = e + 2 := by rw [← he2]; exact Nat.add_comm 2 e
        have hz : sertables.sumFoldD (e + 2) p.1 p.2
            = (List.range (e + 2)).map (fSumD e p.1 p.2) :=
          fSumD_eq e p.1 p.2 hbt
        have hbe : p.2 ≤ e :=
          Nat.le_of_lt_succ (Nat.lt_of_le_of_ne
            (Nat.le_of_lt_succ hpr.2)
            (fun hx => hbt (congrArg (· + 1) hx)))
        exact ⟨fSumD e p.1 p.2, by rw [← he]; exact hz,
          Or.inr (Or.inl ⟨e, p.1, p.2, rfl, hpr.1, hbe, rfl⟩)⟩


/-- The `D` sum family's generic member at three consecutive
interior keys: the eight patterns weakly rising by at most one a
key, capped at two. -/
private theorem sumTripleD (e a b m : Nat) (hab : a < b) (hbe : b ≤ e)
    (hint : m + 3 ≤ e) :
    (fSumD e a b m = 0 ∧ fSumD e a b (m + 1) = 0
        ∧ fSumD e a b (m + 2) = 0)
      ∨ (fSumD e a b m = 0 ∧ fSumD e a b (m + 1) = 0
          ∧ fSumD e a b (m + 2) = 1)
      ∨ (fSumD e a b m = 0 ∧ fSumD e a b (m + 1) = 1
          ∧ fSumD e a b (m + 2) = 1)
      ∨ (fSumD e a b m = 0 ∧ fSumD e a b (m + 1) = 1
          ∧ fSumD e a b (m + 2) = 2)
      ∨ (fSumD e a b m = 1 ∧ fSumD e a b (m + 1) = 1
          ∧ fSumD e a b (m + 2) = 1)
      ∨ (fSumD e a b m = 1 ∧ fSumD e a b (m + 1) = 1
          ∧ fSumD e a b (m + 2) = 2)
      ∨ (fSumD e a b m = 1 ∧ fSumD e a b (m + 1) = 2
          ∧ fSumD e a b (m + 2) = 2)
      ∨ (fSumD e a b m = 2 ∧ fSumD e a b (m + 1) = 2
          ∧ fSumD e a b (m + 2) = 2) := by
  have hm2 : m + 2 < e := hint
  have hm1 : m + 1 < e := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2
  have hm0 : m < e := Nat.lt_trans (Nat.lt_succ_self m) hm1
  by_cases g0 : a ≤ m
  · by_cases g1 : b ≤ m
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨fSumD_two e a b m g1 hm0,
          fSumD_two e a b (m + 1) (Nat.le_trans g1 (Nat.le_succ m)) hm1,
          fSumD_two e a b (m + 2)
            (Nat.le_trans g1 (Nat.le_add_right m 2)) hm2⟩))))))
    · by_cases g2 : b ≤ m + 1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨fSumD_mid e a b m g0 (Nat.lt_of_not_le g1) hbe,
            fSumD_two e a b (m + 1) g2 hm1,
            fSumD_two e a b (m + 2)
              (Nat.le_trans g2 (Nat.le_succ (m + 1))) hm2⟩))))))
      · by_cases g3 : b ≤ m + 2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨fSumD_mid e a b m g0 (Nat.lt_of_not_le g1) hbe,
              fSumD_mid e a b (m + 1) (Nat.le_trans g0 (Nat.le_succ m))
                (Nat.lt_of_not_le g2) hbe,
              fSumD_two e a b (m + 2) g3 hm2⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨fSumD_mid e a b m g0 (Nat.lt_of_not_le g1) hbe,
              fSumD_mid e a b (m + 1) (Nat.le_trans g0 (Nat.le_succ m))
                (Nat.lt_of_not_le g2) hbe,
              fSumD_mid e a b (m + 2)
                (Nat.le_trans g0 (Nat.le_add_right m 2))
                (Nat.lt_of_not_le g3) hbe⟩))))
  · have hx0 : fSumD e a b m = 0 :=
      fSumD_lo e a b m (Nat.lt_of_not_le g0) hab hbe
    by_cases g1 : a ≤ m + 1
    · have hbm1 : ¬ b ≤ m + 1 := fun hc =>
        Nat.lt_irrefl a (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hab hc) (Nat.lt_of_not_le g0))
      by_cases g3 : b ≤ m + 2
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hx0, fSumD_mid e a b (m + 1) g1 (Nat.lt_of_not_le hbm1) hbe,
            fSumD_two e a b (m + 2) g3 hm2⟩)))
      · exact Or.inr (Or.inr (Or.inl
          ⟨hx0, fSumD_mid e a b (m + 1) g1 (Nat.lt_of_not_le hbm1) hbe,
            fSumD_mid e a b (m + 2)
              (Nat.le_trans g1 (Nat.le_succ (m + 1)))
              (Nat.lt_of_not_le g3) hbe⟩))
    · have hy0 : fSumD e a b (m + 1) = 0 :=
        fSumD_lo e a b (m + 1) (Nat.lt_of_not_le g1) hab hbe
      by_cases g2 : a ≤ m + 2
      · exact Or.inr (Or.inl
          ⟨hx0, hy0, fSumD_mid e a b (m + 2) g2
            (Nat.lt_of_le_of_lt (Nat.lt_of_not_le g1) hab) hbe⟩)
      · exact Or.inl ⟨hx0, hy0,
          fSumD_lo e a b (m + 2) (Nat.lt_of_not_le g2) hab hbe⟩

/-- The `D` sum family's last-coordinate member at three
consecutive interior keys: the four positions of the family's
coordinate against them. -/
private theorem sumTripleDt (e a m : Nat) (hae : a ≤ e)
    (hint : m + 3 ≤ e) :
    (fSumDt e a m = 0 ∧ fSumDt e a (m + 1) = 0
        ∧ fSumDt e a (m + 2) = 0)
      ∨ (fSumDt e a m = 0 ∧ fSumDt e a (m + 1) = 0
          ∧ fSumDt e a (m + 2) = 1)
      ∨ (fSumDt e a m = 0 ∧ fSumDt e a (m + 1) = 1
          ∧ fSumDt e a (m + 2) = 1)
      ∨ (fSumDt e a m = 1 ∧ fSumDt e a (m + 1) = 1
          ∧ fSumDt e a (m + 2) = 1) := by
  have hm2 : m + 2 < e := hint
  have hm1 : m + 1 < e := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2
  have hm0 : m < e := Nat.lt_trans (Nat.lt_succ_self m) hm1
  by_cases g0 : a ≤ m
  · exact Or.inr (Or.inr (Or.inr
      ⟨fSumDt_mid e a m g0 hm0,
        fSumDt_mid e a (m + 1) (Nat.le_trans g0 (Nat.le_succ m)) hm1,
        fSumDt_mid e a (m + 2)
          (Nat.le_trans g0 (Nat.le_add_right m 2)) hm2⟩))
  · have hx0 : fSumDt e a m = 0 :=
      fSumDt_lo e a m (Nat.lt_of_not_le g0) hae
    by_cases g1 : a ≤ m + 1
    · exact Or.inr (Or.inr (Or.inl
        ⟨hx0, fSumDt_mid e a (m + 1) g1 hm1,
          fSumDt_mid e a (m + 2)
            (Nat.le_trans g1 (Nat.le_succ (m + 1))) hm2⟩))
    · have hy0 : fSumDt e a (m + 1) = 0 :=
        fSumDt_lo e a (m + 1) (Nat.lt_of_not_le g1) hae
      by_cases g2 : a ≤ m + 2
      · exact Or.inr (Or.inl
          ⟨hx0, hy0, fSumDt_mid e a (m + 2) g2 hm2⟩)
      · exact Or.inl ⟨hx0, hy0,
          fSumDt_lo e a (m + 2) (Nat.lt_of_not_le g2) hae⟩

/-- At an interior key the `D` sum family's generic column sits
below plus two. -/
theorem fSumD_two_refuse (e a b m : Nat) (hab : a < b) (hbe : b ≤ e)
    (hint : m + 3 ≤ e) :
    ¬ 2 * fSumD e a b (m + 1)
      = fSumD e a b m + fSumD e a b (m + 2) + 2 := by
  intro h
  match sumTripleD e a b m hab hbe hint with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
  | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩)))))) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

/-- At an interior key the `D` sum family's generic column sits
above minus two. -/
theorem fSumD_negTwo_refuse (e a b m : Nat) (hab : a < b)
    (hbe : b ≤ e) (hint : m + 3 ≤ e) :
    ¬ fSumD e a b m + fSumD e a b (m + 2)
      = 2 * fSumD e a b (m + 1) + 2 := by
  intro h
  match sumTripleD e a b m hab hbe hint with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))
  | .inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩)))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e0, e1, e2⟩))))))
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨e0, e1, e2⟩)))))) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

/-- At an interior key the `D` sum family's last-coordinate column
sits below plus two. -/
theorem fSumDt_two_refuse (e a m : Nat) (hae : a ≤ e)
    (hint : m + 3 ≤ e) :
    ¬ 2 * fSumDt e a (m + 1)
      = fSumDt e a m + fSumDt e a (m + 2) + 2 := by
  intro h
  match sumTripleDt e a m hae hint with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr ⟨e0, e1, e2⟩)) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)

/-- At an interior key the `D` sum family's last-coordinate column
sits above minus two. -/
theorem fSumDt_negTwo_refuse (e a m : Nat) (hae : a ≤ e)
    (hint : m + 3 ≤ e) :
    ¬ fSumDt e a m + fSumDt e a (m + 2)
      = 2 * fSumDt e a (m + 1) + 2 := by
  intro h
  match sumTripleDt e a m hae hint with
  | .inl ⟨e0, e1, e2⟩
  | .inr (.inl ⟨e0, e1, e2⟩)
  | .inr (.inr (.inl ⟨e0, e1, e2⟩))
  | .inr (.inr (.inr ⟨e0, e1, e2⟩)) =>
    rw [e0, e1, e2] at h
    exact absurd h (by decide +kernel)


/-- The entry one key below vanishes where the key's predecessor
read vanishes. -/
theorem pvD_zeroOf (F : Nat → Nat) (k : Nat)
    (h : ∀ j, k = j + 1 → F j = 0) : pvD F k = 0 := by
  match k with
  | 0 => exact pvD_zero F
  | p + 1 =>
    rw [pvD_succ F p]
    exact h p rfl

/-- The entry two keys below vanishes where the key's second
predecessor read vanishes. -/
theorem pv2D_zeroOf (F : Nat → Nat) (k : Nat)
    (h : ∀ j, k = j + 2 → F j = 0) : pv2D F k = 0 := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | q + 2 =>
    rw [pv2D_succ2 F q]
    exact h q rfl

/-- The entry one key below inherits a family's cap. -/
private theorem pvD_le (F : Nat → Nat) (c k : Nat)
    (h : ∀ i, F i ≤ c) : pvD F k ≤ c := by
  match k with
  | 0 =>
    rw [pvD_zero F]
    exact Nat.zero_le c
  | p + 1 =>
    rw [pvD_succ F p]
    exact h p

/-- The entry two keys below inherits a family's cap. -/
private theorem pv2D_le (F : Nat → Nat) (c k : Nat)
    (h : ∀ i, F i ≤ c) : pv2D F k ≤ c := by
  match k with
  | 0 => exact Nat.zero_le c
  | 1 => exact Nat.zero_le c
  | q + 2 =>
    rw [pv2D_succ2 F q]
    exact h q

set_option linter.unusedVariables false in
/-- The narrow diff window's column is vacant off its three keys,
at the `D` neighbour fold.  The key's own rank bound is the frame
the read is stated at; the proof consumes it nowhere. -/
theorem fDiffD_narrow_off (m l k : Nat) (hml : m + 4 < l)
    (hk : k < l) (h0 : ¬ k = m) (h1 : ¬ k = m + 1)
    (h2 : ¬ k = m + 2) :
    2 * fDiff (m + 1) (m + 2) k = nbD l (fDiff (m + 1) (m + 2)) k := by
  have hG : ∀ j, ¬ j = m + 1 → fDiff (m + 1) (m + 2) j = 0 := by
    intro j hj
    by_cases hle : m + 1 ≤ j
    · exact fDiff_hi (m + 1) (m + 2) j (fun hc =>
        hj (Nat.le_antisymm (Nat.le_of_lt_succ hc) hle))
    · exact fDiff_lo (m + 1) (m + 2) j hle
  have hpv : pvD (fDiff (m + 1) (m + 2)) k = 0 :=
    pvD_zeroOf (fDiff (m + 1) (m + 2)) k (fun j hj1 =>
      hG j (fun hx => h2 (hj1.trans (congrArg (· + 1) hx))))
  have hf1 : fDiff (m + 1) (m + 2) (k + 1) = 0 :=
    hG (k + 1) (fun hx => h0 (Nat.succ.inj hx))
  rw [hG k h1, Nat.mul_zero, nbD_eq]
  by_cases t1 : k + 1 = l
  · rw [if_pos (ground.eqBeqOf t1)]
    refine (pv2D_zeroOf (fDiff (m + 1) (m + 2)) k (fun j hj2 => ?_)).symm
    have hl3 : j + 3 = l := by rw [← t1, hj2]
    have hlj : m + 4 < j + 3 := by rw [hl3]; exact hml
    have hgt : m + 1 < j :=
      Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
        (Nat.lt_of_succ_lt_succ hlj))
    exact hG j (fun hx => Nat.lt_irrefl j (by rw [← hx] at hgt; exact hgt))
  · rw [if_neg (fun hb => t1 (ground.beqEqOf hb))]
    by_cases t2 : k + 2 = l
    · rw [if_pos (ground.eqBeqOf t2), hpv]
    · rw [if_neg (fun hb => t2 (ground.beqEqOf hb))]
      by_cases t3 : k + 3 = l
      · rw [if_pos (ground.eqBeqOf t3), hpv, hf1]
        have hlk : m + 4 < k + 3 := by rw [t3]; exact hml
        have hgt : m + 1 < k :=
          Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
            (Nat.lt_of_succ_lt_succ hlk))
        rw [hG (k + 2) (fun hx => Nat.lt_irrefl k
          (Nat.lt_of_le_of_lt (Nat.le_add_right k 2)
            (by rw [hx]; exact hgt)))]
      · rw [if_neg (fun hb => t3 (ground.beqEqOf hb)), hpv, hf1]


/-! ### The `D` columns' magnitude cap -/

/-- The `D` difference column sits within two of its neighbour
fold: the window's entries stay at or below one, and at the fork
the third read sits beyond the pair's top. -/
private theorem magDiffD (l a b k : Nat) (hbl : b < l) :
    2 * fDiff a b k ≤ nbD l (fDiff a b) k + 2
      ∧ nbD l (fDiff a b) k ≤ 2 * fDiff a b k + 2 := by
  have hone : ∀ i, fDiff a b i ≤ 1 := fDiff_le1 a b
  refine ⟨Nat.le_trans (Nat.mul_le_mul_left 2 (hone k))
      (Nat.le_add_left 2 (nbD l (fDiff a b) k)), ?_⟩
  refine Nat.le_trans ?_ (Nat.le_add_left 2 (2 * fDiff a b k))
  rw [nbD_eq]
  by_cases t1 : k + 1 = l
  · rw [if_pos (ground.eqBeqOf t1)]
    exact Nat.le_trans (pv2D_le (fDiff a b) 1 k hone) (by decide +kernel)
  · rw [if_neg (fun hb => t1 (ground.beqEqOf hb))]
    by_cases t2 : k + 2 = l
    · rw [if_pos (ground.eqBeqOf t2)]
      exact Nat.le_trans (pvD_le (fDiff a b) 1 k hone) (by decide +kernel)
    · rw [if_neg (fun hb => t2 (ground.beqEqOf hb))]
      by_cases t3 : k + 3 = l
      · rw [if_pos (ground.eqBeqOf t3)]
        have hbl3 : b < k + 3 := by rw [t3]; exact hbl
        have hbk : b ≤ k + 2 := Nat.le_of_lt_succ hbl3
        rw [fDiff_hi a b (k + 2) (fun hc =>
            Nat.lt_irrefl (k + 2) (Nat.lt_of_lt_of_le hc hbk)),
          Nat.add_zero]
        exact Nat.add_le_add (pvD_le (fDiff a b) 1 k hone) (hone (k + 1))
      · rw [if_neg (fun hb => t3 (ground.beqEqOf hb))]
        exact Nat.add_le_add (pvD_le (fDiff a b) 1 k hone) (hone (k + 1))

/-- The `D` sum family's last-coordinate column sits within two of
its neighbour fold: its entries stay at or below one, and the fork
key's own read is vacant. -/
private theorem magSumDt (e a k : Nat) :
    2 * fSumDt e a k ≤ nbD (e + 2) (fSumDt e a) k + 2
      ∧ nbD (e + 2) (fSumDt e a) k ≤ 2 * fSumDt e a k + 2 := by
  have hone : ∀ i, fSumDt e a i ≤ 1 := fun i => fSumDt_le1 e a i
  refine ⟨Nat.le_trans (Nat.mul_le_mul_left 2 (hone k))
      (Nat.le_add_left 2 (nbD (e + 2) (fSumDt e a) k)), ?_⟩
  refine Nat.le_trans ?_ (Nat.le_add_left 2 (2 * fSumDt e a k))
  rw [nbD_eq]
  by_cases t1 : k + 1 = e + 2
  · rw [if_pos (ground.eqBeqOf t1)]
    exact Nat.le_trans (pv2D_le (fSumDt e a) 1 k hone) (by decide +kernel)
  · rw [if_neg (fun hb => t1 (ground.beqEqOf hb))]
    by_cases t2 : k + 2 = e + 2
    · rw [if_pos (ground.eqBeqOf t2)]
      exact Nat.le_trans (pvD_le (fSumDt e a) 1 k hone) (by decide +kernel)
    · rw [if_neg (fun hb => t2 (ground.beqEqOf hb))]
      by_cases t3 : k + 3 = e + 2
      · rw [if_pos (ground.eqBeqOf t3)]
        have hke : k + 1 = e := Nat.succ.inj (Nat.succ.inj t3)
        rw [fSumDt_gap e a (k + 1) hke, Nat.add_zero]
        exact Nat.add_le_add (pvD_le (fSumDt e a) 1 k hone) (hone (k + 2))
      · rw [if_neg (fun hb => t3 (ground.beqEqOf hb))]
        exact Nat.add_le_add (pvD_le (fSumDt e a) 1 k hone) (hone (k + 1))

/-- The `D` sum family's generic column sits within two of its
neighbour fold: the window's steps move by one, the two tips read
one, and at the fork the key below sits under the key's double. -/
private theorem magSumD (e a b k : Nat) (hab : a < b) (hbe : b ≤ e)
    (hk : k < e + 2) :
    2 * fSumD e a b k ≤ nbD (e + 2) (fSumD e a b) k + 2
      ∧ nbD (e + 2) (fSumD e a b) k ≤ 2 * fSumD e a b k + 2 := by
  have hcap : ∀ i, fSumD e a b i ≤ 2 := fun i => fSumD_le2 e a b i hbe
  have h0le : fSumD e a b 0 ≤ 1 := by
    by_cases h0a : a ≤ 0
    · rw [fSumD_mid e a b 0 h0a (Nat.lt_of_le_of_lt (Nat.zero_le a) hab)
        hbe]
      exact Nat.le_refl 1
    · rw [fSumD_lo e a b 0 (Nat.lt_of_not_le h0a) hab hbe]
      exact Nat.zero_le 1
  have hstep : ∀ i, i + 1 < e →
      fSumD e a b i ≤ fSumD e a b (i + 1) + 1
        ∧ fSumD e a b (i + 1) ≤ fSumD e a b i + 1 := fun i hi => by
    have hie : i < e := Nat.lt_trans (Nat.lt_succ_self i) hi
    by_cases ha0 : a ≤ i
    · by_cases hb0 : b ≤ i
      · rw [fSumD_two e a b i hb0 hie,
          fSumD_two e a b (i + 1) (Nat.le_succ_of_le hb0) hi]
        exact ⟨by decide +kernel, by decide +kernel⟩
      · rw [fSumD_mid e a b i ha0 (Nat.lt_of_not_le hb0) hbe]
        by_cases hb1 : b ≤ i + 1
        · rw [fSumD_two e a b (i + 1) hb1 hi]
          exact ⟨by decide +kernel, by decide +kernel⟩
        · rw [fSumD_mid e a b (i + 1) (Nat.le_succ_of_le ha0)
            (Nat.lt_of_not_le hb1) hbe]
          exact ⟨by decide +kernel, by decide +kernel⟩
    · rw [fSumD_lo e a b i (Nat.lt_of_not_le ha0) hab hbe]
      by_cases ha1 : a ≤ i + 1
      · have hb1 : ¬ b ≤ i + 1 := fun hc =>
          Nat.lt_irrefl i (Nat.lt_of_lt_of_le (Nat.lt_of_not_le ha0)
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hab hc)))
        rw [fSumD_mid e a b (i + 1) ha1 (Nat.lt_of_not_le hb1) hbe]
        exact ⟨by decide +kernel, by decide +kernel⟩
      · rw [fSumD_lo e a b (i + 1) (Nat.lt_of_not_le ha1) hab hbe]
        exact ⟨by decide +kernel, by decide +kernel⟩
  rw [nbD_eq]
  by_cases t1 : k + 1 = e + 2
  · rw [if_pos (ground.eqBeqOf t1)]
    have hke : k = e + 1 := Nat.succ.inj t1
    rw [show fSumD e a b k = 1 by
      rw [hke]
      exact fSumD_end e a b (e + 1) hbe (Nat.le_succ e)
        (Nat.lt_succ_self (e + 1))]
    exact ⟨Nat.le_add_left 2 _,
      Nat.le_trans (pv2D_le (fSumD e a b) 2 k hcap) (by decide +kernel)⟩
  · rw [if_neg (fun hb => t1 (ground.beqEqOf hb))]
    by_cases t2 : k + 2 = e + 2
    · rw [if_pos (ground.eqBeqOf t2)]
      have hke : k = e := Nat.succ.inj (Nat.succ.inj t2)
      rw [show fSumD e a b k = 1 by
        rw [hke]
        exact fSumD_end e a b e hbe (Nat.le_refl e)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self e) (Nat.le_succ (e + 1)))]
      exact ⟨Nat.le_add_left 2 _,
        Nat.le_trans (pvD_le (fSumD e a b) 2 k hcap) (by decide +kernel)⟩
    · rw [if_neg (fun hb => t2 (ground.beqEqOf hb))]
      by_cases t3 : k + 3 = e + 2
      · rw [if_pos (ground.eqBeqOf t3)]
        have hke : k + 1 = e := Nat.succ.inj (Nat.succ.inj t3)
        have hk2 : k + 2 = e + 1 := congrArg (· + 1) hke
        rw [show fSumD e a b (k + 1) = 1 by
            rw [hke]
            exact fSumD_end e a b e hbe (Nat.le_refl e)
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self e)
                (Nat.le_succ (e + 1))),
          show fSumD e a b (k + 2) = 1 by
            rw [hk2]
            exact fSumD_end e a b (e + 1) hbe (Nat.le_succ e)
              (Nat.lt_succ_self (e + 1))]
        have hpk : pvD (fSumD e a b) k ≤ 2 * fSumD e a b k := by
          match k, hke with
          | 0, _ =>
            rw [pvD_zero]
            exact Nat.zero_le _
          | p + 1, hke =>
            have hpe : p + 1 < e := by
              rw [← hke]
              exact Nat.lt_succ_self (p + 1)
            rw [pvD_succ]
            by_cases hb1 : b ≤ p + 1
            · rw [fSumD_two e a b (p + 1) hb1 hpe]
              exact Nat.le_trans (hcap p) (by decide +kernel)
            · by_cases ha1 : a ≤ p + 1
              · rw [fSumD_mid e a b (p + 1) ha1
                  (Nat.lt_of_not_le hb1) hbe]
                exact Nat.le_trans (hcap p) (by decide +kernel)
              · rw [fSumD_lo e a b p (Nat.lt_trans (Nat.lt_succ_self p)
                  (Nat.lt_of_not_le ha1)) hab hbe]
                exact Nat.zero_le _
        exact ⟨Nat.le_trans (Nat.mul_le_mul_left 2 (hcap k))
            (Nat.le_add_left 4 (pvD (fSumD e a b) k)),
          Nat.add_le_add_right hpk 2⟩
      · rw [if_neg (fun hb => t3 (ground.beqEqOf hb))]
        have hke : k + 1 < e := by
          have hle1 : k ≤ e + 1 := Nat.le_of_lt_succ hk
          have hlt1 : k < e + 1 := Nat.lt_of_le_of_ne hle1
            (fun hx => t1 (congrArg (· + 1) hx))
          have hlt0 : k < e := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt1)
            (fun hx => t2 (congrArg (fun z => z + 2) hx))
          exact Nat.lt_of_le_of_ne hlt0
            (fun hx => t3 (congrArg (fun z => z + 2) hx))
        match k, hke with
        | 0, hke =>
          rw [pvD_zero, Nat.zero_add]
          exact ⟨Nat.le_trans (Nat.mul_le_mul_left 2 h0le)
              (Nat.le_add_left 2 _),
            Nat.le_trans (hcap 1) (Nat.le_add_left 2 _)⟩
        | p + 1, hke =>
          rw [pvD_succ]
          have s1 := hstep p (Nat.lt_trans (Nat.lt_succ_self (p + 1)) hke)
          have s2 := hstep (p + 1) hke
          exact magPairB (fSumD e a b (p + 1)) (fSumD e a b p)
            (fSumD e a b (p + 2)) s1.2 s2.1 s1.1 s2.2

/-- Every `D` family's column sits within two of its neighbour
fold, at every key. -/
theorem colD_magLe (F : Nat → Nat) (k l : Nat) (hk : k < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ e a b, l = e + 2 ∧ a < b ∧ b ≤ e ∧ F = fSumD e a b)
      ∨ (∃ e a, l = e + 2 ∧ a ≤ e ∧ F = fSumDt e a)) :
    2 * F k ≤ nbD l F k + 2 ∧ nbD l F k ≤ 2 * F k + 2 := by
  match hcase with
  | .inl ⟨a, b, _, hbl, hF⟩ =>
    rw [hF]
    exact magDiffD l a b k hbl
  | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
    rw [hF, hle]
    rw [hle] at hk
    exact magSumD e a b k hab hbe hk
  | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
    rw [hF, hle]
    exact magSumDt e a k


/-- A `D` fold read at an occupied rank places the rank beyond
one: the fold list is vacant below the rank two. -/
private theorem oneLtOfFoldD (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsD l) j
      = (List.range l).map F) : 1 < l := by
  match l, hk, hfe with
  | 0, hk, _ => exact absurd hk (Nat.not_lt_zero k)
  | 1, _, hfe =>
    have h0 : (0 : Nat) = 1 := congrArg List.length hfe
    exact Nat.noConfusion h0
  | v + 2, _, _ => exact Nat.succ_lt_succ (Nat.succ_pos v)

/-- The `D` positive list's coroot vectors read their column
values entrywise: the fold's coroot read at a key is the count
pair of the doubled entry against the neighbour fold. -/
theorem posCorootV_entryD (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsD l) j
      = (List.range l).map F) :
    (ground.getAt ground.BPair.unit
      (poly.pnorm (sertables.posCorootV (sertables.tableD l) j))
      k).oneValue
      (ground.BPair.ofCounts (2 * F k) (nbD l F k)) := by
  have h1l : 1 < l := oneLtOfFoldD l j k F hk hfe
  have hkr : k < (sertables.tableD l).rank := hk
  have hf : ground.getAt [] (sertables.tableD l).posFolds j
      = (List.range l).map F := hfe
  rw [nuAtP (sertables.tableD l) j k hkr, hf]
  exact BPair.oneValue_trans (BPair.norm_oneValue _) (colD l h1l F k hk)

/-- A `D` positive fold's balance partner reads the column values'
swap entrywise. -/
theorem negCorootV_entryD (l j k : Nat) (F : Nat → Nat)
    (hk : k < l)
    (hfe : ground.getAt [] (sertables.foldsD l) j
      = (List.range l).map F) :
    (ground.getAt ground.BPair.unit
      (poly.pnorm (poly.neg
        (sertables.posCorootV (sertables.tableD l) j)))
      k).oneValue (ground.BPair.ofCounts (nbD l F k) (2 * F k)) := by
  have h1l : 1 < l := oneLtOfFoldD l j k F hk hfe
  have hkr : k < (sertables.tableD l).rank := hk
  have hf : ground.getAt [] (sertables.tableD l).posFolds j
      = (List.range l).map F := hfe
  rw [nuAtN (sertables.tableD l) j k hkr, hf,
    ← ground.BPair.ofCounts_swap (2 * F k) (nbD l F k)]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (ground.swap_congr (colD l h1l F k hk))

/-- The raised content's entry at the `D` table: the moved
content's own against the letter's Cartan row. -/
private theorem raisedEntryD (l m : Nat) (nu0 : List BPair)
    (hlen : nu0.length = l) (hm1l : m + 1 < l) (y : Nat) (hy : y < l) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableD l).cartan (m + 1)))))
      y).oneValue
      (ground.getAt BPair.unit nu0 y + cartD l (m + 1) y) :=
  raisedEntryG (sertables.tableD l) (fun i j => cartD l i j)
    (cartD_eq l) nu0 hlen (m + 1) hm1l y hy

/-- An interior plus-two column read at a `D` family pins the
narrow window: the doubled entry exceeding the neighbour fold by
two at a chain letter forces the one-key difference window at the
letter, both sum shapes refusing the read outright. -/
theorem narrowOfTwoD (l m : Nat) (F : Nat → Nat) (hml : m + 4 < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ e a b, l = e + 2 ∧ a < b ∧ b ≤ e ∧ F = fSumD e a b)
      ∨ (∃ e a, l = e + 2 ∧ a ≤ e ∧ F = fSumDt e a))
    (hnat : 2 * F (m + 1) = F m + F (m + 2) + 2) :
    F = fDiff (m + 1) (m + 2) := by
  have hm2l : m + 2 < l :=
    Nat.lt_trans (Nat.lt_succ_self (m + 2))
      (Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml)
  match hcase with
  | .inl ⟨a, b, hab, hbl, hF⟩ =>
    have hab2 :=
      (fDiff_two a b m l hab hbl hm2l).mp (by rw [← hF]; exact hnat)
    rw [hF, hab2.1, hab2.2]
  | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
    subst hle
    rw [hF] at hnat
    exact absurd hnat (fSumD_two_refuse e a b m hab hbe
      (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hml)))
  | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
    subst hle
    rw [hF] at hnat
    exact absurd hnat (fSumDt_two_refuse e a m hae
      (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hml)))

/-- At an interior letter every `D` family's column sits above
minus two: all three shapes refuse the read. -/
theorem colD_notNegTwo (l m : Nat) (F : Nat → Nat) (hml : m + 4 < l)
    (hcase : (∃ a b, a < b ∧ b < l ∧ F = fDiff a b)
      ∨ (∃ e a b, l = e + 2 ∧ a < b ∧ b ≤ e ∧ F = fSumD e a b)
      ∨ (∃ e a, l = e + 2 ∧ a ≤ e ∧ F = fSumDt e a))
    (hnat : F m + F (m + 2) = 2 * F (m + 1) + 2) : False := by
  match hcase with
  | .inl ⟨a, b, hab, _, hF⟩ =>
    rw [hF] at hnat
    exact fDiff_negTwo_refuse a b m hab hnat
  | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
    subst hle
    rw [hF] at hnat
    exact fSumD_negTwo_refuse e a b m hab hbe
      (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hml)) hnat
  | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
    subst hle
    rw [hF] at hnat
    exact fSumDt_negTwo_refuse e a m hae
      (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hml)) hnat

/-- The `D` run letters vanish: at a chain letter with the moved
content vacant at the letter's own key and occupied at a witness
off its three keys, the raised content reads the vacant θ count. -/
theorem runVanishD (l m : Nat) (nu0 : List ground.BPair)
    (hml : m + 4 < l) (hlen : nu0.length = l)
    (hv1 : (ground.getAt ground.BPair.unit nu0 (m + 1)).oneValue
      ground.BPair.unit)
    (w : Nat) (hw : w < l) (hwoff : w < m ∨ m + 2 < w)
    (hocc : ¬ (ground.getAt ground.BPair.unit nu0 w).oneValue
      ground.BPair.unit) :
    row.thetaCount (sertables.tableD l)
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (ground.BPair.ofNat 1)
          (ground.getAt [] (sertables.tableD l).cartan (m + 1)))))
      = 0 := by
  have hm3l : m + 3 < l := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
  have hm2l : m + 2 < l := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
  have h1l : 1 < l := Nat.lt_of_le_of_lt
    (Nat.succ_le_succ (Nat.zero_le (m + 3))) hml
  have hmne2 : ¬ m + 2 = l := Nat.ne_of_lt hm2l
  have hmne3 : ¬ m + 3 = l := Nat.ne_of_lt hm3l
  have hmne4 : ¬ m + 4 = l := Nat.ne_of_lt hml
  have hwne : ¬ w = m ∧ ¬ w = m + 1 ∧ ¬ w = m + 2 := by
    match hwoff with
    | .inl h =>
      exact ⟨Nat.ne_of_lt h,
        Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_succ m)),
        Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right m 2))⟩
    | .inr h =>
      exact ⟨fun he => absurd h
          (by rw [he]; exact Nat.not_lt_of_ge (Nat.le_add_right m 2)),
        fun he => absurd h
          (by rw [he]; exact Nat.not_lt_of_ge (Nat.le_succ (m + 1))),
        fun he => absurd h (by rw [he]; exact Nat.lt_irrefl (m + 2))⟩
  have hx1 : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableD l).cartan (m + 1)))))
      (m + 1)).oneValue (BPair.ofNat 2) := by
    refine BPair.oneValue_trans
      (raisedEntryD l m nu0 hlen hm1l (m + 1) hm1l) ?_
    rw [cartDd l (m + 1)]
    exact BPair.oneValue_trans
      (BPair.add_congr hv1 (BPair.oneValue_refl _)) (BPair.unit_add _)
  have hxw : (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd nu0
        (elim.vecScale (BPair.ofNat 1)
          (ground.getAt [] (sertables.tableD l).cartan (m + 1)))))
      w).oneValue (ground.getAt BPair.unit nu0 w) := by
    refine BPair.oneValue_trans (raisedEntryD l m nu0 hlen hm1l w hw) ?_
    rw [cartDoff l (m + 1) w hwne.2.1 (fun he => absurd he hmne2)
      (fun _ _ => hmne4) (fun _ _ he => hwne.1 (Nat.succ.inj he))
      (fun _ _ => hwne.2.2)]
    exact BPair.add_unit _
  refine thetaCountZero (sertables.tableD l) _ ?_ ?_
  · intro he
    have hg : ground.getAt BPair.unit
        (poly.pnorm (elim.vecAdd nu0
          (elim.vecScale (BPair.ofNat 1)
            (ground.getAt [] (sertables.tableD l).cartan (m + 1)))))
        (m + 1) = BPair.unit := by
      rw [he]
      exact ground.getAt_replicate BPair.unit BPair.unit
        (sertables.tableD l).rank (m + 1) hm1l
    rw [hg] at hx1
    exact BPair.ofNat_off_unit 2 (Nat.succ_pos 1) (BPair.oneValue_symm hx1)
  · intro hex
    obtain ⟨j, hj, hor⟩ := hex
    have hjl : j < (sertables.foldsD l).length := Nat.lt_of_succ_lt_succ hj
    obtain ⟨F, hfe, hcase⟩ := foldsD_cases l j hjl
    match hor with
    | .inl he =>
      rw [he] at hx1 hxw
      have hnat : 2 * F (m + 1) = nbD l F (m + 1) + 2 :=
        countsTwo (BPair.oneValue_trans
          (BPair.oneValue_symm
            (posCorootV_entryD l j (m + 1) F hm1l hfe)) hx1)
      rw [nbD_eq, if_neg (fun hb => hmne2 (ground.beqEqOf hb)),
        if_neg (fun hb => hmne3 (ground.beqEqOf hb)),
        if_neg (fun hb => hmne4 (ground.beqEqOf hb)),
        pvD_succ] at hnat
      have hFn : F = fDiff (m + 1) (m + 2) :=
        narrowOfTwoD l m F hml hcase hnat
      refine hocc (BPair.oneValue_trans (BPair.oneValue_symm hxw)
        (BPair.oneValue_trans (posCorootV_entryD l j w F hw hfe)
          (BPair.ofCounts_unit.mpr ?_)))
      rw [hFn]
      exact fDiffD_narrow_off m l w hml hw hwne.1 hwne.2.1 hwne.2.2
    | .inr he =>
      rw [he] at hx1 hxw
      have hnat : nbD l F (m + 1) = 2 * F (m + 1) + 2 :=
        countsTwo (BPair.oneValue_trans
          (BPair.oneValue_symm
            (negCorootV_entryD l j (m + 1) F hm1l hfe)) hx1)
      rw [nbD_eq, if_neg (fun hb => hmne2 (ground.beqEqOf hb)),
        if_neg (fun hb => hmne3 (ground.beqEqOf hb)),
        if_neg (fun hb => hmne4 (ground.beqEqOf hb)),
        pvD_succ] at hnat
      exact colD_notNegTwo l m F hml hcase hnat


end serstable
