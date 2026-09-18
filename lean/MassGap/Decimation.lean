import MassGap.Deckfactor
import MassGap.Greenprod
import MassGap.Certconstruct
import MassGap.Cellcount
import MassGap.Spectator
import MassGap.Depthchain
/-!
`thm:decimation`(i) — the depth direction is the walk's shape.  The
fiber's sector is its fusion closure from the vacuum class, the
depth chain of `con:depthchain`, block tridiagonal over the depth
with the vacuum class the boundary shell
(`depthchain.depth_assemble`), and the count at every level splits
over the chain's pivot recursion, `rev(S) = Σ_κ rev(X_κ)`: at a
depth order listing every position once the datum's split reads the
chain's own count, the pivots' fold (`chain_count` at
`inertia.rev_perm`, the places' permutation, and
`greenprod.countSplit`, the tail recursion's certificate).  The
split is order-free, every split of the assembled datum reading the
one count (`inertia.rev_exchange`), a slab ordering certificate
data.  The ground jump is a divisor point of the decimated head: a
jump of the counting function enters at balance-pair levels as two
counts at a gap over the ordered level pair (`jumpPairAt` at
`certconstruct.countAtPair`), the level is the first two jumps'
distance with the stated level pair within the brackets' gap at
cross-added comparisons (`levelDistRead`), and the boundary defect
is the vacuum's magnetic diagonal, `prop:row`'s Kronecker delta at
two labels, `fusion.unitLaw`'s own instance at the pair `(θ, 𝟏)`,
the batteries' read at the walk's boundary.
The tower tails' clause (`thm:decimation`(ii)) reads at the
dominance comparison: per row the gap is the diagonal's entry joined
to the balance partner of the off-row entries' magnitude fold
(`gapRow` at `offFold`, `windowsep.mag` the carrier, `gapOf` the
gap list), the comparison every gap at its upper side or equal
members (`domAt`, `domAt_rows` and `domAt_of_rows` its two reads at
the rows), the form prices at or beyond the gaps' fold of squares at
every symmetric datum by the peel telescoping (`dom_form`, the cross
terms joined to their magnitudes' squares at one square's multiple
per entry side) and at or beyond the sum's unit where the comparison
holds (`dom_unit`), every split of a dominance-clear datum reads the
upper side throughout (`dom_psd` at `inertia.rev_witness`), at every
gap beyond the sum's unit (`gapPos`) the kernel block is vacant
besides, a kernel column's image off the unit family pricing the
form at the sum's unit against the gaps' strict floor (`dom_pd` at
`inertia.kern_witness`), and at a chain's
tail the count telescopes over the pivot recursion with the tail's
summands at the sum's unit (`dom_count` at `greenprod.countSplit`
over the dropped tail sub-chain, `tailRead_drop`).
The decimated symbol: a dropped block positive definite at its
stated split is a nonsingular principal pivot at its designated
places, and the datum's count is its deflation's onto the head, the
adjugate against the block the deflation's solve (`head_count` at
`inertia.rev_places`, the block's determinant off equal members by
`inertia.minor_of_kern` and the solve `inertia.adjM_solve`), the
tower block its instance at clause (ii); clause (iii)'s far block
reads its count at the ball's pivots' fold (`ball_count`).
The slabs decimate at the deck pivot (`thm:decimation`(iii)): the
bulk data are constant beyond a stated depth, the deck pivot the
ball certificate's located center at the pivot identities with the
tail pivots riding the ball (`bulkRead` at `spectator.ballRead`
over `spectator.ballList`, the validity data the deck symbol's
band read at its cleared-variable monic and the ball's own, the
bulk block's data alone), the decimated symbol's count on the
bracket is the head's (`ball_count` at `spectator.ball_psd` over
the dropped pivots, every ball member's count at the sum's unit),
and two slab families at the stated equal-data reads have pivot
differences within the iterated cap brackets (`windowShareRead` at
`spectator.capWalk` down the tail witnesses from the perturbation
slab to the observable's depth, the head pivots shared below the
slab). At `lem:relfiber`(iv), `relfiber.tensorSum_count` and
`relfiber.pairRoots_least` read the full tensor product. Its
total-content selection is a compression; every coupling to the
further places enters the actual deflation and its count identity.
The count at a stated order is the general read beneath the depth
chain's: at a distinct key list covering the order whose selection
reads one value with an assembled slab chain, the datum's split and
the chain's read one count at the places' permutation (`order_perm`)
and the datum's count is the pivots' fold (`order_count`),
`chain_count` its instance at the depth order.  The decimated symbol
composes the three clauses: the tower block at its designated places
reads the dominance comparison at occupied gaps, so the datum's count
is its deflation's onto the further places (`towerDefl` at
`head_count`, the positive-definite read `dom_pd`'s), the deflated
datum at a stated shell order is a slab chain whose first shell is
the head, and at the far pivots inside the deck pivot's ball the
chain's count is the head pivot's (`decimated_count` at `order_perm`
and `ball_count`), the head pivot the recursion's Schur complement
onto the head, the decimated head at the head's order.
The divisor list's emitted record is the displayed object at its
committed store (`DivRecord` at `Bound`, `recordRead` at
`boundRead`): one cell per sample with its count
(`cellcount.countAt`), the divisor's squarefree witness
(`cellcount.divRead` at `split.pminor`), and per boundary the
binding read of which comparison binds — a jump boundary straddling
one root of the divisor's cleared monic between its flanking
samples, a comparison boundary one root of its stated display with
the divisor's count at the sum's unit across — every straddle
`lem:hermitesign`'s
segment count at the cleared variable (`deckfactor.clearVarBT` at
`deckfactor.clearAt`), the record's shape at the stated cell and
boundary counts.
-/

namespace decimation
open ground elim inertia greenprod certconstruct

/-- A jump of the counting function at balance-pair levels: the two
counts at a gap of at least one over the ordered level pair, each
count `rev(H + yG : xG)` at its split. -/
def jumpPairAt {o : Nat} (H G : Mat) (x1 y1 x2 y2 : Pos) (n g : Nat)
    (sp1 sp2 : Split o) : Prop :=
  countAtPair H G x1 y1 n sp1
  ∧ countAtPair H G x2 y2 (n + g) sp2
  ∧ x1 + y2 < x2 + y1
  ∧ 1 ≤ g

instance instDecimation2 {o : Nat} (H G : Mat) (x1 y1 x2 y2 : Pos) (n g : Nat)
    (sp1 sp2 : Split o) :
    Decidable (jumpPairAt H G x1 y1 x2 y2 n g sp1 sp2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The level as the first two jumps' distance: the ground jump's
bracket from the count's unit, the second jump's bracket at or
beyond it, and the stated level pair within the brackets' gap, the
cross-added comparisons at the ordering and at both ends. -/
def levelDistRead {o : Nat} (H G : Mat)
    (l1x l1y h1x h1y l2x l2y h2x h2y kx ky : Pos) (g1 g2 : Nat)
    (spl1 sph1 spl2 sph2 : Split o) : Prop :=
  jumpPairAt H G l1x l1y h1x h1y 0 g1 spl1 sph1
  ∧ jumpPairAt H G l2x l2y h2x h2y g1 g2 spl2 sph2
  ∧ h1x + l2y ≤ l2x + h1y
  ∧ l2x + h1y + ky ≤ kx + l2y + h1x
  ∧ kx + l1x + h2y ≤ h2x + ky + l1y

instance instDecimation3 {o : Nat} (H G : Mat)
    (l1x l1y h1x h1y l2x l2y h2x h2y kx ky : Pos) (g1 g2 : Nat)
    (spl1 sph1 spl2 sph2 : Split o) :
    Decidable (levelDistRead H G l1x l1y h1x h1y l2x l2y h2x h2y
      kx ky g1 g2 spl1 sph1 spl2 sph2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! Clause (ii)'s dominance tier: the comparison at the rows'
magnitude folds, the quadratic form priced at or beyond the gaps'
fold of squares, and the count telescope over the pivot recursion. -/

/-- The magnitude fold over a list, `thm:windowsep`'s carrier at
the family fold. -/
def magSum : List BPair → BPair :=
  ground.famFold BPair.add BPair.unit windowsep.mag

/-- The off-row fold: the row's magnitude fold at the stated key
withdrawn, the walk counting the key down (`ground.offFoldO` at the
balance-pair bundle). -/
def offFold : Nat → List BPair → BPair :=
  ground.offFoldO ground.bpairOps windowsep.mag

/-- A row's gap: the diagonal's entry joined to the balance partner
of the off-row entries' magnitude fold, at its upper side or equal
members exactly where the comparison `f_i ≤ a_ii` holds
(`thm:decimation`(ii)). -/
def gapRow (i : Nat) (r : List BPair) : BPair :=
  ground.getAt BPair.unit r i + (offFold i r).swap

/-- The gap list, one gap per row, the key stepping with the rows. -/
def gapOf : Nat → Mat → List BPair
  | _, [] => []
  | i, r :: rest => gapRow i r :: gapOf (i + 1) rest

/-- The dominance comparison (`thm:decimation`(ii)): every row's gap
at its upper side or equal members. -/
def domAt (S : Mat) : Prop :=
  ((gapOf 0 S).all (fun g => decide (BPair.unit ≤ g))) = true

instance instDecimation4 (S : Mat) : Decidable (domAt S) :=
  inferInstanceAs (Decidable (_ = _))

/-- The comparison at occupied gaps: every row's gap beyond the
sum's unit. -/
def gapPos (S : Mat) : Prop :=
  ((gapOf 0 S).all (fun g => decide (BPair.unit < g))) = true

instance instDecimation1 (S : Mat) : Decidable (gapPos S) :=
  inferInstanceAs (Decidable (_ = _))

/-- The gap list's count is the rows'. -/
private theorem length_gapOf : ∀ (k : Nat) (S : Mat),
    (gapOf k S).length = S.length
  | _, [] => rfl
  | k, _ :: rest => by
    show (gapOf (k + 1) rest).length + 1 = rest.length + 1
    rw [length_gapOf (k + 1) rest]

/-- The gap list's entry is the row's gap at the walked key. -/
private theorem getAt_gapOf : ∀ (k : Nat) (S : Mat) (i : Nat), i < S.length →
    ground.getAt BPair.unit (gapOf k S) i = gapRow (k + i) (ground.getAt [] S i)
  | _, [], i, hi => absurd hi (Nat.not_lt_zero i)
  | _, _ :: _, 0, _ => rfl
  | k, _ :: rest, i + 1, hi => by
    have e : k + (i + 1) = k + 1 + i :=
      (congrArg (k + ·) (Nat.add_comm i 1)).trans (Nat.add_assoc k 1 i).symm
    rw [e]
    exact getAt_gapOf (k + 1) rest i (Nat.lt_of_succ_lt_succ hi)

/-- The row's fold joined to its gap reads the diagonal's entry. -/
theorem gapRow_read (i : Nat) (r : List BPair) :
    (offFold i r + gapRow i r).oneValue (ground.getAt BPair.unit r i) := by
  show (offFold i r + (ground.getAt BPair.unit r i + (offFold i r).swap)).oneValue _
  rw [BPair.add_comm (offFold i r), BPair.add_assoc, BPair.add_comm (offFold i r).swap]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_swap_null (offFold i r)))
    (BPair.add_unit _)

/-- A comparison reads its gap at its upper side or equal members,
the gap the cross-added read's own witness. -/
private theorem gap_of_le {x y : BPair} (h : x ≤ y) : BPair.unit ≤ y + x.swap :=
  ground.leB_congr_left (BPair.add_swap_null x)
    (ground.leB_add h (ground.leB_refl x.swap))

/-- A gap at its upper side or equal members reads its comparison. -/
private theorem le_of_gap {x y : BPair} (h : BPair.unit ≤ y + x.swap) : x ≤ y := by
  have h1 := ground.leB_add (ground.leB_refl x) h
  refine ground.leB_congr_right ?_ (ground.leB_congr_left (BPair.add_unit x) h1)
  rw [BPair.add_comm y, ← BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_swap_null x) (BPair.oneValue_refl y))
    (BPair.unit_add y)

/-- The comparison read row by row off the dominance fold. -/
theorem domAt_rows {n : Nat} (S : Mat) (hS : S.length = n) (h : domAt S) :
    ∀ i, i < n → offFold i (ground.getAt [] S i)
      ≤ ground.getAt BPair.unit (ground.getAt [] S i) i := by
  intro i hi
  have hi' : i < (gapOf 0 S).length := by rw [length_gapOf, hS]; exact hi
  have hg := ground.all_getAt BPair.unit (gapOf 0 S) h i hi'
  rw [getAt_gapOf 0 S i (by rw [hS]; exact hi), Nat.zero_add] at hg
  exact le_of_gap (of_decide_eq_true hg)

/-- The dominance fold from the rows' comparisons. -/
theorem domAt_of_rows {n : Nat} (S : Mat) (hS : S.length = n)
    (h : ∀ i, i < n → offFold i (ground.getAt [] S i)
      ≤ ground.getAt BPair.unit (ground.getAt [] S i) i) : domAt S := by
  refine ground.all_of_getAt BPair.unit _ (gapOf 0 S) (fun k hk => ?_)
  rw [length_gapOf] at hk
  rw [getAt_gapOf 0 S k hk, Nat.zero_add]
  exact decide_eq_true (gap_of_le (h k (by rw [← hS]; exact hk)))

/-- The entry's pricing device: the doubled cross term joined to
the magnitude's two squares sits at or above the sum's unit, the
weighted squares' pricing at the entry's side
(`ground.leB_crossSq`). -/
private theorem magDevice (c x y : BPair) :
    BPair.unit ≤ (x * (c * y) + x * (c * y))
      + (windowsep.mag c * (x * x) + windowsep.mag c * (y * y)) := by
  have hu := windowsep.unitLe_mag c
  refine ground.leB_congr_right (BPair.oneValue_symm
    (show ((x * (c * y) + x * (c * y))
        + (windowsep.mag c * (x * x) + windowsep.mag c * (y * y))).oneValue
      (windowsep.mag c * (x * x + y * y) + c * (x * y + x * y)) from
    polEqB [x, c, y, windowsep.mag c]
      (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))))) (Pol.add (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))))))
      (Pol.add (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 2))))))
      (by decide +kernel))) ?_
  cases hz : decide (c < c.swap) with
  | true =>
    have hm : windowsep.mag c = c.swap := by
      show (if c < c.swap then c.swap else c) = c.swap
      rw [if_pos (of_decide_eq_true hz)]
    rw [hm] at hu ⊢
    have hsw : (c * (x * y + x * y)).swap
        = c.swap * (x * y + x * y) := by
      rw [BPair.mul_comm c (x * y + x * y),
        ← BPair.mul_swap (x * y + x * y) c,
        BPair.mul_comm (x * y + x * y) c.swap]
    exact ground.leB_unit_add
      (by rw [hsw]; exact ground.leB_crossSq hu x y)
  | false =>
    have hn : ¬ (c < c.swap) := fun hlt =>
      Bool.noConfusion ((decide_eq_true hlt).symm.trans hz)
    have hm : windowsep.mag c = c := by
      show (if c < c.swap then c.swap else c) = c
      rw [if_neg hn]
    rw [hm] at hu ⊢
    exact ground.leB_unit_add (ground.leB_crossSqSwap hu x y)

/-- The row's cross pricing: the doubled cross fold joined to the
magnitude fold's square and the magnitudes' fold against the
squares sits at or above the sum's unit, one device per entry. -/
private theorem crossPrice : ∀ (b vs : List BPair) (x : BPair),
    BPair.unit ≤ (x * dotP b vs + x * dotP b vs)
      + (magSum b * (x * x)
        + dotP (b.map windowsep.mag) (List.zipWith (· * ·) vs vs))
  | [], vs, x => by
    show BPair.unit ≤ (x * BPair.unit + x * BPair.unit)
      + (BPair.unit * (x * x) + BPair.unit)
    refine ground.leB_congr_right (BPair.oneValue_symm ?_)
      (ground.leB_refl BPair.unit)
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_unit x) (BPair.mul_unit x))
        (BPair.unit_add BPair.unit))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.unit_mul (x * x))
          (BPair.oneValue_refl BPair.unit))
        (BPair.unit_add BPair.unit))) ?_
    exact BPair.unit_add BPair.unit
  | b0 :: bt, [], x => by
    show BPair.unit ≤ (x * BPair.unit + x * BPair.unit)
      + ((windowsep.mag b0 + magSum bt) * (x * x) + BPair.unit)
    refine ground.unitLeAdd ?_ ?_
    · exact ground.leB_congr_right
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.add_congr (BPair.mul_unit x) (BPair.mul_unit x))
          (BPair.unit_add BPair.unit)))
        (ground.leB_refl BPair.unit)
    · exact ground.unitLeAdd
        (ground.unitLeMul
          (ground.foldB_nonneg windowsep.mag (b0 :: bt)
            (fun z _ => windowsep.unitLe_mag z))
          (ground.unitLeSq x))
        (ground.leB_refl BPair.unit)
  | b0 :: bt, y :: vst, x => by
    show BPair.unit ≤ (x * (b0 * y + dotP bt vst)
        + x * (b0 * y + dotP bt vst))
      + ((windowsep.mag b0 + magSum bt) * (x * x)
        + (windowsep.mag b0 * (y * y)
          + dotP (bt.map windowsep.mag) (List.zipWith (· * ·) vst vst)))
    refine ground.leB_congr_right (BPair.oneValue_symm
      (polEqB [x, b0, y, dotP bt vst, windowsep.mag b0, magSum bt,
        dotP (bt.map windowsep.mag) (List.zipWith (· * ·) vst vst)]
        (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3)))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 5))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.add (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2)))) (Pol.mon (Mon.var 6)))))
        (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))))) (Pol.add (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2)))))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3)))) (Pol.add (Pol.mul (Pol.mon (Mon.var 5)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mon (Mon.var 6)))))
        (by decide +kernel))) ?_
    exact ground.unitLeAdd (magDevice b0 x y) (crossPrice bt vst x)

/-- A row's fold against a headed vector splits at the row's own
leading entry. -/
private theorem rowHead : ∀ (row : List BPair) (x : BPair)
    (vs : List BPair),
    (dotP row (x :: vs)).oneValue
      (x * ground.getAt BPair.unit row 0 + dotP (row.drop 1) vs)
  | [], x, _ => by
    show BPair.oneValue BPair.unit (x * BPair.unit + BPair.unit)
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit x)
        (BPair.oneValue_refl BPair.unit)) ?_)
    exact BPair.unit_add BPair.unit
  | c :: t, x, vs =>
    BPair.add_congr (BPair.oneValue_of_eq (BPair.mul_comm c x))
      (BPair.oneValue_refl (dotP t vs))

/-- The trailing rows' folds against a headed vector split into the
leading column's scale and the residual datum's own folds. -/
private theorem rowPeel : ∀ (rest : Mat) (x : BPair)
    (vs : List BPair),
    poly.oneValue (rest.map (fun row => dotP row (x :: vs)))
      (vecAdd (vecScale x (elim.colHead BPair.unit rest))
        ((elim.dropCol rest).map (fun row => dotP row vs)))
  | [], _, _ => trivial
  | row :: t, x, vs => ⟨rowHead row x vs, rowPeel t x vs⟩

/-- The peel's read: the trailing block's fold against a headed
vector is the leading column's scaled pairing joined to the
residual datum's own form. -/
private theorem peelRead (rest : Mat) (x : BPair) (vs : List BPair) :
    (dotP vs (rest.map (fun row => dotP row (x :: vs)))).oneValue
      (x * dotP vs (elim.colHead BPair.unit rest)
        + dotP vs
            ((elim.dropCol rest).map (fun row => dotP row vs))) := by
  have hl1 : (vecScale x (elim.colHead BPair.unit rest)).length
      = rest.length :=
    (length_vecScale x (elim.colHead BPair.unit rest)).trans
      (elim.length_colHead BPair.unit rest)
  have hl2 : ((elim.dropCol rest).map (fun row => dotP row vs)).length
      = rest.length :=
    (ground.length_map _ (elim.dropCol rest)).trans
      (elim.length_dropCol rest)
  refine BPair.oneValue_trans
    (dotP_oneValue_right vs _ _ (rowPeel rest x vs)) ?_
  refine BPair.oneValue_trans
    (dotP_vecAdd_right vs _ _ (hl1.trans hl2.symm)) ?_
  exact BPair.add_congr
    (dotP_vecScale_right vs (elim.colHead BPair.unit rest) x)
    (BPair.oneValue_refl _)

/-- The off-row fold at a shifted key splits off the row's leading
entry's magnitude. -/
private theorem offFold_drop : ∀ (j : Nat) (r : List BPair),
    0 < r.length →
    offFold (j + 1) r
      = windowsep.mag (ground.getAt BPair.unit r 0) + offFold j (r.drop 1)
  | _, [], h => absurd h (Nat.lt_irrefl 0)
  | _, _ :: _, _ => rfl

/-- The peel's regrouping: the five summands' exchange at the
collected device. -/
private theorem addShuffle (a b c m nn : BPair) :
    ((a + b) + (c + (m + nn))).oneValue ((m + a) + (c + (b + nn))) :=
  polEqB [a, b, c, m, nn]
    (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 4)))))
    (Pol.add (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 4)))))
    (by decide +kernel)

/-- The peel's induction at the plain fold: the slack's fold
against the squares sits at or below the form, the comparison
descending one row at a time with the leading column's magnitudes
joining the residual datum's slack. -/
private theorem dom_quadGo : ∀ (n : Nat) (S : Mat) (d v : List BPair),
    S.length = n → rowsLen n S → d.length = n → v.length = n →
    (∀ i j, i < n → j < n →
      (ground.getAt BPair.unit (ground.getAt [] S i) j).oneValue
        (ground.getAt BPair.unit (ground.getAt [] S j) i)) →
    (∀ i, i < n →
      offFold i (ground.getAt [] S i) + ground.getAt BPair.unit d i
        ≤ ground.getAt BPair.unit (ground.getAt [] S i) i) →
    dotP d (List.zipWith (· * ·) v v)
      ≤ dotP v (S.map (fun r => dotP r v)) := by
  intro n
  induction n with
  | zero =>
    intro _ d v _ _ hd hv _ _
    cases d with
    | cons _ _ => exact Nat.noConfusion hd
    | nil =>
      cases v with
      | cons _ _ => exact Nat.noConfusion hv
      | nil => exact ground.leB_refl _
  | succ n ih =>
    intro S d v hSl hSr hd hv hsymE hdom
    cases S with
    | nil => exact Nat.noConfusion hSl
    | cons r rest =>
      cases r with
      | nil => exact Nat.noConfusion hSr.1
      | cons a b =>
        cases d with
        | nil => exact Nat.noConfusion hd
        | cons d0 dt =>
          cases v with
          | nil => exact Nat.noConfusion hv
          | cons x vs =>
            have hrl : b.length = n := Nat.succ.inj hSr.1
            have hrestl : rest.length = n := Nat.succ.inj hSl
            have hdtl : dt.length = n := Nat.succ.inj hd
            have hvsl : vs.length = n := Nat.succ.inj hv
            have hcl : (elim.colHead BPair.unit rest).length = n :=
              (elim.length_colHead BPair.unit rest).trans hrestl
            have hcol : ∀ j, j < n →
                (ground.getAt BPair.unit
                    (elim.colHead BPair.unit rest) j).oneValue
                  (ground.getAt BPair.unit b j) := by
              intro j hj
              rw [show ground.getAt BPair.unit
                    (elim.colHead BPair.unit rest) j
                  = ground.getAt BPair.unit (ground.getAt [] rest j) 0
                  from elim.getAt_colHead BPair.unit rest j
                    (by rw [hrestl]; exact hj)]
              exact hsymE (j + 1) 0 (Nat.succ_lt_succ hj) (Nat.succ_pos n)
            have hcolPoly :
                poly.oneValue (elim.colHead BPair.unit rest) b :=
              poly.oneValue_of_entries _ _ (hcl.trans hrl.symm)
                (fun j hj => hcol j (by rw [hcl] at hj; exact hj))
            have hmagPoly : poly.oneValue
                ((elim.colHead BPair.unit rest).map windowsep.mag)
                (b.map windowsep.mag) := by
              refine poly.oneValue_of_entries _ _ ?_ ?_
              · rw [ground.length_map, ground.length_map, hcl, hrl]
              · intro j hj
                rw [ground.length_map, hcl] at hj
                rw [ground.getAt_map BPair.unit BPair.unit windowsep.mag
                    (elim.colHead BPair.unit rest) j
                    (by rw [hcl]; exact hj),
                  ground.getAt_map BPair.unit BPair.unit windowsep.mag
                    b j (by rw [hrl]; exact hj)]
                exact windowsep.mag_congr (hcol j hj)
            have hsymD : ∀ i j, i < n → j < n →
                (ground.getAt BPair.unit
                    (ground.getAt [] (elim.dropCol rest) i) j).oneValue
                  (ground.getAt BPair.unit
                    (ground.getAt [] (elim.dropCol rest) j) i) := by
              intro i j hi hj
              rw [elim.getAt_dropCol rest i (by rw [hrestl]; exact hi),
                elim.getAt_dropCol rest j (by rw [hrestl]; exact hj),
                elim.getAt_drop1 BPair.unit (ground.getAt [] rest i) j,
                elim.getAt_drop1 BPair.unit (ground.getAt [] rest j) i]
              exact hsymE (i + 1) (j + 1) (Nat.succ_lt_succ hi)
                (Nat.succ_lt_succ hj)
            have hdomD : ∀ j, j < n →
                offFold j (ground.getAt [] (elim.dropCol rest) j)
                    + ground.getAt BPair.unit
                        (vecAdd dt
                          ((elim.colHead BPair.unit rest).map
                            windowsep.mag)) j
                  ≤ ground.getAt BPair.unit
                      (ground.getAt [] (elim.dropCol rest) j) j := by
              intro j hj
              have hrow : 0
                  < (ground.getAt ([] : List BPair) rest j).length := by
                rw [rowsLen_getAt rest j hSr.2 (by rw [hrestl]; exact hj)]
                exact Nat.succ_pos n
              have hj1 : offFold (j + 1) (ground.getAt [] rest j)
                    + ground.getAt BPair.unit dt j
                  ≤ ground.getAt BPair.unit
                      (ground.getAt [] rest j) (j + 1) :=
                hdom (j + 1) (Nat.succ_lt_succ hj)
              rw [offFold_drop j (ground.getAt [] rest j) hrow] at hj1
              rw [elim.getAt_dropCol rest j (by rw [hrestl]; exact hj),
                elim.getAt_vecAdd dt
                  ((elim.colHead BPair.unit rest).map windowsep.mag)
                  j (by rw [hdtl]; exact hj)
                  (by rw [ground.length_map, hcl]; exact hj),
                ground.getAt_map BPair.unit BPair.unit windowsep.mag
                  (elim.colHead BPair.unit rest) j
                  (by rw [hcl]; exact hj),
                show ground.getAt BPair.unit
                    (elim.colHead BPair.unit rest) j
                  = ground.getAt BPair.unit (ground.getAt [] rest j) 0
                  from elim.getAt_colHead BPair.unit rest j
                    (by rw [hrestl]; exact hj),
                elim.getAt_drop1 BPair.unit (ground.getAt [] rest j) j]
              refine ground.leB_congr_left (BPair.oneValue_of_eq ?_) hj1
              rw [BPair.add_comm
                  (windowsep.mag (ground.getAt BPair.unit
                    (ground.getAt [] rest j) 0))
                  (offFold j ((ground.getAt [] rest j).drop 1)),
                BPair.add_assoc
                  (offFold j ((ground.getAt [] rest j).drop 1))
                  (windowsep.mag (ground.getAt BPair.unit
                    (ground.getAt [] rest j) 0))
                  (ground.getAt BPair.unit dt j),
                BPair.add_comm
                  (windowsep.mag (ground.getAt BPair.unit
                    (ground.getAt [] rest j) 0))
                  (ground.getAt BPair.unit dt j)]
            have hIH := ih (elim.dropCol rest)
              (vecAdd dt
                ((elim.colHead BPair.unit rest).map windowsep.mag))
              vs ((elim.length_dropCol rest).trans hrestl)
              (elim.rowsLen_dropCol n rest hSr.2)
              (elim.length_vecAdd dt _ n hdtl
                ((ground.length_map _ _).trans hcl)) hvsl
              hsymD hdomD
            have hIH2 : dotP dt (List.zipWith (· * ·) vs vs)
                  + dotP (b.map windowsep.mag)
                      (List.zipWith (· * ·) vs vs)
                ≤ dotP vs
                    ((elim.dropCol rest).map
                      (fun row => dotP row vs)) := by
              refine ground.leB_congr_left ?_ hIH
              refine BPair.oneValue_trans
                (elim.dotP_vecAdd_left dt
                  ((elim.colHead BPair.unit rest).map windowsep.mag)
                  (List.zipWith (· * ·) vs vs)
                  (by rw [ground.length_zipWith (· * ·) vs vs n hvsl hvsl,
                      hdtl]; exact Nat.le_refl n)
                  (by rw [ground.length_zipWith (· * ·) vs vs n hvsl hvsl,
                      ground.length_map, hcl]; exact Nat.le_refl n)) ?_
              exact BPair.add_congr (BPair.oneValue_refl _)
                (dotP_oneValue_left _ _ _ hmagPoly)
            have hdom0 : magSum b + d0 ≤ a := hdom 0 (Nat.succ_pos n)
            have hA : magSum b * (x * x) + d0 * (x * x)
                ≤ a * (x * x) := by
              refine ground.leB_congr ?_ ?_
                (ground.leB_mulR (ground.unitLeSq x) hdom0)
              · exact BPair.oneValue_of_eq
                  ((BPair.mul_comm (x * x) (magSum b + d0)).trans
                    (BPair.right_distrib (magSum b) d0 (x * x)))
              · exact BPair.oneValue_of_eq (BPair.mul_comm (x * x) a)
            have hRHS : (dotP (x :: vs)
                  (((a :: b) :: rest).map
                    (fun row => dotP row (x :: vs)))).oneValue
                (a * (x * x)
                  + ((x * dotP b vs + x * dotP b vs)
                    + dotP vs ((elim.dropCol rest).map
                        (fun row => dotP row vs)))) := by
              show (x * (a * x + dotP b vs)
                + dotP vs (rest.map
                    (fun row => dotP row (x :: vs)))).oneValue _
              refine BPair.oneValue_trans (BPair.add_congr
                (BPair.oneValue_of_eq
                  (BPair.left_distrib x (a * x) (dotP b vs)))
                (BPair.oneValue_trans (peelRead rest x vs)
                  (BPair.add_congr
                    (BPair.mul_congr (BPair.oneValue_refl x)
                      (BPair.oneValue_trans
                        (dotP_oneValue_right vs _ _ hcolPoly)
                        (BPair.oneValue_of_eq (dotP_comm vs b))))
                    (BPair.oneValue_refl _)))) ?_
              refine BPair.oneValue_trans (BPair.add_congr
                (BPair.add_congr
                  (BPair.oneValue_of_eq (BPair.mul_left_comm x a x))
                  (BPair.oneValue_refl _))
                (BPair.oneValue_refl _)) ?_
              refine BPair.oneValue_of_eq ?_
              rw [BPair.add_assoc (a * (x * x)) (x * dotP b vs)
                  (x * dotP b vs
                    + dotP vs ((elim.dropCol rest).map
                        (fun row => dotP row vs))),
                ← BPair.add_assoc (x * dotP b vs) (x * dotP b vs)
                  (dotP vs ((elim.dropCol rest).map
                    (fun row => dotP row vs)))]
            have h1 : d0 * (x * x) + dotP dt (List.zipWith (· * ·) vs vs)
                ≤ (d0 * (x * x) + dotP dt (List.zipWith (· * ·) vs vs))
                  + ((x * dotP b vs + x * dotP b vs)
                    + (magSum b * (x * x)
                      + dotP (b.map windowsep.mag)
                          (List.zipWith (· * ·) vs vs))) :=
              ground.leB_congr_left (BPair.add_unit _)
                (ground.leB_add (ground.leB_refl _) (crossPrice b vs x))
            refine ground.leB_congr_right (BPair.oneValue_symm hRHS) ?_
            exact ground.leB_trans (ground.leB_congr_right
              (addShuffle (d0 * (x * x))
                (dotP dt (List.zipWith (· * ·) vs vs))
                (x * dotP b vs + x * dotP b vs) (magSum b * (x * x))
                (dotP (b.map windowsep.mag)
                  (List.zipWith (· * ·) vs vs))) h1)
              (ground.leB_add hA (ground.leB_add (ground.leB_refl _) hIH2))

/-- A slack list at the comparison prices the quadratic form: the
slack's fold against the coordinates' squares sits at or below the
form, the peel telescoping on the comparison. -/
private theorem quad_gaps (S : Mat) (n : Nat) (d : List BPair)
    (hsq : sqAt S n) (hd : d.length = n)
    (hsym : matOneValue S (transposeM S))
    (hdom : ∀ i, i < n →
      offFold i (ground.getAt [] S i) + ground.getAt BPair.unit d i
        ≤ ground.getAt BPair.unit (ground.getAt [] S i) i)
    (v : List BPair) (hv : v.length = n) :
    dotN d (List.zipWith (· * ·) v v) ≤ dotN v (matVec S v) := by
  have hSl : S.length = n := sqAt_len hsq
  have hSr : rowsLen n S := rowsLen_of_sqAt hsq
  have hsymE : ∀ i j, i < n → j < n →
      (ground.getAt BPair.unit (ground.getAt [] S i) j).oneValue
        (ground.getAt BPair.unit (ground.getAt [] S j) i) :=
    fun i j hi hj => symmRead_entry S hsq hsym i j hi hj
  refine ground.leB_congr (BPair.oneValue_symm (dotN_read d _))
    (BPair.oneValue_symm (quadP_read S v)) ?_
  exact dom_quadGo n S d v hSl hSr hd hv hsymE hdom

/-- A gap list at or above the sum's unit against the coordinates'
squares folds at or above the unit. -/
private theorem dotP_sq_nonneg : ∀ (d u : List BPair),
    (∀ i, i < d.length → BPair.unit ≤ ground.getAt BPair.unit d i) →
    BPair.unit ≤ dotP d (List.zipWith (· * ·) u u)
  | [], _, _ => ground.leB_refl BPair.unit
  | _ :: _, [], _ => ground.leB_refl BPair.unit
  | d0 :: dt, u0 :: ut, h => by
    show BPair.unit ≤ d0 * (u0 * u0) + dotP dt (List.zipWith (· * ·) ut ut)
    exact ground.unitLeAdd
      (ground.unitLeMul (h 0 (Nat.succ_pos _)) (ground.unitLeSq u0))
      (dotP_sq_nonneg dt ut (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

/-- A gap list strictly above the sum's unit against the squares of
a vector off the unit family folds strictly above the unit: the
vector's occupied entry prices its term strictly above, the further
terms at or above. -/
private theorem dotP_sq_pos : ∀ (d u : List BPair),
    (∀ i, i < d.length → BPair.unit < ground.getAt BPair.unit d i) →
    u.length ≤ d.length → ¬ poly.unitTail u →
    BPair.unit < dotP d (List.zipWith (· * ·) u u)
  | _, [], _, _, hu => absurd trivial hu
  | [], _ :: _, _, hl, _ => absurd hl (Nat.not_succ_le_zero _)
  | d0 :: dt, u0 :: ut, h, hl, hu => by
    show BPair.unit < d0 * (u0 * u0) + dotP dt (List.zipWith (· * ·) ut ut)
    by_cases h0 : u0.oneValue BPair.unit
    · have hut : ¬ poly.unitTail ut := fun ht => hu ⟨h0, ht⟩
      have hrest := dotP_sq_pos dt ut
        (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
        (Nat.le_of_succ_le_succ hl) hut
      exact BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (ground.unitLtAdd hrest
          (ground.unitLeMul (ground.leB_of_lt (h 0 (Nat.succ_pos _)))
            (ground.unitLeSq u0)))
    · exact ground.unitLtAdd
        (ground.unitLtMul (h 0 (Nat.succ_pos _)) (ground.sq_pos h0))
        (dotP_sq_nonneg dt ut
          (fun i hi => ground.leB_of_lt (h (i + 1) (Nat.succ_lt_succ hi))))

/-- The dominance comparison prices the quadratic form: the gaps'
fold against the coordinates' squares sits at or below the form at
every symmetric datum, the peel telescoping
(`thm:decimation`(ii)'s display). -/
theorem dom_form {n : Nat} (S : Mat) (hsq : sqAt S n)
    (hsym : matOneValue S (transposeM S)) (v : List BPair) (hv : v.length = n) :
    dotN (gapOf 0 S) (List.zipWith (· * ·) v v) ≤ dotN v (matVec S v) := by
  have hSl : S.length = n := sqAt_len hsq
  refine quad_gaps S n (gapOf 0 S) hsq (by rw [length_gapOf]; exact hSl) hsym ?_ v hv
  intro i hi
  rw [getAt_gapOf 0 S i (by rw [hSl]; exact hi), Nat.zero_add]
  exact Or.inl (gapRow_read i _)

/-- At the comparison the form sits at or beyond the sum's unit at
every vector, the gaps' fold of squares at or beyond it. -/
theorem dom_unit {n : Nat} (S : Mat) (hsq : sqAt S n)
    (hsym : matOneValue S (transposeM S)) (hdom : domAt S)
    (v : List BPair) (hv : v.length = n) : BPair.unit ≤ dotN v (matVec S v) :=
  ground.leB_trans
    (ground.leB_congr_right (BPair.oneValue_symm (dotN_read _ _))
      (dotP_sq_nonneg (gapOf 0 S) v (fun i hi =>
        of_decide_eq_true (ground.all_getAt BPair.unit (gapOf 0 S) hdom i hi))))
    (dom_form S hsq hsym v hv)

/-- Every split of a dominance-clear datum reads the upper side
throughout: an occupied count's witness prices the form strictly
below the sum's unit, against the comparison's own pricing. -/
theorem dom_psd {n : Nat} (S : Mat) (sp : Split n)
    (hdom : domAt S) (h : splitRead S sp) : psdAt sp := by
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hocc =>
    obtain ⟨u, hu, hlt⟩ := rev_witness S sp h hocc
    exact absurd hlt
      (ground.leB_not_lt (dom_unit S h.1 (splitRead_symm S sp h) hdom u hu))

/-! Clause (ii)'s comparison along the root coordinate at the
polynomial carrier: each tower row's dominance polynomial, the
diagonal's entry less the off-row entries' coefficientwise magnitude
fold (`thm:windowsep`'s carrier), keeps its upper side over a located
segment at `lem:stage`'s priced side read, and at every positive
point of the segment the evaluated block's gaps then sit beyond the
sum's unit, the comparison's validity region read at the free cell
(`lem:freecell`'s dominance family). -/

/-- The off-row magnitude fold at the polynomial carrier: each
off-row entry at its coefficientwise magnitudes, the row's fold at
the stated key withdrawn (`ground.offFoldO` at the polynomial
bundle). -/
def offFoldP : Nat → List poly.Poly → poly.Poly :=
  ground.offFoldO poly.polyOps (fun p => p.map windowsep.mag)

/-- A row's dominance polynomial (`thm:decimation`(ii) at the
`α = 1` representative): the diagonal's entry less the off-row
magnitude fold, one polynomial in the root coordinate. -/
def domPoly (i : Nat) (r : List poly.Poly) : poly.Poly :=
  poly.add (ground.getAt [] r i) (poly.neg (offFoldP i r))

/-- The rows' dominance polynomials, one per row at its own key. -/
def domPolys : Nat → split.PMat → List poly.Poly
  | _, [] => []
  | i, r :: rest => domPoly i r :: domPolys (i + 1) rest

/-- The dominance read over a segment: every row's dominance
polynomial keeps its upper side over the segment at the stated bound
(`lem:stage`'s priced side read at `thm:decimation`(ii)'s
comparison). -/
def domRead (P : split.PMat) (lo hi : CPair) (N D : BPair) : Prop :=
  ((domPolys 0 P).all (fun q => decide (stage.keepUpper q lo hi N D))) = true

instance instDecimation9 (P : split.PMat) (lo hi : CPair) (N D : BPair) :
    Decidable (domRead P lo hi N D) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dominance polynomials' count is the rows'. -/
private theorem length_domPolys : ∀ (k : Nat) (P : split.PMat),
    (domPolys k P).length = P.length
  | _, [] => rfl
  | k, _ :: rest => by
    show (domPolys (k + 1) rest).length + 1 = rest.length + 1
    rw [length_domPolys (k + 1) rest]

/-- The dominance polynomial at a key is its row's own. -/
private theorem getAt_domPolys : ∀ (k : Nat) (P : split.PMat) (i : Nat),
    i < P.length →
    ground.getAt ([] : poly.Poly) (domPolys k P) i
      = domPoly (k + i) (ground.getAt [] P i)
  | _, [], i, hi => absurd hi (Nat.not_lt_zero i)
  | _, _ :: _, 0, _ => rfl
  | k, _ :: rest, i + 1, hi => by
    show ground.getAt ([] : poly.Poly) (domPolys (k + 1) rest) i
      = domPoly (k + (i + 1)) (ground.getAt [] rest i)
    rw [getAt_domPolys (k + 1) rest i (Nat.lt_of_succ_lt_succ hi),
      Nat.add_assoc, Nat.add_comm 1 i]

/-- The magnitude polynomials' fold keeps the entries' cap. -/
private theorem length_magSumP (K : Nat) : ∀ t : List poly.Poly,
    (∀ j, (ground.getAt ([] : poly.Poly) t j).length ≤ K + 1) →
    (ground.famFold poly.add ([] : poly.Poly)
      (fun p => p.map windowsep.mag) t).length ≤ K + 1
  | [], _ => Nat.zero_le _
  | x :: t, h => by
    show (poly.add (x.map windowsep.mag) (ground.famFold poly.add ([] : poly.Poly)
      (fun p => p.map windowsep.mag) t)).length ≤ K + 1
    refine poly.add_len_le _ _ _ ?_ (length_magSumP K t (fun j => h (j + 1)))
    rw [ground.length_map]
    exact h 0

/-- The off-row fold keeps the entries' cap. -/
private theorem length_offFoldP (K : Nat) : ∀ (i : Nat) (r : List poly.Poly),
    (∀ j, (ground.getAt ([] : poly.Poly) r j).length ≤ K + 1) →
    (offFoldP i r).length ≤ K + 1
  | 0, [], _ => Nat.zero_le _
  | _ + 1, [], _ => Nat.zero_le _
  | 0, _ :: t, h => length_magSumP K t (fun j => h (j + 1))
  | i + 1, x :: t, h => by
    show (poly.add (x.map windowsep.mag) (offFoldP i t)).length ≤ K + 1
    refine poly.add_len_le _ _ _ ?_ (length_offFoldP K i t (fun j => h (j + 1)))
    rw [ground.length_map]
    exact h 0

/-- The magnitude polynomials' fold evaluates to the entries'
evaluations' fold. -/
private theorem evalClear_magSumP (zn : BPair) (hzn : BPair.unit ≤ zn) (ed : Pos) (K : Nat) :
    ∀ t : List poly.Poly,
      (poly.evalClear (ground.famFold poly.add ([] : poly.Poly)
        (fun p => p.map windowsep.mag) t) zn ed K).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun p => poly.evalClear (p.map windowsep.mag) zn ed K) t)
  | [] => BPair.oneValue_refl _
  | x :: t => by
    show (poly.evalClear (poly.add (x.map windowsep.mag)
        (ground.famFold poly.add ([] : poly.Poly) (fun p => p.map windowsep.mag) t))
        zn ed K).oneValue
      (poly.evalClear (x.map windowsep.mag) zn ed K
        + ground.famFold BPair.add BPair.unit
          (fun p => poly.evalClear (p.map windowsep.mag) zn ed K) t)
    exact BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
      (BPair.add_congr (BPair.oneValue_refl _) (evalClear_magSumP zn hzn ed K t))

/-- The evaluated off-row fold sits at or below the polynomial
fold's evaluation at a point at or beyond the sum's unit, the
entrywise magnitude cap
(`windowsep.evalClear_magDom`) summed along the walk. -/
private theorem offFold_evalP (zn : BPair) (hzn : BPair.unit ≤ zn) (ed : Pos) (K : Nat) :
    ∀ (i : Nat) (r : List poly.Poly),
      offFold i (r.map (fun p => poly.evalClear p zn ed K))
        ≤ poly.evalClear (offFoldP i r) zn ed K
  | 0, [] => ground.leB_refl _
  | _ + 1, [] => ground.leB_refl _
  | 0, _ :: t => by
    show magSum (t.map (fun p => poly.evalClear p zn ed K))
      ≤ poly.evalClear (ground.famFold poly.add ([] : poly.Poly)
          (fun p => p.map windowsep.mag) t) zn ed K
    refine ground.leB_congr_right
      (BPair.oneValue_symm (evalClear_magSumP zn hzn ed K t)) ?_
    show ground.famFold BPair.add BPair.unit windowsep.mag
      (t.map (fun p => poly.evalClear p zn ed K)) ≤ _
    rw [ground.famFold_map BPair.add BPair.unit windowsep.mag
      (fun p => poly.evalClear p zn ed K) t]
    exact ground.bsum_le_of_mem _ _ t
      (fun p _ => windowsep.evalClear_magDom zn hzn ed K (windowsep.magDom_map p))
  | i + 1, x :: t => by
    show windowsep.mag (poly.evalClear x zn ed K)
        + offFold i (t.map (fun p => poly.evalClear p zn ed K))
      ≤ poly.evalClear (poly.add (x.map windowsep.mag) (offFoldP i t))
          zn ed K
    refine ground.leB_congr_right
      (BPair.oneValue_symm (poly.evalClear_add _ _ _ _ _)) ?_
    exact ground.leB_add
      (windowsep.evalClear_magDom zn hzn ed K (windowsep.magDom_map x))
      (offFold_evalP zn hzn ed K i t)

/-- The dominance read prices the gaps at every point of the segment
at or beyond the sum's unit (`thm:decimation`(ii)'s comparison read along the root
coordinate): each evaluated row's gap sits at or beyond its dominance
polynomial's evaluation, and the polynomial keeps its upper side at
the priced side read, so every gap sits beyond the sum's unit. -/
theorem dom_segment (P : split.PMat) (K : Nat) (lo hi : CPair) (N D : BPair)
    (h : domRead P lo hi N D)
    (hdeg : ∀ i j, (ground.getAt ([] : poly.Poly)
      (ground.getAt ([] : List poly.Poly) P i) j).length ≤ K + 1)
    (zn : BPair) (hzn : BPair.unit ≤ zn) (ed : Pos)
    (hlo : lo ≤ (⟨zn, ed⟩ : CPair))
    (hhi : (⟨zn, ed⟩ : CPair) ≤ hi) :
    gapPos (cellcount.evalPC P zn ed K) := by
  have hEl : (cellcount.evalPC P zn ed K).length = P.length :=
    cellcount.length_evalPC _ _ _ _
  refine ground.all_of_getAt BPair.unit _
    (gapOf 0 (cellcount.evalPC P zn ed K)) (fun k hk => ?_)
  rw [length_gapOf, hEl] at hk
  rw [getAt_gapOf 0 _ k (by rw [hEl]; exact hk), Nat.zero_add]
  refine decide_eq_true ?_
  have hkd : k < (domPolys 0 P).length := by
    rw [length_domPolys]
    exact hk
  have hup : stage.keepUpper (domPoly k (ground.getAt [] P k)) lo hi N D := by
    have h1 := ground.all_getAt ([] : poly.Poly) (domPolys 0 P) h k hkd
    rw [getAt_domPolys 0 P k hk, Nat.zero_add] at h1
    exact of_decide_eq_true h1
  have hlen : (domPoly k (ground.getAt [] P k)).length ≤ K + 1 := by
    refine poly.add_len_le _ _ _ (hdeg k k) ?_
    rw [poly.length_neg]
    exact length_offFoldP K k _ (fun j => hdeg k j)
  have hq : BPair.unit
      < poly.evalClear (domPoly k (ground.getAt [] P k)) zn ed K :=
    stage.evalFloor
      (fun d hd => BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit _ d (Nat.le_trans hlen hd)))
      zn ed
      (stage.keepUpper_all _ lo hi N D hup ⟨zn, ed⟩ hlo hhi)
  have hsplit : (poly.evalClear (domPoly k (ground.getAt [] P k))
      zn ed K).oneValue
      (poly.evalClear (ground.getAt [] (ground.getAt [] P k) k) zn ed K
        + (poly.evalClear (offFoldP k (ground.getAt [] P k))
            zn ed K).swap) :=
    BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
      (BPair.add_congr (BPair.oneValue_refl _) (poly.evalClear_neg _ _ _ _))
  show BPair.unit
    < ground.getAt BPair.unit
        (ground.getAt [] (cellcount.evalPC P zn ed K) k) k
      + (offFold k (ground.getAt [] (cellcount.evalPC P zn ed K) k)).swap
  rw [cellcount.getAt_evalPC zn ed K P k k,
    show ground.getAt ([] : List BPair) (cellcount.evalPC P zn ed K) k
      = (ground.getAt ([] : List poly.Poly) P k).map
          (fun p => poly.evalClear p zn ed K)
      from ground.getAt_map ([] : List poly.Poly) ([] : List BPair) _ P k hk]
  refine ground.ltB_trans_le
    (BPair.lt_congr (BPair.oneValue_refl _) hsplit hq) ?_
  exact ground.leB_add (ground.leB_refl _)
    (ground.leB_swap (offFold_evalP zn hzn ed K k _))

/-- At every gap beyond the sum's unit every split of the datum is
positive definite: the upper side throughout, and the kernel block
vacant, a kernel column's image off the unit family pricing the form
at the sum's unit against the gaps' strict floor
(`thm:decimation`(ii)'s kernel read). -/
theorem dom_pd {n : Nat} (S : Mat) (hg : gapPos S)
    (sp : Split n) (h : splitRead S sp) : pdAt sp := by
  have hSl : S.length = n := sqAt_len h.1
  have hposI : ∀ i, i < (gapOf 0 S).length →
      BPair.unit < ground.getAt BPair.unit (gapOf 0 S) i :=
    fun i hi => of_decide_eq_true (ground.all_getAt BPair.unit (gapOf 0 S) hg i hi)
  have hdom : domAt S :=
    ground.all_of_getAt BPair.unit _ (gapOf 0 S) (fun k hk =>
      decide_eq_true (ground.leB_of_lt (hposI k hk)))
  refine ⟨dom_psd S sp hdom h, ?_⟩
  cases Nat.eq_zero_or_pos sp.kern with
  | inl h0 => exact h0
  | inr hk =>
    obtain ⟨u, hu, hoff, hform⟩ := kern_witness S sp h hk
    have hprice := dom_form S h.1 (splitRead_symm S sp h) u hu
    have hlt : BPair.unit < dotN (gapOf 0 S) (List.zipWith (· * ·) u u) :=
      BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (dotN_read _ _))
        (dotP_sq_pos (gapOf 0 S) u hposI
          (by rw [hu, length_gapOf, hSl]; exact Nat.le_refl n) hoff)
    exact absurd hlt
      (ground.leB_not_lt (ground.leB_congr_right hform hprice))

/-- The decimated count: the whole chain's count is the head slabs'
fold wherever the dropped tail sub-chain reads the dominance
comparison, `thm:decimation`(ii)'s count telescope. -/
theorem dom_count {n m : Nat} (diag off : List Mat)
    (Xs Rs : List MatQ) (ns : List Nat)
    (sps : List ((k : Nat) × Split k)) (SP : Split n)
    (h : Nat) (spT : Split m)
    (ht : tailRead diag off Xs Rs ns)
    (hl : revListRead Xs sps)
    (hS : splitRead (assemble diag off) SP)
    (hT : splitRead (assemble (diag.drop h) (off.drop h)) spT)
    (hdom : domAt (assemble (diag.drop h) (off.drop h))) :
    revAt SP = revFold (sps.take h) := by
  cases Nat.lt_or_ge h diag.length with
  | inl hh =>
    have h1 : revAt SP = revFold sps :=
      countSplit diag off Xs Rs ns sps SP ht hl hS
    have h2 : revAt spT = revFold (sps.drop h) :=
      countSplit (diag.drop h) (off.drop h) (Xs.drop h) (Rs.drop h)
        (ns.drop h) (sps.drop h) spT
        (tailRead_drop diag off Xs Rs ns h hh ht)
        (revListRead_drop Xs sps h hl) hT
    have h3 : revAt spT = 0 :=
      dom_psd (assemble (diag.drop h) (off.drop h)) spT hdom hT
    rw [h1, revFold_split sps h, ← h2, h3]
    exact Nat.add_zero (revFold (sps.take h))
  | inr hge =>
    have hlen : sps.length ≤ h := by
      rw [← revListRead_length Xs sps hl, qShape_len ht.2.1,
        slabShape_len_ns ht.1]
      exact hge
    rw [ground.take_of_le sps h hlen]
    exact countSplit diag off Xs Rs ns sps SP ht hl hS

/-- The tower's deflation: the datum deflated onto the further places
at the tower places' block, the adjugate against the block the
solve (`lem:inertia`'s deflation at designated places). -/
def towerDefl (S : Mat) (tw hd : List Nat) : Mat :=
  deflMat (selM tw tw S) (selM tw hd S) (selM hd hd S)
    (matMul (adjM (selM tw tw S)) (selM tw hd S))

/-- The decimated count at designated places: a dropped block
positive definite at its stated split is a nonsingular principal
pivot at its key list, so the datum's count is its deflation's onto
the head, the adjugate against the block the deflation's solve
(`thm:decimation`'s decimated symbol at `lem:inertia`'s addition at
designated places), the key lists' join listing every place of the
order once. -/
theorem head_count {n : Nat} (S : Mat) (tl hd : List Nat)
    (hk0 : 0 < tl.length)
    (hS : sqAt S n) (hsym : matOneValue (transposeM S) S)
    (hlen : (tl ++ hd).length = n) (hdist : ground.distinctList (tl ++ hd))
    (hb : ((tl ++ hd).all (fun i => Nat.blt i n)) = true)
    (spT : Split tl.length) (hT : splitRead (selM tl tl S) spT)
    (hpd : pdAt spT)
    (spS : Split n) (hS' : splitRead S spS)
    (spD : Split hd.length)
    (hD : splitRead (towerDefl S tl hd) spD) :
    revAt spS = revAt spD := by
  have hPnz := minor_of_kern _ spT hT hpd.2
  have hPsq : sqAt (selM tl tl S) tl.length :=
    sqAt_of (length_selM _ _ _) (rowsLen_selM _ _ _)
  have hBl : (selM tl hd S).length = tl.length := length_selM _ _ _
  have hBr : rowsLen hd.length (selM tl hd S) := rowsLen_selM _ _ _
  have hAl : (adjM (selM tl tl S)).length = tl.length :=
    (adjM_len _ (by rw [length_selM]; exact hk0)).trans (length_selM _ _ _)
  have hCl : (matMul (adjM (selM tl tl S)) (selM tl hd S)).length
      = tl.length := (length_matMul _ _).trans hAl
  have hCr : rowsLen hd.length (matMul (adjM (selM tl tl S)) (selM tl hd S)) :=
    rowsLen_cast (length_transposeM _ hBr (by rw [hBl]; exact hk0))
      (rowsLen_matMul _ _)
  have h := rev_places S tl hd hk0 hS hsym hlen hdist hb _ hCl hCr
    (adjM_solve _ _ hPsq hBl hBr hk0) hPnz spS hS' spT hT spD hD
  rw [h, hpd.1, Nat.zero_add]

/-- The count at a stated order: at a distinct key list covering the
order whose selection reads one value with an assembled slab chain,
the datum's split and the chain's split read one count, the places'
permutation conjugating the datum to its selection
(`inertia.rev_perm`). -/
theorem order_perm {n : Nat} (M : Mat) (ord : List Nat) (hM : sqAt M n)
    (hlen : ord.length = n) (hdist : ground.distinctList ord)
    (hb : (ord.all (fun i => Nat.blt i n)) = true)
    (diag off : List Mat)
    (hA : matOneValue (selM ord ord M) (assemble diag off))
    (spM : Split n) (hspM : splitRead M spM)
    (spC : Split n) (hspC : splitRead (assemble diag off) spC) :
    revAt spM = revAt spC := by
  have hSel : sqAt (selM ord ord M) n :=
    sqAt_of ((length_selM _ _ _).trans hlen)
      (rowsLen_cast hlen (rowsLen_selM _ _ _))
  have hspS := splitRead_congr _ _ hSel (matOne_symm hA) spC hspC
  exact (rev_perm M ord hM hlen hdist hb spM hspM spC hspS).symm

/-- The count at a stated order is the chain's own: the datum's
split reads the pivots' fold at the tail recursion's certificate
(`order_perm` at `greenprod.countSplit`). -/
theorem order_count {n : Nat} (M : Mat) (ord : List Nat) (hM : sqAt M n)
    (hlen : ord.length = n) (hdist : ground.distinctList ord)
    (hb : (ord.all (fun i => Nat.blt i n)) = true)
    (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
    (sps : List ((k : Nat) × Split k))
    (hA : matOneValue (selM ord ord M) (assemble diag off))
    (ht : tailRead diag off Xs Rs ns) (hl : revListRead Xs sps)
    (spM : Split n) (hspM : splitRead M spM)
    (spC : Split n) (hspC : splitRead (assemble diag off) spC) :
    revAt spM = revFold sps :=
  (order_perm M ord hM hlen hdist hb diag off hA spM hspM spC hspC).trans
    (countSplit _ _ Xs Rs ns sps spC ht hl hspC)

/-- `thm:decimation`(i): the count at every level splits over the
depth chain's pivot recursion.  At the sector's frame
(`con:depthchain`) a symmetric square datum with its cross entries
at the sum's unit off the members' joins is the assembled slab data
along the depth order, and at a depth order listing every position
once the datum's split reads the chain's own count, the pivots'
fold (`inertia.rev_perm` at the places' permutation,
`greenprod.countSplit` at the tail recursion's certificate). -/
theorem chain_count (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (o : Nat)
    (hT : ∀ T, T ∈ terms → sqAt T o ∧ matOneValue (transposeM T) T)
    (hpos : ∀ s ∈ pos, ∀ i ∈ s, i < o)
    (hocc : ∀ a, a < pos.length → 0 < (ground.getAt [] pos a).length)
    (hn : n = pos.length)
    (M : Mat) (hM : sqAt M o) (hsym : matOneValue (transposeM M) M)
    (hcross : depthchain.crossB terms pos M = true)
    (hlen : (depthchain.depthOrder terms pos n base).length = o)
    (hdist : ground.distinctList (depthchain.depthOrder terms pos n base))
    (hb : ((depthchain.depthOrder terms pos n base).all
      (fun i => Nat.blt i o)) = true)
    (Xs Rs : List MatQ) (ns : List Nat)
    (sps : List ((k : Nat) × Split k))
    (ht : tailRead
      (depthchain.slabDiag M (depthchain.posShells terms pos n base))
      (depthchain.slabOff M (depthchain.posShells terms pos n base)) Xs Rs ns)
    (hl : revListRead Xs sps)
    (spM : Split o) (hspM : splitRead M spM)
    (spC : Split o)
    (hspC : splitRead (assemble
      (depthchain.slabDiag M (depthchain.posShells terms pos n base))
      (depthchain.slabOff M (depthchain.posShells terms pos n base))) spC) :
    revAt spM = revFold sps :=
  order_count M (depthchain.depthOrder terms pos n base) hM hlen hdist hb
    _ _ Xs Rs ns sps
    (depthchain.depth_assemble terms pos n base o hT hpos hocc hn
      M hM hsym hcross) ht hl spM hspM spC hspC


/-! Clause (iii)'s slab tier: the decimated bulk at the deck pivot,
the count on the bracket over the ball's dropped pivots, and two
windows' shared data within the iterated cap brackets. -/

/-- Clause (iii)'s slab step: the bulk data constant beyond the
stated depth, the deck pivot the ball certificate's located center
at the pivot identities — the fixed point's step, the transfer's
contraction pricing the solvent's roots inside, the floor and the
defect with the modulus reads — the tail pivots in the ball, and
the deck symbol's band read at its cleared-variable monic, the
validity data the bulk block's own. -/
def bulkRead {n o1 o2 : Nat} (diag off : List Mat)
    (Xs Rs : List MatQ) (ns : List Nat) (A B : Mat)
    (Y Cc : MatQ) (w0 : Nat) (G : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (spC spF spU0 spL0 : Split n)
    (bsps : List (Split n × Split n))
    (spH : Split o1) (spB : Split o2) : Prop :=
  tailRead diag off Xs Rs ns
  ∧ ((diag.drop w0).all (fun M => decide (matOneValue M A))) = true
  ∧ ((off.drop w0).all (fun M => decide (matOneValue M B))) = true
  ∧ deckfactor.deckSymRead (spectator.deckPoly A B) n
  ∧ deckfactor.bandClear
      (deckfactor.symbolOf (spectator.deckPoly A B) n) spH spB
  ∧ spectator.ballRead Y Cc Y A B G ln ld y0n y0d rn rd r0n r0d
      lcn lcd spC spF spU0 spL0
  ∧ spectator.ballList Y G rn rd (Xs.drop w0) bsps

instance instDecimation5 {n o1 o2 : Nat} (diag off : List Mat) (Xs Rs : List MatQ)
    (ns : List Nat) (A B : Mat) (Y Cc : MatQ) (w0 : Nat)
    (G : Mat) (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (spC spF spU0 spL0 : Split n)
    (bsps : List (Split n × Split n)) (spH : Split o1)
    (spB : Split o2) :
    Decidable (bulkRead diag off Xs Rs ns A B Y Cc w0 G
      ln ld y0n y0d rn rd r0n r0d lcn lcd spC spF spU0 spL0
      bsps spH spB) :=
  inferInstanceAs
    (Decidable (_ ∧ _ = _ ∧ _ = _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Two windows share the decimated data up to their lengths, each
window's own data beyond: the shared heads, the tail deviation's
sandwich down from the perturbation slab, and the iterated cap walk
down the tail witnesses at the gram list's own slab blocks, from
the stated seed at that slab to the observable's depth `j`, one
certificate per slab of the gap. -/
def windowShareRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' Ys Cs Ys' Cs' : List MatQ) (w0 j : Nat)
    (ns : List Nat) (cn cd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2)) :
    Prop :=
  spectator.headShareRead diag off diag' off' Ys Cs Ys' Cs' w0 ns
  ∧ spectator.tailSandwichRead diag off diag' off' Xs Rs Xs' Rs' w0 ns
  ∧ spectator.capWalk Gs cn cd (ground.getAt dM Xs' w0)
      (ground.getAt dM Xs w0) ((Rs.take w0).drop j).reverse
      ((Rs'.take w0).drop j).reverse ((Xs.take w0).drop j).reverse
      ((Xs'.take w0).drop j).reverse certs

instance instDecimation6 (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' Ys Cs Ys' Cs' : List MatQ) (w0 j : Nat)
    (ns : List Nat) (cn cd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2)) :
    Decidable (windowShareRead diag off diag' off' Xs Rs Xs' Rs'
      Ys Cs Ys' Cs' w0 j ns cn cd Gs certs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The ball list's per-position upper-side read: each pivot's
stated split reads the upper side throughout, the ball's own
positivity at the pointwise cap sides. -/
private theorem ballListPsd {o : Nat} (Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF : Split o)
    (hYc : sqAt Yc.1 o)
    (hF : spectator.floorRead Yc G y0n y0d rn rd spF) :
    ∀ (Xs : List MatQ) (bsps : List (Split o × Split o)),
      spectator.ballList Yc G rn rd Xs bsps →
      ∀ i, i < Xs.length → ∀ s : (k : Nat) × Split k,
        splitRead (ground.getAt dM Xs i).1 s.2 → psdAt s.2
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], hb, _, _, _, _ => (hb : False).elim
  | X :: _, b :: _, hb, 0, _, s, hs =>
    spectator.ball_psd_of X Yc G y0n y0d rn rd spF s.2 hb.1 hYc
      (inertia.sqAt_matScale_reflect (rn * (spectator.devQ X Yc).2) G
        hb.2.1.2.1)
      hF
      (spectator.cap_hi (spectator.devQ X Yc) G rn rd b.1 b.2 hb.2.1)
      (spectator.cap_lo (spectator.devQ X Yc) G rn rd b.1 b.2 hb.2.1)
      hs
  | _ :: Xt, _ :: bt, hb, i + 1, hi, s, hs =>
    ballListPsd Yc G y0n y0d rn rd spF hYc hF Xt bt hb.2.2 i
      (Nat.lt_of_succ_lt_succ hi) s hs

/-- The ball's pivots contribute nothing to the slab fold: each
pivot's stated split reads the upper side at the ball's own
positivity, so the fold returns its seed
(`greenprod.revFold_vacant`). -/
private theorem ballFold {o : Nat} (Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF : Split o)
    (hYc : sqAt Yc.1 o)
    (hF : spectator.floorRead Yc G y0n y0d rn rd spF) :
    ∀ (Xs : List MatQ) (sps : List ((k : Nat) × Split k))
      (bsps : List (Split o × Split o)) (a : Nat),
      revListRead Xs sps → spectator.ballList Yc G rn rd Xs bsps →
      sps.foldl (fun m s => m + revAt s.2) a = a :=
  fun Xs sps bsps a hl hb =>
    greenprod.revFold_vacant Xs sps a hl
      (ballListPsd Yc G y0n y0d rn rd spF hYc hF Xs bsps hb)

/-- The decimated count at the deck pivot's ball: the whole chain's
count is the head slabs' fold wherever the dropped pivots sit in
the solvent's ball around the center — the decimated symbol's
count at clause (iii)'s validity cells. -/
theorem ball_count {n o : Nat} (diag off : List Mat)
    (Xs Rs : List MatQ) (ns : List Nat)
    (sps : List ((k : Nat) × Split k)) (SP : Split n) (h : Nat)
    (Y : MatQ) (G : Mat) (y0n y0d rn rd : Pos) (spF : Split o)
    (bsps : List (Split o × Split o))
    (hYc : sqAt Y.1 o)
    (ht : tailRead diag off Xs Rs ns)
    (hl : revListRead Xs sps)
    (hS : splitRead (assemble diag off) SP)
    (hF : spectator.floorRead Y G y0n y0d rn rd spF)
    (hb : spectator.ballList Y G rn rd (Xs.drop h) bsps) :
    revAt SP = revFold (sps.take h) := by
  have h1 : revAt SP = revFold sps :=
    countSplit diag off Xs Rs ns sps SP ht hl hS
  have h2 : revFold (sps.drop h) = 0 :=
    ballFold Y G y0n y0d rn rd spF hYc hF (Xs.drop h)
      (sps.drop h) bsps 0 (revListRead_drop Xs sps h hl) hb
  rw [h1, revFold_split sps h, h2]
  exact Nat.add_zero (revFold (sps.take h))

/-- The decimated symbol (`thm:decimation`): the datum's count is the
decimated head's.  The tower block at its designated places reads
the dominance comparison at occupied gaps, so it is positive definite
at every split and the datum's count is its deflation's onto the
further places (`dom_pd`, `head_count`); the deflated datum at a
stated shell order is a slab chain, the first shell the head and
the further shells the far slabs, and at the far pivots inside the
deck pivot's ball the chain's count is the head pivot's
(`order_perm`, `ball_count`): the head pivot, the recursion's
Schur complement onto the head, is the decimated head at the head's
order. -/
theorem decimated_count {n o : Nat} (S : Mat) (tw hd : List Nat)
    (hk0 : 0 < tw.length)
    (hS : sqAt S n) (hsym : matOneValue (transposeM S) S)
    (hlen : (tw ++ hd).length = n) (hdist : ground.distinctList (tw ++ hd))
    (hb : ((tw ++ hd).all (fun i => Nat.blt i n)) = true)
    (spT : Split tw.length) (hT : splitRead (selM tw tw S) spT)
    (hdom : gapPos (selM tw tw S))
    (spS : Split n) (hS' : splitRead S spS)
    (spD : Split hd.length) (hD : splitRead (towerDefl S tw hd) spD)
    (sh : List (List Nat))
    (hshl : (sh.flatMap (fun s => s)).length = hd.length)
    (hshd : ground.distinctList (sh.flatMap (fun s => s)))
    (hshb : ((sh.flatMap (fun s => s)).all (fun i => Nat.blt i hd.length)) = true)
    (hocc : ∀ s, s ∈ sh → 0 < s.length)
    (hoff : depthchain.offBandB (towerDefl S tw hd) sh = true)
    (X1 : MatQ) (Xs Rs : List MatQ) (ns : List Nat)
    (s1 : (k : Nat) × Split k) (sps : List ((k : Nat) × Split k))
    (ht : tailRead (depthchain.slabDiag (towerDefl S tw hd) sh)
      (depthchain.slabOff (towerDefl S tw hd) sh) (X1 :: Xs) Rs ns)
    (hl : revListRead (X1 :: Xs) (s1 :: sps))
    (spC : Split hd.length)
    (hC : splitRead (assemble (depthchain.slabDiag (towerDefl S tw hd) sh)
      (depthchain.slabOff (towerDefl S tw hd) sh)) spC)
    (Y : MatQ) (G : Mat) (y0n y0d rn rd : Pos) (spF : Split o)
    (bsps : List (Split o × Split o))
    (hYc : sqAt Y.1 o) (hF : spectator.floorRead Y G y0n y0d rn rd spF)
    (hball : spectator.ballList Y G rn rd Xs bsps) :
    revAt spS = revAt s1.2 := by
  have hpd : pdAt spT := dom_pd _ hdom spT hT
  have h1 : revAt spS = revAt spD :=
    head_count S tw hd hk0 hS hsym hlen hdist hb spT hT hpd spS hS' spD hD
  have hbtw : (tw.all (fun i => Nat.blt i n)) = true
      ∧ (hd.all (fun i => Nat.blt i n)) = true := by
    rw [ground.all_append] at hb
    exact ground.andSplitB hb
  have hPsq : sqAt (selM tw tw S) tw.length :=
    sqAt_of (length_selM _ _ _) (rowsLen_selM _ _ _)
  have hBl : (selM tw hd S).length = tw.length := length_selM _ _ _
  have hBr : rowsLen hd.length (selM tw hd S) := rowsLen_selM _ _ _
  have hAl : (adjM (selM tw tw S)).length = tw.length :=
    (adjM_len _ (by rw [length_selM]; exact hk0)).trans (length_selM _ _ _)
  have hCl : (matMul (adjM (selM tw tw S)) (selM tw hd S)).length
      = tw.length := (length_matMul _ _).trans hAl
  have hBt : (transposeM (selM tw hd S)).length = hd.length :=
    length_transposeM _ hBr (by rw [hBl]; exact hk0)
  have hCr : rowsLen hd.length (matMul (adjM (selM tw tw S)) (selM tw hd S)) :=
    rowsLen_cast hBt (rowsLen_matMul _ _)
  have hD1sq : sqAt (towerDefl S tw hd) hd.length :=
    sqAt_deflMat _ _ _ _ hd.length hBt
      (length_transposeM _ hCr (by rw [hCl]; exact hk0))
      (length_selM _ _ _) (rowsLen_selM _ _ _)
  have hD1sym : matOneValue (transposeM (towerDefl S tw hd)) (towerDefl S tw hd) :=
    deflMat_symm S tw hd hk0 hS hsym hbtw.1 hbtw.2 _ hCl hCr
      (adjM_solve _ _ hPsq hBl hBr hk0)
  have hsb : ∀ s, s ∈ sh → ∀ i, i ∈ s → i < hd.length := fun s hs i hi =>
    ground.bltLt (ground.all_of_mem _ _ hshb i
      (ground.mem_flatMap_to (fun s => s) hs hi))
  have hA := depthchain.chain_assemble (towerDefl S tw hd) hd.length
    hD1sq hD1sym sh hocc hsb hoff
  have h2 : revAt spD = revAt spC :=
    order_perm (towerDefl S tw hd) (sh.flatMap (fun s => s)) hD1sq hshl hshd hshb
      _ _ hA spD hD spC hC
  have h3 : revAt spC = revFold ((s1 :: sps).take 1) :=
    ball_count _ _ (X1 :: Xs) Rs ns (s1 :: sps) spC 1 Y G y0n y0d rn rd spF bsps
      hYc ht hl hC hF hball
  rw [h1, h2, h3]
  exact Nat.zero_add (revAt s1.2)

/-! The divisor list's emitted record: the cells, the boundaries'
bindings, and the record's read. -/

set_option genInjectivity false in
/-- A boundary's binding: the comparison that binds there — the
decimated determinant's own root, or a stated comparison entering
at its display — with the straddle's bracket-pencil split data. -/
inductive Bound (oD : Nat) where
  | jump (spB : Split oD)
  | cmp (p : poly.Poly) (spB : Split oD)
      (sp : (k : Nat) × Split k × Split k)

set_option genInjectivity false in
/-- The emitted record: the head pencil with its clearing power and
sample weight, the divisor's squarefree witness, the shared Hermite
split at the divisor's cleared monic, the cells — one sample per
cell with its count and split — and the boundaries' bindings. -/
structure DivRecord (o oD : Nat) where
  S : split.PMat
  K : Nat
  c : Pos
  ct : cellcount.DivCert
  spHD : Split oD
  cells : List (BPair × Nat × Split o)
  bounds : List (Bound oD)

/-- One boundary's read at its flanking samples: a jump boundary
straddles one root of the divisor's cleared monic; a comparison
boundary straddles one root of its stated display with the
divisor's count at the sum's unit across. -/
def boundRead {oD : Nat} (sq : poly.Poly) (spHD : Split oD) (c : Pos)
    (l r : BPair) : Bound oD → Prop
  | .jump spB =>
    hermitesign.segCountRead (deckfactor.clearVarBT sq)
      (deckfactor.clearAt sq l) (deckfactor.clearAt sq r) c 1 spHD spB
  | .cmp p spB sp =>
    hermitesign.segCountRead (deckfactor.clearVarBT sq)
      (deckfactor.clearAt sq l) (deckfactor.clearAt sq r) c 0 spHD spB
    ∧ hermitesign.segCountRead (deckfactor.clearVarBT p)
        (deckfactor.clearAt p l) (deckfactor.clearAt p r) c 1
        sp.2.1 sp.2.2

instance instDecimation7 {oD : Nat} (sq : poly.Poly) (spHD : Split oD) (c : Pos)
    (l r : BPair) (b : Bound oD) :
    Decidable (boundRead sq spHD c l r b) :=
  match b with
  | .jump _ =>
    inferInstanceAs (Decidable (hermitesign.segCountRead _ _ _ _ _ _ _))
  | .cmp _ _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The record's read: the cells one past the stated boundary
count, the divisor's witness, every cell's count at its sample, and
every boundary's binding at its flanking samples. -/
def recordRead {o oD : Nat} (R : DivRecord o oD) : Prop :=
  R.bounds.length + 1 = R.cells.length
  ∧ cellcount.divRead (split.pminor R.S) R.ct
  ∧ (R.cells.all (fun x =>
      decide (cellcount.countAt R.S R.K x.1 R.c x.2.1 x.2.2))) = true
  ∧ ((List.zip (List.zip R.cells (R.cells.drop 1)) R.bounds).all
      (fun y => decide
        (boundRead R.ct.sq R.spHD R.c y.1.1.1 y.1.2.1 y.2))) = true

instance instDecimation8 {o oD : Nat} (R : DivRecord o oD) :
    Decidable (recordRead R) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ ∧ _ = _ ∧ _ = _))

/-- The decimated head at the tower places (`thm:decimation`(ii)): at
an occupied tower the tower block's once-cleared deflation
(`cellcount.pdeflP` at the head's order and the clearing at the tower
order's successor), the datum's count that deflation's, and at a
vacant tower the pencil itself, the count's own presentation. -/
def towerHead (tw : List Nat) (o : Nat) (S : split.PMat) : split.PMat :=
  match tw with
  | [] => S
  | i :: t => cellcount.pdeflP (i :: t) (cellcount.compl (i :: t) o) S

end decimation
