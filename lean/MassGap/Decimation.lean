import MassGap.Deckfactor
import MassGap.Greenprod
import MassGap.Certconstruct
import MassGap.Cellcount
import MassGap.Pairpencil
import MassGap.Grading
import MassGap.Spectator
/-!
`thm:decimation`(i) — the border direction is the walk's shape.
The window pencil re-blocks along the band-component count: the
stated blocking's groups each read one count from one up with the
unit line the head slab, and the pencil is the block tridiagonal at
the assembled slab data (`chainBlockRead` at `greenprod.assemble`, the head group the
vacuum class alone with each further group's members pairwise
distinct at their own count), the walk's shape at matrix blocks.  The count at every level splits
over the chain's pivot recursion, `rev(S) = Σ_κ rev(X_κ)`
(`greenprod.countSplit`), and the split is order-free, every split
of the assembled datum reading the one count
(`inertia.rev_exchange`), a slab ordering certificate data.  The
ground jump is a divisor point of the decimated head: a jump of the
counting function enters at balance-pair levels as two counts at a
gap over the ordered level pair (`jumpPairAt` at
`certconstruct.countAtPair`), the level is the first two jumps'
distance with the stated level pair within the brackets' gap at
cross-added comparisons (`levelDistRead`), and the boundary defect
is the vacuum's magnetic diagonal, `prop:row`'s Kronecker delta at
two labels — `fusion.unitLaw`'s own instance at the pair
`(θ, 𝟏)`, the batteries' read at the walk's boundary.
The tower tails' clause (`thm:decimation`(ii)) reads at the
dominance comparison: per row the off-row entries' magnitude fold
sits at or below the diagonal's entry (`domAt` at `offFold`,
`windowsep.mag` the carrier), the form prices at or beyond the
gaps' fold of squares by the peel telescoping on the comparison
(`dom_quad`, the cross terms joined to their magnitudes' squares at
one square's multiple per entry side), every split of a
dominance-clear datum reads the upper side throughout (`dom_psd` at
`inertia.rev_witness`), and the count telescopes over the pivot
recursion with the tail's summands at the sum's unit (`dom_count`
at `greenprod.countSplit` over the dropped tail sub-chain,
`tailRead_drop`).
The slabs decimate at the deck pivot (`thm:decimation`(iii)): the
bulk data are constant beyond a stated depth, the deck pivot the
ball certificate's located center at the pivot identities with the
tail pivots riding the ball (`bulkRead` at `spectator.ballRead`
over `spectator.ballList`, the validity data the deck symbol's
band read at its cleared-variable monic and the ball's own, the
bulk block's data alone), the decimated symbol's count on the
bracket is the head's (`ball_count` at `spectator.ball_psd` over
the dropped pivots, every ball member's count at the sum's unit),
and two windows share the decimated data up to their lengths with
the reads within the iterated cap brackets (`windowShareRead` at
`spectator.capWalk` down the tail witnesses from the perturbation
slab to the observable's depth, the head pivots shared below the
slab), the far separated sector entering the head through the band
block's cap alone, its dressing the vacuum's own
(`lem:relfiber`(iv): `relfiber.tensorSum_count`, the tensor sum's
count the root pairs' count, and `relfiber.pairRoots_least`, the
joined sector's ground the two grounds' sum).
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

/-- Two configuration lists at one value, the interface equality
memberwise. -/
def confListEq {L : Type} (F : fusion.Data L) :
    List (List L) → List (List L) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: s, b :: t => carrier.eqConf F a b && confListEq F s t

/-- Pairwise distinctness at the interface equality. -/
def distinctGo {L : Type} (F : fusion.Data L) :
    List (List L) → Bool
  | [] => true
  | a :: r => !(carrier.confMem F a r) && distinctGo F r

/-- A group list's per-group reads, one structural pass: each
group's members sit at the group's own band-component count from
the stated key up, and each group's members are pairwise distinct
at the interface equality. -/
def groupsAt {L : Type} (F : fusion.Data L) (R : lattice.Region) :
    Nat → List (List (List L)) → Bool
  | _, [] => true
  | k, g :: t =>
    (g.all (fun a =>
      Nat.beq (grading.components F R a).length k))
    && distinctGo F g
    && groupsAt F R (k + 1) t

/-- The border blocking: the stated index at the concatenated
groups, the head group the vacuum class alone at the count's
seed with each further group's members at its own band-component
count and pairwise distinct, and the window pencil at the
assembled slab data — the walk's shape at matrix blocks with the
vacuum class at the boundary. -/
def chainBlockRead {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (ix : List (List L)) (gs : List (List (List L)))
    (H : Mat) (diag off : List Mat) (ns : List Nat) : Prop :=
  confListEq F (gs.flatMap (fun g => g)) ix = true
  ∧ groupsAt F R 0 gs = true
  ∧ (ground.getAt [] gs 0).length = 1
  ∧ 0 < gs.length
  ∧ slabShape diag off ns
  ∧ ns = gs.map List.length
  ∧ matOneValue H (assemble diag off)

instance {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (ix : List (List L)) (gs : List (List (List L)))
    (H : Mat) (diag off : List Mat) (ns : List Nat) :
    Decidable (chainBlockRead F R ix gs H diag off ns) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ = _ ∧ _ = _ ∧ _ ∧ _ ∧ _ = _ ∧ _))

/-- A jump of the counting function at balance-pair levels: the two
counts at a gap of at least one over the ordered level pair, each
count `rev(H + yG : xG)` at its split. -/
def jumpPairAt {o : Nat} (H G : Mat) (x1 y1 x2 y2 : Pos) (n g : Nat)
    (sp1 sp2 : Split o) : Prop :=
  countAtPair H G x1 y1 n sp1
  ∧ countAtPair H G x2 y2 (n + g) sp2
  ∧ x1 + y2 < x2 + y1
  ∧ 1 ≤ g

instance {o : Nat} (H G : Mat) (x1 y1 x2 y2 : Pos) (n g : Nat)
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

instance {o : Nat} (H G : Mat)
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
withdrawn, the walk counting the key down. -/
def offFold : Nat → List BPair → BPair
  | _, [] => BPair.unit
  | 0, _ :: t => magSum t
  | i + 1, x :: t => windowsep.mag x + offFold i t

/-- The dominance walk at a stated leading key: per row the
off-row entries' magnitude fold sits at or below the diagonal's
entry, the key stepping with the rows. -/
def domGo : Nat → Mat → Bool
  | _, [] => true
  | i, r :: rest =>
    decide (offFold i r ≤ ground.getAt BPair.unit r i)
      && domGo (i + 1) rest

/-- The dominance comparison: per row, the off-row entries'
magnitude fold sits at or below the diagonal's entry
(`thm:decimation`(ii)), the walk from the leading key. -/
def domAt (S : Mat) : Prop := domGo 0 S = true

instance (S : Mat) : Decidable (domAt S) :=
  inferInstanceAs (Decidable (_ = _))

/-- The walk's row read: at a passing walk every row's comparison
holds at the walked key. -/
private theorem domGo_read : ∀ (k : Nat) (S : Mat) (i : Nat),
    domGo k S = true → i < S.length →
    offFold (k + i) (ground.getAt [] S i)
      ≤ ground.getAt BPair.unit (ground.getAt [] S i) (k + i)
  | _, [], i, _, hi => absurd hi (Nat.not_lt_zero i)
  | _, _ :: _, 0, h, _ => of_decide_eq_true (ground.andSplitB h).1
  | k, _ :: rest, i + 1, h, hi => by
    have e : k + (i + 1) = k + 1 + i :=
      (congrArg (k + ·) (Nat.add_comm i 1)).trans
        (Nat.add_assoc k 1 i).symm
    rw [e]
    exact domGo_read (k + 1) rest i (ground.andSplitB h).2
      (Nat.lt_of_succ_lt_succ hi)

/-- The entry's pricing device: the doubled cross term joined to
the magnitude's two squares sits at or above the sum's unit, the
weighted squares' pricing at the entry's side
(`ground.leB_crossSq`). -/
private theorem magDevice (c x y : BPair) :
    BPair.unit ≤ (x * (c * y) + x * (c * y))
      + (windowsep.mag c * (x * x) + windowsep.mag c * (y * y)) := by
  have hu := windowsep.unitLe_mag c
  rw [BPair.mul_left_comm x c y,
    ← BPair.left_distrib c (x * y) (x * y),
    ← BPair.left_distrib (windowsep.mag c) (x * x) (y * y),
    BPair.add_comm (c * (x * y + x * y))
      (windowsep.mag c * (x * x + y * y))]
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
    rw [BPair.left_distrib x (b0 * y) (dotP bt vst),
      BPair.right_distrib (windowsep.mag b0) (magSum bt) (x * x),
      BPair.add_add_comm (x * (b0 * y)) (x * dotP bt vst)
        (x * (b0 * y)) (x * dotP bt vst),
      BPair.add_add_comm (windowsep.mag b0 * (x * x))
        (magSum bt * (x * x)) (windowsep.mag b0 * (y * y))
        (dotP (bt.map windowsep.mag) (List.zipWith (· * ·) vst vst)),
      BPair.add_add_comm (x * (b0 * y) + x * (b0 * y))
        (x * dotP bt vst + x * dotP bt vst)
        (windowsep.mag b0 * (x * x) + windowsep.mag b0 * (y * y))
        (magSum bt * (x * x)
          + dotP (bt.map windowsep.mag) (List.zipWith (· * ·) vst vst))]
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
    (a + b) + (c + (m + nn)) = (m + a) + (c + (b + nn)) := by
  rw [BPair.add_add_comm a b c (m + nn), BPair.add_left_comm b m nn,
    BPair.add_add_comm a c m (b + nn), BPair.add_comm a m]

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
            rw [addShuffle (d0 * (x * x))
              (dotP dt (List.zipWith (· * ·) vs vs))
              (x * dotP b vs + x * dotP b vs) (magSum b * (x * x))
              (dotP (b.map windowsep.mag)
                (List.zipWith (· * ·) vs vs))] at h1
            refine ground.leB_congr_right (BPair.oneValue_symm hRHS) ?_
            exact ground.leB_trans h1
              (ground.leB_add hA (ground.leB_add (ground.leB_refl _) hIH2))

/-- The dominance comparison prices the quadratic form: the slack's
fold against the coordinates' squares sits at or below the form,
the peel telescoping on the comparison
(`thm:decimation`(ii)'s display). -/
theorem dom_quad (S : Mat) (n : Nat) (d : List BPair)
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
        (ground.getAt BPair.unit (ground.getAt [] S j) i) := by
    intro i j hi hj
    have e := poly.oneValue_getAt j
      (matOne_entries S (transposeM S) hsym i (by rw [hSl]; exact hi))
    rw [getAt_transposeM BPair.unit S hSr i j hi
      (by rw [hSl]; exact hj)] at e
    exact e
  refine ground.leB_congr (BPair.oneValue_symm (dotN_read d _))
    (BPair.oneValue_symm (quadP_read S v)) ?_
  exact dom_quadGo n S d v hSl hSr hd hv hsymE hdom

/-- Every split of a dominance-clear datum reads the upper side
throughout: an occupied count's witness prices the form strictly
below the sum's unit, against the comparison's own pricing. -/
theorem dom_psd {n : Nat} (S : Mat) (sp : Split n)
    (hdom : domAt S) (h : splitRead S sp) : psdAt sp := by
  have hSl : S.length = n := sqAt_len h.1
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hpos =>
    obtain ⟨u, hu, hlt⟩ := rev_witness S sp h hpos
    have hdomN : ∀ i, i < n →
        offFold i (ground.getAt [] S i)
            + ground.getAt BPair.unit (List.replicate n BPair.unit) i
          ≤ ground.getAt BPair.unit (ground.getAt [] S i) i := by
      intro i hi
      rw [ground.getAt_replicate_self BPair.unit n i]
      refine ground.leB_congr_left
        (BPair.oneValue_symm (BPair.add_unit _)) ?_
      have h0 := domGo_read 0 S i hdom (by rw [hSl]; exact hi)
      rw [Nat.zero_add] at h0
      exact h0
    have hprice := dom_quad S n (List.replicate n BPair.unit) h.1
      (ground.length_replicate BPair.unit n)
      (splitRead_symm S sp h) hdomN u hu
    exact absurd hlt (ground.leB_not_lt
      (ground.leB_congr_left
        (dotN_nullL (List.replicate n BPair.unit)
          (List.zipWith (· * ·) u u) (poly.unitTail_replicate n))
        hprice))

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

instance {n o1 o2 : Nat} (diag off : List Mat) (Xs Rs : List MatQ)
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

instance (diag off diag' off' : List Mat)
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

instance {oD : Nat} (sq : poly.Poly) (spHD : Split oD) (c : Pos)
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

instance {o oD : Nat} (R : DivRecord o oD) :
    Decidable (recordRead R) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ ∧ _ = _ ∧ _ = _))

end decimation
