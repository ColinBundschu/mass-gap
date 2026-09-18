import MassGap.Elim
/-!
`con:coeff` — the coefficient carrier's pairing at the coordinate
folds: the squared Cauchy--Schwarz as the displayed identity, its
gap the cross squares' fold.  `crossRow` is one head's cross
squares against the zipped tails, `crossSq` the fold over the
place pairs `i < j`, and `dotP_sq_split` the display — the squared
pairing joined to the cross squares reads the self-pairings'
product, the cross monomials entering each member once per place
pair with the one collection at the balance read.  `dotP_sq_le` is
the order's read back: the squared pairing sits at or below the
self-pairings' product, the cross fold's side read
(`elim.side_add` at `ground.sq_side`) against the identity.  The
cut-datum tier sits at `lem:loopcap`
(`loopcap.cutSq`/`cutCap`/`cutForm`), the display consumed at the
joined slot lists; the display's instances at committed lists,
the equality case at proportional data, and the length
hypothesis's own refusal are the check module's.
-/

namespace coeff
open ground elim

/-- One row's cross squares: the head pair against the zipped
tails, the display's `i < j` terms at a fixed first place. -/
def crossRow (a b : BPair) (u v : List BPair) : BPair :=
  (List.zipWith (fun x y =>
    (a * y + (x * b).swap) * (a * y + (x * b).swap)) u v).foldl
    (fun acc g => acc + g) BPair.unit

/-- The cross squares' fold over the place pairs. -/
def crossSq : List BPair → List BPair → BPair
  | [], _ => BPair.unit
  | _ :: _, [] => BPair.unit
  | a :: u, b :: v => crossRow a b u v + crossSq u v

/-! The row's own collection: a row's cross squares expand to the
head's squares against the tail's self-pairings with the doubled
swapped cross fold, so the row is a closed form in the tail's
three pairings (`rowForm`) and the assembly reads it once. -/

/-- The row's closed form: the head's squares against the tail's
self-pairings with the doubled swapped cross fold. -/
private def rowForm (a b : BPair) (u v : List BPair) : BPair :=
  a * a * dotP v v + dotP u u * (b * b)
    + ((a * b * dotP u v).swap + (a * b * dotP u v).swap)

/-- The closed form's head split: one place's cross square peels
off the closed form exactly. -/
private theorem rowForm_cons (a b x y : BPair) (u v : List BPair) :
    (rowForm a b (x :: u) (y :: v)).oneValue
      ((a * y + (x * b).swap) * (a * y + (x * b).swap)
        + rowForm a b u v) := by
  show (a * a * (y * y + dotP v v) + (x * x + dotP u u) * (b * b)
      + ((a * b * (x * y + dotP u v)).swap
        + (a * b * (x * y + dotP u v)).swap)).oneValue
    ((a * y + (x * b).swap) * (a * y + (x * b).swap)
      + (a * a * dotP v v + dotP u u * (b * b)
        + ((a * b * dotP u v).swap + (a * b * dotP u v).swap)))
  rw [BPair.sq_expand_swap (a * y) (x * b)]
  have hS : ((a * b * (x * y + dotP u v)).swap).oneValue
      ((a * y * (x * b)).swap + (a * b * dotP u v).swap) := by
    rw [BPair.left_distrib (a * b) (x * y) (dotP u v),
      ← BPair.swap_add (a * b * (x * y)) (a * b * dotP u v)]
    exact BPair.add_congr (swap_congr (polEqB [a, b, x, y]
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3))))
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 1))))
        (by decide +kernel)))
      (BPair.oneValue_refl _)
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr hS hS)) ?_
  exact polEqB [a, b, x, y, dotP v v, dotP u u, (a * y * (x * b)).swap,
      (a * b * dotP u v).swap]
    (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.add (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4)))) (Pol.mul (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 5))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))) (Pol.add (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 7))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 7)))))
    (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3)))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 1))))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 6)))) (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 4))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))) (Pol.add (Pol.mon (Mon.var 7)) (Pol.mon (Mon.var 7)))))
    (by decide +kernel)

/-- The row's fold against its seed: the accumulating fold reads
the seed joined to the closed form, the place counts matched. -/
private theorem crossRow_fold (a b : BPair) : ∀ (u v : List BPair),
    u.length = v.length → ∀ acc : BPair,
    ((List.zipWith (fun x y =>
        (a * y + (x * b).swap) * (a * y + (x * b).swap)) u v).foldl
      (fun acc g => acc + g) acc).oneValue (acc + rowForm a b u v)
  | [], [], _, acc => by
    have h1 : (a * a * BPair.unit).oneValue BPair.unit :=
      BPair.mul_unit _
    have h2 : (BPair.unit * (b * b)).oneValue BPair.unit :=
      BPair.unit_mul _
    have h3 : ((a * b * BPair.unit).swap).oneValue BPair.unit :=
      ground.swap_congr (BPair.mul_unit (a * b))
    have hz : (rowForm a b [] []).oneValue BPair.unit :=
      BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.add_congr h1 h2)
            (BPair.unit_add BPair.unit))
          (BPair.oneValue_trans (BPair.add_congr h3 h3)
            (BPair.unit_add BPair.unit)))
        (BPair.unit_add BPair.unit)
    show acc.oneValue (acc + rowForm a b [] [])
    exact BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl acc) hz)
      (BPair.add_unit acc))
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | x :: u, y :: v, h, acc => by
    have hst : u.length = v.length := Nat.succ.inj h
    show ((List.zipWith (fun x y =>
          (a * y + (x * b).swap) * (a * y + (x * b).swap)) u v).foldl
        (fun acc g => acc + g)
        (acc + (a * y + (x * b).swap)
          * (a * y + (x * b).swap))).oneValue
      (acc + rowForm a b (x :: u) (y :: v))
    refine BPair.oneValue_trans
      (crossRow_fold a b u v hst
        (acc + (a * y + (x * b).swap) * (a * y + (x * b).swap))) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc acc
      ((a * y + (x * b).swap) * (a * y + (x * b).swap)) (rowForm a b u v))) ?_
    exact BPair.add_congr (BPair.oneValue_refl acc)
      (BPair.oneValue_symm (rowForm_cons a b x y u v))

/-! The sides: the cross fold is a fold of squares, so its second
member sits at or below its first at every list pair, and the fold
against the sum's unit is the order's read. -/

/-- An accumulating fold of upper-side terms keeps the side. -/
private theorem foldl_side (f : BPair → BPair → BPair)
    (hf : ∀ x y : BPair, (f x y).snd ≤ (f x y).fst) :
    ∀ (u v : List BPair) (acc : BPair), acc.snd ≤ acc.fst →
      ((List.zipWith f u v).foldl (fun acc g => acc + g) acc).snd
        ≤ ((List.zipWith f u v).foldl (fun acc g => acc + g) acc).fst
  | [], _, _, hacc => hacc
  | _ :: _, [], _, hacc => hacc
  | x :: u, y :: v, acc, hacc =>
    foldl_side f hf u v (acc + f x y) (side_add hacc (hf x y))

/-- The row's side: a fold of squares. -/
private theorem crossRow_side (a b : BPair) (u v : List BPair) :
    (crossRow a b u v).snd ≤ (crossRow a b u v).fst :=
  foldl_side (fun x y =>
      (a * y + (x * b).swap) * (a * y + (x * b).swap))
    (fun x y => sq_side (a * y + (x * b).swap)) u v BPair.unit
    (Or.inl rfl)

/-- The cross fold's side: the rows' sides summed. -/
private theorem crossSq_side : ∀ u v : List BPair,
    (crossSq u v).snd ≤ (crossSq u v).fst
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inl rfl
  | a :: u, b :: v =>
    side_add (crossRow_side a b u v) (crossSq_side u v)

/-- The assembly at one place: the head's cross terms pair off
against the row's swapped ones, the tail's square joins the tail's
cross fold at the stated read, and the head's squares fill the
product's remaining members. -/
private theorem sq_step (a b S P Q Cr K : BPair)
    (hrow : Cr.oneValue (a * a * Q + P * (b * b)
      + ((a * b * S).swap + (a * b * S).swap)))
    (hcar : (S * S + K).oneValue (P * Q)) :
    ((a * b + S) * (a * b + S) + (Cr + K)).oneValue
      ((a * a + P) * (b * b + Q)) := by
  have hnull : ((a * b * S + a * b * S)
      + ((a * b * S).swap + (a * b * S).swap)).oneValue BPair.unit := by
    rw [BPair.add_add_comm (a * b * S) (a * b * S)
        (a * b * S).swap (a * b * S).swap]
    exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_swap_null (a * b * S))
        (BPair.add_swap_null (a * b * S)))
      (BPair.unit_add BPair.unit)
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr hrow (BPair.oneValue_refl K))) ?_
  refine BPair.oneValue_trans (polEqB [a, b, S, P, Q, K, (a * b * S).swap]
    (Pol.add (Pol.mul (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2)))) (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 4))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 6)))) (Pol.mon (Mon.var 5))))
    (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1)))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 4)))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))) (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 5)))) (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2)))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 6)))))
    (by decide +kernel)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl _) hcar) hnull) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact polEqB [a, b, P, Q]
    (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1)))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 3)))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3))))
    (Pol.mul (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 3))))
    (by decide +kernel)

/-- The display: the squared pairing joined to the cross squares'
fold reads the self-pairings' product, the cross monomials
entering each member once per place pair. -/
theorem dotP_sq_split : ∀ (u v : List BPair), u.length = v.length →
    (dotP u v * dotP u v + crossSq u v).oneValue
      (dotP u u * dotP v v)
  | [], [], _ => BPair.add_unit (BPair.unit * BPair.unit)
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: s, b :: t, h => by
    have hst : s.length = t.length := Nat.succ.inj h
    have hrow : (crossRow a b s t).oneValue (rowForm a b s t) :=
      BPair.oneValue_trans (crossRow_fold a b s t hst BPair.unit)
        (BPair.unit_add _)
    exact sq_step a b (dotP s t) (dotP s s) (dotP t t)
      (crossRow a b s t) (crossSq s t) hrow
      (dotP_sq_split s t hst)

/-- The order's read back: the squared pairing sits at or below
the self-pairings' product, the cross fold's side the witness. -/
theorem dotP_sq_le (u v : List BPair) (h : u.length = v.length) :
    ¬ (dotP u u * dotP v v < dotP u v * dotP u v) :=
  leB_not_lt (leB_congr_right (dotP_sq_split u v h)
    (leB_congr_left (BPair.add_unit (dotP u v * dotP u v))
      (leB_add (leB_refl (dotP u v * dotP u v))
        (unitLeOfSide (crossSq_side u v)))))

/-- The squared Cauchy--Schwarz at the count: a weighted range fold's
square sits at or below its occupancy fold, one per weight off the
sum's unit, against the products' squares' fold, the pairing's read
at the indicator list against the products' list. -/
theorem bsum_sq_le_count (P : Nat) (k w : Nat → BPair) :
    bsum (fun p => k p * w p) (List.range P) * bsum (fun p => k p * w p) (List.range P)
      ≤ bsum (fun p => if (k p).oneValue BPair.unit then BPair.unit else BPair.ofNat 1)
          (List.range P)
        * bsum (fun p => (k p * w p) * (k p * w p)) (List.range P) := by
  let u : List BPair := (List.range P).map (fun p =>
    if (k p).oneValue BPair.unit then BPair.unit else BPair.ofNat 1)
  let v : List BPair := (List.range P).map (fun p => k p * w p)
  have hul : u.length = P := by
    show ((List.range P).map _).length = P
    rw [ground.length_map, ground.length_range]
  have hvl : v.length = P := by
    show ((List.range P).map _).length = P
    rw [ground.length_map, ground.length_range]
  have hu : ∀ p, p < P → getAt BPair.unit u p
      = (if (k p).oneValue BPair.unit then BPair.unit else BPair.ofNat 1) := by
    intro p hp
    show getAt BPair.unit ((List.range P).map _) p = _
    rw [ground.getAt_map 0 BPair.unit _ (List.range P) p (by rw [ground.length_range]; exact hp),
      ground.getAt_range P p hp]
  have hv : ∀ p, p < P → getAt BPair.unit v p = k p * w p := by
    intro p hp
    show getAt BPair.unit ((List.range P).map _) p = _
    rw [ground.getAt_map 0 BPair.unit _ (List.range P) p (by rw [ground.length_range]; exact hp),
      ground.getAt_range P p hp]
  have huv : (dotP u v).oneValue (bsum (fun p => k p * w p) (List.range P)) := by
    rw [dotP_fold P u v hul hvl]
    refine bsum_congr_range_ov _ _ P (fun p hp => ?_)
    rw [hu p hp, hv p hp]
    by_cases hk : (k p).oneValue BPair.unit
    · rw [if_pos hk]
      exact BPair.oneValue_trans (BPair.unit_mul _)
        (BPair.oneValue_symm (BPair.oneValue_trans (BPair.mul_congr_left hk) (BPair.unit_mul _)))
    · rw [if_neg hk]
      exact BPair.ofNat_one_mul _
  have huu : (dotP u u).oneValue
      (bsum (fun p => if (k p).oneValue BPair.unit then BPair.unit else BPair.ofNat 1)
        (List.range P)) := by
    rw [dotP_fold P u u hul hul]
    refine bsum_congr_range_ov _ _ P (fun p hp => ?_)
    rw [hu p hp]
    by_cases hk : (k p).oneValue BPair.unit
    · rw [if_pos hk]
      exact BPair.unit_mul _
    · rw [if_neg hk]
      exact BPair.ofNat_one_mul _
  have hvv : (dotP v v).oneValue
      (bsum (fun p => (k p * w p) * (k p * w p)) (List.range P)) := by
    rw [dotP_fold P v v hvl hvl]
    refine bsum_congr_range_ov _ _ P (fun p hp => ?_)
    rw [hv p hp]
    exact BPair.oneValue_refl _
  have hcs := leB_of_not_lt (dotP_sq_le u v (hul.trans hvl.symm))
  exact leB_congr (BPair.mul_congr huv huv) (BPair.mul_congr huu hvv) hcs

/-- The squared pairing at the fold read: two matched lists' squared
pairing sits at or below their self-pairings' product, `dotP_sq_le`
read at the fold. -/
theorem dotN_sq_le (u v : List BPair) (h : u.length = v.length) :
    dotN u v * dotN u v ≤ dotN u u * dotN v v :=
  ground.leB_congr
    (BPair.oneValue_symm (BPair.mul_congr (dotN_read u v) (dotN_read u v)))
    (BPair.oneValue_symm (BPair.mul_congr (dotN_read u u) (dotN_read v v)))
    (ground.leB_of_not_lt (dotP_sq_le u v h))

/-- `con:coeff`'s joined square: a generator action joined to a
coefficient multiplication at its own involution image squares to
the generator's square, the multiplier's square, and the balance
partner of the multiplication by the generator's read of the
multiplier, the commutator's read — the generator's transpose its
memberwise swap and the multiplier's its own, the pair's scale
absorbed into the generator. -/
theorem joined_sq (n : Nat) (X G : Mat) (hX : sqAt X n) (hG : sqAt G n)
    (hn : 0 < n)
    (hXa : matOneValue (transposeM X) (matSwap X))
    (hGs : matOneValue (transposeM G) G) :
    matOneValue (matMul (transposeM (matAdd X G)) (matAdd X G))
      (matAdd (matAdd (matMul (transposeM X) X) (matMul G G))
        (matAdd (matSwap (matMul X G)) (matMul G X))) := by
  have hXr : rowsLen n X := rowsLen_of_sqAt hX
  have hGr : rowsLen n G := rowsLen_of_sqAt hG
  have hXl : X.length = n := sqAt_len hX
  have hGl : G.length = n := sqAt_len hG
  have hX0 : 0 < X.length := hXl ▸ hn
  have hG0 : 0 < G.length := hGl ▸ hn
  have hXG : X.length = G.length := by rw [hXl, hGl]
  have hSl : (matAdd X G).length = n := by
    rw [length_matAdd X G hXG, hXl]
  have hXtr : rowsLen n (transposeM X) := by
    have h := rowsLen_transposeM X
    rw [hXl] at h
    exact h
  have hGtr : rowsLen n (transposeM G) := by
    have h := rowsLen_transposeM G
    rw [hGl] at h
    exact h
  have hStr : rowsLen n (transposeM (matAdd X G)) := by
    have h := rowsLen_transposeM (matAdd X G)
    rw [hSl] at h
    exact h
  have hXtl : (transposeM X).length = n := length_transposeM X hXr hX0
  have hGtl : (transposeM G).length = n := length_transposeM G hGr hG0
  have hT : transposeM (matAdd X G)
      = matAdd (transposeM X) (transposeM G) :=
    transposeM_matAdd X G hXr hGr hXG hX0
  rw [hT]
  have h1 : matOneValue
      (matMul (matAdd (transposeM X) (transposeM G)) (matAdd X G))
      (matAdd (matMul (transposeM X) (matAdd X G))
        (matMul (transposeM G) (matAdd X G))) :=
    matMul_addL n (matAdd X G) hStr (transposeM X) (transposeM G)
      hXtr hGtr
  have h2 : matOneValue (matMul (transposeM X) (matAdd X G))
      (matAdd (matMul (transposeM X) X) (matMul (transposeM X) G)) :=
    matMul_addR X G hXr hGr hXG hX0 (transposeM X)
      (by rw [hXl]; exact hXtr)
  have h3 : matOneValue (matMul (transposeM G) (matAdd X G))
      (matAdd (matMul (transposeM G) X) (matMul (transposeM G) G)) :=
    matMul_addR X G hXr hGr hXG hX0 (transposeM G)
      (by rw [hXl]; exact hGtr)
  have h4 : matOneValue (matMul (transposeM X) G)
      (matSwap (matMul X G)) := by
    rw [← matMul_swapL]
    exact matMul_congrL _ _ G hXa
  have h5 : matOneValue (matMul (transposeM G) X) (matMul G X) :=
    matMul_congrL _ _ X hGs
  have h6 : matOneValue (matMul (transposeM G) G) (matMul G G) :=
    matMul_congrL _ _ G hGs
  -- row widths of every summand
  have rXtX : rowsLen n (matMul (transposeM X) X) :=
    rowsLen_matMul_of (transposeM X) X (fun _ => hX0) hXr
  have rXtG : rowsLen n (matMul (transposeM X) G) :=
    rowsLen_matMul_of (transposeM X) G (fun _ => hG0) hGr
  have rGtX : rowsLen n (matMul (transposeM G) X) :=
    rowsLen_matMul_of (transposeM G) X (fun _ => hX0) hXr
  have rGtG : rowsLen n (matMul (transposeM G) G) :=
    rowsLen_matMul_of (transposeM G) G (fun _ => hG0) hGr
  have rGX : rowsLen n (matMul G X) :=
    rowsLen_matMul_of G X (fun _ => hX0) hXr
  have rGG : rowsLen n (matMul G G) :=
    rowsLen_matMul_of G G (fun _ => hG0) hGr
  have sXG : sqAt (matMul X G) n :=
    sqAt_of (by rw [length_matMul, hXl])
      (rowsLen_matMul_of X G (fun _ => hG0) hGr)
  have rSw : rowsLen n (matSwap (matMul X G)) :=
    rowsLen_of_sqAt (sqAt_matSwap n (matMul X G) sXG)
  have rXtS : rowsLen n (matMul (transposeM X) (matAdd X G)) :=
    rowsLen_matMul_of (transposeM X) (matAdd X G)
      (fun _ => hSl ▸ hn) (rowsLen_matAdd n X G hXr hGr)
  have rGtS : rowsLen n (matMul (transposeM G) (matAdd X G)) :=
    rowsLen_matMul_of (transposeM G) (matAdd X G)
      (fun _ => hSl ▸ hn) (rowsLen_matAdd n X G hXr hGr)
  have hA : matOneValue
      (matMul (matAdd (transposeM X) (transposeM G)) (matAdd X G))
      (matAdd (matAdd (matMul (transposeM X) X) (matMul (transposeM X) G))
        (matAdd (matMul (transposeM G) X) (matMul (transposeM G) G))) :=
    matOne_trans h1
      (matAdd_cong2 n _ _ _ _ rXtS rGtS
        (rowsLen_matAdd n _ _ rXtX rXtG) (rowsLen_matAdd n _ _ rGtX rGtG)
        h2 h3)
  have hB : matOneValue
      (matAdd (matAdd (matMul (transposeM X) X) (matMul (transposeM X) G))
        (matAdd (matMul (transposeM G) X) (matMul (transposeM G) G)))
      (matAdd (matAdd (matMul (transposeM X) X) (matSwap (matMul X G)))
        (matAdd (matMul G X) (matMul G G))) :=
    matAdd_cong2 n _ _ _ _
      (rowsLen_matAdd n _ _ rXtX rXtG) (rowsLen_matAdd n _ _ rGtX rGtG)
      (rowsLen_matAdd n _ _ rXtX rSw) (rowsLen_matAdd n _ _ rGX rGG)
      (matAdd_cong2 n _ _ _ _ rXtX rXtG rXtX rSw (matOne_refl _) h4)
      (matAdd_cong2 n _ _ _ _ rGtX rGtG rGX rGG h5 h6)
  have hre : matAdd (matAdd (matMul (transposeM X) X) (matSwap (matMul X G)))
        (matAdd (matMul G X) (matMul G G))
      = matAdd (matAdd (matMul (transposeM X) X) (matMul G G))
        (matAdd (matSwap (matMul X G)) (matMul G X)) := by
    rw [matAdd_assoc (matMul (transposeM X) X) (matSwap (matMul X G)),
      matAdd_comm (matMul G X) (matMul G G),
      ← matAdd_assoc (matSwap (matMul X G)) (matMul G G) (matMul G X),
      matAdd_comm (matSwap (matMul X G)) (matMul G G),
      matAdd_assoc (matMul G G) (matSwap (matMul X G)) (matMul G X),
      ← matAdd_assoc (matMul (transposeM X) X) (matMul G G)]
  rw [← hre]
  exact matOne_trans hA hB

end coeff
