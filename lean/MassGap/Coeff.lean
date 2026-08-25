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

/-- The six-member reshuffle the row's expansion collects at: the
head's terms and the tail's terms each land once. -/
private theorem addShuffle (A B C D E F : BPair) :
    A + B + (C + D) + ((E + F) + (E + F))
      = A + C + (E + E) + (B + D + (F + F)) := by
  rw [BPair.add_add_comm A B C D, BPair.add_add_comm E F E F,
    BPair.add_add_comm (A + C) (B + D) (E + E) (F + F)]

/-- The seven-member reshuffle the assembly collects at: the two
squares' cross terms pair off, the tail's square joins the tail's
cross fold, and the head's terms stand together. -/
private theorem addShuffle7 (E F G H I J K : BPair) :
    E + F + G + (H + I + J + K)
      = E + H + I + (F + K) + (G + J) := by
  rw [BPair.add_assoc (H + I) J K, BPair.add_comm J K,
    ← BPair.add_assoc (H + I) K J,
    BPair.add_add_comm (E + F) G (H + I + K) J,
    BPair.add_add_comm E F (H + I) K, ← BPair.add_assoc E H I]

/-- The row's closed form: the head's squares against the tail's
self-pairings with the doubled swapped cross fold. -/
private def rowForm (a b : BPair) (u v : List BPair) : BPair :=
  a * a * dotP v v + dotP u u * (b * b)
    + ((a * b * dotP u v).swap + (a * b * dotP u v).swap)

/-- The closed form's head split: one place's cross square peels
off the closed form exactly. -/
private theorem rowForm_cons (a b x y : BPair) (u v : List BPair) :
    rowForm a b (x :: u) (y :: v)
      = (a * y + (x * b).swap) * (a * y + (x * b).swap)
        + rowForm a b u v := by
  show a * a * (y * y + dotP v v) + (x * x + dotP u u) * (b * b)
      + ((a * b * (x * y + dotP u v)).swap
        + (a * b * (x * y + dotP u v)).swap)
    = (a * y + (x * b).swap) * (a * y + (x * b).swap)
      + (a * a * dotP v v + dotP u u * (b * b)
        + ((a * b * dotP u v).swap + (a * b * dotP u v).swap))
  rw [BPair.left_distrib (a * a) (y * y) (dotP v v),
    BPair.right_distrib (x * x) (dotP u u) (b * b),
    BPair.left_distrib (a * b) (x * y) (dotP u v),
    ← BPair.swap_add (a * b * (x * y)) (a * b * dotP u v),
    BPair.sq_expand_swap (a * y) (x * b),
    BPair.mul_mul_mul_comm a y a y, BPair.mul_mul_mul_comm x b x b,
    BPair.mul_comm x b, BPair.mul_mul_mul_comm a y b x, BPair.mul_comm y x]
  exact addShuffle (a * a * (y * y)) (a * a * dotP v v)
    (x * x * (b * b)) (dotP u u * (b * b))
    (a * b * (x * y)).swap (a * b * dotP u v).swap

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
    rw [rowForm_cons a b x y u v,
      ← BPair.add_assoc acc
        ((a * y + (x * b).swap) * (a * y + (x * b).swap))
        (rowForm a b u v)]
    exact BPair.oneValue_refl _

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
        (a * b * S).swap (a * b * S).swap,
      BPair.add_comm (a * b * S) (a * b * S).swap]
    exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.swap_add_null (BPair.oneValue_refl (a * b * S)))
        (BPair.swap_add_null (BPair.oneValue_refl (a * b * S))))
      (BPair.unit_add BPair.unit)
  rw [BPair.sq_expand (a * b) S, BPair.mul_mul_mul_comm a b a b,
    BPair.right_distrib (a * a) P (b * b + Q),
    BPair.left_distrib (a * a) (b * b) Q,
    BPair.left_distrib P (b * b) Q,
    ← BPair.add_assoc (a * a * (b * b) + a * a * Q) (P * (b * b))
      (P * Q)]
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr hrow (BPair.oneValue_refl K))) ?_
  rw [addShuffle7 (a * a * (b * b)) (S * S) (a * b * S + a * b * S)
    (a * a * Q) (P * (b * b))
    ((a * b * S).swap + (a * b * S).swap) K]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl _) hcar) hnull) ?_
  exact BPair.add_unit _

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

end coeff
