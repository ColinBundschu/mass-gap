import MassGap.Steinberg
import MassGap.C2hat
import MassGap.Weyldim
import MassGap.Dualread
/-!
`con:labels` — the label set: two shapes are one label when they
differ by full columns, each label reading one reduced shape (the
column multiset at an unoccupied full-column key, at most `r` rows
deep); `reduce` withdraws the full columns, the class's one
representative, and `addFulls` adds a stated column count back at
the deepest key.

The data descend to labels.  The dimension is one value at the
class (`dimOf_class`): a full column maps the block's span member
for member, so the span's count is the class's own
(`dualread.spanAddFull` at `cor:weyldim`'s span read).  The fusion
count descends at matched degrees,
`N^{c+(1^{d_f})}_{a+(1^{d_f}), b} = N^c_{ab}`: the label count
`countL` reads at the matched-degree lift — the degree gap's full
columns entering on the deficient side at the divisibility guard,
the count the sum's unit off the matched classes — it is the block
count outright where the degrees already match (`countL_matched`,
`cor:steinberg`'s fast fold at `steinberg.count_fusion`), the
reduced target reads the shape count at the matched degrees
(`countL_reduce`), and it
is one value along the class in each argument (`countL_bumpA`,
`countL_bumpB`, `countL_bumpC`): the moved column enters the lift's
own step at a shifted guard and cofactor, and at the matched
degrees it is the mapped span's descent
(`dualread.fusionCount_addFull`) with the factors' exchange
(`blockcount.fusionCount_comm`) carrying the second argument's, the
count into a target without a full column vacant at either factor's
own.

The dual label is the complement shape's class, the occupancy
reversal off the full-column key (`dualL`), an involution at the
representative (`dualL_dualL`); and the full columns' join of the
two row lists reads it exactly — a constant join puts the reduced
shape at the dual label (`join_dualL`), and at the dual label the
join is the constant at the degrees' quotient (`dualL_join`),
`lem:dualread`(iii)'s condition at `con:labels`' data.  The full
columns' own class is the unit label (`unitL`).  The Casimir read
descends, `def:c2hat`'s cleared bracket one value at the class
(`c2ClassRead`, `c2Class_all`); and the Cartan count sharpens to an
equality on shapes, `N^{a+b}_{ab} = 1`, the stated read
`cartanRead`, its generals `cartan_eq` at the shapes and
`cartan_all` at the read: the content-`a+b` summand of the product
is the two tops' own line, the stated pair list at the union's row
list one member against `lem:blockcount`(iii)'s occupied floor,
since a content of the first block whose complement in the union
is a content of the second sits at and below the first shape's top
at once (`lem:lowerspan`'s dominance clause, the prefix sums
squeezed against the entrywise join).
-/
namespace labels
open ground places

/-- The reduced shape, the class's one representative: the
full-column key read to the unit occupancy. -/
def reduce (s : Shape) : Shape :=
  match s.reverse with
  | [] => []
  | _ :: t => t.reverse ++ [0]

/-- The dual label, the complement shape's class: the occupancy
reversal off the full-column key. -/
def dualL (s : Shape) : Shape :=
  match s.reverse with
  | [] => []
  | _ :: t => t ++ [0]

/-- The unit label, the full columns' own class: the unit shape. -/
def unitL (d : Nat) : Shape := List.replicate d 0

/-- The reduction at the split-off last member: the full-column
key read to the unit occupancy. -/
theorem reduce_snoc (s : Shape) (a : Nat) :
    reduce (s ++ [a]) = s ++ [0] := by
  unfold reduce
  rw [ground.reverse_snoc s a]
  show s.reverse.reverse ++ [0] = s ++ [0]
  rw [ground.reverse_reverse s]

/-- The dual at the split-off last member: the occupancy reversal
off the full-column key. -/
theorem dualL_snoc (s : Shape) (a : Nat) :
    dualL (s ++ [a]) = s.reverse ++ [0] := by
  unfold dualL
  rw [ground.reverse_snoc s a]

/-- The reduction keeps the width. -/
theorem length_reduce : ∀ s : Shape, (reduce s).length = s.length
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, hl⟩ =>
      rw [hs, reduce_snoc s' a, ground.length_append s' [0],
        ground.length_append s' [a]]
      rfl

/-- The dual keeps the width. -/
theorem length_dualL : ∀ s : Shape, (dualL s).length = s.length
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, hl⟩ =>
      rw [hs, dualL_snoc s' a, ground.length_append s'.reverse [0],
        ground.length_reverse s', ground.length_append s' [a]]
      rfl

/-- The full columns added at the deepest key: the class's own move
by a stated column count, the label's representative shifted along
the class. -/
def addFulls (m : Nat) (s : Shape) : Shape :=
  match s.reverse with
  | [] => []
  | a :: t => ((a + m) :: t).reverse

private theorem addFulls_snoc (m : Nat) (s : Shape) (x : Nat) :
    addFulls m (s ++ [x]) = s ++ [x + m] := by
  show (match (s ++ [x]).reverse with
    | [] => []
    | a :: t => ((a + m) :: t).reverse) = s ++ [x + m]
  rw [ground.reverse_snoc s x]
  show ((x + m) :: s.reverse).reverse = s ++ [x + m]
  rw [ground.reverse_cons (x + m) s.reverse, ground.reverse_reverse s]

private theorem addFulls_zero : ∀ s : Shape, addFulls 0 s = s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', y, hs, _⟩ =>
      rw [hs, addFulls_snoc 0 s' y, Nat.add_zero]

private theorem length_addFulls (m : Nat) : ∀ s : Shape,
    (addFulls m s).length = s.length
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', y, hs, _⟩ =>
      rw [hs, addFulls_snoc m s' y, ground.length_append s' [y + m],
        ground.length_append s' [y]]
      rfl

private theorem addFulls_succ (m : Nat) : ∀ s : Shape,
    addFulls (m + 1) s = ground.bumpAt (s.length - 1) (addFulls m s)
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', y, hs, _⟩ =>
      have hl : (s' ++ [y]).length - 1 = s'.length := by
        rw [ground.length_append s' [y]]
        rfl
      rw [hs, addFulls_snoc (m + 1) s' y, hl, addFulls_snoc m s' y,
        ground.bumpAt_snoc s' (y + m), Nat.add_assoc y m 1]

private theorem addFulls_bumped (m : Nat) : ∀ s : Shape,
    addFulls m (ground.bumpAt (s.length - 1) s) = addFulls (m + 1) s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', y, hs, _⟩ =>
      have hl : (s' ++ [y]).length - 1 = s'.length := by
        rw [ground.length_append s' [y]]
        rfl
      rw [hs, hl, ground.bumpAt_snoc s' y, addFulls_snoc m s' (y + 1),
        addFulls_snoc (m + 1) s' y, Nat.add_assoc y 1 m,
        Nat.add_comm 1 m]

private theorem divZeroL : ∀ n : Nat, 0 / n = 0
  | 0 => rfl
  | e + 1 => by
    have h := ground.divMulSelf 0 (e + 1) (Nat.succ_pos e)
    rw [Nat.zero_mul] at h
    exact h

/-- The label fusion count at the matched-degree lift: the degree
gap's full columns enter on the deficient side at the divisibility
guard (`con:labels`' descent,
`N^{c+(1^{d_f})}_{a+(1^{d_f}), b} = N^c_{ab}`), the count read
through the fast fold and the sum's unit off the matched
classes. -/
def countL (a b c : Shape) : Nat :=
  let k := degree a + degree b
  let kc := degree c
  if k < kc then
    if (kc - k) % a.length == 0 then
      steinberg.count (addFulls ((kc - k) / a.length) a) b c
    else 0
  else
    if (k - kc) % a.length == 0 then
      steinberg.count a b (addFulls ((k - kc) / a.length) c)
    else 0

/-- The full columns join back at the withdrawn key: the added
count is the last key's own occupancy. -/
private theorem addFulls_snocZ (s : Shape) (j : Nat) :
    addFulls j (s ++ [0]) = s ++ [j] := by
  rw [addFulls_snoc j s 0, Nat.zero_add j]

/-- The label count at the split-off last key: the degree gap is
the withdrawn column's boxes and the lift restores it. -/
private theorem countL_reduce_snoc (a b s : Shape) (j : Nat)
    (hca : (s ++ [j]).length = a.length)
    (hk : degree (s ++ [j]) = degree a + degree b) :
    countL a b (reduce (s ++ [j])) = steinberg.count a b (s ++ [j]) := by
  have hn : s.length + 1 = a.length := by
    rw [← hca, ground.length_append s [j]]
    exact rfl
  have hl : 0 < a.length := by
    rw [← hn]
    exact Nat.succ_pos s.length
  have hkc : degree (s ++ [0]) = degree s := by
    rw [degree_snoc s 0, Nat.zero_mul (s.length + 1), Nat.add_zero]
  have hsum : degree (s ++ [0]) + j * a.length = degree a + degree b := by
    rw [hkc, ← hn, ← degree_snoc s j]
    exact hk
  have hle : degree (s ++ [0]) ≤ degree a + degree b := by
    rw [← hsum]
    exact Nat.le_add_right _ _
  have hgap : degree a + degree b - degree (s ++ [0]) = j * a.length := by
    rw [← hsum, Nat.add_comm (degree (s ++ [0])) (j * a.length),
      ground.addSubSelfR (j * a.length) (degree (s ++ [0]))]
  rw [reduce_snoc s j]
  show (if degree a + degree b < degree (s ++ [0]) then
        (if (degree (s ++ [0]) - (degree a + degree b)) % a.length == 0 then
          steinberg.count
            (addFulls ((degree (s ++ [0]) - (degree a + degree b))
              / a.length) a) b (s ++ [0])
         else 0)
      else
        (if (degree a + degree b - degree (s ++ [0])) % a.length == 0 then
          steinberg.count a b
            (addFulls ((degree a + degree b - degree (s ++ [0]))
              / a.length) (s ++ [0]))
         else 0))
    = steinberg.count a b (s ++ [j])
  have hnlt : ¬ (degree a + degree b < degree (s ++ [0])) :=
    fun hlt => Nat.not_succ_le_self (degree a + degree b)
      (Nat.le_trans hlt hle)
  rw [if_neg hnlt, hgap, ground.modMulSelf j a.length,
    if_pos (show (((0 : Nat)) == 0) = true from rfl),
    ground.divMulSelf j a.length hl, addFulls_snocZ s j]

/-- The label count at the reduced target reads the shape count:
the degree gap is the withdrawn full columns' and the lift
restores them. -/
theorem countL_reduce (a b c : places.Shape) (hca : c.length = a.length)
    (hk : places.degree c = places.degree a + places.degree b) :
    countL a b (reduce c) = steinberg.count a b c := by
  cases c with
  | nil =>
    have hz : places.degree a + places.degree b = 0 := hk.symm
    have h0m : (0 : Nat) % a.length = 0 :=
      Eq.trans (congrArg (fun z => z % a.length)
        (Nat.zero_mul a.length).symm) (ground.modMulSelf 0 a.length)
    show (if places.degree a + places.degree b < 0 then
        (if (0 - (places.degree a + places.degree b)) % a.length == 0
          then steinberg.count
            (addFulls ((0 - (places.degree a + places.degree b))
              / a.length) a) b []
         else 0)
      else
        (if (places.degree a + places.degree b) % a.length == 0 then
          steinberg.count a b
            (addFulls ((places.degree a + places.degree b)
              / a.length) [])
         else 0))
      = steinberg.count a b []
    rw [if_neg (Nat.not_lt_zero (places.degree a + places.degree b)),
      hz, h0m, if_pos (show ((0 : Nat) == 0) = true from rfl)]
    exact rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s, j, hs, _⟩ =>
      rw [hs] at hca hk ⊢
      exact countL_reduce_snoc a b s j hca hk

/-- The label count at matched degrees is the block count: the
lift is vacant there, the count `cor:steinberg`'s own read at the
stated shapes (`con:labels`' descent at the matched degree). -/
theorem countL_matched (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length)
    (hdeg : degree a + degree b = degree c) :
    countL a b c = blockcount.fusionCount a b c := by
  have hnlt : ¬ degree a + degree b < degree c := by
    rw [hdeg]
    exact Nat.lt_irrefl (degree c)
  have hsub : degree a + degree b - degree c = 0 := by
    rw [hdeg]
    exact Nat.sub_self (degree c)
  show (if degree a + degree b < degree c then
      (if (degree c - (degree a + degree b)) % a.length == 0 then
        steinberg.count
          (addFulls ((degree c - (degree a + degree b)) / a.length) a) b c
      else 0)
    else
      (if (degree a + degree b - degree c) % a.length == 0 then
        steinberg.count a b
          (addFulls ((degree a + degree b - degree c) / a.length) c)
      else 0))
    = blockcount.fusionCount a b c
  rw [if_neg hnlt, hsub, ground.modZeroLeft a.length, divZeroL a.length,
    addFulls_zero c]
  show steinberg.count a b c = blockcount.fusionCount a b c
  exact steinberg.count_fusion a b c hba hca

/-- The dual label is an involution at the class representative:
the occupancy reversal twice reads the reduced shape
(`lem:dualread`(ii)'s complement at the class). -/
theorem dualL_dualL : ∀ s : Shape, dualL (dualL s) = reduce s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', y, hs, _⟩ =>
      rw [hs, dualL_snoc s' y, dualL_snoc s'.reverse 0,
        ground.reverse_reverse s', reduce_snoc s' y]

/-! The full-column join at the two row lists (`lem:dualread`(iii)'s
condition): the second shape's rows joined to the first's reversal
read one constant exactly where the two shapes are one label's dual
pair.  The join peels at the two ends at once — the first shape's
head enters the reversal's last entry and the second's last key
scales every row of the shorter join — so the constant's own
descent reads the shapes' entries against each other, the
representative's key at the mirrored key. -/

private theorem rowList_snoc : ∀ (s : Shape) (n : Nat),
    rowList (s ++ [n]) = (rowList s).map (fun x => x + n) ++ [n]
  | [], _ => rfl
  | x :: t, n => by
    show (x + ground.sumNat (t ++ [n])) :: rowList (t ++ [n])
      = ((x + ground.sumNat t + n) :: (rowList t).map (fun y => y + n))
        ++ [n]
    rw [ground.sumNat_append t [n], rowList_snoc t n]
    show (x + (ground.sumNat t + (n + 0)))
        :: ((rowList t).map (fun y => y + n) ++ [n])
      = (x + ground.sumNat t + n)
        :: ((rowList t).map (fun y => y + n) ++ [n])
    rw [Nat.add_zero n, ← Nat.add_assoc x (ground.sumNat t) n]

private theorem zipAdd_mapL (c : Nat) (x y : List Nat) :
    List.zipWith (fun u w => u + w) (x.map (fun u => u + c)) y
      = (List.zipWith (fun u w => u + w) x y).map (fun u => u + c) := by
  rw [ground.map_congr_all (fun u => u + c) (fun u => c + u)
      (fun u => Nat.add_comm u c) x,
    ground.zipWith_add_mapL c x y,
    ground.map_congr_all (fun u => c + u) (fun u => u + c)
      (fun u => Nat.add_comm c u)]

private theorem join_step (a b : Shape) (hba : b.length = a.length)
    (a0 bL : Nat) :
    List.zipWith (fun x y => x + y) (rowList (b ++ [bL]))
        ((rowList (a0 :: a)).reverse)
      = (List.zipWith (fun x y => x + y) (rowList b)
          ((rowList a).reverse)).map (fun x => x + bL)
        ++ [bL + ground.sumNat (a0 :: a)] := by
  have hlen : ((rowList b).map (fun x => x + bL)).length
      = ((rowList a).reverse).length := by
    rw [ground.length_map, ground.length_reverse,
      places.length_rowList, places.length_rowList, hba]
  show List.zipWith (fun x y => x + y) (rowList (b ++ [bL]))
      ((a0 + ground.sumNat a) :: rowList a).reverse = _
  rw [rowList_snoc b bL,
    ground.reverse_cons (a0 + ground.sumNat a) (rowList a),
    ground.zipWith_append (fun x y => x + y)
      ((rowList b).map (fun x => x + bL)) [bL]
      ((rowList a).reverse) [a0 + ground.sumNat a] hlen,
    zipAdd_mapL bL (rowList b) ((rowList a).reverse)]
  rfl

private theorem mapAdd_replicate : ∀ (x : List Nat) (c n m : Nat),
    x.map (fun u => u + c) = List.replicate n m →
    x = List.replicate n (m - c)
  | [], _, 0, _, _ => rfl
  | [], _, _ + 1, _, h => nomatch h
  | _ :: _, _, 0, _, h => nomatch h
  | u :: t, c, n + 1, m, h => by
    have h1 : u + c = m := (List.cons.inj h).1
    have h2 : t.map (fun u => u + c) = List.replicate n m :=
      (List.cons.inj h).2
    show u :: t = (m - c) :: List.replicate n (m - c)
    rw [mapAdd_replicate t c n m h2, ← h1, ground.addSubSelfR u c]

private theorem join_read : ∀ (a b : Shape), b.length = a.length →
    ∀ aL bL m : Nat,
    List.zipWith (fun x y => x + y) (rowList (b ++ [bL]))
        ((rowList (a ++ [aL])).reverse)
      = List.replicate (a.length + 1) m →
    b = a.reverse ∧ m = bL + ground.sumNat (a ++ [aL])
  | [], b, hb, aL, bL, m, h => by
    have hbn : b = [] := ground.nil_of_length_zero b hb
    rw [hbn] at h
    have h1 : bL + aL = m := (List.cons.inj h).1
    exact ⟨hbn, by rw [← h1]; rfl⟩
  | a0 :: A, b, hb, aL, bL, m, h => by
    match ground.snoc_split A.length b (by rw [hb]; rfl) with
    | ⟨B, bL', hbe, hBl⟩ =>
      have h2 : List.zipWith (fun x y => x + y)
          (rowList ((B ++ [bL']) ++ [bL]))
          ((rowList (a0 :: (A ++ [aL]))).reverse)
        = List.replicate (A.length + 1 + 1) m := by
        rw [← hbe]
        exact h
      have hstep := join_step (A ++ [aL]) (B ++ [bL'])
        (by rw [ground.length_append, ground.length_append, hBl]; rfl)
        a0 bL
      rw [hstep, ← ground.replicate_snoc m (A.length + 1)] at h2
      have hlen : ((List.zipWith (fun x y => x + y)
            (rowList (B ++ [bL']))
            ((rowList (A ++ [aL])).reverse)).map
          (fun x => x + bL)).length
          = (List.replicate (A.length + 1) m).length := by
        rw [ground.length_map, ground.length_replicate,
          ground.length_zipWith (fun x y => x + y) _ _ (A.length + 1)
            (by rw [places.length_rowList, ground.length_append, hBl]
                rfl)
            (by rw [ground.length_reverse, places.length_rowList,
                ground.length_append]
                rfl)]
      match ground.append_inj_len _ _ _ _ hlen h2 with
      | ⟨hpre, hlast⟩ =>
        have hm : bL + ground.sumNat (a0 :: (A ++ [aL])) = m :=
          (List.cons.inj hlast).1
        match join_read A B hBl aL bL' (m - bL)
            (mapAdd_replicate _ bL (A.length + 1) m hpre) with
        | ⟨hBA, hmb⟩ =>
          have hsplit : m - bL = a0 + ground.sumNat (A ++ [aL]) := by
            rw [← hm]
            exact ground.addSubSelfL bL (a0 + ground.sumNat (A ++ [aL]))
          have ha0 : bL' = a0 :=
            ground.addCancelR (ground.sumNat (A ++ [aL]))
              (hmb.symm.trans hsplit)
          refine ⟨?_, hm.symm⟩
          rw [hbe, hBA, ha0, ground.reverse_cons a0 A]

private theorem join_mirror : ∀ (u : Shape) (aL bL : Nat),
    List.zipWith (fun x y => x + y) (rowList (u.reverse ++ [bL]))
        ((rowList (u ++ [aL])).reverse)
      = List.replicate (u.length + 1)
        (bL + ground.sumNat (u ++ [aL]))
  | [], _, _ => rfl
  | u0 :: U, aL, bL => by
    rw [ground.reverse_cons u0 U]
    show List.zipWith (fun x y => x + y)
        (rowList ((U.reverse ++ [u0]) ++ [bL]))
        ((rowList (u0 :: (U ++ [aL]))).reverse)
      = List.replicate (U.length + 1 + 1)
        (bL + (u0 + ground.sumNat (U ++ [aL])))
    rw [join_step (U ++ [aL]) (U.reverse ++ [u0])
        (by rw [ground.length_append, ground.length_append,
          ground.length_reverse]; rfl) u0 bL,
      join_mirror U aL u0,
      ground.map_replicate (fun x => x + bL)
        (u0 + ground.sumNat (U ++ [aL])) (U.length + 1),
      ← ground.replicate_snoc
        (bL + (u0 + ground.sumNat (U ++ [aL]))) (U.length + 1),
      Nat.add_comm (u0 + ground.sumNat (U ++ [aL])) bL]
    rfl

/-- The constant full-column join reads the dual label: the two row
lists joining to one constant put the second shape's keys at the
first's reversed keys, so the reduced shape is the dual label
(`lem:dualread`(iii)'s join condition at `con:labels`' data). -/
theorem join_dualL (a b : Shape) (hba : b.length = a.length) (m : Nat)
    (hj : List.zipWith (fun x y => x + y) (rowList b)
        ((rowList a).reverse)
      = List.replicate a.length m) :
    reduce a = dualL b := by
  cases a with
  | nil =>
    rw [ground.nil_of_length_zero b hba]
    rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨A, aL, hae, hAl⟩ =>
      match ground.snoc_split A.length b
          (by rw [hba, hae, ground.length_append]; rfl) with
      | ⟨B, bL, hbe, hBl⟩ =>
        have hj2 : List.zipWith (fun x y => x + y) (rowList (B ++ [bL]))
            ((rowList (A ++ [aL])).reverse)
          = List.replicate (A.length + 1) m := by
          rw [← hbe, ← hae]
          exact hj.trans (congrArg (fun k => List.replicate k m)
            (by rw [hae, ground.length_append]; rfl))
        match join_read A B hBl aL bL m hj2 with
        | ⟨hBA, _⟩ =>
          rw [hae, hbe, reduce_snoc A aL, dualL_snoc B bL, hBA,
            ground.reverse_reverse A]

/-- The dual pair's join is the constant at the shared degree: at
the dual label the second shape's rows join the first's reversal to
the degrees' quotient, one full column per letter
(`lem:dualread`(iii)'s converse at `con:labels`' data). -/
theorem dualL_join (a b : Shape)
    (hd : reduce a = dualL b) :
    List.zipWith (fun x y => x + y) (rowList b)
        ((rowList a).reverse)
      = List.replicate a.length
        ((degree a + degree b) / a.length) := by
  have hba : b.length = a.length := by
    rw [← length_dualL b, ← hd, length_reduce a]
  cases a with
  | nil =>
    rw [ground.nil_of_length_zero b hba]
    rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨A, aL, hae, hAl⟩ =>
      match ground.snoc_split A.length b
          (by rw [hba, hae, ground.length_append]; rfl) with
      | ⟨B, bL, hbe, hBl⟩ =>
        have hAB : A = B.reverse := by
          rw [hae, hbe, reduce_snoc A aL, dualL_snoc B bL] at hd
          exact ground.snoc_inj A B.reverse 0 hd
        have hBA : B = A.reverse := by
          rw [hAB, ground.reverse_reverse B]
        have hmir := join_mirror A aL bL
        rw [← hBA] at hmir
        have hrl : (rowList (B ++ [bL])).length
            = ((rowList (A ++ [aL])).reverse).length := by
          rw [places.length_rowList, ground.length_reverse,
            places.length_rowList, ground.length_append,
            ground.length_append, hBl]
          rfl
        have hsum : ground.sumNat (List.zipWith (fun x y => x + y)
              (rowList (B ++ [bL])) ((rowList (A ++ [aL])).reverse))
            = degree (B ++ [bL]) + degree (A ++ [aL]) := by
          rw [ground.sumNat_zipWith_add _ _ hrl,
            ground.sumNat_reverse (rowList (A ++ [aL]))]
          rfl
        have hprod : degree (B ++ [bL]) + degree (A ++ [aL])
            = (bL + ground.sumNat (A ++ [aL])) * (A.length + 1) := by
          rw [← hsum, hmir, ground.sumNat_replicate, Nat.mul_comm]
        have hdiv : (degree (A ++ [aL]) + degree (B ++ [bL]))
            / (A ++ [aL]).length = bL + ground.sumNat (A ++ [aL]) := by
          rw [ground.length_append, Nat.add_comm (degree (A ++ [aL]))
            (degree (B ++ [bL])), hprod]
          exact ground.divMulSelf (bL + ground.sumNat (A ++ [aL]))
            (A.length + 1) (Nat.succ_pos A.length)
        rw [hae, hbe, hmir, hdiv, ground.length_append]
        rfl

/-! The class move at one full column (`con:labels`' descent
clause): the count is one value along the class in each argument.
The lift's guard and cofactor move by one modulus step at a moved
degree, so the two reads land at one Steinberg count — the moved
column entering the deficient side's own lift, or the target's at
the matched degrees, where the mapped span reads the fused counts
(`dualread.fusionCount_addFull`, the factors' exchange
`blockcount.fusionCount_comm`). -/

private theorem countL_lt (a b c : Shape)
    (h : degree a + degree b < degree c) :
    countL a b c
      = if (degree c - (degree a + degree b)) % a.length == 0 then
          steinberg.count
            (addFulls ((degree c - (degree a + degree b)) / a.length) a)
            b c
        else 0 := by
  show (if degree a + degree b < degree c then
      (if (degree c - (degree a + degree b)) % a.length == 0 then
        steinberg.count
          (addFulls ((degree c - (degree a + degree b)) / a.length) a) b c
      else 0)
    else
      (if (degree a + degree b - degree c) % a.length == 0 then
        steinberg.count a b
          (addFulls ((degree a + degree b - degree c) / a.length) c)
      else 0))
    = _
  rw [if_pos h]

private theorem countL_ge (a b c : Shape)
    (h : ¬ degree a + degree b < degree c) :
    countL a b c
      = if (degree a + degree b - degree c) % a.length == 0 then
          steinberg.count a b
            (addFulls ((degree a + degree b - degree c) / a.length) c)
        else 0 := by
  show (if degree a + degree b < degree c then
      (if (degree c - (degree a + degree b)) % a.length == 0 then
        steinberg.count
          (addFulls ((degree c - (degree a + degree b)) / a.length) a) b c
      else 0)
    else
      (if (degree a + degree b - degree c) % a.length == 0 then
        steinberg.count a b
          (addFulls ((degree a + degree b - degree c) / a.length) c)
      else 0))
    = _
  rw [if_neg h]

private theorem modShift (t L : Nat) : (t + L) % L = t % L := by
  have h := ground.modAddMul t 1 L
  rw [Nat.one_mul] at h
  exact h

private theorem divShift (t L : Nat) (hL : 0 < L) (ht : t % L = 0) :
    (t + L) / L = t / L + 1 := by
  have hd := (ground.natDivRead t L hL).1
  rw [ht, Nat.add_zero] at hd
  have he : t + L = (t / L + 1) * L := by
    rw [Nat.succ_mul (t / L) L, Nat.mul_comm (t / L) L, hd]
  rw [he]
  exact ground.divMulSelf (t / L + 1) L hL

private theorem modSelf (L : Nat) : L % L = 0 := by
  have h := ground.modMulSelf 1 L
  rw [Nat.one_mul] at h
  exact h

private theorem divSelf (L : Nat) (hL : 0 < L) : L / L = 1 := by
  have h := ground.divMulSelf 1 L hL
  rw [Nat.one_mul] at h
  exact h

private theorem countL_kshift (a b c a2 b2 : Shape) (hL : 0 < a.length)
    (hlen2 : a2.length = a.length)
    (hdeg2 : degree a2 + degree b2 = degree a + degree b + a.length)
    (hif : ∀ m : Nat, steinberg.count (addFulls m a2) b2 c
      = steinberg.count (addFulls (m + 1) a) b c)
    (helse : ∀ m : Nat, steinberg.count a2 b2 (addFulls (m + 1) c)
      = steinberg.count a b (addFulls m c)) :
    countL a2 b2 c = countL a b c := by
  by_cases h1 : degree a + degree b < degree c
  · by_cases h2 : degree a2 + degree b2 < degree c
    · have h2' : degree a + degree b + a.length < degree c := by
        rw [← hdeg2]
        exact h2
      match Nat.le.dest (Nat.le_of_lt h2') with
      | ⟨t, ht⟩ =>
        have hs2 : degree c - (degree a2 + degree b2) = t := by
          rw [hdeg2, ← ht]
          exact ground.addSubSelfL (degree a + degree b + a.length) t
        have hs1 : degree c - (degree a + degree b) = t + a.length := by
          rw [← ht, Nat.add_right_comm (degree a + degree b) a.length t,
            Nat.add_assoc (degree a + degree b) t a.length]
          exact ground.addSubSelfL (degree a + degree b) (t + a.length)
        rw [countL_lt a2 b2 c h2, countL_lt a b c h1, hs2, hs1, hlen2,
          modShift t a.length]
        cases hb : (t % a.length == 0) with
        | false => rfl
        | true =>
          rw [divShift t a.length hL (ground.beqEqOf hb)]
          show steinberg.count (addFulls (t / a.length) a2) b2 c
            = steinberg.count (addFulls (t / a.length + 1) a) b c
          exact hif (t / a.length)
    · have h2' : degree c ≤ degree a + degree b + a.length := by
        rw [← hdeg2]
        exact Nat.le_of_not_lt h2
      match Nat.le.dest h1 with
      | ⟨u, hu⟩ =>
        have hu' : degree a + degree b + (1 + u) = degree c := by
          rw [← Nat.add_assoc]
          exact hu
        have hdle : 1 + u ≤ a.length := by
          refine ground.leCancelL (degree a + degree b) ?_
          rw [hu']
          exact h2'
        match Nat.le.dest hdle with
        | ⟨f, hf⟩ =>
          have hs1 : degree c - (degree a + degree b) = 1 + u := by
            rw [← hu']
            exact ground.addSubSelfL (degree a + degree b) (1 + u)
          have hs2 : degree a2 + degree b2 - degree c = f := by
            rw [hdeg2, ← hf,
              ← Nat.add_assoc (degree a + degree b) (1 + u) f, hu']
            exact ground.addSubSelfL (degree c) f
          rw [countL_lt a b c h1, countL_ge a2 b2 c h2, hs1, hs2, hlen2]
          cases f with
          | zero =>
            have hL1 : 1 + u = a.length := by
              rw [← hf, Nat.add_zero]
            rw [hL1, modSelf a.length, divSelf a.length hL,
              ground.modZeroLeft a.length, divZeroL a.length,
              addFulls_zero c]
            show steinberg.count a2 b2 c
              = steinberg.count (addFulls 1 a) b c
            rw [← addFulls_zero a2]
            exact hif 0
          | succ g =>
            have hdlt : 1 + u < a.length := by
              rw [← hf]
              exact Nat.lt_add_of_pos_right (Nat.succ_pos g)
            have hflt : g + 1 < a.length := by
              rw [← hf, Nat.add_comm (1 + u) (g + 1)]
              exact Nat.lt_add_of_pos_right
                (Nat.lt_of_lt_of_le (Nat.succ_pos 0)
                  (Nat.le_add_right 1 u))
            rw [ground.modOfLt (1 + u) a.length hdlt,
              ground.modOfLt (g + 1) a.length hflt,
              ground.neBeqOf (a := 1 + u) (b := 0)
                (fun he => Nat.noConfusion
                  ((Nat.add_comm 1 u).symm.trans he)),
              ground.neBeqOf (a := g + 1) (b := 0)
                (fun he => Nat.noConfusion he)]
            rfl
  · have h2 : ¬ degree a2 + degree b2 < degree c := by
      rw [hdeg2]
      exact fun hlt => h1 (Nat.lt_of_le_of_lt
        (Nat.le_add_right (degree a + degree b) a.length) hlt)
    match Nat.le.dest (Nat.le_of_not_lt h1) with
    | ⟨r, hr⟩ =>
      have hs1 : degree a + degree b - degree c = r := by
        rw [← hr]
        exact ground.addSubSelfL (degree c) r
      have hs2 : degree a2 + degree b2 - degree c = r + a.length := by
        rw [hdeg2, ← hr, Nat.add_assoc (degree c) r a.length]
        exact ground.addSubSelfL (degree c) (r + a.length)
      rw [countL_ge a b c h1, countL_ge a2 b2 c h2, hs1, hs2, hlen2,
        modShift r a.length]
      cases hb : (r % a.length == 0) with
      | false => rfl
      | true =>
        rw [divShift r a.length hL (ground.beqEqOf hb)]
        show steinberg.count a2 b2 (addFulls (r / a.length + 1) c)
          = steinberg.count a b (addFulls (r / a.length) c)
        exact helse (r / a.length)

private theorem countL_cshift (a b c c2 : Shape) (hL : 0 < a.length)
    (hdeg2 : degree c2 = degree c + a.length)
    (hif : ∀ m : Nat, steinberg.count (addFulls (m + 1) a) b c2
      = steinberg.count (addFulls m a) b c)
    (helse : ∀ m : Nat, steinberg.count a b (addFulls m c2)
      = steinberg.count a b (addFulls (m + 1) c)) :
    countL a b c2 = countL a b c := by
  by_cases h1 : degree a + degree b < degree c
  · have h1' : degree a + degree b < degree c2 := by
      rw [hdeg2]
      exact Nat.lt_of_lt_of_le h1
        (Nat.le_add_right (degree c) a.length)
    match Nat.le.dest (Nat.le_of_lt h1) with
    | ⟨d, hd⟩ =>
      have hs1 : degree c - (degree a + degree b) = d := by
        rw [← hd]
        exact ground.addSubSelfL (degree a + degree b) d
      have hs2 : degree c2 - (degree a + degree b) = d + a.length := by
        rw [hdeg2, ← hd, Nat.add_assoc (degree a + degree b) d a.length]
        exact ground.addSubSelfL (degree a + degree b) (d + a.length)
      rw [countL_lt a b c2 h1', countL_lt a b c h1, hs1, hs2,
        modShift d a.length]
      cases hb : (d % a.length == 0) with
      | false => rfl
      | true =>
        rw [divShift d a.length hL (ground.beqEqOf hb)]
        show steinberg.count (addFulls (d / a.length + 1) a) b c2
          = steinberg.count (addFulls (d / a.length) a) b c
        exact hif (d / a.length)
  · match Nat.le.dest (Nat.le_of_not_lt h1) with
    | ⟨r, hr⟩ =>
      have hs1 : degree a + degree b - degree c = r := by
        rw [← hr]
        exact ground.addSubSelfL (degree c) r
      by_cases h2 : degree a + degree b < degree c2
      · have hrL : r < a.length := by
          refine ground.leCancelL (degree c) ?_
          show (degree c + r).succ ≤ degree c + a.length
          rw [hr, ← hdeg2]
          exact h2
        match Nat.le.dest hrL with
        | ⟨e, he⟩ =>
          have harr : degree c + (r + 1 + e) = degree c + r + (1 + e) := by
            rw [Nat.add_assoc r 1 e, ← Nat.add_assoc (degree c) r (1 + e)]
          have hs2 : degree c2 - (degree a + degree b) = 1 + e := by
            rw [hdeg2, ← he, ← hr]
            show degree c + (r + 1 + e) - (degree c + r) = 1 + e
            rw [harr]
            exact ground.addSubSelfL (degree c + r) (1 + e)
          rw [countL_ge a b c h1, countL_lt a b c2 h2, hs1, hs2]
          cases r with
          | zero =>
            have heL : 1 + e = a.length := by
              rw [← he]
            rw [heL, modSelf a.length, divSelf a.length hL,
              ground.modZeroLeft a.length, divZeroL a.length,
              addFulls_zero c]
            show steinberg.count (addFulls 1 a) b c2
              = steinberg.count a b c
            have h0 := hif 0
            rw [addFulls_zero a] at h0
            exact h0
          | succ q =>
            have hrlt : q + 1 < a.length := by
              rw [← he]
              exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (q + 1))
                (Nat.le_add_right (q + 1).succ e)
            have helt : 1 + e < a.length := by
              rw [← he]
              exact Nat.add_lt_add_right
                (Nat.succ_lt_succ (Nat.succ_pos q)) e
            rw [ground.modOfLt (q + 1) a.length hrlt,
              ground.modOfLt (1 + e) a.length helt,
              ground.neBeqOf (a := q + 1) (b := 0)
                (fun hq => Nat.noConfusion hq),
              ground.neBeqOf (a := 1 + e) (b := 0)
                (fun hq => Nat.noConfusion
                  ((Nat.add_comm 1 e).symm.trans hq))]
            rfl
      · match Nat.le.dest (Nat.le_of_not_lt h2) with
        | ⟨w, hw⟩ =>
          have hs2 : degree a + degree b - degree c2 = w := by
            rw [← hw]
            exact ground.addSubSelfL (degree c2) w
          have hrw : r = w + a.length := by
            refine ground.addCancelL (degree c) ?_
            rw [hr, ← hw, hdeg2, Nat.add_assoc (degree c) a.length w,
              Nat.add_comm a.length w]
          rw [countL_ge a b c h1, countL_ge a b c2 h2, hs1, hs2, hrw,
            modShift w a.length]
          cases hb : (w % a.length == 0) with
          | false => rfl
          | true =>
            rw [divShift w a.length hL (ground.beqEqOf hb)]
            show steinberg.count a b (addFulls (w / a.length) c2)
              = steinberg.count a b (addFulls (w / a.length + 1) c)
            exact helse (w / a.length)

/-- The fused count into a target without a full column is vacant at
a factor carrying one: the bumped factor's pool is the pool's own at
the wedge tensored on (`dualread.countAt_fusedLine`), so every
member's content is occupied at the deepest letter while the
target's row list reads its last key vacant, and the content group
is empty. -/
private theorem fusion_vac (x y c : Shape) (hyx : y.length = x.length)
    (hd : 0 < x.length)
    (hlast : ground.getAt 0 (rowList c) (x.length - 1) = 0) :
    blockcount.fusionCount (ground.bumpAt (x.length - 1) x) y c = 0 := by
  have hbl : (ground.bumpAt (x.length - 1) x).length = x.length :=
    ground.length_bumpAt _ x
  have hlt : x.length - 1 < x.length := Nat.sub_lt hd (Nat.succ_pos 0)
  rw [blockcount.fusionCount_countAt (ground.bumpAt (x.length - 1) x) y c
      (hyx.trans hbl.symm),
    dualread.countAt_fusedLine x y hyx (rowList c)]
  have hnil : blockcount.groupAt
      ((blockcount.fusedAt (blockcount.blockSpan x)
        (blockcount.blockSpan y)).map
        (fun v => blockcount.tensorH
          (blockcount.wedge x.length x.length) v))
      (rowList c) = [] := by
    refine blockcount.groupAt_nil_of_not_mem _ _ ?_
    intro hmem
    match ground.mem_map_of blockcount.HVec.content _ _ hmem with
    | ⟨z, hz, hzc⟩ =>
      match ground.mem_map_of
          (fun v => blockcount.tensorH
            (blockcount.wedge x.length x.length) v) _ z hz with
      | ⟨v, hv, hvz⟩ =>
        have hwv : v.content.length = x.length := by
          match ground.mem_flatMap_of _ _ v hv with
          | ⟨u, hu, huv⟩ =>
            match ground.mem_map_of (blockcount.tensorH u) _ v huv with
            | ⟨w, hw, hwx⟩ =>
              rw [← hwx]
              exact ground.length_zipWith (fun a b => a + b) u.content
                w.content x.length (blockcount.blockSpan_width x u hu)
                ((blockcount.blockSpan_width y w hw).trans hyx)
        have hzent : ground.getAt 0 z.content (x.length - 1)
            = ground.getAt 0
                (blockcount.wedge x.length x.length).content (x.length - 1)
              + ground.getAt 0 v.content (x.length - 1) := by
          rw [← hvz]
          show ground.getAt 0
              (List.zipWith (fun a b => a + b)
                (blockcount.wedge x.length x.length).content v.content)
              (x.length - 1) = _
          exact ground.getAt_zipWith 0 0 0 (fun a b => a + b)
            (blockcount.wedge x.length x.length).content v.content
            (x.length - 1)
            (by rw [blockcount.wedge_clen]; exact hlt)
            (by rw [hwv]; exact hlt)
        rw [blockcount.wedge_full_get x.length (x.length - 1) hlt, hzc,
          hlast,
          Nat.add_comm 1 (ground.getAt 0 v.content (x.length - 1))] at hzent
        exact Nat.noConfusion hzent
  refine blockcount.countAt_of_units _ _ ?_
  intro k hk
  rw [hnil] at hk
  exact absurd hk (Nat.not_lt_zero k)

/-- A full column moves between the two factors: at a target
carrying a full column the two reads are the mapped span's descent
at the exchanged factors (`dualread.fusionCount_addFull` with
`blockcount.fusionCount_comm`), and at a target without one both
counts are vacant. -/
private theorem fusion_move (x y c : Shape) (hyx : y.length = x.length)
    (hcx : c.length = x.length) (hd : 0 < x.length) :
    blockcount.fusionCount (ground.bumpAt (x.length - 1) x) y c
      = blockcount.fusionCount x (ground.bumpAt (x.length - 1) y) c := by
  have hpred : x.length - 1 + 1 = x.length := ground.subAdd hd
  have hyl : (ground.bumpAt (x.length - 1) y).length = y.length :=
    ground.length_bumpAt _ y
  match ground.snoc_split (x.length - 1) c (by rw [hcx, hpred]) with
  | ⟨c', j, hce, hcl⟩ =>
    cases j with
    | zero =>
      have hlast : ground.getAt 0 (rowList c) (x.length - 1) = 0 := by
        rw [places.rowList_last c (x.length - 1) (by rw [hcx, hpred]),
          hce, ← hcl]
        exact ground.getAt_append_add 0 c' [0] 0
      rw [fusion_vac x y c hyx hd hlast, blockcount.fusionCount_comm x
        (ground.bumpAt (x.length - 1) y) c (hyl.trans hyx), ← hyx]
      exact (fusion_vac y x c hyx.symm (by rw [hyx]; exact hd)
        (by rw [hyx]; exact hlast)).symm
    | succ e =>
      have hc0 : (c' ++ [e]).length = x.length := by
        rw [ground.length_append, hcl]
        exact hpred
      have hbump : c = ground.bumpAt (x.length - 1) (c' ++ [e]) := by
        rw [hce, ← hcl, ground.bumpAt_snoc c' e]
      rw [hbump,
        dualread.fusionCount_addFull x y (c' ++ [e]) hyx hc0,
        blockcount.fusionCount_comm x (ground.bumpAt (x.length - 1) y)
          (ground.bumpAt (x.length - 1) (c' ++ [e]))
          (hyl.trans hyx),
        ← hyx,
        dualread.fusionCount_addFull y x (c' ++ [e]) hyx.symm
          (hc0.trans hyx.symm),
        blockcount.fusionCount_comm y x (c' ++ [e]) hyx.symm]

private theorem degree_bumpTop (s : Shape) (h : 0 < s.length) :
    degree (ground.bumpAt (s.length - 1) s) = degree s + s.length := by
  have hlt : s.length - 1 < s.length := Nat.sub_lt h (Nat.succ_pos 0)
  rw [places.degree_bumpAt (s.length - 1) s hlt, ground.subAdd h]

/-- The label count is one value at the class in the first
argument: a full column on the representative is the lift's own
step, and at the matched degrees the count descends with the target
(`con:labels`' class-invariance clause).  The two widths are the
frame, both counts one read at every width by the lift's own
guard. -/
theorem countL_bumpA (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    countL (ground.bumpAt (a.length - 1) a) b c = countL a b c := by
  cases Nat.eq_zero_or_pos a.length with
  | inl h0 =>
    rw [ground.nil_of_length_zero a h0]
    rfl
  | inr hL =>
    have hbl : (ground.bumpAt (a.length - 1) a).length = a.length :=
      ground.length_bumpAt _ a
    refine countL_kshift a b c (ground.bumpAt (a.length - 1) a) b hL
      hbl ?_ ?_ ?_
    · rw [degree_bumpTop a hL]
      exact Nat.add_right_comm (degree a) a.length (degree b)
    · intro m
      rw [addFulls_bumped m a]
    · intro m
      have hcl : (addFulls m c).length = a.length :=
        (length_addFulls m c).trans hca
      rw [addFulls_succ m c, hca,
        steinberg.count_fusion (ground.bumpAt (a.length - 1) a) b
          (ground.bumpAt (a.length - 1) (addFulls m c))
          (hba.trans hbl.symm)
          (by rw [ground.length_bumpAt, hcl, hbl]),
        steinberg.count_fusion a b (addFulls m c) hba hcl]
      exact dualread.fusionCount_addFull a b (addFulls m c) hba hcl

/-- The label count is one value at the class in the second
argument: the moved column reads across the factors' exchange
(`blockcount.fusionCount_comm`), the target's own descent at the
matched degrees.  The second shape's width is load-bearing with its
committed refusal — the bumped key is the first shape's — and the
target's width is the frame. -/
theorem countL_bumpB (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    countL a (ground.bumpAt (b.length - 1) b) c = countL a b c := by
  cases Nat.eq_zero_or_pos a.length with
  | inl h0 =>
    rw [ground.nil_of_length_zero b (hba.trans h0)]
    rfl
  | inr hL =>
    have hbL : 0 < b.length := by
      rw [hba]
      exact hL
    have hbl : (ground.bumpAt (b.length - 1) b).length = b.length :=
      ground.length_bumpAt _ b
    refine countL_kshift a b c a (ground.bumpAt (b.length - 1) b) hL
      rfl ?_ ?_ ?_
    · rw [degree_bumpTop b hbL, hba,
        ← Nat.add_assoc (degree a) (degree b) a.length]
    · intro m
      have hX : (addFulls m a).length = a.length := length_addFulls m a
      have hmove := fusion_move (addFulls m a) b c
        (hba.trans hX.symm) (hca.trans hX.symm) (by rw [hX]; exact hL)
      rw [hX] at hmove
      rw [addFulls_succ m a, hba,
        steinberg.count_fusion (addFulls m a)
          (ground.bumpAt (a.length - 1) b) c
          (by rw [ground.length_bumpAt, hba, hX])
          (hca.trans hX.symm),
        steinberg.count_fusion (ground.bumpAt (a.length - 1)
            (addFulls m a)) b c
          (by rw [ground.length_bumpAt, hX]; exact hba)
          (by rw [ground.length_bumpAt, hX]; exact hca)]
      exact hmove.symm
    · intro m
      have hcl : (addFulls m c).length = a.length :=
        (length_addFulls m c).trans hca
      rw [addFulls_succ m c, hca,
        steinberg.count_fusion a (ground.bumpAt (b.length - 1) b)
          (ground.bumpAt (a.length - 1) (addFulls m c))
          (hbl.trans hba)
          (by rw [ground.length_bumpAt, hcl]),
        steinberg.count_fusion a b (addFulls m c) hba hcl,
        blockcount.fusionCount_comm a (ground.bumpAt (b.length - 1) b)
          (ground.bumpAt (a.length - 1) (addFulls m c))
          (hbl.trans hba),
        blockcount.fusionCount_comm a b (addFulls m c) hba, ← hba]
      exact dualread.fusionCount_addFull b a (addFulls m c) hba.symm
        (hcl.trans hba.symm)

/-- The label count is one value at the class in the target: the
moved column enters the lift's own step on the deficient side, and
at the matched degrees it is the mapped span's descent
(`dualread.fusionCount_addFull`).  The two widths are the frame,
both counts one read at every width by the lift's own guard. -/
theorem countL_bumpC (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    countL a b (ground.bumpAt (c.length - 1) c) = countL a b c := by
  cases Nat.eq_zero_or_pos a.length with
  | inl h0 =>
    rw [ground.nil_of_length_zero c (hca.trans h0)]
    rfl
  | inr hL =>
    have hcL : 0 < c.length := by
      rw [hca]
      exact hL
    refine countL_cshift a b c (ground.bumpAt (c.length - 1) c) hL ?_ ?_ ?_
    · rw [degree_bumpTop c hcL, hca]
    · intro m
      have hX : (addFulls m a).length = a.length := length_addFulls m a
      have hfull := dualread.fusionCount_addFull (addFulls m a) b c
        (hba.trans hX.symm) (hca.trans hX.symm)
      rw [hX] at hfull
      rw [addFulls_succ m a, hca,
        steinberg.count_fusion (ground.bumpAt (a.length - 1)
            (addFulls m a)) b (ground.bumpAt (a.length - 1) c)
          (by rw [ground.length_bumpAt, hX]; exact hba)
          (by rw [ground.length_bumpAt, ground.length_bumpAt, hX]
              exact hca),
        steinberg.count_fusion (addFulls m a) b c
          (hba.trans hX.symm) (hca.trans hX.symm)]
      exact hfull
    · intro m
      rw [addFulls_bumped m c]

/-- The span's count is one value at the class: a full column at
the deepest key maps the span member for member
(`dualread.spanAddFull`), one column at a time. -/
private theorem spanLen_class : ∀ (s' : Shape) (j : Nat),
    (blockcount.blockSpan (s' ++ [j])).length
      = (blockcount.blockSpan (s' ++ [0])).length
  | _, 0 => rfl
  | s', j + 1 => by
    have hlen : (s' ++ [j]).length - 1 = s'.length := by
      rw [ground.length_append s' [j]]
      rfl
    have h := (dualread.spanAddFull (s' ++ [j])).1
    rw [hlen, ground.bumpAt_snoc s' j] at h
    exact h.trans (spanLen_class s' j)

/-- The dimension descends to labels: the block's count is one
value along the class, `con:labels`' first descent clause at
`cor:weyldim`'s span read. -/
theorem dimOf_class (s : Shape) :
    weyldim.dimOf s = weyldim.dimOf (reduce s) := by
  cases s with
  | nil => rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, reduce_snoc s' a, weyldim.dimOf_spanLen (s' ++ [a]),
        weyldim.dimOf_spanLen (s' ++ [0]), spanLen_class s' a]

/-- The Casimir read descends: the cleared bracket one value at
the class, the full column moving every row by one with the gaps
fixed. -/
def c2ClassRead (s : Shape) : Prop :=
  c2hat.dfQ s = c2hat.dfQ (reduce s)

instance (s : Shape) : Decidable (c2ClassRead s) :=
  inferInstanceAs (Decidable (_ = _))

/-- The last key's occupancy is the cleared read's own class datum:
the full columns move every row alike, one column at a time. -/
private theorem dfQ_snoc : ∀ (s : Shape) (j : Nat),
    c2hat.dfQ (s ++ [j]) = c2hat.dfQ (s ++ [0])
  | _, 0 => rfl
  | s, j + 1 => by
    have hlen : (s ++ [j]).length - 1 = s.length :=
      congrArg (fun k => k - 1) (ground.length_append s [j])
    have h := c2hat.dfQ_full (s ++ [j])
    rw [hlen, ground.bumpAt_snoc s j] at h
    exact h.trans (dfQ_snoc s j)

/-- The Casimir read descends at every shape: the cleared bracket
one value at the class, the withdrawn full columns the read's
own. -/
theorem c2Class_all (s : Shape) : c2ClassRead s := by
  show c2hat.dfQ s = c2hat.dfQ (reduce s)
  cases s with
  | nil => rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, reduce_snoc s' a]
      exact dfQ_snoc s' a

/-- The Cartan count's equality on shapes, `N^{a+b}_{ab} = 1`, the
stated read; `cartan_eq` the theorem at matched widths with
`cartan_all` its read at this spelling. -/
def cartanRead (a b : Shape) : Prop := countL a b (places.addS a b) = 1

instance (a b : Shape) : Decidable (cartanRead a b) :=
  inferInstanceAs (Decidable (_ = _))

/-! The Cartan sharpening (`con:labels`' closing sentence): the
content-`a+b` summand of the product is the two tops' own line, so
the pair list at the union's row list holds one member and the
kernel dimension sits at or below the one column, against
`lem:blockcount`(iii)'s occupied floor.  The one line is the
dominance squeeze: a content of the first block whose complement
in the union is a content of the second sits at and below the
first shape's top at once, the two walks' prefix sums read against
the entrywise join. -/

/-- The dominance squeeze at an entrywise join: two lists each at
or below their own comparison list, with the two joins reading one
list, are those comparison lists themselves — per key the walks'
two comparisons against the entries' join force each entry at its
own, and the kept gaps stay vacant along the descent
(`lem:lowerspan`'s dominance clause read through the prefix
sums). -/
private theorem domSqueeze : ∀ X Y A B : List Nat,
    X.length = Y.length →
    weylchar.domBy X A → weylchar.domBy Y B →
    List.zipWith (fun u w => u + w) X Y
        = List.zipWith (fun u w => u + w) A B →
    X = A ∧ Y = B
  | [], [], [], [], _, _, _, _ => ⟨rfl, rfl⟩
  | [], [], [], _ :: _, _, _, hB, _ => Bool.noConfusion hB
  | [], [], _ :: _, _, _, hA, _, _ => Bool.noConfusion hA
  | [], _ :: _, _, _, hl, _, _, _ => Nat.noConfusion hl
  | _ :: _, [], _, _, hl, _, _, _ => Nat.noConfusion hl
  | _ :: _, _ :: _, [], _, _, hA, _, _ => Bool.noConfusion hA
  | _ :: _, _ :: _, _ :: _, [], _, _, hB, _ => Bool.noConfusion hB
  | x :: X, y :: Y, a :: A, b :: B, hl, hA, hB, hz => by
    have hA' : (if x ≤ 0 + a then weylchar.domGo (0 + a - x) X A
        else false) = true := hA
    have hB' : (if y ≤ 0 + b then weylchar.domGo (0 + b - y) Y B
        else false) = true := hB
    by_cases hxa : x ≤ 0 + a
    · by_cases hyb : y ≤ 0 + b
      · rw [if_pos hxa] at hA'
        rw [if_pos hyb] at hB'
        rw [Nat.zero_add a] at hxa
        rw [Nat.zero_add b] at hyb
        have hz' : (x + y) :: List.zipWith (fun u w => u + w) X Y
            = (a + b) :: List.zipWith (fun u w => u + w) A B := hz
        injection hz' with hh ht
        have hax : a ≤ x := by
          have h1 : x + y ≤ x + b := Nat.add_le_add_left hyb x
          rw [hh] at h1
          exact ground.leCancelR b h1
        have hxe : x = a := Nat.le_antisymm hxa hax
        have hye : y = b := by
          rw [hxe] at hh
          exact ground.addCancelL a hh
        rw [hxe, Nat.zero_add a, Nat.sub_self a] at hA'
        rw [hye, Nat.zero_add b, Nat.sub_self b] at hB'
        have hrec := domSqueeze X Y A B (Nat.succ.inj hl) hA' hB' ht
        exact ⟨by rw [hxe, hrec.1], by rw [hye, hrec.2]⟩
      · rw [if_neg hyb] at hB'
        exact Bool.noConfusion hB'
    · rw [if_neg hxa] at hA'
      exact Bool.noConfusion hA'

/-- The top content's one line past the head: the span's top count
is one and the head exhibit already reads that content, so no
later member reads it (`lem:lowerspan`'s top clause at
`def:blockcount`'s span contents). -/
private theorem span_off_top (s : Shape) (tail : List blockcount.HVec)
    (hbs : blockcount.blockSpan s = blockcount.exhibit s :: tail) :
    ∀ v ∈ tail, ¬ v.content = rowList s := by
  have h : ground.countOf (rowList s)
      ((blockcount.blockSpan s).map blockcount.HVec.content) = 1 :=
    lowerspan.topRead_def s
  rw [hbs] at h
  have h2 : ground.countOf (rowList s)
      ((blockcount.exhibit s).content
        :: tail.map blockcount.HVec.content) = 1 := h
  rw [blockcount.content_exhibit s, ground.countOf_head] at h2
  have h3 : ground.countOf (rowList s)
      (tail.map blockcount.HVec.content) = 0 :=
    ground.addCancelR 1 (h2.trans (Nat.zero_add 1).symm)
  intro v hv hc
  have hmem : v.content ∈ tail.map blockcount.HVec.content :=
    ground.mem_map_to blockcount.HVec.content hv
  rw [hc] at hmem
  have hpos := ground.countOf_pos_of_mem hmem
  rw [h3] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- The stated pair list at the column union is the head pair
alone: the guard ties the two members' contents to the union's row
list, the dominance squeeze reads each content at its own shape's
top, and the top's one line names the two exhibits, so every
further pair's guard refuses. -/
private theorem pairsAt_cartan (a b : Shape) (hba : b.length = a.length) :
    blockcount.pairsAt (blockcount.blockSpan a) (blockcount.blockSpan b)
        (rowList (places.addS a b))
      = [blockcount.tensorH (blockcount.exhibit a)
          (blockcount.exhibit b)] := by
  have hrl : rowList (places.addS a b)
      = List.zipWith (fun x y => x + y) (rowList a) (rowList b) :=
    places.rowList_addS a b hba
  have hguard : ∀ v ∈ blockcount.blockSpan a,
      ∀ w ∈ blockcount.blockSpan b,
      List.zipWith (fun x y => x + y) v.content w.content
          = rowList (places.addS a b) →
      v.content = rowList a ∧ w.content = rowList b := by
    intro v hv w hw hz
    refine domSqueeze v.content w.content (rowList a) (rowList b) ?_ ?_ ?_ ?_
    · rw [blockcount.blockSpan_width a v hv,
        blockcount.blockSpan_width b w hw, hba]
    · exact lowerspan.supportRead_def a v.content
        (ground.mem_map_to blockcount.HVec.content hv)
    · exact lowerspan.supportRead_def b w.content
        (ground.mem_map_to blockcount.HVec.content hw)
    · rw [hz, hrl]
  have hcc : List.zipWith (fun x y => x + y)
      (blockcount.exhibit a).content (blockcount.exhibit b).content
      = rowList (places.addS a b) := by
    rw [blockcount.content_exhibit a, blockcount.content_exhibit b, hrl]
  match blockcount.blockSpan_prov a, blockcount.blockSpan_prov b with
  | ⟨ta, hta, _⟩, ⟨tb, htb, _⟩ =>
    have hmemA : ∀ v ∈ ta, v ∈ blockcount.blockSpan a := by
      intro v hv
      rw [hta]
      exact List.Mem.tail _ hv
    have hmemB : ∀ w ∈ blockcount.exhibit b :: tb,
        w ∈ blockcount.blockSpan b := by
      intro w hw
      rw [htb]
      exact hw
    have hoffA : ∀ v ∈ ta, ¬ v.content = rowList a := span_off_top a ta hta
    have hoffB : ∀ w ∈ tb, ¬ w.content = rowList b := span_off_top b tb htb
    have hexA : blockcount.exhibit a ∈ blockcount.blockSpan a := by
      rw [hta]
      exact List.Mem.head _
    have hTa : ta.flatMap (fun v =>
        (blockcount.exhibit b :: tb).flatMap (fun w =>
          if List.zipWith (fun x y => x + y) v.content w.content
              = rowList (places.addS a b) then
            [blockcount.tensorH v w] else [])) = [] := by
      refine ground.flatMap_nil _ ta (fun v hv => ?_)
      refine ground.flatMap_nil _ _ (fun w hw => ?_)
      by_cases hg : List.zipWith (fun x y => x + y) v.content w.content
          = rowList (places.addS a b)
      · exact absurd (hguard v (hmemA v hv) w (hmemB w hw) hg).1 (hoffA v hv)
      · exact if_neg hg
    have hTb : tb.flatMap (fun w =>
        if List.zipWith (fun x y => x + y)
            (blockcount.exhibit a).content w.content
            = rowList (places.addS a b) then
          [blockcount.tensorH (blockcount.exhibit a) w] else []) = [] := by
      refine ground.flatMap_nil _ tb (fun w hw => ?_)
      by_cases hg : List.zipWith (fun x y => x + y)
          (blockcount.exhibit a).content w.content
          = rowList (places.addS a b)
      · exact absurd (hguard (blockcount.exhibit a) hexA w
          (hmemB w (List.Mem.tail _ hw)) hg).2 (hoffB w hw)
      · exact if_neg hg
    rw [hta, htb]
    show ((if List.zipWith (fun x y => x + y)
              (blockcount.exhibit a).content (blockcount.exhibit b).content
              = rowList (places.addS a b) then
            [blockcount.tensorH (blockcount.exhibit a)
              (blockcount.exhibit b)]
          else [])
        ++ tb.flatMap (fun w =>
            if List.zipWith (fun x y => x + y)
                (blockcount.exhibit a).content w.content
                = rowList (places.addS a b) then
              [blockcount.tensorH (blockcount.exhibit a) w] else []))
        ++ ta.flatMap (fun v =>
            (blockcount.exhibit b :: tb).flatMap (fun w =>
              if List.zipWith (fun x y => x + y) v.content w.content
                  = rowList (places.addS a b) then
                [blockcount.tensorH v w] else []))
      = [blockcount.tensorH (blockcount.exhibit a) (blockcount.exhibit b)]
    rw [if_pos hcc, hTb, hTa]
    rfl

/-- The Cartan count's equality on shapes, `N^{a+b}_{ab} = 1`
(`con:labels`' closing sentence): the floor is
`lem:blockcount`(iii)'s occupied read at the column union, and the
cap is the stated pair list's one member — the content-`a+b`
summand the two tops' own line — so the kernel dimension sits at
or below the one column.  The one letter width `hba` is
load-bearing with its committed refusal: a wider shape at a second
occupied letter starves the head pair's guard and the count reads
the sum's unit. -/
theorem cartan_eq (a b : Shape) (hba : b.length = a.length) :
    blockcount.fusionCount a b (places.addS a b) = 1 := by
  refine Nat.le_antisymm ?_ (blockcount.fusionCount_cartan a b hba)
  show elim.kernelDim
      (blockcount.pairsAt (blockcount.blockSpan a) (blockcount.blockSpan b)
        (rowList (places.addS a b))).length
      (elim.crossM (units.stackedRaise (rowList (places.addS a b)))
        ((blockcount.pairsAt (blockcount.blockSpan a)
          (blockcount.blockSpan b)
          (rowList (places.addS a b))).map blockcount.HVec.coords))
    ≤ 1
  rw [pairsAt_cartan a b hba]
  exact Nat.sub_le 1 _

/-- The Cartan read at every matched pair: the column union's
degree is the two degrees' join, so the label count sits at the
matched-degree branch and reads the block count outright
(`countL_matched`), the Cartan equality closing it —
`con:labels`' sharpening on labels.  The width binder carries the
equality's own refusal. -/
theorem cartan_all (a b : Shape) (hba : b.length = a.length) :
    cartanRead a b := by
  show countL a b (places.addS a b) = 1
  have hca : (places.addS a b).length = a.length :=
    ground.length_zipWith (fun x y => x + y) a b a.length rfl hba
  have hdeg : degree a + degree b = degree (places.addS a b) := by
    show sumNat (rowList a) + sumNat (rowList b)
      = sumNat (rowList (places.addS a b))
    rw [places.rowList_addS a b hba,
      ground.sumNat_zipWith_add (rowList a) (rowList b)
        (by rw [places.length_rowList a, places.length_rowList b, hba])]
  rw [countL_matched a b (places.addS a b) hba hca hdeg]
  exact cartan_eq a b hba

end labels
