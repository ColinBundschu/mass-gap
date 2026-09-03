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

/-- The degree joins its dual label's at the width against the
occupancy total: the complement shape's boxes fill the width's
full columns off the shape's own (`lem:dualread`(ii)'s complement
read at `con:labels`' data). -/
theorem degree_dualL_add (s : Shape) :
    degree s + degree (dualL s) = s.length * ground.sumNat s := by
  cases s with
  | nil => rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      have hlen : (s' ++ [a]).length = s'.length + 1 := by
        rw [ground.length_append s' [a]]
        rfl
      have hsum : ground.sumNat (s' ++ [a]) = ground.sumNat s' + a := by
        rw [ground.sumNat_append s' [a]]
        rfl
      rw [hs, dualL_snoc s' a, places.degree_snoc s' a,
        places.degree_snoc s'.reverse 0, ground.length_reverse s',
        Nat.zero_mul (s'.length + 1), Nat.add_zero (degree s'.reverse),
        hlen, hsum,
        Nat.add_right_comm (degree s') (a * (s'.length + 1))
          (degree s'.reverse),
        places.degree_reverse_add s',
        Nat.mul_add (s'.length + 1) (ground.sumNat s') a,
        Nat.mul_comm a (s'.length + 1)]

/-- The full columns added at the deepest key: the class's own move
by a stated column count, the label's representative shifted along
the class. -/
def addFulls (m : Nat) (s : Shape) : Shape :=
  match s.reverse with
  | [] => []
  | a :: t => ((a + m) :: t).reverse

theorem addFulls_snoc (m : Nat) (s : Shape) (x : Nat) :
    addFulls m (s ++ [x]) = s ++ [x + m] := by
  show (match (s ++ [x]).reverse with
    | [] => []
    | a :: t => ((a + m) :: t).reverse) = s ++ [x + m]
  rw [ground.reverse_snoc s x]
  show ((x + m) :: s.reverse).reverse = s ++ [x + m]
  rw [ground.reverse_cons (x + m) s.reverse, ground.reverse_reverse s]

/-- The added full columns add their boxes: each of the stated
columns fills the shape's whole width. -/
theorem degree_addFulls (m : Nat) (s : Shape) :
    degree (addFulls m s) = degree s + m * s.length := by
  cases s with
  | nil =>
    show degree (addFulls m ([] : Shape))
      = degree ([] : Shape) + m * 0
    rw [Nat.mul_zero]
    rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      have hlen : (s' ++ [a]).length = s'.length + 1 := by
        rw [ground.length_append s' [a]]
        rfl
      rw [hs, addFulls_snoc m s' a, places.degree_snoc s' (a + m),
        places.degree_snoc s' a, hlen,
        ground.mulAddR a m (s'.length + 1),
        Nat.add_assoc (degree s') (a * (s'.length + 1))
          (m * (s'.length + 1))]

/-- The reduction is idempotent: the reduced shape's last key sits
at the unit occupancy already. -/
theorem reduce_reduce : ∀ s : Shape, reduce (reduce s) = reduce s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, reduce_snoc s' a, reduce_snoc s' 0]

/-- The reduction reads through the full columns: the added columns
sit on the last key the reduction withdraws. -/
theorem reduce_addFulls (m : Nat) : ∀ s : Shape,
    reduce (addFulls m s) = reduce s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, addFulls_snoc m s' a, reduce_snoc s' (a + m),
        reduce_snoc s' a]

/-- The reduction is injective at one width and one degree: the
prefixes agree at the split and the degree ties the last
occupancies. -/
theorem reduce_inj (r : Nat) (c c' : Shape)
    (hc : c.length = r + 1) (hc' : c'.length = r + 1)
    (hdeg : degree c = degree c')
    (h : reduce c = reduce c') : c = c' := by
  obtain ⟨u, a, hu, hul⟩ := ground.snoc_split r c hc
  obtain ⟨v, b, hv, hvl⟩ := ground.snoc_split r c' hc'
  rw [hu, hv, reduce_snoc u a, reduce_snoc v b] at h
  have huv : u = v := ground.snoc_inj u v 0 h
  have hdeg' : degree u + a * (u.length + 1)
      = degree u + b * (u.length + 1) := by
    rw [← degree_snoc u a, ← degree_snoc u b, ← hu,
      show u ++ [b] = c' from by rw [huv]; exact hv.symm]
    exact hdeg
  have hab : a = b := Nat.eq_of_mul_eq_mul_right
    (Nat.succ_pos u.length) (ground.addCancelL _ hdeg')
  rw [hu, hv, huv, hab]

/-- The row's emission at the label calculus: a shape of the matched
degree reduced where its count in the product is positive, the
vacant read otherwise — the row of `con:fusion`'s instantiation is
the enumeration's members at this emission. -/
def emit (a b c : Shape) : Option Shape :=
  if 0 < steinberg.count a b c then some (reduce c) else none

/-- An occupied emission's reads at any count: the count is positive
and the value is the source's own class, the row's emission its
instance. -/
theorem emit_reads {n : Nat} {a x : Shape}
    (h : (if 0 < n then some (reduce a) else none) = some x) :
    0 < n ∧ reduce a = x := by
  by_cases hp : 0 < n
  · rw [if_pos hp] at h
    exact ⟨hp, Option.some.inj h⟩
  · rw [if_neg hp] at h
    exact nomatch (show (none : Option Shape) = some x from h)

/-- The occupancy total at the added full columns, at an occupied
width: the stated columns join the last key's own count. -/
private theorem sumNat_addFulls_occ (m : Nat) (s : Shape)
    (h : 0 < s.length) :
    ground.sumNat (addFulls m s) = ground.sumNat s + m := by
  cases s with
  | nil => exact absurd h (Nat.lt_irrefl 0)
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, addFulls_snoc m s' a, ground.sumNat_append s' [a + m],
        ground.sumNat_append s' [a]]
      show ground.sumNat s' + (a + m + 0)
        = ground.sumNat s' + (a + 0) + m
      rw [Nat.add_zero (a + m), Nat.add_zero a,
        Nat.add_assoc (ground.sumNat s') a m]

private theorem addFulls_zero : ∀ s : Shape, addFulls 0 s = s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', y, hs, _⟩ =>
      rw [hs, addFulls_snoc 0 s' y, Nat.add_zero]

/-- The full columns keep the width. -/
theorem length_addFulls (m : Nat) : ∀ s : Shape,
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

/-- The label count below the target's degree at a refused
divisibility is vacant: the lift's guard refuses. -/
theorem countL_ltVac (a b c : Shape)
    (hlt : degree a + degree b < degree c)
    (hmod : ¬ (degree c - (degree a + degree b)) % a.length = 0) :
    countL a b c = 0 := by
  rw [countL_lt a b c hlt]
  cases hb : ((degree c - (degree a + degree b)) % a.length == 0) with
  | true => exact absurd (ground.beqEqOf hb) hmod
  | false => rfl

/-- The label count at or above the target's degree at a refused
divisibility is vacant: the lift's guard refuses. -/
theorem countL_geVac (a b c : Shape)
    (hge : ¬ degree a + degree b < degree c)
    (hmod : ¬ (degree a + degree b - degree c) % a.length = 0) :
    countL a b c = 0 := by
  rw [countL_ge a b c hge]
  cases hb : ((degree a + degree b - degree c) % a.length == 0) with
  | true => exact absurd (ground.beqEqOf hb) hmod
  | false => rfl

/-- The label count at or above the target's degree: the gap's
full columns enter the target at the divisibility guard, and the
lifted count is the block count outright (`con:labels`' descent at
the deficient target).  The two widths are the frame carrying the
lifted count's own read; the ordering and the divisibility are the
branch's own data. -/
theorem countL_geRead (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hle : degree c ≤ degree a + degree b)
    (hmod : (degree a + degree b - degree c) % a.length = 0) :
    countL a b c = blockcount.fusionCount a b
      (addFulls ((degree a + degree b - degree c) / a.length) c) := by
  have hnlt : ¬ degree a + degree b < degree c :=
    fun hlt => Nat.not_succ_le_self (degree a + degree b)
      (Nat.le_trans hlt hle)
  rw [countL_ge a b c hnlt, hmod,
    if_pos (show ((0 : Nat)) == 0 from rfl)]
  exact steinberg.count_fusion a b
    (addFulls ((degree a + degree b - degree c) / a.length) c) hba
    ((length_addFulls _ c).trans hca)

/-- The label count below the target's degree: the gap's full
columns enter the first shape at the divisibility guard, and the
lifted count is the block count outright (`con:labels`' descent at
the deficient first shape).  The second shape's width is
load-bearing with its committed refusal; the target's width is the
frame carrying the lifted count's own read, and the ordering and
the divisibility are the branch's own data. -/
theorem countL_ltRead (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hlt : degree a + degree b < degree c)
    (hmod : (degree c - (degree a + degree b)) % a.length = 0) :
    countL a b c = blockcount.fusionCount
      (addFulls ((degree c - (degree a + degree b)) / a.length) a)
      b c := by
  have hal : (addFulls ((degree c - (degree a + degree b))
      / a.length) a).length = a.length :=
    length_addFulls _ a
  rw [countL_lt a b c hlt, hmod,
    if_pos (show ((0 : Nat)) == 0 from rfl)]
  exact steinberg.count_fusion
    (addFulls ((degree c - (degree a + degree b)) / a.length) a) b c
    (hba.trans hal.symm) (hca.trans hal.symm)

/-- The label count at matched degrees is the block count: the
lift is vacant there, the count `cor:steinberg`'s own read at the
stated shapes (`con:labels`' descent at the matched degree). -/
theorem countL_matched (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length)
    (hdeg : degree a + degree b = degree c) :
    countL a b c = blockcount.fusionCount a b c := by
  have hsub : degree a + degree b - degree c = 0 := by
    rw [hdeg]
    exact Nat.sub_self (degree c)
  rw [countL_geRead a b c hba hca
      (by rw [hdeg]; exact Nat.le_refl (degree c))
      (by rw [hsub]; exact ground.modZeroLeft a.length),
    hsub, divZeroL a.length, addFulls_zero c]


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

/-- The dual label is its own representative: the complement shape
carries the unit occupancy at the full-column key. -/
theorem reduce_dualL (s : Shape) :
    reduce (dualL s) = dualL s := by
  cases s with
  | nil => rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, dualL_snoc s' a, reduce_snoc s'.reverse 0]

/-- The dual label is one value along the class: the added full
columns sit at the withdrawn key. -/
theorem dualL_addFulls (m : Nat) (s : Shape) :
    dualL (addFulls m s) = dualL s := by
  cases s with
  | nil => rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, addFulls_snoc m s' a, dualL_snoc s' (a + m),
        dualL_snoc s' a]

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

/-- The row list at the added full columns: every row grows by the
stated column count. -/
theorem rowList_addFulls (m : Nat) (s : Shape) :
    rowList (addFulls m s) = (rowList s).map (fun x => x + m) := by
  cases s with
  | nil => rfl
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hs, _⟩ =>
      rw [hs, addFulls_snoc m s' a, rowList_snoc s' (a + m),
        rowList_snoc s' a,
        ground.map_append (fun y => y + m)
          ((rowList s').map (fun y => y + a)) [a],
        ground.map_map (fun y => y + a) (fun y => y + m) (rowList s'),
        ground.map_congr_all (fun y => y + a + m)
          (fun y => y + (a + m)) (fun y => Nat.add_assoc y a m)
          (rowList s')]
      rfl

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

/-- The dual pair's own join at the shape first: the shape's rows
against its dual label's reversal read the occupancy total, one
full column per letter (`lem:dualread`(iii) at the label's own
dual). -/
theorem join_dual_selfR (s : Shape) :
    List.zipWith (fun x y => x + y) (rowList s)
        ((rowList (dualL s)).reverse)
      = List.replicate s.length (ground.sumNat s) := by
  cases s with
  | nil => rfl
  | cons x t =>
    have hp : 0 < (x :: t).length := Nat.succ_pos t.length
    have hj := dualL_join (dualL (x :: t)) (x :: t)
      (reduce_dualL (x :: t))
    rw [length_dualL (x :: t),
      Nat.add_comm (degree (dualL (x :: t))) (degree (x :: t)),
      degree_dualL_add (x :: t),
      Nat.mul_comm (x :: t).length (ground.sumNat (x :: t)),
      ground.divMulSelf (ground.sumNat (x :: t)) (x :: t).length hp]
      at hj
    exact hj

/-- The dual pair's own join at the dual label first: the dual
label's rows against the shape's reversal read the occupancy
total, the mirrored orientation of the same constant. -/
theorem join_dual_selfL (s : Shape) :
    List.zipWith (fun x y => x + y) (rowList (dualL s))
        ((rowList s).reverse)
      = List.replicate s.length (ground.sumNat s) := by
  cases s with
  | nil => rfl
  | cons x t =>
    have hp : 0 < (x :: t).length := Nat.succ_pos t.length
    have hj := dualL_join (x :: t) (dualL (x :: t))
      (dualL_dualL (x :: t)).symm
    rw [degree_dualL_add (x :: t),
      Nat.mul_comm (x :: t).length (ground.sumNat (x :: t)),
      ground.divMulSelf (ground.sumNat (x :: t)) (x :: t).length hp]
      at hj
    exact hj

/-! The class move at one full column (`con:labels`' descent
clause): the count is one value along the class in each argument.
The lift's guard and cofactor move by one modulus step at a moved
degree, so the two reads land at one Steinberg count — the moved
column entering the deficient side's own lift, or the target's at
the matched degrees, where the mapped span reads the fused counts
(`dualread.fusionCount_addFull`, the factors' exchange
`blockcount.fusionCount_comm`). -/

/-! The lift's reads at the block count: the added full columns
cancel between the first shape and the target
(`dualread.fusionCount_addFull` iterated), and a first shape lifted
past the target's deepest key counts vacantly
(`dualread.fusionCount_bump_off` at the withdrawn column). -/

/-- The block count is one value at the joint lift of the first
shape and the target: each added full column cancels across the
pair (`dualread.fusionCount_addFull`).  The second shape's width
is load-bearing with its committed refusal; the target's width is
the frame, carried across the lift by the one-column read's own
widths. -/
theorem fusionCount_addFullN (m : Nat) (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length) :
    blockcount.fusionCount (addFulls m a) b (addFulls m c)
      = blockcount.fusionCount a b c := by
  induction m with
  | zero => rw [addFulls_zero a, addFulls_zero c]
  | succ k ih =>
    have hlk : (addFulls k a).length = a.length := length_addFulls k a
    have hlc : (addFulls k c).length = a.length :=
      (length_addFulls k c).trans hca
    rw [addFulls_succ k a, addFulls_succ k c, hca,
      show a.length - 1 = (addFulls k a).length - 1 from by rw [hlk],
      dualread.fusionCount_addFull (addFulls k a) b (addFulls k c)
        (hba.trans hlk.symm) (hlc.trans hlk.symm)]
    exact ih

/-- The block count is vacant at a first shape lifted past the
target's deepest key: each added column raises the pool's deepest
letter, and at a target whose own deepest key sits below the
column count the lift is withdrawn one column at a time
(`dualread.fusionCount_addFull`) until the target's key is vacant
against a lifted first shape
(`dualread.fusionCount_bump_off`).  The two widths are frames,
both counts vacant at a forged width; the column count's strict
excess is load-bearing with its isolating contrast, and the letter
count's positivity is load-bearing with its committed refusal. -/
theorem fusionCount_colOff (j : Nat) (a b X : Shape)
    (hba : b.length = a.length) (hXa : X.length = a.length)
    (hlt : ground.getAt 0 (places.rowList X) (a.length - 1) < j)
    (hd : 0 < a.length) :
    blockcount.fusionCount (addFulls j a) b X = 0 := by
  induction j generalizing X with
  | zero => exact absurd hlt (Nat.not_lt_zero _)
  | succ m ih =>
    have hlk : (addFulls m a).length = a.length := length_addFulls m a
    have hpred : a.length - 1 + 1 = a.length := ground.subAdd hd
    match ground.snoc_split (a.length - 1) X (hXa.trans hpred.symm) with
    | ⟨s', x, hXe, hsl⟩ =>
      have hlast : ground.getAt 0 (places.rowList X) (a.length - 1)
          = x := by
        rw [places.rowList_last X (a.length - 1) (hXa.trans hpred.symm),
          hXe, ← hsl]
        exact ground.getAt_append_add 0 s' [x] 0
      rw [addFulls_succ m a,
        show a.length - 1 = (addFulls m a).length - 1 from by rw [hlk]]
      cases x with
      | zero =>
        exact dualread.fusionCount_bump_off (addFulls m a) b X
          (hba.trans hlk.symm)
          (by rw [hlk]; exact hlast) (by rw [hlk]; exact hd)
      | succ k =>
        have hX0l : (s' ++ [k]).length = a.length := by
          rw [ground.length_append s' [k], hsl]
          exact hpred
        have hbump : X = ground.bumpAt ((addFulls m a).length - 1)
            (s' ++ [k]) := by
          rw [hlk, ← hsl, hXe, ground.bumpAt_snoc s' k]
        have hlast0 : ground.getAt 0 (places.rowList (s' ++ [k]))
            (a.length - 1) = k := by
          rw [places.rowList_last (s' ++ [k]) (a.length - 1)
              (hX0l.trans hpred.symm), ← hsl]
          exact ground.getAt_append_add 0 s' [k] 0
        rw [hlast] at hlt
        rw [hbump, dualread.fusionCount_addFull (addFulls m a) b
          (s' ++ [k]) (hba.trans hlk.symm) (hX0l.trans hlk.symm)]
        refine ih (s' ++ [k]) hX0l ?_
        rw [hlast0]
        exact Nat.lt_of_succ_lt_succ hlt

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
      rw [dualread.fusionCount_bump_off x y c hyx hlast hd,
        blockcount.fusionCount_comm x
        (ground.bumpAt (x.length - 1) y) c (hyl.trans hyx), ← hyx]
      exact (dualread.fusionCount_bump_off y x c hyx.symm
        (by rw [hyx]; exact hlast)
        (by rw [hyx]; exact hd)).symm
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

/-- The full columns move between the two factors one at a time:
the one-column move iterated along the lift. -/
private theorem fusion_moveN : ∀ (m : Nat) (x y c : Shape),
    y.length = x.length → c.length = x.length → 0 < x.length →
    blockcount.fusionCount (addFulls m x) y c
      = blockcount.fusionCount x (addFulls m y) c
  | 0, x, y, _, _, _, _ => by rw [addFulls_zero x, addFulls_zero y]
  | m + 1, x, y, c, hyx, hcx, hd => by
    rw [addFulls_succ m x,
      show x.length - 1 = (addFulls m x).length - 1 from by
        rw [length_addFulls],
      fusion_move (addFulls m x) y c
        (by rw [length_addFulls]; exact hyx)
        (by rw [length_addFulls]; exact hcx)
        (by rw [length_addFulls]; exact hd),
      show (addFulls m x).length - 1 = y.length - 1 from by
        rw [length_addFulls, hyx],
      fusion_moveN m x (ground.bumpAt (y.length - 1) y) c
        (by rw [ground.length_bumpAt]; exact hyx) hcx hd,
      addFulls_bumped m y]

private theorem degree_bumpTop (s : Shape) (h : 0 < s.length) :
    degree (ground.bumpAt (s.length - 1) s) = degree s + s.length := by
  have hlt : s.length - 1 < s.length := ground.subOneLt h
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

/-- The label count is one value at the class in the first
argument at any column count: the added full columns iterate the
class's own one-column move (`countL_bumpA`).  The two widths are
the frame, carried across the lift by the class move's own
widths. -/
theorem countL_addFullsA (m : Nat) (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length) :
    countL (addFulls m a) b c = countL a b c := by
  induction m with
  | zero => rw [addFulls_zero a]
  | succ k ih =>
    have hlk : (addFulls k a).length = a.length := length_addFulls k a
    rw [addFulls_succ k a,
      show a.length - 1 = (addFulls k a).length - 1 from by rw [hlk],
      countL_bumpA (addFulls k a) b c (hba.trans hlk.symm)
        (hca.trans hlk.symm)]
    exact ih

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

/-- The label count is one value at the class in the target at any
column count: the added full columns iterate the class's own
one-column move (`countL_bumpC`).  The two widths are frames, the
class move reading one value at every width. -/
theorem countL_addFullsC (m : Nat) (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length) :
    countL a b (addFulls m c) = countL a b c := by
  induction m with
  | zero => rw [addFulls_zero c]
  | succ k ih =>
    have hlk : (addFulls k c).length = c.length := length_addFulls k c
    rw [addFulls_succ k c,
      show c.length - 1 = (addFulls k c).length - 1 from by rw [hlk],
      countL_bumpC a b (addFulls k c) hba (hlk.trans hca)]
    exact ih

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

/-- The count's exchange in its two factors, `prop:repring`'s
commutativity read at the label index: the two lifts meet at the
one-column moves and the fused span's own exchange. -/
theorem countL_comm (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    countL a b c = countL b a c := by
  match Nat.eq_zero_or_pos a.length with
  | Or.inl h0 =>
    rw [ground.nil_of_length_zero a h0,
      ground.nil_of_length_zero b (hba.trans h0),
      ground.nil_of_length_zero c (hca.trans h0)]
  | Or.inr hd =>
    by_cases h : degree a + degree b < degree c
    · rw [countL_lt a b c h,
        countL_lt b a c (by
          rw [Nat.add_comm (degree b) (degree a)]; exact h),
        hba, Nat.add_comm (degree b) (degree a)]
      by_cases hg :
          ((degree c - (degree a + degree b)) % a.length == 0) = true
      · rw [if_pos hg, if_pos hg,
          steinberg.count_fusion _ b c
            (by rw [length_addFulls]; exact hba)
            (by rw [length_addFulls]; exact hca),
          steinberg.count_fusion _ a c
            (by rw [length_addFulls, hba])
            (by rw [length_addFulls, hba]; exact hca),
          fusion_moveN _ a b c hba hca hd]
        exact blockcount.fusionCount_comm a
          (addFulls ((degree c - (degree a + degree b)) / a.length) b) c
          (by rw [length_addFulls]; exact hba)
      · rw [if_neg hg, if_neg hg]
    · rw [countL_ge a b c h,
        countL_ge b a c (by
          rw [Nat.add_comm (degree b) (degree a)]; exact h),
        hba, Nat.add_comm (degree b) (degree a)]
      by_cases hg :
          ((degree a + degree b - degree c) % a.length == 0) = true
      · rw [if_pos hg, if_pos hg,
          steinberg.count_fusion a b _ hba
            (by rw [length_addFulls]; exact hca),
          steinberg.count_fusion b a _ (by rw [hba])
            (by rw [length_addFulls, hba]; exact hca)]
        exact blockcount.fusionCount_comm a b _ hba
      · rw [if_neg hg, if_neg hg]

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

/-! `prop:repring`'s pairing collapse at the full-column target:
the fused pool's enumeration meets the full-column count at one
content — the target's own complement key (`lem:dualread`(iii)'s
join condition, one solution at the enumerated widths) — so the
fold reads one fusion count at that key, and where the complement
key is off the enumeration both sides read the count's unit. -/

private theorem zipAdd_mapR (c : Nat) (x y : List Nat) :
    List.zipWith (fun u w => u + w) x (y.map (fun u => u + c))
      = (List.zipWith (fun u w => u + w) x y).map (fun u => u + c) := by
  rw [ground.map_congr_all (fun u => u + c) (fun u => c + u)
      (fun u => Nat.add_comm u c) y,
    ground.zipWith_add_mapR c x y,
    ground.map_congr_all (fun u => c + u) (fun u => u + c)
      (fun u => Nat.add_comm c u)]

private theorem zipAdd_cancelR : ∀ x y z : List Nat,
    y.length = x.length → z.length = x.length →
    List.zipWith (fun u v => u + v) x y
      = List.zipWith (fun u v => u + v) x z → y = z
  | [], y, z, hy, hz, _ => by
    rw [ground.nil_of_length_zero y hy,
      ground.nil_of_length_zero z hz]
  | w :: x, y, z, hy, hz, h => by
    cases y with
    | nil => exact Nat.noConfusion hy
    | cons u y' =>
      cases z with
      | nil => exact Nat.noConfusion hz
      | cons v z' =>
        have h' : (w + u) :: List.zipWith (fun q e => q + e) x y'
            = (w + v) :: List.zipWith (fun q e => q + e) x z' := h
        rw [ground.addCancelL w (List.cons.inj h').1,
          zipAdd_cancelR x y' z' (Nat.succ.inj hy)
            (Nat.succ.inj hz) (List.cons.inj h').2]

private theorem zipAdd_cancelL : ∀ x y z : List Nat,
    y.length = x.length → z.length = x.length →
    List.zipWith (fun u v => u + v) y x
      = List.zipWith (fun u v => u + v) z x → y = z
  | [], y, z, hy, hz, _ => by
    rw [ground.nil_of_length_zero y hy,
      ground.nil_of_length_zero z hz]
  | w :: x, y, z, hy, hz, h => by
    cases y with
    | nil => exact Nat.noConfusion hy
    | cons u y' =>
      cases z with
      | nil => exact Nat.noConfusion hz
      | cons v z' =>
        have h' : (u + w) :: List.zipWith (fun q e => q + e) y' x
            = (v + w) :: List.zipWith (fun q e => q + e) z' x := h
        rw [ground.addCancelR w (List.cons.inj h').1,
          zipAdd_cancelL x y' z' (Nat.succ.inj hy)
            (Nat.succ.inj hz) (List.cons.inj h').2]

private theorem exhaustMu (d : Nat) (P : List blockcount.HVec)
    (hsz : ∀ x ∈ P, blockcount.sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      blockcount.settledAt P (blockcount.act i j x))
    (mu : List Nat)
    (hmu : mu ∈ (blockcount.exhaust d P).map
      blockcount.HVec.content) :
    rowList (places.shapeOf mu) = mu ∧ mu.length = d :=
  ⟨blockcount.exhaust_rowList_shapeOf d P hsz hwid hcl mu hmu,
   blockcount.exhaust_width d P hsz hwid hcl mu hmu⟩

private theorem foldDeltaPick (d : Nat) (P : List blockcount.HVec)
    (G : Shape → Nat) (D : List Nat → Nat) (K : Shape)
    (hone : D (rowList K) = 1)
    (hoff : ∀ mu, mu ∈ (blockcount.exhaust d P).map
        blockcount.HVec.content → ¬ mu = rowList K → D mu = 0)
    (hvac : ground.countOf (rowList K) ((blockcount.exhaust d P).map
        blockcount.HVec.content) = 0 → G K = 0) :
    ground.famFold Nat.add 0 (fun mu => G (places.shapeOf mu) * D mu)
      (ground.dedupL ((blockcount.exhaust d P).map
        blockcount.HVec.content))
      = G K := by
  rw [ground.famFold_congr_members Nat.add 0
    (fun mu => G (places.shapeOf mu) * D mu)
    (fun mu => if mu = rowList K then G (places.shapeOf mu) * D mu
      else 0) _ (fun x hx => by
      by_cases he : x = rowList K
      · rw [if_pos he]
      · rw [if_neg he, hoff x (ground.mem_of_dedupL
          (ground.mem_of_countOf_pos x _ hx)) he, Nat.mul_zero])]
  cases Nat.eq_zero_or_pos (ground.countOf (rowList K)
      ((blockcount.exhaust d P).map blockcount.HVec.content)) with
  | inl h0 =>
    have hLz : ground.countOf (rowList K)
        (ground.dedupL ((blockcount.exhaust d P).map
          blockcount.HVec.content)) = 0 := by
      cases Nat.eq_zero_or_pos (ground.countOf (rowList K)
          (ground.dedupL ((blockcount.exhaust d P).map
            blockcount.HVec.content))) with
      | inl hz => exact hz
      | inr hpos =>
        have hc := ground.countOf_pos_of_mem (ground.mem_of_dedupL
          (ground.mem_of_countOf_pos _ _ hpos))
        rw [h0] at hc
        exact absurd hc (Nat.lt_irrefl 0)
    rw [ground.famFold_pickZero
      (fun mu => G (places.shapeOf mu) * D mu) (rowList K) _ hLz]
    exact (hvac h0).symm
  | inr hpos =>
    rw [ground.famFold_pick (fun mu => G (places.shapeOf mu) * D mu)
      (rowList K) _ (ground.countOf_dedupL_one
        (ground.mem_of_countOf_pos _ _ hpos))]
    show G (places.shapeOf (rowList K)) * D (rowList K) = G K
    rw [places.shapeOf_rowList K, hone, Nat.mul_one]

private theorem foldDeltaZero (d : Nat) (P : List blockcount.HVec)
    (G : Shape → Nat) (D : List Nat → Nat)
    (hoff : ∀ mu, mu ∈ (blockcount.exhaust d P).map
      blockcount.HVec.content → D mu = 0) :
    ground.famFold Nat.add 0 (fun mu => G (places.shapeOf mu) * D mu)
      (ground.dedupL ((blockcount.exhaust d P).map
        blockcount.HVec.content))
      = 0 := by
  rw [ground.famFold_congr_members Nat.add 0
    (fun mu => G (places.shapeOf mu) * D mu) (fun _ => 0) _
    (fun x hx => by
      rw [hoff x (ground.mem_of_dedupL
        (ground.mem_of_countOf_pos x _ hx)), Nat.mul_zero])]
  exact ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) _

/-- The first pairing's fold at the full-column target: the fused
pool of the lifted first shape with the second, enumerated at its
own contents, meets the full-column count at exactly the target's
complement key, so the fold reads that key's fusion count
(`prop:repring`'s third read at the first read's delta,
`lem:dualread`(iii)).  The two widths carry the pool's enumeration
and the delta's join, and the floor `hp` is the complement key's
column count, the join's own datum. -/
theorem foldCollapseL (a b c : Shape) (p M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hp : ground.sumNat c ≤ M + p) :
    ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls p a) b
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) c
          (dualread.fulls a.length (M + p)))
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt
          (blockcount.blockSpan (addFulls p a))
          (blockcount.blockSpan b))).map blockcount.HVec.content))
    = blockcount.fusionCount (addFulls p a) b
        (addFulls (M + p - ground.sumNat c) (dualL c)) := by
  have hXl : (addFulls p a).length = a.length := length_addFulls p a
  have hbX : b.length = (addFulls p a).length := hba.trans hXl.symm
  obtain ⟨hszP, hwidP, hclP, _⟩ :=
    blockcount.fusedSpan_pack (addFulls p a) b hbX
  rw [hXl] at hwidP hclP
  have hKl : (addFulls (M + p - ground.sumNat c) (dualL c)).length
      = a.length :=
    (length_addFulls _ (dualL c)).trans ((length_dualL c).trans hca)
  have hsum : ground.sumNat c + (M + p - ground.sumNat c) = M + p :=
    match Nat.le.dest hp with
    | ⟨g, hg⟩ => by
      rw [← hg, ground.addSubSelfL (ground.sumNat c) g]
  have hwit : List.zipWith (fun x y => x + y) (rowList c)
      ((rowList (addFulls (M + p - ground.sumNat c)
        (dualL c))).reverse)
      = List.replicate a.length (M + p) := by
    rw [rowList_addFulls (M + p - ground.sumNat c) (dualL c),
      ground.map_reverse (fun x => x + (M + p - ground.sumNat c))
        (rowList (dualL c)),
      zipAdd_mapR (M + p - ground.sumNat c) (rowList c)
        ((rowList (dualL c)).reverse),
      join_dual_selfR c,
      ground.map_replicate (fun x => x + (M + p - ground.sumNat c))
        (ground.sumNat c) c.length, hca, hsum]
  have hdel : ∀ mu, mu ∈ (blockcount.exhaust a.length
      (blockcount.fusedAt (blockcount.blockSpan (addFulls p a))
        (blockcount.blockSpan b))).map blockcount.HVec.content →
      blockcount.fusionCount (places.shapeOf mu) c
          (dualread.fulls a.length (M + p))
        = if List.zipWith (fun x y => x + y) (rowList c) mu.reverse
            = List.replicate a.length (M + p) then 1 else 0 := by
    intro mu hmu
    match exhaustMu a.length _ hszP hwidP hclP mu hmu with
    | ⟨hrt, hml⟩ =>
      have hsl : (places.shapeOf mu).length = a.length :=
        (places.length_shapeOf mu).trans hml
      have hfc := dualread.fusionCount_fulls (places.shapeOf mu) c
        (M + p) (hca.trans hsl.symm)
      rw [hsl, hrt] at hfc
      exact hfc
  refine foldDeltaPick a.length _
    (fun x => blockcount.fusionCount (addFulls p a) b x)
    (fun mu => blockcount.fusionCount (places.shapeOf mu) c
      (dualread.fulls a.length (M + p)))
    (addFulls (M + p - ground.sumNat c) (dualL c)) ?_ ?_ ?_
  · show blockcount.fusionCount (places.shapeOf (rowList
      (addFulls (M + p - ground.sumNat c) (dualL c)))) c
      (dualread.fulls a.length (M + p)) = 1
    rw [places.shapeOf_rowList
      (addFulls (M + p - ground.sumNat c) (dualL c))]
    have hfc := dualread.fusionCount_fulls
      (addFulls (M + p - ground.sumNat c) (dualL c)) c (M + p)
      (hca.trans hKl.symm)
    rw [hKl, if_pos hwit] at hfc
    exact hfc
  · intro mu hmu hne
    show blockcount.fusionCount (places.shapeOf mu) c
      (dualread.fulls a.length (M + p)) = 0
    rw [hdel mu hmu]
    refine if_neg (fun hc => hne ?_)
    have hml := blockcount.exhaust_width a.length _
      hszP hwidP hclP mu hmu
    have hlx : (rowList c).length = a.length :=
      (places.length_rowList c).trans hca
    have h1 : mu.reverse.length = (rowList c).length := by
      rw [ground.length_reverse, hml, hlx]
    have h2 : (rowList (addFulls (M + p - ground.sumNat c)
        (dualL c))).reverse.length = (rowList c).length := by
      rw [ground.length_reverse, places.length_rowList, hKl, hlx]
    have h3 := congrArg List.reverse (zipAdd_cancelR (rowList c)
      mu.reverse (rowList (addFulls (M + p - ground.sumNat c)
        (dualL c))).reverse h1 h2 (hc.trans hwit.symm))
    rw [ground.reverse_reverse mu, ground.reverse_reverse
      (rowList (addFulls (M + p - ground.sumNat c) (dualL c)))]
      at h3
    exact h3
  · intro h0
    show blockcount.fusionCount (addFulls p a) b
      (addFulls (M + p - ground.sumNat c) (dualL c)) = 0
    rw [blockcount.fusionCount_countOf (addFulls p a) b
        (addFulls (M + p - ground.sumNat c) (dualL c)) hbX, hXl]
    exact h0

/-- The second pairing's fold at the full-column target: the fused
pool of the second and third shapes, enumerated at its own
contents, meets the lifted first shape's full-column count at
exactly the first shape's complement key — the lift's own columns
entering both sides of the join — so the fold reads that key's
fusion count with the lift's count `p` withdrawn
(`prop:repring`'s third read at the first read's delta,
`lem:dualread`(iii)).  The two widths carry the pool's enumeration
and the delta's join, and the floor `hMa` is the complement key's
column count, the join's own datum. -/
theorem foldCollapseR (a b c : Shape) (p M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hMa : ground.sumNat a ≤ M) :
    ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount b c (places.shapeOf mu)
        * blockcount.fusionCount (addFulls p a)
          (places.shapeOf mu) (dualread.fulls a.length (M + p)))
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan b)
          (blockcount.blockSpan c))).map blockcount.HVec.content))
    = blockcount.fusionCount b c
        (addFulls (M - ground.sumNat a) (dualL a)) := by
  have hXl : (addFulls p a).length = a.length := length_addFulls p a
  have hcb : c.length = b.length := hca.trans hba.symm
  obtain ⟨hszP, hwidP, hclP, _⟩ := blockcount.fusedSpan_pack b c hcb
  rw [hba] at hwidP hclP
  have hKl : (addFulls (M - ground.sumNat a) (dualL a)).length
      = a.length :=
    (length_addFulls _ (dualL a)).trans (length_dualL a)
  have hsum : ground.sumNat a + (M - ground.sumNat a) = M :=
    match Nat.le.dest hMa with
    | ⟨g, hg⟩ => by
      rw [← hg, ground.addSubSelfL (ground.sumNat a) g]
  have hwit : List.zipWith (fun x y => x + y)
      (rowList (addFulls (M - ground.sumNat a) (dualL a)))
      ((rowList (addFulls p a)).reverse)
      = List.replicate a.length (M + p) := by
    rw [rowList_addFulls (M - ground.sumNat a) (dualL a),
      rowList_addFulls p a,
      ground.map_reverse (fun x => x + p) (rowList a),
      zipAdd_mapL (M - ground.sumNat a) (rowList (dualL a))
        (((rowList a).reverse).map (fun x => x + p)),
      zipAdd_mapR p (rowList (dualL a)) ((rowList a).reverse),
      join_dual_selfL a,
      ground.map_replicate (fun x => x + p) (ground.sumNat a)
        a.length,
      ground.map_replicate (fun x => x + (M - ground.sumNat a))
        (ground.sumNat a + p) a.length,
      Nat.add_right_comm (ground.sumNat a) p
        (M - ground.sumNat a), hsum]
  have hdel : ∀ mu, mu ∈ (blockcount.exhaust a.length
      (blockcount.fusedAt (blockcount.blockSpan b)
        (blockcount.blockSpan c))).map blockcount.HVec.content →
      blockcount.fusionCount (addFulls p a) (places.shapeOf mu)
          (dualread.fulls a.length (M + p))
        = if List.zipWith (fun x y => x + y) mu
            ((rowList (addFulls p a)).reverse)
            = List.replicate a.length (M + p) then 1 else 0 := by
    intro mu hmu
    match exhaustMu a.length _ hszP hwidP hclP mu hmu with
    | ⟨hrt, hml⟩ =>
      have hsl : (places.shapeOf mu).length = a.length :=
        (places.length_shapeOf mu).trans hml
      have hfc := dualread.fusionCount_fulls (addFulls p a)
        (places.shapeOf mu) (M + p) (hsl.trans hXl.symm)
      rw [hXl, hrt] at hfc
      exact hfc
  refine foldDeltaPick a.length _
    (fun x => blockcount.fusionCount b c x)
    (fun mu => blockcount.fusionCount (addFulls p a)
      (places.shapeOf mu) (dualread.fulls a.length (M + p)))
    (addFulls (M - ground.sumNat a) (dualL a)) ?_ ?_ ?_
  · show blockcount.fusionCount (addFulls p a) (places.shapeOf
      (rowList (addFulls (M - ground.sumNat a) (dualL a))))
      (dualread.fulls a.length (M + p)) = 1
    rw [places.shapeOf_rowList
      (addFulls (M - ground.sumNat a) (dualL a))]
    have hfc := dualread.fusionCount_fulls (addFulls p a)
      (addFulls (M - ground.sumNat a) (dualL a)) (M + p)
      (hKl.trans hXl.symm)
    rw [hXl, if_pos hwit] at hfc
    exact hfc
  · intro mu hmu hne
    show blockcount.fusionCount (addFulls p a) (places.shapeOf mu)
      (dualread.fulls a.length (M + p)) = 0
    rw [hdel mu hmu]
    refine if_neg (fun hc => hne ?_)
    have hml := blockcount.exhaust_width a.length _
      hszP hwidP hclP mu hmu
    have hlx : ((rowList (addFulls p a)).reverse).length
        = a.length := by
      rw [ground.length_reverse, places.length_rowList, hXl]
    have h1 : mu.length = ((rowList (addFulls p a)).reverse).length
      := by rw [hlx, hml]
    have h2 : (rowList (addFulls (M - ground.sumNat a)
        (dualL a))).length
        = ((rowList (addFulls p a)).reverse).length := by
      rw [hlx, places.length_rowList, hKl]
    exact zipAdd_cancelL ((rowList (addFulls p a)).reverse) mu
      (rowList (addFulls (M - ground.sumNat a) (dualL a))) h1 h2
      (hc.trans hwit.symm)
  · intro h0
    show blockcount.fusionCount b c
      (addFulls (M - ground.sumNat a) (dualL a)) = 0
    rw [blockcount.fusionCount_countOf b c
        (addFulls (M - ground.sumNat a) (dualL a)) hcb, hba]
    exact h0

/-- The second pairing's fold below the first shape's occupancy
total: an enumerated content's row list heads at its occupancy
total, so the lifted first shape's join already exceeds the
full-column constant at the last position and every summand is
vacant (`prop:repring`'s third read at the refused delta). -/
theorem foldCollapseR_vacant (a b c : Shape) (p M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hlt : M < ground.sumNat a) :
    ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount b c (places.shapeOf mu)
        * blockcount.fusionCount (addFulls p a)
          (places.shapeOf mu) (dualread.fulls a.length (M + p)))
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan b)
          (blockcount.blockSpan c))).map blockcount.HVec.content))
    = 0 := by
  have hd : 0 < a.length := by
    match Nat.eq_zero_or_pos a.length with
    | Or.inr h => exact h
    | Or.inl h0 =>
      rw [ground.nil_of_length_zero a h0] at hlt
      exact absurd hlt (Nat.not_lt_zero M)
  have hXl : (addFulls p a).length = a.length := length_addFulls p a
  have hXp : 0 < (addFulls p a).length := by
    rw [hXl]
    exact hd
  have hcb : c.length = b.length := hca.trans hba.symm
  obtain ⟨hszP, hwidP, hclP, _⟩ := blockcount.fusedSpan_pack b c hcb
  rw [hba] at hwidP hclP
  have hr : a.length - 1 < a.length := ground.subOneLt hd
  refine foldDeltaZero a.length _
    (fun x => blockcount.fusionCount b c x)
    (fun mu => blockcount.fusionCount (addFulls p a)
      (places.shapeOf mu) (dualread.fulls a.length (M + p)))
    ?_
  intro mu hmu
  show blockcount.fusionCount (addFulls p a) (places.shapeOf mu)
    (dualread.fulls a.length (M + p)) = 0
  match exhaustMu a.length _ hszP hwidP hclP mu hmu with
  | ⟨hrt, hml⟩ =>
    have hsl : (places.shapeOf mu).length = a.length :=
      (places.length_shapeOf mu).trans hml
    have hfc := dualread.fusionCount_fulls (addFulls p a)
      (places.shapeOf mu) (M + p) (hsl.trans hXl.symm)
    rw [hXl, hrt] at hfc
    rw [hfc]
    refine if_neg (fun hc => ?_)
    have hgz : ground.getAt 0 (List.zipWith (fun x y => x + y) mu
        ((rowList (addFulls p a)).reverse)) (a.length - 1)
      = ground.getAt 0 (List.replicate a.length (M + p))
        (a.length - 1) :=
      congrArg (fun l => ground.getAt 0 l (a.length - 1)) hc
    rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) mu
        ((rowList (addFulls p a)).reverse) (a.length - 1)
        (by rw [hml]; exact hr)
        (by rw [ground.length_reverse, places.length_rowList, hXl]
            exact hr),
      ground.getAt_reverse 0 (rowList (addFulls p a))
        (a.length - 1) 0
        (by rw [places.length_rowList, hXl, Nat.add_zero]
            exact ground.subAdd hd),
      rowList_head (addFulls p a) hXp,
      sumNat_addFulls_occ p a hd,
      ground.getAt_replicate 0 (M + p) a.length (a.length - 1) hr]
      at hgz
    have h2 : ground.sumNat a + ground.getAt 0 mu (a.length - 1) + p
        = M + p := by
      rw [Nat.add_right_comm (ground.sumNat a)
          (ground.getAt 0 mu (a.length - 1)) p,
        Nat.add_comm (ground.sumNat a + p)
          (ground.getAt 0 mu (a.length - 1))]
      exact hgz
    exact absurd (Nat.le.intro (ground.addCancelR p h2))
      (Nat.not_le_of_lt hlt)

/-- The label count at a refused divisibility: at a target whose
degree joins a stated total to the width's multiple, a first
pairing whose degree total misses the width's multiples against
that total misses them on either side of the lift's branch, so the
guard refuses and the count is vacant. -/
private theorem countL_vacantMod (x y z : Shape) (w M : Nat)
    (hK : degree z + w = M * x.length)
    (hs : ¬ (degree x + degree y + w) % x.length = 0) :
    countL x y z = 0 := by
  match Nat.lt_or_ge (degree x + degree y) (degree z) with
  | Or.inl hlt =>
    have hj : degree x + degree y + (degree z - (degree x + degree y))
        = degree z := ground.natAddSubCancel (Nat.le_of_lt hlt)
    have hsum : (degree z - (degree x + degree y))
        + (degree x + degree y + w) = M * x.length := by
      rw [← Nat.add_assoc, Nat.add_comm
          (degree z - (degree x + degree y)) (degree x + degree y), hj]
      exact hK
    have hne : ¬ (degree z - (degree x + degree y)) % x.length = 0 := by
      intro hg
      refine hs ?_
      have h1 := ground.modAdd (degree z - (degree x + degree y))
        (degree x + degree y + w) x.length
      rw [hg, Nat.zero_add, ground.modMod, hsum,
        ground.modMulSelf] at h1
      exact h1
    rw [countL_lt x y z hlt]
    cases hb : ((degree z - (degree x + degree y)) % x.length == 0) with
    | true => exact absurd (ground.beqEqOf hb) hne
    | false => rfl
  | Or.inr hge =>
    have hj : degree z + (degree x + degree y - degree z)
        = degree x + degree y := ground.natAddSubCancel hge
    have hsum : (degree x + degree y - degree z) + M * x.length
        = degree x + degree y + w := by
      rw [← hK, ← Nat.add_assoc, Nat.add_comm
        (degree x + degree y - degree z) (degree z), hj]
    have hne : ¬ (degree x + degree y - degree z) % x.length = 0 := by
      intro hg
      refine hs ?_
      rw [← hsum, ground.modAddMul]
      exact hg
    rw [countL_ge x y z (fun hlt => Nat.not_succ_le_self
      (degree x + degree y) (Nat.le_trans hlt hge))]
    cases hb : ((degree x + degree y - degree z) % x.length == 0) with
    | true => exact absurd (ground.beqEqOf hb) hne
    | false => rfl

/-- The lift is injective at an occupied width: the added columns
sit on the last key alone and cancel. -/
private theorem addFulls_inj (m : Nat) (x y : Shape)
    (hx : 0 < x.length) (h : addFulls m x = addFulls m y) : x = y := by
  have hly : y.length = x.length := by
    rw [← length_addFulls m y, ← h, length_addFulls m x]
  match ground.snoc_split (x.length - 1) x (ground.subAdd hx).symm with
  | ⟨x', p, hxe, hxl⟩ =>
    match ground.snoc_split (x.length - 1) y
        (hly.trans (ground.subAdd hx).symm) with
    | ⟨y', q, hye, hyl⟩ =>
      rw [hxe, hye, addFulls_snoc m x' p, addFulls_snoc m y' q] at h
      match ground.append_inj_len x' y' [p + m] [q + m]
          (hxl.trans hyl.symm) h with
      | ⟨hpre, hsuf⟩ =>
        have hpq : p = q := ground.addCancelR m (List.cons.inj hsuf).1
        rw [hxe, hye, hpre, hpq]

/-- The lifted carrier's fold: at a weight vacant on every shape
whose deepest key sits below the column count, the enumeration at
the lifted degree folds the weight exactly as the enumeration at
the base degree folds the weight along the lift — the lift is
injective and its image is the enumeration's members at or above
the column count. -/
private theorem foldLift (j D k : Nat) (hd : 0 < D) (G : Shape → Nat)
    (hoff : ∀ X : Shape, X.length = D →
      ground.getAt 0 (rowList X) (D - 1) < j → G X = 0) :
    ground.famFold Nat.add 0 G (places.allShapes D (k + j * D))
      = ground.famFold Nat.add 0 (fun e => G (addFulls j e))
        (places.allShapes D k) := by
  have hpred : D - 1 + 1 = D := ground.subAdd hd
  have hA : ∀ x : Shape,
      0 < ground.countOf x ((places.allShapes D k).map (addFulls j)) →
      ground.countOf x (places.allShapes D (k + j * D)) = 1 := by
    intro x hx
    match ground.mem_map_of (addFulls j) (places.allShapes D k) x
        (ground.mem_of_countOf_pos x _ hx) with
    | ⟨e, he, hex⟩ =>
      obtain ⟨hel, hed⟩ := places.allShapes_sound D k e he
      have hxl : x.length = D := by
        rw [← hex, length_addFulls j e]
        exact hel
      have hxd : degree x = k + j * D := by
        rw [← hex, degree_addFulls j e, hed, hel]
      refine Nat.le_antisymm
        (places.countOf_allShapes_le D (k + j * D) x) ?_
      refine ground.countOf_pos_of_mem ?_
      rw [← hxd]
      exact places.mem_allShapes D x hxl
  rw [← ground.famFold_map Nat.add 0 G (addFulls j)
      (places.allShapes D k),
    ground.famFold_countCollect G
      ((places.allShapes D k).map (addFulls j))
      (places.allShapes D (k + j * D)) hA]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (places.allShapes D (k + j * D)) ?_
  intro m hm
  obtain ⟨hml, hmd⟩ := places.allShapes_sound D (k + j * D) m
    (ground.mem_of_countOf_pos m _ hm)
  match ground.snoc_split (D - 1) m (hml.trans hpred.symm) with
  | ⟨m', p, hme, hml'⟩ =>
    have hlast : ground.getAt 0 (rowList m) (D - 1) = p := by
      rw [places.rowList_last m (D - 1) (hml.trans hpred.symm), hme,
        ← hml']
      exact ground.getAt_append_add 0 m' [p] 0
    match Nat.lt_or_ge p j with
    | Or.inl hlt =>
      rw [hoff m hml (by rw [hlast]; exact hlt), Nat.mul_zero]
    | Or.inr hge =>
      have hm0l : (m' ++ [p - j]).length = D := by
        rw [ground.length_append m' [p - j], hml']
        exact hpred
      have hlift : addFulls j (m' ++ [p - j]) = m := by
        rw [addFulls_snoc j m' (p - j), ground.subAdd hge, hme]
      have hm0d : degree (m' ++ [p - j]) = k := by
        refine ground.addCancelR (j * D) ?_
        rw [← hm0l, ← degree_addFulls j (m' ++ [p - j]), hlift, hmd,
          hm0l]
      have hinj : ∀ y : Shape,
          0 < ground.countOf y (places.allShapes D k) →
          addFulls j y = addFulls j (m' ++ [p - j]) →
          y = m' ++ [p - j] := by
        intro y hy hyy
        refine addFulls_inj j y (m' ++ [p - j]) ?_ hyy
        rw [(places.allShapes_sound D k y
          (ground.mem_of_countOf_pos y _ hy)).1]
        exact hd
      have hc : ground.countOf m
          ((places.allShapes D k).map (addFulls j)) = 1 := by
        rw [← hlift, ground.countOf_map_inj (addFulls j)
          (m' ++ [p - j]) (places.allShapes D k) hinj]
        refine Nat.le_antisymm (places.countOf_allShapes_le D k _) ?_
        refine ground.countOf_pos_of_mem ?_
        rw [← hm0d]
        exact places.mem_allShapes D _ hm0l
      rw [hc, Nat.one_mul]

/-! The carrier bridge: the matched-degree shape enumeration and
the fused pool's own distinct contents index one weighted fold —
the block count at a shape is that shape's row list's occupancy in
the pool's contents (`blockcount.fusionCount_countOf`), the
contents' shapes sit once each in the enumeration
(`places.mem_allShapes` at `blockcount.exhaust_width` and
`blockcount.exhaust_degree`, `places.countOf_allShapes_le`), and
both folds meet at the raw contents' own
(`ground.famFold_countCollect`). -/

/-- The weighted block-count fold reads one value over the two
carriers: the matched-degree enumeration and the fused pool's
distinct contents, at any weight on the shapes.  The one letter
width is load-bearing with its committed refusal, the two
carriers parting at a forged second shape. -/
theorem bridgeFold (a b : Shape) (hba : b.length = a.length)
    (F : Shape → Nat) :
    ground.famFold Nat.add 0
      (fun e => blockcount.fusionCount a b e * F e)
      (places.allShapes a.length (degree a + degree b))
    = ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount a b (places.shapeOf mu)
        * F (places.shapeOf mu))
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan a)
          (blockcount.blockSpan b))).map blockcount.HVec.content)) := by
  obtain ⟨hszP, hwidP, hclP, _⟩ := blockcount.fusedSpan_pack a b hba
  have hrl := blockcount.exhaust_rowList_shapeOf a.length
    (blockcount.fusedAt (blockcount.blockSpan a)
      (blockcount.blockSpan b)) hszP hwidP hclP
  have hwd := blockcount.exhaust_width a.length
    (blockcount.fusedAt (blockcount.blockSpan a)
      (blockcount.blockSpan b)) hszP hwidP hclP
  have hdg := blockcount.exhaust_degree a b hba
  have hmemS : ∀ mu ∈ (blockcount.exhaust a.length
      (blockcount.fusedAt (blockcount.blockSpan a)
        (blockcount.blockSpan b))).map blockcount.HVec.content,
      places.shapeOf mu
        ∈ places.allShapes a.length (degree a + degree b) := by
    intro mu hmu
    have hlen : (places.shapeOf mu).length = a.length := by
      rw [places.length_shapeOf]
      exact hwd mu hmu
    have hdeg : degree (places.shapeOf mu) = degree a + degree b := by
      show ground.sumNat (places.rowList (places.shapeOf mu)) = _
      rw [hrl mu hmu]
      exact hdg mu hmu
    rw [← hdeg]
    exact places.mem_allShapes a.length (places.shapeOf mu) hlen
  have hD : ∀ x : List Nat,
      0 < ground.countOf x ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan a)
          (blockcount.blockSpan b))).map blockcount.HVec.content) →
      ground.countOf x (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan a)
          (blockcount.blockSpan b))).map blockcount.HVec.content))
        = 1 :=
    fun x hx =>
      ground.countOf_dedupL_one (ground.mem_of_countOf_pos x _ hx)
  have hD' : ∀ x : List Nat,
      0 < ground.countOf x ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan a)
          (blockcount.blockSpan b))).map blockcount.HVec.content) →
      ground.countOf x ((places.allShapes a.length
        (degree a + degree b)).map places.rowList) = 1 := by
    intro x hx
    have hmem := ground.mem_of_countOf_pos x _ hx
    rw [← hrl x hmem, ground.countOf_map_inj places.rowList
      (places.shapeOf x) (places.allShapes a.length (degree a + degree b))
      (fun y _ hy => places.rowList_inj y (places.shapeOf x) hy)]
    exact Nat.le_antisymm
      (places.countOf_allShapes_le a.length (degree a + degree b) _)
      (ground.countOf_pos_of_mem (hmemS x hmem))
  have hL1 : ground.famFold Nat.add 0
      (fun e => blockcount.fusionCount a b e * F e)
      (places.allShapes a.length (degree a + degree b))
      = ground.famFold Nat.add 0
        (fun e => ground.countOf (places.rowList e)
          ((blockcount.exhaust a.length
            (blockcount.fusedAt (blockcount.blockSpan a)
              (blockcount.blockSpan b))).map blockcount.HVec.content)
          * F e)
        (places.allShapes a.length (degree a + degree b)) :=
    ground.famFold_congr_all Nat.add 0 _ _
      (fun e => by rw [blockcount.fusionCount_countOf a b e hba])
      (places.allShapes a.length (degree a + degree b))
  have hL2 : ground.famFold Nat.add 0
      (fun mu => ground.countOf mu ((blockcount.exhaust a.length
          (blockcount.fusedAt (blockcount.blockSpan a)
            (blockcount.blockSpan b))).map blockcount.HVec.content)
        * F (places.shapeOf mu))
      ((places.allShapes a.length (degree a + degree b)).map
        places.rowList)
      = ground.famFold Nat.add 0
        (fun e => ground.countOf (places.rowList e)
          ((blockcount.exhaust a.length
            (blockcount.fusedAt (blockcount.blockSpan a)
              (blockcount.blockSpan b))).map blockcount.HVec.content)
          * F e)
        (places.allShapes a.length (degree a + degree b)) := by
    rw [ground.famFold_map Nat.add 0
      (fun mu => ground.countOf mu ((blockcount.exhaust a.length
          (blockcount.fusedAt (blockcount.blockSpan a)
            (blockcount.blockSpan b))).map blockcount.HVec.content)
        * F (places.shapeOf mu)) places.rowList
      (places.allShapes a.length (degree a + degree b))]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun e => by rw [places.shapeOf_rowList e])
      (places.allShapes a.length (degree a + degree b))
  have hL3 := ground.famFold_countCollect
    (fun mu => F (places.shapeOf mu))
    ((blockcount.exhaust a.length
      (blockcount.fusedAt (blockcount.blockSpan a)
        (blockcount.blockSpan b))).map blockcount.HVec.content)
    ((places.allShapes a.length (degree a + degree b)).map
      places.rowList) hD'
  have hR1 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount a b (places.shapeOf mu)
        * F (places.shapeOf mu))
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan a)
          (blockcount.blockSpan b))).map blockcount.HVec.content))
      = ground.famFold Nat.add 0
        (fun mu => ground.countOf mu ((blockcount.exhaust a.length
            (blockcount.fusedAt (blockcount.blockSpan a)
              (blockcount.blockSpan b))).map blockcount.HVec.content)
          * F (places.shapeOf mu))
        (ground.dedupL ((blockcount.exhaust a.length
          (blockcount.fusedAt (blockcount.blockSpan a)
            (blockcount.blockSpan b))).map blockcount.HVec.content)) :=
    ground.famFold_congr_members Nat.add 0 _ _
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan a)
          (blockcount.blockSpan b))).map blockcount.HVec.content))
      (fun mu hmu => by
        rw [blockcount.fusionCount_countOf a b (places.shapeOf mu) hba,
          hrl mu (ground.mem_of_dedupL
            (ground.mem_of_countOf_pos mu _ hmu))])
  have hR2 := ground.famFold_countCollect
    (fun mu => F (places.shapeOf mu))
    ((blockcount.exhaust a.length
      (blockcount.fusedAt (blockcount.blockSpan a)
        (blockcount.blockSpan b))).map blockcount.HVec.content)
    (ground.dedupL ((blockcount.exhaust a.length
      (blockcount.fusedAt (blockcount.blockSpan a)
        (blockcount.blockSpan b))).map blockcount.HVec.content)) hD
  exact ((hL1.trans hL2.symm).trans hL3.symm).trans (hR2.trans hR1.symm)


/-- The associativity display at the label carrier
(`prop:repring`'s and `prop:algebra`'s identity,
`Σ_e N^e_{ab} N^d_{ec} = Σ_f N^f_{bc} N^d_{af}`): the two pairings'
weighted sums over the matched-degree enumerations read one value
at every label quadruple of one width.  The counts descend to the
block counts (`steinberg.count_fusion`); at a degree total missing
the width's multiples against the target's complement every term
of both sums is vacant (`countL_vacantMod`); at or above the
target's degree both sums lift the target
(`countL_geRead`) and meet `lem:blockcount`(iii) across the
carrier bridge (`bridgeFold`, `blockcount.fusionCount_assoc`); and
below it the first shape carries the gap's full columns, the left
carrier travelling along the lift with the vacancy off its image
(`fusionCount_colOff` at `foldLift`) and the right reading the
lift outright (`countL_ltRead`).  The three widths are the frame
carrying the block reads. -/
theorem countL_assoc (a b c dd : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hdd : dd.length = a.length) :
    ground.famFold Nat.add 0
      (fun e => steinberg.count a b e * countL e c dd)
      (places.allShapes a.length (degree a + degree b))
    = ground.famFold Nat.add 0
      (fun f => steinberg.count b c f * countL a f dd)
      (places.allShapes a.length (degree b + degree c)) := by
  cases Nat.eq_zero_or_pos a.length with
  | inl h0 =>
    rw [ground.nil_of_length_zero a h0,
      ground.nil_of_length_zero b (hba.trans h0),
      ground.nil_of_length_zero c (hca.trans h0),
      ground.nil_of_length_zero dd (hdd.trans h0)]
    rfl
  | inr hL =>
    have hcb : c.length = b.length := hca.trans hba.symm
    have hK : degree dd + degree (dualL dd)
        = ground.sumNat dd * a.length := by
      rw [degree_dualL_add dd, hdd]
      exact Nat.mul_comm a.length (ground.sumNat dd)
    have hLc : ground.famFold Nat.add 0
        (fun e => steinberg.count a b e * countL e c dd)
        (places.allShapes a.length (degree a + degree b))
        = ground.famFold Nat.add 0
          (fun e => blockcount.fusionCount a b e * countL e c dd)
          (places.allShapes a.length (degree a + degree b)) :=
      ground.famFold_congr_members Nat.add 0 _ _
        (places.allShapes a.length (degree a + degree b))
        (fun e he => by
          rw [steinberg.count_fusion a b e hba
            (places.allShapes_sound a.length (degree a + degree b) e
              (ground.mem_of_countOf_pos e _ he)).1])
    have hRc : ground.famFold Nat.add 0
        (fun f => steinberg.count b c f * countL a f dd)
        (places.allShapes a.length (degree b + degree c))
        = ground.famFold Nat.add 0
          (fun f => blockcount.fusionCount b c f * countL a f dd)
          (places.allShapes a.length (degree b + degree c)) :=
      ground.famFold_congr_members Nat.add 0 _ _
        (places.allShapes a.length (degree b + degree c))
        (fun f hf => by
          rw [steinberg.count_fusion b c f hcb
            ((places.allShapes_sound a.length (degree b + degree c) f
              (ground.mem_of_countOf_pos f _ hf)).1.trans hba.symm)])
    rw [hLc, hRc]
    by_cases hmod : (degree a + degree b + degree c
        + degree (dualL dd)) % a.length = 0
    · match Nat.lt_or_ge (degree a + degree b + degree c)
          (degree dd) with
      | Or.inl hlt =>
        have hsum : degree a + degree b + degree c
              + degree (dualL dd)
            + (degree dd - (degree a + degree b + degree c))
            = ground.sumNat dd * a.length := by
          rw [Nat.add_right_comm (degree a + degree b + degree c)
              (degree (dualL dd))
              (degree dd - (degree a + degree b + degree c)),
            ground.natAddSubCancel (Nat.le_of_lt hlt)]
          exact hK
        have hgm : (degree dd - (degree a + degree b + degree c))
            % a.length = 0 := by
          have h1 := ground.modAdd (degree a + degree b + degree c
            + degree (dualL dd))
            (degree dd - (degree a + degree b + degree c)) a.length
          rw [hmod, Nat.zero_add, ground.modMod, hsum,
            ground.modMulSelf] at h1
          exact h1
        have hjD : (degree dd - (degree a + degree b + degree c))
              / a.length * a.length
            = degree dd - (degree a + degree b + degree c) := by
          have h1 := (ground.natDivRead
            (degree dd - (degree a + degree b + degree c)) a.length
            hL).1
          rw [hgm, Nat.add_zero] at h1
          rw [Nat.mul_comm ((degree dd
            - (degree a + degree b + degree c)) / a.length) a.length]
          exact h1
        have hdegdd : degree a + degree b + degree c
            + (degree dd - (degree a + degree b + degree c))
                / a.length * a.length
            = degree dd := by
          rw [hjD]
          exact ground.natAddSubCancel (Nat.le_of_lt hlt)
        have hal : (addFulls ((degree dd
            - (degree a + degree b + degree c)) / a.length) a).length
            = a.length :=
          length_addFulls _ a
        have hbl : b.length = (addFulls ((degree dd
              - (degree a + degree b + degree c)) / a.length) a).length :=
          hba.trans hal.symm
        have hoff : ∀ X : Shape, X.length = a.length →
            ground.getAt 0 (rowList X) (a.length - 1)
              < (degree dd - (degree a + degree b + degree c))
                / a.length →
            blockcount.fusionCount (addFulls ((degree dd
                - (degree a + degree b + degree c)) / a.length) a) b X
              * blockcount.fusionCount X c dd = 0 := by
          intro X hXl hXlt
          rw [fusionCount_colOff _ a b X hba hXl hXlt hL, Nat.zero_mul]
        have hlift : ground.famFold Nat.add 0
            (fun e => blockcount.fusionCount a b e * countL e c dd)
            (places.allShapes a.length (degree a + degree b))
            = ground.famFold Nat.add 0
              (fun e => blockcount.fusionCount (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) a)
                  b (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) e)
                * blockcount.fusionCount (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) e)
                  c dd)
              (places.allShapes a.length (degree a + degree b)) := by
          refine ground.famFold_congr_members Nat.add 0 _ _
            (places.allShapes a.length (degree a + degree b)) ?_
          intro e he
          obtain ⟨hel, hed⟩ := places.allShapes_sound a.length
            (degree a + degree b) e (ground.mem_of_countOf_pos e _ he)
          have hjel : (addFulls ((degree dd
              - (degree a + degree b + degree c)) / a.length) e).length
              = a.length := (length_addFulls _ e).trans hel
          have hjed : degree (addFulls ((degree dd
                - (degree a + degree b + degree c)) / a.length) e)
              + degree c = degree dd := by
            rw [degree_addFulls _ e, hel, hed,
              Nat.add_right_comm (degree a + degree b)
                ((degree dd - (degree a + degree b + degree c))
                  / a.length * a.length) (degree c)]
            exact hdegdd
          rw [← fusionCount_addFullN _ a b e hba hel,
            ← countL_addFullsA ((degree dd
                - (degree a + degree b + degree c)) / a.length) e c dd
              (hca.trans hel.symm) (hdd.trans hel.symm),
            countL_matched _ c dd (hca.trans hjel.symm)
              (hdd.trans hjel.symm) hjed]
        have hfl2 : ground.famFold Nat.add 0
            (fun e => blockcount.fusionCount (addFulls ((degree dd
                  - (degree a + degree b + degree c)) / a.length) a)
                b (addFulls ((degree dd
                  - (degree a + degree b + degree c)) / a.length) e)
              * blockcount.fusionCount (addFulls ((degree dd
                  - (degree a + degree b + degree c)) / a.length) e)
                c dd)
            (places.allShapes a.length (degree a + degree b))
            = ground.famFold Nat.add 0
              (fun X => blockcount.fusionCount (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) a)
                  b X
                * blockcount.fusionCount X c dd)
              (places.allShapes a.length (degree a + degree b
                + (degree dd - (degree a + degree b + degree c))
                  / a.length * a.length)) :=
          (foldLift ((degree dd - (degree a + degree b + degree c))
              / a.length) a.length (degree a + degree b) hL
            (fun X => blockcount.fusionCount (addFulls ((degree dd
                  - (degree a + degree b + degree c)) / a.length) a)
                b X
              * blockcount.fusionCount X c dd) hoff).symm
        have hb1 : ground.famFold Nat.add 0
            (fun X => blockcount.fusionCount (addFulls ((degree dd
                  - (degree a + degree b + degree c)) / a.length) a)
                b X
              * blockcount.fusionCount X c dd)
            (places.allShapes a.length (degree a + degree b
              + (degree dd - (degree a + degree b + degree c))
                / a.length * a.length))
            = ground.famFold Nat.add 0
              (fun mu => blockcount.fusionCount (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) a)
                  b (places.shapeOf mu)
                * blockcount.fusionCount (places.shapeOf mu) c dd)
              (ground.dedupL ((blockcount.exhaust a.length
                (blockcount.fusedAt (blockcount.blockSpan
                    (addFulls ((degree dd
                      - (degree a + degree b + degree c)) / a.length)
                      a))
                  (blockcount.blockSpan b))).map
                blockcount.HVec.content)) := by
          have h := bridgeFold (addFulls ((degree dd
              - (degree a + degree b + degree c)) / a.length) a) b hbl
            (fun X => blockcount.fusionCount X c dd)
          rw [hal, degree_addFulls _ a,
            Nat.add_right_comm (degree a)
              ((degree dd - (degree a + degree b + degree c))
                / a.length * a.length) (degree b)] at h
          exact h
        have hassoc := blockcount.fusionCount_assoc (addFulls ((degree dd
            - (degree a + degree b + degree c)) / a.length) a) b c dd
          hbl (hca.trans hal.symm) (hdd.trans hal.symm)
        rw [hal] at hassoc
        have hb2 : ground.famFold Nat.add 0
            (fun f => blockcount.fusionCount b c f
              * blockcount.fusionCount (addFulls ((degree dd
                  - (degree a + degree b + degree c)) / a.length) a)
                f dd)
            (places.allShapes a.length (degree b + degree c))
            = ground.famFold Nat.add 0
              (fun mu => blockcount.fusionCount b c (places.shapeOf mu)
                * blockcount.fusionCount (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) a)
                  (places.shapeOf mu) dd)
              (ground.dedupL ((blockcount.exhaust a.length
                (blockcount.fusedAt (blockcount.blockSpan b)
                  (blockcount.blockSpan c))).map
                blockcount.HVec.content)) := by
          have h := bridgeFold b c hcb
            (fun f => blockcount.fusionCount (addFulls ((degree dd
                - (degree a + degree b + degree c)) / a.length) a)
              f dd)
          rw [hba] at h
          exact h
        have hR3 : ground.famFold Nat.add 0
            (fun f => blockcount.fusionCount b c f * countL a f dd)
            (places.allShapes a.length (degree b + degree c))
            = ground.famFold Nat.add 0
              (fun f => blockcount.fusionCount b c f
                * blockcount.fusionCount (addFulls ((degree dd
                    - (degree a + degree b + degree c)) / a.length) a)
                  f dd)
              (places.allShapes a.length (degree b + degree c)) := by
          refine ground.famFold_congr_members Nat.add 0 _ _
            (places.allShapes a.length (degree b + degree c)) ?_
          intro f hf
          obtain ⟨hfl, hfd⟩ := places.allShapes_sound a.length
            (degree b + degree c) f (ground.mem_of_countOf_pos f _ hf)
          have h1 := countL_ltRead a f dd hfl hdd
            (by rw [hfd,
                  ← Nat.add_assoc (degree a) (degree b) (degree c)]
                exact hlt)
            (by rw [hfd,
                  ← Nat.add_assoc (degree a) (degree b) (degree c)]
                exact hgm)
          rw [hfd, ← Nat.add_assoc (degree a) (degree b) (degree c)]
            at h1
          rw [h1]
        rw [hlift, hfl2, hb1, hassoc, ← hb2, ← hR3]
      | Or.inr hge =>
        have hSw : degree a + degree b + degree c + degree (dualL dd)
            = degree a + degree b + degree c - degree dd
              + ground.sumNat dd * a.length := by
          rw [← hK,
            ← Nat.add_assoc
              (degree a + degree b + degree c - degree dd) (degree dd)
              (degree (dualL dd)),
            Nat.add_comm (degree a + degree b + degree c - degree dd)
              (degree dd),
            ground.natAddSubCancel hge]
        have hgm : (degree a + degree b + degree c - degree dd)
            % a.length = 0 := by
          rw [hSw, ground.modAddMul] at hmod
          exact hmod
        have hDDl : (addFulls ((degree a + degree b + degree c
            - degree dd) / a.length) dd).length = a.length :=
          (length_addFulls _ dd).trans hdd
        have hL2 : ground.famFold Nat.add 0
            (fun e => blockcount.fusionCount a b e * countL e c dd)
            (places.allShapes a.length (degree a + degree b))
            = ground.famFold Nat.add 0
              (fun e => blockcount.fusionCount a b e
                * blockcount.fusionCount e c
                  (addFulls ((degree a + degree b + degree c
                    - degree dd) / a.length) dd))
              (places.allShapes a.length (degree a + degree b)) := by
          refine ground.famFold_congr_members Nat.add 0 _ _
            (places.allShapes a.length (degree a + degree b)) ?_
          intro e he
          obtain ⟨hel, hed⟩ := places.allShapes_sound a.length
            (degree a + degree b) e (ground.mem_of_countOf_pos e _ he)
          have h1 := countL_geRead e c dd (hca.trans hel.symm)
            (hdd.trans hel.symm) (by rw [hed]; exact hge)
            (by rw [hed, hel]; exact hgm)
          rw [hed, hel] at h1
          rw [h1]
        have hR2 : ground.famFold Nat.add 0
            (fun f => blockcount.fusionCount b c f * countL a f dd)
            (places.allShapes a.length (degree b + degree c))
            = ground.famFold Nat.add 0
              (fun f => blockcount.fusionCount b c f
                * blockcount.fusionCount a f
                  (addFulls ((degree a + degree b + degree c
                    - degree dd) / a.length) dd))
              (places.allShapes a.length (degree b + degree c)) := by
          refine ground.famFold_congr_members Nat.add 0 _ _
            (places.allShapes a.length (degree b + degree c)) ?_
          intro f hf
          obtain ⟨hfl, hfd⟩ := places.allShapes_sound a.length
            (degree b + degree c) f (ground.mem_of_countOf_pos f _ hf)
          have h1 := countL_geRead a f dd hfl hdd
            (by rw [hfd,
                  ← Nat.add_assoc (degree a) (degree b) (degree c)]
                exact hge)
            (by rw [hfd,
                  ← Nat.add_assoc (degree a) (degree b) (degree c)]
                exact hgm)
          rw [hfd, ← Nat.add_assoc (degree a) (degree b) (degree c)]
            at h1
          rw [h1]
        have hb1 : ground.famFold Nat.add 0
            (fun e => blockcount.fusionCount a b e
              * blockcount.fusionCount e c
                (addFulls ((degree a + degree b + degree c
                  - degree dd) / a.length) dd))
            (places.allShapes a.length (degree a + degree b))
            = ground.famFold Nat.add 0
              (fun mu => blockcount.fusionCount a b (places.shapeOf mu)
                * blockcount.fusionCount (places.shapeOf mu) c
                  (addFulls ((degree a + degree b + degree c
                    - degree dd) / a.length) dd))
              (ground.dedupL ((blockcount.exhaust a.length
                (blockcount.fusedAt (blockcount.blockSpan a)
                  (blockcount.blockSpan b))).map
                blockcount.HVec.content)) :=
          bridgeFold a b hba
            (fun e => blockcount.fusionCount e c
              (addFulls ((degree a + degree b + degree c
                - degree dd) / a.length) dd))
        have hb2 : ground.famFold Nat.add 0
            (fun f => blockcount.fusionCount b c f
              * blockcount.fusionCount a f
                (addFulls ((degree a + degree b + degree c
                  - degree dd) / a.length) dd))
            (places.allShapes a.length (degree b + degree c))
            = ground.famFold Nat.add 0
              (fun mu => blockcount.fusionCount b c (places.shapeOf mu)
                * blockcount.fusionCount a (places.shapeOf mu)
                  (addFulls ((degree a + degree b + degree c
                    - degree dd) / a.length) dd))
              (ground.dedupL ((blockcount.exhaust a.length
                (blockcount.fusedAt (blockcount.blockSpan b)
                  (blockcount.blockSpan c))).map
                blockcount.HVec.content)) := by
          have h := bridgeFold b c hcb
            (fun f => blockcount.fusionCount a f
              (addFulls ((degree a + degree b + degree c
                - degree dd) / a.length) dd))
          rw [hba] at h
          exact h
        rw [hL2, hR2, hb1, hb2,
          blockcount.fusionCount_assoc a b c
            (addFulls ((degree a + degree b + degree c - degree dd)
              / a.length) dd) hba hca hDDl]
    · have hLz : ground.famFold Nat.add 0
          (fun e => blockcount.fusionCount a b e * countL e c dd)
          (places.allShapes a.length (degree a + degree b)) = 0 := by
        refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
          (fun _ => (0 : Nat))
          (places.allShapes a.length (degree a + degree b)) ?_)
          (ground.famFold_zero (fun _ : Shape => (0 : Nat))
            (fun _ => rfl)
            (places.allShapes a.length (degree a + degree b)))
        intro e he
        obtain ⟨hel, hed⟩ := places.allShapes_sound a.length
          (degree a + degree b) e (ground.mem_of_countOf_pos e _ he)
        rw [countL_vacantMod e c dd (degree (dualL dd))
            (ground.sumNat dd) (by rw [hel]; exact hK)
            (by rw [hel, hed]; exact hmod),
          Nat.mul_zero]
      have hRz : ground.famFold Nat.add 0
          (fun f => blockcount.fusionCount b c f * countL a f dd)
          (places.allShapes a.length (degree b + degree c)) = 0 := by
        refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
          (fun _ => (0 : Nat))
          (places.allShapes a.length (degree b + degree c)) ?_)
          (ground.famFold_zero (fun _ : Shape => (0 : Nat))
            (fun _ => rfl)
            (places.allShapes a.length (degree b + degree c)))
        intro f hf
        obtain ⟨hfl, hfd⟩ := places.allShapes_sound a.length
          (degree b + degree c) f (ground.mem_of_countOf_pos f _ hf)
        rw [countL_vacantMod a f dd (degree (dualL dd))
            (ground.sumNat dd) hK
            (by rw [hfd,
                  ← Nat.add_assoc (degree a) (degree b) (degree c)]
                exact hmod),
          Nat.mul_zero]
      rw [hLz, hRz]

end labels
