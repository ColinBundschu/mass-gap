import MassGap.Labels
import MassGap.Weyldim
/-!
`prop:repring` — a fusion computation is a representation
computation, the label index's calculus: the counts are
`lem:blockcount`'s on labels by `con:labels`, and the layer's
three reads land here with the deferred blockcount identities at
their recorded consumer.  The unit read `N^𝟏_{ab} = δ_{a b̄}`
(`unitRead`, holding at every matched-width pair by
`unitRead_all`: the unit label's count is the full-column-power
count of `lem:dualread`(iii), one exactly at the dual label); the characters' orthonormality for the evaluation,
`Eval(χ_a χ̄_b) = δ_{ab}` (`orthoRead`, the unit read at the
dualized second label); the triple count `m{a,b,c} = N^{c̄}_{ab}`
with its rotation read (`m3`, `mSymRead`, the transposition instance the check module's); the
associativity fold over the matched-degree shapes
(`assocRead`, `lem:blockcount`(iii)'s second identity); and the
dimension identity `Σ_c N^c_{ab} d_c = d_a d_b` over the
matched-degree shapes (`dimRead`, `lem:blockcount`(ii)'s sum at
the tensor product, the dimensions `cor:weyldim`'s gap-product
route).  Instances are the check module's pins; the exhaustion
and the counts' block reads stay `lem:blockcount`'s own,
`def:blockcount`'s layer.
-/

namespace repring
open ground places labels

/-- The unit read `N^𝟏_{ab} = δ_{a b̄}`: the unit label's count in
the product, one exactly at the dual label. -/
def unitRead (a b : Shape) : Prop :=
  countL a b (unitL a.length)
    = (if reduce a = dualL b then 1 else 0)

instance (a b : Shape) : Decidable (unitRead a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit label's own lift is the full-column power: the
representative's deepest key carries the whole count. -/
private theorem addFulls_unit : ∀ (d m : Nat),
    labels.addFulls m (unitL d) = dualread.fulls d m
  | 0, _ => rfl
  | e + 1, m => by
    show (match (List.replicate (e + 1) 0).reverse with
      | [] => []
      | x :: t => ((x + m) :: t).reverse) = dualread.fulls (e + 1) m
    rw [ground.reverse_replicate (e + 1) (0 : Nat)]
    show ((0 + m) :: List.replicate e 0).reverse
      = dualread.fulls (e + 1) m
    rw [ground.reverse_cons (0 + m) (List.replicate e 0),
      ground.reverse_replicate e (0 : Nat), Nat.zero_add]
    rfl

/-- The unit read holds at every matched-width pair: the unit
label's count in the product is the full-column-power count of
`lem:dualread`(iii), one exactly at the dual label.  The lift's
divisibility guard is the join's own — at a passing guard the
target is the full-column power at the degrees' quotient and the
join condition reads the dual label (`labels.join_dualL`,
`labels.dualL_join`), and at a refused guard the dual pair's join
would read the degrees as a full-column multiple, so the count and
the delta are vacant together. -/
theorem unitRead_all (a b : Shape) (hba : b.length = a.length) :
    unitRead a b := by
  have hdu : degree (unitL a.length) = 0 := by
    show ground.sumNat (rowList (List.replicate a.length 0)) = 0
    rw [places.rowList_replicate_zero a.length,
      ground.sumNat_replicate_zero a.length]
  have hrl : (rowList b).length = ((rowList a).reverse).length := by
    rw [places.length_rowList, ground.length_reverse,
      places.length_rowList, hba]
  show (if degree a + degree b < degree (unitL a.length) then
      (if (degree (unitL a.length) - (degree a + degree b))
            % a.length == 0 then
        steinberg.count (labels.addFulls
            ((degree (unitL a.length) - (degree a + degree b))
              / a.length) a) b (unitL a.length)
      else 0)
    else
      (if (degree a + degree b - degree (unitL a.length))
            % a.length == 0 then
        steinberg.count a b (labels.addFulls
          ((degree a + degree b - degree (unitL a.length)) / a.length)
          (unitL a.length))
      else 0))
    = (if reduce a = dualL b then 1 else 0)
  rw [hdu, if_neg (Nat.not_lt_zero (degree a + degree b)),
    Nat.sub_zero (degree a + degree b)]
  cases hb : ((degree a + degree b) % a.length == 0) with
  | true =>
    show steinberg.count a b (labels.addFulls
        ((degree a + degree b) / a.length) (unitL a.length))
      = (if reduce a = dualL b then 1 else 0)
    rw [addFulls_unit a.length ((degree a + degree b) / a.length),
      steinberg.count_fusion a b
        (dualread.fulls a.length ((degree a + degree b) / a.length))
        hba (dualread.length_fulls a.length _),
      dualread.fusionCount_fulls a b
        ((degree a + degree b) / a.length) hba]
    by_cases hred : reduce a = dualL b
    · rw [if_pos hred, if_pos (labels.dualL_join a b hred)]
    · rw [if_neg hred,
        if_neg (fun hj => hred (labels.join_dualL a b hba _ hj))]
  | false =>
    show (0 : Nat) = (if reduce a = dualL b then 1 else 0)
    refine (if_neg ?_).symm
    intro hred
    have hj := labels.dualL_join a b hred
    have hsum : ground.sumNat (List.zipWith (fun x y => x + y)
          (rowList b) ((rowList a).reverse))
        = degree b + degree a := by
      rw [ground.sumNat_zipWith_add _ _ hrl,
        ground.sumNat_reverse (rowList a)]
      rfl
    rw [hj, ground.sumNat_replicate] at hsum
    have hmod : (degree a + degree b) % a.length = 0 := by
      rw [Nat.add_comm (degree a) (degree b), ← hsum,
        Nat.mul_comm a.length ((degree a + degree b) / a.length)]
      exact ground.modMulSelf ((degree a + degree b) / a.length) a.length
    exact Bool.noConfusion (hb.symm.trans (ground.eqBeqOf hmod))

/-- The characters' orthonormality for the evaluation:
`Eval(χ_a χ̄_b) = N^𝟏_{a b̄} = δ_{ab}`, the unit read at the
dualized second label. -/
def orthoRead (a b : Shape) : Prop :=
  countL a (dualL b) (unitL a.length)
    = (if reduce a = reduce b then 1 else 0)

instance (a b : Shape) : Decidable (orthoRead a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The orthonormality holds at every matched-width pair: the unit
read at the dualized second label, the involution returning the
reduced shape (`labels.dualL_dualL`). -/
theorem orthoRead_all (a b : Shape) (hba : b.length = a.length) :
    orthoRead a b := by
  have h := unitRead_all a (labels.dualL b)
    ((labels.length_dualL b).trans hba)
  show countL a (dualL b) (unitL a.length)
    = (if reduce a = reduce b then 1 else 0)
  rw [show (if reduce a = reduce b then (1 : Nat) else 0)
      = (if reduce a = dualL (dualL b) then 1 else 0) from by
    rw [labels.dualL_dualL b]]
  exact h

/-- The triple count `m{a,b,c} = N^{c̄}_{ab}`, the invariant count
of the triple product. -/
def m3 (a b c : Shape) : Nat := countL a b (dualL c)

/-- The involution's index read, the fourth read: the dual label's
matrix is the transpose, `N^c_{ā b} = N^b_{a c}`, the triple count
one value at every argument dualized with the symmetry. -/
def invRead (a b c : Shape) : Prop :=
  countL (dualL a) b c = countL a c b

instance (a b c : Shape) : Decidable (invRead a b c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The triple count's symmetry at a stated argument rotation,
`m{a,b,c} = m{b,c,a}`. -/
def mSymRead (a b c : Shape) : Prop := m3 a b c = m3 b c a

instance (a b c : Shape) : Decidable (mSymRead a b c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The associativity fold over the matched-degree shapes:
`Σ_e N^e_{ab} N^d_{ec} = Σ_f N^f_{bc} N^d_{af}`
(`lem:blockcount`(iii) at its consumer). -/
def assocRead (a b c dd : Shape) : Prop :=
  ((allShapes a.length (degree a + degree b)).foldl (fun acc e =>
      acc + steinberg.count a b e * countL e c dd) 0)
    = ((allShapes a.length (degree b + degree c)).foldl (fun acc f =>
      acc + steinberg.count b c f * countL a f dd) 0)

instance (a b c dd : Shape) : Decidable (assocRead a b c dd) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dimension identity `Σ_c N^c_{ab} d_c = d_a d_b` over the
matched-degree shapes: `lem:blockcount`(ii)'s sum at the tensor
product, the deferred read at its recorded consumer. -/
def dimRead (a b : Shape) : Prop :=
  ((allShapes a.length (degree a + degree b)).foldl (fun acc c =>
      acc + steinberg.count a b c * weyldim.dimOf c) 0)
    = weyldim.dimOf a * weyldim.dimOf b

instance (a b : Shape) : Decidable (dimRead a b) :=
  inferInstanceAs (Decidable (_ = _))

end repring
