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
count of `lem:dualread`(iii), one exactly at the dual label); the
characters' orthonormality for the evaluation,
`Eval(χ_a χ̄_b) = δ_{ab}` (`orthoRead`, the unit read at the
dualized second label); the triple count `m{a,b,c} = N^{c̄}_{ab}`
with its rotation `m{a,b,c} = m{b,c,a}` (`m3`, `mSymRead`, holding
at every matched-width triple by `mSym_all`: the first pairing's
exhaustion collapses at the full-column target on both groupings,
the transposition instance the check module's); the
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

/-- A divisor's multiple splits its summands' remainders: at a
vacant remainder on one summand the other's is vacant too. -/
private theorem modJoin (x y z d : Nat) (h : x + y = z * d)
    (hx : x % d = 0) : y % d = 0 := by
  have h0 : (x + y) % d = 0 := by
    rw [h]
    exact ground.modMulSelf z d
  have h1 := ground.modAdd x y d
  rw [hx, Nat.zero_add, ground.modMod y d, h0] at h1
  exact h1

/-- The dual pair's degree join at a stated width: `con:labels`'
complement read cleared at the width. -/
private theorem dualDegree_mul (s : Shape) (d : Nat)
    (h : s.length = d) :
    degree s + degree (labels.dualL s) = ground.sumNat s * d := by
  rw [labels.degree_dualL_add s, h]
  exact Nat.mul_comm d (ground.sumNat s)

/-- The triple count at a refused divisibility: the three degrees'
total misses the width's multiples, and on either side of the
lift's branch the gap misses them with it — the dual label's own
degree joins its shape's at the width's multiple — so the guard
refuses and the count is vacant. -/
private theorem m3Zero (a b c : Shape) (hca : c.length = a.length)
    (hs : ¬ (degree a + degree b + degree c) % a.length = 0) :
    m3 a b c = 0 := by
  have hK : degree c + degree (dualL c)
      = ground.sumNat c * a.length := dualDegree_mul c a.length hca
  show (if degree a + degree b < degree (dualL c) then
      (if (degree (dualL c) - (degree a + degree b)) % a.length == 0
        then steinberg.count (labels.addFulls
          ((degree (dualL c) - (degree a + degree b)) / a.length) a) b
          (dualL c)
      else 0)
    else
      (if (degree a + degree b - degree (dualL c)) % a.length == 0 then
        steinberg.count a b (labels.addFulls
          ((degree a + degree b - degree (dualL c)) / a.length)
          (dualL c))
      else 0))
    = 0
  match Nat.lt_or_ge (degree a + degree b) (degree (dualL c)) with
  | Or.inl hlt =>
    have hj : degree a + degree b
        + (degree (dualL c) - (degree a + degree b))
        = degree (dualL c) :=
      ground.natAddSubCancel (Nat.le_of_lt hlt)
    have hsum : (degree (dualL c) - (degree a + degree b))
        + (degree a + degree b + degree c)
        = ground.sumNat c * a.length := by
      rw [← Nat.add_assoc, Nat.add_comm
          (degree (dualL c) - (degree a + degree b))
          (degree a + degree b), hj,
        Nat.add_comm (degree (dualL c)) (degree c)]
      exact hK
    have hne : ¬ (degree (dualL c) - (degree a + degree b))
        % a.length = 0 :=
      fun hg => hs (modJoin _ _ _ _ hsum hg)
    rw [if_pos hlt]
    cases hb : ((degree (dualL c) - (degree a + degree b))
        % a.length == 0) with
    | true => exact absurd (ground.beqEqOf hb) hne
    | false => rfl
  | Or.inr hge =>
    have hj : degree (dualL c)
        + (degree a + degree b - degree (dualL c))
        = degree a + degree b :=
      ground.natAddSubCancel hge
    have hsum : degree a + degree b + degree c
        = (degree a + degree b - degree (dualL c))
          + ground.sumNat c * a.length := by
      rw [← hK, Nat.add_comm (degree c) (degree (dualL c)),
        ← Nat.add_assoc, Nat.add_comm
          (degree a + degree b - degree (dualL c)) (degree (dualL c)),
        hj]
    have hne : ¬ (degree a + degree b - degree (dualL c))
        % a.length = 0 := by
      intro hg
      refine hs ?_
      rw [hsum, ground.modAddMul _ (ground.sumNat c) a.length]
      exact hg
    rw [if_neg (fun hlt => Nat.not_le_of_lt hlt hge)]
    cases hb : ((degree a + degree b - degree (dualL c))
        % a.length == 0) with
    | true => exact absurd (ground.beqEqOf hb) hne
    | false => rfl

/-- The triple count at a divisible degree total, read through the
first pairing's exhaustion: the first shape lifted by the third's
occupancy total meets the full-column target at the third's
complement key, and the associativity fold carries the pool over to
the second pairing's own (`lem:blockcount`(iii) at
`lem:dualread`(iii)'s delta).  The lift is free along the class
(`labels.countL_addFullsA`, `con:labels`' descent), the left
grouping's guard asks only the third occupancy total's clearance,
and that total is the guard's least witness at every ambient
count. -/
private theorem rotFold (a b c : Shape) (M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hd : 0 < a.length)
    (hM : degree a + degree b + degree c = a.length * M) :
    m3 a b c = ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount b c (places.shapeOf mu)
        * blockcount.fusionCount
            (labels.addFulls (ground.sumNat c) a)
            (places.shapeOf mu)
            (dualread.fulls a.length (M + ground.sumNat c)))
      (ground.dedupL ((blockcount.exhaust a.length
        (blockcount.fusedAt (blockcount.blockSpan b)
          (blockcount.blockSpan c))).map blockcount.HVec.content)) := by
  have hXl : (labels.addFulls (ground.sumNat c) a).length = a.length :=
    length_addFulls (ground.sumNat c) a
  have hbX : b.length = (labels.addFulls (ground.sumNat c) a).length :=
    hba.trans hXl.symm
  have hcX : c.length = (labels.addFulls (ground.sumNat c) a).length :=
    hca.trans hXl.symm
  have hdc : (dualL c).length = a.length :=
    (labels.length_dualL c).trans hca
  have hK : degree c + degree (dualL c)
      = ground.sumNat c * a.length := dualDegree_mul c a.length hca
  have hdeg : degree (labels.addFulls (ground.sumNat c) a)
      = degree a + ground.sumNat c * a.length :=
    labels.degree_addFulls (ground.sumNat c) a
  have hjoin : degree (dualL c) + M * a.length
      = degree (labels.addFulls (ground.sumNat c) a) + degree b := by
    refine ground.addCancelL (degree c) ?_
    rw [← Nat.add_assoc (degree c) (degree (dualL c)) (M * a.length),
      hK, hdeg, Nat.add_right_comm (degree a)
        (ground.sumNat c * a.length) (degree b),
      Nat.add_comm (degree c)
        (degree a + degree b + ground.sumNat c * a.length),
      Nat.add_right_comm (degree a + degree b)
        (ground.sumNat c * a.length) (degree c),
      hM, Nat.add_comm (ground.sumNat c * a.length) (M * a.length),
      Nat.mul_comm M a.length]
  have hle : degree (dualL c)
      ≤ degree (labels.addFulls (ground.sumNat c) a) + degree b :=
    Nat.le.intro hjoin
  have hgap : degree (labels.addFulls (ground.sumNat c) a) + degree b
      - degree (dualL c) = M * a.length := by
    rw [← hjoin, Nat.add_comm (degree (dualL c)) (M * a.length),
      ground.addSubSelfR (M * a.length) (degree (dualL c))]
  have hmod : (degree (labels.addFulls (ground.sumNat c) a) + degree b
      - degree (dualL c))
      % (labels.addFulls (ground.sumNat c) a).length = 0 := by
    rw [hXl, hgap]
    exact ground.modMulSelf M a.length
  have hgr := labels.countL_geRead
    (labels.addFulls (ground.sumNat c) a) b (dualL c) hbX
    (hdc.trans hXl.symm) hle hmod
  rw [hXl, hgap, ground.divMulSelf M a.length hd] at hgr
  have hafa := labels.countL_addFullsA (ground.sumNat c) a b (dualL c)
    hba hdc
  have hC1 := labels.foldCollapseL a b c (ground.sumNat c) M hba hca
    (Nat.le_add_left (ground.sumNat c) M)
  rw [ground.addSubSelfR M (ground.sumNat c)] at hC1
  have hea : (dualread.fulls a.length (M + ground.sumNat c)).length
      = (labels.addFulls (ground.sumNat c) a).length :=
    (dualread.length_fulls a.length (M + ground.sumNat c)).trans
      hXl.symm
  have hassoc := blockcount.fusionCount_assoc
    (labels.addFulls (ground.sumNat c) a) b c
    (dualread.fulls a.length (M + ground.sumNat c)) hbX hcX hea
  rw [hXl] at hassoc
  exact ((hafa.symm.trans hgr).trans hC1.symm).trans hassoc

/-- The rotation at an occupied complement key: the second
pairing's fold collapses at the first shape's complement key, whose
count is the rotated triple count read back through the lift's
guard. -/
private theorem rotStep (a b c : Shape) (M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hd : 0 < a.length)
    (hM : degree a + degree b + degree c = a.length * M)
    (hMa : ground.sumNat a ≤ M) :
    m3 a b c = m3 b c a := by
  have hdb : 0 < b.length := by
    rw [hba]
    exact hd
  have hcb : c.length = b.length := hca.trans hba.symm
  have hda : (dualL a).length = b.length :=
    (labels.length_dualL a).trans hba.symm
  have hKa : degree a + degree (dualL a)
      = ground.sumNat a * a.length := dualDegree_mul a a.length rfl
  have hsa : ground.sumNat a + (M - ground.sumNat a) = M :=
    match Nat.le.dest hMa with
    | ⟨g, hg⟩ => by
      rw [← hg, ground.addSubSelfL (ground.sumNat a) g]
  have hjoin : degree (dualL a) + (M - ground.sumNat a) * b.length
      = degree b + degree c := by
    rw [hba]
    refine ground.addCancelL (degree a) ?_
    rw [← Nat.add_assoc (degree a) (degree (dualL a))
        ((M - ground.sumNat a) * a.length), hKa,
      ← ground.mulAddR (ground.sumNat a) (M - ground.sumNat a)
        a.length, hsa,
      ← Nat.add_assoc (degree a) (degree b) (degree c), hM,
      Nat.mul_comm M a.length]
  have hle : degree (dualL a) ≤ degree b + degree c :=
    Nat.le.intro hjoin
  have hgap : degree b + degree c - degree (dualL a)
      = (M - ground.sumNat a) * b.length := by
    rw [← hjoin, Nat.add_comm (degree (dualL a))
        ((M - ground.sumNat a) * b.length),
      ground.addSubSelfR ((M - ground.sumNat a) * b.length)
        (degree (dualL a))]
  have hmod : (degree b + degree c - degree (dualL a)) % b.length
      = 0 := by
    rw [hgap]
    exact ground.modMulSelf (M - ground.sumNat a) b.length
  have hgr := labels.countL_geRead b c (dualL a) hcb hda hle hmod
  rw [hgap, ground.divMulSelf (M - ground.sumNat a) b.length hdb]
    at hgr
  exact ((rotFold a b c M hba hca hd hM).trans
    (labels.foldCollapseR a b c (ground.sumNat c) M hba hca
      hMa)).trans hgr.symm

/-- The triple count below the first shape's occupancy total: the
lifted first shape's own last row exceeds the full-column
constant, so the second pairing's fold is vacant and the count with
it. -/
private theorem rotStepVacant (a b c : Shape) (M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hd : 0 < a.length)
    (hM : degree a + degree b + degree c = a.length * M)
    (hlt : M < ground.sumNat a) :
    m3 a b c = 0 :=
  (rotFold a b c M hba hca hd hM).trans
    (labels.foldCollapseR_vacant a b c (ground.sumNat c) M hba hca
      hlt)

/-- The rotation at a divisible degree total: at a complement key
occupied on the first shape the two folds tie the two groupings,
and below any of the three occupancy totals the triple count is
vacant at that argument's own rotation, all three rotations reading
the sum's unit together. -/
private theorem rotAll (a b c : Shape) (M : Nat)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hd : 0 < a.length)
    (hM : degree a + degree b + degree c = a.length * M) :
    m3 a b c = m3 b c a := by
  have hdb : 0 < b.length := by
    rw [hba]
    exact hd
  have hcb : c.length = b.length := hca.trans hba.symm
  have hab : a.length = b.length := hba.symm
  have hMb : degree b + degree c + degree a = b.length * M := by
    rw [hba, Nat.add_comm (degree b + degree c) (degree a),
      ← Nat.add_assoc (degree a) (degree b) (degree c)]
    exact hM
  match Nat.lt_or_ge M (ground.sumNat a) with
  | Or.inr hMa => exact rotStep a b c M hba hca hd hM hMa
  | Or.inl hlt =>
    have hza : m3 a b c = 0 := rotStepVacant a b c M hba hca hd hM hlt
    match Nat.lt_or_ge M (ground.sumNat b) with
    | Or.inl hltb =>
      exact hza.trans
        (rotStepVacant b c a M hcb hab hdb hMb hltb).symm
    | Or.inr hMb' =>
      have hbca : m3 b c a = m3 c a b :=
        rotStep b c a M hcb hab hdb hMb hMb'
      have hdc : 0 < c.length := by
        rw [hca]
        exact hd
      have hac : a.length = c.length := hca.symm
      have hbc : b.length = c.length := hba.trans hca.symm
      have hMc : degree c + degree a + degree b = c.length * M := by
        rw [hca, Nat.add_comm (degree c) (degree a),
          Nat.add_right_comm (degree a) (degree c) (degree b)]
        exact hM
      match Nat.lt_or_ge M (ground.sumNat c) with
      | Or.inl hltc =>
        exact hza.trans (hbca.trans
          (rotStepVacant c a b M hac hbc hdc hMc hltc)).symm
      | Or.inr hMc' =>
        exact hza.trans (hbca.trans
          ((rotStep c a b M hac hbc hdc hMc hMc').trans hza)).symm

/-- The triple count's rotation, `m{a,b,c} = m{b,c,a}`: the
display reads at either pairing of the associativity at the unit
target, the first read keeping each sum at the dual label's
summand alone (`prop:repring`'s third read at
`lem:blockcount`(iii) and `lem:dualread`(iii)). -/
theorem mSym_all (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    m3 a b c = m3 b c a := by
  match Nat.eq_zero_or_pos a.length with
  | Or.inl h0 =>
    rw [ground.nil_of_length_zero a h0,
      ground.nil_of_length_zero b (hba.trans h0),
      ground.nil_of_length_zero c (hca.trans h0)]
  | Or.inr hd =>
    match Nat.eq_zero_or_pos
        ((degree a + degree b + degree c) % a.length) with
    | Or.inl hmod =>
      have hM : degree a + degree b + degree c
          = a.length
            * ((degree a + degree b + degree c) / a.length) := by
        have h := (ground.natDivRead (degree a + degree b + degree c)
          a.length hd).1
        rw [hmod, Nat.add_zero] at h
        exact h.symm
      exact rotAll a b c _ hba hca hd hM
    | Or.inr hpos =>
      have hs : ¬ (degree a + degree b + degree c) % a.length = 0 := by
        intro h
        rw [h] at hpos
        exact Nat.lt_irrefl 0 hpos
      have hs2 : ¬ (degree b + degree c + degree a) % b.length = 0 := by
        rw [Nat.add_comm (degree b + degree c) (degree a),
          ← Nat.add_assoc (degree a) (degree b) (degree c), hba]
        exact hs
      exact (m3Zero a b c hca hs).trans (m3Zero b c a hba.symm hs2).symm

/-- The triple count's transposition, `m{a,b,c} = m{b,a,c}`: the
factors' exchange at the count (`labels.countL_comm`), the
rotation's companion — the two generate the symmetry of `m` in
its three arguments (`prop:repring`'s third read). -/
theorem mSym_swap (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    m3 a b c = m3 b a c :=
  labels.countL_comm a b (labels.dualL c) hba
    ((labels.length_dualL c).trans hca)

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

/-- The associativity fold at every label quadruple of one width:
the two pairings' weighted sums read one value
(`labels.countL_assoc`, `lem:blockcount`(iii) descended to
labels).  The three widths are the frame carrying the label
count's own reads. -/
theorem assocRead_all (a b c dd : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hdd : dd.length = a.length) :
    assocRead a b c dd := by
  show ((allShapes a.length (degree a + degree b)).foldl (fun acc e =>
      acc + steinberg.count a b e * countL e c dd) 0)
    = ((allShapes a.length (degree b + degree c)).foldl (fun acc f =>
      acc + steinberg.count b c f * countL a f dd) 0)
  rw [ground.foldlSum (fun e => steinberg.count a b e * countL e c dd)
      (allShapes a.length (degree a + degree b)) 0,
    ground.foldlSum (fun f => steinberg.count b c f * countL a f dd)
      (allShapes a.length (degree b + degree c)) 0,
    labels.countL_assoc a b c dd hba hca hdd]

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
