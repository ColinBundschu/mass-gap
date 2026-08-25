import MassGap.Ground
import MassGap.Places
/-!
`con:gentable` — the generator table's content fields, the structure
a member instantiation fills (`con:sertables`' opening read): the
key list enters as the simple count, a content in the simple-key
presentation is its coroot list, and the fields are the length list
`⟨α_i, α_i⟩` at one cleared second member, the Cartan reads
`α_k(α_j^∨)` (the simple list carried by its own coroot lists), the
root list at its natural folds, and the highest root's fold.  The
derived reads: a fold's coroot list through the Cartan rows; the
length fold; the derived residue, the cofactor at the residue fold
`2 r · lenDen = Σ_i c_i · lenNums_i` with the naming identity the
decidable read `residueRead` (`con:sertables`' one fold per member);
the cleared form fold `formNum` at the halved products
`⟨α_j, α_i⟩ = [1:2] α_j(α_i^∨) ⟨α_i, α_i⟩`, with `⟨θ,θ⟩ = 2` the
read `thetaNormRead` and the form's simple symmetry `symRead`; and
the root fold's coroot reads `(2ρ)(α_i^∨) = 2`, `rhoRead`, the fold
over the positive list.  The dominance order, the reflections, the
closure and the Casimir field's operator reads land with their
consumers (the descent layer, the alternant layer); the table
spaces' operator content stays at `con:units`' instantiation, the
matrix units the first table.
-/

namespace gentable
open ground

set_option genInjectivity false in
/-- A member's table data: the simple count, the length list at one
cleared second member, the Cartan reads (row `k` the simple
`α_k`'s coroot list), the root list at its natural folds, and the
highest root's fold. -/
structure Table where
  rank : Nat
  lenNums : List Nat
  lenDen : Nat
  cartan : List (List BPair)
  posFolds : List (List Nat)
  thetaFold : List Nat

/-- A fold's coroot read at a key: `(Σ_k f_k α_k)(α_j^∨)`, the fold
against the Cartan rows' column, additive over the contents' sum. -/
def corootAt (t : Table) (f : List Nat) (j : Nat) : BPair :=
  BPair.sum (List.zipWith
    (fun c row => BPair.ofNat c * getAt BPair.unit row j) f t.cartan)

/-- The length fold `Σ_i f_i · lenNums_i`, the fold's squared-length
read at the cleared second member. -/
def lenFold (t : Table) (f : List Nat) : Nat :=
  ground.dotNat f t.lenNums

/-- The derived residue, the member's one fold
(`con:sertables`): the cofactor at
`2 r · lenDen = Σ_i c_i · lenNums_i` over the highest root's fold,
the division's exactness `residueRead`'s. -/
def residue (t : Table) : Nat :=
  lenFold t t.thetaFold / (2 * t.lenDen)

/-- The residue fold's naming identity with the residue's
positivity, the cofactor's whole verification. -/
def residueRead (t : Table) : Prop :=
  residue t * (2 * t.lenDen) = lenFold t t.thetaFold ∧ 0 < residue t

instance (t : Table) : Decidable (residueRead t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The cleared form fold `2 lenDen · ⟨Σ f α, Σ g α⟩`: the halved
products collected, `Σ_j g_j · (Σ f α)(α_j^∨) · lenNums_j`. -/
def formNum (t : Table) (f g : List Nat) : BPair :=
  BPair.sum ((List.range t.rank).map (fun j =>
    BPair.ofNat (getAt 0 g j) * corootAt t f j
      * BPair.ofNat (getAt 0 t.lenNums j)))

/-- The highest root's form read `⟨θ, θ⟩ = 2`, cleared at the
form's second member. -/
def thetaNormRead (t : Table) : Prop :=
  (formNum t t.thetaFold t.thetaFold).oneValue
    (BPair.ofNat (4 * t.lenDen))

instance (t : Table) : Decidable (thetaNormRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The form's symmetry at the simple pairs, the halved products'
two reads: `α_i(α_j^∨) ⟨α_j, α_j⟩ = α_j(α_i^∨) ⟨α_i, α_i⟩`, one
identity per key pair at the cleared second member. -/
def symRead (t : Table) : Prop :=
  ((List.range t.rank).all (fun i => (List.range t.rank).all (fun j =>
    if (getAt BPair.unit (getAt [] t.cartan i) j
          * BPair.ofNat (getAt 0 t.lenNums j)).oneValue
        (getAt BPair.unit (getAt [] t.cartan j) i
          * BPair.ofNat (getAt 0 t.lenNums i))
    then true else false))) = true

instance (t : Table) : Decidable (symRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The root fold's coroot read at a key: `(2ρ)(α_j^∨)`, the fold
over the positive list. -/
def rho2Coroot (t : Table) (j : Nat) : BPair :=
  BPair.sum (t.posFolds.map (fun f => corootAt t f j))

/-- The root fold's coroot reads `(2ρ)(α_i^∨) = 2` at every simple
index (`con:sertables`' first shared read). -/
def rhoRead (t : Table) : Prop :=
  ((List.range t.rank).all (fun j =>
    if (rho2Coroot t j).oneValue (BPair.ofNat 2) then true else false))
    = true

instance (t : Table) : Decidable (rhoRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The positive list's count. -/
def posCount (t : Table) : Nat := t.posFolds.length

/-- The root list's occupancy read: every fold occupied off the
unit fold (`con:gentable`'s root-list clause), the entry sum
positive per member. -/
def occRead (t : Table) : Prop :=
  (t.posFolds.all (fun f =>
    0 < f.foldl (fun a b => a + b) 0)) = true

instance (t : Table) : Decidable (occRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The shape read: the key list's count reads every field's
length, the matched-list clause (`con:gentable`'s contents over
the coordinates). -/
def shapeRead (t : Table) : Prop :=
  (t.lenNums.length == t.rank
    && t.cartan.length == t.rank
    && t.cartan.all (fun row => row.length == t.rank)
    && t.thetaFold.length == t.rank
    && t.posFolds.all (fun f => f.length == t.rank)) = true

instance (t : Table) : Decidable (shapeRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The first table, the powers with the matrix units
(`con:gentable`'s closing read) at the declared residue: the
letter-pair simples' Cartan chain, every length two, the positive
list the letter-pair moves at their interval folds, and the
highest root the full interval. -/
def tableA (r : Nat) : Table :=
  ⟨r, List.replicate r 2, 1,
   ground.matOf r r (fun i j =>
     if j == i then BPair.ofNat 2
     else if j + 1 == i || j == i + 1 then (BPair.ofNat 1).swap
     else BPair.unit),
   (List.range r).flatMap (fun a => (List.range (r + 1)).flatMap
     (fun b => if a < b then
       [(List.range r).map (fun k => if a ≤ k && k < b then 1 else 0)]
      else [])),
   List.replicate r 1⟩

/-! The one-hot fold's coroot read: a coefficient list occupied at
one key alone pairs the Cartan rows off at that key's own row, so
the simple `α_i`'s coroot read at `j` is the Cartan entry
`α_i(α_j^∨)`.  The pairing walks the two lists in lockstep, so the
read holds at any row count. -/

/-- The vacant coefficients' pairing: a coefficient list reading
zero at every key pairs the rows off at the sum's unit. -/
private theorem zipUnit (j : Nat) : ∀ (f : List Nat)
    (M : List (List BPair)), (∀ k, k < f.length → getAt 0 f k = 0) →
    (BPair.sum (List.zipWith
      (fun c row => BPair.ofNat c * getAt BPair.unit row j)
      f M)).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | c :: f, row :: M, h => by
    show (BPair.sum ((BPair.ofNat c * getAt BPair.unit row j)
      :: List.zipWith
        (fun c row => BPair.ofNat c * getAt BPair.unit row j)
        f M)).oneValue BPair.unit
    have hc : c = 0 := h 0 (Nat.succ_pos _)
    rw [hc]
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _)
        (zipUnit j f M (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))))
      (BPair.add_unit BPair.unit)

/-- The one-hot pairing: a coefficient list reading one at a key
and zero at the rest pairs the rows off at that key's own row. -/
private theorem zipPick (j : Nat) : ∀ (f : List Nat)
    (M : List (List BPair)) (i : Nat), i < f.length →
    getAt 0 f i = 1 → (∀ k, k < f.length → ¬ k = i → getAt 0 f k = 0) →
    (BPair.sum (List.zipWith
      (fun c row => BPair.ofNat c * getAt BPair.unit row j)
      f M)).oneValue (getAt BPair.unit (getAt [] M i) j)
  | [], _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, _ => BPair.oneValue_refl _
  | c :: f, row :: M, 0, _, hone, hoff => by
    show (BPair.sum ((BPair.ofNat c * getAt BPair.unit row j)
      :: List.zipWith
        (fun c row => BPair.ofNat c * getAt BPair.unit row j)
        f M)).oneValue (getAt BPair.unit row j)
    have hc : c = 1 := hone
    rw [hc]
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (show ((BPair.ofNat 1) * getAt BPair.unit row j).oneValue
          (getAt BPair.unit row j) by
        rw [BPair.mul_comm]
        exact BPair.mul_ofNat_one _)
      (zipUnit j f M (fun k hk =>
        hoff (k + 1) (Nat.succ_lt_succ hk) (fun he =>
          Nat.noConfusion he)))) ?_
    exact BPair.add_unit _
  | c :: f, row :: M, i + 1, hi, hone, hoff => by
    show (BPair.sum ((BPair.ofNat c * getAt BPair.unit row j)
      :: List.zipWith
        (fun c row => BPair.ofNat c * getAt BPair.unit row j)
        f M)).oneValue (getAt BPair.unit (getAt [] M i) j)
    have hc : c = 0 :=
      hoff 0 (Nat.succ_pos _) (fun he => Nat.noConfusion he)
    rw [hc]
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _)
        (zipPick j f M i (Nat.lt_of_succ_lt_succ hi) hone
          (fun k hk hne => hoff (k + 1) (Nat.succ_lt_succ hk)
            (fun he => hne (Nat.succ.inj he)))))
      (BPair.unit_add _)

/-- The one-hot fold's coroot read: the fold occupied at the simple
key `i` alone reads the Cartan entry `α_i(α_j^∨)`, the `i`-th row's
`j`-th member (`con:gentable`'s Cartan reads). -/
theorem corootAt_oneHot (t : Table) (i j : Nat) (hi : i < t.rank) :
    (corootAt t ((List.range t.rank).map (fun k => if k == i then 1 else 0))
      j).oneValue (getAt BPair.unit (getAt [] t.cartan i) j) := by
  have hlen : ((List.range t.rank).map
      (fun k => if k == i then 1 else 0)).length = t.rank :=
    ground.length_mapRange _ t.rank
  have hread : ∀ k, k < t.rank → getAt 0 ((List.range t.rank).map
      (fun k => if k == i then 1 else 0)) k
      = if k == i then 1 else 0 := fun k hk => by
    rw [ground.getAt_map 0 0 _ (List.range t.rank) k
      (by rw [ground.length_range]; exact hk),
      ground.getAt_range t.rank k hk]
  show (BPair.sum (List.zipWith
    (fun c row => BPair.ofNat c * getAt BPair.unit row j)
    ((List.range t.rank).map (fun k => if k == i then 1 else 0))
    t.cartan)).oneValue _
  refine zipPick j _ t.cartan i (by rw [hlen]; exact hi) ?_ ?_
  · rw [hread i hi, if_pos (ground.eqBeqOf rfl)]
  · intro k hk hne
    rw [hlen] at hk
    rw [hread k hk, if_neg (fun ht : (k == i) = true =>
      hne (ground.beqEqOf ht))]

end gentable
