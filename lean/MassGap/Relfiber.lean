import MassGap.Grading
import MassGap.Fiberdec
/-!
`lem:relfiber` — the separated sector's tensor calculus.  Beyond
the locality band the `ϱ`-sector's pencil agrees, off the collar,
with the components' tensor-sum pencil, and this tier owns that
display's carrier over the balance pairs.

`tensorV` is the tensor product at the product index: two
coefficient lists at key counts `m` and `n` give the list at
`m * n` keys whose entry at `i * n + k` is the factors' entries'
product at its canonical representative.  `tensorM` is the same
join on the rows: at row counts `m`, `n` and widths `p`, `r` the
product carries `m * n` rows of width `p * r`, its entry at the
key pair `(i * n + k, a * r + b)` the two factors' entries'
product.  The reads below are the display's own laws — the shape,
the entry reads at the product index, the pairing factorizing
(the product index's fold collects to the factors' folds'
product, `def:ground`'s identities), the action and the matrix
product reading factorwise, the key-list exchange distributing
over the tensor, linearity in each slot with the scalar weighting
and the memberwise swap passing through, associativity on the
nose, and the identity at the product order the two identities'
own tensor.

`tensorPow G k` is the tensor power `G^{⊗k}`, at the unit power
the scalars' line `idMat 1`; `sumPencil H G ϱ` is the tensor-sum
pencil
`H^{(ϱ)} = ∑_{a+b+1=ϱ} G^{⊗a} ⊗ H^{(1)} ⊗ G^{⊗b}`,
the fold over the factor splittings `a + b + 1 = ϱ`.  The fold
runs on the leading factor: the splitting at `a = 0` is
`H ⊗ G^{⊗(ϱ-1)}`, and every splitting at `a ≥ 1` carries one
leading `G` off a splitting of `ϱ - 1`, so the recursion
`sumPencil H G (ϱ+1) = H ⊗ G^{⊗ϱ} + G ⊗ sumPencil H G ϱ`
enumerates the `ϱ` splittings exactly once, seeded at the vacant
sum `nullMat 1 1`.

A balance pair carries a value rather than a spelling, so each
law is stated at the value read where the canonical
representatives differ and at `Eq` where they agree.

Clause (iii) rides on that calculus.  A gram whose split's blocks
all sit at order one tensors without moving its partner's form off
its side (`tensor_form_left`, `tensor_form_right`), the tensor
congruence reads factorwise (`congr_tensorM`) and a first-slot
factor commutes with a second-slot one (`comm_shift`); the
separated bottom then adds `ϱ` times and the sector's pair clears
every bracket with top at or below `ϱℓ` (`bottomClear`).  Clause
(ii)'s fibering reads through those two congruences at
`lem:fiberdec`'s own chord kit run at the relative translation's
matrix, the batteries pinning the split counts' sum at stated
splittings.

Clause (i) reads at the index layer beneath that calculus.  A
class of band components joins to one configuration in the
region's key order (`joinAll`, the vacant class the unit
configuration at that key range), and the class's separation is
the vertex-disjoint read at every pair — one component against a
class (`allDisj`) and the class over its own members
(`disjAll`), each decided at the region's vertex range.  Two
reads of a separated pair follow.  The electric content adds:
the join's Casimir fold is the two parts' folds' sum
(`contentN_join`), since a key occupied by one part reads the
unit in the other — its tail is a vertex of the region, both
parts' incident labels would meet there, and the vertex-disjoint
read refuses that.  And a plaquette meets at most one
component's reach: at supports separated beyond the locality
band no boundary word of the region reads both neighborhoods
(`sepPlaq`), a vertex shared by the two reaches sitting in both
reach lists against the separation.  The reads close over a
class: the content adds member by member (`contentN_joinAll`)
and the fiber dimensions multiply (`fibProd_joinAll`), each at
the unit's own equality read, the interface's `eqLRefl` field at
the unit; and the stencil row moves one
component with a separated spectator riding every target
(`plaqRow_join`), the pair read whose class form enters at the
spectators' own join.
-/

namespace relfiber
open ground elim

/-! ### The tensor carriers -/

/-- The tensor product at the product index: at key counts `m` and
`n` the entry at `i * n + k` is the two entries' product at its
canonical representative. -/
def tensorV (u v : List BPair) : List BPair :=
  u.flatMap (fun x => v.map (fun y => (x * y).norm))

/-- The rows' tensor product: the row keys join at the product
index, each row the two rows' own tensor. -/
def tensorM (A B : Mat) : Mat :=
  A.flatMap (fun ra => B.map (fun rb => tensorV ra rb))

/-- The tensor power `G^{⊗k}`, at the unit power the scalars'
line. -/
def tensorPow (G : Mat) : Nat → Mat
  | 0 => inertia.idMat 1
  | k + 1 => tensorM G (tensorPow G k)

/-- The tensor-sum pencil `∑_{a+b+1=ϱ} G^{⊗a} ⊗ H ⊗ G^{⊗b}`, the
fold over the factor splittings on the leading factor. -/
def sumPencil (H G : Mat) : Nat → Mat
  | 0 => nullMat 1 1
  | k + 1 => matAdd (tensorM H (tensorPow G k))
      (tensorM G (sumPencil H G k))

/-! ### The list kit the folds consume -/

private theorem matOne_app : ∀ (P P' Q Q' : Mat),
    P.length = P'.length → matOneValue P P' → matOneValue Q Q' →
    matOneValue (P ++ Q) (P' ++ Q')
  | [], [], _, _, _, _, hq => hq
  | [], _ :: _, _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, _, hl, _, _ => nomatch hl
  | _ :: P, _ :: P', Q, Q', hl, hP, hQ =>
    ⟨hP.1, matOne_app P P' Q Q' (Nat.succ.inj hl) hP.2 hQ⟩

/-! ### The index pairing -/

private theorem mulLeMulR (n : Nat) {i a : Nat} (h : i ≤ a) :
    i * n ≤ a * n := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd, ground.mulAddR]
  exact Nat.le_add_right (i * n) (d * n)

private theorem pairLt {n : Nat} (i k a b : Nat) (hk : k < n)
    (hlt : i < a) : i * n + k < a * n + b := by
  have h1 : i * n + k < (i + 1) * n := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left hk (i * n)
  exact Nat.lt_of_lt_of_le h1
    (Nat.le_trans (mulLeMulR n hlt) (Nat.le_add_right (a * n) b))

private theorem pairInj {n : Nat} (i k a b : Nat) (hk : k < n)
    (hb : b < n) (h : i * n + k = a * n + b) : i = a ∧ k = b := by
  have hia : i = a := by
    cases Nat.lt_or_ge i a with
    | inl hlt =>
      exact absurd h (Nat.ne_of_lt (pairLt i k a b hk hlt))
    | inr hge =>
      cases Nat.lt_or_ge a i with
      | inl hlt =>
        exact absurd h.symm (Nat.ne_of_lt (pairLt a b i k hb hlt))
      | inr hge2 => exact Nat.le_antisymm hge2 hge
  refine ⟨hia, ?_⟩
  rw [hia] at h
  exact ground.addCancelL (a * n) h

private theorem pairIdxLt {n m i k : Nat}
    (h : i * n + k < m * n) : i < m := by
  cases Nat.lt_or_ge i m with
  | inl hlt => exact hlt
  | inr hge =>
    exact absurd (Nat.lt_of_lt_of_le h
        (Nat.le_trans (mulLeMulR n hge) (Nat.le_add_right (i * n) k)))
      (Nat.lt_irrefl _)

private theorem pairSplit (n : Nat) (hn : 0 < n) :
    ∀ t : Nat, ∃ i k, k < n ∧ t = i * n + k
  | 0 => ⟨0, 0, hn, (Nat.zero_mul n).symm⟩
  | t + 1 => by
    obtain ⟨i, k, hk, ht⟩ := pairSplit n hn t
    cases Nat.lt_or_ge (k + 1) n with
    | inl hlt =>
      refine ⟨i, k + 1, hlt, ?_⟩
      rw [ht]
      exact Nat.add_assoc (i * n) k 1
    | inr hge =>
      have hkn : k + 1 = n := Nat.le_antisymm hk hge
      have h2 : (i + 1) * n = i * n + (k + 1) := by
        rw [Nat.succ_mul, hkn]
      refine ⟨i + 1, 0, hn, ?_⟩
      show t + 1 = (i + 1) * n + 0
      rw [Nat.add_zero, h2, ← Nat.add_assoc, ← ht]

/-! ### The shape -/

/-- The tensor's key count is the two key counts' product. -/
theorem tensorV_length : ∀ u v : List BPair,
    (tensorV u v).length = u.length * v.length
  | [], v => (Nat.zero_mul v.length).symm
  | x :: u, v => by
    show (v.map (fun y => (x * y).norm) ++ tensorV u v).length
      = (u.length + 1) * v.length
    rw [ground.length_append, ground.length_map, tensorV_length u v,
      Nat.succ_mul]
    exact Nat.add_comm v.length (u.length * v.length)

/-- The tensor's row count is the two row counts' product. -/
theorem tensorM_length : ∀ A B : Mat,
    (tensorM A B).length = A.length * B.length
  | [], B => (Nat.zero_mul B.length).symm
  | ra :: A, B => by
    show ((B.map (fun rb => tensorV ra rb)) ++ tensorM A B).length
      = (A.length + 1) * B.length
    rw [ground.length_append, ground.length_map, tensorM_length A B,
      Nat.succ_mul]
    exact Nat.add_comm B.length (A.length * B.length)

private theorem rowsLen_mapTensor (m n : Nat) (ra : List BPair)
    (hra : ra.length = m) :
    ∀ B : Mat, rowsLen n B →
      rowsLen (m * n) (B.map (fun rb => tensorV ra rb))
  | [], _ => trivial
  | rb :: B, hB =>
    ⟨by rw [tensorV_length ra rb, hra, hB.1],
     rowsLen_mapTensor m n ra hra B hB.2⟩

/-- The tensor's width is the two widths' product. -/
theorem rowsLen_tensorM (m n : Nat) : ∀ A B : Mat, rowsLen m A →
    rowsLen n B → rowsLen (m * n) (tensorM A B)
  | [], _, _, _ => trivial
  | ra :: A, B, hA, hB =>
    rowsLen_append (m * n) (rowsLen_mapTensor m n ra hA.1 B hB)
      (rowsLen_tensorM m n A B hA.2 hB)

/-- The tensor power's shape: the square order the row count's own
power. -/
theorem tensorPow_shape (G : Mat) (hG : rowsLen G.length G) :
    ∀ k : Nat, rowsLen (G.length ^ k) (tensorPow G k)
      ∧ (tensorPow G k).length = G.length ^ k
  | 0 => ⟨inertia.idMat_rows 1, inertia.idMat_len 1⟩
  | k + 1 => by
    have ih := tensorPow_shape G hG k
    refine ⟨?_, ?_⟩
    · show rowsLen (G.length ^ k * G.length)
        (tensorM G (tensorPow G k))
      rw [Nat.mul_comm (G.length ^ k) G.length]
      exact rowsLen_tensorM G.length (G.length ^ k) G (tensorPow G k)
        hG ih.1
    · show (tensorM G (tensorPow G k)).length = G.length ^ k * G.length
      rw [tensorM_length, ih.2, Nat.mul_comm (G.length ^ k) G.length]

/-! ### The entry reads at the product index -/

/-- The tensor's entry at the product index. -/
theorem getAt_tensorV : ∀ (u v : List BPair) (i k : Nat),
    i < u.length → k < v.length →
    ground.getAt BPair.unit (tensorV u v) (i * v.length + k)
      = (ground.getAt BPair.unit u i
        * ground.getAt BPair.unit v k).norm
  | [], _, i, _, hi, _ => absurd hi (Nat.not_lt_zero i)
  | x :: u, v, 0, k, _, hk => by
    show ground.getAt BPair.unit
        (v.map (fun y => (x * y).norm) ++ tensorV u v) (0 * v.length + k)
      = (x * ground.getAt BPair.unit v k).norm
    rw [Nat.zero_mul, Nat.zero_add,
      ground.getAt_append BPair.unit
        (v.map (fun y => (x * y).norm)) (tensorV u v) k,
      if_pos (show k < (v.map (fun y => (x * y).norm)).length from by
        rw [ground.length_map]; exact hk),
      ground.getAt_map BPair.unit BPair.unit
        (fun y => (x * y).norm) v k hk]
  | x :: u, v, i + 1, k, hi, hk => by
    show ground.getAt BPair.unit
        (v.map (fun y => (x * y).norm) ++ tensorV u v)
        ((i + 1) * v.length + k)
      = (ground.getAt BPair.unit u i
        * ground.getAt BPair.unit v k).norm
    have hidx : (i + 1) * v.length + k
        = (v.map (fun y => (x * y).norm)).length
          + (i * v.length + k) := by
      rw [ground.length_map, Nat.succ_mul, Nat.add_right_comm,
        Nat.add_comm (i * v.length + k) v.length]
    rw [hidx, ground.getAt_append_add BPair.unit
        (v.map (fun y => (x * y).norm)) (tensorV u v)
        (i * v.length + k),
      getAt_tensorV u v i k (Nat.lt_of_succ_lt_succ hi) hk]

/-- The tensor's row at the product index. -/
theorem getAt_tensorM : ∀ (A B : Mat) (i k : Nat),
    i < A.length → k < B.length →
    ground.getAt [] (tensorM A B) (i * B.length + k)
      = tensorV (ground.getAt [] A i) (ground.getAt [] B k)
  | [], _, i, _, hi, _ => absurd hi (Nat.not_lt_zero i)
  | ra :: A, B, 0, k, _, hk => by
    show ground.getAt []
        (B.map (fun rb => tensorV ra rb) ++ tensorM A B) (0 * B.length + k)
      = tensorV ra (ground.getAt [] B k)
    rw [Nat.zero_mul, Nat.zero_add,
      ground.getAt_append ([] : List BPair)
        (B.map (fun rb => tensorV ra rb)) (tensorM A B) k,
      if_pos (show k < (B.map (fun rb => tensorV ra rb)).length from by
        rw [ground.length_map]; exact hk),
      ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun rb => tensorV ra rb) B k hk]
  | ra :: A, B, i + 1, k, hi, hk => by
    show ground.getAt []
        (B.map (fun rb => tensorV ra rb) ++ tensorM A B)
        ((i + 1) * B.length + k)
      = tensorV (ground.getAt [] A i) (ground.getAt [] B k)
    have hidx : (i + 1) * B.length + k
        = (B.map (fun rb => tensorV ra rb)).length
          + (i * B.length + k) := by
      rw [ground.length_map, Nat.succ_mul, Nat.add_right_comm,
        Nat.add_comm (i * B.length + k) B.length]
    rw [hidx, ground.getAt_append_add ([] : List BPair)
        (B.map (fun rb => tensorV ra rb)) (tensorM A B)
        (i * B.length + k),
      getAt_tensorM A B i k (Nat.lt_of_succ_lt_succ hi) hk]

/-! ### The pairing factorizes -/

private theorem dotP_mapMul (a b : BPair) (v z : List BPair) :
    (dotP (poly.scaleP a v) (poly.scaleP b z)).oneValue
      (a * b * dotP v z) := by
  refine BPair.oneValue_trans (dotP_scaleRow a v (poly.scaleP b z)) ?_
  rw [BPair.mul_assoc]
  refine BPair.mul_congr (BPair.oneValue_refl a) ?_
  rw [dotP_comm v (poly.scaleP b z)]
  refine BPair.oneValue_trans (dotP_scaleRow b z v) ?_
  rw [dotP_comm z v]
  exact BPair.oneValue_refl _

/-- The product index's fold collects to the factors' folds'
product (`def:ground`'s identities). -/
theorem dotP_tensorV : ∀ (u w v z : List BPair),
    v.length = z.length →
    (dotP (tensorV u v) (tensorV w z)).oneValue (dotP u w * dotP v z)
  | [], _, v, z, _ =>
    BPair.oneValue_symm (BPair.unit_mul (dotP v z))
  | a :: u, [], v, z, _ => by
    show (dotP (tensorV (a :: u) v) []).oneValue (BPair.unit * dotP v z)
    rw [elim.dotP_nil_right]
    exact BPair.oneValue_symm (BPair.unit_mul (dotP v z))
  | a :: u, b :: w, v, z, hl2 => by
    show (dotP (v.map (fun y => (a * y).norm) ++ tensorV u v)
        (z.map (fun y => (b * y).norm) ++ tensorV w z)).oneValue
      ((a * b + dotP u w) * dotP v z)
    refine BPair.oneValue_trans
      (dotP_append (v.map (fun y => (a * y).norm))
        (z.map (fun y => (b * y).norm)) (tensorV u v) (tensorV w z)
        (by rw [ground.length_map, ground.length_map, hl2])) ?_
    rw [BPair.right_distrib (a * b) (dotP u w) (dotP v z)]
    exact BPair.add_congr (dotP_mapMul a b v z)
      (dotP_tensorV u w v z hl2)

/-- The skipping fold at two tensors reads the factors' folds'
product at its canonical representative. -/
theorem dotN_tensorV (ra rb c d : List BPair)
    (h2 : rb.length = d.length) :
    (dotN (tensorV ra rb) (tensorV c d)).oneValue
      ((dotN ra c * dotN rb d).norm) :=
  BPair.oneValue_trans (dotN_read (tensorV ra rb) (tensorV c d))
    (BPair.oneValue_trans (dotP_tensorV ra c rb d h2)
      (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.norm_oneValue (dotN ra c * dotN rb d))
        (BPair.mul_congr (dotN_read ra c) (dotN_read rb d)))))

/-! ### The action reads factorwise -/

private theorem matVec_tensorRow (ra u v : List BPair) :
    ∀ B : Mat, rowsLen v.length B →
      poly.oneValue
        ((B.map (fun rb => tensorV ra rb)).map
          (fun rr => dotN rr (tensorV u v)))
        ((B.map (fun rr => dotN rr v)).map
          (fun y => (dotN ra u * y).norm))
  | [], _ => trivial
  | rb :: B, hB =>
    ⟨dotN_tensorV ra rb u v hB.1, matVec_tensorRow ra u v B hB.2⟩

/-- The action against a tensor is the actions' own tensor. -/
theorem matVec_tensorM : ∀ (A B : Mat) (u v : List BPair),
    rowsLen v.length B →
    poly.oneValue (matVec (tensorM A B) (tensorV u v))
      (tensorV (matVec A u) (matVec B v))
  | [], _, _, _, _ => trivial
  | ra :: A, B, u, v, hB => by
    show poly.oneValue
        (matVec (B.map (fun rb => tensorV ra rb) ++ tensorM A B)
          (tensorV u v))
        ((matVec B v).map (fun y => (dotN ra u * y).norm)
          ++ tensorV (matVec A u) (matVec B v))
    rw [matVec_append]
    exact poly.oneValue_append _ _ _ _
      (by rw [matVec_length, ground.length_map, ground.length_map,
        matVec_length])
      (matVec_tensorRow ra u v B hB)
      (matVec_tensorM A B u v hB)

/-! ### The scalar weighting and the memberwise swap -/

private theorem normMulL (c x y : BPair) :
    ((c * x).norm * y).norm = (c * (x * y).norm).norm := by
  rw [BPair.norm_congr (BPair.mul_congr (BPair.norm_oneValue (c * x))
      (BPair.oneValue_refl y)),
    BPair.norm_congr (BPair.mul_congr (BPair.oneValue_refl c)
      (BPair.norm_oneValue (x * y))),
    BPair.mul_assoc]

private theorem normMulR (c x y : BPair) :
    ((x * (c * y).norm).norm) = (c * (x * y).norm).norm := by
  rw [BPair.norm_congr (BPair.mul_congr (BPair.oneValue_refl x)
      (BPair.norm_oneValue (c * y))),
    BPair.norm_congr (BPair.mul_congr (BPair.oneValue_refl c)
      (BPair.norm_oneValue (x * y))),
    BPair.mul_left_comm x c y]

private theorem tensorV_mapL (g : BPair → BPair)
    (h : ∀ x y : BPair, (g x * y).norm = g ((x * y).norm)) :
    ∀ u v : List BPair, tensorV (u.map g) v = (tensorV u v).map g
  | [], _ => rfl
  | x :: u, v => by
    show v.map (fun y => (g x * y).norm) ++ tensorV (u.map g) v
      = (v.map (fun y => (x * y).norm) ++ tensorV u v).map g
    rw [ground.map_append, ground.map_map, tensorV_mapL g h u v]
    exact congrArg (fun w => w ++ (tensorV u v).map g)
      (ground.map_congr_all _ _ (fun y => h x y) v)

private theorem tensorV_mapR (g : BPair → BPair)
    (h : ∀ x y : BPair, (x * g y).norm = g ((x * y).norm)) :
    ∀ u v : List BPair, tensorV u (v.map g) = (tensorV u v).map g
  | [], _ => rfl
  | x :: u, v => by
    show (v.map g).map (fun y => (x * y).norm) ++ tensorV u (v.map g)
      = (v.map (fun y => (x * y).norm) ++ tensorV u v).map g
    rw [ground.map_append, ground.map_map, ground.map_map,
      tensorV_mapR g h u v]
    exact congrArg (fun w => w ++ (tensorV u v).map g)
      (ground.map_congr_all _ _ (fun y => h x y) v)

private theorem tensorM_rowMapL (g : List BPair → List BPair)
    (h : ∀ ra rb : List BPair, tensorV (g ra) rb = g (tensorV ra rb)) :
    ∀ A B : Mat, tensorM (A.map g) B = (tensorM A B).map g
  | [], _ => rfl
  | ra :: A, B => by
    show B.map (fun rb => tensorV (g ra) rb) ++ tensorM (A.map g) B
      = (B.map (fun rb => tensorV ra rb) ++ tensorM A B).map g
    rw [ground.map_append, ground.map_map, tensorM_rowMapL g h A B]
    exact congrArg (fun w => w ++ (tensorM A B).map g)
      (ground.map_congr_all _ _ (fun rb => h ra rb) B)

private theorem tensorM_rowMapR (g : List BPair → List BPair)
    (h : ∀ ra rb : List BPair, tensorV ra (g rb) = g (tensorV ra rb)) :
    ∀ A B : Mat, tensorM A (B.map g) = (tensorM A B).map g
  | [], _ => rfl
  | ra :: A, B => by
    show (B.map g).map (fun rb => tensorV ra rb) ++ tensorM A (B.map g)
      = (B.map (fun rb => tensorV ra rb) ++ tensorM A B).map g
    rw [ground.map_append, ground.map_map, ground.map_map,
      tensorM_rowMapR g h A B]
    exact congrArg (fun w => w ++ (tensorM A B).map g)
      (ground.map_congr_all _ _ (fun rb => h ra rb) B)

/-- A weight on the first factor is the tensor's own weight. -/
theorem tensorM_scaleL (c : BPair) (A B : Mat) :
    tensorM (inertia.matScaleB c A) B
      = inertia.matScaleB c (tensorM A B) :=
  tensorM_rowMapL (fun r => r.map (fun x => (c * x).norm))
    (fun ra rb => tensorV_mapL (fun x => (c * x).norm)
      (fun x y => normMulL c x y) ra rb) A B

/-- A weight on the second factor is the tensor's own weight. -/
theorem tensorM_scaleR (c : BPair) (A B : Mat) :
    tensorM A (inertia.matScaleB c B)
      = inertia.matScaleB c (tensorM A B) :=
  tensorM_rowMapR (fun r => r.map (fun x => (c * x).norm))
    (fun ra rb => tensorV_mapR (fun x => (c * x).norm)
      (fun x y => normMulR c x y) ra rb) A B

/-- The memberwise swap on the first factor is the tensor's own. -/
theorem tensorM_swapL (A B : Mat) :
    tensorM (matSwap A) B = matSwap (tensorM A B) :=
  tensorM_rowMapL (fun r => r.map BPair.swap)
    (fun ra rb => tensorV_mapL BPair.swap
      (fun x y => by rw [BPair.swap_mul x y, BPair.norm_swap (x * y)])
      ra rb) A B

/-- The memberwise swap on the second factor is the tensor's own. -/
theorem tensorM_swapR (A B : Mat) :
    tensorM A (matSwap B) = matSwap (tensorM A B) :=
  tensorM_rowMapR (fun r => r.map BPair.swap)
    (fun ra rb => tensorV_mapR BPair.swap
      (fun x y => by rw [BPair.mul_swap x y, BPair.norm_swap (x * y)])
      ra rb) A B

/-! ### Associativity -/

private theorem tensorV_append (a b w : List BPair) :
    tensorV (a ++ b) w = tensorV a w ++ tensorV b w :=
  ground.flatMap_append _ a b

/-- The tensor associates on the nose. -/
theorem tensorV_assoc : ∀ u v w : List BPair,
    tensorV (tensorV u v) w = tensorV u (tensorV v w)
  | [], _, _ => rfl
  | x :: u, v, w => by
    show tensorV (v.map (fun y => (x * y).norm) ++ tensorV u v) w
      = (tensorV v w).map (fun z => (x * z).norm)
        ++ tensorV u (tensorV v w)
    rw [tensorV_append, tensorV_mapL (fun y => (x * y).norm)
        (fun y z => normMulL x y z) v w,
      tensorV_assoc u v w]

private theorem tensorM_append (P Q C : Mat) :
    tensorM (P ++ Q) C = tensorM P C ++ tensorM Q C :=
  ground.flatMap_append _ P Q

/-- The rows' tensor associates on the nose. -/
theorem tensorM_assoc : ∀ A B C : Mat,
    tensorM (tensorM A B) C = tensorM A (tensorM B C)
  | [], _, _ => rfl
  | ra :: A, B, C => by
    show tensorM (B.map (fun rb => tensorV ra rb) ++ tensorM A B) C
      = (tensorM B C).map (fun rc => tensorV ra rc)
        ++ tensorM A (tensorM B C)
    rw [tensorM_append, tensorM_rowMapL (fun rb => tensorV ra rb)
        (fun rb rc => tensorV_assoc ra rb rc) B C,
      tensorM_assoc A B C]

/-! ### Linearity in each slot -/

private theorem tensorRow_addL (x x' : BPair) : ∀ rb : List BPair,
    poly.oneValue (rb.map (fun y => ((x + x') * y).norm))
      (List.zipWith (fun p q => p + q) (rb.map (fun y => (x * y).norm))
        (rb.map (fun y => (x' * y).norm)))
  | [] => trivial
  | y :: rb =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue ((x + x') * y)) (by
      rw [BPair.right_distrib x x' y]
      exact BPair.add_congr
        (BPair.oneValue_symm (BPair.norm_oneValue (x * y)))
        (BPair.oneValue_symm (BPair.norm_oneValue (x' * y)))),
     tensorRow_addL x x' rb⟩

private theorem tensorV_addL : ∀ ra ra' rb : List BPair,
    poly.oneValue (tensorV (List.zipWith (fun p q => p + q) ra ra') rb)
      (List.zipWith (fun p q => p + q) (tensorV ra rb) (tensorV ra' rb))
  | [], _, _ => trivial
  | x :: ra, [], rb => by
    show poly.oneValue []
      (List.zipWith (fun p q => p + q) (tensorV (x :: ra) rb) [])
    rw [ground.zipWith_nil_right]
    exact trivial
  | x :: ra, x' :: ra', rb => by
    show poly.oneValue
        (rb.map (fun y => ((x + x') * y).norm)
          ++ tensorV (List.zipWith (fun p q => p + q) ra ra') rb)
        (List.zipWith (fun p q => p + q)
          (rb.map (fun y => (x * y).norm) ++ tensorV ra rb)
          (rb.map (fun y => (x' * y).norm) ++ tensorV ra' rb))
    rw [ground.zipWith_append (fun p q : BPair => p + q) _ _ _ _
      (by rw [ground.length_map, ground.length_map])]
    exact poly.oneValue_append _ _ _ _
      (by rw [ground.length_map,
        length_zipWith (fun p q : BPair => p + q) _ _ rb.length
          (ground.length_map _ rb) (ground.length_map _ rb)])
      (tensorRow_addL x x' rb) (tensorV_addL ra ra' rb)

private theorem tensorM_addRowL (ra ra' : List BPair) : ∀ B : Mat,
    matOneValue
      (B.map (fun rb =>
        tensorV (List.zipWith (fun p q => p + q) ra ra') rb))
      (List.zipWith (List.zipWith (fun p q => p + q))
        (B.map (fun rb => tensorV ra rb))
        (B.map (fun rb => tensorV ra' rb)))
  | [] => trivial
  | rb :: B => ⟨tensorV_addL ra ra' rb, tensorM_addRowL ra ra' B⟩

/-- The tensor adds in its first slot. -/
theorem tensorM_addL : ∀ A A' B : Mat,
    matOneValue (tensorM (matAdd A A') B)
      (matAdd (tensorM A B) (tensorM A' B))
  | [], _, _ => trivial
  | ra :: A, [], B => by
    show matOneValue []
      (List.zipWith (List.zipWith (fun p q => p + q))
        (tensorM (ra :: A) B) [])
    rw [ground.zipWith_nil_right]
    exact trivial
  | ra :: A, ra' :: A', B => by
    show matOneValue
        (B.map (fun rb =>
          tensorV (List.zipWith (fun p q => p + q) ra ra') rb)
          ++ tensorM (matAdd A A') B)
        (List.zipWith (List.zipWith (fun p q => p + q))
          (B.map (fun rb => tensorV ra rb) ++ tensorM A B)
          (B.map (fun rb => tensorV ra' rb) ++ tensorM A' B))
    rw [ground.zipWith_append (List.zipWith (fun p q : BPair => p + q)) _ _ _ _
      (by rw [ground.length_map, ground.length_map])]
    exact matOne_app _ _ _ _
      (by rw [ground.length_map,
        length_zipWith (List.zipWith (fun p q : BPair => p + q)) _ _
          B.length (ground.length_map _ B) (ground.length_map _ B)])
      (tensorM_addRowL ra ra' B) (tensorM_addL A A' B)

private theorem tensorRow_addR (x : BPair) : ∀ rb rb' : List BPair,
    poly.oneValue
      ((List.zipWith (fun p q => p + q) rb rb').map
        (fun y => (x * y).norm))
      (List.zipWith (fun p q => p + q) (rb.map (fun y => (x * y).norm))
        (rb'.map (fun y => (x * y).norm)))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | y :: rb, y' :: rb' =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue (x * (y + y'))) (by
      rw [BPair.left_distrib x y y']
      exact BPair.add_congr
        (BPair.oneValue_symm (BPair.norm_oneValue (x * y)))
        (BPair.oneValue_symm (BPair.norm_oneValue (x * y')))),
     tensorRow_addR x rb rb'⟩

private theorem tensorV_addR : ∀ ra rb rb' : List BPair,
    rb.length = rb'.length →
    poly.oneValue (tensorV ra (List.zipWith (fun p q => p + q) rb rb'))
      (List.zipWith (fun p q => p + q) (tensorV ra rb) (tensorV ra rb'))
  | [], _, _, _ => trivial
  | x :: ra, rb, rb', hl => by
    show poly.oneValue
        ((List.zipWith (fun p q => p + q) rb rb').map
            (fun y => (x * y).norm)
          ++ tensorV ra (List.zipWith (fun p q => p + q) rb rb'))
        (List.zipWith (fun p q => p + q)
          (rb.map (fun y => (x * y).norm) ++ tensorV ra rb)
          (rb'.map (fun y => (x * y).norm) ++ tensorV ra rb'))
    rw [ground.zipWith_append (fun p q : BPair => p + q) _ _ _ _
      (by rw [ground.length_map, ground.length_map, hl])]
    exact poly.oneValue_append _ _ _ _
      (by rw [ground.length_map,
        length_zipWith (fun p q : BPair => p + q) rb rb' rb.length rfl
          hl.symm,
        length_zipWith (fun p q : BPair => p + q) _ _ rb.length
          (ground.length_map _ rb)
          (by rw [ground.length_map]; exact hl.symm)])
      (tensorRow_addR x rb rb') (tensorV_addR ra rb rb' hl)

private theorem tensorM_addRowR (ra : List BPair) (w : Nat) :
    ∀ B B' : Mat, rowsLen w B → rowsLen w B' →
    matOneValue ((matAdd B B').map (fun rb => tensorV ra rb))
      (List.zipWith (List.zipWith (fun p q => p + q))
        (B.map (fun rb => tensorV ra rb))
        (B'.map (fun rb => tensorV ra rb)))
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | rb :: B, rb' :: B', hB, hB' =>
    ⟨tensorV_addR ra rb rb' (by rw [hB.1, hB'.1]),
     tensorM_addRowR ra w B B' hB.2 hB'.2⟩

/-- The tensor adds in its second slot, at a stated width: the
summands' strides are the shared width, so the product index's
blocks meet. -/
theorem tensorM_addR (w : Nat) : ∀ A B B' : Mat,
    B.length = B'.length → rowsLen w B → rowsLen w B' →
    matOneValue (tensorM A (matAdd B B'))
      (matAdd (tensorM A B) (tensorM A B'))
  | [], _, _, _, _, _ => trivial
  | ra :: A, B, B', hl, hB, hB' => by
    show matOneValue
        ((matAdd B B').map (fun rb => tensorV ra rb)
          ++ tensorM A (matAdd B B'))
        (List.zipWith (List.zipWith (fun p q => p + q))
          (B.map (fun rb => tensorV ra rb) ++ tensorM A B)
          (B'.map (fun rb => tensorV ra rb) ++ tensorM A B'))
    rw [ground.zipWith_append (List.zipWith (fun p q : BPair => p + q)) _ _ _ _
      (by rw [ground.length_map, ground.length_map, hl])]
    exact matOne_app _ _ _ _
      (by rw [ground.length_map,
        show (matAdd B B').length = B.length from
          length_zipWith (List.zipWith (fun p q : BPair => p + q)) B B'
            B.length rfl hl.symm,
        length_zipWith (List.zipWith (fun p q : BPair => p + q)) _ _
          B.length (ground.length_map _ B)
          (by rw [ground.length_map]; exact hl.symm)])
      (tensorM_addRowR ra w B B' hB hB')
      (tensorM_addR w A B B' hl hB hB')

/-! ### The key-list exchange -/

private theorem tensorM_nil : ∀ A : Mat, tensorM A [] = []
  | [] => rfl
  | _ :: A => tensorM_nil A

private theorem transposeM_tensorM_pos (p q r s : Nat) (A B : Mat)
    (hAl : A.length = p) (hA : rowsLen q A) (hBl : B.length = r)
    (hB : rowsLen s B) (hp : 0 < A.length) (hr : 0 < B.length) :
    transposeM (tensorM A B)
      = tensorM (transposeM A) (transposeM B) := by
  have hAB : rowsLen (q * s) (tensorM A B) :=
    rowsLen_tensorM q s A B hA hB
  have hABl : (tensorM A B).length = A.length * B.length :=
    tensorM_length A B
  have hAB0 : 0 < (tensorM A B).length := by
    rw [hABl]; exact Nat.mul_pos hp hr
  have hLl : (transposeM (tensorM A B)).length = q * s :=
    length_transposeM (tensorM A B) hAB hAB0
  have hAtl : (transposeM A).length = q := length_transposeM A hA hp
  have hBtl : (transposeM B).length = s := length_transposeM B hB hr
  have hAtr : rowsLen p (transposeM A) := by
    have h := rowsLen_transposeM A; rw [hAl] at h; exact h
  have hBtr : rowsLen r (transposeM B) := by
    have h := rowsLen_transposeM B; rw [hBl] at h; exact h
  have hRl : (tensorM (transposeM A) (transposeM B)).length = q * s := by
    rw [tensorM_length, hAtl, hBtl]
  have hLr : rowsLen (p * r) (transposeM (tensorM A B)) := by
    have h := rowsLen_transposeM (tensorM A B)
    rw [hABl, hAl, hBl] at h
    exact h
  have hRr : rowsLen (p * r)
      (tensorM (transposeM A) (transposeM B)) :=
    rowsLen_tensorM p r (transposeM A) (transposeM B) hAtr hBtr
  refine ground.getAt_ext ([] : List BPair) _ _ (by rw [hLl, hRl]) ?_
  intro t ht
  rw [hLl] at ht
  have hs0 : 0 < s := by
    cases s with
    | zero => rw [Nat.mul_zero] at ht; exact absurd ht (Nat.not_lt_zero t)
    | succ s0 => exact Nat.succ_pos s0
  refine ground.getAt_ext BPair.unit _ _ ?_ ?_
  · rw [rowsLen_getAt _ t hLr (by rw [hLl]; exact ht),
      rowsLen_getAt _ t hRr (by rw [hRl]; exact ht)]
  intro u hu
  rw [rowsLen_getAt _ t hLr (by rw [hLl]; exact ht)] at hu
  have hr0 : 0 < r := by
    cases r with
    | zero => rw [Nat.mul_zero] at hu; exact absurd hu (Nat.not_lt_zero u)
    | succ r0 => exact Nat.succ_pos r0
  obtain ⟨i, k, hk, htik⟩ := pairSplit s hs0 t
  obtain ⟨a, b, hb, huab⟩ := pairSplit r hr0 u
  have hi : i < q := pairIdxLt (by rw [← htik]; exact ht)
  have ha : a < p := pairIdxLt (by rw [← huab]; exact hu)
  have hrowA : (ground.getAt ([] : List BPair) A a).length = q :=
    rowsLen_getAt A a hA (by rw [hAl]; exact ha)
  have hrowB : (ground.getAt ([] : List BPair) B b).length = s :=
    rowsLen_getAt B b hB (by rw [hBl]; exact hb)
  have hL : ground.getAt BPair.unit
      (ground.getAt [] (transposeM (tensorM A B)) t) u
      = (ground.getAt BPair.unit (ground.getAt [] A a) i
        * ground.getAt BPair.unit (ground.getAt [] B b) k).norm := by
    rw [getAt_transposeM BPair.unit (tensorM A B) hAB t u ht
      (by rw [hABl, hAl, hBl]; exact hu)]
    have hu2 : u = a * B.length + b := by rw [hBl]; exact huab
    rw [hu2, getAt_tensorM A B a b (by rw [hAl]; exact ha)
      (by rw [hBl]; exact hb)]
    have ht2 : t
        = i * (ground.getAt ([] : List BPair) B b).length + k := by
      rw [hrowB]; exact htik
    rw [ht2, getAt_tensorV (ground.getAt [] A a)
      (ground.getAt [] B b) i k (by rw [hrowA]; exact hi)
      (by rw [hrowB]; exact hk)]
  have hR : ground.getAt BPair.unit
      (ground.getAt [] (tensorM (transposeM A) (transposeM B)) t) u
      = (ground.getAt BPair.unit (ground.getAt [] A a) i
        * ground.getAt BPair.unit (ground.getAt [] B b) k).norm := by
    have ht2 : t = i * (transposeM B).length + k := by
      rw [hBtl]; exact htik
    rw [ht2, getAt_tensorM (transposeM A) (transposeM B) i k
      (by rw [hAtl]; exact hi) (by rw [hBtl]; exact hk)]
    have hcolA :
        (ground.getAt ([] : List BPair) (transposeM A) i).length = p :=
      rowsLen_getAt (transposeM A) i hAtr (by rw [hAtl]; exact hi)
    have hcolB :
        (ground.getAt ([] : List BPair) (transposeM B) k).length = r :=
      rowsLen_getAt (transposeM B) k hBtr (by rw [hBtl]; exact hk)
    have hu2 : u = a
        * (ground.getAt ([] : List BPair) (transposeM B) k).length + b := by
      rw [hcolB]; exact huab
    rw [hu2, getAt_tensorV (ground.getAt [] (transposeM A) i)
      (ground.getAt [] (transposeM B) k) a b (by rw [hcolA]; exact ha)
      (by rw [hcolB]; exact hb),
      getAt_transposeM BPair.unit A hA i a hi (by rw [hAl]; exact ha),
      getAt_transposeM BPair.unit B hB k b hk (by rw [hBl]; exact hb)]
  rw [hL, hR]

/-- The key-list exchange distributes over the tensor: at stated
shapes the exchanged tensor is the exchanges' own tensor. -/
theorem transposeM_tensorM (p q r s : Nat) (A B : Mat)
    (hAl : A.length = p) (hA : rowsLen q A) (hBl : B.length = r)
    (hB : rowsLen s B) :
    transposeM (tensorM A B)
      = tensorM (transposeM A) (transposeM B) := by
  cases A with
  | nil => rfl
  | cons ra A' =>
    cases B with
    | nil =>
      rw [tensorM_nil (ra :: A')]
      show ([] : Mat) = tensorM (transposeM (ra :: A')) []
      rw [tensorM_nil (transposeM (ra :: A'))]
    | cons rb B' =>
      exact transposeM_tensorM_pos p q r s (ra :: A') (rb :: B') hAl hA
        hBl hB (Nat.succ_pos A'.length) (Nat.succ_pos B'.length)

/-! ### The matrix product reads factorwise -/

private theorem tensorV_dotCol (ra rb c : List BPair) :
    ∀ Dt : Mat, rowsLen rb.length Dt →
    poly.oneValue
      ((Dt.map (fun d => tensorV c d)).map
        (fun cy => dotN (tensorV ra rb) cy))
      ((Dt.map (fun d => dotN rb d)).map
        (fun y => (dotN ra c * y).norm))
  | [], _ => trivial
  | d :: Dt, hD =>
    ⟨dotN_tensorV ra rb c d hD.1.symm,
     tensorV_dotCol ra rb c Dt hD.2⟩

private theorem tensorV_dotRow (ra rb : List BPair) :
    ∀ Ct Dt : Mat, rowsLen rb.length Dt →
    poly.oneValue
      ((tensorM Ct Dt).map (fun cy => dotN (tensorV ra rb) cy))
      (tensorV (Ct.map (fun c => dotN ra c))
        (Dt.map (fun d => dotN rb d)))
  | [], _, _ => trivial
  | c :: Ct, Dt, hD => by
    show poly.oneValue
        ((Dt.map (fun d => tensorV c d) ++ tensorM Ct Dt).map
          (fun cy => dotN (tensorV ra rb) cy))
        ((Dt.map (fun d => dotN rb d)).map
            (fun y => (dotN ra c * y).norm)
          ++ tensorV (Ct.map (fun c => dotN ra c))
            (Dt.map (fun d => dotN rb d)))
    rw [ground.map_append]
    exact poly.oneValue_append _ _ _ _
      (by rw [ground.length_map, ground.length_map, ground.length_map,
        ground.length_map])
      (tensorV_dotCol ra rb c Dt hD)
      (tensorV_dotRow ra rb Ct Dt hD)

private theorem matMul_tensorRow (ra : List BPair) (Ct Dt : Mat)
    (r : Nat) (hDt : rowsLen r Dt) :
    ∀ B : Mat, rowsLen r B →
    matOneValue
      ((B.map (fun rb => tensorV ra rb)).map
        (fun rr => (tensorM Ct Dt).map (fun cy => dotN rr cy)))
      ((B.map (fun rb => Dt.map (fun d => dotN rb d))).map
        (fun rb' => tensorV (Ct.map (fun c => dotN ra c)) rb'))
  | [], _ => trivial
  | rb :: B, hB =>
    ⟨tensorV_dotRow ra rb Ct Dt (by rw [hB.1]; exact hDt),
     matMul_tensorRow ra Ct Dt r hDt B hB.2⟩

private theorem matMul_tensorGo (Ct Dt : Mat) (r : Nat)
    (hDt : rowsLen r Dt) (B : Mat) (hB : rowsLen r B) :
    ∀ A : Mat,
    matOneValue
      ((tensorM A B).map
        (fun rr => (tensorM Ct Dt).map (fun cy => dotN rr cy)))
      (tensorM (A.map (fun ra => Ct.map (fun c => dotN ra c)))
        (B.map (fun rb => Dt.map (fun d => dotN rb d))))
  | [] => trivial
  | ra :: A => by
    show matOneValue
        ((B.map (fun rb => tensorV ra rb) ++ tensorM A B).map
          (fun rr => (tensorM Ct Dt).map (fun cy => dotN rr cy)))
        ((B.map (fun rb => Dt.map (fun d => dotN rb d))).map
            (fun rb' => tensorV (Ct.map (fun c => dotN ra c)) rb')
          ++ tensorM (A.map (fun ra => Ct.map (fun c => dotN ra c)))
            (B.map (fun rb => Dt.map (fun d => dotN rb d))))
    rw [ground.map_append]
    exact matOne_app _ _ _ _
      (by rw [ground.length_map, ground.length_map, ground.length_map,
        ground.length_map])
      (matMul_tensorRow ra Ct Dt r hDt B hB)
      (matMul_tensorGo Ct Dt r hDt B hB A)

/-- The matrix product reads factorwise: a product of two tensors
is the factors' products' tensor. -/
theorem matMul_tensorM (q r s : Nat) (A B C D : Mat)
    (hB : rowsLen r B) (hDl : D.length = r) (hC : rowsLen q C)
    (hD : rowsLen s D) :
    matOneValue (matMul (tensorM A B) (tensorM C D))
      (tensorM (matMul A C) (matMul B D)) := by
  have hDt : rowsLen r (transposeM D) := by
    have h := rowsLen_transposeM D; rw [hDl] at h; exact h
  have hT : transposeM (tensorM C D)
      = tensorM (transposeM C) (transposeM D) :=
    transposeM_tensorM C.length q D.length s C D rfl hC rfl hD
  show matOneValue
      ((tensorM A B).map (fun rr =>
        (transposeM (tensorM C D)).map (fun cy => dotN rr cy)))
      (tensorM (A.map (fun ra => (transposeM C).map (fun c => dotN ra c)))
        (B.map (fun rb => (transposeM D).map (fun d => dotN rb d))))
  rw [hT]
  exact matMul_tensorGo (transposeM C) (transposeM D) r hDt B hB A

/-! ### The identity -/

/-- The identity at the product order is the two identities' own
tensor. -/
theorem tensorM_idMat (m n : Nat) :
    tensorM (inertia.idMat m) (inertia.idMat n)
      = inertia.idMat (m * n) := by
  have hlL : (tensorM (inertia.idMat m) (inertia.idMat n)).length
      = m * n := by
    rw [tensorM_length, inertia.idMat_len, inertia.idMat_len]
  have hrL : rowsLen (m * n)
      (tensorM (inertia.idMat m) (inertia.idMat n)) :=
    rowsLen_tensorM m n (inertia.idMat m) (inertia.idMat n)
      (inertia.idMat_rows m) (inertia.idMat_rows n)
  refine ground.getAt_ext ([] : List BPair) _ _
    (by rw [hlL, inertia.idMat_len]) ?_
  intro t ht
  rw [hlL] at ht
  have hn0 : 0 < n := by
    cases n with
    | zero => rw [Nat.mul_zero] at ht; exact absurd ht (Nat.not_lt_zero t)
    | succ n0 => exact Nat.succ_pos n0
  refine ground.getAt_ext BPair.unit _ _ ?_ ?_
  · rw [rowsLen_getAt _ t hrL (by rw [hlL]; exact ht),
      rowsLen_getAt _ t (inertia.idMat_rows (m * n))
        (by rw [inertia.idMat_len]; exact ht)]
  intro u hu
  rw [rowsLen_getAt _ t hrL (by rw [hlL]; exact ht)] at hu
  obtain ⟨i, k, hk, htik⟩ := pairSplit n hn0 t
  obtain ⟨a, b, hb, huab⟩ := pairSplit n hn0 u
  have hi : i < m := pairIdxLt (by rw [← htik]; exact ht)
  have ha : a < m := pairIdxLt (by rw [← huab]; exact hu)
  have hL : ground.getAt BPair.unit
      (ground.getAt []
        (tensorM (inertia.idMat m) (inertia.idMat n)) t) u
      = ((if a = i then BPair.ofNat 1 else BPair.unit)
        * (if b = k then BPair.ofNat 1 else BPair.unit)).norm := by
    have ht2 : t = i * (inertia.idMat n).length + k := by
      rw [inertia.idMat_len]; exact htik
    rw [ht2, getAt_tensorM (inertia.idMat m) (inertia.idMat n) i k
      (by rw [inertia.idMat_len]; exact hi)
      (by rw [inertia.idMat_len]; exact hk)]
    have hrowM : (ground.getAt ([] : List BPair)
        (inertia.idMat m) i).length = m :=
      rowsLen_getAt (inertia.idMat m) i (inertia.idMat_rows m)
        (by rw [inertia.idMat_len]; exact hi)
    have hrowN : (ground.getAt ([] : List BPair)
        (inertia.idMat n) k).length = n :=
      rowsLen_getAt (inertia.idMat n) k (inertia.idMat_rows n)
        (by rw [inertia.idMat_len]; exact hk)
    have hu2 : u = a * (ground.getAt ([] : List BPair)
        (inertia.idMat n) k).length + b := by
      rw [hrowN]; exact huab
    rw [hu2, getAt_tensorV (ground.getAt [] (inertia.idMat m) i)
      (ground.getAt [] (inertia.idMat n) k) a b
      (by rw [hrowM]; exact ha) (by rw [hrowN]; exact hb),
      inertia.getAt_idMat m i a hi ha, inertia.getAt_idMat n k b hk hb]
  have hR : ground.getAt BPair.unit
      (ground.getAt [] (inertia.idMat (m * n)) t) u
      = if u = t then BPair.ofNat 1 else BPair.unit :=
    inertia.getAt_idMat (m * n) t u ht hu
  rw [hL, hR, htik, huab]
  by_cases hia : a = i
  · by_cases hkb : b = k
    · rw [if_pos hia, if_pos hkb,
        if_pos (show a * n + b = i * n + k by rw [hia, hkb])]
      decide +kernel
    · rw [if_pos hia, if_neg hkb,
        if_neg (show ¬ a * n + b = i * n + k from fun he =>
          hkb (pairInj i k a b hk hb he.symm).2.symm)]
      exact Eq.trans (BPair.norm_congr (BPair.mul_unit _)) (by decide +kernel)
  · rw [if_neg hia,
      if_neg (show ¬ a * n + b = i * n + k from fun he =>
        hia (pairInj i k a b hk hb he.symm).1.symm)]
    exact Eq.trans (BPair.norm_congr (BPair.unit_mul _)) (by decide +kernel)


/-! ### Tier F: the separated bottom adds

`lem:relfiber`(iii)'s clause.  A single-component head pair
positive semidefinite at the level `ℓ` carries its site datum
`S₁` through the tensor sum: each summand of
`H^{(ϱ)} = ϱℓ G^{⊗ϱ} + ∑_{a+b+1=ϱ} G^{⊗a} ⊗ S₁ ⊗ G^{⊗b}` is
positive semidefinite against the positive-definite tensor gram,
and on a bracket with top below `ϱℓ` the sector's pair clears.

The tier's two form theorems are the tensor's own positivity
reads at a split factor whose blocks all sit at order one, so the
congruence's image is a diagonal: `tensor_form_left` at
`G ⊗ X` and `tensor_form_right` at `X ⊗ G`.  Their common route
is `lem:inertia`'s own — the congruence carries the form back at
the determinant's square (`inertia.psd_all`'s route at the
tensored certificate `T ⊗ I`), the image's form is the diagonal's
fold over its keys, and each key's contribution is the entry
against the second factor's own form, on its upper side or of
equal members.  The two folds differ only in how the vector meets
the diagonal: at a left diagonal the vector's blocks are
contiguous, at a right one they are strided, and the strided
extraction enters as the chunk list the fold consumes.
-/

/-! ### The congruences the tier consumes -/

/-- A unit-tail first factor tensors to a unit tail. -/
private theorem tensorV_unitL : ∀ (ra rb : List BPair),
    poly.unitTail ra → poly.unitTail (tensorV ra rb)
  | [], _, _ => trivial
  | _ :: ra, rb, h =>
    unitTail_append (a := _) (b := _) (poly.scaleP_null h.1 rb)
      (tensorV_unitL ra rb h.2)

/-- A unit-tail second factor tensors to a unit tail. -/
private theorem tensorV_unitR : ∀ (ra rb : List BPair),
    poly.unitTail rb → poly.unitTail (tensorV ra rb)
  | [], _, _ => trivial
  | x :: ra, rb, h =>
    unitTail_append (a := _) (b := _) (poly.scaleP_unitTail x rb h)
      (tensorV_unitR ra rb h)

/-- The tensor's one-value read in its first factor. -/
private theorem tensorV_congrL : ∀ (ra ra' rb : List BPair),
    poly.oneValue ra ra' →
    poly.oneValue (tensorV ra rb) (tensorV ra' rb)
  | [], q, rb, h => tensorV_unitL q rb h
  | x :: p, [], rb, h =>
    poly.unitTail_oneValue (tensorV_unitL (x :: p) rb h) trivial
  | x :: p, y :: q, rb, h => by
    show poly.oneValue (rb.map (fun z => (x * z).norm) ++ tensorV p rb)
      (rb.map (fun z => (y * z).norm) ++ tensorV q rb)
    refine poly.oneValue_append _ _ _ _
      (by rw [ground.length_map, ground.length_map]) ?_
      (tensorV_congrL p q rb h.2)
    exact poly.oneValue_map _ _ rb (fun z _ =>
      BPair.oneValue_trans (BPair.norm_oneValue (x * z))
        (BPair.oneValue_trans
          (BPair.mul_congr h.1 (BPair.oneValue_refl z))
          (BPair.oneValue_symm (BPair.norm_oneValue (y * z)))))

/-- The tensor's one-value read in its second factor, at a shared
key count. -/
private theorem tensorV_congrR : ∀ (ra rb rb' : List BPair),
    rb.length = rb'.length → poly.oneValue rb rb' →
    poly.oneValue (tensorV ra rb) (tensorV ra rb')
  | [], _, _, _, _ => trivial
  | x :: ra, rb, rb', hl, h => by
    show poly.oneValue (rb.map (fun z => (x * z).norm) ++ tensorV ra rb)
      (rb'.map (fun z => (x * z).norm) ++ tensorV ra rb')
    refine poly.oneValue_append _ _ _ _
      (by rw [ground.length_map, ground.length_map, hl]) ?_
      (tensorV_congrR ra rb rb' hl h)
    exact poly.oneValue_scaleP x h

/-- The rows' tensor reads one value in its first factor. -/
private theorem tensorM_congrL : ∀ (A A' B : Mat),
    matOneValue A A' → matOneValue (tensorM A B) (tensorM A' B)
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | ra :: A, ra' :: A', B, h => by
    show matOneValue (B.map (fun rb => tensorV ra rb) ++ tensorM A B)
      (B.map (fun rb => tensorV ra' rb) ++ tensorM A' B)
    exact matOne_app _ _ _ _
      (by rw [ground.length_map, ground.length_map])
      (matOne_map _ _ (fun rb => tensorV_congrL ra ra' rb h.1) B)
      (tensorM_congrL A A' B h.2)

private theorem tensorM_rowsCongr (ra : List BPair) (w : Nat) :
    ∀ B B' : Mat, rowsLen w B → rowsLen w B' → matOneValue B B' →
      matOneValue (B.map (fun rb => tensorV ra rb))
        (B'.map (fun rb => tensorV ra rb))
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | rb :: B, rb' :: B', hB, hB', h =>
    ⟨tensorV_congrR ra rb rb' (by rw [hB.1, hB'.1]) h.1,
     tensorM_rowsCongr ra w B B' hB.2 hB'.2 h.2⟩

/-- The rows' tensor reads one value in its second factor, at a
shared width. -/
private theorem tensorM_congrR (w : Nat) (B B' : Mat)
    (hB : rowsLen w B) (hB' : rowsLen w B') (h : matOneValue B B') :
    ∀ A : Mat, matOneValue (tensorM A B) (tensorM A B')
  | [] => trivial
  | ra :: A => by
    show matOneValue (B.map (fun rb => tensorV ra rb) ++ tensorM A B)
      (B'.map (fun rb => tensorV ra rb) ++ tensorM A B')
    exact matOne_app _ _ _ _
      (by rw [ground.length_map, ground.length_map, matOne_length h])
      (tensorM_rowsCongr ra w B B' hB hB' h)
      (tensorM_congrR w B B' hB hB' h A)



/-! ### The relative translation and the tensor congruence -/

private theorem idMat_zero : inertia.idMat 0 = [] := by
  have h := inertia.idMat_len 0
  cases hm : inertia.idMat 0 with
  | nil => rfl
  | cons _ _ => rw [hm] at h; exact Nat.noConfusion h

/-- A first-slot factor commutes with a second-slot factor: at
stated square orders the two act on disjoint slots of the product
index, so the two products read one value — `lem:relfiber`(ii)'s
action instance at the position-free extension, the relative
translation the second slot's factor. -/
theorem comm_shift (nX L : Nat) (X P : Mat) (hX : sqAt X nX)
    (hP : sqAt P L) :
    matOneValue
      (matMul (tensorM X (inertia.idMat L)) (tensorM (inertia.idMat nX) P))
      (matMul (tensorM (inertia.idMat nX) P)
        (tensorM X (inertia.idMat L))) := by
  have hXl : X.length = nX := sqAt_len hX
  have hXr : rowsLen nX X := rowsLen_of_sqAt hX
  have hPl : P.length = L := sqAt_len hP
  have hPr : rowsLen L P := rowsLen_of_sqAt hP
  cases nX with
  | zero =>
    rw [ground.nil_of_length_zero _ hXl, idMat_zero]
    exact trivial
  | succ n0 =>
    cases L with
    | zero =>
      rw [idMat_zero, ground.nil_of_length_zero _ hPl, tensorM_nil X,
        tensorM_nil (inertia.idMat (n0 + 1))]
      exact trivial
    | succ l0 =>
      have hnX : 0 < n0 + 1 := Nat.succ_pos n0
      have hL : 0 < l0 + 1 := Nat.succ_pos l0
      have hP0 : 0 < P.length := by rw [hPl]; exact hL
      have hPt : (transposeM P).length = l0 + 1 :=
        length_transposeM P hPr hP0
      have hIP : rowsLen (l0 + 1) (matMul (inertia.idMat (l0 + 1)) P) :=
        rowsLen_cast hPt (rowsLen_matMul (inertia.idMat (l0 + 1)) P)
      have hPI : rowsLen (l0 + 1) (matMul P (inertia.idMat (l0 + 1))) :=
        rowsLen_cast
          (by rw [inertia.transposeM_idMat (l0 + 1), inertia.idMat_len])
          (rowsLen_matMul P (inertia.idMat (l0 + 1)))
      have hLeft : matOneValue
          (matMul (tensorM X (inertia.idMat (l0 + 1)))
            (tensorM (inertia.idMat (n0 + 1)) P))
          (tensorM X P) :=
        matOne_trans
          (matMul_tensorM (n0 + 1) (l0 + 1) (l0 + 1) X
            (inertia.idMat (l0 + 1)) (inertia.idMat (n0 + 1)) P
            (inertia.idMat_rows (l0 + 1)) hPl
            (inertia.idMat_rows (n0 + 1)) hPr)
          (matOne_trans
            (tensorM_congrL _ _ _
              (inertia.matMul_idR (n0 + 1) X hXr hXl hnX hnX))
            (tensorM_congrR (l0 + 1) _ _ hIP hPr
              (inertia.idMat_matMul (l0 + 1) P hPr hPl hL) X))
      have hRight : matOneValue
          (matMul (tensorM (inertia.idMat (n0 + 1)) P)
            (tensorM X (inertia.idMat (l0 + 1))))
          (tensorM X P) :=
        matOne_trans
          (matMul_tensorM (n0 + 1) (l0 + 1) (l0 + 1)
            (inertia.idMat (n0 + 1)) P X (inertia.idMat (l0 + 1))
            hPr (inertia.idMat_len (l0 + 1)) hXr
            (inertia.idMat_rows (l0 + 1)))
          (matOne_trans
            (tensorM_congrL _ _ _
              (inertia.idMat_matMul (n0 + 1) X hXr hXl hnX))
            (tensorM_congrR (l0 + 1) _ _ hPI hPr
              (inertia.matMul_idR (l0 + 1) P hPr hPl hL hL) X))
      exact matOne_trans hLeft (matOne_symm hRight)

/-- The tensor congruence reads factorwise: a congruence at a
tensored carrier is the two factors' own congruences tensored
(`lem:relfiber`(iii)'s "a product of two tensors reads
factorwise"). -/
theorem congr_tensorM (nX nY a b : Nat) (X Y A B : Mat)
    (hX : sqAt X nX) (hY : sqAt Y nY)
    (hAl : A.length = nX) (hA : rowsLen a A)
    (hBl : B.length = nY) (hB : rowsLen b B) :
    matOneValue
      (matMul (transposeM (tensorM A B))
        (matMul (tensorM X Y) (tensorM A B)))
      (tensorM (matMul (transposeM A) (matMul X A))
        (matMul (transposeM B) (matMul Y B))) := by
  have hXl : X.length = nX := sqAt_len hX
  have hYl : Y.length = nY := sqAt_len hY
  have hYr : rowsLen nY Y := rowsLen_of_sqAt hY
  cases nX with
  | zero =>
    rw [ground.nil_of_length_zero _ hAl, ground.nil_of_length_zero _ hXl]
    exact trivial
  | succ n0 =>
    cases nY with
    | zero =>
      rw [ground.nil_of_length_zero _ hBl, ground.nil_of_length_zero _ hYl, tensorM_nil A]
      show matOneValue ([] : Mat)
        (tensorM (matMul (transposeM A) (matMul X A)) ([] : Mat))
      rw [tensorM_nil (matMul (transposeM A) (matMul X A))]
      exact trivial
    | succ m0 =>
      have hA0 : 0 < A.length := by rw [hAl]; exact Nat.succ_pos n0
      have hB0 : 0 < B.length := by rw [hBl]; exact Nat.succ_pos m0
      have hAt : (transposeM A).length = a := length_transposeM A hA hA0
      have hBt : (transposeM B).length = b := length_transposeM B hB hB0
      have hT : transposeM (tensorM A B)
          = tensorM (transposeM A) (transposeM B) :=
        transposeM_tensorM (n0 + 1) a (m0 + 1) b A B hAl hA hBl hB
      have hXA : rowsLen a (matMul X A) :=
        rowsLen_cast hAt (rowsLen_matMul X A)
      have hYB : rowsLen b (matMul Y B) :=
        rowsLen_cast hBt (rowsLen_matMul Y B)
      have hTl : (transposeM (tensorM A B)).length = a * b := by
        rw [hT, tensorM_length, hAt, hBt]
      have hMid : matOneValue (matMul (tensorM X Y) (tensorM A B))
          (tensorM (matMul X A) (matMul Y B)) :=
        matMul_tensorM a (m0 + 1) b X Y A B hYr hBl hA hB
      have hMr : rowsLen (a * b) (matMul (tensorM X Y) (tensorM A B)) :=
        rowsLen_cast hTl (rowsLen_matMul (tensorM X Y) (tensorM A B))
      have hNr : rowsLen (a * b) (tensorM (matMul X A) (matMul Y B)) :=
        rowsLen_tensorM a b _ _ hXA hYB
      have hLen : (matMul (tensorM X Y) (tensorM A B)).length
          = (tensorM (matMul X A) (matMul Y B)).length := by
        rw [length_matMul, tensorM_length, tensorM_length, length_matMul,
          length_matMul, hXl, hYl]
      rw [hT]
      exact matOne_trans
        (elim.matMul_congrR_of (tensorM (transposeM A) (transposeM B))
          _ _ (elim.transposeM_congrM (a * b) _ _ hMr hNr hLen hMid))
        (matMul_tensorM a (m0 + 1) b (transposeM A) (transposeM B)
          (matMul X A) (matMul Y B)
          (rowsLen_cast hBl (rowsLen_transposeM B))
          ((length_matMul Y B).trans hYl) hXA hYB)


/-! ### The null rows and the split's contiguous fold -/

private def unitRows : Mat → Prop
  | [] => True
  | r :: t => poly.unitTail r ∧ unitRows t

private theorem unitRows_app : ∀ (A B : Mat),
    unitRows A → unitRows B → unitRows (A ++ B)
  | [], _, _, hb => hb
  | _ :: t, B, ha, hb => ⟨ha.1, unitRows_app t B ha.2 hb⟩

private theorem unitRows_map {α : Type} (f : α → List BPair)
    (h : ∀ x : α, poly.unitTail (f x)) :
    ∀ l : List α, unitRows (l.map f)
  | [] => trivial
  | x :: t => ⟨h x, unitRows_map f h t⟩

private theorem unitRows_tensorL : ∀ (A B : Mat),
    unitRows A → unitRows (tensorM A B)
  | [], _, _ => trivial
  | ra :: A, B, h =>
    unitRows_app _ _
      (unitRows_map _ (fun rb => tensorV_unitL ra rb h.1) B)
      (unitRows_tensorL A B h.2)

private theorem unitRows_mapR (ra : List BPair) : ∀ B : Mat,
    unitRows B → unitRows (B.map (fun rb => tensorV ra rb))
  | [], _ => trivial
  | rb :: B, h => ⟨tensorV_unitR ra rb h.1, unitRows_mapR ra B h.2⟩

private theorem unitRows_tensorR : ∀ (A B : Mat),
    unitRows B → unitRows (tensorM A B)
  | [], _, _ => trivial
  | ra :: A, B, h =>
    unitRows_app _ _ (unitRows_mapR ra B h) (unitRows_tensorR A B h)

private theorem matVec_unitRowsM : ∀ (M : Mat), unitRows M →
    ∀ c : List BPair, poly.unitTail (matVec M c)
  | [], _, _ => trivial
  | r :: t, h, c => ⟨elim.dotN_nullL r c h.1, matVec_unitRowsM t h.2 c⟩

private theorem quadForm_unitRows (M : Mat) (h : unitRows M)
    (c : List BPair) : (inertia.quadForm M c).oneValue BPair.unit :=
  elim.dotN_nullR c (matVec M c) (matVec_unitRowsM M h c)

private theorem unitRows_blockNil (k : Nat) :
    unitRows (inertia.blockMat [] k) :=
  unitRows_map _ (fun _ => poly.unitTail_replicate k) (List.range k)

/-- The diagonal's leading entry against a contiguous split: the
entry weights the second factor's own fold, the padded slot
dropping at the sum's unit. -/
private theorem tensorRow_head (a : BPair) (m : Nat)
    (rb c1 c2 : List BPair) (hrb : rb.length = c1.length) :
    (dotN (tensorV (a :: List.replicate m BPair.unit) rb)
        (c1 ++ c2)).oneValue (a * dotN rb c1) := by
  show (dotN (rb.map (fun y => (a * y).norm)
      ++ tensorV (List.replicate m BPair.unit) rb) (c1 ++ c2)).oneValue
    (a * dotN rb c1)
  refine BPair.oneValue_trans
    (inertia.dotN_app _ _ _ _ (by rw [ground.length_map, hrb])) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (inertia.dotN_scaleRow a rb c1)
      (elim.dotN_nullL _ c2
        (tensorV_unitL _ rb (poly.unitTail_replicate m)))) ?_
  exact BPair.add_unit _

/-- A padded diagonal row drops its leading slot: the fold reads
the trailing block alone. -/
private theorem tensorRow_pad (r rb c1 c2 : List BPair)
    (hrb : rb.length = c1.length) :
    (dotN (tensorV (BPair.unit :: r) rb) (c1 ++ c2)).oneValue
      (dotN (tensorV r rb) c2) := by
  show (dotN (rb.map (fun y => (BPair.unit * y).norm) ++ tensorV r rb)
      (c1 ++ c2)).oneValue (dotN (tensorV r rb) c2)
  refine BPair.oneValue_trans
    (inertia.dotN_app _ _ _ _ (by rw [ground.length_map, hrb])) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (elim.dotN_nullL _ c1
        (poly.scaleP_null (BPair.oneValue_refl BPair.unit) rb))
      (BPair.oneValue_refl _)) ?_
  exact BPair.unit_add _

private theorem matVec_headBlock (a : BPair) (m : Nat)
    (c1 c2 : List BPair) : ∀ X : Mat, rowsLen c1.length X →
    poly.oneValue
      (matVec (X.map (fun rb =>
        tensorV (a :: List.replicate m BPair.unit) rb)) (c1 ++ c2))
      (vecScale a (matVec X c1))
  | [], _ => trivial
  | rb :: X, h =>
    ⟨tensorRow_head a m rb c1 c2 h.1,
     matVec_headBlock a m c1 c2 X h.2⟩

private theorem matVec_padRows (r c1 c2 : List BPair) :
    ∀ X : Mat, rowsLen c1.length X →
    poly.oneValue
      (matVec (X.map (fun rb => tensorV (BPair.unit :: r) rb)) (c1 ++ c2))
      (matVec (X.map (fun rb => tensorV r rb)) c2)
  | [], _ => trivial
  | rb :: X, h =>
    ⟨tensorRow_pad r rb c1 c2 h.1, matVec_padRows r c1 c2 X h.2⟩

private theorem matVec_padBlock (c1 c2 : List BPair) (X : Mat)
    (hX : rowsLen c1.length X) : ∀ D : Mat,
    poly.oneValue
      (matVec (tensorM (D.map (fun r => BPair.unit :: r)) X) (c1 ++ c2))
      (matVec (tensorM D X) c2)
  | [] => trivial
  | r :: D => by
    show poly.oneValue
      (matVec (X.map (fun rb => tensorV (BPair.unit :: r) rb)
        ++ tensorM (D.map (fun s => BPair.unit :: s)) X) (c1 ++ c2))
      (matVec (X.map (fun rb => tensorV r rb) ++ tensorM D X) c2)
    rw [matVec_append, matVec_append]
    exact poly.oneValue_append _ _ _ _
      (by rw [matVec_length, matVec_length, ground.length_map,
        ground.length_map])
      (matVec_padRows r c1 c2 X hX) (matVec_padBlock c1 c2 X hX D)

/-- The split's diagonal against a left tensor slot: at blocks all
of order one the image is a diagonal, and the form is the fold over
its keys of the entry against the second factor's own form at the
contiguous block of the vector — each key at or above the sum's
unit, so the fold is (`lem:inertia`'s block reads). -/
private theorem tensorL_fold (X : Mat) (N : Nat) (hXl : X.length = N)
    (hXr : rowsLen N X)
    (hXpos : ∀ v : List BPair, v.length = N →
      BPair.unit ≤ inertia.quadForm X v) :
    ∀ (bs : List inertia.SBlock) (k : Nat),
      (bs.all (fun b => b.order == 1)) = true →
      (bs.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true →
      bs.foldl (fun mm b => mm + b.rev) 0 = 0 →
      ∀ c : List BPair, c.length = inertia.widthOf bs k * N →
        BPair.unit ≤ inertia.quadForm
          (tensorM (inertia.blockMat bs k) X) c
  | [], k, _, _, _, c, _ =>
    ground.leB_congr_right
      (BPair.oneValue_symm (quadForm_unitRows _
        (unitRows_tensorL _ X (unitRows_blockNil k)) c))
      (ground.leB_refl BPair.unit)
  | inertia.SBlock.two _ _ _ :: _, _, hord, _, _, _, _ =>
    Bool.noConfusion ((ground.andSplitB hord).1)
  | inertia.SBlock.one a :: bs, k, hord, hall, hrev, c, hc => by
    have ha : BPair.unit < a :=
      inertia.oneUp (ground.notOfBang ((ground.andSplitB hall).1))
        ((ground.addZeroN (inertia.revSplit.symm.trans hrev)).1)
    have hw : inertia.widthOf (inertia.SBlock.one a :: bs) k
        = inertia.widthOf bs k + 1 := inertia.widthOf_shift bs k 1
    have hc' : c.length = inertia.widthOf bs k * N + N := by
      rw [hc, hw, ground.mulAddR]
      exact congrArg (fun z => inertia.widthOf bs k * N + z)
        (Nat.one_mul N)
    obtain ⟨c1, c2, hce, hc1⟩ := ground.listSplit c N
      (by rw [hc']; exact Nat.le_add_left N _)
    have hlen : c1.length + c2.length = inertia.widthOf bs k * N + N := by
      rw [← ground.length_append, ← hce]; exact hc'
    have hc2 : c2.length = inertia.widthOf bs k * N :=
      ground.addCancelL c1.length (by
        rw [hlen, hc1, Nat.add_comm (inertia.widthOf bs k * N) N])
    have hXc : rowsLen c1.length X := by rw [hc1]; exact hXr
    have hstep : (inertia.quadForm
        (tensorM (inertia.blockMat (inertia.SBlock.one a :: bs) k) X)
        (c1 ++ c2)).oneValue
        (a * inertia.quadForm X c1
          + inertia.quadForm (tensorM (inertia.blockMat bs k) X) c2) := by
      show (dotN (c1 ++ c2) (matVec
          (X.map (fun rb => tensorV (a ::
              List.replicate (inertia.widthOf bs k) BPair.unit) rb)
            ++ tensorM ((inertia.blockMat bs k).map
              (fun r => BPair.unit :: r)) X) (c1 ++ c2))).oneValue
        (a * inertia.quadForm X c1
          + inertia.quadForm (tensorM (inertia.blockMat bs k) X) c2)
      rw [matVec_append]
      refine BPair.oneValue_trans
        (inertia.dotN_app _ _ _ _
          (by rw [hc1, matVec_length, ground.length_map, hXl])) ?_
      refine BPair.add_congr ?_ ?_
      · refine BPair.oneValue_trans
          (dotN_congrR c1 _ _ (matVec_headBlock a _ c1 c2 X hXc)) ?_
        exact elim.dotN_scaleV a c1 (matVec X c1)
      · exact dotN_congrR c2 _ _
          (matVec_padBlock c1 c2 X hXc (inertia.blockMat bs k))
    rw [hce]
    refine ground.leB_congr_right (BPair.oneValue_symm hstep) ?_
    refine ground.unitLeAdd
      (ground.unitLeMul (ground.leB_of_lt ha) (hXpos c1 hc1)) ?_
    exact tensorL_fold X N hXl hXr hXpos bs k
      ((ground.andSplitB hord).2) ((ground.andSplitB hall).2)
      ((ground.addZeroN (inertia.revSplit.symm.trans hrev)).2) c2 hc2


/-! ### The tensor's form at a split first factor -/

/-- A single-component gram positive semidefinite at a split whose
blocks all sit at order one tensors on the left without moving the
second factor's form off its side: the congruence `T ⊗ I` carries
the form back at the determinant's square, the image is the
diagonal against the second factor, and the diagonal's fold reads
each key's entry against the second factor's own form
(`lem:relfiber`(iii)'s summand clause). -/
theorem tensor_form_left {n : Nat} (G : Mat) (sp : inertia.Split n)
    (hread : inertia.splitRead G sp) (hpsd : inertia.psdAt sp)
    (hord : (sp.blocks.all (fun b => b.order == 1)) = true)
    (X : Mat) (N : Nat) (hX : sqAt X N)
    (hXpos : ∀ v : List BPair, v.length = N →
      ¬ (inertia.quadForm X v < BPair.unit))
    (u : List BPair) (hu : u.length = n * N) :
    ¬ (inertia.quadForm (tensorM G X) u < BPair.unit) := by
  obtain ⟨hsq, ⟨hdetT, hprod, _⟩, hcong, hns⟩ := hread
  cases Nat.eq_zero_or_pos n with
  | inl h0 =>
    rw [ground.nil_of_length_zero _ (show u.length = 0 by rw [hu, h0, Nat.zero_mul])]
    show ¬ (BPair.unit < BPair.unit)
    exact ground.leB_not_lt (ground.leB_refl BPair.unit)
  | inr hn =>
    cases Nat.eq_zero_or_pos N with
    | inl h0 =>
      rw [ground.nil_of_length_zero _ (show u.length = 0 by rw [hu, h0, Nat.mul_zero])]
      show ¬ (BPair.unit < BPair.unit)
      exact ground.leB_not_lt (ground.leB_refl BPair.unit)
    | inr hN =>
      have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
      have hTwrows : rowsLen n sp.Tw.val := rowsLen_of_sqAt sp.Tw.shape
      have hTlen : sp.T.val.length = n := sp.T.rows
      have hTwlen : sp.Tw.val.length = n := sp.Tw.rows
      have hGrows : rowsLen n G := rowsLen_of_sqAt hsq
      have hGlen : G.length = n := sqAt_len hsq
      have hXrows : rowsLen N X := rowsLen_of_sqAt hX
      have hXlen : X.length = N := sqAt_len hX
      have hidr : rowsLen N (inertia.idMat N) := inertia.idMat_rows N
      have hidl : (inertia.idMat N).length = N := inertia.idMat_len N
      have hnN : 0 < n * N := Nat.mul_pos hn hN
      have hPl : (tensorM sp.T.val (inertia.idMat N)).length = n * N := by
        rw [tensorM_length, hTlen, hidl]
      have hPr : rowsLen (n * N) (tensorM sp.T.val (inertia.idMat N)) :=
        rowsLen_tensorM n N _ _ hTrows hidr
      have hPwl : (tensorM sp.Tw.val (inertia.idMat N)).length = n * N := by
        rw [tensorM_length, hTwlen, hidl]
      have hPwr : rowsLen (n * N) (tensorM sp.Tw.val (inertia.idMat N)) :=
        rowsLen_tensorM n N _ _ hTwrows hidr
      have hSl : (tensorM G X).length = n * N := by
        rw [tensorM_length, hGlen, hXlen]
      have hSr : rowsLen (n * N) (tensorM G X) :=
        rowsLen_tensorM n N G X hGrows hXrows
      have hSsq : sqAt (tensorM G X) (n * N) := sqAt_of hSl hSr
      have hIt : (transposeM (inertia.idMat N)).length = N := by
        rw [inertia.transposeM_idMat N, hidl]
      have hIIr : rowsLen N (matMul (inertia.idMat N) (inertia.idMat N)) :=
        rowsLen_cast hIt (rowsLen_matMul _ _)
      have hcl : (matVec (tensorM sp.Tw.val (inertia.idMat N)) u).length
          = n * N := by rw [matVec_length]; exact hPwl
      have hMM : matOneValue
          (matMul (tensorM sp.T.val (inertia.idMat N))
            (tensorM sp.Tw.val (inertia.idMat N)))
          (inertia.matScaleB (minor sp.T.val)
            (inertia.idMat (n * N))) := by
        refine matOne_trans (matMul_tensorM n N N sp.T.val
          (inertia.idMat N) sp.Tw.val (inertia.idMat N) hidr hidl
          hTwrows hidr) ?_
        refine matOne_trans (tensorM_congrL _ _ _ hprod) ?_
        refine matOne_trans (tensorM_congrR N _ _ hIIr hidr
          (inertia.idMat_matMul N (inertia.idMat N) hidr hidl hN)
          (inertia.matScaleB (minor sp.T.val) (inertia.idMat n))) ?_
        rw [tensorM_scaleL, tensorM_idMat]
        exact matOne_refl _
      have hA : poly.oneValue
          (matVec (tensorM sp.T.val (inertia.idMat N))
            (matVec (tensorM sp.Tw.val (inertia.idMat N)) u))
          (vecScale (minor sp.T.val) u) := by
        refine poly.oneValue_trans
          (matVec_comp _ _ u (n * N) hPwr hu
            (by rw [hPwl]; exact hPr)) ?_
        refine poly.oneValue_trans (matVec_matOne _ _ u hMM) ?_
        exact inertia.scaleId_act (minor sp.T.val) (n * N) u hu
      have hXIr : rowsLen N (matMul X (inertia.idMat N)) :=
        rowsLen_cast hIt (rowsLen_matMul X (inertia.idMat N))
      have hXIl : (matMul X (inertia.idMat N)).length = N := by
        rw [length_matMul, hXlen]
      have hXIt : (transposeM (matMul X (inertia.idMat N))).length = N :=
        length_transposeM _ hXIr (by rw [hXIl]; exact hN)
      have hXI : matOneValue
          (matMul (transposeM (inertia.idMat N))
            (matMul X (inertia.idMat N))) X := by
        rw [inertia.transposeM_idMat N]
        refine matOne_trans (elim.matMul_congrR_of (inertia.idMat N) _ _
          (elim.transposeM_congrM N _ _ hXIr hXrows (by rw [hXIl, hXlen])
            (inertia.matMul_idR N X hXrows hXlen hN hN))) ?_
        exact inertia.idMat_matMul N X hXrows hXlen hN
      have hR2 : matOneValue
          (matMul (transposeM (tensorM sp.T.val (inertia.idMat N)))
            (matMul (tensorM G X)
              (tensorM sp.T.val (inertia.idMat N))))
          (tensorM (inertia.blockMat sp.blocks sp.kern) X) := by
        refine matOne_trans (congr_tensorM n N n N G X sp.T.val
          (inertia.idMat N) hsq hX hTlen hTrows hidl hidr) ?_
        refine matOne_trans (tensorM_congrL _ _ _ hcong) ?_
        exact tensorM_congrR N _ _
          (rowsLen_cast hXIt (rowsLen_matMul (transposeM (inertia.idMat N))
            (matMul X (inertia.idMat N)))) hXrows hXI
          (inertia.blockMat sp.blocks sp.kern)
      have hwidth : inertia.widthOf sp.blocks sp.kern = n :=
        Nat.eq_of_beq_eq_true sp.width
      have hBlock : BPair.unit ≤ inertia.quadForm
          (tensorM (inertia.blockMat sp.blocks sp.kern) X)
          (matVec (tensorM sp.Tw.val (inertia.idMat N)) u) :=
        tensorL_fold X N hXlen hXrows
          (fun v hv => ground.leB_of_not_lt (hXpos v hv))
          sp.blocks sp.kern hord hns hpsd _
          (by rw [hcl, hwidth])
      have hUp : BPair.unit ≤ inertia.quadForm (tensorM G X)
          (matVec (tensorM sp.T.val (inertia.idMat N))
            (matVec (tensorM sp.Tw.val (inertia.idMat N)) u)) := by
        refine ground.leB_congr_right (BPair.oneValue_symm ?_) hBlock
        refine BPair.oneValue_trans
          (inertia.congQuad (tensorM G X)
            (tensorM sp.T.val (inertia.idMat N)) (n * N) (n * N) hSsq
            hPr hPl _ hcl) ?_
        exact inertia.quadMatOne _ _ _ hR2
      have hScale : (inertia.quadForm (tensorM G X)
          (matVec (tensorM sp.T.val (inertia.idMat N))
            (matVec (tensorM sp.Tw.val (inertia.idMat N)) u))).oneValue
          (minor sp.T.val * minor sp.T.val
            * inertia.quadForm (tensorM G X) u) := by
        refine BPair.oneValue_trans (dotN_read _ _) ?_
        refine BPair.oneValue_trans (dotP_oneValue_left _ _ _ hA) ?_
        refine BPair.oneValue_trans
          (dotP_oneValue_right _ _ _ (matVec_congr (tensorM G X) _ _ hA)) ?_
        refine BPair.oneValue_trans
          (dotP_oneValue_right _ _ _
            (matVec_vecScale_free (tensorM G X) (minor sp.T.val) u)) ?_
        refine BPair.oneValue_trans
          (dotP_vecScale_right (vecScale (minor sp.T.val) u)
            (matVec (tensorM G X) u) (minor sp.T.val)) ?_
        have hinner : (dotP (vecScale (minor sp.T.val) u)
            (matVec (tensorM G X) u)).oneValue
            (minor sp.T.val * inertia.quadForm (tensorM G X) u) := by
          rw [dotP_comm (vecScale (minor sp.T.val) u)
            (matVec (tensorM G X) u)]
          refine BPair.oneValue_trans
            (dotP_vecScale_right (matVec (tensorM G X) u) u
              (minor sp.T.val)) ?_
          refine BPair.mul_congr (BPair.oneValue_refl _) ?_
          rw [dotP_comm (matVec (tensorM G X) u) u]
          exact BPair.oneValue_symm (dotN_read u (matVec (tensorM G X) u))
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (minor sp.T.val))
            hinner) ?_
        exact BPair.oneValue_of_eq
          (BPair.mul_assoc (minor sp.T.val) (minor sp.T.val)
            (inertia.quadForm (tensorM G X) u)).symm
      exact ground.leB_not_lt
        (inertia.scaleRefl (ground.sq_pos hdetT)
          (ground.leB_congr_right hScale hUp))


/-! ### The strided extraction and the split's fold at a right
factor -/

/-- The chunk's leading entry, the strided slice's own key. -/
private def hdU : List BPair → BPair
  | [] => BPair.unit
  | x :: _ => x

private theorem rowsLen_tail (m : Nat) : ∀ cs : List (List BPair),
    rowsLen (m + 1) cs → rowsLen m (cs.map List.tail)
  | [], _ => trivial
  | ch :: cs, h => by
    refine ⟨?_, rowsLen_tail m cs h.2⟩
    cases ch with
    | nil => exact Nat.noConfusion h.1
    | cons _ t => exact Nat.succ.inj h.1

private theorem chunkEx : ∀ (N M : Nat) (c : List BPair),
    c.length = N * M →
    ∃ cs : List (List BPair),
      cs.length = N ∧ rowsLen M cs ∧ elim.flatCat cs = c
  | 0, _, c, hc =>
    ⟨[], rfl, trivial,
      (ground.nil_of_length_zero _ (by rw [hc, Nat.zero_mul])).symm⟩
  | N + 1, M, c, hc => by
    obtain ⟨c1, c2, he, hl⟩ := ground.listSplit c M
      (by rw [hc, Nat.succ_mul]; exact Nat.le_add_left M (N * M))
    have hsum : c1.length + c2.length = N * M + M := by
      rw [← ground.length_append, ← he, hc, Nat.succ_mul]
    have hc2 : c2.length = N * M :=
      ground.addCancelL c1.length (by
        rw [hsum, hl, Nat.add_comm (N * M) M])
    obtain ⟨cs, hcsl, hcsr, hcsf⟩ := chunkEx N M c2 hc2
    refine ⟨c1 :: cs, congrArg (fun z => z + 1) hcsl, ⟨hl, hcsr⟩, ?_⟩
    rw [elim.flatCat_cons, hcsf, he]

/-- The diagonal's leading entry at a strided vector: the entry
weights the first factor's fold against the strided slice. -/
private theorem tensorRowR_head (a : BPair) (m : Nat) :
    ∀ (rx : List BPair) (cs : List (List BPair)),
      rx.length = cs.length → rowsLen (m + 1) cs →
      (dotN (tensorV rx (a :: List.replicate m BPair.unit))
          (elim.flatCat cs)).oneValue (a * dotN rx (cs.map hdU))
  | [], [], _, _ => BPair.oneValue_symm (BPair.mul_unit a)
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | x :: rx, ch :: cs, hl, hcs => by
    cases ch with
    | nil => exact Nat.noConfusion hcs.1
    | cons h t =>
      show (dotN ((a :: List.replicate m BPair.unit).map
            (fun y => (x * y).norm)
          ++ tensorV rx (a :: List.replicate m BPair.unit))
          ((h :: t) ++ elim.flatCat cs)).oneValue
        (a * dotN (x :: rx) (h :: cs.map hdU))
      refine BPair.oneValue_trans
        (inertia.dotN_app _ _ _ _
          (by
            rw [ground.length_map]
            show (List.replicate m BPair.unit).length + 1 = (h :: t).length
            rw [ground.length_replicate]
            exact hcs.1.symm)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (inertia.dotN_scaleRow x
              (a :: List.replicate m BPair.unit) (h :: t))
            (BPair.mul_congr (BPair.oneValue_refl x)
              (BPair.oneValue_trans
                (inertia.dotN_app [a] (List.replicate m BPair.unit)
                  [h] t rfl)
                (BPair.oneValue_trans
                  (BPair.add_congr (inertia.dotN_single a h)
                    (elim.dotN_nullL _ t
                      (poly.unitTail_replicate m)))
                  (BPair.add_unit (a * h))))))
          (tensorRowR_head a m rx cs (Nat.succ.inj hl) hcs.2)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_of_eq (BPair.mul_left_comm x a h))
          (BPair.oneValue_refl _)) ?_
      rw [← BPair.left_distrib a (x * h) (dotN rx (cs.map hdU))]
      refine BPair.mul_congr (BPair.oneValue_refl a) ?_
      exact BPair.oneValue_symm
        (BPair.oneValue_trans (dotN_read (x :: rx) (h :: cs.map hdU))
          (BPair.add_congr (BPair.oneValue_refl (x * h))
            (BPair.oneValue_symm (dotN_read rx (cs.map hdU)))))

/-- A padded diagonal row at a strided vector: the fold reads the
trailing diagonal against the chunks' tails. -/
private theorem tensorRowR_pad (r : List BPair) :
    ∀ (rx : List BPair) (cs : List (List BPair)),
      rx.length = cs.length → rowsLen (r.length + 1) cs →
      (dotN (tensorV rx (BPair.unit :: r)) (elim.flatCat cs)).oneValue
        (dotN (tensorV rx r) (elim.flatCat (cs.map List.tail)))
  | [], [], _, _ => BPair.oneValue_refl _
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | x :: rx, ch :: cs, hl, hcs => by
    cases ch with
    | nil => exact Nat.noConfusion hcs.1
    | cons h t =>
      have ht : t.length = r.length := Nat.succ.inj hcs.1
      show (dotN ((BPair.unit :: r).map (fun y => (x * y).norm)
          ++ tensorV rx (BPair.unit :: r))
          ((h :: t) ++ elim.flatCat cs)).oneValue
        (dotN (r.map (fun y => (x * y).norm) ++ tensorV rx r)
          (t ++ elim.flatCat (cs.map List.tail)))
      refine BPair.oneValue_trans
        (inertia.dotN_app _ _ _ _
          (by rw [ground.length_map]; exact hcs.1.symm)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (inertia.dotN_app [(x * BPair.unit).norm]
              (r.map (fun y => (x * y).norm)) [h] t rfl)
            (BPair.oneValue_trans
              (BPair.add_congr
                (elim.dotN_nullL _ [h]
                  ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
                    (BPair.mul_unit x), trivial⟩)
                (BPair.oneValue_refl _))
              (BPair.unit_add _)))
          (tensorRowR_pad r rx cs (Nat.succ.inj hl) hcs.2)) ?_
      exact BPair.oneValue_symm
        (inertia.dotN_app _ _ _ _ (by rw [ground.length_map, ht]))

private theorem padRowsR (rx : List BPair) (cs0 : List (List BPair))
    (hl : rx.length = cs0.length) (m : Nat)
    (hcs0 : rowsLen (m + 1) cs0) : ∀ D : Mat, rowsLen m D →
    poly.oneValue
      (matVec ((D.map (fun r => BPair.unit :: r)).map
        (fun rd => tensorV rx rd)) (elim.flatCat cs0))
      (matVec (D.map (fun rd => tensorV rx rd)) (elim.flatCat (cs0.map List.tail)))
  | [], _ => trivial
  | r :: D, hDr =>
    ⟨tensorRowR_pad r rx cs0 hl (by rw [hDr.1]; exact hcs0),
     padRowsR rx cs0 hl m hcs0 D hDr.2⟩

/-- The strided fold's peel: the diagonal's leading key contributes
its entry against the first factor's form at the strided slice, and
the trailing diagonal reads the chunks' tails. -/
private theorem quadR_step (a : BPair) (m : Nat) (D : Mat)
    (hDl : D.length = m) (hDr : rowsLen m D)
    (cs0 : List (List BPair)) (hcs0 : rowsLen (m + 1) cs0) :
    ∀ (X : Mat) (cs : List (List BPair)),
      X.length = cs.length → rowsLen cs0.length X →
      rowsLen (m + 1) cs →
      (dotN (elim.flatCat cs) (matVec (tensorM X
          ((a :: List.replicate m BPair.unit)
            :: D.map (fun r => BPair.unit :: r))) (elim.flatCat cs0))).oneValue
        (a * dotN (cs.map hdU) (matVec X (cs0.map hdU))
          + dotN (elim.flatCat (cs.map List.tail))
              (matVec (tensorM X D) (elim.flatCat (cs0.map List.tail))))
  | [], [], _, _, _ =>
    BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit a) (BPair.oneValue_refl BPair.unit))
      (BPair.unit_add BPair.unit))
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl
  | rx :: X, ch :: cs, hl, hX, hcs => by
    cases ch with
    | nil => exact Nat.noConfusion hcs.1
    | cons h t =>
      have hcl : rx.length = cs0.length := hX.1
      have htl : t.length = m := Nat.succ.inj hcs.1
      have hIH := quadR_step a m D hDl hDr cs0 hcs0 X cs
        (Nat.succ.inj hl) hX.2 hcs.2
      show (dotN ((h :: t) ++ elim.flatCat cs)
          (matVec (((a :: List.replicate m BPair.unit)
              :: D.map (fun r => BPair.unit :: r)).map
              (fun rd => tensorV rx rd)
            ++ tensorM X ((a :: List.replicate m BPair.unit)
              :: D.map (fun r => BPair.unit :: r)))
            (elim.flatCat cs0))).oneValue
        (a * dotN (h :: cs.map hdU)
            (dotN rx (cs0.map hdU) :: matVec X (cs0.map hdU))
          + dotN (t ++ elim.flatCat (cs.map List.tail))
              (matVec (D.map (fun rd => tensorV rx rd)
                ++ tensorM X D) (elim.flatCat (cs0.map List.tail))))
      rw [matVec_append, matVec_append]
      have hlenblk : (h :: t).length
          = (matVec (((a :: List.replicate m BPair.unit)
              :: D.map (fun r => BPair.unit :: r)).map
              (fun rd => tensorV rx rd)) (elim.flatCat cs0)).length := by
        rw [matVec_length, ground.length_map]
        show t.length + 1 = (D.map (fun r => BPair.unit :: r)).length + 1
        rw [htl, ground.length_map, hDl]
      refine BPair.oneValue_trans (inertia.dotN_app _ _ _ _ hlenblk) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (inertia.dotN_app [h] t
              [dotN (tensorV rx (a :: List.replicate m BPair.unit))
                (elim.flatCat cs0)] _ rfl)
            (BPair.add_congr
              (BPair.oneValue_trans
                (inertia.dotN_single h _)
                (BPair.mul_congr (BPair.oneValue_refl h)
                  (tensorRowR_head a m rx cs0 hcl hcs0)))
              (dotN_congrR t _ _ (padRowsR rx cs0 hcl m hcs0 D hDr))))
          hIH) ?_
      rw [BPair.add_add_comm]
      refine BPair.add_congr ?_ ?_
      · refine BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_of_eq
              (BPair.mul_left_comm h a (dotN rx (cs0.map hdU))))
            (BPair.oneValue_refl _)) ?_
        rw [← BPair.left_distrib a (h * dotN rx (cs0.map hdU))
          (dotN (cs.map hdU) (matVec X (cs0.map hdU)))]
        refine BPair.mul_congr (BPair.oneValue_refl a) ?_
        exact BPair.oneValue_symm (BPair.oneValue_trans
          (inertia.dotN_app [h] (cs.map hdU) [dotN rx (cs0.map hdU)]
            (matVec X (cs0.map hdU)) rfl)
          (BPair.add_congr (inertia.dotN_single h (dotN rx (cs0.map hdU)))
            (BPair.oneValue_refl _)))
      · exact BPair.oneValue_symm (inertia.dotN_app _ _ _ _
          (by rw [matVec_length, ground.length_map, htl, hDl]))


/-! ### The block diagonal's shape and the strided fold -/

/-- The split's diagonal against a right tensor slot: at blocks all
of order one the form is the fold over the diagonal's keys of the
entry against the first factor's own form at the strided slice of
the vector. -/
private theorem tensorR_fold (X : Mat) (N : Nat) (hXl : X.length = N)
    (hXr : rowsLen N X)
    (hXpos : ∀ v : List BPair, v.length = N →
      BPair.unit ≤ inertia.quadForm X v) :
    ∀ (bs : List inertia.SBlock) (k : Nat),
      (bs.all (fun b => b.order == 1)) = true →
      (bs.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true →
      bs.foldl (fun mm b => mm + b.rev) 0 = 0 →
      ∀ cs : List (List BPair), cs.length = N →
        rowsLen (inertia.widthOf bs k) cs →
        BPair.unit ≤ inertia.quadForm
          (tensorM X (inertia.blockMat bs k)) (elim.flatCat cs)
  | [], k, _, _, _, cs, _, _ =>
    ground.leB_congr_right
      (BPair.oneValue_symm (quadForm_unitRows _
        (unitRows_tensorR X _ (unitRows_blockNil k)) (elim.flatCat cs)))
      (ground.leB_refl BPair.unit)
  | inertia.SBlock.two _ _ _ :: _, _, hord, _, _, _, _, _ =>
    Bool.noConfusion ((ground.andSplitB hord).1)
  | inertia.SBlock.one a :: bs, k, hord, hall, hrev, cs, hcsl, hcsr => by
    have ha : BPair.unit < a :=
      inertia.oneUp (ground.notOfBang ((ground.andSplitB hall).1))
        ((ground.addZeroN (inertia.revSplit.symm.trans hrev)).1)
    rw [show inertia.widthOf (inertia.SBlock.one a :: bs) k
        = inertia.widthOf bs k + 1 from inertia.widthOf_shift bs k 1]
      at hcsr
    have hstep := quadR_step a (inertia.widthOf bs k)
      (inertia.blockMat bs k) (inertia.blockMat_len bs k) (inertia.blockMat_rows bs k)
      cs hcsr X cs (hXl.trans hcsl.symm) (by rw [hcsl]; exact hXr) hcsr
    refine ground.leB_congr_right (BPair.oneValue_symm hstep) ?_
    refine ground.unitLeAdd
      (ground.unitLeMul (ground.leB_of_lt ha)
        (hXpos (cs.map hdU) (by rw [ground.length_map]; exact hcsl))) ?_
    exact tensorR_fold X N hXl hXr hXpos bs k
      ((ground.andSplitB hord).2) ((ground.andSplitB hall).2)
      ((ground.addZeroN (inertia.revSplit.symm.trans hrev)).2)
      (cs.map List.tail) (by rw [ground.length_map]; exact hcsl)
      (rowsLen_tail _ cs hcsr)

/-- The mirror of `tensor_form_left` at the second slot: a single
component gram at an all-order-one split tensors on the right
without moving the first factor's form off its side, the strided
slice the vector's own chunking. -/
theorem tensor_form_right {n : Nat} (G : Mat) (sp : inertia.Split n)
    (hread : inertia.splitRead G sp) (hpsd : inertia.psdAt sp)
    (hord : (sp.blocks.all (fun b => b.order == 1)) = true)
    (X : Mat) (N : Nat) (hX : sqAt X N)
    (hXpos : ∀ v : List BPair, v.length = N →
      ¬ (inertia.quadForm X v < BPair.unit))
    (u : List BPair) (hu : u.length = N * n) :
    ¬ (inertia.quadForm (tensorM X G) u < BPair.unit) := by
  obtain ⟨hsq, ⟨hdetT, hprod, _⟩, hcong, hns⟩ := hread
  cases Nat.eq_zero_or_pos n with
  | inl h0 =>
    rw [ground.nil_of_length_zero _ (show u.length = 0 by rw [hu, h0, Nat.mul_zero])]
    show ¬ (BPair.unit < BPair.unit)
    exact ground.leB_not_lt (ground.leB_refl BPair.unit)
  | inr hn =>
    cases Nat.eq_zero_or_pos N with
    | inl h0 =>
      rw [ground.nil_of_length_zero _ (show u.length = 0 by rw [hu, h0, Nat.zero_mul])]
      show ¬ (BPair.unit < BPair.unit)
      exact ground.leB_not_lt (ground.leB_refl BPair.unit)
    | inr hN =>
      have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
      have hTwrows : rowsLen n sp.Tw.val := rowsLen_of_sqAt sp.Tw.shape
      have hTlen : sp.T.val.length = n := sp.T.rows
      have hTwlen : sp.Tw.val.length = n := sp.Tw.rows
      have hGrows : rowsLen n G := rowsLen_of_sqAt hsq
      have hGlen : G.length = n := sqAt_len hsq
      have hXrows : rowsLen N X := rowsLen_of_sqAt hX
      have hXlen : X.length = N := sqAt_len hX
      have hidr : rowsLen N (inertia.idMat N) := inertia.idMat_rows N
      have hidl : (inertia.idMat N).length = N := inertia.idMat_len N
      have hnN : 0 < N * n := Nat.mul_pos hN hn
      have hPl : (tensorM (inertia.idMat N) sp.T.val).length = N * n := by
        rw [tensorM_length, hidl, hTlen]
      have hPr : rowsLen (N * n) (tensorM (inertia.idMat N) sp.T.val) :=
        rowsLen_tensorM N n _ _ hidr hTrows
      have hPwl : (tensorM (inertia.idMat N) sp.Tw.val).length = N * n := by
        rw [tensorM_length, hidl, hTwlen]
      have hPwr : rowsLen (N * n) (tensorM (inertia.idMat N) sp.Tw.val) :=
        rowsLen_tensorM N n _ _ hidr hTwrows
      have hSl : (tensorM X G).length = N * n := by
        rw [tensorM_length, hXlen, hGlen]
      have hSr : rowsLen (N * n) (tensorM X G) :=
        rowsLen_tensorM N n X G hXrows hGrows
      have hSsq : sqAt (tensorM X G) (N * n) := sqAt_of hSl hSr
      have hIt : (transposeM (inertia.idMat N)).length = N := by
        rw [inertia.transposeM_idMat N, hidl]
      have hTwt : (transposeM sp.Tw.val).length = n :=
        length_transposeM _ hTwrows (by rw [hTwlen]; exact hn)
      have hTt : (transposeM sp.T.val).length = n :=
        length_transposeM _ hTrows (by rw [hTlen]; exact hn)
      have hTTw : rowsLen n (matMul sp.T.val sp.Tw.val) :=
        rowsLen_cast hTwt (rowsLen_matMul sp.T.val sp.Tw.val)
      have hcl : (matVec (tensorM (inertia.idMat N) sp.Tw.val) u).length
          = N * n := by rw [matVec_length]; exact hPwl
      have hMM : matOneValue
          (matMul (tensorM (inertia.idMat N) sp.T.val)
            (tensorM (inertia.idMat N) sp.Tw.val))
          (inertia.matScaleB (minor sp.T.val)
            (inertia.idMat (N * n))) := by
        refine matOne_trans (matMul_tensorM N n n (inertia.idMat N)
          sp.T.val (inertia.idMat N) sp.Tw.val hTrows hTwlen hidr
          hTwrows) ?_
        refine matOne_trans (tensorM_congrL _ _ _
          (inertia.idMat_matMul N (inertia.idMat N) hidr hidl hN)) ?_
        refine matOne_trans (tensorM_congrR n _ _ hTTw
          (inertia.rowsLen_scaleB (minor sp.T.val) n (inertia.idMat n)
            (inertia.idMat_rows n)) hprod (inertia.idMat N)) ?_
        rw [tensorM_scaleR, tensorM_idMat]
        exact matOne_refl _
      have hA : poly.oneValue
          (matVec (tensorM (inertia.idMat N) sp.T.val)
            (matVec (tensorM (inertia.idMat N) sp.Tw.val) u))
          (vecScale (minor sp.T.val) u) := by
        refine poly.oneValue_trans
          (matVec_comp _ _ u (N * n) hPwr hu
            (by rw [hPwl]; exact hPr)) ?_
        refine poly.oneValue_trans (matVec_matOne _ _ u hMM) ?_
        exact inertia.scaleId_act (minor sp.T.val) (N * n) u hu
      have hXIr : rowsLen N (matMul X (inertia.idMat N)) :=
        rowsLen_cast hIt (rowsLen_matMul X (inertia.idMat N))
      have hXIl : (matMul X (inertia.idMat N)).length = N := by
        rw [length_matMul, hXlen]
      have hXI : matOneValue
          (matMul (transposeM (inertia.idMat N))
            (matMul X (inertia.idMat N))) X := by
        rw [inertia.transposeM_idMat N]
        refine matOne_trans (elim.matMul_congrR_of (inertia.idMat N) _ _
          (elim.transposeM_congrM N _ _ hXIr hXrows (by rw [hXIl, hXlen])
            (inertia.matMul_idR N X hXrows hXlen hN hN))) ?_
        exact inertia.idMat_matMul N X hXrows hXlen hN
      have hGTr : rowsLen n (matMul G sp.T.val) :=
        rowsLen_cast hTt (rowsLen_matMul G sp.T.val)
      have hGTl : (matMul G sp.T.val).length = n := by
        rw [length_matMul, hGlen]
      have hGTt : (transposeM (matMul G sp.T.val)).length = n :=
        length_transposeM _ hGTr (by rw [hGTl]; exact hn)
      have hwidth : inertia.widthOf sp.blocks sp.kern = n :=
        Nat.eq_of_beq_eq_true sp.width
      have hBr : rowsLen n (inertia.blockMat sp.blocks sp.kern) := by
        have h := inertia.blockMat_rows sp.blocks sp.kern
        rw [hwidth] at h
        exact h
      have hR2 : matOneValue
          (matMul (transposeM (tensorM (inertia.idMat N) sp.T.val))
            (matMul (tensorM X G)
              (tensorM (inertia.idMat N) sp.T.val)))
          (tensorM X (inertia.blockMat sp.blocks sp.kern)) := by
        refine matOne_trans (congr_tensorM N n N n X G
          (inertia.idMat N) sp.T.val hX hsq hidl hidr hTlen hTrows) ?_
        refine matOne_trans (tensorM_congrL _ _ _ hXI) ?_
        exact tensorM_congrR n _ _
          (rowsLen_cast hGTt (rowsLen_matMul (transposeM sp.T.val)
            (matMul G sp.T.val))) hBr hcong X
      obtain ⟨cs, hcsl, hcsr, hcsf⟩ :=
        chunkEx N n (matVec (tensorM (inertia.idMat N) sp.Tw.val) u) hcl
      have hBlock : BPair.unit ≤ inertia.quadForm
          (tensorM X (inertia.blockMat sp.blocks sp.kern))
          (matVec (tensorM (inertia.idMat N) sp.Tw.val) u) := by
        rw [← hcsf]
        exact tensorR_fold X N hXlen hXrows
          (fun v hv => ground.leB_of_not_lt (hXpos v hv))
          sp.blocks sp.kern hord hns hpsd cs hcsl
          (by rw [hwidth]; exact hcsr)
      have hUp : BPair.unit ≤ inertia.quadForm (tensorM X G)
          (matVec (tensorM (inertia.idMat N) sp.T.val)
            (matVec (tensorM (inertia.idMat N) sp.Tw.val) u)) := by
        refine ground.leB_congr_right (BPair.oneValue_symm ?_) hBlock
        refine BPair.oneValue_trans
          (inertia.congQuad (tensorM X G)
            (tensorM (inertia.idMat N) sp.T.val) (N * n) (N * n) hSsq
            hPr hPl _ hcl) ?_
        exact inertia.quadMatOne _ _ _ hR2
      have hScale : (inertia.quadForm (tensorM X G)
          (matVec (tensorM (inertia.idMat N) sp.T.val)
            (matVec (tensorM (inertia.idMat N) sp.Tw.val) u))).oneValue
          (minor sp.T.val * minor sp.T.val
            * inertia.quadForm (tensorM X G) u) := by
        refine BPair.oneValue_trans (dotN_read _ _) ?_
        refine BPair.oneValue_trans (dotP_oneValue_left _ _ _ hA) ?_
        refine BPair.oneValue_trans
          (dotP_oneValue_right _ _ _ (matVec_congr (tensorM X G) _ _ hA)) ?_
        refine BPair.oneValue_trans
          (dotP_oneValue_right _ _ _
            (matVec_vecScale_free (tensorM X G) (minor sp.T.val) u)) ?_
        refine BPair.oneValue_trans
          (dotP_vecScale_right (vecScale (minor sp.T.val) u)
            (matVec (tensorM X G) u) (minor sp.T.val)) ?_
        have hinner : (dotP (vecScale (minor sp.T.val) u)
            (matVec (tensorM X G) u)).oneValue
            (minor sp.T.val * inertia.quadForm (tensorM X G) u) := by
          rw [dotP_comm (vecScale (minor sp.T.val) u)
            (matVec (tensorM X G) u)]
          refine BPair.oneValue_trans
            (dotP_vecScale_right (matVec (tensorM X G) u) u
              (minor sp.T.val)) ?_
          refine BPair.mul_congr (BPair.oneValue_refl _) ?_
          rw [dotP_comm (matVec (tensorM X G) u) u]
          exact BPair.oneValue_symm (dotN_read u (matVec (tensorM X G) u))
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (minor sp.T.val))
            hinner) ?_
        exact BPair.oneValue_of_eq
          (BPair.mul_assoc (minor sp.T.val) (minor sp.T.val)
            (inertia.quadForm (tensorM X G) u)).symm
      exact ground.leB_not_lt
        (inertia.scaleRefl (ground.sq_pos hdetT)
          (ground.leB_congr_right hScale hUp))


/-! ### The sector's shapes and the tensor power's form -/

private theorem tensorV_idOne : ∀ ra : List BPair,
    poly.oneValue (tensorV ra [BPair.ofPos Pos.one]) ra
  | [] => trivial
  | x :: ra =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_ofNat_one x),
     tensorV_idOne ra⟩

/-- The unit power is the scalars' line: a right tensor by it is the
matrix itself at the one-value read. -/
private theorem tensorM_idOne : ∀ Y : Mat,
    matOneValue (tensorM Y (inertia.idMat 1)) Y
  | [] => trivial
  | ra :: Y => ⟨tensorV_idOne ra, tensorM_idOne Y⟩

/-- The weighting rides out of the form fold. -/
private theorem tensorPow_len (G : Mat) {n : Nat} (hG : sqAt G n) :
    ∀ k : Nat, (tensorPow G k).length = n ^ k
      ∧ rowsLen (n ^ k) (tensorPow G k) := by
  intro k
  have h := tensorPow_shape G
    (rowsLen_cast (sqAt_len hG).symm (rowsLen_of_sqAt hG)) k
  rw [sqAt_len hG] at h
  exact ⟨h.2, h.1⟩

private theorem sumPencil_shape (H G : Mat) {n : Nat} (hH : sqAt H n)
    (hG : sqAt G n) : ∀ k : Nat,
    (sumPencil H G k).length = n ^ k
      ∧ rowsLen (n ^ k) (sumPencil H G k) := by
  have hpw : ∀ j : Nat, n ^ (j + 1) = n * n ^ j := fun j => by
    rw [Nat.pow_succ, Nat.mul_comm]
  intro k
  induction k with
  | zero => exact ⟨length_nullMat 1 1, rowsLen_nullMat 1 1⟩
  | succ k ih =>
    have hp := tensorPow_len G hG k
    refine ⟨?_, ?_⟩
    · show (matAdd (tensorM H (tensorPow G k))
        (tensorM G (sumPencil H G k))).length = n ^ (k + 1)
      rw [hpw k]
      refine ground.length_zipWith _ _ _ _ ?_ ?_
      · rw [tensorM_length, sqAt_len hH, hp.1]
      · rw [tensorM_length, sqAt_len hG, ih.1]
    · show rowsLen (n ^ (k + 1)) (matAdd (tensorM H (tensorPow G k))
        (tensorM G (sumPencil H G k)))
      rw [hpw k]
      exact rowsLen_matAdd _ _ _
        (rowsLen_tensorM n (n ^ k) H _ (rowsLen_of_sqAt hH) hp.2)
        (rowsLen_tensorM n (n ^ k) G _ (rowsLen_of_sqAt hG) ih.2)


private theorem unitRows_nullMat : ∀ k m : Nat, unitRows (nullMat k m)
  | 0, _ => trivial
  | k + 1, m => ⟨poly.unitTail_replicate m, unitRows_nullMat k m⟩

/-- The site datum tensors on the right slot without moving: the
sum and the memberwise swap both pass through. -/
private theorem tensorM_siteL (A B P : Mat) :
    matOneValue (tensorM (inertia.siteDatum A B) P)
      (inertia.siteDatum (tensorM A P) (tensorM B P)) := by
  show matOneValue (tensorM (matAdd A (matSwap B)) P)
    (matAdd (tensorM A P) (matSwap (tensorM B P)))
  rw [← tensorM_swapL B P]
  exact tensorM_addL A (matSwap B) P

/-- The site datum tensors on the left slot at a stated width. -/
private theorem tensorM_siteR (w : Nat) (G A B : Mat)
    (hl : A.length = (matSwap B).length) (hA : rowsLen w A)
    (hB : rowsLen w (matSwap B)) :
    matOneValue (tensorM G (inertia.siteDatum A B))
      (inertia.siteDatum (tensorM G A) (tensorM G B)) := by
  show matOneValue (tensorM G (matAdd A (matSwap B)))
    (matAdd (tensorM G A) (matSwap (tensorM G B)))
  rw [← tensorM_swapR G B]
  exact tensorM_addR w G A (matSwap B) hl hA hB

/-- The site datum's form at or above the sum's unit is the two
members' own order. -/
private theorem siteOrder_of (A B : Mat) (u : List BPair)
    (hAl : A.length = u.length) (hAr : rowsLen u.length A)
    (hBl : B.length = u.length) (hBr : rowsLen u.length B)
    (h : ¬ (inertia.quadForm (inertia.siteDatum A B) u < BPair.unit)) :
    inertia.quadForm B u ≤ inertia.quadForm A u :=
  ground.leB_of_not_lt (inertia.site_side hAl hAr hBl hBr h)

/-- The converse read: the members' order prices the site datum at
or above the sum's unit. -/
private theorem site_of_order (A B : Mat) (u : List BPair)
    (hAl : A.length = u.length) (hAr : rowsLen u.length A)
    (hBl : B.length = u.length) (hBr : rowsLen u.length B)
    (h : inertia.quadForm B u ≤ inertia.quadForm A u) :
    ¬ (inertia.quadForm (inertia.siteDatum A B) u < BPair.unit) :=
  fun hlt => ground.leB_not_lt h (inertia.site_gap hAl hAr hBl hBr hlt)

/-- The tensor power keeps a positive-semidefinite first factor
there: the power's factors enter one at a time through
`tensor_form_right` at the split gram. -/
private theorem tensorPow_form {n : Nat} (G : Mat) (hG : sqAt G n)
    (spG : inertia.Split n) (hGr : inertia.splitRead G spG)
    (hGpsd : inertia.psdAt spG)
    (hGord : (spG.blocks.all (fun b => b.order == 1)) = true) :
    ∀ (k : Nat) (Y : Mat) (nY : Nat), sqAt Y nY →
      (∀ v : List BPair, v.length = nY →
        ¬ (inertia.quadForm Y v < BPair.unit)) →
      ∀ u : List BPair, u.length = nY * n ^ k →
        ¬ (inertia.quadForm (tensorM Y (tensorPow G k)) u < BPair.unit)
  | 0, Y, nY, _, hYpos, u, hu => by
    intro hlt
    refine hYpos u (by rw [hu, Nat.pow_zero, Nat.mul_one]) ?_
    exact BPair.lt_congr (inertia.quadMatOne _ _ u (tensorM_idOne Y))
      (BPair.oneValue_refl BPair.unit) hlt
  | k + 1, Y, nY, hY, hYpos, u, hu => by
    have hYG : sqAt (tensorM Y G) (nY * n) :=
      sqAt_of (by rw [tensorM_length, sqAt_len hY, sqAt_len hG])
        (rowsLen_tensorM nY n Y G (rowsLen_of_sqAt hY)
          (rowsLen_of_sqAt hG))
    have key := tensorPow_form G hG spG hGr hGpsd hGord k (tensorM Y G)
      (nY * n) hYG
      (fun v hv => tensor_form_right G spG hGr hGpsd hGord Y nY hY
        hYpos v hv) u
      (by rw [hu, Nat.pow_succ, Nat.mul_comm (n ^ k) n,
        ← ground.mulAssoc])
    rw [show tensorM Y (tensorPow G (k + 1))
        = tensorM (tensorM Y G) (tensorPow G k) from
      (tensorM_assoc Y G (tensorPow G k)).symm]
    exact key


/-- The tensor sum's floor: at every factor count the sector's
pencil sits at the count's own multiple of the single-component
level against the tensor gram — `lem:relfiber`(iii)'s
`H^{(ϱ)} = ϱℓ G^{⊗ϱ} + ∑ G^{⊗a} ⊗ S₁ ⊗ G^{⊗b}` read as an order at
every vector, the recursion adding one leading factor per step. -/
private theorem sector_floor {n : Nat} (H G : Mat) (hH : sqAt H n)
    (hG : sqAt G n) (x y : Pos) (spF : inertia.Split n)
    (hF : inertia.splitRead (inertia.siteDatum
      (matAdd H (inertia.matScale y G)) (inertia.matScale x G)) spF)
    (hFpsd : inertia.psdAt spF)
    (spG : inertia.Split n) (hGsp : inertia.splitRead G spG)
    (hGpsd : inertia.psdAt spG)
    (hGord : (spG.blocks.all (fun b => b.order == 1)) = true) :
    ∀ (k : Nat) (u : List BPair), u.length = n ^ k →
      (BPair.ofNat k * BPair.ofPos x)
          * inertia.quadForm (tensorPow G k) u
        ≤ inertia.quadForm (sumPencil H G k) u
          + (BPair.ofNat k * BPair.ofPos y)
            * inertia.quadForm (tensorPow G k) u := by
  have hpw : ∀ j : Nat, n ^ (j + 1) = n * n ^ j := fun j => by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hHl : H.length = n := sqAt_len hH
  have hHr : rowsLen n H := rowsLen_of_sqAt hH
  have hGl : G.length = n := sqAt_len hG
  have hGr : rowsLen n G := rowsLen_of_sqAt hG
  have hSyl : (inertia.matScale y G).length = n :=
    (ground.length_map _ G).trans hGl
  have hSyr : rowsLen n (inertia.matScale y G) :=
    rowsLen_mapRows _ G n hGr
  have hSxl : (inertia.matScale x G).length = n :=
    (ground.length_map _ G).trans hGl
  have hSxr : rowsLen n (inertia.matScale x G) :=
    rowsLen_mapRows _ G n hGr
  intro k
  induction k with
  | zero =>
    intro u _
    refine ground.leB_congr_left (BPair.oneValue_symm ?_)
      (ground.leB_congr_right (BPair.oneValue_symm ?_)
        (ground.leB_refl BPair.unit))
    · exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.unit_mul (BPair.ofPos x))
          (BPair.oneValue_refl _))
        (BPair.unit_mul _)
    · refine BPair.oneValue_trans (BPair.add_congr
        (quadForm_unitRows _ (unitRows_nullMat 1 1) u)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.unit_mul (BPair.ofPos y))
            (BPair.oneValue_refl _))
          (BPair.unit_mul _))) ?_
      exact BPair.unit_add BPair.unit
  | succ k ih =>
    intro u hul
    have hun : u.length = n * n ^ k := by rw [hul, hpw k]
    have hp := tensorPow_len G hG k
    have hs := sumPencil_shape H G hH hG k
    have htP : ∀ Z : Mat, Z.length = n → rowsLen n Z →
        (tensorM Z (tensorPow G k)).length = u.length
          ∧ rowsLen u.length (tensorM Z (tensorPow G k)) := by
      intro Z hZl hZr
      refine ⟨?_, ?_⟩
      · rw [tensorM_length, hZl, hp.1, hun]
      · rw [hun]
        exact rowsLen_tensorM n (n ^ k) Z (tensorPow G k) hZr hp.2
    have hGt : ∀ Z : Mat, Z.length = n ^ k → rowsLen (n ^ k) Z →
        (tensorM G Z).length = u.length
          ∧ rowsLen u.length (tensorM G Z) := by
      intro Z hZl hZr
      refine ⟨?_, ?_⟩
      · rw [tensorM_length, hGl, hZl, hun]
      · rw [hun]
        exact rowsLen_tensorM n (n ^ k) G Z hGr hZr
    -- the weighting reads at the two slots
    have hscaleL : ∀ (w : Pos),
        (inertia.quadForm
          (tensorM (inertia.matScale w G) (tensorPow G k)) u).oneValue
          (BPair.ofPos w
            * inertia.quadForm (tensorM G (tensorPow G k)) u) := by
      intro w
      refine BPair.oneValue_trans
        (inertia.quadMatOne _ _ u
          (tensorM_congrL _ _ (tensorPow G k) (inertia.matScale_scaleB w G))) ?_
      rw [tensorM_scaleL]
      exact inertia.quadForm_scaleB (BPair.ofPos w) (tensorM G (tensorPow G k)) u
    have hscaleR : ∀ (c : BPair),
        (inertia.quadForm
          (tensorM G (inertia.matScaleB c (tensorPow G k))) u).oneValue
          (c * inertia.quadForm (tensorM G (tensorPow G k)) u) := by
      intro c
      rw [tensorM_scaleR]
      exact inertia.quadForm_scaleB c (tensorM G (tensorPow G k)) u
    -- (i) the single-component floor, tensored on the right
    have hTP : ¬ (inertia.quadForm
        (tensorM (inertia.siteDatum (matAdd H (inertia.matScale y G))
          (inertia.matScale x G)) (tensorPow G k)) u < BPair.unit) :=
      tensorPow_form G hG spG hGsp hGpsd hGord k _ n hF.1
        (inertia.psd_all _ spF hF hFpsd) u hun
    have hAsh := htP (matAdd H (inertia.matScale y G))
      (ground.length_zipWith _ _ _ _ hHl hSyl)
      (rowsLen_matAdd n _ _ hHr hSyr)
    have hBsh := htP (inertia.matScale x G) hSxl hSxr
    have hi : BPair.ofPos x
        * inertia.quadForm (tensorM G (tensorPow G k)) u
        ≤ inertia.quadForm (tensorM H (tensorPow G k)) u
          + BPair.ofPos y
            * inertia.quadForm (tensorM G (tensorPow G k)) u := by
      refine ground.leB_congr (hscaleL x) ?_
        (siteOrder_of _ _ u hAsh.1 hAsh.2 hBsh.1 hBsh.2
          (fun hlt => hTP (BPair.lt_congr
            (BPair.oneValue_symm (inertia.quadMatOne _ _ u
              (tensorM_siteL (matAdd H (inertia.matScale y G))
                (inertia.matScale x G) (tensorPow G k))))
            (BPair.oneValue_refl BPair.unit) hlt)))
      refine BPair.oneValue_trans
        (inertia.quadMatOne _ _ u
          (tensorM_addL H (inertia.matScale y G) (tensorPow G k))) ?_
      refine BPair.oneValue_trans
        (inertia.quadForm_add _ _ u (htP H hHl hHr).1 (htP H hHl hHr).2
          (htP (inertia.matScale y G) hSyl hSyr).1
          (htP (inertia.matScale y G) hSyl hSyr).2) ?_
      exact BPair.add_congr (BPair.oneValue_refl _) (hscaleL y)
    -- (ii) the accumulated datum, tensored on the left
    have hAyl : (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
        (tensorPow G k)).length = n ^ k :=
      (inertia.length_scaleB _ _).trans hp.1
    have hAyr : rowsLen (n ^ k) (inertia.matScaleB
        (BPair.ofNat k * BPair.ofPos y) (tensorPow G k)) :=
      inertia.rowsLen_scaleB _ _ _ hp.2
    have hAkl : (matAdd (sumPencil H G k)
        (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
          (tensorPow G k))).length = n ^ k :=
      ground.length_zipWith _ _ _ _ hs.1 hAyl
    have hAkr : rowsLen (n ^ k) (matAdd (sumPencil H G k)
        (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
          (tensorPow G k))) :=
      rowsLen_matAdd _ _ _ hs.2 hAyr
    have hBkl : (inertia.matScaleB (BPair.ofNat k * BPair.ofPos x)
        (tensorPow G k)).length = n ^ k :=
      (inertia.length_scaleB _ _).trans hp.1
    have hBkr : rowsLen (n ^ k) (inertia.matScaleB
        (BPair.ofNat k * BPair.ofPos x) (tensorPow G k)) :=
      inertia.rowsLen_scaleB _ _ _ hp.2
    have hMkpos : ∀ v : List BPair, v.length = n ^ k →
        ¬ (inertia.quadForm (inertia.siteDatum
          (matAdd (sumPencil H G k)
            (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
              (tensorPow G k)))
          (inertia.matScaleB (BPair.ofNat k * BPair.ofPos x)
            (tensorPow G k))) v < BPair.unit) := by
      intro v hv
      refine site_of_order _ _ v (by rw [hv]; exact hAkl)
        (by rw [hv]; exact hAkr) (by rw [hv]; exact hBkl)
        (by rw [hv]; exact hBkr) ?_
      refine ground.leB_congr
        (BPair.oneValue_symm (inertia.quadForm_scaleB _ _ v)) ?_ (ih v hv)
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (inertia.quadForm_add _ _ v (by rw [hv]; exact hs.1)
          (by rw [hv]; exact hs.2) (by rw [hv]; exact hAyl)
          (by rw [hv]; exact hAyr)) ?_
      exact BPair.add_congr (BPair.oneValue_refl _)
        (inertia.quadForm_scaleB _ _ v)
    have hMksq : sqAt (inertia.siteDatum
        (matAdd (sumPencil H G k)
          (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
            (tensorPow G k)))
        (inertia.matScaleB (BPair.ofNat k * BPair.ofPos x)
          (tensorPow G k))) (n ^ k) :=
      sqAt_of
        (ground.length_zipWith _ _ _ _ hAkl
          ((length_matSwap _).trans hBkl))
        (rowsLen_matAdd _ _ _ hAkr (rowsLen_mapRows _ _ _ hBkr))
    have hGM : ¬ (inertia.quadForm (tensorM G (inertia.siteDatum
        (matAdd (sumPencil H G k)
          (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
            (tensorPow G k)))
        (inertia.matScaleB (BPair.ofNat k * BPair.ofPos x)
          (tensorPow G k)))) u < BPair.unit) :=
      tensor_form_left G spG hGsp hGpsd hGord _ (n ^ k) hMksq hMkpos u hun
    have hGAsh := hGt _ hAkl hAkr
    have hGBsh := hGt _ hBkl hBkr
    have hii : (BPair.ofNat k * BPair.ofPos x)
        * inertia.quadForm (tensorM G (tensorPow G k)) u
        ≤ inertia.quadForm (tensorM G (sumPencil H G k)) u
          + (BPair.ofNat k * BPair.ofPos y)
            * inertia.quadForm (tensorM G (tensorPow G k)) u := by
      refine ground.leB_congr (hscaleR _) ?_
        (siteOrder_of _ _ u hGAsh.1 hGAsh.2 hGBsh.1 hGBsh.2
          (fun hlt => hGM (BPair.lt_congr
            (BPair.oneValue_symm (inertia.quadMatOne _ _ u
              (tensorM_siteR (n ^ k) G _ _
                (by rw [hAkl, length_matSwap, hBkl]) hAkr
                (rowsLen_mapRows _ _ _ hBkr))))
            (BPair.oneValue_refl BPair.unit) hlt)))
      refine BPair.oneValue_trans
        (inertia.quadMatOne _ _ u
          (tensorM_addR (n ^ k) G (sumPencil H G k)
            (inertia.matScaleB (BPair.ofNat k * BPair.ofPos y)
              (tensorPow G k)) (hs.1.trans hAyl.symm) hs.2 hAyr)) ?_
      refine BPair.oneValue_trans
        (inertia.quadForm_add _ _ u (hGt _ hs.1 hs.2).1
          (hGt _ hs.1 hs.2).2 (hGt _ hAyl hAyr).1
          (hGt _ hAyl hAyr).2) ?_
      exact BPair.add_congr (BPair.oneValue_refl _) (hscaleR _)
    -- (iii) the two floors add
    have hsum : (inertia.quadForm (sumPencil H G (k + 1)) u).oneValue
        (inertia.quadForm (tensorM H (tensorPow G k)) u
          + inertia.quadForm (tensorM G (sumPencil H G k)) u) :=
      inertia.quadForm_add _ _ u (htP H hHl hHr).1 (htP H hHl hHr).2
        (hGt _ hs.1 hs.2).1 (hGt _ hs.1 hs.2).2
    refine ground.leB_congr ?_ ?_ (ground.leB_add hi hii)
    · refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (ground.ofNat_succ_mul k (BPair.ofPos x))
          (BPair.oneValue_refl _)) ?_
      rw [BPair.right_distrib, BPair.add_comm]
      exact BPair.oneValue_refl _
    · rw [BPair.add_add_comm]
      refine BPair.add_congr (BPair.oneValue_symm hsum) ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (ground.ofNat_succ_mul k (BPair.ofPos y))
          (BPair.oneValue_refl _)) ?_
      rw [BPair.right_distrib, BPair.add_comm]
      exact BPair.oneValue_refl _

/-- The sector clears the bracket (`lem:relfiber`(iii)): with the
single-component head pair positive semidefinite at the level
`⟨x : y⟩` and the gram's split at order-one blocks, a bracket
`⟨p : q⟩` with top at or below `ϱ` times that level leaves the
`ϱ`-sector's pair positive semidefinite against the tensor gram —
the tensor sum adds the separated bottom `ϱ` times, each summand
positive semidefinite against `G^{⊗ϱ}`, and the level slack rides
on the gram's own form. -/
theorem bottomClear {n : Nat} (H G : Mat) (hH : sqAt H n) (hG : sqAt G n)
    (x y : Pos) (spF : inertia.Split n)
    (hF : inertia.splitRead (inertia.siteDatum
      (matAdd H (inertia.matScale y G)) (inertia.matScale x G)) spF)
    (hFpsd : inertia.psdAt spF)
    (spG : inertia.Split n) (hGsp : inertia.splitRead G spG)
    (hGpsd : inertia.psdAt spG)
    (hGord : (spG.blocks.all (fun b => b.order == 1)) = true)
    (rho : Nat) (hrho : 1 ≤ rho) (p q : Pos)
    (hlev : BPair.ofPos p + BPair.ofNat rho * BPair.ofPos y
      ≤ BPair.ofNat rho * BPair.ofPos x + BPair.ofPos q)
    {N : Nat} (sp : inertia.Split N)
    (hsp : inertia.splitRead (inertia.siteDatum
      (matAdd (sumPencil H G rho) (inertia.matScale q (tensorPow G rho)))
      (inertia.matScale p (tensorPow G rho))) sp) :
    inertia.psdAt sp := by
  have hp' := tensorPow_len G hG rho
  have hs := sumPencil_shape H G hH hG rho
  have hqPl : (inertia.matScale q (tensorPow G rho)).length = n ^ rho :=
    (ground.length_map _ _).trans hp'.1
  have hqPr : rowsLen (n ^ rho) (inertia.matScale q (tensorPow G rho)) :=
    rowsLen_mapRows _ _ _ hp'.2
  have hpPl : (inertia.matScale p (tensorPow G rho)).length = n ^ rho :=
    (ground.length_map _ _).trans hp'.1
  have hpPr : rowsLen (n ^ rho) (inertia.matScale p (tensorPow G rho)) :=
    rowsLen_mapRows _ _ _ hp'.2
  have hAl : (matAdd (sumPencil H G rho)
      (inertia.matScale q (tensorPow G rho))).length = n ^ rho :=
    ground.length_zipWith _ _ _ _ hs.1 hqPl
  have hAr : rowsLen (n ^ rho) (matAdd (sumPencil H G rho)
      (inertia.matScale q (tensorPow G rho))) :=
    rowsLen_matAdd _ _ _ hs.2 hqPr
  have hMl : (inertia.siteDatum (matAdd (sumPencil H G rho)
      (inertia.matScale q (tensorPow G rho)))
      (inertia.matScale p (tensorPow G rho))).length = n ^ rho :=
    ground.length_zipWith _ _ _ _ hAl ((length_matSwap _).trans hpPl)
  have hN : n ^ rho = N := hMl.symm.trans (sqAt_len hsp.1)
  obtain ⟨j, hj⟩ := Nat.le.dest hrho
  have hrj : rho = j + 1 := by rw [← hj, Nat.add_comm]
  have hW : ∀ u : List BPair, u.length = n ^ rho →
      BPair.unit ≤ inertia.quadForm (tensorPow G rho) u := by
    intro u hu
    refine ground.leB_of_not_lt ?_
    rw [hrj]
    refine tensorPow_form G hG spG hGsp hGpsd hGord j G n hG
      (inertia.psd_all G spG hGsp hGpsd) u ?_
    rw [hu, hrj, Nat.pow_succ, Nat.mul_comm (n ^ j) n]
  have hform : ∀ u : List BPair, u.length = N →
      ¬ (inertia.quadForm (inertia.siteDatum
        (matAdd (sumPencil H G rho)
          (inertia.matScale q (tensorPow G rho)))
        (inertia.matScale p (tensorPow G rho))) u < BPair.unit) := by
    intro u hu
    have hu' : u.length = n ^ rho := hu.trans hN.symm
    refine site_of_order _ _ u (by rw [hu']; exact hAl)
      (by rw [hu']; exact hAr) (by rw [hu']; exact hpPl)
      (by rw [hu']; exact hpPr) ?_
    have hlevW := ground.leB_mulR (hW u hu') hlev
    rw [BPair.left_distrib, BPair.left_distrib,
      BPair.mul_comm (inertia.quadForm (tensorPow G rho) u)
        (BPair.ofPos p),
      BPair.mul_comm (inertia.quadForm (tensorPow G rho) u)
        (BPair.ofNat rho * BPair.ofPos y),
      BPair.mul_comm (inertia.quadForm (tensorPow G rho) u)
        (BPair.ofNat rho * BPair.ofPos x),
      BPair.mul_comm (inertia.quadForm (tensorPow G rho) u)
        (BPair.ofPos q)] at hlevW
    have hchain := ground.leB_trans hlevW
      (ground.leB_add (sector_floor H G hH hG x y spF hF hFpsd spG hGsp
          hGpsd hGord rho u hu')
        (ground.leB_refl (BPair.ofPos q
          * inertia.quadForm (tensorPow G rho) u)))
    rw [BPair.add_right_comm] at hchain
    have hchain2 : BPair.ofNat rho * BPair.ofPos y
          * inertia.quadForm (tensorPow G rho) u
          + BPair.ofPos p * inertia.quadForm (tensorPow G rho) u
        ≤ BPair.ofNat rho * BPair.ofPos y
            * inertia.quadForm (tensorPow G rho) u
          + (inertia.quadForm (sumPencil H G rho) u
            + BPair.ofPos q
              * inertia.quadForm (tensorPow G rho) u) := by
      rw [BPair.add_comm (BPair.ofNat rho * BPair.ofPos y
          * inertia.quadForm (tensorPow G rho) u)
        (BPair.ofPos p * inertia.quadForm (tensorPow G rho) u),
        BPair.add_comm (BPair.ofNat rho * BPair.ofPos y
          * inertia.quadForm (tensorPow G rho) u)
        (inertia.quadForm (sumPencil H G rho) u
          + BPair.ofPos q * inertia.quadForm (tensorPow G rho) u)]
      exact hchain
    have hcanc := ground.leB_cancelL hchain2
    refine ground.leB_congr ?_ ?_ hcanc
    · exact BPair.oneValue_symm
        (inertia.quadForm_ofPos p (tensorPow G rho) u)
    · refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (inertia.quadForm_add _ _ u (by rw [hu']; exact hs.1)
          (by rw [hu']; exact hs.2) (by rw [hu']; exact hqPl)
          (by rw [hu']; exact hqPr)) ?_
      refine BPair.add_congr (BPair.oneValue_refl _) ?_
      exact inertia.quadForm_ofPos q (tensorPow G rho) u
  cases hrev : inertia.revAt sp with
  | zero => exact hrev
  | succ t =>
    obtain ⟨w, hwl, hwlt⟩ := inertia.rev_witness _ sp hsp
      (by rw [hrev]; exact Nat.succ_le_succ (Nat.zero_le t))
    exact absurd hwlt (hform w hwl)

/-! ### Tier I: the components' index reads

`lem:relfiber`(i) at the index layer: a class of band components
joins to one configuration in the key order (`joinAll`), the
class's pairwise separation is one read per pair (`allDisj`,
`disjAll`), the electric content adds over a separated pair
(`contentN_join`) and over a separated class (`contentN_joinAll`),
the fiber dimensions multiply over a separated class
(`fibProd_joinAll`), a plaquette meets at most one separated
component's reach (`sepPlaq`), and a stencil row moves one
component with the spectator riding every target (`plaqRow_join`):
at a plaquette off the spectator's reach the joined class's row
counts a joined target at the moved part's own row count.  The
class folds read the unit's own equality (`F.eqL F.unit F.unit`,
the interface's unit-class reflexivity at the vacant join), and
the row read binds the stated lists' unit-class soundness as one
fold — every entry of the parts, the target and the target lists
off the unit's class or the unit itself — the interface's label
equality being the class read, sound at the reduced
representatives every index carries. -/

/-- The class's join: the components overlaid in the region's key
order, the vacant class the unit configuration at that key
range. -/
def joinAll {L : Type} (F : fusion.Data L) (R : lattice.Region) :
    List (List L) → List L
  | [] => carrier.unitConf F R
  | c :: cs => stableentries.joinConf F R c (joinAll F R cs)

/-- One component against a class: the vertex-disjoint read at
every member of the class. -/
def allDisj {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (c : List L) : List (List L) → Prop
  | [] => True
  | d :: ds => stableentries.disjSupp F R c d ∧ allDisj F R c ds

/-- A class's pairwise separation: every member vertex-disjoint
from the members after it. -/
def disjAll {L : Type} (F : fusion.Data L) (R : lattice.Region) :
    List (List L) → Prop
  | [] => True
  | c :: cs => allDisj F R c cs ∧ disjAll F R cs

/-- The decision at one component against a class, one conjunction
per member. -/
def decAllDisj {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (c : List L) : ∀ ds : List (List L), Decidable (allDisj F R c ds)
  | [] => isTrue trivial
  | _ :: ds => @instDecidableAnd _ _ inferInstance (decAllDisj F R c ds)

instance {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (c : List L) (ds : List (List L)) : Decidable (allDisj F R c ds) :=
  decAllDisj F R c ds

/-- The decision at the class's pairwise separation, one
conjunction per member. -/
def decDisjAll {L : Type} (F : fusion.Data L) (R : lattice.Region) :
    ∀ cs : List (List L), Decidable (disjAll F R cs)
  | [] => isTrue trivial
  | _ :: cs => @instDecidableAnd _ _ inferInstance (decDisjAll F R cs)

instance {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (cs : List (List L)) : Decidable (disjAll F R cs) :=
  decDisjAll F R cs

/-! ### The list kit the index reads consume -/


/-- A keyed image reading a source member's value is nonempty, the
count-free read at an image type without an equality. -/
private theorem filterMap_occ {α β : Type} [DecidableEq α]
    (f : α → Option β) : ∀ (l : List α) (x : α) (y : β),
    0 < countOf x l → f x = some y → ¬ (l.filterMap f).length = 0 :=
  fun l x _ hx hf h =>
    nomatch (ground.filterMap_none f l h x hx).symm.trans hf

/-! ### The incidence reads at an occupied key -/

/-- An occupied link reads incident labels at its tail: the key's
own entry sits in the vertex's incident list at the forward
orientation. -/
private theorem incid_occ {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (c : List L) (k : Nat) (hk : k < R.links)
    (hc : F.eqL (getAt F.unit c k) F.unit = false) :
    ¬ (carrier.incidentLabels F R c (getAt 0 R.tail k)).length = 0 := by
  have hinc : 0 < countOf (k, true)
      (lattice.incident R (getAt 0 R.tail k)) := by
    rw [lattice.incident_read R (getAt 0 R.tail k)]
    refine countOf_pos_of_mem
      (ground.mem_flatMap_to _ (ground.memRange hk) ?_)
    show (k, true) ∈
      (if getAt 0 R.tail k == getAt 0 R.tail k then [(k, true)] else [])
        ++ (if getAt 0 R.head k == getAt 0 R.tail k then [(k, false)]
            else [])
    rw [if_pos (eqBeqOf rfl)]
    exact ground.mem_append_left _ (List.Mem.head [])
  refine filterMap_occ _ (lattice.incident R (getAt 0 R.tail k))
    (k, true) (getAt F.unit c k) hinc ?_
  show (if F.eqL (getAt F.unit c k) F.unit then none
        else if true then some (getAt F.unit c k)
        else some (F.dual (getAt F.unit c k))) = some (getAt F.unit c k)
  rw [if_neg (boolNe hc), if_pos rfl]

/-- The vertex-disjoint read at the link level: at a key occupied
by the first configuration the second reads the unit, both parts'
incident labels meeting at the key's tail otherwise. -/
private theorem link_disj {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a b : List L) (hw : lattice.wellRead R)
    (hd : stableentries.disjSupp F R a b) (k : Nat) (hk : k < R.links)
    (ha : F.eqL (getAt F.unit a k) F.unit = false) :
    F.eqL (getAt F.unit b k) F.unit = true := by
  cases hb : F.eqL (getAt F.unit b k) F.unit with
  | true => rfl
  | false =>
    have hall : (((carrier.incidentLabels F R a (getAt 0 R.tail k)).length == 0)
        || ((carrier.incidentLabels F R b (getAt 0 R.tail k)).length == 0))
        = true := all_range_read R.verts hd _ (lattice.endLt R hw k hk).1
    cases orSplitB hall with
    | inl h => exact absurd (beqEqOf h) (incid_occ F R a k hk ha)
    | inr h => exact absurd (beqEqOf h) (incid_occ F R b k hk hb)

/-! ### The content at a separated pair -/

/-- The content at its additive spelling: the fold over the
configuration's own keys, an occupied key at its Casimir and the
unit key at the sum's unit. -/
private theorem contentN_fam {L : Type} (F : fusion.Data L) (x : List L) :
    carrier.contentN F x
      = famFold Nat.add 0
        (fun l => if F.eqL l F.unit then 0 else F.c2N l) x := by
  show x.foldl (fun acc l =>
      if F.eqL l F.unit then acc else acc + F.c2N l) 0 = _
  rw [foldl_congr (fun acc l => if F.eqL l F.unit then acc else acc + F.c2N l)
      (fun acc l => acc + (if F.eqL l F.unit then 0 else F.c2N l))
      (fun acc l => by cases F.eqL l F.unit <;> rfl) x 0,
    foldlSum (fun l => if F.eqL l F.unit then 0 else F.c2N l) x 0,
    Nat.zero_add]

/-- The content over the key range at a stated width: the fold at
the entries the keys read. -/
private theorem contentN_range {L : Type} (F : fusion.Data L) (n : Nat)
    (x : List L) (hx : x.length = n) :
    carrier.contentN F x
      = famFold Nat.add 0
        (fun k => if F.eqL (getAt F.unit x k) F.unit then 0
          else F.c2N (getAt F.unit x k)) (List.range n) := by
  have h : x = (List.range n).map (getAt F.unit x) := by
    rw [← hx]
    exact (ground.range_map_getAt F.unit x.length x rfl).symm
  exact ((contentN_fam F x).trans
    (congrArg (famFold Nat.add 0
      (fun l => if F.eqL l F.unit then 0 else F.c2N l)) h)).trans
    (famFold_map Nat.add 0 _ _ (List.range n))

/-- The content adds over a vertex-disjoint pair
(`lem:relfiber`(i)'s electric read): the join's Casimir fold is
the two parts' folds' sum, an occupied key of one part reading
the unit in the other at its tail's own vertex. -/
theorem contentN_join {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) (hw : lattice.wellRead R)
    (hd : stableentries.disjSupp F R a b)
    (ha : a.length = R.links) (hb : b.length = R.links) :
    carrier.contentN F (stableentries.joinConf F R a b)
      = carrier.contentN F a + carrier.contentN F b := by
  have hj : carrier.contentN F (stableentries.joinConf F R a b)
      = famFold Nat.add 0 (fun k =>
          if F.eqL (if F.eqL (getAt F.unit a k) F.unit
              then getAt F.unit b k else getAt F.unit a k) F.unit then 0
          else F.c2N (if F.eqL (getAt F.unit a k) F.unit
              then getAt F.unit b k else getAt F.unit a k))
        (List.range R.links) :=
    (contentN_fam F (stableentries.joinConf F R a b)).trans
      (famFold_map Nat.add 0 _ _ (List.range R.links))
  rw [hj, contentN_range F R.links a ha, contentN_range F R.links b hb,
    ← famFold_add_split
      (fun k => if F.eqL (getAt F.unit a k) F.unit then 0
        else F.c2N (getAt F.unit a k))
      (fun k => if F.eqL (getAt F.unit b k) F.unit then 0
        else F.c2N (getAt F.unit b k)) (List.range R.links)]
  refine famFold_congr_members Nat.add 0 _ _ (List.range R.links)
    (fun k hk => ?_)
  have hklt : k < R.links := ground.ltOfMem hk
  cases hak : F.eqL (getAt F.unit a k) F.unit with
  | true =>
    show (if F.eqL (getAt F.unit b k) F.unit then 0
          else F.c2N (getAt F.unit b k))
        = 0 + (if F.eqL (getAt F.unit b k) F.unit then 0
               else F.c2N (getAt F.unit b k))
    rw [Nat.zero_add]
  | false =>
    show (if F.eqL (getAt F.unit a k) F.unit then 0
          else F.c2N (getAt F.unit a k))
        = F.c2N (getAt F.unit a k)
          + (if F.eqL (getAt F.unit b k) F.unit then 0
             else F.c2N (getAt F.unit b k))
    rw [if_neg (boolNe hak),
      if_pos (link_disj F R a b hw hd k hklt hak)]
    rfl

/-! ### The reach at one plaquette -/

/-- A plaquette meets at most one separated component's reach
(`lem:relfiber`(i) at `lem:stableentries`' neighborhood read): at
supports separated beyond the locality band no boundary word of
the region reads both neighborhoods, its shared vertex sitting in
both reach lists otherwise. -/
theorem sepPlaq {L : Type} (F : fusion.Data L) (R : lattice.Region)
    (a b : List L) (hs : grading.sepBeyond F R a b) (i : Nat) :
    ¬ (stableentries.nearPlaq F R a (getAt [] R.plaqs i) = true
      ∧ stableentries.nearPlaq F R b (getAt [] R.plaqs i) = true) := by
  cases Nat.lt_or_ge i R.plaqs.length with
  | inr hge =>
    intro h
    have hnil : getAt ([] : List (Nat × Bool)) R.plaqs i = [] :=
      ground.getAt_over [] R.plaqs i hge
    rw [hnil] at h
    obtain ⟨v, hvm, hvp⟩ := mem_of_any _ (carrier.touched F R a) h.1
    exact Bool.noConfusion hvp
  | inl hi =>
  intro h
  obtain ⟨v, hvm, hvp⟩ := mem_of_any _ (carrier.touched F R a) h.1
  have hvv : v < R.verts :=
    ground.ltOfMemRange (mem_filter_of _ (List.range R.verts) v hvm).1
  have hband : ∀ c : List L,
      stableentries.nearPlaq F R c (getAt [] R.plaqs i) = true →
      v ∈ (List.range R.verts).filter (fun w =>
        R.plaqs.any (fun p =>
          stableentries.nearPlaq F R c p
            && p.any (fun e =>
              lattice.startOf R e == w || lattice.endOf R e == w))) := by
    intro c hc
    refine mem_filter_to _ (ground.memRange hvv) ?_
    refine any_of_mem _ (mem_getAt [] R.plaqs i hi) ?_
    rw [hc, hvp]
    rfl
  have h1 := any_of_mem (fun w => w == v) (hband b h.2) (eqBeqOf rfl)
  have h2 := all_of_mem _ _ hs _ (hband a h.1)
  exact Bool.noConfusion (h1.symm.trans (ground.boolFalseOfNot h2))

/-! ### The folds over a separated class -/

/-- An image at every source member the vacant read is the vacant
list. -/
private theorem filterMap_nil {α β : Type} [DecidableEq α]
    (f : α → Option β) : ∀ l : List α,
    (∀ e, 0 < countOf e l → f e = none) → l.filterMap f = []
  | [], _ => rfl
  | z :: t, h => by
    have hz : f z = none := h z (countOf_pos_of_mem (List.Mem.head t))
    show (match f z with
          | none => t.filterMap f
          | some c => c :: t.filterMap f) = []
    rw [hz]
    exact filterMap_nil f t (fun e he => h e (countOf_cons_pos he))

/-- The unit configuration's incident lists are vacant at the
unit's own equality read. -/
private theorem incid_replicate {L : Type} (F : fusion.Data L)
    (R : lattice.Region)
    (n v : Nat) :
    carrier.incidentLabels F R (List.replicate n F.unit) v = [] := by
  refine filterMap_nil _ (lattice.incident R v) (fun e _ => ?_)
  show (if F.eqL (getAt F.unit (List.replicate n F.unit) e.1) F.unit
        then none
        else if e.2 then some (getAt F.unit (List.replicate n F.unit) e.1)
        else some (F.dual (getAt F.unit (List.replicate n F.unit) e.1)))
      = none
  rw [getAt_replicate_self F.unit n e.1, if_pos (F.eqLRefl F.unit)]

/-- The join's entry at any key: the overlay below the width, the
unit beyond it. -/
private theorem join_entry {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (a b : List L) (k : Nat) :
    getAt F.unit (stableentries.joinConf F R a b) k
      = if k < R.links
        then (if F.eqL (getAt F.unit a k) F.unit
              then getAt F.unit b k else getAt F.unit a k)
        else F.unit := by
  show getAt F.unit ((List.range R.links).map (fun l =>
      let x := getAt F.unit a l
      if F.eqL x F.unit then getAt F.unit b l else x)) k = _
  rw [ground.getAt_map_range F.unit _ R.links k]

/-- An incident read at the vacant value has its entry at the
unit's own read. -/
private theorem entry_unit_of_none {L : Type} (F : fusion.Data L)
    (x : List L) (e : Nat × Bool)
    (h : (if F.eqL (getAt F.unit x e.1) F.unit then none
          else if e.2 then some (getAt F.unit x e.1)
          else some (F.dual (getAt F.unit x e.1))) = (none : Option L)) :
    F.eqL (getAt F.unit x e.1) F.unit = true := by
  cases hq : F.eqL (getAt F.unit x e.1) F.unit with
  | true => rfl
  | false =>
    rw [if_neg (boolNe hq)] at h
    cases he : e.2 with
    | true =>
      rw [if_pos he] at h
      exact nomatch h
    | false =>
      rw [if_neg (boolNe he)] at h
      exact nomatch h

/-- A join's incident list is vacant where both parts' are. -/
private theorem incid_join {L : Type} (F : fusion.Data L)
    (R : lattice.Region)
    (x y : List L) (v : Nat)
    (hx : (carrier.incidentLabels F R x v).length = 0)
    (hy : (carrier.incidentLabels F R y v).length = 0) :
    (carrier.incidentLabels F R (stableentries.joinConf F R x y) v).length
      = 0 := by
  have hnil : carrier.incidentLabels F R
      (stableentries.joinConf F R x y) v = [] := by
    refine filterMap_nil _ (lattice.incident R v) (fun e he => ?_)
    have hxe := entry_unit_of_none F x e
      (ground.filterMap_none _ (lattice.incident R v) hx e he)
    have hye := entry_unit_of_none F y e
      (ground.filterMap_none _ (lattice.incident R v) hy e he)
    show (if F.eqL (getAt F.unit (stableentries.joinConf F R x y) e.1)
            F.unit then none
          else if e.2
            then some (getAt F.unit (stableentries.joinConf F R x y) e.1)
          else some (F.dual
            (getAt F.unit (stableentries.joinConf F R x y) e.1)))
        = none
    rw [join_entry F R x y e.1]
    cases hk : decide (e.1 < R.links) with
    | true =>
      rw [if_pos (of_decide_eq_true hk), if_pos hxe, if_pos hye]
    | false =>
      rw [if_neg (fun hlt => Bool.noConfusion
        (hk.symm.trans (decide_eq_true hlt))), if_pos (F.eqLRefl F.unit)]
  rw [hnil]
  rfl

/-- One component vertex-disjoint from every member of a class,
where its own incidence is occupied, refuses every member's and
the join's with them. -/
private theorem joinAll_incid {L : Type} (F : fusion.Data L)
    (R : lattice.Region)
    (c : List L) : ∀ cs : List (List L), allDisj F R c cs →
    ∀ v, v < R.verts →
    ((carrier.incidentLabels F R c v).length == 0) = false →
    (carrier.incidentLabels F R (joinAll F R cs) v).length = 0
  | [], _, v, _, _ => by
    rw [show joinAll F R ([] : List (List L))
        = List.replicate R.links F.unit from rfl,
      incid_replicate F R R.links v]
    rfl
  | d :: cs, hall, v, hv, hc => by
    have hd : (carrier.incidentLabels F R d v).length = 0 := by
      have hor := all_range_read R.verts hall.1 v hv
      cases orSplitB hor with
      | inl h => exact absurd h (fun h' => Bool.noConfusion (hc.symm.trans h'))
      | inr h => exact beqEqOf h
    exact incid_join F R d (joinAll F R cs) v hd
      (joinAll_incid F R c cs hall.2 v hv hc)

/-- One component vertex-disjoint from every member is disjoint
from the class's join. -/
private theorem disj_joinAll {L : Type} (F : fusion.Data L)
    (R : lattice.Region)
    (c : List L) (cs : List (List L)) (hall : allDisj F R c cs) :
    stableentries.disjSupp F R c (joinAll F R cs) := by
  refine all_range_intro R.verts (fun v hv => ?_)
  cases hc : ((carrier.incidentLabels F R c v).length == 0) with
  | true => rfl
  | false =>
    show ((carrier.incidentLabels F R (joinAll F R cs) v).length == 0)
      = true
    rw [joinAll_incid F R c cs hall v hv hc]
    rfl

/-- The class's join has the region's own width. -/
private theorem joinAll_length {L : Type} (F : fusion.Data L)
    (R : lattice.Region) : ∀ cs : List (List L),
    (joinAll F R cs).length = R.links
  | [] => ground.length_replicate F.unit R.links
  | _ :: _ => ground.length_mapRange _ R.links

/-- The unit configuration's content is the sum's unit at the
unit's own equality read. -/
private theorem contentN_replicate {L : Type} (F : fusion.Data L) :
    ∀ n : Nat, carrier.contentN F (List.replicate n F.unit) = 0
  | 0 => rfl
  | n + 1 => by
    show (List.replicate n F.unit).foldl
      (fun acc l => if F.eqL l F.unit then acc else acc + F.c2N l)
      (if F.eqL F.unit F.unit then 0 else 0 + F.c2N F.unit) = 0
    rw [if_pos (F.eqLRefl F.unit)]
    exact contentN_replicate F n

/-- The content adds over a separated class (`lem:relfiber`(i)'s
electric read at the class): the join's Casimir fold is the
members' folds' sum. -/
theorem contentN_joinAll {L : Type} (F : fusion.Data L)
    (R : lattice.Region)
    (hw : lattice.wellRead R) :
    ∀ cs : List (List L), disjAll F R cs →
    (cs.all (fun c => c.length == R.links)) = true →
    carrier.contentN F (joinAll F R cs)
      = ground.sumNat (cs.map (carrier.contentN F))
  | [], _, _ => contentN_replicate F R.links
  | c :: cs, hdj, hlen => by
    show carrier.contentN F
        (stableentries.joinConf F R c (joinAll F R cs))
      = carrier.contentN F c
        + ground.sumNat (cs.map (carrier.contentN F))
    rw [contentN_join F R c (joinAll F R cs) hw
        (disj_joinAll F R c cs hdj.1)
        (beqEqOf (andSplitB hlen).1) (joinAll_length F R cs),
      contentN_joinAll F R hw cs hdj.2 (andSplitB hlen).2]

/-- A family at every member the refused read filters to the
vacant list. -/
private theorem filter_false {α : Type} [DecidableEq α] (p : α → Bool)
    (l : List α) (h : ∀ e, 0 < countOf e l → p e = false) :
    l.filter p = [] :=
  ground.filter_false p l (fun e he => h e (countOf_pos_of_mem he))

/-- The unit configuration touches no vertex at the unit's own
equality read. -/
private theorem touched_replicate {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (n : Nat) :
    carrier.touched F R (List.replicate n F.unit) = [] := by
  show (List.range R.verts).filter (fun v =>
      (carrier.incidentLabels F R (List.replicate n F.unit) v).length
        != 0) = []
  refine filter_false _ (List.range R.verts) (fun v _ => ?_)
  rw [incid_replicate F R n v]
  rfl

/-- The fiber dimensions multiply over a separated class
(`lem:relfiber`(i)'s factorization at the class): the join's
multiplicity product is the members' products' fold. -/
theorem fibProd_joinAll {L : Type} (F : fusion.Data L)
    (R : lattice.Region) :
    ∀ cs : List (List L), disjAll F R cs →
    windowfinite.fibProd F R (joinAll F R cs)
      = (cs.map (windowfinite.fibProd F R)).foldl (· * ·) 1
  | [], _ => by
    show ground.prodOver
        (carrier.vmult F R (List.replicate R.links F.unit))
        (carrier.touched F R (List.replicate R.links F.unit)) = 1
    rw [touched_replicate F R R.links]
    rfl
  | c :: cs, hdj => by
    show windowfinite.fibProd F R
        (stableentries.joinConf F R c (joinAll F R cs))
      = (cs.map (windowfinite.fibProd F R)).foldl (· * ·)
          (1 * windowfinite.fibProd F R c)
    rw [stableentries.fibProd_join F R c (joinAll F R cs)
        (disj_joinAll F R c cs hdj.1),
      fibProd_joinAll F R cs hdj.2,
      Nat.mul_comm (windowfinite.fibProd F R c)
        ((cs.map (windowfinite.fibProd F R)).foldl (· * ·) 1)]
    exact ground.foldl_mul_seed (fun x y => x * y) Nat.mul_comm
      ground.mulAssoc (fun x => x) (cs.map (windowfinite.fibProd F R))
      1 (windowfinite.fibProd F R c)

/-! ### The stencil row at a separated spectator -/

/-- The separated spectator reads the unit's class on the
boundary's own keys. -/
private theorem far_unit {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (p : List (Nat × Bool)) (b : List L)
    (hw : lattice.wellRead R)
    (hfar : stableentries.nearPlaq F R b p = false)
    (k : Nat) (hk : k < R.links)
    (hkp : (p.any (fun e => e.1 == k)) = true) :
    F.eqL (getAt F.unit b k) F.unit = true := by
  cases hb : F.eqL (getAt F.unit b k) F.unit with
  | true => rfl
  | false =>
    obtain ⟨e, hep, hek⟩ := mem_of_any _ p hkp
    have hek' : e.1 = k := beqEqOf hek
    have hvv : getAt 0 R.tail k < R.verts := (lattice.endLt R hw k hk).1
    have htch : getAt 0 R.tail k ∈ carrier.touched F R b := by
      refine mem_filter_to _ (ground.memRange hvv) ?_
      show (!((carrier.incidentLabels F R b
          (getAt 0 R.tail k)).length == 0)) = true
      rw [ground.neBeqOf (incid_occ F R b k hk hb)]
      rfl
    have hcov : (p.any (fun e' =>
        lattice.startOf R e' == getAt 0 R.tail k
          || lattice.endOf R e' == getAt 0 R.tail k)) = true := by
      refine any_of_mem _ hep ?_
      cases he2 : e.2 with
      | true =>
        show (lattice.startOf R e == getAt 0 R.tail k
          || lattice.endOf R e == getAt 0 R.tail k) = true
        have hst : lattice.startOf R e = getAt 0 R.tail k := by
          show (if e.2 then getAt 0 R.tail e.1
                else getAt 0 R.head e.1) = getAt 0 R.tail k
          rw [if_pos he2, hek']
        rw [hst, eqBeqOf rfl]
        rfl
      | false =>
        show (lattice.startOf R e == getAt 0 R.tail k
          || lattice.endOf R e == getAt 0 R.tail k) = true
        have hen : lattice.endOf R e = getAt 0 R.tail k := by
          show (if e.2 then getAt 0 R.head e.1
                else getAt 0 R.tail e.1) = getAt 0 R.tail k
          rw [if_neg (boolNe he2), hek']
        rw [hen, eqBeqOf rfl]
        cases lattice.startOf R e == getAt 0 R.tail k <;> rfl
    have hnear : stableentries.nearPlaq F R b p = true :=
      any_of_mem _ htch hcov
    exact Bool.noConfusion (hfar.symm.trans hnear)

/-- The join reads the moved part alone on the boundary's keys, the
spectator's labels the unit's own there. -/
private theorem join_far {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (p : List (Nat × Bool)) (a b : List L)
    (hw : lattice.wellRead R)
    (hfar : stableentries.nearPlaq F R b p = false)
    (k : Nat) (hk : k < R.links)
    (hkp : (p.any (fun e => e.1 == k)) = true)
    (hsa : F.eqL (getAt F.unit a k) F.unit = true →
      getAt F.unit a k = F.unit)
    (hsb : F.eqL (getAt F.unit b k) F.unit = true →
      getAt F.unit b k = F.unit) :
    getAt F.unit (stableentries.joinConf F R a b) k
      = getAt F.unit a k := by
  rw [stableentries.join_read F R a b k hk]
  cases ha : F.eqL (getAt F.unit a k) F.unit with
  | false => rw [if_neg (fun h => Bool.noConfusion h)]
  | true =>
    rw [if_pos rfl, hsb (far_unit F R p b hw hfar k hk hkp), hsa ha]

/-- One key's overlay against the spectator: the moved entry where
occupied, the spectator's read at the vacant key. -/
private def ovAt {L : Type} (F : fusion.Data L) (b : List L)
    (k : Nat) (c : L) : L :=
  if F.eqL c F.unit then getAt F.unit b k else c

/-- The target lists at the join read the moved part's own through
the key's overlay. -/
private theorem targets_join {L : Type} [DecidableEq L]
    (F : fusion.Data L)
    (R : lattice.Region) (p : List (Nat × Bool)) (a b : List L)
    (hw : lattice.wellRead R)
    (hfar : stableentries.nearPlaq F R b p = false)
    (k : Nat) (hk : k < R.links)
    (hsa : F.eqL (getAt F.unit a k) F.unit = true →
      getAt F.unit a k = F.unit)
    (hsb : F.eqL (getAt F.unit b k) F.unit = true →
      getAt F.unit b k = F.unit)
    (hsr : ∀ c, 0 < countOf c (algebra.linkTargets F p a k) →
      F.eqL c F.unit = true → c = F.unit) :
    algebra.linkTargets F p (stableentries.joinConf F R a b) k
      = (algebra.linkTargets F p a k).map (ovAt F b k) := by
  cases hkp : (p.any (fun e => e.1 == k)) with
  | true =>
    show (if p.any (fun e => e.1 == k)
          then F.row (getAt F.unit (stableentries.joinConf F R a b) k)
            F.theta
          else [getAt F.unit (stableentries.joinConf F R a b) k])
        = (if p.any (fun e => e.1 == k)
           then F.row (getAt F.unit a k) F.theta
           else [getAt F.unit a k]).map (ovAt F b k)
    rw [hkp, if_pos rfl, if_pos rfl,
      join_far F R p a b hw hfar k hk hkp hsa hsb]
    have hbk : getAt F.unit b k = F.unit :=
      hsb (far_unit F R p b hw hfar k hk hkp)
    have hsr' : ∀ c, 0 < countOf c (F.row (getAt F.unit a k) F.theta) →
        F.eqL c F.unit = true → c = F.unit := by
      intro c hc
      refine hsr c ?_
      show 0 < countOf c (if p.any (fun e => e.1 == k)
        then F.row (getAt F.unit a k) F.theta
        else [getAt F.unit a k])
      rw [hkp, if_pos rfl]
      exact hc
    have hov : ∀ c, 0 < countOf c (F.row (getAt F.unit a k) F.theta) →
        ovAt F b k c = (fun c => c) c := by
      intro c hc
      show (if F.eqL c F.unit then getAt F.unit b k else c) = c
      cases hcq : F.eqL c F.unit with
      | true => rw [if_pos rfl, hbk, hsr' c hc hcq]
      | false => rw [if_neg (fun h => Bool.noConfusion h)]
    rw [ground.map_congr_members (ovAt F b k) (fun c => c)
      (F.row (getAt F.unit a k) F.theta) hov, map_id]
  | false =>
    show (if p.any (fun e => e.1 == k)
          then F.row (getAt F.unit (stableentries.joinConf F R a b) k)
            F.theta
          else [getAt F.unit (stableentries.joinConf F R a b) k])
        = (if p.any (fun e => e.1 == k)
           then F.row (getAt F.unit a k) F.theta
           else [getAt F.unit a k]).map (ovAt F b k)
    rw [hkp, if_neg (fun h => Bool.noConfusion h),
      if_neg (fun h => Bool.noConfusion h)]
    show [getAt F.unit (stableentries.joinConf F R a b) k]
      = [ovAt F b k (getAt F.unit a k)]
    rw [join_entry F R a b k, if_pos hk]
    rfl

/-- The positional overlay over a key list. -/
private def ovK {L : Type} (F : fusion.Data L) (b : List L) :
    List Nat → List L → List L
  | [], _ => []
  | _ :: _, [] => []
  | k :: K, c :: t => ovAt F b k c :: ovK F b K t

/-- The fold at the join is the fold at the moved part, target by
target through the overlay. -/
private theorem fold_join {L : Type} [DecidableEq L]
    (F : fusion.Data L)
    (R : lattice.Region) (p : List (Nat × Bool)) (a b : List L)
    (hw : lattice.wellRead R)
    (hfar : stableentries.nearPlaq F R b p = false)
    (hs : ∀ k, k < R.links →
      (F.eqL (getAt F.unit a k) F.unit = true →
        getAt F.unit a k = F.unit)
      ∧ (F.eqL (getAt F.unit b k) F.unit = true →
        getAt F.unit b k = F.unit)
      ∧ ∀ c, 0 < countOf c (algebra.linkTargets F p a k) →
        F.eqL c F.unit = true → c = F.unit) :
    ∀ K : List Nat, (∀ k, 0 < countOf k K → k < R.links) →
    ground.prodLists (K.map (algebra.linkTargets F p (stableentries.joinConf F R a b)))
      = (ground.prodLists (K.map (algebra.linkTargets F p a))).map (ovK F b K)
  | [], _ => rfl
  | k :: K, hK => by
    have hk : k < R.links :=
      hK k (countOf_pos_of_mem (List.Mem.head K))
    have hIH := fold_join F R p a b hw hfar hs K
      (fun j hj => hK j (countOf_cons_pos hj))
    show (List.flatMap
        (fun c => (ground.prodLists (K.map (algebra.linkTargets F p (stableentries.joinConf F R a b)))).map
          (fun t => c :: t))
        (algebra.linkTargets F p (stableentries.joinConf F R a b) k))
      = (ground.prodLists ((k :: K).map (algebra.linkTargets F p a))).map
          (ovK F b (k :: K))
    rw [targets_join F R p a b hw hfar k hk (hs k hk).1
        (hs k hk).2.1 (hs k hk).2.2, hIH,
      ground.flatMap_map]
    have hstep : ∀ c : L,
        (((ground.prodLists (K.map (algebra.linkTargets F p a))).map
          (ovK F b K)).map (fun t => ovAt F b k c :: t))
        = ((ground.prodLists (K.map (algebra.linkTargets F p a))).map
          (fun t => ovAt F b k c :: ovK F b K t)) :=
      fun c => ground.map_map _ _ _
    rw [ground.flatMap_congr_all _ _ hstep (algebra.linkTargets F p a k)]
    show _ = ((algebra.linkTargets F p a k).flatMap (fun c =>
        (ground.prodLists (K.map (algebra.linkTargets F p a))).map
          (fun t => c :: t))).map (ovK F b (k :: K))
    rw [ground.map_flatMap]
    refine (ground.flatMap_congr_all _ _ (fun c => ?_)
      (algebra.linkTargets F p a k)).symm
    show ((ground.prodLists (K.map (algebra.linkTargets F p a))).map
        (fun t => c :: t)).map (ovK F b (k :: K))
      = (ground.prodLists (K.map (algebra.linkTargets F p a))).map
          (fun t => ovAt F b k c :: ovK F b K t)
    exact ground.map_map _ _ _

/-- A true read at every occupied member folds to true. -/
private theorem all_pos {α : Type} [DecidableEq α] (f : α → Bool) :
    ∀ l : List α, (∀ e, 0 < countOf e l → f e = true) →
    l.all f = true
  | [], _ => rfl
  | z :: t, h => by
    show (f z && t.all f) = true
    rw [h z (countOf_pos_of_mem (List.Mem.head t)),
      all_pos f t (fun e he => h e (countOf_cons_pos he))]
    rfl

/-- The overlay keeps the width. -/
private theorem ovK_length {L : Type} (F : fusion.Data L)
    (b : List L) : ∀ (K : List Nat) (t : List L),
    t.length = K.length → (ovK F b K t).length = K.length
  | [], [], _ => rfl
  | [], _ :: _, hl => Nat.noConfusion hl
  | _ :: _, [], hl => Nat.noConfusion hl
  | k :: K, c :: t, hl => by
    show (ovK F b K t).length + 1 = K.length + 1
    rw [ovK_length F b K t (Nat.succ.inj hl)]

/-- The overlay's entry at a key. -/
private theorem getAt_ovK {L : Type} (F : fusion.Data L)
    (b : List L) : ∀ (K : List Nat) (t : List L) (j : Nat),
    j < K.length → t.length = K.length →
    getAt F.unit (ovK F b K t) j
      = ovAt F b (getAt 0 K j) (getAt F.unit t j)
  | [], _, j, hj, _ => absurd hj (Nat.not_lt_zero j)
  | _ :: _, [], _, _, hl => Nat.noConfusion hl
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: K, _ :: t, j + 1, hj, hl =>
    getAt_ovK F b K t j (Nat.lt_of_succ_lt_succ hj)
      (Nat.succ.inj hl)

/-- The join against the spectator is the key range's overlay. -/
private theorem join_ov {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (t b : List L) (htl : t.length = R.links) :
    stableentries.joinConf F R t b
      = ovK F b (List.range R.links) t := by
  have hlr : t.length = (List.range R.links).length := by
    rw [ground.length_range]
    exact htl
  refine getAt_ext F.unit _ _ ?_ (fun j hj => ?_)
  · show ((List.range R.links).map _).length
      = (ovK F b (List.range R.links) t).length
    rw [ground.length_map,
      ovK_length F b (List.range R.links) t hlr]
  · have hjl : j < R.links := by
      have : ((List.range R.links).map (fun l =>
          let x := getAt F.unit t l
          if F.eqL x F.unit then getAt F.unit b l else x)).length
          = R.links :=
        ground.length_mapRange _ R.links
      rw [show (stableentries.joinConf F R t b).length = R.links
        from this] at hj
      exact hj
    rw [join_entry F R t b j, if_pos hjl,
      getAt_ovK F b (List.range R.links) t j
        (by rw [ground.length_range]; exact hjl) hlr,
      ground.getAt_range R.links j hjl]
    rfl

/-- A touched vertex of one part is touched at the join. -/
private theorem touched_join {L : Type} [DecidableEq L]
    (F : fusion.Data L)
    (R : lattice.Region) (t b : List L) (v : Nat)
    (hocc : ((carrier.incidentLabels F R t v).length != 0) = true) :
    ((carrier.incidentLabels F R
      (stableentries.joinConf F R t b) v).length != 0) = true := by
  cases hl : carrier.incidentLabels F R t v with
  | nil => rw [hl] at hocc; exact Bool.noConfusion hocc
  | cons m rest =>
    have hpos : 0 < countOf m (carrier.incidentLabels F R t v) := by
      rw [hl, countOf_head]
      exact Nat.succ_pos _
    obtain ⟨e, he, hfe⟩ := ground.filterMap_pre _
      (lattice.incident R v) m hpos
    have helt : e.1 < R.links := stableentries.incident_lt R v e he
    have htne : F.eqL (getAt F.unit t e.1) F.unit = false := by
      cases hq : F.eqL (getAt F.unit t e.1) F.unit with
      | false => rfl
      | true =>
        rw [show (if F.eqL (getAt F.unit t e.1) F.unit then none
            else if e.2 then some (getAt F.unit t e.1)
            else some (F.dual (getAt F.unit t e.1)))
          = (none : Option L) from by rw [if_pos hq]] at hfe
        exact nomatch hfe
    have hje : getAt F.unit (stableentries.joinConf F R t b) e.1
        = getAt F.unit t e.1 := by
      rw [stableentries.join_read F R t b e.1 helt,
        if_neg (boolNe htne)]
    have hjf : (fun e' : Nat × Bool =>
        if F.eqL (getAt F.unit (stableentries.joinConf F R t b) e'.1)
            F.unit then none
        else if e'.2
          then some (getAt F.unit (stableentries.joinConf F R t b) e'.1)
        else some (F.dual (getAt F.unit
          (stableentries.joinConf F R t b) e'.1))) e
        = some (if e.2 then getAt F.unit t e.1
            else F.dual (getAt F.unit t e.1)) := by
      show (if F.eqL (getAt F.unit (stableentries.joinConf F R t b) e.1)
            F.unit then none
          else if e.2
            then some (getAt F.unit (stableentries.joinConf F R t b) e.1)
          else some (F.dual (getAt F.unit
            (stableentries.joinConf F R t b) e.1))) = _
      rw [hje, if_neg (boolNe htne)]
      cases he2 : e.2 with
      | true => rw [if_pos rfl, if_pos rfl]
      | false =>
        rw [if_neg (fun h => Bool.noConfusion h),
          if_neg (fun h => Bool.noConfusion h)]
    have hocc' := filterMap_occ (fun e' : Nat × Bool =>
        if F.eqL (getAt F.unit (stableentries.joinConf F R t b) e'.1)
            F.unit then none
        else if e'.2
          then some (getAt F.unit (stableentries.joinConf F R t b) e'.1)
        else some (F.dual (getAt F.unit
          (stableentries.joinConf F R t b) e'.1)))
      (lattice.incident R v) e
      (if e.2 then getAt F.unit t e.1
       else F.dual (getAt F.unit t e.1)) he hjf
    cases hz : (carrier.incidentLabels F R
        (stableentries.joinConf F R t b) v).length with
    | zero => exact absurd hz hocc'
    | succ n => rfl

/-- The join's occupancy at an occupied spectator is the moved
part's own. -/
private theorem occ_join {L : Type} [DecidableEq L]
    (F : fusion.Data L)
    (R : lattice.Region) (t b : List L)
    (hd2 : stableentries.disjSupp F R t b)
    (hob : carrier.occupied F R b = true) :
    carrier.occupied F R (stableentries.joinConf F R t b)
      = carrier.occupied F R t := by
  cases hot : carrier.occupied F R t with
  | true =>
    refine all_pos _ (carrier.touched F R
      (stableentries.joinConf F R t b)) (fun v hvp => ?_)
    have hvm := mem_of_countOf_pos v _ hvp
    have hvr : v < R.verts :=
      ground.ltOfMemRange (mem_filter_of _ (List.range R.verts) v hvm).1
    rw [show carrier.vmult F R (stableentries.joinConf F R t b) v
        = carrier.vmult F R t v * carrier.vmult F R b v
      from stableentries.vmult_join F R t b hd2 v hvr]
    exact decide_eq_true (Nat.mul_pos (carrier.vmult_pos F R t v hvr hot)
      (carrier.vmult_pos F R b v hvr hob))
  | false =>
    cases hoj : carrier.occupied F R
        (stableentries.joinConf F R t b) with
    | false => rfl
    | true =>
      have hcontra : carrier.occupied F R t = true := by
        refine all_pos _ (carrier.touched F R t) (fun v hvp => ?_)
        have hvm := mem_of_countOf_pos v _ hvp
        have hsplit := mem_filter_of _ (List.range R.verts) v hvm
        have hvr : v < R.verts := ground.ltOfMemRange hsplit.1
        have hvj := touched_join F R t b v hsplit.2
        have hmj : v ∈ carrier.touched F R
            (stableentries.joinConf F R t b) :=
          mem_filter_to _ (ground.memRange hvr) hvj
        have hpj : 0 < carrier.vmult F R
            (stableentries.joinConf F R t b) v :=
          of_decide_eq_true (all_of_mem (fun w => decide (0 <
            carrier.vmult F R (stableentries.joinConf F R t b) w))
            _ hoj _ hmj)
        rw [stableentries.vmult_join F R t b hd2 v hvr] at hpj
        refine decide_eq_true ?_
        cases hmt : carrier.vmult F R t v with
        | zero =>
          rw [hmt, Nat.zero_mul] at hpj
          exact absurd hpj (Nat.lt_irrefl 0)
        | succ n => exact Nat.succ_pos n
      exact Bool.noConfusion (hot.symm.trans hcontra)

/-- The join of an occupied target reads occupied entries. -/
private theorem any_join {L : Type} (F : fusion.Data L)
    (R : lattice.Region) (t b : List L) (htl : t.length = R.links)
    (htn : (t.any (fun m => !(F.eqL m F.unit))) = true) :
    ((stableentries.joinConf F R t b).any
      (fun m => !(F.eqL m F.unit))) = true := by
  obtain ⟨m, hm, hf⟩ := mem_of_any _ t htn
  obtain ⟨j, hj, hg⟩ := ground.getAt_of_mem F.unit hm
  have hjl : j < R.links := by
    rw [← htl]
    exact hj
  have hje : getAt F.unit (stableentries.joinConf F R t b) j = m := by
    rw [stableentries.join_read F R t b j hjl, hg,
      if_neg (boolNe (ground.boolFalseOfNot hf))]
  have hlj : j < (stableentries.joinConf F R t b).length := by
    show j < ((List.range R.links).map _).length
    rw [ground.length_mapRange]
    exact hjl
  have hmem : getAt F.unit (stableentries.joinConf F R t b) j
      ∈ stableentries.joinConf F R t b :=
    mem_getAt F.unit (stableentries.joinConf F R t b) j hlj
  rw [hje] at hmem
  exact any_of_mem _ hmem hf

/-- An occupied member's positive read floors the family fold. -/
private theorem famFold_pos_of {α : Type} [DecidableEq α]
    (g : α → Nat) : ∀ (l : List α) (x : α),
    0 < countOf x l → 0 < g x → 0 < famFold Nat.add 0 g l
  | [], x, hx, _ => absurd hx (Nat.lt_irrefl 0)
  | z :: t, x, hx, hg => by
    show 0 < g z + famFold Nat.add 0 g t
    by_cases hxz : x = z
    · refine Nat.add_pos_left ?_ _
      rw [← hxz]
      exact hg
    · rw [countOf_head_ne hxz] at hx
      exact Nat.add_pos_right _ (famFold_pos_of g t x hx hg)

/-- The stencil row at a separated occupied spectator
(`lem:relfiber`(i)'s row read): the joined class's row counts a
joined target at the moved part's own row count, the spectator
riding every target. -/
theorem plaqRow_join {L : Type} [DecidableEq L] (F : fusion.Data L)
    (R : lattice.Region) (p : List (Nat × Bool)) (a b t : List L)
    (hw : lattice.wellRead R)
    (hd : stableentries.disjSupp F R a b)
    (hd2 : stableentries.disjSupp F R t b)
    (hsnd : fusion.oneUnit F (a ++ b ++ t
      ++ (List.range R.links).flatMap
        (fun k => algebra.linkTargets F p a k)))
    (hfar : stableentries.nearPlaq F R b p = false)
    (hob : carrier.occupied F R b = true)
    (ha : a.length = R.links) (hb : b.length = R.links)
    (htl : t.length = R.links)
    (htn : (t.any (fun m => !(F.eqL m F.unit))) = true) :
    countOf (stableentries.joinConf F R t b)
        (algebra.plaqRow F R p (stableentries.joinConf F R a b))
      = countOf t (algebra.plaqRow F R p a) := by
  have hcov : ∀ x, 0 < countOf x (a ++ b ++ t
      ++ (List.range R.links).flatMap
        (fun k => algebra.linkTargets F p a k)) →
      F.eqL x F.unit = true → x = F.unit :=
    fusion.oneUnit_read F _ hsnd
  have hsA : ∀ k, k < R.links →
      F.eqL (getAt F.unit a k) F.unit = true →
      getAt F.unit a k = F.unit := by
    intro k hk hq
    refine hcov _ ?_ hq
    rw [ground.countOf_append, ground.countOf_append,
      ground.countOf_append]
    exact Nat.add_pos_left (Nat.add_pos_left
      (Nat.add_pos_left (countOf_pos_of_mem
        (mem_getAt F.unit a k (by rw [ha]; exact hk))) _) _) _
  have hsB : ∀ k, k < R.links →
      F.eqL (getAt F.unit b k) F.unit = true →
      getAt F.unit b k = F.unit := by
    intro k hk hq
    refine hcov _ ?_ hq
    rw [ground.countOf_append, ground.countOf_append,
      ground.countOf_append]
    exact Nat.add_pos_left (Nat.add_pos_left
      (Nat.add_pos_right _ (countOf_pos_of_mem
        (mem_getAt F.unit b k (by rw [hb]; exact hk)))) _) _
  have hsT : ∀ k, k < R.links →
      F.eqL (getAt F.unit t k) F.unit = true →
      getAt F.unit t k = F.unit := by
    intro k hk hq
    refine hcov _ ?_ hq
    rw [ground.countOf_append, ground.countOf_append,
      ground.countOf_append]
    exact Nat.add_pos_left (Nat.add_pos_right _
      (countOf_pos_of_mem
        (mem_getAt F.unit t k (by rw [htl]; exact hk)))) _
  have hsRow : ∀ k, k < R.links →
      ∀ c, 0 < countOf c (algebra.linkTargets F p a k) →
      F.eqL c F.unit = true → c = F.unit := by
    intro k hk c hc hq
    refine hcov _ ?_ hq
    rw [ground.countOf_append]
    refine Nat.add_pos_right _ ?_
    rw [ground.countOf_flatMap]
    exact famFold_pos_of _ (List.range R.links) k
      (countOf_pos_of_mem (ground.memRange hk)) hc
  have hfold := fold_join F R p a b hw hfar
    (fun k hk => ⟨hsA k hk, hsB k hk, hsRow k hk⟩)
    (List.range R.links) (fun k hk => ground.ltOfMem hk)
  have hinj : ∀ y, 0 < countOf y (ground.prodLists ((List.range R.links).map (algebra.linkTargets F p a))) →
      ovK F b (List.range R.links) y
        = ovK F b (List.range R.links) t → y = t := by
    intro y hyf hov
    have hylen : y.length = R.links := by
      have hpl := (ground.mem_prodLists_of F.unit _ y
        (mem_of_countOf_pos y _ hyf)).1
      rw [ground.length_map, ground.length_range] at hpl
      exact hpl
    refine getAt_ext F.unit y t (by rw [hylen, htl]) (fun j hjy => ?_)
    have hjl : j < R.links := by
      rw [← hylen]
      exact hjy
    have hjr : j < (List.range R.links).length := by
      rw [ground.length_range]
      exact hjl
    have hyr : y.length = (List.range R.links).length := by
      rw [ground.length_range]
      exact hylen
    have htr : t.length = (List.range R.links).length := by
      rw [ground.length_range]
      exact htl
    have hoveq : ovAt F b j (getAt F.unit y j)
        = ovAt F b j (getAt F.unit t j) := by
      have h1 := congrArg (fun l => getAt F.unit l j) hov
      have h2 : getAt F.unit (ovK F b (List.range R.links) y) j
          = getAt F.unit (ovK F b (List.range R.links) t) j := h1
      rw [getAt_ovK F b (List.range R.links) y j hjr hyr,
        getAt_ovK F b (List.range R.links) t j hjr htr,
        ground.getAt_range R.links j hjl] at h2
      exact h2
    have hpk := algebra.prodKeep F p a (List.range R.links) y hyf j hjr
    rw [ground.getAt_range R.links j hjl] at hpk
    have hsY : F.eqL (getAt F.unit y j) F.unit = true →
        getAt F.unit y j = F.unit :=
      fun hq => hsRow j hjl _ hpk hq
    have hbunit : (p.any (fun e => e.1 == j)) = false →
        F.eqL (getAt F.unit y j) F.unit = false →
        F.eqL (getAt F.unit b j) F.unit = true := by
      intro hkp hyq
      have hsing : algebra.linkTargets F p a j = [getAt F.unit a j] := by
        show (if p.any (fun e => e.1 == j)
              then F.row (getAt F.unit a j) F.theta
              else [getAt F.unit a j]) = [getAt F.unit a j]
        rw [hkp, if_neg (fun h => Bool.noConfusion h)]
      have hpk' := hpk
      rw [hsing] at hpk'
      have hya : getAt F.unit y j = getAt F.unit a j :=
        ground.countOf_single hpk'
      rw [hya] at hyq
      exact link_disj F R a b hw hd j hjl hyq
    cases hyq : F.eqL (getAt F.unit y j) F.unit with
    | false =>
      cases htq : F.eqL (getAt F.unit t j) F.unit with
      | false =>
        have h3 := hoveq
        rw [show ovAt F b j (getAt F.unit y j) = getAt F.unit y j
            from by
              show (if F.eqL (getAt F.unit y j) F.unit
                then getAt F.unit b j else getAt F.unit y j) = _
              rw [if_neg (boolNe hyq)],
          show ovAt F b j (getAt F.unit t j) = getAt F.unit t j
            from by
              show (if F.eqL (getAt F.unit t j) F.unit
                then getAt F.unit b j else getAt F.unit t j) = _
              rw [if_neg (boolNe htq)]] at h3
        exact h3
      | true =>
        have h3 := hoveq
        rw [show ovAt F b j (getAt F.unit y j) = getAt F.unit y j
            from by
              show (if F.eqL (getAt F.unit y j) F.unit
                then getAt F.unit b j else getAt F.unit y j) = _
              rw [if_neg (boolNe hyq)],
          show ovAt F b j (getAt F.unit t j) = getAt F.unit b j
            from by
              show (if F.eqL (getAt F.unit t j) F.unit
                then getAt F.unit b j else getAt F.unit t j) = _
              rw [if_pos htq]] at h3
        have hbu : getAt F.unit b j = F.unit := by
          cases hkp : (p.any (fun e => e.1 == j)) with
          | true => exact hsB j hjl (far_unit F R p b hw hfar j hjl hkp)
          | false => exact hsB j hjl (hbunit hkp hyq)
        rw [h3, hbu, hsT j hjl htq]
    | true =>
      cases htq : F.eqL (getAt F.unit t j) F.unit with
      | true => rw [hsY hyq, hsT j hjl htq]
      | false =>
        have h3 := hoveq
        rw [show ovAt F b j (getAt F.unit y j) = getAt F.unit b j
            from by
              show (if F.eqL (getAt F.unit y j) F.unit
                then getAt F.unit b j else getAt F.unit y j) = _
              rw [if_pos hyq],
          show ovAt F b j (getAt F.unit t j) = getAt F.unit t j
            from by
              show (if F.eqL (getAt F.unit t j) F.unit
                then getAt F.unit b j else getAt F.unit t j) = _
              rw [if_neg (boolNe htq)]] at h3
        have hbu : getAt F.unit b j = F.unit :=
          hsB j hjl (link_disj F R t b hw hd2 j hjl htq)
        rw [hsY hyq, ← h3, hbu]
  show countOf (stableentries.joinConf F R t b)
      ((ground.prodLists ((List.range R.links).map (algebra.linkTargets F p (stableentries.joinConf F R a b)))).filter
        (fun s => (s.any (fun m => !(F.eqL m F.unit)))
          && carrier.occupied F R s))
    = countOf t ((ground.prodLists ((List.range R.links).map (algebra.linkTargets F p a))).filter
        (fun s => (s.any (fun m => !(F.eqL m F.unit)))
          && carrier.occupied F R s))
  rw [hfold, ground.filter_map, join_ov F R t b htl,
    ground.countOf_map_inj (ovK F b (List.range R.links)) t _
      (fun y hy hovy => hinj y (by
        rw [countOf_filter] at hy
        cases hq : ((ovK F b (List.range R.links) y).any
            (fun m => !(F.eqL m F.unit))
            && carrier.occupied F R (ovK F b (List.range R.links) y)) with
        | true =>
          rw [if_pos hq] at hy
          exact hy
        | false =>
          rw [if_neg (boolNe hq)] at hy
          exact absurd hy (Nat.lt_irrefl 0)) hovy),
    countOf_filter, countOf_filter, ← join_ov F R t b htl]
  have hq2 : ((stableentries.joinConf F R t b).any
      (fun m => !(F.eqL m F.unit))
      && carrier.occupied F R (stableentries.joinConf F R t b))
    = ((t.any (fun m => !(F.eqL m F.unit)))
      && carrier.occupied F R t) := by
    rw [any_join F R t b htl htn, htn,
      occ_join F R t b hd2 hob]
  rw [hq2]

end relfiber
