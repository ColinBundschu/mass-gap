import MassGap.Speccut
import MassGap.Levelequiv
/-!
`lem:attained` at the window matrices — the edge is the compressed
pair's least root, read at the spectral read with a named edge root
(`edgeRead`, clause (i)'s located edge: every root at the kernel
point or at or beyond the edge with a root at the edge itself), the
eigen column's two moments read equal members there with the first
strictly above the sum's unit (`moment_eq`, clause (ii); the eigen
column is `lem:split`'s kernel-block column at the located root, a
word image at the filled window, `lem:sectorspan`), and the weight
reading (clause (iii)): an occupied weight sits at the kernel point
or at the level exactly (`weights_at`), and a first moment strictly
above the sum's unit puts an occupied weight at the level
(`weight_occupied`), the weights the congruence coordinates'
squares against the certificate Gram's diagonal entries; and the
probe cap (clause (iv)): a probe whose two moments read the pair
`(μ₂ : γ μ₁)` on its lower side refuses the spectral read at the
level, a located root sitting off the kernel point below it
(`probe_cap`, `levelequiv.probe_intro` against
`speccut.spec_to_cut`).

The moments are `thm:momentform`'s quadratic reads at the carrier,
`inertia.quadForm` at the gap and at its square; the reads run at
the unit gram, the committed loop windows' own.
-/

namespace attained
open ground elim inertia split

/-- The spectral read with a named edge: every located root at the
kernel point or at or beyond the edge, and a root at the edge
itself — clause (i)'s located edge, the compressed pair's least
root. -/
def edgeRead (roots : List (BPair × Pos)) (E0 p q : Pos) : Prop :=
  speccut.specRead roots E0 p q
    ∧ (roots.any (fun r =>
        decide ((r.1.scale q).oneValue
          (BPair.ofPos (E0 * p * r.2))))) = true

instance (roots : List (BPair × Pos)) (E0 p q : Pos) :
    Decidable (edgeRead roots E0 p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The per-root read at an equal-membered weighted pair: at a root
off the kernel point and an occupied weight the two clearings' equal
members put the root at the edge. -/
private theorem edgeOfTerm {vj kj wj nj gj : BPair} {dj E0 p q : Pos}
    (hgpos : BPair.unit < gj) (hwoff : ¬ wj.oneValue BPair.unit)
    (hz : ¬ nj.oneValue BPair.unit)
    (hv : vj.oneValue (nj * gj))
    (hk : (BPair.ofPos dj * kj).oneValue (nj * (nj * gj)))
    (heq : ((vj * wj).scale (E0 * p)).oneValue ((kj * wj).scale q)) :
    (nj.scale q).oneValue (BPair.ofPos (E0 * p * dj)) := by
  have hKoff : ¬ (gj * wj).oneValue BPair.unit := fun h =>
    match (BPair.mul_unit_iff gj wj).mp h with
    | Or.inl hg => ground.offOfUnitLt hgpos hg
    | Or.inr hw => hwoff hw
  have h1 : (BPair.ofPos dj * (vj * wj).scale (E0 * p)).oneValue
      (BPair.ofPos dj * (kj * wj).scale q) :=
    BPair.mul_congr (BPair.oneValue_refl _) heq
  rw [BPair.mul_scale (BPair.ofPos dj) (vj * wj) (E0 * p),
    BPair.mul_scale (BPair.ofPos dj) (kj * wj) q] at h1
  have h2 : ((BPair.ofPos dj * (vj * wj)).scale (E0 * p)).oneValue
      (((nj * BPair.ofPos dj).scale (E0 * p)) * (gj * wj)) := by
    refine BPair.oneValue_trans (BPair.scale_congr (E0 * p)
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos dj))
        (BPair.mul_congr_left hv))) ?_
    rw [show BPair.ofPos dj * (nj * gj * wj)
        = nj * BPair.ofPos dj * (gj * wj) from by
      rw [BPair.mul_assoc nj gj wj,
        BPair.mul_left_comm (BPair.ofPos dj) nj (gj * wj),
        BPair.mul_assoc nj (BPair.ofPos dj) (gj * wj)]]
    exact BPair.oneValue_of_eq
      (BPair.scale_mul_left (nj * BPair.ofPos dj) (gj * wj) (E0 * p))
  have h3 : ((BPair.ofPos dj * (kj * wj)).scale q).oneValue
      (((nj * nj).scale q) * (gj * wj)) := by
    rw [show BPair.ofPos dj * (kj * wj) = BPair.ofPos dj * kj * wj from
      (BPair.mul_assoc (BPair.ofPos dj) kj wj).symm]
    refine BPair.oneValue_trans (BPair.scale_congr q
      (BPair.mul_congr_left hk)) ?_
    rw [show nj * (nj * gj) * wj = nj * nj * (gj * wj) from by
      rw [BPair.mul_assoc nj (nj * gj) wj, BPair.mul_assoc nj gj wj,
        BPair.mul_assoc nj nj (gj * wj)]]
    exact BPair.oneValue_of_eq
      (BPair.scale_mul_left (nj * nj) (gj * wj) q)
  have h4 := BPair.oneValue_trans (BPair.oneValue_symm h2)
    (BPair.oneValue_trans h1 h3)
  rw [BPair.mul_comm ((nj * BPair.ofPos dj).scale (E0 * p)) (gj * wj),
    BPair.mul_comm ((nj * nj).scale q) (gj * wj)] at h4
  have h5 := ground.mulCancel hKoff h4
  rw [← BPair.mul_scale nj (BPair.ofPos dj) (E0 * p),
    ← BPair.mul_scale nj nj q] at h5
  have h6 := ground.mulCancel hz h5
  refine BPair.oneValue_trans (BPair.oneValue_symm h6) ?_
  refine BPair.oneValue_trans (BPair.scale_ofPos dj (E0 * p)) ?_
  rw [ground.mul_comm dj (E0 * p)]
  exact BPair.oneValue_refl _

/-! The moments at a vector of the order, read through the
congruence: the diagonalizing congruence's adjugate witness carries
the vector to the congruated coordinates, the two forms there are
the congruated diagonals' own square-weighted folds at the
determinant's square, and the spectral read prices every summand of
the first fold against the second's. -/

/-- The gap's fold at the congruated coordinates is the form at the
vector under the determinant's square. -/
private theorem foldV {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (y : List BPair) (hy : y.length = n) :
    (dotP (split.vDiagL Et T)
        (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y))).oneValue
      (minor T.val * minor T.val * inertia.quadForm Et y) := by
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hd.1
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hcl : (matVec Tw.val y).length = n := by rw [matVec_length, hTwl]
  exact BPair.oneValue_trans
    (BPair.oneValue_symm
      (split.quadFoldV Et T Tw l hd (matVec Tw.val y) hcl))
    (inertia.quadScaleVec Et (minor T.val) y _
      (split.adjAct Et T Tw l hd y hy))

/-- The squared gap's fold at the congruated coordinates is the
form at the vector under the determinant's square. -/
private theorem foldK {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (y : List BPair) (hy : y.length = n) :
    (dotP (split.vDiagL (matMul Et Et) T)
        (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y))).oneValue
      (minor T.val * minor T.val
        * inertia.quadForm (matMul Et Et) y) := by
  have hEt : sqAt Et n := hd.1
  have hEtl : Et.length = n := sqAt_len hEt
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_cast (transposeLen Et hEtr hEtl) (rowsLen_matMul Et Et)
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hcl : (matVec Tw.val y).length = n := by rw [matVec_length, hTwl]
  exact BPair.oneValue_trans
    (BPair.oneValue_symm
      (split.quadFoldK Et T Tw l hd (matVec Tw.val y) hcl))
    (inertia.quadScaleVec (matMul Et Et) (minor T.val) y _
      (split.adjAct Et T Tw l hd y hy))

/-- The two folds' equal-membered read at the two clearings, the
moments' own at the vector. -/
private theorem foldEq {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (y : List BPair) (hy : y.length = n)
    (hmom : ((inertia.quadForm (matMul Et Et) y).scale q).oneValue
      ((inertia.quadForm Et y).scale (E0 * p))) :
    ((dotP (split.vDiagL Et T)
        (List.zipWith (· * ·) (matVec Tw.val y)
          (matVec Tw.val y))).scale (E0 * p)).oneValue
      ((dotP (split.vDiagL (matMul Et Et) T)
        (List.zipWith (· * ·) (matVec Tw.val y)
          (matVec Tw.val y))).scale q) := by
  have hV := foldV Et T Tw l hd y hy
  have hK := foldK Et T Tw l hd y hy
  refine BPair.oneValue_trans (BPair.scale_congr (E0 * p) hV) ?_
  refine BPair.oneValue_trans ?_
    (BPair.scale_congr q (BPair.oneValue_symm hK))
  rw [← BPair.mul_scale (minor T.val * minor T.val)
      (inertia.quadForm Et y) (E0 * p),
    ← BPair.mul_scale (minor T.val * minor T.val)
      (inertia.quadForm (matMul Et Et) y) q]
  exact BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hmom)

/-- The gap's fold at the congruated coordinates sits strictly above
the sum's unit at a first moment strictly above it. -/
private theorem foldPos {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (y : List BPair) (hy : y.length = n)
    (hpos : BPair.unit < inertia.quadForm Et y) :
    BPair.unit < dotP (split.vDiagL Et T)
      (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y)) := by
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm (foldV Et T Tw l hd y hy))
    (ground.unitLtMul (ground.sq_pos hdet) hpos)

/-- Every summand of the gap's fold sits at or above the sum's
unit, the located roots' own sides. -/
private theorem foldUnitLe {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : speccut.specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (c : List BPair) (hc : c.length = n) :
    ∀ j, j < (split.vDiagL Et T).length →
      BPair.unit ≤ ground.getAt BPair.unit (split.vDiagL Et T) j
        * ground.getAt BPair.unit (List.zipWith (· * ·) c c) j := by
  intro j hjv
  rw [split.vDiagL_len] at hjv
  have hcj : j < c.length := by rw [hc]; exact hjv
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hjv
  rw [ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·) c c j
      hcj hcj,
    split.vDiagL_get Et T j hjv]
  refine ground.unitLeMul ?_ (ground.unitLeSq _)
  refine ground.leB_congr_right
    (BPair.oneValue_symm
      (split.diagEntryV Et T Tw l hd j hjv _ _ _ rfl)) ?_
  exact ground.unitLeMul
    (rootUnitLe (speccut.specGet l E0 p q hs j hjl _ _ _ rfl))
    (ground.leB_of_lt (split.scalePos Et T Tw l hd j hjl _ _ _ rfl))

/-- At a root off the kernel point with an occupied weight the two
moments' equal members put the root at the edge. -/
private theorem edgeAt {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : speccut.specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (y : List BPair) (hy : y.length = n)
    (hmom : ((inertia.quadForm (matMul Et Et) y).scale q).oneValue
      ((inertia.quadForm Et y).scale (E0 * p)))
    (j : Nat) (hj : j < n) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj))
    (hz : ¬ nj.oneValue BPair.unit)
    (hwoff : ¬ (ground.getAt BPair.unit (matVec Tw.val y) j
      * ground.getAt BPair.unit (matVec Tw.val y) j).oneValue
        BPair.unit) :
    (nj.scale q).oneValue (BPair.ofPos (E0 * p * dj)) := by
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hcl : (matVec Tw.val y).length = n := by rw [matVec_length, hTwl]
  have hcj : j < (matVec Tw.val y).length := by rw [hcl]; exact hj
  have hjv : j < (split.vDiagL Et T).length := by
    rw [split.vDiagL_len]; exact hj
  have hjw : j < (List.zipWith (· * ·) (matVec Tw.val y)
      (matVec Tw.val y)).length := by
    rw [ground.length_zipWith _ _ _ n hcl hcl]; exact hj
  have hterm := elim.dotP_eq_of_leTerm (E0 * p) q (split.vDiagL Et T)
    (split.vDiagL (matMul Et Et) T)
    (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y))
    (by rw [split.vDiagL_len, split.vDiagL_len])
    (speccut.foldTermLe Et T Tw l E0 p q hd hs (matVec Tw.val y) hcl)
    (foldEq Et T Tw l E0 p q hd y hy hmom) j hjv hjw
  rw [ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
      (matVec Tw.val y) (matVec Tw.val y) j hcj hcj,
    split.vDiagL_get Et T j hj, split.vDiagL_get (matMul Et Et) T j hj] at hterm
  exact edgeOfTerm (split.scalePos Et T Tw l hd j hjl nj gj dj hroot)
    hwoff hz (split.diagEntryV Et T Tw l hd j hj nj gj dj hroot)
    (split.diagEntryK Et T Tw l hd j hj nj gj dj hroot) hterm

/-- The eigen column's two moments read equal members at a root at
the edge, the first strictly above the sum's unit — clause (ii) at
the located root's own column. -/
theorem moment_eq {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j : Nat) (hj : j < n) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj))
    (hedge : (nj.scale q).oneValue (BPair.ofPos (E0 * p * dj))) :
    ((inertia.quadForm (matMul Et Et)
        (matVec T.val (elim.idRow n j))).scale q).oneValue
      ((inertia.quadForm Et (matVec T.val (elim.idRow n j))).scale
        (E0 * p))
    ∧ BPair.unit < inertia.quadForm Et (matVec T.val (elim.idRow n j)) := by
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hgpos : BPair.unit < gj :=
    split.scalePos Et T Tw l hd j hjl nj gj dj hroot
  have qE := split.eigenQuadV Et T Tw l hd j hj nj gj dj hroot
  have qK := split.eigenQuadK Et T Tw l hd j hj nj gj dj hroot
  have hL : (BPair.ofPos dj
      * (inertia.quadForm (matMul Et Et)
          (matVec T.val (elim.idRow n j))).scale q).oneValue
      (BPair.ofPos (E0 * p * dj) * (nj * gj)) := by
    rw [BPair.mul_scale (BPair.ofPos dj)
      (inertia.quadForm (matMul Et Et)
        (matVec T.val (elim.idRow n j))) q]
    refine BPair.oneValue_trans (BPair.scale_congr q qK) ?_
    rw [BPair.scale_mul_left nj (nj * gj) q]
    exact BPair.mul_congr_left hedge
  have hR : (BPair.ofPos dj
      * (inertia.quadForm Et
          (matVec T.val (elim.idRow n j))).scale (E0 * p)).oneValue
      (BPair.ofPos (E0 * p * dj) * (nj * gj)) := by
    rw [BPair.mul_scale (BPair.ofPos dj)
      (inertia.quadForm Et (matVec T.val (elim.idRow n j))) (E0 * p)]
    refine BPair.oneValue_trans (BPair.scale_congr (E0 * p)
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos dj)) qE)) ?_
    rw [BPair.scale_mul_left (BPair.ofPos dj) (nj * gj) (E0 * p)]
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans (BPair.scale_ofPos dj (E0 * p)) ?_
    rw [ground.mul_comm dj (E0 * p)]
    exact BPair.oneValue_refl _
  refine ⟨ground.mulCancel (BPair.ofPos_off dj)
    (BPair.oneValue_trans hL (BPair.oneValue_symm hR)), ?_⟩
  have hnoff : ¬ nj.oneValue BPair.unit := by
    intro hn
    exact ground.offOfUnitLt (ground.unitLtOfPos (E0 * p * dj))
      (BPair.oneValue_trans (BPair.oneValue_symm hedge)
        (BPair.oneValue_trans (BPair.scale_congr q hn)
          (BPair.oneValue_symm (ground.unitScale q))))
  have hnpos : BPair.unit < nj :=
    ground.ltOfLeOff
      (rootUnitLe (Or.inr (ground.leB_not_lt
        (Or.inl (BPair.oneValue_symm hedge))))) hnoff
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm qE) (ground.unitLtMul hnpos hgpos)

/-- The attainment at the named edge: at the spectral read with an
edge root the eigen column at that root is a word image whose two
moments read equal members with the first strictly above the sum's
unit — clauses (i) and (ii) at one read, the consumers' own
composite. -/
theorem attained_at {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (he : edgeRead (l.map (fun r => (r.1, r.2.1))) E0 p q) :
    ∃ j, j < n
      ∧ ((inertia.quadForm (matMul Et Et)
            (matVec T.val (elim.idRow n j))).scale q).oneValue
          ((inertia.quadForm Et
            (matVec T.val (elim.idRow n j))).scale (E0 * p))
      ∧ BPair.unit < inertia.quadForm Et
          (matVec T.val (elim.idRow n j)) := by
  obtain ⟨j, hj, hf⟩ := ground.getAt_of_any _ (BPair.unit, Pos.one)
    (l.map (fun r => (r.1, r.2.1))) he.2
  rw [ground.length_map] at hj
  rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit)
    (BPair.unit, Pos.one) _ l j hj] at hf
  have hjn : j < n := by
    rw [← split.rootLen Et T Tw l hd]
    exact hj
  have hedge : (((ground.getAt (BPair.unit, Pos.one, BPair.unit)
        l j).1).scale q).oneValue
      (BPair.ofPos (E0 * p
        * (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1)) :=
    of_decide_eq_true hf
  exact ⟨j, hjn,
    moment_eq Et T Tw l E0 p q hd j hjn
      (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1
      (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2
      (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1
      rfl hedge⟩

/-- An occupied weight sits at the kernel point or at the level
exactly — clause (iii)'s per-root read at the moments' equal
members. -/
theorem weights_at {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : speccut.specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (y : List BPair) (hy : y.length = n)
    (hmom : ((inertia.quadForm (matMul Et Et) y).scale q).oneValue
      ((inertia.quadForm Et y).scale (E0 * p))) :
    ∀ j, j < n → ∀ nj gj : BPair, ∀ dj : Pos,
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      BPair.unit < (ground.getAt BPair.unit (matVec Tw.val y) j
          * ground.getAt BPair.unit (matVec Tw.val y) j)
          * (gj * BPair.ofPos dj) →
      nj.oneValue BPair.unit
        ∨ (nj.scale q).oneValue (BPair.ofPos (E0 * p * dj)) := by
  intro j hj nj gj dj hroot hw
  by_cases hz : nj.oneValue BPair.unit
  · exact Or.inl hz
  refine Or.inr ?_
  have hwoff : ¬ (ground.getAt BPair.unit (matVec Tw.val y) j
      * ground.getAt BPair.unit (matVec Tw.val y) j).oneValue
        BPair.unit := fun hcs =>
    ground.offOfUnitLt hw (BPair.oneValue_trans (BPair.mul_congr_left hcs)
      (BPair.unit_mul _))
  exact edgeAt Et T Tw l E0 p q hd hs y hy hmom j hj nj gj dj hroot
    hz hwoff

/-- A first moment strictly above the sum's unit puts an occupied
weight at the level — clause (iii)'s occupancy at the located
roots. -/
theorem weight_occupied {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : speccut.specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (y : List BPair) (hy : y.length = n)
    (hmom : ((inertia.quadForm (matMul Et Et) y).scale q).oneValue
      ((inertia.quadForm Et y).scale (E0 * p)))
    (hpos : BPair.unit < inertia.quadForm Et y) :
    ∃ j, j < n ∧ ∃ nj gj : BPair, ∃ dj : Pos,
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj)
      ∧ (nj.scale q).oneValue (BPair.ofPos (E0 * p * dj))
      ∧ BPair.unit < (ground.getAt BPair.unit (matVec Tw.val y) j
          * ground.getAt BPair.unit (matVec Tw.val y) j)
          * (gj * BPair.ofPos dj) := by
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hcl : (matVec Tw.val y).length = n := by rw [matVec_length, hTwl]
  obtain ⟨j, hjv, hjw, hlt⟩ := elim.dotP_pos_mem (split.vDiagL Et T)
    (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y))
    (foldUnitLe Et T Tw l E0 p q hd hs (matVec Tw.val y) hcl)
    (foldPos Et T Tw l hd y hy hpos)
  rw [split.vDiagL_len] at hjv
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hjv
  have hcj : j < (matVec Tw.val y).length := by rw [hcl]; exact hjv
  rw [ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
      (matVec Tw.val y) (matVec Tw.val y) j hcj hcj,
    split.vDiagL_get Et T j hjv] at hlt
  have hgpos : BPair.unit < (ground.getAt
      (BPair.unit, Pos.one, BPair.unit) l j).2.2 :=
    split.scalePos Et T Tw l hd j hjl _ _ _ rfl
  have hv := split.diagEntryV Et T Tw l hd j hjv _ _ _ rfl
  have hwoff : ¬ (ground.getAt BPair.unit (matVec Tw.val y) j
      * ground.getAt BPair.unit (matVec Tw.val y) j).oneValue
        BPair.unit := fun hcs =>
    ground.offOfUnitLt hlt (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hcs) (BPair.mul_unit _))
  have hz : ¬ (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1.oneValue
      BPair.unit := fun hn =>
    ground.offOfUnitLt hlt (BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans hv
          (BPair.oneValue_trans (BPair.mul_congr_left hn)
            (BPair.unit_mul _))))
      (BPair.unit_mul _))
  refine ⟨j, hjv, (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
    (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2,
    (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1, rfl, ?_, ?_⟩
  · exact edgeAt Et T Tw l E0 p q hd hs y hy hmom j hjv _ _ _ rfl
      hz hwoff
  · exact ground.unitLtMul
      (ground.ltOfLeOff (ground.unitLeSq _) hwoff)
      (ground.unitLtMul hgpos (ground.unitLtOfPos _))

/-- The probe cap — clause (iv): at a probe whose two moments read
the pair `(μ₂ : γ μ₁)` on its lower side, the spectral read at the
level fails, a located root off the kernel point sitting below the
level. The operator inequality would price the probe at the
requirement (`levelequiv.probe_intro`), and the spectral read
prices the cut's split (`speccut.spec_to_cut`), so the two refuse
together. -/
theorem probe_cap {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp)
    (y : List BPair) (hy : y.length = n)
    (hlow : (inertia.quadForm (matMul Et Et) y).scale q
      < (inertia.quadForm Et y).scale (E0 * p)) :
    ¬ speccut.specRead (l.map (fun r => (r.1, r.2.1))) E0 p q := by
  intro hs
  have hp : psdAt sp := speccut.spec_to_cut Et T Tw l E0 p q hd hs sp hsp
  have hop : levelequiv.opRead (matMul Et Et) Et (E0 * p) q sp :=
    ⟨sqSquare hd.1, hd.1, hsp, hp⟩
  have hreq := levelequiv.probe_intro (⟨matMul Et Et, sqSquare hd.1⟩ : SqMat n)
    (⟨Et, hd.1⟩ : SqMat n) (E0 * p) q sp hop
    (⟨y, by rw [hy]; exact beqRefl n⟩ : Vec n)
  exact hreq hlow

end attained
