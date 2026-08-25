import MassGap.K
import MassGap.Split
/-!
`lem:speccut` — a window spectral read is the cut at that window:
the level gap's located spectrum at the kernel point and at or
beyond the edge `E₀ κ` (`specRead`, one cleared comparison per
root), and the tie — the factorization read of the gap's own
pencil at those roots with the cut's positive-semidefinite split
(`cutTie`, `lem:split`'s located roots feeding `thm:detector`'s
side reads, the compression keeping the read by `lem:inertia`) —
the cut's own object at every window ground at once, the detector
form compressed whole.

The identification's forward direction is the theorem below at its
stated certificate data (`spec_to_cut`): the diagonalizing
congruence carries the level gap to a diagonal at the located
roots (`lem:split`'s `diagRead` with the eigen-column capstone),
the spectral read prices every root's cut summand on its upper
side, and the congruence's own invertibility carries the read back
to every vector of the order — so a split of the cut's site datum
counts no reversal, the compression keeping the read
(`lem:inertia`'s two transport clauses the consumption).  The
certificates are the theorem's data: the symmetric gap, the
congruence with its adjugate witness, the located root list with
its scales on their upper sides, and the split whose count the
conclusion prices.

The reading back is the theorem beside it (`cut_to_spec`), at the
level gap's own floor datum: `Ẽ` is positive semidefinite by
construction (`def:pencil`'s gap at `ε₀ G + Ẽ = H`, `def:K`'s
`floorRead` clause), and that datum is what locates the roots'
signs — the gap's split prices every eigen column on its upper
side, so each root sits at or above the kernel point, and the
cut's split then reads it at the kernel point or at or beyond the
edge.  The floor datum is load-bearing and not decoration: the
pair `(q Ẽ² : E₀ p Ẽ)` sits on its upper side at a strictly
negative level too (`ε (q ε − E₀ p) ≥ 0` at `ε < 0`), so without
it the cut does not locate the spectrum — the check module's
one-letter window at the negative unit is the committed refusal,
every other clause holding there while the spectral read fails.
-/

namespace speccut
open ground elim inertia split

/-- The spectral read: every located level of the gap at the kernel
point or at or beyond the edge, `spec ⊂ {ε₀} ∪ [ε₀ + E₀κ, ∞)` read
at the gap's roots. -/
def specRead (roots : List (BPair × Pos)) (E0 p q : Pos) : Prop :=
  (roots.all (fun r =>
    decide (r.1.oneValue BPair.unit)
      || !(decide (r.1.scale q < BPair.ofPos (E0 * p * r.2))))) = true

instance (roots : List (BPair × Pos)) (E0 p q : Pos) :
    Decidable (specRead roots E0 p q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The tie: the gap's pencil factorizes at the located roots, the
spectral read holds there, and the cut's split reads the pair —
the spectral read is the cut at the window. -/
def cutTie {o : Nat} (Et : Mat) (roots : List (BPair × Pos))
    (E0 p q : Pos) (sp : Split o) : Prop :=
  split.chiRead Et (idMat Et.length) roots
  ∧ specRead roots E0 p q
  ∧ K.cutRead (matMul Et Et) Et E0 p q sp

instance {o : Nat} (Et : Mat) (roots : List (BPair × Pos))
    (E0 p q : Pos) (sp : Split o) :
    Decidable (cutTie Et roots E0 p q sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! The order kit at the balance carrier: the monotone product with
its positive clearing's reflection, the module's own tier above
`ground`'s side bridges and cross-multiplied comparison. -/

/-- A strictly positive factor keeps the strict order. -/
private theorem mulLtMono {s x y : BPair} (hs : BPair.unit < s)
    (h : x < y) : s * x < s * y := by
  have hc := ground.crossLt (ground.sideOfUnitLt hs)
    (show x.fst + y.snd < y.fst + x.snd from h)
  rw [ground.left_distrib s.fst x.fst y.snd,
    ground.left_distrib s.snd y.fst x.snd,
    ground.left_distrib s.fst y.fst x.snd,
    ground.left_distrib s.snd x.fst y.snd] at hc
  show s.fst * x.fst + s.snd * x.snd + (s.fst * y.snd + s.snd * y.fst)
    < s.fst * y.fst + s.snd * y.snd + (s.fst * x.snd + s.snd * x.fst)
  rw [ground.add_add_comm (s.fst * x.fst) (s.snd * x.snd)
      (s.fst * y.snd) (s.snd * y.fst),
    ground.add_add_comm (s.fst * y.fst) (s.snd * y.snd)
      (s.fst * x.snd) (s.snd * x.fst),
    ground.add_comm (s.snd * x.snd) (s.snd * y.fst),
    ground.add_comm (s.snd * y.snd) (s.snd * x.fst)]
  exact hc

/-- A strictly positive factor reflects the order. -/
private theorem mulLeReflect {s x y : BPair} (hs : BPair.unit < s)
    (h : s * x ≤ s * y) : x ≤ y :=
  ground.leB_of_not_lt (fun hlt => ground.leB_not_lt h (mulLtMono hs hlt))

/-- The rescaling carries out of a product's first member. -/
private theorem scaleMulL (s x : BPair) (w : Pos) :
    (s * x).scale w = s.scale w * x := by
  show BPair.mk ((s.fst * x.fst + s.snd * x.snd) * w)
      ((s.fst * x.snd + s.snd * x.fst) * w)
    = BPair.mk (s.fst * w * x.fst + s.snd * w * x.snd)
      (s.fst * w * x.snd + s.snd * w * x.fst)
  rw [ground.right_distrib, ground.right_distrib,
    ground.mul_right_comm s.fst x.fst w, ground.mul_right_comm s.snd x.snd w,
    ground.mul_right_comm s.fst x.snd w, ground.mul_right_comm s.snd x.fst w]

/-- The rescaling carries out of a product's second member. -/
private theorem scaleMulR (s x : BPair) (w : Pos) :
    (s * x).scale w = s * x.scale w := by
  rw [BPair.mul_comm s x, scaleMulL x s w, BPair.mul_comm (x.scale w) s]

private theorem unitScaleLe (gn gd : Pos) :
    (BPair.unit.scale gn) ≤ (BPair.unit.scale gd) :=
  ground.leB_congr (ground.unitScale gn) (ground.unitScale gd) (ground.leB_refl BPair.unit)

/-! The entry readers at the unit family, the module's own remainder
above `ground`'s beq bridges and the one-value reads at `poly` and
`elim`. -/

private theorem plinRow : ∀ r s : List poly.Poly, split.prowOneValue r s →
    poly.oneValue (r.map (fun p => ground.getAt BPair.unit p 1))
      (s.map (fun p => ground.getAt BPair.unit p 1))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: r, _ :: s, h => ⟨poly.oneValue_getAt 1 h.1, plinRow r s h.2⟩

private theorem plinOne : ∀ a b : split.PMat, split.pmatOneValue a b →
    matOneValue (split.plin a) (split.plin b)
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: a, _ :: b, h => ⟨plinRow _ _ h.1, plinOne a b h.2⟩

/-! The unit family and the diagonal's entry reads, with the
identity's action — the column reader's kit. -/

/-! The diagonal fold: the diagonal's action is the pointwise
product, the form at a vector the entries' own square-weighted sum,
and the sum's order is the entries' termwise order under the two
clearings. -/

private theorem diagAct (ds c : List BPair) (hc : c.length = ds.length) :
    poly.oneValue (matVec (split.diagM ds) c)
      (List.zipWith (· * ·) ds c) := by
  refine getAt_polyOne _ _ ?_ ?_
  · rw [matVec_length, diagM_len,
      ground.length_zipWith (· * ·) ds c ds.length rfl hc]
  · intro i hi
    rw [matVec_length, diagM_len] at hi
    rw [show matVec (split.diagM ds) c
        = (split.diagM ds).map (fun r => dotN r c) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit _ (split.diagM ds) i
        (by rw [diagM_len]; exact hi),
      ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
        ds c i hi (by rw [hc]; exact hi)]
    refine BPair.oneValue_trans (dotN_read _ c) ?_
    rw [dotP_comm (ground.getAt ([] : List BPair) (split.diagM ds) i) c]
    refine BPair.oneValue_trans
      (dotP_oneIndex c (ground.getAt ([] : List BPair) (split.diagM ds) i) i
        (by rw [hc, diagM_rowlen ds i hi])
        (by rw [diagM_rowlen ds i hi]; exact hi) ?_) ?_
    · intro j hj hne
      rw [diagM_rowlen ds i hi] at hj
      rw [diagM_entry ds i j hi hj, if_neg hne]
      exact BPair.oneValue_refl _
    · rw [diagM_entry ds i i hi hi, if_pos rfl]
      exact BPair.oneValue_of_eq (BPair.mul_comm _ _)

private theorem dotP_dmul : ∀ ds c : List BPair,
    (dotP c (List.zipWith (· * ·) ds c)).oneValue
      (dotP ds (List.zipWith (· * ·) c c))
  | [], c => by
    match c with
    | [] => exact BPair.oneValue_refl _
    | _ :: _ => exact BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | d :: ds, x :: c => by
    show (x * (d * x) + dotP c (List.zipWith (· * ·) ds c)).oneValue
      (d * (x * x) + dotP ds (List.zipWith (· * ·) c c))
    exact BPair.add_congr (BPair.oneValue_of_eq (BPair.mul_left_comm x d x))
      (dotP_dmul ds c)

private theorem qsumLe (gn gd : Pos) : ∀ (a b c : List BPair),
    a.length = b.length →
    (∀ j, j < a.length →
      (ground.getAt BPair.unit a j).scale gn
        ≤ (ground.getAt BPair.unit b j).scale gd) →
    (dotP a (List.zipWith (· * ·) c c)).scale gn
      ≤ (dotP b (List.zipWith (· * ·) c c)).scale gd
  | [], [], _, _, _ => unitScaleLe gn gd
  | [], _ :: _, _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], _, hl, _ => Nat.noConfusion hl
  | _ :: _, _ :: _, [], _, _ => unitScaleLe gn gd
  | d :: a, e :: b, x :: c, hl, h => by
    show (d * (x * x) + dotP a (List.zipWith (· * ·) c c)).scale gn
      ≤ (e * (x * x) + dotP b (List.zipWith (· * ·) c c)).scale gd
    rw [BPair.scale_add, BPair.scale_add]
    refine ground.leB_add ?_
      (qsumLe gn gd a b c (Nat.succ.inj hl)
        (fun j hj => h (j + 1) (Nat.succ_lt_succ hj)))
    rw [scaleMulL d (x * x) gn, scaleMulL e (x * x) gd,
      BPair.mul_comm (d.scale gn) (x * x), BPair.mul_comm (e.scale gd) (x * x)]
    exact ground.leB_mulR (unitLeSq x) (h 0 (Nat.succ_pos _))

/-! The entry reads at the congruence: an entry is the unit family's
own pairing, a matrix is its entries, and the congruated entry is
the columns' pairing at the two carried vectors. -/

private theorem entryOf (M : Mat) (n i j : Nat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hi : i < n) (hj : j < n) :
    (dotP (elim.idRow n i) (matVec M (elim.idRow n j))).oneValue
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair) M i) j) := by
  have hlen : (matVec M (elim.idRow n j)).length = n := by
    rw [matVec_length, hMl]
  rw [dotP_comm (elim.idRow n i) (matVec M (elim.idRow n j))]
  refine BPair.oneValue_trans (dotP_idRow _ n i hlen hi) ?_
  rw [show matVec M (elim.idRow n j)
      = M.map (fun r => dotN r (elim.idRow n j)) from rfl,
    ground.getAt_map ([] : List BPair) BPair.unit _ M i
      (by rw [hMl]; exact hi)]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  exact dotP_idRow _ n j
    (rowsLen_getAt M i hMr (by rw [hMl]; exact hi)) hj

private theorem congrShapeL (M T : Mat) (n : Nat)
    (hTl : T.length = n) (hTr : rowsLen n T) :
    (matMul (transposeM T) (matMul M T)).length = n := by
  rw [show (matMul (transposeM T) (matMul M T)).length
      = (transposeM T).length from ground.length_map _ _]
  exact transposeLen T hTr hTl

private theorem congrShapeR (M T : Mat) (n : Nat) (hMl : M.length = n)
    (hTl : T.length = n) (hTr : rowsLen n T) :
    rowsLen n (matMul (transposeM T) (matMul M T)) := by
  have hMTl : (matMul M T).length = n := by
    rw [show (matMul M T).length = M.length from ground.length_map _ M]
    exact hMl
  have hMTr : rowsLen n (matMul M T) :=
    rowsLen_cast (transposeLen T hTr hTl) (rowsLen_matMul M T)
  exact rowsLen_cast (transposeLen (matMul M T) hMTr hMTl)
    (rowsLen_matMul (transposeM T) (matMul M T))

/-- The congruated pairing: the congruence's own datum against two
vectors is the datum against the two carried vectors. -/
private theorem congrPair (M T : Mat) (n : Nat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hTl : T.length = n) (hTr : rowsLen n T)
    (x y : List BPair) (hx : x.length = n) (hy : y.length = n) :
    (dotP (matVec T x) (matVec M (matVec T y))).oneValue
      (dotP x (matVec (matMul (transposeM T) (matMul M T)) y)) := by
  have hMTl : (matMul M T).length = n := by
    rw [show (matMul M T).length = M.length from ground.length_map _ M]
    exact hMl
  have hTtl : (transposeM T).length = n := transposeLen T hTr hTl
  have hTy : (matVec T y).length = n := by rw [matVec_length, hTl]
  refine BPair.oneValue_trans
    (dotP_matVec_transpose n T x (matVec M (matVec T y)) hTr hx
      (by rw [matVec_length, hMl, hTl])) ?_
  refine dotP_oneValue_right x _ _ ?_
  refine poly.oneValue_trans
    (matVec_congr (transposeM T) _ _
      (matVec_comp M T y n hTr hy (rowsLen_cast hTl.symm hMr))) ?_
  exact matVec_comp (transposeM T) (matMul M T) y n
    (rowsLen_cast hTtl (rowsLen_matMul M T)) hy
    (rowsLen_cast hMTl.symm (rowsLen_cast hTl (rowsLen_transposeM T)))

/-- The gap's own symmetry, the pairing's adjoint at the datum. -/
private theorem symAdj (Et : Mat) (n : Nat) (hEtl : Et.length = n)
    (hEtr : rowsLen n Et) (hsym : matOneValue (transposeM Et) Et)
    (x y : List BPair) (hx : x.length = n) (hy : y.length = n) :
    (dotP (matVec Et x) y).oneValue (dotP x (matVec Et y)) := by
  refine BPair.oneValue_trans
    (dotP_matVec_transpose n Et x y hEtr hx (by rw [hEtl]; exact hy)) ?_
  exact dotP_oneValue_right x _ _ (matVec_matOne _ _ y hsym)

/-- A square datum whose off-diagonal unit-family pairings vanish is
the diagonal at its own diagonal entries. -/
private theorem diagOfEntries (A : Mat) (n : Nat) (hAl : A.length = n)
    (hAr : rowsLen n A)
    (hoff : ∀ i j, i < n → j < n → ¬ i = j →
      (dotP (elim.idRow n i) (matVec A (elim.idRow n j))).oneValue
        BPair.unit) :
    matOneValue A (split.diagM ((List.range n).map
      (fun j => dotP (elim.idRow n j) (matVec A (elim.idRow n j))))) := by
  have hdl : ((List.range n).map
      (fun j => dotP (elim.idRow n j) (matVec A (elim.idRow n j)))).length
      = n := ground.length_mapRange _ n
  refine matOne_of_entries A _ n hAl hAr
    (by rw [diagM_len, hdl]) (split.diagM_shape _ n hdl) ?_
  intro i j hi hj
  rw [diagM_entry _ i j (by rw [hdl]; exact hi) (by rw [hdl]; exact hj)]
  by_cases hij : j = i
  · subst hij
    rw [if_pos rfl, ground.getAt_map (0 : Nat) BPair.unit _ (List.range n) j
      (by rw [ground.length_range]; exact hi), ground.getAt_range n j hi]
    exact BPair.oneValue_symm (entryOf A n j j hAl hAr hi hi)
  · rw [if_neg hij]
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.oneValue_symm (hoff i j hi hj (fun he => ?_)))
      (entryOf A n i j hAl hAr hi hj))
    exact hij he.symm

/-! The certificate's reads at the columns: the Gram of the carried
unit family is the certificate's linear diagonal, and the eigen
column is `lem:split`'s capstone with the identity's action read
off. -/

private theorem eigenRead {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hj : j < l.length) :
    poly.oneValue
      (vecScale (BPair.ofPos
          (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1)
        (matVec Et (matVec T.val (elim.idRow n j))))
      (vecScale (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1
        (matVec T.val (elim.idRow n j))) := by
  have hE := split.eigenColumn Et (idMat n) T Tw l j
    (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1
    (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2
    (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1
    hd hj rfl
  refine poly.oneValue_trans hE (vecScale_oneValue _ _ _ ?_)
  exact matVec_idMat n _ (by rw [matVec_length]; exact SqMat.rows T)

private theorem gramRead {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    (dotP (matVec T.val (elim.idRow n i))
        (matVec T.val (elim.idRow n j))).oneValue
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (split.diagM (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) i)
        j) := by
  obtain ⟨hEt, hI, ⟨_, _, _⟩, hcong, _⟩ := hd
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hIl : (idMat n).length = n := sqAt_len hI
  have hIr : rowsLen n (idMat n) := rowsLen_of_sqAt hI
  have hG : matOneValue
      (matMul (transposeM T.val) (matMul (idMat n) T.val))
      (split.diagM (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by
    have h1 := plinOne _ _ hcong
    rw [split.plin_pdiag l] at h1
    exact matOne_trans (matOne_symm (split.plin_congrZ Et (idMat n) T hEt hI)) h1
  refine BPair.oneValue_trans ?_
    (poly.oneValue_getAt j (matOne_entries _ _ hG i (by
      rw [show (matMul (transposeM T.val) (matMul (idMat n) T.val)).length
          = (transposeM T.val).length from ground.length_map _ _,
        transposeLen T.val hTr hTl]
      exact hi)))
  refine BPair.oneValue_trans ?_
    (entryOf (matMul (transposeM T.val) (matMul (idMat n) T.val)) n i j
      (congrShapeL (idMat n) T.val n hTl hTr)
      (congrShapeR (idMat n) T.val n hIl hTl hTr) hi hj)
  refine BPair.oneValue_trans ?_
    (congrPair (idMat n) T.val n hIl hIr hTl hTr _ _
      (length_idRow n i) (length_idRow n j))
  refine dotP_oneValue_right _ _ _ (poly.oneValue_symm ?_)
  exact matVec_idMat n _ (by rw [matVec_length, hTl])

/-! The certificate's own reads at the columns' pairings: the
diagonal entries at the two data, the off-diagonal pairings at the
sum's unit, and the spectral read's per-root disjunct. -/

private theorem pdiag_len (ds : List poly.Poly) :
    (split.pdiag ds).length = ds.length :=
  ground.length_mapRange _ _

/-- The located root list's own order, the certificate's shape. -/
private theorem rootLen {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) : l.length = n := by
  obtain ⟨_, _, ⟨_, _, _⟩, hcong, _⟩ := hd
  have h1 := ground.matched_length hcong
  rw [show (split.congrZ T.val (split.zMat Et (idMat n))).length
      = (transposeM T.val).length from ground.length_map _ _,
    transposeLen T.val (rowsLen_of_sqAt T.shape) (SqMat.rows T),
    pdiag_len, ground.length_map] at h1
  exact h1.symm

private theorem scalePos {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hj : j < l.length)
    (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    BPair.unit < gj := by
  obtain ⟨_, _, ⟨_, _, _⟩, _, hall⟩ := hd
  have h := ground.all_getAt (BPair.unit, Pos.one, BPair.unit) l hall j hj
  rw [hroot] at h
  exact of_decide_eq_true h

private theorem specGet (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (j : Nat) (hj : j < l.length) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    nj.oneValue BPair.unit ∨ ¬ (nj.scale q < BPair.ofPos (E0 * p * dj)) := by
  have hs' : ((l.map (fun r => (r.1, r.2.1))).all (fun r =>
      decide (r.1.oneValue BPair.unit)
        || !(decide (r.1.scale q < BPair.ofPos (E0 * p * r.2))))) = true := hs
  have hall := ground.all_getAt (BPair.unit, Pos.one)
    (l.map (fun r => (r.1, r.2.1))) hs' j (by rw [ground.length_map]; exact hj)
  rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) (BPair.unit, Pos.one)
      _ l j hj, hroot] at hall
  match ground.orSplitB hall with
  | Or.inl h1 => exact Or.inl (of_decide_eq_true h1)
  | Or.inr h2 => exact Or.inr (ground.notOfBang h2)

/-- The eigen column against a vector: the root's two members clear
the gap's own pairing at the carried column. -/
private theorem pairEigen {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hjl : j < l.length)
    (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) (w : List BPair) :
    (BPair.ofPos dj
        * dotP w (matVec Et (matVec T.val (elim.idRow n j)))).oneValue
      (nj * dotP w (matVec T.val (elim.idRow n j))) := by
  have h := eigenRead Et T Tw l hd j hjl
  rw [hroot] at h
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (dotP_vecScale_right w _ _)) ?_
  refine BPair.oneValue_trans (dotP_oneValue_right w _ _ h) ?_
  exact dotP_vecScale_right w _ _

private theorem gramOff {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (i j : Nat)
    (hi : i < n) (hj : j < n) (hne : ¬ i = j) :
    (dotP (matVec T.val (elim.idRow n i))
        (matVec T.val (elim.idRow n j))).oneValue BPair.unit := by
  have hws : (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)).length = n := by
    rw [ground.length_map]; exact rootLen Et T Tw l hd
  have hg := gramRead Et T Tw l hd i j hi hj
  rw [diagM_entry _ i j (by rw [hws]; exact hi) (by rw [hws]; exact hj),
    if_neg (fun he : j = i => hne he.symm)] at hg
  exact hg

private theorem gramDiag {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hj : j < n)
    (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    (dotP (matVec T.val (elim.idRow n j))
        (matVec T.val (elim.idRow n j))).oneValue (gj * BPair.ofPos dj) := by
  have hlo : l.length = n := rootLen Et T Tw l hd
  have hws : (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)).length = n := by
    rw [ground.length_map]; exact hlo
  have hg := gramRead Et T Tw l hd j j hj hj
  rw [diagM_entry _ j j (by rw [hws]; exact hj) (by rw [hws]; exact hj),
    if_pos rfl,
    ground.getAt_map (BPair.unit, Pos.one, BPair.unit) BPair.unit _ l j
      (by rw [hlo]; exact hj), hroot] at hg
  exact BPair.oneValue_trans hg (BPair.norm_oneValue _)

/-- The gap's congruated entry is the two carried columns' own
pairing. -/
private theorem vPair {n : Nat} (Et : Mat) (T : SqMat n) (hEt : sqAt Et n)
    (i j : Nat) :
    (dotP (elim.idRow n i)
        (matVec (matMul (transposeM T.val) (matMul Et T.val))
          (elim.idRow n j))).oneValue
      (dotP (matVec T.val (elim.idRow n i))
        (matVec Et (matVec T.val (elim.idRow n j)))) :=
  BPair.oneValue_symm
    (congrPair Et T.val n (sqAt_len hEt) (rowsLen_of_sqAt hEt) (SqMat.rows T)
      (rowsLen_of_sqAt T.shape) _ _ (length_idRow n i) (length_idRow n j))

/-- The squared gap's congruated entry is the two mapped columns'
pairing, the datum's own symmetry the exchange. -/
private theorem kPair {n : Nat} (Et : Mat) (T : SqMat n)
    (hsym : matOneValue (transposeM Et) Et) (hEt : sqAt Et n) (i j : Nat) :
    (dotP (elim.idRow n i)
        (matVec (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
          (elim.idRow n j))).oneValue
      (dotP (matVec Et (matVec T.val (elim.idRow n i)))
        (matVec Et (matVec T.val (elim.idRow n j)))) := by
  have hEtl : Et.length = n := sqAt_len hEt
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hEEl : (matMul Et Et).length = n := by
    rw [show (matMul Et Et).length = Et.length from ground.length_map _ Et]
    exact hEtl
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_cast (transposeLen Et hEtr hEtl) (rowsLen_matMul Et Et)
  have hvj : (matVec T.val (elim.idRow n j)).length = n := by
    rw [matVec_length, hTl]
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (congrPair (matMul Et Et) T.val n hEEl hEEr hTl hTr _ _
      (length_idRow n i) (length_idRow n j))) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right _ _ _ (poly.oneValue_symm
      (matVec_comp Et Et (matVec T.val (elim.idRow n j)) n hEtr hvj
        (rowsLen_cast hEtl.symm hEtr)))) ?_
  exact BPair.oneValue_symm
    (symAdj Et n hEtl hEtr hsym (matVec T.val (elim.idRow n i))
      (matVec Et (matVec T.val (elim.idRow n j)))
      (by rw [matVec_length, hTl]) (by rw [matVec_length, hEtl]))

private theorem vOff {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (i j : Nat)
    (hi : i < n) (hj : j < n) (hne : ¬ i = j) :
    (dotP (elim.idRow n i)
        (matVec (matMul (transposeM T.val) (matMul Et T.val))
          (elim.idRow n j))).oneValue BPair.unit := by
  have hjl : j < l.length := by rw [rootLen Et T Tw l hd]; exact hj
  refine BPair.oneValue_trans (vPair Et T hd.1 i j) ?_
  refine mul_cancel_unit
    (BPair.ofPos_off (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1) ?_
  refine BPair.oneValue_trans
    (pairEigen Et T Tw l hd j hjl _ _ _ rfl
      (matVec T.val (elim.idRow n i))) ?_
  exact BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _) (gramOff Et T Tw l hd i j hi hj hne))
    (BPair.mul_unit _)

private theorem vVal {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hj : j < n)
    (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    (dotP (elim.idRow n j)
        (matVec (matMul (transposeM T.val) (matMul Et T.val))
          (elim.idRow n j))).oneValue (nj * gj) := by
  have hjl : j < l.length := by rw [rootLen Et T Tw l hd]; exact hj
  refine BPair.oneValue_trans (vPair Et T hd.1 j j) ?_
  refine mulCancel (BPair.ofPos_off dj) ?_
  refine BPair.oneValue_trans
    (pairEigen Et T Tw l hd j hjl nj gj dj hroot
      (matVec T.val (elim.idRow n j))) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl nj)
      (gramDiag Et T Tw l hd j hj nj gj dj hroot)) ?_
  refine BPair.oneValue_of_eq ?_
  rw [← BPair.mul_assoc nj gj (BPair.ofPos dj),
    BPair.mul_comm (nj * gj) (BPair.ofPos dj)]

private theorem kOff {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l) (i j : Nat)
    (hi : i < n) (hj : j < n) (hne : ¬ i = j) :
    (dotP (elim.idRow n i)
        (matVec (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
          (elim.idRow n j))).oneValue BPair.unit := by
  have hlo : l.length = n := rootLen Et T Tw l hd
  have hil : i < l.length := by rw [hlo]; exact hi
  have hjl : j < l.length := by rw [hlo]; exact hj
  refine BPair.oneValue_trans (kPair Et T hsym hd.1 i j) ?_
  refine mul_cancel_unit
    (BPair.ofPos_off (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1)
    (mul_cancel_unit
      (BPair.ofPos_off (ground.getAt (BPair.unit, Pos.one, BPair.unit) l i).2.1) ?_)
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (pairEigen Et T Tw l hd j hjl _ _ _ rfl
        (matVec Et (matVec T.val (elim.idRow n i))))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) ?_)
    (BPair.mul_unit _)
  rw [dotP_comm (matVec Et (matVec T.val (elim.idRow n i)))
    (matVec T.val (elim.idRow n j))]
  refine BPair.oneValue_trans
    (pairEigen Et T Tw l hd i hil _ _ _ rfl
      (matVec T.val (elim.idRow n j))) ?_
  exact BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (gramOff Et T Tw l hd j i hj hi (fun he => hne he.symm)))
    (BPair.mul_unit _)

private theorem kVal {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hj : j < n)
    (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    (BPair.ofPos dj * dotP (elim.idRow n j)
        (matVec (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
          (elim.idRow n j))).oneValue (nj * (nj * gj)) := by
  have hjl : j < l.length := by rw [rootLen Et T Tw l hd]; exact hj
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _) (kPair Et T hsym hd.1 j j)) ?_
  refine mulCancel (BPair.ofPos_off dj) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (pairEigen Et T Tw l hd j hjl nj gj dj hroot
        (matVec Et (matVec T.val (elim.idRow n j))))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
  have hstep : (BPair.ofPos dj
      * dotP (matVec Et (matVec T.val (elim.idRow n j)))
        (matVec T.val (elim.idRow n j))).oneValue
      (nj * (gj * BPair.ofPos dj)) := by
    rw [dotP_comm (matVec Et (matVec T.val (elim.idRow n j)))
      (matVec T.val (elim.idRow n j))]
    exact BPair.oneValue_trans
      (pairEigen Et T Tw l hd j hjl nj gj dj hroot
        (matVec T.val (elim.idRow n j)))
      (BPair.mul_congr (BPair.oneValue_refl nj)
        (gramDiag Et T Tw l hd j hj nj gj dj hroot))
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl nj) hstep) ?_
  refine BPair.oneValue_of_eq ?_
  rw [← BPair.mul_assoc nj gj (BPair.ofPos dj),
    BPair.mul_comm (nj * gj) (BPair.ofPos dj),
    BPair.mul_left_comm nj (BPair.ofPos dj) (nj * gj)]

/-! The per-root comparison: the spectral read prices the cut's own
summand at the root, the clearing weights riding on the two data. -/

private theorem termLe {vj kj nj gj : BPair} {dj E0 p q : Pos}
    (hgpos : BPair.unit < gj)
    (hv : vj.oneValue (nj * gj))
    (hk : (BPair.ofPos dj * kj).oneValue (nj * (nj * gj)))
    (hread : nj.oneValue BPair.unit
      ∨ ¬ (nj.scale q < BPair.ofPos (E0 * p * dj))) :
    vj.scale (E0 * p) ≤ kj.scale q := by
  refine ground.leB_congr_left
    (BPair.scale_congr (E0 * p) (BPair.oneValue_symm hv)) ?_
  refine mulLeReflect (ground.unitLtOfPos dj) ?_
  rw [← scaleMulR (BPair.ofPos dj) (nj * gj) (E0 * p),
    ← scaleMulR (BPair.ofPos dj) kj q]
  refine ground.leB_congr_right
    (BPair.scale_congr q (BPair.oneValue_symm hk)) ?_
  rw [show BPair.ofPos dj * (nj * gj) = gj * (nj * BPair.ofPos dj) from by
      rw [BPair.mul_left_comm (BPair.ofPos dj) nj gj,
        BPair.mul_comm (BPair.ofPos dj) gj,
        BPair.mul_left_comm nj gj (BPair.ofPos dj)],
    show nj * (nj * gj) = gj * (nj * nj) from by
      rw [BPair.mul_comm nj gj, BPair.mul_left_comm nj gj nj],
    scaleMulR gj (nj * BPair.ofPos dj) (E0 * p), scaleMulR gj (nj * nj) q]
  refine ground.leB_mulR (Or.inr hgpos) ?_
  rw [scaleMulR nj (BPair.ofPos dj) (E0 * p), scaleMulR nj nj q]
  match hread with
  | Or.inl hz =>
    exact ground.leB_congr
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left hz) (BPair.unit_mul _)))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left hz) (BPair.unit_mul _)))
      (ground.leB_refl BPair.unit)
  | Or.inr hnl =>
    have hle : BPair.ofPos (E0 * p * dj) ≤ nj.scale q := ground.leB_of_not_lt hnl
    have h1 : BPair.unit.scale q ≤ nj.scale q :=
      ground.leB_congr_left (ground.unitScale q)
        (ground.leB_trans (Or.inr (ground.unitLtOfPos (E0 * p * dj))) hle)
    have hpos : BPair.unit ≤ nj :=
      ground.leB_of_not_lt (fun hlt => ground.leB_not_lt h1 (BPair.scale_lt q hlt))
    refine ground.leB_congr_left ?_ (ground.leB_mulR hpos hle)
    refine BPair.mul_congr (BPair.oneValue_refl nj) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.scale_ofPos dj (E0 * p)) ?_)
    rw [ground.mul_comm dj (E0 * p)]
    exact BPair.oneValue_refl _

/-! The scaled congruence and the identity's scaled action: the
form at a cleared vector is the clearing's square against the form,
the invertibility witness carrying every vector back. -/

private theorem quadScaleVec (A : Mat) (n : Nat) (hAr : rowsLen n A)
    (k : BPair) (u : List BPair) (hu : u.length = n) (x : List BPair)
    (hx : poly.oneValue x (vecScale k u)) :
    (inertia.quadForm A x).oneValue
      (k * k * inertia.quadForm A u) := by
  refine BPair.oneValue_trans (dotN_dotP _ _) ?_
  refine BPair.oneValue_trans (dotP_oneValue_left _ _ _ hx) ?_
  refine BPair.oneValue_trans (dotP_oneValue_right _ _ _
    (matVec_congr A x (vecScale k u) hx)) ?_
  refine BPair.oneValue_trans (dotP_oneValue_right _ _ _
    (matVec_vecScale A n hAr k u hu)) ?_
  refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
  have hstep : (dotP (vecScale k u) (matVec A u)).oneValue
      (k * dotP (matVec A u) u) := by
    rw [dotP_comm (vecScale k u) (matVec A u)]
    exact dotP_vecScale_right _ _ _
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl k) hstep) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_assoc k k _).symm) ?_
  refine BPair.mul_congr (BPair.oneValue_refl (k * k)) ?_
  rw [dotP_comm (matVec A u) u]
  exact BPair.oneValue_symm (dotN_dotP u (matVec A u))

/-! The two congruated diagonals and the cut's side at every vector
of the order: the gap's own diagonal at the roots' first members
against the scales, the squared gap's at their squares, and the
fold's termwise order the spectral read. -/

private def vDiagL {n : Nat} (Et : Mat) (T : SqMat n) : List BPair :=
  (List.range n).map (fun j => dotP (elim.idRow n j)
    (matVec (matMul (transposeM T.val) (matMul Et T.val)) (elim.idRow n j)))

private def kDiagL {n : Nat} (Et : Mat) (T : SqMat n) : List BPair :=
  (List.range n).map (fun j => dotP (elim.idRow n j)
    (matVec (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
      (elim.idRow n j)))

private theorem vDiagL_len {n : Nat} (Et : Mat) (T : SqMat n) :
    (vDiagL Et T).length = n :=
  ground.length_mapRange _ n

private theorem kDiagL_len {n : Nat} (Et : Mat) (T : SqMat n) :
    (kDiagL Et T).length = n :=
  ground.length_mapRange _ n

private theorem vDiagL_get {n : Nat} (Et : Mat) (T : SqMat n) (j : Nat)
    (hj : j < n) :
    ground.getAt BPair.unit (vDiagL Et T) j
      = dotP (elim.idRow n j)
        (matVec (matMul (transposeM T.val) (matMul Et T.val))
          (elim.idRow n j)) := by
  show ground.getAt BPair.unit ((List.range n).map (fun j => dotP
      (elim.idRow n j)
      (matVec (matMul (transposeM T.val) (matMul Et T.val))
        (elim.idRow n j)))) j = _
  rw [ground.getAt_map (0 : Nat) BPair.unit _ (List.range n) j
      (by rw [ground.length_range]; exact hj),
    ground.getAt_range n j hj]

private theorem kDiagL_get {n : Nat} (Et : Mat) (T : SqMat n) (j : Nat)
    (hj : j < n) :
    ground.getAt BPair.unit (kDiagL Et T) j
      = dotP (elim.idRow n j)
        (matVec (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
          (elim.idRow n j)) := by
  show ground.getAt BPair.unit ((List.range n).map (fun j => dotP
      (elim.idRow n j)
      (matVec (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
        (elim.idRow n j)))) j = _
  rw [ground.getAt_map (0 : Nat) BPair.unit _ (List.range n) j
      (by rw [ground.length_range]; exact hj),
    ground.getAt_range n j hj]

private theorem cutSide {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (c : List BPair) (hc : c.length = n) :
    (inertia.quadForm Et (matVec T.val c)).scale (E0 * p)
      ≤ (inertia.quadForm (matMul Et Et) (matVec T.val c)).scale q := by
  have hEt : sqAt Et n := hd.1
  have hEtl : Et.length = n := sqAt_len hEt
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hlo : l.length = n := rootLen Et T Tw l hd
  have hEEl : (matMul Et Et).length = n := by
    rw [show (matMul Et Et).length = Et.length from ground.length_map _ Et]
    exact hEtl
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_cast (transposeLen Et hEtr hEtl) (rowsLen_matMul Et Et)
  have hVd : matOneValue (matMul (transposeM T.val) (matMul Et T.val))
      (split.diagM (vDiagL Et T)) :=
    diagOfEntries _ n (congrShapeL Et T.val n hTl hTr)
      (congrShapeR Et T.val n hEtl hTl hTr)
      (fun i j hi hj hne => vOff Et T Tw l hd i j hi hj hne)
  have hKd : matOneValue
      (matMul (transposeM T.val) (matMul (matMul Et Et) T.val))
      (split.diagM (kDiagL Et T)) :=
    diagOfEntries _ n (congrShapeL (matMul Et Et) T.val n hTl hTr)
      (congrShapeR (matMul Et Et) T.val n hEEl hTl hTr)
      (fun i j hi hj hne => kOff Et T Tw l hsym hd i j hi hj hne)
  have hfV : (inertia.quadForm Et (matVec T.val c)).oneValue
      (dotP (vDiagL Et T) (List.zipWith (· * ·) c c)) := by
    refine BPair.oneValue_trans (dotN_dotP _ _) ?_
    refine BPair.oneValue_trans
      (congrPair Et T.val n hEtl hEtr hTl hTr c c hc hc) ?_
    refine BPair.oneValue_trans
      (dotP_oneValue_right c _ _ (matVec_matOne _ _ c hVd)) ?_
    refine BPair.oneValue_trans (dotP_oneValue_right c _ _
      (diagAct _ c (by rw [vDiagL_len]; exact hc))) ?_
    exact dotP_dmul _ c
  have hfK : (inertia.quadForm (matMul Et Et)
      (matVec T.val c)).oneValue
      (dotP (kDiagL Et T) (List.zipWith (· * ·) c c)) := by
    refine BPair.oneValue_trans (dotN_dotP _ _) ?_
    refine BPair.oneValue_trans
      (congrPair (matMul Et Et) T.val n hEEl hEEr hTl hTr c c hc hc) ?_
    refine BPair.oneValue_trans
      (dotP_oneValue_right c _ _ (matVec_matOne _ _ c hKd)) ?_
    refine BPair.oneValue_trans (dotP_oneValue_right c _ _
      (diagAct _ c (by rw [kDiagL_len]; exact hc))) ?_
    exact dotP_dmul _ c
  refine ground.leB_congr
    (BPair.scale_congr (E0 * p) (BPair.oneValue_symm hfV))
    (BPair.scale_congr q (BPair.oneValue_symm hfK)) ?_
  refine qsumLe (E0 * p) q (vDiagL Et T) (kDiagL Et T) c
    (by rw [vDiagL_len, kDiagL_len]) ?_
  intro j hjv
  rw [vDiagL_len] at hjv
  rw [vDiagL_get Et T j hjv, kDiagL_get Et T j hjv]
  have hjl : j < l.length := by rw [hlo]; exact hjv
  exact termLe (scalePos Et T Tw l hd j hjl _ _ _ rfl)
    (vVal Et T Tw l hd j hjv _ _ _ rfl)
    (kVal Et T Tw l hsym hd j hjv _ _ _ rfl)
    (specGet l E0 p q hs j hjl _ _ _ rfl)

private theorem keyRead {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (u : List BPair) (hu : u.length = n) :
    ¬ ((inertia.quadForm (matMul Et Et) u).scale q
        < (inertia.quadForm Et u).scale (E0 * p)) := by
  intro hlt
  have hEt : sqAt Et n := hd.1
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hTTw : matOneValue (matMul T.val Tw.val)
      (matScaleB (minor T.val) (idMat n)) := hd.2.2.1.2.1
  have hEtl : Et.length = n := sqAt_len hEt
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hEEl : (matMul Et Et).length = n := by
    rw [show (matMul Et Et).length = Et.length from ground.length_map _ Et]
    exact hEtl
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_cast (transposeLen Et hEtr hEtl) (rowsLen_matMul Et Et)
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hTwr : rowsLen n Tw.val := rowsLen_of_sqAt Tw.shape
  have hcl : (matVec Tw.val u).length = n := by rw [matVec_length, hTwl]
  have hxl : (matVec T.val (matVec Tw.val u)).length = n := by
    rw [matVec_length, hTl]
  have hx : poly.oneValue (matVec T.val (matVec Tw.val u))
      (vecScale (minor T.val) u) :=
    poly.oneValue_trans
      (matVec_comp T.val Tw.val u n hTwr hu (rowsLen_cast hTwl.symm hTr))
      (poly.oneValue_trans (matVec_matOne _ _ u hTTw)
        (scaleId_act (minor T.val) n u hu))
  have hmul := mulLtMono (sq_pos hdet) hlt
  rw [← scaleMulR (minor T.val * minor T.val)
      (inertia.quadForm (matMul Et Et) u) q,
    ← scaleMulR (minor T.val * minor T.val)
      (inertia.quadForm Et u) (E0 * p)] at hmul
  refine ground.leB_not_lt
    (cutSide Et T Tw l E0 p q hsym hd hs (matVec Tw.val u) hcl) ?_
  exact BPair.lt_congr
    (BPair.scale_congr q (BPair.oneValue_symm
      (quadScaleVec (matMul Et Et) n hEEr (minor T.val) u hu _ hx)))
    (BPair.scale_congr (E0 * p) (BPair.oneValue_symm
      (quadScaleVec Et n hEtr (minor T.val) u hu _ hx))) hmul

/-- The spectral read is the cut at the window: the level gap's
located spectrum at the kernel point and at or beyond the edge
prices the cut's site datum on its upper side at every vector of
the order, so the datum's split counts no reversal — the
diagonalizing congruence at the located roots the derivation, its
own invertibility the transport back, and `lem:inertia`'s witness
clause the refutation. -/
theorem spec_to_cut {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp) :
    psdAt sp := by
  match Nat.eq_zero_or_pos (revAt sp) with
  | Or.inl h => exact h
  | Or.inr hocc =>
    obtain ⟨u, hu, hlt⟩ := rev_witness _ sp hsp hocc
    have hEt : sqAt Et n := hd.1
    have hEtl : Et.length = n := sqAt_len hEt
    have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
    have hEEl : (matMul Et Et).length = n := by
      rw [show (matMul Et Et).length = Et.length from ground.length_map _ Et]
      exact hEtl
    have hEEr : rowsLen n (matMul Et Et) :=
      rowsLen_cast (transposeLen Et hEtr hEtl) (rowsLen_matMul Et Et)
    exact absurd
      (inertia.scaledSite_gap (by rw [hEEl, hu])
        (by rw [hu]; exact hEEr) (by rw [hEtl, hu]) (by rw [hu]; exact hEtr)
        hlt)
      (keyRead Et T Tw l E0 p q hsym hd hs u hu)

/-! The reading back at the gap's floor datum: the level gap's own
positive-semidefinite split prices every located root on its upper
side (`lem:inertia`'s first transport clause at the eigen column),
and the cut's split then closes the spectral read root by root —
the floor's certificate the sign's source, the two clearings the
root's own members. -/

private theorem rootRead {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (spg : Split n) (hg : splitRead Et spg) (hgp : psdAt spg)
    (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp)
    (hp : psdAt sp) (j : Nat) (hj : j < n) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    (decide (nj.oneValue BPair.unit)
      || !(decide (nj.scale q < BPair.ofPos (E0 * p * dj)))) = true := by
  have hEt : sqAt Et n := hd.1
  have hEtl : Et.length = n := sqAt_len hEt
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hEEl : (matMul Et Et).length = n := by
    rw [show (matMul Et Et).length = Et.length from ground.length_map _ Et]
    exact hEtl
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_cast (transposeLen Et hEtr hEtl) (rowsLen_matMul Et Et)
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hjl : j < l.length := by rw [rootLen Et T Tw l hd]; exact hj
  have hgpos : BPair.unit < gj := scalePos Et T Tw l hd j hjl nj gj dj hroot
  have hvl : (matVec T.val (elim.idRow n j)).length = n := by
    rw [matVec_length, hTl]
  have qE : (inertia.quadForm Et
      (matVec T.val (elim.idRow n j))).oneValue (nj * gj) :=
    BPair.oneValue_trans (dotN_dotP _ _)
      (BPair.oneValue_trans
        (congrPair Et T.val n hEtl hEtr hTl hTr _ _
          (length_idRow n j) (length_idRow n j))
        (vVal Et T Tw l hd j hj nj gj dj hroot))
  have qK : (BPair.ofPos dj * inertia.quadForm (matMul Et Et)
      (matVec T.val (elim.idRow n j))).oneValue (nj * (nj * gj)) :=
    BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (dotN_dotP _ _)
          (congrPair (matMul Et Et) T.val n hEEl hEEr hTl hTr _ _
            (length_idRow n j) (length_idRow n j))))
      (kVal Et T Tw l hsym hd j hj nj gj dj hroot)
  have hgap : ¬ (nj * gj < BPair.unit) := fun hlt =>
    psd_all Et spg hg hgp _ hvl
      (BPair.lt_congr (BPair.oneValue_symm qE)
        (BPair.oneValue_refl BPair.unit) hlt)
  have hnn : BPair.unit ≤ nj :=
    mulLeReflect hgpos
      (ground.leB_congr (BPair.oneValue_symm (BPair.mul_unit gj))
        (BPair.oneValue_of_eq (BPair.mul_comm nj gj))
        (ground.leB_of_not_lt hgap))
  have hside : (inertia.quadForm Et
        (matVec T.val (elim.idRow n j))).scale (E0 * p)
      ≤ (inertia.quadForm (matMul Et Et)
        (matVec T.val (elim.idRow n j))).scale q :=
    ground.leB_of_not_lt
      (inertia.scaledSite_side (by rw [hEEl, hvl])
        (by rw [hvl]; exact hEEr) (by rw [hEtl, hvl])
        (by rw [hvl]; exact hEtr) (psd_all _ sp hsp hp _ hvl))
  have hcl : (nj * BPair.ofPos dj).scale (E0 * p) ≤ (nj * nj).scale q := by
    have h1 := ground.leB_mulR (Or.inr (ground.unitLtOfPos dj)) hside
    rw [← scaleMulR (BPair.ofPos dj) _ (E0 * p),
      ← scaleMulR (BPair.ofPos dj) _ q] at h1
    have h2 : (BPair.ofPos dj * (nj * gj)).scale (E0 * p)
        ≤ (nj * (nj * gj)).scale q :=
      ground.leB_congr
        (BPair.scale_congr (E0 * p)
          (BPair.mul_congr (BPair.oneValue_refl _) qE))
        (BPair.scale_congr q qK) h1
    rw [show BPair.ofPos dj * (nj * gj) = gj * (nj * BPair.ofPos dj) from by
        rw [BPair.mul_left_comm (BPair.ofPos dj) nj gj,
          BPair.mul_comm (BPair.ofPos dj) gj,
          BPair.mul_left_comm nj gj (BPair.ofPos dj)],
      show nj * (nj * gj) = gj * (nj * nj) from by
        rw [BPair.mul_comm nj gj, BPair.mul_left_comm nj gj nj],
      scaleMulR gj (nj * BPair.ofPos dj) (E0 * p),
      scaleMulR gj (nj * nj) q] at h2
    exact mulLeReflect hgpos h2
  by_cases hz : nj.oneValue BPair.unit
  · rw [decide_eq_true hz]
    rfl
  · have hstep : (BPair.ofPos dj).scale (E0 * p) ≤ nj.scale q := by
      refine mulLeReflect (ground.ltOfLeOff hnn hz) ?_
      rw [← scaleMulR nj (BPair.ofPos dj) (E0 * p), ← scaleMulR nj nj q]
      exact hcl
    have hfin : BPair.ofPos (E0 * p * dj) ≤ nj.scale q := by
      refine ground.leB_congr_left ?_ hstep
      refine BPair.oneValue_trans (BPair.scale_ofPos dj (E0 * p)) ?_
      rw [ground.mul_comm dj (E0 * p)]
      exact BPair.oneValue_refl _
    rw [decide_eq_false hz, decide_eq_false (ground.leB_not_lt hfin)]
    rfl

/-- The cut is the spectral read at the window: the level gap's own
floor datum prices every located root on its upper side, and the
cut's split at or above the sum's unit then reads each root at the
kernel point or at or beyond the edge — the eigen columns the
witnesses, the roots' two members the clearings, and
`lem:inertia`'s transport clause the consumption at both splits. -/
theorem cut_to_spec {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (spg : Split n) (hg : splitRead Et spg) (hgp : psdAt spg)
    (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp)
    (hp : psdAt sp) :
    specRead (l.map (fun r => (r.1, r.2.1))) E0 p q := by
  show ((l.map (fun r => (r.1, r.2.1))).all (fun r =>
    decide (r.1.oneValue BPair.unit)
      || !(decide (r.1.scale q < BPair.ofPos (E0 * p * r.2))))) = true
  refine ground.all_of_getAt (BPair.unit, Pos.one) _ _ ?_
  intro j hj
  rw [ground.length_map] at hj
  rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) (BPair.unit, Pos.one)
    _ l j hj]
  exact rootRead Et T Tw l E0 p q hsym hd spg hg hgp sp hsp hp j
    (by rw [← rootLen Et T Tw l hd]; exact hj) _ _ _ rfl

end speccut
