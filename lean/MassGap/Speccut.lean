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

/-- The spectral read's per-root disjunct: at a located root the
read holds at the kernel point or at or beyond the edge. -/
theorem specGet (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
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

/-- The per-root comparison weighted by a square: the two clearings'
order passes a square weight. -/
private theorem termLeSq {vj kj cj : BPair} {E0 p q : Pos}
    (h : vj.scale (E0 * p) ≤ kj.scale q) :
    ((vj * (cj * cj)).scale (E0 * p)) ≤ ((kj * (cj * cj)).scale q) := by
  rw [BPair.scale_mul_left vj (cj * cj) (E0 * p),
    BPair.scale_mul_left kj (cj * cj) q,
    BPair.mul_comm (vj.scale (E0 * p)) (cj * cj),
    BPair.mul_comm (kj.scale q) (cj * cj)]
  exact ground.leB_mulR (ground.unitLeSq cj) h

/-- The spectral read prices the gap's fold summand against the
squared gap's at the two clearings, term by term. -/
theorem foldTermLe {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (c : List BPair) (hc : c.length = n) :
    ∀ j, j < (split.vDiagL Et T).length →
      ((ground.getAt BPair.unit (split.vDiagL Et T) j
          * ground.getAt BPair.unit
            (List.zipWith (· * ·) c c) j).scale (E0 * p))
        ≤ ((ground.getAt BPair.unit (split.vDiagL (matMul Et Et) T) j
            * ground.getAt BPair.unit
              (List.zipWith (· * ·) c c) j).scale q) := by
  intro j hjv
  rw [split.vDiagL_len] at hjv
  have hcj : j < c.length := by rw [hc]; exact hjv
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hjv
  rw [ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·) c c j
      hcj hcj,
    split.vDiagL_get Et T j hjv, split.vDiagL_get (matMul Et Et) T j hjv]
  exact termLeSq (ground.termLe
    (split.scalePos Et T Tw l hd j hjl _ _ _ rfl)
    (split.diagEntryV Et T Tw l hd j hjv _ _ _ rfl)
    (split.diagEntryK Et T Tw l hd j hjv _ _ _ rfl)
    (specGet l E0 p q hs j hjl _ _ _ rfl))


/-! The cut's side at every vector of the order: the two congruated
diagonals' fold displays with the spectral read pricing every
summand, and the congruence's own invertibility carrying the side
back to every vector at the adjugate witness's square. -/

private theorem cutSide {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (c : List BPair) (hc : c.length = n) :
    (inertia.quadForm Et (matVec T.val c)).scale (E0 * p)
      ≤ (inertia.quadForm (matMul Et Et) (matVec T.val c)).scale q := by
  have hfV := split.quadFoldV Et T Tw l hd c hc
  have hfK := split.quadFoldK Et T Tw l hd c hc
  refine ground.leB_congr
    (BPair.scale_congr (E0 * p) (BPair.oneValue_symm hfV))
    (BPair.scale_congr q (BPair.oneValue_symm hfK)) ?_
  exact elim.dotP_le_of_leTerm (E0 * p) q (split.vDiagL Et T)
    (List.zipWith (· * ·) c c) (split.vDiagL (matMul Et Et) T)
    (List.zipWith (· * ·) c c)
    (by rw [split.vDiagL_len, split.vDiagL_len])
    (foldTermLe Et T Tw l E0 p q hd hs c hc)

private theorem keyRead {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hs : specRead (l.map (fun r => (r.1, r.2.1))) E0 p q)
    (u : List BPair) (hu : u.length = n) :
    ¬ ((inertia.quadForm (matMul Et Et) u).scale q
        < (inertia.quadForm Et u).scale (E0 * p)) := by
  intro hlt
  have hEt : sqAt Et n := hd.1
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hEtl : Et.length = n := sqAt_len hEt
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_of_sqAt (sqSquare hEt)
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hcl : (matVec Tw.val u).length = n := by rw [matVec_length, hTwl]
  have hx : poly.oneValue (matVec T.val (matVec Tw.val u))
      (vecScale (minor T.val) u) := split.adjAct Et T Tw l hd u hu
  have hmul := ground.ltB_mulPos hlt (sq_pos hdet)
  rw [BPair.mul_comm ((inertia.quadForm (matMul Et Et) u).scale q)
      (minor T.val * minor T.val),
    BPair.mul_comm ((inertia.quadForm Et u).scale (E0 * p))
      (minor T.val * minor T.val),
    BPair.mul_scale (minor T.val * minor T.val)
      (inertia.quadForm (matMul Et Et) u) q,
    BPair.mul_scale (minor T.val * minor T.val)
      (inertia.quadForm Et u) (E0 * p)] at hmul
  refine ground.leB_not_lt
    (cutSide Et T Tw l E0 p q hd hs (matVec Tw.val u) hcl) ?_
  exact BPair.lt_congr
    (BPair.scale_congr q (BPair.oneValue_symm
      (inertia.quadScaleVec (matMul Et Et) (minor T.val) u _ hx)))
    (BPair.scale_congr (E0 * p) (BPair.oneValue_symm
      (inertia.quadScaleVec Et (minor T.val) u _ hx))) hmul

/-- The spectral read is the cut at the window: the level gap's
located spectrum at the kernel point and at or beyond the edge
prices the cut's site datum on its upper side at every vector of
the order, so the datum's split counts no reversal — the
diagonalizing congruence at the located roots the derivation, its
own invertibility the transport back, and `lem:inertia`'s witness
clause the refutation. -/
theorem spec_to_cut {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
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
    have hEEl : (matMul Et Et).length = n := sqAt_len (sqSquare hEt)
    have hEEr : rowsLen n (matMul Et Et) :=
      rowsLen_of_sqAt (sqSquare hEt)
    exact absurd
      (inertia.scaledSite_gap (by rw [hEEl, hu])
        (by rw [hu]; exact hEEr) (by rw [hEtl, hu]) (by rw [hu]; exact hEtr)
        hlt)
      (keyRead Et T Tw l E0 p q hd hs u hu)

/-! The reading back at the gap's floor datum: the level gap's own
positive-semidefinite split prices every located root on its upper
side (`lem:inertia`'s first transport clause at the eigen column),
and the cut's split then closes the spectral read root by root —
the floor's certificate the sign's source, the two clearings the
root's own members. -/

private theorem rootRead {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos)
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
  have hEEl : (matMul Et Et).length = n := sqAt_len (sqSquare hEt)
  have hEEr : rowsLen n (matMul Et Et) :=
    rowsLen_of_sqAt (sqSquare hEt)
  have hTl : T.val.length = n := SqMat.rows T
  have hjl : j < l.length := by rw [split.rootLen Et T Tw l hd]; exact hj
  have hgpos : BPair.unit < gj :=
    split.scalePos Et T Tw l hd j hjl nj gj dj hroot
  have hvl : (matVec T.val (elim.idRow n j)).length = n := by
    rw [matVec_length, hTl]
  have qE : (inertia.quadForm Et
      (matVec T.val (elim.idRow n j))).oneValue (nj * gj) :=
    split.eigenQuadV Et T Tw l hd j hj nj gj dj hroot
  have qK : (BPair.ofPos dj * inertia.quadForm (matMul Et Et)
      (matVec T.val (elim.idRow n j))).oneValue (nj * (nj * gj)) :=
    split.eigenQuadK Et T Tw l hd j hj nj gj dj hroot
  have hgap : ¬ (nj * gj < BPair.unit) := fun hlt =>
    psd_all Et spg hg hgp _ hvl
      (BPair.lt_congr (BPair.oneValue_symm qE)
        (BPair.oneValue_refl BPair.unit) hlt)
  have hnn : BPair.unit ≤ nj :=
    ground.leB_unscale hgpos
      (ground.leB_congr_left (BPair.oneValue_symm (BPair.unit_mul gj))
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
    rw [BPair.mul_scale (BPair.ofPos dj) _ (E0 * p),
      BPair.mul_scale (BPair.ofPos dj) _ q] at h1
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
      ← BPair.mul_scale gj (nj * BPair.ofPos dj) (E0 * p),
      ← BPair.mul_scale gj (nj * nj) q,
      BPair.mul_comm gj ((nj * BPair.ofPos dj).scale (E0 * p)),
      BPair.mul_comm gj ((nj * nj).scale q)] at h2
    exact ground.leB_unscale hgpos h2
  by_cases hz : nj.oneValue BPair.unit
  · rw [decide_eq_true hz]
    rfl
  · have hstep : (BPair.ofPos dj).scale (E0 * p) ≤ nj.scale q := by
      refine ground.leB_unscale (ground.ltOfLeOff hnn hz) ?_
      rw [← BPair.scale_mul_left (BPair.ofPos dj) nj (E0 * p),
        ← BPair.scale_mul_left nj nj q, BPair.mul_comm (BPair.ofPos dj) nj]
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
  exact rootRead Et T Tw l E0 p q hd spg hg hgp sp hsp hp j
    (by rw [← split.rootLen Et T Tw l hd]; exact hj) _ _ _ rfl

end speccut
