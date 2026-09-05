import MassGap.Momentfold
import MassGap.Cone
import MassGap.Attained
import MassGap.Statespace
/-!
`thm:reconstruct` — the located reconstruction: the passage from the
Euclidean bracket families to the relativistic ones over the located
stage, its inputs the bracketed ground reads (`thm:groundreads`),
the restoration counts with the cone read (`thm:restoration`;
`lem:cone`) and the pairing's definitional positivity
(`def:carrier`), its outputs per member and direction count at
every window of the corner cell.

Clause (i).  Per fiber the energy roots with their weights are the
split's own: the diagonalizing certificate's root list at its
scales (`split.diagRead`), a root's weight the carried column's own
pairing, the scale against the root's clearing (`split.gramDiag`,
`lem:attained`(iii)'s weights at the coordinates' squares).  The
Euclidean families read as the weight folds over them: the upper
witness's power at a probe pair, at the determinant's square, is its
congruated diagonal's fold against the probes' coordinate products,
and each diagonal entry, cleared at the count-against-crossing's
power, is the root's weight at the count-against-clearing's power,
the upper's `[N : N + uγ]` (`euc_hi_fold` at
`groundreads.euc_hi_diag`, `groundreads.euc_hi_root` and
`split.pair_fold`, the certificate's arm the upper datum's own
read); the lower witness's power reads so at the witnessed gap
against the count, the lower's `[g_γ : N]` (`euc_lo_fold` at
`groundreads.euc_lo_diag`, `groundreads.euc_lo_root`), one solved
witness per family, the lower's and the upper's.  On the clearance
cell the moment folds' solve returns the truncated moment vector
from the streams' reads: the adjugate of `lem:momentfold`(ii)'s
square system against the streams' data reads the moment vector at
the determinant's scale (`moment_solve` at
`momentfold.momSys_read` and `inertia.adj_solve`), the
determinant's clearance the located divisor read over the corner
base (`lem:cellcount`).

Clause (ii).  The relativistic bracket families are those data at
the cone's coordinates: per probe pair the family is clause (i)'s
weight fold over the located roots at the fiber's chord
(`euc_hi_fold`, `euc_lo_fold` at the fiber's diagonalized gap), and
the roots' momentum reading is the cone's, at every located root
the locus at the moved level reading the isotropic square at degree
two with the root's located coefficient, the odd degrees at the
sum's unit and the direction data at degree four (`cone.cone_read`
at the profile's degrees, `cone.prof_coef` the coefficient per
root); the families are window-free within the spectator brackets
(`groundreads.window_free`), and the growth caps are their m-point
folds' reads (`groundreads.growth_cap`).

Clause (iii).  The state reads close the families: the pairing's
positivity is the families' own Gram read at every finite probe
list — a family's Gram at a probe list (`famGram`) prices its form
at coefficient data as the family's read at the probes' combination,
the pairing bilinear, that read clause (i)'s fold at the
combination's coordinate squares with every entry at or above the
sum's unit, so every split reads the upper side (`family_hi_psd`,
`family_lo_psd`, the entries' side the pins' at the certificate's
arms); the cut is their spectrum condition (`speccut.cutTie`;
`speccut.spec_to_cut`, `speccut.cut_to_spec`), the word sector is
the state's space (`statespace.pairRead`), and every read holds at
every window ground at once (`lem:speccut`'s tie at every ground);
each output is a located bracket read of the inputs, one solve
(`moment_solve`) and one count (the families' Gram splits and
`speccut.cutTie`'s) per datum.
-/

namespace reconstruct
open ground elim inertia groundreads

/-- Clause (i)'s upper family at the divisor data: at the split's
root list and the certificate's arm, the upper witness's power at a
probe pair reads, at the determinant's square, the congruated
diagonal's fold against the probes' coordinate products, and each
entry cleared at the count-against-crossing's power reads the root's
weight at the count-against-clearing's power — the weight fold over
the located roots at the upper's `[N : N + uγ]`. -/
theorem euc_hi_fold {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (harm : ∀ k, k < l.length →
      ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).oneValue
          BPair.unit
        ∨ ((ground.getAt (BPair.unit, Pos.one,
            BPair.unit) l k).1).oneValue
            (BPair.ofPos (ground.getAt (Pos.one, Pos.one) ws k).1))
    (Vw : Mat) (hVs : sqAt Vw o)
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (x y : List BPair) (hx : x.length = o) (hy : y.length = o) :
    (minor T.val * minor T.val
        * dotP x (matVec (matPow Vw o (n + 1)) y)).oneValue
      (dotP (split.vDiagL (matPow Vw o (n + 1)) T)
        (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y)))
    ∧ ∀ j, j < o → ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      (ground.bpow (BPair.ofPos (posOfSucc n * (ud * dj)) + nj.scale un)
            (n + 1)
          * ground.getAt BPair.unit
              (split.vDiagL (matPow Vw o (n + 1)) T) j).oneValue
        (ground.bpow (BPair.ofPos ((posOfSucc n * (ud * dj)) * vc))
            (n + 1)
          * (gj * BPair.ofPos dj)) :=
  ⟨split.pair_fold Et T Tw l hd (matPow Vw o (n + 1))
      (length_matPow Vw o (sqAt_len hVs) (n + 1))
      (rowsLen_matPow Vw o (sqAt_len hVs) (n + 1))
      (euc_hi_diag Et T Tw l hd un ud vc n ws harm Vw hVs hV) x y hx hy,
    fun j hj nj gj dj hroot =>
      euc_hi_root Et T Tw l hd un ud vc n ws harm Vw hVs hV j hj nj gj dj
        hroot⟩

/-- Clause (i)'s lower family at the divisor data: the lower
witness's power at a probe pair reads, at the determinant's square,
the congruated diagonal's fold against the probes' coordinate
products, and each entry cleared at the count's power reads the
root's weight at the witnessed gap against the clearing's power —
the weight fold over the located roots at the lower's `[g_γ : N]`,
the certificate's gap witnesses the read's data. -/
theorem euc_lo_fold {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw : Mat) (hLs : sqAt Lw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (x y : List BPair) (hx : x.length = o) (hy : y.length = o) :
    (minor T.val * minor T.val
        * dotP x (matVec (matPow Lw o (n + 1)) y)).oneValue
      (dotP (split.vDiagL (matPow Lw o (n + 1)) T)
        (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y)))
    ∧ ∀ j, j < o → ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      (ground.bpow (BPair.ofPos (posOfSucc n * (ud * dj))) (n + 1)
          * ground.getAt BPair.unit
              (split.vDiagL (matPow Lw o (n + 1)) T) j).oneValue
        (ground.bpow
            (BPair.ofPos ((ground.getAt (Pos.one, Pos.one) ws j).2 * lc))
            (n + 1)
          * (gj * BPair.ofPos dj)) :=
  ⟨split.pair_fold Et T Tw l hd (matPow Lw o (n + 1))
      (length_matPow Lw o (sqAt_len hLs) (n + 1))
      (rowsLen_matPow Lw o (sqAt_len hLs) (n + 1))
      (euc_lo_diag Et T Tw l hd un ud kn kd lc n ws hw Lw hLs hL) x y hx hy,
    fun j hj nj gj dj hroot =>
      euc_lo_root Et T Tw l hd un ud kn kd lc n ws hw Lw hLs hL j hj nj gj
        dj hroot⟩

/-- Clause (i)'s moment solve: at the ground's recurrence, the
diagonal's quadratic profile and the constant bond, the adjugate of
the square system at a stated degree against the streams' data reads
the truncated moment vector at the determinant's scale — the moment
folds' solve returning the vector from the streams' reads, the
adjugate's solve read at the system's read (`momentfold.momSys_read`,
`inertia.adj_solve`). -/
theorem moment_solve (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (K : Nat) (h : momentfold.recRead a b psi)
    (hp : momentfold.diagProf a p2 p1 p0)
    (hb : momentfold.constBond b β) (hK : 1 ≤ K) :
    poly.oneValue
      (matVec (adjM (momentfold.momSys K p2 p1 p0 β))
        (momentfold.momRhs psi β K))
      (vecScale (detL (momentfold.momSys K p2 p1 p0 β))
        (momentfold.momVec psi K)) := by
  have hlen : (momentfold.momVec psi K).length = K + 1 + (K + 1 + 1) := by
    show ((List.range (K + 1)).map (fun j => momentfold.mrho psi j)
      ++ ((List.range (K + 1)).map (fun j => momentfold.mc psi j)
        ++ [momentfold.bSq psi])).length = K + 1 + (K + 1 + 1)
    rw [ground.length_append, ground.length_append, ground.length_map,
      ground.length_map, ground.length_range]
    rfl
  exact inertia.adj_solve _
    (sqAt_of (momentfold.momSys_len K p2 p1 p0 β hK)
      (momentfold.momSys_rowsLen K p2 p1 p0 β))
    _ _ hlen (momentfold.momSys_read a b psi p2 p1 p0 β K h hp hb hK)

/-! Clause (iii)'s positivity: a family's Gram at a probe list is
its reads at the probe pairs, and its form at coefficient data is
the family's read at the probes' combination, the pairing bilinear;
at a family congruated to a diagonal at or above the sum's unit that
read is the diagonal's fold at the combination's coordinate squares,
so every split of the Gram reads the upper side. -/

/-- A family's Gram at a probe list: the family's reads at the probe
pairs, one row per probe. -/
def famGram (M : Mat) (P : List (List BPair)) : Mat :=
  P.map (fun x => P.map (fun y => dotP x (matVec M y)))

/-- A family congruated to a diagonal at or above the sum's unit has
its Gram at every probe list positive semidefinite: the Gram's form
at coefficient data is the family's read at the probes' combination
(`elim.dotP_combo`, `elim.matVec_combo`), that read the diagonal's
fold at the combination's coordinate squares (`split.pair_fold`) at
or above the sum's unit (`elim.dotP_unitLe`), and every split then
reads the upper side (`inertia.psd_of_all`). -/
private theorem foldGram_psd {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (M : Mat) (hMl : M.length = o) (hMr : rowsLen o M)
    (hDiag : matOneValue (matMul (transposeM T.val) (matMul M T.val))
      (split.diagM (split.vDiagL M T)))
    (hpos : ∀ j, j < o →
      BPair.unit ≤ ground.getAt BPair.unit (split.vDiagL M T) j)
    (P : List (List BPair)) (hP : rowsLen o P)
    (sp : Split P.length) (h : splitRead (famGram M P) sp) : psdAt sp := by
  refine psd_of_all (famGram M P) sp h (fun u hu hlt => ?_)
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hTwl : Tw.val.length = o := SqMat.rows Tw
  have hMP : rowsLen o (P.map (matVec M)) :=
    rowsLen_map (matVec M) o P (fun x _ => (matVec_length M x).trans hMl)
  have hzl : (combo o u P).length = o := length_combo o u P hP
  have hcl : (matVec Tw.val (combo o u P)).length = o := by
    rw [matVec_length, hTwl]
  have hcomb : poly.oneValue (matVec M (combo o u P))
      (combo o u (P.map (matVec M))) := by
    have hc := matVec_combo M o u P hP
    rw [hMl] at hc
    exact hc
  -- the Gram's action at the coefficients is the family's read at
  -- the combination, row by row
  have hrow : poly.oneValue (matVec (famGram M P) u)
      (P.map (fun x => dotP x (matVec M (combo o u P)))) := by
    show poly.oneValue
      ((P.map (fun x => P.map (fun y => dotP x (matVec M y)))).map
        (fun row => dotN row u))
      (P.map (fun x => dotP x (matVec M (combo o u P))))
    rw [ground.map_map]
    refine poly.oneValue_map _ _ P (fun x _ => ?_)
    refine BPair.oneValue_trans (dotN_read _ u) ?_
    rw [dotP_comm,
      show P.map (fun y => dotP x (matVec M y))
        = (P.map (matVec M)).map (fun row => dotP x row) from
        (ground.map_map _ _ P).symm]
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (dotP_combo u (P.map (matVec M)) x o hMP)) ?_
    exact dotP_oneValue_right x _ _ (poly.oneValue_symm hcomb)
  -- the form at the coefficients is the combination's own read
  have hq : (dotN u (matVec (famGram M P) u)).oneValue
      (dotP (combo o u P) (matVec M (combo o u P))) := by
    refine BPair.oneValue_trans (dotN_congrR u _ _ hrow) ?_
    refine BPair.oneValue_trans (dotN_read u _) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_of_eq
        (dotP_comm (matVec M (combo o u P)) (combo o u P)))
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (dotP_combo u P (matVec M (combo o u P)) o hP))
    rw [dotP_comm u, dotP_comm u]
    refine dotP_congr_left _ _ u (fun j hj => ?_)
    have hjP : j < P.length := hu ▸ hj
    rw [show ground.getAt BPair.unit
          (P.map (fun x => dotP x (matVec M (combo o u P)))) j
        = dotP (ground.getAt [] P j) (matVec M (combo o u P)) from
        ground.getAt_map [] BPair.unit _ P j hjP,
      show ground.getAt BPair.unit
          (P.map (fun row => dotP (matVec M (combo o u P)) row)) j
        = dotP (matVec M (combo o u P)) (ground.getAt [] P j) from
        ground.getAt_map [] BPair.unit _ P j hjP,
      dotP_comm]
    exact BPair.oneValue_refl _
  -- the fold at the coordinate squares sits at or above the unit
  have hfold := split.pair_fold Et T Tw l hd M hMl hMr hDiag
    (combo o u P) (combo o u P) hzl hzl
  have hge : BPair.unit ≤ dotP (split.vDiagL M T)
      (List.zipWith (· * ·) (matVec Tw.val (combo o u P))
        (matVec Tw.val (combo o u P))) := by
    refine dotP_unitLe _ _ (fun j hj => ?_)
    rw [split.vDiagL_len M T] at hj
    rw [ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
      (matVec Tw.val (combo o u P)) (matVec Tw.val (combo o u P)) j
      (by rw [hcl]; exact hj) (by rw [hcl]; exact hj)]
    exact ground.unitLeMul (hpos j hj) (ground.unitLeSq _)
  have hX : dotP (combo o u P) (matVec M (combo o u P)) < BPair.unit :=
    BPair.lt_congr hq (BPair.oneValue_refl _) hlt
  have h1 := ground.ltB_mulPos hX (ground.sq_pos hdet)
  have h2 : minor T.val * minor T.val
      * dotP (combo o u P) (matVec M (combo o u P)) < BPair.unit :=
    BPair.lt_congr (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.unit_mul _) h1
  exact ground.leB_not_lt
    (ground.leB_congr_right (BPair.oneValue_symm hfold) hge) h2

/-- A pinned diagonal entry sits at or above the sum's unit: at the
two clearings and the weight strictly above it, the pin's read puts
the entry strictly above it. -/
private theorem entry_pos {cd cn D w : BPair} (hcd : BPair.unit < cd)
    (hcn : BPair.unit < cn) (hw : BPair.unit < w)
    (hpin : (cd * D).oneValue (cn * w)) : BPair.unit ≤ D :=
  ground.leB_of_lt (ground.unitLt_unscale (ground.leB_of_lt hcd)
    (BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hpin)
      (ground.unitLtMul hcn hw)))

/-- Clause (iii)'s positivity at the upper family: at the split's
root list, the certificate's arm and the upper witness, the family's
Gram at every probe list is positive semidefinite — the pinned
entries at or above the sum's unit at the arm's collected scale, the
weights the gram's positive scales against the roots' clearings, the
fold then on its upper side at every coefficient datum. -/
theorem family_hi_psd {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (harm : ∀ k, k < l.length →
      ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).oneValue
          BPair.unit
        ∨ ((ground.getAt (BPair.unit, Pos.one,
            BPair.unit) l k).1).oneValue
            (BPair.ofPos (ground.getAt (Pos.one, Pos.one) ws k).1))
    (Vw : Mat) (hVs : sqAt Vw o)
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (P : List (List BPair)) (hP : rowsLen o P)
    (sp : Split P.length)
    (h : splitRead (famGram (matPow Vw o (n + 1)) P) sp) : psdAt sp := by
  refine foldGram_psd Et T Tw l hd (matPow Vw o (n + 1))
    (length_matPow Vw o (sqAt_len hVs) (n + 1))
    (rowsLen_matPow Vw o (sqAt_len hVs) (n + 1))
    (euc_hi_diag Et T Tw l hd un ud vc n ws harm Vw hVs hV)
    (fun j hj => ?_) P hP sp h
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
         (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1,
         (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2) := rfl
  have hpin := euc_hi_root Et T Tw l hd un ud vc n ws harm Vw hVs hV
    j hj _ _ _ hroot
  -- the collected scale is positive at either arm
  have hY : BPair.unit
      ≤ ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1).scale un :=
    (harm j hjl).elim
      (fun hk => ground.leB_congr_right
        (BPair.oneValue_trans (ground.unitScale un)
          (BPair.oneValue_symm (BPair.scale_congr un hk)))
        (ground.leB_refl _))
      (fun hp => ground.leB_congr_right
        (BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.scale_congr un hp)
            (BPair.scale_ofPos _ un)))
        (ground.leB_of_lt (ground.unitLtOfPos _)))
  have hcd : BPair.unit
      < BPair.ofPos (posOfSucc n
          * (ud * (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1))
        + ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1).scale un :=
    ground.unitLtAdd (ground.unitLtOfPos _) hY
  exact entry_pos (ground.unitLtBpow hcd (n + 1))
    (ground.unitLtBpow (ground.unitLtOfPos _) (n + 1))
    (ground.unitLtMul (split.scalePos Et T Tw l hd j hjl _ _ _ hroot)
      (ground.unitLtOfPos _))
    hpin

/-- Clause (iii)'s positivity at the lower family: at the split's
root list, the certificate and the lower witness, the family's Gram
at every probe list is positive semidefinite — the pinned entries at
or above the sum's unit at the count's and the witnessed gap's
powers, the weights the gram's positive scales against the roots'
clearings. -/
theorem family_lo_psd {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw : Mat) (hLs : sqAt Lw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (P : List (List BPair)) (hP : rowsLen o P)
    (sp : Split P.length)
    (h : splitRead (famGram (matPow Lw o (n + 1)) P) sp) : psdAt sp := by
  refine foldGram_psd Et T Tw l hd (matPow Lw o (n + 1))
    (length_matPow Lw o (sqAt_len hLs) (n + 1))
    (rowsLen_matPow Lw o (sqAt_len hLs) (n + 1))
    (euc_lo_diag Et T Tw l hd un ud kn kd lc n ws hw Lw hLs hL)
    (fun j hj => ?_) P hP sp h
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
         (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1,
         (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2) := rfl
  exact entry_pos (ground.unitLtBpow (ground.unitLtOfPos _) (n + 1))
    (ground.unitLtBpow (ground.unitLtOfPos _) (n + 1))
    (ground.unitLtMul (split.scalePos Et T Tw l hd j hjl _ _ _ hroot)
      (ground.unitLtOfPos _))
    (euc_lo_root Et T Tw l hd un ud kn kd lc n ws hw Lw hLs hL j hj _ _ _
      hroot)

end reconstruct
