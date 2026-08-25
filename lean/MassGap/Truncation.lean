import MassGap.Certconstruct
/-!
`thm:truncation` — the magnetic cap's transports at the truncation's
site data.

At the coupling `[α : β]` the truncation is a projection and the
off-block coupling of `H` is the magnetic form's alone, `E` being
diagonal reading its off-block part at the sum's unit.  The magnetic
part's two-sided cap is the stated cap datum `inertia.capAt` at
`W · G` — the per-plaquette pricing `lem:loopcap`'s at the interface
tier, arriving with the member pencil families, `W = β #p d_θ` the
adjoint dimension against the region's plaquette count — and the two
blocking ties are the pencil's `M` at `[M₁, B; Bᵀ, M₂]` and its gram
at the block diagonal `[G₁, ·; ·, G₂]` over `elim.nullMat`'s vacant
slab, the coupling block `B` shared by both.

`removed_psd` reads the removed block's floor at the cross-added
comparison `W + f ≥ αΛ_C`: at a level tie `x + W + g = c + y` the
removed block's site datum reads one value with the diagonal's own
datum, the cap's lower split at `W G₂ + M₂`, and a positive gram
multiple, and the three at-or-above reads meet the witness's strict
one.

`shiftSite` is the polarization display's matrix at the witness gap's
clearing, `[W²G₁, ςB; ςBᵀ, ς²G₂]`, and `polar_psd` reads it positive
semidefinite by the tex's own route: the cap's two splits, read at the
vector `W x + ς y` and at its partner `W x + ς y̌` with `y̌` the
memberwise swap of `y`, withdraw the diagonal blocks' reads between the
two reads — `M₁`'s own against its partner, `M₂`'s likewise — and the
surviving terms collect on the shift site at the doubled weight `2W`,
the cofactor `ς c_W = W²` riding the display.  `shift_psd` discharges
the difference site through that polarization at the scaled tie, the
reversal count blind to the positive factor
(`inertia.scaleSplit`, `lem:inertia`'s rescaling invariance).

The two count reads are `lem:inertia`'s: `count_full_le` prices the
counts monotone under the shifted comparison, the block diagonal's
count the head block's alone at the vacant coupling
(`inertia.rev_mono` with `inertia.rev_join`), and `count_head_le` is
the compression side, the head block's count at or below the fiber
datum's own (`inertia.rev_head_le` at the site tie).  `count_shift_le`
composes the shifted side whole at the raised levels, and beside
`count_head_le` it prices the bracket display
`E₀ ς 𝒦 ≤ E₀ ς 𝒦_Λ + β² #p² d_θ²` — one pair comparison each way at
every `α`, the cut level read at `thm:gappos`'s tier.
-/

namespace truncation
open ground elim inertia certconstruct

/-- The polarization display's matrix at the witness gap's clearing:
`[W²G₁, ςB; ςBᵀ, ς²G₂]`, the shifted split's site datum weighted by
the gap. -/
def shiftSite (W s : Pos) (B G1 G2 : Mat) : Mat :=
  inertia.blockJoin (inertia.matScale (W * W) G1)
    (inertia.matScale s B) (inertia.matScale (s * s) G2)

/-- The pairing at two weighted vectors carries both weights out. -/
private theorem bilinScale (A : Mat) (n : Nat) (hAr : rowsLen n A)
    (c d : BPair) (u w : List BPair) (hw : w.length = n) :
    (dotN (vecScale c u) (matVec A (vecScale d w))).oneValue
      (d * (c * dotN u (matVec A w))) := by
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right _ _ _ (matVec_vecScale A n hAr d w hw)) ?_
  refine BPair.oneValue_trans (dotP_vecScale_right _ _ d) ?_
  refine BPair.mul_congr (BPair.oneValue_refl d) ?_
  rw [dotP_comm (vecScale c u) (matVec A w)]
  refine BPair.oneValue_trans (dotP_vecScale_right _ _ c) ?_
  refine BPair.mul_congr (BPair.oneValue_refl c) ?_
  rw [dotP_comm (matVec A w) u]
  exact BPair.oneValue_symm (dotN_read u (matVec A w))

/-- The coupling's exchange at a pairing: the transpose's action
against one vector is the datum's action against the other. -/
private theorem crossFlip (A : Mat) (n : Nat) (hAr : rowsLen n A)
    (u w : List BPair) (hu : u.length = n) (hw : w.length = A.length) :
    (dotN u (matVec (transposeM A) w)).oneValue (dotN w (matVec A u)) := by
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (dotP_matVec_transpose n A u w hAr hu hw)) ?_
  rw [dotP_comm (matVec A u) w]
  exact BPair.oneValue_symm (dotN_read w (matVec A u))

/-- A rescaled datum's pairing carries the ground weight out at the
balance weighting. -/
private theorem scaledCross (w : Pos) (A : Mat) (u v : List BPair) :
    (dotN u (matVec (matScale w A) v)).oneValue
      (BPair.ofPos w * dotN u (matVec A v)) := by
  refine BPair.oneValue_trans
    (dotN_congrR u _ _ (inertia.matVec_matScale w A v)) ?_
  refine BPair.oneValue_trans (dotN_read u _) ?_
  refine BPair.oneValue_trans (dotP_vecScale_right u (matVec A v) _) ?_
  exact BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (dotN_read u (matVec A v)))

/-- The squared weight against the twice-applied balance weighting. -/
private theorem scaleSq (w : Pos) (z : BPair) :
    (z.scale (w * w)).oneValue (BPair.ofPos w * (BPair.ofPos w * z)) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos w))
        (BPair.ofPos_scale w z))
      (BPair.oneValue_trans (BPair.ofPos_scale w (z.scale w))
        (BPair.oneValue_of_eq (BPair.scale_scale z w w))))

/-- A diagonal block's read at the weighted vector is the squared
weight's own rescaling of the block. -/
private theorem sqRead (w : Pos) (A : Mat) (n : Nat) (hAr : rowsLen n A)
    (u : List BPair) (hu : u.length = n) :
    (dotN (vecScale (BPair.ofPos w) u)
        (matVec A (vecScale (BPair.ofPos w) u))).oneValue
      (dotN u (matVec (matScale (w * w) A) u)) :=
  BPair.oneValue_trans
    (bilinScale A n hAr (BPair.ofPos w) (BPair.ofPos w) u u hu)
    (BPair.oneValue_trans
      (BPair.oneValue_symm (scaleSq w (dotN u (matVec A u))))
      (BPair.oneValue_trans
        (BPair.oneValue_symm
          (BPair.ofPos_scale (w * w) (dotN u (matVec A u))))
        (BPair.oneValue_symm (scaledCross (w * w) A u u))))

/-- The polarization's regrouping: the cap read at the weighted
vector is the shift site's own read at the outer weight beside the
two diagonal blocks. -/
private theorem polarL (w gx gy t mx qy : BPair) :
    w * (gx + gy) + ((mx + w * t) + (w * t + qy))
      = w * ((gx + t) + (t + gy)) + (mx + qy) := by
  rw [BPair.left_distrib w gx gy, BPair.left_distrib w (gx + t) (t + gy),
    BPair.left_distrib w gx t, BPair.left_distrib w t gy,
    BPair.add_add_comm (w * gx) (w * gy) (mx + w * t) (w * t + qy),
    BPair.add_comm mx (w * t),
    BPair.add_left_comm (w * gy) (w * t) qy,
    BPair.add_add_comm (w * gx + w * t) (w * t + w * gy) mx qy,
    BPair.add_assoc (w * gx) (w * t) mx,
    BPair.add_assoc (w * t) (w * gy) qy]

/-- A datum and its partner withdraw from the two reads' join. -/
private theorem addSwapCollect (z K : BPair) :
    ((z + K) + (z + K.swap)).oneValue (z + z) := by
  rw [BPair.add_assoc z K, BPair.add_left_comm K z K.swap,
    ← BPair.add_assoc z z]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl (z + z))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm K K.swap))
        (BPair.swap_add_null (BPair.oneValue_refl K))))
    (BPair.add_unit (z + z))

/-- The polarization's close: the cap's two reads at or above the
sum's unit join to the shift site's read at the doubled outer
weight, which refuses a shift-site read strictly below it. -/
private theorem polarClose (w z gx gy t mx qy : BPair)
    (h1 : BPair.unit ≤ w * (gx + gy) + ((mx + w * t) + (w * t + qy)))
    (h2 : BPair.unit
      ≤ w * (gx + gy) + ((mx.swap + w * t) + (w * t + qy.swap)))
    (hz : ((gx + t) + (t + gy)).oneValue z)
    (hlt : z < BPair.unit) (hw : BPair.unit < w) : False := by
  rw [polarL w gx gy t mx qy] at h1
  rw [polarL w gx gy t mx.swap qy.swap] at h2
  have h2' : BPair.unit ≤ w * ((gx + t) + (t + gy)) + (mx + qy).swap := h2
  have hsum := ground.leB_congr_right (addSwapCollect _ _)
    (ground.unitLeAdd h1 h2')
  have hzz : (w * ((gx + t) + (t + gy))).oneValue (w * z) :=
    BPair.mul_congr (BPair.oneValue_refl w) hz
  have hfin : BPair.unit ≤ w * z + w * z :=
    ground.leB_congr_right (BPair.add_congr hzz hzz) hsum
  have hwz : w * z < BPair.unit :=
    BPair.lt_congr (BPair.oneValue_of_eq (BPair.mul_comm z w))
      (BPair.unit_mul w) (ground.ltB_mulPos hlt hw)
  exact absurd (ltUnitAddLe hwz (ground.leB_of_lt hwz))
    (ground.leB_not_lt hfin)

/-- `thm:truncation`'s polarization: the cap's two splits, read at
the vector `W x + ς y` and at its partner `W x + ς y̌`, collect to
the shift site's positive-semidefinite read.  The two diagonal
blocks' reads withdraw between the two reads, the coupling's two
pairings double, and the gram's two reads double with them, so the
joined read prices the shift site at the doubled weight `2W` — a
shift-site vector strictly below the sum's unit is refused there. -/
theorem polar_psd {k m : Nat} (M G M1 M2 B G1 G2 : Mat) (W s : Pos)
    (spU spL : Split (k + m))
    (hcap : capAt M (matScale W G) spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hGt : matOneValue G (blockJoin G1 (elim.nullMat k m) G2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hG1 : sqAt G1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (sp : Split (k + m))
    (hsp : splitRead (shiftSite W s B G1 G2) sp) :
    psdAt sp := by
  cases Nat.eq_zero_or_pos k with
  | inl hk =>
    subst hk
    have hBnil : B = [] := by
      cases B with
      | nil => rfl
      | cons r t => exact Nat.noConfusion hB
    have h0 : (shiftSite W s B G1 G2).length = 0 := by
      rw [hBnil]
      show (List.zipWith (· ++ ·) (matScale (W * W) G1) ([] : Mat)
        ++ List.zipWith (· ++ ·) (transposeM ([] : Mat))
          (matScale (s * s) G2)).length = 0
      rw [ground.zipWith_nil_right (· ++ ·) (matScale (W * W) G1)]
      rfl
    have hm : m = 0 := by
      have h1 : (0 : Nat) = 0 + m := h0.symm.trans (elim.sqAt_len hsp.1)
      rw [Nat.zero_add] at h1
      exact h1.symm
    subst hm
    exact revAt_zero sp
  | inr hkpos =>
    cases Nat.eq_zero_or_pos (revAt sp) with
    | inl h => exact h
    | inr hocc =>
      obtain ⟨v0, hv0, hlt⟩ := rev_witness _ sp hsp hocc
      obtain ⟨x, y, hvxy, hx⟩ := ground.listSplit v0 k
        (by rw [hv0]; exact Nat.le_add_right k m)
      rw [hvxy] at hv0 hlt
      have hy : y.length = m := by
        have h2 := ground.length_append x y
        rw [hx] at h2
        exact ground.addCancelL k (h2.symm.trans hv0)
      have hG1r : rowsLen k G1 := elim.rowsLen_of_sqAt hG1
      have hG1l : G1.length = k := elim.sqAt_len hG1
      have hG2r : rowsLen m G2 := elim.rowsLen_of_sqAt hG2
      have hG2l : G2.length = m := elim.sqAt_len hG2
      have hM1r : rowsLen k M1 := elim.rowsLen_of_sqAt hM1
      have hM1l : M1.length = k := elim.sqAt_len hM1
      have hBt : (transposeM B).length = m :=
        elim.length_transposeM B hBr (by rw [hB]; exact hkpos)
      have hBtr : rowsLen k (transposeM B) :=
        elim.rowsLen_cast hB (elim.rowsLen_transposeM B)
      have hNl : (nullMat k m).length = k := elim.length_nullMat k m
      have hNr : rowsLen m (nullMat k m) := elim.rowsLen_nullMat k m
      have hNt : (transposeM (nullMat k m)).length = m :=
        elim.length_transposeM (nullMat k m) hNr (by rw [hNl]; exact hkpos)
      have hNtr : rowsLen k (transposeM (nullMat k m)) :=
        elim.rowsLen_cast hNl (elim.rowsLen_transposeM (nullMat k m))
      have hSBl : (matScale s B).length = k := (length_matScale s B).trans hB
      have hSBr : rowsLen m (matScale s B) :=
        elim.rowsLen_mapRows (fun z => z.scale s) B m hBr
      have hSBt : (transposeM (matScale s B)).length = m :=
        elim.length_transposeM (matScale s B) hSBr (by rw [hSBl]; exact hkpos)
      have hSBtr : rowsLen k (transposeM (matScale s B)) :=
        elim.rowsLen_cast hSBl (elim.rowsLen_transposeM (matScale s B))
      have hXl : (vecScale (BPair.ofPos W) x).length = k :=
        (elim.length_vecScale _ x).trans hx
      have hYl : (vecScale (BPair.ofPos s) y).length = m :=
        (elim.length_vecScale _ y).trans hy
      have hY'l : ((vecScale (BPair.ofPos s) y).map BPair.swap).length = m :=
        (ground.length_map _ _).trans hYl
      have hvl : ((vecScale (BPair.ofPos W) x)
          ++ (vecScale (BPair.ofPos s) y)).length = k + m := by
        rw [ground.length_append, hXl, hYl]
      have hv'l : ((vecScale (BPair.ofPos W) x)
          ++ (vecScale (BPair.ofPos s) y).map BPair.swap).length = k + m := by
        rw [ground.length_append, hXl, hY'l]
      have hGjoin : ∀ a b : List BPair, a.length = k → b.length = m →
          (dotN (a ++ b) (matVec G (a ++ b))).oneValue
            (dotN a (matVec G1 a) + dotN b (matVec G2 b)) := by
        intro a b ha hb
        refine BPair.oneValue_trans
          (quadMatOne G (blockJoin G1 (nullMat k m) G2) _ hGt) ?_
        refine BPair.oneValue_trans
          (quadJoin G1 (nullMat k m) G2 k m hG1r hG1l hNl hNt hNtr hG2l
            a b a b ha hb ha) ?_
        exact BPair.add_congr
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl _)
              (dotN_nullR a _ (elim.matVec_nullMat k m b)))
            (BPair.add_unit _))
          (BPair.oneValue_trans
            (BPair.add_congr
              (dotN_nullR b _ (elim.matVec_matNull _ a
                (elim.matNull_transposeM _ (elim.matNull_nullMat m k))))
              (BPair.oneValue_refl _))
            (BPair.unit_add _))
      have hMjoin : ∀ a b : List BPair, a.length = k → b.length = m →
          (dotN (a ++ b) (matVec M (a ++ b))).oneValue
            ((dotN a (matVec M1 a) + dotN a (matVec B b))
              + (dotN b (matVec (transposeM B) a)
                + dotN b (matVec M2 b))) :=
        fun a b ha hb =>
          BPair.oneValue_trans (quadMatOne M (blockJoin M1 B M2) _ hMt)
            (quadJoin M1 B M2 k m hM1r hM1l hB hBt hBtr hM2l a b a b ha hb ha)
      have hmul : ∀ z : BPair, BPair.ofPos s * (BPair.ofPos W * z)
          = BPair.ofPos W * (BPair.ofPos s * z) := by
        intro z
        rw [← BPair.mul_assoc, BPair.mul_comm (BPair.ofPos s) (BPair.ofPos W),
          BPair.mul_assoc]
      have hcc : (dotN (vecScale (BPair.ofPos W) x)
            (matVec B (vecScale (BPair.ofPos s) y))).oneValue
          (BPair.ofPos W * dotN x (matVec (matScale s B) y)) :=
        BPair.oneValue_trans
          (bilinScale B m hBr (BPair.ofPos W) (BPair.ofPos s) x y hy)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (hmul (dotN x (matVec B y))))
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_symm (scaledCross s B x y))))
      have hdyx : (dotN (vecScale (BPair.ofPos s) y)
            (matVec (transposeM B) (vecScale (BPair.ofPos W) x))).oneValue
          (BPair.ofPos W * dotN x (matVec (matScale s B) y)) :=
        BPair.oneValue_trans
          (crossFlip B m hBr (vecScale (BPair.ofPos s) y)
            (vecScale (BPair.ofPos W) x) hYl (hXl.trans hB.symm))
          hcc
      have hT : (dotN (x ++ y)
            (matVec (shiftSite W s B G1 G2) (x ++ y))).oneValue
          ((dotN (vecScale (BPair.ofPos W) x)
              (matVec G1 (vecScale (BPair.ofPos W) x))
             + dotN x (matVec (matScale s B) y))
            + (dotN x (matVec (matScale s B) y)
              + dotN (vecScale (BPair.ofPos s) y)
                (matVec G2 (vecScale (BPair.ofPos s) y)))) :=
        BPair.oneValue_trans
          (quadJoin (matScale (W * W) G1) (matScale s B) (matScale (s * s) G2)
            k m (elim.rowsLen_mapRows (fun z => z.scale (W * W)) G1 k hG1r)
            ((length_matScale (W * W) G1).trans hG1l)
            hSBl hSBt hSBtr ((length_matScale (s * s) G2).trans hG2l)
            x y x y hx hy hx)
          (BPair.add_congr
            (BPair.add_congr
              (BPair.oneValue_symm (sqRead W G1 k hG1r x hx))
              (BPair.oneValue_refl _))
            (BPair.add_congr
              (crossFlip (matScale s B) m hSBr y x hy (hx.trans hSBl.symm))
              (BPair.oneValue_symm (sqRead s G2 m hG2r y hy))))
      have hMv : (dotN ((vecScale (BPair.ofPos W) x)
            ++ (vecScale (BPair.ofPos s) y))
            (matVec M ((vecScale (BPair.ofPos W) x)
              ++ (vecScale (BPair.ofPos s) y)))).oneValue
          ((dotN (vecScale (BPair.ofPos W) x)
              (matVec M1 (vecScale (BPair.ofPos W) x))
            + BPair.ofPos W * dotN x (matVec (matScale s B) y))
            + (BPair.ofPos W * dotN x (matVec (matScale s B) y)
              + dotN (vecScale (BPair.ofPos s) y)
                (matVec M2 (vecScale (BPair.ofPos s) y)))) :=
        BPair.oneValue_trans (hMjoin _ _ hXl hYl)
          (BPair.add_congr
            (BPair.add_congr (BPair.oneValue_refl _) hcc)
            (BPair.add_congr hdyx (BPair.oneValue_refl _)))
      have hMv' : (dotN ((vecScale (BPair.ofPos W) x)
            ++ (vecScale (BPair.ofPos s) y).map BPair.swap)
            (matVec M ((vecScale (BPair.ofPos W) x)
              ++ (vecScale (BPair.ofPos s) y).map BPair.swap))).oneValue
          ((dotN (vecScale (BPair.ofPos W) x)
              (matVec M1 (vecScale (BPair.ofPos W) x))
            + (BPair.ofPos W * dotN x (matVec (matScale s B) y)).swap)
            + ((BPair.ofPos W * dotN x (matVec (matScale s B) y)).swap
              + dotN (vecScale (BPair.ofPos s) y)
                (matVec M2 (vecScale (BPair.ofPos s) y)))) := by
        refine BPair.oneValue_trans (hMjoin _ _ hXl hY'l) ?_
        rw [elim.matVec_swapArg (vecScale (BPair.ofPos s) y) B, elim.dotN_swap,
          elim.dotN_swapLeft,
          elim.dotN_matVec_swapMap M2 (vecScale (BPair.ofPos s) y)]
        exact BPair.add_congr
          (BPair.add_congr (BPair.oneValue_refl _) (ground.swap_congr hcc))
          (BPair.add_congr (ground.swap_congr hdyx) (BPair.oneValue_refl _))
      have hGv' : (dotN ((vecScale (BPair.ofPos W) x)
            ++ (vecScale (BPair.ofPos s) y).map BPair.swap)
            (matVec G ((vecScale (BPair.ofPos W) x)
              ++ (vecScale (BPair.ofPos s) y).map BPair.swap))).oneValue
          (dotN (vecScale (BPair.ofPos W) x)
              (matVec G1 (vecScale (BPair.ofPos W) x))
            + dotN (vecScale (BPair.ofPos s) y)
              (matVec G2 (vecScale (BPair.ofPos s) y))) := by
        refine BPair.oneValue_trans (hGjoin _ _ hXl hY'l) ?_
        rw [elim.dotN_matVec_swapMap G2 (vecScale (BPair.ofPos s) y)]
        exact BPair.oneValue_refl _
      have hp1 : BPair.unit ≤
          BPair.ofPos W * (dotN (vecScale (BPair.ofPos W) x)
              (matVec G1 (vecScale (BPair.ofPos W) x))
            + dotN (vecScale (BPair.ofPos s) y)
              (matVec G2 (vecScale (BPair.ofPos s) y)))
          + ((dotN (vecScale (BPair.ofPos W) x)
                (matVec M1 (vecScale (BPair.ofPos W) x))
              + BPair.ofPos W * dotN x (matVec (matScale s B) y))
            + (BPair.ofPos W * dotN x (matVec (matScale s B) y)
              + dotN (vecScale (BPair.ofPos s) y)
                (matVec M2 (vecScale (BPair.ofPos s) y)))) :=
        ground.leB_congr_right
          (BPair.oneValue_trans
            (quadForm_add_sq hcap.2.1 hcap.1 hvl)
            (BPair.add_congr
              (BPair.oneValue_trans (quadForm_ofPos W G _)
                (BPair.mul_congr (BPair.oneValue_refl _)
                  (hGjoin _ _ hXl hYl)))
              hMv))
          (ground.leB_of_not_lt
            (psd_all _ spL hcap.2.2.2.2.1 hcap.2.2.2.2.2 _ hvl))
      have hp2 : BPair.unit ≤
          BPair.ofPos W * (dotN (vecScale (BPair.ofPos W) x)
              (matVec G1 (vecScale (BPair.ofPos W) x))
            + dotN (vecScale (BPair.ofPos s) y)
              (matVec G2 (vecScale (BPair.ofPos s) y)))
          + (((dotN (vecScale (BPair.ofPos W) x)
                (matVec M1 (vecScale (BPair.ofPos W) x))).swap
              + BPair.ofPos W * dotN x (matVec (matScale s B) y))
            + (BPair.ofPos W * dotN x (matVec (matScale s B) y)
              + (dotN (vecScale (BPair.ofPos s) y)
                (matVec M2 (vecScale (BPair.ofPos s) y))).swap)) :=
        ground.leB_congr_right
          (BPair.oneValue_trans
            (quadForm_site_sq hcap.2.1 hcap.1 hv'l)
            (BPair.add_congr
              (BPair.oneValue_trans (quadForm_ofPos W G _)
                (BPair.mul_congr (BPair.oneValue_refl _) hGv'))
              (ground.swap_congr hMv')))
          (ground.leB_of_not_lt
            (psd_all _ spU hcap.2.2.1 hcap.2.2.2.1 _ hv'l))
      exact absurd (polarClose _ _ _ _ _ _ _ hp1 hp2
        (BPair.oneValue_symm hT) hlt (ground.unitLtOfPos W)) (fun z => z)

/-- `lem:inertia`'s compression at the fiber datum's site tie: the
head block's count sits at or below the whole datum's, both counts
read at one balance-pair level over the shared coupling block
(`thm:truncation`'s compression side). -/
theorem count_head_le {k m : Nat} (H G P G1 B Q G2 : Mat) (x y : Pos)
    (nh nf : Nat) (spH : Split k) (spF : Split (k + m))
    (hB : B.length = k)
    (htie : matOneValue
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale y G1)) (matScale x G1)) B
        (siteDatum (matAdd Q (matScale y G2)) (matScale x G2))))
    (hh : countAtPair P G1 x y nh spH)
    (hf : countAtPair H G x y nf spF) :
    nh ≤ nf := by
  have hle := inertia.rev_head_le
    (siteDatum (matAdd H (matScale y G)) (matScale x G))
    (siteDatum (matAdd P (matScale y G1)) (matScale x G1)) B
    (siteDatum (matAdd Q (matScale y G2)) (matScale x G2))
    hB htie spH hh.2.2.1 spF hf.2.2.1
  rw [hh.2.2.2, hf.2.2.2] at hle
  exact hle

/-- `thm:truncation`'s monotone read: at a positive-semidefinite
difference site the shifted block diagonal's count sits at or above
the whole datum's, and the block diagonal's own count is the head
block's alone, the removed block's count vacant at the vacant
coupling (`lem:inertia`'s monotonicity with its addition clause). -/
theorem count_full_le {k m : Nat} (H G P G1 Q G2 : Mat)
    (x y hx hy rx ry : Pos) (nf nh : Nat)
    (spF : Split (k + m)) (spH : Split k) (spR : Split m)
    (spD spd : Split (k + m))
    (hf : countAtPair H G x y nf spF)
    (hh : countAtPair P G1 hx hy nh spH)
    (hr : countAtPair Q G2 rx ry 0 spR)
    (hD : splitRead (blockJoin
      (siteDatum (matAdd P (matScale hy G1)) (matScale hx G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale ry G2)) (matScale rx G2))) spD)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale hy G1)) (matScale hx G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale ry G2)) (matScale rx G2)))) spd)
    (hpsd : psdAt spd) :
    nf ≤ nh := by
  have hmono := inertia.rev_mono
    (blockJoin
      (siteDatum (matAdd P (matScale hy G1)) (matScale hx G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale ry G2)) (matScale rx G2)))
    (siteDatum (matAdd H (matScale y G)) (matScale x G))
    spd spD spF hd hpsd hD hf.2.2.1
  have hjoin := inertia.rev_join
    (siteDatum (matAdd P (matScale hy G1)) (matScale hx G1))
    (siteDatum (matAdd Q (matScale ry G2)) (matScale rx G2))
    spH hh.2.2.1 spR hr.2.2.1 spD hD
  rw [hh.2.2.2, hr.2.2.2] at hjoin
  rw [hjoin, hf.2.2.2] at hmono
  exact hmono

/-- `thm:truncation`'s shifted split: the difference site at the gap's
weighting reads the polarization display, so the difference site is
positive semidefinite — the weighted split reads the shift site
across the stated tie and the reversal count is blind to the positive
factor (`lem:inertia`'s rescaling invariance). -/
theorem shift_psd {k m : Nat} (M G M1 M2 B G1 G2 D S' : Mat)
    (W s : Pos) (spU spL : Split (k + m))
    (hcap : capAt M (matScale W G) spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hGt : matOneValue G (blockJoin G1 (elim.nullMat k m) G2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hG1 : sqAt G1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (htieD : matOneValue (matScale s (siteDatum S' D))
      (shiftSite W s B G1 G2))
    (spd : Split (k + m))
    (hd : splitRead (siteDatum S' D) spd) :
    psdAt spd := by
  cases Nat.eq_zero_or_pos k with
  | inl hk =>
    subst hk
    have hBnil : B = [] := by
      cases B with
      | nil => rfl
      | cons r t => exact Nat.noConfusion hB
    have h0 : (shiftSite W s B G1 G2).length = 0 := by
      rw [hBnil]
      show (List.zipWith (· ++ ·) (matScale (W * W) G1) ([] : Mat)
        ++ List.zipWith (· ++ ·) (transposeM ([] : Mat))
          (matScale (s * s) G2)).length = 0
      rw [ground.zipWith_nil_right (· ++ ·) (matScale (W * W) G1)]
      rfl
    have hm : m = 0 := by
      have h1 : (0 : Nat) = 0 + m :=
        ((elim.matOne_length htieD).trans h0).symm.trans
          ((length_matScale s (siteDatum S' D)).trans (elim.sqAt_len hd.1))
      rw [Nat.zero_add] at h1
      exact h1.symm
    subst hm
    exact revAt_zero spd
  | inr hkpos =>
    have hG1r : rowsLen k G1 := elim.rowsLen_of_sqAt hG1
    have hG1l : G1.length = k := elim.sqAt_len hG1
    have hG2r : rowsLen m G2 := elim.rowsLen_of_sqAt hG2
    have hG2l : G2.length = m := elim.sqAt_len hG2
    have hSBl : (matScale s B).length = k := (length_matScale s B).trans hB
    have hSBr : rowsLen m (matScale s B) :=
      elim.rowsLen_mapRows (fun z => z.scale s) B m hBr
    have hSBt : (transposeM (matScale s B)).length = m :=
      elim.length_transposeM (matScale s B) hSBr (by rw [hSBl]; exact hkpos)
    have hSBtr : rowsLen k (transposeM (matScale s B)) :=
      elim.rowsLen_cast hSBl (elim.rowsLen_transposeM (matScale s B))
    have hSq : sqAt (shiftSite W s B G1 G2) (k + m) :=
      elim.sqAt_of
        (length_blockJoin (matScale (W * W) G1) (matScale s B)
          (matScale (s * s) G2) k m
          ((length_matScale (W * W) G1).trans hG1l) hSBl hSBt
          ((length_matScale (s * s) G2).trans hG2l))
        (rowsLen_blockJoin (matScale (W * W) G1) (matScale s B)
          (matScale (s * s) G2) k m
          (elim.rowsLen_mapRows (fun z => z.scale (W * W)) G1 k hG1r)
          hSBr hSBtr
          (elim.rowsLen_mapRows (fun z => z.scale (s * s)) G2 m hG2r))
    have hread : splitRead (shiftSite W s B G1 G2)
        (scaleSplit (BPair.ofPos s) spd) :=
      splitRead_congr _ _ hSq
        (elim.matOne_trans
          (elim.matOne_symm (matScale_scaleB s (siteDatum S' D))) htieD)
        _ (scaleSplit_read (BPair.ofPos s) (offOfUnitLt (ground.unitLtOfPos s))
            (siteDatum S' D) spd hd)
    have hpsd := polar_psd M G M1 M2 B G1 G2 W s spU spL hcap hMt hGt
      hM1 hM2l hG1 hG2 hB hBr (scaleSplit (BPair.ofPos s) spd) hread
    exact (scaleSplit_rev (BPair.ofPos s) (ground.unitLtOfPos s) spd).symm.trans
      hpsd

/-- `thm:truncation`'s shifted split, composed: the two cuts' values
bracket each other at the priced width.  The whole datum's count at
a level sits at or below the head's count at the level raised by the
shift cap `c_W`, the removed block's count vacant at the level
raised by the witness gap `ς` — the difference site's weighting
reading the shift site (`shift_psd` through the polarization), the
monotone side and the join closing the comparison
(`count_full_le`).  The cofactor tie `ς c_W = W²` is the stated
weighting's own read: the shift site's weights are `W²`, `ς`, `ς²`
by construction, so the weighting tie at the raised levels reads the
cofactor at every occupied gram.  The bracket display
`E₀ ς 𝒦 ≤ E₀ ς 𝒦_Λ + β² #p² d_θ²` is this read beside
`count_head_le`'s, the width the cofactor's own. -/
theorem count_shift_le {k m : Nat} (H G M M1 M2 P G1 Q G2 B : Mat)
    (x y cw W s : Pos) (nf nh : Nat)
    (spU spL : Split (k + m))
    (spF spD spd : Split (k + m)) (spH : Split k) (spR : Split m)
    (hcap : capAt M (matScale W G) spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hGt : matOneValue G (blockJoin G1 (elim.nullMat k m) G2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hG1 : sqAt G1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (htieD : matOneValue (matScale s (siteDatum
        (siteDatum (matAdd H (matScale y G)) (matScale x G))
        (blockJoin
          (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
          (elim.nullMat k m)
          (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2)))))
      (shiftSite W s B G1 G2))
    (hf : countAtPair H G x y nf spF)
    (hh : countAtPair P G1 (x + cw) y nh spH)
    (hr : countAtPair Q G2 (x + s) y 0 spR)
    (hD : splitRead (blockJoin
      (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2))) spD)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2)))) spd) :
    nf ≤ nh :=
  count_full_le H G P G1 Q G2 x y (x + cw) y (x + s) y nf nh
    spF spH spR spD spd hf hh hr hD hd
    (shift_psd M G M1 M2 B G1 G2
      (blockJoin
        (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2)))
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      W s spU spL hcap hMt hGt hM1 hM2l hG1 hG2 hB hBr htieD spd hd)

/-- `thm:truncation`'s removed block: its electric diagonal sits at
or above the cutoff and its magnetic part is capped inside the block,
so at the level tie `x + W + g = c + y` — the floor's cross-added
comparison `W + f ≥ αΛ_C` — the removed block's site datum reads one
value with the diagonal's own datum, the cap's lower split and a
positive gram multiple, three at-or-above reads whose join refuses a
vector below the sum's unit. -/
theorem removed_psd {m : Nat} (Q De M2 G2 : Mat) (c W x y g : Pos)
    (spDi spG spL sp : Split m)
    (hQt : matOneValue Q (matAdd De M2))
    (hdi : splitRead (siteDatum De (matScale c G2)) spDi)
    (hpdi : psdAt spDi)
    (hg : splitRead G2 spG) (hpg : psdAt spG)
    (hL : splitRead (matAdd (matScale W G2) M2) spL)
    (hpL : psdAt spL)
    (hlev : x + W + g = c + y)
    (hs : splitRead
      (siteDatum (matAdd Q (matScale y G2)) (matScale x G2)) sp) :
    psdAt sp := by
  have hG2 : sqAt G2 m := hg.1
  have hG2r : rowsLen m G2 := elim.rowsLen_of_sqAt hG2
  have hD1 : sqAt (siteDatum De (matScale c G2)) m := hdi.1
  have hD2 : sqAt (matAdd (matScale W G2) M2) m := hL.1
  have hD3 : sqAt (matScale g G2) m := sqAt_matScale m g G2 hG2
  have hRsq : sqAt (matAdd (matAdd (siteDatum De (matScale c G2))
      (matAdd (matScale W G2) M2)) (matScale g G2)) m :=
    elim.sqAt_matAdd m _ _ (elim.sqAt_matAdd m _ _ hD1 hD2) hD3
  have hZ1 : rowsLen m (matAdd (matScale y G2) (matSwap (matScale x G2))) :=
    elim.rowsLen_matAdd m _ _
      (elim.rowsLen_mapRows (fun z => z.scale y) G2 m hG2r)
      (elim.rowsLen_mapRows BPair.swap (matScale x G2) m
        (elim.rowsLen_mapRows (fun z => z.scale x) G2 m hG2r))
  have hZ2 : rowsLen m
      (matAdd (matSwap (matScale c G2)) (matScale (W + g) G2)) :=
    elim.rowsLen_matAdd m _ _
      (elim.rowsLen_mapRows BPair.swap (matScale c G2) m
        (elim.rowsLen_mapRows (fun z => z.scale c) G2 m hG2r))
      (elim.rowsLen_mapRows (fun z => z.scale (W + g)) G2 m hG2r)
  have hSeq : siteDatum (matAdd Q (matScale y G2)) (matScale x G2)
      = matAdd Q (matAdd (matScale y G2) (matSwap (matScale x G2))) :=
    elim.matAdd_assoc Q (matScale y G2) (matSwap (matScale x G2))
  have hReq : matAdd (matAdd (siteDatum De (matScale c G2))
        (matAdd (matScale W G2) M2)) (matScale g G2)
      = matAdd (matAdd De M2)
        (matAdd (matSwap (matScale c G2)) (matScale (W + g) G2)) := by
    show matAdd (matAdd (matAdd De (matSwap (matScale c G2)))
        (matAdd (matScale W G2) M2)) (matScale g G2) = _
    rw [elim.matAdd_comm (matScale W G2) M2,
      elim.matAdd_shuffle De (matSwap (matScale c G2)) M2 (matScale W G2),
      elim.matAdd_assoc (matAdd De M2)
        (matAdd (matSwap (matScale c G2)) (matScale W G2)) (matScale g G2),
      elim.matAdd_assoc (matSwap (matScale c G2)) (matScale W G2)
        (matScale g G2),
      ← matScale_addW W g G2]
  have hSrow : rowsLen m
      (matAdd Q (matAdd (matScale y G2) (matSwap (matScale x G2)))) := by
    rw [← hSeq]
    exact elim.rowsLen_of_sqAt hs.1
  have hRrow : rowsLen m (matAdd (matAdd De M2)
      (matAdd (matSwap (matScale c G2)) (matScale (W + g) G2))) := by
    rw [← hReq]
    exact elim.rowsLen_of_sqAt hRsq
  have htie : matOneValue
      (siteDatum (matAdd Q (matScale y G2)) (matScale x G2))
      (matAdd (matAdd (siteDatum De (matScale c G2))
        (matAdd (matScale W G2) M2)) (matScale g G2)) := by
    rw [hSeq, hReq]
    have hpair : (BPair.mk y x).oneValue (BPair.mk (W + g) c) := by
      show y + c = W + g + x
      rw [ground.add_comm y c, ← hlev, ground.add_comm x W,
        ground.add_assoc W x g, ground.add_comm x g,
        ← ground.add_assoc W g x]
    have hlevel : matOneValue
        (matAdd (matScale y G2) (matSwap (matScale x G2)))
        (matAdd (matSwap (matScale c G2)) (matScale (W + g) G2)) := by
      rw [elim.matAdd_comm (matSwap (matScale c G2)) (matScale (W + g) G2)]
      exact elim.matOne_trans (inertia.levelScaleB y x G2)
        (elim.matOne_trans (inertia.matScaleB_congr hpair G2)
          (elim.matOne_symm (inertia.levelScaleB (W + g) c G2)))
    exact elim.matAdd_congT m Q (matAdd De M2) _ _ hQt hlevel hZ1 hZ2 hSrow hRrow
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h => exact h
  | inr hocc =>
    obtain ⟨u, hu, hlt⟩ := rev_witness _ sp hs hocc
    have hp1 : BPair.unit ≤ quadForm (siteDatum De (matScale c G2)) u :=
      ground.leB_of_not_lt (psd_all _ spDi hdi hpdi u hu)
    have hp2 : BPair.unit ≤ quadForm (matAdd (matScale W G2) M2) u :=
      ground.leB_of_not_lt
        (psd_all _ spL hL hpL u hu)
    have hpG : BPair.unit ≤ quadForm G2 u :=
      ground.leB_of_not_lt (psd_all _ spG hg hpg u hu)
    have hp3 : BPair.unit ≤ quadForm (matScale g G2) u :=
      ground.leB_congr_right (BPair.oneValue_symm (quadForm_scale g G2 u))
        (ground.unitLeScale g hpG)
    have hadd2 := quadForm_add (siteDatum De (matScale c G2))
      (matAdd (matScale W G2) M2) u
      ((elim.sqAt_len hD1).trans hu.symm)
      (elim.rowsLen_cast hu.symm (elim.rowsLen_of_sqAt hD1))
      ((elim.sqAt_len hD2).trans hu.symm)
      (elim.rowsLen_cast hu.symm (elim.rowsLen_of_sqAt hD2))
    have hadd1 := quadForm_add
      (matAdd (siteDatum De (matScale c G2)) (matAdd (matScale W G2) M2))
      (matScale g G2) u
      ((elim.sqAt_len (elim.sqAt_matAdd m _ _ hD1 hD2)).trans hu.symm)
      (elim.rowsLen_cast hu.symm
        (elim.rowsLen_of_sqAt (elim.sqAt_matAdd m _ _ hD1 hD2)))
      ((elim.sqAt_len hD3).trans hu.symm)
      (elim.rowsLen_cast hu.symm (elim.rowsLen_of_sqAt hD3))
    have hsum : BPair.unit ≤ quadForm (matAdd
        (matAdd (siteDatum De (matScale c G2))
          (matAdd (matScale W G2) M2)) (matScale g G2)) u :=
      ground.leB_congr_right
        (BPair.oneValue_symm (BPair.oneValue_trans hadd1
          (BPair.add_congr hadd2
            (BPair.oneValue_refl (quadForm (matScale g G2) u)))))
        (ground.unitLeAdd (ground.unitLeAdd hp1 hp2) hp3)
    exact absurd hlt (ground.leB_not_lt
      (ground.leB_congr_right
        (BPair.oneValue_symm (quadMatOne _ _ u htie)) hsum))

end truncation
