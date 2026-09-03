import MassGap.Cornerpivot
import MassGap.Spectator
/-!
`lem:cornerpivot` (vii) — the block chain's ball tier: the center
family with its pairs (`CenterFam`, its read `famRead`) on the
decimated head's chain, the per-depth stated centers the family's
own evaluations, one matrix polynomial in the scale and the depth's
pair reads.  `ball_step_of` is the one-depth
transport: clause (iii)'s image deviation joined to the defect at
the deviation's triangle, the modulus absorbing the contracted
image inside the radius.  `crossing_rebound` is the crossing's rank-one
read: the join's withdrawn term is the recursion witness's
sandwich of the crossing pivot, priced by the withdrawn diagonal —
the positive part at the crossing's stated order-one-lower
presentation — the following pivot at or beyond its diagonal less
the transfer at the congruence determinant's squared clearing.  `strict_lift` and `cap_lift` read the ground
witness and the cap pair through the compression unchanged: a
compressed strict vector occupies the count, and the compressed
two-member cap reads force it at two, the congruence transporting
the forms.  `rebound_floor` is the rebound's seed floor: the
diagonal's floor less the transfer's cap clears the following
pivot, the two comparisons carried through the rebound and closed
against the seed comparison with the crossing's congruence
determinant cancelling.  `domRead` walks the dominance tail
deep-first in lockstep with the chain — per depth the diagonal's
floor at the coordinates' fold of squares and the depth's floor
pair, per bond the square's cap, each deeper depth one
cross-multiplied comparison, and the seed arm at the crossing's
following depth, whose floor is the rebound's own.  `domTail_psd`
reads past the crossing every deep pivot's stated split on the
upper side throughout, the floor list's read, and `domTail_cross`
locates the seed arm's crossing split at the region length's
position.
`famChainRead` reads the chain's stated data at the center family
over the segment's depth range, deep-first — position `p` at depth
`m0 + (diag.length - 1 - p)`, the boundary seed at `m0` the last
position — each stated diagonal at the clearing's stated power
against the family's evaluated diagonal at its position's own
depth, each bond the stated bond, and the four walks' and three
clearing certificates' boxes holding every segment depth's scale
point; `famYc` is the family's evaluated center at a depth with its
clearing's own margin, and `famChain_psd` walks the segment at the
family: from the boundary seed's cap at depth `m0` the one-depth
transport hands each ball from the shallower center to the deeper,
every pivot at its position's own depth in its center's ball, and
every pivot's every stated split reads the upper side throughout,
the slab fold at the count's unit.  `famChainCount` closes the
chain's count at the certificate, the center family its data: the
count splits over the depth pivots (`lem:greenprod`(ii)), the
walked segment's stated splits read vacant at the family's balls,
the crossing's split reads its one lower unit and the dominance
tail's floors read every deeper split vacant, so every split of
the assembled datum reads the count at one.
-/

namespace cornerpivot
open ground poly elim inertia greenprod spectator

set_option genInjectivity false in
/-- Clause (vii)'s center family with its pairs, read at the
canonical carrier: the order, the diagonal family, and the center,
witness and image families at their clearings; the contraction, the
floor, the defect and the modulus pairs with the shared ball pair
and the ceiling; and the four counts' certificate lists — one box
certificate per row, the diagonal's entry less the off-row
magnitude fold — beside the three clearings' own box certificates,
the centers' determinants the clearings' reads. -/
structure CenterFam where
  o : Nat
  Af : List (List (poly.PPoly × poly.PPoly))
  Cf : PfMQ
  Wf : PfMQ
  If : PfMQ
  lam : Pos × Pos
  y0 : Pos × Pos
  rho : Pos × Pos
  dft : Pos × Pos
  lc : Pos × Pos
  e0 : BPair × Pos
  bxC : List BoxCert
  bxF : List BoxCert
  bxU : List BoxCert
  bxL : List BoxCert
  bxClC : BoxCert
  bxClW : BoxCert
  bxClI : BoxCert

/-- The center family's read: the diagonal, center, witness and
image families square at the order with the two stated matrices;
the gram its own exchange, the center its own and the image family
its own — the located symmetric center's read (`lem:spectator`(iii))
with the dominance comparison's symmetric datum
(`thm:decimation`(ii)); the
recursion's two ties — the shallower center's witness against the
bond's exchange, and the image joined to the bond's multiple of
the witness against the diagonal — cross-multiplied at the
clearings; the four counts' site data diagonally dominant on
the box, one box read per row at the diagonal's entry less the
off-row magnitude fold (`lem:spectator`(iii)'s three counts with
the cap's two arms); the center's, the witness's and the image's
clearings positive on the box at their own certificates — the
centers' determinants the clearings' reads; and the modulus
pair's two comparisons — the tie at the floor and radius pairs'
cross-added numerator, and the defect's cap inside the radius at
the modulus's square. -/
def famRead (F : CenterFam) (B G : elim.Mat) : Prop :=
  F.Af.length = F.o ∧ elim.rowsLen F.o F.Af
  ∧ F.Cf.1.length = F.o ∧ elim.rowsLen F.o F.Cf.1
  ∧ F.Wf.1.length = F.o ∧ elim.rowsLen F.o F.Wf.1
  ∧ F.If.1.length = F.o ∧ elim.rowsLen F.o F.If.1
  ∧ elim.sqAt B F.o ∧ elim.sqAt G F.o
  ∧ matOneValue (transposeM G) G
  ∧ pfmOneValue (pfmTr F.Cf.1) F.Cf.1
  ∧ pfmOneValue (pfmTr F.If.1) F.If.1
  ∧ pfmQOneValue (pfmQmul F.Cf (pfmQshift F.Wf))
      (ofPfm (ofMatProf (transposeM B)))
  ∧ pfmQOneValue F.If
      (pfmQadd (ofPfm F.Af)
        (pfmQmul (ofPfm (ofMatProf B)) (pfmQswap F.Wf)))
  ∧ domCertGo F.e0.1 F.e0.2 0 (contrSiteF F.Wf G F.lam.1 F.lam.2)
      F.bxC
  ∧ domCertGo F.e0.1 F.e0.2 0
      (floorSiteF F.Cf G F.y0.1 F.y0.2 F.rho.1 F.rho.2) F.bxF
  ∧ domCertGo F.e0.1 F.e0.2 0 (dcapHiSiteF F.Cf F.If G F.dft.1 F.dft.2)
      F.bxU
  ∧ domCertGo F.e0.1 F.e0.2 0 (dcapLoSiteF F.Cf F.If G F.dft.1 F.dft.2)
      F.bxL
  ∧ boxRead F.Cf.2 F.e0.1 F.e0.2 F.bxClC
  ∧ boxRead F.Wf.2 F.e0.1 F.e0.2 F.bxClW
  ∧ boxRead F.If.2 F.e0.1 F.e0.2 F.bxClI
  ∧ F.y0.1 * (F.lc.1 * (F.lam.2 * F.rho.2))
      = F.lam.1 * ((F.y0.1 * F.rho.2 + F.rho.1 * F.y0.2) * F.lc.2)
  ∧ F.dft.1 * ((F.lc.2 * F.lc.2) * F.rho.2)
        + (F.lc.1 * F.lc.1) * (F.rho.1 * F.dft.2)
      ≤ F.rho.1 * (F.dft.2 * (F.lc.2 * F.lc.2))

instance (F : CenterFam) (B G : elim.Mat) :
    Decidable (famRead F B G) :=
  inferInstanceAs (Decidable
    (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The modulus' own reassociation: the triangle's out-cap weight
against the target's cross-product. -/
private theorem posM1 (rn r0d lcd rd : Pos) :
    rn * (r0d * (lcd * lcd)) * rd = rn * (lcd * lcd * rd * r0d) := by
  rw [ground.mul_assoc rn (r0d * (lcd * lcd)) rd,
    ground.mul_comm r0d (lcd * lcd),
    ground.mul_assoc (lcd * lcd) r0d rd,
    ground.mul_comm r0d rd,
    ← ground.mul_assoc (lcd * lcd) rd r0d]

/-- The triangle's summed numerator at the modulus' own spelling. -/
private theorem posM2 (lcn rn r0d r0n lcd rd : Pos) :
    lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)
      = r0n * (lcd * lcd * rd) + lcn * lcn * (rn * r0d) := by
  rw [ground.add_comm (lcn * lcn * rn * r0d) (r0n * (lcd * lcd * rd)),
    ground.mul_assoc (lcn * lcn) rn r0d]

/-- Clause (vii)'s one-depth transport at the pointwise reads: the
floor, the contraction, the defect's two cap arms and the gram's
symmetry enter as their own reads with the orders' guard at the
truncating folds, and the member's ball at the shallower center
carries to the deeper center's ball — clause (iii)'s image
deviation joined to the center defect at the deviation's triangle,
the modulus absorbing the contracted image inside the radius. -/
theorem ball_step_of {o o' : Nat} (X Xdp Yc Ymid Ycd Cx Cc : MatQ)
    (A B G G' : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (hX : sqAt X.1 o) (hXdp : sqAt Xdp.1 o') (hYc : sqAt Yc.1 o)
    (hYmid : sqAt Ymid.1 o') (hYcd : sqAt Ycd.1 o')
    (hCx : rectAt Cx.1 o o') (hCc : rectAt Cc.1 o o')
    (hA : sqAt A o') (hB : rectAt B o' o) (hG : sqAt G o)
    (hsymX : matOneValue (transposeM X.1) X.1)
    (hsymYc : matOneValue (transposeM Yc.1) Yc.1)
    (hw : oneValueQ (mulQ X Cx) (ofM (transposeM B)))
    (hj : oneValueQ (addQ Xdp (mulQ (ofM B) Cx)) (ofM A))
    (hwc : oneValueQ (mulQ Yc Cc) (ofM (transposeM B)))
    (hjc : oneValueQ (addQ Ymid (mulQ (ofM B) Cc)) (ofM A))
    (hDhi : ∀ u : List BPair, u.length = o →
      (quadForm (devQ X Yc).1 u).scale rd
        ≤ (quadForm G u).scale (rn * (devQ X Yc).2))
    (hDlo : ∀ u : List BPair, u.length = o →
      ((quadForm G u).scale (rn * (devQ X Yc).2)).swap
        ≤ (quadForm (devQ X Yc).1 u).scale rd)
    (hFp : ∀ u : List BPair, u.length = o →
      (quadForm G u).scale (Yc.2 * (y0n * rd + rn * y0d))
        ≤ (quadForm Yc.1 u).scale (y0d * rd))
    (hconp : ∀ u : List BPair, u.length = o' →
      (quadForm G (matVec (transfer Cc).1 u)).scale (ld * ld)
        ≤ (quadForm G' u).scale (ln * ln * (Cc.2 * Cc.2)))
    (hsymG : matOneValue (transposeM G) G)
    (hnz : o = 0 → o' = 0)
    (hdefHi : ∀ w : List BPair, w.length = o' →
      (quadForm (devQ Ymid Ycd).1 w).scale r0d
        ≤ (quadForm G' w).scale (r0n * (devQ Ymid Ycd).2))
    (hdefLo : ∀ w : List BPair, w.length = o' →
      ((quadForm G' w).scale (r0n * (devQ Ymid Ycd).2)).swap
        ≤ (quadForm (devQ Ymid Ycd).1 w).scale r0d)
    (htie : y0n * (lcn * (ld * rd))
      = ln * ((y0n * rd + rn * y0d) * lcd))
    (hmod : r0n * ((lcd * lcd) * rd) + (lcn * lcn) * (rn * r0d)
      ≤ rn * (r0d * (lcd * lcd))) :
    (∀ u : List BPair, u.length = o' →
      (quadForm (devQ Xdp Ycd).1 u).scale rd
        ≤ (quadForm G' u).scale (rn * (devQ Xdp Ycd).2))
    ∧ (∀ u : List BPair, u.length = o' →
      ((quadForm G' u).scale (rn * (devQ Xdp Ycd).2)).swap
        ≤ (quadForm (devQ Xdp Ycd).1 u).scale rd) := by
  have hI := spectator.image_contract_of X Xdp Yc Ymid Cx Cc A B G G'
    ln ld y0n y0d rn rd lcn lcd hX hXdp hYc hYmid hCx hCc
    hA hB hG hsymX hsymYc hw hj hwc hjc hDhi hDlo hFp hconp hsymG
    hnz htie
  have htri := spectator.dev_triangle Xdp Ymid Ycd G'
    (lcn * lcn * rn) (lcd * lcd * rd) r0n r0d hXdp hYmid hYcd
    hI.1 hI.2 hdefHi hdefLo
  have hpos : ∀ u : List BPair, u.length = o' →
      BPair.unit ≤ quadForm G' u := by
    intro u hu
    exact ground.unitLeOfScale
      (ground.unitLeOfSwap (ground.leB_trans (hdefLo u hu) (hdefHi u hu)))
  have hcle : lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)
      ≤ rn * (r0d * (lcd * lcd)) := by
    rw [posM2 lcn rn r0d r0n lcd rd]
    exact hmod
  have hcrd : (lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)) * rd
      ≤ rn * (lcd * lcd * rd * r0d) := by
    have h := ground.mul_le_mul_right rd hcle
    rw [posM1 rn r0d lcd rd] at h
    exact h
  have hkey : (lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd))
        * (devQ Xdp Ycd).2 * rd
      ≤ rn * (devQ Xdp Ycd).2 * (lcd * lcd * rd * r0d) := by
    have h := ground.mul_le_mul_right (devQ Xdp Ycd).2 hcrd
    rw [ground.mul_right_comm
        (lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)) rd
        (devQ Xdp Ycd).2,
      ground.mul_right_comm rn (lcd * lcd * rd * r0d)
        (devQ Xdp Ycd).2] at h
    exact h
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · refine ground.leB_of_scale (w := lcd * lcd * rd * r0d) ?_
    rw [BPair.scale_scale, BPair.scale_scale]
    refine ground.leB_trans ?_ (ground.leB_scaleMono (hpos u hu) hkey)
    have h1 := ground.leB_scale (htri.1 u hu) rd
    rw [BPair.scale_scale, BPair.scale_scale] at h1
    rw [ground.mul_comm rd (lcd * lcd * rd * r0d)]
    exact h1
  · refine ground.leB_of_scale (w := lcd * lcd * rd * r0d) ?_
    rw [← BPair.scale_swap, BPair.scale_scale, BPair.scale_scale]
    refine ground.leB_trans
      (ground.leB_swap (ground.leB_scaleMono (hpos u hu) hkey)) ?_
    have h2 := ground.leB_scale (htri.2 u hu) rd
    rw [← BPair.scale_swap, BPair.scale_scale, BPair.scale_scale] at h2
    rw [ground.mul_comm rd (lcd * lcd * rd * r0d)]
    exact h2

/-- The seed's weight move: the member's clearing rides out of the
boundary block's own expansion. -/
private theorem seedShift (a b : BPair) (x y : Pos) :
    (a.scale x).scale y + b.scale x
      = (a.scale y + b.scale Pos.one).scale x := by
  rw [BPair.scale_add, BPair.scale_scale a x y,
    BPair.scale_scale a y x, BPair.scale_scale b Pos.one x,
    ground.one_mul x, ground.mul_comm y x]

/-- The seed's radius weight at the member's clearing. -/
private theorem posSeed (rn y x : Pos) :
    rn * (Pos.one * y) * x = rn * (x * y) := by
  rw [ground.one_mul y, ground.mul_assoc rn y x, ground.mul_comm y x]

/-- The seed arm's transport: the boundary seed's cap at the boundary
block carries to the seed pivot, the two deviations congruent at
the pivot's own clearing. -/
private theorem seedCap {o : Nat} (X Yc : MatQ) (A G : Mat)
    (rn rd : Pos)
    (hX : sqAt X.1 o) (hYc : sqAt Yc.1 o) (hA : sqAt A o)
    (hXA : oneValueQ X (ofM A))
    (hhi : ∀ u : List BPair, u.length = o →
      (quadForm (devQ (ofM A) Yc).1 u).scale rd
        ≤ (quadForm G u).scale (rn * (devQ (ofM A) Yc).2))
    (hlo : ∀ u : List BPair, u.length = o →
      ((quadForm G u).scale (rn * (devQ (ofM A) Yc).2)).swap
        ≤ (quadForm (devQ (ofM A) Yc).1 u).scale rd) :
    (∀ u : List BPair, u.length = o →
      (quadForm (devQ X Yc).1 u).scale rd
        ≤ (quadForm G u).scale (rn * (devQ X Yc).2))
    ∧ (∀ u : List BPair, u.length = o →
      ((quadForm G u).scale (rn * (devQ X Yc).2)).swap
        ≤ (quadForm (devQ X Yc).1 u).scale rd) := by
  have hXAm : matOneValue X.1 (matScale X.2 A) := by
    have h0 : matOneValue (matScale Pos.one X.1) (matScale X.2 A) :=
      hXA
    rw [matScale_one] at h0
    exact h0
  have hcg : ∀ u : List BPair, u.length = o →
      (quadForm (devQ X Yc).1 u).oneValue
        ((quadForm (devQ (ofM A) Yc).1 u).scale X.2) := by
    intro u hu
    have hq : (quadForm X.1 u).oneValue ((quadForm A u).scale X.2) :=
      BPair.oneValue_trans
        (dotN_matVec_congrM X.1 (matScale X.2 A) u u hXAm)
        (quadForm_scale X.2 A u)
    refine BPair.oneValue_trans
      (spectator.dev_expand X Yc u ((sqAt_len hX).trans hu.symm)
        (by rw [hu]; exact rowsLen_of_sqAt hX)
        ((sqAt_len hYc).trans hu.symm)
        (by rw [hu]; exact rowsLen_of_sqAt hYc)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.scale_congr Yc.2 hq)
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (seedShift (quadForm A u) ((quadForm Yc.1 u).swap)
          X.2 Yc.2)) ?_
    exact BPair.scale_congr X.2
      (BPair.oneValue_symm
        (spectator.dev_expand (ofM A) Yc u
          ((sqAt_len hA).trans hu.symm)
          (by rw [hu]; exact rowsLen_of_sqAt hA)
          ((sqAt_len hYc).trans hu.symm)
          (by rw [hu]; exact rowsLen_of_sqAt hYc)))
  have hps : rn * (devQ (ofM A) Yc).2 * X.2 = rn * (devQ X Yc).2 :=
    posSeed rn Yc.2 X.2
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.scale_congr rd (hcg u hu))) ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        (BPair.scale_comm (quadForm (devQ (ofM A) Yc).1 u) rd X.2))
      (BPair.oneValue_of_eq
        ((BPair.scale_scale (quadForm G u)
            (rn * (devQ (ofM A) Yc).2) X.2).trans
          (congrArg (BPair.scale (quadForm G u)) hps)))
      (ground.leB_scale (hhi u hu) X.2)
  · refine ground.leB_congr_right
      (BPair.oneValue_symm (BPair.scale_congr rd (hcg u hu))) ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        ((BPair.scale_swap
            ((quadForm G u).scale (rn * (devQ (ofM A) Yc).2)) X.2).trans
          (congrArg BPair.swap
            ((BPair.scale_scale (quadForm G u)
                (rn * (devQ (ofM A) Yc).2) X.2).trans
              (congrArg (BPair.scale (quadForm G u)) hps)))))
      (BPair.oneValue_of_eq
        (BPair.scale_comm (quadForm (devQ (ofM A) Yc).1 u) rd X.2))
      (ground.leB_scale (hlo u hu) X.2)

/-- The tail recursion's read at the deeper segment. -/
private theorem tailTail {A A' B : Mat} {As Bs : List Mat}
    {X X' R : MatQ} {Xt Rt : List MatQ} {n n' : Nat} {nt : List Nat}
    (h : tailRead (A :: A' :: As) (B :: Bs) (X :: X' :: Xt) (R :: Rt)
      (n :: n' :: nt)) :
    tailRead (A' :: As) Bs (X' :: Xt) Rt (n' :: nt) :=
  ⟨h.1.2.2.2, h.2.1.2, h.2.2.1.2, h.2.2.2.2⟩

/-- Clause (vii)'s rebound at the crossing block: the join's
withdrawn term is the recursion witness's sandwich of the crossing
pivot, whose form the withdrawn-diagonal read prices — the
positive part at the crossing's stated presentation, the lower
unit at an order-one block — so the following pivot sits at or
beyond its diagonal less the transfer, the crossing pivot's
symmetry the split's own read and the display cleared at the
congruence determinant's square with the witness clearing entering
squared. -/
theorem crossing_rebound {o o' : Nat} (Xf Xc R : MatQ) (A B : Mat)
    (sp : Split o')
    (hk : 0 < o) (hk' : 0 < o')
    (hXf : sqAt Xf.1 o)
    (hB : rectAt B o o') (hR : rectAt R.1 o' o)
    (hwit : oneValueQ (mulQ Xc R) (ofM (transposeM B)))
    (hjoin : oneValueQ (addQ Xf (mulQ (ofM B) R)) (ofM A))
    (hsp : splitRead Xc.1 sp) :
    ∀ u : List BPair, u.length = o →
      minor sp.T.val * minor sp.T.val
          * ((quadForm A u).scale (Xc.2 * (Xf.2 * (R.2 * R.2))))
        ≤ minor sp.T.val * minor sp.T.val
            * ((quadForm Xf.1 u).scale (Xc.2 * (R.2 * R.2)))
          + (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
              (matVec sp.Tw.val (matVec R.1 u))).scale Xf.2 := by
  intro u hu
  have hXc : sqAt Xc.1 o' := hsp.1
  have hsymC : matOneValue (transposeM Xc.1) Xc.1 :=
    matOne_symm (splitRead_symm Xc.1 sp hsp)
  have hRl : R.1.length = o' := rectAt_len hR
  have hRr : rowsLen o R.1 := rectAt_rows hR
  have hXcl : Xc.1.length = o' := sqAt_len hXc
  have hXcr : rowsLen o' Xc.1 := rowsLen_of_sqAt hXc
  have hRTr : rowsLen o' (transposeM R.1) :=
    rowsLen_cast hRl (rowsLen_transposeM R.1)
  have hv : (matVec R.1 u).length = o' :=
    (matVec_length R.1 u).trans hRl
  have hS := greenprod.withdrawn_sandwich (k := o) (k' := o') Xc R B
    hk hk' hXc hB hR hsymC hwit
  have hAs : matOneValue (matMul (matMul (transposeM R.1) Xc.1) R.1)
      (matMul (transposeM R.1) (matMul Xc.1 R.1)) :=
    matMul_assoc (transposeM R.1) Xc.1 R.1 hRTr hXcr hRr hXcl hRl
      hk' hk'
  have hBRX : ((quadForm (matMul B R.1) u).scale
      (Xc.2 * R.2)).oneValue (quadForm Xc.1 (matVec R.1 u)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (quadForm_scale (Xc.2 * R.2) (matMul B R.1) u)) ?_
    refine BPair.oneValue_trans (quadMatOne _ _ u hS) ?_
    refine BPair.oneValue_trans (quadMatOne _ _ u hAs) ?_
    exact BPair.oneValue_symm
      (congQuad Xc.1 R.1 o' o hXc hRr hRl u hu)
  have hJF := greenprod.join_quadSplit Xf R A B hk' hXf hB hR hjoin u hu
  have hEqL : (Xf.2 * R.2) * (Xc.2 * R.2)
      = Xc.2 * (Xf.2 * (R.2 * R.2)) := by
    rw [ground.mul_comm (Xf.2 * R.2) (Xc.2 * R.2),
      ground.mul_assoc Xc.2 R.2 (Xf.2 * R.2),
      ground.mul_comm Xf.2 R.2, ← ground.mul_assoc R.2 R.2 Xf.2,
      ground.mul_comm (R.2 * R.2) Xf.2]
  have hEqR : R.2 * (Xc.2 * R.2) = Xc.2 * (R.2 * R.2) := by
    rw [ground.mul_comm Xc.2 R.2,
      ← ground.mul_assoc R.2 R.2 Xc.2,
      ground.mul_comm (R.2 * R.2) Xc.2]
  have hStep1 : (quadForm A u).scale (Xc.2 * (Xf.2 * (R.2 * R.2)))
      = ((quadForm A u).scale (Xf.2 * R.2)).scale
          (Xc.2 * R.2) := by
    rw [BPair.scale_scale, hEqL]
  have hStep3 : ((quadForm Xf.1 u).scale R.2
        + (quadForm (matMul B R.1) u).scale Xf.2).scale (Xc.2 * R.2)
      = (quadForm Xf.1 u).scale (Xc.2 * (R.2 * R.2))
        + ((quadForm (matMul B R.1) u).scale (Xc.2 * R.2)).scale
            Xf.2 := by
    rw [BPair.scale_add, BPair.scale_scale, hEqR, BPair.scale_comm]
  have hL : (minor sp.T.val * minor sp.T.val
      * ((quadForm A u).scale
          (Xc.2 * (Xf.2 * (R.2 * R.2))))).oneValue
      (minor sp.T.val * minor sp.T.val
          * ((quadForm Xf.1 u).scale (Xc.2 * (R.2 * R.2)))
        + minor sp.T.val * minor sp.T.val
          * ((quadForm Xc.1 (matVec R.1 u)).scale Xf.2)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl
        (minor sp.T.val * minor sp.T.val)) ?_)
      (BPair.oneValue_of_eq (BPair.left_distrib _ _ _))
    refine BPair.oneValue_trans (BPair.oneValue_of_eq hStep1) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (Xc.2 * R.2) hJF) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq hStep3) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.scale_congr Xf.2 hBRX)
  have hle2 : minor sp.T.val * minor sp.T.val
      * ((quadForm Xc.1 (matVec R.1 u)).scale Xf.2)
      ≤ (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec sp.Tw.val (matVec R.1 u))).scale Xf.2 := by
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq
        (BPair.mul_scale (minor sp.T.val * minor sp.T.val)
          (quadForm Xc.1 (matVec R.1 u)) Xf.2).symm) ?_
    exact ground.leB_scale
      (split_posPart Xc.1 sp hsp (matVec R.1 u) hv) Xf.2
  exact ground.leB_congr_left (BPair.oneValue_symm hL)
    (ground.leB_add (ground.leB_refl _) hle2)

set_option genInjectivity false in
/-- One deep depth's dominance data: the order, the diagonal's
floor pair, the depth's floor pair, and the floor's split. -/
structure DomStep where
  ord : Nat
  dg : Pos × Pos
  fl : Pos × Pos
  spM : Split ord

/-- The dominance tail's read, deep-first in lockstep with the
chain: per depth the diagonal's floor at the coordinates' fold of
squares and the depth's floor pair, per bond the square's cap, each
deeper depth one cross-multiplied comparison, and the seed arm at
the crossing's following depth — the crossing's split, the
transfer's cap at the congruence witness's solve, and the seed
comparison, the diagonal's floor at or beyond the seed floor joined
to the transfer's cap (`lem:cornerpivot`(vii)). -/
def domRead (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    List Mat → List Mat → List MatQ → List MatQ → List Nat →
    List DomStep → List ((k : Nat) × (Pos × Pos) × Split k) → Prop
  | A :: _ :: _, _ :: _, _ :: X' :: _, R :: _, n :: n' :: _,
      [D], [] =>
      D.ord = n ∧ spc.1 = n' ∧ spT.1 = n
      ∧ splitRead X'.1 spc.2
      ∧ leAt (matScale D.dg.1 (idMat n)) (matScale D.dg.2 A) D.spM
      ∧ leAt
          (matScale td (matMul
            (transposeM (matMul spc.2.Tw.val R.1))
            (matMul (blockMat (posBlocks spc.2.blocks) spc.2.kern)
              (matMul spc.2.Tw.val R.1))))
          (matScaleB
            ((minor spc.2.T.val * minor spc.2.T.val)
              * BPair.ofPos (tn * (X'.2 * (R.2 * R.2))))
            (idMat n))
          spT.2
      ∧ (D.fl.1 * td + tn * D.fl.2) * D.dg.2 ≤ D.dg.1 * (D.fl.2 * td)
  | A :: A' :: As, B :: Bs, _ :: X' :: Xs, _ :: Rs, n :: n' :: ns,
      D :: D' :: Ds, C :: Cs =>
      (D.ord = n ∧ C.1 = n
       ∧ leAt (matScale D.dg.1 (idMat n)) (matScale D.dg.2 A) D.spM
       ∧ leAt (matScale C.2.1.2 (matMul B (transposeM B)))
           (matScale C.2.1.1 (idMat n)) C.2.2
       ∧ D.fl.1 * (D.dg.2 * (C.2.1.2 * D'.fl.1))
           + C.2.1.1 * (D'.fl.2 * (D.dg.2 * D.fl.2))
         ≤ D.dg.1 * (D.fl.2 * (C.2.1.2 * D'.fl.1)))
      ∧ domRead spc spT tn td (A' :: As) Bs (X' :: Xs) Rs
          (n' :: ns) (D' :: Ds) Cs
  | [], _, _, _, _, _, _ => False
  | [_], _, _, _, _, _, _ => False
  | _ :: _ :: _, [], _, _, _, _, _ => False
  | _ :: _ :: _, _ :: _, [], _, _, _, _ => False
  | _ :: _ :: _, _ :: _, [_], _, _, _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [],
      _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [] => False

def decDomRead (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
    Decidable (domRead spc spT tn td diag off Xs Rs ns Ds Cs)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [] =>
      inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xs, _ :: Rs, _ :: n' :: ns,
      _ :: D' :: Ds, _ :: Cs =>
      @instDecidableAnd _ _
        (inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _)))
        (decDomRead spc spT tn td (A' :: As) Bs (X' :: Xs) Rs
          (n' :: ns) (D' :: Ds) Cs)
  | [], _, _, _, _, _, _ => isFalse (fun h => h)
  | [_], _, _, _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, [], _, _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [], _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [_], _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _ =>
      isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _ =>
      isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _ =>
      isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [],
      _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [] => isFalse (fun h => h)

instance (spc spT : (k : Nat) × Split k) (tn td : Pos)
    (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
    (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)) :
    Decidable (domRead spc spT tn td diag off Xs Rs ns Ds Cs) :=
  decDomRead spc spT tn td diag off Xs Rs ns Ds Cs

/-! The seed floor's weights: the diagonal comparison, the rebound
and the transfer's cap meet at one clearing, the seed comparison's
two terms priced there and the conclusion's own weight the shared
clearing's cofactor. -/

/-- The diagonal comparison's weight at the tail's clearing. -/
private theorem posD1 (md f W fd td : Pos) :
    md * (f * W * fd * td) = f * W * fd * md * td := by
  rw [ground.mul_left_comm md (f * W * fd) td,
    ← ground.mul_assoc (f * W * fd) md td]

/-- The rebound's weight at the tail's clearing. -/
private theorem posD2 (f W fd md td : Pos) :
    f * W * (fd * md * td) = f * W * fd * md * td := by
  rw [← ground.mul_assoc (f * W) (fd * md) td,
    ← ground.mul_assoc (f * W) fd md]

/-- The seed comparison's upper weight at the tail's clearing. -/
private theorem posD4 (mn fd td f W : Pos) :
    mn * (fd * td) * (f * W) = mn * (f * W * fd * td) := by
  rw [ground.mul_assoc mn (fd * td) (f * W),
    ground.mul_comm (fd * td) (f * W),
    ← ground.mul_assoc (f * W) fd td]

/-- The seed comparison's lower weight splits at its two terms. -/
private theorem posD5 (fn tn td fd md f W : Pos) :
    (fn * td + tn * fd) * md * (f * W)
      = fn * td * md * (f * W) + tn * fd * md * (f * W) := by
  rw [ground.right_distrib (fn * td) (tn * fd) md,
    ground.right_distrib (fn * td * md) (tn * fd * md) (f * W)]

/-- The comparison's transfer term reads the cap's own weight. -/
private theorem posD6 (tn fd md f W : Pos) :
    tn * fd * md * (f * W) = tn * W * (f * (fd * md)) := by
  rw [ground.mul_assoc (tn * fd) md (f * W),
    ground.mul_assoc tn fd (md * (f * W)),
    ground.mul_left_comm md f W,
    ground.mul_left_comm fd f (md * W),
    ground.mul_comm md W,
    ground.mul_assoc tn W (f * (fd * md)),
    ground.mul_left_comm W f (fd * md),
    ground.mul_left_comm W fd md]

/-- The comparison's floor term reads the conclusion's weight at
the shared clearing. -/
private theorem posD7 (fn td md f W : Pos) :
    fn * td * md * (f * W) = fn * f * (td * md * W) := by
  rw [ground.mul_assoc (fn * td) md (f * W),
    ground.mul_assoc fn td (md * (f * W)),
    ground.mul_left_comm md f W,
    ground.mul_left_comm td f (md * W),
    ground.mul_assoc fn f (td * md * W),
    ground.mul_assoc td md W]

/-- The rebound's pivot term reads the conclusion's weight at the
shared clearing. -/
private theorem posD8 (W fd md td : Pos) :
    W * (fd * md * td) = fd * (td * md * W) := by
  rw [ground.mul_assoc fd md td,
    ground.mul_left_comm W fd (md * td),
    ground.mul_assoc td md W,
    ground.mul_left_comm W md td,
    ground.mul_left_comm td md W,
    ground.mul_comm W td]

/-- The dominance step's close: the diagonal's floor carried
through the rebound and priced against the transfer's cap leaves
the following pivot's own floor, the shared transfer term and the
crossing clearing withdrawing at the cross-multiplied
comparison. -/
private theorem domClose {M n qa qf p : BPair}
    (f W mn md tn td fn fd : Pos)
    (hMu : BPair.unit < M) (hn : BPair.unit ≤ n)
    (hD : n.scale mn ≤ qa.scale md)
    (hR : M * qa.scale (f * W) ≤ M * qf.scale W + p.scale f)
    (hT : p.scale td ≤ M * n.scale (tn * W))
    (hC : (fn * td + tn * fd) * md ≤ mn * (fd * td)) :
    n.scale (fn * f) ≤ qf.scale fd := by
  have hM : BPair.unit ≤ M := ground.leB_of_lt hMu
  have hMN : BPair.unit ≤ M * n := ground.unitLeMul hM hn
  have s1 : (M * n).scale (mn * (f * W * fd * td))
      ≤ (M * qa).scale (f * W * fd * md * td) := by
    have h := ground.leB_mulR hM (ground.leB_scale hD (f * W * fd * td))
    rw [BPair.scale_scale, BPair.scale_scale, BPair.mul_scale,
      BPair.mul_scale, posD1 md f W fd td] at h
    exact h
  have s2 : (M * qa).scale (f * W * fd * md * td)
      ≤ (M * qf).scale (W * (fd * md * td))
        + p.scale (f * (fd * md * td)) := by
    have h := ground.leB_scale hR (fd * md * td)
    rw [BPair.scale_add, BPair.mul_scale, BPair.scale_scale,
      BPair.mul_scale, BPair.scale_scale, BPair.scale_scale,
      posD2 f W fd md td] at h
    exact h
  have s3 : p.scale (f * (fd * md * td))
      ≤ (M * n).scale (tn * W * (f * (fd * md))) := by
    have h := ground.leB_scale hT (f * (fd * md))
    rw [BPair.scale_scale, BPair.mul_scale, BPair.scale_scale,
      ground.mul_rotate f (fd * md) td] at h
    exact h
  have s4 : (M * n).scale (mn * (f * W * fd * td))
      ≤ (M * qf).scale (W * (fd * md * td))
        + (M * n).scale (tn * W * (f * (fd * md))) :=
    ground.leB_trans (ground.leB_trans s1 s2)
      (ground.leB_add (ground.leB_refl _) s3)
  have hC2 : (fn * td + tn * fd) * md * (f * W)
      ≤ mn * (fd * td) * (f * W) :=
    ground.mul_le_mul_right (f * W) hC
  have s5 : (M * n).scale (fn * td * md * (f * W))
        + (M * n).scale (tn * W * (f * (fd * md)))
      ≤ (M * n).scale (mn * (f * W * fd * td)) := by
    have h := ground.leB_scaleMono hMN hC2
    rw [posD5 fn tn td fd md f W, BPair.scale_addW,
      posD6 tn fd md f W, posD4 mn fd td f W] at h
    exact h
  have s6 : (M * n).scale (tn * W * (f * (fd * md)))
        + (M * n).scale (fn * td * md * (f * W))
      ≤ (M * n).scale (tn * W * (f * (fd * md)))
        + (M * qf).scale (W * (fd * md * td)) :=
    ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (ground.leB_trans s5 s4)
  have s7 : (M * n).scale (fn * td * md * (f * W))
      ≤ (M * qf).scale (W * (fd * md * td)) := ground.leB_cancelL s6
  have s8 : ((M * n).scale (fn * f)).scale (td * md * W)
      ≤ ((M * qf).scale fd).scale (td * md * W) := by
    rw [BPair.scale_scale, BPair.scale_scale, ← posD7 fn td md f W,
      ← posD8 W fd md td]
    exact s7
  refine ground.leB_unscale_left hMu ?_
  rw [BPair.mul_scale, BPair.mul_scale]
  exact ground.leB_of_scale s8

/-- The rebound's seed floor: the following pivot clears the
diagonal's floor less the transfer's cap. -/
theorem rebound_floor {o o' : Nat} (Xf Xc R : MatQ) (A B : Mat)
    (sp : Split o') (mn md tn td fn fd : Pos) :
    0 < o → 0 < o' →
    sqAt Xf.1 o → rectAt B o o' → rectAt R.1 o' o →
    oneValueQ (mulQ Xc R) (ofM (transposeM B)) →
    oneValueQ (addQ Xf (mulQ (ofM B) R)) (ofM A) →
    splitRead Xc.1 sp →
    (∀ u : List BPair, u.length = o →
      (dotN u u).scale mn ≤ (quadForm A u).scale md) →
    (∀ u : List BPair, u.length = o →
      (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec (matMul sp.Tw.val R.1) u)).scale td
        ≤ minor sp.T.val * minor sp.T.val
            * ((dotN u u).scale (tn * (Xc.2 * (R.2 * R.2))))) →
    (fn * td + tn * fd) * md ≤ mn * (fd * td) →
    ∀ u : List BPair, u.length = o →
      (dotN u u).scale (fn * Xf.2)
        ≤ (quadForm Xf.1 u).scale fd := by
  intro hk hk' hXf hB hR hwit hjoin hsp hdiag htcap hcomp u hu
  have hMu : BPair.unit < minor sp.T.val * minor sp.T.val :=
    ground.sq_pos hsp.2.1.1
  have hn : BPair.unit ≤ dotN u u :=
    ground.leB_of_not_lt (elim.dotN_self_side u)
  have hrb := crossing_rebound Xf Xc R A B sp hk hk' hXf hB hR hwit
    hjoin hsp u hu
  rw [ground.mul_left_comm Xc.2 Xf.2 (R.2 * R.2)] at hrb
  have hT := ground.leB_congr_left
    (BPair.scale_congr td
      (inertia.quadForm_congr (blockMat (posBlocks sp.blocks) sp.kern)
        (elim.matVec_matMul sp.Tw.val R.1 o (rectAt_rows hR) u hu)))
    (htcap u hu)
  exact domClose Xf.2 (Xc.2 * (R.2 * R.2)) mn md tn td fn fd hMu hn
    (hdiag u hu) hrb hT hcomp

/-! The dominance walk's reads: the slab's own order, the two
floor data at the coordinates' fold of squares, and the transfer's
cap at the crossing's compression. -/

/-- The withdrawn diagonal keeps the block widths: the withdrawn
order-one entry and every further block carry their own order. -/
private theorem widthOf_posBlocks : ∀ (bs : List SBlock) (k : Nat),
    widthOf (posBlocks bs) k = widthOf bs k
  | [], _ => rfl
  | SBlock.one a :: bs, k =>
    match (inferInstance : Decidable (a < BPair.unit)) with
    | isTrue hg => by
      have hpos := posBlocks_cons_lt bs hg
      rw [hpos]
      exact widthOf_posBlocks bs (k + 1)
    | isFalse hg => by
      have hpos := posBlocks_cons_ge bs hg
      rw [hpos]
      exact widthOf_posBlocks bs (k + 1)
  | SBlock.two _ _ _ :: bs, k => widthOf_posBlocks bs (k + 2)

/-- The withdrawn diagonal's block matrix keeps the split's stated
order. -/
private theorem sqAt_posBlockMat {m : Nat} (sp : Split m) :
    sqAt (blockMat (posBlocks sp.blocks) sp.kern) m := by
  have hw : widthOf (posBlocks sp.blocks) sp.kern = m :=
    (widthOf_posBlocks sp.blocks sp.kern).trans
      (ground.beqEq _ _ sp.width)
  exact sqAt_of ((blockMat_len _ _).trans hw)
    (rowsLen_cast hw (blockMat_rows _ _))

/-- The diagonal's floor at a slab: the comparison's read prices
the coordinates' fold of squares against the slab's own form. -/
private theorem diagFloor {k n : Nat} (A : Mat) (dn dd : Pos)
    (sp : Split k) (hk : k = n) (hA : sqAt A n)
    (h : leAt (matScale dn (idMat n)) (matScale dd A) sp) :
    ∀ u : List BPair, u.length = n →
      (dotN u u).scale dn ≤ (quadForm A u).scale dd := by
  subst hk
  intro u hu
  refine ground.leB_congr ?_ (quadForm_scale dd A u)
    (le_all (matScale dn (idMat k)) (matScale dd A) sp
      (sqAt_matScale k dn (idMat k) (sqAt_idMat k))
      (sqAt_matScale k dd A hA) h u hu)
  exact BPair.oneValue_trans (quadForm_scale dn (idMat k) u)
    (BPair.scale_congr dn (quadForm_idMat k u hu))

/-- The bond's square cap at a slab: the comparison's read prices
the bond square's form against the coordinates' fold of squares. -/
private theorem bondCap {k n n' : Nat} (B : Mat) (bn bd : Pos)
    (sp : Split k) (hk : k = n) (hn : 0 < n) (hn' : 0 < n')
    (hB : rectAt B n n')
    (h : leAt (matScale bd (matMul B (transposeM B)))
      (matScale bn (idMat n)) sp) :
    ∀ u : List BPair, u.length = n →
      (quadForm (matMul B (transposeM B)) u).scale bd
        ≤ (dotN u u).scale bn := by
  subst hk
  intro u hu
  have hBl : B.length = k := rectAt_len hB
  have hBTl : (transposeM B).length = n' :=
    length_transposeM B (rectAt_rows hB) (by rw [hBl]; exact hn)
  have hBTr : rowsLen k (transposeM B) :=
    rowsLen_cast hBl (rowsLen_transposeM B)
  have hBB : sqAt (matMul B (transposeM B)) k :=
    sqAt_of ((length_matMul B (transposeM B)).trans hBl)
      (rowsLen_matMul_of B (transposeM B)
        (fun _ => by rw [hBTl]; exact hn') hBTr)
  refine ground.leB_congr (quadForm_scale bd _ u) ?_
    (le_all (matScale bd (matMul B (transposeM B)))
      (matScale bn (idMat k)) sp
      (sqAt_matScale k bd _ hBB)
      (sqAt_matScale k bn (idMat k) (sqAt_idMat k)) h u hu)
  exact BPair.oneValue_trans (quadForm_scale bn (idMat k) u)
    (BPair.scale_congr bn (quadForm_idMat k u hu))

/-- The transfer's cap at the crossing's compression: the
comparison's read prices the withdrawn diagonal's form at the
carried vector against the coordinates' fold of squares, the
congruence determinant's square riding on the cap. -/
private theorem transferCap {j m n : Nat} (sp : Split m) (P : Mat)
    (w td : Pos) (spT : Split j) (hj : j = n)
    (hm : 0 < m) (hPl : P.length = m) (hPr : rowsLen n P)
    (h : leAt (matScale td (matMul (transposeM P)
        (matMul (blockMat (posBlocks sp.blocks) sp.kern) P)))
      (matScaleB ((minor sp.T.val * minor sp.T.val) * BPair.ofPos w)
        (idMat n)) spT) :
    ∀ u : List BPair, u.length = n →
      (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec P u)).scale td
        ≤ minor sp.T.val * minor sp.T.val * ((dotN u u).scale w) := by
  subst hj
  intro u hu
  have hBM : sqAt (blockMat (posBlocks sp.blocks) sp.kern) m :=
    sqAt_posBlockMat sp
  have hPpos : 0 < P.length := by rw [hPl]; exact hm
  have hYl : (matMul (blockMat (posBlocks sp.blocks) sp.kern) P).length
      = m := (length_matMul _ P).trans (sqAt_len hBM)
  have hYr : rowsLen j
      (matMul (blockMat (posBlocks sp.blocks) sp.kern) P) :=
    rowsLen_matMul_of _ P (fun _ => hPpos) hPr
  have hPTl : (transposeM P).length = j :=
    length_transposeM P hPr hPpos
  refine ground.leB_congr ?_ ?_
    (le_all _ _ spT
      (sqAt_matScale j td _
        (sqAt_of ((length_matMul _ _).trans hPTl)
          (rowsLen_matMul_of _ _ (fun _ => by rw [hYl]; exact hm) hYr)))
      (sqAt_scaleB _ j (idMat j) (sqAt_idMat j)) h u hu)
  · exact BPair.oneValue_trans (quadForm_scale td _ u)
      (BPair.scale_congr td
        (BPair.oneValue_symm (congQuad _ P m j hBM hPr hPl u hu)))
  · refine BPair.oneValue_trans (quadForm_scaleB _ (idMat j) u) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (elim.dotN_congrR u (matVec (idMat j) u) u
          (matVec_idMat j u hu))) ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofPos_scale w (dotN u u)))

/-- The step comparison's upper weight at the depth's clearing. -/
private theorem posE1 (mn fd G f r : Pos) :
    mn * (fd * G) * (f * r) = mn * (f * r) * (G * fd) := by
  rw [ground.mul_assoc mn (fd * G) (f * r),
    ground.mul_comm (fd * G) (f * r),
    ground.mul_comm fd G,
    ← ground.mul_assoc mn (f * r) (G * fd)]

/-- The step comparison's bond term reads the sandwich's own
weight. -/
private theorem posE3 (b1 g2 md fd f r : Pos) :
    b1 * (g2 * (md * fd)) * (f * r) = b1 * (g2 * r) * (f * md * fd) := by
  rw [ground.mul_assoc b1 (g2 * (md * fd)) (f * r),
    ground.mul_assoc g2 (md * fd) (f * r),
    ground.mul_assoc b1 (g2 * r) (f * md * fd),
    ground.mul_assoc g2 r (f * md * fd),
    ground.mul_mul_mul_comm md fd f r,
    ground.mul_left_comm r (f * md) fd,
    ground.mul_comm md f,
    ground.mul_comm fd r]

/-- The join's pivot term reads the conclusion's weight at the
shared clearing. -/
private theorem posE4 (r md G fd : Pos) :
    r * md * (G * fd) = fd * (md * G * r) := by
  rw [ground.mul_comm fd (md * G * r),
    ground.mul_assoc (md * G) r fd,
    ground.mul_mul_mul_comm md G r fd,
    ground.mul_comm r md]

/-- The dominance step's close: the diagonal's floor carried
through the join and priced against the bond's sandwich leaves the
depth's own floor, the shared bond term and the witness clearing
withdrawing at the cross-multiplied comparison. -/
private theorem domStepClose {n0 qa qf p : BPair}
    (f r mn md fn fd g2 b1 G : Pos)
    (hn : BPair.unit ≤ n0)
    (hD : n0.scale mn ≤ qa.scale md)
    (hJ : (qa.scale (f * r)).oneValue (qf.scale r + p.scale f))
    (hT : p.scale G ≤ n0.scale (b1 * (g2 * r)))
    (hC : fn * (md * G) + b1 * (g2 * (md * fd))
      ≤ mn * (fd * G)) :
    n0.scale (fn * f) ≤ qf.scale fd := by
  have s1 : n0.scale (mn * (f * r)) ≤ (qa.scale (f * r)).scale md := by
    have h := ground.leB_scale hD (f * r)
    rw [BPair.scale_scale, BPair.scale_comm qa md (f * r)] at h
    exact h
  have s2 : n0.scale (mn * (f * r))
      ≤ qf.scale (r * md) + p.scale (f * md) := by
    refine ground.leB_congr_right ?_ s1
    refine BPair.oneValue_trans (BPair.scale_congr md hJ) ?_
    rw [BPair.scale_add, BPair.scale_scale, BPair.scale_scale]
    exact BPair.oneValue_refl _
  have s3 : n0.scale (mn * (f * r) * (G * fd))
      ≤ qf.scale (r * md * (G * fd)) + p.scale (f * md * (G * fd)) := by
    have h := ground.leB_scale s2 (G * fd)
    rw [BPair.scale_scale, BPair.scale_add, BPair.scale_scale,
      BPair.scale_scale] at h
    exact h
  have s4 : p.scale (f * md * (G * fd))
      ≤ n0.scale (b1 * (g2 * r) * (f * md * fd)) := by
    have h := ground.leB_scale hT (f * md * fd)
    rw [BPair.scale_scale, BPair.scale_scale,
      ground.mul_left_comm G (f * md) fd] at h
    exact h
  have s5 : n0.scale (mn * (f * r) * (G * fd))
      ≤ qf.scale (r * md * (G * fd))
        + n0.scale (b1 * (g2 * r) * (f * md * fd)) :=
    ground.leB_trans s3 (ground.leB_add (ground.leB_refl _) s4)
  have hC2 : (fn * (md * G) + b1 * (g2 * (md * fd))) * (f * r)
      ≤ mn * (fd * G) * (f * r) :=
    ground.mul_le_mul_right (f * r) hC
  have s6 : n0.scale (fn * f * (md * G * r))
        + n0.scale (b1 * (g2 * r) * (f * md * fd))
      ≤ n0.scale (mn * (f * r) * (G * fd)) := by
    have h := ground.leB_scaleMono hn hC2
    rw [ground.right_distrib (fn * (md * G)) (b1 * (g2 * (md * fd)))
        (f * r),
      BPair.scale_addW, ground.mul_mul_mul_comm fn (md * G) f r,
      posE3 b1 g2 md fd f r,
      posE1 mn fd G f r] at h
    exact h
  have s7 : n0.scale (b1 * (g2 * r) * (f * md * fd))
        + n0.scale (fn * f * (md * G * r))
      ≤ n0.scale (b1 * (g2 * r) * (f * md * fd))
        + qf.scale (r * md * (G * fd)) :=
    ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (ground.leB_trans s6 s5)
  have s8 : n0.scale (fn * f * (md * G * r))
      ≤ qf.scale (r * md * (G * fd)) := ground.leB_cancelL s7
  have s9 : (n0.scale (fn * f)).scale (md * G * r)
      ≤ (qf.scale fd).scale (md * G * r) := by
    rw [BPair.scale_scale, BPair.scale_scale, ← posE4 r md G fd]
    exact s8
  exact ground.leB_of_scale s9

/-- The dominance walk's per-position read: the pivot's form at or
beyond its floor multiple of the coordinates' fold of squares, at
every default the floor list is blind to. -/
private def domAt (Xs : List MatQ) (ns : List Nat) (Ds : List DomStep)
    (i : Nat) : Prop :=
  ∀ d : DomStep, ∀ u : List BPair,
    u.length = ground.getAt 0 ns i →
      (dotN u u).scale ((ground.getAt d Ds i).fl.1
          * (ground.getAt dM Xs i).2)
        ≤ (quadForm (ground.getAt dM Xs i).1 u).scale
          (ground.getAt d Ds i).fl.2

/-- The dominance tail's floor list pairs one depth per pivot below
the crossing's own. -/
private theorem domLen (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
      domRead spc spT tn td diag off Xs Rs ns Ds Cs →
      Ds.length < Xs.length
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [], _ =>
    Nat.succ_lt_succ (Nat.succ_pos _)
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xt, _ :: Rs, _ :: n' :: nt,
      _ :: D' :: Ds, _ :: Cs, hread =>
    Nat.succ_lt_succ
      (domLen spc spT tn td (A' :: As) Bs (X' :: Xt) Rs (n' :: nt)
        (D' :: Ds) Cs hread.2)
  | [], _, _, _, _, _, _, hread => hread.elim
  | [_], _, _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, [], _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [_], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _,
      hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [], hread => hread.elim

/-- The seed arm's crossing split sits at the floor list's own
position, the walk shifting one pivot per depth. -/
theorem domTail_cross (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
      domRead spc spT tn td diag off Xs Rs ns Ds Cs →
      splitRead (ground.getAt dM Xs Ds.length).1 spc.2
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [],
      hread => hread.2.2.2.1
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xt, _ :: Rs, _ :: n' :: nt,
      _ :: D' :: Ds, _ :: Cs, hread =>
    domTail_cross spc spT tn td (A' :: As) Bs (X' :: Xt) Rs (n' :: nt)
      (D' :: Ds) Cs hread.2
  | [], _, _, _, _, _, _, hread => hread.elim
  | [_], _, _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, [], _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [_], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _,
      hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [], hread => hread.elim

/-- Clause (vii)'s dominance walk at the read's own arm
enumeration: the seed arm reads the rebound's floor at the
crossing's following depth and the step arm carries the deeper
floor up through the join, the bond's sandwich pricing the
withdrawn term. -/
private theorem domGo (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
      domRead spc spT tn td diag off Xs Rs ns Ds Cs →
      tailRead diag off Xs Rs ns →
      ∀ i, i < Ds.length → domAt Xs ns Ds i
  | A :: A2 :: As, B :: Bs, X :: X' :: Xt, R :: Rs, n :: n' :: nt,
      [D], [], hread, ht, 0, _ => by
    obtain ⟨hDord, hspc, hspT, hsplit, hdg, htr, hcmp⟩ := hread
    intro _ u hu
    have hn : 0 < n := ht.1.1
    have hn' : 0 < n' :=
      greenprod.slab_pos ht.1.2.2.2 0 (Nat.succ_pos _)
    have hRl : R.1.length = n' := rectAt_len ht.2.2.1.1
    refine rebound_floor (o := n) (o' := spc.1) X X' R A B spc.2
      D.dg.1 D.dg.2 tn td D.fl.1 D.fl.2 hn (by rw [hspc]; exact hn')
      ht.2.1.1 (by rw [hspc]; exact ht.1.2.2.1)
      (by rw [hspc]; exact ht.2.2.1.1)
      ht.2.2.2.1.2.1 ht.2.2.2.1.2.2 hsplit
      (diagFloor A D.dg.1 D.dg.2 D.spM hDord ht.1.2.1 hdg)
      (transferCap spc.2 (matMul spc.2.Tw.val R.1)
        (tn * (X'.2 * (R.2 * R.2))) td spT.2 hspT
        (by rw [hspc]; exact hn')
        ((length_matMul _ R.1).trans spc.2.Tw.rows)
        (rowsLen_matMul_of _ R.1
          (fun _ => by rw [hRl]; exact hn') (rectAt_rows ht.2.2.1.1))
        htr)
      hcmp u hu
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [],
      _, _, _ + 1, hi =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | A :: A' :: As, B :: Bs, X :: X' :: Xt, R :: Rs, n :: n' :: nt,
      D :: D' :: Ds, C :: Cs, hread, ht, 0, _ => by
    obtain ⟨⟨hDord, hCord, hdg, hbd, hcmp⟩, hrest⟩ := hread
    intro d u hu
    have hn : 0 < n := ht.1.1
    have hn' : 0 < n' :=
      greenprod.slab_pos ht.1.2.2.2 0 (Nat.succ_pos _)
    have hrec := domGo spc spT tn td (A' :: As) Bs (X' :: Xt) Rs
      (n' :: nt) (D' :: Ds) Cs hrest (tailTail ht) 0
      (Nat.succ_pos _) d
    have h2 := greenprod.sandwich_cap X' R B D'.fl.1 D'.fl.2
      C.2.1.1 C.2.1.2 hn ht.1.2.2.1 ht.2.2.1.1 ht.2.2.2.1.2.1 hrec
      (bondCap (n' := n') B C.2.1.1 C.2.1.2 C.2.2 hCord hn hn'
        ht.1.2.2.1 hbd)
      u hu
    rw [ground.mul_comm D'.fl.1 C.2.1.2] at h2
    exact domStepClose X.2 R.2 D.dg.1 D.dg.2 D.fl.1 D.fl.2 D'.fl.2
      C.2.1.1 (C.2.1.2 * D'.fl.1)
      (ground.leB_of_not_lt (elim.dotN_self_side u))
      (diagFloor A D.dg.1 D.dg.2 D.spM hDord ht.1.2.1 hdg u hu)
      (greenprod.join_quadSplit X R A B hn' ht.2.1.1 ht.1.2.2.1
        ht.2.2.1.1 ht.2.2.2.1.2.2 u hu)
      h2 hcmp
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xt, _ :: Rs, _ :: n' :: nt,
      _ :: D' :: Ds, _ :: Cs, hread, ht, i + 1, hi =>
    domGo spc spT tn td (A' :: As) Bs (X' :: Xt) Rs (n' :: nt)
      (D' :: Ds) Cs hread.2 (tailTail ht) i
      (Nat.lt_of_succ_lt_succ hi)
  | [], _, _, _, _, _, _, hread, _, _, _ => hread.elim
  | [_], _, _, _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, [], _, _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, [_], _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, hread, _, _, _ =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _, hread, _, _,
      _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _, hread, _, _,
      _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _,
      hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [], hread, _, _, _ => hread.elim

/-- The floor list's blind default. -/
private def dDom : DomStep :=
  ⟨0, (Pos.one, Pos.one), (Pos.one, Pos.one),
    ⟨⟨idMat 0, rfl⟩, ⟨idMat 0, rfl⟩, [], 0, rfl⟩⟩

/-- Past the crossing every deep pivot's stated split reads the
upper side throughout, the floor list's read. -/
theorem domTail_psd : ∀ (spc spT : (k : Nat) × Split k) (tn td : Pos)
    (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
    (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
    domRead spc spT tn td diag off Xs Rs ns Ds Cs →
    tailRead diag off Xs Rs ns →
    ∀ i, i < Ds.length →
      ∀ s : (k : Nat) × Split k,
        splitRead (ground.getAt dM Xs i).1 s.2 → psdAt s.2 := by
  intro spc spT tn td diag off Xs Rs ns Ds Cs hread ht i hi s hs
  have hiX : i < Xs.length :=
    Nat.lt_trans hi (domLen spc spT tn td diag off Xs Rs ns Ds Cs hread)
  have hlen : s.1 = ground.getAt 0 ns i :=
    (sqAt_len hs.1).symm.trans (sqAt_len (qShape_at ht.2.1 i hiX))
  refine inertia.psd_of_all (ground.getAt dM Xs i).1 s.2 hs ?_
  intro u hu
  refine ground.leB_not_lt
    (ground.unitLeOfScale (w := (ground.getAt dDom Ds i).fl.2) ?_)
  exact ground.leB_trans
    (ground.unitLeScale _
      (ground.leB_of_not_lt (elim.dotN_self_side u)))
    (domGo spc spT tn td diag off Xs Rs ns Ds Cs hread ht i hi dDom u
      (hu.trans hlen))

/-! The count's suffix reads: the dropped chain's leading entry
peeled off the trailing segment, the segment's occupancy at the
withdrawn count, and the center family's own nonempty slab
list. -/

/-! Clause (vii)'s walked segment at the family: the stated chain
data read against the family's evaluated reads over a depth range,
the per-depth centers, witnesses and images the family's own
evaluations with their clearings' margins, and the transport run
down the recursion at the pointwise counts. -/

/-- The evaluated center at a depth: the center family's matrix with
its clearing's own margin. -/
def famYc (F : CenterFam) (en ed : Pos) (K d : Nat) : MatQ :=
  (evalPfm F.Cf.1 d en ed K,
   BPair.marginPos (evalProf F.Cf.2 d en ed K))

/-- The evaluated witness at a depth. -/
private def famW (F : CenterFam) (en ed : Pos) (K d : Nat) : MatQ :=
  (evalPfm F.Wf.1 d en ed K,
   BPair.marginPos (evalProf F.Wf.2 d en ed K))

/-- The evaluated image at a depth. -/
private def famI (F : CenterFam) (en ed : Pos) (K d : Nat) : MatQ :=
  (evalPfm F.If.1 d en ed K,
   BPair.marginPos (evalProf F.If.2 d en ed K))

/-- The chain's stated data read at the family over the segment's
depth range, deep-first: position `p` sits at depth
`m0 + (diag.length - 1 - p)`, the boundary seed at depth `m0` the
last position and the deep end the first; the order list constant at
the family's order; each stated diagonal, scaled by the clearing's
stated power, the family's evaluated diagonal at its position's own
depth; each bond the stated bond; the four walks' boxes holding
every segment depth's scale point at clearing powers inside the
counts' own, and the three clearing certificates' boxes holding them
at powers inside the stated one. -/
def famChainRead (F : CenterFam) (B : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (ns : List Nat) : Prop :=
  ns = List.replicate diag.length F.o
  ∧ ((List.range diag.length).all (fun p =>
      decide (elim.matOneValue
        (inertia.matScale (Pos.powC ed K) (ground.getAt [] diag p))
        (evalPfm F.Af (m0 + (diag.length - 1 - p)) en ed K)))) = true
  ∧ ((List.range off.length).all (fun p =>
      decide (elim.matOneValue (ground.getAt [] off p) B))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxC.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxF.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxU.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxL.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p =>
      decide (F.bxClC.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClC.hi)
      && Nat.ble (F.bxClC.K + 1) (K + 1))) = true
  ∧ ((List.range diag.length).all (fun p =>
      decide (F.bxClW.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClW.hi)
      && Nat.ble (F.bxClW.K + 1) (K + 1))) = true
  ∧ ((List.range diag.length).all (fun p =>
      decide (F.bxClI.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClI.hi)
      && Nat.ble (F.bxClI.K + 1) (K + 1))) = true

instance (F : CenterFam) (B : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (ns : List Nat) :
    Decidable (famChainRead F B en ed K m0 diag off ns) :=
  inferInstanceAs
    (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The clearing's margin reads its family's evaluated clearing back
at a depth the certificate's box holds. -/
private theorem clTie (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) (m K : Nat) (en ed : Pos)
    (hr : boxRead V e0n e0d C)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hb : (decide (C.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ C.hi)
        && Nat.ble (C.K + 1) (K + 1)) = true) :
    (BPair.ofPos (BPair.marginPos (evalProf V m en ed K))).oneValue
      (evalProf V m en ed K) := by
  have h2 := ground.andSplitB hb
  have h3 := ground.andSplitB h2.1
  exact BPair.marginPos_read (clearPos V e0n e0d C m K en ed hr he
    (of_decide_eq_true h3.1) (of_decide_eq_true h3.2)
    (ground.bleLe h2.2))

/-- The chain's stated data read position by position: the orders,
the diagonal and bond ties, and the seven certificate boxes at each
segment position's own depth. -/
private def famChainPt (F : CenterFam) (B : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (ns : List Nat) : Prop :=
  (∀ i, i < ns.length → ground.getAt 0 ns i = F.o)
  ∧ (∀ p, p < diag.length → elim.matOneValue
      (inertia.matScale (Pos.powC ed K) (ground.getAt [] diag p))
      (evalPfm F.Af (m0 + (diag.length - 1 - p)) en ed K))
  ∧ (∀ p, p < off.length →
      elim.matOneValue (ground.getAt [] off p) B)
  ∧ (∀ p, p < diag.length → (F.bxC.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length → (F.bxF.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length → (F.bxU.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length → (F.bxL.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length →
      (decide (F.bxClC.lo
        ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
          * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩
            : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClC.hi)
      && Nat.ble (F.bxClC.K + 1) (K + 1)) = true)
  ∧ (∀ p, p < diag.length →
      (decide (F.bxClW.lo
        ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
          * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩
            : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClW.hi)
      && Nat.ble (F.bxClW.K + 1) (K + 1)) = true)
  ∧ (∀ p, p < diag.length →
      (decide (F.bxClI.lo
        ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
          * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩
            : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClI.hi)
      && Nat.ble (F.bxClI.K + 1) (K + 1)) = true)

/-- The stated read's pointwise reads, the range folds walked. -/
private theorem famChainRead_pt (F : CenterFam) (B : elim.Mat)
    (en ed : Pos) (K m0 : Nat) (diag off : List elim.Mat)
    (ns : List Nat) (h : famChainRead F B en ed K m0 diag off ns) :
    famChainPt F B en ed K m0 diag off ns := by
  obtain ⟨hns, hdg, hof, hbC, hbF, hbU, hbL, hcC, hcW, hcI⟩ := h
  refine ⟨fun i hi => ?_,
    fun p hp => of_decide_eq_true
      (ground.all_range_read diag.length hdg p hp),
    fun p hp => of_decide_eq_true
      (ground.all_range_read off.length hof p hp),
    fun p hp => ground.all_range_read diag.length hbC p hp,
    fun p hp => ground.all_range_read diag.length hbF p hp,
    fun p hp => ground.all_range_read diag.length hbU p hp,
    fun p hp => ground.all_range_read diag.length hbL p hp,
    fun p hp => ground.all_range_read diag.length hcC p hp,
    fun p hp => ground.all_range_read diag.length hcW p hp,
    fun p hp => ground.all_range_read diag.length hcI p hp⟩
  rw [hns] at hi ⊢
  rw [ground.length_replicate] at hi
  exact ground.getAt_replicate 0 F.o diag.length i hi

/-- The pointwise read at the deeper segment, the depth formula
stable under the peel: the boundary depth `m0` is the tail's own. -/
private theorem famChainPt_tail (F : CenterFam) (B : elim.Mat)
    (en ed : Pos) (K m0 : Nat) (A B0 : elim.Mat)
    (diag' off' : List elim.Mat) (n : Nat) (ns' : List Nat)
    (h : famChainPt F B en ed K m0 (A :: diag') (B0 :: off')
      (n :: ns')) :
    famChainPt F B en ed K m0 diag' off' ns' := by
  obtain ⟨hno, hdg, hof, hbC, hbF, hbU, hbL, hcC, hcW, hcI⟩ := h
  refine ⟨fun i hi => hno (i + 1) (Nat.succ_lt_succ hi),
    fun p hp => ?_, fun p hp => hof (p + 1) (Nat.succ_lt_succ hp),
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hdg (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbC (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbF (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbU (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbL (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hcC (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hcW (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hcI (p + 1) (Nat.succ_lt_succ hp)

/-- The walk's per-position ball: the pivot in its depth's evaluated
center's ball at the family's radius pair. -/
private def famBallAt (F : CenterFam) (G : elim.Mat) (en ed : Pos)
    (K : Nat) (X : MatQ) (d : Nat) : Prop :=
  (∀ u : List BPair, u.length = F.o →
      (quadForm (devQ X (famYc F en ed K d)).1 u).scale F.rho.2
        ≤ (quadForm G u).scale
            (F.rho.1 * (devQ X (famYc F en ed K d)).2))
  ∧ (∀ u : List BPair, u.length = F.o →
      ((quadForm G u).scale
          (F.rho.1 * (devQ X (famYc F en ed K d)).2)).swap
        ≤ (quadForm (devQ X (famYc F en ed K d)).1 u).scale F.rho.2)

/-- Clause (vii)'s segment walk at the family, deep-first: the seed
arm converts the boundary seed's cap onto the seed pivot at the
boundary depth `m0`, and the step arm hands the ball from the
shallower position's center to the deeper outright, every read the
family's own evaluation at the position's own depth. -/
private theorem famChainGo (F : CenterFam) (B G : elim.Mat)
    (en ed : Pos) (K : Nat)
    (hfam : famRead F B G)
    (he : BPair.ofPos en * BPair.ofPos F.e0.2
      ≤ F.e0.1 * BPair.ofPos ed)
    (hshA : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Af i) j)
        d)).length ≤ K + 1)
    (hshC : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Cf.1 i) j)
        d)).length ≤ K + 1)
    (hshCl : ∀ d, (poly.vnorm (depthPoly F.Cf.2 d)).length ≤ K + 1)
    (hshW : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Wf.1 i) j)
        d)).length ≤ K + 1)
    (hshWcl : ∀ d, (poly.vnorm (depthPoly F.Wf.2 d)).length ≤ K + 1)
    (hshI : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.If.1 i) j)
        d)).length ≤ K + 1)
    (hshIcl : ∀ d, (poly.vnorm (depthPoly F.If.2 d)).length ≤ K + 1) :
    ∀ (diag : List Mat) (m0 : Nat) (off : List Mat) (ns : List Nat)
      (Xs Rs : List MatQ),
      famChainPt F B en ed K m0 diag off ns →
      tailRead diag off Xs Rs ns →
      (∀ i, i < Xs.length → matOneValue
        (transposeM (ground.getAt dM Xs i).1) (ground.getAt dM Xs i).1) →
      (∀ p, p + 1 = diag.length → ∀ u : List BPair, u.length = F.o →
        (quadForm (devQ (ofM (ground.getAt [] diag p))
            (famYc F en ed K m0)).1 u).scale F.rho.2
          ≤ (quadForm G u).scale (F.rho.1
              * (devQ (ofM (ground.getAt [] diag p))
                  (famYc F en ed K m0)).2)) →
      (∀ p, p + 1 = diag.length → ∀ u : List BPair, u.length = F.o →
        ((quadForm G u).scale (F.rho.1
            * (devQ (ofM (ground.getAt [] diag p))
                (famYc F en ed K m0)).2)).swap
          ≤ (quadForm (devQ (ofM (ground.getAt [] diag p))
              (famYc F en ed K m0)).1 u).scale F.rho.2) →
      ∀ i, i < Xs.length →
        famBallAt F G en ed K (ground.getAt dM Xs i)
          (m0 + (diag.length - 1 - i))
  | [], _, _, _, _, _, _, ht, _, _, _, _, _ => ht.1.elim
  | _ :: _, _, _, [], _, _, _, ht, _, _, _, _, _ => ht.1.elim
  | [_], _, _ :: _, [_], _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | [_], _, _ :: _, _ :: _ :: _, _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | [_], _, [], _ :: _ :: _, _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | _ :: _ :: _, _, [], [_], _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | _ :: _ :: _, _, [], _ :: _ :: _, _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | _ :: _ :: _, _, _ :: _, [_], _, _, _, ht, _, _, _, _, _ => ht.1.elim
  | [_], _, [], [_], [], _, _, ht, _, _, _, _, _ => ht.2.1.elim
  | [_], _, [], [_], _ :: _ :: _, _, _, ht, _, _, _, _, _ =>
    ht.2.1.2.elim
  | [_], _, [], [_], [_], _ :: _, _, ht, _, _, _, _, _ =>
    ht.2.2.1.elim
  | [_], _, [], [_], [_], [], _, _, _, _, _, _ + 1, hi =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | [A], m0, [], [n], [X], [], hpt, ht, _, hsdHi, hsdLo, 0, _ => by
    have hn : n = F.o := hpt.1 0 (Nat.succ_pos 0)
    have hXsq : sqAt X.1 F.o := by rw [← hn]; exact ht.2.1.1
    have hAsq : sqAt A F.o := by rw [← hn]; exact ht.1.2
    have hYcq : sqAt (famYc F en ed K m0).1 F.o :=
      elim.sqAt_of ((length_evalPfm m0 F.Cf.1 en ed K).trans hfam.2.2.1)
        (rowsLen_evalPfm F.o m0 F.Cf.1 en ed K hfam.2.2.2.1)
    exact seedCap X (famYc F en ed K m0) A G F.rho.1 F.rho.2
      hXsq hYcq hAsq ht.2.2.2 (hsdHi 0 rfl) (hsdLo 0 rfl)
  | _ :: _ :: _, _, _ :: _, _ :: _ :: _, [], _, _, ht, _, _, _, _, _ =>
    ht.2.1.elim
  | _ :: _ :: _, _, _ :: _, _ :: _ :: _, [_], _, _, ht, _, _, _, _, _ =>
    ht.2.1.2.elim
  | _ :: _ :: _, _, _ :: _, _ :: _ :: _, _ :: _ :: _, [], _, ht, _, _,
      _, _, _ => ht.2.2.1.elim
  | A :: A' :: As, m0, B0 :: Bs, n :: n' :: nt, X :: X' :: Xt, R :: Rt,
      hpt, ht, hsx, hsdHi, hsdLo, 0, _ => by
    obtain ⟨hAl, hAr, hCl, hCr, hWl, hWr, hIl, hIr, hBq, hGq, hsymG,
      hsymCf, hsymIf, hwitF, hjoinF, hwC, hwF, hwU, hwL, hbrC, hbrW,
      hbrI, htie, hmod⟩ := id hfam
    have hn : n = F.o := hpt.1 0 (Nat.succ_pos _)
    have hn' : n' = F.o := hpt.1 1 (Nat.succ_lt_succ (Nat.succ_pos _))
    have ho : 0 < F.o := by rw [← hn]; exact ht.1.1
    -- the deeper and shallower pivots and the segment's data
    have hXq : sqAt X.1 F.o := by rw [← hn]; exact ht.2.1.1
    have hX'q : sqAt X'.1 F.o := by rw [← hn']; exact ht.2.1.2.1
    have hApos : sqAt A F.o := by rw [← hn]; exact ht.1.2.1
    have hRq : rectAt R.1 F.o F.o := by
      have h := ht.2.2.1.1
      rw [hn', hn] at h
      exact h
    have hB0q : rectAt B0 F.o F.o := by
      have h := ht.1.2.2.1
      rw [hn, hn'] at h
      exact h
    have hBr : rectAt B F.o F.o :=
      elim.rectAt_of (elim.sqAt_len hBq) (elim.rowsLen_of_sqAt hBq)
    -- the evaluated centers, witness and image at the step's depths
    have hYcSq : sqAt (famYc F en ed K (m0 + As.length)).1 F.o :=
      elim.sqAt_of
        ((length_evalPfm (m0 + As.length) F.Cf.1 en ed K).trans hCl)
        (rowsLen_evalPfm F.o (m0 + As.length) F.Cf.1 en ed K hCr)
    have hYcTq : sqAt (famYc F en ed K (m0 + (As.length + 1))).1 F.o :=
      elim.sqAt_of
        ((length_evalPfm (m0 + (As.length + 1)) F.Cf.1 en ed K).trans
          hCl)
        (rowsLen_evalPfm F.o (m0 + (As.length + 1)) F.Cf.1 en ed K hCr)
    have hIq : sqAt (famI F en ed K (m0 + (As.length + 1))).1 F.o :=
      elim.sqAt_of
        ((length_evalPfm (m0 + (As.length + 1)) F.If.1 en ed K).trans
          hIl)
        (rowsLen_evalPfm F.o (m0 + (As.length + 1)) F.If.1 en ed K hIr)
    have hCcq : rectAt (famW F en ed K (m0 + (As.length + 1))).1
        F.o F.o :=
      elim.rectAt_of
        ((length_evalPfm (m0 + (As.length + 1)) F.Wf.1 en ed K).trans
          hWl)
        (rowsLen_evalPfm F.o (m0 + (As.length + 1)) F.Wf.1 en ed K hWr)
    -- the clearings' margins at their certificates' boxes
    have hcCS := clTie F.Cf.2 F.e0.1 F.e0.2 F.bxClC (m0 + As.length) K
      en ed hbrC he
      (hpt.2.2.2.2.2.2.2.1 1 (Nat.succ_lt_succ (Nat.succ_pos _)))
    have hcCT := clTie F.Cf.2 F.e0.1 F.e0.2 F.bxClC
      (m0 + (As.length + 1)) K en ed hbrC he
      (hpt.2.2.2.2.2.2.2.1 0 (Nat.succ_pos _))
    have hcWT := clTie F.Wf.2 F.e0.1 F.e0.2 F.bxClW
      (m0 + (As.length + 1)) K en ed hbrW he
      (hpt.2.2.2.2.2.2.2.2.1 0 (Nat.succ_pos _))
    have hcIT := clTie F.If.2 F.e0.1 F.e0.2 F.bxClI
      (m0 + (As.length + 1)) K en ed hbrI he
      (hpt.2.2.2.2.2.2.2.2.2 0 (Nat.succ_pos _))
    -- the bond conversion onto the stated bond
    have hoff : matOneValue B0 B := hpt.2.2.1 0 (Nat.succ_pos _)
    have hw : oneValueQ (mulQ X' R) (ofM (transposeM B)) :=
      elim.matOne_trans ht.2.2.2.1.2.1
        (inertia.matScale_matOne (X'.2 * R.2)
          (elim.transposeM_congrM F.o B0 B (rectAt_rows hB0q)
            (elim.rowsLen_of_sqAt hBq)
            ((rectAt_len hB0q).trans (elim.sqAt_len hBq).symm) hoff))
    have hRrow : rowsLen F.o (matMul B0 R.1) :=
      elim.rowsLen_matMul_of B0 R.1
        (fun _ => by rw [rectAt_len hRq]; exact ho) (rectAt_rows hRq)
    have hRrow' : rowsLen F.o (matMul B R.1) :=
      elim.rowsLen_matMul_of B R.1
        (fun _ => by rw [rectAt_len hRq]; exact ho) (rectAt_rows hRq)
    have hj : oneValueQ (addQ X (mulQ (ofM B) R)) (ofM A) :=
      elim.matOne_trans
        (inertia.matScale_matOne Pos.one
          (elim.matAdd_cong2 F.o _ _ _ _
            (elim.rowsLen_mapRows _ X.1 F.o (elim.rowsLen_of_sqAt hXq))
            (elim.rowsLen_mapRows _ _ F.o hRrow')
            (elim.rowsLen_mapRows _ X.1 F.o (elim.rowsLen_of_sqAt hXq))
            (elim.rowsLen_mapRows _ _ F.o hRrow)
            (elim.matOne_refl _)
            (inertia.matScale_matOne X.2
              (elim.matMul_congrL B B0 R.1 (elim.matOne_symm hoff)))))
        ht.2.2.2.1.2.2
    -- the family's own two ties at the step's two depths
    have hwc := witTie_ptw F.Cf F.Wf B F.o (m0 + As.length) K en ed
      (BPair.marginPos (evalProf F.Cf.2 (m0 + As.length) en ed K))
      (BPair.marginPos (evalProf F.Wf.2 (m0 + As.length + 1) en ed K))
      hCr hWl hWr ho (fun i j => hshC (m0 + As.length) i j)
      (hshCl (m0 + As.length))
      (fun i j => hshW (m0 + As.length + 1) i j)
      (hshWcl (m0 + As.length + 1)) hcCS hcWT hwitF
    have hpow : (BPair.ofPos (Pos.powC ed K)).oneValue
        (ground.bpow (BPair.ofPos ed) K) := by
      rw [Pos.powC_eq]
      exact ground.ofPos_pow ed K
    have hjc := joinTie_ptw F.Af F.Wf F.If A B F.o
      (m0 + (As.length + 1)) K en ed (Pos.powC ed K)
      (BPair.marginPos (evalProf F.If.2 (m0 + (As.length + 1)) en ed K))
      (BPair.marginPos (evalProf F.Wf.2 (m0 + (As.length + 1)) en ed K))
      hAl hAr hWl hWr hIl hIr hBq hApos ho
      (fun i j => hshA (m0 + (As.length + 1)) i j)
      (fun i j => hshW (m0 + (As.length + 1)) i j)
      (hshWcl (m0 + (As.length + 1)))
      (fun i j => hshI (m0 + (As.length + 1)) i j)
      (hshIcl (m0 + (As.length + 1))) hcIT hcWT hpow
      (hpt.2.1 0 (Nat.succ_pos _)) hjoinF
    -- the four pointwise counts
    have hFp := floorCount_ptw F.Cf G F.o F.y0.1 F.y0.2 F.rho.1 F.rho.2
      F.e0.1 F.e0.2 F.bxF (m0 + As.length) K en ed
      (BPair.marginPos (evalProf F.Cf.2 (m0 + As.length) en ed K))
      hCl hCr hGq hsymCf hsymG (fun i j => hshC (m0 + As.length) i j)
      (hshCl (m0 + As.length)) hwF he
      (hpt.2.2.2.2.1 1 (Nat.succ_lt_succ (Nat.succ_pos _))) hcCS
    have hconp := contrCount_ptw F.Wf G F.o F.lam.1 F.lam.2
      F.e0.1 F.e0.2 F.bxC (m0 + (As.length + 1)) K en ed
      (BPair.marginPos (evalProf F.Wf.2 (m0 + (As.length + 1)) en ed K))
      hWl hWr hGq hsymG (fun i j => hshW (m0 + (As.length + 1)) i j)
      (hshWcl (m0 + (As.length + 1))) hwC he
      (hpt.2.2.2.1 0 (Nat.succ_pos _)) hcWT
    have hdefHi := dcapCount_hi F.Cf F.If G F.o F.dft.1 F.dft.2
      F.e0.1 F.e0.2 F.bxU (m0 + (As.length + 1)) K en ed
      (BPair.marginPos (evalProf F.If.2 (m0 + (As.length + 1)) en ed K))
      (BPair.marginPos (evalProf F.Cf.2 (m0 + (As.length + 1)) en ed K))
      hIl hIr hCl hCr hGq hsymCf hsymIf hsymG
      (fun i j => hshI (m0 + (As.length + 1)) i j)
      (hshIcl (m0 + (As.length + 1)))
      (fun i j => hshC (m0 + (As.length + 1)) i j)
      (hshCl (m0 + (As.length + 1))) hwU he
      (hpt.2.2.2.2.2.1 0 (Nat.succ_pos _)) hcIT hcCT
    have hdefLo := dcapCount_lo F.Cf F.If G F.o F.dft.1 F.dft.2
      F.e0.1 F.e0.2 F.bxL (m0 + (As.length + 1)) K en ed
      (BPair.marginPos (evalProf F.If.2 (m0 + (As.length + 1)) en ed K))
      (BPair.marginPos (evalProf F.Cf.2 (m0 + (As.length + 1)) en ed K))
      hIl hIr hCl hCr hGq hsymCf hsymIf hsymG
      (fun i j => hshI (m0 + (As.length + 1)) i j)
      (hshIcl (m0 + (As.length + 1)))
      (fun i j => hshC (m0 + (As.length + 1)) i j)
      (hshCl (m0 + (As.length + 1))) hwL he
      (hpt.2.2.2.2.2.2.1 0 (Nat.succ_pos _)) hcIT hcCT
    -- the shallower position's ball
    have hrec := famChainGo F B G en ed K hfam he
      hshA hshC hshCl hshW hshWcl hshI hshIcl
      (A' :: As) m0 Bs (n' :: nt) (X' :: Xt) Rt
      (famChainPt_tail F B en ed K m0 A B0 (A' :: As) Bs n
        (n' :: nt) hpt)
      (tailTail ht) (fun j hj => hsx (j + 1) (Nat.succ_lt_succ hj))
      (fun p hp => hsdHi (p + 1) (congrArg Nat.succ hp))
      (fun p hp => hsdLo (p + 1) (congrArg Nat.succ hp))
      0 (Nat.succ_pos _)
    exact ball_step_of (o := F.o) (o' := F.o)
      X' X (famYc F en ed K (m0 + As.length))
      (famI F en ed K (m0 + (As.length + 1)))
      (famYc F en ed K (m0 + (As.length + 1))) R
      (famW F en ed K (m0 + (As.length + 1))) A B G G
      F.lam.1 F.lam.2 F.y0.1 F.y0.2 F.rho.1 F.rho.2 F.dft.1 F.dft.2
      F.lc.1 F.lc.2 hX'q hXq hYcSq hIq hYcTq hRq hCcq hApos hBr hGq
      (hsx 1 (Nat.succ_lt_succ (Nat.succ_pos _)))
      (evalSymOf F.Cf.1 F.o (m0 + As.length) K en ed hCl hCr hsymCf)
      hw hj hwc hjc hrec.1 hrec.2 hFp hconp hsymG (fun h => h)
      hdefHi hdefLo htie hmod
  | A :: A' :: As, m0, B0 :: Bs, n :: n' :: nt, X :: X' :: Xt, R :: Rt,
      hpt, ht, hsx, hsdHi, hsdLo, i + 1, hi => by
    have h := famChainGo F B G en ed K hfam he hshA hshC hshCl
      hshW hshWcl hshI hshIcl (A' :: As) m0 Bs (n' :: nt)
      (X' :: Xt) Rt
      (famChainPt_tail F B en ed K m0 A B0 (A' :: As) Bs n
        (n' :: nt) hpt)
      (tailTail ht) (fun j hj => hsx (j + 1) (Nat.succ_lt_succ hj))
      (fun p hp => hsdHi (p + 1) (congrArg Nat.succ hp))
      (fun p hp => hsdLo (p + 1) (congrArg Nat.succ hp))
      i (Nat.lt_of_succ_lt_succ hi)
    have hd : (A :: A' :: As).length - 1 - (i + 1) = As.length - i :=
      Nat.succ_sub_succ As.length i
    rw [hd]
    exact h

/-- Clause (vii)'s walked segment at the family: from the boundary
seed's cap at depth `m0`, the last position, the one-depth transport
hands the ball from each position's center to the deeper position's
down the recursion at the family's evaluated reads — every pivot at
its position's own depth in the ball of the family's center there,
the centers' consecutive drift riding the defect — and every pivot's
every stated split reads the upper side throughout, the slab fold at
the count's unit. -/
theorem famChain_psd (F : CenterFam) (B G : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (Xs Rs : List MatQ)
    (ns : List Nat) (sps : List ((n : Nat) × Split n))
    (spSU spSL : Split F.o)
    (hfam : famRead F B G)
    (he : BPair.ofPos en * BPair.ofPos F.e0.2
      ≤ F.e0.1 * BPair.ofPos ed)
    (hshA : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Af i) j)
        d)).length ≤ K + 1)
    (hshC : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Cf.1 i) j)
        d)).length ≤ K + 1)
    (hshCl : ∀ d, (poly.vnorm (depthPoly F.Cf.2 d)).length ≤ K + 1)
    (hshW : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Wf.1 i) j)
        d)).length ≤ K + 1)
    (hshWcl : ∀ d, (poly.vnorm (depthPoly F.Wf.2 d)).length ≤ K + 1)
    (hshI : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.If.1 i) j)
        d)).length ≤ K + 1)
    (hshIcl : ∀ d, (poly.vnorm (depthPoly F.If.2 d)).length ≤ K + 1)
    (hchain : famChainRead F B en ed K m0 diag off ns)
    (ht : tailRead diag off Xs Rs ns)
    (hsymD : greenprod.symRead diag)
    (hseed : spectator.capQ
      (spectator.devQ
        (greenprod.ofM (ground.getAt [] diag (diag.length - 1)))
        (famYc F en ed K m0)) G F.rho.1 F.rho.2 spSU spSL)
    (hl : revListRead Xs sps) :
    revFold sps = 0 := by
  obtain ⟨hAl, hAr, hCl, hCr, hWl, hWr, hIl, hIr, hBq, hGq, hsymG,
    hsymCf, hsymIf, hwitF, hjoinF, hwC, hwF, hwU, hwL, hbrC, hbrW,
    hbrI, htie, hmod⟩ := id hfam
  have hpt := famChainRead_pt F B en ed K m0 diag off ns hchain
  have hball := famChainGo F B G en ed K hfam he
    hshA hshC hshCl hshW hshWcl hshI hshIcl diag m0 off ns Xs Rs hpt ht
    (greenprod.tailSym diag off Xs Rs ns ht hsymD)
    (fun p hp u hu => by
      have hp' : p = diag.length - 1 := by rw [← hp]; rfl
      subst hp'
      exact spectator.cap_hi _ G F.rho.1 F.rho.2 spSU spSL hseed u hu)
    (fun p hp u hu => by
      have hp' : p = diag.length - 1 := by rw [← hp]; rfl
      subst hp'
      exact spectator.cap_lo _ G F.rho.1 F.rho.2 spSU spSL hseed u hu)
  have hlen : Xs.length = diag.length :=
    (greenprod.qShape_len ht.2.1).trans
      (greenprod.slabShape_len_ns ht.1)
  refine greenprod.revFold_vacant Xs sps 0 hl (fun i hi s hs => ?_)
  have hid : i < diag.length := by rw [← hlen]; exact hi
  have hin : i < ns.length := by
    rw [greenprod.slabShape_len_ns ht.1]; exact hid
  have hXo : sqAt (ground.getAt dM Xs i).1 F.o := by
    have h := greenprod.qShape_at ht.2.1 i hi
    rw [hpt.1 i hin] at h
    exact h
  have hYcq : sqAt (famYc F en ed K (m0 + (diag.length - 1 - i))).1
      F.o :=
    elim.sqAt_of ((length_evalPfm (m0 + (diag.length - 1 - i)) F.Cf.1
        en ed K).trans hCl)
      (rowsLen_evalPfm F.o (m0 + (diag.length - 1 - i)) F.Cf.1
        en ed K hCr)
  have hb := hball i hi
  exact spectator.ball_psd_ptw (ground.getAt dM Xs i)
    (famYc F en ed K (m0 + (diag.length - 1 - i))) G F.y0.1 F.y0.2
    F.rho.1 F.rho.2 s.2 hXo hYcq hGq
    (floorCount_ptw F.Cf G F.o F.y0.1 F.y0.2 F.rho.1 F.rho.2
      F.e0.1 F.e0.2 F.bxF (m0 + (diag.length - 1 - i)) K en ed
      (BPair.marginPos (evalProf F.Cf.2 (m0 + (diag.length - 1 - i))
        en ed K))
      hCl hCr hGq hsymCf hsymG
      (fun a b => hshC (m0 + (diag.length - 1 - i)) a b)
      (hshCl (m0 + (diag.length - 1 - i))) hwF he
      (hpt.2.2.2.2.1 i hid)
      (clTie F.Cf.2 F.e0.1 F.e0.2 F.bxClC (m0 + (diag.length - 1 - i))
        K en ed hbrC he (hpt.2.2.2.2.2.2.2.1 i hid)))
    hb.1 hb.2 hs

/-- The walked segment's boundary key past the withdrawn count: the
trailing segment's last key is the family's own last. -/
private theorem seedIdx : ∀ (L k n : Nat), L + (k + 1) = n →
    k + 1 < n → k + 1 + (L - 1) = n - 1
  | 0, _, _, hL, hlt => by
    rw [← hL, Nat.zero_add] at hlt
    exact absurd hlt (Nat.lt_irrefl _)
  | L' + 1, k, _, hL, _ => by
    rw [← hL]
    show k + 1 + L' = L' + 1 + k
    rw [Nat.add_right_comm k 1 L', Nat.add_right_comm L' 1 k,
      Nat.add_comm k L']

/-- The chain's count closes at the certificate, the center family
its data: the count splits over the depth pivots
(`lem:greenprod`(ii)), the walked segment's stated splits read
vacant at the family's balls from the seed's stated ball at the
boundary block, the crossing's split reads its one lower unit, the
dominance tail's floors read every deeper split vacant, and every
split of the assembled datum reads the count at one. -/
theorem famChainCount {n : Nat} (F : CenterFam) (B G : elim.Mat)
    (en ed : Pos) (K m0 : Nat)
    (spc spT : (k : Nat) × Split k) (tn td : Pos)
    (diag off : List elim.Mat) (ns : List Nat) (Xs Rs : List MatQ)
    (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k))
    (sps : List ((k : Nat) × Split k)) (SP : Split n)
    (spSU spSL : Split F.o)
    (hfam : famRead F B G)
    (he : BPair.ofPos en * BPair.ofPos F.e0.2
      ≤ F.e0.1 * BPair.ofPos ed)
    (hshA : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Af i) j)
        d)).length ≤ K + 1)
    (hshC : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Cf.1 i) j)
        d)).length ≤ K + 1)
    (hshCl : ∀ d, (poly.vnorm (depthPoly F.Cf.2 d)).length ≤ K + 1)
    (hshW : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Wf.1 i) j)
        d)).length ≤ K + 1)
    (hshWcl : ∀ d, (poly.vnorm (depthPoly F.Wf.2 d)).length ≤ K + 1)
    (hshI : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.If.1 i) j)
        d)).length ≤ K + 1)
    (hshIcl : ∀ d, (poly.vnorm (depthPoly F.If.2 d)).length ≤ K + 1)
    (hchain : famChainRead F B en ed K m0 (diag.drop (Ds.length + 1))
      (off.drop (Ds.length + 1)) (ns.drop (Ds.length + 1)))
    (ht : tailRead diag off Xs Rs ns)
    (hl : revListRead Xs sps)
    (hS : splitRead (assemble diag off) SP)
    (hdom : domRead spc spT tn td diag off Xs Rs ns Ds Cs)
    (hone : ∀ d : (k : Nat) × Split k,
      revAt (ground.getAt d sps Ds.length).2 = 1)
    (hsymD : greenprod.symRead (diag.drop (Ds.length + 1)))
    (hseed : spectator.capQ
      (spectator.devQ
        (greenprod.ofM (ground.getAt [] diag (diag.length - 1)))
        (famYc F en ed K m0)) G F.rho.1 F.rho.2 spSU spSL) :
    revAt SP = 1 := by
  have hlen : Ds.length < Xs.length :=
    domLen spc spT tn td diag off Xs Rs ns Ds Cs hdom
  have hc : Ds.length < sps.length := by
    rw [← greenprod.revListRead_length Xs sps hl]
    exact hlen
  have hpsd : ∀ i, i < (Xs.take Ds.length).length →
      ∀ s : (k : Nat) × Split k,
        splitRead (ground.getAt dM (Xs.take Ds.length) i).1 s.2 →
        psdAt s.2 := by
    intro i hi s hs
    rw [ground.length_take Ds.length Xs (Nat.le_of_lt hlen)] at hi
    rw [ground.getAt_take dM Ds.length Xs i hi] at hs
    exact domTail_psd spc spT tn td diag off Xs Rs ns Ds Cs hdom ht i hi
      s hs
  have htake : revFold (sps.take Ds.length) = 0 :=
    greenprod.revFold_vacant (Xs.take Ds.length) (sps.take Ds.length) 0
      (greenprod.revListRead_take Xs sps Ds.length hl) hpsd
  have hXd : Xs.length = diag.length :=
    (greenprod.qShape_len ht.2.1).trans
      (greenprod.slabShape_len_ns ht.1)
  have hdrop : revFold (sps.drop (Ds.length + 1)) = 0 := by
    match Nat.lt_or_ge (Ds.length + 1) diag.length with
    | Or.inl hlt =>
      have hent : ground.getAt ([] : elim.Mat)
          (diag.drop (Ds.length + 1))
          ((diag.drop (Ds.length + 1)).length - 1)
          = ground.getAt [] diag (diag.length - 1) := by
        rw [ground.getAt_drop, seedIdx
          (diag.drop (Ds.length + 1)).length Ds.length diag.length
          (ground.length_drop (Ds.length + 1) diag (Nat.le_of_lt hlt))
          hlt]
      exact famChain_psd F B G en ed K m0 (diag.drop (Ds.length + 1))
        (off.drop (Ds.length + 1)) (Xs.drop (Ds.length + 1))
        (Rs.drop (Ds.length + 1)) (ns.drop (Ds.length + 1))
        (sps.drop (Ds.length + 1)) spSU spSL hfam he
        hshA hshC hshCl hshW hshWcl hshI hshIcl hchain
        (greenprod.tailRead_drop diag off Xs Rs ns (Ds.length + 1)
          hlt ht)
        hsymD (by rw [hent]; exact hseed)
        (greenprod.revListRead_drop Xs sps (Ds.length + 1) hl)
    | Or.inr hge =>
      have hsl : sps.length = diag.length :=
        (greenprod.revListRead_length Xs sps hl).symm.trans hXd
      have heq : sps.length = Ds.length + 1 :=
        Nat.le_antisymm (by rw [hsl]; exact hge) hc
      rw [← heq, ground.dropLength sps]
      rfl
  rw [greenprod.countSplit diag off Xs Rs ns sps SP ht hl hS,
    greenprod.revFold_split sps Ds.length, htake,
    ground.drop_getAt_cons (⟨n, SP⟩ : (k : Nat) × Split k)
      Ds.length sps hc,
    greenprod.revFold_cons, hone ⟨n, SP⟩, hdrop]

/-! The compression lifts: a family read at the compressed datum is
the count's own witness at the full datum, the congruence
transporting every form.  The compression's shape binders (`hPl`,
`hPr`) are the certificate-shape frame at the truncating folds. -/

/-- The compressed cross pairing reads the datum's own at the two
carried vectors, the congruence transporting the pairing. -/
private theorem tiePair {n m : Nat} (S P W : Mat)
    (hS : sqAt S n) (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (x y : List BPair) (hx : x.length = m) (hy : y.length = m) :
    (dotN (matVec P x) (matVec S (matVec P y))).oneValue
      (dotN x (matVec W y)) :=
  BPair.oneValue_trans (dotN_read _ _)
    (BPair.oneValue_trans
      (congrPair S P n m (sqAt_len hS) (rowsLen_of_sqAt hS) hPl hPr
        x y hx hy)
      (BPair.oneValue_trans
        (dotP_oneValue_right x _ _ (matVec_matOne _ _ y htie))
        (BPair.oneValue_symm (dotN_read x (matVec W y)))))

/-- The compressed strict vector occupies the count: a vector whose
form at the compression reads below the sum's unit forces the
reversal count of every split of the datum, the congruence
transporting the form and the forcing clause reading the family. -/
theorem strict_lift {n m : Nat} (S P W : Mat) (sp : Split n)
    (x : List BPair)
    (hsp : splitRead S sp)
    (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (hx : x.length = m)
    (hq : quadForm W x < BPair.unit) :
    1 ≤ revAt sp := by
  refine strictForcing S (matVec P x)
    ((matVec_length P x).trans hPl) ?_ sp hsp
  exact BPair.lt_congr
    (BPair.oneValue_symm (tieQuad S P W hsp.1 hPl hPr htie x hx))
    (BPair.oneValue_refl BPair.unit) hq

/-- The compressed cap pair occupies the count at two: the two
members' reads at the compression — the leading form below the
sum's unit and the doubled cross read below the diagonal product's
quadruple — force the reversal count at two or beyond at every
split of the datum, the congruence transporting the three reads. -/
theorem cap_lift {n m : Nat} (S P W : Mat) (sp : Split n)
    (x x' : List BPair)
    (hsp : splitRead S sp)
    (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (hx : x.length = m) (hx' : x'.length = m)
    (hq : quadForm W x < BPair.unit)
    (hd : (dotN x (matVec W x') + dotN x' (matVec W x))
        * (dotN x (matVec W x') + dotN x' (matVec W x))
      < BPair.ofNat 4 * (quadForm W x * quadForm W x')) :
    2 ≤ revAt sp := by
  have hqx := tieQuad S P W hsp.1 hPl hPr htie x hx
  have hqx' := tieQuad S P W hsp.1 hPl hPr htie x' hx'
  have hc1 := tiePair S P W hsp.1 hPl hPr htie x x' hx hx'
  have hc2 := tiePair S P W hsp.1 hPl hPr htie x' x hx' hx
  refine capForcing S (matVec P x) (matVec P x')
    ((matVec_length P x).trans hPl) ((matVec_length P x').trans hPl)
    (BPair.lt_congr (BPair.oneValue_symm hqx)
      (BPair.oneValue_refl BPair.unit) hq) ?_ sp hsp
  refine BPair.lt_congr
    (BPair.mul_congr
      (BPair.add_congr (BPair.oneValue_symm hc1)
        (BPair.oneValue_symm hc2))
      (BPair.add_congr (BPair.oneValue_symm hc1)
        (BPair.oneValue_symm hc2)))
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 4))
      (BPair.mul_congr (BPair.oneValue_symm hqx)
        (BPair.oneValue_symm hqx')))
    hd

end cornerpivot
