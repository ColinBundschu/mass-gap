import MassGap.Ppolyeval
/-!
`thm:windowsep` — the two-variable fold.  The fold `foldOuterK` is the
outer fold of the coefficients' inner folds at the two bounds and the
two powers, the magnitude carrier at `def:poly`'s polynomials as the
entry carrier, and the two evaluations' folds sit within it at the
points' clearings: the inner evaluation's fold at an inner point
inside the inner bound (`foldK_pevalCP`) and the outer evaluation's
fold at an outer point inside the outer bound (`foldK_pevalOuter`),
each one comparison at the fold's cleared powers.
-/

namespace windowsep
open ground

/-- The two-variable fold at stated bounds and powers: the outer fold
of the coefficients' inner folds, the magnitude carrier at `def:poly`'s
polynomials as the entry carrier, cleared at `dt^Kt ds^Ks`. -/
def foldOuterK (P : poly.PPoly) (nt dt : BPair) (Kt : Nat) (ns ds : BPair)
    (Ks : Nat) : BPair :=
  foldAt (fun k => foldK (ground.getAt [] P k) nt dt Kt) ns ds Ks

/-- The recursion's two summands scaled, regrouped. -/
private theorem rec_scale (x N d F c : BPair) :
    ((x * N + d * F) * c).oneValue (x * c * N + d * (F * c)) :=
  polEqB [x, N, d, F, c]
    (Pol.mul (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 1)))
        (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3)))) (Pol.mon (Mon.var 4)))
    (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 4)) (Mon.var 1)))
      (Pol.mon (Mon.mul (Mon.var 2) (Mon.mul (Mon.var 3) (Mon.var 4)))))
    (by decide +kernel)

/-- The inner evaluation's fold sits within the two-variable fold at
the inner point's clearing: the inner point inside the inner bound,
every coefficient within the inner power. -/
theorem foldK_pevalCP (P : poly.PPoly) (tn : BPair) (tc : Pos) (Kt : Nat)
    {nt dt ns ds : BPair} (hdt : BPair.unit ≤ dt)
    (hns : BPair.unit ≤ ns) (hds : BPair.unit ≤ ds)
    (hin : poly.innerLe P Kt) (ht : mag tn * dt ≤ nt * BPair.ofPos tc) :
    ∀ Ks : Nat,
    foldK (poly.pevalCP P tn tc Kt) ns ds Ks * bpow dt Kt
      ≤ foldOuterK P nt dt Kt ns ds Ks * bpow (BPair.ofPos tc) Kt
  | 0 => by
    refine leB_congr (BPair.oneValue_symm (BPair.mul_congr_left (foldK_zero _ ns ds)))
      (BPair.oneValue_symm (BPair.mul_congr_left (foldAt_zero _ ns ds))) ?_
    show mag (ground.getAt BPair.unit (P.map (fun c => poly.evalClear c tn tc Kt)) 0)
        * bpow dt Kt ≤ _
    rw [getAt_mapT ([] : poly.Poly) BPair.unit _ (poly.evalClear_nil tn tc Kt)]
    exact foldK_cap _ tn tc nt dt Kt hdt (poly.innerLe_getAt hin 0) ht
  | Ks + 1 => by
    have hc : mag (ground.getAt BPair.unit (poly.pevalCP P tn tc Kt) (Ks + 1))
          * bpow dt Kt
        ≤ foldK (ground.getAt [] P (Ks + 1)) nt dt Kt * bpow (BPair.ofPos tc) Kt := by
      show mag (ground.getAt BPair.unit (P.map (fun c => poly.evalClear c tn tc Kt)) (Ks + 1))
        * bpow dt Kt ≤ _
      rw [getAt_mapT ([] : poly.Poly) BPair.unit _ (poly.evalClear_nil tn tc Kt)]
      exact foldK_cap _ tn tc nt dt Kt hdt (poly.innerLe_getAt hin (Ks + 1)) ht
    refine leB_congr (BPair.oneValue_symm (BPair.mul_congr_left (foldK_succ _ ns ds Ks)))
      (BPair.oneValue_symm (BPair.mul_congr_left (foldAt_succ _ ns ds Ks))) ?_
    refine leB_congr (BPair.oneValue_symm (rec_scale _ _ _ _ _))
      (BPair.oneValue_symm (rec_scale _ _ _ _ _)) ?_
    exact leB_add (leB_mulL (unitLeBpow hns (Ks + 1)) hc)
      (leB_mulR hds (foldK_pevalCP P tn tc Kt hdt hns hds hin ht Ks))

/-- A family's sum folds at or below the folds' sum. -/
private theorem foldK_famFold_le (g : Nat → poly.Poly) {n d : BPair}
    (hn : BPair.unit ≤ n) (hd : BPair.unit ≤ d) (K : Nat) : ∀ l : List Nat,
    foldK (ground.famFold poly.add [] g l) n d K
      ≤ ground.famFold BPair.add BPair.unit (fun k => foldK (g k) n d K) l
  | [] => Or.inl (foldK_nil n d K)
  | a :: t => by
    show foldK (poly.add (g a) (ground.famFold poly.add [] g t)) n d K
      ≤ foldK (g a) n d K + ground.famFold BPair.add BPair.unit (fun k => foldK (g k) n d K) t
    exact leB_trans (foldK_add_le _ _ hn hd K)
      (leB_add (leB_refl _) (foldK_famFold_le g hn hd K t))

/-- The outer term's magnitude at the point's clearing, regrouped at
the bound's monomial. -/
private theorem outerL_shuffle (C M F dk dg : BPair) :
    (C * M * F * (dk * dg)).oneValue (F * C * dg * (M * dk)) :=
  polEqB [C, M, F, dk, dg]
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
      (Mon.mul (Mon.var 3) (Mon.var 4))))
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 0)) (Mon.var 4))
      (Mon.mul (Mon.var 1) (Mon.var 3))))
    (by decide +kernel)

/-- The outer term on the bound's side, regrouped. -/
private theorem outerR_shuffle (F nk dg ck C : BPair) :
    (F * nk * dg * (ck * C)).oneValue (F * C * dg * (nk * ck)) :=
  polEqB [F, nk, dg, ck, C]
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
      (Mon.mul (Mon.var 3) (Mon.var 4))))
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 4)) (Mon.var 2))
      (Mon.mul (Mon.var 1) (Mon.var 3))))
    (by decide +kernel)

/-- One outer term: the scale's magnitude against a coefficient's
fold at the outer clearing power sits at or below the fold at the
bound's monomial at the point's clearing power. -/
private theorem outer_term (F : BPair) (sn : BPair) (sc : Pos) (ns ds : BPair)
    (Ks k : Nat) (hF : BPair.unit ≤ F) (hds : BPair.unit ≤ ds)
    (hs : mag sn * ds ≤ ns * BPair.ofPos sc) (hk : k ≤ Ks) :
    mag (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k) * F * bpow ds Ks
      ≤ F * bpow ns k * bpow ds (Ks - k) * bpow (BPair.ofPos sc) Ks := by
  have hcU : BPair.unit ≤ BPair.ofPos sc := leB_of_lt (unitLtOfPos sc)
  have hsplit : k + (Ks - k) = Ks := natAddSubCancel hk
  have hdK : (bpow ds Ks).oneValue (bpow ds k * bpow ds (Ks - k)) := by
    have h := bpow_add ds k (Ks - k)
    rw [hsplit] at h
    exact h
  have hcK : (bpow (BPair.ofPos sc) Ks).oneValue
      (bpow (BPair.ofPos sc) k * bpow (BPair.ofPos sc) (Ks - k)) := by
    have h := bpow_add (BPair.ofPos sc) k (Ks - k)
    rw [hsplit] at h
    exact h
  have hmag : (mag (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)).oneValue
      (bpow (BPair.ofPos sc) (Ks - k) * bpow (mag sn) k) :=
    BPair.oneValue_trans (mag_mul _ _)
      (BPair.mul_congr (BPair.oneValue_of_eq (mag_unitLe (unitLeBpow hcU (Ks - k))))
        (mag_bpow sn k))
  have hpow : bpow (mag sn) k * bpow ds k ≤ bpow ns k * bpow (BPair.ofPos sc) k :=
    leB_congr (bpow_mul (mag sn) ds k) (bpow_mul ns (BPair.ofPos sc) k)
      (bpow_mono (unitLeMul (unitLe_mag sn) hds) hs k)
  have hL : (mag (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k) * F * bpow ds Ks).oneValue
      (F * bpow (BPair.ofPos sc) (Ks - k) * bpow ds (Ks - k)
        * (bpow (mag sn) k * bpow ds k)) :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr_left hmag) hdK)
      (outerL_shuffle (bpow (BPair.ofPos sc) (Ks - k)) (bpow (mag sn) k) F
        (bpow ds k) (bpow ds (Ks - k)))
  have hR : (F * bpow ns k * bpow ds (Ks - k) * bpow (BPair.ofPos sc) Ks).oneValue
      (F * bpow (BPair.ofPos sc) (Ks - k) * bpow ds (Ks - k)
        * (bpow ns k * bpow (BPair.ofPos sc) k)) :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hcK)
      (outerR_shuffle F (bpow ns k) (bpow ds (Ks - k)) (bpow (BPair.ofPos sc) k)
        (bpow (BPair.ofPos sc) (Ks - k)))
  exact leB_congr (BPair.oneValue_symm hL) (BPair.oneValue_symm hR)
    (leB_mulR (unitLeMul (unitLeMul hF (unitLeBpow hcU (Ks - k))) (unitLeBpow hds (Ks - k)))
      hpow)

/-- The outer evaluation's fold sits within the two-variable fold at
the outer point's clearing: the outer point inside the outer bound,
the outer top within the outer power. -/
theorem foldK_pevalOuter (P : poly.PPoly) (sn : BPair) (sc : Pos) (Ks : Nat)
    {nt dt ns ds : BPair} (Kt : Nat)
    (hnt : BPair.unit ≤ nt) (hdt : BPair.unit ≤ dt) (hds : BPair.unit ≤ ds)
    (hP : P.length ≤ Ks + 1) (hs : mag sn * ds ≤ ns * BPair.ofPos sc) :
    foldK (poly.pevalOuter P sn sc Ks) nt dt Kt * bpow ds Ks
      ≤ foldOuterK P nt dt Kt ns ds Ks * bpow (BPair.ofPos sc) Ks := by
  refine leB_trans (leB_mulL (unitLeBpow hds Ks)
    (foldK_famFold_le _ hnt hdt Kt (List.range P.length))) ?_
  have hsc : (ground.famFold BPair.add BPair.unit
      (fun k => foldK (poly.scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
        (ground.getAt [] P k)) nt dt Kt) (List.range P.length)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => mag (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
          * foldK (ground.getAt [] P k) nt dt Kt) (List.range (Ks + 1))) := by
    refine BPair.oneValue_trans
      (ground.famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
        BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) _ _
        (List.range P.length) (fun k _ => foldK_scaleP _ _ nt dt Kt)) ?_
    refine BPair.oneValue_symm (foldRange_le _ P.length (Ks + 1) hP (fun j hj => ?_))
    rw [getAt_over ([] : poly.Poly) P j hj]
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (foldK_nil nt dt Kt))
      (BPair.mul_unit _)
  refine leB_congr (BPair.oneValue_symm (BPair.oneValue_trans (BPair.mul_congr_left hsc)
      (foldB_mul_right _ _ _)))
    (BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.mul_congr_left (foldAt_read _ ns ds Ks)) (foldB_mul_right _ _ _))) ?_
  refine leB_famFold_range (List.range (Ks + 1)) (fun k hk => ?_)
  exact outer_term _ sn sc ns ds Ks k (unitLe_foldK _ hnt hdt Kt) hds hs
    (Nat.le_of_lt_succ (ground.ltOfCountRange hk))

end windowsep
