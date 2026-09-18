import MassGap.Stage
import MassGap.Ppolyfold
/-!
`lem:stage` — the priced side read on a box.  A polynomial in two
variables over the stage, the inner variable's polynomials the outer
variable's coefficients (`poly.PPoly`, `def:poly`'s polynomials as
the entry carrier), keeps its side at every point of a box, one
bracket per variable inside its own bound, where two priced reads
hold: the inner variable's read above at the corner's outer point,
and the outer variable's read at every inner point at once.  The
read (`keepUpperBox`, `keepLowerBox` its memberwise swap) states the
two bounds' clearings above the sum's unit, the two ordered
brackets inside their bounds, and the one priced comparison: the
outer derivative's coefficient fold at the outer bound, each
coefficient read at its own fold at the inner bound, against the
outer width, joined to the inner derivative's fold at the two bounds
against the inner width, clears the corner value.  The folds are
`windowsep.foldOuterK` at the polynomial's own two tops, the inner
top the largest coefficient's (`poly.innerTop`) and the outer top
the key count's predecessor (`outerTop`), the corner value the inner
evaluation at the corner's inner point (`innerC`, `poly.pevalCP` at
the composite point at the inner top) read at the corner's outer
point, and every pair enters at its representative's clearing
(`denC` the inner point's clearing power), the comparison one value
across the representatives by the homogeneity principle.  The
theorem (`keepUpperBox_all`, `keepLowerBox_all`) is the tex's
derivation: at every inner point the outer read's endpoint value
sits within the inner price of the corner value, the inner read
along the inner bracket at the corner's outer value against the
outer evaluation's image width (`evalC_gap_le` at the outer
evaluation, `foldK_pevalOuter` the fold's cap, `pevalOuter_pevalCP`
the two evaluations' meet at the shared points), so the outer read
holds there (`keepUpper` at that inner point's coefficients,
`foldK_pevalCP` the outer fold's cap) and the side follows along
the outer bracket (`keepUpper_all`).
-/

namespace stage
open ground poly windowsep

/-- The inner evaluation at a composite inner point, cleared at the
point's second datum's power at the inner top: the coefficients'
cleared reads there, a polynomial in the outer variable. -/
def innerC (p : PPoly) : CPair → Poly
  | ⟨tn, tc⟩ => pevalCP p tn tc (innerTop p)

/-- A composite point's second datum at a stated power, the
clearing the inner evaluation enters at. -/
def denC : CPair → Nat → CPair
  | ⟨_, tc⟩, K => ofB (BPair.ofPos (Pos.pow tc K))

/-- The outer top, the key count's predecessor. -/
def outerTop (p : PPoly) : Nat := p.length - 1

/-- The inner evaluation at a stated representative. -/
theorem innerC_mk (p : PPoly) (tn : BPair) (tc : Pos) :
    innerC p ⟨tn, tc⟩ = pevalCP p tn tc (innerTop p) := rfl

/-- The clearing power at a stated representative. -/
theorem denC_mk (tn : BPair) (tc : Pos) (K : Nat) :
    denC ⟨tn, tc⟩ K = ofB (BPair.ofPos (Pos.pow tc K)) := rfl

/-- The priced side read on a box: the two bounds' clearings above
the sum's unit, the two ordered brackets inside their bounds
(`lem:stage`'s one bracket per variable inside its own bound, a
bracket's endpoints ordered at the width's gap), and
the corner value clearing the outer fold against the outer width
joined to the inner fold against the inner width, at the corner's
inner clearing against the two bounds' clearing powers at the two
tops. -/
def keepUpperBox (p : PPoly) (t0 t1 s0 s1 : CPair) (Nt Dt Ns Ds : BPair) : Prop :=
  BPair.unit < Dt ∧ t0 < t1
  ∧ cmag t0 * ofB Dt ≤ ofB Nt ∧ cmag t1 * ofB Dt ≤ ofB Nt
  ∧ BPair.unit < Ds ∧ s0 < s1
  ∧ cmag s0 * ofB Ds ≤ ofB Ns ∧ cmag s1 * ofB Ds ≤ ofB Ns
  ∧ (ofB (foldOuterK (derivOuter p) Nt Dt (innerTop p) Ns Ds (outerTop p))
        * (s1 + CPair.swap s0)
      + ofB (foldOuterK (derivInner p) Nt Dt (innerTop p) Ns Ds (outerTop p))
        * (t1 + CPair.swap t0))
      * denC t0 (innerTop p)
    < evalC (innerC p t0) s0 * ofB (bpow Dt (innerTop p) * bpow Ds (outerTop p))

instance instStagebox1 (p : PPoly) (t0 t1 s0 s1 : CPair) (Nt Dt Ns Ds : BPair) :
    Decidable (keepUpperBox p t0 t1 s0 s1 Nt Dt Ns Ds) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The lower side's priced read on a box, the memberwise swap's. -/
def keepLowerBox (p : PPoly) (t0 t1 s0 s1 : CPair) (Nt Dt Ns Ds : BPair) : Prop :=
  BPair.unit < Dt ∧ t0 < t1
  ∧ cmag t0 * ofB Dt ≤ ofB Nt ∧ cmag t1 * ofB Dt ≤ ofB Nt
  ∧ BPair.unit < Ds ∧ s0 < s1
  ∧ cmag s0 * ofB Ds ≤ ofB Ns ∧ cmag s1 * ofB Ds ≤ ofB Ns
  ∧ (ofB (foldOuterK (derivOuter p) Nt Dt (innerTop p) Ns Ds (outerTop p))
        * (s1 + CPair.swap s0)
      + ofB (foldOuterK (derivInner p) Nt Dt (innerTop p) Ns Ds (outerTop p))
        * (t1 + CPair.swap t0))
      * denC t0 (innerTop p)
    < CPair.swap (evalC (innerC p t0) s0)
      * ofB (bpow Dt (innerTop p) * bpow Ds (outerTop p))

instance instStagebox2 (p : PPoly) (t0 t1 s0 s1 : CPair) (Nt Dt Ns Ds : BPair) :
    Decidable (keepLowerBox p t0 t1 s0 s1 Nt Dt Ns Ds) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! The composite order kit the box read reads: the one-key entry's
at-or-below read, the composite unit strictly under a one-key entry,
a member under a second joined to their difference's magnitude, the
strict read's right factor, and the magnitude at the memberwise
swap. -/

/-- The one-key entry keeps the at-or-below read. -/
theorem ofB_le {x y : BPair} (h : x ≤ y) : ofB x ≤ ofB y := by
  show x.scale Pos.one ≤ y.scale Pos.one
  rw [BPair.scale_one, BPair.scale_one]
  exact h

/-- The composite unit sits strictly under a one-key entry strictly
above the sum's unit. -/
theorem unitC_lt_ofB {x : BPair} (h : BPair.unit < x) : unitC < ofB x :=
  (unitC_lt_num x Pos.one).mpr h

/-- A member sits at or below a second joined to their difference's
magnitude. -/
theorem le_add_cmag (x y : CPair) : y ≤ x + cmag (x + CPair.swap y) := by
  have h1 : CPair.swap (cmag (x + CPair.swap y)) ≤ x + CPair.swap y :=
    swap_cmag_le _
  have h2 : y + (CPair.swap (cmag (x + CPair.swap y)) + cmag (x + CPair.swap y))
      ≤ y + (x + CPair.swap y + cmag (x + CPair.swap y)) :=
    CPair.le_add (CPair.le_refl y) (CPair.le_add h1 (CPair.le_refl _))
  have e0 : (CPair.swap (cmag (x + CPair.swap y))
      + cmag (x + CPair.swap y)).oneValue unitC := by
    rw [CPair.add_comm]
    exact addC_swap_unit _
  have e1 : (y + (CPair.swap (cmag (x + CPair.swap y))
      + cmag (x + CPair.swap y))).oneValue y :=
    CPair.oneValue_trans (CPair.add_congr (CPair.oneValue_refl y) e0)
      (by rw [CPair.add_comm]; exact addC_unitC y)
  have e2 : (y + (x + CPair.swap y + cmag (x + CPair.swap y))).oneValue
      (x + cmag (x + CPair.swap y)) := by
    rw [CPair.add_assoc x (CPair.swap y) (cmag (x + CPair.swap y)),
      CPair.add_comm (CPair.swap y) (cmag (x + CPair.swap y)),
      ← CPair.add_assoc x (cmag (x + CPair.swap y)) (CPair.swap y),
      CPair.add_comm y (x + cmag (x + CPair.swap y) + CPair.swap y),
      CPair.add_assoc (x + cmag (x + CPair.swap y)) (CPair.swap y) y,
      CPair.add_comm (CPair.swap y) y]
    exact CPair.add_swap_unit y (x + cmag (x + CPair.swap y))
  exact CPair.le_congr e1 e2 h2

/-- The strict composite read keeps at a right factor strictly above
the composite unit. -/
theorem ltC_mul_right : ∀ {x y z : CPair}, x < y → unitC < z → x * z < y * z
  | ⟨xn, xc⟩, ⟨yn, yc⟩, ⟨zn, zc⟩, h, hz => by
    have h0 : xn.scale yc < yn.scale xc := h
    have hz0 : BPair.unit < zn := (unitC_lt_num zn zc).mp hz
    show (xn * zn).scale (yc * zc) < (yn * zn).scale (xc * zc)
    rw [BPair.scale_mul xn zn yc zc, BPair.scale_mul yn zn xc zc]
    refine ground.ltB_mulPos h0 ?_
    exact BPair.lt_congr
      (BPair.oneValue_of_eqMem
        (rfl : (BPair.unit.scale zc).fst = (BPair.unit.scale zc).snd))
      (BPair.oneValue_refl _) (BPair.scale_lt zc hz0)

/-- The composite magnitude is blind to the memberwise swap. -/
theorem cmag_swap : ∀ x : CPair, (cmag (CPair.swap x)).oneValue (cmag x)
  | ⟨n, d⟩ => by
    refine CPair.oneValue_trans (cmag_num n.swap d) ?_
    rw [mag_swap n]
    exact CPair.oneValue_symm (cmag_num n d)

/-! The inner leg: one variable's image width over its bracket,
cleared at the stated power and a further factor, sits within the
derivative's fold at that power against the width; the composite
bound at a stated representative reads the magnitude carrier's own;
and a value at two clearings reads one one-key entry. -/

/-- The composite bound at a stated representative is the magnitude
carrier's own read. -/
private theorem magBound_num (xn : BPair) (xc : Pos) (N D : BPair)
    (h : cmag (⟨xn, xc⟩ : CPair) * ofB D ≤ ofB N) :
    mag xn * D ≤ N * BPair.ofPos xc := by
  have e1 : (cmag (⟨xn, xc⟩ : CPair) * ofB D).oneValue
      ((⟨mag xn, xc⟩ : CPair) * ofB D) :=
    CPair.mul_congr (cmag_num xn xc) (CPair.oneValue_refl (ofB D))
  have h1 : (⟨mag xn, xc⟩ : CPair) * ofB D ≤ ofB N :=
    CPair.le_congr e1 (CPair.oneValue_refl _) h
  have h2 : (mag xn * D).scale Pos.one ≤ N.scale (xc * Pos.one) := h1
  rw [BPair.scale_one, ground.mul_one xc] at h2
  refine leB_congr_right ?_ h2
  exact BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofPos_scale xc N))
    (BPair.oneValue_of_eq (BPair.mul_comm _ _))

/-- One leg: the image width over a bracket at a stated power and a
further factor. -/
private theorem leg_fold (q : Poly) (a b z : CPair) (N D : BPair)
    (hD : BPair.unit < D)
    (ha : cmag a * ofB D ≤ ofB N) (hb : cmag b * ofB D ≤ ofB N)
    (haz : a ≤ z) (hzb : z ≤ b) (K : Nat) (hq : q.length ≤ K + 1)
    (X : BPair) (hX : BPair.unit ≤ X) :
    cmag (evalC q z + CPair.swap (evalC q a)) * ofB (bpow D K * X)
      ≤ ofB (foldK (deriv q) N D K * X) * (b + CPair.swap a) := by
  have hgap := evalC_gap_le q a b z N D (leB_of_lt hD) ha hb haz hzb
  have hL : (vnorm (deriv q)).length - 1 ≤ K :=
    Nat.pred_le_pred (Nat.le_trans (vnormDeriv_le q) hq)
  obtain ⟨g, hg⟩ := Nat.le.dest hL
  have hbr := foldK_magFold (deriv q) N D g
  rw [hg] at hbr
  have hpos : unitC ≤ ofB (bpow D g * X) :=
    unitC_le_num _ (unitLeMul (unitLeBpow (leB_of_lt hD) g) hX)
  have h2 := mulC_le_right hpos hgap
  refine CPair.le_congr ?_ ?_ h2
  · rw [CPair.mul_assoc]
    refine CPair.mul_congr (CPair.oneValue_refl _) ?_
    refine CPair.oneValue_trans (CPair.oneValue_symm (ofB_mul _ _)) ?_
    refine CPair.num_oneValue ?_ Pos.one
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    refine BPair.mul_congr_left ?_
    rw [← hg]
    exact BPair.oneValue_symm (bpow_add D _ g)
  · rw [CPair.mul_comm (ofB (magFold (deriv q) N D)) (b + CPair.swap a),
      CPair.mul_assoc,
      CPair.mul_comm (b + CPair.swap a) (ofB _ * ofB _)]
    refine CPair.mul_congr ?_ (CPair.oneValue_refl _)
    refine CPair.oneValue_trans (CPair.oneValue_symm (ofB_mul _ _)) ?_
    refine CPair.num_oneValue ?_ Pos.one
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    refine BPair.mul_congr_left ?_
    exact BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.oneValue_symm hbr)

/-- A value at its own clearing reads the one-key entry. -/
private theorem clearOne (X : BPair) (a : Pos) :
    ((⟨X, a⟩ : CPair) * ofB (BPair.ofPos a)).oneValue (ofB X) := by
  show CPair.oneValue ⟨X * BPair.ofPos a, a * Pos.one⟩ ⟨X, Pos.one⟩
  refine CPair.oneValue_trans
    (CPair.num_oneValue (BPair.mul_ofPos X a) (a * Pos.one)) ?_
  rw [ground.mul_one a]
  have h := CPair.scale_oneValue X Pos.one a
  rw [ground.one_mul a] at h
  exact h

/-- The outer evaluation at an inner point reads the inner evaluation
at the outer point, at the inner point's clearing. -/
private theorem outerRead (p : PPoly) (sn : BPair) (sc : Pos) (Ks Kt : Nat)
    (hin : innerLe p Kt) (tn : BPair) (tc : Pos) :
    (evalC (pevalOuter p sn sc Ks) ⟨tn, tc⟩).oneValue
      ⟨evalClear (pevalCP p tn tc Kt) sn sc Ks, Pos.pow tc Kt⟩ := by
  refine CPair.oneValue_trans
    (evalC_read (pevalOuter p sn sc Ks) Kt (length_pevalOuter_le hin sn sc Ks) tn tc) ?_
  refine CPair.num_oneValue ?_ _
  refine BPair.oneValue_trans (eval_clearVar _ tc Kt tn) ?_
  exact pevalOuter_pevalCP p sn sc Ks tn tc Kt

/-- The inner evaluation's read at an outer point, cleared at the
outer point's power. -/
private theorem innerRead (p : PPoly) (tn : BPair) (tc : Pos) (Kt Ks : Nat)
    (hlen : p.length ≤ Ks + 1) (sn : BPair) (sc : Pos) :
    (evalC (pevalCP p tn tc Kt) ⟨sn, sc⟩).oneValue
      ⟨evalClear (pevalCP p tn tc Kt) sn sc Ks, Pos.pow sc Ks⟩ := by
  refine CPair.oneValue_trans
    (evalC_read (pevalCP p tn tc Kt) Ks
      (by rw [length_pevalCP]; exact hlen) sn sc) ?_
  exact CPair.num_oneValue (eval_clearVar _ sc Ks sn) _

/-- The two evaluations at a shared point read one value at their
clearings. -/
private theorem cross_read (p : PPoly) (tn : BPair) (tc : Pos) (Kt Ks : Nat)
    (hin : innerLe p Kt) (hlen : p.length ≤ Ks + 1) (sn : BPair) (sc : Pos) :
    (evalC (pevalOuter p sn sc Ks) ⟨tn, tc⟩
        * ofB (BPair.ofPos (Pos.pow tc Kt))).oneValue
      (evalC (pevalCP p tn tc Kt) ⟨sn, sc⟩
        * ofB (BPair.ofPos (Pos.pow sc Ks))) := by
  refine CPair.oneValue_trans
    (CPair.mul_congr (outerRead p sn sc Ks Kt hin tn tc) (CPair.oneValue_refl _)) ?_
  refine CPair.oneValue_trans (clearOne _ _) ?_
  refine CPair.oneValue_symm ?_
  refine CPair.oneValue_trans
    (CPair.mul_congr (innerRead p tn tc Kt Ks hlen sn sc) (CPair.oneValue_refl _)) ?_
  exact clearOne _ _

/-- The inner leg at a box point: the outer evaluation's image width
along the inner bracket at the corner's outer value within the inner
fold, and the two evaluations' meets at the point and at the
corner. -/
private theorem box_legs (p : PPoly) (t0n : BPair) (t0c : Pos) (t1 : CPair)
    (s0n : BPair) (s0c : Pos) (Nt Dt Ns Ds : BPair)
    (hDt : BPair.unit < Dt)
    (hqt0 : cmag (⟨t0n, t0c⟩ : CPair) * ofB Dt ≤ ofB Nt)
    (hqt1 : cmag t1 * ofB Dt ≤ ofB Nt)
    (hDs : BPair.unit < Ds)
    (hqs0 : cmag (⟨s0n, s0c⟩ : CPair) * ofB Ds ≤ ofB Ns)
    (tn : BPair) (tc : Pos)
    (ht0 : (⟨t0n, t0c⟩ : CPair) ≤ ⟨tn, tc⟩) (ht1 : (⟨tn, tc⟩ : CPair) ≤ t1) :
    cmag (evalC (pevalOuter p s0n s0c (outerTop p)) ⟨tn, tc⟩
          + CPair.swap (evalC (pevalOuter p s0n s0c (outerTop p)) ⟨t0n, t0c⟩))
        * ofB (bpow Dt (innerTop p) * bpow Ds (outerTop p))
      ≤ ofB (foldOuterK (derivInner p) Nt Dt (innerTop p) Ns Ds (outerTop p))
          * ofB (BPair.ofPos (Pos.pow s0c (outerTop p))) * (t1 + CPair.swap ⟨t0n, t0c⟩)
    ∧ (evalC (pevalOuter p s0n s0c (outerTop p)) ⟨tn, tc⟩
          * ofB (BPair.ofPos (Pos.pow tc (innerTop p)))).oneValue
        (evalC (pevalCP p tn tc (innerTop p)) ⟨s0n, s0c⟩
          * ofB (BPair.ofPos (Pos.pow s0c (outerTop p))))
    ∧ (evalC (pevalOuter p s0n s0c (outerTop p)) ⟨t0n, t0c⟩
          * ofB (BPair.ofPos (Pos.pow t0c (innerTop p)))).oneValue
        (evalC (pevalCP p t0n t0c (innerTop p)) ⟨s0n, s0c⟩
          * ofB (BPair.ofPos (Pos.pow s0c (outerTop p)))) := by
  have hin : innerLe p (innerTop p) := innerLe_innerTop p
  have hlen : p.length ≤ outerTop p + 1 := ground.lePredSucc p.length
  have hDt' : BPair.unit ≤ Dt := leB_of_lt hDt
  have hDs' : BPair.unit ≤ Ds := leB_of_lt hDs
  have hNt : BPair.unit ≤ Nt :=
    unitC_le_fst (CPair.le_trans
      (unitC_le_mul (unitC_le_cmag _) (unitC_le_num _ hDt')) hqt0)
  have hwt : unitC ≤ t1 + CPair.swap ⟨t0n, t0c⟩ :=
    CPair.le_congr (addC_swap_unit _) (CPair.oneValue_refl _)
      (CPair.le_add (CPair.le_trans ht0 ht1) (CPair.le_refl _))
  refine And.intro ?_ (And.intro ?_ ?_)
  · have hleg := leg_fold (pevalOuter p s0n s0c (outerTop p)) ⟨t0n, t0c⟩ t1
      ⟨tn, tc⟩ Nt Dt hDt hqt0 hqt1 ht0 ht1 (innerTop p)
      (length_pevalOuter_le hin s0n s0c (outerTop p))
      (bpow Ds (outerTop p)) (unitLeBpow hDs' (outerTop p))
    have hF : foldK (deriv (pevalOuter p s0n s0c (outerTop p))) Nt Dt (innerTop p)
          * bpow Ds (outerTop p)
        ≤ foldOuterK (derivInner p) Nt Dt (innerTop p) Ns Ds (outerTop p)
          * bpow (BPair.ofPos s0c) (outerTop p) :=
      leB_congr_left
        (BPair.mul_congr_left
          (foldK_congr (pevalOuter_derivInner p s0n s0c (outerTop p)) Nt Dt _))
        (foldK_pevalOuter (derivInner p) s0n s0c (outerTop p) (innerTop p) hNt hDt' hDs'
          (by rw [length_derivInner]; exact hlen)
          (magBound_num s0n s0c Ns Ds hqs0))
    refine CPair.le_congr (CPair.oneValue_refl _) ?_
      (CPair.le_trans hleg (mulC_le_right hwt (ofB_le hF)))
    refine CPair.mul_congr ?_ (CPair.oneValue_refl _)
    refine CPair.oneValue_trans (ofB_mul _ _) ?_
    exact CPair.mul_congr (CPair.oneValue_refl _)
      (CPair.num_oneValue (BPair.oneValue_symm (ofPos_pow s0c _)) _)
  · exact cross_read p tn tc (innerTop p) (outerTop p) hin hlen s0n s0c
  · exact cross_read p t0n t0c (innerTop p) (outerTop p) hin hlen s0n s0c

/-- The corner's clearance reaches the inner point: the corner value
less the inner width's price, moved along the inner bracket at
the outer evaluation and read back at the inner evaluation through
the two meets, clears the outer fold's priced width there. -/
private theorem cornerToInner (B A A0 C Tc T0 S0 Zc Fs Ft ws wt : CPair)
    (hTc : unitC < Tc) (hT0 : unitC ≤ T0) (hS0 : unitC < S0) (hZc : unitC ≤ Zc)
    (hII : cmag (A + CPair.swap A0) * Zc ≤ Ft * S0 * wt)
    (hIII : (A * Tc).oneValue (B * S0))
    (hIV : (A0 * T0).oneValue (C * S0))
    (hV : (Fs * ws + Ft * wt) * T0 < C * Zc) : Fs * Tc * ws < B * Zc := by
  have hS0Tc : unitC < S0 * Tc := unitC_lt_mul hS0 hTc
  have hS0T0 : unitC ≤ S0 * T0 := unitC_le_mul (Or.inr hS0) hT0
  have hT0Tc : unitC ≤ T0 * Tc := unitC_le_mul hT0 (Or.inr hTc)
  have hZcTc : unitC ≤ Zc * Tc := unitC_le_mul hZc (Or.inr hTc)
  have h1 : (Fs * ws + Ft * wt) * T0 * (S0 * Tc) < C * Zc * (S0 * Tc) :=
    ltC_mul_right hV hS0Tc
  have h2 : (C * Zc * (S0 * Tc)).oneValue (A0 * T0 * (Zc * Tc)) := by
    rw [CPair.mul_mul_mul_comm C Zc S0 Tc]
    exact CPair.mul_congr (CPair.oneValue_symm hIV) (CPair.oneValue_refl _)
  have h3 : A0 * T0 * (Zc * Tc) ≤ (A + cmag (A + CPair.swap A0)) * T0 * (Zc * Tc) :=
    mulC_le_right hZcTc (mulC_le_right hT0 (le_add_cmag A A0))
  have h4 : ((A + cmag (A + CPair.swap A0)) * T0 * (Zc * Tc)).oneValue
      (A * T0 * (Zc * Tc) + cmag (A + CPair.swap A0) * T0 * (Zc * Tc)) :=
    CPair.oneValue_trans
      (CPair.mul_congr (CPair.add_mul A _ T0) (CPair.oneValue_refl _))
      (CPair.add_mul _ _ _)
  have h5 : (A * T0 * (Zc * Tc)).oneValue (B * S0 * (T0 * Zc)) := by
    rw [CPair.mul_comm Zc Tc, CPair.mul_mul_mul_comm A T0 Tc Zc]
    exact CPair.mul_congr hIII (CPair.oneValue_refl _)
  have h6 : cmag (A + CPair.swap A0) * T0 * (Zc * Tc)
      ≤ Ft * S0 * wt * (T0 * Tc) := by
    rw [CPair.mul_mul_mul_comm _ T0 Zc Tc]
    exact mulC_le_right hT0Tc hII
  have hR : C * Zc * (S0 * Tc) ≤ B * S0 * (T0 * Zc) + Ft * S0 * wt * (T0 * Tc) :=
    CPair.le_trans
      (CPair.le_congr (CPair.oneValue_symm h2) h4 h3)
      (CPair.le_add (Or.inl h5) h6)
  have hfin : (Fs * ws + Ft * wt) * T0 * (S0 * Tc)
      < B * S0 * (T0 * Zc) + Ft * S0 * wt * (T0 * Tc) :=
    ltC_le_trans h1 hR
  have hdist : ((Fs * ws + Ft * wt) * T0 * (S0 * Tc)).oneValue
      (Fs * ws * T0 * (S0 * Tc) + Ft * S0 * wt * (T0 * Tc)) := by
    refine CPair.oneValue_trans
      (CPair.mul_congr (CPair.add_mul _ _ T0) (CPair.oneValue_refl _)) ?_
    refine CPair.oneValue_trans (CPair.add_mul _ _ _) ?_
    rw [CPair.mul_assoc Ft wt T0, CPair.mul_mul_mul_comm Ft (wt * T0) S0 Tc,
      CPair.mul_assoc wt T0 Tc, ← CPair.mul_assoc (Ft * S0) wt (T0 * Tc)]
    exact CPair.oneValue_refl _
  have hlt : Fs * ws * T0 * (S0 * Tc) < B * S0 * (T0 * Zc) :=
    CPair.lt_of_add_lt_add_right
      (CPair.lt_congr hdist (CPair.oneValue_refl _) hfin)
  have eL : Fs * ws * T0 * (S0 * Tc) = S0 * T0 * (Fs * Tc * ws) := by
    rw [CPair.mul_mul_mul_comm (Fs * ws) T0 S0 Tc, CPair.mul_comm (Fs * ws) S0,
      CPair.mul_mul_mul_comm S0 (Fs * ws) T0 Tc, CPair.mul_assoc Fs ws Tc,
      CPair.mul_comm ws Tc, ← CPair.mul_assoc Fs Tc ws]
  have eR : B * S0 * (T0 * Zc) = S0 * T0 * (B * Zc) := by
    rw [CPair.mul_comm B S0, CPair.mul_assoc S0 B (T0 * Zc),
      CPair.mul_comm B (T0 * Zc), ← CPair.mul_assoc S0 (T0 * Zc) B,
      ← CPair.mul_assoc S0 T0 Zc, CPair.mul_assoc (S0 * T0) Zc B,
      CPair.mul_comm Zc B]
  rw [eL, eR] at hlt
  exact ltC_unscale_left hS0T0 hlt

/-- The outer read's price at an inner point: the outer fold's priced
width, cleared at the inner point's power and the inner bound's,
under the inner evaluation's value at the corner's outer point reads
the segment read's own price at the derivative's top. -/
private theorem innerPrice (q : Poly) (Ks : Nat) (hq : q.length ≤ Ks + 1)
    (Ns Ds Dt : BPair) (Kt : Nat) (hDs : BPair.unit < Ds) (hDt : BPair.unit ≤ Dt)
    (tc : Pos) (F : BPair) (B ws : CPair) (hws : unitC ≤ ws)
    (hF : foldK (deriv q) Ns Ds Ks * bpow Dt Kt ≤ F * bpow (BPair.ofPos tc) Kt)
    (hmain : ofB F * ofB (BPair.ofPos (Pos.pow tc Kt)) * ws
      < B * ofB (bpow Dt Kt * bpow Ds Ks)) :
    ofB (magFold (deriv q) Ns Ds) * ws
      < B * ofB (bpow Ds ((vnorm (deriv q)).length - 1)) := by
  have e0 : (ofB (F * bpow (BPair.ofPos tc) Kt)).oneValue
      (ofB F * ofB (BPair.ofPos (Pos.pow tc Kt))) :=
    CPair.oneValue_trans (ofB_mul _ _)
      (CPair.mul_congr (CPair.oneValue_refl _)
        (CPair.num_oneValue (BPair.oneValue_symm (ofPos_pow tc Kt)) _))
  have h1 : ofB (foldK (deriv q) Ns Ds Ks * bpow Dt Kt) * ws
      ≤ ofB F * ofB (BPair.ofPos (Pos.pow tc Kt)) * ws :=
    CPair.le_congr (CPair.oneValue_refl _)
      (CPair.mul_congr e0 (CPair.oneValue_refl _))
      (mulC_le_right hws (ofB_le hF))
  have h2 : ofB (foldK (deriv q) Ns Ds Ks * bpow Dt Kt) * ws
      < B * ofB (bpow Dt Kt * bpow Ds Ks) := leC_lt_trans h1 hmain
  have eL : (ofB (foldK (deriv q) Ns Ds Ks * bpow Dt Kt) * ws).oneValue
      (ofB (bpow Dt Kt) * (ofB (foldK (deriv q) Ns Ds Ks) * ws)) := by
    refine CPair.oneValue_trans
      (CPair.mul_congr (ofB_mul _ _) (CPair.oneValue_refl _)) ?_
    rw [CPair.mul_comm (ofB (foldK (deriv q) Ns Ds Ks)) (ofB (bpow Dt Kt)),
      CPair.mul_assoc]
    exact CPair.oneValue_refl _
  have eR : (B * ofB (bpow Dt Kt * bpow Ds Ks)).oneValue
      (ofB (bpow Dt Kt) * (B * ofB (bpow Ds Ks))) := by
    refine CPair.oneValue_trans
      (CPair.mul_congr (CPair.oneValue_refl _) (ofB_mul _ _)) ?_
    rw [← CPair.mul_assoc B (ofB (bpow Dt Kt)) (ofB (bpow Ds Ks)),
      CPair.mul_comm B (ofB (bpow Dt Kt)), CPair.mul_assoc]
    exact CPair.oneValue_refl _
  have h3 : ofB (foldK (deriv q) Ns Ds Ks) * ws < B * ofB (bpow Ds Ks) :=
    ltC_unscale_left (unitC_le_num _ (unitLeBpow hDt Kt))
      (CPair.lt_congr eL eR h2)
  have hL : (vnorm (deriv q)).length - 1 ≤ Ks :=
    Nat.pred_le_pred (Nat.le_trans (vnormDeriv_le q) hq)
  obtain ⟨g, hg⟩ := Nat.le.dest hL
  have hbr := foldK_magFold (deriv q) Ns Ds g
  rw [hg] at hbr
  have eL2 : (ofB (foldK (deriv q) Ns Ds Ks) * ws).oneValue
      (ofB (bpow Ds g) * (ofB (magFold (deriv q) Ns Ds) * ws)) := by
    refine CPair.oneValue_trans
      (CPair.mul_congr
        (CPair.oneValue_trans (CPair.num_oneValue hbr Pos.one) (ofB_mul _ _))
        (CPair.oneValue_refl _)) ?_
    rw [CPair.mul_assoc]
    exact CPair.oneValue_refl _
  have hsplit : (bpow Ds Ks).oneValue
      (bpow Ds ((vnorm (deriv q)).length - 1) * bpow Ds g) := by
    rw [← hg]
    exact bpow_add Ds _ g
  have eR2 : (B * ofB (bpow Ds Ks)).oneValue
      (ofB (bpow Ds g) * (B * ofB (bpow Ds ((vnorm (deriv q)).length - 1)))) := by
    refine CPair.oneValue_trans
      (CPair.mul_congr (CPair.oneValue_refl _)
        (CPair.oneValue_trans (CPair.num_oneValue hsplit Pos.one) (ofB_mul _ _))) ?_
    rw [CPair.mul_comm (ofB (bpow Ds ((vnorm (deriv q)).length - 1))) (ofB (bpow Ds g)),
      ← CPair.mul_assoc B (ofB (bpow Ds g)) _, CPair.mul_comm B (ofB (bpow Ds g)),
      CPair.mul_assoc]
    exact CPair.oneValue_refl _
  exact ltC_unscale_left (unitC_le_num _ (unitLeBpow (leB_of_lt hDs) g))
    (CPair.lt_congr eL2 eR2 h3)

/-- The value keeps the upper side at every point of the box: the
outer read holds at the point's inner value, and the side follows
along the outer bracket. -/
theorem keepUpperBox_all (p : PPoly) (t0 t1 s0 s1 : CPair) (Nt Dt Ns Ds : BPair)
    (h : keepUpperBox p t0 t1 s0 s1 Nt Dt Ns Ds)
    (t s : CPair) (ht0 : t0 ≤ t) (ht1 : t ≤ t1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) :
    unitC < evalC (innerC p t) s := by
  obtain ⟨t0n, t0c⟩ := t0
  obtain ⟨s0n, s0c⟩ := s0
  obtain ⟨tn, tc⟩ := t
  obtain ⟨hDt, _, hqt0, hqt1, hDs, hs01, hqs0, hqs1, hV⟩ := h
  rw [innerC_mk, denC_mk] at hV
  rw [innerC_mk]
  obtain ⟨hII, hIII, hIV⟩ := box_legs p t0n t0c t1 s0n s0c Nt Dt Ns Ds
    hDt hqt0 hqt1 hDs hqs0 tn tc ht0 ht1
  have hTc : unitC < ofB (BPair.ofPos (Pos.pow tc (innerTop p))) :=
    unitC_lt_ofB (unitLtOfPos _)
  have hT0 : unitC ≤ ofB (BPair.ofPos (Pos.pow t0c (innerTop p))) :=
    Or.inr (unitC_lt_ofB (unitLtOfPos _))
  have hS0 : unitC < ofB (BPair.ofPos (Pos.pow s0c (outerTop p))) :=
    unitC_lt_ofB (unitLtOfPos _)
  have hZc : unitC ≤ ofB (bpow Dt (innerTop p) * bpow Ds (outerTop p)) :=
    unitC_le_num _ (unitLeMul (unitLeBpow (leB_of_lt hDt) _)
      (unitLeBpow (leB_of_lt hDs) _))
  have hws : unitC ≤ s1 + CPair.swap ⟨s0n, s0c⟩ :=
    CPair.le_congr (addC_swap_unit _) (CPair.oneValue_refl _)
      (CPair.le_add (CPair.le_trans hs0 hs1) (CPair.le_refl _))
  have hNs : BPair.unit ≤ Ns :=
    unitC_le_fst (CPair.le_trans
      (unitC_le_mul (unitC_le_cmag _) (unitC_le_num _ (leB_of_lt hDs))) hqs0)
  have hqt : cmag (⟨tn, tc⟩ : CPair) * ofB Dt ≤ ofB Nt :=
    cmag_seg (leB_of_lt hDt) hqt0 hqt1 ht0 ht1
  have hF : foldK (deriv (pevalCP p tn tc (innerTop p))) Ns Ds (outerTop p)
        * bpow Dt (innerTop p)
      ≤ foldOuterK (derivOuter p) Nt Dt (innerTop p) Ns Ds (outerTop p)
        * bpow (BPair.ofPos tc) (innerTop p) :=
    leB_congr_left
      (BPair.mul_congr_left
        (foldK_congr (pevalCP_derivOuter p tn tc (innerTop p)) Ns Ds _))
      (foldK_pevalCP (derivOuter p) tn tc (innerTop p) (leB_of_lt hDt) hNs
        (leB_of_lt hDs) (innerLe_derivOuter (innerLe_innerTop p))
        (magBound_num tn tc Nt Dt hqt) (outerTop p))
  have hmain := cornerToInner _ _ _ _ _ _ _ _ _ _ _ _ hTc hT0 hS0 hZc hII hIII hIV hV
  have hK : keepUpper (pevalCP p tn tc (innerTop p)) ⟨s0n, s0c⟩ s1 Ns Ds :=
    ⟨hDs, hs01, hqs0, hqs1,
     innerPrice (pevalCP p tn tc (innerTop p)) (outerTop p)
       (by rw [length_pevalCP]; exact ground.lePredSucc p.length)
       Ns Ds Dt (innerTop p) hDs (leB_of_lt hDt) tc _ _ _ hws hF hmain⟩
  exact keepUpper_all _ ⟨s0n, s0c⟩ s1 Ns Ds hK s hs0 hs1

/-- The value keeps the lower side at every point of the box, the
upper read at the memberwise swap. -/
theorem keepLowerBox_all (p : PPoly) (t0 t1 s0 s1 : CPair) (Nt Dt Ns Ds : BPair)
    (h : keepLowerBox p t0 t1 s0 s1 Nt Dt Ns Ds)
    (t s : CPair) (ht0 : t0 ≤ t) (ht1 : t ≤ t1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) :
    evalC (innerC p t) s < unitC := by
  obtain ⟨t0n, t0c⟩ := t0
  obtain ⟨s0n, s0c⟩ := s0
  obtain ⟨tn, tc⟩ := t
  obtain ⟨hDt, _, hqt0, hqt1, hDs, hs01, hqs0, hqs1, hV⟩ := h
  rw [innerC_mk, denC_mk] at hV
  rw [innerC_mk]
  obtain ⟨hII, hIII, hIV⟩ := box_legs p t0n t0c t1 s0n s0c Nt Dt Ns Ds
    hDt hqt0 hqt1 hDs hqs0 tn tc ht0 ht1
  have hTc : unitC < ofB (BPair.ofPos (Pos.pow tc (innerTop p))) :=
    unitC_lt_ofB (unitLtOfPos _)
  have hT0 : unitC ≤ ofB (BPair.ofPos (Pos.pow t0c (innerTop p))) :=
    Or.inr (unitC_lt_ofB (unitLtOfPos _))
  have hS0 : unitC < ofB (BPair.ofPos (Pos.pow s0c (outerTop p))) :=
    unitC_lt_ofB (unitLtOfPos _)
  have hZc : unitC ≤ ofB (bpow Dt (innerTop p) * bpow Ds (outerTop p)) :=
    unitC_le_num _ (unitLeMul (unitLeBpow (leB_of_lt hDt) _)
      (unitLeBpow (leB_of_lt hDs) _))
  have hws : unitC ≤ s1 + CPair.swap ⟨s0n, s0c⟩ :=
    CPair.le_congr (addC_swap_unit _) (CPair.oneValue_refl _)
      (CPair.le_add (CPair.le_trans hs0 hs1) (CPair.le_refl _))
  have hNs : BPair.unit ≤ Ns :=
    unitC_le_fst (CPair.le_trans
      (unitC_le_mul (unitC_le_cmag _) (unitC_le_num _ (leB_of_lt hDs))) hqs0)
  have hqt : cmag (⟨tn, tc⟩ : CPair) * ofB Dt ≤ ofB Nt :=
    cmag_seg (leB_of_lt hDt) hqt0 hqt1 ht0 ht1
  have hF : foldK (deriv (pevalCP p tn tc (innerTop p))) Ns Ds (outerTop p)
        * bpow Dt (innerTop p)
      ≤ foldOuterK (derivOuter p) Nt Dt (innerTop p) Ns Ds (outerTop p)
        * bpow (BPair.ofPos tc) (innerTop p) :=
    leB_congr_left
      (BPair.mul_congr_left
        (foldK_congr (pevalCP_derivOuter p tn tc (innerTop p)) Ns Ds _))
      (foldK_pevalCP (derivOuter p) tn tc (innerTop p) (leB_of_lt hDt) hNs
        (leB_of_lt hDs) (innerLe_derivOuter (innerLe_innerTop p))
        (magBound_num tn tc Nt Dt hqt) (outerTop p))
  generalize hA : evalC (pevalOuter p s0n s0c (outerTop p)) ⟨tn, tc⟩ = A at *
  generalize hA0 : evalC (pevalOuter p s0n s0c (outerTop p)) ⟨t0n, t0c⟩ = A0 at *
  generalize hB : evalC (pevalCP p tn tc (innerTop p)) ⟨s0n, s0c⟩ = B at *
  generalize hC : evalC (pevalCP p t0n t0c (innerTop p)) ⟨s0n, s0c⟩ = C at *
  have hII' : cmag (CPair.swap A + CPair.swap (CPair.swap A0))
      * ofB (bpow Dt (innerTop p) * bpow Ds (outerTop p))
      ≤ ofB (foldOuterK (derivInner p) Nt Dt (innerTop p) Ns Ds (outerTop p))
        * ofB (BPair.ofPos (Pos.pow s0c (outerTop p))) * (t1 + CPair.swap ⟨t0n, t0c⟩) :=
    CPair.le_congr
      (CPair.mul_congr (CPair.oneValue_symm (cmag_swap (A + CPair.swap A0)))
        (CPair.oneValue_refl _))
      (CPair.oneValue_refl _) hII
  have hIII' : (CPair.swap A * ofB (BPair.ofPos (Pos.pow tc (innerTop p)))).oneValue
      (CPair.swap B * ofB (BPair.ofPos (Pos.pow s0c (outerTop p)))) := by
    rw [CPair.swap_mul, CPair.swap_mul]
    exact CPair.swap_congr hIII
  have hIV' : (CPair.swap A0 * ofB (BPair.ofPos (Pos.pow t0c (innerTop p)))).oneValue
      (CPair.swap C * ofB (BPair.ofPos (Pos.pow s0c (outerTop p)))) := by
    rw [CPair.swap_mul, CPair.swap_mul]
    exact CPair.swap_congr hIV
  have hmain := cornerToInner _ _ _ _ _ _ _ _ _ _ _ _ hTc hT0 hS0 hZc hII' hIII' hIV' hV
  have hK : keepLower (pevalCP p tn tc (innerTop p)) ⟨s0n, s0c⟩ s1 Ns Ds :=
    ⟨hDs, hs01, hqs0, hqs1, by
      rw [hB]
      exact innerPrice (pevalCP p tn tc (innerTop p)) (outerTop p)
        (by rw [length_pevalCP]; exact ground.lePredSucc p.length)
        Ns Ds Dt (innerTop p) hDs (leB_of_lt hDt) tc _ _ _ hws hF hmain⟩
  exact keepLower_all _ ⟨s0n, s0c⟩ s1 Ns Ds hK s hs0 hs1

end stage
