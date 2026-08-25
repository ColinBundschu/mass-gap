import MassGap.Windowsep
/-!
`lem:stage` — the located stage at one adjunction over the ground:
an extension's certificate is the monic polynomial's below-top list
with the isolating bracket's endpoints (`Ext`, the endpoints
composite pairs), the bracket's side exchange the root's naming
(`bracketRead` at the composite evaluations, `evalC`) with the
isolation at half the separation (`isolRead`, consuming
`windowsep.sepRead` at the doubled width); the stage's elements are
the remainder lists at the monic polynomial with `poly.add` and
`poly.remMul` their displayed sum and product (`poly.divRead`'s
naming identity and `poly.hornerRead` the arithmetic's own reads,
the batteries'), the equal-members read is the reduction's
(`reduceRead`, the remainder's unit tail), the unit witness is the
Bézout read cleared at a constant off equal members (`witnessRead`,
the value's inverse the witness against the clearing, the
homogeneity principle's spelling), and a value's side at the root is
the priced side read of the tex's display (`sideUpper`,
`sideLower`): the width joins the endpoints and the bracket carries
the priced read at the extension polynomial's radius, so the value
keeps the side at every bracket point, the root's among them
(`sideUpper_all`, `sideLower_all`).  That price is the theorem
tier's own: at two points inside a stated bound's segment the
polynomial's two values differ by at most the points' gap against
the derivative's coefficient fold at the bound, cleared at the
fold's power (`eval_gap_le`, the coefficientwise difference
`p(y) - p(x) = (y - x) Σ_k p_k Σ_{i+j=k-1} y^i x^j` collected
termwise against `p'_j = (j+1) p_{j+1}`, the radius pair the
bound's own instance), and the priced side read at a composite
bracket and a stated bound — the bound's clearing above the sum's
unit, the ordered endpoints inside that bound's segment with the
lower endpoint's value on the stated side clearing the bracket's
width against that fold — keeps the side at every bracket point
(`keepUpper`/`keepUpper_all`, `keepLower`/`keepLower_all` the
memberwise swap's, `keepLowerTop`/`keepLowerTop_all` the same
clause read at the upper endpoint — the upper endpoint's value on
the lower side clearing that same bracket width), the composite
points read through their integer representatives
(`evalC_evalClear` at `poly.evalClear`, the homogeneity
principle's own).  The value
arithmetic at a proper factor of the polynomial —
the side-exchange read at the divisor with the Bézout read at its
cofactor, the landed reads its extremes (the reduction at the
whole, the witness at the coprime) — and the stage's closure on
itself, the iterated tower with each extension's polynomial over
the stage the earlier extensions built, are `lem:stagesplit`'s
(`valueNullRead`/`valueUnitRead`; the tower's `opsAt` at the
generic remainder arithmetic), the one-adjunction reads here the
tier's base; the margin floor `margin · U₁ ≥ 1` rides at its
recorded consumers (`lem:hermitesign`'s located values, the
decimation's priced entries).
-/

namespace stage
open ground poly windowsep

/-- A ground coefficient's composite entry at the shared unit
datum. -/
def ofB (b : BPair) : CPair := ⟨b, .one⟩

/-- The composite sum's unit, the equal-membered class. -/
def unitC : CPair := ⟨BPair.unit, .one⟩

/-- The composite magnitude, the sorted first datum's value. -/
def cmag (x : CPair) : CPair := if x < x.swap then x.swap else x

/-- The evaluation at a composite point, the Horner read with the
coefficients entering at the shared unit datum. -/
def evalC : Poly → CPair → CPair
  | [], _ => unitC
  | c :: p, x => ofB c + x * evalC p x

/-! The composite reads: the Horner read at every representative of
the coefficient list and of the point, the unit tail's own and the
memberwise swap's, and the cleared evaluation at the point's integer
representative (`poly.evalClear`, the homogeneity principle's
spelling); beside them the composite side and magnitude at the
stated representative. -/

/-- The equal-membered composite at every second datum. -/
private theorem unitC_den (w : Pos) :
    CPair.oneValue ⟨BPair.unit, w⟩ unitC := by
  show Pos.one * Pos.one + Pos.one * w
    = Pos.one * w + Pos.one * Pos.one
  exact ground.add_comm _ _

/-- Two composites at one second datum join at that datum. -/
private theorem addC_same (u v : BPair) (w : Pos) :
    ((⟨u, w⟩ : CPair) + ⟨v, w⟩).oneValue ⟨u + v, w⟩ := by
  have he : ((⟨u, w⟩ : CPair) + ⟨v, w⟩) = ⟨(u + v).scale w, w * w⟩ := by
    show CPair.mk ⟨u.fst * w + v.fst * w, u.snd * w + v.snd * w⟩ (w * w)
      = ⟨(u + v).scale w, w * w⟩
    rw [← ground.right_distrib, ← ground.right_distrib]
    rfl
  rw [he]
  exact CPair.scale_oneValue (u + v) w w

/-- A composite at the second datum's own rewriting. -/
private theorem denC_eq {u : BPair} {c e : Pos} (h : c = e) :
    (⟨u, c⟩ : CPair).oneValue ⟨u, e⟩ := by
  rw [h]
  exact CPair.oneValue_refl _

/-- A one-datum composite at a rescaled representative. -/
private theorem ofBC_pow (a : BPair) (w : Pos) :
    (⟨a, Pos.one⟩ : CPair).oneValue ⟨a.scale w, w⟩ := by
  have h := CPair.scale_oneValue a Pos.one w
  rw [ground.one_mul w] at h
  exact CPair.oneValue_symm h

/-- The composite unit absorbs a product. -/
private theorem mulC_unitC (x : CPair) : (x * unitC).oneValue unitC :=
  match x with
  | ⟨n, d⟩ =>
    CPair.oneValue_trans
      (CPair.num_oneValue (BPair.mul_unit n) (d * Pos.one))
      (unitC_den (d * Pos.one))

/-- The composite unit is the join's own. -/
private theorem addC_unitC (x : CPair) : (unitC + x).oneValue x := by
  rw [CPair.add_comm]
  exact CPair.opUnit_oneValue x Pos.one Pos.one

/-- A unit-tail list's composite read is the composite unit. -/
theorem evalC_unitTail {p : Poly} (h : poly.unitTail p) (x : CPair) :
    (evalC p x).oneValue unitC :=
  match p, h with
  | [], _ => CPair.oneValue_refl _
  | _ :: _, h =>
    CPair.oneValue_trans
      (CPair.add_congr (CPair.num_oneValue h.1 Pos.one)
        (CPair.mul_congr (CPair.oneValue_refl x) (evalC_unitTail h.2 x)))
      (CPair.oneValue_trans
        (CPair.add_congr (CPair.oneValue_refl unitC) (mulC_unitC x))
        (addC_unitC unitC))

/-- The composite Horner read at every representative of one value:
a further key reads the unit tail through the point's multiple. -/
theorem evalC_congr {p q : Poly} (h : poly.oneValue p q) (x : CPair) :
    (evalC p x).oneValue (evalC q x) :=
  match p, q, h with
  | [], [], _ => CPair.oneValue_refl _
  | [], d :: q, h =>
    CPair.oneValue_symm (evalC_unitTail (p := d :: q) h x)
  | c :: p, [], h => evalC_unitTail (p := c :: p) h x
  | _ :: _, _ :: _, h =>
    CPair.add_congr (CPair.num_oneValue h.1 Pos.one)
      (CPair.mul_congr (CPair.oneValue_refl x) (evalC_congr h.2 x))

/-- The composite Horner read at every representative of the point. -/
theorem evalC_point_congr (p : Poly) {x y : CPair} (h : x.oneValue y) :
    (evalC p x).oneValue (evalC p y) :=
  match p with
  | [] => CPair.oneValue_refl _
  | c :: t =>
    CPair.add_congr (CPair.oneValue_refl (ofB c))
      (CPair.mul_congr h (evalC_point_congr t h))

/-- The composite read at the memberwise swap. -/
theorem evalC_neg (p : Poly) (x : CPair) :
    (evalC (poly.neg p) x).oneValue (CPair.swap (evalC p x)) :=
  match p with
  | [] => CPair.oneValue_refl _
  | c :: t =>
    CPair.add_congr (CPair.oneValue_refl (ofB c.swap))
      (CPair.mul_congr (CPair.oneValue_refl x) (evalC_neg t x))

/-- A count sits at or below its predecessor's successor. -/
private theorem lenLePred : ∀ n : Nat, n ≤ n - 1 + 1
  | 0 => Nat.zero_le 1
  | _ + 1 => Nat.le_refl _

/-- The clearing's leading-key split at the one-value read, the
head entering un-normed (`poly.clearVar_cons`'s read). -/
private theorem clearVar_cons_ov (a : BPair) (t : Poly) (c : Pos)
    (M : Nat) :
    poly.oneValue (poly.clearVar (a :: t) c (M + 1))
      ((a * ground.bpow (BPair.ofPos c) (M + 1))
        :: poly.clearVar t c M) := by
  rw [poly.clearVar_cons a t c (M + 1)]
  exact And.intro (BPair.norm_oneValue _) (poly.oneValue_refl _)

/-- The composite point's Horner read at the cleared list: the
integer representative's own read against the clearing's power. -/
private theorem evalC_read : ∀ (p : Poly) (K : Nat), p.length ≤ K + 1 →
    ∀ (l : BPair) (c : Pos),
      (evalC p ⟨l, c⟩).oneValue
        ⟨poly.eval (poly.clearVar p c K) l, ground.Pos.pow c K⟩
  | [], K, _, _, c =>
    CPair.oneValue_symm (unitC_den (ground.Pos.pow c K))
  | a :: t, 0, h, l, c => by
    have ht : t = [] :=
      ground.nil_of_length_zero t
        (Nat.le_antisymm (Nat.le_of_succ_le_succ h) (Nat.zero_le _))
    subst ht
    have hnum : ((a * ground.bpow (BPair.ofPos c) 0).norm
        + l * BPair.unit).oneValue a :=
      BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.mul_one_read a))
          (BPair.mul_unit l))
        (BPair.add_unit a)
    exact CPair.oneValue_trans
      (CPair.oneValue_trans
        (CPair.add_congr (CPair.oneValue_refl (ofB a))
          (mulC_unitC ⟨l, c⟩))
        (CPair.opUnit_oneValue (ofB a) Pos.one Pos.one))
      (CPair.oneValue_symm (CPair.num_oneValue hnum Pos.one))
  | a :: t, M + 1, h, l, c => by
    have hIH := evalC_read t M (Nat.le_of_succ_le_succ h) l c
    have hscale : (a.scale (ground.Pos.pow c (M + 1))).oneValue
        (a * ground.bpow (BPair.ofPos c) (M + 1)) :=
      BPair.oneValue_trans
        (BPair.oneValue_symm
          (BPair.ofPos_scale (ground.Pos.pow c (M + 1)) a))
        (BPair.oneValue_trans
          (BPair.mul_congr (ground.ofPos_pow c (M + 1))
            (BPair.oneValue_refl a))
          (BPair.oneValue_of_eq
            (BPair.mul_comm (ground.bpow (BPair.ofPos c) (M + 1)) a)))
    have hnum : (a.scale (ground.Pos.pow c (M + 1))
        + l * poly.eval (poly.clearVar t c M) l).oneValue
        (poly.eval (poly.clearVar (a :: t) c (M + 1)) l) :=
      BPair.oneValue_symm
        (BPair.oneValue_trans
          (poly.eval_congr (clearVar_cons_ov a t c M) l)
          (BPair.add_congr (BPair.oneValue_symm hscale)
            (BPair.oneValue_refl _)))
    refine CPair.oneValue_trans
      (CPair.add_congr (ofBC_pow a (ground.Pos.pow c (M + 1)))
        (CPair.mul_congr (CPair.oneValue_refl (⟨l, c⟩ : CPair)) hIH)) ?_
    refine CPair.oneValue_trans
      (addC_same (a.scale (ground.Pos.pow c (M + 1)))
        (l * poly.eval (poly.clearVar t c M) l)
        (ground.Pos.pow c (M + 1))) ?_
    exact CPair.num_oneValue hnum (ground.Pos.pow c (M + 1))

/-- The composite point's read is the cleared evaluation at the
integer representative against the clearing's power. -/
theorem evalC_evalClear (p : Poly) (l : BPair) (c : Pos) :
    (evalC p ⟨l, c⟩).oneValue
      ⟨poly.evalClear p l c (p.length - 1), ground.Pos.pow c (p.length - 1)⟩ :=
  CPair.oneValue_trans
    (evalC_read p (p.length - 1) (lenLePred p.length) l c)
    (CPair.num_oneValue (poly.eval_clearVar p c (p.length - 1) l)
      (ground.Pos.pow c (p.length - 1)))

/-- The composite carrier's side at its stated representative. -/
theorem unitC_lt_num (n : BPair) (d : Pos) :
    unitC < (⟨n, d⟩ : CPair) ↔ BPair.unit < n := by
  constructor
  · intro h
    have h0 : Pos.one * d + n.snd * Pos.one
        < n.fst * Pos.one + Pos.one * d := h
    rw [ground.one_mul d, ground.mul_one n.snd,
      ground.mul_one n.fst] at h0
    have h1 : n.snd + d < n.fst + d := by
      rw [ground.add_comm n.snd d]
      exact h0
    show Pos.one + n.snd < n.fst + Pos.one
    rw [ground.add_comm Pos.one n.snd]
    exact ground.posLtAddLe (ground.posLtCancelR h1) (Or.inl rfl)
  · intro h
    have h0 : Pos.one + n.snd < n.fst + Pos.one := h
    have h1 : n.snd + Pos.one < n.fst + Pos.one := by
      rw [← ground.add_comm Pos.one n.snd]
      exact h0
    have h2 : n.snd < n.fst := ground.posLtCancelR h1
    show Pos.one * d + n.snd * Pos.one
      < n.fst * Pos.one + Pos.one * d
    rw [ground.one_mul d, ground.mul_one n.snd,
      ground.mul_one n.fst, ground.add_comm d n.snd]
    exact ground.posLtAddLe h2 (Or.inl rfl)

/-- The composite carrier's lower side at its stated
representative. -/
private theorem num_lt_unitC {n : BPair} (d : Pos)
    (h : n < BPair.unit) : (⟨n, d⟩ : CPair) < unitC := by
  have h0 : n.fst + Pos.one < Pos.one + n.snd := h
  have h1 : n.fst + Pos.one < n.snd + Pos.one := by
    rw [ground.add_comm n.snd Pos.one]
    exact h0
  have h2 : n.fst < n.snd := ground.posLtCancelR h1
  show n.fst * Pos.one + Pos.one * d
    < Pos.one * d + n.snd * Pos.one
  rw [ground.mul_one n.fst, ground.one_mul d, ground.mul_one n.snd,
    ground.add_comm d n.snd]
  exact ground.posLtAddLe h2 (Or.inl rfl)

/-- The composite side at the stated representative's own. -/
private theorem clt_swap_iff (n : BPair) (d : Pos) :
    (⟨n, d⟩ : CPair) < CPair.swap ⟨n, d⟩ ↔ n < n.swap := by
  constructor
  · intro h
    have h0 : n.fst * d + n.fst * d
        < n.snd * d + n.snd * d := h
    have h1 : (n.fst + n.fst) * d
        < (n.snd + n.snd) * d := by
      rw [ground.right_distrib, ground.right_distrib]
      exact h0
    exact ground.lt_of_mul_lt h1
  · intro h
    have h0 : n.fst + n.fst < n.snd + n.snd := h
    have h1 := ground.mul_lt_mul_right d h0
    show n.fst * d + n.fst * d
      < n.snd * d + n.snd * d
    rw [← ground.right_distrib, ← ground.right_distrib]
    exact h1

/-- The composite magnitude at the stated representative. -/
theorem cmag_num (n : BPair) (d : Pos) :
    (cmag (⟨n, d⟩ : CPair)).oneValue ⟨windowsep.mag n, d⟩ := by
  by_cases hlt : (⟨n, d⟩ : CPair) < CPair.swap ⟨n, d⟩
  · have hn : n < n.swap := (clt_swap_iff n d).mp hlt
    show CPair.oneValue
      (if (⟨n, d⟩ : CPair) < CPair.swap ⟨n, d⟩
        then CPair.swap ⟨n, d⟩ else ⟨n, d⟩)
      ⟨if n < n.swap then n.swap else n, d⟩
    rw [if_pos hlt, if_pos hn]
    exact CPair.oneValue_refl _
  · have hn : ¬ (n < n.swap) := fun hh =>
      hlt ((clt_swap_iff n d).mpr hh)
    show CPair.oneValue
      (if (⟨n, d⟩ : CPair) < CPair.swap ⟨n, d⟩
        then CPair.swap ⟨n, d⟩ else ⟨n, d⟩)
      ⟨if n < n.swap then n.swap else n, d⟩
    rw [if_neg hlt, if_neg hn]
    exact CPair.oneValue_refl _

/-! The composite order kit at a common clearing: the at-or-below
read's transport, the memberwise swap's reversal, and the magnitude,
product and order at a rescaled representative. -/

/-- The composite at-or-below read moves across the one-value
read. -/
private theorem le_congr {x x' y y' : CPair} (hx : x.oneValue x')
    (hy : y.oneValue y') (h : x ≤ y) : x' ≤ y' :=
  match h with
  | Or.inl e =>
    Or.inl (CPair.oneValue_trans (CPair.oneValue_symm hx)
      (CPair.oneValue_trans e hy))
  | Or.inr e => Or.inr (CPair.lt_congr hx hy e)

/-- The memberwise swap reverses the composite order. -/
private theorem cltSwapC {u v : CPair} (h : u < v) :
    CPair.swap v < CPair.swap u :=
  match u, v, h with
  | ⟨un, uc⟩, ⟨vn, vc⟩, h =>
    ground.ltB_swap (x := un.scale vc) (y := vn.scale uc) h

/-- The magnitude at a rescaled datum. -/
private theorem mag_scale (z : BPair) (w : Pos) :
    windowsep.mag (z.scale w) = (windowsep.mag z).scale w := by
  by_cases h : z < z.swap
  · have h' : z.scale w < (z.scale w).swap := BPair.scale_lt w h
    show (if z.scale w < (z.scale w).swap then (z.scale w).swap
        else z.scale w)
      = (if z < z.swap then z.swap else z).scale w
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ (z.scale w < (z.scale w).swap) := fun hh =>
      h (BPair.lt_of_scale_lt (x := z) (y := z.swap) (w := w) hh)
    show (if z.scale w < (z.scale w).swap then (z.scale w).swap
        else z.scale w)
      = (if z < z.swap then z.swap else z).scale w
    rw [if_neg h', if_neg h]

/-- The composite at-or-below read at stated second data is the
scaled numerators' own. -/
private theorem cleNum {u v : BPair} {c e : Pos}
    (h : (⟨u, c⟩ : CPair) ≤ ⟨v, e⟩) : u.scale e ≤ v.scale c := h

/-- The composite order at stated second data is the scaled
numerators' own. -/
private theorem cltNum {u v : BPair} {c e : Pos}
    (h : (⟨u, c⟩ : CPair) < ⟨v, e⟩) : u.scale e < v.scale c := h

/-- The stated bound at a rescaled representative: an endpoint's
composite bound at its stated representative reads the scaled first
datum's own against the clearing. -/
private theorem boundAt {zn : BPair} {zc : Pos} {N D : BPair} (w e : Pos)
    (he : zc * w = e)
    (h : cmag ⟨zn, zc⟩ * ofB D ≤ ofB N) :
    windowsep.mag (zn.scale w) * D ≤ N * BPair.ofPos e := by
  have h1 : (⟨windowsep.mag zn * D, zc⟩ : CPair) ≤ ofB N :=
    le_congr
      (CPair.oneValue_trans
        (CPair.mul_congr (cmag_num zn zc) (CPair.oneValue_refl (ofB D)))
        (denC_eq (ground.mul_one zc)))
      (CPair.oneValue_refl (ofB N)) h
  have h2 := cleNum h1
  rw [BPair.scale_one] at h2
  have h3 := ground.leB_scale h2 w
  rw [BPair.scale_scale, he] at h3
  refine ground.leB_congr ?_ ?_ h3
  · refine BPair.oneValue_of_eq ?_
    rw [mag_scale zn w,
      ← ground.BPair.scale_mul_left (windowsep.mag zn) D w]
  · exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofPos_scale e N))
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos e) N))

set_option genInjectivity false in
/-- An adjunction's certificate: the monic polynomial's below-top
list with the isolating bracket's endpoints. -/
structure Ext where
  pol : Poly
  lo : CPair
  hi : CPair

/-- The bracket's side exchange, the root's naming: the ordered
endpoints with the monic evaluations on exchanged sides. -/
def bracketRead (E : Ext) : Prop :=
  E.lo < E.hi
  ∧ ((evalC (monic E.pol) E.lo < unitC
      ∧ unitC < evalC (monic E.pol) E.hi)
    ∨ (unitC < evalC (monic E.pol) E.lo
      ∧ evalC (monic E.pol) E.hi < unitC))

instance (E : Ext) : Decidable (bracketRead E) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- The isolation at half the separation: the bracket's width
`[wn : wd]` joins the endpoints, and the doubled width sits at or
below `thm:windowsep`'s `δ`. -/
def isolRead (E : Ext) (wn wd : Pos) : Prop :=
  (E.lo + ⟨BPair.ofPos wn, wd⟩).oneValue E.hi
  ∧ windowsep.sepRead (monic E.pol) (2 * wn) wd

instance (E : Ext) (wn wd : Pos) : Decidable (isolRead E wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The equal-members read by reduction: the value at the root reads
equal members exactly at the remainder's unit tail, the division's
descent at the monic polynomial. -/
def reduceRead (E : Ext) (p : Poly) : Prop :=
  poly.unitTail (poly.div E.pol p).2

instance (E : Ext) (p : Poly) : Decidable (reduceRead E p) :=
  poly.decUnitTail _

/-- The unit witness, cleared: `u p + v S = c` at a constant off
equal members, the value's inverse the witness against the clearing,
the homogeneity principle's spelling of the Bézout read. -/
def witnessRead (E : Ext) (p u v : Poly) (c : BPair) : Prop :=
  c.offUnit
  ∧ poly.oneValue (poly.add (poly.mul u p) (poly.mul v (monic E.pol)))
      [c]

instance (E : Ext) (p u v : Poly) (c : BPair) :
    Decidable (witnessRead E p u v c) :=
  inferInstanceAs (Decidable (¬ _ ∧ _))

/-- The priced side read at a composite bracket and a stated bound:
the bound's clearing above the sum's unit, the ordered endpoints
inside the bound's segment, the lower endpoint's value on the upper
side, and that value clearing the bracket's width against the
derivative's coefficient fold at the bound. -/
def keepUpper (p : Poly) (a b : CPair) (N D : BPair) : Prop :=
  BPair.unit < D ∧ a < b ∧ unitC < evalC p a
  ∧ cmag a * ofB D ≤ ofB N ∧ cmag b * ofB D ≤ ofB N
  ∧ ofB (windowsep.magFold (poly.deriv p) N D) * (b + CPair.swap a)
      < evalC p a * ofB (ground.bpow D
          ((poly.vnorm (poly.deriv p)).length - 1))

instance (p : Poly) (a b : CPair) (N D : BPair) :
    Decidable (keepUpper p a b N D) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The lower side's priced read, the memberwise swap's. -/
def keepLower (p : Poly) (a b : CPair) (N D : BPair) : Prop :=
  BPair.unit < D ∧ a < b ∧ evalC p a < unitC
  ∧ cmag a * ofB D ≤ ofB N ∧ cmag b * ofB D ≤ ofB N
  ∧ ofB (windowsep.magFold (poly.deriv p) N D) * (b + CPair.swap a)
      < CPair.swap (evalC p a) * ofB (ground.bpow D
          ((poly.vnorm (poly.deriv p)).length - 1))

instance (p : Poly) (a b : CPair) (N D : BPair) :
    Decidable (keepLower p a b N D) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The lower side's priced read at the upper endpoint, the same
clause's other endpoint: the bound's clearing above the sum's unit,
the ordered endpoints inside the bound's segment, the upper
endpoint's value on the lower side, and that value's memberwise
swap clearing the bracket's width against the derivative's
coefficient fold at the bound. -/
def keepLowerTop (p : Poly) (a b : CPair) (N D : BPair) : Prop :=
  BPair.unit < D ∧ a < b ∧ evalC p b < unitC
  ∧ cmag a * ofB D ≤ ofB N ∧ cmag b * ofB D ≤ ofB N
  ∧ ofB (windowsep.magFold (poly.deriv p) N D) * (b + CPair.swap a)
      < CPair.swap (evalC p b) * ofB (ground.bpow D
          ((poly.vnorm (poly.deriv p)).length - 1))

instance (p : Poly) (a b : CPair) (N D : BPair) :
    Decidable (keepLowerTop p a b N D) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A value's upper side at the root, the priced side read: the
width joins the endpoints and the bracket carries the priced side
read at the extension polynomial's radius — the endpoints inside
that bound's segment and the lower endpoint's value clearing the
bracket's width against the derivative's coefficient fold, the
image-width price — so the value keeps the side at every bracket
point, the root's among them. -/
def sideUpper (E : Ext) (p : Poly) (wn wd : Pos) : Prop :=
  (E.lo + ⟨BPair.ofPos wn, wd⟩).oneValue E.hi
  ∧ keepUpper p E.lo E.hi (windowsep.radiusN (poly.monic E.pol))
      (windowsep.radiusD (poly.monic E.pol))

instance (E : Ext) (p : Poly) (wn wd : Pos) :
    Decidable (sideUpper E p wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The lower side's priced read, the memberwise swap's. -/
def sideLower (E : Ext) (p : Poly) (wn wd : Pos) : Prop :=
  (E.lo + ⟨BPair.ofPos wn, wd⟩).oneValue E.hi
  ∧ keepLower p E.lo E.hi (windowsep.radiusN (poly.monic E.pol))
      (windowsep.radiusD (poly.monic E.pol))

instance (E : Ext) (p : Poly) (wn wd : Pos) :
    Decidable (sideLower E p wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! The priced side read's own kit: the order law at a cleared
factor, the balance folds' vanishing tail, scalar pass and constant
read, and the derivative's coefficient read at every key. -/

/-- A factor strictly above the sum's unit cancels off the order's
strict read. -/
private theorem ltB_unscale {a b c : BPair} (hc : BPair.unit < c)
    (h : a * c < b * c) : a < b :=
  if hlt : a < b then hlt
  else absurd h (ground.leB_not_lt
    (ground.leB_congr
      (BPair.oneValue_of_eq (BPair.mul_comm c b))
      (BPair.oneValue_of_eq (BPair.mul_comm c a))
      (ground.leB_mulR (ground.leB_of_lt hc)
        (ground.leB_of_not_lt hlt))))

/-- A family reading the sum's unit beyond a key leaves its fold at
that key's range. -/
private theorem foldB_range_vanish (U : Nat → BPair) (A : Nat)
    (hv : ∀ j, A ≤ j → (U j).oneValue BPair.unit) : ∀ c : Nat,
    (ground.famFold BPair.add BPair.unit U (List.range (A + c))).oneValue
      (ground.famFold BPair.add BPair.unit U (List.range A))
  | 0 => BPair.oneValue_refl _
  | c + 1 => by
    refine BPair.oneValue_trans (ground.foldB_range_snoc U (A + c)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (foldB_range_vanish U A hv c)
        (hv (A + c) (Nat.le_add_right A c))) ?_
    exact BPair.add_unit _

/-- A scalar passes into the fold on the right. -/
private theorem foldB_mul_right {α : Type} (c : BPair) (f : α → BPair)
    (l : List α) :
    (ground.famFold BPair.add BPair.unit f l * c).oneValue
      (ground.famFold BPair.add BPair.unit (fun i => f i * c) l) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.mul_comm (ground.famFold BPair.add BPair.unit f l) c)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_mul_left c f l)) ?_
  exact BPair.oneValue_of_eq
    (ground.famFold_congr_all BPair.add BPair.unit _ _
      (fun i => BPair.mul_comm c (f i)) l)

/-- A constant family's fold is the family's count against the
constant. -/
private theorem foldB_const {α : Type} (c : BPair) : ∀ l : List α,
    (ground.famFold BPair.add BPair.unit (fun _ => c) l).oneValue
      (BPair.ofNat l.length * c)
  | [] => BPair.oneValue_symm (BPair.unit_mul c)
  | _ :: t => by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl c) (foldB_const c t)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm c (BPair.ofNat t.length * c))) ?_
    exact BPair.oneValue_symm (ground.ofNat_succ_mul t.length c)

/-- A summand and its own balance partner drop out of a join. -/
private theorem swapCancel (P Q R : BPair) :
    (P + Q + (R + P.swap)).oneValue (R + Q) := by
  rw [BPair.add_comm R P.swap, BPair.add_add_comm P Q P.swap R]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm P P.swap))
        (BPair.swap_add_null (BPair.oneValue_refl P)))
      (BPair.oneValue_refl (Q + R))) ?_
  refine BPair.oneValue_trans (BPair.unit_add (Q + R)) ?_
  exact BPair.oneValue_of_eq (BPair.add_comm Q R)

/-- The successor-weighted shift's entry at every key: the shifted
key's coefficient against its own count. -/
private theorem derivFrom_getAt : ∀ (l : Poly) (m j : Nat),
    (ground.getAt BPair.unit (poly.derivFrom (ground.posOfSucc m) l)
        j).oneValue
      (BPair.ofNat (m + j + 1) * ground.getAt BPair.unit l j)
  | [], m, j => by
    show BPair.unit.oneValue (BPair.ofNat (m + j + 1) * BPair.unit)
    exact BPair.oneValue_symm (BPair.mul_unit _)
  | c :: _, m, 0 => by
    show (c.scale (ground.posOfSucc m)).oneValue
      (BPair.ofNat (m + 0 + 1) * c)
    exact BPair.oneValue_symm (BPair.ofPos_scale (ground.posOfSucc m) c)
  | _ :: t, m, j + 1 => by
    show (ground.getAt BPair.unit
        (poly.derivFrom (ground.posOfSucc (m + 1)) t) j).oneValue
      (BPair.ofNat (m + (j + 1) + 1) * ground.getAt BPair.unit t j)
    have he : m + 1 + j + 1 = m + (j + 1) + 1 := by
      rw [Nat.add_right_comm m 1 j, Nat.add_assoc m j 1]
    rw [← he]
    exact derivFrom_getAt t (m + 1) j

/-- The derivative's coefficient at every key: the shifted key's
coefficient against the key's own count. -/
private theorem deriv_getAt : ∀ (p : Poly) (j : Nat),
    (ground.getAt BPair.unit (poly.deriv p) j).oneValue
      (BPair.ofNat (j + 1) * ground.getAt BPair.unit p (j + 1))
  | [], j => by
    show BPair.unit.oneValue (BPair.ofNat (j + 1) * BPair.unit)
    exact BPair.oneValue_symm (BPair.mul_unit _)
  | _ :: t, j => by
    have h := derivFrom_getAt t 0 j
    rw [Nat.zero_add j] at h
    exact h

/-- The successor-weighted shift at the memberwise swap. -/
private theorem derivFrom_neg : ∀ (n : Pos) (l : Poly),
    poly.derivFrom n (poly.neg l) = poly.neg (poly.derivFrom n l)
  | _, [] => rfl
  | n, c :: t => by
    show (c.swap).scale n :: poly.derivFrom (ground.succ n) (poly.neg t)
      = (c.scale n).swap :: poly.neg (poly.derivFrom (ground.succ n) t)
    rw [derivFrom_neg (ground.succ n) t]
    rfl

/-- The derivative at the memberwise swap. -/
private theorem deriv_neg : ∀ l : Poly,
    poly.deriv (poly.neg l) = poly.neg (poly.deriv l)
  | [] => rfl
  | _ :: t => derivFrom_neg .one t

/-! The geometric difference at the two points: the key's power gap
factors through the points' gap against the two points' mixed
monomials, and that fold's magnitude sits under the key count
against the radius. -/

/-- The mixed monomial fold `Σ_{i+j=k-1} y^i x^j`, the power gap's
cofactor. -/
private def geoSum (x y : BPair) (k : Nat) : BPair :=
  ground.famFold BPair.add BPair.unit
    (fun i => ground.bpow y i * ground.bpow x (k - 1 - i))
    (List.range k)

/-- The mixed fold's step: the lower point's own power joined to the
upper point's multiple of the shorter fold. -/
private theorem geoSum_succ (x y : BPair) (k : Nat) :
    (geoSum x y (k + 1)).oneValue
      (ground.bpow x k + y * geoSum x y k) := by
  show (ground.famFold BPair.add BPair.unit
      (fun i => ground.bpow y i * ground.bpow x (k + 1 - 1 - i))
      (List.range (k + 1))).oneValue _
  rw [ground.foldB_range_cons
    (fun i => ground.bpow y i * ground.bpow x (k + 1 - 1 - i)) k]
  refine BPair.add_congr ?_ ?_
  · exact BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_comm (ground.bpow y 0) (ground.bpow x k)))
      (BPair.mul_one_read (ground.bpow x k))
  · refine BPair.oneValue_trans ?_
      (ground.foldB_mul_left y
        (fun j => ground.bpow y j * ground.bpow x (k - 1 - j))
        (List.range k))
    refine ground.foldB_congr_members _ _ (List.range k) (fun j _ => ?_)
    show (ground.bpow y (j + 1) * ground.bpow x (k - (j + 1))).oneValue
      (y * (ground.bpow y j * ground.bpow x (k - 1 - j)))
    rw [show k - (j + 1) = k - 1 - j from by
      rw [ground.subSub k 1 j, Nat.add_comm 1 j]]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.norm_oneValue (y * ground.bpow y j))
        (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_of_eq
      (BPair.mul_assoc y (ground.bpow y j)
        (ground.bpow x (k - 1 - j)))

/-- The power gap factors: the two points' gap against the mixed
monomial fold. -/
private theorem geo_read (x y : BPair) : ∀ k : Nat,
    (ground.bpow y k + (ground.bpow x k).swap).oneValue
      ((y + x.swap) * geoSum x y k)
  | 0 =>
    BPair.oneValue_trans
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.add_comm (ground.bpow y 0) ((ground.bpow x 0).swap)))
        (BPair.swap_add_null (BPair.oneValue_refl (ground.bpow x 0))))
      (BPair.oneValue_symm (BPair.mul_unit (y + x.swap)))
  | k + 1 => by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.norm_oneValue (y * ground.bpow y k))
        (ground.swap_congr
          (BPair.norm_oneValue (x * ground.bpow x k)))) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (y + x.swap))
        (geoSum_succ x y k)) ?_
    rw [BPair.left_distrib (y + x.swap) (ground.bpow x k)
        (y * geoSum x y k),
      BPair.mul_left_comm (y + x.swap) y (geoSum x y k),
      BPair.right_distrib y x.swap (ground.bpow x k),
      BPair.swap_mul x (ground.bpow x k)]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl y)
          (BPair.oneValue_symm (geo_read x y k)))) ?_
    rw [BPair.left_distrib y (ground.bpow y k) ((ground.bpow x k).swap),
      BPair.mul_swap y (ground.bpow x k)]
    exact swapCancel (y * ground.bpow x k)
      ((x * ground.bpow x k).swap) (y * ground.bpow y k)

/-- A mixed monomial inside the radius segment, cleared at the key's
own power. -/
private theorem geo_term {x y N D : BPair}
    (hx : windowsep.mag x * D ≤ N) (hy : windowsep.mag y * D ≤ N)
    (hD : BPair.unit ≤ D) {i j : Nat} (hij : i ≤ j) :
    windowsep.mag (ground.bpow y i * ground.bpow x (j - i))
        * ground.bpow D j
      ≤ ground.bpow N j := by
  have hN : BPair.unit ≤ N :=
    ground.leB_trans (ground.unitLeMul (windowsep.unitLe_mag x) hD) hx
  have he : i + (j - i) = j := ground.natAddSubCancel hij
  have hj : ∀ z : BPair, (ground.bpow z j).oneValue
      (ground.bpow z i * ground.bpow z (j - i)) := fun z =>
    BPair.oneValue_trans
      (BPair.oneValue_of_eq (congrArg (ground.bpow z) he.symm))
      (ground.bpow_add z i (j - i))
  have step : ∀ (z : BPair) (m : Nat), windowsep.mag z * D ≤ N →
      windowsep.mag (ground.bpow z m) * ground.bpow D m
        ≤ ground.bpow N m := fun z m hz =>
    ground.leB_congr_left
      (BPair.oneValue_trans (windowsep.bpow_mul (windowsep.mag z) D m)
        (BPair.mul_congr
          (BPair.oneValue_symm (windowsep.mag_bpow z m))
          (BPair.oneValue_refl (ground.bpow D m))))
      (windowsep.bpow_mono
        (ground.unitLeMul (windowsep.unitLe_mag z) hD) hz m)
  have hAB : (windowsep.mag (ground.bpow y i * ground.bpow x (j - i))
        * ground.bpow D j).oneValue
      (windowsep.mag (ground.bpow y i) * ground.bpow D i
        * (windowsep.mag (ground.bpow x (j - i))
            * ground.bpow D (j - i))) :=
    BPair.oneValue_trans
      (BPair.mul_congr
        (windowsep.mag_mul (ground.bpow y i) (ground.bpow x (j - i)))
        (hj D))
      (BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm (windowsep.mag (ground.bpow y i))
          (windowsep.mag (ground.bpow x (j - i)))
          (ground.bpow D i) (ground.bpow D (j - i))))
  exact ground.leB_congr (BPair.oneValue_symm hAB)
    (BPair.oneValue_symm (hj N))
    (ground.leB_mul_mono
      (ground.unitLeMul (windowsep.unitLe_mag _)
        (windowsep.unitLe_bpow hD (j - i)))
      (windowsep.unitLe_bpow hN i)
      (step y i hy) (step x (j - i) hx))

/-- The mixed fold's magnitude at the radius: the key count against
the radius' own power, cleared. -/
private theorem geo_mag {x y N D : BPair}
    (hx : windowsep.mag x * D ≤ N) (hy : windowsep.mag y * D ≤ N)
    (hD : BPair.unit ≤ D) (j : Nat) :
    windowsep.mag (geoSum x y (j + 1)) * ground.bpow D j
      ≤ BPair.ofNat (j + 1) * ground.bpow N j := by
  have hcap := windowsep.mag_famFold_le
    (fun i => ground.bpow y i * ground.bpow x (j + 1 - 1 - i))
    (List.range (j + 1))
  have hnn : BPair.unit ≤ ground.famFold BPair.add BPair.unit
      (fun i => windowsep.mag
        (ground.bpow y i * ground.bpow x (j + 1 - 1 - i)))
      (List.range (j + 1)) :=
    ground.foldB_nonneg _ (List.range (j + 1))
      (fun i _ => windowsep.unitLe_mag _)
  refine ground.leB_trans
    (ground.leB_mul_mono (windowsep.unitLe_bpow hD j) hnn hcap
      (ground.leB_refl (ground.bpow D j))) ?_
  refine ground.leB_congr_left
    (BPair.oneValue_symm (foldB_mul_right (ground.bpow D j)
      (fun i => windowsep.mag
        (ground.bpow y i * ground.bpow x (j + 1 - 1 - i)))
      (List.range (j + 1)))) ?_
  refine ground.leB_trans
    (ground.bsum_le _ (fun _ => ground.bpow N j) (List.range (j + 1))
      (fun i hi => geo_term hx hy hD
        (Nat.le_of_lt_succ (ground.ltOfMem hi)))) ?_
  refine ground.leB_congr_right ?_ (ground.leB_refl _)
  refine BPair.oneValue_trans
    (foldB_const (ground.bpow N j) (List.range (j + 1))) ?_
  rw [ground.length_range (j + 1)]
  exact BPair.oneValue_refl _

/-- The difference of the two evaluations factors through the
points' gap: the coefficients against the mixed monomial folds. -/
private theorem eval_diff (p : Poly) (x y : BPair) :
    (poly.eval p y + (poly.eval p x).swap).oneValue
      ((y + x.swap) * ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k * geoSum x y k)
        (List.range p.length)) := by
  refine BPair.oneValue_trans
    (BPair.add_congr (poly.eval_famFold p y)
      (ground.swap_congr (poly.eval_famFold p x))) ?_
  rw [← ground.fold_swap
    (fun k => ground.getAt BPair.unit p k * ground.bpow x k)
    (List.range p.length)]
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_add
      (fun k => ground.getAt BPair.unit p k * ground.bpow y k)
      (fun k => (ground.getAt BPair.unit p k * ground.bpow x k).swap)
      (List.range p.length))) ?_
  refine BPair.oneValue_trans ?_
    (ground.foldB_mul_left (y + x.swap)
      (fun k => ground.getAt BPair.unit p k * geoSum x y k)
      (List.range p.length))
  refine ground.foldB_congr_members _ _ (List.range p.length)
    (fun k _ => ?_)
  show (ground.getAt BPair.unit p k * ground.bpow y k
      + (ground.getAt BPair.unit p k * ground.bpow x k).swap).oneValue
    ((y + x.swap) * (ground.getAt BPair.unit p k * geoSum x y k))
  rw [← BPair.mul_swap (ground.getAt BPair.unit p k) (ground.bpow x k),
    ← BPair.left_distrib (ground.getAt BPair.unit p k)
      (ground.bpow y k) ((ground.bpow x k).swap),
    BPair.mul_left_comm (y + x.swap) (ground.getAt BPair.unit p k)
      (geoSum x y k)]
  exact BPair.mul_congr (BPair.oneValue_refl _) (geo_read x y k)

/-- A key below a count sits at or below the count's predecessor. -/
private theorem le_pred_of_lt : ∀ {j L : Nat}, j < L → j ≤ L - 1
  | j, 0, h => absurd h (Nat.not_lt_zero j)
  | _, _ + 1, h => Nat.le_of_lt_succ h

/-- The four-factor product's exchange at the two middle
factors. -/
private theorem mul4_shuffle (a b c d : BPair) :
    a * b * (c * d) = a * c * b * d := by
  rw [BPair.mul_mul_mul_comm a b c d, BPair.mul_assoc (a * c) b d]

/-- One key's priced term: the coefficient against the mixed fold,
cleared, sits under the derivative's own coefficient at the radius. -/
private theorem price_term {p r : Poly} {x y N D : BPair}
    (hx : windowsep.mag x * D ≤ N) (hy : windowsep.mag y * D ≤ N)
    (hD : BPair.unit ≤ D) (hN : BPair.unit ≤ N)
    (hr : ∀ j, (ground.getAt BPair.unit r j).oneValue
      (BPair.ofNat (j + 1) * ground.getAt BPair.unit p (j + 1)))
    (j : Nat) :
    windowsep.mag (ground.getAt BPair.unit p (j + 1)
          * geoSum x y (j + 1))
        * ground.bpow D (r.length - 1)
      ≤ windowsep.mag (ground.getAt BPair.unit r j) * ground.bpow N j
          * ground.bpow D (r.length - 1 - j) := by
  have hm : (windowsep.mag (ground.getAt BPair.unit r j)).oneValue
      (BPair.ofNat (j + 1)
        * windowsep.mag (ground.getAt BPair.unit p (j + 1))) :=
    BPair.oneValue_trans (windowsep.mag_congr (hr j))
      (BPair.oneValue_trans
        (windowsep.mag_mul (BPair.ofNat (j + 1))
          (ground.getAt BPair.unit p (j + 1)))
        (BPair.mul_congr
          (BPair.oneValue_of_eq
            (windowsep.mag_unitLe (ground.unitLeOfNat (j + 1))))
          (BPair.oneValue_refl _)))
  by_cases hj : j < r.length
  · have he : j + (r.length - 1 - j) = r.length - 1 :=
      ground.natAddSubCancel (le_pred_of_lt hj)
    have hsplit : (ground.bpow D (r.length - 1)).oneValue
        (ground.bpow D j * ground.bpow D (r.length - 1 - j)) :=
      BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg (ground.bpow D) he.symm))
        (ground.bpow_add D j (r.length - 1 - j))
    have hA : (windowsep.mag (ground.getAt BPair.unit p (j + 1)
            * geoSum x y (j + 1))
          * ground.bpow D (r.length - 1)).oneValue
        (windowsep.mag (geoSum x y (j + 1)) * ground.bpow D j
          * (windowsep.mag (ground.getAt BPair.unit p (j + 1))
              * ground.bpow D (r.length - 1 - j))) :=
      BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (windowsep.mag_mul (ground.getAt BPair.unit p (j + 1))
              (geoSum x y (j + 1)))
            (BPair.oneValue_of_eq
              (BPair.mul_comm
                (windowsep.mag (ground.getAt BPair.unit p (j + 1)))
                (windowsep.mag (geoSum x y (j + 1))))))
          hsplit)
        (BPair.oneValue_of_eq
          (BPair.mul_mul_mul_comm
            (windowsep.mag (geoSum x y (j + 1)))
            (windowsep.mag (ground.getAt BPair.unit p (j + 1)))
            (ground.bpow D j) (ground.bpow D (r.length - 1 - j))))
    have hB : (BPair.ofNat (j + 1) * ground.bpow N j
          * (windowsep.mag (ground.getAt BPair.unit p (j + 1))
              * ground.bpow D (r.length - 1 - j))).oneValue
        (windowsep.mag (ground.getAt BPair.unit r j) * ground.bpow N j
          * ground.bpow D (r.length - 1 - j)) := by
      rw [mul4_shuffle (BPair.ofNat (j + 1)) (ground.bpow N j)
        (windowsep.mag (ground.getAt BPair.unit p (j + 1)))
        (ground.bpow D (r.length - 1 - j))]
      exact BPair.mul_congr
        (BPair.mul_congr (BPair.oneValue_symm hm)
          (BPair.oneValue_refl _))
        (BPair.oneValue_refl _)
    exact ground.leB_congr (BPair.oneValue_symm hA) hB
      (ground.leB_mul_mono
        (ground.unitLeMul (windowsep.unitLe_mag _)
          (windowsep.unitLe_bpow hD (r.length - 1 - j)))
        (ground.unitLeMul (ground.unitLeOfNat (j + 1))
          (windowsep.unitLe_bpow hN j))
        (geo_mag hx hy hD j) (ground.leB_refl _))
  · have h0 : ground.getAt BPair.unit r j = BPair.unit :=
      ground.getAt_over BPair.unit r j (Nat.le_of_not_lt hj)
    have hm0 : BPair.unit.oneValue
        (BPair.ofNat (j + 1)
          * windowsep.mag (ground.getAt BPair.unit p (j + 1))) := by
      rw [h0, windowsep.mag_unitLe (ground.leB_refl BPair.unit)] at hm
      exact hm
    have hq : (windowsep.mag
        (ground.getAt BPair.unit p (j + 1))).oneValue BPair.unit := by
      refine ground.mulCancel
        (ground.offOfUnitLt (ground.unitLtOfPos (ground.posOfSucc j))) ?_
      exact BPair.oneValue_trans (BPair.oneValue_symm hm0)
        (BPair.oneValue_symm (BPair.mul_unit (BPair.ofNat (j + 1))))
    have hL : (windowsep.mag (ground.getAt BPair.unit p (j + 1)
            * geoSum x y (j + 1))
          * ground.bpow D (r.length - 1)).oneValue BPair.unit :=
      BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (windowsep.mag_mul (ground.getAt BPair.unit p (j + 1))
              (geoSum x y (j + 1)))
            (BPair.mul_congr hq (BPair.oneValue_refl _)))
          (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.unit_mul _) (BPair.oneValue_refl _))
          (BPair.unit_mul _))
    have hR : (windowsep.mag (ground.getAt BPair.unit r j)
          * ground.bpow N j
          * ground.bpow D (r.length - 1 - j)).oneValue BPair.unit := by
      rw [h0, windowsep.mag_unitLe (ground.leB_refl BPair.unit)]
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.unit_mul _) (BPair.oneValue_refl _))
        (BPair.unit_mul _)
    exact ground.leB_congr (BPair.oneValue_symm hL)
      (BPair.oneValue_symm hR) (ground.leB_refl BPair.unit)

/-- The collected price: the coefficients' mixed folds, cleared at
the derivative's own power, sit under the derivative's coefficient
fold at the radius. -/
private theorem fold_price {p r : Poly} {x y N D : BPair}
    (hx : windowsep.mag x * D ≤ N) (hy : windowsep.mag y * D ≤ N)
    (hD : BPair.unit ≤ D) (hN : BPair.unit ≤ N)
    (hr : ∀ j, (ground.getAt BPair.unit r j).oneValue
      (BPair.ofNat (j + 1) * ground.getAt BPair.unit p (j + 1))) :
    windowsep.mag (ground.famFold BPair.add BPair.unit
          (fun k => ground.getAt BPair.unit p k * geoSum x y k)
          (List.range p.length))
        * ground.bpow D (r.length - 1)
      ≤ ground.famFold BPair.add BPair.unit
          (fun i => windowsep.mag (ground.getAt BPair.unit r i)
            * ground.bpow N i * ground.bpow D (r.length - 1 - i))
          (List.range r.length) := by
  have hMvan : ∀ j, p.length ≤ j →
      (windowsep.mag (ground.getAt BPair.unit p j * geoSum x y j)
        * ground.bpow D (r.length - 1)).oneValue BPair.unit := by
    intro j hj
    rw [ground.getAt_over BPair.unit p j hj]
    exact BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_trans
          (windowsep.mag_congr (BPair.unit_mul (geoSum x y j)))
          (BPair.oneValue_of_eq
            (windowsep.mag_unitLe (ground.leB_refl BPair.unit))))
        (BPair.oneValue_refl _))
      (BPair.unit_mul _)
  have hUvan : ∀ j, r.length ≤ j →
      (windowsep.mag (ground.getAt BPair.unit r j) * ground.bpow N j
        * ground.bpow D (r.length - 1 - j)).oneValue BPair.unit := by
    intro j hj
    rw [ground.getAt_over BPair.unit r j hj,
      windowsep.mag_unitLe (ground.leB_refl BPair.unit)]
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.unit_mul _) (BPair.oneValue_refl _))
      (BPair.unit_mul _)
  have h1 := windowsep.mag_famFold_le
    (fun k => ground.getAt BPair.unit p k * geoSum x y k)
    (List.range p.length)
  have hnn : BPair.unit ≤ ground.famFold BPair.add BPair.unit
      (fun k => windowsep.mag
        (ground.getAt BPair.unit p k * geoSum x y k))
      (List.range p.length) :=
    ground.foldB_nonneg _ (List.range p.length)
      (fun _ _ => windowsep.unitLe_mag _)
  have h2 := ground.leB_mul_mono
    (windowsep.unitLe_bpow hD (r.length - 1)) hnn h1
    (ground.leB_refl (ground.bpow D (r.length - 1)))
  have h3 := foldB_mul_right (ground.bpow D (r.length - 1))
    (fun k => windowsep.mag
      (ground.getAt BPair.unit p k * geoSum x y k))
    (List.range p.length)
  have h4 := foldB_range_vanish
    (fun k => windowsep.mag
        (ground.getAt BPair.unit p k * geoSum x y k)
      * ground.bpow D (r.length - 1))
    p.length hMvan (r.length + 1)
  have h5 := ground.foldB_range_cons
    (fun k => windowsep.mag
        (ground.getAt BPair.unit p k * geoSum x y k)
      * ground.bpow D (r.length - 1))
    (p.length + r.length)
  have h6 : (windowsep.mag
        (ground.getAt BPair.unit p 0 * geoSum x y 0)
      * ground.bpow D (r.length - 1)).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_trans
          (windowsep.mag_congr
            (BPair.mul_unit (ground.getAt BPair.unit p 0)))
          (BPair.oneValue_of_eq
            (windowsep.mag_unitLe (ground.leB_refl BPair.unit))))
        (BPair.oneValue_refl _))
      (BPair.unit_mul _)
  have h7 := ground.bsum_le
    (fun j => windowsep.mag
        (ground.getAt BPair.unit p (j + 1) * geoSum x y (j + 1))
      * ground.bpow D (r.length - 1))
    (fun i => windowsep.mag (ground.getAt BPair.unit r i)
      * ground.bpow N i * ground.bpow D (r.length - 1 - i))
    (List.range (p.length + r.length))
    (fun j _ => price_term hx hy hD hN hr j)
  have h9 := foldB_range_vanish
    (fun i => windowsep.mag (ground.getAt BPair.unit r i)
      * ground.bpow N i * ground.bpow D (r.length - 1 - i))
    r.length hUvan p.length
  refine ground.leB_trans h2 ?_
  refine ground.leB_congr_left (BPair.oneValue_symm h3) ?_
  refine ground.leB_congr_left h4 ?_
  refine ground.leB_congr_left (BPair.oneValue_of_eq h5.symm) ?_
  refine ground.leB_congr_left
    (BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr h6 (BPair.oneValue_refl _))
        (BPair.unit_add _))) ?_
  refine ground.leB_trans h7 ?_
  rw [Nat.add_comm p.length r.length]
  exact ground.leB_congr_left (BPair.oneValue_symm h9)
    (ground.leB_refl _)

/-- The image-width price at a stated bound: two values of a
polynomial at points inside the bound's segment differ by at most
the points' gap against the derivative's coefficient fold at the
bound, cleared at the fold's power; the radius pair is the bound's
own instance. -/
theorem eval_gap_le (p : Poly) (x y N D : BPair)
    (hD : BPair.unit ≤ D)
    (hx : windowsep.mag x * D ≤ N) (hy : windowsep.mag y * D ≤ N)
    (hxy : x ≤ y) :
    windowsep.mag (poly.eval p y + (poly.eval p x).swap)
        * ground.bpow D ((poly.vnorm (poly.deriv p)).length - 1)
      ≤ windowsep.magFold (poly.deriv p) N D * (y + x.swap) := by
  have hN : BPair.unit ≤ N :=
    ground.leB_trans (ground.unitLeMul (windowsep.unitLe_mag x) hD) hx
  have hS : BPair.unit ≤ y + x.swap := ground.leB_unit_add hxy
  have hr : ∀ j, (ground.getAt BPair.unit
        (poly.vnorm (poly.deriv p)) j).oneValue
      (BPair.ofNat (j + 1) * ground.getAt BPair.unit p (j + 1)) :=
    fun j => BPair.oneValue_trans
      (poly.oneValue_getAt j (poly.vnorm_ov (poly.deriv p)))
      (deriv_getAt p j)
  have hcore := fold_price (p := p) (r := poly.vnorm (poly.deriv p))
    hx hy hD hN hr
  have hfold := BPair.oneValue_symm
    (windowsep.magFold_read (poly.deriv p) N D)
  have hA : (windowsep.mag
        (poly.eval p y + (poly.eval p x).swap)).oneValue
      ((y + x.swap) * windowsep.mag (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k * geoSum x y k)
        (List.range p.length))) :=
    BPair.oneValue_trans (windowsep.mag_congr (eval_diff p x y))
      (BPair.oneValue_trans
        (windowsep.mag_mul (y + x.swap) _)
        (BPair.mul_congr
          (BPair.oneValue_of_eq (windowsep.mag_unitLe hS))
          (BPair.oneValue_refl _)))
  refine ground.leB_congr_left
    (BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.mul_congr hA (BPair.oneValue_refl _))
        (BPair.oneValue_of_eq
          (BPair.mul_assoc (y + x.swap) _
            (ground.bpow D
              ((poly.vnorm (poly.deriv p)).length - 1)))))) ?_
  exact ground.leB_congr_right
    (BPair.oneValue_of_eq
      (BPair.mul_comm (y + x.swap)
        (windowsep.magFold (poly.deriv p) N D)))
    (ground.leB_mulR hS (ground.leB_congr_right hfold hcore))

/-- A point of the bracket sits inside the stated bound's segment,
its magnitude at one of the endpoints'. -/
private theorem inSeg {a b x N D : BPair} (hD : BPair.unit ≤ D)
    (ha : windowsep.mag a * D ≤ N) (hb : windowsep.mag b * D ≤ N)
    (hax : a ≤ x) (hxb : x ≤ b) : windowsep.mag x * D ≤ N := by
  by_cases hu : BPair.unit ≤ x
  · refine ground.leB_trans ?_ hb
    refine ground.leB_mul_mono hD (windowsep.unitLe_mag b) ?_
      (ground.leB_refl D)
    rw [windowsep.mag_unitLe hu]
    exact ground.leB_trans hxb (windowsep.le_mag b)
  · have hlt : x < BPair.unit :=
      if hc : x < BPair.unit then hc
      else absurd (ground.leB_of_not_lt hc) hu
    have hsw : windowsep.mag x = x.swap := by
      rw [← windowsep.mag_swap x]
      exact windowsep.mag_unitLe
        (ground.leB_of_lt (ground.ltB_swap hlt))
    refine ground.leB_trans ?_ ha
    refine ground.leB_mul_mono hD (windowsep.unitLe_mag a) ?_
      (ground.leB_refl D)
    rw [hsw]
    exact ground.leB_trans (ground.leB_swap hax) (windowsep.swap_le_mag a)

/-- A value joined to its own gap against a second value reads that
second value. -/
private theorem joinDiff (u v : BPair) : (u + (v + u.swap)).oneValue v := by
  rw [BPair.add_comm v u.swap, ← BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm u u.swap))
        (BPair.swap_add_null (BPair.oneValue_refl u)))
      (BPair.oneValue_refl v))
    (BPair.unit_add v)

/-- The priced close at the integer carrier: a gap capped by a width
that the endpoint's value clears keeps the value's side. -/
private theorem sideClose {Δ QA QX G F Wx Wb DL : BPair}
    (hjoin : (QA + Δ).oneValue QX)
    (hDL : BPair.unit < DL)
    (hgap : windowsep.mag Δ * DL ≤ G * F * Wx)
    (hwid : G * F * Wx ≤ G * F * Wb)
    (hpr : G * F * Wb < QA * DL) :
    BPair.unit < QX := by
  have hstrict : windowsep.mag Δ < QA :=
    ltB_unscale hDL
      (ground.leB_ltB_trans (ground.leB_trans hgap hwid) hpr)
  have hswlt : Δ.swap < QA :=
    ground.leB_ltB_trans (windowsep.swap_le_mag Δ) hstrict
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit) hjoin
    (ground.unitLt_of_swap_lt hswlt)

/-- The priced close at the integer carrier read at the upper
endpoint: a gap capped by a width that the upper endpoint's value
clears on the lower side keeps the interior value's lower side. -/
private theorem sideClose_top {Δ QB QX G F Wx Wb DL : BPair}
    (hjoin : (QX + Δ).oneValue QB)
    (hDL : BPair.unit < DL)
    (hgap : windowsep.mag Δ * DL ≤ G * F * Wx)
    (hwid : G * F * Wx ≤ G * F * Wb)
    (hpr : G * F * Wb < QB.swap * DL) :
    QX < BPair.unit := by
  have hstrict : windowsep.mag Δ < QB.swap :=
    ltB_unscale hDL
      (ground.leB_ltB_trans (ground.leB_trans hgap hwid) hpr)
  have hswlt : Δ.swap < QB.swap :=
    ground.leB_ltB_trans (windowsep.swap_le_mag Δ) hstrict
  have hQB : QB < Δ := ground.ltB_swap hswlt
  have hlt2 : QX + Δ < Δ :=
    BPair.lt_congr (BPair.oneValue_symm hjoin)
      (BPair.oneValue_refl Δ) hQB
  have hnull : (Δ + Δ.swap).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm Δ Δ.swap))
      (BPair.swap_add_null (BPair.oneValue_refl Δ))
  refine BPair.lt_congr ?_ hnull
    (ground.ltB_add hlt2 (ground.leB_refl Δ.swap))
  exact BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc QX Δ Δ.swap))
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl QX) hnull)
      (BPair.add_unit QX))

/-! The representative's key count against the derivative's: a key
at or beyond the count reads the sum's unit, the top key's own sits
off it, and the derivative's count drops by at most one. -/

/-- A key at or beyond the representative's count reads the sum's
unit. -/
private theorem vnorm_len_unit {Q : Poly} {k : Nat}
    (h : (poly.vnorm Q).length ≤ k) :
    (ground.getAt BPair.unit Q k).oneValue BPair.unit := by
  have h1 := poly.oneValue_getAt k (poly.vnorm_ov Q)
  rw [ground.getAt_over BPair.unit (poly.vnorm Q) k h] at h1
  exact BPair.oneValue_symm h1

/-- The representative's top key carries a coefficient off the sum's
unit. -/
private theorem vnorm_len_off {Q : Poly} {m : Nat}
    (hlen : (poly.vnorm Q).length = m + 1) :
    ¬ (ground.getAt BPair.unit Q m).oneValue BPair.unit := by
  intro hu
  have hnot : ¬ poly.unitTail Q := by
    intro hut
    rw [poly.vnorm_congr
      (poly.unitTail_oneValue (q := ([] : Poly)) hut trivial)] at hlen
    exact Nat.noConfusion (show (0 : Nat) = m + 1 from hlen)
  refine poly.vnorm_top hnot ?_
  show (poly.topO ground.bpairOps (poly.vnorm Q)).oneValue BPair.unit
  rw [poly.topO_getAt ground.bpairOps (poly.vnorm Q) m hlen]
  exact BPair.oneValue_trans
    (poly.oneValue_getAt m (poly.vnorm_ov Q)) hu

/-- The derivative's representative reaches the key below the
list's top: the top key's coefficient enters against its own
count. -/
private theorem vnormLen_step (p : Poly) (i : Nat)
    (hn : (poly.vnorm p).length = i + 2) :
    i + 1 ≤ (poly.vnorm (poly.deriv p)).length := by
  match Nat.lt_or_ge (poly.vnorm (poly.deriv p)).length (i + 1) with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    exfalso
    have h0 := vnorm_len_unit (Q := poly.deriv p) (Nat.le_of_lt_succ hlt)
    have h2 : (BPair.ofNat (i + 1)
        * ground.getAt BPair.unit p (i + 1)).oneValue BPair.unit :=
      BPair.oneValue_trans (BPair.oneValue_symm (deriv_getAt p i)) h0
    match (BPair.mul_unit_iff (BPair.ofNat (i + 1))
        (ground.getAt BPair.unit p (i + 1))).mp h2 with
    | Or.inl hA => exact BPair.ofNat_off_unit (i + 1) (Nat.succ_pos i) hA
    | Or.inr hB => exact vnorm_len_off (m := i + 1) hn hB

/-- The representative's key count sits inside the derivative's own
count joined to two. -/
private theorem vnormLen_bound (p : Poly) :
    (poly.vnorm p).length
      ≤ (poly.vnorm (poly.deriv p)).length - 1 + 2 := by
  refine Or.elim (Nat.lt_or_ge (poly.vnorm p).length 2)
    (fun hlt => ?_) (fun hge => ?_)
  · exact Nat.le_trans (Nat.le_of_lt_succ hlt)
      (Nat.succ_le_succ (Nat.zero_le _))
  · have hn : (poly.vnorm p).length = (poly.vnorm p).length - 2 + 2 := by
      rw [Nat.add_comm ((poly.vnorm p).length - 2) 2]
      exact (ground.natAddSubCancel hge).symm
    refine Nat.le_trans (Nat.le_of_eq hn) ?_
    have hstep := vnormLen_step p ((poly.vnorm p).length - 2) hn
    exact Nat.add_le_add_right (Nat.sub_le_sub_right hstep 1) 2

/-- The composite value at a rescaled representative: the cleared
list's Horner read at the scaled numerator against the clearing's
power. -/
private theorem evalC_cleared (p : Poly) (z : CPair) (cc : Pos) (L : Nat)
    (zN : BPair) (hVlen : (poly.vnorm p).length ≤ L + 2)
    (hZv : z.oneValue ⟨zN, cc⟩) :
    (evalC p z).oneValue
      ⟨poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) zN,
        ground.Pos.pow cc (L + 1)⟩ :=
  CPair.oneValue_trans (evalC_point_congr p hZv)
    (CPair.oneValue_trans
      (CPair.oneValue_symm (evalC_congr (poly.vnorm_ov p) ⟨zN, cc⟩))
      (evalC_read (poly.vnorm p) (L + 1) hVlen zN cc))

/-- The composite price at a common clearing: the certificate's
strict read cross-multiplies to the scaled numerators against the
clearing's power. -/
private theorem price_cleared (p : Poly) (a b : CPair) (N D : BPair)
    (cc : Pos) (L : Nat) (aN bN : BPair) (V : CPair) (VN : BPair)
    (hAv : a.oneValue ⟨aN, cc⟩) (hBv : b.oneValue ⟨bN, cc⟩)
    (hV : V.oneValue ⟨VN, ground.Pos.pow cc (L + 1)⟩)
    (hpr : ofB (windowsep.magFold (poly.deriv p) N D) * (b + CPair.swap a)
      < V * ofB (ground.bpow D L)) :
    ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)
      < VN * ground.bpow D L := by
  have hL2 : (ofB (windowsep.magFold (poly.deriv p) N D)
      * (b + CPair.swap a)).oneValue
      (⟨windowsep.magFold (poly.deriv p) N D * (bN + aN.swap),
        cc⟩ : CPair) :=
    CPair.oneValue_trans
      (CPair.mul_congr
        (CPair.oneValue_refl (ofB (windowsep.magFold (poly.deriv p) N D)))
        (CPair.oneValue_trans
          (CPair.add_congr hBv (CPair.swap_congr hAv))
          (addC_same bN aN.swap cc)))
      (denC_eq (ground.one_mul cc))
  have hR2 : (V * ofB (ground.bpow D L)).oneValue
      (⟨VN * ground.bpow D L, ground.Pos.pow cc (L + 1)⟩ : CPair) :=
    CPair.oneValue_trans
      (CPair.mul_congr hV
        (CPair.oneValue_refl (ofB (ground.bpow D L))))
      (denC_eq (ground.mul_one (ground.Pos.pow cc (L + 1))))
  have hpr2 := cltNum (CPair.lt_congr hL2 hR2 hpr)
  have e1 : BPair.ofPos cc * ground.bpow (BPair.ofPos cc) L
        * (windowsep.magFold (poly.deriv p) N D * (bN + aN.swap))
      = BPair.ofPos cc * (ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)) := by
    rw [BPair.mul_assoc (BPair.ofPos cc) (ground.bpow (BPair.ofPos cc) L)
        (windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)),
      BPair.mul_assoc (ground.bpow (BPair.ofPos cc) L)
        (windowsep.magFold (poly.deriv p) N D) (bN + aN.swap)]
  refine BPair.lt_of_scale_lt (w := cc) ?_
  refine BPair.lt_congr ?_ (BPair.oneValue_refl _) hpr2
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofPos_scale (ground.Pos.pow cc (L + 1))
      (windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)))) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr
      (BPair.oneValue_trans (ground.ofPos_pow cc (L + 1))
        (BPair.norm_oneValue
          (BPair.ofPos cc * ground.bpow (BPair.ofPos cc) L)))
      (BPair.oneValue_refl
        (windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)))) ?_
  rw [e1]
  exact BPair.ofPos_scale cc _

/-- The cleared list's derivative reads: the representative's
length is the derivative's own, and its coefficient fold at the
scaled bound is the clearing's power against the derivative's
fold. -/
private theorem derivClear_reads (p : Poly) (N D : BPair) (cc : Pos)
    (L : Nat) (hL : L = (poly.vnorm (poly.deriv p)).length - 1) :
    (poly.vnorm
        (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))).length
      = (poly.vnorm (poly.deriv p)).length
    ∧ (windowsep.magFold
        (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))
        (N * BPair.ofPos cc) D).oneValue
        (ground.bpow (BPair.ofPos cc) L
          * windowsep.magFold (poly.deriv p) N D) := by
  have hdv : poly.oneValue (poly.deriv (poly.vnorm p))
      (poly.vnorm (poly.deriv p)) := by
    rw [← poly.vnorm_congr (poly.deriv_congr (poly.vnorm_ov p))]
    exact poly.oneValue_symm (poly.vnorm_ov (poly.deriv (poly.vnorm p)))
  have hdq : poly.oneValue
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))
      (poly.clearVar (poly.vnorm (poly.deriv p)) cc L) :=
    poly.oneValue_trans
      (poly.deriv_clearVar (poly.vnorm p) cc (L + 1))
      (poly.clearVar_congr hdv cc L)
  have hvq : poly.vnorm
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))
      = poly.clearVar (poly.vnorm (poly.deriv p)) cc L :=
    (poly.vnorm_congr hdq).trans
      (poly.vnorm_clearVar (poly.deriv p) cc L)
  have hlenq : (poly.vnorm
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))).length
      = (poly.vnorm (poly.deriv p)).length := by
    rw [hvq, poly.length_clearVar]
  have hfold : (windowsep.magFold
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))
      (N * BPair.ofPos cc) D).oneValue
      (ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D) := by
    rw [windowsep.magFold_congr hdq (N * BPair.ofPos cc) D, hL]
    exact windowsep.magFold_clearVar (poly.deriv p) cc N D
  exact ⟨hlenq, hfold⟩

/-- The cleared engine's close at a common clearing: with the
bracket's points read as scaled numerators at one second datum and
the width priced under the lower endpoint's value, the cleared
list's value stands above the sum's unit at the interior point. -/
private theorem cleared_close (p : Poly) (N D : BPair) (cc : Pos)
    (L : Nat) (aN bN xN : BPair)
    (hL : L = (poly.vnorm (poly.deriv p)).length - 1)
    (hDlt : BPair.unit < D)
    (hqa : windowsep.mag aN * D ≤ N * BPair.ofPos cc)
    (hqb : windowsep.mag bN * D ≤ N * BPair.ofPos cc)
    (hax : aN ≤ xN) (hxb : xN ≤ bN)
    (hpr : ground.bpow (BPair.ofPos cc) L
          * windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)
        < poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) aN
          * ground.bpow D L) :
    BPair.unit
      < poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) xN := by
  have hD : BPair.unit ≤ D := ground.leB_of_lt hDlt
  have hccU : BPair.unit ≤ BPair.ofPos cc :=
    ground.leB_of_lt (ground.unitLtOfPos cc)
  have hNc : BPair.unit ≤ N * BPair.ofPos cc :=
    ground.leB_trans (ground.unitLeMul (windowsep.unitLe_mag aN) hD) hqa
  have hN : BPair.unit ≤ N :=
    ground.leB_unscale (ground.unitLtOfPos cc)
      (ground.leB_congr_left
        (BPair.oneValue_symm (BPair.unit_mul (BPair.ofPos cc))) hNc)
  have hqx : windowsep.mag xN * D ≤ N * BPair.ofPos cc :=
    inSeg hD hqa hqb hax hxb
  have hlenq : (poly.vnorm
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))).length
      = (poly.vnorm (poly.deriv p)).length :=
    (derivClear_reads p N D cc L hL).1
  have hfold : (windowsep.magFold
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))
      (N * BPair.ofPos cc) D).oneValue
      (ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D) :=
    (derivClear_reads p N D cc L hL).2
  have hgap := eval_gap_le (poly.clearVar (poly.vnorm p) cc (L + 1))
    aN xN (N * BPair.ofPos cc) D hD hqa hqx hax
  rw [hlenq, ← hL] at hgap
  have hgapT := ground.leB_congr_right
    (BPair.mul_congr hfold (BPair.oneValue_refl (xN + aN.swap))) hgap
  have hwid : ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D * (xN + aN.swap)
      ≤ ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D * (bN + aN.swap) :=
    ground.leB_mulR
      (ground.unitLeMul (windowsep.unitLe_bpow hccU L)
        (windowsep.unitLe_magFold (poly.deriv p) hN hD))
      (ground.leB_add hxb (ground.leB_refl aN.swap))
  exact sideClose
    (joinDiff (poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) aN)
      (poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) xN))
    (windowsep.unitLt_bpow hDlt L) hgapT hwid hpr

/-- The cleared engine's close at a common clearing read at the
upper endpoint: with the bracket's points read as scaled numerators
at one second datum and the width priced under the upper endpoint's
value on the lower side, the cleared list's value stands below the
sum's unit at the interior point. -/
private theorem cleared_close_top (p : Poly) (N D : BPair) (cc : Pos)
    (L : Nat) (aN bN xN : BPair)
    (hL : L = (poly.vnorm (poly.deriv p)).length - 1)
    (hDlt : BPair.unit < D)
    (hqa : windowsep.mag aN * D ≤ N * BPair.ofPos cc)
    (hqb : windowsep.mag bN * D ≤ N * BPair.ofPos cc)
    (hax : aN ≤ xN) (hxb : xN ≤ bN)
    (hpr : ground.bpow (BPair.ofPos cc) L
          * windowsep.magFold (poly.deriv p) N D * (bN + aN.swap)
        < (poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) bN).swap
          * ground.bpow D L) :
    poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) xN
      < BPair.unit := by
  have hD : BPair.unit ≤ D := ground.leB_of_lt hDlt
  have hccU : BPair.unit ≤ BPair.ofPos cc :=
    ground.leB_of_lt (ground.unitLtOfPos cc)
  have hNc : BPair.unit ≤ N * BPair.ofPos cc :=
    ground.leB_trans (ground.unitLeMul (windowsep.unitLe_mag aN) hD) hqa
  have hN : BPair.unit ≤ N :=
    ground.leB_unscale (ground.unitLtOfPos cc)
      (ground.leB_congr_left
        (BPair.oneValue_symm (BPair.unit_mul (BPair.ofPos cc))) hNc)
  have hqx : windowsep.mag xN * D ≤ N * BPair.ofPos cc :=
    inSeg hD hqa hqb hax hxb
  have hlenq : (poly.vnorm
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))).length
      = (poly.vnorm (poly.deriv p)).length :=
    (derivClear_reads p N D cc L hL).1
  have hfold : (windowsep.magFold
      (poly.deriv (poly.clearVar (poly.vnorm p) cc (L + 1)))
      (N * BPair.ofPos cc) D).oneValue
      (ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D) :=
    (derivClear_reads p N D cc L hL).2
  have hgap := eval_gap_le (poly.clearVar (poly.vnorm p) cc (L + 1))
    xN bN (N * BPair.ofPos cc) D hD hqx hqb hxb
  rw [hlenq, ← hL] at hgap
  have hgapT := ground.leB_congr_right
    (BPair.mul_congr hfold (BPair.oneValue_refl (bN + xN.swap))) hgap
  have hwid : ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D * (bN + xN.swap)
      ≤ ground.bpow (BPair.ofPos cc) L
        * windowsep.magFold (poly.deriv p) N D * (bN + aN.swap) :=
    ground.leB_mulR
      (ground.unitLeMul (windowsep.unitLe_bpow hccU L)
        (windowsep.unitLe_magFold (poly.deriv p) hN hD))
      (ground.leB_add (ground.leB_refl bN) (ground.leB_swap hax))
  exact sideClose_top
    (joinDiff (poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) xN)
      (poly.eval (poly.clearVar (poly.vnorm p) cc (L + 1)) bN))
    (windowsep.unitLt_bpow hDlt L) hgapT hwid hpr

/-- The value keeps the upper side at every point of the bracket. -/
theorem keepUpper_all (p : Poly) (a b : CPair) (N D : BPair)
    (h : keepUpper p a b N D) (x : CPair)
    (hax : a ≤ x) (hxb : x ≤ b) : unitC < evalC p x := by
  obtain ⟨an, ac⟩ := a
  obtain ⟨bn, bc⟩ := b
  obtain ⟨xn, xc⟩ := x
  have hAv : (⟨an, ac⟩ : CPair).oneValue
      ⟨an.scale (bc * xc), ac * bc * xc⟩ := by
    have hs := CPair.scale_oneValue an ac (bc * xc)
    rw [← ground.mul_assoc ac bc xc] at hs
    exact CPair.oneValue_symm hs
  have hBv : (⟨bn, bc⟩ : CPair).oneValue
      ⟨bn.scale (ac * xc), ac * bc * xc⟩ := by
    have hs := CPair.scale_oneValue bn bc (ac * xc)
    rw [← ground.mul_assoc bc ac xc,
      ground.mul_comm bc ac] at hs
    exact CPair.oneValue_symm hs
  have hXv : (⟨xn, xc⟩ : CPair).oneValue
      ⟨xn.scale (ac * bc), ac * bc * xc⟩ := by
    have hs := CPair.scale_oneValue xn xc (ac * bc)
    rw [ground.mul_comm xc (ac * bc)] at hs
    exact CPair.oneValue_symm hs
  have hax0 := cleNum (le_congr hAv hXv hax)
  have hxb0 := cleNum (le_congr hXv hBv hxb)
  have hqa := boundAt (zn := an) (zc := ac) (bc * xc) (ac * bc * xc)
    (ground.mul_assoc ac bc xc).symm h.2.2.2.1
  have hqb := boundAt (zn := bn) (zc := bc) (ac * xc) (ac * bc * xc)
    (by rw [← ground.mul_assoc bc ac xc,
      ground.mul_comm bc ac]) h.2.2.2.2.1
  have hprT := price_cleared p ⟨an, ac⟩ ⟨bn, bc⟩ N D (ac * bc * xc)
    ((poly.vnorm (poly.deriv p)).length - 1)
    (an.scale (bc * xc)) (bn.scale (ac * xc))
    (evalC p ⟨an, ac⟩) _ hAv hBv
    (evalC_cleared p ⟨an, ac⟩ (ac * bc * xc)
      ((poly.vnorm (poly.deriv p)).length - 1)
      (an.scale (bc * xc)) (vnormLen_bound p) hAv)
    h.2.2.2.2.2
  have hcore := cleared_close p N D (ac * bc * xc)
    ((poly.vnorm (poly.deriv p)).length - 1)
    (an.scale (bc * xc)) (bn.scale (ac * xc))
    (xn.scale (ac * bc)) rfl h.1 hqa hqb
    (ground.leB_of_scale hax0) (ground.leB_of_scale hxb0) hprT
  have hread := evalC_cleared p ⟨xn, xc⟩ (ac * bc * xc)
    ((poly.vnorm (poly.deriv p)).length - 1)
    (xn.scale (ac * bc)) (vnormLen_bound p) hXv
  exact CPair.lt_congr (CPair.oneValue_refl unitC)
    (CPair.oneValue_symm hread) ((unitC_lt_num _ _).mpr hcore)

/-- The value keeps the lower side at every point of the bracket,
the upper read at the memberwise swap. -/
theorem keepLower_all (p : Poly) (a b : CPair) (N D : BPair)
    (h : keepLower p a b N D) (x : CPair)
    (hax : a ≤ x) (hxb : x ≤ b) : evalC p x < unitC := by
  have hdf : windowsep.magFold (poly.deriv (poly.neg p)) N D
      = windowsep.magFold (poly.deriv p) N D := by
    rw [deriv_neg p, windowsep.magFold_neg]
  have hlen : (poly.vnorm (poly.deriv (poly.neg p))).length
      = (poly.vnorm (poly.deriv p)).length := by
    rw [deriv_neg p, poly.vnorm_neg, poly.length_neg]
  have hup : keepUpper (poly.neg p) a b N D := by
    refine And.intro h.1 (And.intro h.2.1 (And.intro ?_
      (And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 ?_))))
    · exact CPair.lt_congr (CPair.oneValue_refl unitC)
        (CPair.oneValue_symm (evalC_neg p a)) (cltSwapC h.2.2.1)
    · rw [hdf, hlen]
      refine CPair.lt_congr (CPair.oneValue_refl _) ?_ h.2.2.2.2.2
      exact CPair.mul_congr
        (CPair.oneValue_symm (evalC_neg p a))
        (CPair.oneValue_refl _)
  have hx := keepUpper_all (poly.neg p) a b N D hup x hax hxb
  exact cltSwapC (u := unitC) (v := CPair.swap (evalC p x))
    (CPair.lt_congr (CPair.oneValue_refl unitC) (evalC_neg p x) hx)

/-- The value keeps the lower side at every point of the bracket,
the same clause read at the upper endpoint. -/
theorem keepLowerTop_all (p : Poly) (a b : CPair) (N D : BPair)
    (h : keepLowerTop p a b N D) (x : CPair)
    (hax : a ≤ x) (hxb : x ≤ b) : evalC p x < unitC := by
  obtain ⟨an, ac⟩ := a
  obtain ⟨bn, bc⟩ := b
  obtain ⟨xn, xc⟩ := x
  have hAv : (⟨an, ac⟩ : CPair).oneValue
      ⟨an.scale (bc * xc), ac * bc * xc⟩ := by
    have hs := CPair.scale_oneValue an ac (bc * xc)
    rw [← ground.mul_assoc ac bc xc] at hs
    exact CPair.oneValue_symm hs
  have hBv : (⟨bn, bc⟩ : CPair).oneValue
      ⟨bn.scale (ac * xc), ac * bc * xc⟩ := by
    have hs := CPair.scale_oneValue bn bc (ac * xc)
    rw [← ground.mul_assoc bc ac xc,
      ground.mul_comm bc ac] at hs
    exact CPair.oneValue_symm hs
  have hXv : (⟨xn, xc⟩ : CPair).oneValue
      ⟨xn.scale (ac * bc), ac * bc * xc⟩ := by
    have hs := CPair.scale_oneValue xn xc (ac * bc)
    rw [ground.mul_comm xc (ac * bc)] at hs
    exact CPair.oneValue_symm hs
  have hax0 := cleNum (le_congr hAv hXv hax)
  have hxb0 := cleNum (le_congr hXv hBv hxb)
  have hqa := boundAt (zn := an) (zc := ac) (bc * xc) (ac * bc * xc)
    (ground.mul_assoc ac bc xc).symm h.2.2.2.1
  have hqb := boundAt (zn := bn) (zc := bc) (ac * xc) (ac * bc * xc)
    (by rw [← ground.mul_assoc bc ac xc,
      ground.mul_comm bc ac]) h.2.2.2.2.1
  have hprT := price_cleared p ⟨an, ac⟩ ⟨bn, bc⟩ N D (ac * bc * xc)
    ((poly.vnorm (poly.deriv p)).length - 1)
    (an.scale (bc * xc)) (bn.scale (ac * xc))
    (CPair.swap (evalC p ⟨bn, bc⟩)) _ hAv hBv
    (CPair.swap_congr (evalC_cleared p ⟨bn, bc⟩ (ac * bc * xc)
      ((poly.vnorm (poly.deriv p)).length - 1)
      (bn.scale (ac * xc)) (vnormLen_bound p) hBv))
    h.2.2.2.2.2
  have hcore := cleared_close_top p N D (ac * bc * xc)
    ((poly.vnorm (poly.deriv p)).length - 1)
    (an.scale (bc * xc)) (bn.scale (ac * xc))
    (xn.scale (ac * bc)) rfl h.1 hqa hqb
    (ground.leB_of_scale hax0) (ground.leB_of_scale hxb0) hprT
  have hread := evalC_cleared p ⟨xn, xc⟩ (ac * bc * xc)
    ((poly.vnorm (poly.deriv p)).length - 1)
    (xn.scale (ac * bc)) (vnormLen_bound p) hXv
  exact CPair.lt_congr (CPair.oneValue_symm hread)
    (CPair.oneValue_refl unitC) (num_lt_unitC _ hcore)

/-- The bracket read keeps the side at every bracket point. -/
theorem sideUpper_all (E : Ext) (p : Poly) (wn wd : Pos)
    (h : sideUpper E p wn wd) (x : CPair)
    (hax : E.lo ≤ x) (hxb : x ≤ E.hi) : unitC < evalC p x :=
  keepUpper_all p E.lo E.hi (windowsep.radiusN (poly.monic E.pol))
    (windowsep.radiusD (poly.monic E.pol)) h.2 x hax hxb

/-- The bracket read keeps the lower side at every bracket point. -/
theorem sideLower_all (E : Ext) (p : Poly) (wn wd : Pos)
    (h : sideLower E p wn wd) (x : CPair)
    (hax : E.lo ≤ x) (hxb : x ≤ E.hi) : evalC p x < unitC :=
  keepLower_all p E.lo E.hi (windowsep.radiusN (poly.monic E.pol))
    (windowsep.radiusD (poly.monic E.pol)) h.2 x hax hxb

end stage
