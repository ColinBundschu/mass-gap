import MassGap.Windowsep
/-!
`def:poly` — the iterated carrier's outer evaluation and its two
derivatives at composite points.  A polynomial over the balance-pair
polynomials (`PPoly`, the inner variable's polynomials the outer
variable's coefficients) reads at an inner composite point through
the cleared inner evaluation (`pevalCP`, Poly's) and at an outer
composite point `[sn : sc]` through the monomial fold cleared at one
stated power (`pevalOuter`, `sc^Ks` times the read, a polynomial in
the inner variable, `def:poly`'s occupancy-family read at the entry
carrier); the two reads meet at a point of both variables
(`pevalOuter_pevalCP`, the one cleared value either way).  The outer
derivative is the successor-weighted shift at the coefficient carrier
(`derivOuter`, `def:poly`'s derivative at the entry carrier), the
inner derivative the coefficientwise one (`derivInner`), and the
inner evaluation reads the outer derivative as the derivative of the
evaluated polynomial (`pevalCP_derivOuter`), the outer evaluation the
inner derivative so (`pevalOuter_derivInner`); the outer derivative
keeps the inner-degree cap (`innerLe_derivOuter`) and the outer
evaluation sits within it (`length_pevalOuter_le`).
-/

namespace poly
open ground

/-- The outer derivative from a stated weight: the successor-weighted
shift at the coefficient carrier. -/
def derivOuterFrom : Pos → PPoly → PPoly
  | _, [] => []
  | n, c :: P => scaleP (BPair.ofPos n) c :: derivOuterFrom (succ n) P

/-- The outer derivative, `def:poly`'s successor-weighted shift at
the polynomial entry carrier. -/
def derivOuter : PPoly → PPoly
  | [] => []
  | _ :: P => derivOuterFrom .one P

/-- The inner derivative, coefficientwise. -/
def derivInner (P : PPoly) : PPoly := P.map deriv

/-- The evaluated shift from a weight reads the shift of the
evaluations. -/
private theorem pevalCP_derivOuterFrom (tn : BPair) (tc : Pos) (Kt : Nat) :
    ∀ (n : Pos) (P : PPoly),
    oneValue (pevalCP (derivOuterFrom n P) tn tc Kt)
      (derivFrom n (pevalCP P tn tc Kt))
  | _, [] => trivial
  | n, c :: P =>
    ⟨BPair.oneValue_trans (evalClear_scaleP (BPair.ofPos n) c tn tc Kt)
      (BPair.ofPos_scale n (evalClear c tn tc Kt)),
     pevalCP_derivOuterFrom tn tc Kt (succ n) P⟩

/-- The inner evaluation reads the outer derivative as the
evaluated polynomial's derivative. -/
theorem pevalCP_derivOuter (P : PPoly) (tn : BPair) (tc : Pos) (Kt : Nat) :
    oneValue (pevalCP (derivOuter P) tn tc Kt)
      (deriv (pevalCP P tn tc Kt)) := by
  match P with
  | [] => exact trivial
  | _ :: P => exact pevalCP_derivOuterFrom tn tc Kt .one P

/-- The shifted outer derivative keeps the inner-degree cap. -/
private theorem innerLe_derivOuterFrom {Kt : Nat} : ∀ (n : Pos) {P : PPoly},
    innerLe P Kt → innerLe (derivOuterFrom n P) Kt
  | _, [], _ => rfl
  | n, c :: P, h => by
    show (Nat.ble (scaleP (BPair.ofPos n) c).length (Kt + 1)
      && (derivOuterFrom (succ n) P).all
        (fun c => Nat.ble c.length (Kt + 1))) = true
    rw [length_scaleP]
    exact ground.andIntroB (Nat.ble_eq_true_of_le (innerLe_head h))
      (innerLe_derivOuterFrom (succ n) (innerLe_tail h))

/-- The outer derivative keeps the inner-degree cap. -/
theorem innerLe_derivOuter {P : PPoly} {Kt : Nat} (h : innerLe P Kt) :
    innerLe (derivOuter P) Kt :=
  match P, h with
  | [], _ => rfl
  | _ :: _, h => innerLe_derivOuterFrom .one (innerLe_tail h)

/-- The inner derivative keeps the key count. -/
theorem length_derivInner (P : PPoly) : (derivInner P).length = P.length :=
  ground.length_map _ P

/-- The successor-weighted shift keeps the key count. -/
theorem length_derivFrom : ∀ (n : Pos) (p : Poly),
    (derivFrom n p).length = p.length
  | _, [] => rfl
  | n, _ :: p => by
    show (derivFrom (succ n) p).length + 1 = p.length + 1
    rw [length_derivFrom (succ n) p]

/-- The derivative's key count sits at or below the polynomial's. -/
theorem length_deriv_le : ∀ p : Poly, (deriv p).length ≤ p.length
  | [] => Nat.le_refl 0
  | _ :: p => by
    show (derivFrom .one p).length ≤ p.length + 1
    rw [length_derivFrom .one p]
    exact Nat.le_succ p.length

/-- The derivative's representative sits inside the polynomial's
key count. -/
theorem vnormDeriv_le (p : Poly) : (vnorm (deriv p)).length ≤ p.length :=
  Nat.le_trans (vnormLen_le _) (length_deriv_le p)

/-- The derivative passes the rescaling: the shifted keys' scaled
coefficients. -/
theorem deriv_scaleP (c : BPair) (q : Poly) :
    oneValue (deriv (scaleP c q)) (scaleP c (deriv q)) := by
  have h1 : oneValue (scaleP c q) (q.map (fun x => c * x)) :=
    oneValue_map _ _ q (fun x _ => BPair.norm_oneValue _)
  refine oneValue_trans (deriv_congr h1) ?_
  rw [deriv_map_mul c q]
  exact oneValue_map _ _ (deriv q)
    (fun x _ => BPair.oneValue_symm (BPair.norm_oneValue _))

/-- The derivative of a family's sum is the derivatives' sum. -/
theorem deriv_famFold {α : Type} (g : α → Poly) : ∀ l : List α,
    deriv (ground.famFold add [] g l)
      = ground.famFold add [] (fun k => deriv (g k)) l
  | [] => rfl
  | a :: t => by
    show deriv (add (g a) (ground.famFold add [] g t))
      = add (deriv (g a)) (ground.famFold add [] (fun k => deriv (g k)) t)
    rw [deriv_add, deriv_famFold g t]

/-- The outer evaluation at a composite point `[sn : sc]` cleared at
one stated power: the coefficients scaled at the clearing's power
against the point's power and summed over the keys, `sc^Ks` times
the read, a polynomial in the inner variable. -/
def pevalOuter (P : PPoly) (sn : BPair) (sc : Pos) (Ks : Nat) : Poly :=
  ground.famFold add []
    (fun k => scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
      (ground.getAt [] P k))
    (List.range P.length)

/-- The outer evaluation sits within the inner-degree cap. -/
theorem length_pevalOuter_le {P : PPoly} {Kt : Nat} (hin : innerLe P Kt)
    (sn : BPair) (sc : Pos) (Ks : Nat) :
    (pevalOuter P sn sc Ks).length ≤ Kt + 1 :=
  length_famFold_le _ (Kt + 1) (fun k => by
    rw [length_scaleP]
    exact innerLe_getAt hin k) _

/-- The cleared evaluation of a family's sum is the evaluations'
sum. -/
private theorem evalClear_famFold (tn : BPair) (tc : Pos) (Kt : Nat)
    (g : Nat → Poly) : ∀ l : List Nat,
    (evalClear (ground.famFold add [] g l) tn tc Kt).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => evalClear (g k) tn tc Kt) l)
  | [] => BPair.oneValue_refl _
  | a :: t => by
    show (evalClear (add (g a) (ground.famFold add [] g t)) tn tc Kt).oneValue
      (evalClear (g a) tn tc Kt
        + ground.famFold BPair.add BPair.unit (fun k => evalClear (g k) tn tc Kt) t)
    exact BPair.oneValue_trans (evalClear_add _ _ tn tc Kt)
      (BPair.add_congr (BPair.oneValue_refl _) (evalClear_famFold tn tc Kt g t))

/-- The two evaluations meet at a point of both variables: the outer
evaluation's cleared read at the inner point is the inner
evaluation's cleared read at the outer point, one cleared value
either way. -/
theorem pevalOuter_pevalCP (P : PPoly) (sn : BPair) (sc : Pos) (Ks : Nat)
    (tn : BPair) (tc : Pos) (Kt : Nat) :
    (evalClear (pevalOuter P sn sc Ks) tn tc Kt).oneValue
      (evalClear (pevalCP P tn tc Kt) sn sc Ks) := by
  refine BPair.oneValue_trans (evalClear_famFold tn tc Kt _ _) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (evalClear_read (pevalCP P tn tc Kt) sn sc Ks))
  rw [length_pevalCP]
  refine ground.famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
    BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) _ _
    (List.range P.length) (fun k _ => ?_)
  show (evalClear (scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
      (ground.getAt [] P k)) tn tc Kt).oneValue
    (ground.getAt BPair.unit (P.map (fun c => evalClear c tn tc Kt)) k
      * bpow sn k * bpow (BPair.ofPos sc) (Ks - k))
  rw [ground.getAt_mapT ([] : Poly) BPair.unit (fun c => evalClear c tn tc Kt)
    (evalClear_nil tn tc Kt) P k]
  refine BPair.oneValue_trans (evalClear_scaleP _ _ tn tc Kt) ?_
  exact polEqB [bpow (BPair.ofPos sc) (Ks - k), bpow sn k,
      evalClear (ground.getAt [] P k) tn tc Kt]
    (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
    (Pol.mon (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 1)) (Mon.var 0)))
    (by decide +kernel)

/-- The outer evaluation reads the inner derivative as the evaluated
polynomial's derivative. -/
theorem pevalOuter_derivInner (P : PPoly) (sn : BPair) (sc : Pos) (Ks : Nat) :
    oneValue (pevalOuter (derivInner P) sn sc Ks)
      (deriv (pevalOuter P sn sc Ks)) := by
  show oneValue
    (ground.famFold add []
      (fun k => scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
        (ground.getAt [] (P.map deriv) k))
      (List.range (P.map deriv).length))
    (deriv (ground.famFold add []
      (fun k => scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
        (ground.getAt [] P k))
      (List.range P.length)))
  rw [deriv_famFold, ground.length_map]
  refine ground.famFold_congr_members_ov oneValue add []
    oneValue_refl (fun h1 h2 => add_congr h1 h2) _ _
    (List.range P.length) (fun k _ => ?_)
  show oneValue
    (scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
      (ground.getAt [] (P.map deriv) k))
    (deriv (scaleP (bpow (BPair.ofPos sc) (Ks - k) * bpow sn k)
      (ground.getAt [] P k)))
  rw [ground.getAt_mapT ([] : Poly) ([] : Poly) deriv rfl P k]
  exact oneValue_symm (deriv_scaleP _ _)

end poly
