import MassGap.Stage
/-!
`lem:stagesplit` — the factorization tier: the stage splits every
polynomial into located linear factors and definite quadratic
factors at pair data, over a stored tower.  The division descent's
greatest common divisor at general inputs lands here as its
certificate reads — a stated factor with its cofactor and clearing
(`facRead`), the descent's Bézout witness at the cleared factor
(`bezRead`), the pair the gcd's whole verification (`gcdRead`), and
the squarefree part with its own Bézout at a constant
(`sqfreeRead`) — the multiplicity by iterated divisions
`def:poly`'s own computed read (`poly.multAt`).
The proper-factor value arithmetic of `lem:stage`'s recorded
arrival lands beside it: the value reads equal members exactly at
the divisor's side exchange on the bracket (`valueNullRead`), and
at a value of unequal members the root sits on the coprime cofactor
with the Bézout read the unit witness (`valueUnitRead`).  The
quadratic tier: a definite factor's pair data `(h, q)` at the root
relation `z² + q = h z` and the definiteness gap `g` at
`h² + g = 4q` (`QDatum`, `defRead`), the discriminant datum `D` at
`D + 4q = h²` (`discRead`), a root's relation read at the stage and
at the located pairs — the remainder lists at `z² + 1`, `i` the
linear monomial's class (`rootRead`, `rootReadI`, `iList`), the
key swap the linear key's read at the relation (`keySwap`) — and
the square root of a located pair on three extensions, the
displayed tower identities one read (`sqrtRead`).  The splitting
data: a stated leading coefficient with the factor lists, each
linear factor at its located root and each quadratic at its
definite datum, the product the verification with repeats the
multiplicities (`poly.linFacM`, `quadFacM`, `factorsRead` at
`poly.prodFold`), the multiplicity's reads `def:poly`'s own
(`poly.multAt_read`, `poly.multAt_of`, `poly.multAt_mul`,
`poly.multAt_pos`, `poly.multAt_deriv`).  The split certificate's
own reads sit beside it: a definite quadratic keeps its upper side
at every value, `4(z² - hz + q) = (2z - h)² + g` (`quadFacM_pos`);
a root of the split polynomial is one of the listed located roots,
the lead and the definite factors off the unit everywhere and a
linear factor at the unit only at its own root
(`root_of_factors`, `poly.eval_linFacM`).
The stage's closure on itself, `lem:stage`'s recorded tower, lands
as the iterated remainder-list arithmetic: one operations interface
per level (`Ops`, `baseOps` the ground's), the generic sum, product
and reduction at a level's monic list (`gAdd`, `gMul`, `gRem`,
`gRemMul`), the lift one adjunction (`liftOps`), and the tower the
iterated lift over its stored data, the extension order the type's
own (`TE`, `TowerData`, `opsAt`), the equal-members read by
reduction (`gNull`), a ground constant's class at a stated depth
with the tower unit witness, the discrete field's Bézout read at a
stated element (`gConst`, `gWitnessRead`); the located brackets at tower elements and the
Kronecker, Trager and Laplace productions are the emitted
certificates' tier at their recorded consumers
(`thm:decimation`'s stored towers, `lem:spectator`'s graph reads),
each produced split verified by the reads above.
-/

namespace stagesplit
open ground poly

/-! The greatest common divisor's certificate reads, the division
descent's arrivals. -/

/-- A stated factor's read: the divisor at its cleared below-top
list with the stated positive top, its cofactor reading the
cleared polynomial — the descent's rescaling total at the pair
carrier, so the representative carries the top as data. -/
def facRead (P g A : Poly) (cg cA : Pos) : Prop :=
  poly.oneValue (poly.mul (poly.topped g cg) A)
    (P.map (fun x => x.scale cA))

instance (P g A : Poly) (cg cA : Pos) :
    Decidable (facRead P g A cg cA) :=
  poly.decOneValue _ _

/-- The descent's Bézout witness at the cleared factor:
`u P + v Q = c · (g topped at cg)` at `c` off equal members. -/
def bezRead (P Q g u v : Poly) (cg : Pos) (c : BPair) : Prop :=
  c.offUnit
  ∧ poly.oneValue (poly.add (poly.mul u P) (poly.mul v Q))
      (poly.mul [c] (poly.topped g cg))

instance (P Q g u v : Poly) (cg : Pos) (c : BPair) :
    Decidable (bezRead P Q g u v cg c) :=
  @instDecidableAnd _ _ (@instDecidableNot _ inferInstance)
    (poly.decOneValue _ _)

/-- The greatest common divisor's whole verification: a common
factor at both cofactors with the descent's Bézout witness, the
combination the greatest's read, the divisor at its stated top. -/
def gcdRead (P Q g A B u v : Poly) (cg cA cB : Pos) (c : BPair) :
    Prop :=
  facRead P g A cg cA ∧ facRead Q g B cg cB
  ∧ bezRead P Q g u v cg c

instance (P Q g A B u v : Poly) (cg cA cB : Pos) (c : BPair) :
    Decidable (gcdRead P Q g A B u v cg cA cB c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The squarefree part's read: the gcd at the derivative, the part
the cofactor at the gcd, and the part's own Bézout against its
derivative at a constant off equal members — every root simple
there. -/
def sqfreeRead (P g A B S u v u2 v2 : Poly) (cg cA cB cS : Pos)
    (c c2 : BPair) : Prop :=
  gcdRead P (poly.deriv P) g A B u v cg cA cB c
  ∧ poly.oneValue (poly.mul (poly.topped g cg) S)
      (P.map (fun x => x.scale cS))
  ∧ c2.offUnit
  ∧ poly.oneValue (poly.add (poly.mul u2 S) (poly.mul v2 (poly.deriv S)))
      [c2]

instance (P g A B S u v u2 v2 : Poly) (cg cA cB cS : Pos)
    (c c2 : BPair) :
    Decidable (sqfreeRead P g A B S u v u2 v2 cg cA cB cS c c2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ¬ _ ∧ _))

/-! The proper-factor value arithmetic, `lem:stage`'s recorded
arrival: the value at the root against the divisor's own data. -/

/-- The value reads equal members at the root: the extension's own
bracket with its isolation at half the separation, the divisor `g`
of the value's polynomial dividing the extension's polynomial as
well, and `g` exchanging sides on the bracket — its one possible
root there is simple and is the extension's own. -/
def valueNullRead (E : stage.Ext) (p g A S1 : Poly)
    (wn wd : Pos) : Prop :=
  stage.bracketRead E
  ∧ stage.isolRead E wn wd
  ∧ poly.oneValue (poly.mul (poly.monic g) A) p
  ∧ poly.oneValue (poly.mul (poly.monic g) S1) (poly.monic E.pol)
  ∧ stage.bracketRead ⟨g, E.lo, E.hi⟩

instance (E : stage.Ext) (p g A S1 : Poly) (wn wd : Pos) :
    Decidable (valueNullRead E p g A S1 wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The value's unit witness at a proper factor: the extension's
own bracket with its isolation, the root sitting on the cofactor
`S₁` at `g S₁ = S`, the divisor keeping one side on the bracket,
and the Bézout read at the coprime cofactor clearing at a constant
off equal members, the value's inverse the witness against the
clearing. -/
def valueUnitRead (E : stage.Ext) (p g S1 u v : Poly)
    (c : BPair) (wn wd : Pos) : Prop :=
  stage.bracketRead E
  ∧ stage.isolRead E wn wd
  ∧ poly.oneValue (poly.mul (poly.monic g) S1) (poly.monic E.pol)
  ∧ ((stage.unitC < stage.evalC (poly.monic g) E.lo
      ∧ stage.unitC < stage.evalC (poly.monic g) E.hi)
    ∨ (stage.evalC (poly.monic g) E.lo < stage.unitC
      ∧ stage.evalC (poly.monic g) E.hi < stage.unitC))
  ∧ c.offUnit
  ∧ poly.oneValue (poly.add (poly.mul u p) (poly.mul v S1)) [c]

instance (E : stage.Ext) (p g S1 u v : Poly) (c : BPair)
    (wn wd : Pos) :
    Decidable (valueUnitRead E p g S1 u v c wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ ∨ _) ∧ ¬ _ ∧ _))

/-! The quadratic tier: the definite pair data, the discriminant
datum, the located pairs, and the square-root extensions. -/

set_option genInjectivity false in
/-- A definite quadratic's pair data `(h, q)` at the root relation
`z² + q = h z`, with the definiteness gap `g` at `h² + g = 4q`. -/
structure QDatum where
  h : BPair
  q : BPair
  g : BPair

/-- The definite read: the gap's join with its positivity. -/
def defRead (D : QDatum) : Prop :=
  BPair.oneValue (D.h * D.h + D.g) (BPair.ofNat 4 * D.q)
  ∧ BPair.unit < D.g

instance (D : QDatum) : Decidable (defRead D) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The discriminant datum `D` at `D + 4q = h²`, the trichotomy's
carrier. -/
def discRead (h q D : BPair) : Prop :=
  BPair.oneValue (D + BPair.ofNat 4 * q) (h * h)

instance (h q D : BPair) : Decidable (discRead h q D) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- A stated root's relation read at the stage:
`z² + q = h z`. -/
def rootRead (h q z : BPair) : Prop :=
  BPair.oneValue (z * z + q) (h * z)

instance (h q z : BPair) : Decidable (rootRead h q z) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The located pairs' relation, `z² + 1` at its below-top list:
`i` is the linear monomial's class. -/
def iList : Poly := [BPair.ofPos .one, BPair.unit]

/-- A stated root's relation read at the located pairs: the root
`a + i b` at the remainder arithmetic of `z² + 1`. -/
def rootReadI (h q a b : BPair) : Prop :=
  poly.oneValue
    (poly.add (poly.remMul iList [a, b] [a, b]) [q])
    (poly.mul [h] [a, b])

instance (h q a b : BPair) : Decidable (rootReadI h q a b) :=
  poly.decOneValue _ _

/-- The key swap at a quadratic's remainder lists: the other
root's read, `a + b z ↦ (a + b h) + b̌ z`, the linear key's
memberwise move across the relation. -/
def keySwap (D : QDatum) (x : Poly) : Poly :=
  [(ground.getAt BPair.unit x 0 + ground.getAt BPair.unit x 1 * D.h).norm,
   (ground.getAt BPair.unit x 1).swap]

/-- The square root of a located pair `a + i b` on three
extensions: `w` at `w² = a² + b²`, `u` at `2u² = w + a`, `v` at
`2v² + a = w`, and the displayed square read
`(u + i v)² = a + i b` at the located pairs' arithmetic. -/
def sqrtRead (a b w u v : BPair) : Prop :=
  BPair.oneValue (w * w) (a * a + b * b)
  ∧ BPair.oneValue (BPair.ofNat 2 * (u * u)) (w + a)
  ∧ BPair.oneValue (BPair.ofNat 2 * (v * v) + a) w
  ∧ poly.oneValue (poly.remMul iList [u, v] [u, v]) [a, b]

instance (a b w u v : BPair) : Decidable (sqrtRead a b w u v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! The splitting data: the factor lists with the product's
verification, repeats the multiplicities. -/

/-- The monic quadratic factor at a definite datum, the root
relation's own polynomial. -/
def quadFacM (D : QDatum) : Poly := [D.q, D.h.swap, BPair.ofPos .one]

/-- The splitting data's read: the cleared polynomial is the stated
leading coefficient against the factor fold, each quadratic factor
definite, a repeated factor its own multiplicity. -/
def factorsRead (P : Poly) (c : Pos) (lead : BPair)
    (roots : List BPair) (quads : List QDatum) : Prop :=
  lead.offUnit
  ∧ (quads.all (fun D => decide (defRead D))) = true
  ∧ poly.oneValue (P.map (fun x => x.scale c))
      (poly.mul [lead]
        (poly.prodFold (roots.map poly.linFacM ++ quads.map quadFacM)))

instance (P : Poly) (c : Pos) (lead : BPair) (roots : List BPair)
    (quads : List QDatum) :
    Decidable (factorsRead P c lead roots quads) :=
  inferInstanceAs (Decidable (¬ _ ∧ _ = _ ∧ _))

/-! The split certificate's reads: a definite quadratic factor's
upper side at every value, and a root of the split polynomial among
the listed located roots. -/

/-- A definite quadratic factor keeps its upper side at every value:
`4 ⟨z² + q : h z⟩ = ⟨2z : h⟩² + g` at the definiteness gap, positive
by its shape. -/
theorem quadFacM_pos (D : QDatum) (hD : defRead D) (x : BPair) :
    BPair.unit < poly.eval (quadFacM D) x := by
  have t1 : (poly.eval [BPair.ofPos Pos.one] x).oneValue
      (BPair.ofPos Pos.one) := poly.eval_one (BPair.ofPos Pos.one) x
  have t2 : (x * poly.eval [BPair.ofPos Pos.one] x).oneValue x :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl x) t1)
      (BPair.mul_one_read x)
  have t3 : (D.h.swap + x * poly.eval [BPair.ofPos Pos.one] x).oneValue
      (x + D.h.swap) :=
    BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl D.h.swap) t2)
      (BPair.oneValue_of_eq (BPair.add_comm D.h.swap x))
  have t4 : (x * (D.h.swap + x * poly.eval [BPair.ofPos Pos.one] x)).oneValue
      (x * x + x * D.h.swap) :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl x) t3)
      (BPair.oneValue_of_eq (BPair.left_distrib x x D.h.swap))
  have hE : (poly.eval (quadFacM D) x).oneValue
      (D.q + (x * x + x * D.h.swap)) :=
    BPair.add_congr (BPair.oneValue_refl D.q) t4
  have e1 : (BPair.ofNat 2 * x + D.h.swap) * (BPair.ofNat 2 * x + D.h.swap)
      + D.g
      = BPair.ofNat 2 * BPair.ofNat 2 * (x * x)
        + (BPair.ofNat 2 + BPair.ofNat 2) * (x * D.h.swap)
        + (D.h * D.h + D.g) := by
    rw [BPair.sq_expand (BPair.ofNat 2 * x) D.h.swap,
      BPair.mul_mul_mul_comm (BPair.ofNat 2) x (BPair.ofNat 2) x,
      BPair.swap_mul_swap D.h D.h,
      BPair.mul_assoc (BPair.ofNat 2) x D.h.swap,
      ← BPair.right_distrib (BPair.ofNat 2) (BPair.ofNat 2) (x * D.h.swap),
      BPair.add_assoc (BPair.ofNat 2 * BPair.ofNat 2 * (x * x) + D.h * D.h)
        ((BPair.ofNat 2 + BPair.ofNat 2) * (x * D.h.swap)) D.g,
      BPair.add_add_comm (BPair.ofNat 2 * BPair.ofNat 2 * (x * x))
        (D.h * D.h) ((BPair.ofNat 2 + BPair.ofNat 2) * (x * D.h.swap)) D.g]
  have e2 : BPair.ofNat 4 * (D.q + (x * x + x * D.h.swap))
      = BPair.ofNat 4 * (x * x) + BPair.ofNat 4 * (x * D.h.swap)
        + BPair.ofNat 4 * D.q := by
    rw [BPair.left_distrib (BPair.ofNat 4) D.q (x * x + x * D.h.swap),
      BPair.left_distrib (BPair.ofNat 4) (x * x) (x * D.h.swap),
      BPair.add_comm (BPair.ofNat 4 * D.q)
        (BPair.ofNat 4 * (x * x) + BPair.ofNat 4 * (x * D.h.swap))]
  have c1 : (BPair.ofNat 2 * BPair.ofNat 2 * (x * x)).oneValue
      (BPair.ofNat 4 * (x * x)) :=
    BPair.mul_congr (BPair.oneValue_symm (BPair.ofNat_mul 2 2))
      (BPair.oneValue_refl (x * x))
  have c2 : ((BPair.ofNat 2 + BPair.ofNat 2) * (x * D.h.swap)).oneValue
      (BPair.ofNat 4 * (x * D.h.swap)) :=
    BPair.mul_congr (BPair.oneValue_symm (BPair.ofNat_add 2 2))
      (BPair.oneValue_refl (x * D.h.swap))
  have hsq : ((BPair.ofNat 2 * x + D.h.swap)
      * (BPair.ofNat 2 * x + D.h.swap) + D.g).oneValue
      (BPair.ofNat 4 * (D.q + (x * x + x * D.h.swap))) := by
    rw [e1, e2]
    exact BPair.add_congr (BPair.add_congr c1 c2) hD.1
  have hpos : BPair.unit < (BPair.ofNat 2 * x + D.h.swap)
      * (BPair.ofNat 2 * x + D.h.swap) + D.g :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.oneValue_of_eq (BPair.add_comm D.g _))
      (ground.unitLtAdd hD.2 (ground.unitLeSq _))
  have hsc : BPair.unit
      < (D.q + (x * x + x * D.h.swap)).scale (ground.posOfSucc 3) :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.ofPos_scale (ground.posOfSucc 3) _)
      (BPair.lt_congr (BPair.oneValue_refl BPair.unit) hsq hpos)
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm hE)
    (BPair.lt_of_scale_lt (w := ground.posOfSucc 3)
      (BPair.lt_congr (ground.unitScale _) (BPair.oneValue_refl _) hsc))

/-- A root of the split polynomial is a listed located root: the lead
and every definite factor sit off the unit at every value, and a
linear factor reads the unit at its root alone. -/
theorem root_of_factors (P : Poly) (c : Pos) (lead : BPair)
    (roots : List BPair) (quads : List QDatum)
    (hf : factorsRead P c lead roots quads) (x : BPair)
    (hx : poly.isRoot P x) :
    (roots.any (fun r => decide (x.oneValue r))) = true := by
  have hsc : (poly.eval (P.map (fun y => y.scale c)) x).oneValue
      BPair.unit :=
    BPair.oneValue_trans (poly.eval_mapScale P c x)
      (BPair.oneValue_trans (BPair.scale_congr c hx)
        (BPair.oneValue_symm (ground.unitScale c)))
  have hprod : (poly.eval (poly.mul [lead]
      (poly.prodFold (roots.map poly.linFacM ++ quads.map quadFacM)))
        x).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (poly.eval_congr hf.2.2 x)) hsc
  have hlead : (lead * poly.eval
      (poly.prodFold (roots.map poly.linFacM ++ quads.map quadFacM))
        x).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (poly.eval_mul [lead]
            (poly.prodFold (roots.map poly.linFacM ++ quads.map quadFacM)) x)
          (BPair.mul_congr (poly.eval_one lead x)
            (BPair.oneValue_refl _))))
      hprod
  have hQ : (poly.eval
      (poly.prodFold (roots.map poly.linFacM ++ quads.map quadFacM))
        x).oneValue BPair.unit :=
    match (BPair.mul_unit_iff lead _).mp hlead with
    | Or.inl hs => absurd hs hf.1
    | Or.inr he => he
  match ground.mem_of_any _ _ ((poly.prodFold_unit _ x).mp hQ) with
  | ⟨p, hp, hdec⟩ =>
    have hpu : (poly.eval p x).oneValue BPair.unit := of_decide_eq_true hdec
    match ground.mem_append_of _ _ hp with
    | Or.inl hlin =>
      match ground.mem_map_of poly.linFacM roots p hlin with
      | ⟨r, hr, hrp⟩ =>
        have hlu : (poly.eval (poly.linFacM r) x).oneValue BPair.unit := by
          rw [hrp]; exact hpu
        exact ground.any_of_mem _ hr
          (decide_eq_true (ground.oneOfUnit
            (BPair.oneValue_trans
              (BPair.oneValue_symm (poly.eval_linFacM r x)) hlu)))
    | Or.inr hquad =>
      match ground.mem_map_of quadFacM quads p hquad with
      | ⟨D, hD, hDp⟩ =>
        have hqu : (poly.eval (quadFacM D) x).oneValue BPair.unit := by
          rw [hDp]; exact hpu
        exact absurd hqu (ground.offOfUnitLt (quadFacM_pos D
          (of_decide_eq_true (ground.all_of_mem _ quads hf.2.1 D hD)) x))

/-! The stage's closure on itself: one operations interface per
level, the generic remainder arithmetic, and the tower the iterated
lift over its stored data. -/

set_option genInjectivity false in
/-- A level's operations: the sum, the product, the memberwise
swap, the sum's unit, the product's unit, and the equal-members
test. -/
structure Ops (α : Type) where
  add : α → α → α
  mul : α → α → α
  swap : α → α
  unit : α
  one : α
  isNull : α → Bool

/-- The generic componentwise sum over a level's coefficients. -/
def gAdd {α : Type} (o : Ops α) : List α → List α → List α
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => o.add c d :: gAdd o p q

/-- The generic convolution on the recursion,
`(c + z P) Q = c Q + z (P Q)`. -/
def gMul {α : Type} (o : Ops α) : List α → List α → List α
  | [], _ => []
  | c :: p, q => gAdd o (q.map (o.mul c)) (o.unit :: gMul o p q)

/-- The generic memberwise swap. -/
def gSwapP {α : Type} (o : Ops α) (p : List α) : List α := p.map o.swap

private def gPadTo {α : Type} (o : Ops α) (n : Nat) (l : List α) :
    List α :=
  List.replicate (n - l.length) o.unit ++ l

private def gSubTop {α : Type} (o : Ops α) :
    List α → List α → List α
  | rest, [] => rest
  | [], _ :: _ => []
  | r :: rest, d :: ds => o.add r (o.swap d) :: gSubTop o rest ds

private def gDivGo {α : Type} (o : Ops α) :
    Nat → List α → List α → List α × List α
  | 0, stf, ptf => ([], gPadTo o stf.length ptf)
  | fuel + 1, stf, ptf =>
    if ptf.length ≤ stf.length then ([], gPadTo o stf.length ptf)
    else
      match ptf with
      | [] => ([], gPadTo o stf.length [])
      | c :: rest =>
        let s := gDivGo o fuel stf (gSubTop o rest (stf.map (o.mul c)))
        (c :: s.1, s.2)

/-- The generic remainder at a level's monic list, the division's
descent from the top. -/
def gRem {α : Type} (o : Ops α) (s P : List α) : List α :=
  ((gDivGo o P.length s.reverse P.reverse).2).reverse

/-- The remainder lists' product at a level's monic list. -/
def gRemMul {α : Type} (o : Ops α) (s a b : List α) : List α :=
  gRem o s (gMul o a b)

/-- The equal-members read by reduction, coefficientwise. -/
def gNull {α : Type} (o : Ops α) (p : List α) : Bool := p.all o.isNull

/-- The ground level's operations, `def:ground`'s displayed reads
at the canonical representatives. -/
def baseOps : Ops BPair :=
  ⟨fun x y => (x + y).norm, fun x y => (x * y).norm, BPair.swap,
   BPair.unit, BPair.ofPos .one, fun x => x.norm.isUnitRep⟩

/-- One adjunction's lift: the remainder lists at the stated monic
list over the level below, the displayed sum and product. -/
def liftOps {α : Type} (o : Ops α) (s : List α) : Ops (List α) :=
  ⟨gAdd o, gRemMul o s, gSwapP o, [], [o.one], gNull o⟩

/-- The tower's element type at a stated depth, the iterated
remainder lists. -/
def TE : Nat → Type
  | 0 => BPair
  | d + 1 => List (TE d)

/-- The tower's stored data at a stated depth: one monic below-top
list per extension, each over the stage the earlier extensions
built, the extension order the type's own. -/
def TowerData : Nat → Type
  | 0 => Unit
  | d + 1 => TowerData d × List (TE d)

/-- The tower's operations, the iterated lift over the stored
data: every read runs through the one arithmetic. -/
def opsAt : (d : Nat) → TowerData d → Ops (TE d)
  | 0, _ => baseOps
  | d + 1, (tw, s) => liftOps (opsAt d tw) s

/-- A ground constant's class at a stated tower depth. -/
def gConst : (d : Nat) → BPair → TE d
  | 0, c => c
  | d + 1, c => [gConst d c]

/-- The tower unit witness: `v w = c` at the tower's arithmetic,
`c` a ground constant off equal members — the discrete field's
Bézout unit witness at a stated element, every read the stored
tower's own. -/
def gWitnessRead (d : Nat) (tw : TowerData d) (v w : TE d)
    (c : BPair) : Prop :=
  c.offUnit
  ∧ (opsAt d tw).isNull
      ((opsAt d tw).add ((opsAt d tw).mul v w)
        ((opsAt d tw).swap (gConst d c))) = true

instance (d : Nat) (tw : TowerData d) (v w : TE d) (c : BPair) :
    Decidable (gWitnessRead d tw v w c) :=
  inferInstanceAs (Decidable (¬ _ ∧ _ = _))

end stagesplit
