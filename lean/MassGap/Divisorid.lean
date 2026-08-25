import MassGap.Cellcount
/-!
`thm:divisorid` — the divisor identification.  Clause (i): on a
window a level is a pencil root exactly where the determinant reads
equal members, `lem:split`'s factorization read — at the factorization
`χ = det G · Π ⟨x : ε_j⟩` (`split.chiRead`) with the gram's
determinant off the unit, the pencil polynomial's Horner read at a
level is equal-membered exactly where the level ties a listed root,
the cleared linear factor `d x − n` reading the unit at `d x = n`
(`rootIff`); the Feshbach half reads `lem:inertia`'s determinant
split at the deflation (`inertia.minor_deflMat`): the cleared Schur
complement's determinant is equal-membered exactly with the whole's
at a pivot of unequal-membered determinant (`deflRoot`).

Clause (ii)'s crossing-read tier lands at the two-variable carrier
(`poly.PPoly`, x-polynomials with base-polynomial coefficients): the
squarefree split χ = c ∏_j S_j^j at base polynomial pairs
(`splitRead`), each factor primitive over the base's polynomial ring
at the division descent's iterated greatest common divisors, every
step certified (`primitiveP`, `stagesplit.gcdRead` at
`windowsep.gcdD`'s produced data) and taken at its stated site, the
top coefficient off the unit tail (`topOff`); and the crossing read
D = ∏_j Res_x(S_j, S_j') · ∏_{i<j} Res_x(S_i, S_j) (`crossD`, the
pairs `places.pairsOf` at the list's width), the resultants
`def:elim`'s at the variable `x` over the coefficient carrier
(`presultant`, `elim.shiftMatO`'s determinant at the pivot descent
with `presultant_read` its first-row fold), a base element off the
sum's unit (`crossOff`).  The specialization at a base point reads
the evaluated data (`poly.pevalB`): the resultant evaluates to the
evaluated polynomials' resultant (`pevalB_presultant`), a common
root reads a resultant at the unit through the adjugate row's solve
(`resultant_unit_of_roots`), and off the crossing read's locus, at
the pencil polynomial's leading coefficient off the unit there (the
leading coefficients multiply to it, `elim.ptop_pmul`, so the
content's and every factor's read unequal members), every root of
the pencil polynomial is a root of exactly one factor, simple in it,
at the factor's place as its multiplicity (`specialize`,
`poly.multAt` the count of iterated divisions).

Clause (iii)'s cell read: the one pencil at two levels `l < h`,
the carriers the level datum's own (`cellcount.levelPMat`), and on
a cell certified at both the ground multiplicity is one integer
(`groundMult`, the pair at `l` positive semidefinite and the count
at `h` transported by `lem:cellcount`'s constancy theorem to every
point of the cell); the boundary's own two-sided bracket counts
are `thm:decimation`'s emitted record entries, a move across a
located boundary a ground collision confined to the crossing
read's locus by clause (ii); and the free end reads multiplicity
one over its covered bracket, the level bracket isolating the free
ground at the unit's line against the scaled floor (`lem:freeend`;
`lem:freecell`'s batteries).
-/

namespace divisorid
open ground elim inertia split

/-- A pair against a positive datum's pair reads the pair rescaled
by the datum. -/
private theorem mul_ofPos (x : BPair) (d : Pos) :
    (x * BPair.ofPos d).oneValue (x.scale d) := by
  show x.fst * (d + Pos.one) + x.snd * Pos.one + x.snd * d
    = x.fst * d + (x.fst * Pos.one + x.snd * (d + Pos.one))
  rw [ground.left_distrib, ground.left_distrib, ground.mul_one,
    ground.mul_one, ground.add_assoc (x.fst * d) x.fst x.snd,
    ground.add_assoc (x.fst * d) (x.fst + x.snd) (x.snd * d),
    ground.add_assoc x.fst x.snd (x.snd * d),
    ground.add_comm x.snd (x.snd * d)]

/-- The cleared linear factor reads the unit at a level exactly
where the level ties the root. -/
private theorem linFac_unit (n : BPair) (d : Pos) (x : BPair) :
    (poly.eval (linFac n d) x).oneValue BPair.unit
      ↔ (x.scale d).oneValue n := by
  have h : (poly.eval (linFac n d) x).oneValue (n.swap + x.scale d) := by
    show (n.swap + x * poly.eval [BPair.ofPos d] x).oneValue _
    exact BPair.add_congr (BPair.oneValue_refl n.swap)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl x) (poly.eval_one _ x))
        (mul_ofPos x d))
  refine (BPair.unit_iff h).trans ?_
  rw [BPair.add_comm]
  exact ⟨ground.oneOfUnit, ground.unitOfOne⟩

/-- `thm:divisorid`(i): at `lem:split`'s factorization with the
gram's determinant off the unit, the pencil polynomial's read at a
level is equal-membered exactly where the level ties a listed
root. -/
theorem rootIff (H G : Mat) (roots : List (BPair × Pos))
    (hχ : chiRead H G roots) (hG : ¬ (minor G).oneValue BPair.unit)
    (x : BPair) :
    (poly.eval (charPoly H G) x).oneValue BPair.unit
      ↔ (roots.any (fun r => decide ((x.scale r.2).oneValue r.1)))
        = true := by
  have hE := poly.eval_congr hχ x
  have hL : (poly.eval (poly.mul
      [BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)]
      (charPoly H G)) x).oneValue
      (BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)
        * poly.eval (charPoly H G) x) :=
    BPair.oneValue_trans (poly.eval_mul _ _ x)
      (BPair.mul_congr_left (poly.eval_one _ x))
  have hR : (poly.eval (poly.mul [minor G]
      (poly.prodFold (roots.map (fun r => linFac r.1 r.2)))) x).oneValue
      (minor G
        * poly.eval (poly.prodFoldMap (fun r => linFac r.1 r.2) roots) x) :=
    BPair.oneValue_trans (poly.eval_mul _ _ x)
      (BPair.mul_congr_left (poly.eval_one _ x))
  have h1 : (poly.eval (charPoly H G) x).oneValue BPair.unit
      ↔ (BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)
        * poly.eval (charPoly H G) x).oneValue BPair.unit :=
    (Iff.intro Or.inr (fun h => match h with
      | .inl hc => absurd hc (BPair.ofPos_off _)
      | .inr he => he)).trans (BPair.mul_unit_iff _ _).symm
  have h5 : BPair.oneValue (minor G
        * poly.eval (poly.prodFoldMap (fun r => linFac r.1 r.2) roots) x)
          BPair.unit
      ↔ BPair.oneValue
          (poly.eval (poly.prodFoldMap (fun r => linFac r.1 r.2) roots) x)
          BPair.unit :=
    (BPair.mul_unit_iff _ _).trans (Iff.intro (fun h => match h with
      | .inl hg => absurd hg hG
      | .inr hf => hf) Or.inr)
  refine h1.trans ((BPair.unit_iff hL).symm.trans ((BPair.unit_iff hE).trans
    ((BPair.unit_iff hR).trans (h5.trans
      ((poly.prodFoldMap_unit _ x roots).trans ?_)))))
  constructor
  · intro hany
    obtain ⟨r, hr, hf⟩ := ground.mem_of_any _ roots hany
    exact ground.any_of_mem _ hr (decide_eq_true
      ((linFac_unit r.1 r.2 x).mp (of_decide_eq_true hf)))
  · intro hany
    obtain ⟨r, hr, hf⟩ := ground.mem_of_any _ roots hany
    exact ground.any_of_mem _ hr (decide_eq_true
      ((linFac_unit r.1 r.2 x).mpr (of_decide_eq_true hf)))

/-- `thm:divisorid`(i)'s Feshbach half: at a pivot of
unequal-membered determinant the cleared deflation's determinant
reads the unit exactly where the whole's does, `lem:inertia`'s
determinant split read at the unit. -/
theorem deflRoot {k m : Nat} (P B Q Cw : Mat)
    (hP : sqAt P k) (hBl : B.length = k) (hBr : rowsLen m B)
    (hQ : sqAt Q m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hPs : matOneValue (transposeM P) P)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B))
    (hPnz : ¬ (minor P).oneValue BPair.unit) :
    (minor (deflMat P B Q Cw)).oneValue BPair.unit
      ↔ (minor (blockJoin P B Q)).oneValue BPair.unit := by
  have h := inertia.minor_deflMat P B Q Cw hP hBl hBr hQ hCl hCr hPs hPw hPnz
  have h1 : (minor (deflMat P B Q Cw)).oneValue BPair.unit
      ↔ (minor P * minor (deflMat P B Q Cw)).oneValue BPair.unit :=
    (Iff.intro Or.inr (fun hh => match hh with
      | .inl hp => absurd hp hPnz
      | .inr hd => hd)).trans (BPair.mul_unit_iff _ _).symm
  have h2 : (ground.bpow (minor P) (2 * m) * minor (blockJoin P B Q)).oneValue
        BPair.unit
      ↔ (minor (blockJoin P B Q)).oneValue BPair.unit :=
    (BPair.mul_unit_iff _ _).trans (Iff.intro (fun hh => match hh with
      | .inl hp => absurd hp (bpow_off (minor P) hPnz (2 * m))
      | .inr hd => hd) Or.inr)
  exact h1.trans ((BPair.unit_iff h).trans h2)

/-! `thm:divisorid`(ii)'s crossing-read tier at the two-variable
carrier: the squarefree split's reads and the crossing divisor `D`,
the resultants `def:elim`'s at the variable `x` over the base's
polynomials. -/

/-- The successor-weighted shift from a stated key at the
coefficient carrier. -/
private def pderivFrom : Pos → poly.PPoly → poly.PPoly
  | _, [] => []
  | n, c :: P => poly.scaleP (BPair.ofPos n) c :: pderivFrom (ground.succ n) P

/-- The derivative in the outer variable, `P'_h = (h+1) P_{h+1}` at
every outer key. -/
def pderiv : poly.PPoly → poly.PPoly
  | [] => []
  | _ :: P => pderivFrom .one P

/-- The power at a stated count, the outer product's fold from the
carrier's unit. -/
def ppowOf (P : poly.PPoly) : Nat → poly.PPoly :=
  poly.powO (poly.polyO poly.polyOps) P

/-- The resultant at the variable `x` over the base's polynomials:
the shift matrix's site-datum determinant at the coefficient
carrier. -/
def presultant (p q : poly.PPoly) : poly.Poly :=
  elim.pdetD (elim.shiftMatO poly.polyOps p q)

/-- The descent's resultant reads the first-row fold at the square
shift frame. -/
theorem presultant_read (p q : poly.PPoly) :
    poly.oneValue (presultant p q)
      (split.pminor (elim.shiftMatO poly.polyOps p q)) :=
  elim.pdetD_eq _ (by
    rw [elim.length_shiftMatO]
    exact elim.rowsLen_shiftMatO poly.polyOps p q)

/-- The split's product `∏_j S_j^j`, the exponent the member's place
from one in list order. -/
private def splitProdGo : Nat → List poly.PPoly → poly.PPoly
  | _, [] => [poly.one]
  | j, S :: t => poly.pmul (ppowOf S j) (splitProdGo (j + 1) t)

/-- The split's product `∏_j S_j^j` at the listed factors. -/
def splitProd (S : List poly.PPoly) : poly.PPoly := splitProdGo 1 S

/-- The resultant's stated site at the representative: the factor is
occupied with its top coefficient off the unit tail. -/
def topOff (P : poly.PPoly) : Prop :=
  1 < P.length ∧ ¬ poly.unitTail (poly.ptop P)

instance (P : poly.PPoly) : Decidable (topOff P) :=
  @instDecidableAnd _ _ inferInstance (@instDecidableNot _ (poly.decUnitTail _))

/-- The coefficients' iterated greatest common divisor at the
division descent, each step's divisor carried to its stated top. -/
private def contentRead : poly.Poly → List poly.Poly → Prop
  | g, [] => (poly.vnorm g).length ≤ 1
  | g, p :: t =>
    let d := windowsep.gcdD g p
    stagesplit.gcdRead g p d.g d.A d.B d.u d.v d.top d.cA d.cB d.c
      ∧ contentRead (poly.topped d.g d.top) t

private def decContentRead : ∀ (g : poly.Poly) (t : List poly.Poly),
    Decidable (contentRead g t)
  | g, [] => (Nat.decLe (poly.vnorm g).length 1 :
      Decidable ((poly.vnorm g).length ≤ 1))
  | _, _ :: t => @instDecidableAnd _ _ inferInstance (decContentRead _ t)

private instance (g : poly.Poly) (t : List poly.Poly) :
    Decidable (contentRead g t) := decContentRead g t

/-- Gauss primitivity over the base's polynomial ring: the
coefficients' iterated greatest common divisor at the certified
division descent reads a constant, one walk carrying the
certificates and the content. -/
def primitiveP : poly.PPoly → Prop
  | [] => False
  | c :: t => contentRead (poly.vnorm c) t

private def decPrimitiveP : ∀ P : poly.PPoly, Decidable (primitiveP P)
  | [] => isFalse (fun h => h)
  | c :: t => decContentRead (poly.vnorm c) t

instance (P : poly.PPoly) : Decidable (primitiveP P) := decPrimitiveP P

/-- Every listed factor sits at the resultant's stated site and is
primitive over the base's polynomial ring. -/
def primAll : List poly.PPoly → Prop
  | [] => True
  | S :: t => topOff S ∧ primitiveP S ∧ primAll t

private def decPrimAll : ∀ S : List poly.PPoly, Decidable (primAll S)
  | [] => isTrue trivial
  | _ :: t =>
    @instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance (decPrimAll t))

instance (S : List poly.PPoly) : Decidable (primAll S) := decPrimAll S

/-- `thm:divisorid`(ii)'s split `χ = c ∏_j S_j^j` over the base's
polynomial pairs, each `S_j` primitive at its stated top with the
contents collected into the base polynomial `c`. -/
def splitRead (χ : poly.PPoly) (c : poly.Poly) (S : List poly.PPoly) : Prop :=
  poly.ppOneValue χ (poly.pmul [c] (splitProd S)) ∧ primAll S

instance (χ : poly.PPoly) (c : poly.Poly) (S : List poly.PPoly) :
    Decidable (splitRead χ c S) :=
  @instDecidableAnd _ _ inferInstance (decPrimAll S)


/-! The specialization's evaluation reads: the outer polynomial at a
base point coefficientwise (`poly.pevalB`) reads the outer power as
the power, the derivative as the derivative, and the split's product
as the product. -/

/-- The evaluation reads the outer power as the power. -/
theorem pevalB_ppowOf (P : poly.PPoly) (t : BPair) : ∀ n : Nat,
    poly.oneValue (poly.pevalB (ppowOf P n) t)
      (poly.powOf (poly.pevalB P t) n)
  | 0 => ⟨poly.eval_one _ t, trivial⟩
  | n + 1 =>
    poly.oneValue_trans (poly.pevalB_pmul P (ppowOf P n) t)
      (poly.mul_congr _ (pevalB_ppowOf P t n))

/-- A coefficient's scaled read evaluates to the scaled value. -/
private theorem eval_scaleP_ofPos (c : poly.Poly) (n : Pos) (t : BPair) :
    (poly.eval (poly.scaleP (BPair.ofPos n) c) t).oneValue
      ((poly.eval c t).scale n) := by
  refine BPair.oneValue_trans
    (poly.eval_congr (poly.oneValue_map _ (fun x => BPair.ofPos n * x) c
      (fun x _ => BPair.norm_oneValue _)) t) ?_
  refine BPair.oneValue_trans (poly.eval_scale c (BPair.ofPos n) t) ?_
  rw [BPair.mul_comm]
  exact mul_ofPos _ n

private theorem pevalB_pderivFrom (t : BPair) : ∀ (n : Pos) (P : poly.PPoly),
    poly.oneValue (poly.pevalB (pderivFrom n P) t)
      (poly.derivFrom n (poly.pevalB P t))
  | _, [] => trivial
  | n, c :: P =>
    ⟨eval_scaleP_ofPos c n t, pevalB_pderivFrom t (ground.succ n) P⟩

/-- The evaluation reads the outer derivative as the derivative. -/
theorem pevalB_pderiv (t : BPair) : ∀ P : poly.PPoly,
    poly.oneValue (poly.pevalB (pderiv P) t) (poly.deriv (poly.pevalB P t))
  | [] => trivial
  | _ :: P => pevalB_pderivFrom t .one P

/-- The split's product at a base point, the evaluated factors'
powers folded from the exponent one. -/
def evalSplit (t : BPair) : Nat → List poly.PPoly → poly.Poly
  | _, [] => poly.one
  | j, Q :: S =>
    poly.mul (poly.powOf (poly.pevalB Q t) j) (evalSplit t (j + 1) S)

private theorem pevalB_splitProdGo (t : BPair) :
    ∀ (j : Nat) (S : List poly.PPoly),
    poly.oneValue (poly.pevalB (splitProdGo j S) t) (evalSplit t j S)
  | _, [] => ⟨poly.eval_one _ t, trivial⟩
  | j, Q :: S =>
    poly.oneValue_trans (poly.pevalB_pmul _ _ t)
      (poly.oneValue_trans
        (poly.mul_congr_left (pevalB_ppowOf Q t j) _)
        (poly.mul_congr _ (pevalB_splitProdGo t (j + 1) S)))

/-- The evaluation reads the split's product as the evaluated
factors' product. -/
theorem pevalB_splitProd (t : BPair) (S : List poly.PPoly) :
    poly.oneValue (poly.pevalB (splitProd S) t) (evalSplit t 1 S) :=
  pevalB_splitProdGo t 1 S

/-- The crossing read
`D = ∏_j Res_x(S_j, S_j') · ∏_{i<j} Res_x(S_i, S_j)`, a base
element: the factors' resultants against their derivatives folded
over the list and the pairs' resultants folded over the list's pairs
in order. -/
def crossD (S : List poly.PPoly) : poly.Poly :=
  poly.mul (poly.prodFoldMap (fun Q => presultant Q (pderiv Q)) S)
    (poly.prodFoldMap
      (fun u => presultant (ground.getAt [] S u.1) (ground.getAt [] S u.2))
      (places.pairsOf S.length))

/-- The crossing read sits off the sum's unit: root collisions sit on
`D`'s located root locus alone. -/
def crossOff (S : List poly.PPoly) : Prop := ¬ poly.unitTail (crossD S)

instance (S : List poly.PPoly) : Decidable (crossOff S) :=
  @instDecidableNot _ (poly.decUnitTail _)


/-! The specialization at a base point: the resultant over the base's
polynomials evaluates to the evaluated polynomials' resultant, a
common root reads the resultant at the unit through the adjugate
row's solve, and the crossing read off the unit puts every factor's
resultant against its derivative and every pair's resultant off the
unit there. -/

/-- The evaluation reads the resultant over the base's polynomials as
the evaluated polynomials' resultant. -/
theorem pevalB_presultant (p q : poly.PPoly) (t : BPair) :
    (poly.eval (presultant p q) t).oneValue
      (resultant (poly.pevalB p t) (poly.pevalB q t)) := by
  have hsq : rowsLen (shiftMatO poly.polyOps p q).length
      (shiftMatO poly.polyOps p q) := by
    rw [length_shiftMatO]
    exact rowsLen_shiftMatO poly.polyOps p q
  refine BPair.oneValue_trans (poly.eval_congr (presultant_read p q) t) ?_
  refine BPair.oneValue_trans (eval_minorP _ t hsq) ?_
  rw [shiftMatO_eval]
  exact BPair.oneValue_symm (resultant_read _ _)

/-- Two polynomials at a common root read their resultant at the
unit: the adjugate row's solve evaluated there. -/
theorem resultant_unit_of_roots (p q : poly.Poly)
    (hW : 0 < p.length - 1 + (q.length - 1)) (r : BPair)
    (hp : poly.isRoot p r) (hq : poly.isRoot q r) :
    (resultant p q).oneValue BPair.unit := by
  have h := poly.eval_congr (bezout_all p q hW) r
  refine BPair.oneValue_trans (BPair.oneValue_symm (poly.eval_one _ r)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm h) ?_
  refine BPair.oneValue_trans (poly.eval_add _ _ r) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (poly.eval_mul _ _ r)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hp) (BPair.mul_unit _)))
      (BPair.oneValue_trans (poly.eval_mul _ _ r)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hq) (BPair.mul_unit _)))) ?_
  exact BPair.add_unit _

/-- A polynomial at an off-unit top holding a root has a positive
degree. -/
theorem length_of_root (p : poly.Poly)
    (htop : ¬ (poly.top p).oneValue BPair.unit)
    (r : BPair) (hp : poly.isRoot p r) : 0 < p.length - 1 := by
  match p, htop, hp with
  | [], htop, _ => exact absurd (BPair.oneValue_refl _) htop
  | [c], htop, hp =>
    exact absurd
      (BPair.oneValue_trans (BPair.oneValue_symm (poly.eval_one c r)) hp) htop
  | _ :: _ :: _, _, _ => exact Nat.succ_pos _

/-- A product's evaluation off the unit has both factors' off it. -/
private theorem eval_mul_off {p q : poly.Poly} {t : BPair}
    (h : ¬ (poly.eval (poly.mul p q) t).oneValue BPair.unit) :
    ¬ (poly.eval p t).oneValue BPair.unit
      ∧ ¬ (poly.eval q t).oneValue BPair.unit := by
  refine ⟨fun hp => h ?_, fun hq => h ?_⟩
  · exact BPair.oneValue_trans (poly.eval_mul p q t)
      (BPair.oneValue_trans (BPair.mul_congr_left hp) (BPair.unit_mul _))
  · exact BPair.oneValue_trans (poly.eval_mul p q t)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hq) (BPair.mul_unit _))

/-- The self-resultants' fold off the unit at a base point puts every
factor's resultant against its derivative off the unit there. -/
private theorem crossSelf_off (t : BPair) (S : List poly.PPoly)
    (h : ¬ (poly.eval
      (poly.prodFoldMap (fun Q => presultant Q (pderiv Q)) S) t).oneValue
        BPair.unit)
    (j : Nat) (hj : j < S.length) :
    ¬ (resultant (poly.pevalB (ground.getAt [] S j) t)
        (poly.pevalB (pderiv (ground.getAt [] S j)) t)).oneValue BPair.unit :=
  fun hr => poly.prodFoldMap_off _ t S h _ (ground.mem_getAt [] S j hj)
    (BPair.oneValue_trans (pevalB_presultant _ _ t) hr)

/-- The pair resultants' fold off the unit at a base point puts every
pair's resultant off the unit there, at the listed order. -/
private theorem crossPairs_off (t : BPair) (S : List poly.PPoly)
    (h : ¬ (poly.eval (poly.prodFoldMap
      (fun u => presultant (ground.getAt [] S u.1) (ground.getAt [] S u.2))
      (places.pairsOf S.length)) t).oneValue BPair.unit)
    (i j : Nat) (hij : i < j) (hj : j < S.length) :
    ¬ (resultant (poly.pevalB (ground.getAt [] S i) t)
        (poly.pevalB (ground.getAt [] S j) t)).oneValue BPair.unit :=
  fun hr => poly.prodFoldMap_off _ t _ h (i, j)
    (ground.mem_of_countOf_pos _ _ (places.pairs_complete S.length hij hj))
    (BPair.oneValue_trans (pevalB_presultant _ _ t) hr)

/-- Every listed factor of a primitive split sits at the resultant's
stated site. -/
private theorem primAll_topOff : ∀ (S : List poly.PPoly), primAll S →
    ∀ i, i < S.length → topOff (ground.getAt [] S i)
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, h, 0, _ => h.1
  | _ :: S, h, i + 1, hi => primAll_topOff S h.2.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The outer power's top is the top's power. -/
private theorem ptop_ppowOf (P : poly.PPoly) : ∀ n : Nat,
    poly.oneValue (poly.ptop (ppowOf P n)) (poly.powOf (poly.ptop P) n)
  | 0 => poly.oneValue_refl _
  | n + 1 =>
    poly.oneValue_trans (ptop_pmul P (ppowOf P n))
      (poly.mul_congr _ (ptop_ppowOf P n))

/-- The split's product at occupied factor tops has an occupied outer
top. -/
private theorem ptop_splitProdGo_occ : ∀ (j : Nat) (S : List poly.PPoly),
    0 < j →
    (∀ i, i < S.length → ¬ poly.unitTail (poly.ptop (ground.getAt [] S i))) →
    ¬ poly.unitTail (poly.ptop (splitProdGo j S))
  | _, [], _, _, h => ground.BPair.ofPos_off Pos.one h.1
  | j, Q :: S, _, hS, h =>
    match poly.unitTail_mul_of (poly.unitTail_oneValue_right h
        (ptop_pmul (ppowOf Q j) (splitProdGo (j + 1) S))) with
    | .inl h1 =>
      poly.powOf_occupied (hS 0 (Nat.succ_pos _)) j
        (poly.unitTail_oneValue_right h1 (ptop_ppowOf Q j))
    | .inr h2 =>
      ptop_splitProdGo_occ (j + 1) S (Nat.succ_pos j)
        (fun i hi => hS (i + 1) (Nat.succ_lt_succ hi)) h2

/-- The split's product's outer top evaluated off the unit at a base
point puts every factor's outer top off the unit there: the tops
multiply, the powers at positive exponents. -/
private theorem ptop_splitProdGo_off (t : BPair) :
    ∀ (j : Nat) (S : List poly.PPoly), 0 < j →
    ¬ (poly.eval (poly.ptop (splitProdGo j S)) t).oneValue BPair.unit →
    ∀ i, i < S.length →
      ¬ (poly.eval (poly.ptop (ground.getAt [] S i)) t).oneValue BPair.unit
  | _, [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | j, Q :: S, hj, h, 0, _ => by
    intro hq
    apply h
    refine BPair.oneValue_trans
      (poly.eval_congr (ptop_pmul (ppowOf Q j) (splitProdGo (j + 1) S)) t) ?_
    refine BPair.oneValue_trans (poly.eval_mul _ _ t) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left ?_) (BPair.unit_mul _)
    refine BPair.oneValue_trans (poly.eval_congr (ptop_ppowOf Q j) t) ?_
    cases j with
    | zero => exact absurd hj (Nat.lt_irrefl 0)
    | succ j' =>
      show (poly.eval (poly.mul (poly.ptop Q) (poly.powOf (poly.ptop Q) j'))
        t).oneValue BPair.unit
      exact BPair.oneValue_trans (poly.eval_mul _ _ t)
        (BPair.oneValue_trans (BPair.mul_congr_left hq) (BPair.unit_mul _))
  | j, Q :: S, _, h, i + 1, hi => by
    refine ptop_splitProdGo_off t (j + 1) S (Nat.succ_pos j) ?_ i
      (Nat.lt_of_succ_lt_succ hi)
    intro hs
    apply h
    refine BPair.oneValue_trans
      (poly.eval_congr (ptop_pmul (ppowOf Q j) (splitProdGo (j + 1) S)) t) ?_
    refine BPair.oneValue_trans (poly.eval_mul _ _ t) ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hs) (BPair.mul_unit _)

/-- The evaluated split's product is occupied when every factor's
evaluation is. -/
private theorem evalSplit_occupied (t : BPair) :
    ∀ (k : Nat) (S : List poly.PPoly),
    (∀ i, i < S.length →
      ¬ poly.unitTail (poly.pevalB (ground.getAt [] S i) t)) →
    ¬ poly.unitTail (evalSplit t k S)
  | _, [], _, h => BPair.ofPos_off Pos.one h.1
  | k, _ :: S, hS, h =>
    match poly.unitTail_mul_of h with
    | .inl h1 => poly.powOf_occupied (hS 0 (Nat.succ_pos _)) k h1
    | .inr h2 => evalSplit_occupied t (k + 1) S
        (fun i hi => hS (i + 1) (Nat.succ_lt_succ hi)) h2

/-- A root of the evaluated split is a root of a listed factor. -/
private theorem evalSplit_root (t r : BPair) :
    ∀ (k : Nat) (S : List poly.PPoly),
    0 < k → poly.isRoot (evalSplit t k S) r →
    ∃ i, i < S.length ∧ poly.isRoot (poly.pevalB (ground.getAt [] S i) t) r
  | _, [], _, h => absurd h (poly.isRoot_one r)
  | k, _ :: S, hk, h =>
    match (poly.isRoot_mul _ _ r).mp h with
    | .inl h1 => ⟨0, Nat.succ_pos _, (poly.isRoot_powOf _ r k hk).mp h1⟩
    | .inr h2 =>
      match evalSplit_root t r (k + 1) S (Nat.succ_pos k) h2 with
      | ⟨i, hi, hr⟩ => ⟨i + 1, Nat.succ_lt_succ hi, hr⟩

/-- The evaluated split's multiplicity at a root of exactly one
listed factor, simple there: the factor's exponent. -/
private theorem evalSplit_mult (t r : BPair) :
    ∀ (k j : Nat) (S : List poly.PPoly),
    (∀ i, i < S.length →
      ¬ poly.unitTail (poly.pevalB (ground.getAt [] S i) t)) →
    j < S.length →
    poly.multAt [r.swap] (poly.pevalB (ground.getAt [] S j) t) = 1 →
    (∀ i, i < S.length → ¬ i = j →
      ¬ poly.isRoot (poly.pevalB (ground.getAt [] S i) t) r) →
    poly.multAt [r.swap] (evalSplit t k S) = k + j
  | _, j, [], _, hj, _, _ => absurd hj (Nat.not_lt_zero j)
  | k, j, Q :: S, hS, hj, hm, hoff => by
    have hQ : ¬ poly.unitTail (poly.pevalB Q t) := hS 0 (Nat.succ_pos _)
    have hS' : ∀ i, i < S.length →
        ¬ poly.unitTail (poly.pevalB (ground.getAt [] S i) t) :=
      fun i hi => hS (i + 1) (Nat.succ_lt_succ hi)
    show poly.multAt [r.swap]
      (poly.mul (poly.powOf (poly.pevalB Q t) k) (evalSplit t (k + 1) S))
      = k + j
    rw [poly.multAt_mul r _ _ (poly.powOf_occupied hQ k)
        (evalSplit_occupied t (k + 1) S hS'),
      poly.multAt_powOf r _ hQ k]
    match j, hj, hm, hoff with
    | 0, _, hm, hoff =>
      have hrest : poly.multAt [r.swap] (evalSplit t (k + 1) S) = 0 := by
        have hnr : ¬ poly.isRoot (evalSplit t (k + 1) S) r := fun hr =>
          match evalSplit_root t r (k + 1) S (Nat.succ_pos k) hr with
          | ⟨i, hi, hri⟩ =>
            hoff (i + 1) (Nat.succ_lt_succ hi) (Nat.noConfusion) hri
        cases Nat.lt_or_ge 0 (poly.multAt [r.swap] (evalSplit t (k + 1) S)) with
        | inl hpos =>
          exact absurd
            ((poly.multAt_pos r _ (evalSplit_occupied t (k + 1) S hS')).mpr hpos) hnr
        | inr hle => exact Nat.le_antisymm hle (Nat.zero_le _)
      have hm' : poly.multAt [r.swap] (poly.pevalB Q t) = 1 := hm
      rw [hm', hrest, Nat.mul_one, Nat.add_zero]
    | j + 1, hj, hm, hoff =>
      have hQ0 : poly.multAt [r.swap] (poly.pevalB Q t) = 0 := by
        have hnr : ¬ poly.isRoot (poly.pevalB Q t) r :=
          hoff 0 (Nat.succ_pos _) (fun h => Nat.noConfusion h)
        cases Nat.lt_or_ge 0 (poly.multAt [r.swap] (poly.pevalB Q t)) with
        | inl hpos => exact absurd ((poly.multAt_pos r _ hQ).mpr hpos) hnr
        | inr hle => exact Nat.le_antisymm hle (Nat.zero_le _)
      rw [hQ0, Nat.mul_zero, Nat.zero_add,
        evalSplit_mult t r (k + 1) j S hS' (Nat.lt_of_succ_lt_succ hj) hm
          (fun i hi hij => hoff (i + 1) (Nat.succ_lt_succ hi)
            (fun h => hij (Nat.succ.inj h))),
        Nat.add_assoc, Nat.add_comm 1 j]


/-- `thm:divisorid`(ii)'s specialization: at a base point off the
crossing read's locus with the pencil polynomial's leading
coefficient off the unit there — the leading coefficients multiply to
it, so the content's and every factor's read unequal members and the
degrees hold — every root of the pencil polynomial is a root of
exactly one factor, simple in it, at the factor's place as its
multiplicity in the pencil polynomial: root collisions sit on the
crossing read's locus alone. -/
theorem specialize (χ : poly.PPoly) (c : poly.Poly) (S : List poly.PPoly)
    (h : splitRead χ c S) (t : BPair)
    (hD : ¬ (poly.eval (crossD S) t).oneValue BPair.unit)
    (hlead : ¬ (poly.eval (poly.ptop χ) t).oneValue BPair.unit)
    (r : BPair) (hr : poly.isRoot (poly.pevalB χ t) r) :
    ∃ j, j < S.length
      ∧ poly.isRoot (poly.pevalB (ground.getAt [] S j) t) r
      ∧ poly.multAt [r.swap] (poly.pevalB (ground.getAt [] S j) t) = 1
      ∧ (∀ i, i < S.length →
          poly.isRoot (poly.pevalB (ground.getAt [] S i) t) r → i = j)
      ∧ poly.multAt [r.swap] (poly.pevalB χ t) = j + 1 := by
  have hE : poly.oneValue (poly.pevalB χ t)
      (poly.mul [poly.eval c t] (evalSplit t 1 S)) :=
    poly.oneValue_trans (poly.pevalB_congr t h.1)
      (poly.oneValue_trans (poly.pevalB_pmul [c] _ t)
        (poly.mul_congr _ (pevalB_splitProd t S)))
  -- the content is off the unit at the point: at the unit the pencil
  -- polynomial's evaluation is a unit tail against its leading read
  have hc : ¬ (poly.eval c t).oneValue BPair.unit := by
    intro hcu
    apply hlead
    rw [← poly.top_pevalB]
    exact poly.top_unitTail (poly.unitTail_oneValue_right
      (poly.of_unitTail_mul (p := [poly.eval c t]) (q := evalSplit t 1 S)
        (Or.inl (And.intro hcu trivial)))
      (poly.oneValue_symm hE))
  -- the leading coefficients multiply: the split's outer top is the
  -- content against the factors' tops' product
  have htops : ∀ i, i < S.length →
      ¬ poly.unitTail (poly.ptop (ground.getAt [] S i)) :=
    fun i hi => (primAll_topOff S h.2 i hi).2
  have hQocc : ¬ poly.unitTail (poly.ptop (poly.pmul [c] (splitProd S))) :=
    fun hu =>
      match poly.unitTail_mul_of
          (poly.unitTail_oneValue_right hu (ptop_pmul [c] (splitProd S))) with
      | .inl hcu => hc (poly.eval_unitTail hcu t)
      | .inr hs => ptop_splitProdGo_occ 1 S (Nat.succ_pos 0) htops hs
  have hχocc : ¬ poly.unitTail (poly.ptop χ) :=
    fun hu => hlead (poly.eval_unitTail hu t)
  have hlead' : ¬ (poly.eval (poly.mul c (poly.ptop (splitProd S))) t).oneValue
      BPair.unit :=
    fun hu => hlead (BPair.oneValue_trans
      (poly.eval_congr (poly.ptop_congr h.1 hχocc hQocc) t)
      (BPair.oneValue_trans
        (poly.eval_congr (ptop_pmul [c] (splitProd S)) t) hu))
  have htop : ∀ i, i < S.length →
      ¬ (poly.top (poly.pevalB (ground.getAt [] S i) t)).oneValue
        BPair.unit := by
    intro i hi
    rw [poly.top_pevalB]
    refine ptop_splitProdGo_off t 1 S (Nat.succ_pos 0) ?_ i hi
    intro hs
    exact hlead' (BPair.oneValue_trans (poly.eval_mul _ _ t)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hs) (BPair.mul_unit _)))
  have hocc : ∀ i, i < S.length →
      ¬ poly.unitTail (poly.pevalB (ground.getAt [] S i) t) :=
    fun i hi hu => htop i hi (poly.top_unitTail hu)
  have hDs := (eval_mul_off hD).1
  have hDp := (eval_mul_off hD).2
  have hcl : ¬ poly.unitTail [poly.eval c t] := fun hu => hc hu.1
  have hcr : ¬ poly.isRoot [poly.eval c t] r := fun hx =>
    hc (BPair.oneValue_trans (BPair.oneValue_symm (poly.eval_one _ r)) hx)
  -- a root of the pencil polynomial is a root of a listed factor
  have hr' : poly.isRoot (poly.mul [poly.eval c t] (evalSplit t 1 S)) r :=
    poly.isRoot_congr hE hr
  obtain ⟨j, hj, hrj⟩ : ∃ j, j < S.length
      ∧ poly.isRoot (poly.pevalB (ground.getAt [] S j) t) r :=
    match (poly.isRoot_mul _ _ r).mp hr' with
    | .inl h1 => absurd h1 hcr
    | .inr h2 => evalSplit_root t r 1 S (Nat.succ_pos 0) h2
  -- two listed factors share no root: their resultant is off the unit
  have hW : ∀ i, i < S.length →
      poly.isRoot (poly.pevalB (ground.getAt [] S i) t) r →
      ∀ q : poly.Poly,
      0 < (poly.pevalB (ground.getAt [] S i) t).length - 1 + (q.length - 1) :=
    fun i hi hri q => Nat.lt_of_lt_of_le
      (length_of_root _ (htop i hi) r hri) (Nat.le_add_right _ _)
  have hu : ∀ i, i < S.length →
      poly.isRoot (poly.pevalB (ground.getAt [] S i) t) r → i = j := by
    intro i hi hri
    match Nat.lt_or_ge i j with
    | .inl hij =>
      exact absurd (resultant_unit_of_roots _ _ (hW i hi hri _) r hri hrj)
        (crossPairs_off t S hDp i j hij hj)
    | .inr hge =>
      match Nat.lt_or_ge j i with
      | .inl hji =>
        exact absurd (resultant_unit_of_roots _ _ (hW j hj hrj _) r hrj hri)
          (crossPairs_off t S hDp j i hji hi)
      | .inr hle => exact Nat.le_antisymm hle hge
  -- the root is simple in its factor
  have hm1 : poly.multAt [r.swap] (poly.pevalB (ground.getAt [] S j) t)
      = 1 := by
    have hpos : 0 < poly.multAt [r.swap]
        (poly.pevalB (ground.getAt [] S j) t) :=
      (poly.multAt_pos r _ (hocc j hj)).mp hrj
    have hlt : ¬ 2 ≤ poly.multAt [r.swap]
        (poly.pevalB (ground.getAt [] S j) t) := fun h2 =>
      crossSelf_off t S hDs j hj
        (resultant_unit_of_roots _ _ (hW j hj hrj _) r hrj
          (poly.isRoot_congr
            (poly.oneValue_symm (pevalB_pderiv t (ground.getAt [] S j)))
            (poly.multAt_deriv r _ (hocc j hj) h2)))
    exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hlt)) hpos
  refine ⟨j, hj, hrj, hm1, hu, ?_⟩
  -- the multiplicity in the pencil polynomial is the factor's place
  have hEocc : ¬ poly.unitTail (poly.mul [poly.eval c t] (evalSplit t 1 S)) :=
    fun hu => match poly.unitTail_mul_of hu with
      | .inl h1 => hcl h1
      | .inr h2 => evalSplit_occupied t 1 S hocc h2
  have hχev : ¬ poly.unitTail (poly.pevalB χ t) := fun hu =>
    hEocc (poly.unitTail_oneValue_right hu hE)
  rw [poly.multAt_congr r hE hχev,
    poly.multAt_mul r _ _ hcl (evalSplit_occupied t 1 S hocc),
    evalSplit_mult t r 1 j S hocc hj hm1
      (fun i hi hij hri => hij (hu i hi hri))]
  have hc0 : poly.multAt [r.swap] [poly.eval c t] = 0 := by
    cases Nat.lt_or_ge 0 (poly.multAt [r.swap] [poly.eval c t]) with
    | inl hpos => exact absurd ((poly.multAt_pos r _ hcl).mpr hpos) hcr
    | inr hle => exact Nat.le_antisymm hle (Nat.zero_le _)
  rw [hc0, Nat.zero_add, Nat.add_comm]

/-- `thm:divisorid`(iii)'s cell read: the one pencil at two levels
`l < h`, the carriers the level datum's own — on a cell certified
at both, a point reading the pair at `l` positive semidefinite and
the count `n` at `h` transports both reads to every point of the
cell, the ground multiplicity one integer on the cell; the
boundary's two-sided bracket counts are the emitted records'
entries with clause (ii) confining a move to a ground collision on
the crossing read's locus. -/
theorem groundMult {o : Nat} (A B G : elim.Mat) (mid : List BPair)
    (xl yl xh yh : Pos)
    (_hlh : (⟨xl, yl⟩ : BPair) < ⟨xh, yh⟩)
    (lo hi : CPair) (covl covh : cellcount.Cover)
    (hcl : cellcount.coverRead (cellcount.levelPMat A B G xl yl mid)
      o (mid.length + 1) lo hi covl)
    (hch : cellcount.coverRead (cellcount.levelPMat A B G xh yh mid)
      o (mid.length + 1) lo hi covh)
    (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos)
    (hlx : lo ≤ (⟨xn, xc⟩ : CPair)) (hxh : (⟨xn, xc⟩ : CPair) ≤ hi)
    (hly : lo ≤ (⟨yn, yc⟩ : CPair)) (hyh : (⟨yn, yc⟩ : CPair) ≤ hi)
    (n : Nat) (spxl spxh : inertia.Split o)
    (hx0 : cellcount.countAt (cellcount.levelPMat A B G xl yl mid)
      (mid.length + 1) xn xc 0 spxl)
    (hxn : cellcount.countAt (cellcount.levelPMat A B G xh yh mid)
      (mid.length + 1) xn xc n spxh)
    (spyl spyh : inertia.Split o)
    (hyl : inertia.splitRead
      (cellcount.evalPC (cellcount.levelPMat A B G xl yl mid)
        yn yc (mid.length + 1)) spyl)
    (hyh2 : inertia.splitRead
      (cellcount.evalPC (cellcount.levelPMat A B G xh yh mid)
        yn yc (mid.length + 1)) spyh) :
    inertia.psdAt spyl ∧ inertia.revAt spyh = n :=
  ⟨cellcount.cellCount (cellcount.levelPMat A B G xl yl mid)
      (mid.length + 1) 0 lo hi covl hcl xn xc hlx hxh spxl hx0
      yn yc hly hyh spyl hyl,
   cellcount.cellCount (cellcount.levelPMat A B G xh yh mid)
      (mid.length + 1) n lo hi covh hch xn xc hlx hxh spxh hxn
      yn yc hly hyh spyh hyh2⟩

end divisorid
