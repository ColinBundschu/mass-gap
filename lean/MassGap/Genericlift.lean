import MassGap.Split
import MassGap.Stagesplit
import MassGap.Windowsep
/-!
`lem:genericlift` — the generic lift's polynomial-pair calculus.  A
polynomial pair `[P : Q]` is a pair of ground polynomials named as
`def:ground`'s constructed pairs are, read at every natural
argument through the members' Horner reads and across
representatives by the cross-multiplied identities (`PPair`,
`agreeAt` the one-value read at an argument, `crossD` the
cross-multiplied site datum, `pCofactor` the total cofactor at the
components' cross products).  Clause (i)'s certificate: two pairs
at one value on a pairwise-apart argument list beyond the cross
datum's keys read one value as polynomials, the first member's
located roots inside `thm:windowsep`'s bound (`liftRead` the
per-argument display at the pairs' site reads `pairOcc`, the
occupied second member `def:ground`'s positive datum mirrored;
`crossNull` the symbolic conclusion; the count-against-degree
theorem at `prop:wg`'s scheme outputs and `lem:rankstable`(i)'s
lifts, the batteries tying the two).  A pair moves to its reduced
representative at the descent's tuple (`pReduce`: `thm:windowsep`'s
`gcdD` decided through `stagesplit.gcdRead`, the cofactors
cross-cleared the moved representative, the pair itself wherever the
certificate refuses), the move reading one value with its own pair
(`pReduce_read`, the two arms the reflexivity at the memberwise
swap's cancellation and the two stated factors chased through the
convolution's algebra); `pAddR` is the displayed sum at that
representative, the second spelling carrying the same bridge, the
fold's value the displayed sum's at every seam.  Clause (ii): the
adjugate identity at the polynomial carrier (`split.padj`,
`split.adjRead_all`, `split.adjColRead_all`), the determinant
pair off equal members the genericity read (`detOcc`, the
per-residue Gram independence its instances), the solve stated
at the pair-entried carrier (`PPMat`, the first-row fold `ppminor`,
the transposed cofactors `ppadj`, and `ppadjRead` the whole
identity at `ppSquare`'s stated-order shape read, an unshaped
matrix reading vacuously — the instance deciding at the descent's
pair adjugate `ppadjD` on the occupied square frame with
`ppadjD_eq` the entrywise cross read, the fold branch the further
frames'), `con:res`'s solves the recorded
consumer.  Clause (iii): a pair keeps one side beyond its
members' largest located root — the
radius clearance at a natural argument is the cleared comparison
against `thm:windowsep`'s leading-term bound (`radiusClears`,
`clearsPair`), and the settled side is the leading coefficient's
own (`topUpper`, `topLower`), one decidable read per pair, the
beyond-radius side theorem (`sideUpper`, `sideLower`,
`windowsep.lead_upper`'s instance at the positive
arguments) at `lem:rankstable`(iii)'s
and the decimation's cutoff comparisons with the batteries' eval
pins beside it.  Clause (iv): a claim over
finitely many pairs holds at every residue beyond their computed
radii once its symbolic reads hold (`clearsAll` the radii's fold),
the finitely many residues at or below each their own window read
(`Rec` the divisor record with its floor, clearance, settled point
and classified ranks, `sideCert` clause (iii)'s hypothesis pair at
the settled point, `rootsCert` the window below it with its root
list, `rootsAt` a classification's lookup at a record's places)
— `prop:wg`'s scheme, `con:res`'s solves,
`lem:rankstable`(iii)'s and `lem:serstable`(iii)'s symbolic
counts and the decimation's entry lists the recorded consumers.
Clause (v), the rank read: an exponential-polynomial pair's member
in a natural is the outer polynomial (`poly.PPoly`) read at the
coefficients' Horner reads at the natural and at the outer point
`2^ℓ` (`expoEval`), two members' sums and products the outer sum
and product read as the sum and the product (`expoEval_padd`,
`expoEval_pmul`); the top polynomial is the outer representative's top
(`expoTop` at `poly.ptrim`), and the top's data are the leading
margin at the radius (`windowsep.leadMargin`, the leading-term
bound's own read, positive at an occupied top), the tail
coefficients' magnitudes' fold (`expoTailFold`) and the tail's
largest degree (`expoTailDeg`); the
comparison `c 2^ℓ > F ℓ^m` cleared at the radius' second member's
power (`expoCompare`), the stepping's start at the radius and
`4m²` (`radiusCeil`, `expoStart`), its witness the larger of
`4(m+1)²`, the radius and `[F : c]` (`expoWit`), and the computed
natural the least natural at or beyond the start holding the
comparison, the halving read at the witness (`expoPred`,
`expoKey`); the settled side theorems at every natural at or
beyond it (`expoUpper`, `expoLower`, the tail's magnitude below
the top's at `windowsep.leadTerm_ge` and `windowsep.lead_upper`'s
side for the top); and
clause (iv) at these pairs, the record with its side certificate
and the window below the computed natural (`ERec`,
`expoSideCert`, `expoRootsCert`) and the computed naturals' fold
(`expoClearsAll`) — `lem:serstable`(iii)'s rank divisors and
`lem:serdivisors`' stencil caps the consumers.
-/

namespace genericlift
open ground poly elim

/-- Two pairs read one value at an argument, the cross-multiplied
Horner reads. -/
def agreeAt (x y : PPair) (r : BPair) : Prop :=
  BPair.oneValue (poly.eval x.1 r * poly.eval y.2 r)
    (poly.eval y.1 r * poly.eval x.2 r)

instance instGenericlift1 (x y : PPair) (r : BPair) : Decidable (agreeAt x y r) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The pair's site read: the second member occupied,
`def:ground`'s positive second datum mirrored at the polynomial
carrier. -/
def pairOcc (x : PPair) : Prop := ¬ poly.unitTail x.2

instance instGenericlift2 (x : PPair) : Decidable (pairOcc x) :=
  @instDecidableNot _ (poly.decUnitTail _)

/-- The pair's site read at an argument: the second member's value
occupied there. -/
def pairOccAt (x : PPair) (r : BPair) : Prop :=
  (poly.eval x.2 r).offUnit

instance instGenericlift3 (x : PPair) (r : BPair) : Decidable (pairOccAt x r) :=
  @instDecidableNot _ inferInstance

/-- The cross-multiplied site datum of two pairs, the difference's
polynomial. -/
def crossD (x y : PPair) : Poly :=
  poly.add (poly.mul x.1 y.2) ((poly.mul y.1 x.2).map BPair.swap)

/-- The symbolic conclusion: the cross datum reads the sum's unit
at every key, the pairs one value at every argument. -/
def crossNull (x y : PPair) : Prop := poly.unitTail (crossD x y)

instance instGenericlift4 (x y : PPair) : Decidable (crossNull x y) :=
  poly.decUnitTail _

/-- The cross datum's unit tail is the two products' one-value
read, both ways at the difference's own bridges. -/
theorem crossNull_ov (x y : PPair) :
    crossNull x y ↔
    poly.oneValue (poly.mul x.1 y.2) (poly.mul y.1 x.2) :=
  ⟨fun h => poly.ov_of_diff h, fun h => poly.diff_unitTail h⟩

/-- The cross read's bundle, the pair carrier's entry read. -/
def crossRead : ground.DRead PPair :=
  ⟨crossNull, fun _ _ => poly.decUnitTail _⟩

/-- The cross read at one pair, the difference's own unit tail. -/
private theorem crossNull_refl (x : PPair) : crossNull x x :=
  poly.add_neg (poly.mul x.1 x.2)

/-- The cross read exchanges its pairs. -/
private theorem crossNull_symm {x y : PPair} (h : crossNull x y) :
    crossNull y x :=
  (crossNull_ov y x).mpr
    (poly.oneValue_symm ((crossNull_ov x y).mp h))

/-- The cross read composes at an occupied middle second member. -/
private theorem crossNull_trans {x y z : PPair}
    (hy : ¬ poly.unitTail y.2) (h1 : crossNull x y)
    (h2 : crossNull y z) : crossNull x z :=
  (crossNull_ov x z).mpr
    (elim.cross_trans hy ((crossNull_ov x y).mp h1)
      ((crossNull_ov y z).mp h2))

/-- The pair at its certified reduction: where the descent's tuple
decides the greatest common divisor's read, the cofactors
cross-cleared are the pair at the reduced representative;
anywhere else the pair itself — one value either way, the
representative the one moved datum. -/
def pReduce (x : PPair) : PPair :=
  let d := windowsep.gcdD x.1 x.2
  if decide (stagesplit.gcdRead x.1 x.2 d.g d.A d.B d.u d.v
      d.top d.cA d.cB d.c)
  then (d.A.map (fun e => e.scale d.cB),
        d.B.map (fun e => e.scale d.cA))
  else x

/-- The displayed sum at the reduced representative, the second
spelling with its bridge. -/
def pAddR (x y : PPair) : PPair := pReduce (pAdd x y)

/-- The bridge: the reduction reads one value with its pair. -/
theorem pReduce_read (x : PPair) : crossNull (pReduce x) x := by
  have hneg : crossNull x x := poly.add_neg (poly.mul x.1 x.2)
  have hpos : ∀ d : windowsep.GcdData,
      stagesplit.gcdRead x.1 x.2 d.g d.A d.B d.u d.v
        d.top d.cA d.cB d.c →
      crossNull (d.A.map (fun e => e.scale d.cB),
        d.B.map (fun e => e.scale d.cA)) x := by
    intro d hg
    have F1 : poly.oneValue
        (poly.mul (poly.topped d.g d.top) d.A)
        (x.1.map (fun y => y.scale d.cA)) := hg.1
    have F2 : poly.oneValue
        (poly.mul (poly.topped d.g d.top) d.B)
        (x.2.map (fun y => y.scale d.cB)) := hg.2.1
    have hL : poly.oneValue
        (poly.mul (d.A.map (fun e => e.scale d.cB)) x.2)
        (poly.mul (poly.mul (poly.topped d.g d.top) d.A) d.B) :=
      poly.oneValue_trans
        (poly.mul_congr_left
          (poly.oneValue_symm (poly.ofPos_scale d.cB d.A)) x.2)
        (poly.oneValue_trans
          (poly.mul_assoc [BPair.ofPos d.cB] d.A x.2)
          (poly.oneValue_trans
            (poly.mul_left_comm [BPair.ofPos d.cB] d.A x.2)
            (poly.oneValue_trans
              (poly.mul_congr d.A
                (poly.oneValue_trans (poly.ofPos_scale d.cB x.2)
                  (poly.oneValue_symm F2)))
              (poly.oneValue_trans
                (poly.mul_left_comm d.A (poly.topped d.g d.top) d.B)
                (poly.oneValue_symm
                  (poly.mul_assoc (poly.topped d.g d.top)
                    d.A d.B))))))
    have hR : poly.oneValue
        (poly.mul x.1 (d.B.map (fun e => e.scale d.cA)))
        (poly.mul (poly.mul (poly.topped d.g d.top) d.A) d.B) :=
      poly.oneValue_trans
        (poly.mul_congr x.1
          (poly.oneValue_symm (poly.ofPos_scale d.cA d.B)))
        (poly.oneValue_trans
          (poly.mul_left_comm x.1 [BPair.ofPos d.cA] d.B)
          (poly.oneValue_trans
            (poly.oneValue_symm
              (poly.mul_assoc [BPair.ofPos d.cA] x.1 d.B))
            (poly.mul_congr_left
              (poly.oneValue_trans (poly.ofPos_scale d.cA x.1)
                (poly.oneValue_symm F1)) d.B)))
    exact poly.oneValue_unitTail
      (poly.add_congr (poly.oneValue_trans hL (poly.oneValue_symm hR))
        (poly.oneValue_refl _))
      (poly.add_neg (poly.mul x.1 (d.B.map (fun e => e.scale d.cA))))
  have key : ∀ d : windowsep.GcdData, crossNull
      (if decide (stagesplit.gcdRead x.1 x.2 d.g d.A d.B d.u d.v
          d.top d.cA d.cB d.c)
       then (d.A.map (fun e => e.scale d.cB),
             d.B.map (fun e => e.scale d.cA))
       else x) x := by
    intro d
    exact
      (if hc : stagesplit.gcdRead x.1 x.2 d.g d.A d.B d.u d.v
          d.top d.cA d.cB d.c
       then by rw [if_pos (decide_eq_true hc)]; exact hpos d hc
       else by
         rw [if_neg (fun h => hc (of_decide_eq_true h))]
         exact hneg)
  rw [pReduce]
  generalize windowsep.gcdD x.1 x.2 = d
  exact key d

/-- A pairwise-apart argument list, the values' own distinctness. -/
def pairwiseApart : List BPair → Prop
  | [] => True
  | r :: t =>
    (t.all (fun s => !(decide (r.oneValue s)))) = true
    ∧ pairwiseApart t

def decPairwiseApart : ∀ l : List BPair, Decidable (pairwiseApart l)
  | [] => isTrue trivial
  | _ :: t =>
    @instDecidableAnd _ _ inferInstance (decPairwiseApart t)

instance instGenericlift5 (l : List BPair) : Decidable (pairwiseApart l) :=
  decPairwiseApart l

/-- Clause (i)'s certificate: one value at a pairwise-apart list
beyond the cross datum's keys — the datum's roots at most its
degree, so the equal-members read lifts to every argument, the
theorem's data. -/
def liftRead (x y : PPair) (pts : List BPair) : Prop :=
  pairOcc x ∧ pairOcc y
  ∧ pairwiseApart pts
  ∧ (crossD x y).length ≤ pts.length
  ∧ (pts.all (fun r => decide (poly.isRoot (crossD x y) r))) = true

instance instGenericlift6 (x y : PPair) (pts : List BPair) :
    Decidable (liftRead x y pts) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _))

/-- The genericity read: the determinant pair off equal members,
the per-residue Gram independence its instances. -/
def detOcc (m : split.PMat) : Prop :=
  ¬ poly.unitTail (split.pminor m)

instance instGenericlift7 (m : split.PMat) : Decidable (detOcc m) :=
  match elim.decRowsLen m.length m with
  | isTrue hsq =>
    decidable_of_iff (¬ poly.unitTail (elim.pdetD m))
      ⟨fun hn hu => hn
        (poly.oneValue_unitTail (elim.pdetD_eq m hsq) hu),
       fun hn hu => hn
        (poly.unitTail_oneValue_right hu (elim.pdetD_eq m hsq))⟩
  | isFalse _ => @instDecidableNot _ (poly.decUnitTail _)

/-- The radius clearance at a natural argument: the argument's
cleared comparison against the leading-term bound. -/
def radiusClears (P : Poly) (an : Pos) : Prop :=
  windowsep.radiusN P ≤ BPair.ofPos an * windowsep.radiusD P

instance instGenericlift9 (P : Poly) (an : Pos) : Decidable (radiusClears P an) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The pair's clearance, both members'. -/
def clearsPair (x : PPair) (an : Pos) : Prop :=
  radiusClears x.1 an ∧ radiusClears x.2 an

instance instGenericlift10 (x : PPair) (an : Pos) : Decidable (clearsPair x an) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The settled side's upper read, the leading coefficient's own
at the value's representative, the degree's own read. -/
def topUpper (P : Poly) : Prop :=
  BPair.unit < poly.top (poly.vnorm P)

instance instGenericlift11 (P : Poly) : Decidable (topUpper P) :=
  inferInstanceAs (Decidable (_ < _))

/-- The settled side's lower read. -/
def topLower (P : Poly) : Prop :=
  poly.top (poly.vnorm P) < BPair.unit

instance instGenericlift12 (P : Poly) : Decidable (topLower P) :=
  inferInstanceAs (Decidable (_ < _))

set_option genInjectivity false in
/-- A rank-divisor record: the divisor, its domain's floor, its
clearance (a comparison's ranks are those clearing its families'
reaches), its settled point, and the domain's equal-members ranks
below the settled point (`lem:genericlift`(iii),(iv) at
`lem:rankstable`(iii)'s divisors). -/
structure Rec where
  div : Poly
  lo : Nat
  cl : Nat
  an : Nat
  roots : List Nat

/-- The settled side's certificate, clause (iii)'s side theorems'
hypothesis pair: the radius cleared at the settled point beside the
leading coefficient's own side. -/
def sideCert (R : Rec) : Prop :=
  radiusClears R.div (ground.posOfNat R.an) ∧ (topUpper R.div ∨ topLower R.div)

instance instGenericlift18 (R : Rec) : Decidable (sideCert R) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A classification's lookup at a record's places: the ranks the
table lists at the place pair. -/
def rootsAt (S : List (Nat × Nat × Nat)) (i j : Nat) : List Nat :=
  (S.filter (fun t => decide (t.1 = i) && decide (t.2.1 = j))).map (fun t => t.2.2)

/-- Clause (iv)'s window below the settled point, the ranks from the
domain's floor: the root list holds ranks of the window, each once;
at a counted rank the divisor's evaluation ties the sum's unit; at a
cleared rank off the roots it sits on the divisor's own leading side;
below the clearance off the roots it sits off the sum's unit. -/
def rootsCert (R : Rec) : Prop :=
  (R.roots.all (fun k => decide (R.lo ≤ k) && decide (k < R.an))) = true
  ∧ ground.distinctList R.roots
  ∧ ((List.range R.an).filter (fun k => R.lo ≤ k)).all (fun k =>
    if 0 < ground.countOf k R.roots then
      decide ((poly.eval R.div
        ⟨ground.posOfSucc k, ground.posOfSucc 0⟩).oneValue ground.BPair.unit)
    else if R.cl ≤ k then
      (decide (topUpper R.div)
        && decide (ground.BPair.unit < poly.eval R.div
          ⟨ground.posOfSucc k, ground.posOfSucc 0⟩))
      || (decide (topLower R.div)
        && decide (poly.eval R.div
          ⟨ground.posOfSucc k, ground.posOfSucc 0⟩ < ground.BPair.unit))
    else
      !(decide ((poly.eval R.div
        ⟨ground.posOfSucc k, ground.posOfSucc 0⟩).oneValue ground.BPair.unit))) = true

instance instGenericlift19 (R : Rec) : Decidable (rootsCert R) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! Clause (iii)'s side theorem: beyond the radius the leading
term dominates.  At a margin `y = 1 + d` the geometric telescope
`d · Σ_{i<k} y^i + 1 = y^k` reads the below-top coefficients' cap
`H · Σ_{i<k} y^i` below the top's own `c · y^k`, and the telescope
enters here as the running invariant `H ≤ d · eval`: the radius'
read `c + H ≤ y · c` seeds it at the top monomial and each further
coefficient, priced at or above the height's balance partner,
preserves it exactly. -/

/-- Clause (iii)'s side theorem, the top's upper side: at or beyond
the cleared radius a pair member with an upper leading coefficient
evaluates strictly above the sum's unit — the leading term
dominates the below-top cap at the geometric telescope. -/
theorem sideUpper : ∀ (P : poly.Poly) (an : ground.Pos),
    radiusClears P an → topUpper P →
    ∀ n : ground.Pos, an ≤ n →
    ground.BPair.unit < poly.eval P (ground.BPair.ofPos n) := by
  intro P an hcl htop n hle
  have hx : windowsep.radiusN P
      ≤ windowsep.mag (BPair.ofPos n) * windowsep.radiusD P := by
    rw [windowsep.mag_unitLe (ground.leB_of_lt (ground.unitLtOfPos n))]
    refine ground.leB_trans hcl ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        (BPair.mul_comm (windowsep.radiusD P) (BPair.ofPos an)))
      (BPair.oneValue_of_eq
        (BPair.mul_comm (windowsep.radiusD P) (BPair.ofPos n)))
      (ground.leB_mulR (windowsep.unitLe_radiusD P) (ground.leB_ofPos hle))
  exact windowsep.lead_upper P (BPair.ofPos n) hx
    (ground.unitLtMul htop
      (ground.unitLtBpow (ground.unitLtOfPos n) _))

/-- Clause (iii)'s side theorem, the top's lower side: the upper
read at the memberwise swap, the radius and the height unchanged
across the balance partners. -/
theorem sideLower : ∀ (P : poly.Poly) (an : ground.Pos),
    radiusClears P an → topLower P →
    ∀ n : ground.Pos, an ≤ n →
    poly.eval P (ground.BPair.ofPos n) < ground.BPair.unit := by
  intro P an hcl htop n hle
  have hclN : radiusClears (poly.neg P) an := by
    unfold radiusClears
    rw [windowsep.radiusN_neg P, windowsep.radiusD_neg P]
    exact hcl
  have htopN : topUpper (poly.neg P) := by
    unfold topUpper
    rw [poly.vnorm_neg P, poly.top_neg (poly.vnorm P)]
    exact ground.ltB_swap htop
  have h := sideUpper (poly.neg P) an hclN htopN n hle
  rw [poly.eval_neg P (BPair.ofPos n)] at h
  exact ground.ltB_swap h

/-- Clause (iv)'s radii fold: one argument clearing every stated
member's radius, the claim's residues beyond it the symbolic
reads' own. -/
def clearsAll (Ps : List Poly) (an : Pos) : Prop :=
  (Ps.all (fun P => decide (radiusClears P an))) = true

instance instGenericlift13 (Ps : List Poly) (an : Pos) : Decidable (clearsAll Ps an) :=
  inferInstanceAs (Decidable (_ = _))

/-- A pair-entried matrix, clause (ii)'s stated carrier. -/
abbrev PPMat := List (List PPair)

/-- The first-row fold at pair entries, clause (ii)'s determinant at
its stated carrier, the representative map entrywise with the
collected sum untouched. -/
def ppminor (m : PPMat) : PPair :=
  elim.minorO poly.ppairOps poly.pnormPair id m

/-- The pair cofactor at a struck row and column, the side the key
sum's. -/
def ppcofac (m : PPMat) (i j : Nat) : PPair :=
  elim.cofO ppminor poly.pSwap m i j

/-- The adjugate at pair entries, the transposed cofactors. -/
def ppadj (m : PPMat) : PPMat :=
  elim.adjO ppminor poly.pSwap m

/-- The matrix's application at a pair vector, the rows' folds at
the certified reduction (`pAddR`, the representative moving to the
descent's own per term, `pReduce_read` the bridge). -/
def ppmatVec (m : PPMat) (v : List PPair) : List PPair :=
  m.map (fun r => (List.range r.length).foldl (fun acc k =>
    pAddR acc (pMul (ground.getAt pZero r k)
      (ground.getAt pZero v k))) pZero)

/-- The pair diagonal at stated entries, the off keys at the sum's
unit. -/
def ppdiag (ds : List PPair) : PPMat :=
  elim.diagO poly.ppairOps ds

/-- The pair-matrix product, the entries' folds. -/
def ppmatMul (a b : PPMat) : PPMat :=
  elim.matMulO poly.ppairOps a b

/-- Two pair rows read one value entrywise, the cross reads. -/
def pprowEq : List PPair → List PPair → Prop := ground.matchedOV crossRead

def decPprowEq : ∀ a b, Decidable (pprowEq a b) :=
  ground.decMatchedOV crossRead

instance instGenericlift14 (a b : List PPair) : Decidable (pprowEq a b) :=
  decPprowEq a b

/-- Two pair matrices read one value entrywise. -/
def ppmatEq : PPMat → PPMat → Prop :=
  ground.matchedOV (ground.matchedRead crossRead)

def decPpmatEq : ∀ a b, Decidable (ppmatEq a b) :=
  ground.decMatchedOV (ground.matchedRead crossRead)

instance instGenericlift15 (a b : PPMat) : Decidable (ppmatEq a b) :=
  decPpmatEq a b

/-- The matched read exchanges its matrices. -/
private theorem ppmatEq_symm {A B : PPMat} (h : ppmatEq A B) :
    ppmatEq B A :=
  ground.matched_symm
    (fun h' => ground.matched_symm
      (fun h'' => crossNull_symm h'') h') h

/-- The row read composes at an occupied middle row. -/
private theorem pprowEq_trans {a b c : List PPair}
    (hb : elim.rowOcc b = true) (h1 : pprowEq a b)
    (h2 : pprowEq b c) : pprowEq a c := by
  refine ground.matched_ofGetAt poly.pZero
    ((ground.matched_length h1).trans (ground.matched_length h2))
    (fun k hk => ?_)
  refine crossNull_trans (elim.rowOcc_read b hb k)
    (ground.matched_entry poly.pZero h1 k hk)
    (ground.matched_entry poly.pZero h2 k ?_)
  rw [← ground.matched_length h1]
  exact hk

/-- The matrix read composes at an occupied middle matrix. -/
private theorem ppmatEq_trans {A B C : PPMat}
    (hB : elim.matOcc B = true) (h1 : ppmatEq A B)
    (h2 : ppmatEq B C) : ppmatEq A C := by
  refine ground.matched_ofGetAt []
    ((ground.matched_length h1).trans (ground.matched_length h2))
    (fun i hi => ?_)
  have hi2 : i < B.length := by
    rw [← ground.matched_length h1]
    exact hi
  exact pprowEq_trans (elim.matOcc_read B hB i)
    (ground.matched_entry [] h1 i hi)
    (ground.matched_entry [] h2 i hi2)

/-- The adjugate at the descent, the transposed cofactors entry by
entry the erased frames' pair walks. -/
def ppadjD (m : PPMat) : PPMat :=
  elim.adjO elim.pairDetD poly.pSwap m

/-- The adjugate's occupancy at an occupied frame, at any
determinant read whose value's second member is occupied there. -/
private theorem matOcc_adjO (det : PPMat → PPair)
    (hden : ∀ E : PPMat, elim.matOcc E = true →
      ¬ poly.unitTail (det E).2)
    (m : PPMat) (hocc : elim.matOcc m = true) :
    elim.matOcc (elim.adjO det poly.pSwap m) = true := by
  refine elim.matOcc_intro _ (fun i hi => ?_)
  rw [show (elim.adjO det poly.pSwap m).length = m.length from
    ground.matOf_length m.length m.length _] at hi
  show elim.rowOcc (ground.getAt []
    (ground.matOf m.length m.length
      (fun i j => elim.cofO det poly.pSwap m j i)) i) = true
  rw [ground.matOf_row _ m.length m.length
    (fun i j => elim.cofO det poly.pSwap m j i) i hi]
  refine elim.rowOcc_intro _ (fun k hk => ?_)
  have hkr : k < (List.range m.length).length := by
    rw [ground.length_map] at hk
    exact hk
  rw [ground.getAt_map 0 poly.pZero _ (List.range m.length) k hkr]
  show ¬ poly.unitTail (elim.cofO det poly.pSwap m
    (ground.getAt 0 (List.range m.length) k) i).2
  unfold elim.cofO
  cases places.parityOf (ground.getAt 0 (List.range m.length) k + i) with
  | true => exact hden _ (elim.matOcc_erase m _ _ hocc)
  | false => exact hden _ (elim.matOcc_erase m _ _ hocc)

/-- The walk adjugate reads the fold adjugate at the square
frame, entry by entry at the cross reads. -/
theorem ppadjD_eq (m : PPMat) (hsq : elim.rowsLen m.length m) :
    ppmatEq (ppadjD m) (ppadj m) := by
  unfold ppadjD ppadj elim.adjO
  refine ground.matched_ofGetAt []
    (by rw [ground.matOf_length, ground.matOf_length]) (fun i hi => ?_)
  have him : i < m.length := by
    rw [ground.matOf_length] at hi
    exact hi
  rw [ground.matOf_row _ m.length m.length _ i him,
    ground.matOf_row _ m.length m.length _ i him]
  refine ground.matched_ofGetAt poly.pZero
    (by rw [ground.length_map, ground.length_map]) (fun j hj => ?_)
  have hjm : j < m.length := by
    rw [ground.length_mapRange] at hj
    exact hj
  have hjr : j < (List.range m.length).length := by
    rw [ground.length_range]
    exact hjm
  rw [ground.getAt_map 0 poly.pZero _ (List.range m.length) j hjr,
    ground.getAt_map 0 poly.pZero _ (List.range m.length) j hjr,
    ground.getAt_range m.length j hjm]
  have hje : (m.eraseIdx j).length + 1 = m.length :=
    ground.length_eraseIdx m j hjm
  have hr0 : elim.rowsLen m.length (m.eraseIdx j) :=
    elim.rowsLen_eraseIdx m.length m j hsq
  have hr1 : elim.rowsLen ((m.eraseIdx j).length + 1)
      (m.eraseIdx j) := by
    rw [hje]
    exact hr0
  have hicol : i < (m.eraseIdx j).length + 1 := by
    rw [hje]
    exact him
  have hE0 : elim.rowsLen (m.eraseIdx j).length
      ((m.eraseIdx j).map (fun r => r.eraseIdx i)) :=
    elim.rowsLen_eraseCol _ i hicol _ hr1
  have hE : elim.rowsLen
      (((m.eraseIdx j).map (fun r => r.eraseIdx i)).length)
      ((m.eraseIdx j).map (fun r => r.eraseIdx i)) := by
    rw [ground.length_map]
    exact hE0
  have hDV : crossNull
      (elim.pairDetD ((m.eraseIdx j).map (fun r => r.eraseIdx i)))
      (ppminor ((m.eraseIdx j).map (fun r => r.eraseIdx i))) :=
    (crossNull_ov _ _).mpr (elim.pairDetD_eq _ hE)
  show crossNull (elim.cofO elim.pairDetD poly.pSwap m j i)
    (elim.cofO ppminor poly.pSwap m j i)
  unfold elim.cofO
  cases places.parityOf (j + i) with
  | true =>
    exact (crossNull_ov _ _).mpr
      (poly.pSwap_cross ((crossNull_ov _ _).mp hDV))
  | false => exact hDV

/-- Clause (ii)'s solved witness at the pair carrier, whole:
`M adj(M) = det(M) 1`. -/
def ppadjRead (m : PPMat) : Prop :=
  ppmatEq (ppmatMul m (ppadj m))
    (ppdiag (List.replicate m.length (ppminor m)))

instance instGenericlift16 (m : PPMat) : Decidable (ppadjRead m) :=
  match elim.decRowsLen m.length m with
  | isTrue hsq =>
    match hocc : elim.matOcc m with
    | true =>
      have hMul : ppmatEq (ppmatMul m (ppadjD m))
          (ppmatMul m (ppadj m)) :=
        elim.matMulO_congr_right poly.ppairOps crossRead
          (crossNull_refl poly.pZero)
          (fun {_ _ _ _} h1 h2 => (crossNull_ov _ _).mpr
            (poly.pAdd_cross ((crossNull_ov _ _).mp h1)
              ((crossNull_ov _ _).mp h2)))
          (fun x {_ _} h => (crossNull_ov _ _).mpr
            (poly.pMul_cross
              ((crossNull_ov x x).mp (crossNull_refl x))
              ((crossNull_ov _ _).mp h)))
          (ppadjD_eq m hsq) m
      have hD : ppmatEq
          (ppdiag (List.replicate m.length (elim.pairDetD m)))
          (ppdiag (List.replicate m.length (ppminor m))) :=
        elim.diagO_repl_congr poly.ppairOps crossRead
          (crossNull_refl poly.pZero)
          ((crossNull_ov _ _).mpr (elim.pairDetD_eq m hsq))
          m.length
      have hoccW : elim.matOcc (ppmatMul m (ppadjD m)) = true :=
        elim.matOcc_matMulO m (ppadjD m) hocc
          (matOcc_adjO elim.pairDetD elim.pairDetD_den m hocc)
      have hoccF : elim.matOcc (ppmatMul m (ppadj m)) = true :=
        elim.matOcc_matMulO m (ppadj m) hocc
          (matOcc_adjO ppminor elim.pairMinor_den m hocc)
      have hoccDw : elim.matOcc
          (ppdiag (List.replicate m.length (elim.pairDetD m)))
          = true :=
        elim.matOcc_diagO _
          (elim.rowOcc_replicate _ (elim.pairDetD_den m hocc)
            m.length)
      have hoccDf : elim.matOcc
          (ppdiag (List.replicate m.length (ppminor m))) = true :=
        elim.matOcc_diagO _
          (elim.rowOcc_replicate _ (elim.pairMinor_den m hocc)
            m.length)
      decidable_of_iff
        (ppmatEq (ppmatMul m (ppadjD m))
          (ppdiag (List.replicate m.length (elim.pairDetD m))))
        ⟨fun x => ppmatEq_trans hoccDw
            (ppmatEq_trans hoccW (ppmatEq_symm hMul) x) hD,
         fun x => ppmatEq_trans hoccDf
            (ppmatEq_trans hoccF hMul x) (ppmatEq_symm hD)⟩
    | false => decPpmatEq _ _
  | isFalse _ => decPpmatEq _ _

/-- The pair's total cofactor, the components' cross products —
`def:ground`'s display at the polynomial carrier. -/
def pCofactor (x y : PPair) : PPair :=
  (poly.mul x.1 y.2, poly.mul x.2 y.1)

/-- The stated-order shape read: the matrix square at the order,
every row's length the row count's own. -/
def ppSquare (o : Nat) (m : PPMat) : Prop :=
  m.length = o ∧ (m.all (fun r => r.length == o)) = true

instance instGenericlift17 (o : Nat) (m : PPMat) : Decidable (ppSquare o m) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

/-! Clause (v): the rank read. -/

/-- An exponential-polynomial pair's member in a natural `ℓ`: the
finite fold `Σ_{k≤K} p_k(ℓ) 2^{kℓ}` at ground polynomials `p_k`,
the outer polynomial (`poly.PPoly`, the coefficients its members)
read at the coefficients' Horner reads at `ℓ` and at the outer
point `2^ℓ`; a pair of two such reads memberwise, as `PPair`'s
reads do, its side the members' sides. -/
def expoEval (E : poly.PPoly) (l : Nat) : BPair :=
  poly.eval (poly.pevalB E (BPair.ofNat l)) (ground.bpow (BPair.ofNat 2) l)

/-- The read is one value across the outer polynomial's
representatives. -/
theorem expoEval_congr {E F : poly.PPoly} (h : poly.ppOneValue E F) (l : Nat) :
    (expoEval E l).oneValue (expoEval F l) :=
  poly.eval_congr (poly.pevalB_congr (BPair.ofNat l) h) (ground.bpow (BPair.ofNat 2) l)

/-- Two folds' sum is a fold again, read as the sum at every
natural. -/
theorem expoEval_padd (E F : poly.PPoly) (l : Nat) :
    (expoEval (poly.padd E F) l).oneValue (expoEval E l + expoEval F l) :=
  BPair.oneValue_trans (poly.eval_congr (poly.pevalB_padd E F _) _)
    (poly.eval_add _ _ _)

/-- Two folds' product is a fold again at the keys' sums, read as
the product at every natural. -/
theorem expoEval_pmul (E F : poly.PPoly) (l : Nat) :
    (expoEval (poly.pmul E F) l).oneValue (expoEval E l * expoEval F l) :=
  BPair.oneValue_trans (poly.eval_congr (poly.pevalB_pmul E F _) _)
    (poly.eval_mul _ _ _)

/-- The top polynomial `p_K`: the outer top at the outer
representative, the largest key at a coefficient off the unit
tail. -/
def expoTop (E : poly.PPoly) : Poly := poly.ptop (poly.ptrim E)

/-- The tail: the coefficient polynomials at the keys below the
top key, the outer representative's leading segment. -/
def expoTail (E : poly.PPoly) : poly.PPoly :=
  (poly.ptrim E).take ((poly.ptrim E).length - 1)

/-- The tail's largest degree `m`, the inner top over the tail's
representatives. -/
def expoTailDeg (E : poly.PPoly) : Nat :=
  poly.innerTop ((expoTail E).map poly.vnorm)

/-- The tail coefficients' magnitudes' fold `F` over the keys below
the top, each coefficient polynomial's fold at the bound one. -/
def expoTailFold (E : poly.PPoly) : BPair :=
  ground.famFold BPair.add BPair.unit
    (fun p => windowsep.magFold p (BPair.ofPos .one) (BPair.ofPos .one))
    (expoTail E)

/-! The halving's power clears every power of the natural from
`4m²` on: the seed `2^{4m²} ≥ (4m²)^m` at `m ≤ 2^m`, and the step
`(ℓ+1)^m ≤ 2 ℓ^m` at `ℓ ≥ 2m`, the binomial identity per key
collecting to `(ℓ+1)^m ≤ ℓ^m + m (ℓ+1)^{m-1}`. -/

private theorem succPow_le (l : Nat) : ∀ n : Nat,
    (l + 1) ^ (n + 1) ≤ l ^ (n + 1) + (n + 1) * (l + 1) ^ n
  | 0 => by
    show (l + 1) ^ 1 ≤ l ^ 1 + 1 * (l + 1) ^ 0
    rw [ground.powOne, ground.powOne, Nat.pow_zero, Nat.mul_one]
    exact Nat.le_refl _
  | n + 1 => by
    have h1 : (l + 1) ^ (n + 1 + 1)
        ≤ (l ^ (n + 1) + (n + 1) * (l + 1) ^ n) * (l + 1) := by
      rw [Nat.pow_succ (l + 1) (n + 1)]
      exact Nat.mul_le_mul_right (l + 1) (succPow_le l n)
    have h2 : l ^ (n + 1) ≤ (l + 1) ^ (n + 1) :=
      Nat.pow_le_pow_left (Nat.le_succ l) (n + 1)
    refine Nat.le_trans h1 ?_
    rw [ground.mulAddR, Nat.mul_succ (l ^ (n + 1)) l, ← Nat.pow_succ l (n + 1),
      ground.mulAssoc (n + 1) ((l + 1) ^ n) (l + 1), ← Nat.pow_succ (l + 1) n,
      Nat.succ_mul (n + 1) ((l + 1) ^ (n + 1)), Nat.add_assoc]
    refine Nat.add_le_add_left ?_ _
    rw [Nat.add_comm (l ^ (n + 1))]
    exact Nat.add_le_add_left h2 _

private theorem pow_step (l : Nat) : ∀ m : Nat, 2 * m ≤ l → (l + 1) ^ m ≤ 2 * l ^ m
  | 0, _ => by
    rw [Nat.pow_zero, Nat.pow_zero]
    exact Nat.le_of_lt (by decide)
  | n + 1, h => by
    have h2 : 2 * (n + 1) ≤ l + 1 := Nat.le_succ_of_le h
    have h3 : 2 * ((n + 1) * (l + 1) ^ n) ≤ (l + 1) ^ (n + 1) := by
      rw [← ground.mulAssoc 2 (n + 1) ((l + 1) ^ n), Nat.pow_succ (l + 1) n,
        Nat.mul_comm ((l + 1) ^ n) (l + 1)]
      exact Nat.mul_le_mul_right ((l + 1) ^ n) h2
    have h4 : 2 * (l + 1) ^ (n + 1) ≤ 2 * l ^ (n + 1) + (l + 1) ^ (n + 1) := by
      refine Nat.le_trans (Nat.mul_le_mul_left 2 (succPow_le l n)) ?_
      rw [Nat.mul_add]
      exact Nat.add_le_add_left h3 _
    rw [Nat.two_mul] at h4
    exact ground.leCancelR _ h4

private theorem seed_split (k : Nat) :
    4 * (k + 1) * (k + 1) = (2 + (k + 1 + (k + 1))) * (k + 1) + (k + k) * (k + 1) :=
  polEq [k]
    (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))
      (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))
    (Pol.add
      (Pol.mul (Pol.add (Pol.mon (Mon.cst 2))
          (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))
            (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))))
        (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))
      (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))
        (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))))
    (by decide +kernel)

private theorem four_sq (k : Nat) : 2 * (k + 1) * (2 * (k + 1)) = 4 * (k + 1) * (k + 1) :=
  polEq [k]
    (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))
      (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))))
    (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))
      (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))
    (by decide +kernel)

private theorem twoMul_le_seed : ∀ m : Nat, 2 * m ≤ 4 * m * m
  | 0 => Nat.le_refl _
  | k + 1 => by
    rw [← four_sq k]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by decide) (Nat.succ_pos k))

private theorem pow_seed (m : Nat) : (4 * m * m) ^ m ≤ 2 ^ (4 * m * m) := by
  have hm : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
  have h4 : 4 * m * m ≤ 2 ^ (2 + (m + m)) := by
    rw [ground.powAdd 2 2 (m + m), ground.powAdd 2 m m]
    show 4 * m * m ≤ 4 * (2 ^ m * 2 ^ m)
    rw [← ground.mulAssoc 4 (2 ^ m) (2 ^ m)]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hm) hm
  have hexp : (2 + (m + m)) * m ≤ 4 * m * m := by
    match m with
    | 0 => exact Nat.le_refl _
    | k + 1 =>
      rw [seed_split k]
      exact Nat.le_add_right _ _
  refine Nat.le_trans (Nat.pow_le_pow_left h4 m) ?_
  rw [ground.powPow]
  exact Nat.pow_le_pow_right (by decide) hexp

private theorem twoPow_step (m : Nat) : ∀ t : Nat,
    (4 * m * m + t) ^ m ≤ 2 ^ (4 * m * m + t)
  | 0 => by
    rw [Nat.add_zero]
    exact pow_seed m
  | t + 1 => by
    have hl : 2 * m ≤ 4 * m * m + t :=
      Nat.le_trans (twoMul_le_seed m) (Nat.le_add_right _ _)
    rw [← Nat.add_assoc]
    refine Nat.le_trans (pow_step (4 * m * m + t) m hl) ?_
    rw [Nat.pow_succ 2 (4 * m * m + t), Nat.mul_comm (2 ^ _) 2]
    exact Nat.mul_le_mul_left 2 (twoPow_step m t)

/-- The halving's power clears the natural's power at every natural
from `4m²` on. -/
private theorem twoPow_clears (m l : Nat) (h : 4 * m * m ≤ l) : l ^ m ≤ 2 ^ l := by
  obtain ⟨t, ht⟩ := Nat.le.dest h
  rw [← ht]
  exact twoPow_step m t

/-- The side of a sum whose first summand dominates the second's
magnitude. -/
private theorem side_of_dominant {a b : BPair} (hb : windowsep.mag b < a) :
    BPair.unit < a + b := by
  have h1 : (windowsep.mag b).swap ≤ b := by
    have h := ground.leB_swap (windowsep.swap_le_mag b)
    rw [BPair.swap_swap] at h
    exact h
  have h2 : BPair.unit < a + (windowsep.mag b).swap := by
    refine ground.unitLt_of_swap_lt ?_
    rw [BPair.swap_swap]
    exact hb
  exact ground.ltB_trans_le h2 (ground.leB_add (ground.leB_refl a) h1)

/-- The tail's count at the outer representative's top key. -/
private theorem expoTail_length (E : poly.PPoly) :
    (expoTail E).length = (poly.ptrim E).length - 1 :=
  ground.length_take _ _ (Nat.sub_le _ _)

/-- The tail's keys read within the tail degree. -/
private theorem tailDeg_read (E : poly.PPoly) : ∀ k, k < (poly.ptrim E).length - 1 →
    (poly.vnorm (ground.getAt [] (poly.ptrim E) k)).length ≤ expoTailDeg E + 1 := by
  intro k hk
  have h := poly.innerLe_getAt (poly.innerLe_innerTop ((expoTail E).map poly.vnorm)) k
  rw [ground.getAt_map [] [] poly.vnorm (expoTail E) k (by rw [expoTail_length]; exact hk)] at h
  unfold expoTail at h
  rw [ground.getAt_take [] _ _ k hk] at h
  exact h

/-- The tail's magnitude against the outer point at abstract data:
at or below the tail fold against the natural's power at a degree
every tail key sits within and the outer point's power at the top
key. -/
private theorem tail_core (G : poly.PPoly) (l : Nat) (hl : 1 ≤ l) (x : BPair)
    (hx1 : BPair.ofPos .one ≤ x) (K m : Nat)
    (hdeg : ∀ k, k < K → (poly.vnorm (ground.getAt [] G k)).length ≤ m + 1) :
    windowsep.mag (ground.famFold BPair.add BPair.unit
        (fun k => poly.eval (ground.getAt [] G k) (BPair.ofNat l) * bpow x k)
        (List.range K)) * x
    ≤ ground.famFold BPair.add BPair.unit
        (fun k => windowsep.magFold (ground.getAt [] G k) (BPair.ofPos .one) (BPair.ofPos .one))
        (List.range K)
      * bpow (BPair.ofNat l) m * bpow x K := by
  have hxu : BPair.unit ≤ x := leB_trans (leB_of_lt (unitLtOfPos .one)) hx1
  have hmagx : windowsep.mag x = x := windowsep.mag_unitLe hxu
  have hl1 : BPair.ofPos .one ≤ windowsep.mag (BPair.ofNat l) := by
    rw [windowsep.mag_unitLe (unitLeOfNat l)]
    exact leB_ofNat hl
  have hlu : BPair.unit ≤ BPair.ofNat l := unitLeOfNat l
  refine leB_trans (leB_mulL hxu (windowsep.mag_famFold_le _ (List.range K))) ?_
  refine leB_congr_left (BPair.oneValue_symm (ground.foldB_mul_right x
    (fun k => windowsep.mag (poly.eval (ground.getAt [] G k) (BPair.ofNat l) * bpow x k))
    (List.range K))) ?_
  refine leB_congr_right (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (ground.foldB_mul_right (bpow (BPair.ofNat l) m)
      (fun k => windowsep.magFold (ground.getAt [] G k) (BPair.ofPos .one) (BPair.ofPos .one))
      (List.range K)))
    (ground.foldB_mul_right (bpow x K)
      (fun k => windowsep.magFold (ground.getAt [] G k) (BPair.ofPos .one) (BPair.ofPos .one)
        * bpow (BPair.ofNat l) m)
      (List.range K)))) ?_
  refine windowsep.leB_famFold_range (List.range K) (fun k hk => ?_)
  have hkK : k < K := ground.ltOfCountRange hk
  have hcap := windowsep.magEval_le (ground.getAt [] G k) (BPair.ofNat l) m (hdeg k hkK) hl1
  rw [windowsep.mag_unitLe hlu] at hcap
  have hxk : bpow x k * x ≤ bpow x K := by
    refine leB_congr_left (BPair.oneValue_trans (bpow_succ_read x k)
      (BPair.oneValue_of_eq (BPair.mul_comm x (bpow x k)))) ?_
    exact bpow_le_exp hx1 hkK
  refine leB_congr_left (BPair.oneValue_symm (BPair.mul_congr_left (BPair.oneValue_trans
    (windowsep.mag_mul _ _)
    (BPair.mul_congr (BPair.oneValue_refl _) (windowsep.mag_bpow x k))))) ?_
  rw [hmagx]
  have hFk : BPair.unit ≤ windowsep.magFold (ground.getAt [] G k) (BPair.ofPos .one) (BPair.ofPos .one) :=
    windowsep.unitLe_magFold _ (leB_of_lt (unitLtOfPos .one)) (leB_of_lt (unitLtOfPos .one))
  have hLm : BPair.unit ≤ bpow (BPair.ofNat l) m := unitLeBpow hlu m
  have hXk : BPair.unit ≤ bpow x k := unitLeBpow hxu k
  generalize windowsep.mag (poly.eval (ground.getAt [] G k) (BPair.ofNat l)) = M at hcap ⊢
  generalize windowsep.magFold (ground.getAt [] G k) (BPair.ofPos .one) (BPair.ofPos .one) = Fk
    at hcap hFk ⊢
  generalize bpow (BPair.ofNat l) m = Lm at hcap hLm ⊢
  generalize bpow x k = Xk at hxk hXk ⊢
  generalize bpow x K = XK at hxk ⊢
  refine leB_congr_left (BPair.oneValue_of_eq (BPair.mul_assoc M Xk x).symm) ?_
  exact leB_mul_mono (unitLeMul hXk hxu) (unitLeMul hFk hLm) hcap hxk

/-- The tail's magnitude against the outer point, cleared: at or
below the tail fold against the natural's power at the tail degree
and the outer point's power at the top key. -/
private theorem tail_le (E : poly.PPoly) (l : Nat) (hl : 1 ≤ l) :
    windowsep.mag (ground.famFold BPair.add BPair.unit
        (fun k => poly.eval (ground.getAt [] (poly.ptrim E) k) (BPair.ofNat l)
          * bpow (bpow (BPair.ofNat 2) l) k) (List.range ((poly.ptrim E).length - 1)))
      * bpow (BPair.ofNat 2) l
    ≤ expoTailFold E * bpow (BPair.ofNat l) (expoTailDeg E)
      * bpow (bpow (BPair.ofNat 2) l) ((poly.ptrim E).length - 1) := by
  have hF : (ground.famFold BPair.add BPair.unit
      (fun k => windowsep.magFold (ground.getAt [] (poly.ptrim E) k)
        (BPair.ofPos .one) (BPair.ofPos .one))
      (List.range ((poly.ptrim E).length - 1))).oneValue (expoTailFold E) := by
    unfold expoTailFold
    refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq
      (ground.famFold_getAt BPair.add BPair.unit _ [] (expoTail E) _ (expoTail_length E)))
    refine ground.bsum_congr_range_ov _ _ _ (fun j hj => ?_)
    unfold expoTail
    rw [ground.getAt_take [] _ _ j hj]
    exact BPair.oneValue_refl _
  refine leB_congr_right (BPair.mul_congr (BPair.mul_congr_left hF) (BPair.oneValue_refl _)) ?_
  exact tail_core (poly.ptrim E) l hl (bpow (BPair.ofNat 2) l)
    (oneLeBpow (leB_ofNat (by decide : 1 ≤ 2)) l)
    ((poly.ptrim E).length - 1) (expoTailDeg E) (tailDeg_read E)

/-- The comparison `c 2^ℓ > F ℓ^m` at the top's data, cleared at the
radius' second member's power. -/
def expoCompare (E : poly.PPoly) (l : Nat) : Prop :=
  expoTailFold E
    * ground.bpow (windowsep.radiusD (expoTop E)) ((poly.vnorm (expoTop E)).length - 1)
    * ground.bpow (BPair.ofNat l) (expoTailDeg E)
  < windowsep.leadMargin (expoTop E) * ground.bpow (BPair.ofNat 2) l

instance instGenericlift20 (E : poly.PPoly) (l : Nat) :
    Decidable (expoCompare E l) :=
  inferInstanceAs (Decidable (_ < _))

/-- The least natural at or beyond the radius, the clearing
quotient of the radius' two members (`ground.ceilAt`). -/
def radiusCeil (P : Poly) : Nat :=
  ground.ceilAt (windowsep.radiusN P).marginN (windowsep.radiusD P).marginN

/-- The stepping's start: the natural at or beyond the radius and
`4m²`. -/
def expoStart (E : poly.PPoly) : Nat :=
  Nat.max (4 * expoTailDeg E * expoTailDeg E) (radiusCeil (expoTop E))

/-- The comparison's witness: the larger of `4(m+1)²`, the natural
at or beyond the radius, and the natural at or beyond `[F : c]`,
the division's quotient at its successor. -/
def expoWit (E : poly.PPoly) : Nat :=
  Nat.max
    (Nat.max (4 * (expoTailDeg E + 1) * (expoTailDeg E + 1))
      (radiusCeil (expoTop E)))
    ((expoTailFold E).marginN
        * (windowsep.radiusD (expoTop E)).marginN
            ^ ((poly.vnorm (expoTop E)).length - 1)
      / (windowsep.leadMargin (expoTop E)).marginN + 1)

/-- The stepping's read: at or beyond the start and holding the
comparison. -/
def expoPred (E : poly.PPoly) (l : Nat) : Prop :=
  expoStart E ≤ l ∧ expoCompare E l

instance instGenericlift21 (E : poly.PPoly) : DecidablePred (expoPred E) :=
  inferInstanceAs (DecidablePred (fun l => expoStart E ≤ l ∧ expoCompare E l))

/-- The witness sits at or beyond the start. -/
private theorem expoStart_le_wit (E : poly.PPoly) : expoStart E ≤ expoWit E := by
  refine Nat.le_trans ?_ (ground.le_max_left _ _)
  refine ground.max_le ?_ (ground.le_max_right _ _)
  refine Nat.le_trans ?_ (ground.le_max_left _ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.le_succ _)) (Nat.le_succ _)

/-- The computed natural: the least natural at or beyond the start
holding the comparison, the stepping read by halving on the segment
from the start to the witness (`def:ground`). -/
def expoKey (E : poly.PPoly) : Nat :=
  ground.bisectFrom (expoPred E) (expoStart E) (expoWit E - expoStart E)

/-- The evaluation split at the top key of the outer
representative. -/
private theorem expoEval_split (E : poly.PPoly) (K : Nat) (hE : (poly.ptrim E).length = K + 1)
    (l : Nat) :
    (expoEval E l).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => poly.eval (ground.getAt [] (poly.ptrim E) k) (BPair.ofNat l)
          * bpow (bpow (BPair.ofNat 2) l) k) (List.range K)
      + poly.eval (expoTop E) (BPair.ofNat l) * bpow (bpow (BPair.ofNat 2) l) K) := by
  refine BPair.oneValue_trans (BPair.oneValue_symm (expoEval_congr (poly.ptrim_ov E) l)) ?_
  unfold expoEval expoTop
  generalize poly.ptrim E = G at hE ⊢
  have hf := poly.eval_famFold (poly.pevalB G (BPair.ofNat l)) (bpow (BPair.ofNat 2) l)
  have hlen : (poly.pevalB G (BPair.ofNat l)).length = K + 1 := by
    show (G.map _).length = K + 1
    rw [ground.length_map, hE]
  rw [hlen] at hf
  refine BPair.oneValue_trans hf ?_
  refine BPair.oneValue_trans (ground.foldB_range_snoc _ K) ?_
  refine BPair.add_congr ?_ ?_
  · refine ground.foldB_congr_members _ _ _ (fun k hk => ?_)
    have hkE : k < G.length := by
      rw [hE]
      exact Nat.lt_succ_of_lt (ground.ltOfCountRange hk)
    show (ground.getAt BPair.unit (G.map (fun c => poly.eval c (BPair.ofNat l))) k
      * _).oneValue _
    rw [ground.getAt_map [] BPair.unit _ G k hkE]
    exact BPair.oneValue_refl _
  · show (ground.getAt BPair.unit (G.map (fun c => poly.eval c (BPair.ofNat l))) K
      * _).oneValue _
    rw [ground.getAt_map [] BPair.unit _ G K (by rw [hE]; exact Nat.lt_succ_self K),
      poly.ptop_getAt G K hE]
    exact BPair.oneValue_refl _

/-- The least natural at or beyond the radius clears it. -/
private theorem radiusCeil_clears (P : Poly) (h : ¬ poly.unitTail P) :
    windowsep.radiusN P ≤ BPair.ofNat (radiusCeil P) * windowsep.radiusD P := by
  have hyn : 0 < (windowsep.radiusD P).marginN :=
    BPair.marginN_pos (windowsep.unitLt_radiusD P h)
  refine leB_congr_left (BPair.oneValue_symm
    (BPair.ofNat_marginN (windowsep.unitLe_radiusN P))) ?_
  refine leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (BPair.ofNat_marginN (windowsep.unitLe_radiusD P)))) ?_
  refine leB_congr_right (BPair.oneValue_trans (BPair.ofNat_mul _ _)
    (BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
  exact leB_ofNat (ground.ceilAt_ge _ _ hyn)

/-- The least natural at or beyond the radius is occupied. -/
private theorem radiusCeil_pos (P : Poly) (h : ¬ poly.unitTail P) : 1 ≤ radiusCeil P := by
  have hyn : 0 < (windowsep.radiusD P).marginN :=
    BPair.marginN_pos (windowsep.unitLt_radiusD P h)
  have hxn : 0 < (windowsep.radiusN P).marginN :=
    BPair.marginN_pos (BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (unitLtAdd (windowsep.unitLt_radiusD P h) (windowsep.unitLe_height P)))
  have hge := ground.ceilAt_ge (windowsep.radiusN P).marginN (windowsep.radiusD P).marginN hyn
  match hc : radiusCeil P with
  | 0 =>
    unfold radiusCeil at hc
    rw [hc, Nat.mul_zero] at hge
    exact absurd hxn (Nat.not_lt_of_ge hge)
  | k + 1 => exact Nat.succ_pos k

/-- The tail fold sits at or beyond the sum's unit. -/
private theorem unitLe_expoTailFold (E : poly.PPoly) : BPair.unit ≤ expoTailFold E :=
  ground.foldB_nonneg_mem _ _ (fun p _ =>
    windowsep.unitLe_magFold p (leB_of_lt (unitLtOfPos .one)) (leB_of_lt (unitLtOfPos .one)))

/-- The comparison steps: holding at a natural at or beyond the
start it holds at the successor, `2 ℓ^m ≥ (ℓ+1)^m` at `ℓ ≥ 2m`. -/
private theorem pred_step (E : poly.PPoly) : ∀ k, expoPred E k → expoPred E (k + 1) := by
  intro k hk
  refine ⟨Nat.le_succ_of_le hk.1, ?_⟩
  have h2m : 2 * expoTailDeg E ≤ k :=
    Nat.le_trans (twoMul_le_seed _) (Nat.le_trans (ground.le_max_left _ _) hk.1)
  have hstep : bpow (BPair.ofNat (k + 1)) (expoTailDeg E)
      ≤ BPair.ofNat 2 * bpow (BPair.ofNat k) (expoTailDeg E) := by
    refine leB_congr (bpow_ofNat (k + 1) _)
      (BPair.oneValue_trans (BPair.ofNat_mul 2 _)
        (BPair.mul_congr (BPair.oneValue_refl _) (bpow_ofNat k _))) ?_
    exact leB_ofNat (pow_step k _ h2m)
  have hFD : BPair.unit ≤ expoTailFold E
      * bpow (windowsep.radiusD (expoTop E)) ((poly.vnorm (expoTop E)).length - 1) :=
    unitLeMul (unitLe_expoTailFold E) (unitLeBpow (windowsep.unitLe_radiusD _) _)
  have hc := hk.2
  unfold expoCompare at hc ⊢
  generalize expoTailFold E
    * bpow (windowsep.radiusD (expoTop E)) ((poly.vnorm (expoTop E)).length - 1) = FD
    at hc hFD ⊢
  generalize windowsep.leadMargin (expoTop E) = c at hc ⊢
  generalize hm : expoTailDeg E = m at hc hstep ⊢
  have h3 : FD * bpow (BPair.ofNat k) m * BPair.ofNat 2
      < c * bpow (BPair.ofNat 2) k * BPair.ofNat 2 :=
    ltB_mulPos hc (unitLtNat (by decide : 0 < 2))
  refine ground.leB_ltB_trans (leB_mulR hFD hstep) ?_
  refine BPair.lt_congr (BPair.oneValue_of_eq ?_) ?_ h3
  · rw [← BPair.mul_assoc, BPair.mul_right_comm]
  · refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl c) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    exact BPair.oneValue_symm (bpow_succ_read _ k)

/-- The comparison holds at the witness: the halving's power clears
the power one degree up from `4(m+1)²` on, and the natural at or
beyond `[F : c]` clears `F` against `c`. -/
private theorem pred_wit (E : poly.PPoly) (h : ¬ poly.unitTail (expoTop E)) :
    expoPred E (expoWit E) := by
  refine ⟨expoStart_le_wit E, ?_⟩
  have hc := windowsep.unitLt_leadMargin (expoTop E) h
  have hcn : 0 < (windowsep.leadMargin (expoTop E)).marginN := BPair.marginN_pos hc
  have hcu : BPair.unit ≤ windowsep.leadMargin (expoTop E) := leB_of_lt hc
  have hF := unitLe_expoTailFold E
  have hrD := windowsep.unitLe_radiusD (expoTop E)
  unfold expoCompare
  generalize hw : expoWit E = w
  have hw4 : 4 * (expoTailDeg E + 1) * (expoTailDeg E + 1) ≤ w := by
    rw [← hw]
    exact Nat.le_trans (ground.le_max_left _ _) (ground.le_max_left _ _)
  have hwc : (expoTailFold E).marginN
      * (windowsep.radiusD (expoTop E)).marginN ^ ((poly.vnorm (expoTop E)).length - 1)
      / (windowsep.leadMargin (expoTop E)).marginN + 1 ≤ w := by
    rw [← hw]
    exact ground.le_max_right _ _
  have hw1 : 0 < w := Nat.lt_of_lt_of_le (Nat.succ_pos _) hwc
  generalize hm : expoTailDeg E = m at hw4 ⊢
  generalize hd : (poly.vnorm (expoTop E)).length - 1 = d at hwc ⊢
  have hA : (expoTailFold E).marginN * (windowsep.radiusD (expoTop E)).marginN ^ d
      < (windowsep.leadMargin (expoTop E)).marginN * w := by
    have hread := ground.natDivRead
      ((expoTailFold E).marginN * (windowsep.radiusD (expoTop E)).marginN ^ d)
      (windowsep.leadMargin (expoTop E)).marginN hcn
    refine Nat.lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ hwc)
    have h1 := Nat.add_lt_add_left hread.2 ((windowsep.leadMargin (expoTop E)).marginN
      * ((expoTailFold E).marginN * (windowsep.radiusD (expoTop E)).marginN ^ d
          / (windowsep.leadMargin (expoTop E)).marginN))
    rw [hread.1] at h1
    rw [Nat.mul_succ]
    exact h1
  have hpow : bpow (BPair.ofNat w) (m + 1) ≤ bpow (BPair.ofNat 2) w :=
    leB_congr (bpow_ofNat w (m + 1)) (bpow_ofNat 2 w)
      (leB_ofNat (twoPow_clears (m + 1) w hw4))
  have hFD : (expoTailFold E * bpow (windowsep.radiusD (expoTop E)) d).oneValue
      (BPair.ofNat ((expoTailFold E).marginN * (windowsep.radiusD (expoTop E)).marginN ^ d)) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.ofNat_marginN hF)
      (BPair.oneValue_trans (bpow_congr (BPair.ofNat_marginN hrD) d)
        (BPair.oneValue_symm (bpow_ofNat _ d)))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_mul _ _)
  have hcw : (BPair.ofNat ((windowsep.leadMargin (expoTop E)).marginN * w)).oneValue
      (windowsep.leadMargin (expoTop E) * BPair.ofNat w) :=
    BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_marginN hcu)))
  have hlt : expoTailFold E * bpow (windowsep.radiusD (expoTop E)) d
      < windowsep.leadMargin (expoTop E) * BPair.ofNat w :=
    BPair.lt_congr (BPair.oneValue_symm hFD) hcw (ltB_ofNat hA)
  refine ground.ltB_trans_le (ltB_mulPos hlt (unitLtBpow (unitLtNat hw1) m)) ?_
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (bpow_succ_read (BPair.ofNat w) m))))) ?_
  exact leB_mulR hcu hpow

/-- The core read at every natural at or beyond the computed one:
the natural is occupied and clears the radius, and the tail's
magnitude sits below the top term's. -/
private theorem expoCore (E : poly.PPoly) (K : Nat) (hE : (poly.ptrim E).length = K + 1)
    (h : ¬ poly.unitTail (expoTop E)) (l : Nat) (hl : expoKey E ≤ l) :
    1 ≤ l
    ∧ windowsep.radiusN (expoTop E) ≤ BPair.ofNat l * windowsep.radiusD (expoTop E)
    ∧ windowsep.mag (ground.famFold BPair.add BPair.unit
        (fun k => poly.eval (ground.getAt [] (poly.ptrim E) k) (BPair.ofNat l)
          * bpow (bpow (BPair.ofNat 2) l) k) (List.range K))
      < windowsep.mag (poly.eval (expoTop E) (BPair.ofNat l))
        * bpow (bpow (BPair.ofNat 2) l) K := by
  have hpred : expoPred E l := by
    refine ground.stepMono_of_le (expoPred E) (pred_step E) hl ?_
    refine ground.bisectFrom_hit (expoPred E) (expoStart E) (expoWit E - expoStart E) ?_
    rw [Nat.add_comm, ground.subAdd (expoStart_le_wit E)]
    exact pred_wit E h
  have hceil : radiusCeil (expoTop E) ≤ l :=
    Nat.le_trans (ground.le_max_right _ _) hpred.1
  have hl1 : 1 ≤ l := Nat.le_trans (radiusCeil_pos _ h) hceil
  have hcl : windowsep.radiusN (expoTop E)
      ≤ BPair.ofNat l * windowsep.radiusD (expoTop E) :=
    leB_trans (radiusCeil_clears _ h)
      (leB_mulL (windowsep.unitLe_radiusD _) (leB_ofNat hceil))
  refine ⟨hl1, hcl, ?_⟩
  have hA := windowsep.leadTerm_ge (expoTop E) h l hcl
  have hP := hpred.2
  unfold expoCompare at hP
  have hD : windowsep.mag (ground.famFold BPair.add BPair.unit
        (fun k => poly.eval (ground.getAt [] (poly.ptrim E) k) (BPair.ofNat l)
          * bpow (bpow (BPair.ofNat 2) l) k) (List.range K))
      * bpow (BPair.ofNat 2) l
    ≤ expoTailFold E * bpow (BPair.ofNat l) (expoTailDeg E)
      * bpow (bpow (BPair.ofNat 2) l) K := by
    have hD0 := tail_le E l hl1
    rw [hE] at hD0
    exact hD0
  have hlpos : BPair.unit < BPair.ofNat l := unitLtNat hl1
  have hxpos : BPair.unit < bpow (BPair.ofNat 2) l :=
    unitLtBpow (unitLtNat (by decide : 0 < 2)) l
  have hrN : bpow (windowsep.radiusN (expoTop E)) ((poly.vnorm (expoTop E)).length - 1)
      ≤ bpow (BPair.ofNat l) ((poly.vnorm (expoTop E)).length - 1)
        * bpow (windowsep.radiusD (expoTop E)) ((poly.vnorm (expoTop E)).length - 1) :=
    leB_congr_right (bpow_mul _ _ _) (bpow_mono (windowsep.unitLe_radiusN _) hcl _)
  have hrDu : BPair.unit ≤ bpow (windowsep.radiusD (expoTop E))
      ((poly.vnorm (expoTop E)).length - 1) := unitLeBpow (windowsep.unitLe_radiusD _) _
  have hLdu : BPair.unit < bpow (BPair.ofNat l) ((poly.vnorm (expoTop E)).length - 1) :=
    unitLtBpow hlpos _
  have hMu : BPair.unit ≤ windowsep.mag (poly.eval (expoTop E) (BPair.ofNat l)) :=
    windowsep.unitLe_mag _
  generalize windowsep.mag (ground.famFold BPair.add BPair.unit
      (fun k => poly.eval (ground.getAt [] (poly.ptrim E) k) (BPair.ofNat l)
        * bpow (bpow (BPair.ofNat 2) l) k) (List.range K)) = T at hD ⊢
  generalize windowsep.mag (poly.eval (expoTop E) (BPair.ofNat l)) = M at hA hMu ⊢
  generalize bpow (windowsep.radiusN (expoTop E)) ((poly.vnorm (expoTop E)).length - 1) = RN
    at hA hrN
  generalize bpow (windowsep.radiusD (expoTop E)) ((poly.vnorm (expoTop E)).length - 1) = RD
    at hP hrN hrDu
  generalize bpow (BPair.ofNat l) ((poly.vnorm (expoTop E)).length - 1) = Ld at hA hrN hLdu
  generalize bpow (BPair.ofNat l) (expoTailDeg E) = Lm at hP hD
  generalize windowsep.leadMargin (expoTop E) = c at hA hP
  generalize expoTailFold E = F at hP hD
  generalize bpow (BPair.ofNat 2) l = x at hP hD hxpos ⊢
  generalize hXK : bpow x K = XK at hD ⊢
  have hMx : F * Lm < M * x := by
    have h1 : F * RD * Lm * Ld < c * x * Ld := ltB_mulPos hP hLdu
    have h2 : c * x * Ld ≤ M * RN * x :=
      leB_congr_left (BPair.oneValue_of_eq (BPair.mul_right_comm c Ld x))
        (leB_mulL (leB_of_lt hxpos) hA)
    have h3 : M * RN * x ≤ M * (Ld * RD) * x :=
      leB_mulL (leB_of_lt hxpos) (leB_mulR hMu hrN)
    have h4 : F * Lm * (RD * Ld) < M * x * (RD * Ld) := by
      refine BPair.lt_congr (polEqB [F, RD, Lm, Ld]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2)))
          (Pol.mon (Mon.var 3)))
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 2)))
          (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 3))))
        (by decide +kernel))
        (polEqB [M, Ld, RD, x]
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))))
          (Pol.mon (Mon.var 3)))
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3)))
          (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 1))))
        (by decide +kernel)) ?_
      exact ground.ltB_trans_le h1 (leB_trans h2 h3)
    exact ground.ltB_unscale (unitLeMul hrDu (leB_of_lt hLdu)) h4
  have hXKpos : BPair.unit < XK := by
    rw [← hXK]
    exact unitLtBpow hxpos K
  have h5 : T * x < M * XK * x := by
    refine ground.ltB_trans_le ?_ (leB_congr_left
      (BPair.oneValue_of_eq (BPair.mul_right_comm M XK x)) (leB_refl (M * XK * x)))
    exact ground.leB_ltB_trans hD (ltB_mulPos hMx hXKpos)
  exact ground.ltB_unscale (leB_of_lt hxpos) h5

/-- An occupied top's representative refuses the unit tail. -/
private theorem topOcc_of_upper {P : Poly} (h : topUpper P) : ¬ poly.unitTail P := fun hu =>
  ground.leB_not_lt (leB_refl BPair.unit) (BPair.lt_congr (BPair.oneValue_refl _)
    (poly.top_unitTail (poly.oneValue_unitTail (poly.vnorm_ov P) hu)) h)

private theorem topOcc_of_lower {P : Poly} (h : topLower P) : ¬ poly.unitTail P := fun hu =>
  ground.leB_not_lt (leB_refl BPair.unit) (BPair.lt_congr
    (poly.top_unitTail (poly.oneValue_unitTail (poly.vnorm_ov P) hu)) (BPair.oneValue_refl _) h)

/-- The outer representative's count at an occupied top is its top
key's successor. -/
private theorem ptrim_len_succ (E : poly.PPoly) (h : ¬ poly.unitTail (expoTop E)) :
    (poly.ptrim E).length = (poly.ptrim E).length - 1 + 1 := by
  match hG : poly.ptrim E with
  | [] =>
    unfold expoTop at h
    rw [hG] at h
    exact absurd trivial h
  | _ :: _ => rfl

/-- The settled side, the upper: at or beyond the computed natural
the fold sits strictly above the sum's unit where the top
polynomial's leading coefficient does, the tail's magnitude below
the top's. -/
theorem expoUpper (E : poly.PPoly) (h : topUpper (expoTop E)) :
    ∀ l : Nat, expoKey E ≤ l → BPair.unit < expoEval E l := by
  intro l hl
  have hocc := topOcc_of_upper h
  obtain ⟨hl1, hcl, hT⟩ := expoCore E ((poly.ptrim E).length - 1) (ptrim_len_succ E hocc) hocc l hl
  have htop : BPair.unit < poly.eval (expoTop E) (BPair.ofNat l) := by
    refine windowsep.lead_upper _ _ ?_ (unitLtMul h (unitLtBpow (unitLtNat hl1) _))
    rw [windowsep.mag_unitLe (unitLeOfNat l)]
    exact hcl
  rw [windowsep.mag_unitLe (leB_of_lt htop)] at hT
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_symm (expoEval_split E _ (ptrim_len_succ E hocc) l))) ?_
  exact side_of_dominant hT

/-- The settled side, the lower: the upper read at the memberwise
swap. -/
theorem expoLower (E : poly.PPoly) (h : topLower (expoTop E)) :
    ∀ l : Nat, expoKey E ≤ l → expoEval E l < BPair.unit := by
  intro l hl
  have hocc := topOcc_of_lower h
  obtain ⟨hl1, hcl, hT⟩ := expoCore E ((poly.ptrim E).length - 1) (ptrim_len_succ E hocc) hocc l hl
  have htop : poly.eval (expoTop E) (BPair.ofNat l) < BPair.unit := by
    refine windowsep.lead_lower _ _ ?_ ?_
    · rw [windowsep.mag_unitLe (unitLeOfNat l)]
      exact hcl
    · exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.unit_mul _)
        (ltB_mulPos h (unitLtBpow (unitLtNat hl1) _))
  have hswap : windowsep.mag (poly.eval (expoTop E) (BPair.ofNat l))
      = (poly.eval (expoTop E) (BPair.ofNat l)).swap := by
    unfold windowsep.mag
    rw [if_pos (ground.ltB_trans_le htop (leB_of_lt (ground.ltB_swap htop)))]
  rw [hswap, BPair.swap_mul] at hT
  have hpos : BPair.unit < (poly.eval (expoTop E) (BPair.ofNat l)
      * bpow (bpow (BPair.ofNat 2) l) ((poly.ptrim E).length - 1)
      + ground.famFold BPair.add BPair.unit
        (fun k => poly.eval (ground.getAt [] (poly.ptrim E) k) (BPair.ofNat l)
          * bpow (bpow (BPair.ofNat 2) l) k)
        (List.range ((poly.ptrim E).length - 1))).swap := by
    rw [← BPair.swap_add]
    refine side_of_dominant ?_
    rw [windowsep.mag_swap]
    exact hT
  have hlt := ground.ltB_swap hpos
  rw [BPair.swap_swap] at hlt
  refine BPair.lt_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
    (BPair.oneValue_symm (expoEval_split E _ (ptrim_len_succ E hocc) l))) (BPair.oneValue_refl _)
    hlt

set_option genInjectivity false in
/-- A rank-divisor record at an exponential-polynomial pair: the
divisor, its domain's floor, its clearance, and the domain's
equal-members ranks below the computed natural
(`lem:genericlift`(iv) at (v)). -/
structure ERec where
  div : poly.PPoly
  lo : Nat
  cl : Nat
  roots : List Nat

/-- The settled side's certificate at an exponential-polynomial
record: the top polynomial's leading coefficient's own side. -/
def expoSideCert (R : ERec) : Prop :=
  topUpper (expoTop R.div) ∨ topLower (expoTop R.div)

instance instGenericlift22 (R : ERec) : Decidable (expoSideCert R) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Clause (iv)'s window at (v): the naturals from the domain's floor
below the computed one, each its own read. -/
def expoRootsCert (R : ERec) : Prop :=
  (R.roots.all (fun k => decide (R.lo ≤ k) && decide (k < expoKey R.div))) = true
  ∧ ground.distinctList R.roots
  ∧ ((List.range (expoKey R.div)).filter (fun k => R.lo ≤ k)).all (fun k =>
    if 0 < ground.countOf k R.roots then
      decide ((expoEval R.div k).oneValue BPair.unit)
    else if R.cl ≤ k then
      (decide (topUpper (expoTop R.div))
        && decide (BPair.unit < expoEval R.div k))
      || (decide (topLower (expoTop R.div))
        && decide (expoEval R.div k < BPair.unit))
    else
      !(decide ((expoEval R.div k).oneValue BPair.unit))) = true

instance instGenericlift23 (R : ERec) : Decidable (expoRootsCert R) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Clause (iv)'s fold at (v): one natural at or beyond every stated
member's computed natural. -/
def expoClearsAll (Es : List poly.PPoly) (l : Nat) : Prop :=
  (Es.all (fun E => decide (expoKey E ≤ l))) = true

instance instGenericlift24 (Es : List poly.PPoly) (l : Nat) :
    Decidable (expoClearsAll Es l) :=
  inferInstanceAs (Decidable (_ = _))

end genericlift
