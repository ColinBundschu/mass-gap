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
real roots inside `thm:windowsep`'s bound (`liftRead` the
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
representative, the second spelling carrying the same bridge, and
`wg.pairFull`, `res.deflate1` and `kernel.kernelRead` are the fold seams
recorded as its consumers.  Clause (ii): the adjugate at the
polynomial-matrix cofactors (`pcofac`, `padj`), the identity
`M adj(M) = det(M) 1` the solved witness's whole verification
(`adjRead` at `split.pmatMul` and `split.pdiag`, the instance
deciding at the descent's adjugate `padjD` on a square frame with
`padjD_eq` the entrywise read), the identity a theorem at every
square frame in both product orders (`adjRead_all`,
`adjColRead_all`, `def:elim`'s adjugate identity at the
polynomial carrier), the determinant
pair off equal members the genericity read (`detOcc`, the
per-residue Gram independence its instances), the same solve stated
at the pair-entried carrier (`PPMat`, the first-row fold `ppminor`,
the transposed cofactors `ppadj`, and `ppadjRead` the whole
identity at `ppSquare`'s stated-order shape read, an unshaped
matrix reading vacuously — the instance deciding at the descent's
pair adjugate `ppadjD` on the occupied square frame with
`ppadjD_eq` the entrywise cross read, the fold branch the further
frames'), `con:res`'s solves the recorded
consumer.  Clause (iii): a pair keeps one side beyond its
members' largest real root — the
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
— `prop:wg`'s scheme, `con:res`'s solves,
`lem:rankstable`(iii)'s and `lem:serstable`(iii)'s symbolic
counts and the decimation's entry lists the recorded consumers.
-/

namespace genericlift
open ground poly elim

/-- Two pairs read one value at an argument, the cross-multiplied
Horner reads. -/
def agreeAt (x y : PPair) (r : BPair) : Prop :=
  BPair.oneValue (poly.eval x.1 r * poly.eval y.2 r)
    (poly.eval y.1 r * poly.eval x.2 r)

instance (x y : PPair) (r : BPair) : Decidable (agreeAt x y r) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The pair's site read: the second member occupied,
`def:ground`'s positive second datum mirrored at the polynomial
carrier. -/
def pairOcc (x : PPair) : Prop := ¬ poly.unitTail x.2

instance (x : PPair) : Decidable (pairOcc x) :=
  @instDecidableNot _ (poly.decUnitTail _)

/-- The pair's site read at an argument: the second member's value
occupied there. -/
def pairOccAt (x : PPair) (r : BPair) : Prop :=
  (poly.eval x.2 r).offUnit

instance (x : PPair) (r : BPair) : Decidable (pairOccAt x r) :=
  @instDecidableNot _ inferInstance

/-- The cross-multiplied site datum of two pairs, the difference's
polynomial. -/
def crossD (x y : PPair) : Poly :=
  poly.add (poly.mul x.1 y.2) ((poly.mul y.1 x.2).map BPair.swap)

/-- The symbolic conclusion: the cross datum reads the sum's unit
at every key, the pairs one value at every argument. -/
def crossNull (x y : PPair) : Prop := poly.unitTail (crossD x y)

instance (x y : PPair) : Decidable (crossNull x y) :=
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

instance (l : List BPair) : Decidable (pairwiseApart l) :=
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

instance (x y : PPair) (pts : List BPair) :
    Decidable (liftRead x y pts) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _))

/-- The polynomial cofactor at a struck row and column, the side
the key sum's. -/
def pcofac (m : split.PMat) (i j : Nat) : Poly :=
  elim.cofO split.pminor poly.neg m i j

/-- The adjugate, the transposed cofactors. -/
def padj (m : split.PMat) : split.PMat :=
  elim.adjO split.pminor poly.neg m

/-- Clause (ii)'s solved witness, whole:
`M adj(M) = det(M) 1`. -/
def adjRead (m : split.PMat) : Prop :=
  split.pmatOneValue (split.pmatMul m (padj m))
    (split.pdiag (List.replicate m.length (split.pminor m)))

/-- The adjugate at the descent, the transposed cofactors entry by
entry the erased frames' walks. -/
def padjD (m : split.PMat) : split.PMat :=
  elim.adjO elim.pdetD poly.neg m

/-- The walk adjugate reads the fold adjugate at a square frame,
entry by entry. -/
theorem padjD_eq (m : split.PMat) (hsq : elim.rowsLen m.length m) :
    split.pmatOneValue (padjD m) (padj m) := by
  unfold padjD padj elim.adjO
  refine split.pmatOne_ofGetAt
    (by rw [ground.matOf_length, ground.matOf_length]) (fun i hi => ?_)
  have him : i < m.length := by
    rw [ground.matOf_length] at hi
    exact hi
  rw [ground.matOf_row _ m.length m.length _ i him,
    ground.matOf_row _ m.length m.length _ i him]
  refine elim.matOne_getAt _ _
    (by rw [ground.length_map, ground.length_map]) (fun j hj => ?_)
  have hjm : j < m.length := by
    rw [ground.length_mapRange] at hj
    exact hj
  have hjr : j < (List.range m.length).length := by
    rw [ground.length_range]
    exact hjm
  rw [ground.getAt_map 0 [] _ (List.range m.length) j hjr,
    ground.getAt_map 0 [] _ (List.range m.length) j hjr,
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
  have hDV : poly.oneValue
      (elim.pdetD ((m.eraseIdx j).map (fun r => r.eraseIdx i)))
      (split.pminor ((m.eraseIdx j).map (fun r => r.eraseIdx i))) :=
    elim.pdetD_eq _ hE
  show poly.oneValue
    (elim.cofO elim.pdetD poly.neg m j i)
    (elim.cofO split.pminor poly.neg m j i)
  unfold elim.cofO
  cases places.parityOf (j + i) with
  | true => exact poly.swapMap_oneValue hDV
  | false => exact hDV

instance (m : split.PMat) : Decidable (adjRead m) :=
  match elim.decRowsLen m.length m with
  | isTrue hsq =>
    have hMul : split.pmatOneValue (split.pmatMul m (padjD m))
        (split.pmatMul m (padj m)) :=
      split.pmatMul_congr_right (padjD_eq m hsq) m
    have hD : split.pmatOneValue
        (split.pdiag (List.replicate m.length (elim.pdetD m)))
        (split.pdiag (List.replicate m.length (split.pminor m))) :=
      split.pdiag_repl_congr (elim.pdetD_eq m hsq) m.length
    decidable_of_iff
      (split.pmatOneValue (split.pmatMul m (padjD m))
        (split.pdiag (List.replicate m.length (elim.pdetD m))))
      ⟨fun x => split.pmatOne_trans (split.pmatOne_trans
          (split.pmatOne_symm hMul) x) hD,
       fun x => split.pmatOne_trans (split.pmatOne_trans hMul x)
          (split.pmatOne_symm hD)⟩
  | isFalse _ => split.decPmatOneValue _ _

/-- Clause (ii)'s solved witness as a theorem: at a square frame
the list against its adjugate reads the determinant's diagonal,
`def:elim`'s adjugate identity at the polynomial carrier. -/
theorem adjRead_all (m : split.PMat)
    (hsq : elim.rowsLen m.length m) : adjRead m := by
  have hAh : ((padj m).headD []).length = m.length :=
    elim.headD_len_of (padj m) m.length
      (ground.matOf_length m.length m.length _)
      (elim.rowsLen_matOf m.length m.length _)
  have hAl : (split.pmatMul m (padj m)).length = m.length :=
    ground.length_map _ m
  have hAr : elim.rowsLen m.length (split.pmatMul m (padj m)) :=
    elim.rowsLen_matMulO poly.polyOps m (padj m) m.length hAh
  have hrepl : (List.replicate m.length (split.pminor m)).length
      = m.length := ground.length_replicate _ m.length
  have hDl : (split.pdiag
      (List.replicate m.length (split.pminor m))).length
      = m.length := by
    rw [show (split.pdiag
        (List.replicate m.length (split.pminor m))).length
        = (List.replicate m.length (split.pminor m)).length from
      ground.matOf_length _ _ _]
    exact hrepl
  refine split.pmatOne_ofGetAt (by rw [hAl, hDl]) (fun i hi => ?_)
  rw [hAl] at hi
  have hiA : i < (split.pmatMul m (padj m)).length := by
    rw [hAl]
    exact hi
  have hrowA : (ground.getAt ([] : List poly.Poly)
      (split.pmatMul m (padj m)) i).length = m.length :=
    elim.rowsLen_getAt _ i hAr hiA
  have hrowD : (ground.getAt ([] : List poly.Poly) (split.pdiag
      (List.replicate m.length (split.pminor m))) i).length
      = m.length := by
    rw [show (ground.getAt ([] : List poly.Poly) (split.pdiag
        (List.replicate m.length (split.pminor m))) i).length
        = (List.replicate m.length (split.pminor m)).length from
      ground.matOf_rowLength ([] : List poly.Poly) _ _ _ i
        (by rw [hrepl]; exact hi)]
    exact hrepl
  refine elim.matOne_getAt _ _ (hrowA.trans hrowD.symm)
    (fun j hj => ?_)
  rw [hrowA] at hj
  rw [show ground.getAt ([] : poly.Poly)
      (ground.getAt ([] : List poly.Poly) (split.pdiag
        (List.replicate m.length (split.pminor m))) i) j
      = if j = i then ground.getAt ([] : poly.Poly)
          (List.replicate m.length (split.pminor m)) i
        else ([] : poly.Poly) from
    ground.matOf_entry ([] : List poly.Poly) ([] : poly.Poly) _ _ _
      i j (by rw [hrepl]; exact hi) (by rw [hrepl]; exact hj)]
  by_cases hji : j = i
  · rw [if_pos hji, ground.getAt_replicate ([] : poly.Poly)
      (split.pminor m) m.length i hi, hji]
    exact elim.adjO_row_diag (R := poly.polyRead) elim.polyLaws
      split.pminor poly.neg elim.minorP_detP
      (fun _ => poly.oneValue_refl _) m hsq i hi
  · rw [if_neg hji]
    exact elim.adjO_row_off (R := poly.polyRead) elim.polyLaws
      split.pminor poly.neg elim.minorP_detP
      (fun _ => poly.oneValue_refl _) m hsq i j hi hj
      (fun he => hji he.symm)

/-- Clause (ii)'s solved witness at the exchanged product order:
the adjugate against the list reads that diagonal as well, the
column side of `def:elim`'s adjugate identity. -/
theorem adjColRead_all (m : split.PMat)
    (hsq : elim.rowsLen m.length m) :
    split.pmatOneValue (split.pmatMul (padj m) m)
      (split.pdiag (List.replicate m.length (split.pminor m))) := by
  have hMh : (m.headD []).length = m.length :=
    elim.headD_len_of m m.length rfl hsq
  have hAdjl : (padj m).length = m.length :=
    ground.matOf_length m.length m.length _
  have hAl : (split.pmatMul (padj m) m).length = m.length := by
    rw [show (split.pmatMul (padj m) m).length = (padj m).length from
      ground.length_map _ (padj m)]
    exact hAdjl
  have hAr : elim.rowsLen m.length (split.pmatMul (padj m) m) :=
    elim.rowsLen_matMulO poly.polyOps (padj m) m m.length hMh
  have hrepl : (List.replicate m.length (split.pminor m)).length
      = m.length := ground.length_replicate _ m.length
  have hDl : (split.pdiag
      (List.replicate m.length (split.pminor m))).length
      = m.length := by
    rw [show (split.pdiag
        (List.replicate m.length (split.pminor m))).length
        = (List.replicate m.length (split.pminor m)).length from
      ground.matOf_length _ _ _]
    exact hrepl
  refine split.pmatOne_ofGetAt (by rw [hAl, hDl]) (fun i hi => ?_)
  rw [hAl] at hi
  have hiA : i < (split.pmatMul (padj m) m).length := by
    rw [hAl]
    exact hi
  have hrowA : (ground.getAt ([] : List poly.Poly)
      (split.pmatMul (padj m) m) i).length = m.length :=
    elim.rowsLen_getAt _ i hAr hiA
  have hrowD : (ground.getAt ([] : List poly.Poly) (split.pdiag
      (List.replicate m.length (split.pminor m))) i).length
      = m.length := by
    rw [show (ground.getAt ([] : List poly.Poly) (split.pdiag
        (List.replicate m.length (split.pminor m))) i).length
        = (List.replicate m.length (split.pminor m)).length from
      ground.matOf_rowLength ([] : List poly.Poly) _ _ _ i
        (by rw [hrepl]; exact hi)]
    exact hrepl
  refine elim.matOne_getAt _ _ (hrowA.trans hrowD.symm)
    (fun j hj => ?_)
  rw [hrowA] at hj
  rw [show ground.getAt ([] : poly.Poly)
      (ground.getAt ([] : List poly.Poly) (split.pdiag
        (List.replicate m.length (split.pminor m))) i) j
      = if j = i then ground.getAt ([] : poly.Poly)
          (List.replicate m.length (split.pminor m)) i
        else ([] : poly.Poly) from
    ground.matOf_entry ([] : List poly.Poly) ([] : poly.Poly) _ _ _
      i j (by rw [hrepl]; exact hi) (by rw [hrepl]; exact hj)]
  by_cases hji : j = i
  · rw [if_pos hji, ground.getAt_replicate ([] : poly.Poly)
      (split.pminor m) m.length i hi, hji]
    exact elim.adjO_col_diag (R := poly.polyRead) elim.polyLaws
      split.pminor poly.neg elim.minorP_detP
      (fun _ => poly.oneValue_refl _) m hsq i hi
  · rw [if_neg hji]
    exact elim.adjO_col_off (R := poly.polyRead) elim.polyLaws
      split.pminor poly.neg elim.minorP_detP
      (fun _ => poly.oneValue_refl _) m hsq i j hi hj
      (fun he => hji he.symm)

/-- The genericity read: the determinant pair off equal members,
the per-residue Gram independence its instances. -/
def detOcc (m : split.PMat) : Prop :=
  ¬ poly.unitTail (split.pminor m)

instance (m : split.PMat) : Decidable (detOcc m) :=
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

instance (P : Poly) (an : Pos) : Decidable (radiusClears P an) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The pair's clearance, both members'. -/
def clearsPair (x : PPair) (an : Pos) : Prop :=
  radiusClears x.1 an ∧ radiusClears x.2 an

instance (x : PPair) (an : Pos) : Decidable (clearsPair x an) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The settled side's upper read, the leading coefficient's own
at the value's representative, the degree's own read. -/
def topUpper (P : Poly) : Prop :=
  BPair.unit < poly.top (poly.vnorm P)

instance (P : Poly) : Decidable (topUpper P) :=
  inferInstanceAs (Decidable (_ < _))

/-- The settled side's lower read. -/
def topLower (P : Poly) : Prop :=
  poly.top (poly.vnorm P) < BPair.unit

instance (P : Poly) : Decidable (topLower P) :=
  inferInstanceAs (Decidable (_ < _))

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
      (windowsep.unitLt_bpow (ground.unitLtOfPos n) _))

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

instance (Ps : List Poly) (an : Pos) : Decidable (clearsAll Ps an) :=
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

instance (a b : List PPair) : Decidable (pprowEq a b) :=
  decPprowEq a b

/-- Two pair matrices read one value entrywise. -/
def ppmatEq : PPMat → PPMat → Prop :=
  ground.matchedOV (ground.matchedRead crossRead)

def decPpmatEq : ∀ a b, Decidable (ppmatEq a b) :=
  ground.decMatchedOV (ground.matchedRead crossRead)

instance (a b : PPMat) : Decidable (ppmatEq a b) :=
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

instance (m : PPMat) : Decidable (ppadjRead m) :=
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

instance (o : Nat) (m : PPMat) : Decidable (ppSquare o m) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

end genericlift
