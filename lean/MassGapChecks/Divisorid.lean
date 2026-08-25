import MassGap.Divisorid
/-!
The check module for `thm:divisorid`: the batteries read clause
(i)'s root identification by kernel `decide` beside the theorem's
route — at `lem:split`'s diagonal fixture `diag(1, 3)` against the
unit gram the pencil polynomial reads the unit at the level one and
off it at the level two, the listed roots' tie fold deciding the
same, and the theorem's instance joins the two; the factorization
binder refuses at a forged root list (the level four ties the
forged root while the polynomial reads off the unit), and the
gram's determinant binder refuses at the one-by-one vacant pencil,
whose polynomial is the unit throughout against the vacant root
list.  The Feshbach half reads at a one-by-one pivot against a
one-by-one tail: at the pivot two the cleared deflation's
determinant and the whole's read off the unit together, at the
pivot one the unit together; the pivot's determinant binder
refuses at the vacant pivot, the deflation the unit block against
the whole's determinant off it, and the solve binder at a witness
two against the coupling one, the deflation off the unit against
the whole's determinant at it; the symmetry binder is the clause's
symmetric setting, the deflation the Schur complement at every
pivot.

Clause (ii)'s crossing-read tier is pinned at the pencil
`diag(1, t)` over the base variable `t` against the unit gram: the
pencil polynomial's squarefree split is the single factor
`S_1 = (x − 1)(x − t)` at the content `c = 1`, the factor at its
stated top and primitive over the base's polynomial ring at the
certified division descent; its crossing read is the discriminant
`Res_x(S_1, S_1') = −(t − 1)² = −1 + 2 t − t²`, off the sum's unit,
reading the unit exactly at the collision `t = 1` and off it at
`t = 2`.  The two-factor split `S_2 = x − 1`, `S_3 = x − t` reads its
crossing divisor at the pair resultant `1 − t`, off the unit, while
the repeated pair `S_2, S_2` reads the unit there.  The refusals: the
two-member split reads `S_2 · S_3²` against the pencil polynomial,
the factor `t (1 + x)` of content `t` is not primitive, and the
polynomial `1 + 0 · x` parts with the resultant's stated site at its
vacant top.  The specialization's two binders refuse in turn: the
crossing read's at the collision, where the factor's root doubles,
and the leading coefficient's at the content `t` against `x − 1` at
the base point `t = 0`, where the evaluated pencil polynomial is the
unit tail.
-/
open ground poly elim inertia split divisorid

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

private def rD : List (BPair × Pos) := [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)]

/-! The root read at `diag(1, 3)`: the level one is a root, the
level two is off the roots, the tie fold deciding each. -/

example : (poly.eval (charPoly hD (idMat 2)) ⟨2, 1⟩).oneValue u := by
  decide +kernel
example : (rD.any (fun r => decide ((BPair.scale ⟨2, 1⟩ r.2).oneValue r.1)))
    = true := by decide +kernel
example : ¬ (poly.eval (charPoly hD (idMat 2)) ⟨3, 1⟩).oneValue u := by
  decide +kernel
example : ¬ (rD.any
    (fun r => decide ((BPair.scale ⟨3, 1⟩ r.2).oneValue r.1))) = true := by
  decide +kernel

example : (poly.eval (charPoly hD (idMat 2)) ⟨2, 1⟩).oneValue u :=
  (rootIff hD (idMat 2) rD (by decide +kernel) (by decide +kernel) ⟨2, 1⟩).mpr (by decide +kernel)
example : ¬ (poly.eval (charPoly hD (idMat 2)) ⟨3, 1⟩).oneValue u :=
  fun h => Bool.noConfusion
    ((rootIff hD (idMat 2) rD (by decide +kernel) (by decide +kernel) ⟨3, 1⟩).mp h)

/-! The factorization binder's refusal: at the forged root list the
level four ties the forged root while the polynomial reads off the
unit, so the identification parts with the gram binder holding. -/

private def rF : List (BPair × Pos) := [(⟨2, 1⟩, 1), (⟨5, 1⟩, 1)]

example : ¬ chiRead hD (idMat 2) rF := by decide +kernel
example : ¬ (minor (idMat 2)).oneValue u := by decide +kernel
example : ¬ ((poly.eval (charPoly hD (idMat 2)) ⟨5, 1⟩).oneValue u
    ↔ (rF.any (fun r => decide ((BPair.scale ⟨5, 1⟩ r.2).oneValue r.1)))
      = true) := by decide +kernel

/-! The gram binder's refusal: the one-by-one vacant pencil reads the
unit polynomial, its factorization at the vacant root list holding
at the gram's unit determinant, and the level one reads the unit
against the vacant tie fold. -/

example : chiRead [[u]] [[u]] [] := by decide +kernel
example : (minor [[u]]).oneValue u := by decide +kernel
example : ¬ ((poly.eval (charPoly [[u]] [[u]]) ⟨2, 1⟩).oneValue u
    ↔ (([] : List (BPair × Pos)).any
        (fun r => decide ((BPair.scale ⟨2, 1⟩ r.2).oneValue r.1)))
      = true) := by decide +kernel

/-! The Feshbach half at a one-by-one pivot against a one-by-one
tail. -/

private def p2 : Mat := [[⟨3, 1⟩]]
private def o1 : Mat := [[⟨2, 1⟩]]

example : ¬ (minor (deflMat p2 o1 o1 o1)).oneValue u := by decide +kernel
example : ¬ (minor (blockJoin p2 o1 o1)).oneValue u := by decide +kernel
example : ¬ (minor (deflMat p2 o1 o1 o1)).oneValue u :=
  fun h => (by decide +kernel : ¬ (minor (blockJoin p2 o1 o1)).oneValue u)
    ((deflRoot (k := 1) (m := 1) p2 o1 o1 o1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).mp h)

example : (minor (deflMat o1 o1 o1 o1)).oneValue u := by decide +kernel
example : (minor (blockJoin o1 o1 o1)).oneValue u := by decide +kernel
example : (minor (deflMat o1 o1 o1 o1)).oneValue u :=
  (deflRoot (k := 1) (m := 1) o1 o1 o1 o1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).mpr
    (by decide +kernel)

/-! The pivot's determinant binder's refusal at the vacant pivot, and
the solve binder's at a witness two against the coupling one. -/

example : (minor [[u]]).oneValue u := by decide +kernel
example : ¬ ((minor (deflMat [[u]] o1 o1 o1)).oneValue u
    ↔ (minor (blockJoin [[u]] o1 o1)).oneValue u) := by decide +kernel

example : ¬ matOneValue (matMul o1 p2) (matScaleB (minor o1) o1) := by decide +kernel
example : ¬ ((minor (deflMat o1 o1 o1 p2)).oneValue u
    ↔ (minor (blockJoin o1 o1 o1)).oneValue u) := by decide +kernel

/-! `thm:divisorid`(ii)'s crossing-read tier at the pencil
`diag(1, t)` over the base variable `t`. -/

private def tB : Poly := [u, ⟨2, 1⟩]

private def hP : split.PMat := [[[⟨2, 1⟩], []], [[], tB]]

private def gP : split.PMat := [[[⟨2, 1⟩], []], [[], [⟨2, 1⟩]]]

private def chiP : poly.PPoly := split.ppminor (split.ppzMat hP gP)

/-- `(x − 1)(x − t) = x² − (1 + t) x + t`. -/
private def s1 : poly.PPoly := [tB, [⟨1, 2⟩, ⟨1, 2⟩], [⟨2, 1⟩]]

/-- `x − 1`. -/
private def s2 : poly.PPoly := [[⟨1, 2⟩], [⟨2, 1⟩]]

/-- `x − t`. -/
private def s3 : poly.PPoly := [[u, ⟨1, 2⟩], [⟨2, 1⟩]]

/-! The split at the single factor `S_1 = (x − 1)(x − t)` with the
content `c = 1`: the pencil polynomial reads the product, the factor
sits at its stated top and is primitive over the base. -/

example : splitRead chiP [⟨2, 1⟩] [s1] := by decide +kernel

example : topOff s1 := by decide +kernel
example : primitiveP s1 := by decide +kernel

/-! The crossing read at that split is the discriminant
`Res_x(S_1, S_1') = −(t − 1)² = −1 + 2 t − t²`, a base element off
the sum's unit, and its own root locus is the collision `t = 1`. -/

example : poly.oneValue (crossD [s1]) [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 2⟩] := by decide +kernel

example : crossOff [s1] := by decide +kernel

example : (poly.eval (crossD [s1]) ⟨2, 1⟩).oneValue u := by decide +kernel
example : ¬ (poly.eval (crossD [s1]) ⟨3, 1⟩).oneValue u := by decide +kernel

/-! The coprime pair `S_2 = x − 1`, `S_3 = x − t` reads its crossing
divisor at the pair resultant `1 − t`, off the sum's unit; the
repeated pair reads the unit, no crossing read there. -/

example : poly.oneValue (crossD [s2, s3]) [⟨2, 1⟩, ⟨1, 2⟩] := by decide +kernel

example : crossOff [s2, s3] := by decide +kernel

example : ¬ crossOff [s2, s2] := by decide +kernel

/-! The split's refusals: the two-member split reads `S_2 · S_3²`,
not the pencil polynomial; a factor of content `t` is not primitive;
and a vacant top coefficient parts with the resultant's site. -/

example : ¬ splitRead chiP [⟨2, 1⟩] [s2, s3] := by decide +kernel

example : ¬ primitiveP [tB, tB] := by decide +kernel

example : ¬ topOff [[⟨2, 1⟩], []] := by decide +kernel

/-! The specialization's reads at the split above: the resultant's
evaluation at the base point two reads the evaluated factors'
resultant, a common root of two factors reads their resultant at the
unit, and a rooted factor at an off-unit top has positive degree. -/

example : (poly.eval (presultant s2 s3) ⟨3, 1⟩).oneValue
    (resultant (poly.pevalB s2 ⟨3, 1⟩) (poly.pevalB s3 ⟨3, 1⟩)) := by decide +kernel
example : (poly.eval (presultant s2 s3) ⟨3, 1⟩).oneValue
    (resultant (poly.pevalB s2 ⟨3, 1⟩) (poly.pevalB s3 ⟨3, 1⟩)) :=
  pevalB_presultant s2 s3 ⟨3, 1⟩

example : (resultant [⟨1, 2⟩, ⟨2, 1⟩] [⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩]).oneValue u := by
  decide +kernel
example : (resultant [⟨1, 2⟩, ⟨2, 1⟩] [⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩]).oneValue u :=
  resultant_unit_of_roots _ _ (by decide +kernel) ⟨2, 1⟩ (by decide +kernel) (by decide +kernel)
example : ¬ (resultant [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]).oneValue u := by
  decide +kernel

example : 0 < ([⟨1, 2⟩, ⟨2, 1⟩] : poly.Poly).length - 1 :=
  length_of_root _ (by decide +kernel) ⟨2, 1⟩ (by decide +kernel)

/-! The specialization at the split above: at the base point two,
off the crossing read's locus and at the leading coefficient one off
the unit, the root one of the pencil polynomial is the factor's
simple root at multiplicity one in the pencil polynomial, the
theorem's instance beside the decided counts; at the collision one
the crossing read sits at the unit and the root is the factor's
double root, the pencil polynomial's multiplicity there two. -/

example : ∃ j, j < ([s1] : List poly.PPoly).length
    ∧ poly.isRoot (poly.pevalB (ground.getAt [] [s1] j) ⟨3, 1⟩) ⟨2, 1⟩
    ∧ poly.multAt [⟨1, 2⟩]
        (poly.pevalB (ground.getAt [] [s1] j) ⟨3, 1⟩) = 1
    ∧ (∀ i, i < ([s1] : List poly.PPoly).length →
        poly.isRoot (poly.pevalB (ground.getAt [] [s1] i) ⟨3, 1⟩) ⟨2, 1⟩
          → i = j)
    ∧ poly.multAt [⟨1, 2⟩] (poly.pevalB chiP ⟨3, 1⟩) = j + 1 :=
  specialize chiP [⟨2, 1⟩] [s1] (by decide +kernel) ⟨3, 1⟩ (by decide +kernel) (by decide +kernel)
    ⟨2, 1⟩ (by decide +kernel)

example : poly.multAt [⟨1, 2⟩] (poly.pevalB chiP ⟨3, 1⟩) = 1 := by
  decide +kernel
example : poly.multAt [⟨1, 2⟩] (poly.pevalB s1 ⟨3, 1⟩) = 1 := by decide +kernel
example : poly.multAt [⟨1, 2⟩] (poly.pevalB chiP ⟨2, 1⟩) = 2 := by
  decide +kernel
example : ¬ poly.multAt [⟨1, 2⟩] (poly.pevalB s1 ⟨2, 1⟩) = 1 := by decide +kernel

/-! The leading-coefficient binder's refusal at `χ = t (x − 1)`, the
content `t` against the factor `x − 1`: at the base point `t = 0`
the crossing read `Res_x(x − 1, 1) = 1` is off the unit and the split
holds, while the leading coefficient `t` reads the unit there and the
evaluated pencil polynomial is the unit tail, its multiplicity at the
factor's root one the whole carrier's count two against the factor's
place one.  Clause (iii)'s cell read at the order-one two-level
fixture: the two carriers' covers over one segment, the multiplicity
pair transported from the sample to the interior point decided and
through `groundMult`, and the rooted carrier's refusals isolating
the cover binders. -/

private def chiQ : poly.PPoly := poly.pmul [tB] s2

example : splitRead chiQ tB [s2] := by decide +kernel
example : ¬ (poly.eval (crossD [s2]) ⟨1, 1⟩).oneValue u := by decide +kernel
example : (poly.eval (poly.ptop chiQ) ⟨1, 1⟩).oneValue u := by decide +kernel
example : poly.isRoot (poly.pevalB s2 ⟨1, 1⟩) ⟨2, 1⟩ := by decide +kernel
example : ¬ poly.multAt [⟨1, 2⟩] (poly.pevalB chiQ ⟨1, 1⟩) = 0 + 1 := by
  decide +kernel

/-! Clause (iii)'s cell read at the order-one pencil `(2 + t : aG)`
over `[1, 2]`: the level nought carrier `t + 2` on its upper side at
count nought and the level seven carrier `t - 5` on its lower side
at count one, the multiplicity pair transported from the sample `1`
to the interior point `3/2` decided and through `groundMult`; and
the pencil `(3 + 2t : aG)` at the level five, its carrier `2t - 3`
rooted inside the segment, refusing both side candidates at every
stated bound and reading distinct counts at the two endpoints — the
cover binders the isolated ones. -/

private def mA : elim.Mat := [[⟨3, 1⟩]]
private def mB : elim.Mat := [[⟨2, 1⟩]]
private def mG : elim.Mat := [[⟨2, 1⟩]]
private def sL : split.PMat := cellcount.levelPMat mA mB mG 1 1 []
private def sH : split.PMat := cellcount.levelPMat mA mB mG 8 1 []
private def loG : CPair := ⟨⟨2, 1⟩, 1⟩
private def hiG : CPair := ⟨⟨3, 1⟩, 1⟩
private def cvL : cellcount.Cover :=
  cellcount.Cover.one hiG 0 true ⟨3, 1⟩ ⟨2, 1⟩
    cellcount.Cover.nought cellcount.Cover.done
private def cvH : cellcount.Cover :=
  cellcount.Cover.one hiG 0 false ⟨8, 1⟩ ⟨2, 1⟩
    cellcount.Cover.nought cellcount.Cover.done

private theorem covLr : cellcount.coverRead sL 1 1 loG hiG cvL := by
  decide +kernel
private theorem covHr : cellcount.coverRead sH 1 1 loG hiG cvH := by
  decide +kernel

example :
    inertia.psdAt (inertia.mkSplit 1 (cellcount.evalPC sL ⟨4, 1⟩ 2 1))
    ∧ inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sH ⟨4, 1⟩ 2 1))
      = 1 := by decide +kernel

example :
    inertia.psdAt (inertia.mkSplit 1 (cellcount.evalPC sL ⟨4, 1⟩ 2 1))
    ∧ inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sH ⟨4, 1⟩ 2 1))
      = 1 :=
  groundMult mA mB mG [] 1 1 8 1 (by decide +kernel) loG hiG cvL cvH
    covLr covHr ⟨2, 1⟩ 1 ⟨4, 1⟩ 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 1
    (inertia.mkSplit 1 (cellcount.evalPC sL ⟨2, 1⟩ 1 1))
    (inertia.mkSplit 1 (cellcount.evalPC sH ⟨2, 1⟩ 1 1))
    (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 1 (cellcount.evalPC sL ⟨4, 1⟩ 2 1))
    (inertia.mkSplit 1 (cellcount.evalPC sH ⟨4, 1⟩ 2 1))
    (inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel))
    (inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel))

private def mA2 : elim.Mat := [[⟨4, 1⟩]]
private def mB2 : elim.Mat := [[⟨3, 1⟩]]
private def mG2 : elim.Mat := [[⟨3, 1⟩]]
private def sX : split.PMat := cellcount.levelPMat mA2 mB2 mG2 4 1 []

example : ¬ cellcount.coverRead sX 1 1 loG hiG
    (cellcount.Cover.one hiG 0 false ⟨8, 1⟩ ⟨2, 1⟩
      cellcount.Cover.nought cellcount.Cover.done) := by decide +kernel
example : ¬ cellcount.coverRead sX 1 1 loG hiG
    (cellcount.Cover.one hiG 0 true ⟨8, 1⟩ ⟨2, 1⟩
      cellcount.Cover.nought cellcount.Cover.done) := by decide +kernel
example :
    inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sX ⟨2, 1⟩ 1 1))
      = 1
    ∧ inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sX ⟨3, 1⟩ 1 1))
      = 0 := by decide +kernel
