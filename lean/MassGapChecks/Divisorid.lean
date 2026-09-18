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
and the gram's positive-definite split at the one-by-one pencil
`H = G = [t]`, `χ = t (x − 1)`, at the base point `t = 0`, where the
evaluated gram splits at a kernel block of order one and the
evaluated pencil polynomial is the unit tail.  The leading read
decides at `diag(1, t)`: the pencil polynomial's outer top is the
gram's determinant, the theorem's instance beside the decided read,
and the gram's split at the base point two is positive definite.
-/

namespace divisorid
open ground poly elim inertia split

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

private def rD : List (BPair × Pos) := [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)]

/-! The root read at `diag(1, 3)`: the level one is a root, the
level two is off the roots, the tie fold deciding each. -/

theorem pin1 : (poly.eval (charPoly hD (idMat 2)) ⟨2, 1⟩).oneValue u := by
  decide +kernel
theorem pin2 : (rD.any (fun r => decide ((BPair.scale ⟨2, 1⟩ r.2).oneValue r.1)))
    = true := by decide +kernel
theorem pin3 : ¬ (poly.eval (charPoly hD (idMat 2)) ⟨3, 1⟩).oneValue u := by
  decide +kernel
theorem pin4 : ¬ (rD.any
    (fun r => decide ((BPair.scale ⟨3, 1⟩ r.2).oneValue r.1))) = true := by
  decide +kernel

theorem pin5 : (poly.eval (charPoly hD (idMat 2)) ⟨2, 1⟩).oneValue u :=
  (rootIff hD (idMat 2) rD (by decide +kernel) (by decide +kernel) ⟨2, 1⟩).mpr (by decide +kernel)
theorem pin6 : ¬ (poly.eval (charPoly hD (idMat 2)) ⟨3, 1⟩).oneValue u :=
  fun h => Bool.noConfusion
    ((rootIff hD (idMat 2) rD (by decide +kernel) (by decide +kernel) ⟨3, 1⟩).mp h)

/-! The factorization binder's refusal: at the forged root list the
level four ties the forged root while the polynomial reads off the
unit, so the identification parts with the gram binder holding. -/

private def rF : List (BPair × Pos) := [(⟨2, 1⟩, 1), (⟨5, 1⟩, 1)]

theorem pin7 : ¬ chiRead hD (idMat 2) rF := by decide +kernel
theorem pin8 : ¬ (minor (idMat 2)).oneValue u := by decide +kernel
theorem pin9 : ¬ ((poly.eval (charPoly hD (idMat 2)) ⟨5, 1⟩).oneValue u
    ↔ (rF.any (fun r => decide ((BPair.scale ⟨5, 1⟩ r.2).oneValue r.1)))
      = true) := by decide +kernel

/-! The gram binder's refusal: the one-by-one vacant pencil reads the
unit polynomial, its factorization at the vacant root list holding
at the gram's unit determinant, and the level one reads the unit
against the vacant tie fold. -/

theorem pin10 : chiRead [[u]] [[u]] [] := by decide +kernel
theorem pin11 : (minor [[u]]).oneValue u := by decide +kernel
theorem pin12 : ¬ ((poly.eval (charPoly [[u]] [[u]]) ⟨2, 1⟩).oneValue u
    ↔ (([] : List (BPair × Pos)).any
        (fun r => decide ((BPair.scale ⟨2, 1⟩ r.2).oneValue r.1)))
      = true) := by decide +kernel

/-! The Feshbach half at a one-by-one pivot against a one-by-one
tail. -/

private def p2 : Mat := [[⟨3, 1⟩]]
private def o1 : Mat := [[⟨2, 1⟩]]

theorem pin13 : ¬ (minor (deflMat p2 o1 o1 o1)).oneValue u := by decide +kernel
theorem pin14 : ¬ (minor (blockJoin p2 o1 o1)).oneValue u := by decide +kernel
theorem pin15 : ¬ (minor (deflMat p2 o1 o1 o1)).oneValue u :=
  fun h => (by decide +kernel : ¬ (minor (blockJoin p2 o1 o1)).oneValue u)
    ((deflRoot (k := 1) (m := 1) p2 o1 o1 o1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).mp h)

theorem pin16 : (minor (deflMat o1 o1 o1 o1)).oneValue u := by decide +kernel
theorem pin17 : (minor (blockJoin o1 o1 o1)).oneValue u := by decide +kernel
theorem pin18 : (minor (deflMat o1 o1 o1 o1)).oneValue u :=
  (deflRoot (k := 1) (m := 1) o1 o1 o1 o1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).mpr
    (by decide +kernel)

/-! The pivot's determinant binder's refusal at the vacant pivot, and
the solve binder's at a witness two against the coupling one. -/

theorem pin19 : (minor [[u]]).oneValue u := by decide +kernel
theorem pin20 : ¬ ((minor (deflMat [[u]] o1 o1 o1)).oneValue u
    ↔ (minor (blockJoin [[u]] o1 o1)).oneValue u) := by decide +kernel

theorem pin21 : ¬ matOneValue (matMul o1 p2) (matScaleB (minor o1) o1) := by decide +kernel
theorem pin22 : ¬ ((minor (deflMat o1 o1 o1 p2)).oneValue u
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

theorem pin23 : splitRead chiP [⟨2, 1⟩] [s1] := by decide +kernel

theorem pin24 : topOff s1 := by decide +kernel
theorem pin25 : primitiveP s1 := by decide +kernel

/-! The crossing read at that split is the discriminant
`Res_x(S_1, S_1') = −(t − 1)² = −1 + 2 t − t²`, a base element off
the sum's unit, and its own root locus is the collision `t = 1`. -/

theorem pin26 : poly.oneValue (crossD [s1]) [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 2⟩] := by decide +kernel

theorem pin27 : crossOff [s1] := by decide +kernel

theorem pin28 : (poly.eval (crossD [s1]) ⟨2, 1⟩).oneValue u := by decide +kernel
theorem pin29 : ¬ (poly.eval (crossD [s1]) ⟨3, 1⟩).oneValue u := by decide +kernel

/-! The coprime pair `S_2 = x − 1`, `S_3 = x − t` reads its crossing
divisor at the pair resultant `1 − t`, off the sum's unit; the
repeated pair reads the unit, no crossing read there. -/

theorem pin30 : poly.oneValue (crossD [s2, s3]) [⟨2, 1⟩, ⟨1, 2⟩] := by decide +kernel

theorem pin31 : crossOff [s2, s3] := by decide +kernel

theorem pin32 : ¬ crossOff [s2, s2] := by decide +kernel

/-! The split's refusals: the two-member split reads `S_2 · S_3²`,
not the pencil polynomial; a factor of content `t` is not primitive;
and a vacant top coefficient parts with the resultant's site. -/

theorem pin33 : ¬ splitRead chiP [⟨2, 1⟩] [s2, s3] := by decide +kernel

theorem pin34 : ¬ primitiveP [tB, tB] := by decide +kernel

theorem pin35 : ¬ topOff [[⟨2, 1⟩], []] := by decide +kernel

/-! The specialization's reads at the split above: the resultant's
evaluation at the base point two reads the evaluated factors'
resultant, a common root of two factors reads their resultant at the
unit, and a rooted factor at an off-unit top has positive degree. -/

theorem pin36 : (poly.eval (presultant s2 s3) ⟨3, 1⟩).oneValue
    (resultant (poly.pevalB s2 ⟨3, 1⟩) (poly.pevalB s3 ⟨3, 1⟩)) := by decide +kernel
theorem pin37 : (poly.eval (presultant s2 s3) ⟨3, 1⟩).oneValue
    (resultant (poly.pevalB s2 ⟨3, 1⟩) (poly.pevalB s3 ⟨3, 1⟩)) :=
  pevalB_presultant s2 s3 ⟨3, 1⟩

theorem pin38 : (resultant [⟨1, 2⟩, ⟨2, 1⟩] [⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩]).oneValue u := by
  decide +kernel
theorem pin39 : (resultant [⟨1, 2⟩, ⟨2, 1⟩] [⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩]).oneValue u :=
  resultant_unit_of_roots _ _ (by decide +kernel) ⟨2, 1⟩ (by decide +kernel) (by decide +kernel)
theorem pin40 : ¬ (resultant [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]).oneValue u := by
  decide +kernel

theorem pin41 : 0 < ([⟨1, 2⟩, ⟨2, 1⟩] : poly.Poly).length - 1 :=
  length_of_root _ (by decide +kernel) ⟨2, 1⟩ (by decide +kernel)

/-! The specialization at the split above: at the base point two,
off the crossing read's locus and at the unit gram's positive-definite
split there, the root one of the pencil polynomial is the factor's
simple root at multiplicity one in the pencil polynomial, the
theorem's instance beside the decided counts; at the collision one
the crossing read sits at the unit and the root is the factor's
double root, the pencil polynomial's multiplicity there two. -/

theorem pin42 : ∃ j, j < ([s1] : List poly.PPoly).length
    ∧ poly.isRoot (poly.pevalB (ground.getAt [] [s1] j) ⟨3, 1⟩) ⟨2, 1⟩
    ∧ poly.multAt [⟨1, 2⟩]
        (poly.pevalB (ground.getAt [] [s1] j) ⟨3, 1⟩) = 1
    ∧ (∀ i, i < ([s1] : List poly.PPoly).length →
        poly.isRoot (poly.pevalB (ground.getAt [] [s1] i) ⟨3, 1⟩) ⟨2, 1⟩
          → i = j)
    ∧ poly.multAt [⟨1, 2⟩] (poly.pevalB chiP ⟨3, 1⟩) = j + 1 :=
  specialize hP gP 2 rfl (by decide +kernel) rfl (by decide +kernel) chiP rfl
    [⟨2, 1⟩] [s1] (by decide +kernel) ⟨3, 1⟩ (by decide +kernel)
    (inertia.mkSplit 2 (gP.map (fun row => poly.pevalB row ⟨3, 1⟩)))
    (inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel))
    (by decide +kernel) ⟨2, 1⟩ (by decide +kernel)

theorem pin43 : poly.multAt [⟨1, 2⟩] (poly.pevalB chiP ⟨3, 1⟩) = 1 := by
  decide +kernel
theorem pin44 : poly.multAt [⟨1, 2⟩] (poly.pevalB s1 ⟨3, 1⟩) = 1 := by decide +kernel
theorem pin45 : poly.multAt [⟨1, 2⟩] (poly.pevalB chiP ⟨2, 1⟩) = 2 := by
  decide +kernel
theorem pin46 : ¬ poly.multAt [⟨1, 2⟩] (poly.pevalB s1 ⟨2, 1⟩) = 1 := by decide +kernel

/-! The gram binder's refusal at the one-by-one pencil `H = G = [t]`,
`χ = t (x − 1)`, the content `t` against the factor `x − 1`: at the
base point `t = 0` the crossing read `Res_x(x − 1, 1) = 1` is off the
unit and the split holds, while the evaluated gram `[0]` splits at
the kernel block of order one, its positive-definite read refused,
and the evaluated pencil polynomial is the unit tail, its
multiplicity at the factor's root one the whole carrier's count two
against the factor's place one. -/

private def hQ : split.PMat := [[tB]]
private def chiQ : poly.PPoly := split.ppminor (split.ppzMat hQ hQ)

theorem pin47 : splitRead chiQ tB [s2] := by decide +kernel
theorem pin48 : ¬ (poly.eval (crossD [s2]) ⟨1, 1⟩).oneValue u := by decide +kernel
theorem pin49 :
    inertia.splitRead (hQ.map (fun row => poly.pevalB row ⟨1, 1⟩))
      (inertia.mkSplit 1 (hQ.map (fun row => poly.pevalB row ⟨1, 1⟩)))
    ∧ ¬ inertia.pdAt
      (inertia.mkSplit 1 (hQ.map (fun row => poly.pevalB row ⟨1, 1⟩))) := by
  decide +kernel
theorem pin50 : poly.isRoot (poly.pevalB s2 ⟨1, 1⟩) ⟨2, 1⟩ := by decide +kernel
theorem pin51 : ¬ poly.multAt [⟨1, 2⟩] (poly.pevalB chiQ ⟨1, 1⟩) = 0 + 1 := by
  decide +kernel

/-! The leading read at `diag(1, t)` against the unit gram: the
pencil polynomial's outer top is the gram's determinant, decided
and through `split.ptop_ppzMat`, and the gram's split at the base
point two is positive definite, the specialization's gram binder at
its record. -/

theorem pin52 : poly.oneValue (poly.ptop chiP) (split.pminor gP) := by
  decide +kernel
theorem pin53 : poly.oneValue (poly.ptop chiP) (split.pminor gP) :=
  split.ptop_ppzMat hP gP 2 rfl (by decide +kernel) rfl (by decide +kernel)
theorem pin54 : inertia.pdAt
    (inertia.mkSplit 2 (gP.map (fun row => poly.pevalB row ⟨3, 1⟩))) := by
  decide +kernel

/-! The gram binder's frame record at an indefinite gram, the
one-by-one pencil `H = [1]`, `G = [−1]`, `χ = −(x + 1)`, the content
`−1` against the factor `x + 1`, at the base point two and the root
`−1`: every co-binder holds, the evaluated gram's split reads its
kernel block vacant with one reversal, so the positive-definite read
refuses at its reversal conjunct alone, and the conclusion holds at
the factor's place with the leading coefficient off the unit — the
kernel block is the consumed conjunct and the reversal count the
frame's, thm:divisorid(ii)'s `G ≻ 0`. -/

private def hN : split.PMat := [[[⟨2, 1⟩]]]
private def gN : split.PMat := [[[⟨1, 2⟩]]]
private def chiN : poly.PPoly := split.ppminor (split.ppzMat hN gN)
/-- `x + 1`. -/
private def sN : poly.PPoly := [[⟨2, 1⟩], [⟨2, 1⟩]]

theorem pin55 : splitRead chiN [⟨1, 2⟩] [sN]
    ∧ ¬ (poly.eval (crossD [sN]) ⟨3, 1⟩).oneValue u
    ∧ inertia.splitRead (gN.map (fun row => poly.pevalB row ⟨3, 1⟩))
        (inertia.mkSplit 1 (gN.map (fun row => poly.pevalB row ⟨3, 1⟩)))
    ∧ poly.isRoot (poly.pevalB chiN ⟨3, 1⟩) ⟨1, 2⟩ := by decide +kernel
theorem pin56 :
    ¬ inertia.pdAt (inertia.mkSplit 1 (gN.map (fun row => poly.pevalB row ⟨3, 1⟩)))
    ∧ (inertia.mkSplit 1 (gN.map (fun row => poly.pevalB row ⟨3, 1⟩))).kern = 0
    ∧ inertia.revAt (inertia.mkSplit 1 (gN.map (fun row => poly.pevalB row ⟨3, 1⟩)))
      = 1 := by decide +kernel
theorem pin57 : poly.isRoot (poly.pevalB sN ⟨3, 1⟩) ⟨1, 2⟩
    ∧ poly.multAt [⟨2, 1⟩] (poly.pevalB sN ⟨3, 1⟩) = 1
    ∧ poly.multAt [⟨2, 1⟩] (poly.pevalB chiN ⟨3, 1⟩) = 0 + 1
    ∧ ¬ (poly.eval (poly.ptop chiN) ⟨3, 1⟩).oneValue u := by decide +kernel

/-! The dropped symmetry frame's record: thm:divisorid(ii) frames a
symmetric pencil, and the statement binds the gram's split alone
(the gram's symmetry inside the congruence identity), so at the
pencil `H = [[1, t], [0, 2]]` against the unit gram,
`χ = (x − 1)(x − 2)`, the evaluated pencil member refuses the
symmetry read while the specialization applies whole at the base
point two and the root one. -/

private def hS : split.PMat := [[[⟨2, 1⟩], tB], [[], [⟨3, 1⟩]]]
private def chiS : poly.PPoly := split.ppminor (split.ppzMat hS gP)
/-- `(x − 1)(x − 2) = x² − 3x + 2`. -/
private def sS : poly.PPoly := [[⟨3, 1⟩], [⟨1, 4⟩], [⟨2, 1⟩]]

theorem pin58 : ¬ elim.matOneValue
    (elim.transposeM (hS.map (fun row => poly.pevalB row ⟨3, 1⟩)))
    (hS.map (fun row => poly.pevalB row ⟨3, 1⟩)) := by decide +kernel
theorem pin59 : ∃ j, j < ([sS] : List poly.PPoly).length
    ∧ poly.isRoot (poly.pevalB (ground.getAt [] [sS] j) ⟨3, 1⟩) ⟨2, 1⟩
    ∧ poly.multAt [⟨1, 2⟩]
        (poly.pevalB (ground.getAt [] [sS] j) ⟨3, 1⟩) = 1
    ∧ (∀ i, i < ([sS] : List poly.PPoly).length →
        poly.isRoot (poly.pevalB (ground.getAt [] [sS] i) ⟨3, 1⟩) ⟨2, 1⟩
          → i = j)
    ∧ poly.multAt [⟨1, 2⟩] (poly.pevalB chiS ⟨3, 1⟩) = j + 1 :=
  specialize hS gP 2 rfl (by decide +kernel) rfl (by decide +kernel) chiS rfl
    [⟨2, 1⟩] [sS] (by decide +kernel) ⟨3, 1⟩ (by decide +kernel)
    (inertia.mkSplit 2 (gP.map (fun row => poly.pevalB row ⟨3, 1⟩)))
    (inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel))
    (by decide +kernel) ⟨2, 1⟩ (by decide +kernel)

/-! Clause (iii)'s cell read at the order-one two-level fixture: the
two carriers' covers over one segment, the multiplicity pair
transported from the sample to the interior point decided and
through `groundMult`, and the rooted carrier's refusals isolating
the cover binders.  At the order-one pencil `(2 + t : aG)`
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

theorem pin60 :
    inertia.psdAt (inertia.mkSplit 1 (cellcount.evalPC sL ⟨4, 1⟩ 2 1))
    ∧ inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sH ⟨4, 1⟩ 2 1))
      = 1 := by decide +kernel

theorem pin61 :
    inertia.psdAt (inertia.mkSplit 1 (cellcount.evalPC sL ⟨4, 1⟩ 2 1))
    ∧ inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sH ⟨4, 1⟩ 2 1))
      = 1 :=
  groundMult mA mB mG [] 1 1 8 1 (by decide +kernel) loG hiG cvL cvH
    covLr covHr (by decide +kernel) (by decide +kernel)
    ⟨2, 1⟩ 1 ⟨4, 1⟩ 2 (by decide +kernel)
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

theorem pin62 : ¬ cellcount.coverRead sX 1 1 loG hiG
    (cellcount.Cover.one hiG 0 false ⟨8, 1⟩ ⟨2, 1⟩
      cellcount.Cover.nought cellcount.Cover.done) := by decide +kernel
theorem pin63 : ¬ cellcount.coverRead sX 1 1 loG hiG
    (cellcount.Cover.one hiG 0 true ⟨8, 1⟩ ⟨2, 1⟩
      cellcount.Cover.nought cellcount.Cover.done) := by decide +kernel
theorem pin64 :
    inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sX ⟨2, 1⟩ 1 1))
      = 1
    ∧ inertia.revAt (inertia.mkSplit 1 (cellcount.evalPC sX ⟨3, 1⟩ 1 1))
      = 0 := by decide +kernel

end divisorid
