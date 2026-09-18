import MassGap.Split
import MassGap.Certconstruct
import MassGap.Windowsep
/-!
The check module for `lem:split`: the batteries re-read the pencil
split's identity instances by kernel `decide` — the pencil
polynomial at the diagonal `diag(1, 3)` and at `[[1,2],[2,1]]`
against the unit gram, the factorization reads at the stated root
lists (`chiRead` at `(1, 3)` and `(3, -1)`), the count identities
at the split certificates (`countRead`, the reversal against the
located roots' display), the diagonalizing congruences (`diagRead`
at the identity and at `T = [[1,-1],[1,1]]` with their adjugate
witnesses, the scales two on their upper sides), the completed
certificate's coefficient tier (the congruence's two coefficient
matrices, the diagonal side's two, and the eigen-column read at the
committed diagonalization), the factorization as the congruence
certificate's own read (`diag_chiRead` at the committed
diagonalization, the moved-root refusal beside it), and the
resultant's kernel read at its
arrival: the cross pair at one shared root with the resultant's
equal members, and the Bézout clause at the coprime complement
(`elim.bezout_all` decided beside its own route, `topsUnequal`).
A designation's width clause composes here: the pencil
polynomial's separation read at `thm:windowsep` prices
`thm:certconstruct`'s bracket, the composition's instance beside
the counts. -/

namespace split
set_option maxHeartbeats 4000000

open ground poly elim inertia

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]
private def hM : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩]]

/-! The pencil polynomials: `(x-1)(x-3)` at the diagonal and
`(x-3)(x+1)` at the coupled datum. -/

theorem pin1 : poly.oneValue (charPoly hD (idMat 2))
    [⟨4, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin2 : poly.oneValue (charPoly hM (idMat 2))
    [⟨1, 4⟩, ⟨1, 3⟩, ⟨2, 1⟩] := by decide +kernel

/-! The pencil polynomial at the descent's read (`charPolyD`,
`charPolyD_eq`): the walk against the fold at the two level pairs,
decided and through the theorem, and the square binder isolated at
a two-row level pencil over three columns against the unit gram of
order three, the site datum two rows wide at three keys, where the
walk reads the leading block and the fold the three-column
expansion. -/

theorem pin3 : poly.oneValue (charPolyD hD (idMat 2))
    [⟨4, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin4 : poly.oneValue (charPolyD hM (idMat 2))
    (charPoly hM (idMat 2)) := by decide +kernel
theorem pin5 : poly.oneValue (charPolyD hM (idMat 2))
    (charPoly hM (idMat 2)) :=
  charPolyD_eq hM (idMat 2) (by decide +kernel)

private def hW : Mat :=
  [[⟨2, 1⟩, ⟨3, 1⟩, ⟨5, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩, ⟨7, 1⟩]]

theorem pin6 : ¬ elim.rowsLen (zMat hW (idMat 3)).length (zMat hW (idMat 3))
    ∧ ¬ poly.oneValue (charPolyD hW (idMat 3))
      (charPoly hW (idMat 3)) := by decide +kernel

/-! The factorization reads at the stated root lists. -/

theorem pin7 : chiRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] := by decide +kernel
theorem pin8 : chiRead hM (idMat 2) [(⟨4, 1⟩, 1), (⟨1, 2⟩, 1)] := by decide +kernel

/-! The count identities at the split certificates: the reversal
count against the located roots below the level. -/

theorem pin9 : countRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] 2 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 2⟩, .one ⟨2, 1⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel
theorem pin10 : countRead hM (idMat 2) [(⟨4, 1⟩, 1), (⟨1, 2⟩, 1)] 1 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two u ⟨3, 1⟩ u], 0, rfl⟩
      : Split 2) := by
  decide +kernel

/-! The diagonalizing congruences: the identity at the diagonal
pencil, and `T = [[1,-1],[1,1]]` at the coupled one, the scales on
their upper sides. -/

private def tM : Mat := [[⟨2, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]]
private def tW : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩]]
private def lM : List (BPair × Pos × BPair) :=
  [(⟨4, 1⟩, 1, ⟨3, 1⟩), (⟨1, 2⟩, 1, ⟨3, 1⟩)]

theorem pin11 : diagRead hD (idMat 2) (⟨idMat 2, rfl⟩ : SqMat 2)
    (⟨idMat 2, rfl⟩ : SqMat 2)
    [(⟨2, 1⟩, 1, ⟨2, 1⟩), (⟨4, 1⟩, 1, ⟨2, 1⟩)] := by decide +kernel
private theorem dgM : diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨tW, rfl⟩ : SqMat 2) lM := by decide +kernel

/-! The resultant's kernel read at its arrival: the cross pair at
the shared root of `(z-1)(z-2)` and `(z-1)(z-3)` with the
resultant's equal members, and the Bézout clause at the coprime
complement. -/

private def pShared : Poly := [⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩]
private def qShared : Poly := [⟨4, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩]

theorem pin12 : crossRead pShared qShared [⟨1, 4⟩, ⟨2, 1⟩]
    [⟨3, 1⟩, ⟨1, 2⟩] := by decide +kernel
theorem pin13 : (resultant pShared qShared).oneValue u := by decide +kernel
theorem pin14 : topsUnequal pShared [⟨1, 4⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin15 : poly.oneValue
    (poly.add (poly.mul (bezoutA pShared [⟨1, 4⟩, ⟨2, 1⟩]) pShared)
      (poly.mul (bezoutB pShared [⟨1, 4⟩, ⟨2, 1⟩]) [⟨1, 4⟩, ⟨2, 1⟩]))
    [resultant pShared [⟨1, 4⟩, ⟨2, 1⟩]] := by decide +kernel
theorem pin16 : poly.oneValue
    (poly.add (poly.mul (bezoutA pShared [⟨1, 4⟩, ⟨2, 1⟩]) pShared)
      (poly.mul (bezoutB pShared [⟨1, 4⟩, ⟨2, 1⟩]) [⟨1, 4⟩, ⟨2, 1⟩]))
    [resultant pShared [⟨1, 4⟩, ⟨2, 1⟩]] :=
  bezout_all pShared [⟨1, 4⟩, ⟨2, 1⟩] (by decide +kernel)
theorem pin17 : ¬ (resultant pShared [⟨1, 4⟩, ⟨2, 1⟩]).oneValue u := by
  decide +kernel

/-! The designation whole at the diagonal pencil: the root-three
bracket `[47:16, 49:16]` at width `[1:8]`, the counts at the gap
one, the width joining the endpoints and sitting at the pencil
polynomial's own `δ` — one conjoined read. -/

theorem pin18 : certconstruct.desigWhole hD (idMat 2) 47 16 49 16 1 8 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 32⟩, .one ⟨2, 1⟩], 0,
      rfl⟩ : Split 2)
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 34⟩, .one ⟨1, 2⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel

/-! The unbalanced count with the refusals: the level four's count
two (both roots below), a count at a level on a root refused at the
off-roots clause, a wrong root list refused at the factorization,
a coprime pair refused at the cross read, and an off-adjugate
witness refused at the product reads. -/

theorem pin19 : countRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] 4 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 4⟩, .one ⟨1, 2⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel
theorem pin20 : ¬ countRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] 3 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 3⟩], 1, rfl⟩ : Split 2) := by decide +kernel
theorem pin21 : ¬ chiRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨5, 1⟩, 1)] := by
  decide +kernel
theorem pin22 : ¬ crossRead qShared pShared [⟨1, 4⟩, ⟨2, 1⟩]
    [⟨3, 1⟩, ⟨1, 2⟩] := by decide +kernel
theorem pin23 : ¬ diagRead hD (idMat 2) (⟨idMat 2, rfl⟩ : SqMat 2)
    (⟨idMat 2, rfl⟩ : SqMat 2)
    [(⟨2, 1⟩, 1, ⟨1, 3⟩), (⟨4, 1⟩, 1, ⟨2, 1⟩)] := by decide +kernel
theorem pin24 : ¬ diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨idMat 2, rfl⟩ : SqMat 2) lM := by decide +kernel

/-! The coefficient tier at the coupled instance: the congruence's two
coefficient matrices against the two congruated data — the linear the
second datum's congruence, the constant the first's memberwise swapped
— the diagonal side's two against the scaled root data, and the
eigen-column read at the committed diagonalization: the first root's
column at the cleared relation `1 · (H v) = 3 · (G v)`, the theorem's
own instance beside the same read by kernel decision. -/

theorem pin25 : matOneValue (plin (congrZ tM (zMat hM (idMat 2))))
    (matMul (transposeM tM) (matMul (idMat 2) tM)) := by decide +kernel
theorem pin26 : matOneValue (pconst (congrZ tM (zMat hM (idMat 2))))
    (matSwap (matMul (transposeM tM) (matMul hM tM))) := by decide +kernel
theorem pin27 : matOneValue
    (plin (pdiag (lM.map (fun r =>
      poly.scaleP r.2.2 (linFac r.1 r.2.1)))))
    (diagM (lM.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by decide +kernel
theorem pin28 : matOneValue
    (pconst (pdiag (lM.map (fun r =>
      poly.scaleP r.2.2 (linFac r.1 r.2.1)))))
    (diagM (lM.map (fun r => (r.2.2 * r.1).norm.swap))) := by decide +kernel

theorem pin29 : poly.oneValue
    (vecScale (BPair.ofPos 1) (matVec hM (matVec tM (idRow 2 0))))
    (vecScale ⟨4, 1⟩ (matVec (idMat 2) (matVec tM (idRow 2 0)))) := by decide +kernel
theorem pin30 : poly.oneValue
    (vecScale (BPair.ofPos 1) (matVec hM (matVec tM (idRow 2 0))))
    (vecScale ⟨4, 1⟩ (matVec (idMat 2) (matVec tM (idRow 2 0)))) :=
  eigenColumn hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2) (⟨tW, rfl⟩ : SqMat 2)
    lM 0 ⟨4, 1⟩ ⟨3, 1⟩ 1 dgM (by decide +kernel) rfl

/-! The factorization is the congruence certificate's own read
(`diag_chiRead`): at the committed diagonalization the mapped root
list's `chiRead` arrives through the theorem beside its own kernel
decision, and the moved first root refuses the congruence read and
the factorization read together — the certificate binder's own
refusal, the roots the one datum both reads carry. -/

theorem pin31 : chiRead hM (idMat 2) (lM.map (fun r => (r.1, r.2.1))) := by
  decide +kernel
theorem pin32 : chiRead hM (idMat 2) (lM.map (fun r => (r.1, r.2.1))) :=
  diag_chiRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2) (⟨tW, rfl⟩ : SqMat 2)
    lM dgM
theorem pin33 : ¬ diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨tW, rfl⟩ : SqMat 2)
    [(⟨5, 1⟩, 1, ⟨3, 1⟩), (⟨1, 2⟩, 1, ⟨3, 1⟩)] := by decide +kernel
theorem pin34 : ¬ chiRead hM (idMat 2) [(⟨5, 1⟩, 1), (⟨1, 2⟩, 1)] := by
  decide +kernel

/-! The descent's determinants read the fiber folds: `elim.pdetD`
against `split.pminor` and `elim.ppdetD` against `split.ppminor`,
the theorem routes pinning the two spellings at one object. -/

theorem pin35 : poly.oneValue
    (elim.pdetD [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]])
    (split.pminor [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]]) :=
  elim.pdetD_eq _ (by decide +kernel)

theorem pin36 : poly.ppOneValue
    (elim.ppdetD [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]])
    (split.ppminor [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]]) :=
  elim.ppdetD_eq _ (by decide +kernel)

/-! The congruated pencil's two diagonal reads and the diagonal's
reversal count.  At the committed diagonalization the second datum's
congruence is the diagonal at the scales against the roots' clearings
and the first's is the diagonal at the scales against the roots' first
members, each read by kernel decision beside its theorem route; and a
three-entry diagonal's split — the middle entry at the sum's unit, so
the kernel block enters — reads its lower-side count, the theorem's
value pinned against the constructed split's own. -/

theorem pin37 : matOneValue (matMul (transposeM tM) (matMul (idMat 2) tM))
    (diagM (lM.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by
  decide +kernel
theorem pin38 : matOneValue (matMul (transposeM tM) (matMul (idMat 2) tM))
    (diagM (lM.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) :=
  congr_gram hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2) (⟨tW, rfl⟩ : SqMat 2) lM dgM

theorem pin39 : matOneValue (matMul (transposeM tM) (matMul hM tM))
    (diagM (lM.map (fun r => (r.2.2 * r.1).norm))) := by decide +kernel
theorem pin40 : matOneValue (matMul (transposeM tM) (matMul hM tM))
    (diagM (lM.map (fun r => (r.2.2 * r.1).norm))) :=
  congr_pencil hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2) (⟨tW, rfl⟩ : SqMat 2)
    lM dgM

private def dsC : List BPair := [⟨1, 2⟩, u, ⟨3, 1⟩]

theorem pin41 : revAt (mkSplit 3 (diagM dsC)) = 1 := by decide +kernel
theorem pin42 : dsC.countP (fun d => decide (d < BPair.unit)) = 1 := by
  decide +kernel
theorem pin43 : revAt (mkSplit 3 (diagM dsC))
    = dsC.countP (fun d => decide (d < BPair.unit)) :=
  rev_diagM dsC (mkSplit 3 (diagM dsC))
    (mkSplit_read 3 (diagM dsC) (by decide +kernel) (diagM_sym dsC))

/-! The split binder isolated: a further diagonal's split refuses the
read and parts the count, two lower-side entries against one. -/

private def dsB : List BPair := [⟨1, 2⟩, ⟨1, 2⟩, ⟨3, 1⟩]

theorem pin44 : ¬ splitRead (diagM dsC) (mkSplit 3 (diagM dsB)) := by
  decide +kernel
theorem pin45 : ¬ (revAt (mkSplit 3 (diagM dsB))
    = dsC.countP (fun d => decide (d < BPair.unit))) := by decide +kernel

/-! The diagonal-read binder isolated at the two congruated reads: a
forged scale refuses the read and parts the gram's diagonal, and a
forged root refuses it and parts the pencil's. -/

private def lG : List (BPair × Pos × BPair) :=
  [(⟨4, 1⟩, 1, ⟨2, 1⟩), (⟨1, 2⟩, 1, ⟨3, 1⟩)]
private def lP : List (BPair × Pos × BPair) :=
  [(⟨5, 1⟩, 1, ⟨3, 1⟩), (⟨1, 2⟩, 1, ⟨3, 1⟩)]

theorem pin46 : ¬ diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨tW, rfl⟩ : SqMat 2) lG := by decide +kernel
theorem pin47 : ¬ matOneValue (matMul (transposeM tM) (matMul (idMat 2) tM))
    (diagM (lG.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by
  decide +kernel
theorem pin48 : ¬ diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨tW, rfl⟩ : SqMat 2) lP := by decide +kernel
theorem pin49 : ¬ matOneValue (matMul (transposeM tM) (matMul hM tM))
    (diagM (lP.map (fun r => (r.2.2 * r.1).norm))) := by decide +kernel

/-! The polynomial adjugate's solved witness at the two pencils
`[[t,1],[1,t]]` and `[[t,1,0],[1,t,1],[0,1,t]]`, `def:elim`'s
adjugate identity at the polynomial carrier. -/

private def m2 : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [u, ⟨2, 1⟩]]]
private def m3 : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩], []],
   [[⟨2, 1⟩], [u, ⟨2, 1⟩], [⟨2, 1⟩]],
   [[], [⟨2, 1⟩], [u, ⟨2, 1⟩]]]

theorem pin50 : adjRead m2 := by decide +kernel
theorem pin51 : adjRead m3 := by decide +kernel

/-! The solved witness through its theorem route at the square
frame, both product orders. -/

theorem pin52 : adjRead m2 := adjRead_all m2 (by decide +kernel)

theorem pin53 : split.pmatOneValue (split.pmatMul (padj m2) m2)
    (split.pdiag (List.replicate m2.length (split.pminor m2))) :=
  adjColRead_all m2 (by decide +kernel)

theorem pin54 : split.pmatOneValue (split.pmatMul (padj m3) m3)
    (split.pdiag (List.replicate m3.length (split.pminor m3))) := by
  decide +kernel

/-! The descent's adjugate against the fold's at the value, decided
and read through the theorem's route at the decided square frame. -/

theorem pin55 : split.pmatOneValue (padjD m3) (padj m3) := by decide +kernel
theorem pin56 : split.pmatOneValue (padjD m2) (padj m2) :=
  padjD_eq m2 (by decide +kernel)

/-! The square binder isolated at a ragged frame, and the settled
side's reads at the value's representative — a tail of
equal-membered coefficients moves the representative with both
reads held. -/

private def ragP3 : split.PMat :=
  [[[⟨2, 1⟩], [⟨1, 2⟩], [⟨3, 1⟩]],
   [[⟨1, 3⟩], [⟨5, 1⟩]],
   [[⟨2, 1⟩], [⟨2, 1⟩], [⟨1, 2⟩]]]

theorem pin57 : ¬ split.pmatOneValue (padjD ragP3) (padj ragP3) := by
  decide +kernel

/-- The solved witness at the ragged frames: `ragP3`'s missing entry
sits beyond the walked keys, so the identity reads anyway and the
square binder is a clearance there; at the wide first row the
out-of-range column carries no cofactor and both product orders
refuse, the binder load-bearing. -/
theorem pin58 : adjRead ragP3 := by decide +kernel

theorem pin59 : split.pmatOneValue (split.pmatMul (padj ragP3) ragP3)
    (split.pdiag (List.replicate ragP3.length
      (split.pminor ragP3))) := by decide +kernel

private def ragWide : split.PMat :=
  [[poly.one, poly.one, poly.one], [poly.one]]

theorem pin60 : ¬ adjRead ragWide := by decide +kernel

theorem pin61 : ¬ split.pmatOneValue (split.pmatMul (padj ragWide) ragWide)
    (split.pdiag (List.replicate ragWide.length
      (split.pminor ragWide))) := by decide +kernel

end split
