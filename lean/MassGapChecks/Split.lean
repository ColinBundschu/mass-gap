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
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly elim inertia split

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]
private def hM : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩]]

/-! The pencil polynomials: `(x-1)(x-3)` at the diagonal and
`(x-3)(x+1)` at the coupled datum. -/

example : poly.oneValue (charPoly hD (idMat 2))
    [⟨4, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (charPoly hM (idMat 2))
    [⟨1, 4⟩, ⟨1, 3⟩, ⟨2, 1⟩] := by decide +kernel

/-! The factorization reads at the stated root lists. -/

example : chiRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] := by decide +kernel
example : chiRead hM (idMat 2) [(⟨4, 1⟩, 1), (⟨1, 2⟩, 1)] := by decide +kernel

/-! The count identities at the split certificates: the reversal
count against the located roots below the level. -/

example : countRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] 2 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 2⟩, .one ⟨2, 1⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel
example : countRead hM (idMat 2) [(⟨4, 1⟩, 1), (⟨1, 2⟩, 1)] 1 1
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

example : diagRead hD (idMat 2) (⟨idMat 2, rfl⟩ : SqMat 2)
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

example : crossRead pShared qShared [⟨1, 4⟩, ⟨2, 1⟩]
    [⟨3, 1⟩, ⟨1, 2⟩] := by decide +kernel
example : (resultant pShared qShared).oneValue u := by decide +kernel
example : topsUnequal pShared [⟨1, 4⟩, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue
    (poly.add (poly.mul (bezoutA pShared [⟨1, 4⟩, ⟨2, 1⟩]) pShared)
      (poly.mul (bezoutB pShared [⟨1, 4⟩, ⟨2, 1⟩]) [⟨1, 4⟩, ⟨2, 1⟩]))
    [resultant pShared [⟨1, 4⟩, ⟨2, 1⟩]] := by decide +kernel
example : poly.oneValue
    (poly.add (poly.mul (bezoutA pShared [⟨1, 4⟩, ⟨2, 1⟩]) pShared)
      (poly.mul (bezoutB pShared [⟨1, 4⟩, ⟨2, 1⟩]) [⟨1, 4⟩, ⟨2, 1⟩]))
    [resultant pShared [⟨1, 4⟩, ⟨2, 1⟩]] :=
  bezout_all pShared [⟨1, 4⟩, ⟨2, 1⟩] (by decide +kernel)
example : ¬ (resultant pShared [⟨1, 4⟩, ⟨2, 1⟩]).oneValue u := by
  decide +kernel

/-! The designation whole at the diagonal pencil: the root-three
bracket `[47:16, 49:16]` at width `[1:8]`, the counts at the gap
one, the width joining the endpoints and sitting at the pencil
polynomial's own `δ` — one conjoined read. -/

example : certconstruct.desigWhole hD (idMat 2) 47 16 49 16 1 8 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 32⟩, .one ⟨2, 1⟩], 0,
      rfl⟩ : Split 2)
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 34⟩, .one ⟨1, 2⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel

/-! The unbalanced count with the refusals: the level four's count
two (both roots below), a count at a level on a root refused at the
off-roots clause, a wrong root list refused at the factorization,
a coprime pair refused at the cross read, and an off-adjugate
witness refused at the product reads. -/

example : countRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] 4 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 4⟩, .one ⟨1, 2⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel
example : ¬ countRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨4, 1⟩, 1)] 3 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 3⟩], 1, rfl⟩ : Split 2) := by decide +kernel
example : ¬ chiRead hD (idMat 2) [(⟨2, 1⟩, 1), (⟨5, 1⟩, 1)] := by
  decide +kernel
example : ¬ crossRead qShared pShared [⟨1, 4⟩, ⟨2, 1⟩]
    [⟨3, 1⟩, ⟨1, 2⟩] := by decide +kernel
example : ¬ diagRead hD (idMat 2) (⟨idMat 2, rfl⟩ : SqMat 2)
    (⟨idMat 2, rfl⟩ : SqMat 2)
    [(⟨2, 1⟩, 1, ⟨1, 3⟩), (⟨4, 1⟩, 1, ⟨2, 1⟩)] := by decide +kernel
example : ¬ diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨idMat 2, rfl⟩ : SqMat 2) lM := by decide +kernel

/-! The coefficient tier at the coupled instance: the congruence's two
coefficient matrices against the two congruated data — the linear the
second datum's congruence, the constant the first's memberwise swapped
— the diagonal side's two against the scaled root data, and the
eigen-column read at the committed diagonalization: the first root's
column at the cleared relation `1 · (H v) = 3 · (G v)`, the theorem's
own instance beside the same read by kernel decision. -/

example : matOneValue (plin (congrZ tM (zMat hM (idMat 2))))
    (matMul (transposeM tM) (matMul (idMat 2) tM)) := by decide +kernel
example : matOneValue (pconst (congrZ tM (zMat hM (idMat 2))))
    (matSwap (matMul (transposeM tM) (matMul hM tM))) := by decide +kernel
example : matOneValue
    (plin (pdiag (lM.map (fun r =>
      poly.scaleP r.2.2 (linFac r.1 r.2.1)))))
    (diagM (lM.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by decide +kernel
example : matOneValue
    (pconst (pdiag (lM.map (fun r =>
      poly.scaleP r.2.2 (linFac r.1 r.2.1)))))
    (diagM (lM.map (fun r => (r.2.2 * r.1).norm.swap))) := by decide +kernel

example : poly.oneValue
    (vecScale (BPair.ofPos 1) (matVec hM (matVec tM (idRow 2 0))))
    (vecScale ⟨4, 1⟩ (matVec (idMat 2) (matVec tM (idRow 2 0)))) := by decide +kernel
example : poly.oneValue
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

example : chiRead hM (idMat 2) (lM.map (fun r => (r.1, r.2.1))) := by
  decide +kernel
example : chiRead hM (idMat 2) (lM.map (fun r => (r.1, r.2.1))) :=
  diag_chiRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2) (⟨tW, rfl⟩ : SqMat 2)
    lM dgM
example : ¬ diagRead hM (idMat 2) (⟨tM, rfl⟩ : SqMat 2)
    (⟨tW, rfl⟩ : SqMat 2)
    [(⟨5, 1⟩, 1, ⟨3, 1⟩), (⟨1, 2⟩, 1, ⟨3, 1⟩)] := by decide +kernel
example : ¬ chiRead hM (idMat 2) [(⟨5, 1⟩, 1), (⟨1, 2⟩, 1)] := by
  decide +kernel

/-! The descent's determinants read the fiber folds: `elim.pdetD`
against `split.pminor` and `elim.ppdetD` against `split.ppminor`,
the theorem routes pinning the two spellings at one object. -/

example : poly.oneValue
    (elim.pdetD [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]])
    (split.pminor [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]]) :=
  elim.pdetD_eq _ (by decide +kernel)

example : poly.ppOneValue
    (elim.ppdetD [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]])
    (split.ppminor [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]]) :=
  elim.ppdetD_eq _ (by decide +kernel)
