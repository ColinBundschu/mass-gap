import MassGap.Levelequiv
/-!
`cor:momentdivisor` — two moments against a divisor: on a window
the probe family's requirement reads the compressed form pair's
positive-semidefinite split, one reversal count over the located
stage, at the moment spelling `Ẽ²` against `Ẽ`.  Right to left the
split's positivity transports to every sector vector
(`window_intro`, `thm:levelequiv`'s spectrum side at
`thm:momentform`'s requirement), left to right the count's own
witness comes off the elimination (`window_elim`,
`thm:certconstruct`(2)); both are `thm:levelequiv`'s pair applied
at the square, the moments' packaging the only step between them.
The two directions' instances are the check module's paired pins.
-/

namespace momentdivisor
open ground elim inertia

/-- The window's spectrum side: at the compressed pair's split
read with an unoccupied reversal count the requirement holds at
every probe of the window, the moments' comparison the
theorem's own. -/
theorem window_intro {n : Nat} (Et : SqMat n) (gn gd : Pos)
    (sp : Split n)
    (h : splitRead (siteDatum
        (matScale gd (matMul Et.val Et.val))
        (matScale gn Et.val)) sp)
    (hp : psdAt sp) :
    ∀ y : Vec n, momentform.reqRead Et y gn gd :=
  levelequiv.probe_intro ⟨matMul Et.val Et.val, sqSquare Et.shape⟩ Et gn gd
    sp ⟨sqSquare Et.shape, Et.shape, h, hp⟩

/-- The window's failing side: at an occupied reversal count the
elimination exhibits a probe whose moments refuse the
requirement, the count's own witness at the moment spelling. -/
theorem window_elim {n : Nat} (Et : SqMat n) (gn gd : Pos)
    (sp : Split n)
    (h : splitRead (siteDatum
        (matScale gd (matMul Et.val Et.val))
        (matScale gn Et.val)) sp)
    (hocc : 1 ≤ revAt sp) :
    ∃ y : Vec n, ¬ momentform.reqRead Et y gn gd :=
  levelequiv.probe_elim ⟨matMul Et.val Et.val, sqSquare Et.shape⟩ Et gn gd
    sp h hocc

end momentdivisor
