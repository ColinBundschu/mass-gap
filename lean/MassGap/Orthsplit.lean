import MassGap.Elim
/-!
`lem:orthsplit` — a transpose-closed action splits orthogonally:
the orthogonal complement of an invariant subspace is invariant.
The pairing walks across the transpose partner
(`perp_invariant`'s adjoint hypothesis, the units' instance
`units.matUnit_transpose_read`) to the source group's span, and
`elim.perp_span` closes the fold there — the moved content's group
the pairing's rows, the source content's group the transposed
image's own.  The tex's invariant subspace is one; at the graded
carrier it reads as the two content groups, and the diagonal
instance is the two lists coinciding.  The exhaustion tier
(`lem:blockcount`(i)) is the arriving consumer, the residual
carrier's descent at the maximal-content top.
-/

namespace orthsplit
open ground

/-- The complement's invariance read: at an operator whose
transpose partner sends the moved content's group into the source
content's group's span, a vector perpendicular to every source row
has its image perpendicular to every moved row — the pairing walks
across the transpose partner to the source group's span, and
`elim.perp_span` closes the fold there. -/
theorem perp_invariant (n : Nat) (T Tt : elim.Mat)
    (Us Ut : elim.Mat) (u' : List BPair)
    (hUs : elim.rowsLen n Us) (hu'n : u'.length = n)
    (hadj : ∀ k, k < Ut.length →
      (elim.dotP (elim.matVec T u')
        (ground.getAt [] Ut k)).oneValue
      (elim.dotP u' (elim.matVec Tt (ground.getAt [] Ut k))))
    (hinv : ∀ k, k < Ut.length →
      elim.spanRel n Us (elim.matVec Tt (ground.getAt [] Ut k)))
    (hperp : ∀ k, k < Us.length →
      (elim.dotP u' (ground.getAt [] Us k)).oneValue BPair.unit) :
    ∀ k, k < Ut.length →
      (elim.dotP (elim.matVec T u')
        (ground.getAt [] Ut k)).oneValue BPair.unit := by
  intro k hk
  exact BPair.oneValue_trans (hadj k hk)
    (elim.perp_span n Us u'
      (elim.matVec Tt (ground.getAt [] Ut k)) hUs hu'n hperp
      (hinv k hk))

end orthsplit
