import MassGap.Fusion
/-!
`prop:fusionfinite` — fusion rows lie in content balls, read at the
interface: `rowBall`, every nonunit member of the fusion row at its
cleared Casimir at or below the Cartan product's, the unit member
inside every ball outright — the dominance growth along a row
`con:fusion` names.  A product pool's attained maximum
is the pool's own window content (`leastwindow.windowContent` at
`def:algebra`'s row), the multiplication window bound's read at the
changed edge, so the bound enters as the index-direct
reads with
the ball comparison the interface law; the check module pins the
square's `θ`-loop pool at the summed per-link ball with the maximum
attained exactly there.
-/

namespace fusionfinite
open ground fusion

/-- The content ball's row read at the interface: every nonunit
member of the fusion row reads its cleared Casimir at or below the
Cartan product's, `def:c2hat`'s pair at the one shared second
member. -/
def rowBall {L : Type} (F : Data L) (a b : L) : Prop :=
  ((F.row a b).all (fun c =>
    F.eqL c F.unit || decide (F.c2N c ≤ F.c2N (F.add a b)))) = true

instance instFusionfinite1 {L : Type} (F : Data L) (a b : L) :
    Decidable (rowBall F a b) :=
  inferInstanceAs (Decidable (_ = _))

end fusionfinite
