import MassGap.Gradingrows
import MassGapChecks.Grading
import MassGapChecks.Carrier
/-!
The second check module for `lem:grading`, the rows at the window's
entries: the far binder's refusal at the plaquette chain of nine
squares, the fundamental loop's row at the adjacent plaquette
holding a target off the far target, with the vertex neighborhood
read at the adjacent and the four-apart plaquettes; the stencil reads
at the square window, the fundamental loop a target on its own row
with the reads holding, refused at a configuration with a label off
the row, that configuration off the row; the loop labels and the
entry read at the square window's two loops with the loop clause
through `entryAt_loop`; the border row at the four-apart plaquette
through `borderRow` at its binders decided one theorem each, the
kernel twins the first module's (`pin134`, `pin137`); the changed
edge at the square window's diagonal entry through `entryShape`; the
content read at the square window through `stencilContent` at the
row's ball; and the tower display at two and three letters by kernel,
through `towerEntry` at three, and the degree binder's refusal at the
diagonal.

The binder classification.  `farRow`'s `hfar` is load-bearing with
its committed refusal (`pin147` at the adjacent plaquette, `pin148`
the read at both plaquettes); `hw`, `hlen` and `hun` are frame
records, `con:lattice`'s well-formed region and `def:carrier`'s
configuration at one reduced spelling per label, and `hrow` is the
interface's unit row law (`con:fusion`'s count laws), discharged at
the label calculus by `unitRowLaw_dataA`.  `borderRow`'s
`hoff` is load-bearing with its refusal the far row's own, and its
further binders are `components_border`'s, classified in the first
module.  `stencilContent`'s `hball` is the interface's row ball
(`prop:fusionfinite`), decided at the label calculus.  `entryShape`'s
`hsup` is `pairpencil.termSupport`, pinned with its refusals in
Pairpencil's check module, and `hM` its own read.  `towerEntry`'s
`hdeg` is load-bearing with its committed refusal (`pin159`, the
diagonal at the unmatched degree with every co-binder standing),
`hd`, `hld` and `hcd` are the frame records `deepRow` classifies,
and `hdeep` is `deepRow`'s with its refusals in the first module.
-/

namespace grading
set_option maxHeartbeats 4000000

open ground lattice fusion elim

private def R9 : Region := fiberdec.chainRegion 9
private def lp0 : List places.Shape := fiberdec.loopAt 9 0
private def plaqOf (i : Nat) : List (Nat × Bool) := getAt [] R9.plaqs i
private def sqLoop1 : List places.Shape := [[1, 0], [1, 0], [1, 0], [1, 0]]
private def sqOff : List places.Shape := [[2, 0], [1, 0], [1, 0], [1, 0]]
private def gSq : Mat := elim.idMat 3
private def mSq : Mat := pairpencil.loopMag (dataA 2) [[1, 0], adjchar.theta 2]

theorem pin147 : ¬ ((algebra.plaqRow (dataA 3) R9 (plaqOf 1) lp0).all
    (fun b => decide (b = stableentries.farConf (dataA 3) R9 lp0 (plaqOf 1)))) = true := by
  decide +kernel
theorem pin148 : stableentries.nearPlaq (dataA 3) R9 lp0 (plaqOf 1) = true
    ∧ stableentries.nearPlaq (dataA 3) R9 lp0 (plaqOf 4) = false := by decide +kernel
theorem pin149 : stencilAt (dataA 2) square sqPlaq sqLoop1 sqLoop1 := by decide +kernel
theorem pin150 : ¬ stencilAt (dataA 2) square sqPlaq sqLoop1 sqOff := by decide +kernel
theorem pin151 : 0 < countOf sqLoop1 (algebra.plaqRow (dataA 2) square sqPlaq sqLoop1)
    ∧ countOf sqOff (algebra.plaqRow (dataA 2) square sqPlaq sqLoop1) = 0 := by decide +kernel
theorem pin152 : pairpencil.loopLabel (dataA 2) square sqPlaq
      (pairpencil.posConf (dataA 2) square carrier.sqIx2 1) = some [1, 0]
    ∧ pairpencil.loopLabel (dataA 2) square sqPlaq
      (pairpencil.posConf (dataA 2) square carrier.sqIx2 2) = some [2, 0]
    ∧ pairpencil.entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqPlaq 1 2 = true
    ∧ pairpencil.entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqPlaq 2 2 = true := by
  decide +kernel
theorem pin153 : (getAt BPair.unit (getAt [] mSq 2) 2).oneValue
    (BPair.ofPos 1 * BPair.ofNat ((dataA 2).count (adjchar.theta 2) [2, 0] [2, 0])) :=
  pairpencil.entryAt_loop (dataA 2) square carrier.sqIx2 1 gSq mSq sqPlaq 2 2 [2, 0] [2, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The border row through the theorem at the four-apart plaquette,
its binders one theorem each in the theorem's own order. -/

private theorem chainWell : wellRead R9 := by decide +kernel
private theorem chainTheta : (dataA 3).eqL (dataA 3).theta (dataA 3).unit = false := by
  decide +kernel
private theorem chainRow : unitRowLaw (dataA 3) (dataA 3).theta :=
  unitRowLaw_dataA 3 (adjchar.theta 3) (adjchar.length_theta 3) (by decide)
private theorem chainLen : lp0.length = R9.links := by decide +kernel
private theorem chainUnit : oneUnit (dataA 3) lp0 := by decide +kernel
private theorem chainMem : plaqOf 4 ∈ R9.plaqs := mem_getAt [] R9.plaqs 4 (by decide +kernel)
private theorem chainTarget : 0 < countOf (stableentries.farConf (dataA 3) R9 lp0 (plaqOf 4))
    (algebra.plaqRow (dataA 3) R9 (plaqOf 4) lp0) := by decide +kernel
theorem pin154 : (components (dataA 3) R9 (stableentries.farConf (dataA 3) R9 lp0 (plaqOf 4))).filter
      (fun c => c.any (fun x => !((dataA 3).eqL (getAt (dataA 3).unit lp0 x) (dataA 3).unit)))
    = components (dataA 3) R9 lp0
    ∧ (components (dataA 3) R9 (stableentries.farConf (dataA 3) R9 lp0 (plaqOf 4))).filter
      (fun c => !(c.any (fun x => !((dataA 3).eqL (getAt (dataA 3).unit lp0 x) (dataA 3).unit))))
    = [(List.range R9.links).filter (fun l => (plaqOf 4).any (fun e => e.1 == l))] :=
  (borderRow (dataA 3) R9 chainWell pin133 chainTheta chainRow lp0 chainLen chainUnit
    (plaqOf 4) chainMem pin95 _ chainTarget).2

/-! The changed edge at the square window's diagonal entry: the
fundamental loop's term entry against itself sits off the sum's
unit, so the position pair meets across the changed edge. -/

theorem pin155 : (∃ b, 0 < countOf b (algebra.plaqRow (dataA 2) square sqPlaq
        (pairpencil.posConf (dataA 2) square carrier.sqIx2 1))
      ∧ carrier.eqConf (dataA 2) (pairpencil.posConf (dataA 2) square carrier.sqIx2 1) b = true)
    ∨ (∃ b, 0 < countOf b (algebra.plaqRow (dataA 2) square sqPlaq
        (pairpencil.posConf (dataA 2) square carrier.sqIx2 1))
      ∧ carrier.eqConf (dataA 2) (pairpencil.posConf (dataA 2) square carrier.sqIx2 1) b = true) :=
  entryShape (dataA 2) square 3 carrier.sqIx2 sqPlaq mSq (by decide +kernel) 1 1
    (by decide) (by decide) (by decide +kernel)

/-! The content read at the square window: the row's ball at every
link of the fundamental loop, and the loop's own label on the
boundary at or below the Cartan product's Casimir. -/

private theorem sqBall : ∀ l, l < square.links →
    fusionfinite.rowBall (dataA 2) (getAt (dataA 2).unit sqLoop1 l) (dataA 2).theta :=
  fun l hl => of_decide_eq_true (all_range_read square.links
    (by decide +kernel : (List.range square.links).all (fun l =>
      decide (fusionfinite.rowBall (dataA 2) (getAt (dataA 2).unit sqLoop1 l) (dataA 2).theta))
      = true) l hl)
theorem pin156 : ((sqPlaq.any (fun e => e.1 == 0)) = true →
      (dataA 2).eqL (getAt (dataA 2).unit sqLoop1 0) (dataA 2).unit = true
        ∨ (dataA 2).c2N (getAt (dataA 2).unit sqLoop1 0)
          ≤ (dataA 2).c2N ((dataA 2).add (getAt (dataA 2).unit sqLoop1 0) (dataA 2).theta))
    ∧ ((sqPlaq.all (fun e => e.1 != 0)) = true →
      getAt (dataA 2).unit sqLoop1 0 = getAt (dataA 2).unit sqLoop1 0) :=
  stencilContent (dataA 2) square sqPlaq sqLoop1 sqLoop1 pin151.1 sqBall 0 (by decide)

/-! The tower display at the label calculus: by kernel at two and
three letters, through `towerEntry` at three, and the degree
binder's refusal at the diagonal, the count two against the read
at the sum's unit with every co-binder standing. -/

theorem pin157 : (dataA 2).count (adjchar.theta 2) [2, 0] [4, 0] = rowRead 2 [2, 0] [4, 0]
    ∧ (dataA 3).count (adjchar.theta 3) [2, 2, 0] [3, 3, 0] = rowRead 3 [2, 2, 0] [3, 3, 0] := by
  decide +kernel
theorem pin158 : (dataA 3).count (adjchar.theta 3) [2, 2, 0] [3, 3, 0] = rowRead 3 [2, 2, 0] [3, 3, 0] :=
  towerEntry 3 (by decide) [2, 2, 0] [3, 3, 0] rfl rfl (by decide +kernel) (by decide +kernel)
theorem pin159 : ¬ ((dataA 3).count (adjchar.theta 3) [2, 2, 0] [2, 2, 0]
      = rowRead 3 [2, 2, 0] [2, 2, 0])
    ∧ ¬ collarAt [2, 2, 0]
    ∧ ¬ (places.degree (adjchar.theta 3) + places.degree [2, 2, 0] = places.degree [2, 2, 0]) := by
  decide +kernel

end grading
