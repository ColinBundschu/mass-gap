import MassGap.Lap
/-!
`prop:link` — the shared-link Casimir as the joint insertion.
`Δ_L` is the simultaneous right translation's read: the insertion
identity is `prop:lap`'s at the sides exchanged — the column index
for an undaggered factor and the row for a daggered — with all
factors of both variables participating, and a factor pair joins
the display at its dagger reads: a matched pair reads its
transposition term, an undaggered pair at the values and a
daggered at the places (the exchange of `prop:lap`'s sides), and
a mixed pair its contraction at the exchanged wiring, the closed
case `π(j) = i` (`linkAct` at `lap.crcTerm`'s exchanged
arguments, `linkComb` the linear extension at `con:states`' generic
extension).  The site unitary's
conjugation is absorbed on the conjugation-invariant fiber, the
absorbed form the read here.  The identity instances are the
check module's pins at the word index — `Δ_L tr U = c_f tr U`,
`Δ_L χ_adj(U) = d_f χ_adj(U)`, the cross-variable graded reads
`d_f Δ_L s + 2s = d_f (d_f + 1) s` at `s = tr U tr V + tr(UV)`
with `d_f Δ_L w + (d_f + 2) w = d_f² w` at
`w = ⟨tr U tr V : tr(UV)⟩`, and the module energy
`E χ_adj = 4 d_f χ_adj` at the two-plaquette weights
`E = 3 Δ_U + Δ_L + 3 Δ_V` — all cleared polynomial identities in
the residue, `rem:kernel`'s combination equality their read.
-/

namespace link
open ground poly places states genericlift

/-- The joint insertion's action at a generator: `prop:lap`'s
display at the sides exchanged, all factors of both variables
participating. -/
def linkAct (F : states.FList) (π : List Nat) : states.Comb :=
  let und := wg.posIf F (0, false) ++ wg.posIf F (1, false)
  let dag := wg.posIf F (0, true) ++ wg.posIf F (1, true)
  let uu := lap.pairsOf und
  let dd := lap.pairsOf dag
  let mixed := und.flatMap (fun i => dag.map (fun j => (i, j)))
  [(π, poly.pMul lap.cfP (lap.natP (und.length + dag.length))),
   (π, ([BPair.ofNat mixed.length
          + (BPair.ofNat (uu.length + dd.length)).swap],
        [⟨2, 1⟩, ⟨2, 1⟩]))]
  ++ uu.map (fun p => (lap.mapVals p.1 p.2 π, poly.pOne))
  ++ dd.map (fun p => (lap.swapIdx p.1 p.2 π, poly.pOne))
  ++ mixed.map (fun p =>
      let t := lap.crcTerm π p.2 p.1
      (t.1, poly.pMul lap.negP t.2))

/-- The action's linear extension over a state, the generic
extension's instance at the joint insertion. -/
def linkComb (F : states.FList) (c : states.Comb) : states.Comb :=
  states.extComb (linkAct F) c

end link
