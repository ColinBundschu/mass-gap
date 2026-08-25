import MassGap.Kernel
/-!
`prop:lap` — the plaquette Laplacian as a group-algebra insertion.
On the presentation's generators the insertion identity reads
`d_f`-cleared, and the action is its solved read: per stated
variable, the within-factor terms at the trace form's own Casimir
`c_f = [r(r+2) : 2 d_f]` (`cfP`), the same-dagger transpositions —
an undaggered pair composing at the places (`swapIdx`, `π ∘ (i j)`)
and a daggered pair at the values (`mapVals`, `(i j) ∘ π`) — the
mixed pairs' contraction `C_rc(i, j)` at the wiring, the closed
case `π(i) = j` reading the loop value `d_f` and the open case the
witness transposition at the place reading `j` (`crcTerm` at
`places.posOf`), and the counting coefficients collected at the
count's pair, one combination per generator
(`lapAct`, `lapComb` the linear extension at `con:states`' generic
extension, `scaleComb` and the concatenation the states' own sum).  The identity instances are
the check module's pins at the word index — `Δ_U tr U = c_f tr U`,
the unit the kernel point at `1 = [1 : d_f] tr(U U†)`,
`Δ_U χ_adj = d_f χ_adj`, and the graded squares
`d_f Δ_U s + 2s = d_f (d_f + 1) s` at `s = (tr U)² + tr U²` with
`d_f Δ_U w + (d_f + 2) w = d_f² w` at
`w = ⟨(tr U)² : tr U²⟩` — all cleared polynomial identities in the
residue, `rem:kernel`'s combination equality their read.
-/

namespace lap
open ground poly places states genericlift

/-- A natural's pair. -/
def natP (n : Nat) : poly.PPair :=
  ([BPair.ofNat n], poly.one)

/-- The trace form's Casimir read, `c_f = [r(r+2) : 2 d_f]`. -/
def cfP : poly.PPair :=
  ([BPair.unit, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩])

/-- The count's pair, `d_f = r + 1`. -/
def dfP : poly.PPair := ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])

/-- The negation's pair. -/
def negP : poly.PPair := ([⟨1, 2⟩], [⟨2, 1⟩])

/-- The composition at the places, `π ∘ (i j)`: the entries at the
two places exchanged. -/
def swapIdx (i j : Nat) (π : List Nat) : List Nat :=
  (π.set i (ground.getAt 0 π j)).set j (ground.getAt 0 π i)

/-- The composition at the values, `(i j) ∘ π`. -/
def mapVals (i j : Nat) (π : List Nat) : List Nat :=
  π.map (fun v => if v == i then j else if v == j then i else v)

/-- The place pairs `i < j` of a position list. -/
def pairsOf (ps : List Nat) : List (Nat × Nat) :=
  (List.range ps.length).flatMap (fun a =>
    (List.range a).map (fun b =>
      (ground.getAt 0 ps b, ground.getAt 0 ps a)))

/-- A state rescaled, the coefficients' product. -/
def scaleComb (x : poly.PPair) (c : states.Comb) :
    states.Comb :=
  c.map (fun e => (e.1, poly.pMul x e.2))

/-- The mixed pair's contraction `C_rc(i, j)`: the closed case
`π(i) = j` the loop value, the open case the witness transposition
at the place reading `j`. -/
def crcTerm (π : List Nat) (i j : Nat) :
    List Nat × poly.PPair :=
  if ground.getAt 0 π i == j then (π, dfP)
  else (swapIdx i (places.posOf j π) π, poly.pOne)

/-- The Laplacian's action at a generator, the insertion display's
solved read at the stated variable. -/
def lapAct (F : states.FList) (W : Bool) (π : List Nat) :
    states.Comb :=
  let und := wg.posIf F (W, false)
  let dag := wg.posIf F (W, true)
  let uu := pairsOf und
  let dd := pairsOf dag
  let mixed := und.flatMap (fun i => dag.map (fun j => (i, j)))
  [(π, poly.pMul cfP (natP (und.length + dag.length))),
   (π, ([BPair.ofNat mixed.length
          + (BPair.ofNat (uu.length + dd.length)).swap],
        [⟨2, 1⟩, ⟨2, 1⟩]))]
  ++ uu.map (fun p => (swapIdx p.1 p.2 π, poly.pOne))
  ++ dd.map (fun p => (mapVals p.1 p.2 π, poly.pOne))
  ++ mixed.map (fun p =>
      let t := crcTerm π p.1 p.2
      (t.1, poly.pMul negP t.2))

/-- The action's linear extension over a state, the generic
extension's instance at the plaquette insertion. -/
def lapComb (F : states.FList) (W : Bool) (c : states.Comb) :
    states.Comb :=
  states.extComb (lapAct F W) c

end lap
