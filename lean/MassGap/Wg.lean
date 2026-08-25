import MassGap.States
import MassGap.Serpairing
/-!
`prop:wg` — the pairing in the permutation presentation.  The
conjugation flips daggers and transposes wirings, the transpose the
inverse permutation (`conjF` at `places.invPerm`).  The invariant
span's Gram is the cycle count, `𝖦_{αβ} = d_f^{#cycles(α βᵀ)}`, a
polynomial matrix in the residue (`gramWg` at `dfPow`,
`lem:mixedinv`'s object at its recorded consumer), the place
permutations `con:places`' enumeration at the unit content
(`places.perms`); the Weingarten value is the adjugate column against
the determinant, `𝖦 w = e_id` the solved witness's whole
verification (`wgPair` at `lem:genericlift`'s adjugate).  The
evaluation of a generator is the contraction sum: per variable at
matched dagger counts, over the permutation pairs `(σ, τ)`, the
`δ`-wirings close the chains into loops — the wiring's matching
against the `σ, τ`-matchings at the index slots, `σ` the undaggered
rows against the daggered columns and `τ` the exchange (a daggered
factor's conjugate row is its own column), the loop count the
alternating cycles' half count (`evalPhi`, `matchIn`,
the loop fold `places.cyclesOf`'s) — each loop a factor `d_f`, the
sum one numerator fold over the one shared determinant — the
adjugate and determinant hoisted once per evaluation, the
factorial route's recorded headroom the next tier's rework site —
and a mismatched dagger count reads the sum's unit.  The pairing
of two states on their factor lists is `Eval(Φ̄_A Φ_B)`, the
conjugated key against the second at the concatenated site
(`pairPhi`, `pairFull` the combinations' bilinear fold).  Every
output reads at one of the two tags: the symbolic polynomial pair
at its clearance radius, the factor count
(`lem:genericlift`(iv)'s fold), or the direct per-residue read at
or below it; the mixed-power derivation — the invariants the
permutation span at `k ≤ d_f`, the projection the span's Gram
projection — sits at `lem:mixedinv` with the span's independence,
the batteries' fusion-read instances the scheme's own pins
(`prop:repring`'s displays), the `S₄` closed form the emitted
gate's; and the `B`, `C` and `D` members' presentation runs at
the defining factors' pair partitions with the member Gram
(`lem:serpairing`'s): per variable at an even factor count — an
odd count reads the sum's unit — the contraction sum over the
partition pairs at the member adjugate against its determinant,
the wirings closing the dual-pair and form edges into loops on
the composite graph, the bonds with a daggered factor's two
twist nodes, each loop one value — the dimension `r + 3` at `B`
and `D`, one engine at the shared Gram and loop value
(`evalPhiBD`), and the doubled rank `2r` at `C` at the loop's
parity, half the edge count joined to the dual-pair edges read
forward and the form edges read against (`evalPhiC`) — and the
pairing mirrors at the engine argument (`pairPhiSer`,
`pairFullSer` the combinations' bilinear fold).
-/

namespace wg
open ground poly elim places states genericlift

/-- The fundamental count's power, a polynomial in the residue at
`d_f = r + 1`. -/
def dfPow (c : Nat) : Poly := poly.powOf [⟨2, 1⟩, ⟨2, 1⟩] c

/-- The span's Gram: the cycle count `d_f^{#cycles(α βᵀ)}`
entrywise, a polynomial matrix in the residue. -/
def gramWg (k : Nat) : split.PMat :=
  (places.perms k).map (fun a => (places.perms k).map (fun b =>
    dfPow (places.cyclesOf
      (places.expo a (places.invPerm k b))).length))

/-- The Weingarten pair at a class member: the adjugate column
against the determinant, `𝖦 w = e_id` the solved witness. -/
def wgPair (k : Nat) (γ : List Nat) : poly.PPair :=
  (ground.getAt []
    (ground.getAt [] (genericlift.padj (gramWg k))
      (places.idxOf γ (places.perms k)))
    (places.idxOf (List.range k) (places.perms k)),
   split.pminor (gramWg k))

/-- The factors at one letter, the positions' filter. -/
def posIf (G : states.FList) (f : states.Factor) : List Nat :=
  (List.range G.length).filter
    (fun i => ground.getAt (false, false) G i == f)

private def matchIn (m2 : List Nat) (ps qs σ : List Nat)
    (offP offQ : Nat) : List Nat :=
  (List.range ps.length).foldl (fun acc s =>
    let a := 2 * ground.getAt 0 ps s + offP
    let b := 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ
    (acc.set a b).set b a) m2

/-- The evaluation of a generator, the contraction sum: per
variable at matched dagger counts, over the permutation pairs, the
`δ`-wirings close into loops — the wiring's matching at the row
and column slots against the `σ, τ`-matchings, the loop count the
alternating cycles' half count — each loop a factor `d_f`. -/
def evalPhi (G : states.FList) (π : List Nat) : poly.PPair :=
  let m := G.length
  let uU := posIf G (false, false)
  let dU := posIf G (false, true)
  let uV := posIf G (true, false)
  let dV := posIf G (true, true)
  if uU.length == dU.length && uV.length == dV.length then
    let permsU := places.perms uU.length
    let permsV := places.perms uV.length
    let adjU := genericlift.padj (gramWg uU.length)
    let detU := split.pminor (gramWg uU.length)
    let adjV := genericlift.padj (gramWg uV.length)
    let detV := split.pminor (gramWg uV.length)
    let idU := places.idxOf (List.range uU.length) permsU
    let idV := places.idxOf (List.range uV.length) permsV
    let m1 := (List.range m).foldl (fun acc i =>
      let a := 2 * i
      let b := 2 * ground.getAt 0 π i + 1
      (acc.set a b).set b a) (List.replicate (2 * m) 0)
    let num := permsU.foldl (fun acc σU =>
      permsU.foldl (fun acc τU =>
        permsV.foldl (fun acc σV =>
          permsV.foldl (fun acc τV =>
            let m2 := matchIn (matchIn (matchIn (matchIn
              (List.replicate (2 * m) 0) uU dU σU 0 1) uU dU τU 1 0)
              uV dV σV 0 1) uV dV τV 1 0
            let comp := (List.range (2 * m)).map (fun i =>
              ground.getAt 0 m2 (ground.getAt 0 m1 i))
            let loops := (places.cyclesOf comp).length / 2
            let nU := ground.getAt [] (ground.getAt [] adjU
              (places.idxOf (places.expo σU
                (places.invPerm uU.length τU)) permsU)) idU
            let nV := ground.getAt [] (ground.getAt [] adjV
              (places.idxOf (places.expo σV
                (places.invPerm uV.length τV)) permsV)) idV
            poly.add acc (poly.mul nU (poly.mul nV (dfPow loops))))
            acc) acc) acc) ([] : Poly)
    (num, poly.mul detU detV)
  else poly.pZero

/-- The conjugation: the daggers flip. -/
def conjF (F : states.FList) : states.FList :=
  F.map (fun f => (f.1, !f.2))

/-- The pairing of two generators at their factor lists,
`Eval(Φ̄_A Φ_B)`: the conjugated key — the daggers flipped, the
wiring transposed — against the second at the concatenated
site. -/
def pairPhi (Fa Fb : states.FList) (πa πb : List Nat) :
    poly.PPair :=
  evalPhi (conjF Fa ++ Fb)
    (places.invPerm Fa.length πa ++ states.shiftW Fa.length πb)

/-- The pairing of two states at their factor lists, the
combinations' bilinear fold at the certified reduction:
`lem:genericlift`'s `pAddR` accumulates, so the representative
moves to the descent's own at every term and the fold's value is
the displayed sum's, `pReduce_read` the bridge. -/
def pairFull (Fa Fb : states.FList) (a b : states.Comb) :
    poly.PPair :=
  a.foldl (fun acc ea => b.foldl (fun acc2 eb =>
    genericlift.pAddR acc2 (poly.pMul
      (poly.pMul ea.2 eb.2) (pairPhi Fa Fb ea.1 eb.1))) acc)
    poly.pZero

/-! The `B`, `C` and `D` member tier: the presentation at the
defining factors' pair partitions with the member Gram
(`lem:serpairing`), `prop:wg`'s member display. -/

/-- The factors at one variable across both dagger reads, the
member presentation's slot list — the `u`-th factor in list order
the local slot `u`. -/
private def posVar (G : states.FList) (v : Bool) : List Nat :=
  (List.range G.length).filter
    (fun i => (ground.getAt (false, false) G i).1 == v)

/-- A daggered factor's `a`-node on the composite graph: the site
length past two nodes per earlier daggered factor, the `b`-node
its successor; the bonds the nodes below the site length. -/
private def aNode (m : Nat) (dag : List Bool) (j : Nat) : Nat :=
  m + 2 * ground.countOf true (dag.take j)

/-- A factor's row end: the `b`-node at a daggered factor — the
slots exchanged at the form's twist — else its own bond. -/
private def rvar (m : Nat) (dag : List Bool) (j : Nat) : Nat :=
  if ground.getAt false dag j then aNode m dag j + 1 else j

/-- A factor's column end: the `a`-node at a daggered factor, else
the bond of the factor wired onto it. -/
private def svar (m : Nat) (dag : List Bool) (invw : List Nat)
    (j : Nat) : Nat :=
  if ground.getAt false dag j then aNode m dag j
  else ground.getAt 0 invw j

/-- A partition's dual-pair edges at an end read, the local slots
at their global factor indices. -/
private def pairEdges (gs : List Nat) (f : Nat → Nat)
    (pp : List (Nat × Nat)) : List (Nat × Nat × Nat) :=
  pp.map (fun pr =>
    (f (ground.getAt 0 gs pr.1), f (ground.getAt 0 gs pr.2), 0))

/-- A daggered factor's two twist edges in factor order: the bond
onto the `a`-node, then the `b`-node onto the wired bond at the
form tag. -/
private def dagEdges (m : Nat) (dag : List Bool) (invw : List Nat) :
    List (Nat × Nat × Nat) :=
  ((List.range m).filter (fun j => ground.getAt false dag j)).flatMap
    (fun j => [(j, aNode m dag j, 0),
               (aNode m dag j + 1, ground.getAt 0 invw j, 1)])

/-- The other edge at a node — every node carries exactly two edge
ends — the least index off the current. -/
private def otherEdge (edges : List (Nat × Nat × Nat)) (c y : Nat) :
    Nat :=
  (List.range edges.length).foldl (fun acc i =>
    let e := ground.getAt (0, 0, 0) edges i
    if acc == edges.length && i != c && (e.1 == y || e.2.1 == y)
    then i else acc) edges.length

/-- One loop's walk from a start edge: each edge traversed forward
off its from-node, the state the edge count, the dual-pair edges
read forward, the form edges read against, and the visited
edges. -/
private def loopGoSer (edges : List (Nat × Nat × Nat)) (start : Nat) :
    Nat → Nat → Nat → Nat × Nat × Nat × List Nat →
    Nat × Nat × Nat × List Nat
  | 0, _, _, st => st
  | fuel + 1, c, x, (ec, fc, bc, vis) =>
    let e := ground.getAt (0, 0, 0) edges c
    let fwd := e.1 == x
    let y := if fwd then e.2.1 else e.1
    let ec' := ec + 1
    let fc' := if e.2.2 == 0 && fwd then fc + 1 else fc
    let bc' := if e.2.2 == 1 && !fwd then bc + 1 else bc
    let nxt := otherEdge edges c y
    if nxt == start then (ec', fc', bc', vis ++ [c])
    else loopGoSer edges start fuel nxt y (ec', fc', bc', vis ++ [c])

/-- The loops' fold over the composite graph: the walk takes the
least unused edge, one loop per orbit; the fold reads the loop
count with the parity sum, per loop half the edge count joined to
the forward dual-pair and backward form counts —
`serpairing.loopFold`'s walk idiom on the richer graph. -/
private def loopFoldSer (edges : List (Nat × Nat × Nat)) :
    Nat × Nat :=
  let st := (List.range edges.length).foldl (fun st i =>
    if 0 < ground.countOf i st.2.2 then st
    else
      let w := loopGoSer edges i edges.length i
        (ground.getAt (0, 0, 0) edges i).1 (0, 0, 0, [])
      (st.1 + 1,
       (st.2.1 + w.1 / 2 + w.2.1 + w.2.2.1, st.2.2 ++ w.2.2.2)))
    ((0, (0, [])) : Nat × Nat × List Nat)
  (st.1, st.2.1)

/-- The member engine's core, `evalPhi`'s architecture at the pair
partitions: per variable at an even factor count — else the sum's
unit — the fold over the partition pairs of the member adjugate
entries against the loop value at the composite walk's count, the
adjugate and determinant hoisted once per evaluation, the signed
series negating at an odd walk parity. -/
private def evalSer (gram : Nat → split.PMat) (loopPoly : Nat → Poly)
    (signed : Bool) (G : states.FList) (π : List Nat) :
    poly.PPair :=
  let m := G.length
  let pU := posVar G false
  let pV := posVar G true
  if pU.length % 2 == 0 && pV.length % 2 == 0 then
    let kU := pU.length / 2
    let kV := pV.length / 2
    let partsU := serpairing.allParts kU
    let partsV := serpairing.allParts kV
    let adjU := genericlift.padj (gram kU)
    let detU := split.pminor (gram kU)
    let adjV := genericlift.padj (gram kV)
    let detV := split.pminor (gram kV)
    let dag := G.map (fun f => f.2)
    let invw := places.invPerm m π
    let num := partsU.foldl (fun acc PU =>
      partsU.foldl (fun acc QU =>
        partsV.foldl (fun acc PV =>
          partsV.foldl (fun acc QV =>
            let edges :=
              pairEdges pU (rvar m dag) PU
              ++ pairEdges pV (rvar m dag) PV
              ++ pairEdges pU (svar m dag invw) QU
              ++ pairEdges pV (svar m dag invw) QV
              ++ dagEdges m dag invw
            let w := loopFoldSer edges
            let lp := if signed && w.2 % 2 == 1
              then poly.neg (loopPoly w.1) else loopPoly w.1
            let nU := ground.getAt [] (ground.getAt [] adjU
              (places.idxOf PU partsU)) (places.idxOf QU partsU)
            let nV := ground.getAt [] (ground.getAt [] adjV
              (places.idxOf PV partsV)) (places.idxOf QV partsV)
            poly.add acc (poly.mul nU (poly.mul nV lp)))
            acc) acc) acc) ([] : Poly)
    (num, poly.mul detU detV)
  else poly.pZero

/-- The `B` and `D` member evaluation — one engine, the Gram and
the loop value shared (`serpairing.gramBD`, the dimension `r + 3`
per loop at `serpairing.dimPow`): the contraction sum over the
pair partitions, `prop:wg`'s member display. -/
def evalPhiBD (G : states.FList) (π : List Nat) : poly.PPair :=
  evalSer serpairing.gramBD serpairing.dimPow false G π

/-- The `C` member evaluation: the doubled rank `2r` per loop
(`serpairing.rankPow`, `serpairing.gramC`), a term at an odd walk
parity entering negated. -/
def evalPhiC (G : states.FList) (π : List Nat) : poly.PPair :=
  evalSer serpairing.gramC serpairing.rankPow true G π

/-- The member pairing of two generators at an engine, `pairPhi`'s
body: the conjugated key against the second at the concatenated
site. -/
def pairPhiSer (ev : states.FList → List Nat → poly.PPair)
    (Fa Fb : states.FList) (πa πb : List Nat) : poly.PPair :=
  ev (conjF Fa ++ Fb)
    (places.invPerm Fa.length πa ++ states.shiftW Fa.length πb)

/-- The member pairing of two states at an engine, `pairFull`'s
bilinear fold at the certified reduction. -/
def pairFullSer (ev : states.FList → List Nat → poly.PPair)
    (Fa Fb : states.FList) (a b : states.Comb) : poly.PPair :=
  a.foldl (fun acc ea => b.foldl (fun acc2 eb =>
    genericlift.pAddR acc2 (poly.pMul
      (poly.pMul ea.2 eb.2)
      (pairPhiSer ev Fa Fb ea.1 eb.1))) acc)
    poly.pZero

end wg
