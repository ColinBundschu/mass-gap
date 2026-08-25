import MassGap.Stableentries
import MassGapChecks.Fiberdec
import MassGap.Fiberdec
/-!
The check module for `lem:stableentries`: the batteries re-read the
locality band by kernel `decide` at the label calculus's
instantiation on two disjoint squares and the theta graph — the
vertex neighborhood reads (`nearPlaq` at the own and the far
plaquette, the shared-link plaquette near through the joint
vertex), the far row's factorization at two and three letters (the
one concatenation, the `θ`-loop entering on the far boundary with
the configuration kept), and the near case's changed-edge read at
the shared link (the row splitting at that link's fusion row alone,
the further boundary links at the unit law's `θ`). -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

open ground lattice fusion stableentries fiberdec

private def twoSq : Region :=
  ⟨8, 8, [0, 1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 0, 5, 6, 7, 4],
   [[(0, true), (1, true), (2, true), (3, true)],
    [(4, true), (5, true), (6, true), (7, true)]],
   [true, false, true, false, true, false, true, false], rfl, rfl⟩

private def plaqA : List (Nat × Bool) :=
  [(0, true), (1, true), (2, true), (3, true)]

private def plaqB : List (Nat × Bool) :=
  [(4, true), (5, true), (6, true), (7, true)]

private def plaqBT : List (Nat × Bool) :=
  [(4, true), (5, true), (6, true), (3, false)]

private def fLoop8 : List places.Shape :=
  List.replicate 4 [1, 0] ++ List.replicate 4 (labels.unitL 2)

private def fLoop8c : List places.Shape :=
  List.replicate 4 [1, 0, 0] ++ List.replicate 4 (labels.unitL 3)

private def fLoop7 : List places.Shape :=
  List.replicate 4 [1, 0] ++ List.replicate 3 (labels.unitL 2)

/-! The vertex neighborhood reads: the own plaquette near, the
disjoint square far, the shared-link plaquette near through the
joint vertex. -/

example : nearPlaq (dataA 2) twoSq fLoop8 plaqA = true := by decide +kernel
example : nearPlaq (dataA 2) twoSq fLoop8 plaqB = false := by decide +kernel
example : nearPlaq (dataA 2) thetaG fLoop7 plaqBT = true := by decide +kernel

/-! The far row's factorization: one concatenation, the `θ`-loop on
the far boundary with the configuration kept. -/

example : farRead (dataA 2) twoSq fLoop8 plaqB := by decide +kernel
example : farRead (dataA 3) twoSq fLoop8c plaqB := by decide +kernel

/-! The near case's changed-edge read at the shared link: the row
splits at that link's fusion row alone, the further boundary links
at the unit law's `θ`. -/

example : algebra.plaqRow (dataA 2) thetaG plaqBT fLoop7
    = [[[1, 0], [1, 0], [1, 0], [3, 0], [2, 0], [2, 0], [2, 0]],
       [[1, 0], [1, 0], [1, 0], [1, 0], [2, 0], [2, 0], [2, 0]]] := by
  decide +kernel

/-! The border factorization at the plaquette chain of nine
squares: the loops at two squares four apart read no shared vertex
and join to one configuration whose fiber dimension is the parts'
product, while the adjacent pair shares the rung between the
squares and refuses the vertex-disjoint read. -/

private def R9 : Region := fiberdec.chainRegion 9

/-! The reach at one link: the square's own rung meets its
boundary, the rung four squares along does not. -/

example : nearLink R9 (ground.getAt [] R9.plaqs 0) 0 = true := by decide +kernel
example : nearLink R9 (ground.getAt [] R9.plaqs 0) 4 = false := by
  decide +kernel

/-! The vertex-disjoint read: the four-apart pair holds it, the
adjacent pair refuses it at the shared rung's two vertices. -/

example : carrier.occupied (dataA 3) R9 (loopAt 9 0) = true := by decide +kernel
example : disjSupp (dataA 3) R9 (loopAt 9 0) (loopAt 9 4) := by decide +kernel
example : ¬ disjSupp (dataA 3) R9 (loopAt 9 0) (loopAt 9 1) := by
  decide +kernel

/-! The join's fiber: the created loop's corners at the unit law,
every vertex multiplicity the parts' product. -/

example : carrier.occupied (dataA 3) R9
    (joinConf (dataA 3) R9 (loopAt 9 0) (loopAt 9 4)) = true := by
  decide +kernel
example : windowfinite.fibProd (dataA 3) R9 (loopAt 9 0) = 1 := by
  decide +kernel
example : windowfinite.fibProd (dataA 3) R9 (loopAt 9 4) = 1 := by
  decide +kernel
example : windowfinite.fibProd (dataA 3) R9
    (joinConf (dataA 3) R9 (loopAt 9 0) (loopAt 9 4)) = 1 := by
  decide +kernel
example : ((List.range R9.verts).all (fun v =>
    carrier.vmult (dataA 3) R9
        (joinConf (dataA 3) R9 (loopAt 9 0) (loopAt 9 4)) v
      == carrier.vmult (dataA 3) R9 (loopAt 9 0) v
        * carrier.vmult (dataA 3) R9 (loopAt 9 4) v)) = true := by
  decide +kernel

/-! The factorization's theorem route at the four-apart pair with
its computed twin. -/

example : windowfinite.fibProd (dataA 3) R9
      (joinConf (dataA 3) R9 (loopAt 9 0) (loopAt 9 4))
    = windowfinite.fibProd (dataA 3) R9 (loopAt 9 0)
      * windowfinite.fibProd (dataA 3) R9 (loopAt 9 4) :=
  fibProd_join (dataA 3) R9 (loopAt 9 0) (loopAt 9 4) (by decide +kernel)
example : windowfinite.fibProd (dataA 3) R9
      (joinConf (dataA 3) R9 (loopAt 9 0) (loopAt 9 4))
    = windowfinite.fibProd (dataA 3) R9 (loopAt 9 0)
      * windowfinite.fibProd (dataA 3) R9 (loopAt 9 4) := by decide +kernel

/-! The far row at the chain: the plaquette four squares along
factorizes at the loop, the neighbouring plaquette refuses the
factorization through the shared vertices. -/

example : farRead (dataA 3) R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 4) := by decide +kernel
example : ¬ farRead (dataA 3) R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 1) := by decide +kernel

/-! The factorization at occupied multiplicities: two adjoint
tubes, each corner at the square's channel count, read the
dimensions sixteen apiece with the join at their product. -/

private def adjA : List places.Shape :=
  (List.range R9.links).map (fun l =>
    if l == 0 || l == 1 || l == 2 || l == 3 || l == 9 || l == 10
        || l == 11 || l == 18 || l == 19 || l == 20
      then [1, 1, 0] else [0, 0, 0])
private def adjB : List places.Shape :=
  (List.range R9.links).map (fun l =>
    if l == 5 || l == 6 || l == 7 || l == 8 || l == 14 || l == 15
        || l == 16 || l == 23 || l == 24 || l == 25
      then [1, 1, 0] else [0, 0, 0])

example : windowfinite.fibProd (dataA 3) R9 adjA = 16 := by decide +kernel
example : windowfinite.fibProd (dataA 3) R9 adjB = 16 := by decide +kernel
example : disjSupp (dataA 3) R9 adjA adjB := by decide +kernel
example : windowfinite.fibProd (dataA 3) R9
    (joinConf (dataA 3) R9 adjA adjB) = 256 := by decide +kernel
example : windowfinite.fibProd (dataA 3) R9
      (joinConf (dataA 3) R9 adjA adjB)
    = windowfinite.fibProd (dataA 3) R9 adjA
      * windowfinite.fibProd (dataA 3) R9 adjB :=
  fibProd_join (dataA 3) R9 adjA adjB (by decide +kernel)
