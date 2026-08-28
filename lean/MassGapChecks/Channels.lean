import MassGap.Channels
/-!
The check module for `lem:channels`: the batteries re-read the
adjoint square's table by kernel `decide`.  The whole list is the
exhaustive read `tableRead` — over every shape at the matched
degree the fast count reads the table's occupancy — decided at the
degenerate counts and applied through `readAll` at the generic
residues, with the matched degree's lower bound refused at the two
counts beneath it and the width binder dropped at the off-width
read.  The dimension and Casimir columns pin against the table's
closed forms at `r = 2, 3, 5`, and the fast route chains to the
definitional count through `cor:steinberg`'s pinned reads at the
shared instances, with the general second slot's fold displayed at
the `θ` row's stored shape and the count at `θ` its own reading.
The Casimir column's closed forms pin at
`r = 1, 2, 3` with `rows_dfQ`'s own instance beside them, the `2θ`
row's stored shape against the tower label at `m = 2`, and the
distance joins read off the column.  The cleared dimension column
pins the same way — decided at `r = 1, 2, 3` and applied through
`rows_dim` at `r = 5` — and the two closure identities run through
their theorems at `r = 4` beside the decided instances, with the
fundamental count's lower bound classified at `d_f = 1` and at the
vacant count.
-/
set_option maxHeartbeats 4000000

open ground places channels

/-! The rows at the degenerations: the dual pair enters at
`r ≥ 2`, the last row at `r ≥ 3`. -/

example : rows 2 = [([0, 2], 1), ([2, 1], 1), ([4, 0], 1)] := rfl
example : rows 3 = [([0, 0, 2], 1), ([1, 1, 1], 2), ([2, 2, 0], 1),
  ([3, 0, 1], 1), ([0, 3, 0], 1)] := rfl
example : (rows 4).length = 6 := rfl

/-! The fast route against the definitional count at shared
instances (`cor:steinberg`'s battery pins the read there). -/

example : countAt 2 [2, 1] = steinberg.count [2, 0] [2, 0] [2, 1] := by
  decide +kernel
example : countAt 3 [1, 1, 1]
    = steinberg.count [1, 1, 0] [1, 1, 0] [1, 1, 1] := by decide +kernel

/-! The general second slot: the fold's display at the `θ` row's
own stored shape, over every shape at that product's degree, and
the count at `θ` the general fold's own reading. -/

example : (allShapes 3 9).map (fun c => adjCount 3 (rowTheta 3) c)
    = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1] := by decide +kernel

example : countAt 3 [1, 1, 1] = adjCount 3 (adjchar.theta 3) [1, 1, 1] := rfl

/-! The two multiplicity reads' agreement at a committed tie, the
theorem's route and decided; its floor binder is load-bearing —
at the width one the definitional span occupancy reads the tie the
content formula refuses — and the width binder is a frame, both
folds refusing their ties at a mismatched target length. -/

example : steinberg.gradedSums (adjchar.theta 3) [1, 0, 0] [2, 1, 0]
    = steinberg.sumsWith (adjchar.multRead 3) 3 [1, 0, 0] [2, 1, 0] :=
  sumsWith_agree 3 [1, 0, 0] [2, 1, 0] (by decide +kernel) (by decide +kernel)

example : steinberg.gradedSums (adjchar.theta 3) [1, 0, 0] [2, 1, 0]
    = steinberg.sumsWith (adjchar.multRead 3) 3 [1, 0, 0] [2, 1, 0] := by
  decide +kernel

example : ¬ steinberg.gradedSums (adjchar.theta 1) [0] [2]
    = steinberg.sumsWith (adjchar.multRead 1) 1 [0] [2] := by decide +kernel

example : steinberg.gradedSums (adjchar.theta 3) [1, 0, 0] [1, 0]
    = steinberg.sumsWith (adjchar.multRead 3) 3 [1, 0, 0] [1, 0] := by
  decide +kernel

/-! The whole list, exhaustively: the degenerations decided and
the generic residues through the general theorem. -/

example : tableRead 2 := by decide +kernel
example : tableRead 3 := by decide +kernel
example : tableRead 4 := by decide +kernel

example : tableRead 5 := readAll 5 (by decide +kernel)
example : tableRead 6 := readAll 6 (by decide +kernel)

/-! The binder record: the matched degree's lower bound is
load-bearing on `readAll` — at both counts beneath it the fast
count parts from the table's occupancy and the whole list
refuses. -/

example : ¬ tableRead 0 := by decide +kernel
example : ¬ tableRead 1 := by decide +kernel

/-! The width record: the fast count reads the table's occupancy
with the width binder dropped — a shape of a further width reads
the fold's unit on both sides, the theorem's quantifier the
matched-degree enumeration's own. -/

example : countAt 5 [2, 2] = rowRead 5 [2, 2] := by decide +kernel

/-! The two anchor counts through their theorems at a residue off
the decided instances, the values decided beside them. -/

example : countAt 6 (rowTheta 6) = 2 := countAt_rowTheta 1
example : countAt 6 (rowTheta 6) = 2 := by decide +kernel
example : countAt 6 (rowUnit 6) = 1 := countAt_rowUnit 1
example : countAt 6 (rowUnit 6) = 1 := by decide +kernel

/-! The dimension column against the table's closed forms. -/

example : (rows 3).map (fun r => weyldim.dimOf r.1)
    = [1, 8, 27, 10, 10] := by decide +kernel
example : (rows 4).map (fun r => weyldim.dimOf r.1)
    = [1, 15, 84, 45, 45, 20] := by decide +kernel
example : (rows 6).map (fun r => weyldim.dimOf r.1)
    = [1, 35, 405, 280, 280, 189] := by decide +kernel

/-! The Casimir column, cleared at `2 d_f²`. -/

example : (rows 3).map (fun r => c2hat.dfQ r.1)
    = [0, 18, 48, 36, 36] := by decide +kernel
example : (rows 6).map (fun r => c2hat.dfQ r.1)
    = [0, 72, 168, 144, 144, 120] := by decide +kernel

/-! The two closure identities at the committed residues. -/

example : dimClosure 2 := by decide +kernel
example : dimClosure 3 := by decide +kernel
example : dimClosure 4 := by decide +kernel
example : dimClosure 6 := by decide +kernel
example : casClosure 2 := by decide +kernel
example : casClosure 3 := by decide +kernel
example : casClosure 4 := by decide +kernel
example : casClosure 6 := by decide +kernel

/-! The `2θ` row's stored shape against the tower label at `m = 2`
(`prop:anchor`), the tex's own `m = 2` read. -/

example : ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (2 - 2)
    (ground.bumpAt (2 - 2) (List.replicate 2 0))))
    = anchor.towerShape 2 2 := by decide +kernel
example : ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (4 - 2)
    (ground.bumpAt (4 - 2) (List.replicate 4 0))))
    = anchor.towerShape 4 2 := by decide +kernel
example : ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (4 - 2)
    (ground.bumpAt (4 - 2) (List.replicate 4 0))))
    = anchor.towerShape 4 2 :=
  row2Theta_towerShape 4

/-! The tower-shape identity is binder-free: the two degenerate
widths read it as well, the vacant list and the one-letter
square. -/

example : ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (0 - 2)
    (ground.bumpAt (0 - 2) (List.replicate 0 0))))
    = anchor.towerShape 0 2 := by decide +kernel
example : ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (1 - 2)
    (ground.bumpAt (1 - 2) (List.replicate 1 0))))
    = anchor.towerShape 1 2 := by decide +kernel

/-! The Casimir column's closed forms at the committed residues,
the guarded segments entering at their own thresholds. -/

example : (rows 2).map (fun p => c2hat.dfQ p.1)
    = [0, 2 * (2 * 2), 2 * (2 * 2) + 2 * (2 * (2 + 2))]
      ++ (if 3 ≤ 2 then [4 * (2 * 2), 4 * (2 * 2)] else [])
      ++ (if 4 ≤ 2 then [2 * (2 * 2) + 2 * (2 * (2 - 2))] else []) := by
  decide +kernel
example : (rows 3).map (fun p => c2hat.dfQ p.1)
    = [0, 2 * (3 * 3), 2 * (3 * 3) + 2 * (3 * (3 + 2))]
      ++ (if 3 ≤ 3 then [4 * (3 * 3), 4 * (3 * 3)] else [])
      ++ (if 4 ≤ 3 then [2 * (3 * 3) + 2 * (3 * (3 - 2))] else []) := by
  decide +kernel
example : (rows 4).map (fun p => c2hat.dfQ p.1)
    = [0, 2 * (4 * 4), 2 * (4 * 4) + 2 * (4 * (4 + 2))]
      ++ (if 3 ≤ 4 then [4 * (4 * 4), 4 * (4 * 4)] else [])
      ++ (if 4 ≤ 4 then [2 * (4 * 4) + 2 * (4 * (4 - 2))] else []) := by
  decide +kernel

example : (rows 6).map (fun p => c2hat.dfQ p.1)
    = [0, 2 * (6 * 6), 2 * (6 * 6) + 2 * (6 * (6 + 2))]
      ++ (if 3 ≤ 6 then [4 * (6 * 6), 4 * (6 * 6)] else [])
      ++ (if 4 ≤ 6 then [2 * (6 * 6) + 2 * (6 * (6 - 2))] else []) :=
  rows_dfQ 6 (by decide +kernel)

/-! The distance joins read off the column, positive at the rows'
own residues through the theorems, with the joins' values at two
instances. -/

example : 0 < 2 * (3 * (3 + 2)) := dist2Theta_pos 3 (by decide +kernel)
example : 2 * (3 * 3) + 2 * (3 * (3 + 2)) = 48 := by decide +kernel
example : 0 < 2 * (4 * (4 - 2)) := distOmega_pos 4 (by decide +kernel)
example : 2 * (4 * 4) + 2 * (4 * (4 - 2)) = 48 := by decide +kernel
example : 0 < 2 * (9 * (9 + 2)) := dist2Theta_pos 9 (by decide +kernel)
example : 0 < 2 * (7 * (7 - 2)) := distOmega_pos 7 (by decide +kernel)

/-! The dimension column against the table's closed forms, decided
at the degenerations and applied through the theorem at the first
generic residue. -/

example : (rows 2).map (fun p => 4 * weyldim.dimOf p.1)
    = [4, 4 * (2 * 2 - 1), 2 * 2 * ((2 - 1) * (2 + 3))]
      ++ (if 3 ≤ 2 then
          [(2 - 2) * ((2 - 1) * ((2 + 1) * (2 + 2))),
           (2 - 2) * ((2 - 1) * ((2 + 1) * (2 + 2)))] else [])
      ++ (if 4 ≤ 2 then [2 * 2 * ((2 + 1) * (2 - 3))] else []) := by
  decide +kernel
example : (rows 3).map (fun p => 4 * weyldim.dimOf p.1)
    = [4, 4 * (3 * 3 - 1), 3 * 3 * ((3 - 1) * (3 + 3))]
      ++ (if 3 ≤ 3 then
          [(3 - 2) * ((3 - 1) * ((3 + 1) * (3 + 2))),
           (3 - 2) * ((3 - 1) * ((3 + 1) * (3 + 2)))] else [])
      ++ (if 4 ≤ 3 then [3 * 3 * ((3 + 1) * (3 - 3))] else []) := by
  decide +kernel
example : (rows 4).map (fun p => 4 * weyldim.dimOf p.1)
    = [4, 4 * (4 * 4 - 1), 4 * 4 * ((4 - 1) * (4 + 3))]
      ++ (if 3 ≤ 4 then
          [(4 - 2) * ((4 - 1) * ((4 + 1) * (4 + 2))),
           (4 - 2) * ((4 - 1) * ((4 + 1) * (4 + 2)))] else [])
      ++ (if 4 ≤ 4 then [4 * 4 * ((4 + 1) * (4 - 3))] else []) := by
  decide +kernel

example : (rows 6).map (fun p => 4 * weyldim.dimOf p.1)
    = [4, 4 * (6 * 6 - 1), 6 * 6 * ((6 - 1) * (6 + 3))]
      ++ (if 3 ≤ 6 then
          [(6 - 2) * ((6 - 1) * ((6 + 1) * (6 + 2))),
           (6 - 2) * ((6 - 1) * ((6 + 1) * (6 + 2)))] else [])
      ++ (if 4 ≤ 6 then [6 * 6 * ((6 + 1) * (6 - 3))] else []) :=
  rows_dim 6 (by decide +kernel)

/-! The two closure identities through their theorems at a residue
off the decided instances. -/

example : dimClosure 5 := dimClosureAll 5 (by decide +kernel)
example : casClosure 5 := casClosureAll 5 (by decide +kernel)

/-! The binder record: the fundamental count's lower bound is
load-bearing on `rows_dim` and on the first closure identity — at
`d_f = 1` the rows are the three self-dual labels alone, every
dimension reads one, and both statements refuse.  On the second
identity the bound is the proof's frame rather than the
conclusion's: at `d_f = 1` and at the vacant count the Casimir
column is the kernel point at every row and both sides read zero,
so the read survives there while the derivation, which runs through
`rows_dim`, does not. -/

example : rows 1 = [([2], 1), ([3], 2), ([4], 1)] := rfl
example : (rows 1).map (fun p => 4 * weyldim.dimOf p.1) = [4, 4, 4] := by
  decide +kernel

example : ¬ ((rows 1).map (fun p => 4 * weyldim.dimOf p.1)
    = [4, 4 * (1 * 1 - 1), 1 * 1 * ((1 - 1) * (1 + 3))]
      ++ (if 3 ≤ 1 then
          [(1 - 2) * ((1 - 1) * ((1 + 1) * (1 + 2))),
           (1 - 2) * ((1 - 1) * ((1 + 1) * (1 + 2)))] else [])
      ++ (if 4 ≤ 1 then [1 * 1 * ((1 + 1) * (1 - 3))] else [])) := by
  decide +kernel
example : ¬ dimClosure 1 := by decide +kernel
example : ¬ dimClosure 0 := by decide +kernel

example : (rows 1).map (fun p => c2hat.dfQ p.1) = [0, 0, 0] := by decide +kernel
example : casClosure 1 := by decide +kernel
example : casClosure 0 := by decide +kernel
