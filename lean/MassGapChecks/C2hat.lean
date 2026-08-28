import MassGap.C2hat
import MassGap.Adjchar
/-!
The check module for `def:c2hat`: the batteries re-read the cleared
Casimir by kernel `decide` — the gap folds on the sorted rows, the
cleared traceless read `d_f Q` at the adjoint (`2 d_f²` at every
committed count) and its neighbors, the class invariance under a
full column, and the square identity, the join's collection.
-/
set_option maxHeartbeats 4000000

open ground places c2hat

/-! The gap folds. -/

example : rho2 [4, 2, 0] = 8 := rfl
example : sqGaps [4, 2, 0] = 24 := rfl

/-! The adjoint's cleared read `2 d_f²`, and its neighbors. -/

example : dfQ (adjchar.theta 2) = 8 := by decide +kernel
example : dfQ (adjchar.theta 3) = 18 := by decide +kernel
example : dfQ (adjchar.theta 6) = 72 := by decide +kernel
example : dfQ [4, 0] = 24 := by decide +kernel
example : dfQ [2, 2, 0] = 48 := by decide +kernel

/-- The class invariance: a full column moves every row by one and
the gaps are fixed. -/
example : dfQ [1, 1, 1] = dfQ [1, 1, 0] := by decide +kernel

/-! The square identity `d_f q(λ) = k² + Σ ⟨λ_p : λ_q⟩²`, with the
general theorem's own instances beside the decided reads: the
shape-level `squareAll` and the row-level `squareRows` at the
adjoint's rows. -/

example : squareRead [1, 1, 0] := by decide +kernel
example : squareRead [2, 2, 0] := by decide +kernel
example : squareRead [0, 3, 0] := by decide +kernel
example : squareRead [2, 0, 0, 2] := by decide +kernel
example : squareRead [2, 0, 0, 2] := squareAll [2, 0, 0, 2]
example : ([2, 1, 0] : List Nat).length * sumSq [2, 1, 0]
    = ground.sumNat [2, 1, 0] * ground.sumNat [2, 1, 0]
      + sqGaps [2, 1, 0] := by decide +kernel
example : ([2, 1, 0] : List Nat).length * sumSq [2, 1, 0]
    = ground.sumNat [2, 1, 0] * ground.sumNat [2, 1, 0]
      + sqGaps [2, 1, 0] :=
  squareRows [2, 1, 0] (by decide +kernel)

/-! The fold kit at the replicate blocks and the class moves: the
two replicate folds, the block-prefix reads, the vacant family,
the two homogeneities, the shift invariance, and the class reads
at a full column and at the vacant shape. -/

example : (List.replicate 3 2).foldl (fun acc y => acc + (7 - y)) 1
    = 1 + 3 * (7 - 2) := c2hat.gapFold_replicate 7 2 3 1
example : (List.replicate 3 2).foldl
      (fun acc y => acc + (7 - y) * (7 - y)) 1
    = 1 + 3 * ((7 - 2) * (7 - 2)) := c2hat.sqFold_replicate 7 2 3 1
example : c2hat.rho2 (List.replicate 2 3 ++ [1, 0])
    = 2 * ([1, 0].foldl (fun acc y => acc + (3 - y)) 0)
      + c2hat.rho2 [1, 0] := c2hat.rho2_replicate_app 3 2 [1, 0]
example : c2hat.sqGaps (List.replicate 2 3 ++ [1, 0])
    = 2 * ([1, 0].foldl (fun acc y => acc + (3 - y) * (3 - y)) 0)
      + c2hat.sqGaps [1, 0] := c2hat.sqGaps_replicate_app 3 2 [1, 0]
example : c2hat.rho2 (List.replicate 5 0) = 0 := c2hat.rho2_zeros 5
example : c2hat.sqGaps (List.replicate 5 0) = 0 := c2hat.sqGaps_zeros 5
example : c2hat.rho2 ([3, 1, 0].map (fun z => z * 2))
    = 2 * c2hat.rho2 [3, 1, 0] := c2hat.rho2_scale 2 [3, 1, 0]
example : c2hat.sqGaps ([3, 1, 0].map (fun z => z * 2))
    = 2 * 2 * c2hat.sqGaps [3, 1, 0] := c2hat.sqGaps_scale 2 [3, 1, 0]
example : c2hat.rho2 ([3, 1, 0].map (fun z => z + 1))
    = c2hat.rho2 [3, 1, 0] := c2hat.rho2_shift [3, 1, 0]
example : c2hat.sqGaps ([3, 1, 0].map (fun z => z + 1))
    = c2hat.sqGaps [3, 1, 0] := c2hat.sqGaps_shift [3, 1, 0]
example : c2hat.dfQ (ground.bumpAt (([1, 0, 1, 0] :
      places.Shape).length - 1) [1, 0, 1, 0])
    = c2hat.dfQ [1, 0, 1, 0] := c2hat.dfQ_full [1, 0, 1, 0]
example : c2hat.dfQ (List.replicate 6 0) = 0 :=
  c2hat.dfQ_replicate_zero 6
