import MassGap.C2hat
import MassGap.Adjchar
/-!
The check module for `def:c2hat`: the batteries re-read the cleared
Casimir by kernel `decide` — the gap folds on the sorted rows, the
cleared traceless read `d_f Q` at the adjoint (`2 d_f²` at every
committed count) and its neighbors, the class invariance under a
full column, and the square identity, the join's collection.
-/

namespace c2hat
set_option maxHeartbeats 4000000

open ground places

/-! The gap folds. -/

theorem pin1 : rho2 [4, 2, 0] = 8 := rfl
theorem pin2 : sqGaps [4, 2, 0] = 24 := rfl

/-! The adjoint's cleared read `2 d_f²`, and its neighbors. -/

theorem pin3 : dfQ (adjchar.theta 2) = 8 := by decide +kernel
theorem pin4 : dfQ (adjchar.theta 3) = 18 := by decide +kernel
theorem pin5 : dfQ (adjchar.theta 6) = 72 := by decide +kernel
theorem pin6 : dfQ [4, 0] = 24 := by decide +kernel
theorem pin7 : dfQ [2, 2, 0] = 48 := by decide +kernel

/-! `degree_le_dfQ`'s route at the reduced shape `[2, 1, 0]`: the
cleared read thirty-two clears the count's multiple of the degree,
twelve; the reduced binder isolated at `[1]`, whose count multiple
of the degree exceeds its vacant cleared read. -/

theorem pin8 : (3 : Nat) * places.degree [2, 1, 0]
    ≤ c2hat.dfQ [2, 1, 0] :=
  degree_le_dfQ [2, 1, 0] 2 rfl rfl
theorem pin9 : (3 : Nat) * places.degree [2, 1, 0] = 12 := by decide +kernel
theorem pin10 : c2hat.dfQ [2, 1, 0] = 32 := by decide +kernel
theorem pin11 : ¬ ((1 : Nat) * places.degree [1] ≤ c2hat.dfQ [1]) := by
  decide +kernel
theorem pin12 : ([1] : places.Shape).length = 0 + 1 := by decide +kernel
theorem pin13 : ¬ (ground.getAt 0 [1] 0 = 0) := by decide +kernel

/-- The class invariance: a full column moves every row by one and
the gaps are fixed. -/
theorem pin14 : dfQ [1, 1, 1] = dfQ [1, 1, 0] := by decide +kernel

/-! The square identity `d_f q(λ) = k² + Σ ⟨λ_p : λ_q⟩²`, with the
general theorem's own instances beside the decided reads: the
shape-level `squareAll` and the row-level `squareRows` at the
adjoint's rows. -/

theorem pin15 : squareRead [1, 1, 0] := by decide +kernel
theorem pin16 : squareRead [2, 2, 0] := by decide +kernel
theorem pin17 : squareRead [0, 3, 0] := by decide +kernel
theorem pin18 : squareRead [2, 0, 0, 2] := by decide +kernel
theorem pin19 : squareRead [2, 0, 0, 2] := squareAll [2, 0, 0, 2]
theorem pin20 : ([2, 1, 0] : List Nat).length * sumSq [2, 1, 0]
    = ground.sumNat [2, 1, 0] * ground.sumNat [2, 1, 0]
      + sqGaps [2, 1, 0] := by decide +kernel
theorem pin21 : ([2, 1, 0] : List Nat).length * sumSq [2, 1, 0]
    = ground.sumNat [2, 1, 0] * ground.sumNat [2, 1, 0]
      + sqGaps [2, 1, 0] :=
  squareRows [2, 1, 0] (by decide +kernel)

/-! The fold kit at the replicate blocks and the class moves: the
two replicate folds, the block-prefix reads, the vacant family,
the two homogeneities, the shift invariance, and the class reads
at a full column and at the vacant shape. -/

theorem pin22 : (List.replicate 3 2).foldl (fun acc y => acc + (7 - y)) 1
    = 1 + 3 * (7 - 2) := c2hat.gapFold_replicate 7 2 3 1
theorem pin23 : (List.replicate 3 2).foldl
      (fun acc y => acc + (7 - y) * (7 - y)) 1
    = 1 + 3 * ((7 - 2) * (7 - 2)) := c2hat.sqFold_replicate 7 2 3 1
theorem pin24 : c2hat.rho2 (List.replicate 2 3 ++ [1, 0])
    = 2 * ([1, 0].foldl (fun acc y => acc + (3 - y)) 0)
      + c2hat.rho2 [1, 0] := c2hat.rho2_replicate_app 3 2 [1, 0]
theorem pin25 : c2hat.sqGaps (List.replicate 2 3 ++ [1, 0])
    = 2 * ([1, 0].foldl (fun acc y => acc + (3 - y) * (3 - y)) 0)
      + c2hat.sqGaps [1, 0] := c2hat.sqGaps_replicate_app 3 2 [1, 0]
theorem pin26 : c2hat.rho2 (List.replicate 5 0) = 0 := c2hat.rho2_zeros 5
theorem pin27 : c2hat.sqGaps (List.replicate 5 0) = 0 := c2hat.sqGaps_zeros 5
theorem pin28 : c2hat.rho2 ([3, 1, 0].map (fun z => z * 2))
    = 2 * c2hat.rho2 [3, 1, 0] := c2hat.rho2_scale 2 [3, 1, 0]
theorem pin29 : c2hat.sqGaps ([3, 1, 0].map (fun z => z * 2))
    = 2 * 2 * c2hat.sqGaps [3, 1, 0] := c2hat.sqGaps_scale 2 [3, 1, 0]
theorem pin30 : c2hat.rho2 ([3, 1, 0].map (fun z => z + 1))
    = c2hat.rho2 [3, 1, 0] := c2hat.rho2_shift [3, 1, 0]
theorem pin31 : c2hat.sqGaps ([3, 1, 0].map (fun z => z + 1))
    = c2hat.sqGaps [3, 1, 0] := c2hat.sqGaps_shift [3, 1, 0]
theorem pin32 : c2hat.dfQ (ground.bumpAt (([1, 0, 1, 0] :
      places.Shape).length - 1) [1, 0, 1, 0])
    = c2hat.dfQ [1, 0, 1, 0] := c2hat.dfQ_full [1, 0, 1, 0]
theorem pin33 : c2hat.dfQ (List.replicate 6 0) = 0 :=
  c2hat.dfQ_replicate_zero 6

/-! The two gap folds at place pairs, including an unordered list
whose downward gaps use the count difference's vacant read. -/

theorem pin34 : rho2 [5, 3, 0] = famFold Nat.add 0
    (fun p => getAt 0 [5, 3, 0] p.1 - getAt 0 [5, 3, 0] p.2)
    (places.pairsOf 3) := rho2_pairs [5, 3, 0]
theorem pin35 : sqGaps [5, 3, 0] = famFold Nat.add 0
    (fun p => (getAt 0 [5, 3, 0] p.1 - getAt 0 [5, 3, 0] p.2)
      * (getAt 0 [5, 3, 0] p.1 - getAt 0 [5, 3, 0] p.2))
    (places.pairsOf 3) := sqGaps_pairs [5, 3, 0]
theorem pin36 : rho2 [5, 3, 0] = 10 ∧ sqGaps [5, 3, 0] = 38 := by decide +kernel
theorem pin37 : rho2 [0, 4, 1] = famFold Nat.add 0
    (fun p => getAt 0 [0, 4, 1] p.1 - getAt 0 [0, 4, 1] p.2)
    (places.pairsOf 3) := rho2_pairs [0, 4, 1]
theorem pin38 : sqGaps [0, 4, 1] = famFold Nat.add 0
    (fun p => (getAt 0 [0, 4, 1] p.1 - getAt 0 [0, 4, 1] p.2)
      * (getAt 0 [0, 4, 1] p.1 - getAt 0 [0, 4, 1] p.2))
    (places.pairsOf 3) := sqGaps_pairs [0, 4, 1]
theorem pin39 : rho2 [0, 4, 1] = 3 ∧ sqGaps [0, 4, 1] = 9 := by decide +kernel

end c2hat
