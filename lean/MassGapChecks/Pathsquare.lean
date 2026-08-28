import MassGap.Pathsquare
/-!
The check module for `lem:pathsquare`: the batteries re-read the
path recursion by kernel `decide` — the removals on the column
multiset, the path counts (the standard tableau counts), the
recursion's two reads, and the square sum at the factorial with
the width binder's refusal.
-/
set_option maxHeartbeats 4000000

open ground places pathsquare
open units (removals)

/-! The removals, the covered shapes. -/

example : removals [1, 1, 0] = [[0, 1, 0], [2, 0, 0]] := rfl
example : removals [2, 0] = [[1, 0]] := rfl
example : removals [0, 1] = [[1, 0]] := rfl

/-! Both removal arms at one shape: `[1, 0, 1]` covers the
shortened head `[0, 0, 1]` and the grown column `[1, 1, 0]`. -/

example : removals [1, 0, 1] = [[0, 0, 1], [1, 1, 0]] := rfl

/-! The path counts, the standard tableau counts. -/

example : pathCount [2, 0] = 1 := by decide +kernel
example : pathCount [1, 1] = 2 := by decide +kernel
example : pathCount [1, 1, 0] = 2 := by decide +kernel
example : pathCount [0, 2, 0] = 2 := by decide +kernel
example : pathCount [2, 1] = 3 := by decide +kernel
example : pathCount [0, 0, 1] = 1 := by decide +kernel
example : pathCount [1, 1, 1] = 16 := by decide +kernel
example : pathCount [1, 0, 1] = 3 := by decide +kernel

/-! The recursion's two reads at instances: the seed at the vacant
degree and the step as the removals' fold. -/

example : pathCount [0, 0] = 1 := pathCount_vac [0, 0] rfl
example : pathCount [1, 0, 1]
    = ground.famFold Nat.add 0 pathCount (removals [1, 0, 1]) :=
  pathCount_step [1, 0, 1] 3 rfl

/-! The square sum at the factorial, decided and through the theorem;
the width binder's refusal at a degree beyond the letter count, the
theorem's own value read decided. -/

example : ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
    (places.allShapes 3 3) = 6 := by decide +kernel
example : ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
    (places.allShapes 3 3) = ground.factorial 3 := squareSum 3 3 (Nat.le_refl 3)
example : ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
    (places.allShapes 4 3) = ground.factorial 3 := squareSum 4 3 (by decide +kernel)
example : ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
    (places.allShapes 2 3) = 5 := by decide +kernel
example : ¬ ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
    (places.allShapes 2 3) = ground.factorial 3 := by decide +kernel
example : ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
    (places.allShapes 4 4) = ground.factorial 4 := by decide +kernel

/-! The mirror and the descent read at instances: the row's
occupancy at a target is the target's removals' at the source, the
mismatched widths vacant on both sides, and a removal descends the
degree by one at the source's width. -/

example : ground.countOf [1, 1, 0] (pieri.row [0, 1, 0])
    = ground.countOf [0, 1, 0] (removals [1, 1, 0]) :=
  row_removals [0, 1, 0] [1, 1, 0]
example : ground.countOf [2, 0] (pieri.row [1, 0])
    = ground.countOf [1, 0] (removals [2, 0]) :=
  row_removals [1, 0] [2, 0]
example : ground.countOf [1, 0] (pieri.row [1, 1, 0])
    = ground.countOf [1, 1, 0] (removals [1, 0]) :=
  row_removals [1, 1, 0] [1, 0]
example : ground.countOf [1, 0] (pieri.row [1, 1, 0]) = 0 := by decide +kernel
example : places.degree [0, 1, 0] + 1 = places.degree [1, 1, 0]
    ∧ [0, 1, 0].length = [1, 1, 0].length :=
  degree_removals [1, 1, 0] [0, 1, 0] (by decide +kernel)
