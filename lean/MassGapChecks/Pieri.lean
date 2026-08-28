import MassGap.Pieri
/-!
The check module for `lem:pieri`: the batteries re-read the one-box
row by kernel `decide` — the targets on the column multiset, and
the row read's coherence with `def:blockcount`'s kernel-dimension
count at the su(2) and su(3) instances, a same-degree off-row
target and a mismatched-degree target among them.

The complement tier rides beside it: the one-column shape at the gap
depth, its row of dominant one-box withdrawals of the full-column
raise, and the complement read's coherence with the same count at
the su(2) and su(3) instances — the theorem route at each, an
off-row target's vacant read, and the depth binder's refusals at the
vacant and the one-row widths, where the row's count is occupied
against a vacant fusion count.
-/
set_option maxHeartbeats 4000000

open ground places pieri

/-! The rows, the one-box additions on the column multiset. -/

example : oneBox 2 = [1, 0] := rfl
example : row [1, 0] = [[2, 0], [0, 1]] := rfl
example : row [1, 1, 0] = [[2, 1, 0], [0, 2, 0], [1, 0, 1]] := rfl
example : row [1, 0, 0] = [[2, 0, 0], [0, 1, 0]] := rfl
example : row [2, 0, 0] = [[3, 0, 0], [1, 1, 0]] := rfl

/-! The row read against the definitional count. -/

example : pieri.read [1, 0] [2, 0] := by decide +kernel
example : pieri.read [1, 0] [0, 1] := by decide +kernel
example : pieri.read [1, 0] [1, 1] := by decide +kernel
example : pieri.read [1, 0, 0] [2, 0, 0] := by decide +kernel
example : pieri.read [1, 0, 0] [0, 1, 0] := by decide +kernel
example : pieri.read [2, 0, 0] [0, 0, 1] := by decide +kernel

/-! The general theorem's own route at the same data, the grown
column's arm beside the new column's. -/

example : pieri.read [1, 0] [2, 0] :=
  pieri.readAll [1, 0] [2, 0] (by decide +kernel) rfl
example : pieri.read [1, 0] [1, 1] :=
  pieri.readAll [1, 0] [1, 1] (by decide +kernel) rfl
example : pieri.read [2, 0, 0] [0, 0, 1] :=
  pieri.readAll [2, 0, 0] [0, 0, 1] (by decide +kernel) rfl
example : pieri.read [1, 0] [0, 1] :=
  pieri.readAll [1, 0] [0, 1] (by decide +kernel) rfl
example : pieri.read [1, 1, 0] [1, 0, 1] :=
  pieri.readAll [1, 1, 0] [1, 0, 1] (by decide +kernel) rfl
example : pieri.read [1, 1, 0] [0, 2, 0] :=
  pieri.readAll [1, 1, 0] [0, 2, 0] (by decide +kernel) rfl

/-! The theorem's two binders.  The positive width is load-bearing:
at the vacant width the one-box factor's fusion count reads one
pair against the vacant row, so the read refuses.  The matched
width is unrefusable at either direction — a narrow or a wide
target sits off every row member and off the fused pool alike, both
counts vacant. -/

example : ¬ pieri.read [] [] := by decide +kernel
example : pieri.read [1, 0] [1] := by decide +kernel
example : pieri.read [1, 0] [1, 1, 0] := by decide +kernel

/-! The complement's one-column shape and its row: the dominant
one-box withdrawals of the full-column raise. -/

example : pieri.complBox 2 = [1, 0] := rfl
example : pieri.complBox 3 = [0, 1, 0] := rfl
example : pieri.rowD [1, 0] = [[0, 1], [2, 0]] := rfl
example : pieri.rowD [2, 0] = [[1, 1], [3, 0]] := rfl
example : pieri.rowD [1, 1, 0] = [[0, 1, 1], [2, 0, 1], [1, 2, 0]] := rfl
example : pieri.rowD [2, 2, 0] = [[1, 2, 1], [3, 1, 1], [2, 3, 0]] := rfl

/-! The complement read against the definitional count at the two
depths, an off-row target's vacant read beside the occupied ones. -/

example : pieri.readD [1, 0] [0, 1] := by decide +kernel
example : pieri.readD [2, 0] [1, 1] := by decide +kernel
example : pieri.readD [2, 0] [3, 0] := by decide +kernel
example : pieri.readD [1, 1, 0] [0, 1, 1] := by decide +kernel
example : pieri.readD [1, 1, 0] [0, 2, 0] := by decide +kernel

/-! The general theorem's own route at the same data, both binders
decided. -/

example : pieri.readD [1, 0] [0, 1] :=
  pieri.readAllD [1, 0] [0, 1] (by decide +kernel) rfl
example : pieri.readD [2, 0] [1, 1] :=
  pieri.readAllD [2, 0] [1, 1] (by decide +kernel) rfl
example : pieri.readD [1, 1, 0] [1, 2, 0] :=
  pieri.readAllD [1, 1, 0] [1, 2, 0] (by decide +kernel) rfl
example : pieri.readD [2, 2, 0] [1, 2, 1] :=
  pieri.readAllD [2, 2, 0] [1, 2, 1] (by decide +kernel) rfl
example : pieri.readD [2, 2, 0] [2, 3, 0] :=
  pieri.readAllD [2, 2, 0] [2, 3, 0] (by decide +kernel) rfl

/-! The depth binder is load-bearing at both ends.  At the vacant
width the complement box is the empty shape, the fusion count reads
one pair against a vacant row and the read refuses; at the one-row
width the row carries the shape itself while the complement's fusion
count is vacant, so the row read's own occupancy is what the count
distinguishes.  The matched width is unrefusable at either
direction — a narrow or a wide target sits off every row member and
off the fused pool alike. -/

example : ¬ pieri.readD [] [] := by decide +kernel
example : pieri.rowD [1] = [[1]] := rfl
example : ¬ pieri.readD [1] [1] := by decide +kernel
example : pieri.readD [1, 0] [1] := by decide +kernel
example : pieri.readD [1, 0] [1, 1, 0] := by decide +kernel
