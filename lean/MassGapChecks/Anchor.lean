import MassGap.Anchor
/-!
The check module for `prop:anchor`: the batteries re-read the
charged tower by kernel `decide` — the tower label at the committed
residues, the cleared traceless read `d_f Q(mθ) = 2 d_f m (m + r)`
along the `r = 1` tower and beyond, the adjoint's own `m = 1` value
`2 d_f²`, the vacant index `m = 0`, the binder record at the
degenerate counts (`d = 0` decided, `d = 1` refused), and the tower
law's cross-multiplied display through the theorem.
-/

namespace anchor

open ground places

/-! The tower label, the adjoint's columns scaled by the index. -/

theorem pin1 : towerShape 2 1 = [2, 0] := rfl
theorem pin2 : towerShape 2 2 = [4, 0] := rfl
theorem pin3 : towerShape 2 3 = [6, 0] := rfl
theorem pin4 : towerShape 3 1 = [1, 1, 0] := rfl
theorem pin5 : towerShape 3 2 = [2, 2, 0] := rfl
theorem pin6 : towerShape 5 3 = [3, 0, 0, 3, 0] := rfl

/-! The cleared traceless read at the tower: the `r = 1` string's
cleared values `8, 24, 48` against `2 d_f² = 8`, so
`ĉ₂ = [1], [3], [6]`, and the general display at wider counts. -/

theorem pin7 : c2hat.dfQ (towerShape 2 1) = 2 * 2 * (1 * (1 + (2 - 1))) := by
  decide +kernel
theorem pin8 : c2hat.dfQ (towerShape 2 2) = 2 * 2 * (2 * (2 + (2 - 1))) := by
  decide +kernel
theorem pin9 : c2hat.dfQ (towerShape 2 3) = 2 * 2 * (3 * (3 + (2 - 1))) := by
  decide +kernel
theorem pin10 : c2hat.dfQ (towerShape 3 1) = 2 * 3 * (1 * (1 + (3 - 1))) := by
  decide +kernel
theorem pin11 : c2hat.dfQ (towerShape 3 2) = 2 * 3 * (2 * (2 + (3 - 1))) := by
  decide +kernel
theorem pin12 : c2hat.dfQ (towerShape 5 3) = 2 * 5 * (3 * (3 + (5 - 1))) := by
  decide +kernel

theorem pin13 : c2hat.dfQ (towerShape 2 1) = 8 := by decide +kernel
theorem pin14 : c2hat.dfQ (towerShape 2 2) = 24 := by decide +kernel
theorem pin15 : c2hat.dfQ (towerShape 2 3) = 48 := by decide +kernel

/-! The cleared cross-products of `ĉ₂(mθ) = [m (m + r) : r + 1]` at
`r = 1`: the string reads `1, 3, 6` against `2 d_f² = 8`. -/

theorem pin16 : c2hat.dfQ (towerShape 2 1) * 1 = 1 * (2 * (2 * 2)) := by decide +kernel
theorem pin17 : c2hat.dfQ (towerShape 2 2) * 1 = 3 * (2 * (2 * 2)) := by decide +kernel
theorem pin18 : c2hat.dfQ (towerShape 2 3) * 1 = 6 * (2 * (2 * 2)) := by decide +kernel

/-! The adjoint read `m = 1`: `d_f Q(θ) = 2 d_f²`, so `ĉ₂(θ) = 1`. -/

theorem pin19 : c2hat.dfQ (towerShape 2 1) = 2 * (2 * 2) := by decide +kernel
theorem pin20 : c2hat.dfQ (towerShape 3 1) = 2 * (3 * 3) := by decide +kernel
theorem pin21 : c2hat.dfQ (towerShape 4 1) = 2 * (4 * 4) := by decide +kernel

/-! The vacant index: `0 · θ` is the vacant occupancy and the
display reads vacant with it. -/

theorem pin22 : towerShape 4 0 = [0, 0, 0, 0] := rfl
theorem pin23 : c2hat.dfQ (towerShape 4 0) = 2 * 4 * (0 * (0 + (4 - 1))) := by
  decide +kernel

/-! The binder record at the degenerate counts.  At `d = 0` the
label is vacant and the display reads vacant, so the count is not
load-bearing there; at `d = 1` the adjoint's two columns collapse
onto one place, the row list is a single row with no pair, and the
display refuses — the binder `2 ≤ d` is load-bearing at `d = 1`. -/

theorem pin24 : c2hat.dfQ (towerShape 0 2) = 2 * 0 * (2 * (2 + (0 - 1))) := by
  decide +kernel
theorem pin25 : towerShape 1 1 = [2] := rfl
theorem pin26 : c2hat.dfQ (towerShape 1 1) = 0 := by decide +kernel
theorem pin27 : ¬ c2hat.dfQ (towerShape 1 1) = 2 * 1 * (1 * (1 + (1 - 1))) := by
  decide +kernel
theorem pin28 : ¬ c2hat.dfQ (towerShape 1 2) = 2 * 1 * (2 * (2 + (1 - 1))) := by
  decide +kernel

/-! The general theorems' own instances beside the decided reads. -/

theorem pin29 : c2hat.dfQ (towerShape 5 3) = 2 * 5 * (3 * (3 + (5 - 1))) :=
  tower_dfQ 5 3 (by decide +kernel)

theorem pin30 : c2hat.dfQ (towerShape 3 2) * 3 = 2 * (2 + (3 - 1)) * (2 * (3 * 3)) :=
  towerRead 3 2 (by decide +kernel)

theorem pin31 : c2hat.dfQ (towerShape 3 2) * 3 = 2 * (2 + (3 - 1)) * (2 * (3 * 3)) := by
  decide +kernel

end anchor
