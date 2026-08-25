import MassGap.Pencil
import MassGapChecks.Carrier
/-!
The check module for `def:pencil`'s electric diagonal: the batteries
re-read the window diagonal by kernel `decide` at the label
calculus's instantiation — the content list over the index at the
square's committed windows (the fundamental loop's entry alone, then
the two label loops'), and the diagonal's positivity at the square
and the theta graph, the unit line the kernel beside it.
-/

open ground lattice fusion pencil

/-! The diagonal's content list at the square: the fundamental
loop's entry alone at the first cutoff, the two label loops' at the
second. -/

example : elecDiag (dataA 2) square 12 = [12] := by decide +kernel
private theorem hDiag32 : elecDiag (dataA 2) square 32 = [12, 32] :=
  elecDiag_at (dataA 2) square 32 carrier.sqIx2 [12, 32]
    carrier.sqIx2_pin (by decide +kernel)

example : (elecDiag (dataA 2) square 32).length = 2 := by
  rw [hDiag32]; rfl

/-! The diagonal's positivity: every occupied content positive, the
unit line the kernel beside the list. -/

example : diagPos (dataA 2) square 12 := by decide +kernel
example : diagPos (dataA 2) square 32 := by
  show ((elecDiag (dataA 2) square 32).all (fun c => 0 < c)) = true
  rw [hDiag32]
  decide +kernel
private theorem hDiagTh12 :
    elecDiag (tabulate (dataA 2) 12) thetaG 12 = [12, 12] :=
  elecDiag_at (tabulate (dataA 2) 12) thetaG 12 carrier.thIx12
    [12, 12] carrier.thIx12_pin (by decide +kernel)

example : diagPos (tabulate (dataA 2) 12) thetaG 12 := by
  show ((elecDiag (tabulate (dataA 2) 12) thetaG 12).all
    (fun c => 0 < c)) = true
  rw [hDiagTh12]
  decide +kernel
