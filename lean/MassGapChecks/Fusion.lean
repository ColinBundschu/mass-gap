import MassGap.Fusion
import MassGap.Drift
/-!
The check module for `con:fusion`: the batteries re-read the
interface at the label calculus's instantiation by kernel `decide`
— the count laws through the structure's own fields (the unit
read, commutativity, Cartan strictness, associativity), the
dimension identity and the drift identity over the rows (the
adjoint square's fold at `2 d_θ² · c2D` cleared), with
`thm:drift`'s general theorem entering at two of the decided
drift labels by its own route, the Casimir's positivity over the
enumeration, the orientation reversal's two blindnesses at the
interface (the dual label's Casimir its label's own and `θ`
self-dual, `thm:restoration`'s two fixings) with a forged Casimir
and a forged involution refusing, and the below-cutoff
enumeration's soundness with
its displayed small values (the
degree window's completeness the cleared bracket's own growth,
`d_f Q` at or beyond the fundamental count's multiple of the
degree at a reduced shape).
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground places fusion

/-! The count laws through the interface at two and three
letters. -/

example : unitLaw (dataA 2) [1, 0] [1, 0] := by decide +kernel
example : unitLaw (dataA 2) [2, 0] [2, 0] := by decide +kernel
example : unitLaw (dataA 3) [1, 0, 0] [0, 1, 0] := by decide +kernel
example : unitLaw (dataA 3) [1, 1, 0] [1, 1, 0] := by decide +kernel
example : unitLaw (dataA 3) [1, 0, 0] [1, 0, 0] := by decide +kernel
example : commLaw (dataA 3) [1, 0, 0] [1, 1, 0] [2, 1, 0] := by decide +kernel
example : cartanLaw (dataA 2) [1, 0] [1, 0] := by decide +kernel
example : cartanLaw (dataA 3) [1, 1, 0] [1, 1, 0] := by decide +kernel
example : assocLaw (dataA 2) [1, 0] [1, 0] [1, 0] [1, 1] := by decide +kernel
example : assocLaw (dataA 3) [1, 0, 0] [1, 0, 0] [1, 0, 0]
    [1, 1, 0] := by decide +kernel

/-! The dimension identity over the rows. -/

example : dimLaw (dataA 2) [1, 0] [1, 0] := by decide +kernel
example : dimLaw (dataA 2) [2, 0] [2, 0] := by decide +kernel
example : dimLaw (dataA 3) [1, 0, 0] [1, 0, 0] := by decide +kernel
example : dimLaw (dataA 3) [1, 0, 0] [1, 1, 0] := by decide +kernel
example : dimLaw (dataA 3) [1, 1, 0] [1, 1, 0] := by decide +kernel

/-! The drift identity, uniform in the label: the adjoint square's
`Σ m d ĉ₂ = 2 d_θ²` at the `θ` instances with the fundamental and
symmetric-square instances beside them. -/

example : driftLaw (dataA 2) (adjchar.theta 2) := by decide +kernel
example : driftLaw (dataA 3) (adjchar.theta 3) := by decide +kernel
example : driftLaw (dataA 2) [1, 0] := by decide +kernel
example : driftLaw (dataA 3) [1, 0, 0] := by decide +kernel
example : driftLaw (dataA 3) [2, 0, 0] := by decide +kernel

/-! The same identity through `thm:drift` at the two-letter `θ`
and at the three-letter symmetric square, the general theorem
against the decided values. -/

example : driftLaw (dataA 2) (adjchar.theta 2) :=
  drift.readAll 2 (by decide +kernel) (adjchar.theta 2) (adjchar.length_theta 2)
example : driftLaw (dataA 3) [2, 0, 0] :=
  drift.readAll 3 (by decide +kernel) [2, 0, 0] rfl

/-! The orientation reversal's two blindnesses
(`thm:restoration`): the dual label's Casimir reads its label's
own at the committed labels, and `θ` is self-dual at both letter
counts, each beside the refusal that isolates it — a Casimir read
off the degree and an involution constant at one label. -/

example : casDualLaw (dataA 2) [1, 0] := by decide +kernel
example : casDualLaw (dataA 2) [2, 0] := by decide +kernel
example : casDualLaw (dataA 3) [1, 0, 0] := by decide +kernel
example : casDualLaw (dataA 3) [1, 1, 0] := by decide +kernel
example : casDualLaw (dataA 3) [2, 1, 0] := by decide +kernel
example : thetaSelfDual (dataA 2) := by decide +kernel
example : thetaSelfDual (dataA 3) := by decide +kernel

example : ¬ casDualLaw
    { dataA 3 with c2N := fun s => places.degree s }
    [1, 0, 0] := by decide +kernel
example : ¬ thetaSelfDual
    { dataA 3 with dual := fun _ => [1, 0, 0] } := by decide +kernel

/-! The row's support at the adjoint square, the channel count. -/

example : ((dataA 2).row [2, 0] [2, 0]).length = 3 := by decide +kernel
example : ((dataA 3).row [1, 1, 0] [1, 1, 0]).length = 5 := by decide +kernel

/-! The Casimir's positivity over the enumeration, the
enumeration's soundness, and its displayed small values. -/

example : (((dataA 2).below 8).all (fun l =>
    if casPos (dataA 2) l then true else false)) = true := by decide +kernel
example : (((dataA 3).below 18).all (fun l =>
    if casPos (dataA 3) l then true else false)) = true := by decide +kernel
example : belowSound (dataA 2) 8 := by decide +kernel
example : belowSound (dataA 3) 18 := by decide +kernel
example : (dataA 2).below 3 = [[1, 0]] := by decide +kernel
example : (dataA 2).below 8 = [[1, 0], [2, 0]] := by decide +kernel
example : (dataA 3).below 18
    = [[1, 0, 0], [0, 1, 0], [1, 1, 0]] := by decide +kernel

/-! The base field's ties at the committed counts. -/

example : (dataA 2).c1 = 1 := by decide +kernel
example : (dataA 3).c1 = 2 := by decide +kernel

/-! The enumeration's degree windows close: every reduced shape
of the six degrees past the cutoff clears it (`prop:windowfinite`'s
degree read, `d_f Q` at or beyond the count's multiple of the
degree). -/

example : (((List.range 6).all (fun i =>
    (allShapes 1 (33 + i)).all (fun s =>
      32 < c2hat.dfQ (s ++ [0]))))) = true := by decide +kernel
example : (((List.range 6).all (fun i =>
    (allShapes 2 (19 + i)).all (fun s =>
      18 < c2hat.dfQ (s ++ [0]))))) = true := by decide +kernel

/-! The tabulated route reads one value with the interface at a
representative off the reduced set as well, the fallback's own
read. -/

example : (tabulate (dataA 2) 12).count [1, 0] [1, 0] [0, 1]
    = (dataA 2).count [1, 0] [1, 0] [0, 1] := by decide +kernel
