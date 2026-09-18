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

namespace fusion
set_option maxHeartbeats 4000000

open ground places

/-! The count laws through the interface at two and three
letters. -/

theorem pin1 : unitLaw (dataA 2) [1, 0] [1, 0] := by decide +kernel
theorem pin2 : unitLaw (dataA 2) [2, 0] [2, 0] := by decide +kernel
theorem pin3 : unitLaw (dataA 3) [1, 0, 0] [0, 1, 0] := by decide +kernel
theorem pin4 : unitLaw (dataA 3) [1, 1, 0] [1, 1, 0] := by decide +kernel
theorem pin5 : unitLaw (dataA 3) [1, 1, 0] [1, 1, 0] :=
  unitLaw_dataA 3 [1, 1, 0] [1, 1, 0] rfl rfl
theorem pin6 : unitLaw (dataA 3) [1, 0, 0] [0, 1, 0] :=
  unitLaw_dataA 3 [1, 0, 0] [0, 1, 0] rfl rfl
theorem pin7 : unitLaw (dataA 3) [1, 0, 0] [1, 0, 0] := by decide +kernel
theorem pin8 : commLaw (dataA 3) [1, 0, 0] [1, 1, 0] [2, 1, 0] := by decide +kernel
theorem pin9 : commLaw (dataA 3) [1, 0, 0] [1, 1, 0] [2, 1, 0] :=
  commLaw_dataA 3 [1, 0, 0] [1, 1, 0] [2, 1, 0] (by decide +kernel)
    (by decide +kernel)
theorem pin10 : cartanLaw (dataA 2) [1, 0] [1, 0] := by decide +kernel
theorem pin11 : cartanLaw (dataA 3) [1, 1, 0] [1, 1, 0] :=
  labels.cartan_all [1, 1, 0] [1, 1, 0] rfl
theorem pin12 : assocLaw (dataA 2) [1, 0] [1, 0] [1, 0] [1, 1] := by decide +kernel
theorem pin13 : assocLaw (dataA 2) [1, 0] [1, 0] [1, 0] [1, 1] :=
  assocLaw_dataA 2 [1, 0] [1, 0] [1, 0] [1, 1] rfl rfl rfl rfl
theorem pin14 : assocLaw (dataA 3) [1, 0, 0] [1, 0, 0] [1, 0, 0]
    [1, 1, 0] :=
  assocLaw_dataA 3 [1, 0, 0] [1, 0, 0] [1, 0, 0] [1, 1, 0] rfl rfl
    rfl rfl
theorem pin15 : assocLaw (dataA 2) [1, 0] [1, 0] [1, 0] [1, 2] := by
  decide +kernel
theorem pin16 : assocLaw (dataA 2) [1, 0] [1, 0] [1, 0] [1, 2] :=
  assocLaw_dataA 2 [1, 0] [1, 0] [1, 0] [1, 2] rfl rfl rfl rfl

/-! The dimension identity over the rows. -/

theorem pin17 : dimLaw (dataA 2) [1, 0] [1, 0] := by decide +kernel
theorem pin18 : dimLaw (dataA 2) [2, 0] [2, 0] := by decide +kernel
theorem pin19 : dimLaw (dataA 3) [1, 0, 0] [1, 0, 0] := by decide +kernel
theorem pin20 : dimLaw (dataA 3) [1, 0, 0] [1, 1, 0] := by decide +kernel
theorem pin21 : dimLaw (dataA 3) [1, 1, 0] [1, 1, 0] := by decide +kernel

/-! The drift identity, uniform in the label: the adjoint square's
`Σ m d ĉ₂ = 2 d_θ²` at the `θ` instances with the fundamental and
symmetric-square instances beside them. -/

theorem pin22 : driftLaw (dataA 2) (adjchar.theta 2) := by decide +kernel
theorem pin23 : driftLaw (dataA 3) (adjchar.theta 3) := by decide +kernel
theorem pin24 : driftLaw (dataA 2) [1, 0] := by decide +kernel
theorem pin25 : driftLaw (dataA 3) [1, 0, 0] := by decide +kernel
theorem pin26 : driftLaw (dataA 3) [2, 0, 0] := by decide +kernel

/-! The same identity through `thm:drift` at the two-letter `θ`
and at the three-letter symmetric square, the general theorem
against the decided values. -/

theorem pin27 : driftLaw (dataA 2) (adjchar.theta 2) :=
  drift.readAll 2 (by decide +kernel) (adjchar.theta 2) (adjchar.length_theta 2)
theorem pin28 : driftLaw (dataA 3) [2, 0, 0] :=
  drift.readAll 3 (by decide +kernel) [2, 0, 0] rfl

/-! The orientation reversal's two blindnesses
(`thm:restoration`): the dual label's Casimir reads its label's
own at the committed labels, and `θ` is self-dual at both letter
counts, each beside the refusal that isolates it — a Casimir read
off the degree and an involution constant at one label. -/

theorem pin29 : casDualLaw (dataA 2) [1, 0] := by decide +kernel
theorem pin30 : casDualLaw (dataA 2) [2, 0] := by decide +kernel
theorem pin31 : casDualLaw (dataA 3) [1, 0, 0] := by decide +kernel
theorem pin32 : casDualLaw (dataA 3) [1, 1, 0] := by decide +kernel
theorem pin33 : casDualLaw (dataA 3) [2, 1, 0] := by decide +kernel
theorem pin34 : thetaSelfDual (dataA 2) := by decide +kernel
theorem pin35 : thetaSelfDual (dataA 3) := thetaSelfDual_dataA 3 (by decide)

theorem pin36 : ¬ casDualLaw
    { dataA 3 with c2N := fun s => places.degree s }
    [1, 0, 0] := by decide +kernel
theorem pin37 : ¬ thetaSelfDual
    { dataA 3 with dual := fun _ => [1, 0, 0] } := by decide +kernel

/-! The row's support at the adjoint square, the channel count. -/

theorem pin38 : ((dataA 2).row [2, 0] [2, 0]).length = 3 := by decide +kernel
theorem pin39 : ((dataA 3).row [1, 1, 0] [1, 1, 0]).length = 5 := by decide +kernel

/-! The Casimir's positivity over the enumeration, the
enumeration's soundness, and its displayed small values. -/

theorem pin40 : (((dataA 2).below 8).all (fun l =>
    if casPos (dataA 2) l then true else false)) = true := by decide +kernel
theorem pin41 : (((dataA 3).below 18).all (fun l =>
    if casPos (dataA 3) l then true else false)) = true := by decide +kernel
theorem pin42 : belowSound (dataA 2) 8 := by decide +kernel
theorem pin43 : belowSound (dataA 3) 18 := by decide +kernel
theorem pin44 : belowSound (dataA 6) 35 ∧ ((dataA 6).below 35).length = 2 := by
  decide +kernel
theorem pin45 : (dataA 2).below 3 = [[1, 0]] := by decide +kernel
theorem pin46 : (dataA 2).below 8 = [[1, 0], [2, 0]] := by decide +kernel
theorem pin47 : (dataA 3).below 18
    = [[1, 0, 0], [0, 1, 0], [1, 1, 0]] := by decide +kernel

/-! The base field's ties at the committed counts. -/

theorem pin48 : (dataA 2).c1 = 1 := by decide +kernel
theorem pin49 : (dataA 3).c1 = 2 := by decide +kernel

/-! The enumeration's degree windows close: every reduced shape
of the six degrees past the cutoff clears it (`prop:windowfinite`'s
degree read, `d_f Q` at or beyond the count's multiple of the
degree). -/

theorem pin50 : (((List.range 6).all (fun i =>
    (allShapes 1 (33 + i)).all (fun s =>
      32 < c2hat.dfQ (s ++ [0]))))) = true := by decide +kernel
theorem pin51 : (((List.range 6).all (fun i =>
    (allShapes 2 (19 + i)).all (fun s =>
      18 < c2hat.dfQ (s ++ [0]))))) = true := by decide +kernel

/-! The tabulated route reads one value with the interface at a
representative off the reduced set as well, the fallback's own
read. -/

theorem pin52 : (tabulate (dataA 2) 12).count [1, 0] [1, 0] [0, 1]
    = (dataA 2).count [1, 0] [1, 0] [0, 1] := by decide +kernel

/-! The row-is-support law at the instantiation: the occupied
constituent on the row once, the vacant target off it. -/

theorem pin53 : rowLaw (dataA 2) [1, 0] [1, 0] [2, 0] := by decide +kernel
theorem pin54 : rowLaw (dataA 2) [1, 0] [1, 0] [0, 0] := by decide +kernel
theorem pin55 : rowLaw (dataA 2) [1, 0] [1, 0] [3, 1] := by decide +kernel

/-! The law through `rowLaw_dataA` beside the decided reads, at the
three arms of the lift: the occupied target at the matched degree,
the vacant target, and the reduced target beyond the pairing's
degree, whose lifted count is vacant at the first shape's full
column; the refusal at the unreduced target, the full column's
class member occupied in the count and off the reduced row, the
reduced binder's own record; the widths are the frame, the law
holding at the ragged forges outright. -/

theorem pin56 : rowLaw (dataA 2) [1, 0] [1, 0] [2, 0] :=
  rowLaw_dataA 2 [1, 0] [1, 0] [2, 0] rfl rfl rfl rfl
theorem pin57 : rowLaw (dataA 2) [1, 0] [1, 0] [0, 0] :=
  rowLaw_dataA 2 [1, 0] [1, 0] [0, 0] rfl rfl rfl rfl
theorem pin58 : rowLaw (dataA 2) [1, 0] [1, 0] [4, 0] := by decide +kernel
theorem pin59 : rowLaw (dataA 2) [1, 0] [1, 0] [4, 0] :=
  rowLaw_dataA 2 [1, 0] [1, 0] [4, 0] rfl rfl rfl rfl
theorem pin60 : rowLaw (dataA 3) [1, 0, 0] [1, 1, 0] [2, 1, 0] := by decide +kernel
theorem pin61 : rowLaw (dataA 3) [1, 0, 0] [1, 1, 0] [2, 1, 0] :=
  rowLaw_dataA 3 [1, 0, 0] [1, 1, 0] [2, 1, 0] rfl rfl rfl rfl
theorem pin62 : rowLaw (dataA 0) [] [] [] := rowLaw_dataA 0 [] [] [] rfl rfl rfl rfl
theorem pin63 : ¬ rowLaw (dataA 2) [1, 0] [1, 0] [0, 1] := by decide +kernel
theorem pin64 : 0 < (dataA 2).count [1, 0] [1, 0] [0, 1] := by decide +kernel
theorem pin65 : rowLaw (dataA 2) [1, 0] [1, 0] [2, 0, 0] := by decide +kernel
theorem pin66 : rowLaw (dataA 2) [1, 0] [2, 0, 0] [1, 0] := by decide +kernel

/-! The labels at a fundamental count: the unit, the involution and
the rows inside the domain, with the refusals at the unreduced
shape and at the ragged width. -/

theorem pin67 : labelA 2 [1, 0] = true := by decide +kernel
theorem pin68 : labelA 2 (dataA 2).unit = true := labelA_unit 2
theorem pin69 : labelA 3 ((dataA 3).dual [1, 0, 0]) = true :=
  labelA_dual 3 [1, 0, 0] (by decide +kernel)
theorem pin70 : ((dataA 3).row [1, 0, 0] [1, 1, 0]).all (labelA 3) = true :=
  labelA_row 3 [1, 0, 0] [1, 1, 0]
theorem pin71 : ((dataA 3).row [1, 0, 0] [1, 1, 0]).all (labelA 3) = true := by
  decide +kernel
theorem pin72 : labelA 2 [0, 1] = false := by decide +kernel
theorem pin73 : labelA 2 [1, 0, 0] = false := by decide +kernel
theorem pin74 : ((dataA 2).unit :: (dataA 2).below 12).all (labelA 2) = true :=
  labelA_below 2 12
theorem pin75 : ((dataA 3).unit :: (dataA 3).below 18).all (labelA 3) = true := by
  decide +kernel
theorem pin76 : ((dataA 0).unit :: (dataA 0).below 5).all (labelA 0) = true :=
  labelA_below 0 5
theorem pin77 : (dataA 0).below 5 = [] := by decide +kernel
theorem pin78 : ground.distinctList ((dataA 2).unit :: (dataA 2).below 12) :=
  below_distinct_dataA 2 12
theorem pin79 : ground.distinctList ((dataA 2).unit :: (dataA 2).below 12) := by
  decide +kernel
theorem pin80 : ground.distinctList ((dataA 3).unit :: (dataA 3).below 18) := by
  decide +kernel
theorem pin81 : (dataA 3).residue = 2 ∧ (dataA 2).residue = 1 := by decide +kernel

/-! The enumeration's nesting and its nonunit read (`def:carrier`'s
directed windows): the enumeration at a cutoff is the larger
cutoff's filtered at the cleared Casimir, through the theorem at two
letters and decided at two and three letters; the refusal at a
forged enumeration dropping a member at the larger cutoff alone; the
nonunit read at three letters through the theorem, and its refusal
at the unit label joined to the enumeration. -/

theorem pin82 : belowNest (dataA 2) 3 8 := belowNest_dataA 2 3 8 (by decide)
theorem pin83 : belowNest (dataA 2) 3 8 ∧ belowNest (dataA 3) 8 18 := by decide +kernel
theorem pin84 : ¬ belowNest { dataA 3 with
    below := fun C => if C == 18 then [[1, 1, 0]] else (dataA 3).below C } 8 18 := by
  decide +kernel
theorem pin85 : belowNonunit (dataA 3) 18 := belowNonunit_dataA 3 18
theorem pin86 : ¬ belowNonunit { dataA 3 with
    below := fun C => (dataA 3).unit :: (dataA 3).below C } 18 := by decide +kernel

/-! The dimension identity through the interface theorem. The
full-column representatives have the reduced labels' dimensions.
The two width refusals isolate the factor width and the enumeration
width; the row with its unit channel removed refuses the count. -/

theorem pin87 : dimLaw (dataA 2) [1, 0] [1, 0] :=
  dimLaw_dataA 2 [1, 0] [1, 0] rfl rfl
theorem pin88 : dimLaw (dataA 3) [1, 1, 0] [1, 1, 0] :=
  dimLaw_dataA 3 [1, 1, 0] [1, 1, 0] rfl rfl
theorem pin89 : dimLaw (dataA 4) [1, 0, 0, 0] [1, 0, 0, 0] :=
  dimLaw_dataA 4 [1, 0, 0, 0] [1, 0, 0, 0] rfl rfl
theorem pin90 : dimLaw (dataA 2) [1, 1] [0, 1] :=
  dimLaw_dataA 2 [1, 1] [0, 1] rfl rfl
theorem pin91 : dimLaw (dataA 2) [1, 1] [0, 1] := by decide +kernel
theorem pin92 : dimLaw (dataA 0) [] [] := dimLaw_dataA 0 [] [] rfl rfl
theorem pin93 : ¬ dimLaw (dataA 0) [] [1, 0] := by decide +kernel
theorem pin94 : ¬ dimLaw (dataA 0) [1, 0] [1, 0] := by decide +kernel
theorem pin95 : ¬ dimLaw { dataA 2 with
    row := fun _ _ => [[2, 0]] } [1, 0] [1, 0] := by decide +kernel

/-! The positivity, duality and cutoff reads at the interface,
with the width and the cutoff filter isolated by refusals. -/

theorem pin96 : casPos (dataA 4) [2, 1, 0, 3] := casPos_dataA 4 [2, 1, 0, 3] rfl
theorem pin97 : casPos (dataA 2) [0, 3] := casPos_dataA 2 [0, 3] rfl
theorem pin98 : casPos (dataA 0) [] := casPos_dataA 0 [] rfl
theorem pin99 : ¬ casPos (dataA 0) [0] := by decide +kernel
theorem pin100 : casDualLaw (dataA 4) [2, 1, 0, 3] := labels.casDual_all [2, 1, 0, 3]
theorem pin101 : dimDualLaw (dataA 4) [2, 1, 0, 3] := labels.dimDual_all [2, 1, 0, 3]
theorem pin102 : belowSound (dataA 2) 8 := belowSound_dataA 2 8
theorem pin103 : belowSound (dataA 3) 18 := belowSound_dataA 3 18
theorem pin104 : belowSound (dataA 0) 5 := belowSound_dataA 0 5
theorem pin105 : ¬ belowSound { dataA 2 with below := fun _ => [[1, 0]] } 0 := by
  decide +kernel

/-- Distinct-key lookups agree with the guarded natural fold. -/
theorem pin106 (k : Nat) :
    (lookupBy (fun a b : Nat => decide (a = b)) k [(1, 3), (2, 5)]).getD 0
      = ground.famFold Nat.add 0 (fun p => if p.1 = k then p.2 else 0) [(1, 3), (2, 5)] :=
  lookupBy_sum _ (fun _ _ => rfl) k _ (by decide +kernel)

/-- A repeated key distinguishes the first lookup from the
sum of both entries, refusing the distinct-key premise. -/
theorem pin107 : (lookupBy (fun a b : Nat => decide (a = b)) 1 [(1, 3), (1, 5)]).getD 0 = 3
    ∧ ground.famFold Nat.add 0 (fun p : Nat × Nat => if p.1 = 1 then p.2 else 0) [(1, 3), (1, 5)] = 8
    ∧ ¬ ground.distinctList (([(1, 3), (1, 5)] : List (Nat × Nat)).map Prod.fst) := by decide +kernel

end fusion
