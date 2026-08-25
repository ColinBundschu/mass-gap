import MassGap.Chaininstances
/-!
The check module for `lem:chaininstances`: the battery reads the
whole record list by kernel `decide` — the count 37, the eight
families' cleared reads `dfQ(member) = dfQ(f) + gap` at
`rankstable.casPoly`, and both certificates at every record, the
settled side's radius clearance with its leading side and the
window below the settled point — and then the classification's
five rows one at a time, each the stated divisor's cross-multiplied
evaluation at its stated rank reading equal members: the family
`ω₃+ω₂*`'s gap at the rank two, and the binding pairs
`(2ω₁+ω₁*, ω₁+ω₂+ω₂*)` at two, `(ω₂+ω₁*, ω₃+ω₂*)` at three,
`(ω₃+2ω₁*, 2ω₁+ω₁*)` at three, and `(ω₃+ω₂*, 2ω₁+ω₁*)` at five.
The refusals isolate one committed datum each: the gap's shift
witness, at the family `ω₂+ω₁*`'s row carrying `s := 2`, where the
cleared read parts with `rankstable.casPoly`; the root list's
completeness, at the comparison `(ω₂+ω₁*, ω₃+ω₂*)` with its root
withdrawn and again with the rank four forged onto it; the settled
point, at the comparison `(ω₂+ω₁*, 3ω₁+2ω₁*)` of radius six read
at three, its clearance conjunct alone refusing; and the leading
side's occupancy, at the vacant divisor `gap₀ - gap₀`, whose
radius clears at every point while both side reads part with the
sum's unit, so the side conjunct carries the nonvacancy.
-/
open ground chaininstances

private def fam (i : Nat) : Fam :=
  ground.getAt ⟨[], [], 0, 0, 0, false, 0⟩ fams i

/-- The rank-`k` pair, the balance carrier's own read of the
count. -/
private def rk (k : Nat) : BPair :=
  ⟨ground.posOfSucc k, ground.posOfSucc 0⟩

/-- A family's excess gap at its place. -/
private def gd (i : Nat) : poly.Poly := gapOf (fam i)

/-- A frontier-binding comparison at its two places. -/
private def pd (i j : Nat) : poly.Poly :=
  poly.add (gd i) (poly.neg (gd j))

/-! The whole read: the record count, the families' cleared reads,
and both certificates over the 37 records. -/

example : recsRead := by decide +kernel

/-! The classification's five rows, one cross-multiplied
evaluation each: `ω₃+ω₂*`'s gap at the rank two, then the four
binding pairs at their stated ranks. -/

example : (poly.eval (gd 2) (rk 2)).oneValue BPair.unit := by
  decide +kernel
example : (poly.eval (pd 0 2) (rk 3)).oneValue BPair.unit := by
  decide +kernel
example : (poly.eval (pd 1 3) (rk 3)).oneValue BPair.unit := by
  decide +kernel
example : (poly.eval (pd 2 3) (rk 5)).oneValue BPair.unit := by
  decide +kernel
example : (poly.eval (pd 3 5) (rk 2)).oneValue BPair.unit := by
  decide +kernel

/-! The gap witness's refusal: the family `ω₂+ω₁*`'s row at the
forged shift `s := 2`, the gap `2n g` at `2 + g = n`, parts with
the cleared read at `rankstable.casPoly`. -/

example : ¬ gapRead ⟨[0, 1], [1], 2, 1, 2, false, 6⟩ := by
  decide +kernel

/-! The root list's refusals at the comparison
`(ω₂+ω₁*, ω₃+ω₂*)`, settled at eight: the rank three's withdrawal
leaves an equal-members read uncounted, and the rank four forged
onto the list counts a rank whose evaluation clears the sum's
unit. -/

example : ¬ rootsCert ⟨pd 0 2, 2, 8, 8, []⟩ := by decide +kernel
example : ¬ rootsCert ⟨pd 0 2, 2, 8, 8, [3, 4]⟩ := by decide +kernel

/-! The clearance's refusal at the same comparison: lowered to two
it asks the leading side of every windowed rank off the root, and
the rank two sits on the divisor's other side, below the crossing;
the committed clearance eight keeps the below-clearance ranks at
the off-unit read alone. -/

example : ¬ rootsCert ⟨pd 0 2, 2, 2, 8, [3]⟩ := by decide +kernel
example : rootsCert ⟨pd 0 2, 2, 8, 8, [3]⟩ := by decide +kernel

/-! The settled point's refusal at the comparison
`(ω₂+ω₁*, 3ω₁+2ω₁*)`, whose radius is six: read at three the
clearance conjunct refuses, and at six it holds. -/

example : ¬ sideCert ⟨pd 0 6, 2, 3, 3, []⟩ := by decide +kernel
example : genericlift.radiusClears (pd 0 6) (ground.posOfSucc 5) := by
  decide +kernel

/-! The leading side's refusal at the vacant divisor
`gap₀ - gap₀`: its radius clears at the settled point while both
side reads sit at the sum's unit, so the side conjunct is the
nonvacancy's own binder. -/

example : genericlift.radiusClears (pd 0 0) (ground.posOfSucc 5) := by
  decide +kernel
example : ¬ genericlift.topUpper (pd 0 0) := by decide +kernel
example : ¬ genericlift.topLower (pd 0 0) := by decide +kernel
example : ¬ sideCert ⟨pd 0 0, 2, 6, 6, []⟩ := by decide +kernel
