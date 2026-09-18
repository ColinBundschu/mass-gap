import MassGap.Stagebox
/-!
The check module for `lem:stage`'s box read: the batteries re-read
the priced side read on a box by kernel `decide` — at `5 + t + s` on
the box `[0, 1] × [0, 1]` at the bounds `[1 : 1]`, the read decided
at its two tops one and one, the side kept at the interior point
`(1/2, 1/2)` through the theorem (`keepUpperBox_all`), and each
binder refused on its own: the inner bound's clearing at the sum's
unit, the inner bracket at equal ends, the inner bound refused at a
bracket reaching two, the outer bound's clearing and bracket so, and
the price at `1 - 4t + s`, whose value crosses on the box; the lower
read at `-5 + t + s` decided with the interior point through its
theorem (`keepLowerBox_all`); and the read at a box off the origin
with the inner top two, `3 + t² + s` on `[1/2, 1] × [0, 1/2]` at the
bounds `[1 : 1]` and `[1 : 2]`, decided with the interior point
`(3/4, 1/4)` through the theorem (the value `61` there) and the
inner bound refused at the clearing two.  Beside them the composite
order kit at signed instances: a member under a second joined to
their difference's magnitude, the strict read's right factor, the
magnitude at the memberwise swap, and the swap's product read. -/

namespace stage
set_option maxHeartbeats 4000000

open ground poly windowsep

private def u : BPair := BPair.unit

/-- `5 + t + s`. -/
private def pA : PPoly := [[BPair.ofNat 5, BPair.ofNat 1], [BPair.ofNat 1]]
/-- `-5 + t + s`. -/
private def pB : PPoly := [[(BPair.ofNat 5).swap, BPair.ofNat 1], [BPair.ofNat 1]]
/-- `1 - 4t + s`. -/
private def pC : PPoly := [[BPair.ofNat 1, (BPair.ofNat 4).swap], [BPair.ofNat 1]]
/-- `3 + t² + s`. -/
private def pD : PPoly := [[BPair.ofNat 3, u, BPair.ofNat 1], [BPair.ofNat 1]]

private def c0 : CPair := ⟨u, 1⟩
private def c1 : CPair := ⟨BPair.ofNat 1, 1⟩
private def c2 : CPair := ⟨BPair.ofNat 2, 1⟩
private def half : CPair := ⟨BPair.ofNat 1, 2⟩

/-! The read at `5 + t + s` on the unit box at its two tops, decided,
with the side kept at the interior point through the theorem. -/

theorem pin84 : innerTop pA = 1 := by decide +kernel
theorem pin85 : outerTop pA = 1 := by decide +kernel
theorem pin86 : keepUpperBox pA c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin87 : unitC < evalC (innerC pA half) half := by decide +kernel
theorem pin88 : unitC < evalC (innerC pA half) half :=
  keepUpperBox_all pA c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) pin86 half half
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! Each binder refused on its own. -/

theorem pin89 : ¬ keepUpperBox pA c0 c1 c0 c1 (BPair.ofNat 1) u
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin90 : ¬ keepUpperBox pA c0 c0 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin91 : ¬ keepUpperBox pA c0 c2 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin92 : ¬ keepUpperBox pA c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) u := by decide +kernel
theorem pin93 : ¬ keepUpperBox pA c0 c1 c0 c0 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin94 : ¬ keepUpperBox pA c0 c1 c0 c2 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin95 : ¬ keepUpperBox pC c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin96 : evalC (innerC pC c1) c0 < unitC := by decide +kernel

/-! The lower read at `-5 + t + s`, decided, with the interior point
through the theorem. -/

theorem pin97 : keepLowerBox pB c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
theorem pin98 : evalC (innerC pB half) half < unitC := by decide +kernel
theorem pin99 : evalC (innerC pB half) half < unitC :=
  keepLowerBox_all pB c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) pin97 half half
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin100 : ¬ keepLowerBox pA c0 c1 c0 c1 (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel

/-! The read off the origin at the inner top two: `3 + t² + s` on
`[1/2, 1] × [0, 1/2]` at the bounds `[1 : 1]` and `[1 : 2]`. -/

private def q34 : CPair := ⟨BPair.ofNat 3, 4⟩
private def q14 : CPair := ⟨BPair.ofNat 1, 4⟩

theorem pin101 : innerTop pD = 2 := by decide +kernel
theorem pin102 : keepUpperBox pD half c1 c0 half (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 2) := by decide +kernel
theorem pin103 : unitC < evalC (innerC pD q34) q14 :=
  keepUpperBox_all pD half c1 c0 half (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 2) pin102 q34 q14
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin104 : (evalC (innerC pD q34) q14).oneValue ⟨BPair.ofNat 61, 1⟩ := by
  decide +kernel
theorem pin105 : ¬ keepUpperBox pD half c1 c0 half (BPair.ofNat 1) (BPair.ofNat 2)
    (BPair.ofNat 1) (BPair.ofNat 2) := by decide +kernel

/-! The composite order kit at signed instances. -/

private def m2 : CPair := ⟨(BPair.ofNat 2).swap, 1⟩
private def p3h : CPair := ⟨BPair.ofNat 3, 2⟩

theorem pin106 : p3h ≤ m2 + cmag (m2 + CPair.swap p3h) := by decide +kernel
theorem pin107 : m2 ≤ p3h + cmag (p3h + CPair.swap m2) := by decide +kernel
theorem pin108 : m2 * p3h < c1 * p3h := by decide +kernel
theorem pin109 : m2 * p3h < c1 * p3h := ltC_mul_right (by decide +kernel) (by decide +kernel)
theorem pin110 : (cmag (CPair.swap m2)).oneValue (cmag m2) := by decide +kernel
theorem pin111 : (cmag (CPair.swap p3h)).oneValue ⟨BPair.ofNat 3, 2⟩ := by decide +kernel
theorem pin112 : (m2 + CPair.swap m2).oneValue unitC := by decide +kernel
theorem pin113 : unitC < CPair.swap m2 * CPair.swap m2 :=
  unitC_lt_mul (by decide +kernel) (by decide +kernel)
theorem pin114 : (CPair.swap m2 * p3h) = CPair.swap (m2 * p3h) := CPair.swap_mul m2 p3h
theorem pin115 : ofB (BPair.ofNat 2) ≤ ofB (BPair.ofNat 3) := ofB_le (by decide +kernel)

end stage
