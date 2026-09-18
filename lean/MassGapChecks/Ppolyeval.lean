import MassGap.Ppolyeval
/-!
The check module for `def:poly`'s outer evaluation and two
derivatives at composite points, at `P(t, s) = (1 + 2t) + (3 + t) s`,
the inner variable `t` and the outer `s`: the outer derivative
`(3 + t)` and the inner derivative `2 + s` at their evaluations,
decided and through the theorems, the outer derivative keeping the
inner-degree cap, the outer evaluation at `s = 3` (`10 + 5t`) within
the cap, the two evaluations' meet at `(t, s) = (2, 3)` (the value
`20` either way) decided and through the theorem, the outer
evaluation of the inner derivative against the derivative of the
outer evaluation, and the derivative of a rescaling with the
key-count reads.  Integers enter as one-member balance data,
`BPair.ofNat n`. -/

namespace poly
set_option maxHeartbeats 4000000

open ground

private def u : BPair := BPair.unit

/-- `(1 + 2t) + (3 + t) s`. -/
private def P : PPoly := [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3, BPair.ofNat 1]]

/-! The two derivatives at their evaluations, and the outer
derivative's inner-degree cap. -/

theorem pin135 : ppOneValue (derivOuter P) [[BPair.ofNat 3, BPair.ofNat 1]] := by
  decide +kernel
theorem pin136 : ppOneValue (derivInner P) [[BPair.ofNat 2], [BPair.ofNat 1]] := by
  decide +kernel
theorem pin137 : oneValue (pevalCP (derivOuter P) (BPair.ofNat 2) 1 1)
    (deriv (pevalCP P (BPair.ofNat 2) 1 1)) := by decide +kernel
theorem pin138 : oneValue (pevalCP (derivOuter P) (BPair.ofNat 3) 2 1)
    (deriv (pevalCP P (BPair.ofNat 3) 2 1)) :=
  pevalCP_derivOuter P (BPair.ofNat 3) 2 1
theorem pin139 : innerLe (derivOuter P) 1 := by decide +kernel
theorem pin140 : innerLe (derivOuter P) 1 := innerLe_derivOuter (by decide +kernel)
theorem pin141 : (derivInner P).length = P.length := by decide +kernel

/-! The outer evaluation at `s = 3` within the inner cap, and the
two evaluations' meet at `(2, 3)`, the value `20` either way. -/

theorem pin142 : oneValue (pevalOuter P (BPair.ofNat 3) 1 1)
    [BPair.ofNat 10, BPair.ofNat 5] := by decide +kernel
theorem pin143 : (pevalOuter P (BPair.ofNat 3) 1 1).length ≤ 1 + 1 := by decide +kernel
theorem pin144 : (pevalOuter P (BPair.ofNat 3) 1 1).length ≤ 1 + 1 :=
  length_pevalOuter_le (by decide +kernel) (BPair.ofNat 3) 1 1
theorem pin145 : (evalClear (pevalOuter P (BPair.ofNat 3) 1 1) (BPair.ofNat 2) 1 1).oneValue
    (BPair.ofNat 20) := by decide +kernel
theorem pin146 : (evalClear (pevalOuter P (BPair.ofNat 3) 1 1) (BPair.ofNat 2) 1 1).oneValue
    (evalClear (pevalCP P (BPair.ofNat 2) 1 1) (BPair.ofNat 3) 1 1) := by decide +kernel
theorem pin147 : (evalClear (pevalOuter P (BPair.ofNat 7) 2 1) (BPair.ofNat 3) 2 1).oneValue
    (evalClear (pevalCP P (BPair.ofNat 3) 2 1) (BPair.ofNat 7) 2 1) :=
  pevalOuter_pevalCP P (BPair.ofNat 7) 2 1 (BPair.ofNat 3) 2 1

/-! The outer evaluation of the inner derivative against the
derivative of the outer evaluation, decided and through the theorem,
and the derivative of a rescaling with the key-count reads. -/

theorem pin148 : oneValue (pevalOuter (derivInner P) (BPair.ofNat 3) 1 1)
    (deriv (pevalOuter P (BPair.ofNat 3) 1 1)) := by decide +kernel
theorem pin149 : oneValue (pevalOuter (derivInner P) (BPair.ofNat 7) 2 1)
    (deriv (pevalOuter P (BPair.ofNat 7) 2 1)) :=
  pevalOuter_derivInner P (BPair.ofNat 7) 2 1
theorem pin150 : oneValue (deriv (scaleP (BPair.ofNat 3) [BPair.ofNat 1, BPair.ofNat 2, u, BPair.ofNat 4]))
    (scaleP (BPair.ofNat 3) (deriv [BPair.ofNat 1, BPair.ofNat 2, u, BPair.ofNat 4])) := by
  decide +kernel
theorem pin151 : (deriv [BPair.ofNat 1, BPair.ofNat 2, u, BPair.ofNat 4]).length
    ≤ ([BPair.ofNat 1, BPair.ofNat 2, u, BPair.ofNat 4] : Poly).length := by decide +kernel
theorem pin152 : (vnorm (deriv [BPair.ofNat 1, BPair.ofNat 2, u, BPair.ofNat 4])).length
    ≤ ([BPair.ofNat 1, BPair.ofNat 2, u, BPair.ofNat 4] : Poly).length := by decide +kernel

end poly
