import MassGap.Ppolyfold
/-!
The check module for `thm:windowsep`'s two-variable fold: the
batteries re-read the fold of `(1 + 2t) + (3 + t) s` at the bounds
`[2 : 1]` and `[3 : 1]` and the powers one and one (`20`) by kernel
`decide`, and the two evaluations' folds within it, the inner
evaluation's at `t = 3/2` and the outer's at `s = 1/2`, each decided
and through its theorem, with the inner-degree and outer-degree
binders refused at forged powers and the point binders refused past
the bounds.  Integers enter as one-member balance data,
`BPair.ofNat n`. -/

namespace windowsep
set_option maxHeartbeats 4000000

open ground poly

/-- `(1 + 2t) + (3 + t) s`. -/
private def P : PPoly := [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3, BPair.ofNat 1]]

/-! The two-variable fold at the two bounds and the two powers: the
inner folds `5` and `5`, the outer fold `5 + 3·5 = 20`. -/

theorem pin91 : (foldOuterK P (BPair.ofNat 2) (BPair.ofNat 1) 1 (BPair.ofNat 3) (BPair.ofNat 1) 1).oneValue
    (BPair.ofNat 20) := by decide +kernel

/-! The inner evaluation's fold at `t = 3/2` within the two-variable
fold, decided and through the theorem; the inner-degree binder
refused at the power nought and the point binder past the bound. -/

theorem pin92 : foldK (pevalCP P (BPair.ofNat 3) 2 1) (BPair.ofNat 3) (BPair.ofNat 1) 1
      * bpow (BPair.ofNat 1) 1
    ≤ foldOuterK P (BPair.ofNat 2) (BPair.ofNat 1) 1 (BPair.ofNat 3) (BPair.ofNat 1) 1
      * bpow (BPair.ofPos 2) 1 := by decide +kernel
theorem pin93 : foldK (pevalCP P (BPair.ofNat 3) 2 1) (BPair.ofNat 3) (BPair.ofNat 1) 1
      * bpow (BPair.ofNat 1) 1
    ≤ foldOuterK P (BPair.ofNat 2) (BPair.ofNat 1) 1 (BPair.ofNat 3) (BPair.ofNat 1) 1
      * bpow (BPair.ofPos 2) 1 :=
  foldK_pevalCP P (BPair.ofNat 3) 2 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 1
theorem pin94 : ¬ innerLe P 0 := by decide +kernel
theorem pin95 : ¬ (mag (BPair.ofNat 5) * BPair.ofNat 1 ≤ BPair.ofNat 2 * BPair.ofPos 2) := by
  decide +kernel

/-! The outer evaluation's fold at `s = 1/2` within the two-variable
fold, decided and through the theorem; the outer-degree binder
refused at the power nought and the point binder past the bound. -/

theorem pin96 : foldK (pevalOuter P (BPair.ofNat 1) 2 1) (BPair.ofNat 2) (BPair.ofNat 1) 1
      * bpow (BPair.ofNat 1) 1
    ≤ foldOuterK P (BPair.ofNat 2) (BPair.ofNat 1) 1 (BPair.ofNat 3) (BPair.ofNat 1) 1
      * bpow (BPair.ofPos 2) 1 := by decide +kernel
theorem pin97 : foldK (pevalOuter P (BPair.ofNat 1) 2 1) (BPair.ofNat 2) (BPair.ofNat 1) 1
      * bpow (BPair.ofNat 1) 1
    ≤ foldOuterK P (BPair.ofNat 2) (BPair.ofNat 1) 1 (BPair.ofNat 3) (BPair.ofNat 1) 1
      * bpow (BPair.ofPos 2) 1 :=
  foldK_pevalOuter P (BPair.ofNat 1) 2 1 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin98 : ¬ (P.length ≤ 0 + 1) := by decide +kernel
theorem pin99 : ¬ (mag (BPair.ofNat 7) * BPair.ofNat 1 ≤ BPair.ofNat 3 * BPair.ofPos 2) := by
  decide +kernel

/-! The magnitude domination: `−2 + 3t` under `2 + 3t` key by key,
refused against `1 + 3t`, and the cleared evaluation's magnitude at
the positive point `[1 : 2]` capped by the dominating list's own,
decided and through its theorem; at the lower-side point `−1` the
cap's shape refuses at `t`. -/

private def pM : Poly := [⟨1, 3⟩, BPair.ofNat 3]
private def qM : Poly := [BPair.ofNat 2, BPair.ofNat 3]

theorem pin100 : magDom pM qM := by decide +kernel
theorem pin101 : ¬ magDom pM [BPair.ofNat 1, BPair.ofNat 3] := by decide +kernel
theorem pin102 : mag (poly.evalClear pM (BPair.ofPos 1) 2 1)
    ≤ poly.evalClear qM (BPair.ofPos 1) 2 1 := by decide +kernel
theorem pin103 : mag (poly.evalClear pM (BPair.ofPos 1) 2 1)
    ≤ poly.evalClear qM (BPair.ofPos 1) 2 1 :=
  evalClear_magDom (BPair.ofPos 1) (by decide +kernel) 2 1 (by decide +kernel)
theorem pin104 : ¬ (mag (poly.evalClear [BPair.unit, BPair.ofNat 1] ⟨1, 2⟩ 1 1)
    ≤ poly.evalClear [BPair.unit, BPair.ofNat 1] ⟨1, 2⟩ 1 1) := by decide +kernel

end windowsep
