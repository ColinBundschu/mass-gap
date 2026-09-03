import MassGap.Twoaction
/-!
The check module for `thm:twoaction`'s invariant clause: the
bridge's coefficient `2 d_f` at committed residues fixes the two
ends and moves every interior pair, each read routed through the
characterization's member instance; and the corner outputs'
comparison bracket (`compare_bracket`) at the certificates
`[1, 3]` about the output `2` and `[1/2, 2]` about `1`, the
cross-added ends decided beside the route, with each of the four
ends load-bearing at the output `5` beyond its certificate. -/

open ground segment twoaction

example : rayEq .free (unitschain.bridgeMap (2 * posOfSucc 1) .free) := by
  decide +kernel
example : rayEq .free (unitschain.bridgeMap (2 * posOfSucc 1) .free) :=
  (ends_fixed 1 .free).mpr (Or.inl rfl)
example : rayEq .contact
    (unitschain.bridgeMap (2 * posOfSucc 2) .contact) := by
  decide +kernel
example : rayEq .contact
    (unitschain.bridgeMap (2 * posOfSucc 2) .contact) :=
  (ends_fixed 2 .contact).mpr (Or.inr rfl)
example : ¬ rayEq (.mid 3 7)
    (unitschain.bridgeMap (2 * posOfSucc 1) (.mid 3 7)) := by
  decide +kernel
example : ¬ rayEq (.mid 3 7)
    (unitschain.bridgeMap (2 * posOfSucc 1) (.mid 3 7)) :=
  fun h => ((ends_fixed 1 (.mid 3 7)).mp h).elim
    (fun h1 => Coupling.noConfusion h1)
    (fun h2 => Coupling.noConfusion h2)

/-! ## The corner outputs' comparison bracket -/

private def c1 : CPair := ⟨BPair.ofNat 1, 1⟩
private def c2 : CPair := ⟨BPair.ofNat 2, 1⟩
private def c3 : CPair := ⟨BPair.ofNat 3, 1⟩
private def cHalf : CPair := ⟨BPair.ofNat 1, 2⟩
private def c5 : CPair := ⟨BPair.ofNat 5, 1⟩

example : c1 + c1 ≤ c2 + c2 ∧ c2 + cHalf ≤ c3 + c1 := by decide +kernel
example : c1 + c1 ≤ c2 + c2 ∧ c2 + cHalf ≤ c3 + c1 :=
  compare_bracket c1 c3 cHalf c2 c2 c1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The second family's upper end is load-bearing: at the output `5`
beyond the certificate `[1/2, 2]` the first cross-added read
parts, `1 + 5` against `2 + 2`. -/
example : ¬ (c1 + c5 ≤ c2 + c2) := by decide +kernel
example : ¬ (c5 ≤ c2) := by decide +kernel

/-- The first family's lower end is load-bearing: at `5` beyond the
output `2` the first read parts, `5 + 1` against `2 + 2`. -/
example : ¬ (c5 ≤ c2) ∧ ¬ (c5 + c1 ≤ c2 + c2) := by decide +kernel
/-- The first family's upper end is load-bearing: at the output `5`
beyond `3` the second read parts, `5 + 1` against `3 + 1`. -/
example : ¬ (c5 ≤ c3) ∧ ¬ (c5 + c1 ≤ c3 + c1) := by decide +kernel
/-- The second family's lower end is load-bearing: at `5` beyond the
output `1` the second read parts, `2 + 5` against `3 + 1`. -/
example : ¬ (c5 ≤ c1) ∧ ¬ (c2 + c5 ≤ c3 + c1) := by decide +kernel
