import MassGap.Unitschain
/-!
`thm:twoaction` — the invariant clause: the invariant is fixed
under the scheme bridge, the rescaling `b_f^equiv = 2 d_f b_X` of
the coupling coordinate (`thm:bridge`) acting on the base with the
two ends its fixed points (`unitschain.bridge_fixed` at the
member's coefficient, `invariant_fixed`), so the two families'
invariants read one pair, the contact pair at the ends' own values
(`thm:closing`); the comparison at the corner outputs runs at the
families' certificates (`lem:corner`).
-/

namespace twoaction
open ground segment

/-- The unit sits below every doubled carrier member: the factor's
growth at the product's monotone read, the trichotomy closing the
seed. -/
private theorem one_lt_two_mul (x : Pos) : (1 : Pos) < 2 * x :=
  have hx2 : x < 2 * x := by
    have h2 := ground.mul_lt_mul_right x
      (show (1 : Pos) < 2 by decide +kernel)
    rw [show (1 : Pos) * x = x from ground.one_mul x] at h2
    exact h2
  match ground.trich 1 x with
  | .eq e => e ▸ hx2
  | .lt g hg => ground.lt_trans (⟨g, hg⟩ : (1 : Pos) < x) hx2
  | .gt g hg => absurd (⟨g, hg⟩ : x < 1) (ground.not_lt_one x)

/-- The bridge's rescaling at the member's own coefficient
`2 d_f` fixes exactly the two ends of the base, every interior ray
moved — the characterization's instance at the coefficient, the
invariant's reads taken at the ends (`thm:closing`). -/
theorem ends_fixed (r : Nat) (c : Coupling) :
    rayEq c (unitschain.bridgeMap (2 * posOfSucc r) c)
      ↔ (c = .free ∨ c = .contact) :=
  unitschain.bridge_fixed (2 * posOfSucc r)
    (one_lt_two_mul (posOfSucc r)) c

end twoaction
