import MassGap.Unitschain
/-!
`thm:twoaction` — the invariant clause: the invariant is fixed
under the scheme bridge, the rescaling `b_f^equiv = 2 d_f b_X` of
the coupling coordinate (`thm:bridge`) acting on the base with the
two ends its fixed points (`unitschain.bridge_fixed` at the
member's coefficient, `invariant_fixed`), so the two families'
invariants read one pair, the contact pair at the ends' own values
(`thm:closing`); the comparison at the corner outputs runs at the
families' certificates (`lem:corner`): `compare_bracket` reads each
output's comparison as one bracket at the two families'
certificates, the two members' brackets cross-added, finite and
decidable at the pair carrier's order.
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

/-- A corner output's comparison at the two families is one bracket
at their certificates: with each family's output between its
certificate's two ends, the comparison sits between the cross-added
ends, the lower end of one against the upper of the other, both
reads the certificates' own. -/
theorem compare_bracket (l h l' h' x x' : CPair)
    (hl : l ≤ x) (hh : x ≤ h) (hl' : l' ≤ x') (hh' : x' ≤ h') :
    l + x' ≤ x + h' ∧ x + l' ≤ h + x' :=
  ⟨CPair.le_add hl hh', CPair.le_add hh hl'⟩

end twoaction
