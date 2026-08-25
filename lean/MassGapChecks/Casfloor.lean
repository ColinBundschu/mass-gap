import MassGap.Casfloor
/-!
The check module for `lem:casfloor`'s member floors: the batteries
re-read the end lists by kernel `decide` at all twelve committed
members — the cleared folds' coroot witnesses (`endsRead`), the
displayed evaluations at the cross-multiplied reads (`c2Read`, the
series' displayed pairs, the fixed members' displayed minima, and
the `θ` entries at level one, the denominator's own coherence), and
the member floors as the lists' trichotomy least (`floorRead` at the
displayed floors, the `B` trichotomy's exchange between the spinor
and the vector across `ℓ = 3, 4` and the `D` equality at `ℓ = 4`
among them).  A fixed member's reads join in one `decide` — its
positive list is the descent's output, and one forcing per member
prices the module (the pointer-keyed sharing at the one table
constant).  The `A`-series reads at the shapes: the endpoint
display's instances (`endpointRead`), and the crown coherence of the
fold route against `def:c2hat`'s cleared bracket at the shared
instances, the first adjugate row's fold at the fundamental's
shape.  The descent's pins close the module: the general floor and
its sharpness at committed shapes with the theorems' own instances
beside the decided values, the fall identity at the `θ`-to-unit
move, `θ`'s read, the endpoint theorem at a fresh key pair, and
the hypothesis boundary's value reads below the floor.  The unit
class's own floor closes the module: `θ`'s class attaining `2 d_f²`
exactly, a wider unit-class shape above it, and the class, the
occupancy, the reduction and the width each forged in turn
against the conclusion.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground gentable sertables casfloor

/-! The cleared folds' coroot witnesses, one read per entry. -/

example : endsRead (tableB 2) (endsB 0) := by decide +kernel
example : endsRead (tableB 3) (endsB 1) := by decide +kernel
example : endsRead (tableB 4) (endsB 2) := by decide +kernel
example : endsRead (tableC 3) (endsC 0) := by decide +kernel
example : endsRead (tableC 4) (endsC 1) := by decide +kernel
example : endsRead (tableD 4) (endsD 0) := by decide +kernel
example : endsRead (tableD 5) (endsD 1) := by decide +kernel

private def at0 : List EndFold → Nat → EndFold := getAt ⟨[], 1, []⟩

/-! The series' displayed evaluations: the vector `[ℓ : r+1]` and
the spinor `[ℓ(2ℓ+1) : 8(r+1)]` at `B`, the first fundamental
`[2r+1 : 4(r+1)]` with the short dominant root's `[r : r+1]` at
`C`, and the vector `[r+2 : 2(r+1)]` with the spinors'
`[ℓ(r+2) : 8(r+1)]` at `D`. -/

example : c2Read (tableB 2) (at0 (endsB 0) 0) 2 3 := by decide +kernel
example : c2Read (tableB 2) (at0 (endsB 0) 1) 10 24 := by decide +kernel
example : c2Read (tableB 3) (at0 (endsB 1) 0) 3 5 := by decide +kernel
example : c2Read (tableB 3) (at0 (endsB 1) 1) 21 40 := by decide +kernel
example : c2Read (tableB 4) (at0 (endsB 2) 0) 4 7 := by decide +kernel
example : c2Read (tableB 4) (at0 (endsB 2) 1) 36 56 := by decide +kernel
example : c2Read (tableC 3) (at0 (endsC 0) 0) 7 16 := by decide +kernel
example : c2Read (tableC 3) (at0 (endsC 0) 1) 3 4 := by decide +kernel
example : c2Read (tableC 4) (at0 (endsC 1) 0) 9 20 := by decide +kernel
example : c2Read (tableC 4) (at0 (endsC 1) 1) 4 5 := by decide +kernel
example : c2Read (tableD 4) (at0 (endsD 0) 0) 7 12 := by decide +kernel
example : c2Read (tableD 4) (at0 (endsD 0) 1) 28 48 := by decide +kernel
example : c2Read (tableD 4) (at0 (endsD 0) 2) 28 48 := by decide +kernel
example : c2Read (tableD 5) (at0 (endsD 1) 0) 9 16 := by decide +kernel
example : c2Read (tableD 5) (at0 (endsD 1) 1) 45 64 := by decide +kernel
example : c2Read (tableD 5) (at0 (endsD 1) 2) 45 64 := by decide +kernel

/-! The series' `θ` entries at level one, the denominator's
coherence with the form and residue reads. -/

example : c2Read (tableB 2) (at0 (endsB 0) 2) 1 1 := by decide +kernel
example : c2Read (tableB 3) (at0 (endsB 1) 2) 1 1 := by decide +kernel
example : c2Read (tableB 4) (at0 (endsB 2) 2) 1 1 := by decide +kernel
example : c2Read (tableC 3) (at0 (endsC 0) 2) 1 1 := by decide +kernel
example : c2Read (tableC 4) (at0 (endsC 1) 2) 1 1 := by decide +kernel
example : c2Read (tableD 4) (at0 (endsD 0) 3) 1 1 := by decide +kernel
example : c2Read (tableD 5) (at0 (endsD 1) 3) 1 1 := by decide +kernel

/-! The series' floors, the lists' trichotomy least at the
displayed pairs: the `B` least exchanges from the spinor to the
vector across `ℓ = 3, 4`, and the `D` equality at `ℓ = 4` attains
at the vector and the spinors at once. -/

example : floorRead (tableB 2) (endsB 0) 10 24 := by decide +kernel
example : floorRead (tableB 3) (endsB 1) 21 40 := by decide +kernel
example : floorRead (tableB 4) (endsB 2) 4 7 := by decide +kernel
example : floorRead (tableC 3) (endsC 0) 7 16 := by decide +kernel
example : floorRead (tableC 4) (endsC 1) 9 20 := by decide +kernel
example : floorRead (tableD 4) (endsD 0) 7 12 := by decide +kernel
example : floorRead (tableD 5) (endsD 1) 9 16 := by decide +kernel

/-! The fixed members, one forcing per member (a fixed table's
positive list is its descent's output, so a member's reads join in
one `decide`): the coroot witnesses, the displayed minima, the `θ`
entry at level one, and the floor as the fundamental list's
trichotomy least. -/

example : endsRead tableG2 endsG2
    ∧ c2Read tableG2 (at0 endsG2 0) 1 2
    ∧ c2Read tableG2 (at0 endsG2 1) 1 1
    ∧ floorRead tableG2 endsG2 1 2 := by decide +kernel

example : endsRead tableF4 endsF4
    ∧ c2Read tableF4 (at0 endsF4 3) 2 3
    ∧ c2Read tableF4 (at0 endsF4 0) 1 1
    ∧ floorRead tableF4 endsF4 2 3 := by decide +kernel

example : endsRead tableE6 endsE6
    ∧ c2Read tableE6 (at0 endsE6 0) 13 18
    ∧ c2Read tableE6 (at0 endsE6 5) 13 18
    ∧ c2Read tableE6 (at0 endsE6 1) 1 1
    ∧ floorRead tableE6 endsE6 13 18 := by decide +kernel

example : endsRead tableE7 endsE7
    ∧ c2Read tableE7 (at0 endsE7 6) 19 24
    ∧ c2Read tableE7 (at0 endsE7 0) 1 1
    ∧ floorRead tableE7 endsE7 19 24 := by decide +kernel

example : endsRead tableE8 endsE8
    ∧ c2Read tableE8 (at0 endsE8 7) 1 1
    ∧ floorRead tableE8 endsE8 1 1 := by decide +kernel

/-! The `A`-series' endpoint display at the shapes,
`d_f Q(ω_j) = j g_j (r+2)`, the fundamental and its complement the
least ends. -/

example : endpointRead 1 1 := by decide +kernel
example : endpointRead 1 2 := by decide +kernel
example : endpointRead 2 1 := by decide +kernel
example : endpointRead 2 2 := by decide +kernel
example : endpointRead 3 2 := by decide +kernel
example : endpointRead 2 3 := by decide +kernel
example : endpointRead 1 5 := by decide +kernel
example : endpointRead 5 1 := by decide +kernel

/-! The crown coherence at the shared `A` instances: the fold route
at the first adjugate row against `def:c2hat`'s cleared bracket at
the fundamental's shape, the two routes' one value. -/

example : corootRead (tableA 2) ⟨[2, 1], 3, [1, 0]⟩ := by decide +kernel
example : c2Read (tableA 2) ⟨[2, 1], 3, [1, 0]⟩
    (c2hat.dfQ [1, 0, 0]) (2 * 3 * 3) := by decide +kernel
example : corootRead (tableA 3) ⟨[3, 2, 1], 4, [1, 0, 0]⟩ := by decide +kernel
example : c2Read (tableA 3) ⟨[3, 2, 1], 4, [1, 0, 0]⟩
    (c2hat.dfQ [1, 0, 0, 0]) (2 * 4 * 4) := by decide +kernel

/-! The descent's pins (`lem:casfloor`'s general floor): the floor
at committed shapes with the theorems' own instances beside the
decided values, the fall identity at the `θ`-to-unit move, `θ`'s
read, the endpoint theorem at a fresh key pair, and the two
attained shapes; the value reads at `[0, 0, 1]` (a full column,
`hred` the refusing clause) and the unit shape (`hocc`) sit below
the floor, the hypotheses' committed boundary; the walk's
move-short-of-the-last-key carrier `[0, 2, 0, 0]` and the interior
endpoint's strict clearance (`fundShape 2 2` at `20` against the
floor `15`) pin the two further arms. -/

example : c2hat.dfQ [1, 1, 0] = 18 := by decide +kernel
example : 2 * (2 + 2) ≤ c2hat.dfQ [1, 1, 0] :=
  floorAll 2 [1, 1, 0] rfl rfl (by decide +kernel)
example : c2hat.dfQ [2, 0, 1, 0] = 55 := by decide +kernel
example : 3 * (3 + 2) ≤ c2hat.dfQ [2, 0, 1, 0] :=
  floorAll 3 [2, 0, 1, 0] rfl rfl (by decide +kernel)
example : 1 * (1 + 2) ≤ c2hat.dfQ [1, 0] :=
  floorAll 1 [1, 0] rfl rfl (by decide +kernel)

example : c2hat.dfQ (fundShape 1 2) = 2 * (2 + 2) := by decide +kernel
example : c2hat.dfQ (fundShape 2 1) = 2 * (2 + 2) := by decide +kernel
example : ([1, 0, 0] : places.Shape) = fundShape 1 2
    ∨ [1, 0, 0] = fundShape 2 1 :=
  floorSharp 2 [1, 0, 0] rfl rfl (by decide +kernel) (by decide +kernel)
example : ([1, 0] : places.Shape) = fundShape 1 1
    ∨ [1, 0] = fundShape 1 1 :=
  floorSharp 1 [1, 0] rfl rfl (by decide +kernel) (by decide +kernel)

example : c2hat.dfQ [0, 0, 1] = 0 := by decide +kernel
example : c2hat.dfQ [0, 0, 0] = 0 := by decide +kernel

example : c2hat.dfQ [1, 1, 0] + 3 * (0 + 1)
    = c2hat.dfQ [0, 0, 1] + 3 * (2 + 1) + 2 * 3 * 2 := by decide +kernel
example : c2hat.dfQ [1, 1, 0] + 3 * (0 + 1)
    = c2hat.dfQ [0, 0, 1] + 3 * (2 + 1) + 2 * 3 * 2 :=
  boxFall [1, 1, 0] [0, 0, 1] 0 2 rfl rfl rfl
    (by decide +kernel)
example : c2hat.dfQ [0, 0, 1] < c2hat.dfQ [1, 1, 0] :=
  fallStrict [1, 1, 0] [0, 0, 1] 0 2 rfl rfl rfl
    (by decide +kernel)

example : c2hat.dfQ (adjchar.theta 4) = 32 := by decide +kernel
example : c2hat.dfQ (adjchar.theta 4) = 2 * 4 * 4 :=
  thetaRead 2

example : endpointRead 4 3 := endpointAll 4 3
example : c2hat.dfQ (fundShape 4 3) = 96 := by decide +kernel

example : c2hat.dfQ [0, 2, 0, 0] = 48 := by decide +kernel
example : 3 * (3 + 2) ≤ c2hat.dfQ [0, 2, 0, 0] :=
  floorAll 3 [0, 2, 0, 0] rfl rfl (by decide +kernel)

example : c2hat.dfQ (fundShape 2 2) = 20 := by decide +kernel
example : endpointRead 2 2 := endpointAll 2 2

/-! The unit class's own floor: an occupied reduced shape whose
degree reads the unit class clears `2 d_f²`.  `θ`'s class at
`d_f = 3` reads the bound exactly, a wider unit-class shape sits
above it, and the three further binders are forged one at a time —
the class, the occupancy, the reduction — each with the others
standing and each moving the conclusion. -/

example : places.degree [1, 1, 0] % (2 + 1) = 0 := by decide +kernel
example : 2 * ((2 + 1) * (2 + 1)) = c2hat.dfQ [1, 1, 0] := by decide +kernel
example : 2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [1, 1, 0] :=
  unitClassFloor 2 [1, 1, 0] rfl rfl rfl (by decide +kernel)

example : places.degree [3, 0, 0] % (2 + 1) = 0 := by decide +kernel
example : c2hat.dfQ [3, 0, 0] = 36 := by decide +kernel
example : 2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [3, 0, 0] :=
  unitClassFloor 2 [3, 0, 0] rfl rfl rfl (by decide +kernel)
example : 2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [3, 0, 0] := by decide +kernel

example : ([1, 0] : places.Shape).length = 1 + 1 := rfl
example : ground.getAt 0 [1, 0] 1 = 0 := rfl
example : 0 < ground.sumNat [1, 0] := by decide +kernel
example : ¬ (places.degree [1, 0] % (1 + 1) = 0) := by decide +kernel
example : ¬ (2 * ((1 + 1) * (1 + 1)) ≤ c2hat.dfQ [1, 0]) := by decide +kernel

example : ([0, 0] : places.Shape).length = 1 + 1 := rfl
example : ground.getAt 0 [0, 0] 1 = 0 := rfl
example : places.degree [0, 0] % (1 + 1) = 0 := by decide +kernel
example : ¬ (0 < ground.sumNat [0, 0]) := by decide +kernel
example : ¬ (2 * ((1 + 1) * (1 + 1)) ≤ c2hat.dfQ [0, 0]) := by decide +kernel

example : ([0, 0, 1] : places.Shape).length = 2 + 1 := rfl
example : places.degree [0, 0, 1] % (2 + 1) = 0 := by decide +kernel
example : 0 < ground.sumNat [0, 0, 1] := by decide +kernel
example : ¬ (ground.getAt 0 [0, 0, 1] 2 = 0) := by decide +kernel
example : ¬ (2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [0, 0, 1]) := by decide +kernel

example : ground.getAt 0 [3, 0] 2 = 0 := rfl
example : places.degree [3, 0] % (2 + 1) = 0 := by decide +kernel
example : 0 < ground.sumNat [3, 0] := by decide +kernel
example : ¬ (([3, 0] : places.Shape).length = 2 + 1) := by decide +kernel
example : ¬ (2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [3, 0]) := by decide +kernel

/-! `boxMove`'s route at the reduced list `[2, 0]`: the produced
move descends, its two keys inside the reduced range; the two
binders isolated — at `[1, 0]` every entry sits below two and the
existential's entry read parts, and at `[2, 1]` the last entry
occupied forces every admissible move's target off the weak
descent, the witness pair bounded by the reduced range's own
reads. -/

example : ∃ i g : Nat, 0 < g ∧ i + g ≤ 1
    ∧ 2 ≤ ground.getAt 0 [2, 0] i := by
  obtain ⟨i, g, hg, hig, h2i, -, -, -, -, -⟩ :=
    casfloor.boxMove 1 [2, 0] rfl
      (by
        intro p hp
        cases p with
        | zero => exact Nat.zero_le 2
        | succ n =>
          exact absurd hp (fun h =>
            Nat.not_lt_zero n
              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))))
      rfl 0 (by decide +kernel) (by decide +kernel)
  exact ⟨i, g, hg, hig, h2i⟩

example : ¬ ∃ i g : Nat, 0 < g ∧ i + g ≤ 1
    ∧ 2 ≤ ground.getAt 0 [1, 0] i := by
  intro ⟨i, g, hg, hig, h2⟩
  have hi1 : i ≤ 1 := Nat.le_trans (Nat.le_add_right i g) hig
  cases i with
  | zero => exact absurd h2 (by decide +kernel)
  | succ i' =>
    cases i' with
    | zero => exact absurd h2 (by decide +kernel)
    | succ n =>
      exact absurd (Nat.le_of_succ_le_succ hi1)
        (Nat.not_succ_le_zero n)

example : ¬ ∃ i g : Nat, 0 < g ∧ i + g ≤ 1
    ∧ 2 ≤ ground.getAt 0 [2, 1] i
    ∧ (ground.bumpAt (i + g) (ground.dipAt i [2, 1])).length = 2
    ∧ (∀ p, p + 1 < (ground.bumpAt (i + g)
        (ground.dipAt i [2, 1])).length →
        ground.getAt 0 (ground.bumpAt (i + g)
          (ground.dipAt i [2, 1])) (p + 1)
          ≤ ground.getAt 0 (ground.bumpAt (i + g)
            (ground.dipAt i [2, 1])) p) := by
  intro ⟨i, g, hg, hig, h2, hlen, hdesc⟩
  cases g with
  | zero => exact absurd hg (Nat.lt_irrefl 0)
  | succ g' =>
    cases i with
    | zero =>
      cases g' with
      | zero => exact absurd (hdesc 0 (by decide +kernel)) (by decide +kernel)
      | succ g'' =>
        exact absurd (Nat.le_of_succ_le_succ hig)
          (Nat.not_succ_le_zero (0 + g''))
    | succ i' =>
      exact absurd
        (Nat.le_trans
          (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le i'))
            (Nat.le_add_right (i' + 1) g'))
          (Nat.le_of_succ_le_succ hig))
        (Nat.not_succ_le_zero 0)
