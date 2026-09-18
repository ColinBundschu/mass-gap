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

namespace casfloor
set_option maxHeartbeats 4000000

open ground gentable sertables

/-! The cleared folds' coroot witnesses, one read per entry. -/

theorem pin1 : endsRead (tableB 2) (endsB 0) := by decide +kernel
theorem pin2 : endsRead (tableB 3) (endsB 1) := by decide +kernel
theorem pin3 : endsRead (tableB 4) (endsB 2) := by decide +kernel
theorem pin4 : endsRead (tableC 3) (endsC 0) := by decide +kernel
theorem pin5 : endsRead (tableC 4) (endsC 1) := by decide +kernel
theorem pin6 : endsRead (tableD 4) (endsD 0) := by decide +kernel
theorem pin7 : endsRead (tableD 5) (endsD 1) := by decide +kernel

private def at0 : List EndFold → Nat → EndFold := getAt ⟨[], 1, []⟩

/-! The series' displayed evaluations: the vector `[ℓ : r+1]` and
the spinor `[ℓ(2ℓ+1) : 8(r+1)]` at `B`, the first fundamental
`[2r+1 : 4(r+1)]` with the short dominant root's `[r : r+1]` at
`C`, and the vector `[r+2 : 2(r+1)]` with the spinors'
`[ℓ(r+2) : 8(r+1)]` at `D`. -/

theorem pin8 : c2Read (tableB 2) (at0 (endsB 0) 0) 2 3 := by decide +kernel
theorem pin9 : c2Read (tableB 2) (at0 (endsB 0) 1) 10 24 := by decide +kernel
theorem pin10 : c2Read (tableB 3) (at0 (endsB 1) 0) 3 5 := by decide +kernel
theorem pin11 : c2Read (tableB 3) (at0 (endsB 1) 1) 21 40 := by decide +kernel
theorem pin12 : c2Read (tableB 4) (at0 (endsB 2) 0) 4 7 := by decide +kernel
theorem pin13 : c2Read (tableB 4) (at0 (endsB 2) 1) 36 56 := by decide +kernel
theorem pin14 : c2Read (tableC 3) (at0 (endsC 0) 0) 7 16 := by decide +kernel
theorem pin15 : c2Read (tableC 3) (at0 (endsC 0) 1) 3 4 := by decide +kernel
theorem pin16 : c2Read (tableC 4) (at0 (endsC 1) 0) 9 20 := by decide +kernel
theorem pin17 : c2Read (tableC 4) (at0 (endsC 1) 1) 4 5 := by decide +kernel
theorem pin18 : c2Read (tableD 4) (at0 (endsD 0) 0) 7 12 := by decide +kernel
theorem pin19 : c2Read (tableD 4) (at0 (endsD 0) 1) 28 48 := by decide +kernel
theorem pin20 : c2Read (tableD 4) (at0 (endsD 0) 2) 28 48 := by decide +kernel
theorem pin21 : c2Read (tableD 5) (at0 (endsD 1) 0) 9 16 := by decide +kernel
theorem pin22 : c2Read (tableD 5) (at0 (endsD 1) 1) 45 64 := by decide +kernel
theorem pin23 : c2Read (tableD 5) (at0 (endsD 1) 2) 45 64 := by decide +kernel

/-! The series' `θ` entries at level one, the denominator's
coherence with the form and residue reads. -/

theorem pin24 : c2Read (tableB 2) (at0 (endsB 0) 2) 1 1 := by decide +kernel
theorem pin25 : c2Read (tableB 3) (at0 (endsB 1) 2) 1 1 := by decide +kernel
theorem pin26 : c2Read (tableB 4) (at0 (endsB 2) 2) 1 1 := by decide +kernel
theorem pin27 : c2Read (tableC 3) (at0 (endsC 0) 2) 1 1 := by decide +kernel
theorem pin28 : c2Read (tableC 4) (at0 (endsC 1) 2) 1 1 := by decide +kernel
theorem pin29 : c2Read (tableD 4) (at0 (endsD 0) 3) 1 1 := by decide +kernel
theorem pin30 : c2Read (tableD 5) (at0 (endsD 1) 3) 1 1 := by decide +kernel

/-! The series' floors, the lists' trichotomy least at the
displayed pairs: the `B` least exchanges from the spinor to the
vector across `ℓ = 3, 4`, and the `D` equality at `ℓ = 4` attains
at the vector and the spinors at once. -/

theorem pin31 : floorRead (tableB 2) (endsB 0) 10 24 := by decide +kernel
theorem pin32 : floorRead (tableB 3) (endsB 1) 21 40 := by decide +kernel
theorem pin33 : floorRead (tableB 4) (endsB 2) 4 7 := by decide +kernel
theorem pin34 : floorRead (tableC 3) (endsC 0) 7 16 := by decide +kernel
theorem pin35 : floorRead (tableC 4) (endsC 1) 9 20 := by decide +kernel
theorem pin36 : floorRead (tableD 4) (endsD 0) 7 12 := by decide +kernel
theorem pin37 : floorRead (tableD 5) (endsD 1) 9 16 := by decide +kernel

/-! The fixed members, one forcing per member (a fixed table's
positive list is its descent's output, so a member's reads join in
one `decide`): the coroot witnesses, the displayed minima, the `θ`
entry at level one, and the floor as the fundamental list's
trichotomy least. -/

theorem pin38 : endsRead tableG2 endsG2
    ∧ c2Read tableG2 (at0 endsG2 0) 1 2
    ∧ c2Read tableG2 (at0 endsG2 1) 1 1
    ∧ floorRead tableG2 endsG2 1 2 := by decide +kernel

theorem pin39 : endsRead tableF4 endsF4
    ∧ c2Read tableF4 (at0 endsF4 3) 2 3
    ∧ c2Read tableF4 (at0 endsF4 0) 1 1
    ∧ floorRead tableF4 endsF4 2 3 := by decide +kernel

theorem pin40 : endsRead tableE6 endsE6
    ∧ c2Read tableE6 (at0 endsE6 0) 13 18
    ∧ c2Read tableE6 (at0 endsE6 5) 13 18
    ∧ c2Read tableE6 (at0 endsE6 1) 1 1
    ∧ floorRead tableE6 endsE6 13 18 := by decide +kernel

theorem pin41 : endsRead tableE7 endsE7
    ∧ c2Read tableE7 (at0 endsE7 6) 19 24
    ∧ c2Read tableE7 (at0 endsE7 0) 1 1
    ∧ floorRead tableE7 endsE7 19 24 := by decide +kernel

theorem pin42 : endsRead tableE8 endsE8
    ∧ c2Read tableE8 (at0 endsE8 7) 1 1
    ∧ floorRead tableE8 endsE8 1 1 := by decide +kernel

/-! The `A`-series' endpoint display at the shapes,
`d_f Q(ω_j) = j g_j (r+2)`, the fundamental and its complement the
least ends. -/

theorem pin43 : endpointRead 1 1 := by decide +kernel
theorem pin44 : endpointRead 1 2 := by decide +kernel
theorem pin45 : endpointRead 2 1 := by decide +kernel
theorem pin46 : endpointRead 2 2 := by decide +kernel
theorem pin47 : endpointRead 3 2 := by decide +kernel
theorem pin48 : endpointRead 2 3 := by decide +kernel
theorem pin49 : endpointRead 1 5 := by decide +kernel
theorem pin50 : endpointRead 5 1 := by decide +kernel

/-! The crown coherence at the shared `A` instances: the fold route
at the first adjugate row against `def:c2hat`'s cleared bracket at
the fundamental's shape, the two routes' one value. -/

theorem pin51 : corootRead (tableA 2) ⟨[2, 1], 3, [1, 0]⟩ := by decide +kernel
theorem pin52 : c2Read (tableA 2) ⟨[2, 1], 3, [1, 0]⟩
    (c2hat.dfQ [1, 0, 0]) (2 * 3 * 3) := by decide +kernel
theorem pin53 : corootRead (tableA 3) ⟨[3, 2, 1], 4, [1, 0, 0]⟩ := by decide +kernel
theorem pin54 : c2Read (tableA 3) ⟨[3, 2, 1], 4, [1, 0, 0]⟩
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

theorem pin55 : c2hat.dfQ [1, 1, 0] = 18 := by decide +kernel
theorem pin56 : 2 * (2 + 2) ≤ c2hat.dfQ [1, 1, 0] :=
  floorAll 2 [1, 1, 0] rfl rfl (by decide +kernel)
theorem pin57 : c2hat.dfQ [2, 0, 1, 0] = 55 := by decide +kernel
theorem pin58 : 3 * (3 + 2) ≤ c2hat.dfQ [2, 0, 1, 0] :=
  floorAll 3 [2, 0, 1, 0] rfl rfl (by decide +kernel)
theorem pin59 : 1 * (1 + 2) ≤ c2hat.dfQ [1, 0] :=
  floorAll 1 [1, 0] rfl rfl (by decide +kernel)

theorem pin60 : c2hat.dfQ (fundShape 1 2) = 2 * (2 + 2) := by decide +kernel
theorem pin61 : c2hat.dfQ (fundShape 2 1) = 2 * (2 + 2) := by decide +kernel
theorem pin62 : ([1, 0, 0] : places.Shape) = fundShape 1 2
    ∨ [1, 0, 0] = fundShape 2 1 :=
  floorSharp 2 [1, 0, 0] rfl rfl (by decide +kernel) (by decide +kernel)
theorem pin63 : ([1, 0] : places.Shape) = fundShape 1 1
    ∨ [1, 0] = fundShape 1 1 :=
  floorSharp 1 [1, 0] rfl rfl (by decide +kernel) (by decide +kernel)

theorem pin64 : c2hat.dfQ [0, 0, 1] = 0 := by decide +kernel
theorem pin65 : c2hat.dfQ [0, 0, 0] = 0 := by decide +kernel

theorem pin66 : c2hat.dfQ [1, 1, 0] + 3 * (0 + 1)
    = c2hat.dfQ [0, 0, 1] + 3 * (2 + 1) + 2 * 3 * 2 := by decide +kernel
theorem pin67 : c2hat.dfQ [1, 1, 0] + 3 * (0 + 1)
    = c2hat.dfQ [0, 0, 1] + 3 * (2 + 1) + 2 * 3 * 2 :=
  boxFall [1, 1, 0] [0, 0, 1] 0 2 rfl rfl rfl
    (by decide +kernel)
theorem pin68 : c2hat.dfQ [0, 0, 1] < c2hat.dfQ [1, 1, 0] :=
  fallStrict [1, 1, 0] [0, 0, 1] 0 2 rfl rfl rfl
    (by decide +kernel)

theorem pin69 : c2hat.dfQ (adjchar.theta 4) = 32 := by decide +kernel
theorem pin70 : c2hat.dfQ (adjchar.theta 4) = 2 * 4 * 4 :=
  thetaRead 2

theorem pin71 : endpointRead 4 3 := endpointAll 4 3
theorem pin72 : c2hat.dfQ (fundShape 4 3) = 96 := by decide +kernel

theorem pin73 : c2hat.dfQ [0, 2, 0, 0] = 48 := by decide +kernel
theorem pin74 : 3 * (3 + 2) ≤ c2hat.dfQ [0, 2, 0, 0] :=
  floorAll 3 [0, 2, 0, 0] rfl rfl (by decide +kernel)

theorem pin75 : c2hat.dfQ (fundShape 2 2) = 20 := by decide +kernel
theorem pin76 : endpointRead 2 2 := endpointAll 2 2

/-! The unit class's own floor: an occupied reduced shape whose
degree reads the unit class clears `2 d_f²`.  `θ`'s class at
`d_f = 3` reads the bound exactly, a wider unit-class shape sits
above it, and the three further binders are forged one at a time —
the class, the occupancy, the reduction — each with the others
standing and each moving the conclusion. -/

theorem pin77 : places.degree [1, 1, 0] % (2 + 1) = 0 := by decide +kernel
theorem pin78 : 2 * ((2 + 1) * (2 + 1)) = c2hat.dfQ [1, 1, 0] := by decide +kernel
theorem pin79 : 2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [1, 1, 0] :=
  unitClassFloor 2 [1, 1, 0] rfl rfl rfl (by decide +kernel)

theorem pin80 : places.degree [3, 0, 0] % (2 + 1) = 0 := by decide +kernel
theorem pin81 : c2hat.dfQ [3, 0, 0] = 36 := by decide +kernel
theorem pin82 : 2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [3, 0, 0] :=
  unitClassFloor 2 [3, 0, 0] rfl rfl rfl (by decide +kernel)
theorem pin83 : 2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [3, 0, 0] := by decide +kernel

theorem pin84 : ([1, 0] : places.Shape).length = 1 + 1 := rfl
theorem pin85 : ground.getAt 0 [1, 0] 1 = 0 := rfl
theorem pin86 : 0 < ground.sumNat [1, 0] := by decide +kernel
theorem pin87 : ¬ (places.degree [1, 0] % (1 + 1) = 0) := by decide +kernel
theorem pin88 : ¬ (2 * ((1 + 1) * (1 + 1)) ≤ c2hat.dfQ [1, 0]) := by decide +kernel

theorem pin89 : ([0, 0] : places.Shape).length = 1 + 1 := rfl
theorem pin90 : ground.getAt 0 [0, 0] 1 = 0 := rfl
theorem pin91 : places.degree [0, 0] % (1 + 1) = 0 := by decide +kernel
theorem pin92 : ¬ (0 < ground.sumNat [0, 0]) := by decide +kernel
theorem pin93 : ¬ (2 * ((1 + 1) * (1 + 1)) ≤ c2hat.dfQ [0, 0]) := by decide +kernel

theorem pin94 : ([0, 0, 1] : places.Shape).length = 2 + 1 := rfl
theorem pin95 : places.degree [0, 0, 1] % (2 + 1) = 0 := by decide +kernel
theorem pin96 : 0 < ground.sumNat [0, 0, 1] := by decide +kernel
theorem pin97 : ¬ (ground.getAt 0 [0, 0, 1] 2 = 0) := by decide +kernel
theorem pin98 : ¬ (2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [0, 0, 1]) := by decide +kernel

theorem pin99 : ground.getAt 0 [3, 0] 2 = 0 := rfl
theorem pin100 : places.degree [3, 0] % (2 + 1) = 0 := by decide +kernel
theorem pin101 : 0 < ground.sumNat [3, 0] := by decide +kernel
theorem pin102 : ¬ (([3, 0] : places.Shape).length = 2 + 1) := by decide +kernel
theorem pin103 : ¬ (2 * ((2 + 1) * (2 + 1)) ≤ c2hat.dfQ [3, 0]) := by decide +kernel

/-! `boxMove`'s route at the reduced list `[2, 0]`: the produced
move descends, its two keys inside the reduced range; the two
binders isolated — at `[1, 0]` every entry sits below two and the
existential's entry read parts, and at `[2, 1]` the last entry
occupied forces every admissible move's target off the weak
descent, the witness pair bounded by the reduced range's own
reads. -/

theorem pin104 : ∃ i g : Nat, 0 < g ∧ i + g ≤ 1
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

theorem pin105 : ¬ ∃ i g : Nat, 0 < g ∧ i + g ≤ 1
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

theorem pin106 : ¬ ∃ i g : Nat, 0 < g ∧ i + g ≤ 1
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

end casfloor
