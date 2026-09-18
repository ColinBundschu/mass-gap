import MassGap.Chordmap
/-!
The check module for `thm:chordmap`: the batteries decide the level
joins at stated data by kernel `decide` — the bound-state join and
the two crossing joins at base two, the double-root read holding at
the two crossings and refusing at an interior and at an exterior
level, the band probed at its interior, at both crossings and at
both exteriors, the width-four read by the theorem's own route, and
the defect root's witness with the cleared evaluation at the join.
Every hypothesis of every theorem is decided at the data it is
applied to, and each is isolated by a refusal beside its own
instance.
-/

namespace chordmap

open ground

/-! The joins at base two: the bound-state level `2 y₊ + 1 = 2 y₋`
at `y₊ = [1:2]`, `y₋ = [1:1]`, the lower crossing at `y₊ = y₋ = 1`
and the upper at `y₊ = 5`, `y₋ = 1`; a level off the bound-state
join refuses it. -/

theorem pin1 : boundJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin2 : crossLo 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin3 : crossHi 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin4 : ¬ boundJoin 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

/-! The double-root read at base two with `y₋ = 1`: the crossings
sit at `y₊ = 1` and `y₊ = 5`, and the read refuses at the interior
level `y₊ = 2` and at the exterior level `y₊ = 7`. -/

theorem pin5 : crossAt 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin6 : crossAt 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin7 : ¬ crossAt 2 ⟨2, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin8 : ¬ crossAt 2 ⟨7, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

/-! The split read at both directions, the theorem's own route: the
double root at a crossing produces the join, a stated join produces
the double root, and at the interior level both joins refuse. -/

theorem pin9 : crossLo 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩
    ∨ crossHi 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ :=
  (cross_split 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩).mp (by decide +kernel)

theorem pin10 : crossAt 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩ :=
  (cross_split 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩).mpr (Or.inr (by decide +kernel))

theorem pin11 : ¬ (crossLo 2 ⟨2, Pos.one⟩ ⟨Pos.one, Pos.one⟩
    ∨ crossHi 2 ⟨2, Pos.one⟩ ⟨Pos.one, Pos.one⟩) := by decide +kernel

/-! The band at base two with `y₋ = 1`, probed at five levels: the
interior `y₊ = 2`, the two crossings `y₊ = 1` and `y₊ = 5` its
endpoints, and the exteriors `y₊ = 7` above and `y₊ = [1:2]` below
refusing.  The two crossing memberships also read by their own
theorems, whose crossing binders refuse at the exterior level. -/

theorem pin12 : bandAt 2 ⟨2, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin13 : bandAt 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin14 : bandAt 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin15 : ¬ bandAt 2 ⟨7, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin16 : ¬ bandAt 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

theorem pin17 : bandAt 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ :=
  cross_band_lo 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ (by decide +kernel)

theorem pin18 : bandAt 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩ :=
  cross_band_hi 2 ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩ (by decide +kernel)

theorem pin19 : ¬ crossLo 2 ⟨7, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin20 : ¬ crossHi 2 ⟨7, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

/-! The width-four read by the theorem's route at base two, both
crossing binders decided.  Each binder is load-bearing and its
refusal is committed beside the failing conclusion: the interior
level `y₊ = 2` refuses the lower crossing and the four-join with
it, and `y₊' = 4` refuses the upper crossing and its four-join. -/

theorem pin21 : (⟨5, Pos.one⟩ : Pair).oneValue (⟨Pos.one, Pos.one⟩ + Pair.ofPos 4) :=
  band_width 2 ⟨Pos.one, Pos.one⟩ ⟨5, Pos.one⟩ ⟨Pos.one, Pos.one⟩
    (by decide +kernel) (by decide +kernel)

theorem pin22 : ¬ crossLo 2 ⟨2, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin23 : ¬ (⟨5, Pos.one⟩ : Pair).oneValue (⟨2, Pos.one⟩ + Pair.ofPos 4) := by
  decide +kernel
theorem pin24 : ¬ crossHi 2 ⟨4, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel
theorem pin25 : ¬ (⟨4, Pos.one⟩ : Pair).oneValue
    (⟨Pos.one, Pos.one⟩ + Pair.ofPos 4) := by decide +kernel

/-! The defect root's witness at base two by both routes, and the
cleared evaluation at the defect root reading the bound-state join
through the theorem, with a level off the join refusing it. -/

theorem pin26 : (Pair.ofPos 2 * defectRoot 2).oneValue (Pair.ofPos Pos.one) := by
  decide +kernel

theorem pin27 : (Pair.ofPos 2 * defectRoot 2).oneValue (Pair.ofPos Pos.one) :=
  defect_read 2

theorem pin28 : defectLevel 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

theorem pin29 : boundJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ :=
  (defect_level 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩).mp (by decide +kernel)

theorem pin30 : defectLevel 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ :=
  (defect_level 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩).mpr (by decide +kernel)

theorem pin31 : ¬ defectLevel 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

/-! The two integers: the coordination count fixing the band's
width against the base, agreeing exactly at base two — the
member-key count's two-key read (`prop:row`) — and separating at
base one.  At base one the bound-state level is itself the lower
crossing, the double root there, while at base two the bound-state
level sits off the crossings. -/

theorem pin32 : (Pair.ofPos 2 * Pair.ofPos 2).oneValue (Pair.ofPos 4) := by
  decide +kernel

/-! The chord's join at a general chord, and the crossing and band
reads at levels of occupied denominators — base three at
`y₋ = [3:2]`, the crossings at `[5:2]` and `[13:2]`. -/

theorem pin33 : chordJoin 3 (⟨5, 2⟩ : Pair) (⟨3, 2⟩ : Pair)
    (Pair.ofPos 2) := by decide +kernel
theorem pin34 : ¬ chordJoin 3 (⟨5, 2⟩ : Pair) (⟨3, 2⟩ : Pair)
    (Pair.ofPos 3) := by decide +kernel
theorem pin35 : crossLo 3 (⟨5, 2⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin36 : crossHi 3 (⟨13, 2⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin37 : crossAt 3 (⟨5, 2⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin38 : crossAt 3 (⟨13, 2⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin39 : ¬ crossAt 3 (⟨7, 2⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin40 : bandAt 3 (⟨7, 2⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin41 : ¬ bandAt 3 (⟨9, 4⟩ : Pair) (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin42 : (⟨13, 2⟩ : Pair).oneValue ((⟨5, 2⟩ : Pair) + Pair.ofPos 4) :=
  band_width 3 (⟨5, 2⟩ : Pair) (⟨13, 2⟩ : Pair) (⟨3, 2⟩ : Pair)
    (by decide +kernel) (by decide +kernel)

theorem pin43 : boundJoin 1 ⟨Pos.one, 2⟩ (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin44 : crossLo 1 ⟨Pos.one, 2⟩ (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin45 : crossAt 1 ⟨Pos.one, 2⟩ (⟨3, 2⟩ : Pair) := by decide +kernel
theorem pin46 : ¬ crossAt 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ := by decide +kernel

end chordmap
