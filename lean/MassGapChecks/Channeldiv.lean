import MassGap.Channeldiv
/-!
The check module for `thm:channeldiv`: the batteries re-read the
divisor's displayed identities by kernel `decide` — the symbol's
witness, the crossing read with its equal-members outcome at base
one and the `[9:4]` value at base two, the margin's square at the
crossing pair's multiple, the base collecting at the orders' sum,
and the lower crossing's level reading its members at one value
exactly at base two, both directions at data with the crossing
binder isolated.  The coherence with `thm:chordmap` reads the
symbol as that theorem's chord at the bound-state level, its join
binder isolated by a refusal.
-/

namespace channeldiv
set_option maxHeartbeats 4000000

open ground

/-! The symbol's witness at the two bases. -/

theorem pin1 : symbolRead 1 := by decide +kernel
theorem pin2 : symbolRead 2 := by decide +kernel

/-! The crossing read, with the equal-members outcome at base one
and the `[9:4]` value at base two. -/

theorem pin3 : crossingRead 1 := by decide +kernel
theorem pin4 : crossingRead 2 := by decide +kernel
theorem pin5 : crossingRead 3 := by decide +kernel
theorem pin6 : (crossPair 1).oneValue ⟨BPair.unit, Pos.one⟩ := by decide +kernel
theorem pin7 : ¬ (crossPair 2).oneValue ⟨BPair.unit, Pos.one⟩ := by decide +kernel
theorem pin8 : (crossPair 2).oneValue
    (CPair.ofPair ⟨9, 4⟩ Pos.one) := by decide +kernel

/-! The margin's square at the crossing pair's multiple, and the
mass weight's sum with its complement at one. -/

theorem pin9 : marginRead 1 := by decide +kernel
theorem pin10 : marginRead 2 := by decide +kernel
theorem pin11 : marginRead 3 := by decide +kernel
theorem pin12 : weightSumRead 1 := by decide +kernel
theorem pin13 : weightSumRead 2 := by decide +kernel
theorem pin14 : weightSumRead 3 := by decide +kernel

/-! The base collects at the orders' sum. -/

theorem pin15 : baseRead 1 := by decide +kernel
theorem pin16 : baseRead 2 := by decide +kernel

/-! The lower crossing's level reads its two members at one value
exactly at base two, both directions at data: the mpr produces the
read at a base-two crossing level, the mp refuses the members at a
base-three crossing level — the theorem's route carrying the
refusal — and the crossing binder is isolated by its own refusal,
equal members off base two sitting off the crossing. -/

theorem pin17 : (⟨3, 2⟩ : Pair).oneValue ⟨3, 2⟩ :=
  (crossLo_members 2 ⟨3, 2⟩ ⟨3, 2⟩ (by decide +kernel)).mpr rfl
theorem pin18 : ¬ (⟨5, 2⟩ : Pair).oneValue ⟨3, 2⟩ :=
  fun hm => absurd
    ((crossLo_members 3 ⟨5, 2⟩ ⟨3, 2⟩ (by decide +kernel)).mp hm) (by decide +kernel)
theorem pin19 : ¬ chordmap.crossLo 3 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by
  decide +kernel

/-! The coherence with `thm:chordmap`: at the bound-state level of
base two the chord's join holds at the symbol, and at base one the
level `y₊ = [1:2]`, `y₋ = [3:2]` reads the two-term chord.  The
join binder is load-bearing: a level off the bound-state join
refuses the chord's join, and a chord off the symbol refuses it at
a level that meets the join. -/

theorem pin20 : chordmap.chordJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ (chord 2) := by
  decide +kernel

theorem pin21 : chordmap.chordJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ (chord 2) :=
  chord_bound 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ (by decide +kernel)

theorem pin22 : chordmap.chordJoin 1 ⟨Pos.one, 2⟩ (⟨3, 2⟩ : Pair) (chord 1) :=
  chord_bound 1 ⟨Pos.one, 2⟩ ⟨3, 2⟩ (by decide +kernel)

theorem pin23 : ¬ chordmap.boundJoin 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by
  decide +kernel
theorem pin24 : ¬ chordmap.chordJoin 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩
    (chord 2) := by decide +kernel
theorem pin25 : ¬ chordmap.chordJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩
    (Pair.ofPos 3) := by decide +kernel

end channeldiv
