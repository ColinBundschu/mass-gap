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
set_option maxHeartbeats 4000000

open ground channeldiv

/-! The symbol's witness at the two bases. -/

example : symbolRead 1 := by decide +kernel
example : symbolRead 2 := by decide +kernel

/-! The crossing read, with the equal-members outcome at base one
and the `[9:4]` value at base two. -/

example : crossingRead 1 := by decide +kernel
example : crossingRead 2 := by decide +kernel
example : crossingRead 3 := by decide +kernel
example : (crossPair 1).oneValue ⟨BPair.unit, Pos.one⟩ := by decide +kernel
example : ¬ (crossPair 2).oneValue ⟨BPair.unit, Pos.one⟩ := by decide +kernel
example : (crossPair 2).oneValue
    (CPair.ofPair ⟨9, 4⟩ Pos.one) := by decide +kernel

/-! The margin's square at the crossing pair's multiple, and the
mass weight's sum with its complement at one. -/

example : marginRead 1 := by decide +kernel
example : marginRead 2 := by decide +kernel
example : marginRead 3 := by decide +kernel
example : weightSumRead 1 := by decide +kernel
example : weightSumRead 2 := by decide +kernel
example : weightSumRead 3 := by decide +kernel

/-! The base collects at the orders' sum. -/

example : baseRead 1 := by decide +kernel
example : baseRead 2 := by decide +kernel

/-! The lower crossing's level reads its two members at one value
exactly at base two, both directions at data: the mpr produces the
read at a base-two crossing level, the mp refuses the members at a
base-three crossing level — the theorem's route carrying the
refusal — and the crossing binder is isolated by its own refusal,
equal members off base two sitting off the crossing. -/

example : (⟨3, 2⟩ : Pair).oneValue ⟨3, 2⟩ :=
  (crossLo_members 2 ⟨3, 2⟩ ⟨3, 2⟩ (by decide +kernel)).mpr rfl
example : ¬ (⟨5, 2⟩ : Pair).oneValue ⟨3, 2⟩ :=
  fun hm => absurd
    ((crossLo_members 3 ⟨5, 2⟩ ⟨3, 2⟩ (by decide +kernel)).mp hm) (by decide +kernel)
example : ¬ chordmap.crossLo 3 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by
  decide +kernel

/-! The coherence with `thm:chordmap`: at the bound-state level of
base two the chord's join holds at the symbol, and at base one the
level `y₊ = [1:2]`, `y₋ = [3:2]` reads the two-term chord.  The
join binder is load-bearing: a level off the bound-state join
refuses the chord's join, and a chord off the symbol refuses it at
a level that meets the join. -/

example : chordmap.chordJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ (chord 2) := by
  decide +kernel

example : chordmap.chordJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ (chord 2) :=
  chord_bound 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩ (by decide +kernel)

example : chordmap.chordJoin 1 ⟨Pos.one, 2⟩ (⟨3, 2⟩ : Pair) (chord 1) :=
  chord_bound 1 ⟨Pos.one, 2⟩ ⟨3, 2⟩ (by decide +kernel)

example : ¬ chordmap.boundJoin 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩ := by
  decide +kernel
example : ¬ chordmap.chordJoin 2 ⟨Pos.one, Pos.one⟩ ⟨Pos.one, Pos.one⟩
    (chord 2) := by decide +kernel
example : ¬ chordmap.chordJoin 2 ⟨Pos.one, 2⟩ ⟨Pos.one, Pos.one⟩
    (Pair.ofPos 3) := by decide +kernel
