import MassGap.Blockirr
/-!
The check module for `lem:blockirr`(i): the irreducibility read at
the committed block — the fundamental at `d = 2`, `blockSpan [1,0]`
pinned to its two literal members with the lowering equation the
provenance consumes — instantiated at two stated lists.  The whole
pool as the list attains the left disjunct (every member inside
the list's own group span) and the unit list at the head's content
attains the right one, its left disjunct refused.  The refusals
isolate the load-bearing hypotheses one at a time: the top-only
list is not closed (`hLcl`), the trivial-content vector is not a
span member (`hLmem`), and two pools refuse the provenance
(`hprov`) — the second member sitting at a content the head cannot
lower to, and two independent members at one content, which the
height descent forbids outright since every word's fold sits
strictly below the head's.  Every hypothesis decides: the closure read in its
nested-bound spelling, and the provenance read through the
carrier's own equality (`blockcount.HVec.decEq`) with the two
guard-shaped existential instances at `def:ground`
(`∃ p, p + 1 < n ∧ P p` and `∃ p, p ≤ n ∧ P p`, the core's
`propext`-bearing routes replaced).  Clause (ii) adds the
intertwining, value and provenance refusals; clause (iii) the
source-closure, target-provenance and off-unit-value ones, with
the target head's unit read the derived one's exhibit — each
refusal decides every surviving hypothesis beside the refused
one and the conclusion's failure.  Clause (iv)'s tier pins
`dim_eq` at two genuinely independent tops of one content with
its four isolating refusals.
-/
set_option maxRecDepth 8192

open ground places blockcount

/-! The committed block: the fundamental's span at two letters is
the exhibit with its one lowering, and the lowering equation is
the provenance read the clause consumes. -/

example : blockSpan [1, 0]
    = [⟨[1, 0], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩] := rfl

example : (blockSpan [1, 0]).length = 2 := by decide +kernel

example : lowerH 0 (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
    = some ⟨[0, 1], [BPair.ofNat 1]⟩ := rfl

/-! The whole pool as the stated list: every decidable hypothesis
decided, the clause's own instance, and the left disjunct
attained. -/

example : ∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
    ⟨[0, 1], [BPair.ofNat 1]⟩], sized w := by decide +kernel

example : ∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
    ⟨[0, 1], [BPair.ofNat 1]⟩], w.content.length = 2 := by decide +kernel

example : ∀ x ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 1], [BPair.ofNat 1]⟩],
    settledAt [⟨[1, 0], [BPair.ofNat 1]⟩,
      ⟨[0, 1], [BPair.ofNat 1]⟩] x := by decide +kernel

example : ∀ x ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 1], [BPair.ofNat 1]⟩],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt [⟨[1, 0], [BPair.ofNat 1]⟩,
        ⟨[0, 1], [BPair.ofNat 1]⟩] (act i j x) := by decide +kernel

example : (∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
      settledAt [⟨[1, 0], [BPair.ofNat 1]⟩,
        ⟨[0, 1], [BPair.ofNat 1]⟩] w)
    ∨ (∀ x ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[0, 1], [BPair.ofNat 1]⟩], poly.unitTail x.coords) :=
  blockirr.irred 2 ⟨[1, 0], [BPair.ofNat 1]⟩
    [⟨[0, 1], [BPair.ofNat 1]⟩]
    [⟨[1, 0], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The unit list at the head's content: the right disjunct
attained with the left one refused. -/

example : ∀ x ∈ [(⟨[1, 0], [BPair.unit]⟩ : HVec)], sized x := by
  decide +kernel

example : ∀ x ∈ [(⟨[1, 0], [BPair.unit]⟩ : HVec)],
    settledAt [⟨[1, 0], [BPair.ofNat 1]⟩,
      ⟨[0, 1], [BPair.ofNat 1]⟩] x := by decide +kernel

example : ∀ x ∈ [(⟨[1, 0], [BPair.unit]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt [⟨[1, 0], [BPair.unit]⟩] (act i j x) := by decide +kernel

example : (∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
      settledAt [⟨[1, 0], [BPair.unit]⟩] w)
    ∨ (∀ x ∈ [(⟨[1, 0], [BPair.unit]⟩ : HVec)],
        poly.unitTail x.coords) :=
  blockirr.irred 2 ⟨[1, 0], [BPair.ofNat 1]⟩
    [⟨[0, 1], [BPair.ofNat 1]⟩] [⟨[1, 0], [BPair.unit]⟩]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ∀ x ∈ [(⟨[1, 0], [BPair.unit]⟩ : HVec)],
    poly.unitTail x.coords := by decide +kernel

example : ¬ (∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
    :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    settledAt [⟨[1, 0], [BPair.unit]⟩] w) := by decide +kernel

/-! The closure refusal (`hLcl`): the head alone is a span member
at the pool's own reads but is not closed — its lowering leaves
the list — and both disjuncts fail. -/

example : ∀ x ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)],
    sized x ∧ settledAt [⟨[1, 0], [BPair.ofNat 1]⟩,
      ⟨[0, 1], [BPair.ofNat 1]⟩] x := by decide +kernel

example : ¬ (∀ x ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt [⟨[1, 0], [BPair.ofNat 1]⟩] (act i j x)) := by decide +kernel

example : ¬ ((∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
      settledAt [⟨[1, 0], [BPair.ofNat 1]⟩] w)
    ∨ (∀ x ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)],
        poly.unitTail x.coords)) := by decide +kernel

/-! The membership refusal (`hLmem`): the trivial content's vector
is killed by both letter pairs — the closure holds — but it is no
member of the pool's span, and both disjuncts fail. -/

example : ∀ x ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
    sized x ∧ ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt [⟨[0, 0], [BPair.ofNat 1]⟩] (act i j x) := by decide +kernel

example : ¬ (∀ x ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
    settledAt [⟨[1, 0], [BPair.ofNat 1]⟩,
      ⟨[0, 1], [BPair.ofNat 1]⟩] x) := by decide +kernel

example : ¬ ((∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
      settledAt [⟨[0, 0], [BPair.ofNat 1]⟩] w)
    ∨ (∀ x ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
        poly.unitTail x.coords)) := by decide +kernel

/-! The provenance refusal (`hprov`), the unreachable content: the
pool's second member sits at a content the head cannot lower to —
the head's letter is unoccupied, so the only interior lowering is
absent — while every other read holds, and both disjuncts fail. -/

example : lowerH 0 (⟨[0, 0], [BPair.ofNat 1]⟩ : HVec) = none := rfl

example : ∀ w ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 1], [BPair.ofNat 1]⟩],
    sized w ∧ w.content.length = 2 := by decide +kernel

example : ∀ x ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
    settledAt [⟨[0, 0], [BPair.ofNat 1]⟩,
        ⟨[0, 1], [BPair.ofNat 1]⟩] x
      ∧ ∀ i < 2, ∀ j < 2, ¬ i = j →
          settledAt [⟨[0, 0], [BPair.ofNat 1]⟩] (act i j x) := by
  decide +kernel

example : ¬ ((∀ w ∈ (⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
      settledAt [⟨[0, 0], [BPair.ofNat 1]⟩] w)
    ∨ (∀ x ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
        poly.unitTail x.coords)) := by decide +kernel

/-! The provenance refusal (`hprov`), the doubled content: two
independent members at one content — the singlet and one word,
the singlet killed by both letter pairs and a member of the pool's
own group — so every other read holds while the second member can
carry no provenance at all, the height descent placing every
word's fold strictly below the head's.  Both disjuncts fail. -/

example : ∀ w ∈ [(⟨[1, 1],
        [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩],
    sized w ∧ w.content.length = 2 := by decide +kernel

example : ∀ x ∈ [(⟨[1, 1],
      [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)],
    settledAt [⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩,
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩] x
      ∧ ∀ i < 2, ∀ j < 2, ¬ i = j →
          settledAt
            [⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩]
            (act i j x) := by decide +kernel

example : lowerspan.ht [1, 1] = 1 := by decide +kernel

example : ¬ ((∀ w ∈ (⟨[1, 1],
        [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)
      :: [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      settledAt [⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩] w)
    ∨ (∀ x ∈ [(⟨[1, 1],
        [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)],
        poly.unitTail x.coords)) := by decide +kernel

/-! `lem:blockirr`(ii) at the same block: the endomorphism family
is a scalar.  The identity family and the constant doubling both
satisfy the intertwining and read the cleared line; the
content-dependent family breaks the intertwining at one pair and
the display with it, and a family sending the head off its own
line breaks the value's settled read while the intertwining
survives — the moved contents' one-entry matrices absorb it. -/

example : ∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    poly.oneValue
      (elim.vecScale
        (elim.dotP [BPair.ofNat 1] [BPair.ofNat 1])
        (elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
          w.coords))
      (elim.vecScale
        (elim.dotP
          (elim.matVec ((fun _ => [[BPair.ofNat 1]]) [1, 0])
            [BPair.ofNat 1])
          [BPair.ofNat 1])
        w.coords) :=
  blockirr.endo_scalar 2 ⟨[1, 0], [BPair.ofNat 1]⟩
    [⟨[0, 1], [BPair.ofNat 1]⟩] (fun _ => [[BPair.ofNat 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    poly.oneValue
      (elim.vecScale
        (elim.dotP [BPair.ofNat 1] [BPair.ofNat 1])
        (elim.matVec ((fun _ => [[BPair.ofNat 2]]) w.content)
          w.coords))
      (elim.vecScale
        (elim.dotP
          (elim.matVec ((fun _ => [[BPair.ofNat 2]]) [1, 0])
            [BPair.ofNat 1])
          [BPair.ofNat 1])
        w.coords) :=
  blockirr.endo_scalar 2 ⟨[1, 0], [BPair.ofNat 1]⟩
    [⟨[0, 1], [BPair.ofNat 1]⟩] (fun _ => [[BPair.ofNat 2]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The intertwining refusal (`hmv`): the family reading one at the
head's content and two below it is square with its value settled,
but it fails the moved read at the lowering pair, and the display
fails with it. -/

example : ∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    elim.sqAt ((fun mu => if mu = [1, 0] then [[BPair.ofNat 1]]
      else [[BPair.ofNat 2]]) w.content) w.coords.length := by decide +kernel

example : settledAt ((⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)])
    ⟨[1, 0], elim.matVec ((fun mu => if mu = [1, 0]
      then [[BPair.ofNat 1]] else [[BPair.ofNat 2]]) [1, 0])
      [BPair.ofNat 1]⟩ := by decide +kernel

example : ¬ (∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec ((fun mu => if mu = [1, 0]
            then [[BPair.ofNat 1]] else [[BPair.ofNat 2]])
            w.content) w.coords))
        (elim.matVec ((fun mu => if mu = [1, 0]
            then [[BPair.ofNat 1]] else [[BPair.ofNat 2]])
            (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords))) := by decide +kernel

example : ¬ (∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    poly.oneValue
      (elim.vecScale
        (elim.dotP [BPair.ofNat 1] [BPair.ofNat 1])
        (elim.matVec ((fun mu => if mu = [1, 0]
          then [[BPair.ofNat 1]] else [[BPair.ofNat 2]]) w.content)
          w.coords))
      (elim.vecScale
        (elim.dotP
          (elim.matVec ((fun mu => if mu = [1, 0]
            then [[BPair.ofNat 1]] else [[BPair.ofNat 2]]) [1, 0])
            [BPair.ofNat 1])
          [BPair.ofNat 1])
        w.coords)) := by decide +kernel

/-! The value refusal (`hval`): at the one-member pool carrying a
word at the doubled content, the family sending it off its own
line still intertwines — the moved contents' one-entry matrices
take up the slack — but the head's value leaves the pool's group
span, and the display fails. -/

example : ∀ k, k < ([] : List HVec).length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec) :: []) i)
        = some (getAt (⟨[], []⟩ : HVec) ([] : List HVec) k) := by
  decide +kernel

example : ∀ w ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
    sized w ∧ w.content.length = 2
      ∧ elim.sqAt ((fun mu => if mu = [1, 1]
          then [[BPair.ofNat 1, BPair.unit],
                [BPair.ofNat 1, BPair.unit]]
          else [[BPair.ofNat 2]]) w.content) w.coords.length := by
  decide +kernel

example : ∀ w ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec ((fun mu => if mu = [1, 1]
            then [[BPair.ofNat 1, BPair.unit],
                  [BPair.ofNat 1, BPair.unit]]
            else [[BPair.ofNat 2]]) w.content) w.coords))
        (elim.matVec ((fun mu => if mu = [1, 1]
            then [[BPair.ofNat 1, BPair.unit],
                  [BPair.ofNat 1, BPair.unit]]
            else [[BPair.ofNat 2]]) (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords)) := by decide +kernel

example : ¬ settledAt [(⟨[1, 1],
      [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
    ⟨[1, 1], elim.matVec ((fun mu => if mu = [1, 1]
      then [[BPair.ofNat 1, BPair.unit],
            [BPair.ofNat 1, BPair.unit]]
      else [[BPair.ofNat 2]]) [1, 1])
      [BPair.ofNat 1, BPair.unit]⟩ := by decide +kernel

example : ¬ (∀ w ∈ [(⟨[1, 1],
      [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
    poly.oneValue
      (elim.vecScale
        (elim.dotP [BPair.ofNat 1, BPair.unit]
          [BPair.ofNat 1, BPair.unit])
        (elim.matVec ((fun mu => if mu = [1, 1]
          then [[BPair.ofNat 1, BPair.unit],
                [BPair.ofNat 1, BPair.unit]]
          else [[BPair.ofNat 2]]) w.content) w.coords))
      (elim.vecScale
        (elim.dotP
          (elim.matVec ((fun mu => if mu = [1, 1]
            then [[BPair.ofNat 1, BPair.unit],
                  [BPair.ofNat 1, BPair.unit]]
            else [[BPair.ofNat 2]]) [1, 1])
            [BPair.ofNat 1, BPair.unit])
          [BPair.ofNat 1, BPair.unit])
        w.coords)) := by decide +kernel

/-! `lem:blockirr`(iii) at two blocks: the identity family carries
the fundamental into its own doubled copy — a genuinely different
list at the same top content — and every hypothesis decides. -/

example : (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec).content
    = (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content :=
  blockirr.hom_content 2 ⟨[1, 0], [BPair.ofNat 1]⟩
    [⟨[0, 1], [BPair.ofNat 1]⟩] ⟨[1, 0], [BPair.ofNat 2]⟩
    [⟨[0, 1], [BPair.ofNat 2]⟩] (fun _ => [[BPair.ofNat 1]])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : lowerH 0 (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
    = some ⟨[0, 1], [BPair.ofNat 2]⟩ := rfl

/-! The off-unit-value refusal (`hoff`): the unit family carries
the fundamental into the symmetric square's span — every other
read holds — but no value is off the sum's unit, and the top
contents differ. -/

example : ∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    elim.sqAt ((fun _ => [[BPair.unit]]) w.content) w.coords.length
      ∧ settledAt (blockSpan [2, 0])
        ⟨w.content, elim.matVec ((fun _ => [[BPair.unit]]) w.content)
          w.coords⟩ := by decide +kernel

example : ∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec ((fun _ => [[BPair.unit]]) w.content)
            w.coords))
        (elim.matVec ((fun _ => [[BPair.unit]])
            (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords)) := by decide +kernel

example : ∀ w ∈ blockSpan [2, 0], sized w ∧ w.content.length = 2 := by
  decide +kernel

example : ∀ k, k < (blockSpan [2, 0]).tail.length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec) (blockSpan [2, 0]) i)
        = some (getAt (⟨[], []⟩ : HVec) (blockSpan [2, 0]).tail k) := by
  decide +kernel

example : ¬ poly.unitTail
    (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec).coords := by decide +kernel

example : ¬ (∃ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
    :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    ¬ poly.unitTail
      (elim.matVec ((fun _ => [[BPair.unit]]) w.content)
        w.coords)) := by decide +kernel

example : ¬ ((⟨[1, 0], [BPair.ofNat 1]⟩ : HVec).content
    = (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec).content) := by decide +kernel

example : blockSpan [2, 0]
    = [⟨[2, 0], [BPair.ofNat 1]⟩,
       ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
       ⟨[0, 2], [BPair.ofNat 2]⟩] := rfl

/-! The target head's off-unit read is derived, not data
(`blockirr`'s `head_off`), and this is its demonstration: at a
target pool whose head reads the unit every member does — the
provenance images of a unit tail are unit tails — so every value
settled there is a unit tail and the off-unit value `hoff` cannot
hold.  The committed instance: the unit family into the one-member
pool at the symmetric square's unit-reading top, the settled reads
holding, `hoff` refused there, and the identity family's values
refusing those same settled reads — the two ways the clause's
hypotheses can meet a unit head.  The top contents differ
throughout. -/

example : poly.unitTail (⟨[2, 0], [BPair.unit]⟩ : HVec).coords := by
  decide +kernel

example : ∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    settledAt [(⟨[2, 0], [BPair.unit]⟩ : HVec)]
      ⟨w.content, elim.matVec ((fun _ => [[BPair.unit]]) w.content)
        w.coords⟩ := by decide +kernel

example : ¬ (∃ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
    :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    ¬ poly.unitTail
      (elim.matVec ((fun _ => [[BPair.unit]]) w.content)
        w.coords)) := by decide +kernel

example : ¬ (∀ w ∈ (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
    :: [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    settledAt [(⟨[2, 0], [BPair.unit]⟩ : HVec)]
      ⟨w.content, elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
        w.coords⟩) := by decide +kernel

/-! The source-closure refusal (`hclv`): the fundamental's lowered
member alone is a target-span member with its value settled and
its own provenance vacuous, but its raising leaves the one-member
source pool, and the top contents differ. -/

example : ∀ w ∈ [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    sized w ∧ w.content.length = 2
      ∧ elim.sqAt ((fun _ => [[BPair.ofNat 1]]) w.content)
        w.coords.length := by decide +kernel

example : ∀ k, k < ([] : List HVec).length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[0, 1], [BPair.ofNat 1]⟩ : HVec) :: []) i)
        = some (getAt (⟨[], []⟩ : HVec) ([] : List HVec) k) := by
  decide +kernel

example : ∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
    ⟨[0, 1], [BPair.ofNat 1]⟩], sized w ∧ w.content.length = 2 := by
  decide +kernel

example : ∀ k, k < [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
            :: [⟨[0, 1], [BPair.ofNat 1]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
          [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)] k) := by decide +kernel

example : ∀ w ∈ [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    settledAt [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[0, 1], [BPair.ofNat 1]⟩]
      ⟨w.content, elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
        w.coords⟩
      ∧ ∀ i < 2, ∀ j < 2, ¬ i = j →
        poly.oneValue
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            (elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
              w.coords))
          (elim.matVec ((fun _ => [[BPair.ofNat 1]])
              (moveAt i j w.content))
            (elim.matVec
              (units.matUnitAt (moveAt i j w.content) w.content i j)
              w.coords)) := by decide +kernel

example : ∃ w ∈ [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    ¬ poly.unitTail
      (elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
        w.coords) := by decide +kernel

example : ¬ (∀ w ∈ [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)]
        (act i j w)) := by decide +kernel

example : ¬ ((⟨[0, 1], [BPair.ofNat 1]⟩ : HVec).content
    = (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec).content) := by decide +kernel

/-! The target-provenance refusal (`hprovu`): the identity family
carries the fundamental into a target list whose head is the
symmetric square's top — every other read holds, the values
settled in the target's own groups — but the target's second
member is no lowering image of its head, and the top contents
differ. -/

example : ∀ w ∈ [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
    ⟨[1, 0], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩],
    sized w ∧ w.content.length = 2 := by decide +kernel

example : ∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 1], [BPair.ofNat 1]⟩],
    settledAt [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 0], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩]
      ⟨w.content, elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
        w.coords⟩ := by decide +kernel

example : ∃ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 1], [BPair.ofNat 1]⟩],
    ¬ poly.unitTail
      (elim.matVec ((fun _ => [[BPair.ofNat 1]]) w.content)
        w.coords) := by decide +kernel

example : ¬ (∀ k, k < [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 1], [BPair.ofNat 1]⟩].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
            :: [⟨[1, 0], [BPair.ofNat 1]⟩,
                ⟨[0, 1], [BPair.ofNat 1]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
          [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
           ⟨[0, 1], [BPair.ofNat 1]⟩] k)) := by decide +kernel

example : ¬ ((⟨[1, 0], [BPair.ofNat 1]⟩ : HVec).content
    = (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec).content) := by decide +kernel

/-! The provenance refusal at clause (ii) (`hprov`): a pool
carrying the fundamental's head beside a member at the trivial
content — every letter pair kills that member, so the family
reading two there against one at the head still intertwines and
its head value is settled — but the second member is no lowering
image of the first, and the display fails at it.  The disconnected
member is what makes the refusal reachable: on a provenance-linked
pool the intertwining forces one scalar throughout, which is the
clause itself. -/

example : ∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 0], [BPair.ofNat 1]⟩],
    sized w ∧ w.content.length = 2
      ∧ elim.sqAt ((fun mu => if mu = [0, 0] then [[BPair.ofNat 2]]
          else [[BPair.ofNat 1]]) w.content) w.coords.length := by
  decide +kernel

example : settledAt [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 0], [BPair.ofNat 1]⟩]
    ⟨[1, 0], elim.matVec ((fun mu => if mu = [0, 0]
      then [[BPair.ofNat 2]] else [[BPair.ofNat 1]]) [1, 0])
      [BPair.ofNat 1]⟩ := by decide +kernel

example : ∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 0], [BPair.ofNat 1]⟩],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec ((fun mu => if mu = [0, 0]
            then [[BPair.ofNat 2]] else [[BPair.ofNat 1]])
            w.content) w.coords))
        (elim.matVec ((fun mu => if mu = [0, 0]
            then [[BPair.ofNat 2]] else [[BPair.ofNat 1]])
            (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords)) := by decide +kernel

example : ¬ (∀ k, k < [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)
            :: [⟨[0, 0], [BPair.ofNat 1]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
          [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)] k)) := by decide +kernel

example : ¬ (∀ w ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[0, 0], [BPair.ofNat 1]⟩],
    poly.oneValue
      (elim.vecScale
        (elim.dotP [BPair.ofNat 1] [BPair.ofNat 1])
        (elim.matVec ((fun mu => if mu = [0, 0]
          then [[BPair.ofNat 2]] else [[BPair.ofNat 1]]) w.content)
          w.coords))
      (elim.vecScale
        (elim.dotP
          (elim.matVec ((fun mu => if mu = [0, 0]
            then [[BPair.ofNat 2]] else [[BPair.ofNat 1]]) [1, 0])
            [BPair.ofNat 1])
          [BPair.ofNat 1])
        w.coords)) := by decide +kernel

/-! Clause (iv)'s dimension read `dim_eq`: the positive pin at two
genuinely independent tops of one content, each hypothesis decided
at the committed pools with the counts' equality, and the four
isolating refusals — shared content, independence, closure, and
provenance — each forged pool at every surviving hypothesis with
the counts' failure decided.  The sized, width and top binders are
the tex's frame (`lem:blockirr`(iv)'s two tops at the span
calculus's stated data): sized rides `indepAll`'s per-group width
read, and a raising image's group sits above the head where the
height fold refuses every word, so the frame is derivable at the
stated data and refusals cannot isolate it. -/

/-- The committed pair: sized and width at both pools. -/
example : ∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩],
    sized w ∧ w.content.length = 2 := by decide +kernel

example : ∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩],
    sized w ∧ w.content.length = 2 := by decide +kernel

/-- The committed pair: the provenance at both pools. -/
example : ∀ k, k < [act 1 0 (⟨[2, 1], [BPair.ofNat 1,
      (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec)].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec)
            :: [act 1 0 ⟨[2, 1], [BPair.ofNat 1,
              (BPair.ofNat 1).swap, BPair.unit]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
          [act 1 0 (⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec)] k) := by decide +kernel

example : ∀ k, k < [act 1 0 (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩ : HVec)].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[2, 1], [BPair.ofNat 1, BPair.unit,
            (BPair.ofNat 1).swap]⟩ : HVec)
            :: [act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
              (BPair.ofNat 1).swap]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
          [act 1 0 (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
            (BPair.ofNat 1).swap]⟩ : HVec)] k) := by decide +kernel

/-- The committed pair: the group independence at both pools. -/
example : indepAll [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩] := by decide +kernel

example : indepAll [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩] := by decide +kernel

/-- The committed pair: the closure at both pools. -/
example : ∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩],
    ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          BPair.unit]⟩ : HVec),
        act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          BPair.unit]⟩] (act i j w) := by decide +kernel

example : ∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩],
    ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩ : HVec),
        act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩] (act i j w) := by decide +kernel

/-- The committed pair: the two heads' top reads. -/
example : ∀ j, j < 2 → ∀ i, i < j →
    poly.unitTail (act i j (⟨[2, 1], [BPair.ofNat 1,
      (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec)).coords
      ∧ poly.unitTail (act i j (⟨[2, 1], [BPair.ofNat 1,
        BPair.unit, (BPair.ofNat 1).swap]⟩ : HVec)).coords
  := by decide +kernel

/-- The committed pair: the counts' equality, `dim_eq`'s display at
two genuinely independent tops. -/
example : [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩].length
    = [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩].length := by decide +kernel

/-- The shared-content binder is load-bearing: at the unit-content
partner pool every further hypothesis holds — sized, width, the
vacuous provenance, independence, closure and the top read — and
the counts differ. -/
example : (∀ w ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
      sized w ∧ w.content.length = 2)
    ∧ (∀ k, k < ([] : List HVec).length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
        lowerH j (getAt (⟨[], []⟩ : HVec)
            [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)] i)
          = some (getAt (⟨[], []⟩ : HVec) ([] : List HVec) k))
    ∧ indepAll [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)]
    ∧ (∀ w ∈ [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)],
      ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
        settledAt [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)] (act i j w))
    ∧ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail
        (act i j (⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)).coords)
    := by decide +kernel

example : ¬ ([2, 1] = [0, 0])
    ∧ ¬ ([(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩].length
      = [(⟨[0, 0], [BPair.ofNat 1]⟩ : HVec)].length) := by decide +kernel

/-- The independence binder is load-bearing: the duplicated
lowering's pool keeps sized, width, provenance, closure and the
top read, refuses the independence, and the counts differ. -/
example : ¬ indepAll [(⟨[2, 1], [BPair.ofNat 1,
      (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩,
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩] := by decide +kernel

example : (∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩],
      sized w ∧ w.content.length = 2)
    ∧ (∀ k, k < [act 1 0 (⟨[2, 1], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩].length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
        lowerH j (getAt (⟨[], []⟩ : HVec)
            ((⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
              BPair.unit]⟩ : HVec)
              :: [act 1 0 ⟨[2, 1], [BPair.ofNat 1,
                (BPair.ofNat 1).swap, BPair.unit]⟩,
              act 1 0 ⟨[2, 1], [BPair.ofNat 1,
                (BPair.ofNat 1).swap, BPair.unit]⟩]) i)
          = some (getAt (⟨[], []⟩ : HVec)
            [act 1 0 (⟨[2, 1], [BPair.ofNat 1,
              (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec),
            act 1 0 ⟨[2, 1], [BPair.ofNat 1,
              (BPair.ofNat 1).swap, BPair.unit]⟩] k))
    ∧ (∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩],
      ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
        settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec),
          act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩,
          act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩] (act i j w))
    ∧ ¬ ([(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩].length
      = [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩ : HVec),
        act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩].length) := by decide +kernel

/-- The closure binder is load-bearing: the lowering-stripped pool
keeps sized, width, the vacuous provenance, independence and the
top read, refuses the closure at the adjacent lowering, and the
counts differ. -/
example : ¬ (∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1,
      (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec)],
    ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)] (act i j w)) := by decide +kernel

example : (∀ k, k < ([] : List HVec).length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
        lowerH j (getAt (⟨[], []⟩ : HVec)
            [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
              BPair.unit]⟩ : HVec)] i)
          = some (getAt (⟨[], []⟩ : HVec) ([] : List HVec) k))
    ∧ indepAll [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩ : HVec)]
    ∧ ¬ ([(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)].length
      = [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩ : HVec),
        act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩].length) := by decide +kernel

/-- The provenance binder is load-bearing: the two-blocks-stacked
pool keeps sized, width, independence, closure and the top read,
refuses the provenance at the second head, and the counts
differ. -/
example : ¬ (∀ k, k < [act 1 0 (⟨[2, 1], [BPair.ofNat 1,
      (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec),
    (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec)
            :: [act 1 0 ⟨[2, 1], [BPair.ofNat 1,
              (BPair.ofNat 1).swap, BPair.unit]⟩,
            ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
              (BPair.ofNat 1).swap]⟩,
            act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
              (BPair.ofNat 1).swap]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
          [act 1 0 (⟨[2, 1], [BPair.ofNat 1,
            (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec),
          (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
            (BPair.ofNat 1).swap]⟩ : HVec),
          act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
            (BPair.ofNat 1).swap]⟩] k)) := by decide +kernel

example : (∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      ⟨[2, 1], [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩],
      sized w ∧ w.content.length = 2)
    ∧ indepAll [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      ⟨[2, 1], [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩]
    ∧ (∀ w ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      ⟨[2, 1], [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩],
      ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
        settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec),
          act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩,
          ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
            (BPair.ofNat 1).swap]⟩,
          act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
            (BPair.ofNat 1).swap]⟩] (act i j w))
    ∧ ¬ ([(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩,
      ⟨[2, 1], [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]⟩,
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩].length
      = [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩ : HVec),
        act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap]⟩].length) := by decide +kernel

/-- The committed pair reads `dim_eq` applied whole, every
hypothesis its own decided instance. -/
example : [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩ : HVec),
    act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩].length
    = [(⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec),
      act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩].length :=
  blockirr.dim_eq 2
    ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
    [act 1 0 ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
      BPair.unit]⟩]
    ⟨[2, 1], [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]⟩
    [act 1 0 ⟨[2, 1], [BPair.ofNat 1, BPair.unit,
      (BPair.ofNat 1).swap]⟩]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
