import MassGap.Tops
/-!
The check module for `lem:tops`(i): the vacant-group top read at
the fundamental's pool — the raising image's content unoccupied
and the image at the unit tail, `max_top` applied whole — and the
occupancy refusal: at a pool occupying the raised content the
settled read holds through the occupied group's span while the
image sits off the unit tail.
-/

open ground places blockcount

/-- The committed instance: the head's raising settled at the
vacant group with the occupancy read, `max_top`'s two
hypotheses. -/
example : (∀ j, j < 2 → ∀ i, i < j →
      settledAt [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[0, 1], [BPair.ofNat 1]⟩]
        (act i j (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)))
    ∧ (∀ j, j < 2 → ∀ i, i < j →
      occ (moveAt i j [1, 0])
        [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[0, 1], [BPair.ofNat 1]⟩] = 0) := by decide +kernel

/-- The committed instance reads `max_top` applied whole. -/
example : ∀ j, j < 2 → ∀ i, i < j →
    poly.unitTail
      (act i j (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec)).coords :=
  tops.max_top 2
    [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec), ⟨[0, 1], [BPair.ofNat 1]⟩]
    ⟨[1, 0], [BPair.ofNat 1]⟩
    (by decide +kernel) (by decide +kernel)

/-- The occupancy binder is load-bearing: at the pool occupying
the raised content the settled read holds through the occupied
group's span, the occupancy refuses, and the image sits off the
unit tail. -/
example : (∀ j, j < 2 → ∀ i, i < j →
      settledAt [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 0], [BPair.ofNat 1]⟩]
        (act i j (⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)))
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      occ (moveAt i j [0, 1])
        [(⟨[0, 1], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 0], [BPair.ofNat 1]⟩] = 0)
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail
        (act i j (⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)).coords)
  := by decide +kernel

/-- Clause (ii)'s pin: the committed top's content is dominant,
`dominant` applied whole at its decided hypotheses. -/
example : ∀ k, k + 1 < 2 →
    ground.getAt 0 ([2, 1] : List Nat) (k + 1)
      ≤ ground.getAt 0 ([2, 1] : List Nat) k :=
  tops.dominant 2
    ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The off-unit binder is load-bearing: at the unit-tail member
every raising image reads the unit tail while the content ascends
— the top read holds, the off-unit read refuses, and the
dominance refuses with it. -/
example : (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail
        (act i j (⟨[0, 1], [BPair.unit]⟩ : HVec)).coords)
    ∧ ¬ ¬ poly.unitTail
        (⟨[0, 1], [BPair.unit]⟩ : HVec).coords
    ∧ ¬ (∀ k, k + 1 < 2 →
      ground.getAt 0 ([0, 1] : List Nat) (k + 1)
        ≤ ground.getAt 0 ([0, 1] : List Nat) k) := by decide +kernel

/-- The top binder is load-bearing: at an ascending content with
an occupied member the raising survives — the off-unit read holds,
the top read refuses, and the dominance refuses with it. -/
example : ¬ poly.unitTail
      (⟨[0, 1], [BPair.ofNat 1]⟩ : HVec).coords
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail
        (act i j (⟨[0, 1], [BPair.ofNat 1]⟩ : HVec)).coords)
    ∧ ¬ (∀ k, k + 1 < 2 →
      ground.getAt 0 ([0, 1] : List Nat) (k + 1)
        ≤ ground.getAt 0 ([0, 1] : List Nat) k) := by decide +kernel
