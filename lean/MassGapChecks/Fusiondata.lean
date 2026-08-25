import MassGap.Fusiondata
import MassGapChecks.Blockcount
/-!
The check module for the exhaustion tier's block dimension: the
seed's closure pool against the shape's own span at the committed
top — `seedBlock_dim` applied whole with the display's two counts
decided, the shape inverse's read among the pins.  The producer's
reads, the descent's completeness, the split's two clauses, the
orthogonality tier, the exhaustion count, the dimension display
and its graded refinement at the blocks' occupancies
close the module, each theorem applied whole at committed carriers
with its conclusion's value decided beside it and the load-bearing
binders' isolating refusals pinned.  The fusion identities sit at
the end: the fusion count at the fused pool's own
count, a shape's block reading the Kronecker delta at its row list,
and the unit shape's line reading the first factor back — the last
one's width binder the frame, its probe record standing where a
refusal would.
-/

open ground places blockcount

/-- The committed top's shape inverse reads back. -/
example : rowList (shapeOf [2, 1]) = [2, 1] := by decide +kernel

/-- The committed top's closure pool reads the shape's own count,
`seedBlock_dim` applied whole. -/
example : (closeSpan 2 (lowerspan.ht [2, 1])
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]).length
    = (blockSpan (shapeOf [2, 1])).length :=
  blockcount.seedBlock_dim 2
    ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (lowerspan.ht [2, 1]) (Nat.le_refl _)

/-- The display's two counts decided at the committed data. -/
example : (closeSpan 2 (lowerspan.ht [2, 1])
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]).length = 2
    ∧ (blockSpan (shapeOf [2, 1])).length = 2 := by decide +kernel

/-- The committed top's closure pool reads the shape's own
occupancy content by content, `seedBlock_occ` applied whole at
the block's two contents. -/
example : occ [2, 1] (closeSpan 2 (lowerspan.ht [2, 1])
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)])
    = occ [2, 1] (blockSpan (shapeOf [2, 1])) :=
  blockcount.seedBlock_occ 2
    ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (lowerspan.ht [2, 1]) (Nat.le_refl _) [2, 1]

example : occ [1, 2] (closeSpan 2 (lowerspan.ht [2, 1])
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)])
    = occ [1, 2] (blockSpan (shapeOf [2, 1])) :=
  blockcount.seedBlock_occ 2
    ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (lowerspan.ht [2, 1]) (Nat.le_refl _) [1, 2]

/-- The two occupancies' shared values at the committed data. -/
example : occ [2, 1] (blockSpan (shapeOf [2, 1])) = 1
    ∧ occ [1, 2] (blockSpan (shapeOf [2, 1])) = 1 := by decide +kernel

/-- The fuel bound at a strictly larger fuel, the at-or-beyond
read exercised off the reflexive instance. -/
example : occ [2, 1] (closeSpan 2 (lowerspan.ht [2, 1] + 1)
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)]
      [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)])
    = occ [2, 1] (blockSpan (shapeOf [2, 1])) :=
  blockcount.seedBlock_occ 2
    ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (lowerspan.ht [2, 1] + 1) (Nat.le_succ _) [2, 1]


/-- The producer at the degree-two power's monomial carrier: two
rounds, the symmetric block's top at the two-box row then the
column pair's antisymmetric survivor, the residual carrier dying
at the second block. -/
example : (exhaust 2
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩]).length = 2 := by decide +kernel

example : (exhaust 2
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩]).map HVec.content
    = [[2, 0], [1, 1]] := by decide +kernel

/-- The pick reads at the committed carrier: the height-maximal
member off the unit tail, its three reads decided. -/
example : pickTop
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩]
    = some ⟨[2, 0], [BPair.ofNat 1]⟩ := by decide +kernel

example : pickTop
      [(⟨[1, 0], [BPair.unit]⟩ : HVec)] = none := by decide +kernel

/-! The producer's theorem reads: the pick's top read, the
residual carrier's invariants with the closure, and the
exhaustion's members — application pins at the degree-two
monomial carrier with the load-bearing hypotheses' isolating
refusals, every surviving co-binder kernel-decided beside each. -/

/-- The committed block reads its literal members: the top, the
paired lowering, and the doubled bottom. -/
example : closeSpan 2 (lowerspan.ht [2, 0])
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)]
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)]
  = [⟨[2, 0], [BPair.ofNat 1]⟩,
     ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
     ⟨[0, 2], [BPair.ofNat 2]⟩] := by decide +kernel

/-- The pick's top read applied whole at the carrier. -/
example : ∀ j, j < 2 → ∀ i, i < j →
    poly.unitTail (act i j
      (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)).coords :=
  pickTop_top 2
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 1]⟩]
    (by decide +kernel) (by decide +kernel)
    ⟨[2, 0], [BPair.ofNat 1]⟩ (by decide +kernel)

/-- The pick's closure hypothesis is load-bearing: at the
unclosed singleton the pick's raising image sits off the unit
tail — the surviving co-binders decided beside the refusal. -/
example : ((∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      x.content.length = 2)
    ∧ (∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      ¬ poly.unitTail x.coords)
    ∧ pickTop [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
        = some ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩)
    ∧ ¬ (∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
          (act i j x))
    ∧ ¬ (∀ j < 2, ∀ i < j,
      poly.unitTail (act i j
        (⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)).coords)
  := by decide +kernel

/-- The residual carrier's closure applied whole at the carrier
against the committed block. -/
example : ∀ y ∈ residCarrier
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩]
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 2]⟩],
    ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt (residCarrier
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 1]⟩]
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 2]⟩]) (act i j y) :=
  residCarrier_closed 2
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 1]⟩]
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 2]⟩]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The stated carrier's closure hypothesis is load-bearing: at
the unclosed singleton against the vacant block the residual's
raising image escapes — the surviving co-binders decided beside
the refusal. -/
example : ((∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      sized x)
    ∧ (∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      x.content.length = 2)
    ∧ (∀ x ∈ ([] : List HVec), sized x)
    ∧ (∀ x ∈ ([] : List HVec),
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt ([] : List HVec) (act i j x)))
    ∧ ¬ (∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
          (act i j x))
    ∧ ¬ (∀ y ∈ residCarrier
        [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
        ([] : List HVec),
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt (residCarrier
          [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
          ([] : List HVec)) (act i j y)) := by decide +kernel

/-- The block's closure hypothesis is load-bearing: at the
unclosed one-member block the carrier's residuals lose the
withdrawn image — the surviving co-binders decided beside the
refusal. -/
example : ((∀ x ∈
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt
          [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
            ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
            ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 1]⟩] (act i j x))
    ∧ (∀ x ∈
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩],
      sized x ∧ x.content.length = 2)
    ∧ (∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      sized x))
    ∧ ¬ (∀ x ∈ [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)]
          (act i j x))
    ∧ ¬ (∀ y ∈ residCarrier
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 1]⟩]
        [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt (residCarrier
          [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
            ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
            ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 1]⟩]
          [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec)])
          (act i j y)) := by decide +kernel

/-- The residual carrier's reads applied whole at the carrier
against the committed block. -/
example : (∀ y ∈ residCarrier
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩]
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 2]⟩],
    sized y ∧ y.content.length = 2
      ∧ ¬ poly.unitTail y.coords) := by decide +kernel

/-- The exhaustion's members are tops, applied whole at the
degree-two monomial carrier. -/
example : ∀ w ∈ exhaust 2
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩],
    sized w ∧ w.content.length = 2
      ∧ (¬ poly.unitTail w.coords)
      ∧ ∀ j, j < 2 → ∀ i, i < j →
          poly.unitTail (act i j w).coords :=
  exhaust_top 2
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 1]⟩]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The closure at a dependent stated block: the collected groups
read the residuals whole, the joined-collection read's own
instance. -/
example : ∀ y ∈ residCarrier
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 1]⟩]
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
     ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
     ⟨[0, 2], [BPair.ofNat 2]⟩,
     ⟨[2, 0], [BPair.ofNat 2]⟩],
    ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt (residCarrier
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 1]⟩]
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
         ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
         ⟨[0, 2], [BPair.ofNat 2]⟩,
         ⟨[2, 0], [BPair.ofNat 2]⟩]) (act i j y) := by decide +kernel

/-- The closure applied whole at the width-three degree-two
carrier against the symmetric block. -/
example : ∀ y ∈ residCarrier
      [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
        ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 0, 2], [BPair.ofNat 1]⟩]
      (closeSpan 3 (lowerspan.ht [2, 0, 0])
        [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec)]
        [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec)]),
    ∀ i, i < 3 → ∀ j, j < 3 → ¬ i = j →
      settledAt (residCarrier
        [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
          ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 0, 2], [BPair.ofNat 1]⟩]
        (closeSpan 3 (lowerspan.ht [2, 0, 0])
          [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec)]
          [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec)]))
        (act i j y) :=
  residCarrier_closed 3
    [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
      ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 0, 2], [BPair.ofNat 1]⟩]
    (closeSpan 3 (lowerspan.ht [2, 0, 0])
      [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec)]
      [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The producer at the width-three degree-two carrier: the
symmetric top then the antisymmetric survivor. -/
example : (exhaust 3
      [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
        ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 0, 2], [BPair.ofNat 1]⟩]).map HVec.content
    = [[2, 0, 0], [1, 1, 0]] := by decide +kernel

/-! The descent's completeness: every stated member inside the
produced blocks' joined span — `exhaust_span` applied whole at
both widths, the strict decrease's two reads, the fuel binder's
isolating refusal with the surviving co-binders decided beside it,
and the positive pins at the unclosed and unit-bearing carriers,
the off-unit and closure binders the orthogonality half's. -/

/-- The completeness applied whole at the degree-two monomial
carrier. -/
example : ∀ x ∈
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩],
    elim.spanRel x.coords.length
      (groupAt (blockJoin 2 (exhaust 2
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 1]⟩])) x.content)
      x.coords :=
  exhaust_span 2
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 1]⟩]
    (by decide +kernel) (by decide +kernel)

/-- The completeness applied whole at the width-three degree-two
carrier. -/
example : ∀ x ∈
      [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
        ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 0, 2], [BPair.ofNat 1]⟩],
    elim.spanRel x.coords.length
      (groupAt (blockJoin 3 (exhaust 3
        [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
          ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
          ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
          ⟨[0, 0, 2], [BPair.ofNat 1]⟩])) x.content)
      x.coords :=
  exhaust_span 3
    [(⟨[2, 0, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1, 0], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 1, 0], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[1, 0, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[1, 0, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 2, 0], [BPair.ofNat 1]⟩,
      ⟨[0, 1, 1], [BPair.ofNat 1, BPair.unit]⟩,
      ⟨[0, 1, 1], [BPair.unit, BPair.ofNat 1]⟩,
      ⟨[0, 0, 2], [BPair.ofNat 1]⟩]
    (by decide +kernel) (by decide +kernel)

/-- The round's strict decrease: the pick's residual at its own
block reads the unit family, and the residual carrier is strictly
shorter. -/
example : allU (residAt
      (closeSpan 2 (lowerspan.ht [2, 0])
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)]
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)])
      ⟨[2, 0], [BPair.ofNat 1]⟩).coords = true
    ∧ (residCarrier
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
        ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 1]⟩]
      (closeSpan 2 (lowerspan.ht [2, 0])
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)]
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)])).length < 4 := by
  decide +kernel

/-- The fuel binder is load-bearing: at fuel short of the
carrier's length an off-unit member escapes the empty join — the
surviving co-binders decided beside the refusal. -/
example : ((∀ x ∈ [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)], sized x)
      ∧ (∀ x ∈ [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)],
        x.content.length = 2))
    ∧ ¬ ∀ x ∈ [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)],
      elim.spanRel x.coords.length
        (groupAt (blockJoin 2 (exhaustGo 2 0
          [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)])) x.content)
        x.coords := by decide +kernel

/-- The completeness at an unclosed carrier: the closure binder is
the orthogonality half's, the span read holding without it. -/
example : ∀ x ∈
      [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec),
        ⟨[2, 0], [BPair.ofNat 1]⟩],
    elim.spanRel x.coords.length
      (groupAt (blockJoin 2 (exhaust 2
        [(⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩ : HVec),
          ⟨[2, 0], [BPair.ofNat 1]⟩])) x.content)
      x.coords := by decide +kernel

/-- The completeness at a unit-bearing carrier: the off-unit
binder is the producer's top read's, the span read holding
without it. -/
example : ∀ x ∈
      [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[1, 1], [BPair.unit, BPair.unit]⟩],
    elim.spanRel x.coords.length
      (groupAt (blockJoin 2 (exhaust 2
        [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[1, 1], [BPair.unit, BPair.unit]⟩])) x.content)
      x.coords := by decide +kernel

/-! The raising kernels' split at the orthogonal split
(`top_split`): the theorem applied whole at the committed block
pair, and the isolating refusals — the closure binders at each
side, the two perpendicularity binders, the top and span reads —
each forged datum's surviving co-binders kernel-decided beside
it. -/

/-- The split applied whole at the committed pair: the
`[2,0]`-block against the antisymmetric line, the doubled
antisymmetric top's residual and combination both tops of their
sides. -/
example :
    elim.spanRel (places.monomialsAt [1, 1]).length
      (groupAt [(⟨[1, 1], [BPair.ofNat 1,
          (BPair.ofNat 1).swap]⟩ : HVec)] [1, 1])
      (elim.residV (places.monomialsAt [1, 1]).length
        (elim.collectOf (places.monomialsAt [1, 1]).length
          (groupAt [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
            ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩] [1, 1]))
        [BPair.ofNat 2, (BPair.ofNat 2).swap])
    ∧ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [1, 1]) [1, 1] i j)
        (elim.residV (places.monomialsAt [1, 1]).length
          (elim.collectOf (places.monomialsAt [1, 1]).length
            (groupAt [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
              ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
              ⟨[0, 2], [BPair.ofNat 2]⟩] [1, 1]))
          [BPair.ofNat 2, (BPair.ofNat 2).swap]))) :=
  ⟨(top_split 2 [1, 1]
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 2]⟩]
    [(⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    [BPair.ofNat 2, (BPair.ofNat 2).swap]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).1,
   (top_split 2 [1, 1]
    [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 2]⟩]
    [(⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    [BPair.ofNat 2, (BPair.ofNat 2).swap]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2.1⟩

/-- The head's closure binder is load-bearing: at the raising-open
head list the top's residual reads an occupied raising image — the
surviving co-binders decided beside the refusal. -/
example :
    ((∀ x ∈ [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
        BPair.ofNat 1]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩],
      ∀ j, j < 2 → ∀ i, i < j →
        settledAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
          BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] (act i j x))
    ∧ (∀ k, k < (groupAt [(⟨[2, 1], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, (BPair.ofNat 1).swap]⟩ : HVec)]
        [2, 1]).length →
      ∀ l, l < (groupAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
        BPair.ofNat 1]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩] [2, 1]).length →
      (elim.dotP (ground.getAt [] (groupAt
        [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          (BPair.ofNat 1).swap]⟩ : HVec)] [2, 1]) k)
        (ground.getAt [] (groupAt
          [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
            BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] [2, 1]) l)).oneValue
        BPair.unit)
    ∧ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        [BPair.ofNat 6, (BPair.ofNat 3).swap,
          (BPair.ofNat 3).swap]))
    ∧ elim.spanRel (places.monomialsAt [2, 1]).length
      (groupAt ([(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          (BPair.ofNat 1).swap]⟩ : HVec)]
        ++ [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
          BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩]) [2, 1])
      [BPair.ofNat 6, (BPair.ofNat 3).swap, (BPair.ofNat 3).swap])
    ∧ ¬ (∀ x ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        (BPair.ofNat 1).swap]⟩ : HVec)],
      ∀ j, j < 2 → ∀ i, i < j →
        settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          (BPair.ofNat 1).swap]⟩ : HVec)] (act i j x))
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        (elim.residV (places.monomialsAt [2, 1]).length
          (elim.collectOf (places.monomialsAt [2, 1]).length
            (groupAt [(⟨[2, 1], [BPair.ofNat 1,
              (BPair.ofNat 1).swap, (BPair.ofNat 1).swap]⟩ : HVec)]
              [2, 1]))
          [BPair.ofNat 6, (BPair.ofNat 3).swap,
            (BPair.ofNat 3).swap]))) := by decide +kernel

/-- The tail's closure binder is load-bearing: at the raising-open
tail list the residual sits in the tail's span while its raising
image reads occupied. -/
example :
    ((∀ x ∈ [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
        BPair.ofNat 1]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩],
      ∀ j, j < 2 → ∀ i, i < j →
        settledAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
          BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] (act i j x))
    ∧ elim.spanRel (places.monomialsAt [2, 1]).length
      (groupAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        (BPair.ofNat 1).swap]⟩ : HVec)] [2, 1])
      (elim.residV (places.monomialsAt [2, 1]).length
        (elim.collectOf (places.monomialsAt [2, 1]).length
          (groupAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
            BPair.ofNat 1]⟩ : HVec),
            ⟨[3, 0], [BPair.ofNat 1]⟩] [2, 1]))
        [BPair.ofNat 6, (BPair.ofNat 3).swap,
          (BPair.ofNat 3).swap]))
    ∧ ¬ (∀ x ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        (BPair.ofNat 1).swap]⟩ : HVec)],
      ∀ j, j < 2 → ∀ i, i < j →
        settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          (BPair.ofNat 1).swap]⟩ : HVec)] (act i j x))
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        (elim.residV (places.monomialsAt [2, 1]).length
          (elim.collectOf (places.monomialsAt [2, 1]).length
            (groupAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
              BPair.ofNat 1]⟩ : HVec),
              ⟨[3, 0], [BPair.ofNat 1]⟩] [2, 1]))
          [BPair.ofNat 6, (BPair.ofNat 3).swap,
            (BPair.ofNat 3).swap]))) := by decide +kernel

/-- The content's perpendicularity binder is load-bearing: at two
crossing top lines the residual escapes the tail's span. -/
example :
    ((∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap]))
    ∧ ¬ (∀ k, k < (groupAt [(⟨[2, 1], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec)] [2, 1]).length →
      ∀ l, l < (groupAt [(⟨[2, 1], [BPair.unit, BPair.ofNat 1,
        (BPair.ofNat 1).swap]⟩ : HVec)] [2, 1]).length →
      (elim.dotP (ground.getAt [] (groupAt
        [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          BPair.unit]⟩ : HVec)] [2, 1]) k)
        (ground.getAt [] (groupAt
          [(⟨[2, 1], [BPair.unit, BPair.ofNat 1,
            (BPair.ofNat 1).swap]⟩ : HVec)] [2, 1]) l)).oneValue
        BPair.unit))
    ∧ ¬ (elim.spanRel (places.monomialsAt [2, 1]).length
      (groupAt [(⟨[2, 1], [BPair.unit, BPair.ofNat 1,
        (BPair.ofNat 1).swap]⟩ : HVec)] [2, 1])
      (elim.residV (places.monomialsAt [2, 1]).length
        (elim.collectOf (places.monomialsAt [2, 1]).length
          (groupAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec)] [2, 1]))
        [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap])) := by
  decide +kernel

/-- The moved contents' perpendicularity binder is load-bearing:
at sides perpendicular at the content but crossing at the raised
one, the residual's raising image reads occupied. -/
example :
    ((∀ x ∈ [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        (BPair.ofNat 1).swap]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩],
      ∀ j, j < 2 → ∀ i, i < j →
        settledAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          (BPair.ofNat 1).swap]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] (act i j x)))
    ∧ ¬ (∀ k, k < (groupAt [(⟨[2, 1], [BPair.ofNat 2,
        BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩] (moveAt 0 1 [2, 1])).length →
      ∀ l, l < (groupAt [(⟨[2, 1], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, (BPair.ofNat 1).swap]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩] (moveAt 0 1 [2, 1])).length →
      (elim.dotP (ground.getAt [] (groupAt
        [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
          BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] (moveAt 0 1 [2, 1])) k)
        (ground.getAt [] (groupAt
          [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            (BPair.ofNat 1).swap]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] (moveAt 0 1 [2, 1])) l)).oneValue
        BPair.unit)
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        (elim.residV (places.monomialsAt [2, 1]).length
          (elim.collectOf (places.monomialsAt [2, 1]).length
            (groupAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
              BPair.ofNat 1]⟩ : HVec),
              ⟨[3, 0], [BPair.ofNat 1]⟩] [2, 1]))
          [BPair.ofNat 6, (BPair.ofNat 3).swap,
            (BPair.ofNat 3).swap]))) := by decide +kernel

/-- The top binder is load-bearing: at a raising-occupied member
of the tail's own span the residual keeps the occupied image —
the surviving co-binders decided beside the refusal, the span
read among them. -/
example :
    ((∀ x ∈ [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
        BPair.ofNat 1]⟩ : HVec),
        ⟨[3, 0], [BPair.ofNat 1]⟩],
      ∀ j, j < 2 → ∀ i, i < j →
        settledAt [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
          BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩] (act i j x))
    ∧ elim.spanRel (places.monomialsAt [2, 1]).length
      (groupAt (([] : List HVec)
        ++ [(⟨[2, 1], [BPair.ofNat 2, BPair.ofNat 1,
          BPair.ofNat 1]⟩ : HVec),
          ⟨[3, 0], [BPair.ofNat 1]⟩]) [2, 1])
      [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 1])
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 1]))
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        (elim.residV (places.monomialsAt [2, 1]).length
          (elim.collectOf (places.monomialsAt [2, 1]).length
            (groupAt ([] : List HVec) [2, 1]))
          [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 1]))) := by
  decide +kernel

/-- The span binder is load-bearing: off the joined span the
residual escapes the tail. -/
example :
    ((∀ j, j < 2 → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j [2, 1]) [2, 1] i j)
        [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap]))
    ∧ ¬ elim.spanRel (places.monomialsAt [2, 1]).length
      (groupAt ([(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)] ++ ([] : List HVec)) [2, 1])
      [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap])
    ∧ ¬ (elim.spanRel (places.monomialsAt [2, 1]).length
      (groupAt ([] : List HVec) [2, 1])
      (elim.residV (places.monomialsAt [2, 1]).length
        (elim.collectOf (places.monomialsAt [2, 1]).length
          (groupAt [(⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
            BPair.unit]⟩ : HVec)] [2, 1]))
        [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap])) := by
  decide +kernel

/-! The count's additivity over the split (`countAt_append`): the
theorem applied whole at the committed orthogonal pair — the
symmetric degree-two block against the wedge line at width two —
with the joined pool's value beside it, and the refusal isolating
the perpendicularity binders at a pool joined to itself, where
every other binder survives.  The surviving binders are pinned
beside the refusal: the sizes at the block and the closure read at
the doubled pool. -/

/-- The count adds over the committed orthogonal split,
`countAt_append` applied whole: the symmetric block against the
wedge line at width two, every binder decided. -/
example : countAt (blockSpan (shapeOf [2, 0]) ++ blockSpan (shapeOf [1, 1]))
      [1, 1]
    = countAt (blockSpan (shapeOf [2, 0])) [1, 1]
      + countAt (blockSpan (shapeOf [1, 1])) [1, 1] :=
  countAt_append [1, 1] _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The theorem applied whole at a committed pair occupying the
perpendicularity's moved content on both sides: the two blocks at
row lists `[3, 0]` and `[2, 1]` share the moved content `[2, 1]`
above `[1, 2]`, so the split's raised pairing quantifier reads an
occupied pair, and each side's count at `[1, 2]` is nought. -/
example : countAt (blockSpan (shapeOf [3, 0]) ++ blockSpan (shapeOf [2, 1]))
      [1, 2]
    = countAt (blockSpan (shapeOf [3, 0])) [1, 2]
      + countAt (blockSpan (shapeOf [2, 1])) [1, 2] :=
  countAt_append [1, 2] _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The occupied-move instance's value: nought on both sides and
at the join. -/
example : countAt (blockSpan (shapeOf [3, 0])
      ++ blockSpan (shapeOf [2, 1])) [1, 2] = 0
    ∧ (groupAt (blockSpan (shapeOf [3, 0])) [2, 1]).length = 1
    ∧ (groupAt (blockSpan (shapeOf [2, 1])) [2, 1]).length = 1 := by
  decide +kernel

/-- The joined pool's own value at the wedge content: the wedge
line's one against the symmetric block's nought. -/
example : countAt (blockSpan (shapeOf [2, 0])
      ++ blockSpan (shapeOf [1, 1])) [1, 1] = 1 := by decide +kernel

/-- Refusal at the split's content perpendicularity,
`countAt_append`'s `hperpMu` binder: a pool joined to itself keeps
the sizes, the closure and the raised perpendicularity (the moved
group above `[2, 0]` is unoccupied, pinned below) while the
`[2, 0]` groups are parallel, the count reads the one collection,
and the sum doubles it. -/
example : ¬ (countAt (blockSpan (shapeOf [2, 0])
      ++ blockSpan (shapeOf [2, 0])) [2, 0]
    = countAt (blockSpan (shapeOf [2, 0])) [2, 0]
      + countAt (blockSpan (shapeOf [2, 0])) [2, 0]) := by decide +kernel

/-- The sizes binder survives the refusal's forgery: every member
of the block sits at its content's enumeration width. -/
example : (∀ x ∈ blockSpan (shapeOf [2, 0]), sized x) := by decide +kernel

/-- The closure binder survives it too: at the doubled pool every
member's adjacent raising image is settled inside the pool's own
group. -/
example : (∀ x ∈ blockSpan (shapeOf [2, 0]) ++ blockSpan (shapeOf [2, 0]),
    ∀ i, i + 1 < ([2, 0] : List Nat).length →
      settledAt (blockSpan (shapeOf [2, 0])
        ++ blockSpan (shapeOf [2, 0])) (act i (i + 1) x)) := by decide +kernel

/-- The raised perpendicularity survives the refusal's forgery as
well, its moved group unoccupied at the doubled pool: the refusal
isolates the content perpendicularity alone.  Its own isolating
refusal — a pair perpendicular at the content and parallel at an
occupied moved content — is landed below, at two width-two pools
sharing one member at the raised content. -/
example : ∀ i, i + 1 < ([2, 0] : List Nat).length →
    ∀ k, k < (groupAt (blockSpan (shapeOf [2, 0]))
      (moveAt i (i + 1) [2, 0])).length →
    ∀ l, l < (groupAt (blockSpan (shapeOf [2, 0]))
      (moveAt i (i + 1) [2, 0])).length →
    (elim.dotP
      (ground.getAt [] (groupAt (blockSpan (shapeOf [2, 0]))
        (moveAt i (i + 1) [2, 0])) k)
      (ground.getAt [] (groupAt (blockSpan (shapeOf [2, 0]))
        (moveAt i (i + 1) [2, 0])) l)).oneValue BPair.unit := by
  decide +kernel

/-! Refusal at the split's raised perpendicularity,
`countAt_append`'s `hperpUp` binder, the read owed above.  Two
width-two pools share one member at the raised content `[2, 0]`,
so their raised groups are parallel, while their `[1, 1]` groups
pair at the sum's unit; each member's adjacent raising image sits
inside its own pool's raised group's span, so the closure survives
on both sides.  The two `[1, 1]` members' raising images are one
line, so the joined collection carries a kernel line neither side
carries and the additivity parts. -/

private def upA : List HVec :=
  [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 1]⟩,
   ⟨[2, 0], [BPair.ofNat 1]⟩]

private def upB : List HVec :=
  [⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 2).swap]⟩,
   ⟨[2, 0], [BPair.ofNat 1]⟩]

/-- The sizes binders survive at both pools. -/
example : ∀ x ∈ upA, sized x := by decide +kernel

example : ∀ x ∈ upB, sized x := by decide +kernel

/-- The closure binders survive at both pools: the `[1, 1]`
member's raising image sits inside its own pool's `[2, 0]` group's
span, and the `[2, 0]` member's image reads the sum's unit. -/
example : ∀ x ∈ upA, ∀ i, i + 1 < ([1, 1] : List Nat).length →
    settledAt upA (act i (i + 1) x) := by decide +kernel

example : ∀ x ∈ upB, ∀ i, i + 1 < ([1, 1] : List Nat).length →
    settledAt upB (act i (i + 1) x) := by decide +kernel

/-- The content perpendicularity survives: the two pools' `[1, 1]`
groups pair at the sum's unit. -/
example : ∀ k, k < (groupAt upA [1, 1]).length →
    ∀ l, l < (groupAt upB [1, 1]).length →
    (elim.dotP (ground.getAt [] (groupAt upA [1, 1]) k)
      (ground.getAt [] (groupAt upB [1, 1]) l)).oneValue
      BPair.unit := by decide +kernel

/-- The raised perpendicularity refuses: the shared member at the
raised content pairs with itself off the sum's unit. -/
example : ¬ (∀ i, i + 1 < ([1, 1] : List Nat).length →
    ∀ k, k < (groupAt upA (moveAt i (i + 1) [1, 1])).length →
    ∀ l, l < (groupAt upB (moveAt i (i + 1) [1, 1])).length →
    (elim.dotP
      (ground.getAt [] (groupAt upA (moveAt i (i + 1) [1, 1])) k)
      (ground.getAt []
        (groupAt upB (moveAt i (i + 1) [1, 1])) l)).oneValue
      BPair.unit) := by decide +kernel

/-- The additivity parts at the withdrawn read. -/
example : ¬ (countAt (upA ++ upB) [1, 1]
    = countAt upA [1, 1] + countAt upB [1, 1]) := by decide +kernel

/-- Its values: the join's one against the two sides' nought. -/
example : countAt (upA ++ upB) [1, 1] = 1
    ∧ countAt upA [1, 1] = 0
    ∧ countAt upB [1, 1] = 0 := by decide +kernel

/-! The block's own count at the committed data, `countAt_block`
applied whole: the symmetric degree-two block's pool at its
head-cons form reads one at the head's content and nought at every
other — an occupied one and an unoccupied one — with the three
isolating refusals beside it, the head at the sum's unit, the pool
without its closure, and the pool without its provenance, each
with the surviving binders pinned. -/

/-- The theorem applied whole at the committed block's own content:
the pool at its computed head-cons form, every binder decided. -/
example : countAt (blockSpan (shapeOf [2, 0])) [2, 0]
    = if ([2, 0] : List Nat) = [2, 0] then 1 else 0 := by
  rw [show blockSpan (shapeOf [2, 0])
      = (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩] from by decide +kernel]
  exact countAt_block 2 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) [2, 0]

/-- The same instance at the block's other occupied content: the
delta reads nought. -/
example : countAt (blockSpan (shapeOf [2, 0])) [1, 1]
    = if ([1, 1] : List Nat) = [2, 0] then 1 else 0 := by
  rw [show blockSpan (shapeOf [2, 0])
      = (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩] from by decide +kernel]
  exact countAt_block 2 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) [1, 1]

/-- The same instance at a content the block does not carry: the
vacant group's own nought. -/
example : countAt (blockSpan (shapeOf [2, 0])) [3, 1]
    = if ([3, 1] : List Nat) = [2, 0] then 1 else 0 := by
  rw [show blockSpan (shapeOf [2, 0])
      = (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩] from by decide +kernel]
  exact countAt_block 2 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) [3, 1]

/-- Refusal at `hoff`: at the unit-head singleton the count at the
head's own content reads nought against the delta's one. -/
example : ¬ (countAt [(⟨[1, 1], [BPair.unit, BPair.unit]⟩ : HVec)]
    [1, 1] = 1) := by decide +kernel

/-- The surviving binders at the unit-head singleton — the sizes,
the widths and the closure, the unit member's actions themselves at
the unit — so the refusal isolates `hoff`, pinned beside as the
head's own unit tail. -/
example : (∀ w ∈ [(⟨[1, 1], [BPair.unit, BPair.unit]⟩ : HVec)],
      sized w)
    ∧ (∀ w ∈ [(⟨[1, 1], [BPair.unit, BPair.unit]⟩ : HVec)],
      w.content.length = 2)
    ∧ (∀ w ∈ [(⟨[1, 1], [BPair.unit, BPair.unit]⟩ : HVec)],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt [(⟨[1, 1], [BPair.unit, BPair.unit]⟩ : HVec)]
          (act i j w))
    ∧ poly.unitTail ([BPair.unit, BPair.unit] : List BPair) := by
  decide +kernel

/-- Refusal at `hcl`: the symmetric block's `[1, 1]` member alone
sits off the unit with a vacuous provenance, but its raising
escapes the singleton pool, and the count at its own content reads
nought against the delta's one. -/
example : ¬ (countAt
    [(⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec)] [1, 1]
      = 1) := by decide +kernel

/-- The closure's own failure at that singleton, the refusal's
isolated binder. -/
example : ¬ (∀ w ∈ [(⟨[1, 1],
      [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec)],
    ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt [(⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec)]
        (act i j w)) := by decide +kernel

/-- The other binders survive that forgery: the size, the width and
the head off the sum's unit. -/
example : (∀ w ∈ [(⟨[1, 1],
        [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec)], sized w)
    ∧ (∀ w ∈ [(⟨[1, 1],
        [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec)],
      w.content.length = 2)
    ∧ ¬ poly.unitTail
      ([BPair.ofNat 1, BPair.ofNat 1] : List BPair) := by decide +kernel

/-- Refusal at `hprov`: the reordered union — the wedge line ahead
of the symmetric block — reads one at the off-head content against
the delta's nought. -/
example : ¬ (countAt (blockSpan (shapeOf [1, 1])
      ++ blockSpan (shapeOf [2, 0])) [2, 0]
    = if ([2, 0] : List Nat) = [1, 1] then 1 else 0) := by decide +kernel

/-- The union's own head-cons form. -/
example : blockSpan (shapeOf [1, 1]) ++ blockSpan (shapeOf [2, 0])
    = (⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)
      :: [⟨[2, 0], [BPair.ofNat 1]⟩,
          ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 2]⟩] := by decide +kernel

/-- The provenance's own failure at that union, the refusal's
isolated binder: the symmetric block's top is no lowering image of
any earlier member. -/
example : ¬ (∀ k, k < [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
      ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
      ⟨[0, 2], [BPair.ofNat 2]⟩].length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < 2 ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          ((⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]⟩ : HVec)
            :: [⟨[2, 0], [BPair.ofNat 1]⟩,
                ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
                ⟨[0, 2], [BPair.ofNat 2]⟩]) i)
        = some (getAt (⟨[], []⟩ : HVec)
            [(⟨[2, 0], [BPair.ofNat 1]⟩ : HVec),
              ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
              ⟨[0, 2], [BPair.ofNat 2]⟩] k)) := by decide +kernel

/-- The other binders survive it: the sizes, the widths, the
closure at the union, and the head off the sum's unit. -/
example : (∀ w ∈ blockSpan (shapeOf [1, 1])
        ++ blockSpan (shapeOf [2, 0]), sized w)
    ∧ (∀ w ∈ blockSpan (shapeOf [1, 1])
        ++ blockSpan (shapeOf [2, 0]), w.content.length = 2)
    ∧ (∀ w ∈ blockSpan (shapeOf [1, 1])
        ++ blockSpan (shapeOf [2, 0]), ∀ i < 2, ∀ j < 2, ¬ i = j →
      settledAt (blockSpan (shapeOf [1, 1])
        ++ blockSpan (shapeOf [2, 0])) (act i j w))
    ∧ ¬ poly.unitTail
      ([BPair.ofNat 1, (BPair.ofNat 1).swap] : List BPair) := by
  decide +kernel

/-- The delta at width three, the repeated-content regime: the
eight-member block at row list `[2, 1]` reads one at its own top
and nought at the doubly-occupied `[1, 1, 1]`, the theorem applied
whole at the computed head-cons form with the values beside. -/
example : countAt (blockSpan (shapeOf [2, 1, 0])) [2, 1, 0]
    = if ([2, 1, 0] : List Nat) = [2, 1, 0] then 1 else 0 := by
  rw [show blockSpan (shapeOf [2, 1, 0])
      = ground.getAt (⟨[], []⟩ : HVec)
          (blockSpan (shapeOf [2, 1, 0])) 0
        :: (blockSpan (shapeOf [2, 1, 0])).drop 1 from by decide +kernel]
  exact countAt_block 3 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) [2, 1, 0]

example : countAt (blockSpan (shapeOf [2, 1, 0])) [2, 1, 0] = 1
    ∧ countAt (blockSpan (shapeOf [2, 1, 0])) [1, 1, 1] = 0 := by
  decide +kernel

/-! The exhaustion's orthogonality tier at the committed carriers:
the produced blocks pairwise perpendicular (`exhaust_perp`), every
produced member settled in the stated carrier (`exhaust_settle`)
and the join independent at every content (`exhaust_indep`) —
each theorem applied whole with its conclusion's value decided
beside it — and the producer's dropped off-unit binder covered at
a carrier carrying a unit member, invisible to the descent. -/

/-- The committed orthogonal pair at width two: the symmetric
degree-two block joined to the wedge line. -/
private def orthPair : List HVec :=
  blockSpan (shapeOf [2, 0]) ++ blockSpan (shapeOf [1, 1])

private theorem orthPair_sz : ∀ x ∈ orthPair, sized x := by decide +kernel
private theorem orthPair_wid : ∀ x ∈ orthPair, x.content.length = 2 := by
  decide +kernel
private theorem orthPair_cl : ∀ x ∈ orthPair, ∀ i, i < 2 → ∀ j, j < 2 →
    ¬ i = j → settledAt orthPair (act i j x) := by decide +kernel

/-- The committed width-three block at row list `[2, 1]`. -/
private def wideBlock : List HVec := blockSpan (shapeOf [2, 1, 0])

private theorem wideBlock_pack :
    (∀ x ∈ wideBlock, sized x)
      ∧ (∀ x ∈ wideBlock, x.content.length = 3)
      ∧ (∀ x ∈ wideBlock, ∀ i, i < 3 → ∀ j, j < 3 →
          ¬ i = j → settledAt wideBlock (act i j x)) := by decide +kernel

private theorem wideBlock_sz : ∀ x ∈ wideBlock, sized x :=
  wideBlock_pack.1
private theorem wideBlock_wid : ∀ x ∈ wideBlock, x.content.length = 3 :=
  wideBlock_pack.2.1
private theorem wideBlock_cl : ∀ x ∈ wideBlock, ∀ i, i < 3 → ∀ j, j < 3 →
    ¬ i = j → settledAt wideBlock (act i j x) :=
  wideBlock_pack.2.2

/-- A unit member at the wedge content, its coordinates the
enumeration's width of unit entries. -/
private def unitMember : HVec :=
  ⟨[1, 1], List.replicate (places.monomialsAt [1, 1]).length
    BPair.unit⟩

/-- The committed unit-bearing carrier: the symmetric block joined
to that unit member. -/
private def unitCarrier : List HVec :=
  blockSpan (shapeOf [2, 0]) ++ [unitMember]

private theorem unitCarrier_sz : ∀ x ∈ unitCarrier, sized x := by decide +kernel
private theorem unitCarrier_wid : ∀ x ∈ unitCarrier, x.content.length = 2 := by
  decide +kernel
private theorem unitCarrier_cl : ∀ x ∈ unitCarrier, ∀ i, i < 2 → ∀ j, j < 2 →
    ¬ i = j → settledAt unitCarrier (act i j x) := by decide +kernel

/-- The producer's two rounds at the committed pair: the symmetric
top then the wedge line's own. -/
example : (exhaust 2 orthPair).length = 2
    ∧ (exhaust 2 orthPair).map HVec.content = [[2, 0], [1, 1]] := by
  decide +kernel

/-- The blocks' perpendicularity applied whole at the committed
pair, the second round's block against the first at the wedge
content. -/
example : ∀ k, k < (groupAt (blockOf 2
      (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 0))
      [1, 1]).length →
    ∀ l, l < (groupAt (blockOf 2
      (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 1))
      [1, 1]).length →
      (elim.dotP
        (ground.getAt [] (groupAt (blockOf 2
          (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 0))
          [1, 1]) k)
        (ground.getAt [] (groupAt (blockOf 2
          (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 1))
          [1, 1]) l)).oneValue BPair.unit :=
  exhaust_perp 2 orthPair orthPair_sz orthPair_wid orthPair_cl 0 1
    (by decide +kernel) (by decide +kernel) [1, 1]

/-- The display's own value at the computed pools: one row per
block at the wedge content, their pairing at the sum's unit. -/
example : (groupAt (blockOf 2
      (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 0))
      [1, 1]).length = 1
    ∧ (groupAt (blockOf 2
      (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 1))
      [1, 1]).length = 1
    ∧ ∀ k, k < (groupAt (blockOf 2
      (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 0))
      [1, 1]).length →
    ∀ l, l < (groupAt (blockOf 2
      (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 1))
      [1, 1]).length →
      (elim.dotP
        (ground.getAt [] (groupAt (blockOf 2
          (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 0))
          [1, 1]) k)
        (ground.getAt [] (groupAt (blockOf 2
          (ground.getAt (⟨[], []⟩ : HVec) (exhaust 2 orthPair) 1))
          [1, 1]) l)).oneValue BPair.unit := by
  decide +kernel

/-- The settled read applied whole at the committed pair. -/
example : ∀ y ∈ blockJoin 2 (exhaust 2 orthPair),
    sized y ∧ y.content.length = 2 ∧ settledAt orthPair y :=
  exhaust_settle 2 orthPair orthPair_sz orthPair_wid orthPair_cl

/-- The settled read's own value at the computed join. -/
example : ∀ y ∈ blockJoin 2 (exhaust 2 orthPair),
    sized y ∧ y.content.length = 2 ∧ settledAt orthPair y := by
  decide +kernel

/-- The join's independence applied whole at the committed
pair. -/
example : indepAll (blockJoin 2 (exhaust 2 orthPair)) :=
  exhaust_indep 2 orthPair orthPair_sz orthPair_wid orthPair_cl

/-- The independence's own value at the computed join. -/
example : indepAll (blockJoin 2 (exhaust 2 orthPair)) := by decide +kernel

/-- The settled read applied whole at the width-three block. -/
example : ∀ y ∈ blockJoin 3 (exhaust 3 wideBlock),
    sized y ∧ y.content.length = 3 ∧ settledAt wideBlock y :=
  exhaust_settle 3 wideBlock wideBlock_sz wideBlock_wid wideBlock_cl

/-- Its own value at the computed join. -/
example : ∀ y ∈ blockJoin 3 (exhaust 3 wideBlock),
    sized y ∧ y.content.length = 3 ∧ settledAt wideBlock y := by
  decide +kernel

/-- The join's independence applied whole at the width-three
block. -/
example : indepAll (blockJoin 3 (exhaust 3 wideBlock)) :=
  exhaust_indep 3 wideBlock wideBlock_sz wideBlock_wid wideBlock_cl

/-- Its own value at the computed join. -/
example : indepAll (blockJoin 3 (exhaust 3 wideBlock)) := by decide +kernel

/-- The producer's off-unit binder is off the top theorem's path:
the committed carrier carries a member at the sum's unit, so the
withdrawn read refuses outright. -/
example : sized unitMember ∧ poly.unitTail unitMember.coords
    ∧ ¬ (∀ x ∈ unitCarrier, ¬ poly.unitTail x.coords) := by decide +kernel

/-- The unit member is invisible to the descent: the producer
reads the symmetric block's own exhaustion, one round. -/
example : exhaust 2 unitCarrier = exhaust 2 (blockSpan (shapeOf [2, 0]))
    ∧ (exhaust 2 unitCarrier).length = 1 := by decide +kernel

/-- The exhaustion's members are tops at that carrier, the top
theorem applied whole without the withdrawn read. -/
example : ∀ w ∈ exhaust 2 unitCarrier,
    sized w ∧ w.content.length = 2
      ∧ (¬ poly.unitTail w.coords)
      ∧ ∀ j, j < 2 → ∀ i, i < j →
          poly.unitTail (act i j w).coords :=
  exhaust_top 2 unitCarrier unitCarrier_sz unitCarrier_wid unitCarrier_cl

/-! The exhaustion count and the dimension display at the committed
carriers: `countAt_exhaust` applied whole at each content with the
two sides' shared value decided beside, `dimOf_countAt` applied
whole with the dimension's own value beside, the closure binder
isolated at the lone wedge line, and the unit-bearing carrier
covered at the symmetric block's own reads. -/

/-- The committed degree-two symmetric block at width two. -/
private def symBlock : List HVec := blockSpan (shapeOf [2, 0])

private theorem symBlock_sz : ∀ x ∈ symBlock, sized x := by decide +kernel
private theorem symBlock_wid : ∀ x ∈ symBlock, x.content.length = 2 := by
  decide +kernel
private theorem symBlock_cl : ∀ x ∈ symBlock, ∀ i, i < 2 → ∀ j, j < 2 →
    ¬ i = j → settledAt symBlock (act i j x) := by decide +kernel

/-- The redundant carrier: the symmetric block with its own head
listed a second time, the collection refusing the repetition. -/
private def dupCarrier : List HVec :=
  symBlock ++ [ground.getAt (⟨[], []⟩ : HVec) symBlock 0]

private theorem dupCarrier_sz : ∀ x ∈ dupCarrier, sized x := by decide +kernel
private theorem dupCarrier_wid : ∀ x ∈ dupCarrier, x.content.length = 2 := by
  decide +kernel
private theorem dupCarrier_cl : ∀ x ∈ dupCarrier, ∀ i, i < 2 → ∀ j, j < 2 →
    ¬ i = j → settledAt dupCarrier (act i j x) := by decide +kernel

/-- The lone wedge line: the symmetric block's paired lowering
alone, its raising image off the carrier's span. -/
private def wedgeAlone : List HVec :=
  [ground.getAt (⟨[], []⟩ : HVec) symBlock 1]

/-- The count at the block's own top content, `countAt_exhaust`
applied whole. -/
example : countAt symBlock [2, 0] = occ [2, 0] (exhaust 2 symBlock) :=
  countAt_exhaust 2 symBlock symBlock_sz symBlock_wid symBlock_cl
    [2, 0]

/-- Its two sides' shared value. -/
example : countAt symBlock [2, 0] = 1
    ∧ occ [2, 0] (exhaust 2 symBlock) = 1 := by decide +kernel

/-- The count at the block's paired lowering content, the
occupied content off the produced tops'. -/
example : countAt symBlock [1, 1] = occ [1, 1] (exhaust 2 symBlock) :=
  countAt_exhaust 2 symBlock symBlock_sz symBlock_wid symBlock_cl
    [1, 1]

example : countAt symBlock [1, 1] = 0
    ∧ occ [1, 1] (exhaust 2 symBlock) = 0 := by decide +kernel

/-- The count at a content the carrier does not carry. -/
example : countAt symBlock [3, 1] = occ [3, 1] (exhaust 2 symBlock) :=
  countAt_exhaust 2 symBlock symBlock_sz symBlock_wid symBlock_cl
    [3, 1]

example : countAt symBlock [3, 1] = 0
    ∧ occ [3, 1] (exhaust 2 symBlock) = 0 := by decide +kernel

/-- The count at the committed orthogonal pair's two top
contents, the descent's two rounds read one each. -/
example : countAt orthPair [2, 0] = occ [2, 0] (exhaust 2 orthPair) :=
  countAt_exhaust 2 orthPair orthPair_sz orthPair_wid orthPair_cl
    [2, 0]

example : countAt orthPair [1, 1] = occ [1, 1] (exhaust 2 orthPair) :=
  countAt_exhaust 2 orthPair orthPair_sz orthPair_wid orthPair_cl
    [1, 1]

/-- The pair's two shared values, one at each top content. -/
example : countAt orthPair [2, 0] = 1
    ∧ occ [2, 0] (exhaust 2 orthPair) = 1
    ∧ countAt orthPair [1, 1] = 1
    ∧ occ [1, 1] (exhaust 2 orthPair) = 1 := by decide +kernel

/-- The count at the width-three block's own top content and at
its doubly-occupied interior content. -/
example : countAt wideBlock [2, 1, 0]
    = occ [2, 1, 0] (exhaust 3 wideBlock) :=
  countAt_exhaust 3 wideBlock wideBlock_sz wideBlock_wid wideBlock_cl
    [2, 1, 0]

example : countAt wideBlock [1, 1, 1]
    = occ [1, 1, 1] (exhaust 3 wideBlock) :=
  countAt_exhaust 3 wideBlock wideBlock_sz wideBlock_wid wideBlock_cl
    [1, 1, 1]

example : countAt wideBlock [2, 1, 0] = 1
    ∧ occ [2, 1, 0] (exhaust 3 wideBlock) = 1
    ∧ countAt wideBlock [1, 1, 1] = 0
    ∧ occ [1, 1, 1] (exhaust 3 wideBlock) = 0 := by decide +kernel

/-- The dimension display applied whole at the symmetric block. -/
example : dimOf symBlock = ground.famFold Nat.add 0
    (fun mu => countAt symBlock mu * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 2 symBlock).map HVec.content)) :=
  dimOf_countAt 2 symBlock symBlock_sz symBlock_wid symBlock_cl

/-- The block's own dimension. -/
example : dimOf symBlock = 3 := by decide +kernel

/-- The dimension display applied whole at the committed
orthogonal pair, the two blocks' dimensions added. -/
example : dimOf orthPair = ground.famFold Nat.add 0
    (fun mu => countAt orthPair mu * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 2 orthPair).map HVec.content)) :=
  dimOf_countAt 2 orthPair orthPair_sz orthPair_wid orthPair_cl

example : dimOf orthPair = 4 := by decide +kernel

/-- The dimension display applied whole at the redundant carrier,
and the discriminator beside it: the repeated member joins the
carrier's length while the collection refuses it, so the
dimension sits strictly below. -/
example : dimOf dupCarrier = ground.famFold Nat.add 0
    (fun mu => countAt dupCarrier mu
      * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 2 dupCarrier).map HVec.content)) :=
  dimOf_countAt 2 dupCarrier dupCarrier_sz dupCarrier_wid dupCarrier_cl

example : dimOf dupCarrier = 3 ∧ dupCarrier.length = 4 := by decide +kernel

/-- The dimension display applied whole at the width-three
block. -/
example : dimOf wideBlock = ground.famFold Nat.add 0
    (fun mu => countAt wideBlock mu * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 3 wideBlock).map HVec.content)) :=
  dimOf_countAt 3 wideBlock wideBlock_sz wideBlock_wid wideBlock_cl

example : dimOf wideBlock = 8 := by decide +kernel

/-- The closure binder is load-bearing: at the lone wedge line the
carrier's count sits at nought while the descent produces its own
top, so the count read refuses — the surviving binders and the two
refused values decided beside, `hcl` the withdrawn read. -/
example : ¬ (countAt wedgeAlone [1, 1]
    = occ [1, 1] (exhaust 2 wedgeAlone)) := by decide +kernel

example : (∀ x ∈ wedgeAlone, sized x)
    ∧ (∀ x ∈ wedgeAlone, x.content.length = 2)
    ∧ countAt wedgeAlone [1, 1] = 0
    ∧ occ [1, 1] (exhaust 2 wedgeAlone) = 1
    ∧ ¬ (∀ x ∈ wedgeAlone, ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt wedgeAlone (act i j x)) := by decide +kernel

/-- The closure binder at the settling read: the lone wedge line's
produced block escapes the carrier's span, so the settled
conclusion refuses at the withdrawn closure. -/
example : ¬ (∀ y ∈ blockJoin 2 (exhaust 2 wedgeAlone),
    sized y ∧ y.content.length = 2 ∧ settledAt wedgeAlone y) := by
  decide +kernel

/-- The closure binder at the dimension display: the lone wedge
line's dimension reads one against the display's fold at nought,
the refused count the coefficient. -/
example : ¬ (dimOf wedgeAlone = ground.famFold Nat.add 0
    (fun mu => countAt wedgeAlone mu
      * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 2 wedgeAlone).map HVec.content))) := by
  decide +kernel

example : dimOf wedgeAlone = 1
    ∧ ground.famFold Nat.add 0
      (fun mu => countAt wedgeAlone mu
        * (blockSpan (shapeOf mu)).length)
      (ground.dedupL ((exhaust 2 wedgeAlone).map HVec.content))
      = 0 := by decide +kernel

/-- The graded display applied whole at the symmetric block's
three contents, the off-carrier content among them. -/
example : dimAt symBlock [2, 0]
    = ground.famFold Nat.add 0
        (fun nu => countAt symBlock nu
          * occ [2, 0] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 symBlock).map HVec.content)) :=
  gradedDim_countAt 2 symBlock symBlock_sz symBlock_wid symBlock_cl
    [2, 0]

example : dimAt symBlock [1, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt symBlock nu
          * occ [1, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 symBlock).map HVec.content)) :=
  gradedDim_countAt 2 symBlock symBlock_sz symBlock_wid symBlock_cl
    [1, 1]

example : dimAt symBlock [3, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt symBlock nu
          * occ [3, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 symBlock).map HVec.content)) :=
  gradedDim_countAt 2 symBlock symBlock_sz symBlock_wid symBlock_cl
    [3, 1]

/-- The three graded values at the committed block. -/
example : dimAt symBlock [2, 0] = 1
    ∧ dimAt symBlock [1, 1] = 1
    ∧ dimAt symBlock [3, 1] = 0 := by decide +kernel

/-- The graded display at the orthogonal pair's shared content:
the fold sums over the two blocks, one summand each. -/
example : dimAt orthPair [1, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt orthPair nu
          * occ [1, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 orthPair).map HVec.content)) :=
  gradedDim_countAt 2 orthPair orthPair_sz orthPair_wid orthPair_cl
    [1, 1]

/-- The shared content's value with its two summands. -/
example : dimAt orthPair [1, 1] = 2
    ∧ countAt orthPair [2, 0]
        * occ [1, 1] (blockSpan (shapeOf [2, 0])) = 1
    ∧ countAt orthPair [1, 1]
        * occ [1, 1] (blockSpan (shapeOf [1, 1])) = 1 := by decide +kernel

/-- The graded display at the redundant carrier: the collection's
count refuses the repetition where the raw occupancy reads it,
the display at the collected side. -/
example : dimAt dupCarrier [2, 0]
    = ground.famFold Nat.add 0
        (fun nu => countAt dupCarrier nu
          * occ [2, 0] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 dupCarrier).map HVec.content)) :=
  gradedDim_countAt 2 dupCarrier dupCarrier_sz dupCarrier_wid
    dupCarrier_cl [2, 0]

example : dimAt dupCarrier [2, 0] = 1
    ∧ occ [2, 0] dupCarrier = 2 := by decide +kernel

/-- The closure binder at the graded display: the lone wedge
line's content reads one against the display's fold at nought,
`hcl` the withdrawn read with the two refused values decided
beside. -/
example : ¬ (dimAt wedgeAlone [1, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt wedgeAlone nu
          * occ [1, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL
          ((exhaust 2 wedgeAlone).map HVec.content))) := by
  decide +kernel

example : dimAt wedgeAlone [1, 1] = 1
    ∧ ground.famFold Nat.add 0
        (fun nu => countAt wedgeAlone nu
          * occ [1, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 wedgeAlone).map HVec.content))
      = 0 := by decide +kernel

/-! The graded display's repeated top: the triple-fused carrier
`V ⊗ V ⊗ V` at width two, whose exhaustion produces the content
`[2, 1]` twice — the count two where the single top `[3, 0]` reads
one, the display's coefficient carrying the repetition. -/

/-- The triple-fused carrier, eight members at width two. -/
private def triCarrier : List HVec :=
  fusedAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
    (blockSpan [1, 0])

private theorem triCarrier_pack :
    (∀ x ∈ triCarrier, sized x)
      ∧ (∀ x ∈ triCarrier, x.content.length = 2)
      ∧ (∀ x ∈ triCarrier, ∀ i, i < 2 → ∀ j, j < 2 →
          ¬ i = j → settledAt triCarrier (act i j x)) := by decide +kernel

private theorem triCarrier_sz : ∀ x ∈ triCarrier, sized x :=
  triCarrier_pack.1
private theorem triCarrier_wid : ∀ x ∈ triCarrier,
    x.content.length = 2 := triCarrier_pack.2.1
private theorem triCarrier_cl : ∀ x ∈ triCarrier, ∀ i, i < 2 → ∀ j,
    j < 2 → ¬ i = j → settledAt triCarrier (act i j x) :=
  triCarrier_pack.2.2

/-- The carrier's two tops with their counts, and the graded
dimension at the repeated one. -/
example : ground.dedupL ((exhaust 2 triCarrier).map HVec.content)
      = [[3, 0], [2, 1]]
    ∧ countAt triCarrier [3, 0] = 1
    ∧ countAt triCarrier [2, 1] = 2
    ∧ dimAt triCarrier [2, 1] = 3 := by decide +kernel

/-- The display's two sides at the repeated top, the fold read at
the carrier's own top list: the symmetric block's occupancy at
`[2, 1]` enters at the single top's count one and the mixed
block's at the repeated top's two. -/
example : dimAt triCarrier [2, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt triCarrier nu
          * occ [2, 1] (blockSpan (shapeOf nu)))
        [[3, 0], [2, 1]] := by decide +kernel

/-- The graded display applied whole at the repeated top. -/
example : dimAt triCarrier [2, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt triCarrier nu
          * occ [2, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 2 triCarrier).map HVec.content)) :=
  gradedDim_countAt 2 triCarrier triCarrier_sz triCarrier_wid
    triCarrier_cl [2, 1]

/-- The off-unit binder is load-bearing: the unit-tail seed's
closure is one line against the shape's three, `hoff` the
withdrawn read with the surviving binders decided beside — the
length display refuses with the occupancy. -/
private def wU : HVec := ⟨[2, 0], [BPair.unit]⟩

example : sized wU ∧ wU.content.length = 2
    ∧ poly.unitTail wU.coords
    ∧ (∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j wU).coords) := by decide +kernel

example : ¬ (occ [1, 1] (closeSpan 2 (lowerspan.ht wU.content)
      [wU] [wU])
    = occ [1, 1] (blockSpan (shapeOf wU.content))) := by decide +kernel

example : ¬ ((closeSpan 2 (lowerspan.ht wU.content)
      [wU] [wU]).length
    = (blockSpan (shapeOf wU.content)).length) := by decide +kernel

/-- The top binder is load-bearing: the paired lowering seeds a
closure reaching its own raising line where the shape's block at
the lowered content misses it, `htop` the withdrawn read with the
surviving binders decided beside. -/
private def wLow : HVec :=
  ground.getAt (⟨[], []⟩ : HVec) symBlock 1

example : sized wLow ∧ wLow.content.length = 2
    ∧ ¬ poly.unitTail wLow.coords
    ∧ ¬ (∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j wLow).coords) := by decide +kernel

example : ¬ (occ [0, 2] (closeSpan 2 (lowerspan.ht wLow.content)
      [wLow] [wLow])
    = occ [0, 2] (blockSpan (shapeOf wLow.content))) := by decide +kernel

/-- The width binder is load-bearing at the stated letter count:
the width-three top's closure at two letters misses the third
letter's lowerings, `hwd` the withdrawn read with the surviving
binders decided beside. -/
private def w3 : HVec :=
  ground.getAt (⟨[], []⟩ : HVec) (blockSpan (shapeOf [1, 1, 0])) 0

example : sized w3 ∧ ¬ (w3.content.length = 2)
    ∧ ¬ poly.unitTail w3.coords
    ∧ (∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j w3).coords) := by decide +kernel

example : ¬ (occ [1, 0, 1] (closeSpan 2 (lowerspan.ht w3.content)
      [w3] [w3])
    = occ [1, 0, 1] (blockSpan (shapeOf w3.content))) := by decide +kernel

/-- The fuel bound is load-bearing: at fuel nought the closure
never opens, `hfuel` the withdrawn read decided beside. -/
example : ¬ (lowerspan.ht [2, 0] ≤ 0) := by decide +kernel

example : ¬ (occ [1, 1] (closeSpan 2 0
      [ground.getAt (⟨[], []⟩ : HVec) symBlock 0]
      [ground.getAt (⟨[], []⟩ : HVec) symBlock 0])
    = occ [1, 1] (blockSpan (shapeOf [2, 0]))) := by decide +kernel

/-- The width binder is load-bearing at both displays: the
mixed-width carrier keeps the sizes and the closure while the
width read refuses, and each display refuses with it — `hwid` the
withdrawn read with the surviving binders decided beside. -/
private def mixedWidth : List HVec :=
  symBlock ++ [ground.getAt (⟨[], []⟩ : HVec)
    (blockSpan (shapeOf [1, 1, 0])) 0]

example : (∀ x ∈ mixedWidth, sized x)
    ∧ ¬ (∀ x ∈ mixedWidth, x.content.length = 2) := by decide +kernel

example : ∀ x ∈ mixedWidth, ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
    settledAt mixedWidth (act i j x) := by decide +kernel

example : ¬ (dimAt mixedWidth [1, 0, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt mixedWidth nu
          * occ [1, 0, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL
          ((exhaust 2 mixedWidth).map HVec.content))) := by decide +kernel

example : ¬ (dimOf mixedWidth = ground.famFold Nat.add 0
    (fun mu => countAt mixedWidth mu
      * (blockSpan (shapeOf mu)).length)
    (ground.dedupL
      ((exhaust 2 mixedWidth).map HVec.content))) := by decide +kernel

example : dimOf mixedWidth = 4
    ∧ ground.famFold Nat.add 0
        (fun mu => countAt mixedWidth mu
          * (blockSpan (shapeOf mu)).length)
        (ground.dedupL ((exhaust 2 mixedWidth).map HVec.content))
      = 6 := by decide +kernel

/-- The size binders are the frame at both displays: the padded
block refuses the size read while each display still stands, the
binder consumed as the group rows' width read
(`rowsLen_groupAt` at the collection and the exchange), its probe
record standing where a refusal would. -/
private def padBlock : List HVec :=
  symBlock.map (fun w => ⟨w.content, w.coords ++ [BPair.unit]⟩)

example : ¬ (∀ x ∈ padBlock, sized x)
    ∧ (∀ x ∈ padBlock, x.content.length = 2) := by decide +kernel

example : dimOf padBlock = ground.famFold Nat.add 0
    (fun mu => countAt padBlock mu
      * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 2 padBlock).map HVec.content)) := by
  decide +kernel

example : dimAt padBlock [1, 1] = ground.famFold Nat.add 0
    (fun nu => countAt padBlock nu
      * occ [1, 1] (blockSpan (shapeOf nu)))
    (ground.dedupL ((exhaust 2 padBlock).map HVec.content)) := by
  decide +kernel

/-- The graded display at the width-three block's doubly occupied
content: the occupancy above one read against the count. -/
example : dimAt wideBlock [1, 1, 1]
    = ground.famFold Nat.add 0
        (fun nu => countAt wideBlock nu
          * occ [1, 1, 1] (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust 3 wideBlock).map HVec.content)) :=
  gradedDim_countAt 3 wideBlock wideBlock_sz wideBlock_wid
    wideBlock_cl [1, 1, 1]

example : dimAt wideBlock [1, 1, 1] = 2
    ∧ occ [1, 1, 1] (blockSpan (shapeOf [2, 1, 0])) = 2 := by decide +kernel

/-- The closure binder at the join's independence: two seeds at one
content whose blocks reach the depth-two content at one shared
line — the carrier off the closure read, the produced join's group
dependent there, `hcl` the withdrawn read with the surviving
binders decided beside. -/
private def escPair : List HVec :=
  [⟨[2, 1], [BPair.ofNat 2, BPair.unit, BPair.unit]⟩,
   ⟨[2, 1], [BPair.unit, BPair.ofNat 2, BPair.unit]⟩]

example : ¬ indepAll (blockJoin 2 (exhaust 2 escPair)) := by decide +kernel

example : (∀ x ∈ escPair, sized x)
    ∧ (∀ x ∈ escPair, x.content.length = 2)
    ∧ ¬ (∀ x ∈ escPair, ∀ i, i < 2 → ∀ j, j < 2 → ¬ i = j →
      settledAt escPair (act i j x)) := by decide +kernel

/-- The unit-bearing carrier reads the symmetric block's own count
and dimension, the unit member invisible to both. -/
example : countAt unitCarrier [2, 0]
    = occ [2, 0] (exhaust 2 unitCarrier) :=
  countAt_exhaust 2 unitCarrier unitCarrier_sz unitCarrier_wid unitCarrier_cl
    [2, 0]

example : countAt unitCarrier [1, 1]
    = occ [1, 1] (exhaust 2 unitCarrier) :=
  countAt_exhaust 2 unitCarrier unitCarrier_sz unitCarrier_wid unitCarrier_cl
    [1, 1]

example : dimOf unitCarrier = ground.famFold Nat.add 0
    (fun mu => countAt unitCarrier mu
      * (blockSpan (shapeOf mu)).length)
    (ground.dedupL ((exhaust 2 unitCarrier).map HVec.content)) :=
  dimOf_countAt 2 unitCarrier unitCarrier_sz unitCarrier_wid unitCarrier_cl

/-- Its values, the symmetric block's own throughout. -/
example : dimOf unitCarrier = 3
    ∧ countAt unitCarrier [2, 0] = 1
    ∧ occ [2, 0] (exhaust 2 unitCarrier) = 1
    ∧ countAt unitCarrier [1, 1] = 0
    ∧ occ [1, 1] (exhaust 2 unitCarrier) = 0 := by decide +kernel

/-! `lem:blockcount`(ii)'s closing display at the shapes' own block
and (iii)'s bridge and delta at the exhaustion tier: the fusion
count is the fused pool's own count at the target
content, a shape's block reads the Kronecker delta at its row
list, and the unit shape's line reads the first factor back.  Each
theorem is applied whole at committed shapes with its conclusion's
value decided beside it, and the unit read's one-width frame
carries its probe record rather than a refusal. -/

/-- The fusion count at the fused pool's own count, the theorem
applied whole at the one-box row's symmetric target: the one letter
width is the display's only binder, the two blocks' independence
the derivation's own (`lowerspan.spanReads`). -/
example : fusionCount [1, 0] [1, 0] [2, 0]
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      (rowList [2, 0]) :=
  fusionCount_countAt [1, 0] [1, 0] [2, 0] (by decide +kernel)

/-- Its two sides' one value. -/
example : fusionCount [1, 0] [1, 0] [2, 0] = 1
    ∧ countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      (rowList [2, 0]) = 1 := by decide +kernel

/-- The shape's own block reads the delta at its row list, the
theorem applied whole on and off the content at the one-box row's
block and at the one-column block. -/
example : countAt (blockSpan [1, 0]) [1, 0]
    = if ([1, 0] : List Nat) = rowList [1, 0] then 1 else 0 :=
  countAt_blockSpan [1, 0] [1, 0]

example : countAt (blockSpan [1, 0]) [2, 0]
    = if ([2, 0] : List Nat) = rowList [1, 0] then 1 else 0 :=
  countAt_blockSpan [1, 0] [2, 0]

example : countAt (blockSpan [0, 1]) [1, 1]
    = if ([1, 1] : List Nat) = rowList [0, 1] then 1 else 0 :=
  countAt_blockSpan [0, 1] [1, 1]

example : countAt (blockSpan [0, 1]) [0, 0]
    = if ([0, 0] : List Nat) = rowList [0, 1] then 1 else 0 :=
  countAt_blockSpan [0, 1] [0, 0]

/-- The four values, the delta's occupied read at each block's own
row list and nought at every other content. -/
example : countAt (blockSpan [1, 0]) [1, 0] = 1
    ∧ countAt (blockSpan [1, 0]) [2, 0] = 0
    ∧ countAt (blockSpan [0, 1]) [1, 1] = 1
    ∧ countAt (blockSpan [0, 1]) [0, 0] = 0 := by decide +kernel

/-- The unit shape's own span, the exhibit's singleton — no letter
occupied, so no interior lowering is present. -/
example : (blockSpan ([0, 0] : Shape)).length = 1 := by decide +kernel

/-- The unit read applied whole at the one-box row's own shape, at
a target off it, and at the two-box row. -/
example : fusionCount [1, 0]
      (List.replicate ([1, 0] : Shape).length 0) [1, 0]
    = if ([1, 0] : Shape) = [1, 0] then 1 else 0 :=
  fusionCount_unit [1, 0] [1, 0] rfl

example : fusionCount [1, 0]
      (List.replicate ([1, 0] : Shape).length 0) [2, 0]
    = if ([2, 0] : Shape) = [1, 0] then 1 else 0 :=
  fusionCount_unit [1, 0] [2, 0] (by decide +kernel)

example : fusionCount [2, 0]
      (List.replicate ([2, 0] : Shape).length 0) [2, 0]
    = if ([2, 0] : Shape) = [2, 0] then 1 else 0 :=
  fusionCount_unit [2, 0] [2, 0] rfl

/-- The unit read's values at two letters, the shape's own target
occupied once and every other target vacant. -/
example : fusionCount [1, 0] [0, 0] [1, 0] = 1
    ∧ fusionCount [1, 0] [0, 0] [2, 0] = 0
    ∧ fusionCount [1, 0] [0, 0] [0, 1] = 0 := by decide +kernel

/-- The unit read at three letters, the crown instance. -/
example : fusionCount [1, 1, 0] [0, 0, 0] [1, 1, 0] = 1 := by decide +kernel

/-! `fusionCount_unit`'s width binder `hca` is the frame
(`con:places`' one letter width), not a load-bearing read: at a
ragged target the fused contents carry the first shape's width
alone, no pair row matches the target's row list, and both sides
read nought — the width refused at the fixture and the conclusion
still standing, so no refusal exists to commit. -/

example : ¬ (([1, 0, 0] : Shape).length
    = ([1, 0] : Shape).length) := by decide +kernel

example : fusionCount [1, 0] [0, 0] [1, 0, 0]
    = if ([1, 0, 0] : Shape) = [1, 0] then 1 else 0 := by decide +kernel

/-! `fusionCount_comm`'s own reads: the two orders of one pair of
shapes at one target read one count, the theorem applied whole
beside the decided values. -/

example : fusionCount [1, 0] [2, 0] [3, 0]
    = fusionCount [2, 0] [1, 0] [3, 0] :=
  fusionCount_comm [1, 0] [2, 0] [3, 0] (by decide +kernel)

example : fusionCount [1, 0] [2, 0] [1, 1]
    = fusionCount [2, 0] [1, 0] [1, 1] :=
  fusionCount_comm [1, 0] [2, 0] [1, 1] (by decide +kernel)

/-- The crown instance at three letters, the theorem applied whole
at the decided value. -/
example : fusionCount [1, 0, 0] [2, 0, 0] [1, 1, 0]
    = fusionCount [2, 0, 0] [1, 0, 0] [1, 1, 0] :=
  fusionCount_comm [1, 0, 0] [2, 0, 0] [1, 1, 0] (by decide +kernel)

example : fusionCount [1, 0] [2, 0] [3, 0]
    = fusionCount [2, 0] [1, 0] [3, 0] := by decide +kernel

example : fusionCount [1, 0] [2, 0] [1, 1]
    = fusionCount [2, 0] [1, 0] [1, 1] := by decide +kernel

/-! `fusionCount_comm`'s width binder `hba`, its isolating
refusal: a wider second shape at a second occupied letter parts
the two orders' counts — the truncating column union reads the
two enumerations at distinct pair lists.  The binder is
load-bearing; single-occupied-letter ragged pairs read the two
orders equal, the artifact recorded beside the refusal. -/

example : ¬ (([1, 1] : Shape).length
    = ([2, 1, 0] : Shape).length) := by decide +kernel

private theorem hOrdA : fusionCount [2, 1, 0] [1, 1] [2, 1] = 1 := by
  decide +kernel

private theorem hOrdB : fusionCount [1, 1] [2, 1, 0] [2, 1] = 0 := by
  decide +kernel

example : ¬ (fusionCount [2, 1, 0] [1, 1] [2, 1]
    = fusionCount [1, 1] [2, 1, 0] [2, 1]) :=
  fun h => absurd (hOrdA.symm.trans (h.trans hOrdB)) (by decide +kernel)

/-- A single-occupied-letter ragged pair reads the two orders
equal, the truncation artifact off the refusal's shape. -/
example : fusionCount [1, 0] [0, 1, 0, 0] [1, 1]
    = fusionCount [0, 1, 0, 0] [1, 0] [1, 1] := by decide +kernel

/-! `lem:blockcount`(iii)'s block transport applied whole
(`countAt_fused_block`): the scaled degree-two provenance pool at
the `[2, 0]` top, fused against the unit column's block, reads the
shape's own block's fused count content by content — the pool and
the shape's `blockSpan` distinct lists, the counts one value. -/

/-- Both sides' values decided first: one at the two crossing
contents the fused pools carry, nought at the third and at a
content neither carries. -/
example : countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
            ⟨[0, 2], [BPair.ofNat 4]⟩])
      (blockSpan (shapeOf [1, 0]))) [3, 0] = 1
    ∧ countAt (fusedAt (blockSpan (shapeOf [2, 0]))
      (blockSpan (shapeOf [1, 0]))) [3, 0] = 1
    ∧ countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
            ⟨[0, 2], [BPair.ofNat 4]⟩])
      (blockSpan (shapeOf [1, 0]))) [2, 1] = 1
    ∧ countAt (fusedAt (blockSpan (shapeOf [2, 0]))
      (blockSpan (shapeOf [1, 0]))) [2, 1] = 1
    ∧ countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
            ⟨[0, 2], [BPair.ofNat 4]⟩])
      (blockSpan (shapeOf [1, 0]))) [1, 2] = 0
    ∧ countAt (fusedAt (blockSpan (shapeOf [2, 0]))
      (blockSpan (shapeOf [1, 0]))) [1, 2] = 0
    ∧ countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
            ⟨[0, 2], [BPair.ofNat 4]⟩])
      (blockSpan (shapeOf [1, 0]))) [5, 0] = 0
    ∧ countAt (fusedAt (blockSpan (shapeOf [2, 0]))
      (blockSpan (shapeOf [1, 0]))) [5, 0] = 0 := by decide +kernel

/-- The pool and the shape's block are distinct lists: the
transport is no identity here. -/
example : ¬ (((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
      :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
          ⟨[0, 2], [BPair.ofNat 4]⟩])
    = blockSpan (shapeOf [2, 0])) := by decide +kernel

/-- The theorem applied whole at the crossing content, every binder
decided. -/
example : countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
      :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
          ⟨[0, 2], [BPair.ofNat 4]⟩]) (blockSpan (shapeOf [1, 0])))
      [3, 0]
    = countAt (fusedAt (blockSpan (shapeOf [2, 0]))
        (blockSpan (shapeOf [1, 0]))) [3, 0] :=
  countAt_fused_block 2 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (blockSpan (shapeOf [1, 0]))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [3, 0]

/-- The same instance at a content the fused pools do not carry:
both counts nought. -/
example : countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
      :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
          ⟨[0, 2], [BPair.ofNat 4]⟩]) (blockSpan (shapeOf [1, 0])))
      [5, 0]
    = countAt (fusedAt (blockSpan (shapeOf [2, 0]))
        (blockSpan (shapeOf [1, 0]))) [5, 0] :=
  countAt_fused_block 2 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (blockSpan (shapeOf [1, 0]))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [5, 0]

/-! `hind` and `hiC` find no refusal at these fixtures and are
recorded as the frame: the count reads the pools' content spans
alone (`countAt`'s collection), so a repeated member changes
neither side.  The two forgeries below carry the surviving binders
beside them — the repeated `[1, 1]` row inside the block pool, and
the repeated `[0, 1]` row inside the fused second factor — each
with its independence refused and the display still holding. -/

/-- `hind`'s forgery: the block pool with its `[1, 1]` member
repeated refuses the independence while every other binder
survives, and the display still reads. -/
example : ¬ indepAll ((⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
    :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
        ⟨[0, 2], [BPair.ofNat 2]⟩]) := by decide +kernel

example : (∀ w ∈ (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩], sized w)
    ∧ (∀ w ∈ (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩], w.content.length = 2)
    ∧ (∀ w ∈ (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
        :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
            ⟨[0, 2], [BPair.ofNat 2]⟩],
      ∀ i < 2, ∀ j < 2, ¬ i = j →
        settledAt ((⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
          :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
              ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
              ⟨[0, 2], [BPair.ofNat 2]⟩]) (act i j w))
    ∧ (∀ j < 2, ∀ i < j, poly.unitTail
      (act i j (⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)).coords) := by
  decide +kernel

example : countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 1]⟩ : HVec)
      :: [⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
          ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩,
          ⟨[0, 2], [BPair.ofNat 2]⟩]) (blockSpan (shapeOf [1, 0])))
      [3, 0]
    = countAt (fusedAt (blockSpan (shapeOf [2, 0]))
        (blockSpan (shapeOf [1, 0]))) [3, 0] := by decide +kernel

/-- `hiC`'s forgery: the second factor with its `[0, 1]` member
repeated refuses the independence while its sizes and widths
survive, and the display still reads. -/
example : ¬ indepAll [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
    ⟨[0, 1], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩] := by
  decide +kernel

example : (∀ y ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[0, 1], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩],
      sized y)
    ∧ (∀ y ∈ [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[0, 1], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩],
      y.content.length = 2) := by decide +kernel

example : countAt (fusedAt ((⟨[2, 0], [BPair.ofNat 2]⟩ : HVec)
      :: [⟨[1, 1], [BPair.ofNat 2, BPair.ofNat 2]⟩,
          ⟨[0, 2], [BPair.ofNat 4]⟩])
      [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
        ⟨[0, 1], [BPair.ofNat 1]⟩, ⟨[0, 1], [BPair.ofNat 1]⟩])
      [3, 0]
    = countAt (fusedAt (blockSpan (shapeOf [2, 0]))
        [(⟨[1, 0], [BPair.ofNat 1]⟩ : HVec),
          ⟨[0, 1], [BPair.ofNat 1]⟩,
          ⟨[0, 1], [BPair.ofNat 1]⟩]) [3, 0] := by decide +kernel

/-! `lem:blockcount`(iii)'s dimension clause at the fused carrier,
`fusionCount_dim` applied whole with the display's two sides
decided beside it, and the letter-width frame's isolating refusal.
-/

set_option maxRecDepth 100000 in
/-- The dimension display at the two unit blocks, `fusionCount_dim`
applied whole: the graded fold reads 1*3 + 1*1 against the two
blocks' counts' product 2*2. -/
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [1, 0] (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length)
      (ground.dedupL
        ((exhaust [1, 0].length
          (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))).map
          HVec.content))
    = (blockSpan [1, 0]).length * (blockSpan [1, 0]).length :=
  fusionCount_dim [1, 0] [1, 0] (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The display's summands at that instance, the two occupied
contents' counts against their block dimensions. -/
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [1, 0] (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length)
      (ground.dedupL
        ((exhaust [1, 0].length
          (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))).map
          HVec.content))
    = 4 := by decide +kernel

set_option maxRecDepth 100000 in
example : (blockSpan [1, 0]).length * (blockSpan [1, 0]).length = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The display at the exchanged second shape, `fusionCount_dim`
applied whole. -/
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [0, 1] (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length)
      (ground.dedupL
        ((exhaust [1, 0].length
          (fusedAt (blockSpan [1, 0]) (blockSpan [0, 1]))).map
          HVec.content))
    = (blockSpan [1, 0]).length * (blockSpan [0, 1]).length :=
  fusionCount_dim [1, 0] [0, 1] (by decide +kernel)

set_option maxRecDepth 100000 in
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [0, 1] (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length)
      (ground.dedupL
        ((exhaust [1, 0].length
          (fusedAt (blockSpan [1, 0]) (blockSpan [0, 1]))).map
          HVec.content))
    = 2 := by decide +kernel

set_option maxRecDepth 100000 in
/-- `hba`'s isolating refusal: at the ragged second shape `[1]` the
display reads one against the two blocks' counts' product two, so
the letter-width binder is load-bearing at this clause — unlike the
unit read's, which the probes leave unrefused. -/
example : ¬ (ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [1] (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length)
      (ground.dedupL
        ((exhaust [1, 0].length
          (fusedAt (blockSpan [1, 0]) (blockSpan [1]))).map
          HVec.content))
    = (blockSpan [1, 0]).length * (blockSpan [1]).length) := by decide +kernel

/-! `countAt_fused_exhaust`'s degree binder `hdeg`, its isolating
refusal at the mixed-degree carrier: every other stated read holds
beside it — the enumerations, the widths, the two closures, the
second factor's independence, each decided below — while the
degree read refuses and the display parts, the fused count at
`[3, 0]` one against the per-top display's two.  The per-top
summands each transport (`countAt_fused_block`) and the carrier's
fused count agrees with the produced join's; the additivity alone
parts, the cross pairing running through two first factors of
distinct degrees where the tensor's vanishing read
(`dotP_tensorH_off`) prices one degree: `hdeg` is load-bearing,
`con:places`' one-degree blocks the tex's own frame. -/

/-- The degree read itself refuses at the mixed carrier, at both
occupied degrees: the two heads read distinct degrees, so no one
degree serves. -/
example : ¬ (∀ x ∈ blockSpan [1, 0] ++ blockSpan [2, 0],
    ground.sumNat x.content = 1) := by decide +kernel

example : ¬ (∀ x ∈ blockSpan [1, 0] ++ blockSpan [2, 0],
    ground.sumNat x.content = 2) := by decide +kernel

example : ground.sumNat (exhibit [1, 0]).content = 1
    ∧ ground.sumNat (exhibit [2, 0]).content = 2 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The refuting carrier's stated data: sizes, widths, the
carrier's closure at every distinct letter pair, and the
independence. -/
example : (∀ x ∈ blockSpan [1, 0] ++ blockSpan [2, 0], sized x)
    ∧ (∀ x ∈ blockSpan [1, 0] ++ blockSpan [2, 0],
        x.content.length = 2)
    ∧ (∀ x ∈ blockSpan [1, 0] ++ blockSpan [2, 0], ∀ i < 2, ∀ j < 2,
        ¬ i = j →
        settledAt (blockSpan [1, 0] ++ blockSpan [2, 0]) (act i j x))
    ∧ indepAll (blockSpan [1, 0] ++ blockSpan [2, 0]) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The fused count at the refuting content. -/
example : countAt (fusedAt (blockSpan [1, 0] ++ blockSpan [2, 0])
      (blockSpan [1, 0] ++ blockSpan [2, 0])) [3, 0] = 1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The per-top display at the same data, two against the fused
count's one. -/
example : ground.famFold Nat.add 0
      (fun mu => countAt (blockSpan [1, 0] ++ blockSpan [2, 0]) mu
        * countAt (fusedAt (blockSpan (places.shapeOf mu))
            (blockSpan [1, 0] ++ blockSpan [2, 0])) [3, 0])
      (ground.dedupL ((exhaust 2
        (blockSpan [1, 0] ++ blockSpan [2, 0])).map HVec.content))
    = 2 := by decide +kernel

/-! The expansion applied whole at the one-degree carrier, and the
associativity display's two theorem-route reads beside its decided
value. -/

set_option maxRecDepth 100000 in
/-- The expansion applied whole at the fundamental block against
itself, the display's sum the fused count. -/
example : countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [2, 0]
    = ground.famFold Nat.add 0
        (fun mu => countAt (blockSpan [1, 0]) mu
          * countAt (fusedAt (blockSpan (places.shapeOf mu))
              (blockSpan [1, 0])) [2, 0])
        (ground.dedupL (((exhaust 2 (blockSpan [1, 0]))).map
          HVec.content)) :=
  countAt_fused_exhaust 2 1 (blockSpan [1, 0]) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (blockSpan [1, 0])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [2, 0]

set_option maxRecDepth 100000 in
/-- The associativity display applied whole at three distinct
shapes, the two exhaustion carriers distinct lists. -/
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [2, 0] (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) [0, 1] [1, 2])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 0]) (blockSpan [2, 0]))).map
        HVec.content))
    = ground.famFold Nat.add 0
      (fun mu => fusionCount [2, 0] [0, 1] (places.shapeOf mu)
        * fusionCount [1, 0] (places.shapeOf mu) [1, 2])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [2, 0]) (blockSpan [0, 1]))).map
        HVec.content)) :=
  fusionCount_assoc [1, 0] [2, 0] [0, 1] [1, 2] rfl rfl rfl

set_option maxRecDepth 100000 in
/-- The distinct-shape display at the second target. -/
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [2, 0] (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) [0, 1] [3, 1])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 0]) (blockSpan [2, 0]))).map
        HVec.content))
    = ground.famFold Nat.add 0
      (fun mu => fusionCount [2, 0] [0, 1] (places.shapeOf mu)
        * fusionCount [1, 0] (places.shapeOf mu) [3, 1])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [2, 0]) (blockSpan [0, 1]))).map
        HVec.content)) :=
  fusionCount_assoc [1, 0] [2, 0] [0, 1] [3, 1] rfl rfl rfl

set_option maxRecDepth 100000 in
/-- The two sides' value at the first target, decided each. -/
example : ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [2, 0] (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) [0, 1] [1, 2])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 0]) (blockSpan [2, 0]))).map
        HVec.content)) = 1
    ∧ ground.famFold Nat.add 0
      (fun mu => fusionCount [2, 0] [0, 1] (places.shapeOf mu)
        * fusionCount [1, 0] (places.shapeOf mu) [1, 2])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [2, 0]) (blockSpan [0, 1]))).map
        HVec.content)) = 1 := by decide +kernel

/-! `fusionCount_assoc`'s width binders.  `hba` and `hca` are
load-bearing, their isolating refusals at a wider factor with a
second occupied letter; the target's width `hea` is the frame,
unrefusable — an off-width target's row list empties both pair
lists and both sums read the sum's unit, the probes at
`[1]`, `[2]`, `[1,0,0]`, `[0,1,0]`, `[2,1,0]`, `[1,1,1]` each
reading both sides at nought. -/

set_option maxRecDepth 100000 in
/-- `hba`'s isolating refusal: the wider middle factor parts the
two sums. -/
example : ¬ (ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [1, 1, 0] (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) [1, 0] [3, 0])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 0]) (blockSpan [1, 1, 0]))).map
        HVec.content))
    = ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 1, 0] [1, 0] (places.shapeOf mu)
        * fusionCount [1, 0] (places.shapeOf mu) [3, 0])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 1, 0]) (blockSpan [1, 0]))).map
        HVec.content))) := by
  rw [blockcount.span110_pin]; decide +kernel

set_option maxRecDepth 100000 in
/-- `hca`'s isolating refusal: the wider third factor parts the
two sums. -/
example : ¬ (ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [1, 0] (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) [1, 1, 0] [4, 0])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))).map
        HVec.content))
    = ground.famFold Nat.add 0
      (fun mu => fusionCount [1, 0] [1, 1, 0] (places.shapeOf mu)
        * fusionCount [1, 0] (places.shapeOf mu) [4, 0])
      (ground.dedupL ((exhaust 2
        (fusedAt (blockSpan [1, 0]) (blockSpan [1, 1, 0]))).map
        HVec.content))) := by
  rw [blockcount.span110_pin]; decide +kernel
