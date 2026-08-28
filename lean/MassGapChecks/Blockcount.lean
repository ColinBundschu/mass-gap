import MassGap.Blockcount
/-!
The check module for `def:blockcount`: the batteries re-read the
definitional carrier by kernel `decide` — the lowering spans'
dimensions (the Weyl dimensions among them) and `lem:blockcount`'s
reads at instances: the dimension sum over the power's blocks, the
fusion symmetry, and the mismatched degree's empty summand — with
the span walk's own data beside them: the head equation, the
indexed provenance and the width decided at one, two and three
letters, the three-letter shape the first whose interior range
holds two lowering keys.  The
counts' derived fast reads with their coherence pins are the
`lem:pieri`, `lem:mixedinv` and `cor:steinberg` check modules'.
The letter pair's Leibniz split on a tensor, the collecting read
at the fused pool, and the Cartan floor at the column union close
the module, each with its own binder record: the split's width binder refuses at the ragged pair, its
index and sized binders are frames; the collecting read's member-width
binders are frames, the conclusion holding at an off-width carrier
on either side; the floor's width binder is load-bearing, its
refusal at a wider second shape with a second occupied letter,
single-occupied ragged probes reading the conclusion.  The raised
word
pairings close the module at the two committed tops of one
content: one leading raising against a plain word and one on each
side, applied whole and decided, the moved-content binder refused
on the one-sided read and probed on the two-sided.  The seed
closure's stationary converse closes the module: the theorem
applied whole at the full-column seed, with its length hypothesis
isolated at the two-column seed whose closure grows past its own
member and whose interior lowering refuses the unit tail.
-/
set_option maxHeartbeats 4000000

open ground places blockcount

/-! The committed span enumerations, the tier's shared fixtures:
each a stated value of `blockSpan` at a sampled shape, its pin the
one kernel walk of the closure in the tree, the consuming batteries'
reads rewrites at the literal (`MassGapChecks.Carrier`'s
committed-enumeration pattern). -/

namespace blockcount

/-- The adjoint shape's span at three letters, `blockSpan [1, 1, 0]`:
the exhibit with its seven lowering images, the doubled content
`[1, 1, 1]` at its two members. -/
def span110 : List HVec :=
  [⟨[2, 1, 0], [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩,
   ⟨[1, 2, 0], [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]⟩,
   ⟨[2, 0, 1], [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩,
   ⟨[1, 1, 1], [⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]⟩,
   ⟨[1, 1, 1], [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩]⟩,
   ⟨[0, 2, 1], [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩,
   ⟨[1, 0, 2], [⟨3, 1⟩, ⟨1, 3⟩, ⟨1, 1⟩]⟩,
   ⟨[0, 1, 2], [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]⟩]

theorem span110_pin : blockSpan [1, 1, 0] = span110 := by
  decide +kernel

/-- The two-row shape's span at two letters, `blockSpan [2, 1]`:
the exhibit with its two lowering images. -/
def span21 : List HVec :=
  [⟨[3, 1], [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩,
   ⟨[2, 2], [⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩]⟩,
   ⟨[1, 3], [⟨3, 1⟩, ⟨1, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩]⟩]

theorem span21_pin : blockSpan [2, 1] = span21 := by
  decide +kernel

/-- The one-row shape's span at six boxes and two letters: one
member per content down the lowering chain, the coordinates
constant per member at the walk's accumulated scales. -/
def span60 : List HVec :=
  [⟨[6, 0], [⟨2, 1⟩]⟩,
   ⟨[5, 1], List.replicate 6 ⟨2, 1⟩⟩,
   ⟨[4, 2], List.replicate 15 ⟨3, 1⟩⟩,
   ⟨[3, 3], List.replicate 20 ⟨7, 1⟩⟩,
   ⟨[2, 4], List.replicate 15 ⟨25, 1⟩⟩,
   ⟨[1, 5], List.replicate 6 ⟨121, 1⟩⟩,
   ⟨[0, 6], [⟨721, 1⟩]⟩]

theorem span60_pin : blockSpan [6, 0] = span60 := by
  decide +kernel

end blockcount

/-! The spans' dimensions. -/

example : (blockSpan [1, 0]).length = 2 := by decide +kernel
example : (blockSpan [2, 0]).length = 3 := by decide +kernel
example : (blockSpan [0, 1]).length = 1 := by decide +kernel
example : (blockSpan [1, 0, 0]).length = 3 := by decide +kernel
example : (blockSpan [1, 1, 0]).length = 8 := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The fundamental block's span in closed form (`blockSpan_fund`):
the unit contents in letter order at the one-coordinate unit read.
The positive width is load-bearing — at the vacant width the
closure keeps the vacant shape's exhibit against the vacant closed
form — and the coefficient read discriminates. -/

example : blockSpan (unitAt 2 0)
    = (List.range 2).map (fun i =>
        ⟨unitAt 2 i, [BPair.ofNat 1]⟩) := by decide +kernel
example : blockSpan (unitAt 5 0)
    = (List.range 5).map (fun i =>
        ⟨unitAt 5 i, [BPair.ofNat 1]⟩) := by decide +kernel
example : ¬ (blockSpan (unitAt 0 0)
    = (List.range 0).map (fun i =>
        ⟨unitAt 0 i, [BPair.ofNat 1]⟩)) := by decide +kernel
example : ¬ (blockSpan (unitAt 2 0)
    = (List.range 2).map (fun i =>
        ⟨unitAt 2 i, [BPair.ofNat 2]⟩)) := by decide +kernel
example : blockSpan (unitAt 3 0)
    = (List.range 3).map (fun i =>
        ⟨unitAt 3 i, [BPair.ofNat 1]⟩) :=
  blockSpan_fund 3 (by decide +kernel)

/-! The seed clause: the exhibit's coordinate family sits off the
unit tail at every committed shape, the membership guard's
independent seed. -/

example : ¬ poly.unitTail (exhibit [1, 0]).coords := by decide +kernel
example : ¬ poly.unitTail (exhibit [2, 0]).coords := by decide +kernel
example : ¬ poly.unitTail (exhibit [0, 1]).coords := by decide +kernel
example : ¬ poly.unitTail (exhibit [1, 0, 0]).coords := by decide +kernel
example : ¬ poly.unitTail (exhibit [1, 1, 0]).coords := by decide +kernel

/-! `lem:blockcount`'s reads at instances: the dimension sum over
the power's blocks, the fusion symmetry, and the mismatched
degree's empty summand. -/

example : countPower [2, 0] * (blockSpan [2, 0]).length
    + countPower [0, 1] * (blockSpan [0, 1]).length = 4 := by decide +kernel
example : fusionCount [1, 0, 0] [2, 0, 0] [1, 1, 0]
    = fusionCount [2, 0, 0] [1, 0, 0] [1, 1, 0] := by decide +kernel
example : fusionCount [1, 0] [0, 1] [1, 1] = 1 := by decide +kernel
example : fusionCount [1, 0] [0, 1] [3, 0] = 0 := by decide +kernel
example : fusionCount [1, 0] [2, 0] [2, 0] = 0 := by decide +kernel

/-- The crown, the definitional value at the walk's `r = 2`
parameter: the adjoint's multiplicity in its square at the
matched-degree shape, the fast read's coherence partner at the one
triple (`cor:steinberg`'s battery pins the derived count there).
The battery's one over-budget pin, the kernel dimension at the
degree-six tensor summand. -/
example : fusionCount [1, 1, 0] [1, 1, 0] [1, 1, 1] = 2 := by decide +kernel

/-! The seed's theorem instances beside the decided pins: the
exhibit's coordinate family off the unit tail at every shape
(`exhibit_off_unit`). -/

example : ¬ poly.unitTail (exhibit [1, 0]).coords :=
  exhibit_off_unit [1, 0]
example : ¬ poly.unitTail (exhibit [2, 0]).coords :=
  exhibit_off_unit [2, 0]
example : ¬ poly.unitTail (exhibit [0, 1]).coords :=
  exhibit_off_unit [0, 1]
example : ¬ poly.unitTail (exhibit [1, 0, 0]).coords :=
  exhibit_off_unit [1, 0, 0]
example : ¬ poly.unitTail (exhibit [1, 1, 0]).coords :=
  exhibit_off_unit [1, 1, 0]

/-! The closure tier's pins: the exhibit's top reads at the
adjacent and the non-adjacent pair, the gap descent's two
directions at the three-letter shape, and the diagonal's other
occupancy scalar. -/

/-- The adjacent raising's top read at the two-letter shape, the
decided value beside `exhibit_top`'s instance. -/
example : poly.unitTail (elim.matVec
    (units.matUnitAt (units.moveUp 0 (rowList [1, 1]))
      (rowList [1, 1]) 0 1) (exhibit [1, 1]).coords) := by decide +kernel

example : poly.unitTail (elim.matVec
    (units.matUnitAt (units.moveUp 0 (rowList [1, 1]))
      (rowList [1, 1]) 0 1) (exhibit [1, 1]).coords) :=
  exhibit_top [1, 1] 0 (by decide +kernel)

/-- The non-adjacent pair at the three-letter shape, the crossed
composite's read: `exhibit_top_all` beside its decided value. -/
example : poly.unitTail (elim.matVec
    (units.matUnitAt (moveAt 0 2 (rowList [1, 1, 0]))
      (rowList [1, 1, 0]) 0 2) (exhibit [1, 1, 0]).coords) := by
  decide +kernel

example : poly.unitTail (elim.matVec
    (units.matUnitAt (moveAt 0 2 (rowList [1, 1, 0]))
      (rowList [1, 1, 0]) 0 2) (exhibit [1, 1, 0]).coords) :=
  exhibit_top_all [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel)

/-- The gap descent's raising direction at `s = [1, 1, 0]`: the
pool's member at content `[1, 1, 1]` maps under the gap-two
raising into the head group at `[2, 1, 0]`, the residual's pass
the membership and `resid_sound` the span read. -/
example : poly.unitTail (elim.residV 3
    (groupAt (blockSpan [1, 1, 0]) [2, 1, 0])
    (act 0 2 (ground.getAt (exhibit [1, 1, 0])
      (blockSpan [1, 1, 0]) 3)).coords) := by
  rw [blockcount.span110_pin]; decide +kernel

example : elim.spanRel 3 (groupAt (blockSpan [1, 1, 0]) [2, 1, 0])
    (act 0 2 (ground.getAt (exhibit [1, 1, 0])
      (blockSpan [1, 1, 0]) 3)).coords := by
  rw [blockcount.span110_pin]
  exact elim.resid_sound 3 _ _ ⟨rfl, trivial⟩ rfl (by decide +kernel)
    (by decide +kernel)

/-- The image itself: the raised member reads the group's one row,
the exhibit's own coordinates. -/
example : poly.oneValue
    (act 0 2 (ground.getAt (exhibit [1, 1, 0])
      (blockSpan [1, 1, 0]) 3)).coords
    (exhibit [1, 1, 0]).coords := by
  rw [blockcount.span110_pin]; decide +kernel

/-- The lowering direction at the same shape: the head maps under
the gap-two lowering into the `[1, 1, 1]` group, and the image is
a genuine combination — the two rows' difference, off either row
alone. -/
example : poly.unitTail (elim.residV 6
    (groupAt (blockSpan [1, 1, 0]) [1, 1, 1])
    (act 2 0 (exhibit [1, 1, 0])).coords) := by
  rw [blockcount.span110_pin]; decide +kernel

example : elim.spanRel 6 (groupAt (blockSpan [1, 1, 0]) [1, 1, 1])
    (act 2 0 (exhibit [1, 1, 0])).coords := by
  rw [blockcount.span110_pin]
  exact elim.resid_sound 6 _ _ ⟨rfl, rfl, trivial⟩ rfl (by decide +kernel)
    (by decide +kernel)

example : poly.oneValue (act 2 0 (exhibit [1, 1, 0])).coords
    (elim.vecAdd
      (ground.getAt [] (groupAt (blockSpan [1, 1, 0]) [1, 1, 1]) 0)
      ((ground.getAt [] (groupAt (blockSpan [1, 1, 0]) [1, 1, 1])
        1).map BPair.swap)) := by decide +kernel

/-- The diagonal clause's other scalar (`diag_closed`'s read at a
letter of occupancy one): the second letter of `[2, 1]` acts as
the unit scalar, against the first letter's two. -/
example : poly.oneValue
    (elim.matVec (units.matUnitAt [2, 1] [2, 1] 1 1)
      [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩])
    (elim.vecScale (BPair.ofNat 1) [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]) := by
  decide +kernel

/-! `lem:blockirr`'s two span data at instances: the head equation
with the indexed provenance — every member beyond the first an
occupied interior lowering of a member listed at or before its own
predecessor — and the letter width, decided at the one-letter shape
(the interior range empty, the clause vacuous) and at a
two-letter one. -/

example : blockSpan [1] = exhibit [1] :: (blockSpan [1]).drop 1 := by
  decide +kernel

example : ∀ k, k < ((blockSpan [1]).drop 1).length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < ([1] : Shape).length ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          (exhibit [1] :: (blockSpan [1]).drop 1) i)
        = some (getAt (⟨[], []⟩ : HVec)
            ((blockSpan [1]).drop 1) k) := by
  decide +kernel

example : blockSpan [2, 1]
    = exhibit [2, 1] :: (blockSpan [2, 1]).drop 1 := by
  rw [blockcount.span21_pin]; decide +kernel

example : ∀ k, k < ((blockSpan [2, 1]).drop 1).length →
    ∃ i, i ≤ k ∧ ∃ j, j + 1 < ([2, 1] : Shape).length ∧
      lowerH j (getAt (⟨[], []⟩ : HVec)
          (exhibit [2, 1] :: (blockSpan [2, 1]).drop 1) i)
        = some (getAt (⟨[], []⟩ : HVec)
            ((blockSpan [2, 1]).drop 1) k) := by
  rw [blockcount.span21_pin]; decide +kernel

example : ∀ v ∈ blockSpan [1],
    v.content.length = ([1] : Shape).length := by decide +kernel

example : ∀ v ∈ blockSpan [2, 1],
    v.content.length = ([2, 1] : Shape).length := by
  rw [blockcount.span21_pin]; decide +kernel

-- the provenance and width at three letters: the interior range's
-- first shape with two lowering keys
example : ∀ v ∈ blockSpan [1, 1, 0], v.content.length = 3 := by
  rw [blockcount.span110_pin]; decide +kernel

/-! `lem:dualread`(ii)'s engine tier at instances: the full wedge
off the unit tail with its lowering image at the unit, the added
column's tensor factorization, and the wedge-tensored lowering at
an occupied and at a vacant letter.  Each theorem instance sits
beside the decided read of the object it speaks about. -/

example : ¬ poly.unitTail (wedge 2 2).coords := by decide +kernel

example : ¬ poly.unitTail (wedge 2 2).coords :=
  wedge_off_unit 2

example : (lowerH 0 (wedge 2 2)).isSome = true := by decide +kernel

example : ∃ u, lowerH 0 (wedge 2 2) = some u
    ∧ poly.unitTail u.coords :=
  wedge_lowerH_unit 2 0 (by decide +kernel)

example : (lowerH 1 (wedge 3 3)).isSome = true := by decide +kernel

example : ∃ u, lowerH 1 (wedge 3 3) = some u
    ∧ poly.unitTail u.coords :=
  wedge_lowerH_unit 3 1 (by decide +kernel)

example : (exhibit (ground.bumpAt 1 [1, 0])).content
      = (tensorH (wedge 2 2) (exhibit [1, 0])).content
    ∧ poly.oneValue (exhibit (ground.bumpAt 1 [1, 0])).coords
      (tensorH (wedge 2 2) (exhibit [1, 0])).coords := by decide +kernel

example : (exhibit (ground.bumpAt 1 [1, 0])).content
      = (tensorH (wedge 2 2) (exhibit [1, 0])).content
    ∧ poly.oneValue (exhibit (ground.bumpAt 1 [1, 0])).coords
      (tensorH (wedge 2 2) (exhibit [1, 0])).coords :=
  exhibit_addFull [1, 0]

example : (exhibit (ground.bumpAt 2 [1, 0, 0])).content
      = (tensorH (wedge 3 3) (exhibit [1, 0, 0])).content
    ∧ poly.oneValue (exhibit (ground.bumpAt 2 [1, 0, 0])).coords
      (tensorH (wedge 3 3) (exhibit [1, 0, 0])).coords := by decide +kernel

example : (exhibit (ground.bumpAt 2 [1, 0, 0])).content
      = (tensorH (wedge 3 3) (exhibit [1, 0, 0])).content
    ∧ poly.oneValue (exhibit (ground.bumpAt 2 [1, 0, 0])).coords
      (tensorH (wedge 3 3) (exhibit [1, 0, 0])).coords :=
  exhibit_addFull [1, 0, 0]

example : (lowerH 0 (tensorH (wedge 2 2) (exhibit [1, 0]))).isSome
    = true := by decide +kernel

example : ∃ u u', lowerH 0 (tensorH (wedge 2 2) (exhibit [1, 0]))
      = some u
    ∧ lowerH 0 (exhibit [1, 0]) = some u'
    ∧ u.content = (tensorH (wedge 2 2) u').content
    ∧ poly.oneValue u.coords (tensorH (wedge 2 2) u').coords :=
  lowerH_tensorW 2 0 (exhibit [1, 0]) (exhibit_sized [1, 0])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The vacant letter at the lowered exhibit: the second factor is
the lowering image of `exhibit [1, 0]`, its content vacant at the
moved letter. -/
example : ground.getAt 0
    ((lowerH 0 (exhibit [1, 0])).getD ⟨[], []⟩).content 0 = 0 := by
  decide +kernel

example : ∃ u, lowerH 0 (tensorH (wedge 2 2)
      ((lowerH 0 (exhibit [1, 0])).getD ⟨[], []⟩)) = some u
    ∧ poly.unitTail u.coords :=
  lowerH_tensorW_vacant 2 0
    ((lowerH 0 (exhibit [1, 0])).getD ⟨[], []⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The unit-tail read of the tensor at a factor's unit tail and
the regrouping at three one-letter-wide factors, both decided
beside their theorem instances. -/
example : (poly.unitTail (tensorH (wedge 2 0) (wedge 2 2)).coords
    ↔ (poly.unitTail (wedge 2 0).coords
      ∨ poly.unitTail (wedge 2 2).coords)) := by decide +kernel

example : (poly.unitTail (tensorH (wedge 2 0) (wedge 2 2)).coords
    ↔ (poly.unitTail (wedge 2 0).coords
      ∨ poly.unitTail (wedge 2 2).coords)) :=
  tensorH_unitTail (wedge 2 0) (wedge 2 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : (tensorH (tensorH (wedge 2 1) (wedge 2 2))
        (wedge 2 1)).content
      = (tensorH (wedge 2 1)
        (tensorH (wedge 2 2) (wedge 2 1))).content
    ∧ poly.oneValue (tensorH (tensorH (wedge 2 1) (wedge 2 2))
        (wedge 2 1)).coords
      (tensorH (wedge 2 1)
        (tensorH (wedge 2 2) (wedge 2 1))).coords := by decide +kernel

example : (tensorH (tensorH (wedge 2 1) (wedge 2 2))
        (wedge 2 1)).content
      = (tensorH (wedge 2 1)
        (tensorH (wedge 2 2) (wedge 2 1))).content
    ∧ poly.oneValue (tensorH (tensorH (wedge 2 1) (wedge 2 2))
        (wedge 2 1)).coords
      (tensorH (wedge 2 1)
        (tensorH (wedge 2 2) (wedge 2 1))).coords :=
  tensorH_assoc (wedge 2 1) (wedge 2 2) (wedge 2 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The pairing's factorization at one pair of two-letter factors,
the coefficient families distinct across the two sides. -/
example : (elim.dotP
      (tensorH ⟨[1, 0], [BPair.ofNat 2]⟩
        ⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 2).swap]⟩).coords
      (tensorH ⟨[1, 0], [BPair.ofNat 3]⟩
        ⟨[1, 1], [(BPair.ofNat 1).swap,
          BPair.ofNat 4]⟩).coords).oneValue
    (elim.dotP (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).coords
        (⟨[1, 0], [BPair.ofNat 3]⟩ : HVec).coords
      * elim.dotP
        (⟨[1, 1],
          [BPair.ofNat 1, (BPair.ofNat 2).swap]⟩ : HVec).coords
        (⟨[1, 1], [(BPair.ofNat 1).swap,
          BPair.ofNat 4]⟩ : HVec).coords) := by decide +kernel

example : (elim.dotP
      (tensorH ⟨[1, 0], [BPair.ofNat 2]⟩
        ⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 2).swap]⟩).coords
      (tensorH ⟨[1, 0], [BPair.ofNat 3]⟩
        ⟨[1, 1], [(BPair.ofNat 1).swap,
          BPair.ofNat 4]⟩).coords).oneValue
    (elim.dotP (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).coords
        (⟨[1, 0], [BPair.ofNat 3]⟩ : HVec).coords
      * elim.dotP
        (⟨[1, 1],
          [BPair.ofNat 1, (BPair.ofNat 2).swap]⟩ : HVec).coords
        (⟨[1, 1], [(BPair.ofNat 1).swap,
          BPair.ofNat 4]⟩ : HVec).coords) :=
  dotP_tensorH ⟨[1, 0], [BPair.ofNat 2]⟩
    ⟨[1, 1], [BPair.ofNat 1, (BPair.ofNat 2).swap]⟩
    ⟨[1, 0], [BPair.ofNat 3]⟩
    ⟨[1, 1], [(BPair.ofNat 1).swap, BPair.ofNat 4]⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The width binder's refusals: the matched letter count in the
pairing factorization and the unit-tail split is load-bearing —
at factors of unequal widths the summed content truncates and the
rank arithmetic misplaces the scatter, and the kernel refutes the
displays outright. -/

/-- The pairing factorization refuses at unequal widths: one
letter against two, every other hypothesis holding. -/
example : ¬ (elim.dotP
      (tensorH ⟨[1], [BPair.ofNat 1]⟩
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩).coords
      (tensorH ⟨[1], [BPair.ofNat 1]⟩
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩).coords).oneValue
    (elim.dotP (⟨[1], [BPair.ofNat 1]⟩ : HVec).coords
        (⟨[1], [BPair.ofNat 1]⟩ : HVec).coords
      * elim.dotP
        (⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec).coords
        (⟨[1, 1],
          [BPair.ofNat 1, BPair.ofNat 1]⟩ : HVec).coords) := by
  decide +kernel

/-- The unit-tail split refuses at unequal widths: the truncated
scatter reads the unit tail while both factors sit off it. -/
example : ¬ (poly.unitTail
      (tensorH ⟨[0, 1], [BPair.ofNat 1]⟩
        ⟨[1], [BPair.ofNat 1]⟩).coords ↔
    (poly.unitTail (⟨[0, 1], [BPair.ofNat 1]⟩ : HVec).coords
      ∨ poly.unitTail (⟨[1], [BPair.ofNat 1]⟩ : HVec).coords)) := by
  decide +kernel

/-- The carrier frame's refusal at the unit-tail split: oversized
coordinates put an entry beyond the basis, the truncated scatter
ignores it, and the split's two sides part — the `sized` binder is
the carrier's own frame with the kernel's witness beside it. -/
example : ¬ (poly.unitTail
      (tensorH ⟨[1, 0], [BPair.unit, BPair.ofNat 1]⟩
        ⟨[1, 0], [BPair.ofNat 1]⟩).coords ↔
    (poly.unitTail
        (⟨[1, 0], [BPair.unit, BPair.ofNat 1]⟩ : HVec).coords
      ∨ poly.unitTail
          (⟨[1, 0], [BPair.ofNat 1]⟩ : HVec).coords)) := by
  decide +kernel

/-! `lem:dualread`(ii)'s transport kit at instances: the wedge
tensored onto the further factor is additive and passes a
rescaling through, it withdraws at matched widths, and a stationary
exhibit's span is its own singleton — each read decided beside its
theorem's instance. -/

/-- The additive transport at two letters, the kernel's read. -/
example : poly.oneValue
    (tensorH (wedge 2 2) ⟨[1, 1], elim.vecAdd
      [BPair.ofNat 1, BPair.ofNat 2]
      [BPair.ofNat 2, BPair.unit]⟩).coords
    (elim.vecAdd
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩).coords
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 2, BPair.unit]⟩).coords) := by
  decide +kernel

/-- The addition's theorem at that data. -/
example : poly.oneValue
    (tensorH (wedge 2 2) ⟨[1, 1], elim.vecAdd
      [BPair.ofNat 1, BPair.ofNat 2]
      [BPair.ofNat 2, BPair.unit]⟩).coords
    (elim.vecAdd
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩).coords
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 2, BPair.unit]⟩).coords) :=
  tensorW_vecAdd 2 [1, 1] [BPair.ofNat 1, BPair.ofNat 2]
    [BPair.ofNat 2, BPair.unit] rfl rfl rfl

/-- The rescaling's transport at two letters, the kernel's read. -/
example : poly.oneValue
    (tensorH (wedge 2 2) ⟨[1, 1],
      elim.vecScale (BPair.ofNat 2)
        [BPair.ofNat 1, BPair.ofNat 2]⟩).coords
    (elim.vecScale (BPair.ofNat 2)
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩).coords) := by
  decide +kernel

/-- The rescaling's theorem at that data. -/
example : poly.oneValue
    (tensorH (wedge 2 2) ⟨[1, 1],
      elim.vecScale (BPair.ofNat 2)
        [BPair.ofNat 1, BPair.ofNat 2]⟩).coords
    (elim.vecScale (BPair.ofNat 2)
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 1, BPair.ofNat 2]⟩).coords) :=
  tensorW_vecScale 2 [1, 1] (BPair.ofNat 2)
    [BPair.ofNat 1, BPair.ofNat 2] rfl rfl

/-- The withdrawal at a decided hypothesis: the two wedge tensors
read one value at the kernel, and the theorem hands back the
factors' own read. -/
example : poly.oneValue [BPair.ofNat 1, BPair.ofNat 2]
    [BPair.ofNat 1, BPair.ofNat 2] :=
  tensorW_cancel 2 [1, 1] [BPair.ofNat 1, BPair.ofNat 2]
    [BPair.ofNat 1, BPair.ofNat 2] rfl rfl rfl
    (by decide +kernel)

/-- The stationary span at the one-column shape: the interior
lowerings read the sum's unit and the span is the exhibit's own
singleton. -/
example : blockSpan [0, 1] = [exhibit [0, 1]] := by
  refine blockSpan_stationary [0, 1] (fun j u hj hl => ?_)
  have hall : ∀ k, k < 1 →
      optRead (fun w => poly.unitTail w.coords)
        (lowerH k (exhibit [0, 1])) := by decide +kernel
  have h := hall j (Nat.lt_of_succ_lt_succ hj)
  rw [hl] at h
  exact h

/-! The transport kit's binder refusals.  The sized coordinate
families are load-bearing on both sides of the addition and on both
sides of the withdrawal — a mis-sized family truncates at the
memberwise sum while the tensors read their own lengths — and the
withdrawal's width binder refuses outright, the wedge's own family
collapsing against a content of the wrong letter count.  The
rescaling's two binders and the addition's width binder are the
carrier's frame (`con:places`' `d_f`-wide contents, the sized
coordinate families): the kernel refuses neither across the swept
configurations. -/

/-- The addition refuses at a mis-sized left family: the memberwise
sum truncates to the shorter family while the right tensor reads
its own whole length. -/
example : ¬ poly.oneValue
    (tensorH (wedge 2 2) ⟨[1, 1], elim.vecAdd []
      [BPair.ofNat 1, BPair.unit]⟩).coords
    (elim.vecAdd
      (tensorH (wedge 2 2) ⟨[1, 1], []⟩).coords
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩).coords) := by
  decide +kernel

/-- The addition refuses at a mis-sized further family, the
withdrawal of the left family's twin. -/
example : ¬ poly.oneValue
    (tensorH (wedge 2 2) ⟨[1, 1], elim.vecAdd
      [BPair.ofNat 1, BPair.unit] []⟩).coords
    (elim.vecAdd
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩).coords
      (tensorH (wedge 2 2) ⟨[1, 1], []⟩).coords) := by
  decide +kernel

/-- The withdrawal refuses at a mismatched width: one letter of
content against two of the wedge's, the summed content truncating,
and two distinct families read one value at the tensor. -/
example : ¬ (poly.oneValue
      (tensorH (wedge 2 2) ⟨[1], [BPair.ofNat 1]⟩).coords
      (tensorH (wedge 2 2) ⟨[1], [BPair.ofNat 2]⟩).coords →
    poly.oneValue [BPair.ofNat 1] [BPair.ofNat 2]) := by
  decide +kernel

/-- The withdrawal refuses at an oversized left family: the tensor
ignores the entry beyond the enumeration and the two families part
there. -/
example : ¬ (poly.oneValue
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.unit, BPair.unit, BPair.ofNat 1]⟩).coords
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.unit, BPair.unit]⟩).coords →
    poly.oneValue [BPair.unit, BPair.unit, BPair.ofNat 1]
      [BPair.unit, BPair.unit]) := by
  decide +kernel

/-- The withdrawal refuses at an oversized further family, the
left family's twin. -/
example : ¬ (poly.oneValue
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.unit, BPair.unit]⟩).coords
      (tensorH (wedge 2 2)
        ⟨[1, 1], [BPair.unit, BPair.unit, BPair.ofNat 1]⟩).coords →
    poly.oneValue [BPair.unit, BPair.unit]
      [BPair.unit, BPair.unit, BPair.ofNat 1]) := by
  decide +kernel

/-- The stationarity hypothesis is load-bearing: at the one-box
shape the exhibit's interior lowering sits off the unit tail and
the span holds a second member. -/
example : ¬ optRead (fun w => poly.unitTail w.coords)
    (lowerH 0 (exhibit [1, 0])) := by decide +kernel

example : ¬ (blockSpan [1, 0] = [exhibit [1, 0]]) := by decide +kernel

/-- The wedge-tensored lowering's step hypothesis is load-bearing:
at the one-box shape the further factor's own lowering sits off the
unit tail and so does the tensored image. -/
example : ¬ optRead (fun w => poly.unitTail w.coords)
    (lowerH 0 (tensorH (wedge 2 2) (exhibit [1, 0]))) := by decide +kernel

/-- The wedge-tensored lowering refuses at a mismatched width: two
letters of content against three of the wedge's, the further
factor with no lowering at all, and the tensored image off the unit
tail. -/
example : ¬ optRead (fun w => poly.unitTail w.coords)
    (lowerH 0 (tensorH (wedge 3 3)
      ⟨[0, 0], [BPair.ofNat 1]⟩)) := by decide +kernel

/-- The wedge-tensored lowering refuses beyond the adjacent
generators' index range: at the vacant letter count the tensored
content is unoccupied and the promised image is absent. -/
example : lowerH 0 (tensorH (wedge 0 0)
    ⟨[], [BPair.ofNat 1]⟩) = none := by decide +kernel

/-! `lem:dualread`(ii)'s transport tier at the bumped shape: the
walks pair member for member, the contents the tensor's own and
the coordinates its one-value class, the occupancies at the
shifted contents, with the width binder's refusal committed. -/

example : (blockSpan (ground.bumpAt 1 [1, 0])).length
    = (blockSpan [1, 0]).length := by decide +kernel

example : (getAt (⟨[], []⟩ : HVec)
      (blockSpan (ground.bumpAt 1 [1, 0])) 0).content
    = (tensorH (wedge 2 2)
        (getAt (⟨[], []⟩ : HVec) (blockSpan [1, 0]) 0)).content
  := by decide +kernel

example : poly.oneValue
    (getAt (⟨[], []⟩ : HVec)
      (blockSpan (ground.bumpAt 1 [1, 0])) 0).coords
    (tensorH (wedge 2 2)
      (getAt (⟨[], []⟩ : HVec) (blockSpan [1, 0]) 0)).coords
  := by decide +kernel

example : (getAt (⟨[], []⟩ : HVec)
      (blockSpan (ground.bumpAt 1 [1, 0])) 1).content
    = (tensorH (wedge 2 2)
        (getAt (⟨[], []⟩ : HVec) (blockSpan [1, 0]) 1)).content
  := by decide +kernel

example : poly.oneValue
    (getAt (⟨[], []⟩ : HVec)
      (blockSpan (ground.bumpAt 1 [1, 0])) 1).coords
    (tensorH (wedge 2 2)
      (getAt (⟨[], []⟩ : HVec) (blockSpan [1, 0]) 1)).coords
  := by decide +kernel

example : occupancyAt (blockSpan (ground.bumpAt 1 [1, 0]))
      (tensorH (wedge 2 2) (⟨[1, 0], []⟩ : HVec)).content
    = occupancyAt (blockSpan [1, 0]) [1, 0] := by decide +kernel

example : occupancyAt (blockSpan (ground.bumpAt 1 [1, 0]))
      (tensorH (wedge 2 2) (⟨[0, 1], []⟩ : HVec)).content
    = occupancyAt (blockSpan [1, 0]) [0, 1] := by decide +kernel

/-- The occupancy read's width binder is load-bearing: at a content
beyond the shape's letter count the shifted content truncates onto
an occupied one while the stated content misses every member. -/
example : ¬ (occupancyAt (blockSpan (ground.bumpAt 0 [1]))
      (tensorH (wedge 1 1) (⟨[1, 0], []⟩ : HVec)).content
    = occupancyAt (blockSpan [1]) [1, 0]) := by decide +kernel

/-! `lem:blockirr`(iv)'s word-pair tier: the cross-multiplied Gram
display at genuinely independent tops of one content — the
one-value read at matched word pairs, with the shared-content, top,
sized and one-moved-content binders' refusals committed. -/

/-- Two independent tops at one content, the display at one word
against itself. -/
example : (elim.dotP (act 1 0 (⟨[2, 1], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec)).coords
      (act 1 0 (⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]⟩ : HVec)).coords
      * elim.dotP [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]
        [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]).oneValue
    (elim.dotP (act 1 0 (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec)).coords
      (act 1 0 (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec)).coords
      * elim.dotP [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]
        [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit])
  := by decide +kernel

/-- The distinct-words matched pair at three letters: the two
crossings land at one content and the display reads one value. -/
example : (elim.dotP
      (act 1 0 (act 2 1 (⟨[2, 1, 0], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec))).coords
      (act 2 1 (act 1 0 (⟨[2, 1, 0], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec))).coords
      * elim.dotP [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]
        [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]).oneValue
    (elim.dotP
      (act 1 0 (act 2 1 (⟨[2, 1, 0], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec))).coords
      (act 2 1 (act 1 0 (⟨[2, 1, 0], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec))).coords
      * elim.dotP [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]
        [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit])
  := by decide +kernel

/-- The one-moved-content binder is load-bearing: at unbalanced
words the two coordinate lists sit over distinct enumerations and
the display refutes — the committed witness at two independent
tops. -/
example : ¬ ((elim.dotP (act 1 0 (⟨[2, 1], [BPair.ofNat 1,
        (BPair.ofNat 1).swap, BPair.unit]⟩ : HVec)).coords
      [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]
      * elim.dotP [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]
        [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]).oneValue
    (elim.dotP (act 1 0 (⟨[2, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap]⟩ : HVec)).coords
      [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]
      * elim.dotP [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit]
        [BPair.ofNat 1, (BPair.ofNat 1).swap,
          BPair.unit])) := by decide +kernel

/-- The shared-content binder is load-bearing: two tops at
distinct contents refute the display at a matched word pair. -/
example : ¬ ((elim.dotP (act 1 0 (exhibit [1, 0])).coords
      (act 1 0 (exhibit [1, 0])).coords
      * elim.dotP (exhibit [0, 1]).coords
        (exhibit [0, 1]).coords).oneValue
    (elim.dotP (act 1 0 (exhibit [0, 1])).coords
      (act 1 0 (exhibit [0, 1])).coords
      * elim.dotP (exhibit [1, 0]).coords
        (exhibit [1, 0]).coords)) := by decide +kernel

/-- The top binder is load-bearing, the refusal isolating: at one
content, both members sized, one a genuine top and the other
killed by the first adjacent raising alone — the further raising
survives — the display refutes at a matched word pair. -/
example : ¬ poly.unitTail (act 1 2 (⟨[2, 1, 1],
    [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap, BPair.unit,
      BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit,
      BPair.unit, BPair.unit, BPair.unit]⟩ : HVec)).coords
  := by decide +kernel

example : ¬ ((elim.dotP
      (act 2 1 (⟨[2, 1, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap, BPair.unit, BPair.unit, BPair.unit,
        BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit,
        BPair.unit]⟩ : HVec)).coords
      (act 2 1 (⟨[2, 1, 1], [BPair.ofNat 1, BPair.unit,
        (BPair.ofNat 1).swap, BPair.unit, BPair.unit, BPair.unit,
        BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit,
        BPair.unit]⟩ : HVec)).coords
      * elim.dotP
        (⟨[2, 1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          BPair.unit, BPair.unit, BPair.unit, BPair.unit,
          (BPair.ofNat 1).swap, BPair.ofNat 1, BPair.unit,
          BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
            : HVec).coords
        (⟨[2, 1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
          BPair.unit, BPair.unit, BPair.unit, BPair.unit,
          (BPair.ofNat 1).swap, BPair.ofNat 1, BPair.unit,
          BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
            : HVec).coords).oneValue
    (elim.dotP
      (act 2 1 (⟨[2, 1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit, BPair.unit, BPair.unit, BPair.unit,
        (BPair.ofNat 1).swap, BPair.ofNat 1, BPair.unit,
        BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
          : HVec)).coords
      (act 2 1 (⟨[2, 1, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap,
        BPair.unit, BPair.unit, BPair.unit, BPair.unit,
        (BPair.ofNat 1).swap, BPair.ofNat 1, BPair.unit,
        BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩
          : HVec)).coords
      * elim.dotP
        (⟨[2, 1, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap, BPair.unit, BPair.unit, BPair.unit,
          BPair.unit, BPair.unit, BPair.unit, BPair.unit,
          BPair.unit, BPair.unit]⟩ : HVec).coords
        (⟨[2, 1, 1], [BPair.ofNat 1, BPair.unit,
          (BPair.ofNat 1).swap, BPair.unit, BPair.unit, BPair.unit,
          BPair.unit, BPair.unit, BPair.unit, BPair.unit,
          BPair.unit, BPair.unit]⟩ : HVec).coords))
  := by decide +kernel

/-- The second top's sized binder is load-bearing in its own
right: the mirror forge oversizes the second member alone and the
display refutes at a matched word pair. -/
example : ¬ ((elim.dotP (act 1 0 (exhibit [1, 0])).coords
      (act 1 0 (exhibit [1, 0])).coords
      * elim.dotP (⟨(exhibit [1, 0]).content,
        (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
          : HVec).coords
        (⟨(exhibit [1, 0]).content,
          (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
            : HVec).coords).oneValue
    (elim.dotP (act 1 0 (⟨(exhibit [1, 0]).content,
        (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
          : HVec)).coords
      (act 1 0 (⟨(exhibit [1, 0]).content,
        (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
          : HVec)).coords
      * elim.dotP (exhibit [1, 0]).coords
        (exhibit [1, 0]).coords)) := by decide +kernel

/-- The sized binder is load-bearing: a coordinate family with an
entry beyond the enumeration refutes the display. -/
example : ¬ ((elim.dotP
      (act 1 0 (⟨(exhibit [1, 0]).content,
        (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
          : HVec)).coords
      (act 1 0 (⟨(exhibit [1, 0]).content,
        (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
          : HVec)).coords
      * elim.dotP (exhibit [1, 0]).coords
        (exhibit [1, 0]).coords).oneValue
    (elim.dotP (act 1 0 (exhibit [1, 0])).coords
      (act 1 0 (exhibit [1, 0])).coords
      * elim.dotP (⟨(exhibit [1, 0]).content,
        (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
          : HVec).coords
        (⟨(exhibit [1, 0]).content,
          (exhibit [1, 0]).coords ++ [BPair.ofNat 5]⟩
            : HVec).coords)) := by decide +kernel

/-! The block count's own reads at the committed pools: the
symmetric degree-two block `blockSpan [2, 0]` — three members at
contents `[2,0]`, `[1,1]`, `[0,2]` — and the wedge line
`blockSpan [0, 1]`, the shape at the row list `[1,1]`.  A block's
count sits at its own top content alone, the other block's content
reading nought there. -/

/-- The symmetric block counts one at its own top content. -/
example : countAt (blockSpan [2, 0]) [2, 0] = 1 := by decide +kernel

/-- Its count at the wedge's content reads nought: the group at
that content is the block's own middle member, already inside the
stacked raisings' image. -/
example : countAt (blockSpan [2, 0]) [1, 1] = 0 := by decide +kernel

/-- The wedge line counts one at its own top content. -/
example : countAt (blockSpan [0, 1]) [1, 1] = 1 := by decide +kernel

/-- Its count at the symmetric block's top content reads nought,
the line carrying no member there. -/
example : countAt (blockSpan [0, 1]) [2, 0] = 0 := by decide +kernel

/-- The unoccupied content's count beside the four landed value
pins: the vacant group reads nought. -/
example : countAt (blockSpan (shapeOf [2, 0])) [3, 1] = 0 := by decide +kernel

/-! `lem:blockcount`(iii)'s pair reads at committed data: two
tensors at one fused content but distinct first contents pair at
the sum's unit, the value instance at degree one in two letters
with a refusal per binder.  The two width binders carry the
frame's own d-wide contents (Construction `con:places`); their
refusals ride truncating `zipWith` data, where a content past the
frame's width still reads the fused content its partner does. -/

/-- The pair read at matched degree: the two tensors sit at
distinct arrangements of the fused content, so the pairing reads
the sum's unit — the theorem applied whole beside the value. -/
example : (elim.dotP
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[0, 1], [BPair.ofNat 5]⟩ : HVec)
      (⟨[1, 0], [BPair.ofNat 7]⟩ : HVec)).coords).oneValue
    BPair.unit :=
  dotP_tensorH_off (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
    (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)
    (⟨[0, 1], [BPair.ofNat 5]⟩ : HVec)
    (⟨[1, 0], [BPair.ofNat 7]⟩ : HVec)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (elim.dotP
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[0, 1], [BPair.ofNat 5]⟩ : HVec)
      (⟨[1, 0], [BPair.ofNat 7]⟩ : HVec)).coords).oneValue
    BPair.unit := by decide +kernel

/-- Refusal isolating the degree binder: at first factors of
degrees one against two the two tensors share an arrangement of the
fused content and the pairing reads that place's product. -/
example : (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content.length
    = (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec).content.length := by decide +kernel

example : (⟨[1, 1], [BPair.ofNat 5, BPair.unit]⟩ : HVec).content.length
    = (⟨[0, 0], [BPair.ofNat 7]⟩ : HVec).content.length := by decide +kernel

example : ¬ (sumNat (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = sumNat (⟨[1, 1], [BPair.ofNat 5, BPair.unit]⟩ : HVec).content) := by
  decide +kernel

example : (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).content
    = (tensorH (⟨[1, 1], [BPair.ofNat 5, BPair.unit]⟩ : HVec)
      (⟨[0, 0], [BPair.ofNat 7]⟩ : HVec)).content := by decide +kernel

example : ¬ ((⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = (⟨[1, 1], [BPair.ofNat 5, BPair.unit]⟩ : HVec).content) := by decide +kernel

example : ¬ (elim.dotP
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[1, 1], [BPair.ofNat 5, BPair.unit]⟩ : HVec)
      (⟨[0, 0], [BPair.ofNat 7]⟩ : HVec)).coords).oneValue
    BPair.unit := by decide +kernel

/-- Refusal isolating the distinct-contents binder: a tensor
against itself pairs at its own square, off the sum's unit. -/
example : ¬ ¬ ((⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content) := by decide +kernel

example : ¬ (elim.dotP
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords).oneValue
    BPair.unit := by decide +kernel

/-- Refusal isolating the fused-content binder: two pairs at
distinct fused contents each carry one arrangement, and the two
singleton coordinate families pair at their product. -/
example : sumNat (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = sumNat (⟨[0, 1], [BPair.ofNat 2]⟩ : HVec).content := by decide +kernel

example : ¬ ((tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[1, 0], [BPair.ofNat 3]⟩ : HVec)).content
    = (tensorH (⟨[0, 1], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).content) := by decide +kernel

example : ¬ ((⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = (⟨[0, 1], [BPair.ofNat 2]⟩ : HVec).content) := by decide +kernel

example : ¬ (elim.dotP
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[1, 0], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[0, 1], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords).oneValue
    BPair.unit := by decide +kernel

/-- Refusal isolating the first pair's width binder: a first
content one letter past its partner's still reads the fused
content, and the truncated pair shares its arrangement with the
primed pair. -/
example : ¬ ((⟨[1, 0, 0], [BPair.ofNat 2]⟩ : HVec).content.length
    = (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec).content.length) := by decide +kernel

example : sumNat (⟨[1, 0, 0], [BPair.ofNat 2]⟩ : HVec).content
    = sumNat (⟨[1, 0], [BPair.ofNat 5]⟩ : HVec).content := by decide +kernel

example : (tensorH (⟨[1, 0, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).content
    = (tensorH (⟨[1, 0], [BPair.ofNat 5]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 7]⟩ : HVec)).content := by decide +kernel

example : ¬ ((⟨[1, 0, 0], [BPair.ofNat 2]⟩ : HVec).content
    = (⟨[1, 0], [BPair.ofNat 5]⟩ : HVec).content) := by decide +kernel

example : ¬ (elim.dotP
    (tensorH (⟨[1, 0, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[1, 0], [BPair.ofNat 5]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 7]⟩ : HVec)).coords).oneValue
    BPair.unit := by decide +kernel

/-- Refusal isolating the second pair's width binder, the
truncation moved to the primed side. -/
example : (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content.length
    = (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec).content.length := by decide +kernel

example : ¬ ((⟨[1, 0, 0], [BPair.ofNat 5]⟩ : HVec).content.length
    = (⟨[0, 1], [BPair.ofNat 7]⟩ : HVec).content.length) := by decide +kernel

example : sumNat (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = sumNat (⟨[1, 0, 0], [BPair.ofNat 5]⟩ : HVec).content := by decide +kernel

example : (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).content
    = (tensorH (⟨[1, 0, 0], [BPair.ofNat 5]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 7]⟩ : HVec)).content := by decide +kernel

example : ¬ ((⟨[1, 0], [BPair.ofNat 2]⟩ : HVec).content
    = (⟨[1, 0, 0], [BPair.ofNat 5]⟩ : HVec).content) := by decide +kernel

example : ¬ (elim.dotP
    (tensorH (⟨[1, 0], [BPair.ofNat 2]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 3]⟩ : HVec)).coords
    (tensorH (⟨[1, 0, 0], [BPair.ofNat 5]⟩ : HVec)
      (⟨[0, 1], [BPair.ofNat 7]⟩ : HVec)).coords).oneValue
    BPair.unit := by decide +kernel

/-! `lem:blockcount`(iii)'s independence and the fused carrier at
committed data: the stated pair list stands independent and the
fusion count reads the fused pool's own count, each pinned through
its theorem with the value beside it, and one refusal per binder.
The refusals' width pairs ride truncating `zipWith` data, where a
partner past the frame's width still reads the fused content its
shorter partner does (Construction `con:places`' d-wide contents). -/

/-! The one-box row at two letters: the two blocks' tensors carry
the symmetric and the antisymmetric target once each, and the
degree-mismatched target reads nought. -/

example : fusionCount [1, 0] [1, 0] [2, 0] = 1 := by decide +kernel
example : fusionCount [1, 0] [1, 0] [0, 1] = 1 := by decide +kernel
example : fusionCount [1, 0] [1, 0] [1, 0] = 0 := by decide +kernel

/-- The fusion count at the fused pool's own count, the display's
two sides decided at the one-box row's symmetric target; the read
itself is `blockcount.fusionCount_countAt` at the exhaustion tier,
applied whole in ChecksFusiondata. -/
example : fusionCount [1, 0] [1, 0] [2, 0]
    = countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      (rowList [2, 0]) := by decide +kernel

/-- The bridge at the same fixture, the pool's count against the
display's kernel dimension, its independence binder the headline's
own read. -/
example : countAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      [2, 0]
    = elim.kernelDim
      (pairsAt (blockSpan [1, 0]) (blockSpan [1, 0]) [2, 0]).length
      (elim.crossM (units.stackedRaise [2, 0])
        ((pairsAt (blockSpan [1, 0]) (blockSpan [1, 0]) [2, 0]).map
          HVec.coords)) :=
  countAt_pairs (blockSpan [1, 0]) (blockSpan [1, 0]) [2, 0]
    (tensor_indep (blockSpan [1, 0]) (blockSpan [1, 0]) [2, 0] 2 1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- The pair list's independence, the theorem applied whole at the
same fixture beside the read's own value. -/
example : elim.indepRows (monomialsAt [2, 0]).length
    ((pairsAt (blockSpan [1, 0]) (blockSpan [1, 0]) [2, 0]).map
      HVec.coords) :=
  tensor_indep (blockSpan [1, 0]) (blockSpan [1, 0]) [2, 0] 2 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (pairsAt (blockSpan [1, 0]) (blockSpan [1, 0])
    [2, 0]).length = 1 := by decide +kernel

example : (pairsAt (blockSpan [1, 0]) (blockSpan [1, 0])
    [2, 0]).map HVec.content = [[2, 0]] := by decide +kernel

/-- The headline at a two-pair list, the off-content arm live: the
two blocks' pairs at the mixed target read distinct first contents
against each other. -/
example : elim.indepRows (monomialsAt [1, 1]).length
    ((pairsAt (blockSpan [1, 0]) (blockSpan [1, 0]) [1, 1]).map
      HVec.coords) :=
  tensor_indep (blockSpan [1, 0]) (blockSpan [1, 0]) [1, 1] 2 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (pairsAt (blockSpan [1, 0]) (blockSpan [1, 0])
    [1, 1]).length = 2 := by decide +kernel

/-- The headline at a four-pair list with a two-member first-factor
group, the contraction's own case. -/
private def Agrp : List HVec :=
  [⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩,
   ⟨[1, 1], [BPair.unit, BPair.ofNat 1]⟩]

example : elim.indepRows (monomialsAt [2, 2]).length
    ((pairsAt Agrp Agrp [2, 2]).map HVec.coords) :=
  tensor_indep Agrp Agrp [2, 2] 2 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (pairsAt Agrp Agrp [2, 2]).length = 4 := by decide +kernel

/-! The adjoint square's channel row at three letters, the shape at
rows `[2,1,0]` against itself beside the landed crown's base count
two at rows `[3,2,1]`: the doubled-top target at rows `[4,2,0]`
and the two mixed targets at rows `[4,1,1]` and `[3,3,0]` each
enter once (`lem:blockcount`(iii) at the square's row list).  The
unit-class target at rows `[2,2,2]` reads `1` at the dimension
identity's fold, its display pin withheld at the module budget. -/

private theorem fc220_pin :
    fusionCount [1, 1, 0] [1, 1, 0] [2, 2, 0] = 1 := by decide +kernel

example : fusionCount [1, 1, 0] [1, 1, 0] [2, 2, 0] = 1 := fc220_pin

example : fusionCount [1, 1, 0] [1, 1, 0] [3, 0, 1] = 1 := by decide +kernel

example : fusionCount [1, 1, 0] [1, 1, 0] [0, 3, 0] = 1 := by decide +kernel

/-! The refusals' committed carriers: a first list at two degrees, a
first list carrying one member twice, its mirror at the second
list, and the two truncating width pairs. -/

private def Apart : List HVec := [⟨[1, 0], [BPair.ofNat 2]⟩]
private def Bpart : List HVec := [⟨[0, 1], [BPair.ofNat 3]⟩]

private def Amix : List HVec :=
  [⟨[1, 0], [BPair.ofNat 2]⟩,
   ⟨[1, 1], [BPair.ofNat 5, BPair.unit]⟩]

private def Bmix : List HVec :=
  [⟨[0, 1], [BPair.ofNat 3]⟩, ⟨[0, 0], [BPair.ofNat 7]⟩]

private def Atwin : List HVec :=
  [⟨[1, 0], [BPair.ofNat 2]⟩, ⟨[1, 0], [BPair.ofNat 2]⟩]

private def Btwin : List HVec :=
  [⟨[0, 1], [BPair.ofNat 3]⟩, ⟨[0, 1], [BPair.ofNat 3]⟩]

private def Awide : List HVec :=
  [⟨[1, 0], [BPair.ofNat 2]⟩, ⟨[1, 0, 0], [BPair.ofNat 2]⟩]

private def Bwide : List HVec :=
  [⟨[0, 1], [BPair.ofNat 3]⟩, ⟨[0, 1, 0], [BPair.ofNat 3]⟩]

/-- Refusal isolating `tensor_indep`'s degree binder: a first list
at two degrees pairs its members' tensors at one fused content
without the off-content read, and the two pairs' rows fall
dependent. -/
example : ∀ v ∈ Amix, v.content.length = 2 := by decide +kernel

example : ∀ w ∈ Bmix, w.content.length = 2 := by decide +kernel

example : ¬ (∀ v ∈ Amix, sumNat v.content = 1) := by decide +kernel

example : indepAll Amix := by decide +kernel

example : indepAll Bmix := by decide +kernel

example : ¬ elim.indepRows (monomialsAt [1, 1]).length
    ((pairsAt Amix Bmix [1, 1]).map HVec.coords) := by decide +kernel

/-- Refusal isolating `tensor_indep`'s first-list independence
binder: a member listed twice repeats its own pair row. -/
example : ∀ v ∈ Atwin, v.content.length = 2 := by decide +kernel

example : ∀ w ∈ Bpart, w.content.length = 2 := by decide +kernel

example : ∀ v ∈ Atwin, sumNat v.content = 1 := by decide +kernel

example : ¬ indepAll Atwin := by decide +kernel

example : indepAll Bpart := by decide +kernel

example : ¬ elim.indepRows (monomialsAt [1, 1]).length
    ((pairsAt Atwin Bpart [1, 1]).map HVec.coords) := by decide +kernel

/-- Refusal isolating `tensor_indep`'s second-list independence
binder, the mirror at the second list. -/
example : ∀ v ∈ Apart, v.content.length = 2 := by decide +kernel

example : ∀ w ∈ Btwin, w.content.length = 2 := by decide +kernel

example : ∀ v ∈ Apart, sumNat v.content = 1 := by decide +kernel

example : indepAll Apart := by decide +kernel

example : ¬ indepAll Btwin := by decide +kernel

example : ¬ elim.indepRows (monomialsAt [1, 1]).length
    ((pairsAt Apart Btwin [1, 1]).map HVec.coords) := by decide +kernel

/-- Refusal isolating `tensor_indep`'s first width binder: a first
content one letter past the frame's width reads the fused content
its shorter partner does, and the two pair rows repeat. -/
example : ¬ (∀ v ∈ Awide, v.content.length = 2) := by decide +kernel

example : ∀ v ∈ Awide, sumNat v.content = 1 := by decide +kernel

example : indepAll Awide := by decide +kernel

example : ¬ elim.indepRows (monomialsAt [1, 1]).length
    ((pairsAt Awide Bpart [1, 1]).map HVec.coords) := by decide +kernel

/-- Refusal isolating `tensor_indep`'s second width binder, the
truncation moved to the second list. -/
example : ¬ (∀ w ∈ Bwide, w.content.length = 2) := by decide +kernel

example : indepAll Bwide := by decide +kernel

example : ¬ elim.indepRows (monomialsAt [1, 1]).length
    ((pairsAt Apart Bwide [1, 1]).map HVec.coords) := by decide +kernel

/-- Refusal isolating `countAt_pairs`' independence binder: at the
repeated pair row the collection withdraws a row and the pool's
count parts from the display's own kernel dimension. -/
example : ¬ (countAt (fusedAt Atwin Bpart) [1, 1]
    = elim.kernelDim (pairsAt Atwin Bpart [1, 1]).length
      (elim.crossM (units.stackedRaise [1, 1])
        ((pairsAt Atwin Bpart [1, 1]).map HVec.coords))) := by decide +kernel

/-- Refusal isolating `blockcount.fusionCount_countAt`'s one-width
binder, its one binder, the two blocks' independence derived at
`lowerspan.spanReads`: at a second shape two letters past the
first, two members agreeing on
the first shape's letters share one pair row, and the fusion count
parts from the fused pool's count.  The two blocks' independence
stands decided beside the refusal, so the parting is the width's
alone. -/
example : ¬ (([0, 1, 0, 0] : Shape).length
    = ([1, 0] : Shape).length) := by decide +kernel

example : indepAll (blockSpan [1, 0]) := by decide +kernel

example : indepAll (blockSpan [0, 1, 0, 0]) := by decide +kernel

example : ¬ (fusionCount [1, 0] [0, 1, 0, 0] [2, 0]
    = countAt (fusedAt (blockSpan [1, 0])
      (blockSpan [0, 1, 0, 0])) (rowList [2, 0])) := by decide +kernel

/-! The letter pair's Leibniz split on a tensor (`con:units`'
composite clause at `def:blockcount`'s carrier): the moved
composite reads the two one-sided images' sum, at the adjoint
square's own pair in both index orders and at the raised first
factor — the decided displays beside the theorem's own
applications. -/

example : poly.oneValue
    (act 1 0 (tensorH (exhibit [1, 0]) (exhibit [1, 0]))).coords
    (elim.vecAdd
      (tensorH (act 1 0 (exhibit [1, 0])) (exhibit [1, 0])).coords
      (tensorH (exhibit [1, 0]) (act 1 0 (exhibit [1, 0]))).coords) := by
  decide +kernel

example : poly.oneValue
    (act 0 1 (tensorH (exhibit [1, 0]) (exhibit [1, 0]))).coords
    (elim.vecAdd
      (tensorH (act 0 1 (exhibit [1, 0])) (exhibit [1, 0])).coords
      (tensorH (exhibit [1, 0]) (act 0 1 (exhibit [1, 0]))).coords) := by
  decide +kernel

example : poly.oneValue
    (act 1 0 (tensorH (exhibit [2, 0]) (exhibit [1, 0]))).coords
    (elim.vecAdd
      (tensorH (act 1 0 (exhibit [2, 0])) (exhibit [1, 0])).coords
      (tensorH (exhibit [2, 0]) (act 1 0 (exhibit [1, 0]))).coords) := by
  decide +kernel

example : poly.oneValue
    (act 1 0 (tensorH (exhibit [1, 0]) (exhibit [1, 0]))).coords
    (elim.vecAdd
      (tensorH (act 1 0 (exhibit [1, 0])) (exhibit [1, 0])).coords
      (tensorH (exhibit [1, 0]) (act 1 0 (exhibit [1, 0]))).coords) :=
  act_tensorH 1 0 (exhibit [1, 0]) (exhibit [1, 0])
    (exhibit_sized _) (exhibit_sized _) rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : poly.oneValue
    (act 1 0 (tensorH (exhibit [2, 0]) (exhibit [1, 0]))).coords
    (elim.vecAdd
      (tensorH (act 1 0 (exhibit [2, 0])) (exhibit [1, 0])).coords
      (tensorH (exhibit [2, 0]) (act 1 0 (exhibit [1, 0]))).coords) :=
  act_tensorH 1 0 (exhibit [2, 0]) (exhibit [1, 0])
    (exhibit_sized _) (exhibit_sized _) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `act_tensorH`'s width binder: at the ragged
pair the three composite contents part and the display fails. -/
example : ¬ poly.oneValue
    (act 1 0 (tensorH (exhibit [1]) (exhibit [1, 0]))).coords
    (elim.vecAdd
      (tensorH (act 1 0 (exhibit [1])) (exhibit [1, 0])).coords
      (tensorH (exhibit [1]) (act 1 0 (exhibit [1, 0]))).coords) := by
  decide +kernel

/-! The index binders `hi`, `hj` and the distinctness `hij` are the
letter frame (`con:units`' index frame), not refusable here: the
displays at `act 1 1`, at `act 5 0` and at `act 0 5` on the adjoint
square's pair all hold, the truncating folds off the frame carrying
no content — probes, not pins.  The sized binders `hsv`, `hsw` are
the coordinate-width frame the same way: a sweep of mis-sized
coordinate families (lengths 0, 1, 2, 3 and 4 against the five
contents `[1,0]`, `[2,0]`, `[1,1]`, `[0,1]`, `[2,1]` on either
factor, at both index orders) found no refusal, so they are
recorded here as the frame rather than pinned. -/

/-! The collecting read (`con:places`' collecting sentence at
`lem:blockcount`(iii)): a tensor of two combinations collects to
the pairs at the coefficients' products.  The adjoint square's own
pair at two letters, the decided display beside the theorem's
application. -/

private def Asq : List HVec := blockSpan [1, 0]

example : elim.spanRel
    (monomialsAt (List.zipWith (fun p q => p + q) [1, 0] [1, 0])).length
    (groupAt (fusedAt Asq Asq)
      (List.zipWith (fun p q => p + q) [1, 0] [1, 0]))
    (tensorH ⟨[1, 0], (exhibit [1, 0]).coords⟩
      ⟨[1, 0], (exhibit [1, 0]).coords⟩).coords := by decide +kernel

example : elim.spanRel
    (monomialsAt (List.zipWith (fun p q => p + q) [1, 0] [1, 0])).length
    (groupAt (fusedAt (blockSpan [1, 0]) (blockSpan [1, 0]))
      (List.zipWith (fun p q => p + q) [1, 0] [1, 0]))
    (tensorH ⟨[1, 0], (exhibit [1, 0]).coords⟩
      ⟨[1, 0], (exhibit [1, 0]).coords⟩).coords :=
  tensor_span (blockSpan [1, 0]) (blockSpan [1, 0]) 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [1, 0] [1, 0] rfl rfl
    (exhibit [1, 0]).coords (exhibit [1, 0]).coords (by decide +kernel)
    (by decide +kernel)

/-- The carrier off `tensor_span`'s member-width binders: a first
list carrying one member three letters wide beside the two-letter
span, its own width read refused. -/
private def Aoff : List HVec :=
  blockSpan [1, 0] ++ [⟨[1, 0, 0], (exhibit [1, 0, 0]).coords⟩]

example : ¬ (∀ v ∈ Aoff, v.content.length = 2) := by decide +kernel

example : elim.spanRel
    (monomialsAt (List.zipWith (fun p q => p + q) [1, 0] [1, 0])).length
    (groupAt (fusedAt Aoff (blockSpan [1, 0]))
      (List.zipWith (fun p q => p + q) [1, 0] [1, 0]))
    (tensorH ⟨[1, 0], (exhibit [1, 0]).coords⟩
      ⟨[1, 0], (exhibit [1, 0]).coords⟩).coords := by decide +kernel

example : elim.spanRel
    (monomialsAt (List.zipWith (fun p q => p + q) [1, 0] [1, 0])).length
    (groupAt (fusedAt (blockSpan [1, 0]) Aoff)
      (List.zipWith (fun p q => p + q) [1, 0] [1, 0]))
    (tensorH ⟨[1, 0], (exhibit [1, 0]).coords⟩
      ⟨[1, 0], (exhibit [1, 0]).coords⟩).coords := by decide +kernel

/-! `tensor_span`'s member-width binders `hwidA`, `hwidB` with
their letter count `d` are the carrier's frame (`con:places`' one
letter width), not refusable: at `Aoff` — the two-letter span with
one three-letter member joined, whose own width read refuses above
— the conclusion holds on either side of the tensor, the two
probes recorded here; the proof term consumes neither binder.  The
coordinate widths of `x` and `y` are not binders at all,
`elim.spanRel` carrying them. -/

/-! The Cartan floor at the column union (`lem:blockcount`(iii)'s
closing sentence): the fusion count is occupied at the shapes' own
sum, the theorem's applications beside the decided values —
`addS [1,0] [1,0] = [2,0]`, `addS [2,0] [1,0] = [3,0]` and
`addS [1,1,0] [1,1,0] = [2,2,0]`, each read by `decide` before its
pin. -/

example : places.addS [1, 0] [1, 0] = [2, 0] := by decide +kernel
example : places.addS [2, 0] [1, 0] = [3, 0] := by decide +kernel
example : places.addS [1, 1, 0] [1, 1, 0] = [2, 2, 0] := by decide +kernel

example : 1 ≤ fusionCount [1, 0] [1, 0] [2, 0] := by decide +kernel
example : 1 ≤ fusionCount [2, 0] [1, 0] [3, 0] := by decide +kernel
example : 1 ≤ fusionCount [1, 1, 0] [1, 1, 0] [2, 2, 0] := by
  rw [fc220_pin]; decide +kernel

example : 1 ≤ fusionCount [1, 0] [1, 0]
    (places.addS [1, 0] [1, 0]) :=
  fusionCount_cartan [1, 0] [1, 0] (by decide +kernel)

example : 1 ≤ fusionCount [2, 0] [1, 0]
    (places.addS [2, 0] [1, 0]) :=
  fusionCount_cartan [2, 0] [1, 0] (by decide +kernel)

example : 1 ≤ fusionCount [1, 1, 0] [1, 1, 0]
    (places.addS [1, 1, 0] [1, 1, 0]) :=
  fusionCount_cartan [1, 1, 0] [1, 1, 0] (by decide +kernel)

/-! `fusionCount_cartan`'s width binder `hba`, its isolating
refusal: a wider second shape at a second occupied letter starves
the head pair's guard — the truncated column union misses the
tensor's content — and the count reads the sum's unit.
Single-occupied ragged pairs truncate to a still-guarded union
and read the conclusion, the artifact beside the refusal. -/

example : ¬ (([3] : Shape).length = ([1, 2] : Shape).length) := by
  decide +kernel

example : ¬ (1 ≤ fusionCount [1, 2] [3]
    (places.addS [1, 2] [3])) := by decide +kernel

/-- The single-occupied ragged artifact: the truncated union stays
guarded and the floor holds. -/
example : 1 ≤ fusionCount [1] [1, 0]
    (places.addS [1] [1, 0]) := by decide +kernel

/-! `dotP_stackedRaise`'s own data: the stacked pairing of a
committed tensor against itself, read as the fold over the adjacent
moves. -/

private def stkT : HVec := tensorH (exhibit [1, 0]) (exhibit [2, 0])

private def stkU : HVec := tensorH (exhibit [1, 0]) (exhibit [1, 0])

/-- The split applied whole at the column union `[3, 0]`, the
tensor's content, beside the same read decided. -/
example : (elim.dotP
      (elim.matVec (units.stackedRaise [3, 0]) stkT.coords)
      (elim.matVec (units.stackedRaise [3, 0]) stkT.coords)).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun i => elim.dotP (act i (i + 1) stkT).coords
        (act i (i + 1) stkT).coords)
      (List.range (([3, 0] : List Nat).length - 1))) :=
  dotP_stackedRaise [3, 0] stkT stkT (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : (elim.dotP
      (elim.matVec (units.stackedRaise [3, 0]) stkT.coords)
      (elim.matVec (units.stackedRaise [3, 0]) stkT.coords)).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun i => elim.dotP (act i (i + 1) stkT).coords
        (act i (i + 1) stkT).coords)
      (List.range (([3, 0] : List Nat).length - 1))) := by decide +kernel

/-- The split at the two-box union, the second committed shape. -/
example : (elim.dotP
      (elim.matVec (units.stackedRaise [2, 0]) stkU.coords)
      (elim.matVec (units.stackedRaise [2, 0]) stkU.coords)).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun i => elim.dotP (act i (i + 1) stkU).coords
        (act i (i + 1) stkU).coords)
      (List.range (([2, 0] : List Nat).length - 1))) :=
  dotP_stackedRaise [2, 0] stkU stkU (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The raised word pairings (`lem:blockcount`(iii)'s transport
sentence at `lem:blockirr`(iv)'s walk): the two committed tops at
one content — `lem:blockirr`'s own two-top fixtures — with the
words read at the two-letter frame, where `0` is the one letter
with `j + 1 < 2`. -/

private def wgT : HVec :=
  ⟨[2, 1], [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit]⟩

private def wgU : HVec :=
  ⟨[2, 1], [BPair.ofNat 1, BPair.unit, (BPair.ofNat 1).swap]⟩

/-- The fixtures' frame decided: both tops sized at the two-letter
width, one shared content, and every raising's read at the sum's
unit. -/
example : sized wgT ∧ sized wgU ∧ wgT.content.length = 2
    ∧ wgT.content = wgU.content
    ∧ (∀ j, j < 2 → ∀ i, i < j → poly.unitTail (act i j wgT).coords)
    ∧ (∀ j, j < 2 → ∀ i, i < j → poly.unitTail (act i j wgU).coords)
  := by decide +kernel

/-- The words' contents at the frame: the one-letter word's move,
the two-letter word's, and the raising landing back on the shorter
word's content — the moved-content binder's own reads. -/
example : (wact [0] wgT).content = [1, 2]
    ∧ (wact [0, 0] wgT).content = [0, 3]
    ∧ (act 0 1 (wact [0] wgT)).content
      = (wact ([] : List Nat) wgT).content
    ∧ (act 0 1 (wact [0, 0] wgT)).content = (wact [0] wgT).content
  := by decide +kernel

/-! The graded pairing and the walk over `lowerTable` at the same
fixtures: the pairing decided inside and outside the content
summand, the two-table walk applied whole at the committed pair,
and the cross-added tie isolated by a second top at another
content. -/

/-- The graded pairing at the committed top: inside one content it
is the coordinate fold, and against the top's raised image — a
distinct content — it is the sum's unit. -/
example : dotG wgT wgT = elim.dotP wgT.coords wgT.coords
    ∧ dotG wgT (act 0 1 wgT) = BPair.unit
    ∧ ¬ (wgT.content = (act 0 1 wgT).content) := by decide +kernel

/-- The committed pair's crossing tie at `lowerTable` on both
sides: the two tops share their content, so each word's two images
read one content and the two cross-added scalar sums are the same
two entries. -/
private theorem wgTie : ∀ (ws : List Nat) (j : Nat), j + 1 < 2 →
    (∀ l ∈ ws, l + 1 < 2) →
    ¬ poly.unitTail (wactT lowerTable ws wgT).coords →
    ¬ poly.unitTail (wactT lowerTable ws wgU).coords →
    ground.getAt 0 (wactT lowerTable ws wgT).content
        (lowerTable.uLet j)
        + ground.getAt 0 (wactT lowerTable ws wgU).content
          (lowerTable.dLet j)
      = ground.getAt 0 (wactT lowerTable ws wgU).content
          (lowerTable.uLet j)
        + ground.getAt 0 (wactT lowerTable ws wgT).content
          (lowerTable.dLet j) := by
  intro ws _ _ _ _ _
  rw [wactT_content lowerTable ws wgT, wactT_content lowerTable ws wgU,
    show wgU.content = wgT.content from rfl]

/-- `wordGramT` applied whole at `lowerTable` on both sides: the
one-letter word against itself at the committed pair, the display
read at the graded pairing. -/
example : (dotG (wact [0] wgT) (wact [0] wgT)
      * elim.dotP wgU.coords wgU.coords).oneValue
    (dotG (wact [0] wgU) (wact [0] wgU)
      * elim.dotP wgT.coords wgT.coords) :=
  wordGramT lowerTable lowerTable 2 wgT wgU (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun j hjd => (by decide +kernel : ∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j wgT).coords)
      (j + 1) hjd j (Nat.lt_succ_self j))
    (fun j hjd => (by decide +kernel : ∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j wgU).coords)
      (j + 1) hjd j (Nat.lt_succ_self j))
    wgTie [0] [0] (by decide +kernel) (by decide +kernel)

/-- `wordGramStepT` applied whole at the same tables: the
two-letter word led by its first letter against the one-letter
word, with the display decided beside it — the pairing sits at the
sum's unit, the two words' images carrying distinct contents. -/
example : (dotG (wact [0, 0] wgT) (wact [0] wgT)
      * elim.dotP wgU.coords wgU.coords).oneValue
    (dotG (wact [0, 0] wgU) (wact [0] wgU)
      * elim.dotP wgT.coords wgT.coords) :=
  wordGramStepT lowerTable lowerTable 2 wgT wgU (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun j hjd => (by decide +kernel : ∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j wgT).coords)
      (j + 1) hjd j (Nat.lt_succ_self j))
    (fun j hjd => (by decide +kernel : ∀ j, j < 2 → ∀ i, i < j →
        poly.unitTail (act i j wgU).coords)
      (j + 1) hjd j (Nat.lt_succ_self j))
    wgTie 0 [0] [0] (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (dotG (wact [0, 0] wgT) (wact [0] wgT)
      * elim.dotP wgU.coords wgU.coords).oneValue
    (dotG (wact [0, 0] wgU) (wact [0] wgU)
      * elim.dotP wgT.coords wgT.coords)
    ∧ dotG (wact [0, 0] wgT) (wact [0] wgT) = BPair.unit
    ∧ ¬ ((wact [0, 0] wgT).content = (wact [0] wgT).content)
  := by decide +kernel

/-- A second top at another content: the one-monomial vector at
`[3, 0]`, sized at the two-letter width, whose adjacent raising
consumes a vacant letter and so reads the sum's unit. -/
private def wgV : HVec := ⟨[3, 0], [BPair.ofNat 1]⟩

/-- `wordGramT`'s cross-added tie is load-bearing: at the two tops
`wgT` and `wgV` of distinct contents every co-binder stands — both
sized at the two-letter width, both tops at every raising, the word
`[0]` inside the letter bound and both its images off the unit
tail — while the crossing scalars at that word read `1 + 3` against
`0 + 2`, and the display fails. -/
example : sized wgV ∧ wgV.content.length = 2
    ∧ (∀ j, j < 2 → ∀ i, i < j → poly.unitTail (act i j wgV).coords)
    ∧ ¬ (wgV.content = wgT.content)
    ∧ ¬ poly.unitTail (wact [0] wgT).coords
    ∧ ¬ poly.unitTail (wact [0] wgV).coords
    ∧ ¬ (ground.getAt 0 (wact [0] wgT).content 1
        + ground.getAt 0 (wact [0] wgV).content 0
      = ground.getAt 0 (wact [0] wgV).content 1
        + ground.getAt 0 (wact [0] wgT).content 0)
    ∧ ¬ ((dotG (wact [0] wgT) (wact [0] wgT)
        * elim.dotP wgV.coords wgV.coords).oneValue
      (dotG (wact [0] wgV) (wact [0] wgV)
        * elim.dotP wgT.coords wgT.coords)) := by decide +kernel
/-- `wordGramRaise` applied whole at the committed pair: the
one-letter word raised against the empty word. -/
example : (elim.dotP (act 0 1 (wact [0] wgT)).coords
      (wact ([] : List Nat) wgT).coords
      * elim.dotP wgU.coords wgU.coords).oneValue
    (elim.dotP (act 0 1 (wact [0] wgU)).coords
      (wact ([] : List Nat) wgU).coords
      * elim.dotP wgT.coords wgT.coords) :=
  wordGramRaise 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [0] [] (by decide +kernel)
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)

/-- `wordGramRaise` applied whole at the longer pair: the
two-letter word raised against the one-letter word, with the same
display decided beside it. -/
example : (elim.dotP (act 0 1 (wact [0, 0] wgT)).coords
      (wact [0] wgT).coords
      * elim.dotP wgU.coords wgU.coords).oneValue
    (elim.dotP (act 0 1 (wact [0, 0] wgU)).coords
      (wact [0] wgU).coords
      * elim.dotP wgT.coords wgT.coords) :=
  wordGramRaise 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [0, 0] [0] (by decide +kernel)
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)

example : (elim.dotP (act 0 1 (wact [0, 0] wgT)).coords
      (wact [0] wgT).coords
      * elim.dotP wgU.coords wgU.coords).oneValue
    (elim.dotP (act 0 1 (wact [0, 0] wgU)).coords
      (wact [0] wgU).coords
      * elim.dotP wgT.coords wgT.coords) := by decide +kernel

/-- `wordGramRaise`'s moved-content binder is load-bearing: at the
one-letter word against itself the raised content `[2, 1]` misses
the word's own `[1, 2]` and the display fails, every co-binder
standing at the refusal (the frame above, both words at the letter
bound). -/
example : ¬ ((act 0 1 (wact [0] wgT)).content
      = (wact [0] wgT).content)
    ∧ (∀ j ∈ [0], j + 1 < 2)
    ∧ ¬ ((elim.dotP (act 0 1 (wact [0] wgT)).coords
        (wact [0] wgT).coords
        * elim.dotP wgU.coords wgU.coords).oneValue
      (elim.dotP (act 0 1 (wact [0] wgU)).coords
        (wact [0] wgU).coords
        * elim.dotP wgT.coords wgT.coords)) := by decide +kernel

/-- `wordGramRaise2` applied whole at the committed pair: the
one-letter word raised on both sides. -/
example : (elim.dotP (act 0 1 (wact [0] wgT)).coords
      (act 0 1 (wact [0] wgT)).coords
      * elim.dotP wgU.coords wgU.coords).oneValue
    (elim.dotP (act 0 1 (wact [0] wgU)).coords
      (act 0 1 (wact [0] wgU)).coords
      * elim.dotP wgT.coords wgT.coords) :=
  wordGramRaise2 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [0] [0] (by decide +kernel)
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)

/-- `wordGramRaise2` applied whole at the two-letter word on both
sides — the crossing at the raised content past the first move —
with the same display decided beside it. -/
example : (elim.dotP (act 0 1 (wact [0, 0] wgT)).coords
      (act 0 1 (wact [0, 0] wgT)).coords
      * elim.dotP wgU.coords wgU.coords).oneValue
    (elim.dotP (act 0 1 (wact [0, 0] wgU)).coords
      (act 0 1 (wact [0, 0] wgU)).coords
      * elim.dotP wgT.coords wgT.coords) :=
  wordGramRaise2 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) [0, 0] [0, 0] (by decide +kernel)
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)

example : (elim.dotP (act 0 1 (wact [0, 0] wgT)).coords
      (act 0 1 (wact [0, 0] wgT)).coords
      * elim.dotP wgU.coords wgU.coords).oneValue
    (elim.dotP (act 0 1 (wact [0, 0] wgU)).coords
      (act 0 1 (wact [0, 0] wgU)).coords
      * elim.dotP wgT.coords wgT.coords) := by decide +kernel

/-! `wordGramRaise2`'s moved-content binder finds no refusal at
these fixtures: the six mismatched word pairs `([0,0], [])`,
`([0,0], [0])`, `([], [0])`, `([0], [0,0])`, `([0,0,0], [0])` and
`([0], [0,0,0])` all display, as do `wordGramRaise`'s further
mismatches `([0,0], [])`, `([], [0])` and `([0,0], [0,0])` —
probes, not pins; the binder's committed refusal is
`wordGramRaise`'s above.  The top, sized, width and shared-content
binders are `wordGram`'s own frame, the letter bounds
`con:units`' index frame. -/

/-! `lem:blockcount`(iii)'s cross-top transport at the pair lists:
the one word family read at the two committed tops, tensored
against the degree-two block, reads one kernel dimension.  The
plain and stacked cross-top pair Grams are privates and carry no
batteries; their public faces are the identity below and the
independence transport beside it. -/

/-- The two enumerations' pair counts and their kernel dimensions
decided at the two crossing contents: two pairs a side, one
dimension at the first and nought at the second. -/
example : (pairsAt (([[], [0]] : List (List Nat)).map
        (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
        [3, 2]).length = 2
    ∧ (pairsAt (([[], [0]] : List (List Nat)).map
        (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
        [3, 2]).length = 2
    ∧ elim.kernelDim
        (pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
          [3, 2]).length
        (elim.crossM (units.stackedRaise [3, 2])
          ((pairsAt (([[], [0]] : List (List Nat)).map
            (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
            [3, 2]).map HVec.coords)) = 1
    ∧ elim.kernelDim
        (pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
          [3, 2]).length
        (elim.crossM (units.stackedRaise [3, 2])
          ((pairsAt (([[], [0]] : List (List Nat)).map
            (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
            [3, 2]).map HVec.coords)) = 1
    ∧ elim.kernelDim
        (pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
          [2, 3]).length
        (elim.crossM (units.stackedRaise [2, 3])
          ((pairsAt (([[], [0]] : List (List Nat)).map
            (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
            [2, 3]).map HVec.coords)) = 0 := by decide +kernel

/-- `kernelDim_pairs_words` applied whole at the committed tops:
every binder decided, the two-word family against the degree-two
block at the crossing content. -/
example : elim.kernelDim
      (pairsAt (([[], [0]] : List (List Nat)).map
        (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
        [3, 2]).length
      (elim.crossM (units.stackedRaise [3, 2])
        ((pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
          [3, 2]).map HVec.coords))
    = elim.kernelDim
      (pairsAt (([[], [0]] : List (List Nat)).map
        (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
        [3, 2]).length
      (elim.crossM (units.stackedRaise [3, 2])
        ((pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
          [3, 2]).map HVec.coords)) :=
  kernelDim_pairs_words 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [[], [0]] (by decide +kernel) (blockSpan (shapeOf [2, 0]))
    (by decide +kernel) (by decide +kernel) [3, 2]

/-- The same instance at the neighbouring content, where both
dimensions read nought. -/
example : elim.kernelDim
      (pairsAt (([[], [0]] : List (List Nat)).map
        (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
        [2, 3]).length
      (elim.crossM (units.stackedRaise [2, 3])
        ((pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgT)) (blockSpan (shapeOf [2, 0]))
          [2, 3]).map HVec.coords))
    = elim.kernelDim
      (pairsAt (([[], [0]] : List (List Nat)).map
        (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
        [2, 3]).length
      (elim.crossM (units.stackedRaise [2, 3])
        ((pairsAt (([[], [0]] : List (List Nat)).map
          (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
          [2, 3]).map HVec.coords)) :=
  kernelDim_pairs_words 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [[], [0]] (by decide +kernel) (blockSpan (shapeOf [2, 0]))
    (by decide +kernel) (by decide +kernel) [2, 3]

/-- The independence transport applied whole at the same fixtures:
the second top's pair list is independent where the first top's
is. -/
example : elim.indepRows (monomialsAt [3, 2]).length
    ((pairsAt (([[], [0]] : List (List Nat)).map
      (fun ws => wact ws wgU)) (blockSpan (shapeOf [2, 0]))
      [3, 2]).map HVec.coords) :=
  tensor_indep_words 2 wgT wgU (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [[], [0]] (by decide +kernel) (blockSpan (shapeOf [2, 0]))
    (by decide +kernel) (by decide +kernel) [3, 2] (by decide +kernel)

/-! The word family's own collapse recorded beside them: at the
three-word family `[[], [0], [0, 0]]` the last word's image at
either top reads the sum's unit outright — the walk meets a vacant
letter — so at the crossing content `[2, 3]` both pair lists are
dependent (at `[3, 2]` they stay independent) and the transport's
independence hypothesis refuses there.  The two identities above
still display at that family, the kernel dimensions one apiece at
both contents: the collapse is the fold's own vacancy arm, not a
refusal of the transport.  Probes, not pins. -/

/-! The factor enumeration under the display's pair list: the
enumeration's map is the list itself, decided and through the
theorem, with the enumeration's length at the display's own. -/

example : pairsAt (blockSpan [2, 0]) (blockSpan [2, 0]) [2, 2]
    = (pairIdx (blockSpan [2, 0]) (fun v => v)
        (blockSpan [2, 0]) [2, 2]).map
      (fun p => tensorH p.1 p.2) := by decide +kernel
example : pairsAt (blockSpan [1, 1]) (blockSpan [1, 1]) [3, 3]
    = (pairIdx (blockSpan [1, 1]) (fun v => v)
        (blockSpan [1, 1]) [3, 3]).map
      (fun p => tensorH p.1 p.2) :=
  pairsAt_pairIdx (blockSpan [1, 1]) (blockSpan [1, 1]) [3, 3]
example : (pairIdx (blockSpan [1, 1]) (fun v => v)
    (blockSpan [1, 1]) [3, 3]).length = 2 := by decide +kernel

/-! The seed closure's stationary converse
(`closeSpan_seed_line`): at a seed whose closure stands at one
member every interior lowering reads the unit tail, the theorem
applied whole at the full-column seed.  The closure's length
hypothesis is load-bearing: at the two-column seed the round joins
a second member, and the seed's own interior lowering refuses the
unit tail. -/

example : (closeSpan 2 3 [exhibit [0, 1]] [exhibit [0, 1]]).length = 1 := by
  decide +kernel
example : ∀ v, lowerH 0 (exhibit [0, 1]) = some v →
    poly.unitTail v.coords :=
  fun v hv => closeSpan_seed_line 2 2 (exhibit [0, 1]) (by decide +kernel) 0 v
    (by decide +kernel) hv
example : (closeSpan 2 0 [exhibit [1, 1]]
    [exhibit [1, 1]]).length = 1 := by decide +kernel
example : ¬ ((closeSpan 2 (0 + 1) [exhibit [1, 1]]
    [exhibit [1, 1]]).length = 1) := by decide +kernel
example : ¬ ((closeSpan 2 (1 + 1) [exhibit [1, 1]]
    [exhibit [1, 1]]).length = 1) := by decide +kernel
example : ¬ poly.unitTail (match lowerH 0 (exhibit [1, 1]) with
    | some v => v.coords
    | none => []) := by decide +kernel

/-! The wedge-tensored action tier: the wedge a top at the adjacent
raisings, the tensored raising's unit read the further factor's
own, and the bumped shape's row list the wedge's content joined to
the shape's — each decided beside the theorem's route.  The width
binder's isolating refusal: at a member one letter wider than the
stated count, sized, the tensored raising's read and the member's
own part, the index range and the sizing held beside it. -/

example : poly.unitTail (act 0 1 (wedge 2 2)).coords := by decide +kernel
example : poly.unitTail (act 1 2 (wedge 3 1)).coords :=
  wedge_top 3 1 1 (by decide +kernel)

example : (poly.unitTail
      (act 0 1 (tensorH (wedge 2 2) (exhibit [1, 0]))).coords
    ↔ poly.unitTail (act 0 1 (exhibit [1, 0])).coords) :=
  act_tensorW_unit 2 0 (by decide +kernel) (exhibit [1, 0]) (by decide +kernel)
    (by decide +kernel)
example : poly.unitTail
    (act 0 1 (tensorH (wedge 2 2) (exhibit [1, 0]))).coords := by
  decide +kernel

example : sized (exhibit ([0, 0, 1] : places.Shape)) := by decide +kernel
example : ¬ ((exhibit ([0, 0, 1] : places.Shape)).content.length
    = 2) := by decide +kernel
example : ¬ poly.unitTail
    (act 0 1 (tensorH (wedge 2 2) (exhibit [0, 0, 1]))).coords := by
  decide +kernel
example : poly.unitTail
    (act 0 1 (exhibit ([0, 0, 1] : places.Shape))).coords := by
  decide +kernel

example : places.rowList (ground.bumpAt 1 [1, 1])
    = List.zipWith (fun a b => a + b) (wedge 2 2).content
      (places.rowList [1, 1]) := by decide +kernel
example : places.rowList (ground.bumpAt 2 [2, 0, 1])
    = List.zipWith (fun a b => a + b) (wedge 3 3).content
      (places.rowList [2, 0, 1]) := rowList_addFull [2, 0, 1]
