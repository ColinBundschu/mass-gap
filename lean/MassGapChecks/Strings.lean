import MassGap.Strings
import MassGapChecks.Blockcount
/-!
The check module for `lem:strings`: the exhaustion's pins — the
pair's string data on committed spans, the string counts against
the span occupancies content by content, the height reads, the
semantic tier's theorem instances with the spanning reads, the
sl2 kit at the column exhibit, the residual's committed refusal
at the doubled content, the threaded evaluator's own value, and
`thm:weylchar`'s per-depth string weights — the two side weights
hand-computed at every content of the two-letter block's one
string and at a content the span never carries, with the weight
list's width against the collected members' beside them.  The
content symmetry follows: the reflection read decided at
the two-letter block's contents, the depth run's mirror at the
exchanged pair, and `symRead_def` instantiated at the one-box
shape and at that block.  `lem:casimir`'s trace collection closes
the module: the moved folds hand-computed at that block's pair and
`stringCollect` discharged twice — at a content the string reaches
(the gap identity at its depth) and at a content below the ladder
(the two folds equal at the depth run's reversal).
-/

namespace strings

open ground places blockcount

/-! The committed exhaustions, the walk tier's shared fixtures: the
walk's value at the committed spans at the residuals' canonical
representatives, each pin one kernel collection
at the span literal, the consuming batteries' reads rewrites at the
literal (`MassGapChecks.Blockcount`'s span fixtures). -/


/-- The adjoint span's exhaustion at the far pair,
`walk 0 2 (blockSpan [1, 1, 0])`: the four strings at the height
run. -/
def walk110 : List PairString :=
  [⟨⟨[2, 1, 0], [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩, 2⟩,
   ⟨⟨[2, 0, 1], [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩, 1⟩,
   ⟨⟨[1, 2, 0], [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]⟩, 1⟩,
   ⟨⟨[1, 1, 1], [⟨3, 1⟩, ⟨5, 1⟩, ⟨1, 3⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨1, 3⟩]⟩, 0⟩]

theorem walk110_pin :
    walk 0 2 (blockcount.blockSpan [1, 1, 0]) = walk110 := by
  rw [blockcount.span110_pin]; decide +kernel

/-- The two-row span's exhaustion at the pair,
`walk 0 1 (blockSpan [2, 1])`: the one string at height two. -/
def walk21 : List PairString :=
  [⟨⟨[3, 1], [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]⟩, 2⟩]

theorem walk21_pin :
    walk 0 1 (blockcount.blockSpan [2, 1]) = walk21 := by
  rw [blockcount.span21_pin]; decide +kernel


/-! The one sl2 string at two letters: the top with its height,
and the counts at both contents. -/

theorem pin1 : (walk 0 1 (blockSpan [1, 1])).map
    (fun s => (s.top.content, s.ht)) = [([2, 1], 1)] := by decide +kernel

theorem pin2 : stringCount 0 1 (walk 0 1 (blockSpan [1, 1])) [2, 1]
    = occupancyAt (blockSpan [1, 1]) [2, 1] := by decide +kernel

theorem pin3 : stringCount 0 1 (walk 0 1 (blockSpan [1, 1])) [1, 2]
    = occupancyAt (blockSpan [1, 1]) [1, 2] := by decide +kernel

/-! The adjoint's exhaustion at three letters, the far pair: four
strings at the height run, the members' total the span's eight,
and the doubled content's count at the occupancy. -/

theorem pin4 : (walk 0 2 (blockSpan [1, 1, 0])).map
    (fun s => (s.top.content, s.ht))
    = [([2, 1, 0], 2), ([2, 0, 1], 1), ([1, 2, 0], 1),
       ([1, 1, 1], 0)] := by
  rw [strings.walk110_pin]; decide +kernel

theorem pin5 : stringCount 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
    [1, 1, 1] = 2 := by
  rw [strings.walk110_pin]; decide +kernel

theorem pin6 : stringCount 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
    [1, 1, 1]
    = occupancyAt (blockSpan [1, 1, 0]) [1, 1, 1] := by
  rw [strings.walk110_pin, blockcount.span110_pin]; decide +kernel

theorem pin7 : stringCount 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
    [2, 1, 0]
    = occupancyAt (blockSpan [1, 1, 0]) [2, 1, 0] := by
  rw [strings.walk110_pin, blockcount.span110_pin]; decide +kernel

set_option maxHeartbeats 4000000

/-! The semantic tier's theorem instances at the same block: every
collected string good, the count at the doubled content reading
the span occupancy, and the members there off the sum's unit and
pairwise perpendicular. -/

theorem pin8 : ∀ str ∈ walk 0 2 (blockSpan [1, 1, 0]),
    goodString 0 2 [1, 1, 0].length (blockSpan [1, 1, 0]) str :=
  walk_good [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin9 : stringCount 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
    [1, 1, 1] = occupancyAt (blockSpan [1, 1, 0]) [1, 1, 1] :=
  walk_count [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [1, 1, 1]

theorem pin10 : ¬ poly.unitTail (ground.getAt []
    (membersAt 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
      [1, 1, 1]) 0) :=
  walk_off [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [1, 1, 1] 0 (by decide +kernel)

theorem pin11 : (elim.dotP
    (ground.getAt []
      (membersAt 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
        [1, 1, 1]) 0)
    (ground.getAt []
      (membersAt 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
        [1, 1, 1]) 1)).oneValue BPair.unit :=
  walk_perp [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [1, 1, 1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The spanning reads at the doubled content: a collected member
inside its content group's span, and a group row inside the
collected members' span. -/

theorem pin12 : elim.spanRel (monomialsAt [1, 1, 1]).length
    (groupAt (blockSpan [1, 1, 0]) [1, 1, 1])
    (ground.getAt []
      (membersAt 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
        [1, 1, 1]) 0) :=
  walk_span [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [1, 1, 1] 0 (by decide +kernel)

theorem pin13 : elim.spanRel (monomialsAt [1, 1, 1]).length
    (membersAt 0 2 (walk 0 2 (blockSpan [1, 1, 0])) [1, 1, 1])
    (ground.getAt []
      (groupAt (blockSpan [1, 1, 0]) [1, 1, 1]) 0) :=
  walk_spanRowL [1, 1, 0] 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [1, 1, 1] 0 (by decide +kernel)

/-! The sl2 kit at the column exhibit, `lem:tops`(iii)'s own top:
the run's termination one step below the height, the raising's
coefficient at the first step, and the self-pairing's telescope at
the run's end. -/

theorem pin14 : poly.unitTail
    (iterAct 0 2 (2 + 1) (exhibit [1, 1, 0])).coords :=
  iterAct_term 0 2 (by decide +kernel) (exhibit [1, 1, 0]) 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin15 : poly.oneValue
    (act 0 2 (iterAct 0 2 (0 + 1) (exhibit [1, 1, 0]))).coords
    (elim.vecScale (BPair.ofNat ((0 + 1) * (2 - 0)))
      (iterAct 0 2 0 (exhibit [1, 1, 0])).coords) :=
  iterAct_raise 0 2 (by decide +kernel) (exhibit [1, 1, 0]) 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

theorem pin16 : (elim.dotP (iterAct 0 2 2 (exhibit [1, 1, 0])).coords
      (iterAct 0 2 2 (exhibit [1, 1, 0])).coords).oneValue
    (BPair.ofNat (coeffProd 2 2)
      * elim.dotP (exhibit [1, 1, 0]).coords
        (exhibit [1, 1, 0]).coords) :=
  iterAct_selfpair 0 2 (by decide +kernel) (exhibit [1, 1, 0]) 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

/-! The coefficient product down the height-two run: the unit at
the top and the factors joined per step. -/

theorem pin17 : coeffProd 2 0 = 1 := by decide +kernel
theorem pin18 : coeffProd 2 1 = 2 := by decide +kernel
theorem pin19 : coeffProd 2 2 = 4 := by decide +kernel

/-! Beyond the height the step factor is the floor and the whole
product dies — `iterAct_selfpair`'s `hb : b ≤ h` is the bite: it
is what keeps the telescoped self-pairing off the sum's unit. -/

theorem pin20 : coeffProd 2 3 = 0 := by decide +kernel

/-! The walk's residual is what makes a top: at the doubled
content both raw span members fail the raising test, while the
collected top there passes it — the joined residual's own vector,
not any pool row, is the string's head. -/

theorem pin21 : ¬ poly.unitTail (act 0 2
    ⟨[1, 1, 1],
      ground.getAt []
        (groupAt (blockSpan [1, 1, 0]) [1, 1, 1]) 0⟩).coords := by
  rw [blockcount.span110_pin]; decide +kernel

theorem pin22 : ¬ poly.unitTail (act 0 2
    ⟨[1, 1, 1],
      ground.getAt []
        (groupAt (blockSpan [1, 1, 0]) [1, 1, 1]) 1⟩).coords := by
  rw [blockcount.span110_pin]; decide +kernel

theorem pin23 : poly.unitTail (act 0 2
    ⟨[1, 1, 1],
      ground.getAt []
        (membersAt 0 2 (walk 0 2 (blockSpan [1, 1, 0]))
          [1, 1, 1]) 1⟩).coords := by
  rw [strings.walk110_pin]; decide +kernel

/-! The threaded evaluator at the same block: the string data
through the carried member pool, beside the walk's identity. -/

theorem pin24 : (walkT 0 2 (blockSpan [1, 1, 0])).map
    (fun s => (s.top.content, s.ht))
    = [([2, 1, 0], 2), ([2, 0, 1], 1), ([1, 2, 0], 1),
       ([1, 1, 1], 0)] := by
  rw [blockcount.span110_pin]; decide +kernel

theorem pin25 : walkT 0 2 (blockSpan [1, 1, 0])
    = walk 0 2 (blockSpan [1, 1, 0]) :=
  walkT_eq 0 2 (blockSpan [1, 1, 0])

/-! `thm:weylchar`'s per-depth string weights at the two-letter
block's one string (top `[3, 1]` at height two, its members the
three contents): the raising side reads `(b+1)(h-b)` and the
lowering side `b(h-b+1)`, so the top's own depth carries the whole
raising weight and none of the lowering one, the middle content
carries two on each side — the display's `(j+1)d + j(d+1)` at the
pair `⟨2:1⟩` — and the deepest content mirrors the top.  A content
the span never carries reads the sum's own unit on both sides, the
collected list vacant. -/

theorem pin26 : stringWeightUp 0 1 (walk 0 1 (blockSpan [2, 1]))
    [3, 1] = 2 := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin27 : stringWeightDn 0 1 (walk 0 1 (blockSpan [2, 1]))
    [3, 1] = 0 := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin28 : stringWeightUp 0 1 (walk 0 1 (blockSpan [2, 1]))
    [2, 2] = 2 := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin29 : stringWeightDn 0 1 (walk 0 1 (blockSpan [2, 1]))
    [2, 2] = 2 := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin30 : weightList 0 1 (fun ht b => (b + 1) * (ht - b))
    (walk 0 1 (blockSpan [2, 1])) [1, 3] = [0] := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin31 : weightList 0 1 (fun ht b => b * (ht - b + 1))
    (walk 0 1 (blockSpan [2, 1])) [1, 3] = [2] := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin32 : stringWeightUp 0 1 (walk 0 1 (blockSpan [2, 1]))
    [5, 5] = 0 := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin33 : stringWeightDn 0 1 (walk 0 1 (blockSpan [2, 1]))
    [5, 5] = 0 := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin34 : (weightList 0 1 (fun ht b => (b + 1) * (ht - b))
      (walk 0 1 (blockSpan [2, 1])) [2, 2]).length
    = (membersAt 0 1 (walk 0 1 (blockSpan [2, 1]))
      [2, 2]).length :=
  weightList_length 0 1 (fun ht b => (b + 1) * (ht - b))
    (walk 0 1 (blockSpan [2, 1])) [2, 2]

/-! `lem:strings`' content symmetry: the reflection read decided at
the two-letter block's own three contents (the letter swap
exchanging `[3, 1]` with `[1, 3]`, the middle content its own
image), the depth run's mirror at that exchanged pair — the one
string's depths zero and two, the reversal `b ↦ h - b` — and the
theorem instances at the one-box shape and at the same block. -/

theorem pin35 : weylchar.symRead [2, 1].length
    ((blockSpan [2, 1]).map HVec.content) := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin36 : stringCount 0 1 (walk 0 1 (blockSpan [2, 1]))
    (swapPair 0 1 [3, 1])
    = stringCount 0 1 (walk 0 1 (blockSpan [2, 1])) [3, 1] := by
  rw [strings.walk21_pin]; decide +kernel

theorem pin37 : weylchar.symRead [1].length
    ((blockSpan [1]).map HVec.content) := symRead_def [1]

theorem pin38 : weylchar.symRead [2, 1].length
    ((blockSpan [2, 1]).map HVec.content) := symRead_def [2, 1]

/-! `lem:casimir`'s trace collection at the same block: the
per-pair identity discharged at the two-letter block's own pair,
once at a content the one string reaches and once at a content
below its ladder — the moved reads' whole run.  The through
content `[2, 2]` sits at depth one of the height-two string: its
two side weights are two and two, its multiplicity one, and its
moved reads run the shifts one and two, the second off the span,
so the folds read `gSnd = 2` and `gFst = 4` and the identity is
`2 + 2 + 2·2 + 1·2 = 2·4 + 1·2`, both sides ten.  The content
`[0, 4]` sits below the ladder: no member carries it, its shifts
walk the whole ladder (three of the four occupied), and the two
folds are equal at twelve — the depth pairs at the join swapping
members, the identity the doubled folds' own. -/

theorem pin39 : ground.countOf [2, 2]
    ((blockSpan [2, 1]).map HVec.content) = 1 := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin40 : weylchar.gSnd (fun chi => ground.countOf chi
    ((blockSpan [2, 1]).map HVec.content)) [2, 2] 0 1 = 2 := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin41 : weylchar.gFst (fun chi => ground.countOf chi
    ((blockSpan [2, 1]).map HVec.content)) [2, 2] 0 1 = 4 := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin42 : 2 + 2 + 2 * 2 + 1 * 2 = 2 * 4 + 1 * 2 := by decide +kernel

theorem pin43 : stringWeightUp 0 1 (walk 0 1 (blockSpan [2, 1]))
      [2, 2]
    + stringWeightDn 0 1 (walk 0 1 (blockSpan [2, 1])) [2, 2]
    + 2 * weylchar.gSnd (fun chi => ground.countOf chi
        ((blockSpan [2, 1]).map HVec.content)) [2, 2] 0 1
    + ground.countOf [2, 2] ((blockSpan [2, 1]).map HVec.content)
        * getAt 0 [2, 2] 1
  = 2 * weylchar.gFst (fun chi => ground.countOf chi
        ((blockSpan [2, 1]).map HVec.content)) [2, 2] 0 1
    + ground.countOf [2, 2] ((blockSpan [2, 1]).map HVec.content)
        * getAt 0 [2, 2] 0 :=
  stringCollect [2, 1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [2, 2] (by decide +kernel)

theorem pin44 : ground.countOf [0, 4]
    ((blockSpan [2, 1]).map HVec.content) = 0 := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin45 : weylchar.gSnd (fun chi => ground.countOf chi
    ((blockSpan [2, 1]).map HVec.content)) [0, 4] 0 1 = 12 := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin46 : weylchar.gFst (fun chi => ground.countOf chi
    ((blockSpan [2, 1]).map HVec.content)) [0, 4] 0 1 = 12 := by
  rw [blockcount.span21_pin]; decide +kernel

theorem pin47 : stringWeightUp 0 1 (walk 0 1 (blockSpan [2, 1]))
      [0, 4]
    + stringWeightDn 0 1 (walk 0 1 (blockSpan [2, 1])) [0, 4]
    + 2 * weylchar.gSnd (fun chi => ground.countOf chi
        ((blockSpan [2, 1]).map HVec.content)) [0, 4] 0 1
    + ground.countOf [0, 4] ((blockSpan [2, 1]).map HVec.content)
        * getAt 0 [0, 4] 1
  = 2 * weylchar.gFst (fun chi => ground.countOf chi
        ((blockSpan [2, 1]).map HVec.content)) [0, 4] 0 1
    + ground.countOf [0, 4] ((blockSpan [2, 1]).map HVec.content)
        * getAt 0 [0, 4] 0 :=
  stringCollect [2, 1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [0, 4] (by decide +kernel)

-- the collection identity at three letters: the reversed pair and
-- the repeated-letter content among the reads
theorem pin48 : strings.stringWeightUp 0 1
      (strings.walk 0 1 (blockSpan [1,1,0])) [1,1,1]
      + strings.stringWeightDn 0 1
        (strings.walk 0 1 (blockSpan [1,1,0])) [1,1,1]
      + 2 * weylchar.gSnd
          (fun chi => ground.countOf chi
            ((blockSpan [1,1,0]).map HVec.content)) [1,1,1] 0 1
      + ground.countOf [1,1,1]
          ((blockSpan [1,1,0]).map HVec.content)
          * getAt 0 [1,1,1] 1
    = 2 * weylchar.gFst
          (fun chi => ground.countOf chi
            ((blockSpan [1,1,0]).map HVec.content)) [1,1,1] 0 1
      + ground.countOf [1,1,1]
          ((blockSpan [1,1,0]).map HVec.content)
          * getAt 0 [1,1,1] 0 := by
  rw [blockcount.span110_pin]; decide +kernel

-- the theorem discharged at the reversed pair's instance
theorem pin49 : strings.stringWeightUp 2 0
      (strings.walk 2 0 (blockSpan [1,1,0])) [2,0,1]
      + strings.stringWeightDn 2 0
        (strings.walk 2 0 (blockSpan [1,1,0])) [2,0,1]
      + 2 * weylchar.gSnd
          (fun chi => ground.countOf chi
            ((blockSpan [1,1,0]).map HVec.content)) [2,0,1] 2 0
      + ground.countOf [2,0,1]
          ((blockSpan [1,1,0]).map HVec.content)
          * getAt 0 [2,0,1] 0
    = 2 * weylchar.gFst
          (fun chi => ground.countOf chi
            ((blockSpan [1,1,0]).map HVec.content)) [2,0,1] 2 0
      + ground.countOf [2,0,1]
          ((blockSpan [1,1,0]).map HVec.content)
          * getAt 0 [2,0,1] 2 :=
  strings.stringCollect [1,1,0] 2 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) [2,0,1] rfl

/-! The reversal clause's pins (`lem:strings`' close): the row
list's reversal occupied once at both committed spans, decided and
through the theorem; the dominance floor decided over the whole
occupancy family and read through the theorem at a member, the
membership discharged at the count; and the discrimination — a
content off the floor reads the occupancy at the count's unit. -/

theorem pin50 : ground.countOf ((rowList [1, 1]).reverse)
    ((blockSpan [1, 1]).map HVec.content) = 1 := by decide +kernel
theorem pin51 : ground.countOf ((rowList [1, 1]).reverse)
    ((blockSpan [1, 1]).map HVec.content) = 1 :=
  strings.rev_occupied [1, 1]
theorem pin52 : ground.countOf ((rowList [1, 1, 0]).reverse)
    ((blockSpan [1, 1, 0]).map HVec.content) = 1 := by
  rw [blockcount.span110_pin]; decide +kernel
theorem pin53 : ground.countOf ((rowList [1, 1, 0]).reverse)
    ((blockSpan [1, 1, 0]).map HVec.content) = 1 :=
  strings.rev_occupied [1, 1, 0]

theorem pin54 : ∀ nu ∈ (blockSpan [1, 1, 0]).map HVec.content,
    weylchar.domBy ((rowList [1, 1, 0]).reverse) nu := by
  rw [blockcount.span110_pin]; decide +kernel
theorem pin55 : weylchar.domBy ((rowList [1, 1, 0]).reverse) [1, 1, 1] :=
  strings.rev_floor [1, 1, 0] [1, 1, 1]
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
theorem pin56 : weylchar.domBy ((rowList [1, 1]).reverse) [1, 2] :=
  strings.rev_floor [1, 1] [1, 2]
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))

theorem pin57 : ¬ weylchar.domBy ((rowList [1, 1, 0]).reverse)
    [0, 0, 3] := by decide +kernel
theorem pin58 : ground.countOf [0, 0, 3]
    ((blockSpan [1, 1, 0]).map HVec.content) = 0 := by
  rw [blockcount.span110_pin]; decide +kernel

end strings
