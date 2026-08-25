import MassGap.Units
/-!
The check module for `con:units`: the batteries re-read the unit
action's identity instances by kernel `decide` — the Leibniz
summands, the units' matrices on a monomial basis, the commutator
table `[E_ab, E_cd] + δ_da E_cb = δ_bc E_ad` at two instances on
the power, the stacked adjacent raisings' shape, and the grading's
null read at a compression between contents the action does not
connect, its reached mirror off it.
-/

open ground places units elim

/-! The Leibniz action. -/

example : unitAct 0 1 [0, 1] = [[0, 0]] := rfl
example : unitAct 0 1 [1, 1] = [[0, 1], [1, 0]] := rfl
example : unitAct 1 0 [0, 0] = [[1, 0], [0, 1]] := rfl

/-! The commutator table on `V^⊗2` at two letters:
`[E_01, E_10] + E_11 = E_00`, and `[E_00, E_01] = E_01`. -/

example : matOneValue
    (matAdd
      (matAdd (matMul (matUnit (allMon 2 2) (allMon 2 2) 0 1)
        (matUnit (allMon 2 2) (allMon 2 2) 1 0))
        (matSwap (matMul (matUnit (allMon 2 2) (allMon 2 2) 1 0)
          (matUnit (allMon 2 2) (allMon 2 2) 0 1))))
      (matUnit (allMon 2 2) (allMon 2 2) 1 1))
    (matUnit (allMon 2 2) (allMon 2 2) 0 0) := by decide +kernel

example : matOneValue
    (matAdd (matMul (matUnit (allMon 2 2) (allMon 2 2) 0 0)
      (matUnit (allMon 2 2) (allMon 2 2) 0 1))
      (matSwap (matMul (matUnit (allMon 2 2) (allMon 2 2) 0 1)
        (matUnit (allMon 2 2) (allMon 2 2) 0 0))))
    (matUnit (allMon 2 2) (allMon 2 2) 0 1) := by decide +kernel

/-- The both-zero table row: `[E_00, E_11] = 0` on the power. -/
example : matOneValue
    (matAdd (matMul (matUnit (allMon 2 2) (allMon 2 2) 0 0)
      (matUnit (allMon 2 2) (allMon 2 2) 1 1))
      (matSwap (matMul (matUnit (allMon 2 2) (allMon 2 2) 1 1)
        (matUnit (allMon 2 2) (allMon 2 2) 0 0))))
    ((allMon 2 2).map (fun _ => (allMon 2 2).map (fun _ => BPair.unit)))
    := by decide +kernel

/-! The pairing's transpose read `E_ij^T = E_ji`. -/

example : matOneValue
    (transposeM (matUnit (allMon 2 2) (allMon 2 2) 0 1))
    (matUnit (allMon 2 2) (allMon 2 2) 1 0) := by decide +kernel

/-! The scatter-built unit matrix agrees with the counted one at
content bases. -/

example : matOneValue (matUnitAt [2, 1] [1, 2] 0 1)
    (matUnit (monomialsAt [2, 1]) (monomialsAt [1, 2]) 0 1) := by decide +kernel
example : matOneValue (matUnitAt [1, 2, 0] [1, 1, 1] 1 2)
    (matUnit (monomialsAt [1, 2, 0]) (monomialsAt [1, 1, 1]) 1 2) := by
  decide +kernel

/-! The stacked raisings' key counts at the adjoint content. -/

example : (stackedRaise [1, 1]).length = 1 := rfl
example : (stackedRaise [2, 0]).length = 0 := rfl

/-! The commutator table at the monomial level: the count identity's
theorem instances beside decided values, the contraction's occupied
read among them. -/

example :
    ground.countOf [0, 1]
        ((unitAct 1 0 [0, 1]).flatMap (unitAct 0 1))
      + (if (0 : Nat) == 0 then
          ground.countOf [0, 1] (unitAct 1 1 [0, 1]) else 0)
    = ground.countOf [0, 1]
        ((unitAct 0 1 [0, 1]).flatMap (unitAct 1 0))
      + (if (1 : Nat) == 1 then
          ground.countOf [0, 1] (unitAct 0 0 [0, 1]) else 0) := by
  decide +kernel

example :
    ground.countOf [0, 1]
        ((unitAct 1 0 [0, 1]).flatMap (unitAct 0 1))
      + (if (0 : Nat) == 0 then
          ground.countOf [0, 1] (unitAct 1 1 [0, 1]) else 0)
    = ground.countOf [0, 1]
        ((unitAct 0 1 [0, 1]).flatMap (unitAct 1 0))
      + (if (1 : Nat) == 1 then
          ground.countOf [0, 1] (unitAct 0 0 [0, 1]) else 0) :=
  act_comm 0 1 1 0 [0, 1] [0, 1]

example :
    ground.countOf [2, 0, 1]
        ((unitAct 2 1 [1, 0, 1]).flatMap (unitAct 1 0))
      + (if (1 : Nat) == 1 then
          ground.countOf [2, 0, 1] (unitAct 2 0 [1, 0, 1]) else 0)
    = ground.countOf [2, 0, 1]
        ((unitAct 1 0 [1, 0, 1]).flatMap (unitAct 2 1))
      + (if (0 : Nat) == 2 then
          ground.countOf [2, 0, 1] (unitAct 1 1 [1, 0, 1]) else 0) :=
  act_comm 1 0 2 1 [1, 0, 1] [2, 0, 1]

/-! The matrix tier's pins (`con:units`): the unit matrix's entry
the Leibniz count at the row's monomial, with the transpose and
diagonal count reads — theorem instances beside decided values. -/

example : (ground.getAt BPair.unit
    (ground.getAt [] (matUnitAt [1, 2, 0] [2, 1, 0] 1 0) 0)
    0).oneValue
  (BPair.ofNat (ground.countOf
    (ground.getAt [] (monomialsAt [1, 2, 0]) 0)
    (unitAct 1 0 (ground.getAt [] (monomialsAt [2, 1, 0]) 0)))) := by
  decide +kernel
example : ground.countOf [0, 2, 1] (unitAct 0 1 [1, 2, 1])
    = ground.countOf [1, 2, 1] (unitAct 1 0 [0, 2, 1]) :=
  countOf_unitAct_swap 0 1 [1, 2, 1] [0, 2, 1]
example : ground.countOf [0, 2, 1] (unitAct 0 1 [1, 2, 1]) = 1 := by
  decide +kernel
example : ground.countOf [1, 2, 1] (unitAct 2 2 [1, 2, 1])
    = if [1, 2, 1] = [1, 2, 1] then ground.countOf 2 [1, 2, 1]
      else 0 :=
  countOf_unitAct_diag 2 [1, 2, 1] [1, 2, 1]
example : ground.countOf [1, 2, 1] (unitAct 2 2 [1, 2, 1]) = 1 := by
  decide +kernel

/-! The convolution's pin: the composed Leibniz counts collect over
the moved content's enumeration, the theorem instance beside the
decided value. -/

example : ground.countOf [0, 1]
      ((unitAct 1 0 [0, 1]).flatMap (unitAct 0 1))
    = ground.famFold Nat.add 0
      (fun m => ground.countOf m (unitAct 1 0 [0, 1])
        * ground.countOf [0, 1] (unitAct 0 1 m))
      (monomialsAt [0, 2]) :=
  countOf_unitAct_comp 0 1 1 0 [0, 2] [0, 1] [0, 1]
    (fun m hm => by
      by_cases hme : m = [1, 1]
      · rw [hme]
        decide +kernel
      · rw [show ground.countOf m (unitAct 1 0 [0, 1])
            = ground.countOf m [[1, 1]] from rfl,
          ground.countOf_cons m [1, 1] ([] : List (List Nat)),
          if_neg hme] at hm
        exact absurd hm (Nat.lt_irrefl 0))

example : ground.countOf [0, 1]
      ((unitAct 1 0 [0, 1]).flatMap (unitAct 0 1)) = 1 := by decide +kernel

/-! The matrix tier's action pins: the equal-lettered unit at the
letter's occupancy scalar, and the transpose's letter exchange at
the square and the rectangular pair. -/

/-- The occupancy-2 diagonal on the content `[2, 1]`, off the
value-1 case: the matrix is the scalar 2 at the three monomials,
the theorem instance beside the acted read. -/
example : matOneValue (matUnitAt [2, 1] [2, 1] 0 0)
    [[⟨3, 1⟩, BPair.unit, BPair.unit],
     [BPair.unit, ⟨3, 1⟩, BPair.unit],
     [BPair.unit, BPair.unit, ⟨3, 1⟩]] := by decide +kernel

example : poly.oneValue
    (matVec (matUnitAt [2, 1] [2, 1] 0 0) [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩])
    (vecScale (BPair.ofNat 2) [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]) := by decide +kernel

example : poly.oneValue
    (matVec (matUnitAt [2, 1] [2, 1] 0 0) [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩])
    (vecScale (BPair.ofNat 2) [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩]) :=
  matVec_diag_read [2, 1] 0 (by decide +kernel) [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩] rfl

/-- `E_ij^T = E_ji` at the moved contents: the raising pair on the
two-letter power, then the rectangular exchange where the source
enumeration is three monomials wide and the target one. -/
example : matOneValue (transposeM (matUnitAt [2, 0] [1, 1] 0 1))
    (matUnitAt [1, 1] [2, 0] 1 0) := by decide +kernel

example : matOneValue (transposeM (matUnitAt [3, 0] [2, 1] 0 1))
    (matUnitAt [2, 1] [3, 0] 1 0) := by decide +kernel

/-! The grading's null read (`matUnitAt_null_offcontent`): the
raising sends the content `[1,1]` to `[2,0]`, so the compression
back onto `[1,1]` meets no output and is the null map, while the
compression onto the content the action does reach is off it. -/

example : matNull (matUnitAt [1, 1] [1, 1] 0 1) := by decide +kernel

example : ¬ matNull (matUnitAt [2, 0] [1, 1] 0 1) := by decide +kernel

/-! The adjacent lowering's row read: both binders are
load-bearing — past the width the moved key is the singleton's own
and the raise misses, and at a vacant key the lowering reads the
subtraction's floor rather than a move — with the held pair's read
standing beside them through the theorem. -/

example : ¬ (places.rowList (moveDn 0 [1])
    = ground.bumpAt 1 (places.rowList [1])) := by decide +kernel
example : ¬ (places.rowList (moveDn 0 [0, 1])
    = ground.bumpAt 1 (places.rowList [0, 1])) := by decide +kernel
example : places.rowList (moveDn 0 [1, 1])
    = ground.bumpAt 1 (places.rowList [1, 1]) := by decide +kernel
example : places.rowList (moveDn 0 [1, 1])
    = ground.bumpAt 1 (places.rowList [1, 1]) :=
  rowList_moveDn 0 [1, 1] (by decide +kernel) (by decide +kernel)
