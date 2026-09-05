import MassGap.Slotpower
import MassGap.Adjchar
import MassGap.Mixedinv
/-!
The check module for `con:slotpower`: the batteries re-read the
presentation carrier by kernel `decide` at the label calculus —
the word pairs at the fundamental and the adjoint across the counts
two to four with the tie at the count two and at the self-dual
middle column, the slot signatures at both orientations, the dual
wedge's content and side reads, the block's top killed by every
raising at its signature against the standard wedge at the
daggered slot surviving one, the blocks' spans at the word pairs
at the blocks' counts against the closure at the standard action
on the daggered slot reading below the count, the block's raising
kernel one line, the unit weight at the tensors of a block against
its dual and its refusal at unmatched weights with the fused span
at the unit weight throughout, the graded vector at a stated
monomial family and the primitive representative's scale
invariance, the unit's action at one slot folding to the carrier's
action at the occupied moves, the wiring tensors pairing at the
cycle count and at `lem:mixedinv`'s flat forms, and the through
pairing's projection at the block's count at the wiring and at the
star, the star's raw self-pairing at the factorial's multiple of
the count and the projection's soundness at every pool member. -/
set_option maxHeartbeats 4000000

open ground places slotpower

private def th (d : Nat) : Shape := adjchar.theta d
private def fd (d : Nat) : Shape := ground.bumpAt 0 (labels.unitL d)
private def fdb (d : Nat) : Shape := labels.dualL (fd d)

example : wordPair 2 (th 2) = (2, 0) ∧ wordPair 3 (th 3) = (1, 1)
    ∧ wordPair 4 (th 4) = (1, 1) ∧ wordPair 4 (fd 4) = (1, 0)
    ∧ wordPair 4 [0, 1, 0, 0] = (2, 0) ∧ wordPair 4 [2, 0, 2, 0] = (2, 2)
    ∧ wordPair 3 (fdb 3) = (0, 1) := by decide +kernel

example : labelSig 3 (th 3) = [false, true]
    ∧ labelSig 3 (fdb 3) = [true]
    ∧ labelSig 2 (th 2) = [false, false]
    ∧ endSig 3 (th 3, false) = [true, false]
    ∧ vertexSig 3 [(th 3, true), (th 3, false)] = [false, true, true, false]
    ∧ upSlots [false, true, true, false] = [0, 3]
    ∧ downSlots [false, true, true, false] = [1, 2] := by decide +kernel

/-! The dual wedge at the complement's length sits on the last
letters, each arrangement on its permutation's side; the block's
top is killed by every raising at the label's signature, and the
standard wedge at the daggered slot in its place survives one. -/

example : (dualWedge 3 2).content = [0, 1, 1]
    ∧ (dualWedge 3 2).coords = [BPair.ofNat 1, (BPair.ofNat 1).swap] := by
  decide +kernel

private def topKilled (d : Nat) (s : Shape) : Bool :=
  (List.range (d - 1)).all (fun i => gtrim (raiseS (labelSig d s) i [blockTop d s]) == [])

private def wrongTop (d : Nat) (s : Shape) : blockcount.HVec :=
  (botCols d s).foldl (fun acc l => blockcount.tensorH acc (blockcount.wedge d (d - l)))
    ((topCols d s).foldl (fun acc l => blockcount.tensorH acc (blockcount.wedge d l))
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩)

example : topKilled 3 (th 3) = true ∧ topKilled 3 (fdb 3) = true
    ∧ topKilled 4 (th 4) = true
    ∧ (List.range 2).all (fun i =>
        gtrim (raiseS (labelSig 3 (th 3)) i [wrongTop 3 (th 3)]) == []) = false := by
  decide +kernel

/-! The blocks' spans at the word pairs read the blocks' counts:
the adjoint three at two letters, eight at three and fifteen at
four, the fundamental and its dual three at three letters, and the
self-dual middle column six at four; the closure at the standard
action on the daggered slot reads three against the adjoint's
eight; and the block's raising kernel over its span is one line. -/

example : (blockSpanAt 2 (th 2)).length = 3
    ∧ (blockSpanAt 3 (th 3)).length = 8
    ∧ (blockSpanAt 3 (fd 3)).length = 3
    ∧ (blockSpanAt 3 (fdb 3)).length = 3
    ∧ (blockSpanAt 4 (th 4)).length = 15
    ∧ (blockSpanAt 4 [0, 1, 0, 0]).length = 6 := by decide +kernel

/-- The lowering at the standard action on every slot, the dual
action withdrawn. -/
private def lowerStd (sig : List Bool) (i : Nat) (g : GVec) : GVec :=
  g.foldl (fun acc v => (List.range sig.length).foldl (fun acc2 s =>
    match slotAct s (i + 1) i v with
    | none => acc2
    | some w => gjoin acc2 w) acc) []

/-- The membership read at the whole pool's Gram. -/
private def joinAll (pool : List GVec) (g : GVec) : List GVec :=
  if (elim.detD (gramOf (pool ++ [g]))).oneValue BPair.unit then pool else pool ++ [g]

private def closeStd (d : Nat) (s : Shape) : List GVec :=
  let sig := labelSig d s
  ground.closeBy (fun g => (List.range (d - 1)).map (fun i => gtrim (lowerStd sig i g)))
    joinAll (sig.length * d + 1) [[blockTop d s]] [[blockTop d s]]

example : (closeStd 3 (th 3)).length = 3 := by decide +kernel

example : (kernelAt 3 (labelSig 3 (th 3)) (blockSpanAt 3 (th 3))).length = 1
    ∧ (kernelAt 3 (labelSig 3 (fdb 3)) (blockSpanAt 3 (fdb 3))).length = 1
    ∧ (kernelAt 4 (labelSig 4 [0, 1, 1, 0]) (blockSpanAt 4 [0, 1, 1, 0])).length = 1 := by
  decide +kernel

/-! The unit weight: a block's top tensored with its own at the
exchanged signature reads the unit weight, and against a further
member's off it; the fused span of the adjoint against its dual at
three letters holds the weight-matched pairs, ten, every member at
the unit weight. -/

example : gUnitWeight 3 [false, true, true, false]
      (gtensor [blockTop 3 (th 3)] [blockTop 3 (th 3)]) = true
    ∧ gUnitWeight 3 [false, true, true, false]
      (gtensor [blockTop 3 (th 3)] (ground.getAt [] (blockSpanAt 3 (th 3)) 1)) = false
    ∧ (fusedSpan 3 [(th 3, true), (th 3, false)]).length = 10
    ∧ (fusedSpan 3 [(th 3, true), (th 3, false)]).all
        (gUnitWeight 3 (vertexSig 3 [(th 3, true), (th 3, false)])) = true := by
  decide +kernel

/-! The graded vector at a stated monomial family scatters each
coefficient at its monomial's rank, one piece per content; and the
primitive representative is one value across a scale. -/

private def gm : GVec :=
  gOfMons 3 [([1, 0], BPair.ofNat 1), ([0, 1], BPair.ofNat 1), ([1, 0], BPair.ofNat 1)]

example : gm.length = 1
    ∧ List.zipWith (fun x n => decide (x.oneValue (BPair.ofNat n)))
        (pieceAt [1, 1, 0] gm) [1, 2] = [true, true]
    ∧ gprim (gscale (BPair.ofNat 5) [blockTop 3 (th 3)]) = gprim [blockTop 3 (th 3)] := by
  decide +kernel

/-! The unit's action at one slot folds to the carrier's action at
an occupied move: the slot fold's one piece reads the moved content
with the coordinates' gap at the unit family. -/

private def actFold (n i j : Nat) (v : blockcount.HVec) : GVec :=
  (List.range n).foldl (fun acc s =>
    match slotAct s i j v with
    | none => acc
    | some w => gjoin acc w) []

private def actTie (n i j : Nat) (v : blockcount.HVec) : Bool :=
  match actFold n i j v with
  | [] => false
  | [w] => w.content == (blockcount.act i j v).content
      && blockcount.allU (elim.vecAdd w.coords (poly.neg (blockcount.act i j v).coords))
  | _ :: _ :: _ => false

example : actTie 2 1 0 (blockTop 3 (th 3)) = true
    ∧ actTie 2 2 0 (blockTop 3 (th 3)) = true
    ∧ actTie 3 1 0 (blockcount.exhibit [1, 1, 0]) = true
    ∧ actTie 3 2 1 (blockcount.tensorH (blockcount.wedge 3 2) (blockcount.wedge 3 1)) = true
    ∧ actTie 3 2 0 (blockcount.tensorH (blockcount.wedge 3 2) (blockcount.wedge 3 1)) = true := by
  decide +kernel

/-! The wirings' tensors pair at the cycle count: at two rows over
three letters the identity against itself two cycles, nine, and
against the swap one cycle, three; and the pairings are the flat
forms' (`lem:mixedinv`'s coordinate form) at every permutation
pair. -/

private def sig2 : List Bool := [false, false, true, true]

example : (gdot (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [0, 1])).oneValue (BPair.ofNat 9)
    ∧ (gdot (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [1, 0])).oneValue (BPair.ofNat 3)
    ∧ (places.perms 2).all (fun σ => (places.perms 2).all (fun τ =>
        decide ((gdot (wiringG 3 sig2 σ) (wiringG 3 sig2 τ)).oneValue
          (elim.dotP (mixedinv.flatF 3 2 (mixedinv.permMat σ))
            (mixedinv.flatF 3 2 (mixedinv.permMat τ)))))) = true := by
  decide +kernel

/-! The through pairing and its projection: at the adjoint against
its dual over three letters the pairing is the wiring, its
self-pairing the two cycles' nine, and the projection to the fused
span reads the block's coevaluation at the count eight over the
projection's clearing squared, every pool member pairing the
projection as it pairs the target at the clearing; at two outgoing
adjoints over two letters the star, the projection at the count
three; at the self-dual middle column over four letters the star's
raw self-pairing twenty-four at the clearing two, the factorial's
multiple of the count six, and at the two tie columns of the
(2, 2) shape the clearing four; and off the dual pair the vacant
pairing. -/

example : (throughPair 3 (th 3, true) (th 3, false)).2 = Pos.one
    ∧ (gdot (throughPair 3 (th 3, true) (th 3, false)).1
        (throughPair 3 (th 3, true) (th 3, false)).1).oneValue (BPair.ofNat 9)
    ∧ (throughPair 3 (fd 3, true) (fd 3, true)).1 = []
    ∧ posVal (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).2 = 2
    ∧ (gdot (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1
        (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1).oneValue
        (BPair.ofNat 24)
    ∧ posVal (throughPair 4 ([0, 2, 0, 0], true) ([0, 2, 0, 0], true)).2 = 4 := by
  decide +kernel

private def prTh3 : GVec × Pos :=
  projectS (fusedSpan 3 [(th 3, true), (th 3, false)])
    (throughPair 3 (th 3, true) (th 3, false)).1
private def prTh2 : GVec × Pos :=
  projectS (fusedSpan 2 [(th 2, true), (th 2, true)])
    (throughPair 2 (th 2, true) (th 2, true)).1

example : (gdot prTh3.1 prTh3.1).oneValue
    (BPair.ofNat (8 * posVal prTh3.2 * posVal prTh3.2)) := by decide +kernel
example : (gdot prTh2.1 prTh2.1).oneValue
    (BPair.ofNat (3 * posVal prTh2.2 * posVal prTh2.2)) := by decide +kernel
example : posVal prTh3.2 = 12
    ∧ (fusedSpan 3 [(th 3, true), (th 3, false)]).all (fun u =>
        decide ((gdot u prTh3.1).oneValue
          (gdot u (throughPair 3 (th 3, true) (th 3, false)).1
            * BPair.ofNat (posVal prTh3.2)))) = true := by decide +kernel
