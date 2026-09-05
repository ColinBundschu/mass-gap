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
the count, the projection's soundness at every pool member, the
fused span's groups at the ends' weight lists with the projection
group by group one value with the whole span's and its refusals at
a forged grouping, the cycle-count Gram one value with the wiring
tensors' pairings, and the tensor at the target's enumeration one
value with the scattered fold and parting at unequal letter
counts. -/
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
    ∧ wordSig (2, 1) = [false, false, true]
    ∧ endWordSig (2, 1) false = [true, true, false]
    ∧ vertexSig 3 [(th 3, true), (th 3, false)] = [false, true, true, false]
    ∧ upSlots [false, true, true, false] = [0, 3]
    ∧ downSlots [false, true, true, false] = [1, 2] := by decide +kernel

/-! The tensor at the target's enumeration is the scattered fold's
own read: at two wedges over four letters, at a wedge against the
dual wedge over three, at non-canonical coefficients and unit
entries, at the vacant power on either side, and at a ragged
coordinate list; and the two reads part at factors of unequal
letter counts, the tie's letter-count binder load-bearing. -/

private def nc : BPair := ⟨2, 2⟩
private def v1 : blockcount.HVec := ⟨[1, 0], [⟨5, 3⟩, nc]⟩
private def w1 : blockcount.HVec := ⟨[0, 1], [⟨3, 1⟩]⟩
private def v2 : blockcount.HVec := ⟨[1, 1], [⟨1, 1⟩, ⟨4, 1⟩]⟩
private def w2 : blockcount.HVec := ⟨[1, 0], [⟨1, 3⟩]⟩
private def vac : blockcount.HVec := ⟨[0, 0], [BPair.ofNat 1]⟩
private def vac2 : blockcount.HVec := ⟨[0, 0], [nc]⟩
private def rag : blockcount.HVec := ⟨[1, 1], [⟨3, 1⟩]⟩
private def tall : blockcount.HVec := ⟨[1, 0, 0], [⟨2, 1⟩]⟩

example : blockcount.tensorS (blockcount.wedge 4 2) (blockcount.wedge 4 2)
      = blockcount.tensorH (blockcount.wedge 4 2) (blockcount.wedge 4 2)
    ∧ blockcount.tensorS (blockcount.wedge 3 1) (dualWedge 3 2)
      = blockcount.tensorH (blockcount.wedge 3 1) (dualWedge 3 2)
    ∧ blockcount.tensorS (blockcount.wedge 3 2) (blockcount.wedge 3 1)
      = blockcount.tensorH (blockcount.wedge 3 2) (blockcount.wedge 3 1)
    ∧ blockcount.tensorS v1 w1 = blockcount.tensorH v1 w1
    ∧ blockcount.tensorS w1 v1 = blockcount.tensorH w1 v1
    ∧ blockcount.tensorS v2 w2 = blockcount.tensorH v2 w2
    ∧ blockcount.tensorS vac v2 = blockcount.tensorH vac v2
    ∧ blockcount.tensorS v2 vac = blockcount.tensorH v2 vac
    ∧ blockcount.tensorS vac2 v2 = blockcount.tensorH vac2 v2
    ∧ blockcount.tensorS rag w2 = blockcount.tensorH rag w2
    ∧ blockcount.tensorS (blockcount.wedge 2 1) (dualWedge 2 1)
      = blockcount.tensorH (blockcount.wedge 2 1) (dualWedge 2 1)
    ∧ blockcount.tensorS (blockcount.wedge 4 3) (blockcount.wedge 4 1)
      = blockcount.tensorH (blockcount.wedge 4 3) (blockcount.wedge 4 1) := by
  decide +kernel
example : blockcount.tensorS v1 tall ≠ blockcount.tensorH v1 tall := by
  decide +kernel

/-! The weight at two contents, the unit-weight read at canonical
and non-canonical representatives with its refusal, and the
projection's reduced representative at a shared count over
negative and non-canonical coordinates, the all-unit vector
collapsing the clearing to one. -/

example : weightAt [2, 0, 1] [1, 1, 0]
      = [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.ofNat 1]
    ∧ unitWeightAt [BPair.ofNat 2, ⟨3, 1⟩, ⟨5, 3⟩] = true
    ∧ unitWeightAt [BPair.ofNat 2, ⟨3, 1⟩, ⟨5, 4⟩] = false
    ∧ unitWeightAt [] = true
    ∧ reducePr ([⟨[1, 0], [⟨1, 7⟩, ⟨5, 1⟩]⟩], (4 : Pos))
      = ([⟨[1, 0], [⟨1, 4⟩, ⟨3, 1⟩]⟩], (2 : Pos))
    ∧ reducePr ([⟨[1, 0], [⟨3, 9⟩, BPair.unit]⟩], (9 : Pos))
      = ([⟨[1, 0], [⟨1, 3⟩, BPair.unit]⟩], (3 : Pos))
    ∧ reducePr ([⟨[1, 0], [BPair.unit, BPair.unit]⟩], (6 : Pos))
      = ([⟨[1, 0], [BPair.unit, BPair.unit]⟩], (1 : Pos)) := by
  decide +kernel

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

/-! A graded vector's occupied monomials read back the family it
was scattered from, each at its coefficient: the identity wiring's
nine monomials, the letter at the paired slots, one at each, and
the exchanged wiring's family scattered again one value with the
wiring at every content and at the pairing. -/

example : (gMons (wiringG 3 sig2 [0, 1])).length = 9
    ∧ ((gMons (wiringG 3 sig2 [0, 1])).map Prod.fst).all (fun m =>
        getAt 0 m 0 == getAt 0 m 2 && getAt 0 m 1 == getAt 0 m 3) = true
    ∧ ((gMons (wiringG 3 sig2 [0, 1])).map Prod.snd).all (fun x =>
        decide (x.oneValue (BPair.ofNat 1))) = true
    ∧ (gOfMons 3 (gMons (wiringG 3 sig2 [1, 0]))).map (fun v => v.content)
      = (wiringG 3 sig2 [1, 0]).map (fun v => v.content)
    ∧ (gdot (gOfMons 3 (gMons (wiringG 3 sig2 [1, 0]))) (wiringG 3 sig2 [1, 0])).oneValue
      (BPair.ofNat 9) := by
  decide +kernel

example : (gdot (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [0, 1])).oneValue (BPair.ofNat 9)
    ∧ (gdot (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [1, 0])).oneValue (BPair.ofNat 3)
    ∧ (places.perms 2).all (fun σ => (places.perms 2).all (fun τ =>
        decide ((gdot (wiringG 3 sig2 σ) (wiringG 3 sig2 τ)).oneValue
          (elim.dotP (mixedinv.flatF 3 2 (mixedinv.permMat σ))
            (mixedinv.flatF 3 2 (mixedinv.permMat τ)))))) = true
    ∧ mixedinv.cycleGram 3 2
      = gramOf ((places.perms 2).map (wiringG 3 [false, true, true, false]))
    ∧ mixedinv.cycleGram 2 3
      = gramOf ((places.perms 3).map
          (wiringG 2 [false, false, false, true, true, true])) := by
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

/-! The fused span's groups at the ends' weight lists, the adjoint
against its dual over three letters at seven groups with the unit
weight's four, and the projection group by group the one solve's
own read: the same coevaluation at the count eight, its clearing
reduced to three. -/

private def prG3 : GVec × Pos :=
  projectGroups (fusedGroups 3 [(th 3, true), (th 3, false)])
    (throughPair 3 (th 3, true) (th 3, false)).1

example : (fusedGroups 3 [(th 3, true), (th 3, false)]).map (fun g => g.length)
      = [1, 1, 1, 4, 1, 1, 1]
    ∧ posVal prG3.2 = 3
    ∧ (gdot prG3.1 prG3.1).oneValue (BPair.ofNat (8 * 3 * 3))
    ∧ (gdot prG3.1 prTh3.1).oneValue (BPair.ofNat (8 * 3 * 12)) := by decide +kernel

/-! The grouped solve is the whole span's solve at its reduced
representative, vector and clearing, at the adjoint against its
dual over three letters, the star over two and the fundamental pair
over three; the negated target projects to the negated vector at
the clearing, at either solve, and a scaled target to the scaled
vector at the reduced clearing; and the groups are pairwise
orthogonal at five vertices with every block member and through
pairing at one weight. -/

private def tp2 : GVec := (throughPair 2 (th 2, true) (th 2, true)).1
private def tpF : GVec := (throughPair 3 (fd 3, true) (fd 3, false)).1
private def tp3 : GVec := (throughPair 3 (th 3, true) (th 3, false)).1
private def prN3 : GVec × Pos :=
  projectGroups (fusedGroups 3 [(th 3, true), (th 3, false)])
    (gscale (BPair.ofNat 1).swap tp3)
private def prNW : GVec × Pos :=
  projectS (fusedSpan 3 [(th 3, true), (th 3, false)])
    (gscale (BPair.ofNat 1).swap tp3)
private def pr5 : GVec × Pos :=
  projectGroups (fusedGroups 3 [(th 3, true), (th 3, false)])
    (gscale (BPair.ofNat 5) tp3)

example : reducePr prTh3 = prG3
    ∧ reducePr (projectS (fusedSpan 2 [(th 2, true), (th 2, true)]) tp2)
      = projectGroups (fusedGroups 2 [(th 2, true), (th 2, true)]) tp2
    ∧ reducePr (projectS (fusedSpan 3 [(fd 3, true), (fd 3, false)]) tpF)
      = projectGroups (fusedGroups 3 [(fd 3, true), (fd 3, false)]) tpF
    ∧ prN3.2 = prG3.2 ∧ gtrim (gadd prN3.1 prG3.1) = []
    ∧ prNW.2 = prTh3.2 ∧ gtrim (gadd prNW.1 prTh3.1) = []
    ∧ pr5.2 = prG3.2
    ∧ gtrim (gadd pr5.1 (gscale (BPair.ofNat 5).swap prG3.1)) = [] := by
  decide +kernel

/-- Every cross-group pairing the sum's unit. -/
private def groupsOrth (gs : List (List GVec)) : Bool :=
  (List.range gs.length).all (fun i => (List.range gs.length).all (fun j =>
    i == j || (getAt [] gs i).all (fun u => (getAt [] gs j).all (fun v =>
      decide ((gdot u v).oneValue BPair.unit)))))

/-- Every occupied monomial's weight the vector's. -/
private def homog (d : Nat) (sig : List Bool) (g : GVec) : Bool :=
  g.all (fun v => (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
    v.coords).all (fun p =>
      decide (p.2.oneValue BPair.unit) || weightOf d sig p.1 == gWeight d sig g))

example : groupsOrth (fusedGroups 3 [(th 3, true), (th 3, false)]) = true
    ∧ groupsOrth (fusedGroups 2 [(th 2, true), (th 2, true)]) = true
    ∧ groupsOrth (fusedGroups 3 [(fd 3, true), (fd 3, false)]) = true
    ∧ groupsOrth (fusedGroups 2 [(th 2, true), (th 2, true), (th 2, false)]) = true
    ∧ groupsOrth (fusedGroups 2
        [(fd 2, true), (fd 2, true), (fd 2, true), (fd 2, true)]) = true := by
  decide +kernel
example : (blockSpanAt 3 (th 3)).all (homog 3 (labelSig 3 (th 3))) = true
    ∧ (blockSpanAt 4 (th 4)).all (homog 4 (labelSig 4 (th 4))) = true
    ∧ (blockSpanAt 4 [1, 1, 0, 0]).all (homog 4 (labelSig 4 [1, 1, 0, 0])) = true
    ∧ (blockSpanAt 3 (fdb 3)).all (homog 3 (labelSig 3 (fdb 3))) = true
    ∧ homog 3 (vertexSig 3 [(th 3, true), (th 3, false)]) tp3 = true
    ∧ homog 4 (vertexSig 4 [([0, 1, 0, 0], true), ([0, 1, 0, 0], true)])
        (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1 = true := by
  decide +kernel

/-! The grouping's refusals: the unit-weight group split into two
pairs, and the pair spelling of the weight (the undaggered content
beside the daggered in place of their balance) splitting one
weight into several, each parting the coevaluation's self-pairing
from the count at the clearing squared. -/

private def forgedSplit : List (List GVec) :=
  (fusedGroups 3 [(th 3, true), (th 3, false)]).flatMap (fun g =>
    if g.length == 4 then [g.take 2, g.drop 2] else [g])

private def pairKey (d : Nat) (sig : List Bool) (g : GVec) : List Nat × List Nat :=
  let m := g.foldl (fun (acc : Option (List Nat)) v =>
    match acc with
    | some _ => acc
    | none => (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
        v.coords).foldl (fun acc2 p =>
          match acc2 with
          | some _ => acc2
          | none => if decide (p.2.oneValue BPair.unit) then none else some p.1)
        none) none
  match m with
  | none => ([], [])
  | some m => (content d ((upSlots sig).map (fun s => getAt 0 m s)),
      content d ((downSlots sig).map (fun s => getAt 0 m s)))

private def forgedPair : List (List GVec) :=
  let es := [(th 3, true), (th 3, false)]
  let keyed := (fusedSpan 3 es).map (fun g => (g, pairKey 3 (vertexSig 3 es) g))
  (ground.dedupF (keyed.map Prod.snd)).map (fun key =>
    (keyed.filter (fun t => t.2 == key)).map Prod.fst)

private def prS : GVec × Pos := projectGroups forgedSplit tp3
private def prP : GVec × Pos := projectGroups forgedPair tp3

example : forgedSplit.map (fun g => g.length) = [1, 1, 1, 2, 2, 1, 1, 1]
    ∧ forgedPair.map (fun g => g.length) = [2, 4, 2, 1, 1]
    ∧ ¬ (gdot prS.1 prS.1).oneValue (BPair.ofNat (8 * posVal prS.2 * posVal prS.2))
    ∧ ¬ (gdot prP.1 prP.1).oneValue
        (BPair.ofNat (8 * posVal prP.2 * posVal prP.2)) := by decide +kernel
