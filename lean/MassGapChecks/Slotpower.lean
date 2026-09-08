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
at the unit weight throughout, the collection at a stated
monomial family with the unit entries withdrawn and the primitive
representative's scale invariance, the table's action at one slot
one value with the carrier's action at the occupied moves, the
wiring tensors pairing at the cycle count and at `lem:mixedinv`'s
flat forms, and the through pairing's projection at the block's
count at the wiring and at the star, the star's raw self-pairing
at the factorial's multiple of the count, the projection's
soundness at every pool member, the fused span's groups at the
ends' weight lists with the projection group by group one value
with the whole span's and its refusals at a forged grouping, the
cycle-count Gram one value with the wiring tensors' pairings, and
the tensor at the target's enumeration one value with the
scattered fold and parting at unequal letter counts. -/
set_option maxHeartbeats 4000000

open ground places slotpower

private def th (d : Nat) : Shape := adjchar.theta d
private def fd (d : Nat) : Shape := ground.bumpAt 0 (labels.unitL d)
private def fdb (d : Nat) : Shape := labels.dualL (fd d)
private def tabL (d : Nat) : memtable.Table := memtable.lettersT d

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

/-! The sparse tensor is the dense tensor's occupied family: at two
wedges over four letters and at a wedge against the dual wedge
over three, `tensorV` at the exhibits' occupied monomials one value
with `blockcount.tensorS`'s. -/

example : oneValueV (tensorV (ofH (blockcount.wedge 4 2)) (ofH (blockcount.wedge 4 2)))
      (ofH (blockcount.tensorS (blockcount.wedge 4 2) (blockcount.wedge 4 2))) = true
    ∧ oneValueV (tensorV (ofH (blockcount.wedge 3 1)) (ofH (dualWedge 3 2)))
      (ofH (blockcount.tensorS (blockcount.wedge 3 1) (dualWedge 3 2))) = true
    ∧ oneValueV (tensorV (ofH v1) (ofH w1)) (ofH (blockcount.tensorS v1 w1)) = true := by
  decide +kernel

/-! The weight at two contents, the unit-weight read at canonical
and non-canonical representatives with its refusal, the collection
at a stated monomial family with the unit entries withdrawn, and
the projection's reduced representative at a shared count over
negative and non-canonical coordinates, the all-unit vector
collapsing the clearing to one. -/

example : weightAt [2, 0, 1] [1, 1, 0]
      = [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.ofNat 1]
    ∧ unitWeightAt [BPair.ofNat 2, ⟨3, 1⟩, ⟨5, 3⟩] = true
    ∧ unitWeightAt [BPair.ofNat 2, ⟨3, 1⟩, ⟨5, 4⟩] = false
    ∧ unitWeightAt [] = true
    ∧ collect [([1, 0], BPair.ofNat 1), ([0, 1], BPair.ofNat 1), ([1, 0], BPair.ofNat 1)]
      = [([0, 1], BPair.ofNat 1), ([1, 0], BPair.ofNat 2)]
    ∧ collect [([0], ⟨4, 4⟩), ([1], ⟨5, 3⟩)] = [([1], BPair.ofNat 2)]
    ∧ reduceV ([([1, 0], ⟨1, 7⟩), ([0, 1], ⟨5, 1⟩)], (4 : Pos))
      = ([([1, 0], ⟨1, 4⟩), ([0, 1], ⟨3, 1⟩)], (2 : Pos))
    ∧ reduceV ([([1, 0], ⟨3, 9⟩)], (9 : Pos)) = ([([1, 0], ⟨1, 3⟩)], (3 : Pos))
    ∧ reduceV ([], (6 : Pos)) = ([], (1 : Pos))
    ∧ prim (scaleV (BPair.ofNat 5) (ofH (blockTop 3 (th 3))))
      = prim (ofH (blockTop 3 (th 3))) := by
  decide +kernel

/-! The dual wedge at the complement's length sits on the last
letters, each arrangement on its permutation's side; the block's
top is killed by every raising at the label's signature, and the
standard wedge at the daggered slot in its place survives one. -/

example : (dualWedge 3 2).content = [0, 1, 1]
    ∧ (dualWedge 3 2).coords = [BPair.ofNat 1, (BPair.ofNat 1).swap] := by
  decide +kernel

private def topKilled (d : Nat) (s : Shape) : Bool :=
  (List.range (d - 1)).all (fun i =>
    raiseT (tabL d) (labelSig d s) i (ofH (blockTop d s)) == [])

private def wrongTop (d : Nat) (s : Shape) : blockcount.HVec :=
  (botCols d s).foldl (fun acc l => blockcount.tensorH acc (blockcount.wedge d (d - l)))
    ((topCols d s).foldl (fun acc l => blockcount.tensorH acc (blockcount.wedge d l))
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩)

example : topKilled 3 (th 3) = true ∧ topKilled 3 (fdb 3) = true
    ∧ topKilled 4 (th 4) = true
    ∧ (List.range 2).all (fun i =>
        raiseT (tabL 3) (labelSig 3 (th 3)) i (ofH (wrongTop 3 (th 3))) == []) = false := by
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

/-! The block at the stored descents against the closure at the
fresh walk from the top's own join (`blockSpanAt_eq`), decided at
the adjoint over three letters; the symmetry binder of
`blockSpanT_eq` refused at the letters' weight joined one entry off
the diagonal, the two closures parting; the weighted read at the
`B_2` defining table's top, the two closures one list of five; and
at a symmetric indefinite weight whose top pairs against itself at
the unit, the top refused at the vacant pool, the two closures one
list where the closure seeded at the top outright parts. -/

example : blockSpanAt 3 (th 3)
    = closeT (tabL 3) (labelSig 3 (th 3))
        ((labelSig 3 (th 3)).length * (tabL 3).keys + 1)
        (tryAddT (tabL 3) (labelSig 3 (th 3)) [] (ofH (blockTop 3 (th 3))))
        [ofH (blockTop 3 (th 3))] := by decide +kernel

private def asymL : memtable.Table :=
  { tabL 3 with wt := [(0, 0, BPair.ofNat 1), (1, 1, BPair.ofNat 1),
      (2, 2, BPair.ofNat 1), (0, 1, BPair.ofNat 1)] }
private def asymTop : SVec := [([1, 0], BPair.ofNat 1), ([2, 2], BPair.ofNat 1)]

example : ¬ memtable.symmWt asymL
    ∧ ¬ (blockSpanT asymL [false, true] asymTop
        = closeT asymL [false, true] ([false, true].length * asymL.keys + 1)
            (tryAddT asymL [false, true] [] asymTop) [asymTop]) := by
  decide +kernel

private def bTop : SVec := [([0], BPair.ofNat 1)]

example : memtable.symmWt (memtable.definingB 2)
    ∧ blockSpanT (memtable.definingB 2) [false] bTop
      = closeT (memtable.definingB 2) [false]
          ([false].length * (memtable.definingB 2).keys + 1)
          (tryAddT (memtable.definingB 2) [false] [] bTop) [bTop]
    ∧ (blockSpanT (memtable.definingB 2) [false] bTop).length = 5 := by
  decide +kernel

private def isoL : memtable.Table :=
  { tabL 3 with
      wt := [(0, 1, BPair.ofNat 1), (1, 0, BPair.ofNat 1), (2, 2, BPair.ofNat 1)],
      hdiag := [[BPair.unit, BPair.unit, BPair.unit],
        [BPair.unit, BPair.unit, BPair.unit]] }
private def isoTop : SVec := [([0], BPair.ofNat 1)]

example : memtable.symmWt isoL
    ∧ elim.joinIndep (fun u v => (dotT isoL (unitWtRead isoL) u v).norm) []
        isoTop = false
    ∧ blockSpanT isoL [false] isoTop
      = closeT isoL [false] ([false].length * isoL.keys + 1)
          (tryAddT isoL [false] [] isoTop) [isoTop]
    ∧ ¬ (blockSpanT isoL [false] isoTop
        = closeT isoL [false] ([false].length * isoL.keys + 1)
            [isoTop] [isoTop]) := by decide +kernel

/-- The lowering at the standard action on every slot, the dual
action withdrawn. -/
private def lowerStd (d : Nat) (sig : List Bool) (i : Nat) (v : SVec) : SVec :=
  collect ((List.range sig.length).flatMap (fun s =>
    actT (ground.getAt [] (tabL d).lowers i) false s v))

private def closeStd (d : Nat) (s : Shape) : List SVec :=
  let sig := labelSig d s
  ground.closeBy (fun v => ((List.range (d - 1)).map (fun i => lowerStd d sig i v)).filter
      (fun w => w.length != 0))
    (tryAddT (tabL d) sig) (sig.length * d + 1) [ofH (blockTop d s)] [ofH (blockTop d s)]

example : (closeStd 3 (th 3)).length = 3 := by decide +kernel

example : (kernelT (tabL 3) (labelSig 3 (th 3)) (blockSpanAt 3 (th 3))).length = 1
    ∧ (kernelT (tabL 3) (labelSig 3 (fdb 3)) (blockSpanAt 3 (fdb 3))).length = 1
    ∧ (kernelT (tabL 4) (labelSig 4 [0, 1, 1, 0]) (blockSpanAt 4 [0, 1, 1, 0])).length = 1 := by
  decide +kernel

/-! The unit weight: a block's top tensored with its own at the
exchanged signature reads the unit weight, and against a further
member's off it; the fused span of the adjoint against its dual at
three letters holds the weight-matched pairs, ten, every member at
the unit weight. -/

private def unitW (d : Nat) (sig : List Bool) (v : SVec) : Bool :=
  (weightV (tabL d) sig v).all (fun x => decide (x.oneValue BPair.unit))

example : unitW 3 [false, true, true, false]
      (tensorV (ofH (blockTop 3 (th 3))) (ofH (blockTop 3 (th 3)))) = true
    ∧ unitW 3 [false, true, true, false]
      (tensorV (ofH (blockTop 3 (th 3))) (ground.getAt [] (blockSpanAt 3 (th 3)) 1)) = false
    ∧ (fusedSpanT (tabL 3) (endBlocks 3 [(th 3, true), (th 3, false)])).length = 10
    ∧ (fusedSpanT (tabL 3) (endBlocks 3 [(th 3, true), (th 3, false)])).all
        (unitW 3 (vertexSig 3 [(th 3, true), (th 3, false)])) = true := by
  decide +kernel

/-! The table's action at one slot is the carrier's action at an
occupied move: the letters' raising at a slot on an exhibit one
value with `blockcount.act` there, at the adjoint's top over three
letters and at the exhibits' tensors. -/

private def actTie (d i j : Nat) (v : blockcount.HVec) : Bool :=
  let m : memtable.SMap := if i < j then ground.getAt [] (tabL d).raises i
    else ground.getAt [] (tabL d).lowers j
  oneValueV (collect ((List.range v.content.length).flatMap (fun s => actT m false s (ofH v))))
    (ofH (blockcount.act i j v))

example : actTie 3 1 0 (blockcount.exhibit [1, 1, 0]) = true
    ∧ actTie 3 2 1 (blockcount.tensorH (blockcount.wedge 3 2) (blockcount.wedge 3 1)) = true
    ∧ actTie 3 0 1 (blockcount.tensorH (blockcount.wedge 3 2) (blockcount.wedge 3 1)) = true
    ∧ actTie 3 1 2 (blockcount.exhibit [2, 1, 0]) = true := by
  decide +kernel

/-! The wirings' tensors pair at the cycle count: at two rows over
three letters the identity against itself two cycles, nine, and
against the swap one cycle, three; and the pairings are the flat
forms' (`lem:mixedinv`'s coordinate form) at every permutation
pair. -/

private def sig2 : List Bool := [false, false, true, true]

/-! A wiring's family: the identity wiring's nine monomials, the
letter at the paired slots, one at each. -/

example : (wiringG 3 sig2 [0, 1]).length = 9
    ∧ ((wiringG 3 sig2 [0, 1]).map Prod.fst).all (fun m =>
        getAt 0 m 0 == getAt 0 m 2 && getAt 0 m 1 == getAt 0 m 3) = true
    ∧ ((wiringG 3 sig2 [0, 1]).map Prod.snd).all (fun x =>
        decide (x.oneValue (BPair.ofNat 1))) = true := by
  decide +kernel

private def dot3 (u v : SVec) : BPair := dotT (tabL 3) true u v

example : (dot3 (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [0, 1])).oneValue (BPair.ofNat 9)
    ∧ (dot3 (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [1, 0])).oneValue (BPair.ofNat 3)
    ∧ (places.perms 2).all (fun σ => (places.perms 2).all (fun τ =>
        decide ((dot3 (wiringG 3 sig2 σ) (wiringG 3 sig2 τ)).oneValue
          (elim.dotP (mixedinv.flatF 3 2 (mixedinv.permMat σ))
            (mixedinv.flatF 3 2 (mixedinv.permMat τ)))))) = true
    ∧ mixedinv.cycleGram 3 2
      = gramT (tabL 3) ((places.perms 2).map (wiringG 3 [false, true, true, false]))
    ∧ mixedinv.cycleGram 2 3
      = gramT (tabL 2) ((places.perms 3).map
          (wiringG 2 [false, false, false, true, true, true])) := by
  decide +kernel

/-! The star's family at the withdrawn content's arrangements
against the permutations opening at the arrangement
(`starFam_perms`), decided over four letters at a two-letter and a
one-letter arrangement, vacant at a repeated letter, and through
the theorem. -/

example : starFam 4 [1, 0]
    = (perms 4).filterMap (fun ls =>
        if ls.take 2 == [1, 0] then
          some (ls.drop 2,
            if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1)
        else none)
    ∧ starFam 4 [2]
      = (perms 4).filterMap (fun ls =>
          if ls.take 1 == [2] then
            some (ls.drop 1,
              if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1)
          else none)
    ∧ (starFam 4 [1, 0]).length = 2
    ∧ starFam 4 [1, 1] = [] := by decide +kernel
example : starFam 4 [1, 0]
    = (perms 4).filterMap (fun ls =>
        if ls.take 2 == [1, 0] then
          some (ls.drop 2,
            if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1)
        else none) :=
  starFam_perms 4 [1, 0]

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
    ∧ (dot3 (throughPair 3 (th 3, true) (th 3, false)).1
        (throughPair 3 (th 3, true) (th 3, false)).1).oneValue (BPair.ofNat 9)
    ∧ (throughPair 3 (fd 3, true) (fd 3, true)).1 = []
    ∧ posVal (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).2 = 2
    ∧ (dotT (tabL 4) true (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1
        (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1).oneValue
        (BPair.ofNat 24)
    ∧ posVal (throughPair 4 ([0, 2, 0, 0], true) ([0, 2, 0, 0], true)).2 = 4 := by
  decide +kernel

private def span3 : List SVec := fusedSpanT (tabL 3) (endBlocks 3 [(th 3, true), (th 3, false)])
private def span2 : List SVec := fusedSpanT (tabL 2) (endBlocks 2 [(th 2, true), (th 2, true)])
private def tp3 : SVec := (throughPair 3 (th 3, true) (th 3, false)).1
private def tp2 : SVec := (throughPair 2 (th 2, true) (th 2, true)).1
private def prTh3 : SVec × Pos := projectT (tabL 3) span3 tp3
private def prTh2 : SVec × Pos := projectT (tabL 2) span2 tp2

example : (dot3 prTh3.1 prTh3.1).oneValue
    (BPair.ofNat (8 * posVal prTh3.2 * posVal prTh3.2)) := by decide +kernel
example : (dotT (tabL 2) true prTh2.1 prTh2.1).oneValue
    (BPair.ofNat (3 * posVal prTh2.2 * posVal prTh2.2)) := by decide +kernel
example : posVal prTh3.2 = 12
    ∧ span3.all (fun u =>
        decide ((dot3 u prTh3.1).oneValue
          (dot3 u tp3 * BPair.ofNat (posVal prTh3.2)))) = true := by decide +kernel

/-! The fused span's groups at the ends' weight lists, the adjoint
against its dual over three letters at seven groups with the unit
weight's four, and the projection group by group the one solve's
own read: the same coevaluation at the count eight, its clearing
reduced to three. -/

private def groups3 : List (List SVec) :=
  fusedGroupsT (tabL 3) (endBlocks 3 [(th 3, true), (th 3, false)])
private def prG3 : SVec × Pos := projectGroupsT (tabL 3) groups3 tp3

example : groups3.map (fun g => g.length) = [1, 1, 1, 4, 1, 1, 1]
    ∧ posVal prG3.2 = 3
    ∧ (dot3 prG3.1 prG3.1).oneValue (BPair.ofNat (8 * 3 * 3))
    ∧ (dot3 prG3.1 prTh3.1).oneValue (BPair.ofNat (8 * 3 * 12)) := by decide +kernel

/-! The grouped solve is the whole span's solve at its reduced
representative, vector and clearing, at the adjoint against its
dual over three letters, the star over two and the fundamental pair
over three; the negated target projects to the negated vector at
the clearing, at either solve, and a scaled target to the scaled
vector at the reduced clearing; and the groups are pairwise
orthogonal at five vertices with every block member and through
pairing at one weight. -/

private def tpF : SVec := (throughPair 3 (fd 3, true) (fd 3, false)).1
private def spanF : List SVec := fusedSpanT (tabL 3) (endBlocks 3 [(fd 3, true), (fd 3, false)])
private def groupsF : List (List SVec) :=
  fusedGroupsT (tabL 3) (endBlocks 3 [(fd 3, true), (fd 3, false)])
private def groups2 : List (List SVec) :=
  fusedGroupsT (tabL 2) (endBlocks 2 [(th 2, true), (th 2, true)])
private def prN3 : SVec × Pos :=
  projectGroupsT (tabL 3) groups3 (scaleV (BPair.ofNat 1).swap tp3)
private def prNW : SVec × Pos := projectT (tabL 3) span3 (scaleV (BPair.ofNat 1).swap tp3)
private def pr5 : SVec × Pos := projectGroupsT (tabL 3) groups3 (scaleV (BPair.ofNat 5) tp3)

example : reduceV prTh3 = prG3
    ∧ reduceV (projectT (tabL 2) span2 tp2) = projectGroupsT (tabL 2) groups2 tp2
    ∧ reduceV (projectT (tabL 3) spanF tpF) = projectGroupsT (tabL 3) groupsF tpF
    ∧ prN3.2 = prG3.2 ∧ addV prN3.1 prG3.1 = []
    ∧ prNW.2 = prTh3.2 ∧ addV prNW.1 prTh3.1 = []
    ∧ pr5.2 = prG3.2
    ∧ addV pr5.1 (scaleV (BPair.ofNat 5).swap prG3.1) = [] := by
  decide +kernel

/-- Every cross-group pairing the sum's unit. -/
private def groupsOrth (d : Nat) (gs : List (List SVec)) : Bool :=
  (List.range gs.length).all (fun i => (List.range gs.length).all (fun j =>
    i == j || (getAt [] gs i).all (fun u => (getAt [] gs j).all (fun v =>
      decide ((dotT (tabL d) true u v).oneValue BPair.unit)))))

/-- Every occupied monomial's weight the vector's. -/
private def homog (d : Nat) (sig : List Bool) (v : SVec) : Bool :=
  v.all (fun p => weightT (tabL d) sig p.1 == weightV (tabL d) sig v)

example : groupsOrth 3 groups3 = true
    ∧ groupsOrth 2 groups2 = true
    ∧ groupsOrth 3 groupsF = true
    ∧ groupsOrth 2 (fusedGroupsT (tabL 2)
        (endBlocks 2 [(th 2, true), (th 2, true), (th 2, false)])) = true
    ∧ groupsOrth 2 (fusedGroupsT (tabL 2)
        (endBlocks 2 [(fd 2, true), (fd 2, true), (fd 2, true), (fd 2, true)])) = true := by
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

private def forgedSplit : List (List SVec) :=
  groups3.flatMap (fun g => if g.length == 4 then [g.take 2, g.drop 2] else [g])

private def pairKey (d : Nat) (sig : List Bool) (v : SVec) : List Nat × List Nat :=
  match v.head? with
  | none => ([], [])
  | some p => (content d ((upSlots sig).map (fun s => getAt 0 p.1 s)),
      content d ((downSlots sig).map (fun s => getAt 0 p.1 s)))

private def forgedPair : List (List SVec) :=
  let es := [(th 3, true), (th 3, false)]
  let keyed := span3.map (fun g => (g, pairKey 3 (vertexSig 3 es) g))
  (ground.dedupF (keyed.map Prod.snd)).map (fun key =>
    (keyed.filter (fun t => t.2 == key)).map Prod.fst)

private def prS : SVec × Pos := projectGroupsT (tabL 3) forgedSplit tp3
private def prP : SVec × Pos := projectGroupsT (tabL 3) forgedPair tp3

example : forgedSplit.map (fun g => g.length) = [1, 1, 1, 2, 2, 1, 1, 1]
    ∧ forgedPair.map (fun g => g.length) = [2, 2, 4, 1, 1]
    ∧ ¬ (dot3 prS.1 prS.1).oneValue (BPair.ofNat (8 * posVal prS.2 * posVal prS.2))
    ∧ ¬ (dot3 prP.1 prP.1).oneValue
        (BPair.ofNat (8 * posVal prP.2 * posVal prP.2)) := by decide +kernel

/-! The paired tensor and the through pairing at a table: the
letters' identity at two slot pairs reads the four monomials of
the two-letter wiring at the clearing one, and the span membership
at the letters reads the projection inside the span and refuses the
target off it. -/

example : (throughT (tabL 2) [(0, 2), (1, 3)] 4).1
      = [([0, 0, 0, 0], BPair.ofNat 1), ([0, 1, 0, 1], BPair.ofNat 1),
         ([1, 0, 1, 0], BPair.ofNat 1), ([1, 1, 1, 1], BPair.ofNat 1)]
    ∧ (throughT (tabL 2) [(0, 2), (1, 3)] 4).2 = Pos.one
    ∧ dualThroughT (tabL 2) [(0, 1)] 2 = none
    ∧ spanMemberT (tabL 3) span3 prTh3.1 = true
    ∧ spanMemberT (tabL 3) span3 tp3 = false := by decide +kernel
