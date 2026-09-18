import MassGap.Slotpower
import MassGap.Adjchar
import MassGap.Mixedinv
/-!
The check module for `con:slotpower`: the batteries re-read the
presentation carrier by kernel `decide` at the label calculus —
the word pairs at the fundamental and the adjoint across the counts
two to four with the tie at the count two and at the self-dual
middle column, the slot signatures at both orientations, the dual
wedge's content and side reads, the block's top at the sum's unit
under every raising at its signature against the standard wedge at the
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
flat forms, the pairing at the sorted walk one value with the fold
at the unit weight and at a stated weight against the applied
vector, the weight applied to a vector at a diagonal and at a
swapping weight, and the through pairing's projection at the block's
count at the wiring and at the star, the star's raw self-pairing
at the factorial's multiple of the count, the projection's
soundness at every pool member, the fused span's groups at the
ends' weight lists with the projection group by group one value
with the whole span's and its refusals at a forged grouping, the
cycle-count Gram one value with the wiring tensors' pairings, and
the tensor at the target's enumeration one value with the
scattered fold and parting at unequal letter counts. -/

namespace slotpower
set_option maxHeartbeats 4000000

open ground places

private def th (d : Nat) : Shape := adjchar.theta d
private def fd (d : Nat) : Shape := ground.bumpAt 0 (labels.unitL d)
private def fdb (d : Nat) : Shape := labels.dualL (fd d)
private def tabL (d : Nat) : memtable.Table := memtable.lettersT d

theorem pin1 : wordPair 2 (th 2) = (2, 0) ∧ wordPair 3 (th 3) = (1, 1)
    ∧ wordPair 4 (th 4) = (1, 1) ∧ wordPair 4 (fd 4) = (1, 0)
    ∧ wordPair 4 [0, 1, 0, 0] = (2, 0) ∧ wordPair 4 [2, 0, 2, 0] = (2, 2)
    ∧ wordPair 3 (fdb 3) = (0, 1) := by decide +kernel

theorem pin2 : labelSig 3 (th 3) = [false, true]
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

theorem pin3 : blockcount.tensorS (blockcount.wedge 4 2) (blockcount.wedge 4 2)
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
theorem pin4 : blockcount.tensorS v1 tall ≠ blockcount.tensorH v1 tall := by
  decide +kernel

/-! The sparse tensor is the dense tensor's occupied family: at two
wedges over four letters and at a wedge against the dual wedge
over three, `tensorV` at the exhibits' occupied monomials one value
with `blockcount.tensorS`'s. -/

theorem pin5 : oneValueV (tensorV (ofH (blockcount.wedge 4 2)) (ofH (blockcount.wedge 4 2)))
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

theorem pin6 : weightAt [2, 0, 1] [1, 1, 0]
      = [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.ofNat 1]
    ∧ unitWeightAt [BPair.ofNat 2, ⟨3, 1⟩, ⟨5, 3⟩] = true
    ∧ unitWeightAt [BPair.ofNat 2, ⟨3, 1⟩, ⟨5, 4⟩] = false
    ∧ unitWeightAt [] = true
    ∧ (collect 2 [([1, 0], BPair.ofNat 1), ([0, 1], BPair.ofNat 1), ([1, 0], BPair.ofNat 1)]
        rfl).val
      = [([0, 1], BPair.ofNat 1), ([1, 0], BPair.ofNat 2)]
    ∧ (collect 1 [([0], ⟨4, 4⟩), ([1], ⟨5, 3⟩)] rfl).val = [([1], BPair.ofNat 2)]
    ∧ (reduceV (collect 2 [([1, 0], ⟨1, 7⟩), ([0, 1], ⟨5, 1⟩)] rfl, (4 : Pos))).1.val
      = [([0, 1], ⟨3, 1⟩), ([1, 0], ⟨1, 4⟩)]
    ∧ (reduceV (collect 2 [([1, 0], ⟨1, 7⟩), ([0, 1], ⟨5, 1⟩)] rfl, (4 : Pos))).2 = (2 : Pos)
    ∧ (reduceV (collect 2 [([1, 0], ⟨3, 9⟩)] rfl, (9 : Pos))).1.val = [([1, 0], ⟨1, 3⟩)]
    ∧ (reduceV (collect 2 [([1, 0], ⟨3, 9⟩)] rfl, (9 : Pos))).2 = (3 : Pos)
    ∧ (reduceV (emptyV 2, (6 : Pos))).1.val = []
    ∧ (reduceV (emptyV 2, (6 : Pos))).2 = (1 : Pos)
    ∧ prim (scaleV (BPair.ofNat 5) (ofH (blockTop 3 (th 3))))
      = prim (ofH (blockTop 3 (th 3))) := by
  decide +kernel

/-! The dual wedge at the complement's length sits on the last
letters, each arrangement on its permutation's side; the block's
top reads the sum's unit under every raising at the label's
signature, and the
standard wedge at the daggered slot in its place survives one. -/

theorem pin7 : (dualWedge 3 2).content = [0, 1, 1]
    ∧ (dualWedge 3 2).coords = [BPair.ofNat 1, (BPair.ofNat 1).swap] := by
  decide +kernel

private def topRead (d : Nat) (s : Shape) : Bool :=
  if h : sumNat (blockTop d s).content = (labelSig d s).length then
    raisedUnit (tabL d) (labelSig d s) (castV h (ofH (blockTop d s)))
  else false

private def wrongTop (d : Nat) (s : Shape) : blockcount.HVec :=
  (botCols d s).foldl (fun acc l => blockcount.tensorH acc (blockcount.wedge d (d - l)))
    ((topCols d s).foldl (fun acc l => blockcount.tensorH acc (blockcount.wedge d l))
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩)

theorem pin8 : topRead 3 (th 3) = true ∧ topRead 3 (fdb 3) = true
    ∧ topRead 4 (th 4) = true
    ∧ (List.range 2).all (fun i =>
        (raiseT (tabL 3) (labelSig 3 (th 3)) i
          (castV (by decide) (ofH (wrongTop 3 (th 3))))).val == []) = false := by
  decide +kernel

/-! The blocks' spans at the word pairs read the blocks' counts:
the adjoint three at two letters, eight at three and fifteen at
four, the fundamental and its dual three at three letters, and the
self-dual middle column six at four; the closure at the standard
action on the daggered slot reads three against the adjoint's
eight; and the block's raising kernel over its span is one line. -/

theorem pin9 : (blockSpanAt 2 (th 2)).length = 3
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

theorem pin10 : blockSpanAt 3 (th 3)
    = closeT (tabL 3) (labelSig 3 (th 3))
        ((labelSig 3 (th 3)).length * (tabL 3).keys + 1)
        (tryAddT (tabL 3) (labelSig 3 (th 3)) [] (ofH (blockTop 3 (th 3))))
        [ofH (blockTop 3 (th 3))] := by decide +kernel

private def asymL : memtable.Table :=
  { tabL 3 with wt := [(0, 0, BPair.ofNat 1), (1, 1, BPair.ofNat 1),
      (2, 2, BPair.ofNat 1), (0, 1, BPair.ofNat 1)] }
private def asymTop : SVec 2 := collect 2 [([1, 0], BPair.ofNat 1), ([2, 2], BPair.ofNat 1)] rfl

theorem pin11 : ¬ memtable.symmWt asymL
    ∧ ¬ (blockSpanT asymL [false, true] asymTop
        = closeT asymL [false, true] ([false, true].length * asymL.keys + 1)
            (tryAddT asymL [false, true] [] asymTop) [asymTop]) := by
  decide +kernel

private def bTop : SVec 1 := collect 1 [([0], BPair.ofNat 1)] rfl

theorem pin12 : memtable.symmWt (memtable.definingB 2)
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
private def isoTop : SVec 1 := collect 1 [([0], BPair.ofNat 1)] rfl

theorem pin13 : memtable.symmWt isoL
    ∧ elim.joinIndep (fun u v => (dotT isoL (unitWtRead isoL) u v).norm) []
        isoTop = false
    ∧ blockSpanT isoL [false] isoTop
      = closeT isoL [false] ([false].length * isoL.keys + 1)
          (tryAddT isoL [false] [] isoTop) [isoTop]
    ∧ ¬ (blockSpanT isoL [false] isoTop
        = closeT isoL [false] ([false].length * isoL.keys + 1)
            [isoTop] [isoTop]) := by decide +kernel

/-! The block's weight grades at the stored descents
(`blockGroupsT`, `blockGroupsAt`, `blockGroupsW`; `lem:lowerspan`'s
collection at `def:elim`'s grown descent): the adjoint over two
letters at three grades of one member and over three letters at
seven with the unit weight's grade of two, each grade's members the
span's members at the grade's weight, its Gram the members' `gramT`,
its determinant the Gram's, and every leading minor off the unit,
decided and read through `blockGroupsT_reads` at the letters'
symmetric weight; the grades' count the distinct weights'
(`blockGroupsT_length`); the weight places at the grades' members
(`weightPlaces`, `weightPlaces_read`); and a stated list's grades at
its collection (`listGroupsT`, `listGroupsT_reads`), a list of two
members at distinct weights two grades of one. -/

private def gG2 := blockGroupsAt 2 (th 2)
private def gG3 := blockGroupsAt 3 (th 3)
private def gS2 := blockSpanAt 2 (th 2)
private def gS3 := blockSpanAt 3 (th 3)
private def wA : SVec 1 := addV (monV 1 [0] rfl) (monV 1 [1] rfl)
private def wB : SVec 1 := monV 1 [1] rfl
private def top3 : SVec (labelSig 3 (th 3)).length := castV (by decide) (ofH (blockTop 3 (th 3)))

theorem pin40 : gG2.map (fun g => g.mems.length) = [1, 1, 1]
    ∧ gG3.map (fun g => g.mems.length) = [1, 1, 1, 2, 1, 1, 1]
    ∧ (∀ i : Nat, i < 7 →
        (getAt (elim.vacantG _) gG3 i).mems
          = gS3.filter (fun v => weightV (tabL 3) (labelSig 3 (th 3)) v
              == getAt [] (dedupF (gS3.map (weightV (tabL 3) (labelSig 3 (th 3))))) i))
    ∧ (∀ i : Nat, i < 7 →
        (getAt (elim.vacantG _) gG3 i).gram = gramT (tabL 3) (getAt (elim.vacantG _) gG3 i).mems)
    ∧ (∀ i : Nat, i < 7 →
        ((getAt (elim.vacantG _) gG3 i).det).oneValue
          (elim.detL (getAt (elim.vacantG _) gG3 i).gram))
    ∧ (∀ i : Nat, i < 7 → ∀ k : Nat, k < (getAt (elim.vacantG _) gG3 i).mems.length →
        ¬ (elim.leadMinor (getAt (elim.vacantG _) gG3 i).gram (k + 1)).oneValue BPair.unit)
    ∧ (∀ i : Nat, i < 7 → elim.traceOf (getAt (elim.vacantG _) gG3 i).st
        (getAt (elim.vacantG _) gG3 i).gram)
    ∧ (∀ i : Nat, i < 3 →
        (getAt (elim.vacantG _) gG2 i).mems
          = gS2.filter (fun v => weightV (tabL 2) (labelSig 2 (th 2)) v
              == getAt [] (dedupF (gS2.map (weightV (tabL 2) (labelSig 2 (th 2))))) i))
    ∧ weightPlaces (tabL 3) (labelSig 3 (th 3)) gS3 = [[0], [1], [2], [3, 4], [5], [6], [7]]
    ∧ (∀ i : Nat, i < 7 →
        (getAt (elim.vacantG _) gG3 i).mems
          = (getAt [] (weightPlaces (tabL 3) (labelSig 3 (th 3)) gS3) i).map (getAt (emptyV _) gS3))
    ∧ (listGroupsT (tabL 2) [false] [wA, wB]).map (fun g => g.mems) = [[wA], [wB]]
    ∧ (listGroupsT (tabL 2) [false] [wA, wB]).map (fun g => g.gram)
      = [gramT (tabL 2) [wA], gramT (tabL 2) [wB]] := by decide +kernel
theorem pin41 : ((getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).mems
      = (blockSpanT (tabL 3) (labelSig 3 (th 3)) top3).filter
          (fun v => weightV (tabL 3) (labelSig 3 (th 3)) v
            == getAt [] (dedupF ((blockSpanT (tabL 3) (labelSig 3 (th 3)) top3).map
                  (weightV (tabL 3) (labelSig 3 (th 3))))) 3)
    ∧ (getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).gram
      = gramT (tabL 3) (getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).mems
    ∧ ((getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).det).oneValue
      (elim.detL (getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).gram)
    ∧ ∀ k, k < (getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).mems.length →
      ¬ (elim.leadMinor (getAt (elim.vacantG _) (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3) 3).gram
          (k + 1)).oneValue BPair.unit)
    ∧ (blockGroupsT (tabL 3) (labelSig 3 (th 3)) top3).length
      = (dedupF ((blockSpanT (tabL 3) (labelSig 3 (th 3)) top3).map
          (weightV (tabL 3) (labelSig 3 (th 3))))).length
    ∧ (blockSpanT (tabL 3) (labelSig 3 (th 3)) top3).filter
          (fun v => weightV (tabL 3) (labelSig 3 (th 3)) v
            == getAt [] (dedupF ((blockSpanT (tabL 3) (labelSig 3 (th 3)) top3).map
                  (weightV (tabL 3) (labelSig 3 (th 3))))) 3)
      = (getAt [] (weightPlaces (tabL 3) (labelSig 3 (th 3))
          (blockSpanT (tabL 3) (labelSig 3 (th 3)) top3)) 3).map
          (getAt (emptyV _) (blockSpanT (tabL 3) (labelSig 3 (th 3)) top3))
    ∧ (getAt (elim.vacantG _) (listGroupsT (tabL 2) [false] [wA, wB]) 1).gram
      = gramT (tabL 2) (getAt (elim.vacantG _) (listGroupsT (tabL 2) [false] [wA, wB]) 1).mems :=
  ⟨blockGroupsT_reads (tabL 3) (labelSig 3 (th 3)) top3 (memtable.lettersT_symm 3) 3
      (by decide +kernel),
   blockGroupsT_length (tabL 3) (labelSig 3 (th 3)) top3 (memtable.lettersT_symm 3),
   weightPlaces_read (tabL 3) (labelSig 3 (th 3)) _ 3 (by decide +kernel),
   (listGroupsT_reads (tabL 2) [false] [wA, wB] (memtable.lettersT_symm 2) 1
      (by decide +kernel)).2.1⟩

/-- The lowering at the standard action on every slot, the dual
action withdrawn. -/
private theorem lowerStd_widths (d : Nat) (sig : List Bool) (i : Nat) (v : SVec sig.length) :
    ((List.range sig.length).flatMap (fun s =>
      (actT (ground.getAt [] (tabL d).lowers i) false s v).val)).all
      (fun p => p.1.length == sig.length) = true := by
  rw [all_flatMap]
  exact all_of_pointwise _ _ (fun s => (actT _ false s v).property.2)

private def lowerStd (d : Nat) (sig : List Bool) (i : Nat) (v : SVec sig.length) :
    SVec sig.length :=
  collect sig.length ((List.range sig.length).flatMap (fun s =>
    (actT (ground.getAt [] (tabL d).lowers i) false s v).val))
    (lowerStd_widths d sig i v)

private def closeStd (d : Nat) (s : Shape) : List (SVec (labelSig d s).length) :=
  let sig := labelSig d s
  if h : sumNat (blockTop d s).content = sig.length then
    ground.closeBy (fun v => ((List.range (d - 1)).map (fun i => lowerStd d sig i v)).filter
        (fun w => w.val.length != 0))
      (tryAddT (tabL d) sig) (sig.length * d + 1) [castV h (ofH (blockTop d s))]
      [castV h (ofH (blockTop d s))]
  else []

theorem pin14 : (closeStd 3 (th 3)).length = 3 := by decide +kernel

theorem pin15 : (kernelT (tabL 3) (labelSig 3 (th 3)) (blockSpanAt 3 (th 3))).length = 1
    ∧ (kernelT (tabL 3) (labelSig 3 (fdb 3)) (blockSpanAt 3 (fdb 3))).length = 1
    ∧ (kernelT (tabL 4) (labelSig 4 [0, 1, 1, 0]) (blockSpanAt 4 [0, 1, 1, 0])).length = 1 := by
  decide +kernel

/-! The unit weight: a block's top tensored with its own at the
exchanged signature reads the unit weight, and against a further
member's off it; the fused span of the adjoint against its dual at
three letters holds the weight-matched pairs, ten, every member at
the unit weight. -/

private def unitW (d : Nat) (sig : List Bool) {k : Nat} (v : SVec k) : Bool :=
  (weightV (tabL d) sig v).all (fun x => decide (x.oneValue BPair.unit))

theorem pin16 : unitW 3 [false, true, true, false]
      (tensorV (ofH (blockTop 3 (th 3))) (ofH (blockTop 3 (th 3)))) = true
    ∧ unitW 3 [false, true, true, false]
      (tensorV (ofH (blockTop 3 (th 3)))
        (ground.getAt (emptyV _) (blockSpanAt 3 (th 3)) 1)) = false
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
  decide ((collect (sumNat v.content) ((List.range v.content.length).flatMap (fun s =>
      (actT m false s (ofH v)).val))
      (by
        rw [all_flatMap]
        exact all_of_pointwise _ _ (fun s => (actT m false s (ofH v)).property.2))).val
    = (ofH (blockcount.act i j v)).val)

theorem pin17 : actTie 3 1 0 (blockcount.exhibit [1, 1, 0]) = true
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

theorem pin18 : (wiringG 3 sig2 [0, 1]).val.length = 9
    ∧ ((wiringG 3 sig2 [0, 1]).val.map Prod.fst).all (fun m =>
        getAt 0 m 0 == getAt 0 m 2 && getAt 0 m 1 == getAt 0 m 3) = true
    ∧ ((wiringG 3 sig2 [0, 1]).val.map Prod.snd).all (fun x =>
        decide (x.oneValue (BPair.ofNat 1))) = true := by
  decide +kernel

private def dot3 {k : Nat} (u v : SVec k) : BPair := dotT (tabL 3) true u v

theorem pin19 : (dot3 (wiringG 3 sig2 [0, 1]) (wiringG 3 sig2 [0, 1])).oneValue (BPair.ofNat 9)
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

/-! The pairing at the sorted walk (`dotTS`): one value with the
fold at two vectors by kernel and through `dotTS_read`, the walk
against the second vector at the unit weight and against the
applied second at a stated weight, and the walk's value at the
exchanged vectors one value with the fold's. -/

private def sw1 : SVec 2 :=
  collect 2 [([0, 1], BPair.ofNat 2), ([1, 1], BPair.ofNat 3), ([2, 0], (BPair.ofNat 1).swap)] rfl
private def sw2 : SVec 2 :=
  collect 2 [([1, 1], BPair.ofNat 4), ([1, 2], BPair.ofNat 5), ([2, 0], BPair.ofNat 2)] rfl

theorem pin32 : (dotTS (tabL 3) true sw1 sw2).oneValue (dotT (tabL 3) true sw1 sw2)
    ∧ (dotTS (tabL 3) true sw1 sw2).oneValue (BPair.ofNat 10)
    ∧ dotTS (tabL 3) true sw1 sw2 = mergeDot lexLt (fun a b => a == b) 6 sw1.val sw2.val
    ∧ (dotTS (memtable.definingB 2) false sw1 sw2).oneValue
        (dotT (memtable.definingB 2) false sw1 sw2)
    ∧ (dotTS (memtable.definingB 2) false sw1 sw2).oneValue (BPair.ofNat 40)
    ∧ dotTS (memtable.definingB 2) false sw1 sw2
      = mergeDot lexLt (fun a b => a == b) 6 sw1.val (applyWt (memtable.definingB 2) sw2).val
    ∧ (dotTS (tabL 3) true sw2 sw1).oneValue (dotT (tabL 3) true sw1 sw2) := by decide +kernel
theorem pin33 : (dotTS (tabL 3) true sw1 sw2).oneValue (dotT (tabL 3) true sw1 sw2)
    ∧ (dotTS (memtable.definingB 2) false sw1 sw2).oneValue
        (dotT (memtable.definingB 2) false sw1 sw2) :=
  ⟨dotTS_read (tabL 3) true sw1 sw2, dotTS_read (memtable.definingB 2) false sw1 sw2⟩

/-! The weight applied to a vector (`applyWt`): at the `B₂` defining
table's diagonal weight each coefficient scaled at its keys' entries,
two at the vector keys and one at the null key, at the swapping
weight `isoL` the monomials moved along the swap, and at the
asymmetric weight `asymL` the entry at both orders with the
pairing's exchange refused there; a monomial's pairing at the weight
its coefficient in the applied vector (`monDotT_apply`), the weighted
pairing the unit-weight pairing against the applied vector
(`dotT_apply`), the canonical pairing one value across the two
spellings (`pairT_apply`), and the Gram at the applied vectors the
pairings' Gram (`gramT_eq`), each by kernel and through its theorem;
the unit-weight read of `dotT` refused against the stated weight's
at `isoL`; the map applied at stated slots (`applyAt`) one display
with the slotwise action's fold and with the weight applied at
every key. -/

private def av : SVec 2 := collect 2 [([0, 1], BPair.ofNat 2), ([1, 0], BPair.ofNat 3),
  ([0, 0], BPair.ofNat 5), ([1, 1], BPair.ofNat 7)] rfl
private def au1 : SVec 2 := collect 2 [([0, 1], BPair.ofNat 1)] rfl
private def au2 : SVec 2 := collect 2 [([1, 1], BPair.ofNat 1)] rfl

theorem pin34 : (applyWt (memtable.definingB 2) sw2).val
      = [([1, 1], BPair.ofNat 16), ([1, 2], BPair.ofNat 20), ([2, 0], BPair.ofNat 8)]
    ∧ (applyWt isoL sw2).val
      = [([0, 0], BPair.ofNat 4), ([0, 2], BPair.ofNat 5), ([2, 1], BPair.ofNat 2)]
    ∧ (monDotT isoL false [0, 1] sw2).oneValue (coefAt [0, 1] (applyWt isoL sw2))
    ∧ (monDotT (memtable.definingB 2) false [1, 1] sw2).oneValue (BPair.ofNat 16)
    ∧ (dotT isoL false sw1 sw2).oneValue (dotT isoL true sw1 (applyWt isoL sw2))
    ∧ (dotT isoL false sw1 sw2).oneValue BPair.unit
    ∧ pairT (memtable.definingB 2) false sw1 sw2
      = pairT (memtable.definingB 2) true sw1 (applyWt (memtable.definingB 2) sw2)
    ∧ gramT isoL [sw1, sw2] = elim.gramBy (pairT isoL false) [sw1, sw2]
    ∧ gramT (memtable.definingB 2) [sw1, sw2]
      = elim.gramBy (pairT (memtable.definingB 2) false) [sw1, sw2]
    ∧ ¬ memtable.symmWt asymL
    ∧ (monDotT asymL false [0, 1] av).oneValue (coefAt [0, 1] (applyWt asymL av))
    ∧ (monDotT asymL false [1, 0] av).oneValue (coefAt [1, 0] (applyWt asymL av))
    ∧ (monDotT asymL false [0, 1] av).oneValue (BPair.ofNat 9)
    ∧ (monDotT asymL false [1, 0] av).oneValue (BPair.ofNat 10)
    ∧ (dotT asymL false au1 au2).oneValue (BPair.ofNat 1)
    ∧ (dotT asymL false au2 au1).oneValue BPair.unit
    ∧ gramT asymL [au1, au2, av] = elim.gramBy (pairT asymL false) [au1, au2, av]
    ∧ ¬ elim.symmRead (gramT asymL [au1, au2, av])
    ∧ ¬ (dotT isoL true sw1 sw2).oneValue (dotT isoL false sw1 sw2) := by decide +kernel
theorem pin35 : (monDotT isoL false [0, 1] sw2).oneValue (coefAt [0, 1] (applyWt isoL sw2))
    ∧ (dotT isoL false sw1 sw2).oneValue (dotT isoL true sw1 (applyWt isoL sw2))
    ∧ pairT (memtable.definingB 2) false sw1 sw2
      = pairT (memtable.definingB 2) true sw1 (applyWt (memtable.definingB 2) sw2)
    ∧ gramT (memtable.definingB 2) [sw1, sw2]
      = elim.gramBy (pairT (memtable.definingB 2) false) [sw1, sw2]
    ∧ (monDotT asymL false [1, 0] av).oneValue (coefAt [1, 0] (applyWt asymL av))
    ∧ (dotT asymL false au1 au2).oneValue (dotT asymL true au1 (applyWt asymL au2))
    ∧ pairT asymL false au1 av = pairT asymL true au1 (applyWt asymL av)
    ∧ gramT asymL [au1, au2, av] = elim.gramBy (pairT asymL false) [au1, au2, av] :=
  ⟨monDotT_apply isoL [0, 1] sw2, dotT_apply isoL sw1 sw2,
   pairT_apply (memtable.definingB 2) sw1 sw2, gramT_eq (memtable.definingB 2) [sw1, sw2],
   monDotT_apply asymL [1, 0] av, dotT_apply asymL au1 au2, pairT_apply asymL au1 av,
   gramT_eq asymL [au1, au2, av]⟩

theorem pin36 : (applyAt (memtable.definingB 2).wt [0, 1] sw2).val
      = (applyWt (memtable.definingB 2) sw2).val
    ∧ applyAt isoL.wt [0, 1] sw2 = applyWt isoL sw2
    ∧ applyAt asymL.wt [0, 1] av = applyWt asymL av
    ∧ applyAt asymL.wt [0, 1] av
      = (List.range 2).foldl (fun w s => actT asymL.wt false s w) av
    ∧ applyAt isoL.wt [1] sw2 = (List.range 1).foldl (fun w s => actT isoL.wt false (s + 1) w) sw2
    ∧ (applyAt isoL.wt [1] sw2).val
      = [([1, 0], BPair.ofNat 4), ([1, 2], BPair.ofNat 5), ([2, 1], BPair.ofNat 2)] := by
  decide +kernel

/-! The displays' equality is the one-value walk (`oneValueV`,
`oneValueV_read`), and the merged sum is the collection of the
displays' join (`addV`, `addV_read`), each by kernel and through the
theorem. -/

theorem pin37 : oneValueV sw1 sw1 = true ∧ oneValueV sw1 sw2 = false
    ∧ oneValueV sw1 sw1 = oneValueBy lexLt (fun a b => a == b) sw1.val sw1.val
    ∧ oneValueV sw1 sw2 = oneValueBy lexLt (fun a b => a == b) sw1.val sw2.val
    ∧ oneValueV (collect 1 [([0], BPair.ofNat 2)] rfl) (collect 1 [([0], ⟨5, 3⟩)] rfl) = true
    ∧ (addV sw1 sw2).val
      = [([0, 1], BPair.ofNat 2), ([1, 1], BPair.ofNat 7), ([1, 2], BPair.ofNat 5),
         ([2, 0], BPair.ofNat 1)]
    ∧ (addV sw1 sw2).val = collectBy lexLt (fun a b => a == b) (sw1.val ++ sw2.val)
    ∧ (addV sw1 (scaleV (BPair.ofNat 1).swap sw1)).val = [] := by decide +kernel
theorem pin38 : oneValueV sw1 sw2 = oneValueBy lexLt (fun a b => a == b) sw1.val sw2.val
    ∧ (addV sw1 sw2).val = collectBy lexLt (fun a b => a == b) (sw1.val ++ sw2.val) :=
  ⟨oneValueV_read sw1 sw2, addV_read sw1 sw2⟩

/-! The star's family at the withdrawn content's arrangements
against the permutations opening at the arrangement
(`starFam_perms`), decided over four letters at a two-letter and a
one-letter arrangement, vacant at a repeated letter, and through
the theorem. -/

theorem pin20 : starFam 4 [1, 0]
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
theorem pin21 : starFam 4 [1, 0]
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

theorem pin22 : (throughPair 3 (th 3, true) (th 3, false)).2 = Pos.one
    ∧ (dot3 (throughPair 3 (th 3, true) (th 3, false)).1
        (throughPair 3 (th 3, true) (th 3, false)).1).oneValue (BPair.ofNat 9)
    ∧ (throughPair 3 (fd 3, true) (fd 3, true)).1.val = []
    ∧ posVal (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).2 = 2
    ∧ (dotT (tabL 4) true (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1
        (throughPair 4 ([0, 1, 0, 0], true) ([0, 1, 0, 0], true)).1).oneValue
        (BPair.ofNat 24)
    ∧ posVal (throughPair 4 ([0, 2, 0, 0], true) ([0, 2, 0, 0], true)).2 = 4 := by
  decide +kernel

private def span3 := fusedSpanT (tabL 3) (endBlocks 3 [(th 3, true), (th 3, false)])
private def span2 := fusedSpanT (tabL 2) (endBlocks 2 [(th 2, true), (th 2, true)])
private def tp3 := castV (twoEnds_len 3 (th 3, true) (th 3, false))
  (throughPair 3 (th 3, true) (th 3, false)).1
private def tp2 := castV (twoEnds_len 2 (th 2, true) (th 2, true))
  (throughPair 2 (th 2, true) (th 2, true)).1
private def prTh3 := projectT (tabL 3) span3 tp3
private def prTh2 := projectT (tabL 2) span2 tp2

theorem pin23 : (dot3 prTh3.1 prTh3.1).oneValue
    (BPair.ofNat (8 * posVal prTh3.2 * posVal prTh3.2)) := by decide +kernel
theorem pin24 : (dotT (tabL 2) true prTh2.1 prTh2.1).oneValue
    (BPair.ofNat (3 * posVal prTh2.2 * posVal prTh2.2)) := by decide +kernel
theorem pin25 : posVal prTh3.2 = 12
    ∧ span3.all (fun u =>
        decide ((dot3 u prTh3.1).oneValue
          (dot3 u tp3 * BPair.ofNat (posVal prTh3.2)))) = true := by decide +kernel

/-! The fused span's groups at the ends' weight lists, the adjoint
against its dual over three letters at seven groups with the unit
weight's four, and the projection group by group the one solve's
own read: the same coevaluation at the count eight, its clearing
reduced to three. -/

private def groups3 := fusedGroupsT (tabL 3) (endBlocks 3 [(th 3, true), (th 3, false)])
private def prG3 := projectGroupsT (tabL 3) groups3 tp3

theorem pin26 : groups3.map (fun g => g.length) = [1, 1, 1, 4, 1, 1, 1]
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

private def tpF := castV (twoEnds_len 3 (fd 3, true) (fd 3, false))
  (throughPair 3 (fd 3, true) (fd 3, false)).1
private def spanF := fusedSpanT (tabL 3) (endBlocks 3 [(fd 3, true), (fd 3, false)])
private def groupsF := fusedGroupsT (tabL 3) (endBlocks 3 [(fd 3, true), (fd 3, false)])
private def groups2 := fusedGroupsT (tabL 2) (endBlocks 2 [(th 2, true), (th 2, true)])
private def prN3 := projectGroupsT (tabL 3) groups3 (scaleV (BPair.ofNat 1).swap tp3)
private def prNW := projectT (tabL 3) span3 (scaleV (BPair.ofNat 1).swap tp3)
private def pr5 := projectGroupsT (tabL 3) groups3 (scaleV (BPair.ofNat 5) tp3)

theorem pin27 : reduceV prTh3 = prG3
    ∧ reduceV (projectT (tabL 2) span2 tp2) = projectGroupsT (tabL 2) groups2 tp2
    ∧ reduceV (projectT (tabL 3) spanF tpF) = projectGroupsT (tabL 3) groupsF tpF
    ∧ prN3.2 = prG3.2 ∧ (addV prN3.1 prG3.1).val = []
    ∧ prNW.2 = prTh3.2 ∧ (addV prNW.1 prTh3.1).val = []
    ∧ pr5.2 = prG3.2
    ∧ (addV pr5.1 (scaleV (BPair.ofNat 5).swap prG3.1)).val = [] := by
  decide +kernel

/-- Every cross-group pairing the sum's unit. -/
private def groupsOrth (d : Nat) {k : Nat} (gs : List (List (SVec k))) : Bool :=
  (List.range gs.length).all (fun i => (List.range gs.length).all (fun j =>
    i == j || (getAt [] gs i).all (fun u => (getAt [] gs j).all (fun v =>
      decide ((dotT (tabL d) true u v).oneValue BPair.unit)))))

/-- Every occupied monomial's weight the vector's. -/
private def homog (d : Nat) (sig : List Bool) {k : Nat} (v : SVec k) : Bool :=
  decide (homogRead (tabL d) sig v (weightV (tabL d) sig v))

theorem pin28 : groupsOrth 3 groups3 = true
    ∧ groupsOrth 2 groups2 = true
    ∧ groupsOrth 3 groupsF = true
    ∧ groupsOrth 2 (fusedGroupsT (tabL 2)
        (endBlocks 2 [(th 2, true), (th 2, true), (th 2, false)])) = true
    ∧ groupsOrth 2 (fusedGroupsT (tabL 2)
        (endBlocks 2 [(fd 2, true), (fd 2, true), (fd 2, true), (fd 2, true)])) = true := by
  decide +kernel
theorem pin29 : (blockSpanAt 3 (th 3)).all (homog 3 (labelSig 3 (th 3))) = true
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

private def forgedSplit :=
  groups3.flatMap (fun g => if g.length == 4 then [g.take 2, g.drop 2] else [g])

private def pairKey (d : Nat) (sig : List Bool) {k : Nat} (v : SVec k) : List Nat × List Nat :=
  match v.val.head? with
  | none => ([], [])
  | some p => (content d ((upSlots sig).map (fun s => getAt 0 p.1 s)),
      content d ((downSlots sig).map (fun s => getAt 0 p.1 s)))

private def forgedPair :=
  let es := [(th 3, true), (th 3, false)]
  let keyed := span3.map (fun g => (g, pairKey 3 (vertexSig 3 es) g))
  (ground.dedupF (keyed.map Prod.snd)).map (fun key =>
    (keyed.filter (fun t => t.2 == key)).map Prod.fst)

private def prS := projectGroupsT (tabL 3) forgedSplit tp3
private def prP := projectGroupsT (tabL 3) forgedPair tp3

theorem pin30 : forgedSplit.map (fun g => g.length) = [1, 1, 1, 2, 2, 1, 1, 1]
    ∧ forgedPair.map (fun g => g.length) = [2, 2, 4, 1, 1]
    ∧ ¬ (dot3 prS.1 prS.1).oneValue (BPair.ofNat (8 * posVal prS.2 * posVal prS.2))
    ∧ ¬ (dot3 prP.1 prP.1).oneValue
        (BPair.ofNat (8 * posVal prP.2 * posVal prP.2)) := by decide +kernel

/-! The paired tensor and the through pairing at a table: the
letters' identity at two slot pairs reads the four monomials of
the two-letter wiring at the clearing one, and the span membership
at the letters reads the projection inside the span and refuses the
target off it. -/

theorem pin31 : (throughT (tabL 2) [(0, 2), (1, 3)] 4).1.val
      = [([0, 0, 0, 0], BPair.ofNat 1), ([0, 1, 0, 1], BPair.ofNat 1),
         ([1, 0, 1, 0], BPair.ofNat 1), ([1, 1, 1, 1], BPair.ofNat 1)]
    ∧ (throughT (tabL 2) [(0, 2), (1, 3)] 4).2 = Pos.one
    ∧ dualThroughT (tabL 2) [(0, 1)] 2 = none
    ∧ spanMemberT (tabL 3) span3 prTh3.1 = true
    ∧ spanMemberT (tabL 3) span3 tp3 = false := by decide +kernel

/-! The counted reads: two vectors with their counts are one value
at one count and one display alone, the vacant displays parting at
distinct counts; a vector off the pool's power is refused at the
span membership and read vacant at the solve, the pool's own member
passing at the solve's read; and the vectors at stated monomials
read their monomials at the coefficient one. -/

theorem pin39 : oneValueW ⟨2, sw1⟩ ⟨2, sw1⟩ = true
    ∧ oneValueW ⟨_, sw1⟩ ⟨_, sw2⟩ = false
    ∧ oneValueW ⟨_, emptyV 2⟩ ⟨_, emptyV 3⟩ = false
    ∧ spanMemberW (tabL 3) span3 ⟨_, prTh3.1⟩ = true
    ∧ spanMemberW (tabL 3) span3 ⟨_, sw1⟩ = false
    ∧ spanCoeffsW (tabL 3) span3 ⟨_, sw1⟩ = ([], Pos.one)
    ∧ spanCoeffsW (tabL 3) span3 ⟨_, prTh3.1⟩ = spanCoeffsT (tabL 3) span3 prTh3.1
    ∧ (monV 2 [0, 1] rfl).val = [([0, 1], BPair.ofNat 1)]
    ∧ (monsV 2 (allMon 2 2) (allMon_widths 2 2)).map (fun v => v.val.map Prod.fst)
      = [[[0, 0]], [[0, 1]], [[1, 0]], [[1, 1]]] := by decide +kernel

/-- The coefficient read splits at the first factor's slot
count, at arbitrary vectors and monomials. -/
theorem pin42 {k l : Nat} (u : SVec k) (v : SVec l) (m n : List Nat) (hm : m.length = k) :
    (coefAt (m ++ n) (tensorV u v)).oneValue (coefAt m u * coefAt n v) :=
  coefAt_tensorV u v m n hm

theorem pin43 {k l : Nat} (u : SVec k) (v : SVec l) (hu : u.val ≠ []) (hv : v.val ≠ []) :
    (tensorV u v).val ≠ [] := tensorV_occupied u v hu hv

private def topG2 : SVec 1 := monV 1 [0] rfl

private theorem topG2_keys : keysRead memtable.genG2.keys topG2 := by decide +kernel
private theorem topG2_weight : homogRead memtable.genG2 [false] topG2 [BPair.ofNat 1, BPair.unit] := by
  decide +kernel

theorem pin44 : homogRead memtable.genG2 [false, false] (tensorV topG2 topG2)
    [BPair.ofNat 2, BPair.unit] :=
  homogRead_tensorV memtable.genG2 [false] [false] topG2 topG2 _ _ rfl rfl
    memtable.genG2_diagonals.1 memtable.genG2_diagonals.2 topG2_keys topG2_keys topG2_weight topG2_weight

theorem pin45 : homogRead memtable.genG2 [false] (lowerT memtable.genG2 [false] 0 topG2)
    [(BPair.ofNat 1).swap, BPair.ofNat 1] :=
  homogRead_lowerT_G2 [false] 0 (by decide +kernel) topG2 _ topG2_keys topG2_weight

theorem pin46 : (lowerT memtable.genG2 [false] 0 topG2).val ≠ []
    ∧ (lowerT memtable.genG2 [false] 1 topG2).val = [] := by decide +kernel

theorem pin47 (sig : List Bool) (top : SVec sig.length) (hk : keysRead memtable.genG2.keys top) :
    ∀ v ∈ blockSpanT memtable.genG2 sig top, (weightV memtable.genG2 sig v).length = 2 :=
  blockSpanT_weight_length_G2 sig top hk

/-- Homogeneity at a vacant vector does not identify its
selected weight, and tensor occupancy needs both factors. -/
theorem pin48 : homogRead memtable.genG2 [false] (emptyV 1) [BPair.ofNat 9, BPair.unit]
    ∧ weightV memtable.genG2 [false] (emptyV 1) ≠ [BPair.ofNat 9, BPair.unit]
    ∧ (tensorV (emptyV 1) topG2).val = [] := by decide +kernel

/-- The wrong tensor split reads a different coefficient. -/
theorem pin49 : ¬ (coefAt [0, 0] (tensorV topG2 topG2)).oneValue
    (coefAt [] topG2 * coefAt [0, 0] topG2) := by decide +kernel

theorem pin50 : ¬ keysRead 8 (monV 1 [8] rfl)
    ∧ ¬ homogRead memtable.genG2 [false] (lowerT memtable.genG2 [false] 0 topG2)
      [BPair.ofNat 1, BPair.unit] := by decide +kernel

theorem pin51 (sig : List Bool) (top : SVec sig.length) (ho : top.val ≠ []) :
    top ∈ blockSpanT memtable.genG2 sig top := blockSpanT_top_G2 sig top ho

theorem pin52 (T : memtable.Table) {k : Nat} (v : SVec k) (hv : v.val ≠ []) :
    BPair.unit < pairT T true v v := pairT_self_pos T v hv

theorem pin53 : (pairT memtable.genG2 true (emptyV 1) (emptyV 1)).oneValue BPair.unit := by
  decide +kernel

/-- The sparse action splits at either tensor factor. -/
theorem pin54 (M : memtable.SMap) (neg : Bool) (s : Nat) {k l : Nat}
    (u : SVec k) (v : SVec l) (hs : s < k) :
    actT M neg s (tensorV u v) = tensorV (actT M neg s u) v :=
  actT_tensor_left M neg s u v hs

theorem pin55 (M : memtable.SMap) (neg : Bool) (s : Nat) {k l : Nat}
    (u : SVec k) (v : SVec l) :
    actT M neg (k + s) (tensorV u v) = tensorV u (actT M neg s v) :=
  actT_tensor_right M neg s u v

theorem pin56 (T : memtable.Table) (sig tau : List Bool) (i : Nat)
    (u : SVec sig.length) (v : SVec tau.length) :
    castV (length_append sig tau)
      (raiseT T (sig ++ tau) i (castV (length_append sig tau).symm (tensorV u v)))
      = addV (tensorV (raiseT T sig i u) v) (tensorV u (raiseT T tau i v)) :=
  raiseT_tensorV T sig tau i u v

theorem pin57 (T : memtable.Table) (sig tau : List Bool) (i : Nat)
    (u : SVec sig.length) (v : SVec tau.length) :
    castV (length_append sig tau)
      (lowerT T (sig ++ tau) i (castV (length_append sig tau).symm (tensorV u v)))
      = addV (tensorV (lowerT T sig i u) v) (tensorV u (lowerT T tau i v)) :=
  lowerT_tensorV T sig tau i u v

/-- The first-factor slot condition and both top reads are needed. -/
theorem pin58 :
    actT [(0, 1, BPair.ofNat 1)] false 1
      (tensorV (monV 1 [0] rfl) (monV 1 [1] rfl))
      ≠ tensorV (actT [(0, 1, BPair.ofNat 1)] false 1 (monV 1 [0] rfl)) (monV 1 [1] rfl)
    ∧ raisedUnit (memtable.lettersT 2) [false, false]
      (tensorV (monV 1 [0] rfl) (monV 1 [1] rfl)) = false
    ∧ raisedUnit (memtable.lettersT 2) [false, false]
      (tensorV (monV 1 [1] rfl) (monV 1 [0] rfl)) = false := by decide +kernel

/-- The dual slot contributes the exchanged map's balance partner. -/
theorem pin59 :
    raisedUnit (memtable.lettersT 2) [false, true]
      (tensorV (monV 1 [0] rfl) (monV 1 [1] rfl)) = true
    ∧ (raiseT (memtable.lettersT 2) [false, true] 0
      (tensorV (monV 1 [1] rfl) (monV 1 [0] rfl))).val
      = [([0, 0], BPair.ofNat 1), ([1, 1], (BPair.ofNat 1).swap)] := by decide +kernel

theorem pin60 (T : memtable.Table) (sig : List Bool) (i : Nat)
    (u v : SVec sig.length) :
    lowerT T sig i (addV u v) = addV (lowerT T sig i u) (lowerT T sig i v) :=
  lowerT_addV T sig i u v

theorem pin61 (T : memtable.Table) (sig : List Bool) (i : Nat)
    (v : SVec sig.length) (c : BPair) :
    lowerT T sig i (scaleV c v) = scaleV c (lowerT T sig i v) :=
  lowerT_scaleV T sig i v c

/-- The actual G2 span reads at every further fuel. -/
theorem pin62 (sig : List Bool) (top : SVec sig.length) (extra : Nat)
    (hsig : sig.all (fun b => !b) = true) :
    blockSpanT memtable.genG2 sig top
      = closeT memtable.genG2 sig (sig.length * memtable.genG2.keys + 1 + extra)
        (tryAddT memtable.genG2 sig [] top) [top] :=
  blockSpanT_fuel_G2 sig top extra hsig

/-- The height drops on occupied standard lowerings. The dual
signature reverses the move, and a vacant image has unit height. -/
theorem pin63 :
    heightV memtable.keyHeightsG2 topG2 = 6
    ∧ heightV memtable.keyHeightsG2 (lowerT memtable.genG2 [false] 0 topG2) = 5
    ∧ ¬ heightV memtable.keyHeightsG2
        (lowerT memtable.genG2 [true] 0 (monV 1 [1] rfl))
        < heightV memtable.keyHeightsG2 (monV 1 [1] rfl)
    ∧ ¬ heightV memtable.keyHeightsG2 (lowerT memtable.genG2 [] 0 unitV)
        < heightV memtable.keyHeightsG2 unitV := by decide +kernel

/-- The cap and the drop read refuse forged heights. -/
theorem pin64 :
    heightV [0, 7] (monV 1 [1] rfl) = 7
    ∧ ¬ ([0, 7] : List Nat).all (fun h => decide (h ≤ 6)) = true
    ∧ heightV memtable.keyHeightsG2 (monV 1 [8] rfl) = 0
    ∧ ¬ (getAt [] memtable.genG2.lowers 0).all (fun e =>
      getAt 0 [0, 0, 0, 0, 0, 0, 0, 0] e.1 + 1
        == getAt 0 [0, 0, 0, 0, 0, 0, 0, 0] e.2.1) = true := by decide +kernel

/-- Coordinate equality reads the vector when the list covers its keys. -/
theorem pin65 (ms : List (List Nat)) {k : Nat} (u v : SVec k)
    (hu : ∀ p ∈ u.val, p.1 ∈ ms) (hv : ∀ p ∈ v.val, p.1 ∈ ms)
    (h : poly.oneValue (coordsV ms u) (coordsV ms v)) : u = v := coordsV_injective ms u v hu hv h

/-- A missing monomial can hide either vector's coefficient. -/
theorem pin66 : poly.oneValue (coordsV [] topG2) (coordsV [] (emptyV 1))
    ∧ poly.oneValue (coordsV [] (emptyV 1)) (coordsV [] topG2)
    ∧ topG2 ≠ emptyV 1 := by decide +kernel

/-- A repeated or missing coordinate changes the pairing. -/
theorem pin67 :
    ¬ (elim.dotP (coordsV [[0], [0]] topG2) (coordsV [[0], [0]] topG2)).oneValue
      (pairT memtable.genG2 true topG2 topG2)
    ∧ ¬ (elim.dotP (coordsV [] topG2) (coordsV [] topG2)).oneValue
      (pairT memtable.genG2 true topG2 topG2) := by decide +kernel

/-- Matched coefficients are the elimination combination's coefficients. -/
theorem pin68 (ms : List (List Nat)) {k : Nat} (pool : List (SVec k)) (cs : List BPair) :
    poly.oneValue (coordsV ms (comboV pool cs)) (elim.combo ms.length cs (pool.map (coordsV ms))) :=
  coordsV_comboV ms pool cs

/-- A signed combination keeps its scalar factors and truncates at the
matched list, including a vacant coefficient family. -/
theorem pin69 :
    (coefAt [0] (comboV [topG2, monV 1 [1] rfl] [BPair.ofNat 2, (BPair.ofNat 3).swap])).oneValue
      (BPair.ofNat 2)
    ∧ (coefAt [1] (comboV [topG2, monV 1 [1] rfl] [BPair.ofNat 2, (BPair.ofNat 3).swap])).oneValue
      ((BPair.ofNat 3).swap)
    ∧ comboV [topG2] [] = emptyV 1 := by decide +kernel

/-- Repeated vectors and insufficient coordinate coverage refuse
the coordinate-independence read after a join. -/
theorem pin70 : indepGroupsT memtable.genG2 [false] (allMon 8 1) [topG2, monV 1 [1] rfl]
    ∧ ¬ indepGroupsT memtable.genG2 [false] (allMon 8 1) [topG2, topG2]
    ∧ ¬ indepGroupsT memtable.genG2 [false] (allMon 1 1)
      (tryAddT memtable.genG2 [false] [] (monV 1 [1] rfl))
    ∧ indepGroupsT memtable.genG2 [false] (allMon 1 1) [addV topG2 (monV 1 [1] rfl)]
    ∧ ¬ indepGroupsT memtable.genG2 [false] (allMon 1 1)
      (tryAddT memtable.genG2 [false] [addV topG2 (monV 1 [1] rfl)] topG2) := by decide +kernel

private def vacantWt2 : memtable.Table := { memtable.lettersT 2 with wt := [] }

/-- A degenerate pairing can reject a vector outside the current
coordinate span; the unit pairing is part of the join theorem's frame. -/
theorem pin71 : unitWtRead vacantWt2 = false
    ∧ ¬ elim.spanRel (allMon 2 1).length
      ((tryAddT vacantWt2 [false] [] topG2).map (coordsV (allMon 2 1)))
      (coordsV (allMon 2 1) topG2) := by decide +kernel

/-- The actual G2 block has independent grades and closed listed lowerings. -/
theorem pin72 (sig : List Bool) (top : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top) :
    indepGroupsT memtable.genG2 sig (allMon memtable.genG2.keys sig.length)
      (blockSpanT memtable.genG2 sig top) ∧
      ∀ v ∈ blockSpanT memtable.genG2 sig top, ∀ i, i < memtable.genG2.rank →
        elim.spanRel (allMon memtable.genG2.keys sig.length).length
          ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
          (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i v)) :=
  blockSpanT_reads_G2 sig top hs ht

/-- The closure read extends to every vector in the coordinate span. -/
theorem pin73 (sig : List Bool) (top v : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hv : keysRead memtable.genG2.keys v) (i : Nat) (hi : i < memtable.genG2.rank)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) v)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i v)) :=
  blockSpanT_lower_span_G2 sig top v hs ht hv i hi hspan

/-- Distinct selected weights alone do not imply perpendicularity
when a vector is not homogeneous. -/
theorem pin74 :
    weightV memtable.genG2 [false] (addV topG2 (monV 1 [1] rfl))
      ≠ weightV memtable.genG2 [false] (monV 1 [1] rfl)
    ∧ ¬ homogRead memtable.genG2 [false] (addV topG2 (monV 1 [1] rfl))
      (weightV memtable.genG2 [false] (addV topG2 (monV 1 [1] rfl)))
    ∧ ¬ (pairT memtable.genG2 true (addV topG2 (monV 1 [1] rfl)) (monV 1 [1] rfl)).oneValue
      BPair.unit
    ∧ ¬ (pairT memtable.genG2 true (monV 1 [1] rfl) (addV topG2 (monV 1 [1] rfl))).oneValue
      BPair.unit
    ∧ ¬ (pairT memtable.genG2 true topG2 topG2).oneValue BPair.unit := by decide +kernel

/-- Every stored member has an admissible simple-word witness. -/
theorem pin75 (T : memtable.Table) (sig : List Bool) (top : SVec sig.length)
    (hw : memtable.symmWt T) (v : SVec sig.length) (hv : v ∈ blockSpanT T sig top) :
    ∃ word : List Nat, word.all (fun i => decide (i < T.rank)) = true ∧
      word.foldl (fun v i => lowerT T sig i v) top = v :=
  blockSpanT_words T sig top hw v hv

/-- Admissible words of every length belong to the stored G2 span,
including the vacant word and words at a vacant seed. -/
theorem pin76 (sig : List Bool) (top : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (word : List Nat) (hw : word.all (fun i => decide (i < memtable.genG2.rank)) = true) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length)
        (word.foldl (fun v i => lowerT memtable.genG2 sig i v) top)) :=
  blockSpanT_word_span_G2 sig top hs ht word hw

/-- The actual homogeneous G2 block is independent at its full
coordinate list. -/
theorem pin77 (sig : List Bool) (top : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hh : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top)) :
    elim.indepRows (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length))) :=
  blockSpanT_indep_G2 sig top hs ht hh

/-- The independent block's count is bounded by its coordinates. -/
theorem pin78 (sig : List Bool) (top : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hh : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top)) :
    (blockSpanT memtable.genG2 sig top).length ≤ (allMon memtable.genG2.keys sig.length).length :=
  blockSpanT_length_le_G2 sig top hs ht hh

/-- Raising reads the original coefficients at the image pool. -/
theorem pin79 (T : memtable.Table) (sig : List Bool) (i : Nat)
    (pool : List (SVec sig.length)) (cs : List BPair) :
    raiseT T sig i (comboV pool cs) = comboV (pool.map (raiseT T sig i)) cs :=
  raiseT_comboV T sig i pool cs

/-- Raising preserves the span at its listed-image reads. -/
theorem pin80 (T : memtable.Table) (sig : List Bool) (d i : Nat)
    (pool : List (SVec sig.length)) (v : SVec sig.length)
    (hp : ∀ w ∈ pool, keysRead d w) (hv : keysRead d v)
    (hi : ∀ w ∈ pool, elim.spanRel (allMon d sig.length).length
      (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) (raiseT T sig i w)))
    (hs : elim.spanRel (allMon d sig.length).length
      (pool.map (coordsV (allMon d sig.length))) (coordsV (allMon d sig.length) v)) :
    elim.spanRel (allMon d sig.length).length
      (pool.map (coordsV (allMon d sig.length)))
      (coordsV (allMon d sig.length) (raiseT T sig i v)) :=
  raiseT_span T sig d i pool v hp hv hi hs

/-- Scalar and vacant seeds read the independent line and the
vacant list in the one-coordinate scalar power. -/
theorem pin81 :
    elim.indepRows 1 ((blockSpanT memtable.genG2 [] unitV).map (coordsV (allMon 8 0)))
    ∧ elim.indepRows 1 ((blockSpanT memtable.genG2 [] (emptyV 0)).map (coordsV (allMon 8 0))) := by
  decide +kernel

/-- The simple commutator reads the homogeneous coroot at every
standard slot count and both simple indices. -/
theorem pin82 (sig : List Bool) (v : SVec sig.length) (w : List BPair)
    (hs : sig.all (fun b => !b) = true) (hv : keysRead memtable.genG2.keys v)
    (hh : homogRead memtable.genG2 sig v w) (i j : Nat)
    (hi : i < memtable.genG2.rank) (hj : j < memtable.genG2.rank) :
    raiseT memtable.genG2 sig i (lowerT memtable.genG2 sig j v) =
      addV (lowerT memtable.genG2 sig j (raiseT memtable.genG2 sig i v))
        (scaleV (if i = j then getAt BPair.unit w i else BPair.unit) v) :=
  raiseT_lowerT_G2 sig v w hs hv hh i j hi hj

/-- Raising every admissible word at a top stays in its computed
span, at every word length. -/
theorem pin83 (sig : List Bool) (top : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hh : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top))
    (hr : raisedUnit memtable.genG2 sig top = true)
    (word : List Nat) (hw : word.all (fun j => decide (j < memtable.genG2.rank)) = true)
    (i : Nat) (hi : i < memtable.genG2.rank) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length)
        (raiseT memtable.genG2 sig i (word.foldl (fun v j => lowerT memtable.genG2 sig j v) top))) :=
  raiseT_word_span_G2 sig top hs ht hh hr word hw i hi

/-- Every raising preserves the actual span at its top's reads. -/
theorem pin84 (sig : List Bool) (top v : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hh : homogRead memtable.genG2 sig top (weightV memtable.genG2 sig top))
    (hr : raisedUnit memtable.genG2 sig top = true)
    (hv : keysRead memtable.genG2.keys v) (i : Nat) (hi : i < memtable.genG2.rank)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) v)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) (raiseT memtable.genG2 sig i v)) :=
  blockSpanT_raise_span_G2 sig top v hs ht hh hr hv i hi hspan

/-- The actual single-slot actions read the commutator on every
key, including distinct simple indices and both coroot diagonals. -/
theorem pin85 : ∀ i, i < 2 → ∀ j, j < 2 → ∀ q, q < 8 →
    raiseT memtable.genG2 [false] i (lowerT memtable.genG2 [false] j (monV 1 [q] rfl)) =
      addV (lowerT memtable.genG2 [false] j (raiseT memtable.genG2 [false] i (monV 1 [q] rfl)))
        (scaleV (if i = j then getAt BPair.unit (memtable.keyWeight memtable.genG2 q) i
          else BPair.unit) (monV 1 [q] rfl)) := by decide +kernel

/-- The two-slot commutator reads both factors' coroots. A
nonhomogeneous sum does not read its first key's scalar, and a
lowering seed with an occupied raising need not have raising closure. -/
theorem pin86 :
    raiseT memtable.genG2 [false, false] 0
      (lowerT memtable.genG2 [false, false] 0 (tensorV topG2 topG2))
      = scaleV (BPair.ofNat 2) (tensorV topG2 topG2)
    ∧ raiseT memtable.genG2 [false] 0
      (lowerT memtable.genG2 [false] 0 (addV topG2 (monV 1 [1] rfl)))
      ≠ addV (lowerT memtable.genG2 [false] 0
        (raiseT memtable.genG2 [false] 0 (addV topG2 (monV 1 [1] rfl))))
        (scaleV (BPair.ofNat 1) (addV topG2 (monV 1 [1] rfl)))
    ∧ raisedUnit memtable.genG2 [false] (monV 1 [4] rfl) = false
    ∧ ¬ elim.spanRel (allMon 8 1).length
      ((blockSpanT memtable.genG2 [false] (monV 1 [4] rfl)).map (coordsV (allMon 8 1)))
      (coordsV (allMon 8 1) (raiseT memtable.genG2 [false] 0 (monV 1 [4] rfl))) := by
  decide +kernel

/-- Equivalent sparse maps act equally at both signs. -/
theorem pin87 (A B : memtable.SMap) (h : memtable.sOneValue A B = true)
    (neg : Bool) (s : Nat) {k : Nat} (v : SVec k) : actT A neg s v = actT B neg s v :=
  actT_congr A B h neg s v

/-- Entry reordering and a signed repeated key give one map and
one action at the collected coefficient. -/
theorem pin88 :
    memtable.sOneValue [(1, 0, BPair.ofNat 3), (1, 0, (BPair.ofNat 2).swap), (0, 1, BPair.ofNat 2)]
      [(0, 1, BPair.ofNat 2), (1, 0, BPair.ofNat 1)] = true
    ∧ actT [(1, 0, BPair.ofNat 3), (1, 0, (BPair.ofNat 2).swap), (0, 1, BPair.ofNat 2)] false 0 topG2
      = monV 1 [1] rfl
    ∧ actT [(0, 1, BPair.ofNat 2), (1, 0, BPair.ofNat 1)] true 0 topG2
      = scaleV ((BPair.ofNat 1).swap) (monV 1 [1] rfl) := by decide +kernel

/-- Transpose pairing holds at every valid slot and sign. -/
theorem pin89 (T : memtable.Table) (M : memtable.SMap) (neg : Bool)
    {k : Nat} (s : Nat) (hs : s < k) (u v : SVec k) :
    (pairT T true (actT M neg s u) v).oneValue
      (pairT T true u (actT (memtable.sT M) neg s v)) := pairT_actT T M neg s hs u v

/-- Standard and dual slots read the actual G2 adjoint pair. -/
theorem pin90 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank) (u v : SVec sig.length) :
    (pairT memtable.genG2 true (raiseT memtable.genG2 sig i u) v).oneValue
      (pairT memtable.genG2 true u (lowerT memtable.genG2 sig i v)) := pairT_raise_lower_G2 sig i hi u v

/-- Unequal transposed coefficients and the signed action distinguish
the transpose; the default key beyond the slot count refuses its law. -/
theorem pin91 :
    (pairT memtable.genG2 true (actT [(1, 0, BPair.ofNat 2), (0, 1, BPair.ofNat 3)] false 0 topG2)
      (monV 1 [1] rfl)).oneValue (BPair.ofNat 2)
    ∧ (pairT memtable.genG2 true topG2
      (actT (memtable.sT [(1, 0, BPair.ofNat 2), (0, 1, BPair.ofNat 3)]) true 0 (monV 1 [1] rfl))).oneValue
      ((BPair.ofNat 2).swap)
    ∧ ¬ (pairT memtable.genG2 true (actT [(1, 0, BPair.ofNat 1)] false 0 unitV) unitV).oneValue
      (pairT memtable.genG2 true unitV (actT (memtable.sT [(1, 0, BPair.ofNat 1)]) false 0 unitV)) := by
  decide +kernel

/-- Canonical scalars compose and add on one sparse vector. -/
theorem pin92 {k : Nat} (v : SVec k) (a b c : BPair) (h : a.oneValue b) :
    scaleV a v = scaleV b v ∧ scaleV (BPair.ofNat 1) v = v ∧ scaleV BPair.unit v = emptyV k
      ∧ scaleV a (scaleV c v) = scaleV (a * c) v
      ∧ addV (scaleV a v) (scaleV c v) = scaleV (a + c) v ∧ addV (emptyV k) v = v :=
  ⟨scaleV_oneValue v a b h, scaleV_one v, scaleV_unit v, scaleV_scale v a c,
    scaleV_add v a c, addV_empty_left v⟩

/-- Every iterate keeps its keys and the next depth is one lowering. -/
theorem pin93 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (hv : keysRead memtable.genG2.keys v) (n : Nat) :
    keysRead memtable.genG2.keys (iterLowerT memtable.genG2 sig i n v)
      ∧ iterLowerT memtable.genG2 sig i (n + 1) v = lowerT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i n v) :=
  ⟨keysRead_iterLowerT_G2 sig i hi v hv n, iterLowerT_succ memtable.genG2 sig i n v⟩

/-- The string weight and its chosen coroot read at every occupied monomial. -/
theorem pin94 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (n : Nat) (p : List Nat × BPair) (hp : p ∈ (iterLowerT memtable.genG2 sig i n v).val) :
    homogRead memtable.genG2 sig (iterLowerT memtable.genG2 sig i n v)
      (poly.pnorm (elim.vecAdd w (elim.vecScale (BPair.ofNat n)
        (poly.neg (getAt [] sertables.tableG2.cartan i))))) ∧
    (getAt BPair.unit (weightT memtable.genG2 sig p.1) i + BPair.ofNat (2 * n)).oneValue (getAt BPair.unit w i) :=
  ⟨homogRead_iterLowerT_G2 sig i hi v w hv hw hh n, iterLowerT_coroot_G2 sig i hi v w hv hw hh n p hp⟩

/-- An occupied simple top reads a natural coroot height. -/
theorem pin95 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = []) (ho : v.val ≠ []) :
    BPair.unit ≤ getAt BPair.unit w i := top_coroot_G2 sig i hi v w hv hw hh hs ht ho

/-- The raising coefficient holds at every depth through the height. -/
theorem pin96 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (b : Nat) (hb : b ≤ h) :
    raiseT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i (b + 1) v)
      = scaleV (BPair.ofNat ((b + 1) * (h - b))) (iterLowerT memtable.genG2 sig i b v) :=
  iterLowerT_raise_G2 sig i hi v w hv hw hh hs ht h hhg b hb

/-- The terminal depth is vacant and every earlier depth occupied,
with the self-pairing at the coefficient product. -/
theorem pin97 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (ho : v.val ≠ []) (b : Nat) (hb : b ≤ h) :
    iterLowerT memtable.genG2 sig i (h + 1) v = emptyV sig.length ∧
    (iterLowerT memtable.genG2 sig i b v).val ≠ [] ∧
    (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig i b v)
      (iterLowerT memtable.genG2 sig i b v)).oneValue
      (BPair.ofNat (strings.coeffProd h b) * pairT memtable.genG2 true v v) :=
  ⟨iterLowerT_term_G2 sig i hi v w hv hw hh hs ht h hhg,
    iterLowerT_occupied_G2 sig i hi v w hv hw hh hs ht h hhg ho b hb,
    iterLowerT_selfpair_G2 sig i hi v w hv hw hh hs ht h hhg b hb⟩

/-- Both simple one-slot strings terminate at their next depth;
a top for the second simple need not be a top for the first. -/
theorem pin98 :
    (iterLowerT memtable.genG2 [false] 0 1 topG2).val ≠ []
    ∧ iterLowerT memtable.genG2 [false] 0 2 topG2 = emptyV 1
    ∧ iterLowerT memtable.genG2 [false] 0 3 topG2 = emptyV 1
    ∧ (raiseT memtable.genG2 [false] 1 (monV 1 [1] rfl)).val = []
    ∧ (raiseT memtable.genG2 [false] 0 (monV 1 [1] rfl)).val ≠ []
    ∧ (iterLowerT memtable.genG2 [false] 1 1 (monV 1 [1] rfl)).val ≠ []
    ∧ iterLowerT memtable.genG2 [false] 1 2 (monV 1 [1] rfl) = emptyV 1 := by decide +kernel

/-- Height three distinguishes the two occupied trace coefficients,
and the second depth has the self-pairing product twelve. -/
theorem pin99 :
    let sig := [false, false, false]
    let t := tensorV (tensorV topG2 topG2) topG2
    let y := iterLowerT memtable.genG2 sig 0 1 t
    let z := iterLowerT memtable.genG2 sig 0 2 t
    raiseT memtable.genG2 sig 0 (lowerT memtable.genG2 sig 0 y) = scaleV (BPair.ofNat 4) y ∧
    lowerT memtable.genG2 sig 0 (raiseT memtable.genG2 sig 0 y) = scaleV (BPair.ofNat 3) y ∧
    (pairT memtable.genG2 true z z).oneValue (BPair.ofNat 12) := by decide +kernel

/-- A middle weight at natural coroot zero has an occupied raising,
and its next raising-after-lowering refuses the top's zero coefficient. -/
theorem pin100 :
    let sig := [false, false]
    let y := lowerT memtable.genG2 sig 0 (tensorV topG2 topG2)
    homogRead memtable.genG2 sig y [BPair.unit, BPair.ofNat 1] ∧
    (raiseT memtable.genG2 sig 0 y).val ≠ [] ∧
    raiseT memtable.genG2 sig 0 (lowerT memtable.genG2 sig 0 y) ≠ scaleV BPair.unit y := by decide +kernel

/-- Distinct depths are perpendicular at every homogeneous seed. -/
theorem pin101 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (a b : Nat) (hab : a ≠ b) :
    (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig i a v)
      (iterLowerT memtable.genG2 sig i b v)).oneValue BPair.unit :=
  iterLowerT_perp_G2 sig i hi v w hv hw hh a b hab

/-- Iterates of any span member stay inside the computed G2 span. -/
theorem pin102 (sig : List Bool) (top v : SVec sig.length)
    (hs : sig.all (fun b => !b) = true) (ht : keysRead memtable.genG2.keys top)
    (hv : keysRead memtable.genG2.keys v) (i : Nat) (hi : i < memtable.genG2.rank)
    (hspan : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) v)) (n : Nat) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((blockSpanT memtable.genG2 sig top).map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i n v)) :=
  iterLowerT_span_G2 sig top v hs ht hv i hi hspan n

/-- Both ordered string words read their own depth coefficient. -/
theorem pin103 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (b : Nat) (hb : b ≤ h) :
    raiseT memtable.genG2 sig i (lowerT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i b v))
      = scaleV (BPair.ofNat ((b + 1) * (h - b))) (iterLowerT memtable.genG2 sig i b v) ∧
    lowerT memtable.genG2 sig i (raiseT memtable.genG2 sig i (iterLowerT memtable.genG2 sig i b v))
      = scaleV (BPair.ofNat (b * (h + 1 - b))) (iterLowerT memtable.genG2 sig i b v) :=
  iterLowerT_trace_G2 sig i hi v w hv hw hh hs ht h hhg b hb

/-- The unit pairing reads its exchange, scalar, sum and vacant
vector laws at every slot count. -/
theorem pin104 (T : memtable.Table) {k : Nat} (u v z : SVec k) (c : BPair) :
    (pairT T true u v).oneValue (pairT T true v u) ∧
    (pairT T true u (scaleV c v)).oneValue (c * pairT T true u v) ∧
    (pairT T true u (addV v z)).oneValue (pairT T true u v + pairT T true u z) ∧
    (pairT T true u (emptyV k)).oneValue BPair.unit :=
  ⟨pairT_unit_comm T u v, pairT_unit_scale T u v c, pairT_unit_add T u v z, pairT_unit_empty T u⟩

/-- The first string determines the pairing coefficient at an arbitrary second seed. -/
theorem pin105 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (z : SVec sig.length) (b : Nat) (hb : b ≤ h) :
    (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig i b v)
      (iterLowerT memtable.genG2 sig i b z)).oneValue
      (BPair.ofNat (strings.coeffProd h b) * pairT memtable.genG2 true v z) :=
  iterLowerT_pair_G2 sig i hi v w hv hw hh hs ht h hhg z b hb

/-- Every depth past the string height reads the vacant vector. -/
theorem pin106 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (extra : Nat) :
    iterLowerT memtable.genG2 sig i (h + 1 + extra) v = emptyV sig.length :=
  iterLowerT_past_G2 sig i hi v w hv hw hh hs ht h hhg extra

/-- Complementary depths read the actual simple reflection. -/
theorem pin107 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (ho : v.val ≠ []) (b : Nat) (hb : b ≤ h) :
    weightV memtable.genG2 sig (iterLowerT memtable.genG2 sig i (h - b) v) =
      sertables.reflAt sertables.tableG2 i
        (weightV memtable.genG2 sig (iterLowerT memtable.genG2 sig i b v)) :=
  iterLowerT_reflect_G2 sig i hi v w hv hw hh hs ht h hhg ho b hb

/-- All depths through the height form an independent finite coordinate list. -/
theorem pin108 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (ho : v.val ≠ []) :
    elim.indepRows (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i b v))) :=
  iterLowerT_indep_G2 sig i hi v w hv hw hh hs ht h hhg ho

/-- The actual height is bounded by the finite monomial carrier. -/
theorem pin109 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h)) (ho : v.val ≠ []) :
    h + 1 ≤ (allMon memtable.genG2.keys sig.length).length :=
  iterLowerT_length_le_G2 sig i hi v w hv hw hh hs ht h hhg ho

/-- The chosen raise action preserves every vector in the finite string span. -/
theorem pin110 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (u : SVec sig.length) (hu : keysRead memtable.genG2.keys u)
    (hsp : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i b v)))
      (coordsV (allMon memtable.genG2.keys sig.length) u)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i b v)))
      (coordsV (allMon memtable.genG2.keys sig.length) (raiseT memtable.genG2 sig i u)) :=
  iterLowerT_raise_span_G2 sig i hi v w hv hw hh hs ht h hhg u hu hsp

/-- The chosen lower action preserves every vector in the finite string span. -/
theorem pin111 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (v : SVec sig.length) (w : List BPair) (hv : keysRead memtable.genG2.keys v)
    (hw : w.length = memtable.genG2.rank) (hh : homogRead memtable.genG2 sig v w)
    (hs : sig.all (fun b => !b) = true) (ht : (raiseT memtable.genG2 sig i v).val = [])
    (h : Nat) (hhg : (getAt BPair.unit w i).oneValue (BPair.ofNat h))
    (u : SVec sig.length) (hu : keysRead memtable.genG2.keys u)
    (hsp : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i b v)))
      (coordsV (allMon memtable.genG2.keys sig.length) u)) :
    elim.spanRel (allMon memtable.genG2.keys sig.length).length
      ((List.range (h + 1)).map (fun b => coordsV (allMon memtable.genG2.keys sig.length) (iterLowerT memtable.genG2 sig i b v)))
      (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i u)) :=
  iterLowerT_lower_span_G2 sig i hi v w hv hw hh hs ht h hhg u hu hsp

/-- An arbitrary second seed may mix two weights and have an
occupied raising, while the first string still fixes the pairing. -/
theorem pin112 :
    let sig := [false, false]
    let t := tensorV topG2 topG2
    let z := addV (scaleV (BPair.ofNat 3) t) (lowerT memtable.genG2 sig 0 t)
    (raiseT memtable.genG2 sig 0 z).val ≠ [] ∧
    (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig 0 1 t)
      (iterLowerT memtable.genG2 sig 0 1 z)).oneValue (BPair.ofNat 6) ∧
    (pairT memtable.genG2 true (iterLowerT memtable.genG2 sig 0 2 t)
      (iterLowerT memtable.genG2 sig 0 2 z)).oneValue (BPair.ofNat 12) := by decide +kernel

/-- Reflection pairs endpoints and interior depths of a tensor
string, and the second simple pairs its own endpoints. -/
theorem pin113 :
    let sig := [false, false, false]
    let t := tensorV (tensorV topG2 topG2) topG2
    (∀ b, b < 4 →
      weightV memtable.genG2 sig (iterLowerT memtable.genG2 sig 0 (3 - b) t) =
        sertables.reflAt sertables.tableG2 0
          (weightV memtable.genG2 sig (iterLowerT memtable.genG2 sig 0 b t))) ∧
    weightV memtable.genG2 [false] (iterLowerT memtable.genG2 [false] 1 1 (monV 1 [1] rfl)) =
      sertables.reflAt sertables.tableG2 1 (weightV memtable.genG2 [false] (monV 1 [1] rfl)) ∧
    weightV memtable.genG2 [false] (iterLowerT memtable.genG2 [false] 0 (1 - 2) topG2) ≠
      sertables.reflAt sertables.tableG2 0
        (weightV memtable.genG2 [false] (iterLowerT memtable.genG2 [false] 0 2 topG2)) := by decide +kernel

/-- The height-two tensor string is independent and its span
contains both actions on a sum of its first two members. -/
theorem pin114 :
    let sig := [false, false]
    let t := tensorV topG2 topG2
    let ms := allMon 8 2
    let rows := (List.range 3).map (fun b => coordsV ms (iterLowerT memtable.genG2 sig 0 b t))
    let u := addV t (lowerT memtable.genG2 sig 0 t)
    rows.length = 3 ∧ elim.indepRows ms.length rows ∧
    elim.spanRel ms.length rows (coordsV ms u) ∧
    elim.spanRel ms.length rows (coordsV ms (raiseT memtable.genG2 sig 0 u)) ∧
    elim.spanRel ms.length rows (coordsV ms (lowerT memtable.genG2 sig 0 u)) := by decide +kernel

/-- The height-zero scalar string is one independent line, the
vacant seed is dependent, and both stay vacant after the first lowering. -/
theorem pin115 :
    elim.indepRows 1 [(coordsV (allMon 8 0) unitV)] ∧
    ¬ elim.indepRows 1 [(coordsV (allMon 8 0) (emptyV 0))] ∧
    iterLowerT memtable.genG2 [] 0 4 unitV = emptyV 0 ∧
    iterLowerT memtable.genG2 [] 1 4 (emptyV 0) = emptyV 0 := by decide +kernel

/-- A middle member at natural coroot height zero is not a top;
its one-member list refuses both raising and lowering closure. -/
theorem pin116 :
    let sig := [false, false]
    let y := lowerT memtable.genG2 sig 0 (tensorV topG2 topG2)
    let ms := allMon 8 2
    let rows := [coordsV ms y]
    homogRead memtable.genG2 sig y [BPair.unit, BPair.ofNat 1] ∧
    ¬ elim.spanRel ms.length rows (coordsV ms (raiseT memtable.genG2 sig 0 y)) ∧
    ¬ elim.spanRel ms.length rows (coordsV ms (lowerT memtable.genG2 sig 0 y)) := by decide +kernel

/-- Residuals preserve the finite key carrier. -/
theorem pin117 (T : memtable.Table) (d : Nat) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead d u) (hv : keysRead d v) :
    keysRead d (residT T pool v) :=
  keysRead_residT T d pool v hp hv

/-- A homogeneous pool and seed give a homogeneous residual. -/
theorem pin118 (T : memtable.Table) (sig : List Bool) {k : Nat}
    (pool : List (SVec k)) (v : SVec k) (w : List BPair)
    (hp : ∀ u ∈ pool, homogRead T sig u w) (hv : homogRead T sig v w) :
    homogRead T sig (residT T pool v) w :=
  homogRead_residT T sig pool v w hp hv

/-- Sparse residual coordinates read the existing elimination residual. -/
theorem pin119 (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k)))) :
    poly.oneValue (coordsV (allMon T.keys k) (residT T pool v))
      (elim.residW (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k)))
        (coordsV (allMon T.keys k) v)) :=
  coordsV_residT T hunit pool v hp hv hind

/-- Perpendicularity extends from a sparse pool to its coordinate span. -/
theorem pin120 (T : memtable.Table) (d : Nat) {k : Nat}
    (pool : List (SVec k)) (x y : SVec k) (hx : keysRead d x)
    (hperp : ∀ u ∈ pool, (pairT T true x u).oneValue BPair.unit)
    (hspan : elim.spanRel (allMon d k).length (pool.map (coordsV (allMon d k)))
      (coordsV (allMon d k) y)) : (pairT T true x y).oneValue BPair.unit :=
  pairT_span_unit T d pool x y hx hperp hspan

/-- The computed residual pairs each collected member at the unit. -/
theorem pin121 (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k))))
    (u : SVec k) (hu : u ∈ pool) :
    (pairT T true u (residT T pool v)).oneValue BPair.unit :=
  residT_perp T hunit pool v hp hv hind u hu

/-- The residual stays inside the containing coordinate span. -/
theorem pin122 (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k))))
    (base : List (SVec k))
    (hpool : ∀ u ∈ pool, elim.spanRel (allMon T.keys k).length
      (base.map (coordsV (allMon T.keys k))) (coordsV (allMon T.keys k) u))
    (hvspan : elim.spanRel (allMon T.keys k).length
      (base.map (coordsV (allMon T.keys k))) (coordsV (allMon T.keys k) v)) :
    elim.spanRel (allMon T.keys k).length (base.map (coordsV (allMon T.keys k)))
      (coordsV (allMon T.keys k) (residT T pool v)) :=
  residT_span T hunit pool v hp hv hind base hpool hvspan

/-- A refused vector gives an occupied independent residual extension. -/
theorem pin123 (T : memtable.Table) (hunit : unitWtRead T = true) {k : Nat}
    (pool : List (SVec k)) (v : SVec k)
    (hp : ∀ u ∈ pool, keysRead T.keys u) (hv : keysRead T.keys v)
    (hind : elim.indepRows (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k))))
    (hnot : ¬ elim.spanRel (allMon T.keys k).length (pool.map (coordsV (allMon T.keys k)))
      (coordsV (allMon T.keys k) v)) :
    (residT T pool v).val ≠ [] ∧
    elim.indepRows (allMon T.keys k).length
      ((pool ++ [residT T pool v]).map (coordsV (allMon T.keys k))) :=
  residT_refuse T hunit pool v hp hv hind hnot

/-- The G2 residual-top step holds at the actual table actions. -/
theorem pin124 (sig : List Bool) (i : Nat) (hi : i < memtable.genG2.rank)
    (pool above : List (SVec sig.length)) (v : SVec sig.length)
    (hp : ∀ u ∈ pool, keysRead memtable.genG2.keys u)
    (ha : ∀ u ∈ above, keysRead memtable.genG2.keys u)
    (hv : keysRead memtable.genG2.keys v)
    (hind : elim.indepRows (allMon memtable.genG2.keys sig.length).length
      (pool.map (coordsV (allMon memtable.genG2.keys sig.length))))
    (hraise : elim.spanRel (allMon memtable.genG2.keys sig.length).length
      (above.map (coordsV (allMon memtable.genG2.keys sig.length)))
      (coordsV (allMon memtable.genG2.keys sig.length)
        (raiseT memtable.genG2 sig i (residT memtable.genG2 pool v))))
    (hlower : ∀ u ∈ above,
      elim.spanRel (allMon memtable.genG2.keys sig.length).length
        (pool.map (coordsV (allMon memtable.genG2.keys sig.length)))
        (coordsV (allMon memtable.genG2.keys sig.length) (lowerT memtable.genG2 sig i u))) :
    raiseT memtable.genG2 sig i (residT memtable.genG2 pool v) = emptyV sig.length :=
  residT_raise_G2 sig i hi pool above v hp ha hv hind hraise hlower

/-- Unequal pooled norms read the determinant clearing on a
third coordinate, and the residual extends the pool independently. -/
theorem pin125 :
    let a := monV 1 [0] rfl
    let b := monV 1 [1] rfl
    let c := monV 1 [2] rfl
    let pool := [scaleV (BPair.ofNat 2) a, scaleV (BPair.ofNat 3) b]
    let v := addV (addV a b) c
    let R := residT memtable.genG2 pool v
    R = scaleV (BPair.ofNat 36) c ∧
    (pairT memtable.genG2 true (getAt (emptyV 1) pool 0) R).oneValue BPair.unit ∧
    (pairT memtable.genG2 true (getAt (emptyV 1) pool 1) R).oneValue BPair.unit ∧
    elim.indepRows 8 ((pool ++ [R]).map (coordsV (allMon 8 1))) := by decide +kernel

/-- A member's residual is vacant, and at a vacant pool the
residual is the seed with its occupied signed coefficients. -/
theorem pin126 :
    let a := scaleV (BPair.ofNat 2) (monV 1 [0] rfl)
    let b := scaleV (BPair.ofNat 3) (monV 1 [1] rfl)
    let v := addV a (scaleV ((BPair.ofNat 2).swap) b)
    residT memtable.genG2 [a, b] v = emptyV 1 ∧
    residT memtable.genG2 [] v = v ∧
    residT memtable.genG2 [] (emptyV 0) = emptyV 0 := by decide +kernel

/-- A dependent pool does not yield an occupied independent
extension, even at a seed outside its span. -/
theorem pin127 :
    let a := monV 1 [0] rfl
    let b := monV 1 [1] rfl
    let pool := [a, scaleV (BPair.ofNat 2) a]
    ¬ elim.spanRel 8 (pool.map (coordsV (allMon 8 1))) (coordsV (allMon 8 1) b) ∧
    residT memtable.genG2 pool b = emptyV 1 ∧
    ¬ elim.indepRows 8 ((pool ++ [residT memtable.genG2 pool b]).map (coordsV (allMon 8 1))) := by
  decide +kernel

/-- The homogeneous tensor residual is a top: the above member's
lowering lies in the collected group. A one-slot top for the
second simple can have an occupied first raising. -/
theorem pin128 :
    let sig := [false, false]
    let a := monV 2 [0, 1] rfl
    let b := monV 2 [1, 0] rfl
    let t := tensorV topG2 topG2
    let pool := [addV a b]
    let R := residT memtable.genG2 pool a
    let ms := allMon 8 2
    R.val ≠ [] ∧ homogRead memtable.genG2 sig R [BPair.unit, BPair.ofNat 1] ∧
    elim.spanRel ms.length (pool.map (coordsV ms)) (coordsV ms (lowerT memtable.genG2 sig 0 t)) ∧
    raiseT memtable.genG2 sig 0 R = emptyV 2 ∧
    raiseT memtable.genG2 [false] 1 (residT memtable.genG2 [] (monV 1 [1] rfl)) = emptyV 1 ∧
    (raiseT memtable.genG2 [false] 0 (residT memtable.genG2 [] (monV 1 [1] rfl))).val ≠ [] := by
  decide +kernel

/-- Membership of the raising in the above group alone does not
force a top when that group's lowering fails the collected span. -/
theorem pin129 :
    let v := monV 1 [1] rfl
    let R := residT memtable.genG2 [] v
    let ms := allMon 8 1
    elim.spanRel ms.length [coordsV ms topG2] (coordsV ms (raiseT memtable.genG2 [false] 0 R)) ∧
    ¬ elim.spanRel ms.length [] (coordsV ms (lowerT memtable.genG2 [false] 0 topG2)) ∧
    (raiseT memtable.genG2 [false] 0 R).val ≠ [] := by decide +kernel

/-- A mixed-weight pool can move the residual off its seed's
weight; a seed outside the stated key carrier keeps that refusal
at the vacant pool. -/
theorem pin130 :
    let a := monV 1 [0] rfl
    let b := monV 1 [1] rfl
    homogRead memtable.genG2 [false] a [BPair.ofNat 1, BPair.unit] ∧
    ¬ homogRead memtable.genG2 [false] (residT memtable.genG2 [addV a b] a)
      [BPair.ofNat 1, BPair.unit] ∧
    ¬ keysRead 8 (residT memtable.genG2 [] (monV 1 [8] rfl)) := by decide +kernel

/-- A weighted residual need not be perpendicular at the unit
pairing: the unit-weight condition distinguishes the two reads. -/
theorem pin131 :
    let T := { memtable.lettersT 2 with wt := [(0, 0, BPair.ofNat 2), (1, 1, BPair.ofNat 3)] }
    let a := monV 1 [0] rfl
    let b := monV 1 [1] rfl
    let u := addV a b
    unitWtRead T = false ∧
    (pairT T true u (residT T [u] a)).oneValue (BPair.ofNat 1) ∧
    ¬ (pairT T true u (residT T [u] a)).oneValue BPair.unit := by decide +kernel

/-- A vacant processed group has the lowering condition, but a
raising outside its span need not read the vacant vector. -/
theorem pin132 :
    let R := residT memtable.genG2 [] (monV 1 [1] rfl)
    let y := raiseT memtable.genG2 [false] 0 R
    ¬ elim.spanRel 8 [] (coordsV (allMon 8 1) y) ∧ y.val ≠ [] := by decide +kernel

/-- A coordinate carrier omitting the paired vector's key reads
its coordinates vacant while its self-pairing is occupied. -/
theorem pin133 :
    ¬ keysRead 0 topG2 ∧
    elim.spanRel 0 [] (coordsV (allMon 0 1) topG2) ∧
    ¬ (pairT memtable.genG2 true topG2 topG2).oneValue BPair.unit := by decide +kernel

end slotpower
