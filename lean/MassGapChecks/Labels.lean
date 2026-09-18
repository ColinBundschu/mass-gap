import MassGap.Labels
import MassGap.Adjchar
/-!
The check module for `con:labels`: the batteries re-read the label
set by kernel `decide` — the reduction and the dual label's
occupancy reversal with the involution and the self-dual adjoint,
the label count's matched-degree lift in both degree directions
with the definitional route's coherence (the crown among the
pins), the Casimir read's class invariance, and the Cartan
equality's instances.
-/

namespace labels
set_option maxHeartbeats 4000000

open ground places

/-! The reduction and the dual label. -/

theorem pin1 : reduce [2, 1] = [2, 0] := rfl
theorem pin2 : reduce [1, 0, 2] = [1, 0, 0] := rfl
theorem pin3 : dualL [1, 0, 0] = [0, 1, 0] := rfl
theorem pin4 : dualL [2, 0, 0] = [0, 2, 0] := rfl
theorem pin5 : dualL [1, 1, 0] = [1, 1, 0] := rfl
theorem pin6 : dualL [0, 0, 0] = [0, 0, 0] := rfl
theorem pin7 : dualL (dualL [2, 1, 0]) = [2, 1, 0] := rfl
theorem pin8 : dualL (dualL [1, 0, 2, 0]) = [1, 0, 2, 0] := rfl
theorem pin9 : unitL 3 = [0, 0, 0] := rfl

/-! The label count's coherence with the definitional route at the
matched degree, the crown triple among the pins. -/

theorem pin10 : countL [1, 0] [1, 0] [2, 0]
    = blockcount.fusionCount [1, 0] [1, 0] [2, 0] := by decide +kernel
theorem pin11 : countL [1, 0] [1, 0] [0, 1]
    = blockcount.fusionCount [1, 0] [1, 0] [0, 1] := by decide +kernel
theorem pin12 : countL [1, 1, 0] [1, 1, 0] [1, 1, 1] = 2 := by decide +kernel

/-! The matched-degree lift in both degree directions, with the
divisibility guard's refusals. -/

theorem pin13 : countL [1, 0] [1, 0] (unitL 2) = 1 := by decide +kernel
theorem pin14 : countL (unitL 2) [1, 0] [1, 1] = 1 := by decide +kernel
theorem pin15 : countL [1, 0, 0] [1, 0, 0] (unitL 3) = 0 := by decide +kernel
theorem pin16 : countL [1, 0, 0] [0, 1, 0] (unitL 3) = 1 := by decide +kernel
theorem pin17 : countL [1, 1, 0] [1, 1, 0] (unitL 3) = 1 := by decide +kernel

/-! The unit label's own row, `N^c_{a 𝟏} = δ_{ac}`
(`lem:blockcount`(iii)'s third identity at labels). -/

theorem pin18 : countL [1, 0] (unitL 2) [1, 0] = 1 := by decide +kernel
theorem pin19 : countL [1, 0] (unitL 2) [2, 0] = 0 := by decide +kernel
theorem pin20 : countL [1, 1, 0] (unitL 3) [1, 1, 0] = 1 := by decide +kernel
theorem pin21 : countL [1, 1, 0] (unitL 3) [1, 0, 0] = 0 := by decide +kernel

/-! The matched-degree coherence as the general theorem's own
route, the lift's discriminator against the block count, and the
second width's refusal. -/

theorem pin22 : countL [1, 0] [1, 0] [2, 0]
    = blockcount.fusionCount [1, 0] [1, 0] [2, 0] :=
  countL_matched [1, 0] [1, 0] [2, 0] rfl rfl rfl

theorem pin23 : countL [1, 0] [1, 0] [0, 1]
    = blockcount.fusionCount [1, 0] [1, 0] [0, 1] :=
  countL_matched [1, 0] [1, 0] [0, 1] rfl rfl rfl

theorem pin24 : countL [1, 1, 0] [1, 0, 0] [1, 0, 1]
    = blockcount.fusionCount [1, 1, 0] [1, 0, 0] [1, 0, 1] :=
  countL_matched [1, 1, 0] [1, 0, 0] [1, 0, 1] rfl rfl rfl

theorem pin25 : countL [1, 0] [1, 0] (unitL 2) = 1 := by decide +kernel
theorem pin26 : blockcount.fusionCount [1, 0] [1, 0] (unitL 2) = 0 := by decide +kernel

theorem pin27 : countL [1, 0] [1, 0, 0] [2, 0] = 0 := by decide +kernel
theorem pin28 : blockcount.fusionCount [1, 0] [1, 0, 0] [2, 0] = 1 := by decide +kernel

/-! The class move at one full column, each argument: the general
theorem's route beside the kernel read. -/

theorem pin29 : countL (ground.bumpAt 1 [1, 0]) [1, 0] [2, 0]
    = countL [1, 0] [1, 0] [2, 0] :=
  countL_bumpA [1, 0] [1, 0] [2, 0] rfl rfl

theorem pin30 : countL [1, 0] (ground.bumpAt 1 [1, 0]) [2, 0]
    = countL [1, 0] [1, 0] [2, 0] :=
  countL_bumpB [1, 0] [1, 0] [2, 0] rfl rfl

theorem pin31 : countL [1, 0] [1, 0] (ground.bumpAt 1 [2, 0])
    = countL [1, 0] [1, 0] [2, 0] :=
  countL_bumpC [1, 0] [1, 0] [2, 0] rfl rfl

theorem pin32 : countL [1, 0, 0] (ground.bumpAt 2 [0, 1, 0]) (unitL 3)
    = countL [1, 0, 0] [0, 1, 0] (unitL 3) :=
  countL_bumpB [1, 0, 0] [0, 1, 0] (unitL 3) rfl rfl

theorem pin33 : countL (ground.bumpAt 2 [1, 0, 0]) [0, 1, 0] [1, 1, 0]
    = countL [1, 0, 0] [0, 1, 0] [1, 1, 0] :=
  countL_bumpA [1, 0, 0] [0, 1, 0] [1, 1, 0] rfl rfl

theorem pin34 : countL [1, 0, 0] [0, 1, 0] (ground.bumpAt 2 [1, 1, 0])
    = countL [1, 0, 0] [0, 1, 0] [1, 1, 0] :=
  countL_bumpC [1, 0, 0] [0, 1, 0] [1, 1, 0] rfl rfl

theorem pin35 : countL (ground.bumpAt 1 [1, 0]) [1, 0] [2, 0] = 1 := by decide +kernel

/-! The dual label's involution at the class representative, the
non-reduced shapes among the instances. -/

theorem pin36 : dualL (dualL [2, 1]) = reduce [2, 1] := dualL_dualL [2, 1]
theorem pin37 : dualL (dualL [1, 0, 2]) = reduce [1, 0, 2] :=
  dualL_dualL [1, 0, 2]
theorem pin38 : dualL (dualL [0, 3, 1, 2]) = reduce [0, 3, 1, 2] := by decide +kernel

/-! The full-column join against the dual label, the asymmetric
pair among the instances, with the non-constant join and the
second width's refusals. -/

theorem pin39 : reduce [2, 0, 0] = dualL [0, 2, 0] :=
  join_dualL [2, 0, 0] [0, 2, 0] rfl 2 (by decide +kernel)

theorem pin40 : List.zipWith (fun x y => x + y) (rowList [0, 2, 0])
      ((rowList [2, 0, 0]).reverse)
    = List.replicate ([2, 0, 0] : Shape).length
      ((degree [2, 0, 0] + degree [0, 2, 0])
        / ([2, 0, 0] : Shape).length) :=
  dualL_join [2, 0, 0] [0, 2, 0] (by decide +kernel)

theorem pin41 : ¬ List.zipWith (fun x y => x + y) (rowList [1, 1, 0])
      ((rowList [2, 0, 0]).reverse) = List.replicate 3 2 := by decide +kernel
theorem pin42 : ¬ reduce [2, 0, 0] = dualL [1, 1, 0] := by decide +kernel

theorem pin43 : List.zipWith (fun x y => x + y) (rowList [1, 0, 0])
    ((rowList [1, 0]).reverse) = List.replicate 2 1 := by decide +kernel
theorem pin44 : ¬ reduce [1, 0] = dualL [1, 0, 0] := by decide +kernel

/-! The dimension at the class, the general theorem's route with
one kernel read beside it. -/

theorem pin45 : weyldim.dimOf ([] : Shape) = weyldim.dimOf (reduce []) :=
  dimOf_class []
theorem pin46 : weyldim.dimOf [1, 2] = weyldim.dimOf (reduce [1, 2]) :=
  dimOf_class [1, 2]
theorem pin47 : weyldim.dimOf [0, 1, 2] = weyldim.dimOf (reduce [0, 1, 2]) :=
  dimOf_class [0, 1, 2]
theorem pin48 : weyldim.dimOf [1, 2] = weyldim.dimOf (reduce [1, 2]) := by decide +kernel

/-! The Casimir read's class invariance, the general theorem's own
instances with one kernel read beside them. -/

theorem pin49 : c2ClassRead [1, 1] := by decide +kernel
theorem pin50 : c2ClassRead [2, 2] := c2Class_all _
theorem pin51 : c2ClassRead [1, 0, 1] := c2Class_all _
theorem pin52 : c2ClassRead [1, 1, 2] := c2Class_all _
theorem pin53 : c2ClassRead [0, 1, 0, 3] := c2Class_all _

/-! The Cartan equality's instances. -/

theorem pin54 : cartanRead [1, 0] [1, 0] := by decide +kernel
theorem pin55 : cartanRead [1, 0] [2, 0] := by decide +kernel
theorem pin56 : cartanRead [1, 0, 0] [1, 1, 0] := by decide +kernel
theorem pin57 : cartanRead [1, 1, 0] [1, 1, 0] := by decide +kernel
theorem pin58 : cartanRead [2, 0, 0] [0, 1, 0] := by decide +kernel

/-! The label count at the reduced target, the shape count's own
read at the matched degrees. -/

theorem pin59 : labels.countL [1, 0] (adjchar.theta 2)
      (labels.reduce [1, 1])
    = steinberg.count [1, 0] (adjchar.theta 2) [1, 1] := by decide +kernel
theorem pin60 : labels.countL (adjchar.theta 3) (adjchar.theta 3)
      (labels.reduce [1, 1, 1])
    = steinberg.count (adjchar.theta 3) (adjchar.theta 3) [1, 1, 1] :=
  by decide +kernel
theorem pin61 : labels.countL [1, 0, 0] (adjchar.theta 3)
      (labels.reduce [0, 2, 0])
    = steinberg.count [1, 0, 0] (adjchar.theta 3) [0, 2, 0] :=
  labels.countL_reduce [1, 0, 0] (adjchar.theta 3) [0, 2, 0] rfl
    (by decide +kernel)

/-- The lift's two binders isolated.  The degree tie `hk` is
load-bearing: off the tie the reduced target's lift restores the
wrong column count and the two reads part, the unit pair against
the one-column target the committed refusal.  The width `hca` is
the frame: at the wide target with the tie held both reads are
vacant and the display holds, the binder unrefusable there. -/
theorem pin62 : ¬ (labels.countL [0, 0] [0, 0] (labels.reduce [0, 1])
    = steinberg.count [0, 0] [0, 0] [0, 1]) := by decide +kernel
theorem pin63 : labels.countL [1, 0] (adjchar.theta 2)
      (labels.reduce [1, 1, 0])
    = steinberg.count [1, 0] (adjchar.theta 2) [1, 1, 0] := by decide +kernel

/-! The Cartan sharpening's generals: the fusion count at the
column union, the theorem's route beside its kernel value, with
the two tower steps among the pairs — the doubled first
fundamental at the two-letter width and `θ` against `2θ` at the
three — and the unit shape's own pair at the vacant width. -/

theorem pin64 : blockcount.fusionCount [1, 0] [1, 0]
    (places.addS [1, 0] [1, 0]) = 1 := by decide +kernel
theorem pin65 : blockcount.fusionCount [1, 0] [1, 0]
    (places.addS [1, 0] [1, 0]) = 1 :=
  cartan_eq [1, 0] [1, 0] (by decide +kernel)

theorem pin66 : blockcount.fusionCount [2, 0] [4, 0]
    (places.addS [2, 0] [4, 0]) = 1 := by decide +kernel
theorem pin67 : blockcount.fusionCount [2, 0] [4, 0]
    (places.addS [2, 0] [4, 0]) = 1 :=
  cartan_eq [2, 0] [4, 0] (by decide +kernel)

theorem pin68 : blockcount.fusionCount [1, 1, 0] [2, 2, 0]
    (places.addS [1, 1, 0] [2, 2, 0]) = 1 :=
  cartan_eq [1, 1, 0] [2, 2, 0] (by decide +kernel)

theorem pin69 : blockcount.fusionCount ([] : Shape) []
    (places.addS [] []) = 1 :=
  cartan_eq [] [] rfl

theorem pin70 : cartanRead [2, 0] [4, 0] := by decide +kernel
theorem pin71 : cartanRead [2, 0] [4, 0] := cartan_all [2, 0] [4, 0] (by decide +kernel)

theorem pin72 : cartanRead [1, 1, 0] [2, 2, 0] := by decide +kernel
theorem pin73 : cartanRead [1, 1, 0] [2, 2, 0] :=
  cartan_all [1, 1, 0] [2, 2, 0] (by decide +kernel)

theorem pin74 : cartanRead [2, 0, 0] [0, 1, 0] :=
  cartan_all [2, 0, 0] [0, 1, 0] (by decide +kernel)

/-- The stated pair list at the column union is the head pair
alone, the sharpening's cap read at the two-letter width. -/
theorem pin75 : blockcount.pairsAt (blockcount.blockSpan [1, 0])
      (blockcount.blockSpan [1, 0])
      (rowList (places.addS [1, 0] [1, 0]))
    = [blockcount.tensorH (blockcount.exhibit [1, 0])
        (blockcount.exhibit [1, 0])] := by decide +kernel

/-! The width binder `hba`'s isolating refusal, the floor's own
fixture: a wider first shape at a second occupied letter starves
the head pair's guard — the truncated column union misses the
tensor's content — and both the fusion count and the label read
sit off the unit. -/

theorem pin76 : ¬ (([3] : Shape).length = ([1, 2] : Shape).length) := by decide +kernel

theorem pin77 : ¬ (blockcount.fusionCount [1, 2] [3]
    (places.addS [1, 2] [3]) = 1) := by decide +kernel

theorem pin78 : ¬ cartanRead [1, 2] [3] := by decide +kernel

/-! The second argument's width refusal: at a second shape one
letter wider the bumped key is the wider shape's own and the two
counts part, the first and target widths held beside it. -/

theorem pin79 : ¬ (([0, 0, 1] : Shape).length = ([0, 0] : Shape).length) := by
  decide +kernel
theorem pin80 : countL [0, 0]
    (ground.bumpAt (([0, 0, 1] : Shape).length - 1) [0, 0, 1])
    [0, 0] = 1 := by decide +kernel
theorem pin81 : countL [0, 0] [0, 0, 1] [0, 0] = 0 := by decide +kernel

/-! The dual pair's binder refusal: off the dual label the join
misses the constant at the degrees' quotient. -/

theorem pin82 : ¬ (reduce [2, 0] = dualL [1, 0]) := by decide +kernel
theorem pin83 : ¬ (List.zipWith (fun x y => x + y) (rowList [1, 0])
      ((rowList [2, 0]).reverse)
    = List.replicate ([2, 0] : Shape).length
      ((degree [2, 0] + degree [1, 0])
        / ([2, 0] : Shape).length)) := by decide +kernel

/-! `prop:repring`'s exchange at the label count, landed by the
theorem route beside a decided instance at unequal factors. -/

theorem pin84 : labels.countL [2, 1, 0] [1, 1, 0] [2, 2, 0]
    = labels.countL [1, 1, 0] [2, 1, 0] [2, 2, 0] := by decide +kernel

theorem pin85 : labels.countL [2, 1, 0] [1, 1, 0] [2, 2, 0]
    = labels.countL [1, 1, 0] [2, 1, 0] [2, 2, 0] :=
  labels.countL_comm [2, 1, 0] [1, 1, 0] [2, 2, 0]
    (by decide +kernel) (by decide +kernel)

theorem pin86 : ¬ (labels.countL [0, 0] [0, 0, 2] [0, 0]
    = labels.countL [0, 0, 2] [0, 0] [0, 0]) := by decide +kernel
theorem pin87 : ¬ (labels.countL [1, 0] [0, 0, 2] [1, 0]
    = labels.countL [0, 0, 2] [1, 0] [1, 0]) := by decide +kernel

/-! The class moves at the label data: the added full columns
against the degree, the row list and the occupancy total, and the
dual label's own join. -/

/-- The battery's label shape: three columns at descending
occupancies. -/
private def sTri : Shape := [2, 1, 0]

theorem pin88 : degree (addFulls 2 sTri)
    = degree sTri + 2 * sTri.length := by decide +kernel
theorem pin89 : degree (addFulls 2 sTri)
    = degree sTri + 2 * sTri.length :=
  degree_addFulls 2 sTri

theorem pin90 : rowList (addFulls 2 sTri)
    = (rowList sTri).map (fun x => x + 2) := by decide +kernel
theorem pin91 : rowList (addFulls 2 sTri)
    = (rowList sTri).map (fun x => x + 2) :=
  rowList_addFulls 2 sTri

theorem pin92 : degree sTri + degree (dualL sTri)
    = sTri.length * ground.sumNat sTri := by decide +kernel
theorem pin93 : degree sTri + degree (dualL sTri)
    = sTri.length * ground.sumNat sTri :=
  degree_dualL_add sTri

theorem pin94 : reduce (dualL sTri) = dualL sTri := reduce_dualL sTri
theorem pin95 : dualL (addFulls 2 sTri) = dualL sTri :=
  dualL_addFulls 2 sTri

/-! The occupancy total at the added full columns reads the last
key's own count only at an occupied width: the vacant shape
carries no key and the added count is refused. -/

theorem pin96 : ground.sumNat (addFulls 2 sTri)
    = ground.sumNat sTri + 2 := by decide +kernel
theorem pin97 : ¬ (ground.sumNat (addFulls 2 ([] : Shape))
    = ground.sumNat ([] : Shape) + 2) := by decide +kernel

/-! The dual pair's own join in both orientations. -/

/-- The battery's join shape: three columns at a raised middle. -/
private def sJoin : Shape := [1, 2, 0]

theorem pin98 : List.zipWith (fun x y => x + y) (rowList sJoin)
      ((rowList (dualL sJoin)).reverse)
    = List.replicate sJoin.length (ground.sumNat sJoin) := by
  decide +kernel
theorem pin99 : List.zipWith (fun x y => x + y) (rowList sJoin)
      ((rowList (dualL sJoin)).reverse)
    = List.replicate sJoin.length (ground.sumNat sJoin) :=
  join_dual_selfR sJoin

theorem pin100 : List.zipWith (fun x y => x + y) (rowList (dualL sJoin))
      ((rowList sJoin).reverse)
    = List.replicate sJoin.length (ground.sumNat sJoin) := by
  decide +kernel
theorem pin101 : List.zipWith (fun x y => x + y) (rowList (dualL sJoin))
      ((rowList sJoin).reverse)
    = List.replicate sJoin.length (ground.sumNat sJoin) :=
  join_dual_selfL sJoin

/-! The label count along the class in the first argument at any
column count, and the count at or above the target's degree. -/

theorem pin102 : countL (addFulls 1 [1, 0]) [1, 0] [2, 0]
    = countL [1, 0] [1, 0] [2, 0] := by decide +kernel
theorem pin103 : countL (addFulls 1 [1, 1, 0]) [1, 1, 0] [1, 1, 1]
    = countL [1, 1, 0] [1, 1, 0] [1, 1, 1] :=
  countL_addFullsA 1 [1, 1, 0] [1, 1, 0] [1, 1, 1] rfl rfl

theorem pin104 : countL (addFulls 1 [1, 0]) [0, 0] [0, 1]
    = countL [1, 0] [0, 0] [0, 1] :=
  countL_addFullsA 1 [1, 0] [0, 0] [0, 1] rfl rfl

theorem pin105 : countL (addFulls 0 [1, 0]) [1, 0] [0, 1]
    = countL [1, 0] [1, 0] [0, 1] :=
  countL_addFullsA 0 [1, 0] [1, 0] [0, 1] rfl rfl

theorem pin106 : countL [1, 0] [1, 0] [0, 0]
    = blockcount.fusionCount [1, 0] [1, 0]
      (addFulls ((degree [1, 0] + degree [1, 0]
        - degree ([0, 0] : Shape)) / ([1, 0] : Shape).length)
        [0, 0]) := by decide +kernel
theorem pin107 : countL [1, 0] [1, 0] [0, 0]
    = blockcount.fusionCount [1, 0] [1, 0]
      (addFulls ((degree [1, 0] + degree [1, 0]
        - degree ([0, 0] : Shape)) / ([1, 0] : Shape).length)
        [0, 0]) :=
  countL_geRead [1, 0] [1, 0] [0, 0] rfl rfl (by decide +kernel)
    (by decide +kernel)

/-! `prop:repring`'s two pairing collapses at the full-column
target, each at the theorem's own route beside its decided
equation, the floors' records beneath. -/

/-- The collapse cells' one-column shape. -/
private def sOne : Shape := [1, 0]

/-- The collapse cells' complement shape. -/
private def sComp : Shape := [0, 1]

theorem pin108 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls 0 sOne) sOne
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) sComp
          (dualread.fulls sOne.length (2 + 0)))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan (addFulls 0 sOne))
          (blockcount.blockSpan sOne))).map
        blockcount.HVec.content))
    = blockcount.fusionCount (addFulls 0 sOne) sOne
      (addFulls (2 + 0 - ground.sumNat sComp) (dualL sComp)) := by
  decide +kernel

theorem pin109 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls 0 sOne) sOne
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) sComp
          (dualread.fulls sOne.length (2 + 0)))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan (addFulls 0 sOne))
          (blockcount.blockSpan sOne))).map
        blockcount.HVec.content))
    = blockcount.fusionCount (addFulls 0 sOne) sOne
      (addFulls (2 + 0 - ground.sumNat sComp) (dualL sComp)) :=
  foldCollapseL sOne sOne sComp 0 2 rfl rfl (by decide +kernel)

theorem pin110 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls 0 sComp) sComp
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) sComp
          (dualread.fulls sComp.length (3 + 0)))
      (ground.dedupF ((blockcount.exhaust sComp.length
        (blockcount.fusedAt (blockcount.blockSpan (addFulls 0 sComp))
          (blockcount.blockSpan sComp))).map
        blockcount.HVec.content))
    = blockcount.fusionCount (addFulls 0 sComp) sComp
      (addFulls (3 + 0 - ground.sumNat sComp) (dualL sComp)) :=
  foldCollapseL sComp sComp sComp 0 3 rfl rfl
    (by decide +kernel)

theorem pin111 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sOne sComp
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 0 sOne)
          (places.shapeOf mu) (dualread.fulls sOne.length (2 + 0)))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan sOne)
          (blockcount.blockSpan sComp))).map
        blockcount.HVec.content))
    = blockcount.fusionCount sOne sComp
      (addFulls (2 - ground.sumNat sOne) (dualL sOne)) := by
  decide +kernel

theorem pin112 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sOne sComp
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 0 sOne)
          (places.shapeOf mu) (dualread.fulls sOne.length (2 + 0)))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan sOne)
          (blockcount.blockSpan sComp))).map
        blockcount.HVec.content))
    = blockcount.fusionCount sOne sComp
      (addFulls (2 - ground.sumNat sOne) (dualL sOne)) :=
  foldCollapseR sOne sOne sComp 0 2 rfl rfl (by decide +kernel)

/-- The vacant arm's cell: the doubled first column against the
two vacant shapes, the occupancy total past the ambient count. -/
private def sTwo : Shape := [2, 0]

/-- The vacant arm's second shape, the width-two unit shape. -/
private def sUnit : Shape := [0, 0]

/-- The overshooting complement key's shape, its occupancy total
past the ambient count. -/
private def sOver : Shape := [3, 0]

theorem pin113 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sUnit sUnit
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 1 sTwo)
          (places.shapeOf mu) (dualread.fulls sTwo.length (1 + 1)))
      (ground.dedupF ((blockcount.exhaust sTwo.length
        (blockcount.fusedAt (blockcount.blockSpan sUnit)
          (blockcount.blockSpan sUnit))).map
        blockcount.HVec.content))
    = 0 := by decide +kernel

theorem pin114 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sUnit sUnit
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 1 sTwo)
          (places.shapeOf mu) (dualread.fulls sTwo.length (1 + 1)))
      (ground.dedupF ((blockcount.exhaust sTwo.length
        (blockcount.fusedAt (blockcount.blockSpan sUnit)
          (blockcount.blockSpan sUnit))).map
        blockcount.HVec.content))
    = 0 :=
  foldCollapseR_vacant sTwo sUnit sUnit 1 1 rfl rfl
    (by decide +kernel)

/-! The floors' reads.  The floors `hp` and `hMa` are load-bearing
with their committed refusals: off the degree tie an overshooting
complement key truncates onto an occupied count while the fold
stays vacant, parting the two sides.  At the tie held the
overshooting key sits off the pool and both sides read the count's
unit, the passing records beneath; and the vacant width reads the
collapse whole, the theorem's own instance. -/

theorem pin115 : ¬ (ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls 0 sOne) sOne
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) sTwo
          (dualread.fulls sOne.length (1 + 0)))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan (addFulls 0 sOne))
          (blockcount.blockSpan sOne))).map
        blockcount.HVec.content))
    = blockcount.fusionCount (addFulls 0 sOne) sOne
        (addFulls (1 + 0 - ground.sumNat sTwo) (dualL sTwo))) := by
  decide +kernel

theorem pin116 : ¬ (ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sOne sOne
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 0 sTwo)
          (places.shapeOf mu)
          (dualread.fulls sTwo.length (1 + 0)))
      (ground.dedupF ((blockcount.exhaust sTwo.length
        (blockcount.fusedAt (blockcount.blockSpan sOne)
          (blockcount.blockSpan sOne))).map
        blockcount.HVec.content))
    = blockcount.fusionCount sOne sOne
        (addFulls (1 - ground.sumNat sTwo) (dualL sTwo))) := by
  decide +kernel

theorem pin117 : ground.sumNat sOver > 2 + 0 := by decide +kernel
theorem pin118 : degree sOne + degree sUnit + degree sOver
    = sOne.length * 2 := by decide +kernel
theorem pin119 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls 0 sOne) sUnit
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) sOver
          (dualread.fulls sOne.length (2 + 0)))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt
          (blockcount.blockSpan (addFulls 0 sOne))
          (blockcount.blockSpan sUnit))).map
        blockcount.HVec.content))
    = blockcount.fusionCount (addFulls 0 sOne) sUnit
      (addFulls (2 + 0 - ground.sumNat sOver) (dualL sOver)) := by
  decide +kernel

theorem pin120 : ground.sumNat sTwo > 1 := by decide +kernel
theorem pin121 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sUnit sUnit
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 1 sTwo)
          (places.shapeOf mu) (dualread.fulls sTwo.length (1 + 1)))
      (ground.dedupF ((blockcount.exhaust sTwo.length
        (blockcount.fusedAt (blockcount.blockSpan sUnit)
          (blockcount.blockSpan sUnit))).map
        blockcount.HVec.content))
    = blockcount.fusionCount sUnit sUnit
      (addFulls (1 - ground.sumNat sTwo) (dualL sTwo)) := by
  decide +kernel

theorem pin122 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount (addFulls 0 ([] : Shape)) []
          (places.shapeOf mu)
        * blockcount.fusionCount (places.shapeOf mu) []
          (dualread.fulls ([] : Shape).length (0 + 0)))
      (ground.dedupF ((blockcount.exhaust ([] : Shape).length
        (blockcount.fusedAt
          (blockcount.blockSpan (addFulls 0 ([] : Shape)))
          (blockcount.blockSpan []))).map
        blockcount.HVec.content))
    = blockcount.fusionCount (addFulls 0 ([] : Shape)) []
      (addFulls (0 + 0 - ground.sumNat ([] : Shape))
        (dualL [])) :=
  foldCollapseL [] [] [] 0 0 rfl rfl (by decide +kernel)

theorem pin123 : ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount ([] : Shape) []
          (places.shapeOf mu)
        * blockcount.fusionCount (addFulls 0 ([] : Shape))
          (places.shapeOf mu)
          (dualread.fulls ([] : Shape).length (0 + 0)))
      (ground.dedupF ((blockcount.exhaust ([] : Shape).length
        (blockcount.fusedAt (blockcount.blockSpan ([] : Shape))
          (blockcount.blockSpan []))).map
        blockcount.HVec.content))
    = blockcount.fusionCount ([] : Shape) []
      (addFulls (0 - ground.sumNat ([] : Shape))
        (dualL [])) :=
  foldCollapseR [] [] [] 0 0 rfl rfl (by decide +kernel)

/-! The class move in the target at any column count, the label
count's own read. -/

theorem pin124 : countL sOne sOne sComp = 1 := by decide +kernel
theorem pin125 : countL sOne sOne (addFulls 2 sComp)
    = countL sOne sOne sComp := by decide +kernel
theorem pin126 : countL sOne sOne (addFulls 2 sComp)
    = countL sOne sOne sComp :=
  countL_addFullsC 2 sOne sOne sComp rfl rfl

/-! The label count below the target's degree: the gap's full
columns enter the first shape. -/

/-- The lift's own target: the pairing's degree two full columns
below it at the width two. -/
private def sHi : Shape := [0, 2]

theorem pin127 : countL sOne sOne sHi = 1 := by decide +kernel
theorem pin128 : countL sOne sOne sHi
    = blockcount.fusionCount
      (addFulls ((degree sHi - (degree sOne + degree sOne))
        / sOne.length) sOne) sOne sHi := by decide +kernel
theorem pin129 : countL sOne sOne sHi
    = blockcount.fusionCount
      (addFulls ((degree sHi - (degree sOne + degree sOne))
        / sOne.length) sOne) sOne sHi :=
  countL_ltRead sOne sOne sHi rfl rfl (by decide +kernel)
    (by decide +kernel)

/-! The block count at a first shape lifted past the target's
deepest key, and the isolating contrast at the refused strict
excess: at a target whose deepest key reaches the column count the
lifted count is occupied. -/

theorem pin130 : ground.getAt 0 (rowList sTwo) (sOne.length - 1) < 1 := by
  decide +kernel
theorem pin131 : blockcount.fusionCount (addFulls 1 sOne) sOne sTwo = 0 := by
  decide +kernel
theorem pin132 : blockcount.fusionCount (addFulls 1 sOne) sOne sTwo = 0 :=
  fusionCount_colOff 1 sOne sOne sTwo rfl rfl (by decide +kernel)
    (by decide +kernel)
theorem pin133 : ¬ (ground.getAt 0 (rowList sHi) (sOne.length - 1) < 1) := by
  decide +kernel
theorem pin134 : 0 < blockcount.fusionCount (addFulls 1 sOne) sOne sHi := by
  decide +kernel

/-! The letter count's positivity refused at the vacant width: the
vacant shape carries no deepest column, its own row list reads the
vacant key, and both the bumped and the lifted counts read one
against the vacancy — the two widths hold, so the binder parts
alone. -/

theorem pin135 : ¬ 0 < ([] : Shape).length := by decide +kernel
theorem pin136 : ground.getAt 0 (rowList ([] : Shape))
    (([] : Shape).length - 1) = 0 := by decide +kernel
theorem pin137 : ¬ (blockcount.fusionCount
    (ground.bumpAt (([] : Shape).length - 1) []) [] [] = 0) := by
  decide +kernel
theorem pin138 : ¬ (blockcount.fusionCount (addFulls 1 ([] : Shape)) [] []
    = 0) := by decide +kernel

/-! The second shape's width refused at the joint lift and at the
lift below the target: at a second shape one letter wider the two
counts part. -/

theorem pin139 : ¬ (([2, 0, 0] : Shape).length = ([0, 0] : Shape).length) := by
  decide +kernel
theorem pin140 : ¬ (blockcount.fusionCount (addFulls 1 ([0, 0] : Shape))
      [2, 0, 0] (addFulls 1 sOne)
    = blockcount.fusionCount [0, 0] [2, 0, 0] sOne) := by decide +kernel
theorem pin141 : ¬ (([0, 0, 0] : Shape).length = ([0, 0] : Shape).length) := by
  decide +kernel
theorem pin142 : ¬ (countL [0, 0] [0, 0, 0] sComp
    = blockcount.fusionCount
      (addFulls ((degree sComp - (degree ([0, 0] : Shape)
        + degree ([0, 0, 0] : Shape))) / ([0, 0] : Shape).length)
        [0, 0]) [0, 0, 0] sComp) := by decide +kernel

/-! The carrier bridge at the two enumerations, the degree its own
weight. -/

theorem pin143 : ground.famFold Nat.add 0
      (fun e => blockcount.fusionCount sOne sOne e * degree e)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sOne sOne (places.shapeOf mu)
        * degree (places.shapeOf mu))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan sOne)
          (blockcount.blockSpan sOne))).map
        blockcount.HVec.content)) := by decide +kernel
theorem pin144 : ground.famFold Nat.add 0
      (fun e => blockcount.fusionCount sOne sOne e * degree e)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sOne sOne (places.shapeOf mu)
        * degree (places.shapeOf mu))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan sOne)
          (blockcount.blockSpan sOne))).map
        blockcount.HVec.content)) :=
  bridgeFold sOne sOne rfl degree

/-! The bridge's letter width refused: at a second shape one
letter wider the enumeration's fold and the pool's part. -/

theorem pin145 : ¬ (([1, 0, 0] : Shape).length = sOne.length) := by
  decide +kernel
theorem pin146 : ¬ (ground.famFold Nat.add 0
      (fun e => blockcount.fusionCount sOne [1, 0, 0] e * degree e)
      (allShapes sOne.length (degree sOne + degree ([1, 0, 0] : Shape)))
    = ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount sOne [1, 0, 0]
          (places.shapeOf mu)
        * degree (places.shapeOf mu))
      (ground.dedupF ((blockcount.exhaust sOne.length
        (blockcount.fusedAt (blockcount.blockSpan sOne)
          (blockcount.blockSpan [1, 0, 0]))).map
        blockcount.HVec.content))) := by decide +kernel

/-! The associativity display at the three branches of the lift's
guard: the target at or below the pairing's degree, above it at a
divisible gap, and off the width's multiples with both sums
vacant.  The three widths are frames: at a forged width the two
sums still read one value. -/

/-- The associativity display's raised target: the pairing's
degree one full column below it at the width two. -/
private def dLift : Shape := [1, 2]

theorem pin147 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne sOne)
      (allShapes sOne.length (degree sOne + degree sOne)) = 2 := by
  decide +kernel
theorem pin148 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne sOne)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun f => steinberg.count sOne sOne f * countL sOne f sOne)
      (allShapes sOne.length (degree sOne + degree sOne)) := by
  decide +kernel
theorem pin149 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne sOne)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun f => steinberg.count sOne sOne f * countL sOne f sOne)
      (allShapes sOne.length (degree sOne + degree sOne)) :=
  countL_assoc sOne sOne sOne sOne rfl rfl rfl

theorem pin150 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne dLift)
      (allShapes sOne.length (degree sOne + degree sOne)) = 2 := by
  decide +kernel
theorem pin151 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne dLift)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun f => steinberg.count sOne sOne f * countL sOne f dLift)
      (allShapes sOne.length (degree sOne + degree sOne)) := by
  decide +kernel
theorem pin152 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne dLift)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun f => steinberg.count sOne sOne f * countL sOne f dLift)
      (allShapes sOne.length (degree sOne + degree sOne)) :=
  countL_assoc sOne sOne sOne dLift rfl rfl rfl

theorem pin153 : ¬ (degree sOne + degree sOne + degree sOne - degree sComp)
    % sOne.length = 0 := by decide +kernel
theorem pin154 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne sComp)
      (allShapes sOne.length (degree sOne + degree sOne)) = 0 := by
  decide +kernel
theorem pin155 : ground.famFold Nat.add 0
      (fun f => steinberg.count sOne sOne f * countL sOne f sComp)
      (allShapes sOne.length (degree sOne + degree sOne)) = 0 := by
  decide +kernel
theorem pin156 : ground.famFold Nat.add 0
      (fun e => steinberg.count sOne sOne e * countL e sOne sComp)
      (allShapes sOne.length (degree sOne + degree sOne))
    = ground.famFold Nat.add 0
      (fun f => steinberg.count sOne sOne f * countL sOne f sComp)
      (allShapes sOne.length (degree sOne + degree sOne)) :=
  countL_assoc sOne sOne sOne sComp rfl rfl rfl

/-! The weighted row transport at the dimension, with the
class-invariance refusal at the degree. At the two fundamentals'
product, the full-column channel reduces to the unit label, so its
dimension is fixed and its degree changes. -/

theorem pin157 : ground.famFold Nat.add 0
    (fun v => ground.optVal (fun e => countL [1, 0] [1, 0] e * weyldim.dimOf e)
      (emit [1, 0] [1, 0] v)) (allShapes 2 2)
    = ground.famFold Nat.add 0
      (fun e => steinberg.count [1, 0] [1, 0] e * weyldim.dimOf e) (allShapes 2 2) :=
  rowFold [1, 0] [1, 0] weyldim.dimOf (fun c _ => (dimOf_class c).symm)
theorem pin158 : ground.famFold Nat.add 0
    (fun v => ground.optVal (fun e => countL [1, 0] [1, 0] e * weyldim.dimOf e)
      (emit [1, 0] [1, 0] v)) (allShapes 2 2)
    = ground.famFold Nat.add 0
      (fun e => steinberg.count [1, 0] [1, 0] e * weyldim.dimOf e) (allShapes 2 2) := by
  decide +kernel
theorem pin159 : ¬ (ground.famFold Nat.add 0
    (fun v => ground.optVal (fun e => countL [1, 0] [1, 0] e * degree e)
      (emit [1, 0] [1, 0] v)) (allShapes 2 2)
    = ground.famFold Nat.add 0
      (fun e => steinberg.count [1, 0] [1, 0] e * degree e) (allShapes 2 2)) := by
  decide +kernel
theorem pin160 : ¬ degree (reduce [0, 1]) = degree [0, 1] := by decide +kernel

/-! The duality reads at an asymmetric reduced shape and at a
full-column representative, with the involution's actual labels
and the computed invariants beside the general theorems. -/

theorem pin161 : c2hat.dfQ (dualL [2, 1, 0, 0]) = c2hat.dfQ [2, 1, 0, 0] :=
  casDual_all [2, 1, 0, 0]
theorem pin162 : weyldim.dimOf (dualL [2, 1, 0, 0]) = weyldim.dimOf [2, 1, 0, 0] :=
  dimDual_all [2, 1, 0, 0]
theorem pin163 : dualL [2, 1, 0, 0] = [0, 1, 2, 0]
    ∧ c2hat.dfQ [0, 1, 2, 0] = c2hat.dfQ [2, 1, 0, 0]
    ∧ weyldim.dimOf [0, 1, 2, 0] = weyldim.dimOf [2, 1, 0, 0] := by decide +kernel
theorem pin164 : c2hat.dfQ (dualL [2, 1, 0, 3]) = c2hat.dfQ [2, 1, 0, 3] :=
  casDual_all [2, 1, 0, 3]
theorem pin165 : weyldim.dimOf (dualL [2, 1, 0, 3]) = weyldim.dimOf [2, 1, 0, 3] :=
  dimDual_all [2, 1, 0, 3]
theorem pin166 : dualL [2, 1, 0, 3] = [0, 1, 2, 0]
    ∧ c2hat.dfQ [0, 1, 2, 0] = c2hat.dfQ [2, 1, 0, 3]
    ∧ weyldim.dimOf [0, 1, 2, 0] = weyldim.dimOf [2, 1, 0, 3] := by decide +kernel
theorem pin167 : c2hat.dfQ (dualL []) = c2hat.dfQ [] := casDual_all []
theorem pin168 : weyldim.dimOf (dualL []) = weyldim.dimOf [] := dimDual_all []

/-! The row's uniqueness at reduced targets and arbitrary input
representatives, at zero width as well. -/

theorem pin169 (d : Nat) (a b c : places.Shape) : countOf c (rowL d a b) ≤ 1 :=
  rowL_count_le d a b c
theorem pin170 : rowL 2 [1, 0] [1, 0] = [[2, 0], [0, 0]] := by decide +kernel

theorem pin171 (n : Nat) : reduce (unitL n) = unitL n := reduce_unit n

end labels
