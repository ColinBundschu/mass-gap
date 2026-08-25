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
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground places labels

/-! The reduction and the dual label. -/

example : reduce [2, 1] = [2, 0] := rfl
example : reduce [1, 0, 2] = [1, 0, 0] := rfl
example : dualL [1, 0, 0] = [0, 1, 0] := rfl
example : dualL [2, 0, 0] = [0, 2, 0] := rfl
example : dualL [1, 1, 0] = [1, 1, 0] := rfl
example : dualL [0, 0, 0] = [0, 0, 0] := rfl
example : dualL (dualL [2, 1, 0]) = [2, 1, 0] := rfl
example : dualL (dualL [1, 0, 2, 0]) = [1, 0, 2, 0] := rfl
example : unitL 3 = [0, 0, 0] := rfl

/-! The label count's coherence with the definitional route at the
matched degree, the crown triple among the pins. -/

example : countL [1, 0] [1, 0] [2, 0]
    = blockcount.fusionCount [1, 0] [1, 0] [2, 0] := by decide +kernel
example : countL [1, 0] [1, 0] [0, 1]
    = blockcount.fusionCount [1, 0] [1, 0] [0, 1] := by decide +kernel
example : countL [1, 1, 0] [1, 1, 0] [1, 1, 1] = 2 := by decide +kernel

/-! The matched-degree lift in both degree directions, with the
divisibility guard's refusals. -/

example : countL [1, 0] [1, 0] (unitL 2) = 1 := by decide +kernel
example : countL (unitL 2) [1, 0] [1, 1] = 1 := by decide +kernel
example : countL [1, 0, 0] [1, 0, 0] (unitL 3) = 0 := by decide +kernel
example : countL [1, 0, 0] [0, 1, 0] (unitL 3) = 1 := by decide +kernel
example : countL [1, 1, 0] [1, 1, 0] (unitL 3) = 1 := by decide +kernel

/-! The unit label's own row, `N^c_{a 𝟏} = δ_{ac}`
(`lem:blockcount`(iii)'s third identity at labels). -/

example : countL [1, 0] (unitL 2) [1, 0] = 1 := by decide +kernel
example : countL [1, 0] (unitL 2) [2, 0] = 0 := by decide +kernel
example : countL [1, 1, 0] (unitL 3) [1, 1, 0] = 1 := by decide +kernel
example : countL [1, 1, 0] (unitL 3) [1, 0, 0] = 0 := by decide +kernel

/-! The matched-degree coherence as the general theorem's own
route, the lift's discriminator against the block count, and the
second width's refusal. -/

example : countL [1, 0] [1, 0] [2, 0]
    = blockcount.fusionCount [1, 0] [1, 0] [2, 0] :=
  countL_matched [1, 0] [1, 0] [2, 0] rfl rfl rfl

example : countL [1, 0] [1, 0] [0, 1]
    = blockcount.fusionCount [1, 0] [1, 0] [0, 1] :=
  countL_matched [1, 0] [1, 0] [0, 1] rfl rfl rfl

example : countL [1, 1, 0] [1, 0, 0] [1, 0, 1]
    = blockcount.fusionCount [1, 1, 0] [1, 0, 0] [1, 0, 1] :=
  countL_matched [1, 1, 0] [1, 0, 0] [1, 0, 1] rfl rfl rfl

example : countL [1, 0] [1, 0] (unitL 2) = 1 := by decide +kernel
example : blockcount.fusionCount [1, 0] [1, 0] (unitL 2) = 0 := by decide +kernel

example : countL [1, 0] [1, 0, 0] [2, 0] = 0 := by decide +kernel
example : blockcount.fusionCount [1, 0] [1, 0, 0] [2, 0] = 1 := by decide +kernel

/-! The class move at one full column, each argument: the general
theorem's route beside the kernel read. -/

example : countL (ground.bumpAt 1 [1, 0]) [1, 0] [2, 0]
    = countL [1, 0] [1, 0] [2, 0] :=
  countL_bumpA [1, 0] [1, 0] [2, 0] rfl rfl

example : countL [1, 0] (ground.bumpAt 1 [1, 0]) [2, 0]
    = countL [1, 0] [1, 0] [2, 0] :=
  countL_bumpB [1, 0] [1, 0] [2, 0] rfl rfl

example : countL [1, 0] [1, 0] (ground.bumpAt 1 [2, 0])
    = countL [1, 0] [1, 0] [2, 0] :=
  countL_bumpC [1, 0] [1, 0] [2, 0] rfl rfl

example : countL [1, 0, 0] (ground.bumpAt 2 [0, 1, 0]) (unitL 3)
    = countL [1, 0, 0] [0, 1, 0] (unitL 3) :=
  countL_bumpB [1, 0, 0] [0, 1, 0] (unitL 3) rfl rfl

example : countL (ground.bumpAt 2 [1, 0, 0]) [0, 1, 0] [1, 1, 0]
    = countL [1, 0, 0] [0, 1, 0] [1, 1, 0] :=
  countL_bumpA [1, 0, 0] [0, 1, 0] [1, 1, 0] rfl rfl

example : countL [1, 0, 0] [0, 1, 0] (ground.bumpAt 2 [1, 1, 0])
    = countL [1, 0, 0] [0, 1, 0] [1, 1, 0] :=
  countL_bumpC [1, 0, 0] [0, 1, 0] [1, 1, 0] rfl rfl

example : countL (ground.bumpAt 1 [1, 0]) [1, 0] [2, 0] = 1 := by decide +kernel

/-! The dual label's involution at the class representative, the
non-reduced shapes among the instances. -/

example : dualL (dualL [2, 1]) = reduce [2, 1] := dualL_dualL [2, 1]
example : dualL (dualL [1, 0, 2]) = reduce [1, 0, 2] :=
  dualL_dualL [1, 0, 2]
example : dualL (dualL [0, 3, 1, 2]) = reduce [0, 3, 1, 2] := by decide +kernel

/-! The full-column join against the dual label, the asymmetric
pair among the instances, with the non-constant join and the
second width's refusals. -/

example : reduce [2, 0, 0] = dualL [0, 2, 0] :=
  join_dualL [2, 0, 0] [0, 2, 0] rfl 2 (by decide +kernel)

example : List.zipWith (fun x y => x + y) (rowList [0, 2, 0])
      ((rowList [2, 0, 0]).reverse)
    = List.replicate ([2, 0, 0] : Shape).length
      ((degree [2, 0, 0] + degree [0, 2, 0])
        / ([2, 0, 0] : Shape).length) :=
  dualL_join [2, 0, 0] [0, 2, 0] (by decide +kernel)

example : ¬ List.zipWith (fun x y => x + y) (rowList [1, 1, 0])
      ((rowList [2, 0, 0]).reverse) = List.replicate 3 2 := by decide +kernel
example : ¬ reduce [2, 0, 0] = dualL [1, 1, 0] := by decide +kernel

example : List.zipWith (fun x y => x + y) (rowList [1, 0, 0])
    ((rowList [1, 0]).reverse) = List.replicate 2 1 := by decide +kernel
example : ¬ reduce [1, 0] = dualL [1, 0, 0] := by decide +kernel

/-! The dimension at the class, the general theorem's route with
one kernel read beside it. -/

example : weyldim.dimOf ([] : Shape) = weyldim.dimOf (reduce []) :=
  dimOf_class []
example : weyldim.dimOf [1, 2] = weyldim.dimOf (reduce [1, 2]) :=
  dimOf_class [1, 2]
example : weyldim.dimOf [0, 1, 2] = weyldim.dimOf (reduce [0, 1, 2]) :=
  dimOf_class [0, 1, 2]
example : weyldim.dimOf [1, 2] = weyldim.dimOf (reduce [1, 2]) := by decide +kernel

/-! The Casimir read's class invariance, the general theorem's own
instances with one kernel read beside them. -/

example : c2ClassRead [1, 1] := by decide +kernel
example : c2ClassRead [2, 2] := c2Class_all _
example : c2ClassRead [1, 0, 1] := c2Class_all _
example : c2ClassRead [1, 1, 2] := c2Class_all _
example : c2ClassRead [0, 1, 0, 3] := c2Class_all _

/-! The Cartan equality's instances. -/

example : cartanRead [1, 0] [1, 0] := by decide +kernel
example : cartanRead [1, 0] [2, 0] := by decide +kernel
example : cartanRead [1, 0, 0] [1, 1, 0] := by decide +kernel
example : cartanRead [1, 1, 0] [1, 1, 0] := by decide +kernel
example : cartanRead [2, 0, 0] [0, 1, 0] := by decide +kernel

/-! The label count at the reduced target, the shape count's own
read at the matched degrees. -/

example : labels.countL [1, 0] (adjchar.theta 2)
      (labels.reduce [1, 1])
    = steinberg.count [1, 0] (adjchar.theta 2) [1, 1] := by decide +kernel
example : labels.countL (adjchar.theta 3) (adjchar.theta 3)
      (labels.reduce [1, 1, 1])
    = steinberg.count (adjchar.theta 3) (adjchar.theta 3) [1, 1, 1] :=
  by decide +kernel
example : labels.countL [1, 0, 0] (adjchar.theta 3)
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
example : ¬ (labels.countL [0, 0] [0, 0] (labels.reduce [0, 1])
    = steinberg.count [0, 0] [0, 0] [0, 1]) := by decide +kernel
example : labels.countL [1, 0] (adjchar.theta 2)
      (labels.reduce [1, 1, 0])
    = steinberg.count [1, 0] (adjchar.theta 2) [1, 1, 0] := by decide +kernel

/-! The Cartan sharpening's generals: the fusion count at the
column union, the theorem's route beside its kernel value, with
the two tower steps among the pairs — the doubled first
fundamental at the two-letter width and `θ` against `2θ` at the
three — and the unit shape's own pair at the vacant width. -/

example : blockcount.fusionCount [1, 0] [1, 0]
    (places.addS [1, 0] [1, 0]) = 1 := by decide +kernel
example : blockcount.fusionCount [1, 0] [1, 0]
    (places.addS [1, 0] [1, 0]) = 1 :=
  cartan_eq [1, 0] [1, 0] (by decide +kernel)

example : blockcount.fusionCount [2, 0] [4, 0]
    (places.addS [2, 0] [4, 0]) = 1 := by decide +kernel
example : blockcount.fusionCount [2, 0] [4, 0]
    (places.addS [2, 0] [4, 0]) = 1 :=
  cartan_eq [2, 0] [4, 0] (by decide +kernel)

example : blockcount.fusionCount [1, 1, 0] [2, 2, 0]
    (places.addS [1, 1, 0] [2, 2, 0]) = 1 :=
  cartan_eq [1, 1, 0] [2, 2, 0] (by decide +kernel)

example : blockcount.fusionCount ([] : Shape) []
    (places.addS [] []) = 1 :=
  cartan_eq [] [] rfl

example : cartanRead [2, 0] [4, 0] := by decide +kernel
example : cartanRead [2, 0] [4, 0] := cartan_all [2, 0] [4, 0] (by decide +kernel)

example : cartanRead [1, 1, 0] [2, 2, 0] := by decide +kernel
example : cartanRead [1, 1, 0] [2, 2, 0] :=
  cartan_all [1, 1, 0] [2, 2, 0] (by decide +kernel)

example : cartanRead [2, 0, 0] [0, 1, 0] :=
  cartan_all [2, 0, 0] [0, 1, 0] (by decide +kernel)

/-- The stated pair list at the column union is the head pair
alone, the sharpening's cap read at the two-letter width. -/
example : blockcount.pairsAt (blockcount.blockSpan [1, 0])
      (blockcount.blockSpan [1, 0])
      (rowList (places.addS [1, 0] [1, 0]))
    = [blockcount.tensorH (blockcount.exhibit [1, 0])
        (blockcount.exhibit [1, 0])] := by decide +kernel

/-! The width binder `hba`'s isolating refusal, the floor's own
fixture: a wider first shape at a second occupied letter starves
the head pair's guard — the truncated column union misses the
tensor's content — and both the fusion count and the label read
sit off the unit. -/

example : ¬ (([3] : Shape).length = ([1, 2] : Shape).length) := by decide +kernel

example : ¬ (blockcount.fusionCount [1, 2] [3]
    (places.addS [1, 2] [3]) = 1) := by decide +kernel

example : ¬ cartanRead [1, 2] [3] := by decide +kernel

/-! The second argument's width refusal: at a second shape one
letter wider the bumped key is the wider shape's own and the two
counts part, the first and target widths held beside it. -/

example : ¬ (([0, 0, 1] : Shape).length = ([0, 0] : Shape).length) := by
  decide +kernel
example : countL [0, 0]
    (ground.bumpAt (([0, 0, 1] : Shape).length - 1) [0, 0, 1])
    [0, 0] = 1 := by decide +kernel
example : countL [0, 0] [0, 0, 1] [0, 0] = 0 := by decide +kernel

/-! The dual pair's binder refusal: off the dual label the join
misses the constant at the degrees' quotient. -/

example : ¬ (reduce [2, 0] = dualL [1, 0]) := by decide +kernel
example : ¬ (List.zipWith (fun x y => x + y) (rowList [1, 0])
      ((rowList [2, 0]).reverse)
    = List.replicate ([2, 0] : Shape).length
      ((degree [2, 0] + degree [1, 0])
        / ([2, 0] : Shape).length)) := by decide +kernel
