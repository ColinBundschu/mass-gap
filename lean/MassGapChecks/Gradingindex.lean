import MassGap.Gradingindex
import MassGapChecks.Fiberdec
/-!
The third check module for `lem:grading`, the fiber's index: the
torus of side three over two letters at the translation group's nine
composite shifts, the torus of side two over three directions at its
eight, and the plaquette chain of nine squares at its nine steps.
The action lists read as region actions and as groups by kernel, the
group read refused at a two-action list off the composite closure
and the region read at a forged action whose witness is the map
itself; the class list of the two orbits' join is the two
representatives, both free, the join fixed at both shifts
(`fiberdec.idxFixed`, the graded index's tie to the window index),
and the fiber's graded index at the bound thirty-three the loop at
the head with the bowtie at the tail, the loop's place through
`fiberIdx_head_of` and the bowtie's through `fiberIdx_tail_of`; the
head read at the moved loop by kernel and through `headAt_perm` at
the shift's action, the class's read through `classOf_head`, the
cover through `classList_cover` and refused at an action list off
the identity, the disjointness through `classList_disjoint` at the
two classes and refused at the two-action list, where the loop sits
in two classes' orbits, and the free read along the orbit through
`freeB_perm`; the isomorphism binder refused at a constant link map,
the folded configuration a head class at the bound nine against the
loop off it.  At the chain the three loops at the squares nought,
three and six are a class fixed by the shift by three, refusing the
free read while occupied and at content at or beyond twice the
loop's (`lem:fiberdec`'s fixed classes), the class list of the two
orbits' join the two representatives and the fiber's index at the
bound thirty-three the loop alone; the plaquette permutation binder
refused at the chain with one plaquette listed, where the shift
keeps the links and the vertices with the plaquette read holding,
the moved loop's head read differs, and the identity permutation
refuses the cyclic clause; the head's price through `comp_floor`
and `head_floor` at the loop's one component; and the closures'
class reads at the chain's supports by kernel and through the
theorems.

The binder classification.  `headAt_perm`'s `h` (the isomorphism
read) and `hpm` (the plaquette permutation read) are load-bearing
with their committed refusals (`pin173`, `pin179`); `hw` and `hpr`
are `con:lattice`'s region frame.  `classList_cover`'s `hid` (the
identity among the actions) is load-bearing with its refusal
(`pin185`); `hlen` is `def:carrier`'s configuration width.
`classList_disjoint`'s group read is load-bearing with its refusal
(`pin162`, `pin172`), `hacts` the action list's region read at the
witnesses the proof reads, `hlen` and `hix` `def:carrier`'s width
and label domain, and `hred` `con:labels`' one reduced shape per
label, discharged at the label calculus by `fusion.eqL_labelA`;
`freeB_perm`'s and `classOf_head`'s binders are those.
`comp_floor`'s `hlab` is `def:carrier`'s label domain and `hfl` the
window's floor read (`fusion.belowFloor`, `lem:casfloor`), both
decided at the label calculus.  The closures' class reads
(`closure_sat`, `closure_symm`, `compOf_eq_of_mem`, `compOf_drop`,
`components_compOf`, `compOf_mem_components`, `components_disjoint`)
take the support's own reads, the member's place, the distinct keys
and the count at or below the region's links, each read in the
proof.
-/

namespace grading
set_option maxHeartbeats 4000000

open ground lattice fusion

private def tor : Region := fiberdec.torusRegion 2 3
private def FA2 : Data places.Shape := dataA 2
private def plq (s : Nat) : List (Nat × Bool) := ground.getAt [] tor.plaqs s
private def thB : places.Shape := adjchar.theta 2
private def loopT : List places.Shape :=
  (List.range tor.links).map (fun l => if (plq 0).any (fun e => e.1 == l) then thB else [0, 0])
private def bowT : List places.Shape :=
  (List.range tor.links).map (fun l =>
    if (plq 0).any (fun e => e.1 == l) || (plq 8).any (fun e => e.1 == l) then thB else [0, 0])
private def actsT : List Act := torusActs 2 3
private def ixT : List (List places.Shape) :=
  orbitOf FA2 18 actsT loopT ++ orbitOf FA2 18 actsT bowT
private def acts2 : List Act := [torusAct 2 3 [0, 0], torusAct 2 3 [1, 0]]
private def acts1 : List Act := [torusAct 2 3 [1, 0]]
private def forged : Act := { torusAct 2 3 [1, 0] with s := fiberdec.compShift 2 3 [1, 0] }
private def A10 : Act := torusAct 2 3 [1, 0]
private def loopT' : List places.Shape := pairpencil.permConf FA2 A10.t A10.s 18 loopT

/-! The action lists: region actions and groups by kernel, the group
read refused at the two-action list and the region read at the
forged witness; the torus of side two over three directions, the
plaquette permutation's site split at three pairs per site. -/

theorem pin160 : regionActs tor actsT := by decide +kernel
theorem pin161 : groupRead 18 actsT := by decide +kernel
theorem pin162 : ¬ groupRead 18 acts2 := by decide +kernel
theorem pin163 : ¬ regionAct tor forged := by decide +kernel
theorem pin185 : ¬ idAmong 18 acts1 = true := by decide +kernel
theorem pin186 : regionActs (fiberdec.torusRegion 3 2) (torusActs 3 2)
    ∧ groupRead 24 (torusActs 3 2) := by decide +kernel

/-! The class list at the two orbits' join, both classes free, the
join fixed at both shifts, and the fiber's graded index at the bound
thirty-three, the two places through the theorems. -/

theorem pin164 : classList FA2 18 actsT ixT = [loopT, bowT] := by decide +kernel
theorem pin165 : freeB FA2 18 actsT loopT = true ∧ freeB FA2 18 actsT bowT = true := by
  decide +kernel
theorem pin166 : fiberdec.idxFixed FA2 tor ixT (fiberdec.torusTransl 2 3 0)
      (fiberdec.torusTranslInv 2 3 0)
    ∧ fiberdec.idxFixed FA2 tor ixT (fiberdec.torusTransl 2 3 1)
      (fiberdec.torusTranslInv 2 3 1) := by decide +kernel
theorem pin167 : fiberIdx FA2 tor 33 actsT ixT = ([loopT], [bowT]) := by decide +kernel

private theorem torWell : wellRead tor := by decide +kernel
private theorem torPlaq : plaqRead tor := by decide +kernel
private theorem actA10 : regionAct tor A10 := by decide +kernel
private theorem loopHead : headAt FA2 tor 33 loopT := by decide +kernel
private theorem bowTail : ¬ headAt FA2 tor 33 bowT := by decide +kernel
private theorem loopClass : loopT ∈ classList FA2 18 actsT ixT :=
  mem_of_containsB (by decide +kernel)
private theorem bowClass : bowT ∈ classList FA2 18 actsT ixT :=
  mem_of_containsB (by decide +kernel)
private theorem ixLen : ∀ a ∈ ixT, a.length = 18 := fun a ha =>
  beqEqOf (all_of_mem _ _ (by decide +kernel : (ixT.all (fun a => a.length == 18)) = true) a ha)
private theorem ixLab : ∀ a ∈ ixT, a.all (labelA 2) = true := fun a ha =>
  all_of_mem _ _ (by decide +kernel : (ixT.all (fun a => a.all (labelA 2))) = true) a ha

theorem pin187 : loopT ∈ (fiberIdx FA2 tor 33 actsT ixT).1 :=
  fiberIdx_head_of FA2 tor 33 actsT ixT loopT loopClass pin165.1 loopHead
theorem pin188 : bowT ∈ (fiberIdx FA2 tor 33 actsT ixT).2 :=
  fiberIdx_tail_of FA2 tor 33 actsT ixT bowT bowClass pin165.2 bowTail

/-! The head read at the moved loop by kernel and through the
theorem at the shift's action, the class's read through the class
theorem, the cover through its theorem, and the free read along the
orbit. -/

theorem pin168 : headAt FA2 tor 33 loopT' := by decide +kernel
theorem pin169 : headAt FA2 tor 33 loopT' :=
  (headAt_perm FA2 tor torWell torPlaq A10.t A10.s A10.v A10.w A10.pm A10.pm'
    actA10.1 actA10.2 33 loopT).2 loopHead
theorem pin170 : headAt FA2 tor 33 loopT' :=
  (classOf_head FA2 tor torWell torPlaq actsT pin160 (labelA 2) (labelA_unit 2)
    (eqL_labelA 2) 33 loopT' loopT (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2 loopHead
theorem pin171 : ∃ c, c ∈ classList FA2 18 actsT ixT ∧ inOrbit FA2 18 actsT loopT' c = true :=
  classList_cover FA2 18 actsT (andSplitB (andSplitB pin161).1).1 ixT ixLen loopT'
    (mem_of_containsB (by decide +kernel))
theorem pin189 : freeB FA2 18 actsT loopT' = freeB FA2 18 actsT loopT :=
  freeB_perm FA2 tor actsT pin160 pin161 (labelA 2) (labelA_unit 2) (eqL_labelA 2)
    A10 (mem_map_to (torusAct 2 3) (mem_of_containsB (by decide +kernel)))
    loopT (by decide +kernel) (by decide +kernel)
theorem pin190 : freeB FA2 18 actsT loopT' = true := by decide +kernel

/-! The disjointness through the theorem at the two classes, and
refused at the two-action list, where the loop sits in two classes'
orbits. -/

theorem pin191 : ¬ (inOrbit FA2 18 actsT loopT bowT = true
    ∧ inOrbit FA2 18 actsT loopT loopT = true) := fun h =>
  classList_disjoint FA2 tor actsT pin160 pin161 (labelA 2) (labelA_unit 2) (eqL_labelA 2)
    ixT ixLen ixLab 0 1 (by decide) (by decide +kernel) loopT (by decide +kernel)
    (by
      show inOrbit FA2 18 actsT loopT (ground.getAt [] (classList FA2 18 actsT ixT) 0) = true
      rw [pin164]
      exact h.2)
    (by
      show inOrbit FA2 18 actsT loopT (ground.getAt [] (classList FA2 18 actsT ixT) 1) = true
      rw [pin164]
      exact h.1)
private def ixT0 : List (List places.Shape) := orbitOf FA2 18 actsT loopT
theorem pin172 : (classList FA2 18 acts2 ixT0).length = 6
    ∧ inOrbit FA2 18 acts2 loopT (ground.getAt [] (classList FA2 18 acts2 ixT0) 0) = true
    ∧ inOrbit FA2 18 acts2 loopT (ground.getAt [] (classList FA2 18 acts2 ixT0) 3) = true := by
  decide +kernel

/-! The isomorphism binder refused at a constant link map: the folded
loop reads one link, a head class at the bound nine against the loop
off it. -/

private def badT : List places.Shape :=
  pairpencil.permConf FA2 (fun _ => 0) (fun l => l) 18 loopT
theorem pin173 : headAt FA2 tor 9 badT ∧ ¬ headAt FA2 tor 9 loopT
    ∧ ¬ isoRead tor tor (fun _ => 0) (fun l => l) (fun x => x) (fun x => x)
      (fun _ => false) := by decide +kernel

/-! The chain of nine squares: the actions at the steps, the class
fixed by the shift by three refusing the free read at content at or
beyond twice the loop's, the class list and the fiber's index. -/

private def R9 : Region := fiberdec.chainRegion 9
private def FA3 : Data places.Shape := dataA 3
private def three : List places.Shape :=
  stableentries.joinConf FA3 R9 (fiberdec.loopAt 9 0)
    (stableentries.joinConf FA3 R9 (fiberdec.loopAt 9 3) (fiberdec.loopAt 9 6))
private def actsC : List Act := chainActs 9
private def ix9 : List (List places.Shape) :=
  orbitOf FA3 27 actsC (fiberdec.loopAt 9 0) ++ orbitOf FA3 27 actsC three

theorem pin174 : regionActs R9 actsC := by decide +kernel
theorem pin175 : groupRead 27 actsC := by decide +kernel
theorem pin176 : freeB FA3 27 actsC three = false
    ∧ freeB FA3 27 actsC (fiberdec.loopAt 9 0) = true
    ∧ carrier.occupied FA3 R9 three = true
    ∧ 2 * carrier.contentN FA3 (fiberdec.loopAt 9 0) ≤ carrier.contentN FA3 three := by
  decide +kernel
theorem pin177 : classList FA3 27 actsC ix9 = [fiberdec.loopAt 9 0, three] := by
  decide +kernel
theorem pin178 : fiberIdx FA3 R9 33 actsC ix9 = ([fiberdec.loopAt 9 0], []) := by
  decide +kernel

/-! The plaquette permutation binder refused: the chain with one
plaquette listed keeps its links and vertices under the shift, so
the isomorphism read holds and the plaquette read holds, while the
moved loop's components split and its head read differs at the
bound thirty-three; the identity permutation refuses the cyclic
clause, the moved word off the one listed plaquette. -/

private def R1 : Region := { R9 with plaqs := [ground.getAt [] R9.plaqs 0] }
private def sh1 : List places.Shape :=
  pairpencil.permConf FA3 (fiberdec.chainTransl 9) (fiberdec.chainTranslInv 9) 27
    (fiberdec.loopAt 9 0)
theorem pin179 : headAt FA3 R1 33 (fiberdec.loopAt 9 0) ∧ ¬ headAt FA3 R1 33 sh1
    ∧ wellRead R1 ∧ plaqRead R1
    ∧ isoRead R1 R1 (fiberdec.chainTransl 9) (fiberdec.chainTranslInv 9)
      (fiberdec.chainVert 9) (fiberdec.chainVertInv 9) (fun _ => false)
    ∧ ¬ plaqPermRead R1 (fiberdec.chainTransl 9) (fun _ => false)
      (fun q => q) (fun q => q)
    ∧ ¬ cycEq (moveWord (fiberdec.chainTransl 9) (fun _ => false)
      (ground.getAt [] R1.plaqs 0)) (ground.getAt [] R1.plaqs 0) = true := by
  decide +kernel

/-! The head's price at the loop's one component through the two
theorems, the label domain and the floor decided at the label
calculus. -/

private theorem loopLab : (loopT.all (fun l => containsB (FA2.unit :: FA2.below 40) l)) = true := by
  decide +kernel
private theorem floor40 : belowFloor FA2 40 3 := by decide +kernel
private theorem loopComp : ground.getAt [] (components FA2 tor loopT) 0 ∈ components FA2 tor loopT :=
  mem_getAt [] _ 0 (by decide +kernel)

theorem pin180 : (ground.getAt [] (components FA2 tor loopT) 0).length * 3
    ≤ compContent FA2 loopT (ground.getAt [] (components FA2 tor loopT) 0) :=
  comp_floor FA2 tor loopT (by decide +kernel) 40 3
    (fun l hl => mem_of_containsB (all_of_mem _ _ loopLab l hl)) floor40 _ loopComp
theorem pin181 : (ground.getAt [] (components FA2 tor loopT) 0).length * 3 < 33 :=
  head_floor FA2 tor loopT (by decide +kernel) 40 3 33
    (fun l hl => mem_of_containsB (all_of_mem _ _ loopLab l hl)) floor40 loopHead _ loopComp
theorem pin182 : (ground.getAt [] (components FA2 tor loopT) 0).length * 3 = 12
    ∧ compContent FA2 loopT (ground.getAt [] (components FA2 tor loopT) 0) = 32 := by
  decide +kernel

/-! The closures as classes at the chain's supports by kernel and
through the theorems: two members of one component read one
component, the second loop's component within the support past the
first's is its own, the parts are the members' components, and two
parts at distinct places are disjoint. -/

private def two : List places.Shape :=
  stableentries.joinConf FA3 R9 (fiberdec.loopAt 9 0) (fiberdec.loopAt 9 4)
private def S2 : List Nat := carrier.support FA3 R9 two
private theorem S2dist : distinctList S2 := carrier.support_distinct FA3 R9 two
private theorem S2len : S2.length ≤ R9.links := by decide +kernel
private theorem mem0 : 0 ∈ S2 := mem_of_containsB (by decide +kernel)
private theorem mem4 : 4 ∈ S2 := mem_of_containsB (by decide +kernel)
theorem pin183 : compOf R9 S2 1 = compOf R9 S2 0
    ∧ compOf R9 (S2.filter (fun x => !(containsB (compOf R9 S2 0) x))) 4 = compOf R9 S2 4
    ∧ components FA3 R9 two = [compOf R9 S2 0, compOf R9 S2 4] := by decide +kernel
theorem pin184 : compOf R9 S2 1 = compOf R9 S2 0 :=
  compOf_eq_of_mem R9 S2 0 1 mem0 S2dist S2len (mem_of_containsB (by decide +kernel))
theorem pin192 : compOf R9 (S2.filter (fun x => !(containsB (compOf R9 S2 0) x))) 4
    = compOf R9 S2 4 :=
  compOf_drop R9 S2 0 4 mem0 S2dist S2len mem4 (fun h => by
    have h2 := containsB_of_mem h
    rw [show containsB (compOf R9 S2 0) 4 = false by decide +kernel] at h2
    exact Bool.noConfusion h2)
theorem pin193 : containsB (closure R9 S2 0) 1 = true ∧ containsB (closure R9 S2 1) 0 = true := by
  decide +kernel
theorem pin194 : 0 ∈ closure R9 S2 1 :=
  closure_symm R9 S2 0 1 mem0 S2dist S2len (mem_of_containsB (by decide +kernel))
theorem pin195 : 9 ∈ closure R9 S2 0 :=
  closure_sat R9 S2 0 mem0 S2dist S2len 0 9 (mem_closure_self R9 S2 0)
    (mem_of_containsB (by decide +kernel)) (by decide +kernel)
theorem pin196 : ∃ l, l ∈ compOf R9 S2 4 ∧ compOf R9 S2 4 = compOf R9 S2 l :=
  components_compOf FA3 R9 two _ (mem_of_containsB (by decide +kernel))
theorem pin197 : ∃ c, c ∈ components FA3 R9 two ∧ c = compOf R9 S2 4 :=
  compOf_mem_components FA3 R9 two 4 mem4
theorem pin198 : ¬ (0 ∈ ground.getAt [] (components FA3 R9 two) 1) := fun h =>
  components_disjoint FA3 R9 two 0 1 (by decide) (by decide +kernel) 0
    (mem_of_containsB (by decide +kernel)) h

end grading
