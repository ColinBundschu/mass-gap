import MassGap.Carrier
/-!
The check module for `def:carrier`: the batteries re-read the
index layer by kernel `decide` at the label calculus's
instantiation — the invariant count's row fold (the unit's one,
the single nonunit label's refusal, the pair at the dual, the
adjoint triple at the base `c₁`), the content fold, the vertex
multiplicities at the square's corners, the occupied reads (the
fundamental loop occupied, the single link and the all-`f` theta
assignment refused — the degree-one endpoint and the odd parity),
and the window index's members at stated cutoffs.
-/

namespace carrier
set_option maxHeartbeats 4000000

open ground places lattice fusion

/-! The invariant count's row fold. -/

theorem pin1 : invCount (dataA 2) [] = 1 := by decide +kernel
theorem pin2 : invCount (dataA 2) [[1, 0]] = 0 := by decide +kernel
theorem pin3 : invCount (dataA 2) [[1, 0], [1, 0]] = 1 := by decide +kernel
theorem pin4 : invCount (dataA 3) [[1, 0, 0], [0, 1, 0]] = 1 := by decide +kernel
theorem pin5 : invCount (dataA 3) [[1, 0, 0], [1, 0, 0]] = 0 := by decide +kernel
theorem pin6 : invCount (dataA 3) [[1, 0, 0], [1, 0, 0], [1, 0, 0]] = 1 := by
  decide +kernel
theorem pin7 : invCount (dataA 3) [[1, 1, 0], [1, 1, 0], [1, 1, 0]] = 2 := by
  decide +kernel
theorem pin8 : invCount (dataA 3) [[1, 1, 0], [1, 1, 0], [1, 1, 0]]
    = (dataA 3).c1 := by decide +kernel

/-! The content fold at the cleared second member. -/

theorem pin9 : contentN (dataA 2) [[1, 0], [1, 0], [1, 0], [1, 0]] = 12 := by
  decide +kernel
theorem pin10 : contentN (dataA 2) [[1, 0], [0, 0], [2, 0], [0, 0]] = 11 := by
  decide +kernel

/-! The vertex multiplicities and the occupied reads at the
square: the fundamental loop occupied at every corner's unit
multiplicity, the single link refused at its degree-one ends. -/

theorem pin11 : vmult (dataA 2) square [[1, 0], [1, 0], [1, 0], [1, 0]] 0
    = 1 := by decide +kernel
theorem pin12 : occupied (dataA 2) square [[1, 0], [1, 0], [1, 0], [1, 0]]
    = true := by decide +kernel
theorem pin13 : occupied (dataA 2) square [[1, 0], [0, 0], [0, 0], [0, 0]]
    = false := by decide +kernel
theorem pin14 : occupied (dataA 2) square
    [[2, 0], [2, 0], [2, 0], [2, 0]] = true := by decide +kernel

/-! The incoming dualization at three letters: the constant
fundamental loop occupied (each corner `f` against the incoming
dual's dual), the alternating `f`, `f̄` assignment refused at the
corners' matched pair. -/

theorem pin15 : occupied (dataA 3) square
    [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]] = true := by decide +kernel
theorem pin16 : occupied (dataA 3) square
    [[1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 1, 0]] = false := by decide +kernel

/-! The all-`f` theta assignment refused at the shared ends' odd
parity. -/

theorem pin17 : occupied (tabulate (dataA 2) 3) thetaG
    [[1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 0]]
    = false := by decide +kernel

/-! The window index's members at stated cutoffs: the fundamental
loop alone below the next label's loop. -/

theorem pin18 : (idx (dataA 2) square 12).length = 1 := by
  rw [← idxA_eq]; decide +kernel
theorem pin19 : (idx (dataA 2) square 32).length = 2 := by
  rw [← idxA_eq]; decide +kernel

/-! The pruned walk reads the enumeration itself
(`prop:windowfinite`'s per-link cutoff read, `idxA_eq`), pinned at
the committed windows and at a window where the refusal bites at
depth. -/

theorem pin20 : idxA (dataA 2) square 12
    = idx (dataA 2) square 12 := by decide +kernel
theorem pin21 : idxA (tabulate (dataA 2) 12) thetaG 12
    = idx (tabulate (dataA 2) 12) thetaG 12 := by decide +kernel

/-! The tabulated route's coherence with the interface at stated
reads. -/

theorem pin22 : (tabulate (dataA 2) 12).count [1, 0] [1, 0] [2, 0]
    = (dataA 2).count [1, 0] [1, 0] [2, 0] := by decide +kernel
theorem pin23 : (tabulate (dataA 2) 12).count [1, 0] [1, 0] (labels.unitL 2)
    = (dataA 2).count [1, 0] [1, 0] (labels.unitL 2) := by decide +kernel
theorem pin24 : (tabulate (dataA 2) 12).row [1, 0] [1, 0]
    = (dataA 2).row [1, 0] [1, 0] := by decide +kernel

/-! The committed window enumerations, the tier's shared fixtures:
each a stated value of `def:carrier`'s index at a committed window,
its pin `prop:windowfinite`'s content-pruned walk (`idxA_eq`), the
consuming modules' reads the named displays' applications. -/


/-- The square window at two letters, cutoff 32: the fundamental
loop with the two-box loop. -/
def sqIx2 : List (List places.Shape) :=
  [[[1, 0], [1, 0], [1, 0], [1, 0]],
   [[2, 0], [2, 0], [2, 0], [2, 0]]]

theorem sqIx2_pin : idx (dataA 2) square 32 = sqIx2 := by
  rw [← idxA_eq]; decide +kernel

/-! The index's two membership reads at the pinned window: a member
reads the five data (`idx_sound`) and the data read the membership
back (`mem_idx`), each decided beside its route, with the refusal
at a configuration off the index — the two-box loop, occupied at
every vertex but beyond the cutoff twelve. -/

private def sqLoop2 : List places.Shape := [[2, 0], [2, 0], [2, 0], [2, 0]]
private def sqLoop1 : List places.Shape := [[1, 0], [1, 0], [1, 0], [1, 0]]

private theorem sqLoop2_mem : sqLoop2 ∈ idx (dataA 2) square 32 := by
  rw [sqIx2_pin]
  exact List.Mem.tail _ (List.Mem.head _)

theorem pin25 : sqLoop2.length = square.links
    ∧ contentN (dataA 2) sqLoop2 ≤ 32
    ∧ occupied (dataA 2) square sqLoop2 = true :=
  let h := idx_sound (dataA 2) square 32 sqLoop2 sqLoop2_mem
  ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
theorem pin26 : sqLoop2.length = square.links
    ∧ contentN (dataA 2) sqLoop2 ≤ 32
    ∧ occupied (dataA 2) square sqLoop2 = true := by decide +kernel
theorem pin27 : sqLoop1 ∈ idx (dataA 2) square 32 :=
  mem_idx (dataA 2) square 32 sqLoop1 rfl
    (fun l hl => by
      have hall : (sqLoop1.all (fun x =>
            ((dataA 2).unit :: (dataA 2).below 32).any
              (fun m => m == x))) = true := by
        decide +kernel
      obtain ⟨m, hm, hml⟩ :=
        ground.mem_of_any _ _ (ground.all_of_mem _ _ hall l hl)
      rw [← ground.listBeqEq hml]
      exact hm)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin28 : ground.countOf sqLoop2 (idx (dataA 2) square 12) = 0 := by
  rw [← idxA_eq]
  decide +kernel
theorem pin29 : confMem (dataA 2) sqLoop2 sqIx2 = true :=
  confMem_of_mem (dataA 2) sqLoop2 sqIx2 (List.Mem.tail _ (List.Mem.head _))
theorem pin30 : confMem (dataA 2) sqLoop2 sqIx2 = true := by decide +kernel
theorem pin31 : eqConf (dataA 2) sqLoop1 sqLoop1 = true := eqConf_refl (dataA 2) _

/-! The index is distinct at the distinct label carrier, decided
beside its route, and the equality read is structural on the
labels at the calculus. -/

theorem pin32 : ground.distinctList sqIx2 := by decide +kernel
theorem pin33 : ground.distinctList (idx (dataA 2) square 32) :=
  idx_distinct (dataA 2) square 32 (below_distinct_dataA 2 32)
theorem pin34 : eqConf (dataA 2) sqLoop1 [[1, 0], [1, 0], [1, 0], [1, 0]] = true
    → sqLoop1 = [[1, 0], [1, 0], [1, 0], [1, 0]] :=
  eqConf_labelA 2 sqLoop1 _ (by decide +kernel) (by decide +kernel)

/-- The square window at three letters, cutoff 32: the fundamental
loop with the anti-fundamental's. -/
def sqIx3 : List (List places.Shape) :=
  [[[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]],
   [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]]

theorem sqIx3_pin : idx (dataA 3) square 32 = sqIx3 := by
  rw [← idxA_eq]; decide +kernel

/-- The theta window at two letters, cutoff 18: the two plaquette
loops with the hexagon. -/
def thIx18 : List (List places.Shape) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [1, 0]],
   [[1, 0], [1, 0], [1, 0], [0, 0], [1, 0], [1, 0], [1, 0]],
   [[1, 0], [1, 0], [1, 0], [1, 0], [0, 0], [0, 0], [0, 0]]]

theorem thIx18_pin :
    idx (tabulate (dataA 2) 18) thetaG 18 = thIx18 := by
  rw [← idxA_eq]; decide +kernel

/-- The theta window at two letters, cutoff 12: the two plaquette
loops, the hexagon beyond the cutoff. -/
def thIx12 : List (List places.Shape) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [1, 0]],
   [[1, 0], [1, 0], [1, 0], [1, 0], [0, 0], [0, 0], [0, 0]]]

theorem thIx12_pin :
    idx (tabulate (dataA 2) 12) thetaG 12 = thIx12 := by
  rw [← idxA_eq]; decide +kernel

/-- The theta window at two letters, cutoff 26: the two plaquette
loops, the hexagon, and the join at the adjoint on the shared link
with the fundamental on the six further links, its two trivalent
vertices at one member each. -/
def thIx26 : List (List places.Shape) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [1, 0]],
   [[1, 0], [1, 0], [1, 0], [0, 0], [1, 0], [1, 0], [1, 0]],
   [[1, 0], [1, 0], [1, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [1, 0], [1, 0], [2, 0], [1, 0], [1, 0], [1, 0]]]

theorem thIx26_pin : idx (dataA 2) thetaG 26 = thIx26 := by
  rw [← idxA_eq]; decide +kernel

/-! The window index nests (`thm:truncation`'s projection as the
index): the square's index at the cutoff twelve is the index at
thirty-two filtered at content at or below twelve, through the
theorem at the `A`-series' enumeration laws, the two lists decided
at the pruned read; and the refusal at a forged enumeration whose
larger cutoff lists the adjoint alone, the nesting law bitten. -/

theorem pin35 : idx (dataA 2) square 12
    = (idx (dataA 2) square 32).filter (fun a => decide (contentN (dataA 2) a ≤ 12)) :=
  idx_filter (dataA 2) square 12 32 (by decide) (belowNest_dataA 2 12 32 (by decide))
    (belowNonunit_dataA 2 32)
theorem pin36 : idx (dataA 2) square 12 = [[[1, 0], [1, 0], [1, 0], [1, 0]]] := by
  rw [← idxA_eq]; decide +kernel
theorem pin37 : ¬ (idx { dataA 2 with
      below := fun C => if C == 32 then [[2, 0]] else (dataA 2).below C } square 12
    = (idx { dataA 2 with
      below := fun C => if C == 32 then [[2, 0]] else (dataA 2).below C } square 32).filter
        (fun a => decide (contentN (dataA 2) a ≤ 12))) := by
  rw [← idxA_eq, ← idxA_eq]; decide +kernel

/-! The two further binders bitten: at an enumeration constant
across the cutoffs the nesting and nonunit laws hold at the reversed
cutoff pair while the index at twelve holds the fundamental loop and
the index at three is vacant; and at the theta window with the unit
label joined to the larger cutoff's enumeration at a Casimir beyond
the smaller cutoff, the nesting law holds, the nonunit law refuses,
and the larger index lists each loop at every unit spelling of its
vacant links, eighteen members against two. -/

private def fConst : Data places.Shape := { dataA 2 with below := fun _ => [[1, 0]] }
private def fUnit : Data places.Shape := { tabulate (dataA 2) 18 with
  below := fun C => if C == 18 then (dataA 2).unit :: (tabulate (dataA 2) 18).below 18
    else (tabulate (dataA 2) 18).below C,
  c2N := fun l => if l == (dataA 2).unit then 50 else c2hat.dfQ l }

theorem pin38 : belowNest fConst 12 3 ∧ belowNonunit fConst 3
    ∧ ¬ (idx fConst square 12
      = (idx fConst square 3).filter (fun a => decide (contentN fConst a ≤ 12))) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [← idxA_eq, ← idxA_eq]; decide +kernel
theorem pin39 : belowNest fUnit 12 18 ∧ ¬ belowNonunit fUnit 18
    ∧ (idxA fUnit thetaG 18).length = 18 ∧ (idxA fUnit thetaG 12).length = 2
    ∧ ¬ (idx fUnit thetaG 12
      = (idx fUnit thetaG 18).filter (fun a => decide (contentN fUnit a ≤ 12))) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rw [← idxA_eq, ← idxA_eq]; decide +kernel


end carrier
