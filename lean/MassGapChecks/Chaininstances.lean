import MassGap.Chaininstances
import MassGap.Contactcell
/-!
The check module for `lem:chaininstances`: the battery reads the
whole record list by kernel `decide` — the count 29, the clearance
column, the isolated reads' count, the seven gap identities
`d_f Q(λ)` at `rankstable.casPoly` against the displayed products,
the cap's identity with the dimension polynomials, the three merged
levels at the sum's unit, and both
certificates at every further record, the settled side's radius
clearance with its leading side and the window below the clearance.
The seven families are the depth-two closure: at the count five the
unit label's reach at two steps under the fundamental pair over the
window at the cutoff 56 is the unit and the seven members in the
reach's order (`con:depthchain` at `depthchain.reach`); the gap
identity meets `def:c2hat` through `rankstable.casPoly_eval` at the
square's member; and the stencil cap reads three times the dimension
fold ten at the count five.  The classification's rows read one at
a time: the eight isolated reads at their stated ranks, the second
fundamentals' gaps and the six comparisons each evaluating at equal
members, and the three merged levels.  The refusals isolate one committed datum each: the gap's
witness, at the fundamental's row at `w := 2`, where the
identity parts with `rankstable.casPoly`; the root list's
completeness, at the comparison `(ω₁, ω₂)` with its root withdrawn
and again with the rank four forged onto it, and a listed rank off
the window; the clearance, lowered to two at the comparison
`(ω₁, ω₂)`, asking the leading side of a rank on the divisor's
other side; the clearance column, at the fundamental's word with a
trailing vacant key; the settled point, at the comparison
`(ω₁, 2ω₁)` of radius four read at three; the domain floor, the
fundamental's gap tying the sum's unit at the rank one, off the
counts; and the merged read's own binder, a dual pair's comparison
refusing the settled side while reading the sum's unit at every key,
where an unmerged comparison refuses the merged read.
-/

namespace chaininstances
open ground

/-- The rank-`k` pair, the balance carrier's own read of the count. -/
private def rk (k : Nat) : BPair := ⟨posOfSucc k, posOfSucc 0⟩

/-- A family's excess gap at its place. -/
private def gd (i : Nat) : poly.Poly := gapOf (famAt i)

/-! The whole read: the record count, the gap identities, the merged
levels and both certificates over the 29 records. -/

theorem pin1 : recsRead := by decide +kernel

/-! The seven families are the depth-two closure under the
fundamental pair at the count five: the reach at two steps from the
unit over the window at the cutoff 56, in the reach's order, is the
unit and the seven members. -/

def F5 : fusion.Data (List Nat) := fusion.dataA 5
def f5 : List Nat := [1, 0, 0, 0, 0]
def win5 : List (List Nat) := contactcell.winIdx F5 56
def closure5 : List (List Nat) :=
  (depthchain.reach [fpcap.closureMat F5 [] [f5] win5] (contactcell.singles win5.length)
    win5.length [0] 2).map (fun i => getAt F5.unit win5 i)

theorem pin2 : closure5 = [F5.unit, rankstable.member [1] [] 5, rankstable.member [2] [] 5,
    rankstable.member [0, 1] [] 5, rankstable.member [] [0, 1] 5, rankstable.member [] [1] 5,
    rankstable.member [1] [1] 5, rankstable.member [] [2] 5] := by decide +kernel

/-! The gap identity meets `def:c2hat`: the square's displayed
product at the count five reads the member's cleared Casimir, the
route through `rankstable.casPoly_eval` beside the decided value. -/

theorem pin3 : (poly.eval (gd 2) (BPair.ofNat 5)).oneValue
    (BPair.ofNat (c2hat.dfQ (rankstable.member [2] [] 5))) :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (poly.eval_congr (show gapRead (famAt 2) by decide +kernel) _))
    (rankstable.casPoly_eval [2] [] 5 (by decide))
theorem pin4 : c2hat.dfQ (rankstable.member [2] [] 5) = 56 := by decide +kernel

/-! The stencil cap at the count five: three times the fundamental
pair's dimension fold ten, the fundamental's dimension polynomial
reading its dimension five through `rankstable.dimPair_eval`. -/

theorem pin5 : (poly.eval (rankstable.dimNum [1] []) (BPair.ofNat 5)).oneValue
    (BPair.ofNat (weyldim.dimOf (rankstable.member [1] [] 5))
      * poly.eval (rankstable.dimDen [1] []) (BPair.ofNat 5)) :=
  rankstable.dimPair_eval [1] [] 5 (by decide)
theorem pin6 : weyldim.dimOf (rankstable.member [1] [] 5) = 5 := by decide +kernel

theorem pin7 : fpcap.dimFold F5 [] [f5] = 10 := by decide +kernel
theorem pin8 : (poly.eval capPoly (rk 5)).oneValue (BPair.ofNat (3 * fpcap.dimFold F5 [] [f5])) := by
  decide +kernel

/-! The classification's eight isolated reads at their ranks, the
second fundamentals' gaps at the rank two first, and the three
merged levels. -/

theorem pin9 : (poly.eval (gd 4) (rk 2)).oneValue BPair.unit := by decide +kernel
theorem pin10 : (poly.eval (gd 5) (rk 2)).oneValue BPair.unit := by decide +kernel
theorem pin11 : (poly.eval (compAt 2 6) (rk 2)).oneValue BPair.unit := by decide +kernel
theorem pin12 : (poly.eval (compAt 3 6) (rk 2)).oneValue BPair.unit := by decide +kernel
theorem pin13 : (poly.eval (compAt 0 4) (rk 3)).oneValue BPair.unit := by decide +kernel
theorem pin14 : (poly.eval (compAt 0 5) (rk 3)).oneValue BPair.unit := by decide +kernel
theorem pin15 : (poly.eval (compAt 1 4) (rk 3)).oneValue BPair.unit := by decide +kernel
theorem pin16 : (poly.eval (compAt 1 5) (rk 3)).oneValue BPair.unit := by decide +kernel
theorem pin17 : poly.unitTail (compAt 0 1) := by decide +kernel
theorem pin18 : poly.unitTail (compAt 2 3) := by decide +kernel
theorem pin19 : poly.unitTail (compAt 4 5) := by decide +kernel

/-! The gap witness's refusal: the fundamental's row at the forged
witness `w := 2`, the gap `(n + 1) g` at `2 + g = n`, parts with the
Casimir polynomial. -/

theorem pin20 : ¬ gapRead ⟨[1], [], 1, 1, 2⟩ := by decide +kernel

/-! The clearance column's refusal: the fundamental's word at a
trailing vacant key reads the gap identity and the member at the
count five alike, and its clearance five parts from the column's
four. -/

theorem pin21 : gapRead ⟨[1, 0], [], 1, 1, 1⟩ := by decide +kernel
theorem pin22 : rankstable.member [1, 0] [] 5 = rankstable.member [1] [] 5 := by decide +kernel
theorem pin23 : ¬ ((fams.map clearanceOf).set 0 (clearanceOf ⟨[1, 0], [], 1, 1, 1⟩)
    = [4, 4, 4, 4, 5, 5, 5]) := by decide +kernel

/-! The root list's refusals at the comparison `(ω₁, ω₂)`, settled
at five: the rank three's withdrawal leaves an equal-members read
uncounted, and the rank four forged onto the list counts a rank
whose evaluation sits off the sum's unit. -/

theorem pin24 : ¬ genericlift.rootsCert ⟨compAt 0 4, 2, 5, 5, []⟩ := by decide +kernel
theorem pin25 : ¬ genericlift.rootsCert ⟨compAt 0 4, 2, 5, 5, [3, 4]⟩ := by decide +kernel
theorem pin26 : genericlift.rootsCert ⟨compAt 0 4, 2, 5, 5, [3]⟩ := by decide +kernel

/-! The root list's window: a listed rank at or beyond the settled
point, below the floor, or listed twice refuses. -/

theorem pin27 : ¬ genericlift.rootsCert ⟨compAt 0 4, 2, 5, 5, [3, 9]⟩ := by decide +kernel
theorem pin28 : ¬ genericlift.rootsCert ⟨compAt 0 4, 2, 5, 5, [3, 0]⟩ := by decide +kernel
theorem pin29 : ¬ genericlift.rootsCert ⟨compAt 0 4, 2, 5, 5, [3, 3]⟩ := by decide +kernel

/-! The clearance's refusal at the comparison `(ω₁, ω₂)`: lowered to two
it asks the leading side of the rank two, which sits on the
divisor's other side below the crossing. -/

theorem pin30 : ¬ genericlift.rootsCert ⟨compAt 0 4, 2, 2, 5, [3]⟩ := by decide +kernel

/-! The settled point's refusal at the comparison `(ω₁, 2ω₁)`, whose
radius is four: read at three the clearance conjunct refuses, and
at four it holds. -/

theorem pin31 : ¬ genericlift.sideCert ⟨compAt 0 2, 2, 3, 3, []⟩ := by decide +kernel
theorem pin32 : genericlift.radiusClears (compAt 0 2) (posOfNat 4) := by decide +kernel

/-! The domain floor's refusal: the fundamental's gap `n² − 1` ties
the sum's unit at the rank one, off the counts, so the window from
one refuses where the window from two holds. -/

theorem pin33 : ¬ genericlift.rootsCert ⟨gd 0, 1, 4, 4, []⟩ := by decide +kernel
theorem pin34 : genericlift.rootsCert ⟨gd 0, 2, 4, 4, []⟩ := by decide +kernel

/-! The merged read's own binder: a dual pair's comparison reads the
sum's unit at every key and refuses the settled side, both leading
reads parting with the unit, while an unmerged comparison refuses
the merged read. -/

theorem pin35 : ¬ genericlift.sideCert ⟨compAt 0 1, 2, 4, 4, []⟩ := by decide +kernel
theorem pin36 : ¬ poly.unitTail (compAt 0 2) := by decide +kernel

end chaininstances
