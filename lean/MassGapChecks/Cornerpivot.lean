import MassGap.Cornerpivot
/-!
The check module for `lem:cornerpivot`'s walk tier.  The stage-gauge
instance runs at the bond weight `1`: the walk at the constant
diagonal `3` has leading minors `1, 3, 8, 21, 55`, and the anchors
read those minors and the recursion
`D_{k+2} + β² D_k = a_{k+1} D_{k+1}` by kernel `decide`, each beside
the theorem route at that data.  Clause (i)'s induction is anchored
on the segment of length two at the constant list `v ≡ 1`, with its
six binders refused one at a time — the bond's positivity at the
weight `0`, where the recursion degenerates and the minor `D_1`
carries equal members; the recursion at a forged minor list
`1, 3, -1`; the termwise read at the diagonal `1` where the minors
run `1, 1, 0, -1`; the positivity of `v` at the constant list `-1`;
the head minor's positivity at the list `-1, -1, -2`; and the head's
entry read at the list `1, -1, -4`.  A second anchor carries the
bond weight `2` at the diagonal `5`, whose minors are `1, 5, 21, 85`
and whose entry read at the depth one is `2 · 5 ≤ 21`.  Clause
(iii)'s crossing data are `β = 1`, `a = 3`, `D_0 = 1`, `D_1 = -1`,
`D_2 = -4`, the recursion `-4 + 1 = 3 · (-1)`: the rebound
`-4 < -3`, the swapped recursion `4 + (-1) = 3 · 1`, and the reseed
`1 ≤ 4` at `v_1 = v_2 = 1`, each with its binders refused, the
rebound's bond positivity refused at the weight `0`.  Clause (iv)
reads the constant supersolution at `a = 3`, `β = 1`, `c = 2`
(`4 ≤ 6`) and the clearance to the head's end at the minors of the
diagonal `3`.  The constant-floor list at `g = 3` reads `U_0 = 0`,
`U_1 = 1`, `U_4 = 21` with its recurrence at one depth.

The profile tier runs at the profile `1 − s` at the residue `2` and
the rate `[2 : 1]`, the u⁰-slab carrying `1` and `−1` at the two
s-powers with the u¹-slab vacant: at the scale `[1 : 64]` and the
clearing `1` the per-depth collapses read `64 − m²`, the cleared
diagonal reads `24192 + 4m² + 8m` at the square-scale clearing and
the bond weight is `3 · 64² = 12288`, and the shape, the positivity
on the segment of length two, the two termwise comparisons and the
supersolution read collecting them at the shared collapse list are
each decided by kernel `decide`, the read's two projection bridges
beside them.  The comparison polynomial's origin coefficient, its
shifted-tail read and the unpacked comparison stand beside their
routes with the comparison read's two binders refused — the shape at
a truncated clearing whose comparison read holds while the unpacked
one refuses, and the read itself at the scale `[1 : 4]` — and the
clearance to the depth two runs on the minors
`1, 24204, 435322752, 6902765756928`.  The five binders of that
clearance are refused one at a time — the supersolution read at the
scale `[1 : 8]` from the depth two, where the segment's positivity
conjunct refuses at the depth-four collapse; the recursion at the
forged minors `1, 24204, -1`; the head minor at
`-1, -1, 150970720`; the entry read at `1, -1, -151019168`; and the
rate's denominator at the degenerate rate `[0 : 0]`, where the bond
weight and the cleared diagonal both collapse to the sum's unit —
with the numerator's forcing at that denominator recorded beside it.

The evaluated glue's battery runs the magnitude price at three
profiles beside their theorem routes and the dominance glue at two
sites, the scale-carrying `−500η` off entry and the depth-carrying
`−100u` one, the box membership's isolation at the second — its
own section's account.
-/


open ground cornerpivot


/-! The bond weights: the stage-gauge unit, the weight `2`, and the
degenerate weight `0`. -/

private def bOne : BPair := BPair.ofNat 1

private def bTwo : BPair := BPair.ofNat 2

/-! The diagonals: the constant `3`, the constant `1` and the
constant `5`. -/

private def aThree : Nat → BPair := fun _ => BPair.ofNat 3

private def aOne : Nat → BPair := fun _ => BPair.ofNat 1

private def aFive : Nat → BPair := fun _ => BPair.ofNat 5

/-! The positive lists: the constant `1` and the constant `-1`. -/

private def vOne : Nat → BPair := fun _ => BPair.ofNat 1

private def vNeg : Nat → BPair := fun _ => (⟨1, 2⟩ : BPair)

/-! The leading minors at the unit bond and the constant diagonal
`3`: `1, 3, 8, 21, 55`. -/

private def dMin : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 3
  | 2 => BPair.ofNat 8
  | 3 => BPair.ofNat 21
  | _ => BPair.ofNat 55

/-! The leading minors at the bond weight `2` and the constant
diagonal `5`: `1, 5, 21, 85`. -/

private def dBeta : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 5
  | 2 => BPair.ofNat 21
  | _ => BPair.ofNat 85

/-! The list at the degenerate bond weight `0` and the diagonal `3`:
`1`, the equal-membered `⟨2 : 2⟩`, the sum's unit. -/

private def dBond : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => (⟨2, 2⟩ : BPair)
  | _ => BPair.unit

/-! The forged list `1, 3, -1`, off the recursion at the first
depth. -/

private def dForge : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 3
  | _ => (⟨1, 2⟩ : BPair)

/-! The minors of the diagonal `1` at the unit bond:
`1, 1, 0, -1`. -/

private def dFlat : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 1
  | 2 => BPair.unit
  | _ => (⟨1, 2⟩ : BPair)

/-! The list `-1, -1, -2, -5` at the unit bond and the diagonal `3`,
its head minor below the sum's unit. -/

private def dNegHead : Nat → BPair := fun k =>
  match k with
  | 0 => (⟨1, 2⟩ : BPair)
  | 1 => (⟨1, 2⟩ : BPair)
  | 2 => (⟨1, 3⟩ : BPair)
  | _ => (⟨1, 6⟩ : BPair)

/-! The list `1, -1, -4, -11` at the unit bond and the diagonal `3`,
its head entry read off the lower side. -/

private def dCross : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => (⟨1, 2⟩ : BPair)
  | 2 => (⟨1, 5⟩ : BPair)
  | _ => (⟨1, 12⟩ : BPair)

/-! The walk at the unit bond and the constant diagonal `3`: the
minor pair at the depth three reads `(21, 55)`, and the recursion
read at the depth two stands beside its decided anchor. -/

example : (walkGo bOne aThree 3).1.oneValue (BPair.ofNat 21) := by decide +kernel

example : (walkGo bOne aThree 3).2.oneValue (BPair.ofNat 55) := by decide +kernel

example : walkGo bOne aThree 0 = (BPair.ofNat 1, aThree 0) := walk_zero bOne aThree

example :
    ((walkGo bOne aThree 3).2 + bOne * bOne * (walkGo bOne aThree 2).1).oneValue
      (aThree 3 * (walkGo bOne aThree 2).2) := by decide +kernel

example :
    ((walkGo bOne aThree 3).2 + bOne * bOne * (walkGo bOne aThree 2).1).oneValue
      (aThree 3 * (walkGo bOne aThree 2).2) :=
  walk_rec bOne aThree 2

/-! The walk at the bond weight `2` and the constant diagonal `5`:
the minor pair at the depth two reads `(21, 85)`. -/

example : (walkGo bTwo aFive 2).1.oneValue (BPair.ofNat 21) := by decide +kernel

example : (walkGo bTwo aFive 2).2.oneValue (BPair.ofNat 85) := by decide +kernel

/-! Clause (i) at the segment of length two: the minors of the
diagonal `3` at the unit bond against the constant list `v ≡ 1`, the
conclusion at the depth two decided beside the theorem route. -/

example :
    BPair.unit < dMin 3 ∧ bOne * (dMin 2 * vOne 3) ≤ dMin 3 * vOne 2 := by
  decide +kernel

example :
    BPair.unit < dMin 3 ∧ bOne * (dMin 2 * vOne 3) ≤ dMin 3 * vOne 2 :=
  pivot_clears aThree vOne dMin bOne 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 2 (Nat.le_refl 2)

/-! Clause (i) at the bond weight `2`: the minors of the diagonal
`5` on the segment of length one, the entry read `2 · 5 ≤ 21` at the
depth one decided beside the theorem route. -/

example :
    BPair.unit < dBeta 2 ∧ bTwo * (dBeta 1 * vOne 2) ≤ dBeta 2 * vOne 1 := by
  decide +kernel

example :
    BPair.unit < dBeta 2 ∧ bTwo * (dBeta 1 * vOne 2) ≤ dBeta 2 * vOne 1 :=
  pivot_clears aFive vOne dBeta bTwo 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 1 (Nat.le_refl 1)

/-! The bond binder `hβ` isolated: at the weight `0` the recursion
degenerates — the five further binders hold at the list
`1, ⟨2 : 2⟩, 0` — the bond's positivity fails, and the conclusion's
positivity fails at the depth naught, where the minor carries equal
members. -/

example :
    (∀ k, k < 1 →
        (dBond (k + 2) + BPair.unit * BPair.unit * dBond k).oneValue
          (aThree (k + 1) * dBond (k + 1)))
      ∧ (∀ k, k < 1 →
        BPair.unit * (vOne k + vOne (k + 2)) ≤ aThree (k + 1) * vOne (k + 1))
      ∧ (∀ k, k ≤ 1 + 1 → BPair.unit < vOne k)
      ∧ BPair.unit < dBond 0
      ∧ BPair.unit * (dBond 0 * vOne 1) ≤ dBond 1 * vOne 0
      ∧ ¬ (BPair.unit < BPair.unit)
      ∧ ¬ (BPair.unit < dBond 1) := by decide +kernel

/-! The recursion binder `hrec` isolated: at the forged list
`1, 3, -1` the five further binders hold and the conclusion's
positivity fails at the depth one. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        bOne * (vOne k + vOne (k + 2)) ≤ aThree (k + 1) * vOne (k + 1))
      ∧ (∀ k, k ≤ 2 + 1 → BPair.unit < vOne k)
      ∧ BPair.unit < dForge 0
      ∧ bOne * (dForge 0 * vOne 1) ≤ dForge 1 * vOne 0
      ∧ ¬ (∀ k, k < 2 →
        (dForge (k + 2) + bOne * bOne * dForge k).oneValue
          (aThree (k + 1) * dForge (k + 1)))
      ∧ ¬ (BPair.unit < dForge 2) := by decide +kernel

/-! The termwise binder `hterm` isolated: at the diagonal `1` the
constant list's termwise read `2 ≤ 1` fails, the five further
binders hold, and the conclusion's positivity fails at the depth
one. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dFlat (k + 2) + bOne * bOne * dFlat k).oneValue
          (aOne (k + 1) * dFlat (k + 1)))
      ∧ (∀ k, k ≤ 2 + 1 → BPair.unit < vOne k)
      ∧ BPair.unit < dFlat 0
      ∧ bOne * (dFlat 0 * vOne 1) ≤ dFlat 1 * vOne 0
      ∧ ¬ (∀ k, k < 2 →
        bOne * (vOne k + vOne (k + 2)) ≤ aOne (k + 1) * vOne (k + 1))
      ∧ ¬ (BPair.unit < dFlat 2) := by decide +kernel

/-! The positivity binder `hpos` isolated: at the constant list `-1`
the termwise read `-2 ≤ -1` holds with the four further binders, the
list's positivity fails, and the conclusion's positivity fails at
the depth one. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dFlat (k + 2) + bOne * bOne * dFlat k).oneValue
          (aOne (k + 1) * dFlat (k + 1)))
      ∧ (∀ k, k < 2 →
        bOne * (vNeg k + vNeg (k + 2)) ≤ aOne (k + 1) * vNeg (k + 1))
      ∧ BPair.unit < dFlat 0
      ∧ bOne * (dFlat 0 * vNeg 1) ≤ dFlat 1 * vNeg 0
      ∧ ¬ (∀ k, k ≤ 2 + 1 → BPair.unit < vNeg k)
      ∧ ¬ (BPair.unit < dFlat 2) := by decide +kernel

/-! The head binder `h0` isolated: at the list `-1, -1, -2` the five
further binders hold, the head minor sits below the sum's unit, and
the conclusion's positivity fails at the depth naught. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dNegHead (k + 2) + bOne * bOne * dNegHead k).oneValue
          (aThree (k + 1) * dNegHead (k + 1)))
      ∧ (∀ k, k < 2 →
        bOne * (vOne k + vOne (k + 2)) ≤ aThree (k + 1) * vOne (k + 1))
      ∧ (∀ k, k ≤ 2 + 1 → BPair.unit < vOne k)
      ∧ bOne * (dNegHead 0 * vOne 1) ≤ dNegHead 1 * vOne 0
      ∧ ¬ (BPair.unit < dNegHead 0)
      ∧ ¬ (BPair.unit < dNegHead 1) := by decide +kernel

/-! The head entry binder `hseed` isolated: at the list `1, -1, -4`
the five further binders hold, the head's entry read fails, and the
conclusion's positivity fails at the depth naught. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dCross (k + 2) + bOne * bOne * dCross k).oneValue
          (aThree (k + 1) * dCross (k + 1)))
      ∧ (∀ k, k < 2 →
        bOne * (vOne k + vOne (k + 2)) ≤ aThree (k + 1) * vOne (k + 1))
      ∧ (∀ k, k ≤ 2 + 1 → BPair.unit < vOne k)
      ∧ BPair.unit < dCross 0
      ∧ ¬ (bOne * (dCross 0 * vOne 1) ≤ dCross 1 * vOne 0)
      ∧ ¬ (BPair.unit < dCross 1) := by decide +kernel

/-! Clause (iii)'s crossing data at the unit bond: `a = 3`,
`D_0 = 1`, `D_1 = -1`, `D_2 = -4`, the recursion `-4 + 1 = 3·(-1)`. -/

private def cAp : BPair := BPair.ofNat 3

private def cD0 : BPair := BPair.ofNat 1

private def cD1 : BPair := ⟨1, 2⟩

private def cD2 : BPair := ⟨1, 5⟩

private def cOne : BPair := BPair.ofNat 1

/-! The rebound `-4 < -3`, decided beside its route. -/

example : (cD2 + bOne * bOne * cD0).oneValue (cAp * cD1) := by decide +kernel

example : cD2 < cAp * cD1 := by decide +kernel

example : cD2 < cAp * cD1 :=
  rebound cAp bOne cD0 cD1 cD2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The rebound's `h0` isolated: at `D_0 = -1`, `D_1 = 1`,
`D_2 = 4` the recursion and the bond's positivity hold, the
predecessor's positivity fails, and the conclusion `4 < 3` fails. -/

example :
    (BPair.ofNat 4 + bOne * bOne * (⟨1, 2⟩ : BPair)).oneValue
        (cAp * BPair.ofNat 1)
      ∧ BPair.unit < bOne * bOne
      ∧ ¬ (BPair.unit < (⟨1, 2⟩ : BPair))
      ∧ ¬ (BPair.ofNat 4 < cAp * BPair.ofNat 1) := by decide +kernel

/-! The rebound's `hβ` isolated: at the weight `0` the recursion
holds at `D_1 = ⟨2 : 2⟩`, `D_2 = 0`, the predecessor's positivity
holds, the bond square's positivity fails, and the conclusion fails
at equal members. -/

example :
    (BPair.unit + BPair.unit * BPair.unit * BPair.ofNat 1).oneValue
        (cAp * (⟨2, 2⟩ : BPair))
      ∧ BPair.unit < BPair.ofNat 1
      ∧ ¬ (BPair.unit < BPair.unit * BPair.unit)
      ∧ ¬ (BPair.unit < cAp * (⟨2, 2⟩ : BPair)) := by decide +kernel

/-! The rebound's `hrec` isolated: at the forged triple `D_0 = 1`,
`D_1 = 1`, `D_2 = 100` the bond square's positivity and the
predecessor's hold, the recursion fails, and the conclusion
`100 < 3` fails. -/

example :
    BPair.unit < bOne * bOne
      ∧ BPair.unit < cD0
      ∧ ¬ ((BPair.ofNat 100 + bOne * bOne * cD0).oneValue
        (cAp * BPair.ofNat 1))
      ∧ ¬ (BPair.ofNat 100 < cAp * BPair.ofNat 1) := by decide +kernel

/-! The swapped recursion at the crossing triple, decided beside its
route. -/

example : (cD2.swap + bOne * bOne * cD0.swap).oneValue (cAp * cD1.swap) := by
  decide +kernel

example : (cD2.swap + bOne * bOne * cD0.swap).oneValue (cAp * cD1.swap) :=
  rec_swap (by decide +kernel)

/-! The swapped recursion's `hrec` isolated: at the forged triple
`D_k = 1`, `D_{k+1} = -1`, `D_{k+2} = 1` the recursion fails and the
swapped read fails with it. -/

example :
    ¬ ((BPair.ofNat 1 + bOne * bOne * cD0).oneValue (cAp * cD1))
      ∧ ¬ ((BPair.ofNat 1).swap + bOne * bOne * cD0.swap).oneValue
        (cAp * cD1.swap) := by decide +kernel

/-! The reseed at the crossing: `β · (D_1.swap · v_2) = 1` at or
below `D_2.swap · v_1 = 4`, decided beside its route. -/

example : bOne * (cD1.swap * cOne) ≤ cD2.swap * cOne := by decide +kernel

example : bOne * (cD1.swap * cOne) ≤ cD2.swap * cOne :=
  seed_after_crossing cAp bOne cD0 cD1 cD2 cOne cOne (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The reseed's crossing binder `hc` isolated: at `D_1 = 1`,
`D_2 = 2` the four further binders hold, the crossing read fails,
and the conclusion `-1 ≤ -2` fails. -/

example :
    ((BPair.ofNat 2 + bOne * bOne * cD0).oneValue (cAp * BPair.ofNat 1))
      ∧ BPair.unit ≤ cD0
      ∧ BPair.unit < cOne
      ∧ bOne * cOne ≤ cAp * cOne
      ∧ ¬ (BPair.ofNat 1 < BPair.unit)
      ∧ ¬ (bOne * ((BPair.ofNat 1).swap * cOne) ≤ (BPair.ofNat 2).swap * cOne) := by
  decide +kernel

/-! The reseed's positivity binder `hpos` isolated: at `v_1 = -1`,
`v_2 = -3` the four further binders hold, the list's positivity
fails, and the conclusion `-3 ≤ -4` fails. -/

example :
    (cD2 + bOne * bOne * cD0).oneValue (cAp * cD1)
      ∧ BPair.unit ≤ cD0
      ∧ cD1 < BPair.unit
      ∧ bOne * (⟨1, 4⟩ : BPair) ≤ cAp * (⟨1, 2⟩ : BPair)
      ∧ ¬ (BPair.unit < (⟨1, 2⟩ : BPair))
      ∧ ¬ (bOne * (cD1.swap * (⟨1, 4⟩ : BPair)) ≤ cD2.swap * (⟨1, 2⟩ : BPair)) := by
  decide +kernel

/-! The reseed's termwise binder `hterm` isolated: at `v_1 = 1`,
`v_2 = 5` the four further binders hold, the termwise read `5 ≤ 3`
fails, and the conclusion `5 ≤ 4` fails. -/

example :
    (cD2 + bOne * bOne * cD0).oneValue (cAp * cD1)
      ∧ BPair.unit ≤ cD0
      ∧ cD1 < BPair.unit
      ∧ BPair.unit < cOne
      ∧ ¬ (bOne * BPair.ofNat 5 ≤ cAp * cOne)
      ∧ ¬ (bOne * (cD1.swap * BPair.ofNat 5) ≤ cD2.swap * cOne) := by
  decide +kernel

/-! The reseed's head binder `h0` isolated: at `D_0 = -4`,
`D_1 = -1`, `D_2 = 1` the four further binders hold, the
predecessor's upper-side-or-equal read fails, and the conclusion
`1 ≤ -1` fails. -/

example :
    (BPair.ofNat 1 + bOne * bOne * (⟨1, 5⟩ : BPair)).oneValue (cAp * cD1)
      ∧ cD1 < BPair.unit
      ∧ BPair.unit < cOne
      ∧ bOne * cOne ≤ cAp * cOne
      ∧ ¬ (BPair.unit ≤ (⟨1, 5⟩ : BPair))
      ∧ ¬ (bOne * (cD1.swap * cOne) ≤ (BPair.ofNat 1).swap * cOne) := by
  decide +kernel

/-! The reseed's recursion binder `hrec` isolated: at the forged
triple `D_0 = 1`, `D_1 = -1`, `D_2 = 100` the four further binders
hold, the recursion fails, and the conclusion `1 ≤ -100` fails. -/

example :
    BPair.unit ≤ cD0
      ∧ cD1 < BPair.unit
      ∧ BPair.unit < cOne
      ∧ bOne * cOne ≤ cAp * cOne
      ∧ ¬ ((BPair.ofNat 100 + bOne * bOne * cD0).oneValue (cAp * cD1))
      ∧ ¬ (bOne * (cD1.swap * cOne) ≤ (BPair.ofNat 100).swap * cOne) := by
  decide +kernel

/-! Clause (iv)'s termwise read at `a = 3`, `β = 1`, `c = 2`:
`4 ≤ 6`, decided beside its route. -/

example : bOne * (BPair.ofNat 2 + BPair.ofNat 2) ≤ cAp * BPair.ofNat 2 := by
  decide +kernel

example : bOne * (BPair.ofNat 2 + BPair.ofNat 2) ≤ cAp * BPair.ofNat 2 :=
  const_term cAp bOne (BPair.ofNat 2) (by decide +kernel) (by decide +kernel)

/-! The constant list's positivity binder isolated: at `c = -1` the
diagonal's clearance holds, the list's read at or above the sum's
unit fails, and the conclusion `-2 ≤ -3` fails. -/

example :
    bOne * BPair.ofNat 2 ≤ cAp
      ∧ ¬ (BPair.unit ≤ (⟨1, 2⟩ : BPair))
      ∧ ¬ (bOne * ((⟨1, 2⟩ : BPair) + (⟨1, 2⟩ : BPair))
        ≤ cAp * (⟨1, 2⟩ : BPair)) := by decide +kernel

/-! The diagonal's clearance binder isolated: at `a = 1`, `c = 1`
the list's read holds, the clearance of the bond's double fails, and
the conclusion `2 ≤ 1` fails. -/

example :
    BPair.unit ≤ cOne
      ∧ ¬ (bOne * BPair.ofNat 2 ≤ BPair.ofNat 1)
      ∧ ¬ (bOne * (cOne + cOne) ≤ BPair.ofNat 1 * cOne) := by decide +kernel

/-! Clause (iv)'s clearance to the head's end at the unit bond and
the diagonal `3`: the minor at the depth three sits above the sum's
unit, decided beside its route. -/

example : BPair.unit < dMin 3 := by decide +kernel

example : BPair.unit < dMin 3 :=
  tail_clear aThree dMin bOne 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 2
    (Nat.le_refl 2)

/-! The clearance binder `ha` isolated: at the diagonal `1` the four
further binders hold, the clearance of the bond's double fails, and
the conclusion's positivity fails at the depth one. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dFlat (k + 2) + bOne * bOne * dFlat k).oneValue
          (aOne (k + 1) * dFlat (k + 1)))
      ∧ BPair.unit < dFlat 0
      ∧ bOne * dFlat 0 ≤ dFlat 1
      ∧ ¬ (∀ k, k < 2 → bOne * BPair.ofNat 2 ≤ aOne (k + 1))
      ∧ ¬ (BPair.unit < dFlat 2) := by decide +kernel

/-! The head binder `h0` isolated at the clearance: the list
`-1, -1, -2` keeps the four further binders and fails the conclusion
at the depth naught. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dNegHead (k + 2) + bOne * bOne * dNegHead k).oneValue
          (aThree (k + 1) * dNegHead (k + 1)))
      ∧ (∀ k, k < 2 → bOne * BPair.ofNat 2 ≤ aThree (k + 1))
      ∧ bOne * dNegHead 0 ≤ dNegHead 1
      ∧ ¬ (BPair.unit < dNegHead 0)
      ∧ ¬ (BPair.unit < dNegHead 1) := by decide +kernel

/-! The head entry binder `hseed` isolated at the clearance: the
list `1, -1, -4` keeps the four further binders, fails the head's
order read, and fails the conclusion at the depth naught. -/

example :
    BPair.unit < bOne
      ∧ (∀ k, k < 2 →
        (dCross (k + 2) + bOne * bOne * dCross k).oneValue
          (aThree (k + 1) * dCross (k + 1)))
      ∧ (∀ k, k < 2 → bOne * BPair.ofNat 2 ≤ aThree (k + 1))
      ∧ BPair.unit < dCross 0
      ∧ ¬ (bOne * dCross 0 ≤ dCross 1)
      ∧ ¬ (BPair.unit < dCross 1) := by decide +kernel

/-! The clearance's bond binder `hβ` isolated: at the weight `0` and
the diagonal at the sum's unit the recursion degenerates, the three
further binders hold at the minors `1, ⟨2 : 2⟩, 0`, the bond's
positivity fails, and the conclusion fails at the depth naught. -/

example :
    (∀ k, k < 1 →
        (dBond (k + 2) + BPair.unit * BPair.unit * dBond k).oneValue
          (BPair.ofNat 0 * dBond (k + 1)))
      ∧ (∀ k, k < 1 → BPair.unit * BPair.ofNat 2 ≤ BPair.ofNat 0)
      ∧ BPair.unit < dBond 0
      ∧ BPair.unit * dBond 0 ≤ dBond 1
      ∧ ¬ (BPair.unit < BPair.unit)
      ∧ ¬ (BPair.unit < dBond 1) := by decide +kernel

/-! The clearance's recursion binder `hrec` isolated: at the forged
minors `1, 3, -1` the three further binders hold, the recursion
fails at the first depth, and the conclusion's positivity fails at
the depth one. -/

example :
    (∀ k, k < 2 → bOne * BPair.ofNat 2 ≤ aThree (k + 1))
      ∧ BPair.unit < dForge 0
      ∧ bOne * dForge 0 ≤ dForge 1
      ∧ ¬ (∀ k, k < 2 →
        (dForge (k + 2) + bOne * bOne * dForge k).oneValue
          (aThree (k + 1) * dForge (k + 1)))
      ∧ ¬ (BPair.unit < dForge 2) := by decide +kernel

/-! The constant-floor list at `g = 3`: the boundary entry at the
sum's unit, the boundary's unit seed `U_1 = 1`, and `U_4 = 21`, with
the recurrence at the depth one decided beside its route. -/

example : uWalk cAp 0 = BPair.unit := uWalk_zero cAp

example : uWalk cAp 1 = BPair.ofNat 1 := uWalk_one cAp

example : (uWalk cAp 4).oneValue (BPair.ofNat 21) := by decide +kernel

example : (uWalk cAp 3 + uWalk cAp 1).oneValue (cAp * uWalk cAp 2) := by
  decide +kernel

example : (uWalk cAp 3 + uWalk cAp 1).oneValue (cAp * uWalk cAp 2) :=
  uWalk_rec cAp 1

/-! The profile tier's shared fixture: the profile `1 − s` at the
residue `2` and the rate `[2 : 1]` — the u⁰-slab carrying `1` at the
s-power naught and `−1` at the s-power one, the u¹-slab vacant — at
`r = 2`, `qn = 2`, `qd = 1` and the clearing `K = 1`.  At the scale
`[1 : 64]` its per-depth collapses read `64 − m²` (`63, 60, 55, 48`
at the depths one to four), its cleared diagonal reads
`24192 + 4m² + 8m` (`24204, 24224, 24252` at the depths one to
three, the square-scale clearing `64²` on the band read against the
scale's own on the rate), and the bond weight is `3 · 64² = 12288`. -/

private def vProf : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 1], [(⟨1, 2⟩ : BPair)]], [])

/-! The profile's shape, its positivity on the segment of length
two, the termwise comparison at the depths one and two —
`12288 · (63 + 55) = 1449984` at or below `24224 · 60 = 1453440` and
`12288 · (60 + 48) = 1327104` at or below `24252 · 55 = 1333860` —
and the supersolution read collecting them at the shared collapse
list. -/

example : profShape vProf 1 := by decide +kernel

example : profPos vProf 1 64 1 1 2 := by decide +kernel

example : termRead vProf 2 2 1 1 64 1 1 := by decide +kernel

example : termRead vProf 2 2 1 1 64 1 2 := by decide +kernel

example : superRead vProf 2 2 1 1 64 1 1 2 := by decide +kernel

/-! The segment read's two projection bridges at the fixture: the
profile's positivity and the termwise reads, each the collapse
list's own member read. -/

example : profPos vProf 1 64 1 1 2 :=
  superRead_pos (by decide +kernel : superRead vProf 2 2 1 1 64 1 1 2)

example : termRead vProf 2 2 1 1 64 1 (1 + 1) :=
  superRead_term (by decide +kernel : superRead vProf 2 2 1 1 64 1 1 2)
    1 (by decide +kernel)

/-! The comparison polynomial's origin coefficient at the depth one,
decided beside its route, and the shifted-tail read at that
data. -/

example :
    (ground.getAt BPair.unit (termPoly vProf 2 2 1 1) 0).oneValue
      BPair.unit := by decide +kernel

example :
    (ground.getAt BPair.unit (termPoly vProf 2 2 1 1) 0).oneValue
      BPair.unit :=
  termPoly_base vProf 2 2 1 1

example :
    poly.oneValue (termPoly vProf 2 2 1 1)
      (poly.shiftUp 1 (List.drop 1 (termPoly vProf 2 2 1 1))) := by
  decide +kernel

example :
    poly.oneValue (termPoly vProf 2 2 1 1)
      (poly.shiftUp 1 (List.drop 1 (termPoly vProf 2 2 1 1))) :=
  termPoly_shift vProf 2 2 1 1

/-! The comparison read unpacked at the depth one: the bond weight's
multiple of the neighbour depths' cleared sum at or below the
diagonal's multiple of the standing depth, decided beside its
route. -/

example :
    BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
        * (poly.evalClear (depthPoly vProf 1) (BPair.ofPos 1) 64 1
           + poly.evalClear (depthPoly vProf (1 + 2)) (BPair.ofPos 1) 64 1)
      ≤ poly.evalClear (diagPoly 2 2 1 (1 + 1)) (BPair.ofPos 1) 64 2
        * poly.evalClear (depthPoly vProf (1 + 1)) (BPair.ofPos 1) 64 1 := by
  decide +kernel

example :
    BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
        * (poly.evalClear (depthPoly vProf 1) (BPair.ofPos 1) 64 1
           + poly.evalClear (depthPoly vProf (1 + 2)) (BPair.ofPos 1) 64 1)
      ≤ poly.evalClear (diagPoly 2 2 1 (1 + 1)) (BPair.ofPos 1) 64 2
        * poly.evalClear (depthPoly vProf (1 + 1)) (BPair.ofPos 1) 64 1 :=
  termRead_read (by decide +kernel) (by decide +kernel)

/-! The clearance transport's shape binder isolated: at the slab
`[1, 1, 1]` and the clearing naught the shape read fails and the
depth collapse's key count clears the power, refused together. -/

example :
    ¬ profShape (([[BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]],
        []) : poly.PPoly × poly.PPoly) 0
      ∧ ¬ ((depthPoly (([[BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]],
        []) : poly.PPoly × poly.PPoly) 1).length ≤ 0 + 1) := by
  decide +kernel

/-! The comparison read's shape binder `hsh` isolated: at the
u¹-slab `[1, 1]` and the clearing naught the comparison read holds
at the truncated clearing while the shape read and the unpacked
comparison refuse — the shape conjunct the faithfulness's own
guard. -/

example :
    termRead (([], [[BPair.ofNat 1, BPair.ofNat 1]])
        : poly.PPoly × poly.PPoly) 2 2 1 1 64 0 1
      ∧ ¬ profShape (([], [[BPair.ofNat 1, BPair.ofNat 1]])
        : poly.PPoly × poly.PPoly) 0
      ∧ ¬ (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
        * (poly.evalClear (depthPoly (([], [[BPair.ofNat 1, BPair.ofNat 1]])
            : poly.PPoly × poly.PPoly) 1) (BPair.ofPos 1) 64 0
           + poly.evalClear (depthPoly
              (([], [[BPair.ofNat 1, BPair.ofNat 1]])
                : poly.PPoly × poly.PPoly) (1 + 2)) (BPair.ofPos 1) 64 0)
      ≤ poly.evalClear (diagPoly 2 2 1 (1 + 1)) (BPair.ofPos 1) 64 2
        * poly.evalClear (depthPoly (([], [[BPair.ofNat 1, BPair.ofNat 1]])
            : poly.PPoly × poly.PPoly) (1 + 1)) (BPair.ofPos 1) 64 0) := by
  decide +kernel

/-! The comparison read's own binder `h` isolated: at the shared
profile and the scale `[1 : 4]` the shape read holds, the comparison
read fails at the depth two, and the unpacked comparison fails with
it. -/

example :
    profShape vProf 1
      ∧ ¬ termRead vProf 2 2 1 1 4 1 2
      ∧ ¬ (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 4 * BPair.ofPos 4
        * (poly.evalClear (depthPoly vProf 2) (BPair.ofPos 1) 4 1
           + poly.evalClear (depthPoly vProf (2 + 2)) (BPair.ofPos 1) 4 1)
      ≤ poly.evalClear (diagPoly 2 2 1 (2 + 1)) (BPair.ofPos 1) 4 2
        * poly.evalClear (depthPoly vProf (2 + 1)) (BPair.ofPos 1) 4 1) := by
  decide +kernel

/-! The walk's minors at the cleared diagonal from the depth one:
`1, 24204, 435322752, 6902765756928`, with
`D_2 = 24224 · 24204 − 12288² · 1` and
`D_3 = 24252 · D_2 − 12288² · 24204`. -/

private def dProf : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 24204
  | 2 => BPair.ofNat 435322752
  | _ => BPair.ofNat 6902765756928

/-! The supersolution clears the pivots to the depth two, decided
beside its route. -/

example :
    BPair.unit < dProf (2 + 1)
      ∧ BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
          * (dProf 2 * poly.evalClear (depthPoly vProf (1 + 2 + 1))
              (BPair.ofPos 1) 64 1)
        ≤ dProf (2 + 1) * poly.evalClear (depthPoly vProf (1 + 2))
            (BPair.ofPos 1) 64 1 := by decide +kernel

example :
    BPair.unit < dProf (2 + 1)
      ∧ BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
          * (dProf 2 * poly.evalClear (depthPoly vProf (1 + 2 + 1))
              (BPair.ofPos 1) 64 1)
        ≤ dProf (2 + 1) * poly.evalClear (depthPoly vProf (1 + 2))
            (BPair.ofPos 1) 64 1 :=
  super_clears vProf 2 2 1 1 64 1 1 2 dProf (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 2 (Nat.le_refl 2)

/-! The five binders of the supersolution clearance refused one at a
time, the kept binders decided at their own reads inside each
conjunction and the dropped one beside the refused conclusion. -/

/-! The supersolution binder `hsr` isolated: at the scale `[1 : 8]`
from the depth two the profile's collapses run `4, −1, −8`, the
depth-four collapse below the sum's unit, so the segment read's
positivity conjunct refuses; the four further binders hold at the
minors `1, 1, −36468` (`D_2 = 396 · 1 − 192² · 1`), and the
conclusion's positivity fails at the depth one. -/

private def dHsr : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 1
  | _ => (⟨1, 36469⟩ : BPair)

example :
    (∀ k, k < 1 →
        (dHsr (k + 2)
            + BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 8 * BPair.ofPos 8
              * (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 8
                * BPair.ofPos 8) * dHsr k).oneValue
          (poly.evalClear (diagPoly 2 2 1 (2 + k + 1)) (BPair.ofPos 1) 8 2
            * dHsr (k + 1)))
      ∧ BPair.unit < dHsr 0
      ∧ BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 8 * BPair.ofPos 8
          * (dHsr 0 * poly.evalClear (depthPoly vProf (2 + 1))
              (BPair.ofPos 1) 8 1)
        ≤ dHsr 1 * poly.evalClear (depthPoly vProf 2) (BPair.ofPos 1) 8 1
      ∧ 0 < 1
      ∧ ¬ superRead vProf 2 2 1 1 8 1 2 1
      ∧ ¬ (BPair.unit < dHsr (1 + 1)) := by decide +kernel

/-! The recursion binder `hrec` isolated: at the good fixture the
forged minors `1, 24204, −1` keep the four further binders, fail the
recursion at the depth one, and fail the conclusion's positivity at
the depth one. -/

private def dRec : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => BPair.ofNat 24204
  | _ => (⟨1, 2⟩ : BPair)

example :
    superRead vProf 2 2 1 1 64 1 1 1
      ∧ BPair.unit < dRec 0
      ∧ BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
          * (dRec 0 * poly.evalClear (depthPoly vProf (1 + 1))
              (BPair.ofPos 1) 64 1)
        ≤ dRec 1 * poly.evalClear (depthPoly vProf 1) (BPair.ofPos 1) 64 1
      ∧ 0 < 1
      ∧ ¬ (∀ k, k < 1 →
        (dRec (k + 2)
            + BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
              * (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64
                * BPair.ofPos 64) * dRec k).oneValue
          (poly.evalClear (diagPoly 2 2 1 (1 + k + 1)) (BPair.ofPos 1) 64 2
            * dRec (k + 1)))
      ∧ ¬ (BPair.unit < dRec (1 + 1)) := by decide +kernel

/-! The head binder `h0` isolated: the minors `−1, −1, 150970720`
(`D_2 = 24224 · (−1) + 12288²`) keep the four further binders —
the entry read `12288 · ((−1) · 60) = −737280` at or below
`(−1) · 63 = −63` — the head minor sits below the sum's unit, and the
conclusion's positivity fails at the depth naught. -/

private def dHead : Nat → BPair := fun k =>
  match k with
  | 0 => (⟨1, 2⟩ : BPair)
  | 1 => (⟨1, 2⟩ : BPair)
  | _ => BPair.ofNat 150970720

example :
    superRead vProf 2 2 1 1 64 1 1 1
      ∧ (∀ k, k < 1 →
        (dHead (k + 2)
            + BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
              * (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64
                * BPair.ofPos 64) * dHead k).oneValue
          (poly.evalClear (diagPoly 2 2 1 (1 + k + 1)) (BPair.ofPos 1) 64 2
            * dHead (k + 1)))
      ∧ BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
          * (dHead 0 * poly.evalClear (depthPoly vProf (1 + 1))
              (BPair.ofPos 1) 64 1)
        ≤ dHead 1 * poly.evalClear (depthPoly vProf 1) (BPair.ofPos 1) 64 1
      ∧ 0 < 1
      ∧ ¬ (BPair.unit < dHead 0)
      ∧ ¬ (BPair.unit < dHead (0 + 1)) := by decide +kernel

/-! The entry binder `hseed` isolated: the minors `1, −1, −151019168`
(`D_2 = 24224 · (−1) − 12288² · 1`) keep the four further binders,
fail the entry read `12288 · (1 · 60) = 737280` against
`(−1) · 63 = −63`, and fail the conclusion's positivity at the depth
naught. -/

private def dSeed : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => (⟨1, 2⟩ : BPair)
  | _ => (⟨1, 151019169⟩ : BPair)

example :
    superRead vProf 2 2 1 1 64 1 1 1
      ∧ (∀ k, k < 1 →
        (dSeed (k + 2)
            + BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
              * (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64
                * BPair.ofPos 64) * dSeed k).oneValue
          (poly.evalClear (diagPoly 2 2 1 (1 + k + 1)) (BPair.ofPos 1) 64 2
            * dSeed (k + 1)))
      ∧ BPair.unit < dSeed 0
      ∧ 0 < 1
      ∧ ¬ (BPair.ofNat ((2 + 1) * 1) * BPair.ofPos 64 * BPair.ofPos 64
          * (dSeed 0 * poly.evalClear (depthPoly vProf (1 + 1))
              (BPair.ofPos 1) 64 1)
        ≤ dSeed 1 * poly.evalClear (depthPoly vProf 1) (BPair.ofPos 1) 64 1)
      ∧ ¬ (BPair.unit < dSeed (0 + 1)) := by decide +kernel

/-! The rate binder `hqd` isolated: at the degenerate rate `[0 : 0]`
the bond weight collapses to the sum's unit and the cleared diagonal
reads it too, so the four further binders hold at the minors
`1, ⟨2 : 2⟩, 0` — the supersolution read included, its termwise
comparison at the unit — while the rate's second count sits at
nought and the conclusion's positivity fails at the depth naught,
where the minor carries equal members.  The numerator is forced to
nought beside it: at an occupied numerator the cleared diagonal
reads `−384` at every depth while the profile is strictly above the
unit, so no supersolution read stands at the vacant denominator. -/

private def dQd : Nat → BPair := fun k =>
  match k with
  | 0 => BPair.ofNat 1
  | 1 => (⟨2, 2⟩ : BPair)
  | _ => BPair.unit

example :
    superRead vProf 2 0 0 1 64 1 1 1
      ∧ (∀ k, k < 1 →
        (dQd (k + 2)
            + BPair.ofNat ((2 + 1) * 0) * BPair.ofPos 64 * BPair.ofPos 64
              * (BPair.ofNat ((2 + 1) * 0) * BPair.ofPos 64
                * BPair.ofPos 64) * dQd k).oneValue
          (poly.evalClear (diagPoly 2 0 0 (1 + k + 1)) (BPair.ofPos 1) 64 2
            * dQd (k + 1)))
      ∧ BPair.unit < dQd 0
      ∧ BPair.ofNat ((2 + 1) * 0) * BPair.ofPos 64 * BPair.ofPos 64
          * (dQd 0 * poly.evalClear (depthPoly vProf (1 + 1))
              (BPair.ofPos 1) 64 1)
        ≤ dQd 1 * poly.evalClear (depthPoly vProf 1) (BPair.ofPos 1) 64 1
      ∧ ¬ (0 < 0)
      ∧ ¬ (BPair.unit < dQd (0 + 1)) := by decide +kernel

/-! The vacant denominator at an occupied numerator: the cleared
diagonal reads `−384` at every depth while the profile's collapse
reads `60` at the depth two, so the termwise comparison at the depth
one fails and the supersolution read with it. -/

example : ¬ superRead vProf 2 2 0 1 64 1 1 1 := by decide +kernel



/-! `lem:cornerpivot`(v)'s arithmetic tier.  The anchors run at the
endpoint `8`: the family's value at the depth three, its square sum,
the well's two parts and the bond-square sum, with two power sums
beside them and the lower rate's two data at the scale pair
`[1 : 10]` and the residue `2`.  The endpoint key holds at that data
and at the residue `1` with the endpoint `7`.  The small endpoints
`1` and `2` read the family's square and the bond-square sum at the
vacant and the one-bond cases.  The three closed polynomials read
their tops — `16` at the key nine, `44` at the key seven and `80` at
the key eleven — and the tops' pairs against their clearings are the
tex's displayed pairs: `[16 : 630]` reads `[8 : 315]` and
`[80 : 6930]` reads `[8 : 693]`, each cross-multiplied, while
`[44 : 105]` is the displayed pair outright. -/

example : witVal 8 3 = 495 := by decide +kernel

example : witSq 8 = 3403332 := by decide +kernel

example : witSqM 8 = 17844624 := by decide +kernel

example : witSqMM 8 = 98691732 := by decide +kernel

example : witDiffSq 8 = 829575 := by decide +kernel

example : powSum 4 8 = 8772 := by decide +kernel

example : powSum 10 5 = 10874275 := by decide +kernel

example : qLowNum 1 10 2 8 = 787587120 := by decide +kernel

example : qLowDen 1 10 2 8 = 102099960 := by decide +kernel

example : endRead 1 10 2 8 := by decide +kernel

example : endRead 1 10 1 7 := by decide +kernel

example : witSq 2 = 9 := by decide +kernel

example : witDiffSq 2 = 9 := by decide +kernel

example : witSq 1 = 0 := by decide +kernel

example : witDiffSq 1 = 0 := by decide +kernel

example : ground.getAt BPair.unit sqClosedPoly 9 = BPair.ofNat 16 := by
  decide +kernel

example : ground.getAt BPair.unit diffClosedPoly 7 = BPair.ofNat 44 := by
  decide +kernel

example : ground.getAt BPair.unit wellClosedPoly 11 = BPair.ofNat 80 := by
  decide +kernel

example : 16 * 315 = 8 * 630 := by decide +kernel

example : 80 * 693 = 8 * 6930 := by decide +kernel

/-! The difference sum's closed read carries its endpoint binder:
at the endpoint naught the cleared read's two sides sit apart at
`105` against the sum's unit, so the read refuses there, and the
difference polynomial's evaluation refuses with it — the polynomial
reads its constant key `−105` at the vacant argument while the
cleared sum is the sum's unit. -/

example : ¬ (105 * witDiffSq 0 + 147 * 0 ^ 5 + 105 * 0 ^ 4 + 23 * 0 + 105
    = 44 * 0 ^ 7 + 126 * 0 ^ 3 + 210 * 0 ^ 2) := by decide +kernel

example : ¬ ((poly.eval diffClosedPoly (BPair.ofNat 0)).oneValue
    (BPair.ofNat (105 * witDiffSq 0))) := by decide +kernel

/-! The endpoint key's three conjuncts isolated.  At the scale pair
`[10 : 1]`, the residue `1` and the endpoint `1` the comparison and
its predecessor's refusal both hold while the depth sits below two.
At the scale pair `[1 : 10]` and the residue `2` the endpoint `7`
holds the depth and the predecessor's refusal while the comparison
fails, and the endpoint `9` holds the depth and the comparison while
the predecessor already reads the comparison. -/

example : ¬ endRead 10 1 1 1 := by decide +kernel

example : 363 * (1 + 1) * 1 ^ 2 ≤ 40 * 1 ^ 4 * 10 ^ 2 := by decide +kernel

example : ¬ 363 * (1 + 1) * 1 ^ 2 ≤ 40 * (1 - 1) ^ 4 * 10 ^ 2 := by
  decide +kernel

example : ¬ endRead 1 10 2 7 := by decide +kernel

example : 2 ≤ 7 := by decide +kernel

example : ¬ 363 * (2 + 1) * 10 ^ 2 ≤ 40 * (7 - 1) ^ 4 * 1 ^ 2 := by
  decide +kernel

example : ¬ endRead 1 10 2 9 := by decide +kernel

example : 2 ≤ 9 := by decide +kernel

example : 363 * (2 + 1) * 10 ^ 2 ≤ 40 * 9 ^ 4 * 1 ^ 2 := by decide +kernel

/-! The count tier runs at the sample's endpoint data —
`r = 2`, the scale pair `[1 : 10]`, the endpoint `N = 8` — where the
lower rate reads `[787587120 : 102099960]`.  At the order `n = 10`
the head's form at the witness family reads the sum's unit, the two
sides of the kernel identity joining, and the window binder carries
slack: the order `n = N − 1` still reads the unit, while the order
`n = N − 2` does not, so the family's own window is the binder's
least honest refusal. -/

example : (inertia.quadForm
    (wellMat 2 (qLowNum 1 10 2 8) (qLowDen 1 10 2 8) 1 10 10)
    (witList 8 10)).oneValue BPair.unit :=
  witQuad 1 10 2 8 10 (by decide +kernel)

example : (inertia.quadForm
    (wellMat 2 (qLowNum 1 10 2 8) (qLowDen 1 10 2 8) 1 10 10)
    (witList 8 10)).oneValue BPair.unit := by decide +kernel

example : (inertia.quadForm
    (wellMat 2 (qLowNum 1 10 2 4) (qLowDen 1 10 2 4) 1 10 3)
    (witList 4 3)).oneValue BPair.unit := by decide +kernel

example : ¬ (inertia.quadForm
    (wellMat 2 (qLowNum 1 10 2 4) (qLowDen 1 10 2 4) 1 10 2)
    (witList 4 2)).oneValue BPair.unit := by decide +kernel

/-! At the member line `[7 : 6]` — the gap one against the second
scale six — the same family's form sits strictly below the sum's
unit.  The gap binder is isolated at the equal member line `[1 : 1]`,
where the gap is vacant and the form returns to the kernel line's
own equal-members read; the occupancy binder is isolated at the
endpoint one, where the family is vacant at every depth and the form
again reads the unit. -/

example : inertia.quadForm
    (wellMat 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 10)
    (witList 8 10) < BPair.unit :=
  witStrict 1 10 2 8 10 7 6 1 (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel)

example : inertia.quadForm
    (wellMat 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 10)
    (witList 8 10) < BPair.unit := by decide +kernel

example : ¬ (inertia.quadForm
    (wellMat 2 (1 * qLowNum 1 10 2 8) (1 * qLowDen 1 10 2 8) 1 10 10)
    (witList 8 10) < BPair.unit) := by decide +kernel

example : (inertia.quadForm
    (wellMat 2 (1 * qLowNum 1 10 2 8) (1 * qLowDen 1 10 2 8) 1 10 10)
    (witList 8 10)).oneValue BPair.unit := by decide +kernel

example : ¬ (inertia.quadForm
    (wellMat 2 (7 * qLowNum 1 10 2 1) (6 * qLowDen 1 10 2 1) 1 10 10)
    (witList 1 10) < BPair.unit) := by decide +kernel

/-! The forcing clause at the least honest order: at the endpoint
two the head is the two-by-two `[[-132840, -486000],
[-486000, -165240]]` at the member line `[7 : 6]`, whose
split is the leading-entry clearing `T = [[1, -B], [0, A]]` against
its adjugate, the block diagonal `diag(A, A(AC - B²))`.  Its
reversal count is one, the count the family forces. -/

private def sCap : elim.Mat :=
  wellMat 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 2
private def aCap : BPair := ground.getAt BPair.unit (ground.getAt [] sCap 0) 0
private def bCap : BPair := ground.getAt BPair.unit (ground.getAt [] sCap 0) 1
private def cCap : BPair := ground.getAt BPair.unit (ground.getAt [] sCap 1) 1

private def spCap : inertia.Split 2 :=
  ⟨⟨[[BPair.ofNat 1, bCap.swap], [BPair.unit, aCap]], rfl⟩,
   ⟨[[aCap, bCap], [BPair.unit, BPair.ofNat 1]], rfl⟩,
   [.one aCap, .one ((aCap * (aCap * cCap + (bCap * bCap).swap)).norm)],
   0, rfl⟩

example : inertia.splitRead sCap spCap := by decide +kernel

example : inertia.revAt spCap = 1 := by decide +kernel

example : 1 ≤ inertia.revAt spCap :=
  witCount 1 10 2 2 2 7 6 1 (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) spCap (by decide +kernel)

/-! The cap pair at the two-by-two data, the two members the
coordinate vectors.  At the diagonal `diag(-1, -1)` the leading
entry sits below the sum's unit and the doubled cross read, vacant,
sits below the diagonal product's quadruple `4`, so every split
reads the count at two — the split at the identity's own congruence
reads exactly two.  The two binders are isolated in turn: at the
identity the doubled cross read still sits below the quadruple while
the leading entry sits above the unit, and its split reads the count
nought; at the diagonal `diag(-1, 1)` the leading entry sits below
the unit while the quadruple is `-4`, below the vacant cross read,
and its split reads the count one. -/

private def xCap : List BPair := [BPair.ofNat 1, BPair.unit]
private def yCap : List BPair := [BPair.unit, BPair.ofNat 1]
private def sBoth : elim.Mat := [[⟨1, 2⟩, BPair.unit], [BPair.unit, ⟨1, 2⟩]]
private def sOne : elim.Mat := [[⟨1, 2⟩, BPair.unit], [BPair.unit, ⟨2, 1⟩]]

private def spBoth : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨1, 2⟩], 0, rfl⟩
private def spUnit : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨2, 1⟩], 0, rfl⟩
private def spOne : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨2, 1⟩], 0, rfl⟩

example : inertia.splitRead sBoth spBoth := by decide +kernel
example : inertia.splitRead (inertia.idMat 2) spUnit := by decide +kernel
example : inertia.splitRead sOne spOne := by decide +kernel

example : 2 ≤ inertia.revAt spBoth :=
  capForcing sBoth xCap yCap rfl rfl (by decide +kernel) (by decide +kernel)
    spBoth (by decide +kernel)

example : inertia.revAt spBoth = 2 := by decide +kernel

example : ¬ (inertia.quadForm (inertia.idMat 2) xCap < BPair.unit) := by
  decide +kernel

example : (elim.dotN xCap (elim.matVec (inertia.idMat 2) yCap)
      + elim.dotN yCap (elim.matVec (inertia.idMat 2) xCap))
    * (elim.dotN xCap (elim.matVec (inertia.idMat 2) yCap)
      + elim.dotN yCap (elim.matVec (inertia.idMat 2) xCap))
  < BPair.ofNat 4 * (inertia.quadForm (inertia.idMat 2) xCap
      * inertia.quadForm (inertia.idMat 2) yCap) := by decide +kernel

example : ¬ (2 ≤ inertia.revAt spUnit) := by decide +kernel

example : inertia.quadForm sOne xCap < BPair.unit := by decide +kernel

example : ¬ ((elim.dotN xCap (elim.matVec sOne yCap)
      + elim.dotN yCap (elim.matVec sOne xCap))
    * (elim.dotN xCap (elim.matVec sOne yCap)
      + elim.dotN yCap (elim.matVec sOne xCap))
  < BPair.ofNat 4 * (inertia.quadForm sOne xCap
      * inertia.quadForm sOne yCap)) := by decide +kernel

example : ¬ (2 ≤ inertia.revAt spOne) := by decide +kernel

/-! Clause (vi)'s count spine runs at the same sample.  At the member
line `[7 : 6]` and the endpoint `N = 8` the walk's minors read
`+, +, +, −, −, …`: the crossing depth is `c = 2`, the minors sitting
on the upper side through it and on the swapped side beyond, so every
split of the order-five head reads the reversal count one.  At the
line `[1 : 6]` — the numerator unscaled against the sixfold
denominator — the minors stay on the upper side to the head's end and
the count is vacant. -/

private def wA5 : elim.Mat :=
  wellMat 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 5
private def wP5 : elim.Mat :=
  wellMat 2 (qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 5

private theorem wA5lo : ∀ k, k < 2 →
    BPair.unit < wellWalk 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8)
      1 10 (k + 1) := by decide +kernel

private theorem wA5hi : ∀ k, 2 ≤ k → k < 5 →
    wellWalk 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 (k + 1)
      < BPair.unit := by
  have h : ∀ j, j < 3 →
      wellWalk 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8)
        1 10 (j + 2 + 1) < BPair.unit := by decide +kernel
  intro k hk1 hk2
  rw [← ground.subAdd hk1]
  exact h (k - 2)
    (Nat.lt_succ_of_le (Nat.sub_le_sub_right (Nat.le_of_lt_succ hk2) 2))

private theorem wP5lo : ∀ k, k < 5 →
    BPair.unit < wellWalk 2 (qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8)
      1 10 (k + 1) := by decide +kernel

example : inertia.splitRead wA5 (inertia.mkSplit 5 wA5) := by decide +kernel

example : inertia.revAt (inertia.mkSplit 5 wA5) = 1 :=
  certRevOne 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 5 2
    (by decide +kernel) wA5lo wA5hi (inertia.mkSplit 5 wA5) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 5 wA5) = 1 := by decide +kernel

example : inertia.splitRead wP5 (inertia.mkSplit 5 wP5) := by decide +kernel

example : inertia.revAt (inertia.mkSplit 5 wP5) = 0 :=
  certRevZero 2 (qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 5
    wP5lo (inertia.mkSplit 5 wP5) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 5 wP5) = 0 := by decide +kernel

/-! The crossing window is isolated at the positive line: both sign
families hold at `c = 5`, the crossing depth's own binder `c < n` is
the only one that fails, and the conclusion fails with it — the count
there is vacant, not one. -/

example : ¬ (5 < 5) := by decide +kernel

example : ¬ (∀ k, 2 ≤ k → k < 5 →
    wellWalk 2 (qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 (k + 1)
      < BPair.unit) := by
  intro h
  exact absurd (h 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel)

example : ¬ (inertia.revAt (inertia.mkSplit 5 wP5) = 1) := by decide +kernel

/-! The crossing-free arm's own binder is refused at the crossing
line: its minors leave the upper side at the depth three, and the
count there is one rather than vacant. -/

example : ¬ (∀ k, k < 5 →
    BPair.unit < wellWalk 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8)
      1 10 (k + 1)) := by
  intro h
  exact absurd (h 2 (by decide +kernel)) (by decide +kernel)

example : ¬ (inertia.revAt (inertia.mkSplit 5 wA5) = 0) := by decide +kernel

/-! The pivots' cleared data at the endpoint two, where the member
line's first minor reads `−165240`: the margin's carrier is that
minor's own count, the boundary pivot reads its slab's diagonal, and
the pivot against the recursion's witness reads the off block's
exchange. -/

example : ground.posVal
    (margP (wellWalk 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 1))
  = 165240 := by decide +kernel

example : greenprod.oneValueQ
    (pivotQ 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 1)
    (greenprod.ofM
      [[wellDiag 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 1]]) := by
  decide +kernel

example : greenprod.oneValueQ
    (greenprod.mulQ
      (pivotQ 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 2)
      (pivotR 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 2))
    (greenprod.ofM (elim.transposeM
      [[(wellBond 2 (6 * qLowDen 1 10 2 2) 10).swap]])) := by decide +kernel

/-! The two member lines' site identity at the endpoint two, the
lines `[7 : 6]` and `[8 : 7]` with the gap `7·7 = 8·6 + 1`: the
second line's scaled head is the first's against the gap's own
positive diagonal.  The gap's witness is load-bearing — at the gap
two the matrix read decides false. -/

private def wLo2 : elim.Mat :=
  wellMat 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 2
private def wUp2 : elim.Mat :=
  wellMat 2 (8 * qLowNum 1 10 2 2) (7 * qLowDen 1 10 2 2) 1 10 2

example : elim.matOneValue
    (elim.matAdd (inertia.matScaleB (BPair.ofNat 7) wLo2)
      (inertia.matScaleB
        (BPair.ofNat ((2 + 1) * (1 * qLowNum 1 10 2 2))
          * BPair.ofPos 1 * BPair.ofPos 10)
        (inertia.idMat 2)))
    (inertia.matScaleB (BPair.ofNat 6) wUp2) :=
  lineSite 2 (qLowNum 1 10 2 2) (qLowDen 1 10 2 2) 1 10 2 7 6 8 7 1 (by decide +kernel)

example : elim.matOneValue
    (elim.matAdd (inertia.matScaleB (BPair.ofNat 7) wLo2)
      (inertia.matScaleB
        (BPair.ofNat ((2 + 1) * (1 * qLowNum 1 10 2 2))
          * BPair.ofPos 1 * BPair.ofPos 10)
        (inertia.idMat 2)))
    (inertia.matScaleB (BPair.ofNat 6) wUp2) := by decide +kernel

example : ¬ elim.matOneValue
    (elim.matAdd (inertia.matScaleB (BPair.ofNat 7) wLo2)
      (inertia.matScaleB
        (BPair.ofNat ((2 + 1) * (2 * qLowNum 1 10 2 2))
          * BPair.ofPos 1 * BPair.ofPos 10)
        (inertia.idMat 2)))
    (inertia.matScaleB (BPair.ofNat 6) wUp2) := by decide +kernel

/-! The multiple cut's downward closure at the endpoint two, where
the member line's minors sit on the swapped side from the depth one,
so the crossing depth is the nought: the upper line `[8 : 7]` reads
the count one, forced from below by the witness family and from above
by the site datum's positive diagonal.  The order conjunct is the
lines' own — exchanging them refuses it. -/

private theorem wLo2hi : ∀ k, 0 ≤ k → k < 2 →
    wellWalk 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 (k + 1)
      < BPair.unit := by
  have h : ∀ j, j < 2 →
      wellWalk 2 (7 * qLowNum 1 10 2 2) (6 * qLowDen 1 10 2 2) 1 10 (j + 1)
        < BPair.unit := by decide +kernel
  intro k _ hk
  exact h k hk

example : inertia.splitRead wLo2 (inertia.mkSplit 2 wLo2) := by decide +kernel

example : inertia.splitRead wUp2 (inertia.mkSplit 2 wUp2) := by decide +kernel

example : inertia.revAt (inertia.mkSplit 2 wUp2) = 1 :=
  cutFlat 1 10 2 2 2 0 7 6 8 7 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) wLo2hi
    (inertia.mkSplit 2 wLo2) (by decide +kernel)
    (inertia.mkSplit 2 wUp2) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 2 wUp2) = 1 := by decide +kernel

example : ¬ (7 * 7 ≤ 8 * 6) := by decide +kernel

example : 8 * 6 ≤ 7 * 7 := by decide +kernel

/-! The lower rate's two data are occupied at the endpoint eight, and
each of the three binders is isolated: at the endpoint one the family
is vacant and both data read nought, while at a vacant scale member
the denominator alone dies with the numerator standing. -/

example : 0 < qLowNum 1 10 2 8 ∧ 0 < qLowDen 1 10 2 8 :=
  qLowPos 1 10 2 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ¬ (0 < qLowNum 1 10 2 1) := by decide +kernel

example : ¬ (0 < qLowDen 1 10 2 1) := by decide +kernel

example : ¬ (0 < qLowDen 0 10 2 8) := by decide +kernel

example : 0 < qLowNum 0 10 2 8 := by decide +kernel

example : ¬ (0 < qLowDen 1 0 2 8) := by decide +kernel

example : 0 < qLowNum 1 0 2 8 := by decide +kernel

/-! The composed cut at an interior head: the endpoint four at the
scale pair `[1:3]`, the head order five holding the family whole, and
the member lines `[7:6]` against `[8:7]` — the crossing at the
boundary pivot, the count one at both lines, the equal-lines instance
running the vacant-gap arm.  The regime read beside them: at the
endpoint's key already holding at the depth one, the endpoint depth
is the two outright, the leastness's own arm. -/

example : endRead 1 3 2 4 := by decide +kernel

example : endRead 10 1 1 2 := by decide +kernel

private def wLo45 : elim.Mat :=
  wellMat 2 (7 * qLowNum 1 3 2 4) (6 * qLowDen 1 3 2 4) 1 3 5

private def wUp45 : elim.Mat :=
  wellMat 2 (8 * qLowNum 1 3 2 4) (7 * qLowDen 1 3 2 4) 1 3 5

private theorem wLo45hi : ∀ k, 0 ≤ k → k < 5 →
    wellWalk 2 (7 * qLowNum 1 3 2 4) (6 * qLowDen 1 3 2 4) 1 3 (k + 1)
      < BPair.unit := by
  have h : ∀ j, j < 5 →
      wellWalk 2 (7 * qLowNum 1 3 2 4) (6 * qLowDen 1 3 2 4) 1 3 (j + 1)
        < BPair.unit := by decide +kernel
  intro k _ hk
  exact h k hk

example : inertia.revAt (inertia.mkSplit 5 wUp45) = 1 :=
  cutFlat 1 3 2 4 5 0 7 6 8 7 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) wLo45hi
    (inertia.mkSplit 5 wLo45) (by decide +kernel)
    (inertia.mkSplit 5 wUp45) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 5 wUp45) = 1 := by decide +kernel

example : inertia.revAt (inertia.mkSplit 5 wLo45) = 1 :=
  cutFlat 1 3 2 4 5 0 7 6 7 6 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) wLo45hi
    (inertia.mkSplit 5 wLo45) (by decide +kernel)
    (inertia.mkSplit 5 wLo45) (by decide +kernel)

/-! The cap pair at the well head: the second family at the endpoint
two, the cap line `(12:1)` beyond both endpoints' rates at the gaps
`238500` and `378`, the compressed pencil's entries the closed
power-sum reads — each diagonal entry the line read's own gap and
the doubled cross the mixed folds' value `-11556` — and every split
of the order-four head reading the count at two, the raw count
beside the theorem route with the line reads' and the cross read's
own cells beside their raw decides.  The refusals isolate the
load-bearing binders in turn: the discriminant at the degenerate
second family `N' = N`, where the doubled cross squares exactly to
the diagonal product's quadruple and the count-one head at the line
`(9:1)` parts the conclusion; the two line ties at forged gaps,
each with the discriminant holding at the forged values and the
count-one head parting; the window binder at the order-one
head, the n-free hypotheses holding at the committed data with the
discriminant's own cell beside them; and the endpoint order
`N' ≤ N` at the second family past the window — with `N ≤ n` it
hands the second family its own window read `N' ≤ n`, the line
read's consumed order, the theorem's hypotheses symmetric in the
two endpoints so the naming keeps every instance, and the refusal's
data hold every further binder at the order parted, the count-one
order-two head. -/

private def wCap45 : elim.Mat :=
  wellMat 2 (2 * qLowNum 1 3 2 4) (1 * qLowDen 1 3 2 4) 1 3 5

private def wCapN : elim.Mat := wellMat 2 12 1 1 3 4

example : crossSq 4 2 = 45 := by decide +kernel
example : crossSqM 4 2 = 45 := by decide +kernel
example : crossSqMM 4 2 = 45 := by decide +kernel
example : crossBond 4 2 = 144 := by decide +kernel

example : (crossVal 2 12 1 1 3 4 2).oneValue (BPair.ofNat 11556).swap := by
  decide +kernel

example : (elim.dotN (witList 4 4) (elim.matVec wCapN (witList 2 4))
    + elim.dotN (witList 2 4)
      (elim.matVec wCapN (witList 4 4))).oneValue
    (crossVal 2 12 1 1 3 4 2) :=
  crossRead 2 12 1 4 2 4 1 3 (by decide +kernel) (by decide +kernel)

example : (elim.dotN (witList 4 4) (elim.matVec wCapN (witList 2 4))
    + elim.dotN (witList 2 4)
      (elim.matVec wCapN (witList 4 4))).oneValue
    (crossVal 2 12 1 1 3 4 2) := by
  decide +kernel

example : (inertia.quadForm wCapN (witList 4 4)).oneValue
    (BPair.ofNat 238500).swap :=
  witLineRead 1 3 2 4 4 12 1 238500 (by decide +kernel)
    (by decide +kernel)

example : (inertia.quadForm wCapN (witList 4 4)).oneValue
    (BPair.ofNat 238500).swap := by decide +kernel

example : (inertia.quadForm wCapN (witList 2 4)).oneValue
    (BPair.ofNat 378).swap :=
  witLineRead 1 3 2 2 4 12 1 378 (by decide +kernel) (by decide +kernel)

example : 2 ≤ inertia.revAt (inertia.mkSplit 4 wCapN) :=
  capPair 1 3 2 4 2 4 12 1 238500 378 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (inertia.mkSplit 4 wCapN) (by decide +kernel)

example : 2 ≤ inertia.revAt (inertia.mkSplit 4 wCapN) := by decide +kernel

private def wCap9 : elim.Mat := wellMat 2 9 1 1 3 4

example : qLowNum 1 3 2 4 * 1 + 63054 = 9 * qLowDen 1 3 2 4 := by
  decide +kernel
example : ¬ (crossVal 2 9 1 1 3 4 4 * crossVal 2 9 1 1 3 4 4
    < BPair.ofNat (4 * (63054 * 63054))) := by decide +kernel
example : inertia.revAt (inertia.mkSplit 4 wCap9) = 1 := by decide +kernel
example : inertia.splitRead wCap9 (inertia.mkSplit 4 wCap9) := by
  decide +kernel

example : crossVal 2 9 1 1 3 4 2 * crossVal 2 9 1 1 3 4 2
    < BPair.ofNat (4 * (238500 * 135)) := by decide +kernel
example : qLowNum 1 3 2 2 * 1 + 135 = 9 * qLowDen 1 3 2 2 := by
  decide +kernel
example : ¬ (qLowNum 1 3 2 4 * 1 + 238500 = 9 * qLowDen 1 3 2 4) := by
  decide +kernel

example : crossVal 2 9 1 1 3 4 2 * crossVal 2 9 1 1 3 4 2
    < BPair.ofNat (4 * (63054 * 135000)) := by decide +kernel
example : ¬ (qLowNum 1 3 2 2 * 1 + 135000 = 9 * qLowDen 1 3 2 2) := by
  decide +kernel

example : crossVal 2 12 1 1 3 4 2 * crossVal 2 12 1 1 3 4 2
    < BPair.ofNat (4 * (238500 * 378)) := by decide +kernel
example : inertia.revAt
    (inertia.mkSplit 1 (wellMat 2 12 1 1 3 1)) = 1 := by decide +kernel
example : inertia.splitRead (wellMat 2 12 1 1 3 1)
    (inertia.mkSplit 1 (wellMat 2 12 1 1 3 1)) := by decide +kernel

example : qLowNum 1 3 2 2 * 1 + 216 = 10 * qLowDen 1 3 2 2 := by
  decide +kernel
example : qLowNum 1 3 2 4 * 1 + 121536 = 10 * qLowDen 1 3 2 4 := by
  decide +kernel
example : crossVal 2 10 1 1 3 2 4 * crossVal 2 10 1 1 3 2 4
    < BPair.ofNat (4 * (216 * 121536)) := by decide +kernel
example : inertia.revAt
    (inertia.mkSplit 2 (wellMat 2 10 1 1 3 2)) = 1 := by decide +kernel
example : inertia.splitRead (wellMat 2 10 1 1 3 2)
    (inertia.mkSplit 2 (wellMat 2 10 1 1 3 2)) := by decide +kernel

/-! The rates\' gap at the cut member `[7:6]`, its data occupied and
its tie the one cross-multiplied identity. -/

example : gapLow 1 3 2 4 1 6 = (463284, 350892) := by decide +kernel

example : 0 < (gapLow 1 3 2 4 1 6).1 ∧ 0 < (gapLow 1 3 2 4 1 6).2 :=
  gapLow_pos 1 3 2 4 1 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : qLowNum 1 3 2 4 * (6 * qLowDen 1 3 2 4)
      + 1 * qLowNum 1 3 2 4 * qLowDen 1 3 2 4
    = 7 * qLowNum 1 3 2 4 * qLowDen 1 3 2 4 :=
  gapLow_tie 1 3 2 4 1 6 7 rfl

example : qLowNum 1 3 2 4 * (6 * qLowDen 1 3 2 4)
      + 1 * qLowNum 1 3 2 4 * qLowDen 1 3 2 4
    = 7 * qLowNum 1 3 2 4 * qLowDen 1 3 2 4 := by decide +kernel

/-! The arithmetic tier's statements at decided instances: each
theorem's read beside its own kernel decide, one pair per statement. -/

example : powSum 0 8 = 8 :=
  powSum0_closed 8

example : powSum 0 8 = 8 := by decide +kernel

example : 2 * powSum 1 8 = 8 ^ 2 + 8 :=
  powSum1_closed 8

example : 2 * powSum 1 8 = 8 ^ 2 + 8 := by decide +kernel

example : 6 * powSum 2 8 = 2 * 8 ^ 3 + 3 * 8 ^ 2 + 8 :=
  powSum2_closed 8

example : 6 * powSum 2 8 = 2 * 8 ^ 3 + 3 * 8 ^ 2 + 8 := by decide +kernel

example : 4 * powSum 3 8 = 8 ^ 4 + 2 * 8 ^ 3 + 8 ^ 2 :=
  powSum3_closed 8

example : 4 * powSum 3 8 = 8 ^ 4 + 2 * 8 ^ 3 + 8 ^ 2 := by decide +kernel

example : 30 * powSum 4 8 + 8 = 6 * 8 ^ 5 + 15 * 8 ^ 4 + 10 * 8 ^ 3 :=
  powSum4_closed 8

example : 30 * powSum 4 8 + 8 = 6 * 8 ^ 5 + 15 * 8 ^ 4 + 10 * 8 ^ 3 := by decide +kernel

example : 12 * powSum 5 8 + 8 ^ 2 = 2 * 8 ^ 6 + 6 * 8 ^ 5 + 5 * 8 ^ 4 :=
  powSum5_closed 8

example : 12 * powSum 5 8 + 8 ^ 2 = 2 * 8 ^ 6 + 6 * 8 ^ 5 + 5 * 8 ^ 4 := by decide +kernel

example : 42 * powSum 6 8 + 7 * 8 ^ 3 = 6 * 8 ^ 7 + 21 * 8 ^ 6 + 21 * 8 ^ 5 + 8 :=
  powSum6_closed 8

example : 42 * powSum 6 8 + 7 * 8 ^ 3 = 6 * 8 ^ 7 + 21 * 8 ^ 6 + 21 * 8 ^ 5 + 8 := by decide +kernel

example : 24 * powSum 7 8 + 7 * 8 ^ 4 = 3 * 8 ^ 8 + 12 * 8 ^ 7 + 14 * 8 ^ 6 + 2 * 8 ^ 2 :=
  powSum7_closed 8

example : 24 * powSum 7 8 + 7 * 8 ^ 4 = 3 * 8 ^ 8 + 12 * 8 ^ 7 + 14 * 8 ^ 6 + 2 * 8 ^ 2 := by decide +kernel

example : 90 * powSum 8 8 + 42 * 8 ^ 5 + 3 * 8 = 10 * 8 ^ 9 + 45 * 8 ^ 8 + 60 * 8 ^ 7 + 20 * 8 ^ 3 :=
  powSum8_closed 8

example : 90 * powSum 8 8 + 42 * 8 ^ 5 + 3 * 8 = 10 * 8 ^ 9 + 45 * 8 ^ 8 + 60 * 8 ^ 7 + 20 * 8 ^ 3 := by decide +kernel

example : 20 * powSum 9 8 + 14 * 8 ^ 6 + 3 * 8 ^ 2 = 2 * 8 ^ 10 + 10 * 8 ^ 9 + 15 * 8 ^ 8 + 10 * 8 ^ 4 :=
  powSum9_closed 8

example : 20 * powSum 9 8 + 14 * 8 ^ 6 + 3 * 8 ^ 2 = 2 * 8 ^ 10 + 10 * 8 ^ 9 + 15 * 8 ^ 8 + 10 * 8 ^ 4 := by decide +kernel

example : 66 * powSum 10 5 + 66 * 5 ^ 7 + 33 * 5 ^ 3 = 6 * 5 ^ 11 + 33 * 5 ^ 10 + 55 * 5 ^ 9 + 66 * 5 ^ 5 + 5 * 5 :=
  powSum10_closed 5

example : 66 * powSum 10 5 + 66 * 5 ^ 7 + 33 * 5 ^ 3 = 6 * 5 ^ 11 + 33 * 5 ^ 10 + 55 * 5 ^ 9 + 66 * 5 ^ 5 + 5 * 5 := by decide +kernel

example : witSq 8 + 2 * 8 ^ 2 * powSum 6 8 = 8 ^ 4 * powSum 4 8 + powSum 8 8 :=
  witSq_bridge 8

example : witSq 8 + 2 * 8 ^ 2 * powSum 6 8 = 8 ^ 4 * powSum 4 8 + powSum 8 8 := by decide +kernel

example : witSqM 8 + 2 * 8 ^ 2 * powSum 7 8 = 8 ^ 4 * powSum 5 8 + powSum 9 8 :=
  witSqM_bridge 8

example : witSqM 8 + 2 * 8 ^ 2 * powSum 7 8 = 8 ^ 4 * powSum 5 8 + powSum 9 8 := by decide +kernel

example : witSqMM 8 + 2 * 8 ^ 2 * powSum 8 8 = 8 ^ 4 * powSum 6 8 + powSum 10 8 :=
  witSqMM_bridge 8

example : witSqMM 8 + 2 * 8 ^ 2 * powSum 8 8 = 8 ^ 4 * powSum 6 8 + powSum 10 8 := by decide +kernel

example : witDiffSq 8 + 2 * 8 ^ 2 * powSum 0 (8 - 1) + 12 * 8 ^ 2 * powSum 1 (8 - 1) + 28 * 8 ^ 2 * powSum 2 (8 - 1) + 32 * 8 ^ 2 * powSum 3 (8 - 1) + 16 * 8 ^ 2 * powSum 4 (8 - 1) = powSum 0 (8 - 1) + 8 ^ 4 * powSum 0 (8 - 1) + 8 * powSum 1 (8 - 1) + 4 * 8 ^ 4 * powSum 1 (8 - 1) + 28 * powSum 2 (8 - 1) + 4 * 8 ^ 4 * powSum 2 (8 - 1) + 56 * powSum 3 (8 - 1) + 68 * powSum 4 (8 - 1) + 48 * powSum 5 (8 - 1) + 16 * powSum 6 (8 - 1) :=
  witDiffSq_bridge 8

example : witDiffSq 8 + 2 * 8 ^ 2 * powSum 0 (8 - 1) + 12 * 8 ^ 2 * powSum 1 (8 - 1) + 28 * 8 ^ 2 * powSum 2 (8 - 1) + 32 * 8 ^ 2 * powSum 3 (8 - 1) + 16 * 8 ^ 2 * powSum 4 (8 - 1) = powSum 0 (8 - 1) + 8 ^ 4 * powSum 0 (8 - 1) + 8 * powSum 1 (8 - 1) + 4 * 8 ^ 4 * powSum 1 (8 - 1) + 28 * powSum 2 (8 - 1) + 4 * 8 ^ 4 * powSum 2 (8 - 1) + 56 * powSum 3 (8 - 1) + 68 * powSum 4 (8 - 1) + 48 * powSum 5 (8 - 1) + 16 * powSum 6 (8 - 1) := by decide +kernel

example : 630 * witSq 8 + 105 * 8 ^ 5 + 21 * 8 = 16 * 8 ^ 9 + 110 * 8 ^ 3 :=
  witSq_closed 8

example : 630 * witSq 8 + 105 * 8 ^ 5 + 21 * 8 = 16 * 8 ^ 9 + 110 * 8 ^ 3 := by decide +kernel

example : 60 * witSqM 8 + 12 * 8 ^ 6 + 9 * 8 ^ 2 = 8 ^ 10 + 20 * 8 ^ 4 :=
  witSqM_closed 8

example : 60 * witSqM 8 + 12 * 8 ^ 6 + 9 * 8 ^ 2 = 8 ^ 10 + 20 * 8 ^ 4 := by decide +kernel

example : 6930 * witSqMM 8 + 1617 * 8 ^ 7 + 3003 * 8 ^ 3 = 80 * 8 ^ 11 + 4015 * 8 ^ 5 + 525 * 8 :=
  witSqMM_closed 8

example : 6930 * witSqMM 8 + 1617 * 8 ^ 7 + 3003 * 8 ^ 3 = 80 * 8 ^ 11 + 4015 * 8 ^ 5 + 525 * 8 := by decide +kernel

example : 105 * witDiffSq 8 + 147 * 8 ^ 5 + 105 * 8 ^ 4 + 23 * 8 + 105 = 44 * 8 ^ 7 + 126 * 8 ^ 3 + 210 * 8 ^ 2 :=
  witDiffSq_closed 8 (by decide +kernel)

example : 105 * witDiffSq 8 + 147 * 8 ^ 5 + 105 * 8 ^ 4 + 23 * 8 + 105 = 44 * 8 ^ 7 + 126 * 8 ^ 3 + 210 * 8 ^ 2 := by decide +kernel

example : (BPair.ofNat (marg 7 3 ^ 2)).oneValue (BPair.ofCounts 7 3 * BPair.ofCounts 7 3) :=
  margSq_read 7 3

example : (BPair.ofNat (marg 7 3 ^ 2)).oneValue (BPair.ofCounts 7 3 * BPair.ofCounts 7 3) := by decide +kernel

example : (BPair.ofNat (marg 3 7 ^ 2)).oneValue (BPair.ofCounts 3 7 * BPair.ofCounts 3 7) :=
  margSq_read 3 7

example : (BPair.ofNat (marg 3 7 ^ 2)).oneValue (BPair.ofCounts 3 7 * BPair.ofCounts 3 7) := by decide +kernel

example : (poly.eval sqClosedPoly (BPair.ofNat 8)).oneValue (BPair.ofNat (630 * witSq 8)) :=
  sqClosedPoly_eval 8

example : (poly.eval sqClosedPoly (BPair.ofNat 8)).oneValue (BPair.ofNat (630 * witSq 8)) := by decide +kernel

example : (poly.eval diffClosedPoly (BPair.ofNat 8)).oneValue (BPair.ofNat (105 * witDiffSq 8)) :=
  diffClosedPoly_eval 8 (by decide +kernel)

example : (poly.eval diffClosedPoly (BPair.ofNat 8)).oneValue (BPair.ofNat (105 * witDiffSq 8)) := by decide +kernel

example : (poly.eval wellClosedPoly (BPair.ofNat 8)).oneValue (BPair.ofNat (6930 * witSqMM 8)) :=
  wellClosedPoly_eval 8

example : (poly.eval wellClosedPoly (BPair.ofNat 8)).oneValue (BPair.ofNat (6930 * witSqMM 8)) := by decide +kernel

example : 4 * 1 ^ 2 * 80 * 630 * (11 * (2 + 1) * 10) = 6930 * (1 * 10 * (2 + 1) * 16) * (20 * 1) :=
  topWell_read 1 10 2

example : 4 * 1 ^ 2 * 80 * 630 * (11 * (2 + 1) * 10) = 6930 * (1 * 10 * (2 + 1) * 16) * (20 * 1) := by decide +kernel

example : (2 + 1) * 10 ^ 2 * 44 * 630 * (2 * 1) = 105 * (1 * 10 * (2 + 1) * 16) * (33 * 10) :=
  topDiff_read 1 10 2

example : (2 + 1) * 10 ^ 2 * 44 * 630 * (2 * 1) = 105 * (1 * 10 * (2 + 1) * 16) * (33 * 10) := by decide +kernel

example : (20 * 1 * 8 ^ 2) * (2 * 1 * 8 ^ 2) = 363 * (2 + 1) * 10 ^ 2
    ↔ 40 * 8 ^ 4 * 1 ^ 2 = 363 * (2 + 1) * 10 ^ 2 :=
  keyEq_read 1 10 2 8

example : ((20 * 1 * 8 ^ 2) * (2 * 1 * 8 ^ 2) = 363 * (2 + 1) * 10 ^ 2
    ↔ 40 * 8 ^ 4 * 1 ^ 2 = 363 * (2 + 1) * 10 ^ 2) := by decide +kernel

example : (BPair.ofNat (2 * witSq 4)).oneValue
    (BPair.ofNat (2 * ground.sumNat ((List.range 4).map (fun k =>
        witVal 4 (k + 1) * witVal 4 (k + 2))))
      + BPair.ofNat ((witVal 4 1) ^ 2)
      + ground.bsum (fun k =>
          BPair.ofCounts (witVal 4 (k + 2)) (witVal 4 (k + 1))
            * BPair.ofCounts (witVal 4 (k + 2)) (witVal 4 (k + 1)))
        (List.range 4)) :=
  witTele 4

example : (BPair.ofNat (2 * witSq 4)).oneValue
    (BPair.ofNat (2 * ground.sumNat ((List.range 4).map (fun k =>
        witVal 4 (k + 1) * witVal 4 (k + 2))))
      + BPair.ofNat ((witVal 4 1) ^ 2)
      + ground.bsum (fun k =>
          BPair.ofCounts (witVal 4 (k + 2)) (witVal 4 (k + 1))
            * BPair.ofCounts (witVal 4 (k + 2)) (witVal 4 (k + 1)))
        (List.range 4)) := by decide +kernel

example : (ground.bsum (fun k =>
        poly.evalClear (diagPoly 1 3 2 (k + 1)) (BPair.ofPos 1) 1 2
          * (BPair.ofNat (witVal 2 (k + 1))
              * BPair.ofNat (witVal 2 (k + 1))))
      (List.range 2)).oneValue
    (BPair.ofNat 2
        * (BPair.ofNat ((1 + 1) * 2) * BPair.ofPos 1 * BPair.ofPos 1)
        * BPair.ofNat (ground.sumNat ((List.range 2).map (fun k =>
            witVal 2 (k + 1) * witVal 2 (k + 2))))
      + BPair.ofNat ((1 + 1) * 2) * BPair.ofPos 1 * BPair.ofPos 1
        * BPair.ofNat ((witVal 2 1) ^ 2)
      + BPair.ofNat ((1 + 1) * 2) * BPair.ofPos 1 * BPair.ofPos 1
        * ground.bsum (fun k =>
            BPair.ofCounts (witVal 2 (k + 2)) (witVal 2 (k + 1))
              * BPair.ofCounts (witVal 2 (k + 2)) (witVal 2 (k + 1)))
          (List.range 2)
      + ground.bsum (fun k =>
          (BPair.ofNat (4 * 2 * ((k + 1) * (k + 1) + 1 * (k + 1)))
              * BPair.ofPos 1 * BPair.ofPos 1
            + (BPair.ofNat ((1 + 1) * 3) * BPair.ofPos 1
                * BPair.ofPos 1).swap)
            * (BPair.ofNat (witVal 2 (k + 1))
                * BPair.ofNat (witVal 2 (k + 1))))
        (List.range 2)) :=
  witForm 1 3 2 2 1 1

example : (ground.bsum (fun k =>
        poly.evalClear (diagPoly 1 3 2 (k + 1)) (BPair.ofPos 1) 1 2
          * (BPair.ofNat (witVal 2 (k + 1))
              * BPair.ofNat (witVal 2 (k + 1))))
      (List.range 2)).oneValue
    (BPair.ofNat 2
        * (BPair.ofNat ((1 + 1) * 2) * BPair.ofPos 1 * BPair.ofPos 1)
        * BPair.ofNat (ground.sumNat ((List.range 2).map (fun k =>
            witVal 2 (k + 1) * witVal 2 (k + 2))))
      + BPair.ofNat ((1 + 1) * 2) * BPair.ofPos 1 * BPair.ofPos 1
        * BPair.ofNat ((witVal 2 1) ^ 2)
      + BPair.ofNat ((1 + 1) * 2) * BPair.ofPos 1 * BPair.ofPos 1
        * ground.bsum (fun k =>
            BPair.ofCounts (witVal 2 (k + 2)) (witVal 2 (k + 1))
              * BPair.ofCounts (witVal 2 (k + 2)) (witVal 2 (k + 1)))
          (List.range 2)
      + ground.bsum (fun k =>
          (BPair.ofNat (4 * 2 * ((k + 1) * (k + 1) + 1 * (k + 1)))
              * BPair.ofPos 1 * BPair.ofPos 1
            + (BPair.ofNat ((1 + 1) * 3) * BPair.ofPos 1
                * BPair.ofPos 1).swap)
            * (BPair.ofNat (witVal 2 (k + 1))
                * BPair.ofNat (witVal 2 (k + 1))))
        (List.range 2)) := by decide +kernel

/-! `lem:cornerpivot`(ii)'s canonical carrier algebra and the box
device.  The collapse bridges are anchored at the shifted square
scale `sh1`, the shifted scale read `u1` and a two-slab profile with
both slabs occupied at two outer keys, each decided instance beside
its theorem route.  The box device runs at the profile whose one
u⁰-slab key carries the origin coefficient ten with the u¹-slab
vacant, on the box `[0 : 4]` at the interior cut `2`, the priced
bound `[8 : 2]`, the square-scale ceiling four, both floors one and
the clearing one; the vacant cut list is decided beside it, the
chained cover is anchored at the two-piece chain over the constant
polynomial eight, and the scale-tail read and the step clearance run
at their own data.  Every conjunct and every theorem binder is
classified at an isolating instance.  The read conjuncts are refused
with the surviving conjuncts decided true beside each refusal — the
shape clearing at a coefficient past the stated power, the
square-scale tie at a forged ceiling over two occupied outer keys,
the second floor's positivity at a swapped floor, the two caps each
at a forged floor with the clearing's power discriminated at a
rational ceiling, one piece of a chained cover, and both conjuncts
of the step clearance and of the scale-tail read — and each refusal
whose conjunct is load-bearing for the theorem sits beside the
premises decided true and the conclusion decided false.  The
theorem's own premises are refused one at a time at certificates the
read accepts: the scale bound past the ceiling, and the box's two
membership reads at a depth past the top and below the floor. -/

/-- A two-slab profile with both slabs occupied at two outer keys. -/
private def twoSlab : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 1], [BPair.ofNat 2]],
   [[BPair.ofNat 1], [BPair.ofNat 1]])

example : poly.oneValue (depthPoly (profAdd sh1 u1) 2)
    (poly.add (depthPoly sh1 2) (depthPoly u1 2)) := by decide +kernel

example : poly.oneValue (depthPoly (profAdd sh1 u1) 2)
    (poly.add (depthPoly sh1 2) (depthPoly u1 2)) :=
  depthPoly_profAdd sh1 u1 2

example : poly.oneValue (depthPoly (profMul twoSlab u1) 2)
    (poly.mul (depthPoly twoSlab 2) (depthPoly u1 2)) := by decide +kernel

example : poly.oneValue (depthPoly (profMul twoSlab u1) 2)
    (poly.mul (depthPoly twoSlab 2) (depthPoly u1 2)) :=
  depthPoly_profMul twoSlab u1 2

example : poly.oneValue (depthPoly (profShift sh1) 3) (depthPoly sh1 4) := by
  decide +kernel

example : poly.oneValue (depthPoly (profShift sh1) 3) (depthPoly sh1 4) :=
  depthPoly_profShift sh1 3

example : poly.oneValue (depthPoly (profShift twoSlab) 1)
    (depthPoly twoSlab 2) := by decide +kernel

example : poly.oneValue (depthPoly (profShift twoSlab) 1)
    (depthPoly twoSlab 2) :=
  depthPoly_profShift twoSlab 1

example : poly.oneValue (depthPoly (profScale 3 twoSlab) 2)
    (poly.scaleP (BPair.ofNat 3) (depthPoly twoSlab 2)) := by decide +kernel

example : poly.oneValue (depthPoly (profScale 3 twoSlab) 2)
    (poly.scaleP (BPair.ofNat 3) (depthPoly twoSlab 2)) :=
  depthPoly_profScale twoSlab 3 2

example : poly.oneValue (depthPoly (profNeg twoSlab) 2)
    (poly.neg (depthPoly twoSlab 2)) := by decide +kernel

example : poly.oneValue (depthPoly (profNeg twoSlab) 2)
    (poly.neg (depthPoly twoSlab 2)) :=
  depthPoly_profNeg twoSlab 2

example : poly.oneValue (depthPoly (diagProf 1 3 2) 2) (diagPoly 1 3 2 2) := by
  decide +kernel

example : poly.oneValue (depthPoly (diagProf 1 3 2) 2) (diagPoly 1 3 2 2) :=
  depthPoly_diagProf 1 3 2 2

example : poly.oneValue (depthPoly (termProf u1 1 3 2) 1)
    (termPoly u1 1 3 2 1) := by decide +kernel

example : poly.oneValue (depthPoly (termProf u1 1 3 2) 1)
    (termPoly u1 1 3 2 1) :=
  depthPoly_termProf u1 1 3 2 1

/-- The box device's fixture profile: one occupied u⁰-slab key at the
origin coefficient ten, the u¹-slab vacant. -/
private def boxV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]], ([] : poly.PPoly))

/-- The fixture certificate: the box `[0 : 4]` at the interior cut
`2`, the priced bound `[8 : 2]`, the square-scale ceiling four, the
four floors one, the clearing one. -/
private def boxC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, [⟨BPair.ofNat 2, 1⟩],
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 1⟩

example : boxRead boxV (BPair.ofNat 1) 1 boxC := by decide +kernel

example : boxRead boxV (BPair.ofNat 1) 1
    { boxC with cuts := ([] : List CPair) } := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly boxV 2) (BPair.ofPos 1) 1 1 := by
  decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly boxV 2) (BPair.ofPos 1) 1 boxC.K :=
  boxRead_pos boxV (BPair.ofNat 1) 1 boxC (by decide +kernel) 2 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- the box device at a genuinely rational ceiling, the fourth
example : boxRead boxV (BPair.ofNat 1) 4 boxC := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly boxV 2) (BPair.ofPos 1) 8 1 := by
  decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly boxV 2) (BPair.ofPos 1) 8 boxC.K :=
  boxRead_pos boxV (BPair.ofNat 1) 4 boxC (by decide +kernel) 2 1 8
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The four-arm fixture: both slabs occupied at two outer keys,
every remainder arm's comparison live. -/
private def armV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 50, BPair.ofNat 2, (BPair.ofNat 1).swap],
    [BPair.ofNat 1, (BPair.ofNat 1).swap]],
   [[BPair.ofNat 1, (BPair.ofNat 1).swap]])

/-- The four-arm certificate: the box `[0 : 1]` at the priced bound
`[2 : 1]`, the squared floor five at the live squared chain, the
clearing two. -/
private def armC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 5, BPair.ofNat 2, 2⟩

example : boxRead armV (BPair.ofNat 1) 1 armC := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly armV 1) (BPair.ofPos 1) 1 2 := by
  decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly armV 1) (BPair.ofPos 1) 1 armC.K :=
  boxRead_pos armV (BPair.ofNat 1) 1 armC (by decide +kernel) 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The box-priced side read's widening: a scale key at one
thousand, read on the box against the floors' join at the unit —
while the ceiling fold prices the key at its whole magnitude, and
the floors' join at that price refuses the chain. -/
private def wV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10, BPair.ofNat 1000]], ([] : poly.PPoly))

private def wC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.unit, BPair.unit, BPair.ofNat 1, BPair.unit, 1⟩

example : boxRead wV (BPair.ofNat 1) 1 wC := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly wV 2) (BPair.ofPos 1) 1 wC.K :=
  boxRead_pos wV (BPair.ofNat 1) 1 wC (by decide +kernel) 2 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- the ceiling fold's price of the same key, and the floors' join
-- at that price refusing the chain
example : (capS (BPair.ofNat 1) 1 (BPair.ofNat 4) 1
    (wV.1.map (List.drop 1))).oneValue (BPair.ofNat 1000) := by
  decide +kernel

example : ¬ chainRead (poly.add (profBase wV)
    (poly.neg [BPair.ofNat 1000 + BPair.ofNat 1]))
    (BPair.ofNat 8) (BPair.ofNat 2)
    (wC.lo :: wC.cuts ++ [wC.hi]) := by decide +kernel

/-- The first leading floor absorbing a negative scale key: the
side chain at the floor four, the collapse positive at the box
top. -/
private def nV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10, (BPair.ofNat 3).swap]], ([] : poly.PPoly))

private def nC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 4, BPair.unit, BPair.ofNat 1, BPair.unit, 1⟩

example : boxRead nV (BPair.ofNat 1) 1 nC := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly nV 2) (BPair.ofPos 1) 1 nC.K :=
  boxRead_pos nV (BPair.ofNat 1) 1 nC (by decide +kernel) 2 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : chainRead [BPair.ofNat 8] (BPair.ofNat 8) (BPair.ofNat 2)
    [stage.unitC, ⟨BPair.ofNat 2, 1⟩, ⟨BPair.ofNat 4, 1⟩] := by
  decide +kernel

example : stage.unitC < stage.evalC [BPair.ofNat 8] ⟨BPair.ofNat 3, 1⟩ :=
  chainRead_all [BPair.ofNat 8] (BPair.ofNat 8) (BPair.ofNat 2)
    [stage.unitC, ⟨BPair.ofNat 2, 1⟩, ⟨BPair.ofNat 4, 1⟩]
    ⟨BPair.ofNat 3, 1⟩ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : lowRead [BPair.ofNat 10, BPair.ofNat 1] (BPair.ofNat 1) 1 1 := by
  decide +kernel

example : BPair.unit < poly.evalClear [BPair.ofNat 10, BPair.ofNat 1]
    (BPair.ofPos 1) 1 1 :=
  lowRead_pos [BPair.ofNat 10, BPair.ofNat 1] (BPair.ofNat 1) 1 1
    (by decide +kernel) (by decide +kernel) 1 1 (by decide +kernel)

-- the scale-tail read at a genuinely rational ceiling, the fourth
example : lowRead [BPair.ofNat 10, BPair.ofNat 1] (BPair.ofNat 1) 4 1 := by
  decide +kernel

example : BPair.unit < poly.evalClear [BPair.ofNat 10, BPair.ofNat 1]
    (BPair.ofPos 1) 8 1 :=
  lowRead_pos [BPair.ofNat 10, BPair.ofNat 1] (BPair.ofNat 1) 4 1
    (by decide +kernel) (by decide +kernel) 1 8 (by decide +kernel)

example : stepClear ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 9, 1⟩
    (BPair.ofNat 1) 1 := by
  decide +kernel

example : (⟨BPair.ofNat ((2 + 1) * (2 + 1)) * BPair.ofPos 1, 1⟩ : CPair)
    ≤ ⟨BPair.ofNat 9, 1⟩ :=
  stepClear_step ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 9, 1⟩ (BPair.ofNat 1) 1
    (by decide +kernel) 2 1 1 (by decide +kernel) (by decide +kernel)

/-- The scale-free part's chained floor, the box read's fifth
conjunct. -/
private abbrev floorChain (V : poly.PPoly × poly.PPoly)
    (C : BoxCert) : Prop :=
  chainRead (poly.add (profBase V)
      (poly.neg [C.f1L + C.f1D + (C.f2L + C.f2D)]))
    C.bN C.bD (C.lo :: C.cuts ++ [C.hi])

/-- The scale coefficients' chained side read, the box read's
seventh conjunct. -/
private abbrev linChain (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) : Prop :=
  chainRead (poly.add [C.f1L * BPair.ofPos e0d]
      (poly.scaleP e0n (profLin V)))
    C.bN C.bD (C.lo :: C.cutsL ++ [C.hi])

/-- The u-slab origins' squared chained read, the box read's
eighth conjunct. -/
private abbrev sqChain (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) : Prop :=
  chainRead (poly.add [C.f2L * C.f2L * BPair.ofPos e0d]
      (poly.neg (poly.scaleP e0n
        (poly.shiftUp 1 (poly.mul (profBaseU V) (profBaseU V))))))
    C.bN C.bD (C.lo :: C.cutsU ++ [C.hi])

/-- The deeper u⁰ tails' ceiling fold, the box read's ninth
conjunct. -/
private abbrev tailCapB (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) : Prop :=
  e0n * (e0n * capS e0n e0d C.shB C.K (V.1.map (List.drop 2)))
    ≤ C.f1D * BPair.ofPos (Pos.powC e0d (C.K + 2))

/-- The deeper u¹ tails' squared ceiling fold, the box read's
tenth conjunct. -/
private abbrev slabCapD (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) : Prop :=
  e0n * (C.shB
      * ((e0n * capS e0n e0d C.shB C.K (V.2.map (List.drop 1)))
        * (e0n * capS e0n e0d C.shB C.K (V.2.map (List.drop 1)))))
    ≤ C.f2D * C.f2D * BPair.ofPos (Pos.powC e0d (2 * C.K + 3))

/-! Each restating name is pinned to its conjunct: the projection
elaborates exactly where the name's body is the box read's own
clause, so a respell of either side refuses the build. -/

example (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) (h : boxRead V e0n e0d C) : floorChain V C :=
  h.2.2.2.2.1

example (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) (h : boxRead V e0n e0d C) : linChain V e0n e0d C :=
  h.2.2.2.2.2.2.1

example (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) (h : boxRead V e0n e0d C) : sqChain V e0n e0d C :=
  h.2.2.2.2.2.2.2.1

example (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) (h : boxRead V e0n e0d C) : tailCapB V e0n e0d C :=
  h.2.2.2.2.2.2.2.2.1

example (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) (h : boxRead V e0n e0d C) : slabCapD V e0n e0d C :=
  h.2.2.2.2.2.2.2.2.2

/-! The committed refusals, one isolating instance per conjunct. -/

/-- The shape clearing's isolating refusal: a coefficient past the
stated clearing sits unpriced at a depth the cleared evaluation
never truncates — every other conjunct decided true, the deep
coefficient's ceiling fold paid at the floor one hundred, and the
collapse's value below the sum's unit at the scale two. -/
private def sV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 110, BPair.unit, (BPair.ofNat 100).swap]],
   ([] : poly.PPoly))

private def sC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 100, BPair.ofNat 1, BPair.ofNat 1, 0⟩

example : ¬ boxRead sV (BPair.ofNat 1) 1 sC := by decide +kernel

example : ¬ profShape sV sC.K := by decide +kernel

example : sC.hi ≤ stage.ofB sC.shB
    ∧ BPair.unit ≤ sC.f2L ∧ BPair.unit ≤ sC.f2D
    ∧ floorChain sV sC
    ∧ BPair.unit ≤ sC.f1L
    ∧ linChain sV (BPair.ofNat 1) 1 sC
    ∧ sqChain sV (BPair.ofNat 1) 1 sC
    ∧ tailCapB sV (BPair.ofNat 1) 1 sC
    ∧ slabCapD sV (BPair.ofNat 1) 1 sC := by decide +kernel

example : BPair.ofPos 2 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 2
    ∧ sC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 2, 2⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 2, 2⟩ : CPair) ≤ sC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly sV 1) (BPair.ofPos 2) 2 sC.K) := by
  decide +kernel

/-- The square-scale tie's isolating refusal: a ceiling forged
below the box's top under-weights the deeper fold's price, every
other conjunct decided true at the deep outer key's paid floor,
and the collapse's value below the sum's unit at the box top. -/
private def fV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 79],
    [BPair.unit, BPair.unit, (BPair.ofNat 25).swap]],
   ([] : poly.PPoly))

private def fC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 3,
   BPair.ofNat 1, BPair.ofNat 75, BPair.ofNat 1, BPair.ofNat 1, 3⟩

example : ¬ boxRead fV (BPair.ofNat 1) 1 fC := by decide +kernel

example : ¬ (fC.hi ≤ stage.ofB fC.shB) := by decide +kernel

example : profShape fV fC.K
    ∧ BPair.unit ≤ fC.f2L ∧ BPair.unit ≤ fC.f2D
    ∧ floorChain fV fC
    ∧ BPair.unit ≤ fC.f1L
    ∧ linChain fV (BPair.ofNat 1) 1 fC
    ∧ sqChain fV (BPair.ofNat 1) 1 fC
    ∧ tailCapB fV (BPair.ofNat 1) 1 fC
    ∧ slabCapD fV (BPair.ofNat 1) 1 fC := by decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ fC.lo ≤ (⟨BPair.ofNat (2 * 2) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (2 * 2) * BPair.ofPos 1, 1⟩ : CPair) ≤ fC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly fV 2) (BPair.ofPos 1) 1 fC.K) := by
  decide +kernel

/-- The squared floor's sign guard, isolated: the floor's square
clears its chain while the read-back's sign refuses — the occupied
u-slab origin drives the collapse below the sum's unit with every
other conjunct decided true. -/
private def gV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]], [[(BPair.ofNat 40).swap]])

private def gC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair),
   [⟨BPair.ofNat 1, 1⟩, ⟨BPair.ofNat 2, 1⟩, ⟨BPair.ofNat 3, 1⟩],
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, (BPair.ofNat 81).swap,
   BPair.ofNat 1, 1⟩

example : ¬ boxRead gV (BPair.ofNat 1) 1 gC := by decide +kernel

example : ¬ (BPair.unit ≤ gC.f2L) := by decide +kernel

example : profShape gV gC.K
    ∧ gC.hi ≤ stage.ofB gC.shB
    ∧ BPair.unit ≤ gC.f2D
    ∧ floorChain gV gC
    ∧ BPair.unit ≤ gC.f1L
    ∧ linChain gV (BPair.ofNat 1) 1 gC
    ∧ sqChain gV (BPair.ofNat 1) 1 gC
    ∧ tailCapB gV (BPair.ofNat 1) 1 gC
    ∧ slabCapD gV (BPair.ofNat 1) 1 gC := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gV 1) (BPair.ofPos 1) 1 gC.K) := by
  decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ gC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ gC.hi := by
  decide +kernel

/-- The deeper squared floor's sign guard, isolated: the deep
u-slab key's squared fold clears at the floor's square while the
read-back's sign refuses, the collapse below the sum's unit. -/
private def gdV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]], [[BPair.unit, (BPair.ofNat 40).swap]])

private def gdC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
   (BPair.ofNat 81).swap, 2⟩

example : ¬ boxRead gdV (BPair.ofNat 1) 1 gdC := by decide +kernel

example : ¬ (BPair.unit ≤ gdC.f2D) := by decide +kernel

example : profShape gdV gdC.K
    ∧ gdC.hi ≤ stage.ofB gdC.shB
    ∧ BPair.unit ≤ gdC.f2L
    ∧ floorChain gdV gdC
    ∧ BPair.unit ≤ gdC.f1L
    ∧ linChain gdV (BPair.ofNat 1) 1 gdC
    ∧ sqChain gdV (BPair.ofNat 1) 1 gdC
    ∧ tailCapB gdV (BPair.ofNat 1) 1 gdC
    ∧ slabCapD gdV (BPair.ofNat 1) 1 gdC := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gdV 1) (BPair.ofPos 1) 1 gdC.K) := by
  decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ gdC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ gdC.hi := by
  decide +kernel

/-- The floor chain's isolating refusal: the scale coefficient
forces the first leading floor past the base, the floors' join
refused with every other conjunct decided true and the collapse at
the sum's unit exactly. -/
private def bV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 4, (BPair.ofNat 4).swap]], ([] : poly.PPoly))

private def bC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   [⟨BPair.ofNat 1, 1⟩, ⟨BPair.ofNat 2, 1⟩, ⟨BPair.ofNat 3, 1⟩],
   ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 17, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 1⟩

example : ¬ boxRead bV (BPair.ofNat 1) 1 bC := by decide +kernel

example : ¬ floorChain bV bC := by decide +kernel

example : profShape bV bC.K
    ∧ bC.hi ≤ stage.ofB bC.shB
    ∧ BPair.unit ≤ bC.f2L ∧ BPair.unit ≤ bC.f2D
    ∧ BPair.unit ≤ bC.f1L
    ∧ linChain bV (BPair.ofNat 1) 1 bC
    ∧ sqChain bV (BPair.ofNat 1) 1 bC
    ∧ tailCapB bV (BPair.ofNat 1) 1 bC
    ∧ slabCapD bV (BPair.ofNat 1) 1 bC := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly bV 1) (BPair.ofPos 1) 1 bC.K) := by
  decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ bC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ bC.hi := by
  decide +kernel

/-- The first leading floor's sign guard, isolated: the clearing
ratio eats the recovered arm — the side chain holds at the lower
floor's balance partner, the base clears the shrunken join, and at
the clearing two against the scale one the collapse reads below
the sum's unit with every other conjunct decided true. -/
private def rV : poly.PPoly × poly.PPoly :=
  ([[(BPair.ofNat 5).swap, BPair.ofNat 9]],
   [[(BPair.ofNat 1).swap]])

private def rC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   (BPair.ofNat 8).swap, BPair.unit, BPair.ofNat 2, BPair.unit, 1⟩

example : ¬ boxRead rV (BPair.ofNat 1) 1 rC := by decide +kernel

example : ¬ (BPair.unit ≤ rC.f1L) := by decide +kernel

example : profShape rV rC.K
    ∧ rC.hi ≤ stage.ofB rC.shB
    ∧ BPair.unit ≤ rC.f2L ∧ BPair.unit ≤ rC.f2D
    ∧ floorChain rV rC
    ∧ linChain rV (BPair.ofNat 1) 1 rC
    ∧ sqChain rV (BPair.ofNat 1) 1 rC
    ∧ tailCapB rV (BPair.ofNat 1) 1 rC
    ∧ slabCapD rV (BPair.ofNat 1) 1 rC := by decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 2
    ∧ rC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 2⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 2⟩ : CPair) ≤ rC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly rV 1) (BPair.ofPos 1) 2 rC.K) := by
  decide +kernel

/-- The side chain's isolating refusal: a scale coefficient below
the floor's reach drives the collapse below the sum's unit, the
chain refused with every other conjunct decided true. -/
private def lV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10, (BPair.ofNat 40).swap]], ([] : poly.PPoly))

private def lC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 1⟩

example : ¬ boxRead lV (BPair.ofNat 1) 1 lC := by decide +kernel

example : ¬ linChain lV (BPair.ofNat 1) 1 lC := by decide +kernel

example : profShape lV lC.K
    ∧ lC.hi ≤ stage.ofB lC.shB
    ∧ BPair.unit ≤ lC.f2L ∧ BPair.unit ≤ lC.f2D
    ∧ floorChain lV lC
    ∧ BPair.unit ≤ lC.f1L
    ∧ sqChain lV (BPair.ofNat 1) 1 lC
    ∧ tailCapB lV (BPair.ofNat 1) 1 lC
    ∧ slabCapD lV (BPair.ofNat 1) 1 lC := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly lV 1) (BPair.ofPos 1) 1 lC.K) := by
  decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ lC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ lC.hi := by
  decide +kernel

/-- The squared chain's isolating refusal: an occupied u-slab
origin past the squared floor's reach, the chain refused with
every other conjunct decided true and the collapse below the
sum's unit. -/
private def uV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]], [[(BPair.ofNat 40).swap]])

private def uC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 1⟩

example : ¬ boxRead uV (BPair.ofNat 1) 1 uC := by decide +kernel

example : ¬ sqChain uV (BPair.ofNat 1) 1 uC := by decide +kernel

example : profShape uV uC.K
    ∧ uC.hi ≤ stage.ofB uC.shB
    ∧ BPair.unit ≤ uC.f2L ∧ BPair.unit ≤ uC.f2D
    ∧ floorChain uV uC
    ∧ BPair.unit ≤ uC.f1L
    ∧ linChain uV (BPair.ofNat 1) 1 uC
    ∧ tailCapB uV (BPair.ofNat 1) 1 uC
    ∧ slabCapD uV (BPair.ofNat 1) 1 uC := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly uV 1) (BPair.ofPos 1) 1 uC.K) := by
  decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ uC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ uC.hi := by
  decide +kernel

/-- The deeper u⁰ fold's clearing power: one deep u⁰ key whose
ceiling fold fails at the unit ceiling and passes at the ceiling
one quarter. -/
private def tV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10, BPair.unit, (BPair.ofNat 2).swap]],
   ([] : poly.PPoly))

private def tC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 2⟩

example : boxRead tV (BPair.ofNat 1) 4 tC := by decide +kernel

example : ¬ boxRead tV (BPair.ofNat 1) 1 tC := by decide +kernel

example : ¬ tailCapB tV (BPair.ofNat 1) 1 tC := by decide +kernel

/-- The deeper u⁰ fold's isolating refusal: a deep u⁰ key past the
vacant floor's reach drives the collapse below the sum's unit, the
fold refused with every other conjunct decided true. -/
private def tV2 : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10, BPair.unit, (BPair.ofNat 1000).swap]],
   ([] : poly.PPoly))

private def tC2 : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.unit, BPair.ofNat 1, BPair.unit, 2⟩

example : ¬ boxRead tV2 (BPair.ofNat 1) 1 tC2 := by decide +kernel

example : ¬ tailCapB tV2 (BPair.ofNat 1) 1 tC2 := by decide +kernel

example : profShape tV2 tC2.K
    ∧ tC2.hi ≤ stage.ofB tC2.shB
    ∧ BPair.unit ≤ tC2.f2L ∧ BPair.unit ≤ tC2.f2D
    ∧ floorChain tV2 tC2
    ∧ BPair.unit ≤ tC2.f1L
    ∧ linChain tV2 (BPair.ofNat 1) 1 tC2
    ∧ sqChain tV2 (BPair.ofNat 1) 1 tC2
    ∧ slabCapD tV2 (BPair.ofNat 1) 1 tC2 := by decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ tC2.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ tC2.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly tV2 1) (BPair.ofPos 1) 1 tC2.K) := by
  decide +kernel

/-- The deeper u¹ fold's clearing power: one deep u¹ key whose
squared ceiling fold fails at the unit ceiling and passes at the
ceiling one quarter. -/
private def dV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]], [[BPair.unit, (BPair.ofNat 1).swap]])

private def dC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 2⟩

example : boxRead dV (BPair.ofNat 1) 4 dC := by decide +kernel

example : ¬ boxRead dV (BPair.ofNat 1) 1 dC := by decide +kernel

example : ¬ slabCapD dV (BPair.ofNat 1) 1 dC := by decide +kernel

/-- The deeper u¹ fold's isolating refusal: a deep u¹ key past the
vacant floor's square drives the collapse below the sum's unit,
the fold refused with every other conjunct decided true. -/
private def dV2 : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]],
   [[BPair.unit, (BPair.ofNat 1000).swap]])

private def dC2 : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.unit, BPair.ofNat 1, BPair.unit, 2⟩

example : ¬ boxRead dV2 (BPair.ofNat 1) 1 dC2 := by decide +kernel

example : ¬ slabCapD dV2 (BPair.ofNat 1) 1 dC2 := by decide +kernel

example : profShape dV2 dC2.K
    ∧ dC2.hi ≤ stage.ofB dC2.shB
    ∧ BPair.unit ≤ dC2.f2L ∧ BPair.unit ≤ dC2.f2D
    ∧ floorChain dV2 dC2
    ∧ BPair.unit ≤ dC2.f1L
    ∧ linChain dV2 (BPair.ofNat 1) 1 dC2
    ∧ sqChain dV2 (BPair.ofNat 1) 1 dC2
    ∧ tailCapB dV2 (BPair.ofNat 1) 1 dC2 := by decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ dC2.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 1⟩ : CPair) ≤ dC2.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly dV2 1) (BPair.ofPos 1) 1 dC2.K) := by
  decide +kernel

/-- The premises' isolating refusals: a certificate the read
accepts whose conclusion fails at a depth past the box's top and
at a scale past the ceiling, one premise refused each with the
further premises decided true. -/
private def pV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 50], [BPair.unit, (BPair.ofNat 10).swap]],
   ([] : poly.PPoly))

private def pC : BoxCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, ([] : List CPair),
   [⟨BPair.ofNat 1, 1⟩, ⟨BPair.ofNat 2, 1⟩, ⟨BPair.ofNat 3, 1⟩],
   ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 41, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, 2⟩

example : boxRead pV (BPair.ofNat 1) 1 pC := by decide +kernel

-- the box's top: `hhi` refused at the depth three
example : ¬ ((⟨BPair.ofNat (3 * 3) * BPair.ofPos 1, 1⟩ : CPair)
    ≤ pC.hi) := by decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ pC.lo ≤ (⟨BPair.ofNat (3 * 3) * BPair.ofPos 1, 1⟩ : CPair) := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly pV 3) (BPair.ofPos 1) 1 pC.K) := by
  decide +kernel

-- the ceiling: `he` refused at the scale four
example : ¬ (BPair.ofPos 4 * BPair.ofPos 1
    ≤ BPair.ofNat 1 * BPair.ofPos 1) := by decide +kernel

example : pC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 4, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 4, 1⟩ : CPair) ≤ pC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly pV 1) (BPair.ofPos 4) 1 pC.K) := by
  decide +kernel

/-- The box floor's isolating refusal: an occupied floor with the
depth nought below it, the collapse's origin on the lower side. -/
private def oV : poly.PPoly × poly.PPoly :=
  ([[(BPair.ofNat 1).swap], [BPair.ofNat 8]], ([] : poly.PPoly))

private def oC : BoxCert :=
  ⟨⟨BPair.ofNat 1, 1⟩, ⟨BPair.ofNat 4, 1⟩,
   [⟨BPair.ofNat 3, 2⟩, ⟨BPair.ofNat 5, 2⟩],
   ([] : List CPair), ([] : List CPair),
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 1, BPair.unit, BPair.ofNat 1, BPair.unit, 1⟩

example : boxRead oV (BPair.ofNat 1) 1 oC := by decide +kernel

example : ¬ (oC.lo
    ≤ (⟨BPair.ofNat (0 * 0) * BPair.ofPos 1, 1⟩ : CPair)) := by
  decide +kernel

example : (⟨BPair.ofNat (0 * 0) * BPair.ofPos 1, 1⟩ : CPair) ≤ oC.hi
    ∧ BPair.ofPos 1 * BPair.ofPos 1
      ≤ BPair.ofNat 1 * BPair.ofPos 1 := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly oV 0) (BPair.ofPos 1) 1 oC.K) := by
  decide +kernel

-- one piece of a chained cover refused, the surviving piece decided
example : ¬ chainRead [BPair.ofNat 8] (BPair.ofNat 8) (BPair.ofNat 2)
    [stage.unitC, ⟨BPair.ofNat 4, 1⟩, ⟨BPair.ofNat 2, 1⟩] := by
  decide +kernel

example : chainRead [BPair.ofNat 8] (BPair.ofNat 8) (BPair.ofNat 2)
    [stage.unitC, ⟨BPair.ofNat 4, 1⟩] := by decide +kernel

-- the step clearance's two conjuncts
example : ¬ stepClear stage.unitC stage.unitC (BPair.ofNat 1) 1 := by
  decide +kernel

example : stage.ofB (BPair.ofNat 4) * (stage.unitC * stage.ofB (BPair.ofNat 1))
    ≤ (stage.unitC + CPair.swap stage.unitC
        + CPair.swap (stage.ofB (BPair.ofNat 1)))
      * (stage.unitC + CPair.swap stage.unitC
        + CPair.swap (stage.ofB (BPair.ofNat 1))) := by decide +kernel

example : ¬ stepClear ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 6, 1⟩
    (BPair.ofNat 1) 1 := by
  decide +kernel

example : (⟨BPair.ofNat 4, 1⟩ : CPair) + stage.ofB (BPair.ofNat 1)
    ≤ ⟨BPair.ofNat 6, 1⟩ := by decide +kernel

example : ¬ ((⟨BPair.ofNat ((2 + 1) * (2 + 1)) * BPair.ofPos 1, 1⟩ : CPair)
    ≤ ⟨BPair.ofNat 6, 1⟩) := by decide +kernel

-- the scale-tail read's two conjuncts
example : ¬ lowRead [BPair.unit, BPair.ofNat 1]
    (BPair.ofNat 1).swap 1 1 := by
  decide +kernel

example : (BPair.ofNat 1).swap
    * capF (BPair.ofNat 1).swap 1 1
        (List.drop 1 [BPair.unit, BPair.ofNat 1])
    < ground.getAt BPair.unit [BPair.unit, BPair.ofNat 1] 0
      * BPair.ofPos (Pos.powC 1 (1 + 1)) := by
  decide +kernel

example : ¬ lowRead [BPair.ofNat 1, (BPair.ofNat 4).swap]
    (BPair.ofNat 1) 1 1 := by
  decide +kernel

-- the cleared conjunct isolated at the rational ceiling: the tail's
-- price passes at the unit ceiling and fails at the ceiling three
-- halves
example : lowRead [BPair.ofNat 3, BPair.ofNat 2] (BPair.ofNat 1) 1 1 := by
  decide +kernel

example : ¬ lowRead [BPair.ofNat 3, BPair.ofNat 2]
    (BPair.ofNat 3) 2 1 := by
  decide +kernel

example : BPair.unit
    < ground.getAt BPair.unit [BPair.ofNat 3, BPair.ofNat 2] 0 := by
  decide +kernel

example : BPair.unit
    < ground.getAt BPair.unit [BPair.ofNat 1, (BPair.ofNat 4).swap] 0 := by
  decide +kernel

example : ¬ (BPair.unit < poly.evalClear
    [BPair.ofNat 1, (BPair.ofNat 4).swap] (BPair.ofPos 1) 1 1) := by
  decide +kernel

/-! The monotone core at the landed member-line family: the head at
the endpoint four and the order five, the lines `[2:1]`, `[7:6]` and
`[8:7]`.  The cross-multiplied order carries the count downward — the
cap line's count two against the member line's one is the strict
instance, and the two member lines `[7:6]` and `[8:7]` sit at
equality.  The binders classify beside the routes: the
cross-multiplied order is refused at the exchanged lines with the
conclusion failing, each certificate hypothesis at a split forged
against the other line's head at one shared line pair, and the
scale pairs' positive members are the pair carrier's own frame
(`def:ground`'s occupied data). -/

example : inertia.revAt (inertia.mkSplit 5 wCap45) = 3 := by decide +kernel

example : inertia.revAt (inertia.mkSplit 5 wUp45) = 1 := by decide +kernel

example : inertia.revAt (inertia.mkSplit 5 wLo45) = 1 := by decide +kernel

example : inertia.revAt (inertia.mkSplit 5 wUp45)
    ≤ inertia.revAt (inertia.mkSplit 5 wCap45) :=
  cutMono 2 (qLowNum 1 3 2 4) (qLowDen 1 3 2 4) 1 3 5 2 1 8 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 5 wCap45) (by decide +kernel)
    (inertia.mkSplit 5 wUp45) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 5 wUp45)
    ≤ inertia.revAt (inertia.mkSplit 5 wLo45) :=
  cutMono 2 (qLowNum 1 3 2 4) (qLowDen 1 3 2 4) 1 3 5 7 6 8 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 5 wLo45) (by decide +kernel)
    (inertia.mkSplit 5 wUp45) (by decide +kernel)

-- the cross-multiplied order refused at the exchanged lines, the
-- conclusion failing with it
example : ¬ ((2 : Nat) * 7 ≤ 8 * 1) := by decide +kernel

example : ¬ (inertia.revAt (inertia.mkSplit 5 wCap45)
    ≤ inertia.revAt (inertia.mkSplit 5 wUp45)) := by decide +kernel

-- the two certificate hypotheses refused at splits forged against
-- the other line's head, the line pair shared so the order holds
example : ¬ inertia.splitRead wCap45 (inertia.mkSplit 5 wUp45) := by
  decide +kernel

example : ¬ inertia.splitRead wUp45 (inertia.mkSplit 5 wCap45) := by
  decide +kernel

/-! The scale strip and its collapse bridge.  The vacancy fixture
carries both slabs' origin coefficients at the sum's unit, so the
whole collapse is the stripped collapse's scale shift; at an occupied
u-slab origin the read fails and the bridge's conclusion fails with
it, the u⁰-slab's own vacancy standing. -/

/-- The vacancy fixture: both slabs vacant at the origin key. -/
private def vacV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5]], [[BPair.unit, BPair.ofNat 3]])

example : profVac vacV := by decide +kernel

example : profStrip vacV = ([[BPair.ofNat 5]], [[BPair.ofNat 3]]) := by
  decide +kernel

example : poly.oneValue (depthPoly vacV 2)
    (poly.shiftUp 1 (depthPoly (profStrip vacV) 2)) := by decide +kernel

example : poly.oneValue (depthPoly vacV 2)
    (poly.shiftUp 1 (depthPoly (profStrip vacV) 2)) :=
  depthPoly_profStrip vacV 2 (by decide +kernel)

/-- The graded device's fixture profile: the u⁰-slab vacant at the
origin with the scale key five, the u-slab's origin three. -/
private def gradV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5]], [[BPair.ofNat 3]])

example : ¬ profVac gradV := by decide +kernel

example : poly.unitTail (profBase gradV) := by decide +kernel

example : ¬ poly.oneValue (depthPoly gradV 2)
    (poly.shiftUp 1 (depthPoly (profStrip gradV) 2)) := by decide +kernel

example : profBaseU gradV = [BPair.ofNat 3] := by decide +kernel

example : profLin gradV = [BPair.ofNat 5] := by decide +kernel

/-- The fixture certificate: the box `[0 : 4]` at one piece, the
stated cap two — the cap's square scale four reaching the box's
top — and the shape clearing one. -/
private def gradC : GradCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, [], [2], 0, 1⟩

example : gradRead gradV (BPair.ofNat 1) 1 gradC := by decide +kernel

example : stage.unitC ≤ pieceB gradV stage.unitC ⟨BPair.ofNat 4, 1⟩
    ∧ stage.unitC < pieceL gradV (BPair.ofNat 1) 1 0 2
        stage.unitC ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 4, 1⟩ := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly gradV 2) (BPair.ofPos 1) 1 gradC.K :=
  gradRead_pos gradV (BPair.ofNat 1) 1 gradC (by decide +kernel) 2 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : BPair.unit
    < poly.evalClear (depthPoly gradV 1) (BPair.ofPos 1) 1 gradC.K :=
  gradRead_pos gradV (BPair.ofNat 1) 1 gradC (by decide +kernel) 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : BPair.unit
    < poly.evalClear (depthPoly gradV 2) (BPair.ofPos 1) 1 1 := by
  decide +kernel

/-- The graded fixture's certificate at a genuinely rational
ceiling, the fourth: the box `[0 : 1]` at one piece, the stated
cap two whose square scale at the quarter reads one, the box's
top. -/
private def gradCR : GradCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [], [2], 0, 1⟩

example : gradRead gradV (BPair.ofNat 1) 4 gradCR := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly gradV 2) (BPair.ofPos 1) 8 gradCR.K :=
  gradRead_pos gradV (BPair.ofNat 1) 4 gradCR (by decide +kernel) 2 1 8
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : BPair.unit
    < poly.evalClear (depthPoly gradV 2) (BPair.ofPos 1) 8 1 := by
  decide +kernel

/-! The two degenerate arms at a committed degenerate spot.  At the
residue two, the rate `[16 : 3]` and the scale `[3 : 4]` the walk's
minors read `1, 36, 0, −746496, −1719926784`: the depth two carries
equal members exactly, the depth one sits on the upper side and every
depth beyond the spot on the swapped side.  At the order four the
spot is interior (`c = 1`) and every split of the head reads the
count one; at the order two the spot is the head's own last minor and
every split reads the count vacant. -/

private def wDg4 : elim.Mat := wellMat 2 16 3 3 4 4

private def wDg2 : elim.Mat := wellMat 2 16 3 3 4 2

example : wellWalk 2 16 3 3 4 1 = BPair.ofNat 36 := by decide +kernel

example : (wellWalk 2 16 3 3 4 2).oneValue BPair.unit := by decide +kernel

example : wellWalk 2 16 3 3 4 3 < BPair.unit := by decide +kernel

example : wellWalk 2 16 3 3 4 4 < BPair.unit := by decide +kernel

private theorem dgLo : ∀ k, k < 1 → BPair.unit < wellWalk 2 16 3 3 4 (k + 1) := by
  decide +kernel

private theorem dgHi : ∀ k, 1 + 1 ≤ k → k < 4 →
    wellWalk 2 16 3 3 4 (k + 1) < BPair.unit := by
  have h : ∀ j, j < 2 →
      wellWalk 2 16 3 3 4 (j + 2 + 1) < BPair.unit := by decide +kernel
  intro k hk1 hk2
  rw [← ground.subAdd hk1]
  exact h (k - 2)
    (Nat.lt_succ_of_le (Nat.sub_le_sub_right (Nat.le_of_lt_succ hk2) 2))

example : inertia.splitRead wDg4 (inertia.mkSplit 4 wDg4) := by decide +kernel

example : inertia.revAt (inertia.mkSplit 4 wDg4) = 1 :=
  certRevOneMixed 2 16 3 3 4 4 1 (by decide +kernel) dgLo dgHi
    (inertia.mkSplit 4 wDg4) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 4 wDg4) = 1 := by decide +kernel

private theorem dgKernLo : ∀ k, k + 1 < 2 →
    BPair.unit < wellWalk 2 16 3 3 4 (k + 1) := by decide +kernel

example : inertia.splitRead wDg2 (inertia.mkSplit 2 wDg2) := by decide +kernel

example : inertia.revAt (inertia.mkSplit 2 wDg2) = 0 :=
  certRevZeroKern 2 16 3 3 4 2 dgKernLo (by decide +kernel)
    (inertia.mkSplit 2 wDg2) (by decide +kernel)

example : inertia.revAt (inertia.mkSplit 2 wDg2) = 0 := by decide +kernel

-- the degeneracy binder refused at the crossing family's order
-- three: the shallow family holds with the last walk off equal
-- members, and the count is one, not vacant
example : ¬ ((wellWalk 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8)
    1 10 3).oneValue BPair.unit) := by decide +kernel

example : ∀ k, k + 1 < 3 →
    BPair.unit < wellWalk 2 (7 * qLowNum 1 10 2 8)
      (6 * qLowDen 1 10 2 8) 1 10 (k + 1) := by decide +kernel

example : inertia.splitRead
    (wellMat 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 3)
    (inertia.mkSplit 3
      (wellMat 2 (7 * qLowNum 1 10 2 8)
        (6 * qLowDen 1 10 2 8) 1 10 3)) := by decide +kernel

example : ¬ (inertia.revAt (inertia.mkSplit 3
    (wellMat 2 (7 * qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 3))
    = 0) := by decide +kernel

-- the certificate hypothesis refused at a split forged against the
-- boundary-degenerate head, its count one against the vacant read
example : ¬ inertia.splitRead (wellMat 2 16 3 3 4 2)
    (inertia.mkSplit 2 wUp2) := by decide +kernel

example : ¬ (inertia.revAt (inertia.mkSplit 2 wUp2) = 0) := by
  decide +kernel

/-! The spot's own binder is isolated at the boundary: at the order
two the same data satisfy all three sign families at `c = 1` — the
shallow family at the depth one, the degeneracy at the depth two, and
the deep family vacuously — and the interior binder `c + 2 ≤ n` alone
fails.  The count there is vacant, not one: the boundary arm carries
it.  The deep family cannot be broken at a degenerate spot in this
family: the walk's own recursion forces `D_{c+2} = (β²D_c).swap`, so
the first deep minor is on the swapped side whenever the shallow
family holds.  The deep family's own refusal reads at the
crossing-free walk: the positive line holds every further binder at
the spot nought with the count vacant, not one. -/

example : ¬ (1 + 2 ≤ 2) := by decide +kernel

example : ¬ (∀ k, 0 + 1 ≤ k → k < 5 →
    wellWalk 2 (qLowNum 1 10 2 8) (6 * qLowDen 1 10 2 8) 1 10 (k + 1)
      < BPair.unit) := fun h =>
  absurd (h 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel)

example : (0 : Nat) + 2 ≤ 5 := by decide +kernel

example : (∀ k, k < 1 → BPair.unit < wellWalk 2 16 3 3 4 (k + 1))
    ∧ (wellWalk 2 16 3 3 4 (1 + 1)).oneValue BPair.unit
    ∧ (∀ k, 1 + 1 ≤ k → k < 2 →
        wellWalk 2 16 3 3 4 (k + 1) < BPair.unit) :=
  ⟨by decide +kernel, by decide +kernel,
   fun k hk1 hk2 => absurd (Nat.lt_of_lt_of_le hk2 hk1) (Nat.lt_irrefl k)⟩

example : ¬ (inertia.revAt (inertia.mkSplit 2 wDg2) = 1) := by decide +kernel

/-! The shallow family's isolating refusal: a head whose last read
is equal members with the first minor on the lower side — the
degeneracy and the certificate hold, the shallow family alone is
refused, and the count is one rather than vacant. -/

example : (wellWalk 3 30 3 2 4 2).oneValue BPair.unit := by decide +kernel

example : ¬ (∀ k, k + 1 < 2 →
    BPair.unit < wellWalk 3 30 3 2 4 (k + 1)) := by
  intro h
  exact absurd (h 0 (by decide +kernel)) (by decide +kernel)

example : inertia.splitRead (wellMat 3 30 3 2 4 2)
    (inertia.mkSplit 2 (wellMat 3 30 3 2 4 2)) := by decide +kernel

example : ¬ (inertia.revAt (inertia.mkSplit 2 (wellMat 3 30 3 2 4 2))
    = 0) := by decide +kernel

/-! The graded device's committed refusals, each isolating one
conjunct with the surviving ones decided true beside it: the shape
clearing at a deep key past a forged clearing, the vacancy at an
occupied u⁰-slab origin, the stated cap's square scale at a forged
cap under the piece's top — with the validity's load-bearing
witness, a vacant cap admitting a false conclusion at an occupied
u-tail — the line arm's origin floor at a u-slab origin below its
balance partner, its forge admitting a false conclusion at depth
two, the caps' one-per-piece shape at a withdrawn and at an
excess cap list, the chain at a stalled piece, and the two slabs'
deep tails read at the ceiling's powers with the ceiling's two
members each load-bearing. -/

-- the shape clearing
private def gsV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 110, BPair.unit, (BPair.ofNat 100).swap]],
   [[BPair.ofNat 3]])

private def gsC : GradCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, [], [2], 0, 1⟩

example : ¬ gradRead gsV (BPair.ofNat 1) 1 gsC := by decide +kernel

example : ¬ profShape gsV gsC.K := by decide +kernel

example : poly.unitTail (profBase gsV)
    ∧ chainK gsV (BPair.ofNat 1) 1 gsC.hi gsC.hk
        (gsC.lo :: gsC.cuts ++ [gsC.hi]) gsC.mcaps := by
  decide +kernel

example : BPair.ofPos 2 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 2
    ∧ gsC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 2, 2⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 2, 2⟩ : CPair) ≤ gsC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gsV 1) (BPair.ofPos 2) 2 gsC.K) := by
  decide +kernel

-- the vacancy conjunct
private def occV : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 7, BPair.ofNat 5]], [[BPair.ofNat 3]])

example : ¬ gradRead occV (BPair.ofNat 1) 1 gradC := by decide +kernel

example : ¬ poly.unitTail (profBase occV) := by decide +kernel

example : profShape occV gradC.K
    ∧ chainK occV (BPair.ofNat 1) 1 gradC.hi gradC.hk
        (gradC.lo :: gradC.cuts ++ [gradC.hi]) gradC.mcaps := by
  decide +kernel

-- the stated cap's square scale at a forged cap under the top
example : ¬ gradRead gradV (BPair.ofNat 1) 1
    { gradC with mcaps := [1] } := by decide +kernel

example : ¬ ((⟨BPair.ofNat 4, 1⟩ : CPair)
    ≤ ⟨BPair.ofNat (1 * 1) * BPair.ofNat 1, 1⟩) := by decide +kernel

example : stage.unitC ≤ pieceB gradV stage.unitC ⟨BPair.ofNat 4, 1⟩
    ∧ stage.unitC < pieceL gradV (BPair.ofNat 1) 1 0 1
        stage.unitC ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 4, 1⟩ := by decide +kernel

-- the validity's load-bearing witness: at an occupied u-tail a
-- vacant stated cap withdraws the tail's price, the arms pass, and
-- the collapse sits on the lower side — the square-scale conjunct
-- is the refusal that stops the forge
private def uLbV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5]],
   [[BPair.ofNat 1, (BPair.ofNat 60).swap]])

private def uLbC : GradCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, [], [0], 0, 2⟩

example : ¬ gradRead uLbV (BPair.ofNat 1) 1 uLbC := by decide +kernel

example : ¬ ((⟨BPair.ofNat 4, 1⟩ : CPair)
    ≤ ⟨BPair.ofNat (0 * 0) * BPair.ofNat 1, 1⟩) := by decide +kernel

example : profShape uLbV uLbC.K
    ∧ poly.unitTail (profBase uLbV)
    ∧ stage.unitC ≤ pieceB uLbV stage.unitC ⟨BPair.ofNat 4, 1⟩
    ∧ stage.unitC < pieceL uLbV (BPair.ofNat 1) 1 0 0
        stage.unitC ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 4, 1⟩ := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly uLbV 1) (BPair.ofPos 1) 1 uLbC.K) := by
  decide +kernel

-- the line arm's origin-floor conjunct, load-bearing: at a u-slab
-- origin below its balance partner the arm's floor refuses while
-- every further conjunct passes, and the collapse crosses at depth
-- two — the origin floor is the refusal that stops the forge
private def bflV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5]], [[(BPair.ofNat 3).swap]])

private def bflC : GradCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, [], [2], 0, 1⟩

example : ¬ gradRead bflV (BPair.ofNat 1) 1 bflC := by decide +kernel

example : ¬ (stage.unitC
    ≤ pieceB bflV stage.unitC ⟨BPair.ofNat 4, 1⟩) := by decide +kernel

example : profShape bflV bflC.K
    ∧ poly.unitTail (profBase bflV) := by decide +kernel

example : stage.unitC < (⟨BPair.ofNat 4, 1⟩ : CPair)
    ∧ (⟨BPair.ofNat 4, 1⟩ : CPair)
      ≤ ⟨BPair.ofNat (2 * 2) * BPair.ofNat 1, 1⟩ := by decide +kernel

example : stage.unitC
    < pieceL bflV (BPair.ofNat 1) 1 0 2 stage.unitC
        ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 4, 1⟩ := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly bflV 2) (BPair.ofPos 1) 1 bflC.K) := by
  decide +kernel

-- the caps' one-per-piece shape: the withdrawn and the excess list
example : ¬ gradRead gradV (BPair.ofNat 1) 1
    { gradC with mcaps := [] } := by decide +kernel

example : ¬ gradRead gradV (BPair.ofNat 1) 1
    { gradC with mcaps := [2, 2] } := by decide +kernel

-- the chain's stalled piece inside the composite cover
example : ¬ gradRead gradV (BPair.ofNat 1) 1
    { gradC with cuts := [⟨BPair.ofNat 4, 1⟩], mcaps := [2, 2] } := by
  decide +kernel

example : ¬ pieceKeep gradV (BPair.ofNat 1) 1 ⟨BPair.ofNat 4, 1⟩ 0 2
    ⟨BPair.ofNat 4, 1⟩ ⟨BPair.ofNat 4, 1⟩ := by decide +kernel

example : pieceKeep gradV (BPair.ofNat 1) 1 ⟨BPair.ofNat 4, 1⟩ 0 2
    stage.unitC ⟨BPair.ofNat 4, 1⟩ := by decide +kernel

-- the u-slab's deep tail at the stated cap's multiple: the price
-- passes at the ceiling one quarter and refuses at the unit
-- ceiling, the ceiling's second member load-bearing
private def capUV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5]], [[BPair.ofNat 3, BPair.ofNat 9]])

example : gradRead capUV (BPair.ofNat 1) 4
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [], [2], 9, 2⟩ := by decide +kernel

example : ¬ gradRead capUV (BPair.ofNat 1) 1
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [], [1], 9, 2⟩ := by decide +kernel

example : ¬ (stage.unitC < pieceL capUV (BPair.ofNat 1) 1 9 1
    stage.unitC ⟨BPair.ofNat 1, 1⟩ ⟨BPair.ofNat 1, 1⟩) := by decide +kernel

example : profShape capUV 2
    ∧ poly.unitTail (profBase capUV)
    ∧ (⟨BPair.ofNat 1, 1⟩ : CPair)
        ≤ ⟨BPair.ofNat (1 * 1) * BPair.ofNat 1, 1⟩ := by decide +kernel

-- the ceiling's first member load-bearing at the same tail
example : ¬ gradRead capUV (BPair.ofNat 4) 4
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [], [2], 9, 2⟩ := by decide +kernel

example : ¬ (stage.unitC < pieceL capUV (BPair.ofNat 4) 4 9 2
    stage.unitC ⟨BPair.ofNat 1, 1⟩ ⟨BPair.ofNat 1, 1⟩) := by decide +kernel

-- the u⁰-slab's deep tail at the ceiling's powers
private def capBV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5, BPair.ofNat 9]], [[BPair.ofNat 3]])

example : gradRead capBV (BPair.ofNat 1) 4
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [], [2], 9, 2⟩ := by decide +kernel

example : ¬ gradRead capBV (BPair.ofNat 1) 1
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [], [1], 9, 2⟩ := by decide +kernel

example : ¬ (stage.unitC < pieceL capBV (BPair.ofNat 1) 1 9 1
    stage.unitC ⟨BPair.ofNat 1, 1⟩ ⟨BPair.ofNat 1, 1⟩) := by decide +kernel

example : profShape capBV 2
    ∧ poly.unitTail (profBase capBV) := by decide +kernel

-- the tail's handover key is load-bearing: at a sloped u-column
-- the box-top magnitude fold refuses where the piece rewrite
-- keeps, the key two admitting the cover the key nought refuses
private def hybV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 13]],
   [[BPair.ofNat 3, BPair.ofNat 8], [BPair.unit, (BPair.ofNat 8).swap]])

example : gradRead hybV (BPair.ofNat 1) 1
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [⟨BPair.ofNat 1, 2⟩],
     [1, 1], 2, 3⟩ := by decide +kernel

example : ¬ gradRead hybV (BPair.ofNat 1) 1
    ⟨stage.unitC, ⟨BPair.ofNat 1, 1⟩, [⟨BPair.ofNat 1, 2⟩],
     [1, 1], 0, 3⟩ := by decide +kernel

example : ¬ (stage.unitC < pieceL hybV (BPair.ofNat 1) 1 0 1
    stage.unitC ⟨BPair.ofNat 1, 2⟩ ⟨BPair.ofNat 1, 1⟩) := by
  decide +kernel

example : stage.unitC < pieceL hybV (BPair.ofNat 1) 1 2 1
    stage.unitC ⟨BPair.ofNat 1, 2⟩ ⟨BPair.ofNat 1, 1⟩ := by
  decide +kernel

/-! The graded theorem's binders, each at an isolating instance:
the squared comparison's own passing piece at a floored box — the
scale-key read on its lower side at every point with the squared
arm keeping the piece — beside the box floor's refusal of the
depth nought, the squared comparison's ceiling members each
load-bearing at the moved clearing, the read itself refused at
the withdrawn scale slab, and the scale bound with the box's two
membership reads at a floored box under a rational ceiling. -/

private def gvV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, (BPair.ofNat 2).swap]], [[BPair.ofNat 3]])

/-- The squared arm's certificate: the box `[1 : 4]` at one piece
and the stated cap two, the scale-key read two below the floors'
join at every point, the squared comparison's `9s` above the cap's
square four at the ceiling one. -/
private def gvC : GradCert :=
  ⟨⟨BPair.ofNat 1, 1⟩, ⟨BPair.ofNat 4, 1⟩, [], [2], 0, 1⟩

example : gradRead gvV (BPair.ofNat 1) 1 gvC := by decide +kernel

-- the line arm sits on its lower side, the squared arm the
-- piece's own read
example : ¬ (stage.unitC < pieceL gvV (BPair.ofNat 1) 1 0 2
    gvC.lo gvC.hi gvC.hi) := by decide +kernel

example : stage.unitC < pieceB gvV gvC.lo gvC.hi
    ∧ (⟨BPair.ofNat 1, 1⟩ : CPair)
        * (pieceX gvV (BPair.ofNat 1) 1 0 2 gvC.lo gvC.hi gvC.hi
          * pieceX gvV (BPair.ofNat 1) 1 0 2 gvC.lo gvC.hi gvC.hi)
      < gvC.lo * (pieceB gvV gvC.lo gvC.hi
          * pieceB gvV gvC.lo gvC.hi) := by decide +kernel

example : BPair.unit
    < poly.evalClear (depthPoly gvV 1) (BPair.ofPos 1) 1 gvC.K :=
  gradRead_pos gvV (BPair.ofNat 1) 1 gvC (by decide +kernel) 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : BPair.unit
    < poly.evalClear (depthPoly gvV 2) (BPair.ofPos 1) 1 gvC.K :=
  gradRead_pos gvV (BPair.ofNat 1) 1 gvC (by decide +kernel) 2 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : BPair.unit
    < poly.evalClear (depthPoly gvV 1) (BPair.ofPos 1) 1 gvC.K := by
  decide +kernel

-- the box's floor refuses the depth nought, its collapse on the
-- lower side
example : ¬ (gvC.lo
    ≤ (⟨BPair.ofNat (0 * 0) * BPair.ofPos 1, 1⟩ : CPair)) := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gvV 0) (BPair.ofPos 1) 1 gvC.K) := by
  decide +kernel

-- the ceiling's two members at the squared comparison's moved
-- clearing: the matched clearing passes, the moved one refuses
example : gradRead gvV (BPair.ofNat 4) 4 gvC := by decide +kernel

example : ¬ gradRead gvV (BPair.ofNat 4) 1 gvC := by decide +kernel

example : ¬ ((⟨BPair.ofNat 4, 1⟩ : CPair)
    * (pieceX gvV (BPair.ofNat 4) 1 0 2 gvC.lo gvC.hi gvC.hi
      * pieceX gvV (BPair.ofNat 4) 1 0 2 gvC.lo gvC.hi gvC.hi)
    < gvC.lo * (pieceB gvV gvC.lo gvC.hi
        * pieceB gvV gvC.lo gvC.hi)) := by decide +kernel

-- the read itself refused at the withdrawn scale slab
private def gvW : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, (BPair.ofNat 2).swap]], ([] : poly.PPoly))

example : ¬ gradRead gvW (BPair.ofNat 1) 1 gvC := by decide +kernel

example : poly.unitTail (profBaseU gvW) := by decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gvW 1) (BPair.ofPos 1) 1 gvC.K) := by
  decide +kernel

/-- The floored box under the rational ceiling: the scale-key read
on its lower side with the squared comparison's `64s` above the
cap's square twenty-five past the floor, the box `[1/2 : 1]` at
one piece and the stated cap two. -/
private def gxV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, (BPair.ofNat 5).swap]], [[BPair.ofNat 4]])

private def gxC : GradCert :=
  ⟨⟨BPair.ofNat 1, 2⟩, ⟨BPair.ofNat 1, 1⟩, [], [2], 0, 1⟩

example : gradRead gxV (BPair.ofNat 1) 4 gxC := by decide +kernel

-- the scale bound refused at the scale one half
example : ¬ (BPair.ofPos 1 * BPair.ofPos 4
    ≤ BPair.ofNat 1 * BPair.ofPos 2) := by decide +kernel

example : gxC.lo ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 2⟩ : CPair)
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 2⟩ : CPair) ≤ gxC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gxV 1) (BPair.ofPos 1) 2 gxC.K) := by
  decide +kernel

-- the box's floor refused at the scale one quarter
example : ¬ (gxC.lo
    ≤ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 4⟩ : CPair)) := by
  decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 4 ≤ BPair.ofNat 1 * BPair.ofPos 4
    ∧ (⟨BPair.ofNat (1 * 1) * BPair.ofPos 1, 4⟩ : CPair) ≤ gxC.hi := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gxV 1) (BPair.ofPos 1) 4 gxC.K) := by
  decide +kernel

/-- The box's top refused past a sloped first slab: the scale-key
read climbs across the box and falls past it, the depth three's
value on the lower side beyond the top. -/
private def gyV : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 50], [BPair.unit, (BPair.ofNat 10).swap]],
   [[BPair.ofNat 1]])

private def gyC : GradCert :=
  ⟨stage.unitC, ⟨BPair.ofNat 4, 1⟩, [], [2], 0, 2⟩

example : gradRead gyV (BPair.ofNat 1) 1 gyC := by decide +kernel

example : ¬ ((⟨BPair.ofNat (3 * 3) * BPair.ofPos 1, 1⟩ : CPair)
    ≤ gyC.hi) := by decide +kernel

example : BPair.ofPos 1 * BPair.ofPos 1 ≤ BPair.ofNat 1 * BPair.ofPos 1
    ∧ gyC.lo ≤ (⟨BPair.ofNat (3 * 3) * BPair.ofPos 1, 1⟩ : CPair) := by
  decide +kernel

example : ¬ (BPair.unit
    < poly.evalClear (depthPoly gyV 3) (BPair.ofPos 1) 1 gyC.K) := by
  decide +kernel

/-! The profile-matrix stage runs at the two-key center family
`[[1, u], [u, s]]`, the constant one and the kernel's two generators
at the corners: the collapse values at the depth three read the
scale's own powers — the u-slab's `3`, the square scale's `9`, and
the kernel's `u · u = ηs` at the square key `9` — with the constant
one's product returning the u-slab unchanged.  Each of the six
collapse bridges is decided raw at that family and beside its
theorem route, the constant family's at the stated matrix
`[[2, 1], [1, 3]]`. -/

private def blU : poly.PPoly × poly.PPoly :=
  (([] : poly.PPoly), [[BPair.ofNat 1]])
private def blOne : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 1]], ([] : poly.PPoly))
private def blS : poly.PPoly × poly.PPoly :=
  ([([] : poly.Poly), [BPair.ofNat 1]], ([] : poly.PPoly))
private def blA : List (List (poly.PPoly × poly.PPoly)) :=
  [[blOne, blU], [blU, blS]]

example : poly.oneValue (depthPoly blU 3) [BPair.unit, BPair.ofNat 3] := by
  decide +kernel

example : poly.oneValue (depthPoly blS 3) [BPair.unit, BPair.ofNat 9] := by
  decide +kernel

-- the kernel's u · u = ηs read
example : poly.oneValue (depthPoly (profMul blU blU) 3)
    [BPair.unit, BPair.unit, BPair.ofNat 9] := by decide +kernel

example : poly.oneValue
    (depthPoly (profMul ([poly.one], ([] : poly.PPoly)) blU) 3)
    (depthPoly blU 3) := by decide +kernel

example : split.pmatOneValue (pfmDepth 3 (pfmMul blA blA))
    (split.pmatMul (pfmDepth 3 blA) (pfmDepth 3 blA)) := by decide +kernel

example : split.pmatOneValue (pfmDepth 3 (pfmMul blA blA))
    (split.pmatMul (pfmDepth 3 blA) (pfmDepth 3 blA)) :=
  pfmDepth_mul blA blA 3

example : split.pmatOneValue (pfmDepth 3 (pfmAdd blA blA))
    (split.pmatAdd (pfmDepth 3 blA) (pfmDepth 3 blA)) := by decide +kernel

example : split.pmatOneValue (pfmDepth 3 (pfmAdd blA blA))
    (split.pmatAdd (pfmDepth 3 blA) (pfmDepth 3 blA)) :=
  pfmDepth_add blA blA 3

example : split.pmatOneValue (pfmDepth 3 (pfmSwap blA))
    (split.pswapM (pfmDepth 3 blA)) := by decide +kernel

example : split.pmatOneValue (pfmDepth 3 (pfmSwap blA))
    (split.pswapM (pfmDepth 3 blA)) := pfmDepth_swap blA 3

example : split.pmatOneValue (pfmDepth 3 (pfmShift blA))
    (pfmDepth (3 + 1) blA) := by decide +kernel

example : split.pmatOneValue (pfmDepth 3 (pfmShift blA))
    (pfmDepth (3 + 1) blA) := pfmDepth_shift blA 3

example : split.pmatOneValue (pfmDepth 3 (pfmTr blA))
    (elim.transposeO poly.polyOps (pfmDepth 3 blA)) := by decide +kernel

example : split.pmatOneValue (pfmDepth 3 (pfmTr blA))
    (elim.transposeO poly.polyOps (pfmDepth 3 blA)) := pfmDepth_tr blA 3

example : split.pmatOneValue
    (pfmDepth 3 (ofMatProf [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 3]]))
    (([[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 3]] :
        elim.Mat).map (fun r => r.map (fun c => ([c] : poly.Poly)))) := by
  decide +kernel

example : split.pmatOneValue
    (pfmDepth 3 (ofMatProf [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 3]]))
    (([[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 3]] :
        elim.Mat).map (fun r => r.map (fun c => ([c] : poly.Poly)))) :=
  pfmDepth_ofMat [[BPair.ofNat 2, BPair.unit],
    [BPair.unit, BPair.ofNat 3]] 3

/-! The evaluated glue runs at the ceiling `[1 : 200]`, the scale
`[1 : 200]` and the shared clearing power two.  The magnitude price
is read at three profiles at the depth three, the scale `[1 : 2]`
and the clearing two: the constant `10`, whose collapse `40` is its
own magnitude; the mixed-sign scale profile `−2 + 4η`, whose
collapse cancels at the sum's unit against the magnitude profile's
`16`; and the u-carrying profile `−2 + u`, whose collapse `−2`
prices at the magnitude profile's `14` — each decided raw beside
its theorem route.  The glue reads two sites, the diagonal `10`
against a scale-carrying and against a depth-carrying off entry.
At the off entry `−500η` the rows certify at the box
`(3, 0, 1, 0; 2)` on `[[1 : 2], [2 : 1]]` and the depth-twelve
composite point `144/200` sits inside it, the row comparison
`100000 ≤ 400000` with the evaluated form closing at the
replicate-unit slack.  At the off entry `−100u` the off-row fold
grows with the depth, the rows certify at the box on
`[[1 : 2], [5 : 4]]` with the u-slab floor eight at its squared
price — the device's second-slab arms occupied — and the box
membership is the load-bearing binder: at the depth twelve the
comparison reads `240000 ≤ 400000` and the evaluated datum is
dominant, while at the depth twenty-one the composite point
`441/200` runs past the box top, the membership read decides false
with the certificate walk standing, and the evaluated conclusion
parts, `420000` past the diagonal's `400000`. -/

private def bl2Diag : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 10]], ([] : poly.PPoly))
private def bl2Mix : poly.PPoly × poly.PPoly :=
  ([[(⟨1, 3⟩ : BPair), BPair.ofNat 4]], ([] : poly.PPoly))
private def bl2MixU : poly.PPoly × poly.PPoly :=
  ([[(⟨1, 3⟩ : BPair)]], [[BPair.ofNat 1]])

example : windowsep.mag (evalProf bl2Diag 3 1 2 2)
    ≤ evalProf (magProf bl2Diag) 3 1 2 2 := by decide +kernel

example : windowsep.mag (evalProf bl2Diag 3 1 2 2)
    ≤ evalProf (magProf bl2Diag) 3 1 2 2 :=
  evalProf_mag bl2Diag 3 1 2 2

example : windowsep.mag (evalProf bl2Mix 3 1 2 2)
    ≤ evalProf (magProf bl2Mix) 3 1 2 2 := by decide +kernel

example : windowsep.mag (evalProf bl2Mix 3 1 2 2)
    ≤ evalProf (magProf bl2Mix) 3 1 2 2 :=
  evalProf_mag bl2Mix 3 1 2 2

example : windowsep.mag (evalProf bl2MixU 3 1 2 2)
    ≤ evalProf (magProf bl2MixU) 3 1 2 2 := by decide +kernel

example : windowsep.mag (evalProf bl2MixU 3 1 2 2)
    ≤ evalProf (magProf bl2MixU) 3 1 2 2 :=
  evalProf_mag bl2MixU 3 1 2 2

-- the three collapses and their magnitude profiles' own
example : poly.oneValue (depthPoly bl2Mix 3) [(⟨1, 3⟩ : BPair), BPair.ofNat 4]
    ∧ poly.oneValue (depthPoly bl2MixU 3) [(⟨1, 3⟩ : BPair), BPair.ofNat 3] := by
  decide +kernel

private def bl2Off : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, (BPair.ofNat 500).swap]], ([] : poly.PPoly))

private def bl2Bx : BoxCert :=
  ⟨⟨BPair.ofNat 1, 2⟩, ⟨BPair.ofNat 2, 1⟩, [], [], [],
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat 3, BPair.unit, BPair.ofNat 1, BPair.unit, 2⟩

private def bl2Row : List (poly.PPoly × poly.PPoly) := [bl2Diag, bl2Off]

private def bl2Site : List (List (poly.PPoly × poly.PPoly)) :=
  [[bl2Diag, bl2Off], [bl2Off, bl2Diag]]

example : domRowRead (BPair.ofNat 1) 200 0 bl2Row bl2Bx := by decide +kernel

example : decimation.offFold 0
      (bl2Row.map (fun e => evalProf e 12 1 200 2))
    ≤ ground.getAt BPair.unit
      (bl2Row.map (fun e => evalProf e 12 1 200 2)) 0 := by decide +kernel

example : decimation.offFold 0
      (bl2Row.map (fun e => evalProf e 12 1 200 2))
    ≤ ground.getAt BPair.unit
      (bl2Row.map (fun e => evalProf e 12 1 200 2)) 0 :=
  domRow_le (BPair.ofNat 1) 200 0 12 2 1 200 bl2Row bl2Bx
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : domCertGo (BPair.ofNat 1) 200 0 bl2Site [bl2Bx, bl2Bx] := by
  decide +kernel

example : decimation.domAt (evalPfm bl2Site 12 1 200 2) := by decide +kernel

example : decimation.domAt (evalPfm bl2Site 12 1 200 2) :=
  domCert_domAt (BPair.ofNat 1) 200 12 2 1 200 bl2Site [bl2Bx, bl2Bx]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : elim.sqAt (evalPfm bl2Site 12 1 200 2) bl2Site.length := by
  decide +kernel

example : elim.matOneValue (evalPfm bl2Site 12 1 200 2)
    (elim.transposeM (evalPfm bl2Site 12 1 200 2)) := by decide +kernel

example : ∀ v : List BPair, v.length = bl2Site.length →
    BPair.unit ≤ inertia.quadForm (evalPfm bl2Site 12 1 200 2) v :=
  domCert_form (BPair.ofNat 1) 200 12 2 1 200 bl2Site [bl2Bx, bl2Bx]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

-- the depth-carrying site: the off entry `−100u`, the fold growing
-- with the depth
private def bl2OffU : poly.PPoly × poly.PPoly :=
  (([] : poly.PPoly), [[(BPair.ofNat 100).swap]])

private def bl2BxU : BoxCert :=
  ⟨⟨BPair.ofNat 1, 2⟩, ⟨BPair.ofNat 5, 4⟩, [], [], [],
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 2,
   BPair.ofNat 1, BPair.unit, BPair.ofNat 8, BPair.unit, 1⟩

private def bl2RowU : List (poly.PPoly × poly.PPoly) := [bl2Diag, bl2OffU]

private def bl2SiteU : List (List (poly.PPoly × poly.PPoly)) :=
  [[bl2Diag, bl2OffU], [bl2OffU, bl2Diag]]

example : domRowRead (BPair.ofNat 1) 200 0 bl2RowU bl2BxU := by
  decide +kernel

example : domCertGo (BPair.ofNat 1) 200 0 bl2SiteU [bl2BxU, bl2BxU] := by
  decide +kernel

example : decimation.domAt (evalPfm bl2SiteU 12 1 200 2) := by
  decide +kernel

example : decimation.domAt (evalPfm bl2SiteU 12 1 200 2) :=
  domCert_domAt (BPair.ofNat 1) 200 12 2 1 200 bl2SiteU [bl2BxU, bl2BxU]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : elim.sqAt (evalPfm bl2SiteU 12 1 200 2) bl2SiteU.length := by
  decide +kernel

example : elim.matOneValue (evalPfm bl2SiteU 12 1 200 2)
    (elim.transposeM (evalPfm bl2SiteU 12 1 200 2)) := by decide +kernel

example : ∀ v : List BPair, v.length = bl2SiteU.length →
    BPair.unit ≤ inertia.quadForm (evalPfm bl2SiteU 12 1 200 2) v :=
  domCert_form (BPair.ofNat 1) 200 12 2 1 200 bl2SiteU [bl2BxU, bl2BxU]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

-- the box membership load-bearing at the depth twenty-one: the
-- composite point past the box top, the certificate walk standing,
-- and the evaluated conclusion parted
example : ¬ (([bl2BxU, bl2BxU].all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat (21 * 21) * BPair.ofPos 1, 200⟩
        : CPair))
      && decide ((⟨BPair.ofNat (21 * 21) * BPair.ofPos 1, 200⟩
        : CPair) ≤ g.hi)
      && Nat.ble (g.K + 1) (2 + 1))) = true) := by decide +kernel

example : ¬ decimation.domAt (evalPfm bl2SiteU 21 1 200 2) := by
  decide +kernel

/-! ## The well head's reads

The well's diagonal at the residue `2`, the rate `[3 : 2]`, the
scale `[2 : 3]` and the depth `1` reads the three-term count form,
`2·(3·2·9) + 4·2·3·4 − 3·3·2·3`, decided beside the `wellDiag_read`
route and at the collected count form beside `wellDiag_count`, and
the well's entries at the order three read the chain
chart at the tower's diagonal list and the bond list through
`wellEntry`, the diagonal, bond and far cells decided beside it. -/

example : (wellDiag 2 3 2 2 3 1).oneValue
    (BPair.ofNat 2 * (BPair.ofNat ((2 + 1) * 2) * BPair.ofPos 3 * BPair.ofPos 3)
      + (BPair.ofNat (4 * 2 * (1 * 1 + 2 * 1)) * BPair.ofPos 2 * BPair.ofPos 2
        + (BPair.ofNat ((2 + 1) * 3) * BPair.ofPos 2 * BPair.ofPos 3).swap)) := by
  decide +kernel
example : (wellDiag 2 3 2 2 3 1).oneValue
    (BPair.ofNat 2 * (BPair.ofNat ((2 + 1) * 2) * BPair.ofPos 3 * BPair.ofPos 3)
      + (BPair.ofNat (4 * 2 * (1 * 1 + 2 * 1)) * BPair.ofPos 2 * BPair.ofPos 2
        + (BPair.ofNat ((2 + 1) * 3) * BPair.ofPos 2 * BPair.ofPos 3).swap)) :=
  wellDiag_read 2 3 2 1 2 3

example : (wellDiag 2 3 2 2 3 1).oneValue
    (BPair.ofNat (2 * ((2 + 1) * 2 * 3 * 3) + 4 * 2 * (1 * 1 + 2 * 1) * 2 * 2)
      + (BPair.ofNat ((2 + 1) * 3 * 2 * 3)).swap) := by decide +kernel
example : (wellDiag 2 3 2 2 3 1).oneValue
    (BPair.ofNat (2 * ((2 + 1) * 2 * 3 * 3) + 4 * 2 * (1 * 1 + 2 * 1) * 2 * 2)
      + (BPair.ofNat ((2 + 1) * 3 * 2 * 3)).swap) :=
  wellDiag_count 2 3 2 1 2 3

example : ground.getAt BPair.unit (ground.getAt [] (wellMat 2 3 2 2 3 3) 1) 1
    = greenprod.chainAt (wDiagE 2 3 2 2 3 3) (wOffE 2 2 3 3) 1 1 := by
  decide +kernel
example : ground.getAt BPair.unit (ground.getAt [] (wellMat 2 3 2 2 3 3) 1) 1
    = greenprod.chainAt (wDiagE 2 3 2 2 3 3) (wOffE 2 2 3 3) 1 1 :=
  wellEntry 2 3 2 2 3 2 1 1 (by decide +kernel) (by decide +kernel)
example : ground.getAt BPair.unit (ground.getAt [] (wellMat 2 3 2 2 3 3) 1) 2
    = greenprod.chainAt (wDiagE 2 3 2 2 3 3) (wOffE 2 2 3 3) 1 2 :=
  wellEntry 2 3 2 2 3 2 1 2 (by decide +kernel) (by decide +kernel)
example : ground.getAt BPair.unit (ground.getAt [] (wellMat 2 3 2 2 3 3) 0) 2
    = BPair.unit := by decide +kernel
example : ground.getAt BPair.unit (ground.getAt [] (wellMat 2 3 2 2 3 3) 1) 2
    = (wellBond 2 2 3).swap := by decide +kernel
