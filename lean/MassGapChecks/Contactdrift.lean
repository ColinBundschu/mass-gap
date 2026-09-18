import MassGap.Contactdrift
/-!
The check module for `lem:contactdrift`: the contact drift's fixture at
the electric form `E = diag(3, 1)`, the magnetic form `M = diag(2, 1)`
and the unit gram, the drift's two order conjuncts the statement's
frame, and the tiers below at their own fixtures.

The grade-key block reads `lem:contactdrift`'s key `G(λ) = λ(θ^∨)` at the
tables: the halved summands' join to the residue and their naming
read at the five classical and exceptional fixtures, the four
displayed closed forms decided beside their theorem routes, the
sorted words' subtracted key displays at the three series decided
beside one theorem route each with the full-length boundary words
their own anchors, the `A`-series shape key's two class moves, and
the isolating refusal of every binder — the naming read, the shape
read, the length frames, the sorted binder, `D`'s rank binder and
the two closed-form rank guards.

The move-cap block reads the two table reads at the same fixtures,
the `θ` content list at the fixture builder with its caps decided
over the whole family, the theorem routes for the positive member's
two walls, a content's cap at the list membership and the key's
move under a fused target's coroot list, and the isolating refusal
of every binder — the dominance join, the dominant reads, the norm
and the symmetry each at their own table, the naming read at a
truncated halved summand and the shape read at off-rank Cartan and
fold data, with the membership, order and tie binders beside them.

The Casimir-cap block reads the caps at the boxed words and
shapes: the three series' displayed numerators over the sorted
words of the box `[4, 4]` at rank four with the empty word beside
them, the `A` series' cleared traceless read over the shapes of
`[3, 3, 3]`, and the fundamental display over the coefficient
boxes at `G2`'s and `F4`'s adjugate Grams, whose cap reads decide
at `[12, 18]` and `[12, 42]` — each beside its theorem route, with
the sorted, clearance, rank, width, naming and entry binders
refused at their own fixtures and the two order frames read
jointly load-bearing at the committed joint witness, each side's
own truncation keeping the cap.

The per-key counts block: the key list's
identification over the box `[4,4,4]` at `B3`, its length cap, the
gap product's factors against the `θ` factor, the `θ` factor's own
read at `B3` and `C3`, the member dimension's cap over the box
`[2,2,2]` and the two strict per-key caps at `B2` — each beside
its theorem route — with the naming, length, shape,
positive-list and length-denominator binders refused at their own
tables, and the gap comparison's shape and dominance-join binders
refused at a length family past the rank, at the vacant rank, and
at a fold beyond the top.

The Rayleigh-close block reads the dimension-weighted
family: the toy head's four fold caps — the vacuum floor, the move
cap, the boundary cap and the electric cap — each routed once at
the scale triple `(1, 7, 8)` with its conclusion decided beside the
route; the trial family's three quadratic reads each routed beside
their decided anchors; and the ground read routed twice at that
head's own site datum, the whole assembly through `family_ground`
and the count's witness through `rayleigh_count` at the trial
vector's own lower-side read, the assembled level
`⟨1007574152 : 1⟩` against `⟨50421 : 1⟩` with the margin one, where
the negative-definite site's cleared upper-triangular congruence
reads three negative one-blocks and the count three.  Each cap's
binders stand refused at their own fixtures with the co-binders
decided true beside them — the move cap's raised target and broken
eigen-identity, the boundary cap's top-key count at the heavy key
and its certificate comparison at the reversed scale pair, the
electric cap's Casimir comparison and per-key counts, and the
vacuum floor's key, dimension and window reads — and the drift's
two arithmetic closes are routed at their own small instances with
the drift close's bracket and the rate close's drift and bracket
binders each refused beside the other decided true.

The rate composition is routed at the drift battery's own data with its four
binders — the margin, the bracket's two sides and the cap's atom
tie — refused at fixtures whose conclusion fails.

The join read at the count carrier closes with its own composition:
the drift's margin comparison at the levels `⟨3 : 2⟩` and `⟨5 : 1⟩`
with the counts `1 + 2`, `2`, `2 + 3` and `1` (`drift_margin`), and
the whole join at the one-place head `H = [3]` over the unit gram —
the level `⟨1 : 1⟩` vacant, the level `⟨5 : 1⟩` occupied,
`certconstruct.count_below_occupied` holding the one at or below
the other and `drift_margin` reading that order back as the margin
comparison `0 + 1 ≤ 2 + 3`.
-/

namespace contactdrift
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct contactdrift

private def u : BPair := BPair.unit

/-! The contact drift's fixture: the electric form `E = diag(3, 1)`,
the magnetic form `M = diag(2, 1)` and the unit gram over the
coordinate vector `ψ = e₁`, where the three quadratic reads are
`⟨ψ,Eψ⟩ = 3`, `⟨ψ,Mψ⟩ = 2`, `⟨ψ,Gψ⟩ = 1`.  At the cleared
representative `σ = [1 : 1]`, the level `⟨4 : 3⟩` and the top root
`⟨4 : 1⟩` the ground identity cross-adds — `1·3 + 3·1 = 4·1 + 1·2`
— and the cap's site `4G − (M + G) = diag(1, 2)` reads its diagonal
split positive semidefinite, so the drift `⟨4 + 1·4 : 3 + 1·1⟩`
prices the electric weight, `3 + 4 ≤ 8`. -/

private def dE : Mat := [[⟨4, 1⟩, u], [u, ⟨2, 1⟩]]

private def dM : Mat := [[⟨3, 1⟩, u], [u, ⟨2, 1⟩]]

private def dpsi : List BPair := [⟨2, 1⟩, u]

private theorem dLen : dpsi.length = 2 := by decide +kernel
private theorem dId : (BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos 3 * quadForm (idMat 2) dpsi).oneValue
    (BPair.ofPos 4 * quadForm (idMat 2) dpsi
      + BPair.ofPos 1 * quadForm dM dpsi) := by decide +kernel
private theorem dCapSplit : splitRead
    (siteDatum (matScale 4 (idMat 2))
      (matAdd dM (matScale 1 (idMat 2)))) (inertia.oneSplit [⟨10, 9⟩, ⟨10, 8⟩]) := by
  decide +kernel
private theorem dCapPsd : psdAt (inertia.oneSplit [⟨10, 9⟩, ⟨10, 8⟩]) := by
  decide +kernel

theorem pin1 : BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos (3 + 1 * 1) * quadForm (idMat 2) dpsi
    ≤ BPair.ofPos (4 + 1 * 4) * quadForm (idMat 2) dpsi :=
  drift_cap dE dM (idMat 2) dpsi 1 1 4 3 4 1 (inertia.oneSplit [⟨10, 9⟩, ⟨10, 8⟩])
    dLen (by decide +kernel) (by decide +kernel) dId dCapSplit dCapPsd

/-! The ground identity isolated: at the level's first member `2`
the identity's cross-add fails — `1·3 + 3·1 = 6` against
`2·1 + 1·2 = 4` — and the drift `⟨2 + 1·4 : 3 + 1·1⟩` sits under the
electric weight, `3 + 4 ≤ 6` refused. -/

theorem pin2 : ¬ (BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos 3 * quadForm (idMat 2) dpsi).oneValue
    (BPair.ofPos 2 * quadForm (idMat 2) dpsi
      + BPair.ofPos 1 * quadForm dM dpsi) := by decide +kernel
theorem pin3 : ¬ (BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos (3 + 1 * 1) * quadForm (idMat 2) dpsi
    ≤ BPair.ofPos (2 + 1 * 4) * quadForm (idMat 2) dpsi) := by
  decide +kernel

/-! The top root isolated: at the root `⟨1 : 1⟩` the magnetic form
stands above it, the cap's site `G − (M + G) = diag(-2, -1)`
reading two lower-side blocks at its diagonal split — the
positive-semidefinite read refused — and the drift `⟨4 + 1·1 :
3 + 1·1⟩` failing to price the electric weight, `3 + 4 ≤ 5`
refused. -/

theorem pin4 : splitRead
    (siteDatum (matScale 1 (idMat 2))
      (matAdd dM (matScale 1 (idMat 2)))) (inertia.oneSplit [⟨4, 6⟩, ⟨4, 5⟩]) := by
  decide +kernel
theorem pin5 : ¬ psdAt (inertia.oneSplit [⟨4, 6⟩, ⟨4, 5⟩]) := by decide +kernel
theorem pin6 : ¬ (BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos (3 + 1 * 1) * quadForm (idMat 2) dpsi
    ≤ BPair.ofPos (4 + 1 * 1) * quadForm (idMat 2) dpsi) := by
  decide +kernel

/-! The two order conjuncts are the statement's frame, the head's
own square matrices: the cap's site is the entrywise sum's own,
and the sum truncates at its two operands' shared extent, so an
operand off the stated order still assembles a site at that order
— the frame is underivable from the co-binders, the tree's stated
orders the truncation's refusal.  At the order one over `ψ = [1]`
with the gram `G = [1]` the magnetic form `M = diag(1, 1)` at the
order two assembles the site `3G − (M + G) = [1]`, every other
read of the drift standing — the ground identity
`1·1 + 2·1 = 2·1 + 1·1`, the site's split, its
positive-semidefinite read — while the magnetic form's own order
read at one is refused; exchanging the two members, `M = [1]`
against `G = diag(1, 1)`, refuses the gram's. -/

private def dpsi1 : List BPair := [⟨2, 1⟩]

private def dG1 : Mat := [[⟨2, 1⟩]]

private def dM2 : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]

theorem pin7 : dpsi1.length = 1 := by decide +kernel
theorem pin8 : (BPair.ofPos 1 * quadForm dG1 dpsi1
      + BPair.ofPos 2 * quadForm dG1 dpsi1).oneValue
    (BPair.ofPos 2 * quadForm dG1 dpsi1
      + BPair.ofPos 1 * quadForm dM2 dpsi1) := by decide +kernel
theorem pin9 : splitRead
    (siteDatum (matScale 3 dG1) (matAdd dM2 (matScale 1 dG1)))
    (inertia.oneSplit [⟨8, 7⟩]) := by decide +kernel
theorem pin10 : psdAt (inertia.oneSplit [⟨8, 7⟩]) := by decide +kernel
theorem pin11 : ¬ elim.sqAt dM2 1 := by decide +kernel

theorem pin12 : (BPair.ofPos 1 * quadForm dM2 dpsi1
      + BPair.ofPos 2 * quadForm dM2 dpsi1).oneValue
    (BPair.ofPos 2 * quadForm dM2 dpsi1
      + BPair.ofPos 1 * quadForm dG1 dpsi1) := by decide +kernel
theorem pin13 : splitRead
    (siteDatum (matScale 3 dM2) (matAdd dG1 (matScale 1 dM2)))
    (inertia.oneSplit [⟨8, 7⟩]) := by decide +kernel


/-! `lem:contactdrift`'s grade-key anchors: the halved summands join to
the residue and the naming read holds at the classical tables at
the small ranks and at the exceptional tables. -/

theorem pin14 : ground.sumNat (contactdrift.cvee (sertables.tableB 4))
    = gentable.residue (sertables.tableB 4) := by decide +kernel
theorem pin15 : ground.sumNat (contactdrift.cvee (sertables.tableC 3))
    = gentable.residue (sertables.tableC 3) := by decide +kernel
theorem pin16 : ground.sumNat (contactdrift.cvee (sertables.tableD 4))
    = gentable.residue (sertables.tableD 4) := by decide +kernel
theorem pin17 : ground.sumNat (contactdrift.cvee (gentable.tableA 3))
    = gentable.residue (gentable.tableA 3) := by decide +kernel
theorem pin18 : ground.sumNat (contactdrift.cvee sertables.tableG2)
    = gentable.residue sertables.tableG2 := by decide +kernel
theorem pin19 : ground.sumNat (contactdrift.cvee sertables.tableF4)
    = gentable.residue sertables.tableF4 := by decide +kernel

theorem pin20 : contactdrift.cveeRead (sertables.tableB 4) := by decide +kernel
theorem pin21 : contactdrift.cveeRead (sertables.tableC 3) := by decide +kernel
theorem pin22 : contactdrift.cveeRead (sertables.tableD 4) := by decide +kernel
theorem pin23 : contactdrift.cveeRead (gentable.tableA 3) := by decide +kernel
theorem pin24 : contactdrift.cveeRead sertables.tableG2 := by decide +kernel
theorem pin25 : contactdrift.cveeRead sertables.tableF4 := by decide +kernel
theorem pin26 : contactdrift.cveeRead sertables.tableE6 := by decide +kernel
theorem pin27 : contactdrift.cveeRead sertables.tableE7 := by decide +kernel
theorem pin28 : contactdrift.cveeRead sertables.tableE8 := by decide +kernel

/-! The displayed closed forms, each decided at its rank and taken
again through its theorem: one at the first and last keys and two
between at `B`, one at every key at `C` and at `A`, one at the
first and last two keys and two between at `D`. -/

theorem pin29 : contactdrift.cvee (sertables.tableB 4)
    = (List.range 4).map (fun i =>
        if i == 0 then 1 else if i + 1 == 4 then 1 else 2) := by
  decide +kernel
theorem pin30 : contactdrift.cvee (sertables.tableB 4)
    = (List.range 4).map (fun i =>
        if i == 0 then 1 else if i + 1 == 4 then 1 else 2) :=
  contactdrift.cvee_B 4 (by decide +kernel)

theorem pin31 : contactdrift.cvee (sertables.tableC 4) = List.replicate 4 1 := by
  decide +kernel
theorem pin32 : contactdrift.cvee (sertables.tableC 4) = List.replicate 4 1 :=
  contactdrift.cvee_C 4

theorem pin33 : contactdrift.cvee (sertables.tableD 5)
    = (List.range 5).map (fun i =>
        if i == 0 then 1 else if 5 ≤ i + 2 then 1 else 2) := by
  decide +kernel
theorem pin34 : contactdrift.cvee (sertables.tableD 5)
    = (List.range 5).map (fun i =>
        if i == 0 then 1 else if 5 ≤ i + 2 then 1 else 2) :=
  contactdrift.cvee_D 5 (by decide +kernel)

theorem pin35 : contactdrift.cvee (gentable.tableA 3) = List.replicate 3 1 := by
  decide +kernel
theorem pin36 : contactdrift.cvee (gentable.tableA 3) = List.replicate 3 1 :=
  contactdrift.cvee_A 3

/-! The sorted words' key reads: the decided value at each of the
six word-and-rank pairs, and one theorem route per series at the
sorted binder and the length frame. -/

theorem pin37 : contactdrift.grade (sertables.tableB 4) (serstable.member [3, 1, 1] 4)
    = 3 + 1 := by decide +kernel
theorem pin38 : contactdrift.grade (sertables.tableB 3) (serstable.member [2, 2] 3)
    = 2 + 2 := by decide +kernel
theorem pin39 : contactdrift.grade (sertables.tableC 3) (serstable.member [2, 1, 1] 3)
    = 2 := by decide +kernel
theorem pin40 : contactdrift.grade (sertables.tableC 4) (serstable.member [3, 1] 4)
    = 3 := by decide +kernel
theorem pin41 : contactdrift.grade (sertables.tableD 5) (serstable.member [2, 2, 1] 5)
    = 2 + 2 := by decide +kernel
theorem pin42 : contactdrift.grade (sertables.tableD 4) (serstable.member [3, 1] 4)
    = 3 + 1 := by decide +kernel

theorem pin43 : contactdrift.grade (sertables.tableB 4) (serstable.member [3, 1, 1] 4)
    = ground.getAt 0 [3, 1, 1] 0 + ground.getAt 0 [3, 1, 1] 1
      - ground.getAt 0 [3, 1, 1] (4 - 1) :=
  contactdrift.grade_member_B [3, 1, 1] 4 (by decide +kernel)
    (by decide +kernel)
theorem pin44 : contactdrift.grade (sertables.tableC 3) (serstable.member [2, 1, 1] 3)
    = ground.getAt 0 [2, 1, 1] 0 :=
  contactdrift.grade_member_C [2, 1, 1] 3 (by decide +kernel)
    (by decide +kernel)
theorem pin45 : contactdrift.grade (sertables.tableD 5) (serstable.member [2, 2, 1] 5)
    = ground.getAt 0 [2, 2, 1] 0 + ground.getAt 0 [2, 2, 1] 1
      - ground.getAt 0 [2, 2, 1] (5 - 2) :=
  contactdrift.grade_member_D [2, 2, 1] 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The `A`-series shape key: the full columns and the reduction
both move off the read, the key the top row's total. -/

theorem pin46 : contactdrift.gradeA (labels.addFulls 2 [2, 1, 0, 1])
    = contactdrift.gradeA [2, 1, 0, 1] := by decide +kernel
theorem pin47 : contactdrift.gradeA (labels.reduce [2, 1, 0, 1])
    = contactdrift.gradeA [2, 1, 0, 1] := by decide +kernel
theorem pin48 : contactdrift.gradeA [2, 1, 0, 1] = 3 := by decide +kernel

/-! The isolating refusals, one per binder of the general
theorems. -/

/-- `cveeRead`'s refusal at `cvee_sum`: the odd-entry table —
shaped at every field, residue two, its first halved summand
truncated by the division, so the summands' total loses the
join. -/
private def tKodd : gentable.Table :=
  ⟨2, [1, 1], 1,
   [[ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap],
    [(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 2]],
   [[1, 0], [0, 1], [1, 3]], [1, 3]⟩
theorem pin49 : gentable.shapeRead tKodd := by decide +kernel
theorem pin50 : ¬ contactdrift.cveeRead tKodd := by decide +kernel
theorem pin51 : ¬ (ground.sumNat (contactdrift.cvee tKodd)
    = gentable.residue tKodd) := by decide +kernel

/-- `shapeRead`'s refusal at `cvee_sum`: off-rank tail data — the
naming read holds at the key range while the residue fold reads the
length list and the highest root's fold past it, so the two sides
part. -/
private def tKtail : gentable.Table :=
  ⟨1, [2, 2], 1, [[ground.BPair.ofNat 2]], [[1]], [1, 8]⟩
theorem pin52 : ¬ gentable.shapeRead tKtail := by decide +kernel
theorem pin53 : contactdrift.cveeRead tKtail := by decide +kernel
theorem pin54 : ¬ (ground.sumNat (contactdrift.cvee tKtail)
    = gentable.residue tKtail) := by decide +kernel

/-- `cveeRead`'s refusal at `coeffSum_le`: a vacant halved summand,
the coefficient's weight withdrawn from the key. -/
private def tKzero : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [[1]], [1]⟩
theorem pin55 : ¬ contactdrift.cveeRead tKzero := by decide +kernel
theorem pin56 : ¬ (ground.sumNat [5] ≤ contactdrift.grade tKzero [5]) := by
  decide +kernel

/-! `coeffSum_le`'s length frame: a coefficient list past the key
count pairs off truncated, the tail entry dropped from the key
while the coefficient total keeps it. -/

theorem pin57 : ¬ (ground.sumNat [0, 5]
    ≤ contactdrift.grade (gentable.tableA 1) [0, 5]) := by decide +kernel

/-! The word reads' sorted binder: an unsorted word's consecutive
gaps truncate at the reversed step, and the collected reads
overshoot the withdrawn top pair's sum. -/

theorem pin58 : ¬ (contactdrift.grade (sertables.tableB 3)
      (serstable.member [0, 5] 3)
    = ground.getAt 0 [0, 5] 0 + ground.getAt 0 [0, 5] 1
      - ground.getAt 0 [0, 5] (3 - 1)) := by
  decide +kernel

/-! The withdrawal at full-length words: the boundary coordinate
enters the subtracted display, decided at each series' least
covered rank. -/

theorem pin59 : contactdrift.grade (sertables.tableB 2)
    (serstable.member [2, 1] 2) = 2 + 1 - 1 := by decide +kernel
theorem pin60 : contactdrift.grade (sertables.tableC 3)
    (serstable.member [3, 2, 1] 3) = 3 := by decide +kernel
theorem pin61 : contactdrift.grade (sertables.tableD 3)
    (serstable.member [2, 1] 3) = 2 + 1 - 1 := by decide +kernel

/-! The length frames, one per series: a word past the rank feeds
the last gap an occupied entry off the member's keys, and the
subtracted display parts from the fold. -/

theorem pin62 : ¬ (contactdrift.grade (sertables.tableB 3)
      (serstable.member [3, 2, 1, 1] 3)
    = ground.getAt 0 [3, 2, 1, 1] 0 + ground.getAt 0 [3, 2, 1, 1] 1
      - ground.getAt 0 [3, 2, 1, 1] (3 - 1)) := by decide +kernel
theorem pin63 : ¬ (contactdrift.grade (sertables.tableC 1)
      (serstable.member [2, 1] 1)
    = ground.getAt 0 [2, 1] 0) := by decide +kernel
theorem pin64 : ¬ (contactdrift.grade (sertables.tableD 3)
      (serstable.member [3, 2, 1, 1] 3)
    = ground.getAt 0 [3, 2, 1, 1] 0 + ground.getAt 0 [3, 2, 1, 1] 1
      - ground.getAt 0 [3, 2, 1, 1] (3 - 2)) := by decide +kernel

/-! `grade_member_D`'s rank binder: at rank one the fold shape
holds one doubled key, and the key reads past the vacant
subtracted display. -/

theorem pin65 : ¬ (contactdrift.grade (sertables.tableD 1)
      (serstable.member [5] 1)
    = ground.getAt 0 [5] 0 + ground.getAt 0 [5] 1
      - ground.getAt 0 [5] (1 - 2)) := by decide +kernel

/-! The closed forms' rank guards: below the stated rank the
highest root's fold collapses onto the short keys and the halved
summand vanishes there, so the displayed form is refused. -/

theorem pin66 : ¬ (contactdrift.cvee (sertables.tableB 1)
    = (List.range 1).map (fun i =>
        if i == 0 then 1 else if i + 1 == 1 then 1 else 2)) := by
  decide +kernel
theorem pin67 : ¬ (contactdrift.cvee (sertables.tableD 2)
    = (List.range 2).map (fun i =>
        if i == 0 then 1 else if 2 ≤ i + 2 then 1 else 2)) := by
  decide +kernel


/-! `lem:contactdrift`'s move-cap anchors: the highest root's dominant
reads and the dominance join at the top, decided at the classical
tables at the small ranks and at the exceptional tables. -/

theorem pin68 : contactdrift.thetaDomRead (sertables.tableB 4) := by decide +kernel
theorem pin69 : contactdrift.thetaDomRead (sertables.tableC 3) := by decide +kernel
theorem pin70 : contactdrift.thetaDomRead (sertables.tableD 4) := by decide +kernel
theorem pin71 : contactdrift.thetaDomRead (gentable.tableA 3) := by decide +kernel
theorem pin72 : contactdrift.thetaDomRead sertables.tableG2 := by decide +kernel
theorem pin73 : contactdrift.thetaDomRead sertables.tableF4 := by decide +kernel
theorem pin74 : contactdrift.thetaDomRead sertables.tableE6 := by decide +kernel
theorem pin75 : contactdrift.thetaDomRead sertables.tableE7 := by decide +kernel
theorem pin76 : contactdrift.thetaDomRead sertables.tableE8 := by decide +kernel

theorem pin77 : contactdrift.thetaTopRead (sertables.tableB 4) := by decide +kernel
theorem pin78 : contactdrift.thetaTopRead (sertables.tableC 3) := by decide +kernel
theorem pin79 : contactdrift.thetaTopRead (sertables.tableD 4) := by decide +kernel
theorem pin80 : contactdrift.thetaTopRead (gentable.tableA 3) := by decide +kernel
theorem pin81 : contactdrift.thetaTopRead sertables.tableG2 := by decide +kernel
theorem pin82 : contactdrift.thetaTopRead sertables.tableF4 := by decide +kernel
theorem pin83 : contactdrift.thetaTopRead sertables.tableE6 := by decide +kernel
theorem pin84 : contactdrift.thetaTopRead sertables.tableE7 := by decide +kernel
theorem pin85 : contactdrift.thetaTopRead sertables.tableE8 := by decide +kernel

/-- The `θ` content list at a table: the unit content at the
coordinate count, then each positive member's coroot vector with
its balance partner (`prop:row`'s member list). -/
private def thetaL (t : gentable.Table) : List (List ground.BPair) :=
  List.replicate t.rank (List.replicate t.rank ground.BPair.unit)
    ++ (List.range t.posFolds.length).flatMap (fun j =>
        [poly.pnorm (sertables.posCorootV t j),
         poly.pnorm (poly.neg (sertables.posCorootV t j))])

/-! The content list reads at the fixtures, and the cap decided
over the whole list: every content's key read and its balance
partner's at or below two. -/

theorem pin86 : row.thetaFamRead (sertables.tableB 2)
    (thetaL (sertables.tableB 2)) := by decide +kernel
theorem pin87 : row.thetaFamRead (sertables.tableC 3)
    (thetaL (sertables.tableC 3)) := by decide +kernel
theorem pin88 : row.thetaFamRead sertables.tableG2
    (thetaL sertables.tableG2) := by decide +kernel

theorem pin89 : ((thetaL (sertables.tableB 3)).all (fun nu =>
    (contactdrift.gradeV (sertables.tableB 3) nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((contactdrift.gradeV (sertables.tableB 3) nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel
theorem pin90 : ((thetaL (sertables.tableC 3)).all (fun nu =>
    (contactdrift.gradeV (sertables.tableC 3) nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((contactdrift.gradeV (sertables.tableC 3) nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel
theorem pin91 : ((thetaL (sertables.tableD 4)).all (fun nu =>
    (contactdrift.gradeV (sertables.tableD 4) nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((contactdrift.gradeV (sertables.tableD 4) nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel
theorem pin92 : ((thetaL sertables.tableG2).all (fun nu =>
    (contactdrift.gradeV sertables.tableG2 nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((contactdrift.gradeV sertables.tableG2 nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel

/-! The theorem routes beside the decided caps: the positive
member's two walls, a content's cap at the list membership, and the
key's move under a fused target's coroot list. -/

theorem pin93 : ground.BPair.unit ≤ contactdrift.gradeV (sertables.tableB 2)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    ∧ contactdrift.gradeV (sertables.tableB 2)
        (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
      ≤ ground.BPair.ofNat 2 :=
  contactdrift.posGrade_cap (sertables.tableB 2) 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin94 : contactdrift.gradeV (sertables.tableB 2)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    ≤ ground.BPair.ofNat 2
    ∧ (contactdrift.gradeV (sertables.tableB 2)
        (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))).swap
      ≤ ground.BPair.ofNat 2 :=
  contactdrift.content_cap (sertables.tableB 2) (thetaL (sertables.tableB 2))
    (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (ground.mem_of_countOf_pos _ (thetaL (sertables.tableB 2))
      (by decide +kernel))

theorem pin95 : contactdrift.grade (sertables.tableB 2) [1, 3]
      ≤ contactdrift.grade (sertables.tableB 2) [1, 1] + 2
    ∧ contactdrift.grade (sertables.tableB 2) [1, 1]
      ≤ contactdrift.grade (sertables.tableB 2) [1, 3] + 2 :=
  contactdrift.grade_move (sertables.tableB 2) (thetaL (sertables.tableB 2))
    [1, 1] [1, 3]
    (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (ground.mem_of_countOf_pos _ (thetaL (sertables.tableB 2))
      (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The move cap's isolating refusals, one table per binder: each
carries the other five reads and breaks a wall at a positive
member's key read. -/

/-- `thetaTopRead`'s refusal: a fold beyond the top — the join
`ν + Σ d_i α_i = θ` has no natural witness there, and the key read
at that member overshoots the norm's wall. -/
private def tMtop : gentable.Table :=
  ⟨1, [2], 1, [[ground.BPair.ofNat 2]], [[1], [3]], [1]⟩
theorem pin96 : ¬ contactdrift.thetaTopRead tMtop := by decide +kernel
theorem pin97 : gentable.shapeRead tMtop := by decide +kernel
theorem pin98 : gentable.symRead tMtop := by decide +kernel
theorem pin99 : contactdrift.cveeRead tMtop := by decide +kernel
theorem pin100 : gentable.thetaNormRead tMtop := by decide +kernel
theorem pin101 : contactdrift.thetaDomRead tMtop := by decide +kernel
theorem pin102 : ¬ (contactdrift.gradeV tMtop
    (poly.pnorm (sertables.posCorootV tMtop 1))
      ≤ ground.BPair.ofNat 2) := by decide +kernel

/-- `thetaDomRead`'s refusal: the `G2` geometry at the fold `[3,1]`
— the norm holds while the second simple's coroot pair reads the
lower side, and that member's key read falls under the sum's
unit. -/
private def tMdom : gentable.Table :=
  ⟨2, [2, 6], 3,
   [[ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap],
    [(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2]],
   [[1, 0], [0, 1], [1, 1], [2, 1], [3, 1]], [3, 1]⟩
theorem pin103 : ¬ contactdrift.thetaDomRead tMdom := by decide +kernel
theorem pin104 : gentable.shapeRead tMdom := by decide +kernel
theorem pin105 : gentable.symRead tMdom := by decide +kernel
theorem pin106 : gentable.thetaNormRead tMdom := by decide +kernel
theorem pin107 : contactdrift.cveeRead tMdom := by decide +kernel
theorem pin108 : contactdrift.thetaTopRead tMdom := by decide +kernel
theorem pin109 : ¬ (ground.BPair.unit ≤ contactdrift.gradeV tMdom
    (poly.pnorm (sertables.posCorootV tMdom 1))) := by decide +kernel

/-- `thetaNormRead`'s refusal: the doubled top — its form fold
reads sixteen against the cleared four, and the simple member's key
read stands at four, off the wall the norm sets. -/
private def tMnorm : gentable.Table :=
  ⟨1, [2], 1, [[ground.BPair.ofNat 2]], [[1], [2]], [2]⟩
theorem pin110 : ¬ gentable.thetaNormRead tMnorm := by decide +kernel
theorem pin111 : gentable.shapeRead tMnorm := by decide +kernel
theorem pin112 : gentable.symRead tMnorm := by decide +kernel
theorem pin113 : contactdrift.cveeRead tMnorm := by decide +kernel
theorem pin114 : contactdrift.thetaDomRead tMnorm := by decide +kernel
theorem pin115 : contactdrift.thetaTopRead tMnorm := by decide +kernel
theorem pin116 : ¬ (contactdrift.gradeV tMnorm
    (poly.pnorm (sertables.posCorootV tMnorm 0))
      ≤ ground.BPair.ofNat 2) := by decide +kernel

/-- `symRead`'s refusal: the asymmetric edge at matched lengths —
the halved products' exchange breaks, so the row keys part from
the top's coroot pairs and a key read falls under the sum's unit. -/
private def tMsym : gentable.Table :=
  ⟨2, [2, 4], 1,
   [[ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap],
    [(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2]],
   [[1, 0], [0, 1], [1, 1], [2, 1]], [2, 1]⟩
theorem pin117 : ¬ gentable.symRead tMsym := by decide +kernel
theorem pin118 : gentable.shapeRead tMsym := by decide +kernel
theorem pin119 : gentable.thetaNormRead tMsym := by decide +kernel
theorem pin120 : contactdrift.cveeRead tMsym := by decide +kernel
theorem pin121 : contactdrift.thetaDomRead tMsym := by decide +kernel
theorem pin122 : contactdrift.thetaTopRead tMsym := by decide +kernel
theorem pin123 : ¬ (ground.BPair.unit ≤ contactdrift.gradeV tMsym
    (poly.pnorm (sertables.posCorootV tMsym 1))) := by decide +kernel

/-- `cveeRead`'s refusal: the second key's halved summand truncated
by the division and left vacant — the naming read fails there while
the other five stand, and the key reads collapse onto the first
summand alone, breaking both walls: the fold `[2,0]` overshoots at
four and the fold `[0,1]` falls under the sum's unit. -/
private def tMcvee : gentable.Table :=
  ⟨2, [2, 1], 2,
   [[ground.BPair.ofNat 2, (ground.BPair.ofNat 2).swap],
    [(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 2]],
   [[2, 0], [0, 1]], [2, 2]⟩
theorem pin124 : ¬ contactdrift.cveeRead tMcvee := by decide +kernel
theorem pin125 : gentable.shapeRead tMcvee := by decide +kernel
theorem pin126 : gentable.symRead tMcvee := by decide +kernel
theorem pin127 : gentable.thetaNormRead tMcvee := by decide +kernel
theorem pin128 : contactdrift.thetaDomRead tMcvee := by decide +kernel
theorem pin129 : contactdrift.thetaTopRead tMcvee := by decide +kernel
theorem pin130 : contactdrift.cvee tMcvee = [1, 0] := by decide +kernel
theorem pin131 : ¬ (contactdrift.gradeV tMcvee
    (poly.pnorm (sertables.posCorootV tMcvee 0))
      ≤ ground.BPair.ofNat 2) := by decide +kernel
theorem pin132 : ¬ (ground.BPair.unit ≤ contactdrift.gradeV tMcvee
    (poly.pnorm (sertables.posCorootV tMcvee 1))) := by decide +kernel

/-- `shapeRead`'s refusal: off-rank Cartan and fold data — the
coroot read zips the fold against every stored row while the form
fold, the halved summands and the key reads stop at the key range,
so the member's coroot vector carries a row the walls never price
and its key read falls under the sum's unit. -/
private def tMshape : gentable.Table :=
  ⟨1, [2], 1,
   [[ground.BPair.ofNat 2], [(ground.BPair.ofNat 1).swap]],
   [[1, 3]], [1, 0]⟩
theorem pin133 : ¬ gentable.shapeRead tMshape := by decide +kernel
theorem pin134 : gentable.symRead tMshape := by decide +kernel
theorem pin135 : gentable.thetaNormRead tMshape := by decide +kernel
theorem pin136 : contactdrift.cveeRead tMshape := by decide +kernel
theorem pin137 : contactdrift.thetaDomRead tMshape := by decide +kernel
theorem pin138 : contactdrift.thetaTopRead tMshape := by decide +kernel
theorem pin139 : ¬ (ground.BPair.unit ≤ contactdrift.gradeV tMshape
    (poly.pnorm (sertables.posCorootV tMshape 0))) := by decide +kernel

/-! `content_cap`'s membership binder: a vector off the content
list breaks the cap — at `B2` the coroot list `⟨3 : 0⟩` reads its
key at three, and its count in the content list is vacant. -/

theorem pin140 : ¬ (contactdrift.gradeV (sertables.tableB 2)
    [ground.BPair.ofNat 3, ground.BPair.unit]
      ≤ ground.BPair.ofNat 2) := by decide +kernel
theorem pin141 : ground.countOf [ground.BPair.ofNat 3, ground.BPair.unit]
    (thetaL (sertables.tableB 2)) = 0 := by decide +kernel

/-! `gradeV_add`'s order binder: at unmatched orders the join
truncates at the shorter content, so the joined key read parts from
the summands' — at `A2` the truncated join reads two against the
summands' seven. -/

theorem pin142 : ¬ ((contactdrift.gradeV (gentable.tableA 2)
      (poly.pnorm (elim.vecAdd
        [ground.BPair.ofNat 1, ground.BPair.ofNat 5]
        [ground.BPair.ofNat 1]))).oneValue
    (contactdrift.gradeV (gentable.tableA 2)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 5]
      + contactdrift.gradeV (gentable.tableA 2)
        [ground.BPair.ofNat 1])) := by decide +kernel

/-! `grade_move`'s tie binder: a coroot list off the moved content
loses the cap — at `B2` the list `[4, 4]` reads its key at eight
against the source's one. -/

theorem pin143 : ¬ (contactdrift.grade (sertables.tableB 2) [4, 4]
    ≤ contactdrift.grade (sertables.tableB 2) [1, 0] + 2) := by decide +kernel

/-! `lem:contactdrift`'s Casimir caps: the three series' coordinate
routes at the boxed sorted words, the `A`-series' cleared traceless
read at the reduced representative, and the fundamental display's
cap at the two exceptional Grams — each beside its theorem route
and its isolating refusals. -/

/-! The series' displayed numerators against the key's square, the
sorted words of the box `[4, 4]` at rank four: the `B` and `D` keys
the top pair's sum, the `C` key the top coordinate. -/

theorem pin144 : ((ground.boxAll [4, 4]).all (fun w =>
    let W := if ground.getAt 0 w 1 ≤ ground.getAt 0 w 0 then w
             else [ground.getAt 0 w 1, ground.getAt 0 w 0]
    let K := ground.getAt 0 W 0 + ground.getAt 0 W 1
    serstable.casNumB W 4 < (4 * 4 + 4) * (K * K + 1))) = true := by
  decide +kernel

theorem pin145 : ((ground.boxAll [4, 4]).all (fun w =>
    let W := if ground.getAt 0 w 1 ≤ ground.getAt 0 w 0 then w
             else [ground.getAt 0 w 1, ground.getAt 0 w 0]
    let K := ground.getAt 0 W 0
    serstable.casNumC W 4 < (4 * 4 + 4) * (K * K + 1))) = true := by
  decide +kernel

theorem pin146 : ((ground.boxAll [4, 4]).all (fun w =>
    let W := if ground.getAt 0 w 1 ≤ ground.getAt 0 w 0 then w
             else [ground.getAt 0 w 1, ground.getAt 0 w 0]
    let K := ground.getAt 0 W 0 + ground.getAt 0 W 1
    serstable.casNumD W 4 < (4 * 4 + 4) * (K * K + 1))) = true := by
  decide +kernel

theorem pin147 : serstable.casNumB [] 1 < (1 * 1 + 1) * (0 * 0 + 1) := by
  decide +kernel

/-! The `A`-series' cleared traceless read at the reduced
representative, the shapes of the box `[3, 3, 3]` against
`d²(d+1)(K² + 1)`. -/

theorem pin148 : ((ground.boxAll [3, 3, 3]).all (fun s =>
    c2hat.dfQ (labels.reduce s)
      < s.length * s.length * (s.length + 1)
        * (contactdrift.gradeA s * contactdrift.gradeA s + 1))) = true := by
  decide +kernel

/-! The fundamental display's cap at the two exceptional tables:
the displayed adjugate rows' Gram reads its walls at `[12, 18]`
(`G2`) and `[12, 42]` (`F4`), and every coefficient list of the
box sits below `(FN + RN)(G² + 1)`. -/

theorem pin149 : contactdrift.gramCapRead sertables.tableG2
    (sertables.gramRows sertables.tableG2 sertables.adjG2) 12 18 := by
  decide +kernel

theorem pin150 : ((ground.boxAll [3, 3]).all (fun m =>
    memberdata.c2M sertables.tableG2
      (sertables.gramRows sertables.tableG2 sertables.adjG2) m
    < (12 + 18) * (contactdrift.grade sertables.tableG2 m
        * contactdrift.grade sertables.tableG2 m + 1))) = true := by
  decide +kernel

theorem pin151 : contactdrift.gramCapRead sertables.tableF4
    (sertables.gramRows sertables.tableF4 sertables.adjF4) 12 42 := by
  decide +kernel

theorem pin152 : ((ground.boxAll [2, 2, 2, 2]).all (fun m =>
    memberdata.c2M sertables.tableF4
      (sertables.gramRows sertables.tableF4 sertables.adjF4) m
    < (12 + 42) * (contactdrift.grade sertables.tableF4 m
        * contactdrift.grade sertables.tableF4 m + 1))) = true := by
  decide +kernel

/-! The theorem routes at the decided anchors: the fundamental
display at `G2`'s Gram, the three series at the sorted word
`[3, 1]` at rank four, and the `A` series at the shape
`[2, 1, 0, 1]`. -/

theorem pin153 : memberdata.c2M sertables.tableG2
    (sertables.gramRows sertables.tableG2 sertables.adjG2) [2, 1]
    < (12 + 18) * (contactdrift.grade sertables.tableG2 [2, 1]
        * contactdrift.grade sertables.tableG2 [2, 1] + 1) :=
  contactdrift.c2M_cap sertables.tableG2
    (sertables.gramRows sertables.tableG2 sertables.adjG2) 12 18 [2, 1]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pin154 : serstable.casNumB [3, 1] 4 < (4 * 4 + 4)
    * ((ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1)
        * (ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1) + 1) :=
  contactdrift.casCap_B [3, 1] 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pin155 : serstable.casNumC [3, 1] 4 < (4 * 4 + 4)
    * (ground.getAt 0 [3, 1] 0 * ground.getAt 0 [3, 1] 0 + 1) :=
  contactdrift.casCap_C [3, 1] 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pin156 : serstable.casNumD [3, 1] 4 < (4 * 4 + 4)
    * ((ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1)
        * (ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1) + 1) :=
  contactdrift.casCap_D [3, 1] 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pin157 : c2hat.dfQ (labels.reduce [2, 1, 0, 1])
    < [2, 1, 0, 1].length * [2, 1, 0, 1].length
      * ([2, 1, 0, 1].length + 1)
      * (contactdrift.gradeA [2, 1, 0, 1] * contactdrift.gradeA [2, 1, 0, 1] + 1) :=
  contactdrift.dfQ_cap [2, 1, 0, 1] (by decide +kernel)

/-! `casCap_X`'s sorted binder: an unsorted word carries its
occupancy off the head pair, so the key `W₀ + W₁` reads vacant
while the square fold is occupied. -/

theorem pin158 : ¬ (serstable.casNumB [0, 0, 9] 3
    < (3 * 3 + 3) * ((0 + 0) * (0 + 0) + 1)) := by decide +kernel

/-! `casCap_X`'s clearance binder: a word past the rank collects
entries the rank's own scale never prices — twenty unit entries at
rank one read the numerator forty against the cap's ten. -/

theorem pin159 : ¬ (serstable.casNumB (List.replicate 20 1) 1
    < (1 * 1 + 1) * ((1 + 1) * (1 + 1) + 1)) := by decide +kernel

/-! `casCap_X`'s rank binder: at the vacant rank the cleared
factor `l(l+1)` is itself vacant, so no numerator sits below it. -/

theorem pin160 : ¬ (serstable.casNumB [] 0
    < (0 * 0 + 0) * ((0 + 0) * (0 + 0) + 1)) := by decide +kernel

/-! `dfQ_cap`'s width binder: at the vacant width the cleared
factor `d²(d+1)` is vacant, so the traceless read never sits below
it. -/

theorem pin161 : ¬ (c2hat.dfQ (labels.reduce [])
    < 0 * 0 * (0 + 1)
      * (contactdrift.gradeA [] * contactdrift.gradeA [] + 1)) := by decide +kernel

/-- `c2M_cap`'s naming binder: the odd-summand table — the halved
summand truncates to the count's unit, so the key reads vacant at
an occupied coefficient list while the Gram's walls hold. -/
private def tCzero : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [[1]], [1]⟩

theorem pin162 : contactdrift.gramCapRead tCzero [[ground.BPair.ofNat 1]] 1 1 := by
  decide +kernel
theorem pin163 : ¬ contactdrift.cveeRead tCzero := by decide +kernel
theorem pin164 : ¬ (memberdata.c2M tCzero [[ground.BPair.ofNat 1]] [5]
    < (1 + 1) * (contactdrift.grade tCzero [5]
        * contactdrift.grade tCzero [5] + 1)) := by decide +kernel

/-! `gramCapRead`'s refusal at understated walls: `G2`'s displayed
Gram carries an entry past twelve's understatement and a `ρ`-dot
past ten's. -/

theorem pin165 : ¬ contactdrift.gramCapRead sertables.tableG2
    (sertables.gramRows sertables.tableG2 sertables.adjG2) 6 10 := by
  decide +kernel

/-- `c2M_cap`'s entry binder: the naming read holds and the
`ρ`-dot wall holds at nine, while one Gram entry stands past the
base's own — and there the display sits at twenty-seven against
the cap's twenty. -/
private def tCentry : gentable.Table :=
  ⟨1, [2], 1, [[ground.BPair.ofNat 2]], [[1]], [1]⟩

theorem pin166 : contactdrift.cveeRead tCentry := by decide +kernel
theorem pin167 : elim.dotP (ground.getAt [] [[ground.BPair.ofNat 9]] 0)
    (sertables.rhoV tCentry) ≤ ground.BPair.ofNat 9 := by decide +kernel
theorem pin168 : ¬ contactdrift.gramCapRead tCentry [[ground.BPair.ofNat 9]] 1 9 := by
  decide +kernel
theorem pin169 : ¬ (memberdata.c2M tCentry [[ground.BPair.ofNat 9]] [1]
    < (1 + 9) * (contactdrift.grade tCentry [1]
        * contactdrift.grade tCentry [1] + 1)) := by decide +kernel

/-! `c2M_cap`'s two order frames are jointly load-bearing: the
pairing truncates at the shorter of the coefficient list and the
Gram, so EITHER side off the rank alone drops exactly the summands
the key drops — the four one-sided reads below hold the cap at a
coefficient list past the rank, short of it, a Gram row past the
rank and a Gram short of it — while BOTH sides past the rank keep
summands the key never reads, and the cap refuses at the committed
joint witness beneath them. -/

theorem pin170 : memberdata.c2M tCentry [[ground.BPair.ofNat 1]] [5, 99]
    < (1 + 1) * (contactdrift.grade tCentry [5, 99]
        * contactdrift.grade tCentry [5, 99] + 1) := by decide +kernel

theorem pin171 : ((ground.boxAll [3, 3]).all (fun m =>
    memberdata.c2M sertables.tableG2
      (sertables.gramRows sertables.tableG2 sertables.adjG2
        ++ [[ground.BPair.ofNat 99, ground.BPair.ofNat 99]]) m
    < (12 + 18) * (contactdrift.grade sertables.tableG2 m
        * contactdrift.grade sertables.tableG2 m + 1))) = true := by
  decide +kernel

theorem pin172 : memberdata.c2M (gentable.tableA 2)
    [[ground.BPair.ofNat 1, ground.BPair.unit],
     [ground.BPair.unit, ground.BPair.ofNat 1]] [40]
    < (1 + 1) * (contactdrift.grade (gentable.tableA 2) [40]
        * contactdrift.grade (gentable.tableA 2) [40] + 1) := by decide +kernel

theorem pin173 : memberdata.c2M (gentable.tableA 2)
    [[ground.BPair.ofNat 1, ground.BPair.unit]] [5, 5]
    < (1 + 1) * (contactdrift.grade (gentable.tableA 2) [5, 5]
        * contactdrift.grade (gentable.tableA 2) [5, 5] + 1) := by decide +kernel

/-- The joint refusal: the coefficient list and the Gram both past
the rank — the pairing pairs the off-rank coefficient against the
off-rank row, a summand the key never reads, and the cap
refuses. -/
private def gJoint : elim.Mat :=
  [[ground.BPair.ofNat 1], [ground.BPair.ofNat 99]]

theorem pin174 : contactdrift.gramCapRead tCentry gJoint 1 1 := by decide +kernel
theorem pin175 : contactdrift.cveeRead tCentry := by decide +kernel
theorem pin176 : ¬ (([1, 99] : List Nat).length = tCentry.rank) := by
  decide +kernel
theorem pin177 : ¬ (gJoint.length = tCentry.rank) := by decide +kernel
theorem pin178 : ¬ (memberdata.c2M tCentry gJoint [1, 99]
    < (1 + 1) * (contactdrift.grade tCentry [1, 99]
        * contactdrift.grade tCentry [1, 99] + 1)) := by decide +kernel

/-! `lem:contactdrift`'s per-key counts: the key list's identification at
the boxed coroot lists, its length cap, the `θ` factor's read at
the raised member with its dominance over the gap product's
factors, the member dimension's cap, and the two strict per-key
caps — each beside its theorem route, with the binders refused at
their own tables. -/

theorem pin179 : ((ground.boxAll [4, 4, 4]).all (fun m =>
    ground.countOf m (contactdrift.keyAll (sertables.tableB 3) 3)
      == if m.length = 3 ∧ contactdrift.grade (sertables.tableB 3) m = 3
         then 1 else 0)) = true := by decide +kernel

theorem pin180 : (contactdrift.keyAll (sertables.tableB 3) 3).length
    ≤ ground.prodOver (fun _ => 3 + 1) (List.range 3) := by
  decide +kernel

theorem pin181 : ((List.range (sertables.tableB 3).posFolds.length).all
    (fun j => serstable.gapAt (sertables.tableB 3) [3, 2, 1] j
      ≤ contactdrift.thetaGap (sertables.tableB 3) [3, 2, 1])) = true := by
  decide +kernel

theorem pin182 : contactdrift.thetaGap (sertables.tableB 3) ([2, 1, 0].map (· + 1))
    = 2 * (sertables.tableB 3).lenDen
      * (contactdrift.grade (sertables.tableB 3) [2, 1, 0]
          + gentable.residue (sertables.tableB 3)) := by decide +kernel

theorem pin183 : contactdrift.thetaGap (sertables.tableC 3) ([2, 1, 0].map (· + 1))
    = 2 * (sertables.tableC 3).lenDen
      * (contactdrift.grade (sertables.tableC 3) [2, 1, 0]
          + gentable.residue (sertables.tableC 3)) := by decide +kernel

/-! The member dimension's cap over the coefficient box `[2,2,2]`
at `B3`: every gap-product factor at or below the `θ` factor, the
`θ` factor itself the member's own `2 lenDen (G + r)`. -/

theorem pin184 : ((ground.boxAll [2, 2, 2]).all (fun m =>
    memberdata.dimM (sertables.tableB 3) m
      ≤ ground.prodOver
          (fun _ => 2 * (sertables.tableB 3).lenDen
            * (contactdrift.grade (sertables.tableB 3) m
                + gentable.residue (sertables.tableB 3)))
          (List.range (sertables.tableB 3).posFolds.length))) = true := by
  decide +kernel

/-! The two strict per-key caps at `B2` and the key three. -/

theorem pin185 : (contactdrift.keyAll (sertables.tableB 2) 2).length
    < contactdrift.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (contactdrift.capP (sertables.tableB 2))) := by
  decide +kernel

theorem pin186 : ground.sumNat ((contactdrift.keyAll (sertables.tableB 2) 2).map
      (memberdata.dimM (sertables.tableB 2)))
    < contactdrift.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (contactdrift.capP (sertables.tableB 2))) := by
  decide +kernel

/-! The theorem routes beside the decided anchors: the
identification at an inside member and at a member off the rank,
the length cap, the `θ` factor's read, the dimension cap and the
two strict caps. -/

theorem pin187 : ground.countOf [1, 1] (contactdrift.keyAll (sertables.tableB 2) 2)
    = if ([1, 1] : List Nat).length = (sertables.tableB 2).rank
        ∧ contactdrift.grade (sertables.tableB 2) [1, 1] = 2
      then 1 else 0 :=
  contactdrift.keyAll_countOf (sertables.tableB 2) 2 [1, 1] (by decide +kernel)

theorem pin188 : ground.countOf [2] (contactdrift.keyAll (sertables.tableB 2) 2)
    = if ([2] : List Nat).length = (sertables.tableB 2).rank
        ∧ contactdrift.grade (sertables.tableB 2) [2] = 2
      then 1 else 0 :=
  contactdrift.keyAll_countOf (sertables.tableB 2) 2 [2] (by decide +kernel)

theorem pin189 : (contactdrift.keyAll (sertables.tableB 2) 2).length
    ≤ ground.prodOver (fun _ => 2 + 1)
      (List.range (sertables.tableB 2).rank) :=
  contactdrift.keyAll_length (sertables.tableB 2) 2

theorem pin190 : contactdrift.thetaGap (sertables.tableB 3) ([2, 1, 0].map (· + 1))
    = 2 * (sertables.tableB 3).lenDen
      * (contactdrift.grade (sertables.tableB 3) [2, 1, 0]
          + gentable.residue (sertables.tableB 3)) :=
  contactdrift.thetaGap_read (sertables.tableB 3) [2, 1, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin191 : memberdata.dimM (sertables.tableB 3) [2, 1, 0]
    ≤ ground.prodOver
        (fun _ => 2 * (sertables.tableB 3).lenDen
          * (contactdrift.grade (sertables.tableB 3) [2, 1, 0]
              + gentable.residue (sertables.tableB 3)))
        (List.range (sertables.tableB 3).posFolds.length) :=
  contactdrift.dimM_cap (sertables.tableB 3) [2, 1, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pin192 : (contactdrift.keyAll (sertables.tableB 2) 2).length
    < contactdrift.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (contactdrift.capP (sertables.tableB 2))) :=
  contactdrift.keyCount_cap (sertables.tableB 2) 2 (by decide +kernel)
    (by decide +kernel)

theorem pin193 : ground.sumNat ((contactdrift.keyAll (sertables.tableB 2) 2).map
      (memberdata.dimM (sertables.tableB 2)))
    < contactdrift.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (contactdrift.capP (sertables.tableB 2))) :=
  contactdrift.keyDim_cap (sertables.tableB 2) 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! `keyAll_countOf`'s naming binder: at the odd-summand table the
halved summand truncates to the count's unit, so every coroot list
reads the key vacant while the entry bound the box carries is that
same vacant key — the solution `[7]` escapes the box and its count
falls under the identification's unit. -/

theorem pin194 : ground.countOf [7] (contactdrift.keyAll tCzero 0) = 0 := by
  decide +kernel
theorem pin195 : ¬ (ground.countOf [7] (contactdrift.keyAll tCzero 0)
    = if ([7] : List Nat).length = tCzero.rank
        ∧ contactdrift.grade tCzero [7] = 0
      then 1 else 0) := by decide +kernel

/-- `thetaGap_read`'s length binder: a table at the rank one whose
halved summand is the count's unit — the vacant coroot list reads
the `θ` factor at the sum's unit while the cleared right side
carries the residue. -/
private def tDlen : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [[1]], [2]⟩

theorem pin196 : gentable.shapeRead tDlen := by decide +kernel
theorem pin197 : contactdrift.cveeRead tDlen := by decide +kernel
theorem pin198 : ¬ (([] : List Nat).length = tDlen.rank) := by decide +kernel
theorem pin199 : ¬ (contactdrift.thetaGap tDlen (([] : List Nat).map (· + 1))
    = 2 * tDlen.lenDen
      * (contactdrift.grade tDlen [] + gentable.residue tDlen)) := by
  decide +kernel

/-! `thetaGap_read`'s shape binder: the off-rank tail table — the
naming read holds at the rank while the residue and the length
fold read the tail, so the two sides part at the coroot list
`[0]`. -/

theorem pin200 : contactdrift.cveeRead tKtail := by decide +kernel
theorem pin201 : ([0] : List Nat).length = tKtail.rank := by decide +kernel
theorem pin202 : ¬ (contactdrift.thetaGap tKtail (([0] : List Nat).map (· + 1))
    = 2 * tKtail.lenDen
      * (contactdrift.grade tKtail [0] + gentable.residue tKtail)) := by
  decide +kernel

/-- `keyCount_cap`'s and `keyDim_cap`'s positive-list binder: at a
vacant positive list the base `A` is the product's own unit and
the exponent `p` the rank alone, so the cap reads one against the
vacuum's own single label. -/
private def tDnop : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [], [2]⟩

theorem pin203 : gentable.shapeRead tDnop := by decide +kernel
theorem pin204 : contactdrift.cveeRead tDnop := by decide +kernel
theorem pin205 : (1 : Nat) ≤ tDnop.lenDen := by decide +kernel
theorem pin206 : ¬ (1 ≤ tDnop.posFolds.length) := by decide +kernel
theorem pin207 : ¬ ((contactdrift.keyAll tDnop 0).length
    < contactdrift.capA tDnop * ground.prodOver (fun _ => 0 + 1)
        (List.range (contactdrift.capP tDnop))) := by decide +kernel
theorem pin208 : ¬ (ground.sumNat ((contactdrift.keyAll tDnop 0).map
      (memberdata.dimM tDnop))
    < contactdrift.capA tDnop * ground.prodOver (fun _ => 0 + 1)
        (List.range (contactdrift.capP tDnop))) := by decide +kernel

/-- `keyCount_cap`'s and `keyDim_cap`'s length-denominator binder:
at the vacant denominator the base `A` is vacant at an occupied
positive list, so no count sits below it. -/
private def tDden : gentable.Table :=
  ⟨0, [], 0, [], [[]], []⟩

theorem pin209 : gentable.shapeRead tDden := by decide +kernel
theorem pin210 : contactdrift.cveeRead tDden := by decide +kernel
theorem pin211 : (1 : Nat) ≤ tDden.posFolds.length := by decide +kernel
theorem pin212 : ¬ (1 ≤ tDden.lenDen) := by decide +kernel
theorem pin213 : contactdrift.capA tDden = 0 := by decide +kernel
theorem pin214 : ¬ ((contactdrift.keyAll tDden 0).length
    < contactdrift.capA tDden * ground.prodOver (fun _ => 0 + 1)
        (List.range (contactdrift.capP tDden))) := by decide +kernel
theorem pin215 : ¬ (ground.sumNat ((contactdrift.keyAll tDden 0).map
      (memberdata.dimM tDden))
    < contactdrift.capA tDden * ground.prodOver (fun _ => 0 + 1)
        (List.range (contactdrift.capP tDden))) := by decide +kernel

/-! The gap comparison's dominance-join binder, isolated
(`gapAt_le`): at a fold beyond the top — `tMtop`'s second — the
gap product's factor overshoots the `θ` factor outright, the
join the comparison's one witness with the shape and naming reads
held beside it. -/

theorem pin216 : ¬ contactdrift.thetaTopRead tMtop := by decide +kernel
theorem pin217 : ¬ (serstable.gapAt tMtop [1] 1
    ≤ contactdrift.thetaGap tMtop [1]) := by decide +kernel

/-- The gap comparison's shape binder, isolated: the dominance
join reads the folds against the top at the keys below the rank
alone, so a table whose length family runs past the rank prices
gap-product entries the top never sees.  Here the length family
carries two entries at the rank one and the positive fold reads
seven at the second key: the join holds while the gap factor
stands at eight against the `θ` factor's one. -/
private def tDwide : gentable.Table :=
  ⟨1, [1, 1], 1, [[ground.BPair.ofNat 2]], [[1, 7]], [1]⟩

theorem pin218 : contactdrift.thetaTopRead tDwide := by decide +kernel
theorem pin219 : ¬ gentable.shapeRead tDwide := by decide +kernel
theorem pin220 : (0 : Nat) < tDwide.posFolds.length := by decide +kernel
theorem pin221 : ¬ (serstable.gapAt tDwide [1, 1] 0
    ≤ contactdrift.thetaGap tDwide [1, 1]) := by decide +kernel

/-- The same refusal at the vacant rank, where the dominance join
is vacuous: the positive fold reads five at the one key the length
family prices, the highest root's fold vacant there. -/
private def tDvac : gentable.Table :=
  ⟨0, [1], 1, [], [[5]], []⟩

theorem pin222 : contactdrift.thetaTopRead tDvac := by decide +kernel
theorem pin223 : ¬ gentable.shapeRead tDvac := by decide +kernel
theorem pin224 : (0 : Nat) < tDvac.posFolds.length := by decide +kernel
theorem pin225 : ¬ (serstable.gapAt tDvac [1] 0
    ≤ contactdrift.thetaGap tDvac [1]) := by decide +kernel

/-! The grade-key tier's remaining reads at their theorem routes:
the residue join, the vacuum and `ρ` keys, the `A`-series class
reads, the fold's additivity, and the gap factor's dominance —
each the theorem applied at a decided fixture, the route beside
the tier's decided anchors. -/

theorem pin226 : ground.sumNat (contactdrift.cvee (sertables.tableB 4))
    = gentable.residue (sertables.tableB 4) :=
  contactdrift.cvee_sum (sertables.tableB 4) (by decide +kernel)
    (by decide +kernel)

theorem pin227 : contactdrift.grade (sertables.tableB 4)
    (List.replicate (sertables.tableB 4).rank 0) = 0 :=
  contactdrift.grade_vac (sertables.tableB 4)

theorem pin228 : contactdrift.grade (sertables.tableB 4)
    (List.replicate (sertables.tableB 4).rank 1)
    = gentable.residue (sertables.tableB 4) :=
  contactdrift.grade_rho (sertables.tableB 4) (by decide +kernel)
    (by decide +kernel)

theorem pin229 : contactdrift.gradeA (labels.addFulls 2 [2, 1, 0, 1])
    = contactdrift.gradeA [2, 1, 0, 1] :=
  contactdrift.gradeA_fulls 2 [2, 1, 0, 1]

theorem pin230 : contactdrift.gradeA (labels.reduce [2, 1, 0, 1])
    = contactdrift.gradeA [2, 1, 0, 1] :=
  contactdrift.gradeA_reduce [2, 1, 0, 1]

theorem pin231 : (contactdrift.gradeV (sertables.tableB 2)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
      [ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap]))).oneValue
    (contactdrift.gradeV (sertables.tableB 2)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
      + contactdrift.gradeV (sertables.tableB 2)
        [ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap]) :=
  contactdrift.gradeV_add (sertables.tableB 2)
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
    [ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap] rfl

theorem pin232 : serstable.gapAt (sertables.tableB 3) [3, 2, 1] 0
    ≤ contactdrift.thetaGap (sertables.tableB 3) [3, 2, 1] :=
  contactdrift.gapAt_le (sertables.tableB 3) [3, 2, 1] 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! `lem:contactdrift`'s Rayleigh close: the dimension-weighted family's
three quadratic reads, the count occupancy at the cleared head, and
the drift's two arithmetic closes.  The toy head carries three rows
at the dimensions `(1, 3, 5)`, the keys `(0, 2, 4)`, the fusion rows
`[[0,1,0],[1,1,1],[0,1,2]]` and the diagonal `(0, 5, 25)` with
`2N = 4`, `d_θ = 3`, `A = 2`, `p = 1`, `K_N = 5`, `K_D = 1`, and the
scale triple `(a, b, c) = (1, 7, 8)` — the certificate fixture,
where `hcert` reads `4800 ≤ 117440512`.  There the four fold caps
are routed once each with their conclusions decided beside them, and
the ground read is routed at the head's own site datum, the level
members `⟨1007574152 : 1⟩` and `⟨50421 : 1⟩` with the margin one:
the site is negative definite, and its cleared upper-triangular
congruence reads the three one-blocks
`(−1007523732, −1018372697145279453282637632,
−1004061736470154614240993500077194479552435200)`, the count three.
Beside each cap stands its isolating refusal — the move cap's two
binders at the raised target and at the interior row's broken
eigen-identity, the boundary cap's certificate comparison at the
reversed scale pair, the electric cap's Casimir and count binders,
and the vacuum floor's two vacuum reads — and the rate close's two
arithmetic binders are refused at the drift and at the bracket. -/

private def dRt : Nat → Nat := ground.getAt 0 [1, 3, 5]

private def gRt : Nat → Nat := ground.getAt 0 [0, 2, 4]

private def eRt : Nat → Nat := ground.getAt 0 [0, 5, 25]

private def nRt : Nat → Nat → Nat := fun i =>
  ground.getAt 0
    (ground.getAt [] [[0, 1, 0], [1, 1, 1], [0, 1, 2]] i)

private theorem tMove : ∀ i j, i < 3 → j < 3 → 0 < nRt i j →
    gRt j ≤ gRt i + 2 :=
  fun i j hi hj hn =>
    (by decide +kernel : ∀ i, i < 3 → ∀ j, j < 3 → 0 < nRt i j →
      gRt j ≤ gRt i + 2) i hi j hj hn

private theorem tDim : ∀ i, i < 3 → gRt i + 2 ≤ 4 →
    ground.famFold Nat.add 0 (fun j => nRt i j * dRt j)
        (List.range 3)
      = 3 * dRt i := by decide +kernel

private theorem tHe : ∀ i, i < 3 →
    eRt i * 1 ≤ 5 * (gRt i * gRt i + 1) := by decide +kernel

private theorem tCnt : ∀ k, k ≤ 4 →
    ground.famFold Nat.add 0
        (fun i => if gRt i == k then dRt i else 0) (List.range 3)
      ≤ 2 * ground.prodOver (fun _ => k + 1) (List.range 1) := by
  decide +kernel

private theorem tCert : 2 * 3 * (2 * 2)
    * ground.prodOver (fun _ => 4 + 1) (List.range (2 * 1))
    * ground.prodOver (fun _ => 1) (List.range (2 * 4)) * 8
  ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4)) := by
  decide +kernel

/-! The four fold caps at the toy head, each theorem route beside
its decided anchor. -/

theorem pin233 : ground.prodOver (fun _ => 8) (List.range (2 * 4))
    ≤ contactdrift.pairFold 3 4 1 8 dRt gRt :=
  contactdrift.vac_floor 3 4 1 8 0 dRt gRt (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem pin234 : ground.prodOver (fun _ => 8) (List.range (2 * 4))
    ≤ contactdrift.pairFold 3 4 1 8 dRt gRt := by decide +kernel

theorem pin235 : 1 * 1 * 3 * contactdrift.pairFold 3 4 1 8 dRt gRt
    ≤ 8 * 8 * contactdrift.magFold 3 4 1 8 dRt gRt nRt
      + 1 * 1 * 3 * contactdrift.topFold 3 4 1 8 dRt gRt :=
  contactdrift.mag_low 3 4 1 8 3 dRt gRt nRt (by decide +kernel)
    tMove tDim

theorem pin236 : 1 * 1 * 3 * contactdrift.pairFold 3 4 1 8 dRt gRt
    ≤ 8 * 8 * contactdrift.magFold 3 4 1 8 dRt gRt nRt
      + 1 * 1 * 3 * contactdrift.topFold 3 4 1 8 dRt gRt := by
  decide +kernel

theorem pin237 : 1 * 1 * 3 * contactdrift.topFold 3 4 1 8 dRt gRt
    ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4 + 1)) :=
  contactdrift.top_cap 3 4 1 7 8 3 2 1 dRt gRt (by decide +kernel)
    (tCnt 4 (by decide +kernel)) (tCnt (4 - 1) (by decide +kernel))
    tCert

theorem pin238 : 1 * 1 * 3 * contactdrift.topFold 3 4 1 8 dRt gRt
    ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4 + 1)) := by
  decide +kernel

theorem pin239 : ground.prodOver (fun _ => 7) (List.range (2 * 1 + 3)) * 1
      * contactdrift.elecFold 3 4 1 8 dRt gRt eRt
    ≤ 5 * (2 * 2) * ground.rise 1 (2 * 1 + 2)
      * ground.prodOver (fun _ => 8)
          (List.range (2 * 4 + (2 * 1 + 3))) :=
  contactdrift.elec_cap 3 4 1 7 8 2 1 5 1 dRt gRt eRt (by decide +kernel)
    tHe tCnt

theorem pin240 : ground.prodOver (fun _ => 7) (List.range (2 * 1 + 3)) * 1
      * contactdrift.elecFold 3 4 1 8 dRt gRt eRt
    ≤ 5 * (2 * 2) * ground.rise 1 (2 * 1 + 2)
      * ground.prodOver (fun _ => 8)
          (List.range (2 * 4 + (2 * 1 + 3))) := by decide +kernel

/-! The ground read at the toy head: the site datum's own count at
the assembled level and the margin one. -/

private def tSite : Mat :=
  inertia.siteDatum
    (ground.matOf 3 3 (fun i j => BPair.ofNat
      (1 * ground.prodOver (fun _ => 7) (List.range (2 * 1 + 3))
        * (8 * 8) * 1 * (if i == j then eRt i else 0))))
    (ground.matOf 3 3 (fun i j => BPair.ofNat
      (1 * ground.prodOver (fun _ => 7) (List.range (2 * 1 + 3))
        * (8 * 8) * 1 * nRt i j)))

private def tSplit : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1075649, 1⟩, ⟨1157018619905, 1⟩],
     [u, ⟨1, 1007523733⟩, ⟨1, 1083740887278337⟩],
     [u, u, ⟨1010767949975474577, 1⟩]], rfl⟩,
   ⟨[[⟨1, 1018372697145279453282637633⟩,
      ⟨1, 1087230523855219276725249⟩, u],
     [u, ⟨1010767949975474577, 1⟩, ⟨1083740887278337, 1⟩],
     [u, u, ⟨1, 1007523733⟩]], rfl⟩,
   [.one ⟨1, 1007523733⟩,
    .one ⟨1, 1018372697145279453282637633⟩,
    .one ⟨1, 1004061736470154614240993500077194479552435201⟩],
   0, rfl⟩

private theorem tCount : countAtPair tSite (idMat 3)
    ((1007574152 : Pos) + (1 : Pos)) (50421 : Pos) 3 tSplit := by decide +kernel

theorem pin241 : 1 ≤ 3 :=
  contactdrift.family_ground 4 1 7 8 3 2 1 5 1 1 1 0 dRt gRt eRt nRt
    tSite (1007574152 : Pos) (50421 : Pos) (1 : Pos) 3 tSplit
    (by decide +kernel) tMove tDim tHe tCnt tCert
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    tCount

/-! The trial family's three quadratic reads at the toy head, the
theorem route beside its decided anchor each, and the count's
Rayleigh witness routed at the head's own site datum. -/

theorem pin242 : (quadForm
      (ground.matOf 3 3 (fun i j =>
        if i == j then BPair.ofNat (eRt i) else ground.BPair.unit))
      (contactdrift.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (contactdrift.elecFold 3 4 1 8 dRt gRt eRt)) :=
  contactdrift.quad_diag 3 4 1 8 dRt gRt eRt

theorem pin243 : (quadForm
      (ground.matOf 3 3 (fun i j =>
        if i == j then BPair.ofNat (eRt i) else ground.BPair.unit))
      (contactdrift.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (contactdrift.elecFold 3 4 1 8 dRt gRt eRt)) := by
  decide +kernel

theorem pin244 : (quadForm (idMat 3)
      (contactdrift.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (contactdrift.pairFold 3 4 1 8 dRt gRt)) :=
  contactdrift.quad_gram 3 4 1 8 dRt gRt

theorem pin245 : (quadForm (idMat 3)
      (contactdrift.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (contactdrift.pairFold 3 4 1 8 dRt gRt)) := by
  decide +kernel

theorem pin246 : (quadForm
      (ground.matOf 3 3 (fun i j => BPair.ofNat (nRt i j)))
      (contactdrift.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (contactdrift.magFold 3 4 1 8 dRt gRt nRt)) :=
  contactdrift.quad_rows 3 4 1 8 dRt gRt nRt

theorem pin247 : (quadForm
      (ground.matOf 3 3 (fun i j => BPair.ofNat (nRt i j)))
      (contactdrift.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (contactdrift.magFold 3 4 1 8 dRt gRt nRt)) := by
  decide +kernel

theorem pin248 : 1 ≤ 3 :=
  contactdrift.rayleigh_count tSite (idMat 3)
    ((1007574152 : Pos) + (1 : Pos)) (50421 : Pos) 3 tSplit
    (contactdrift.trialVec 3 4 1 8 dRt gRt) (by decide +kernel) tCount
    (by decide +kernel)

/-! The drift's two arithmetic closes, one decided instance each. -/

theorem pin249 : 2 * 1
      * (1 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
          * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
        + 1 * 1 * ground.prodOver (fun _ => 1)
            (List.range (2 * 0 + 4)) * 2)
    + 2 * 1
      * (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2)) * 1 * 1
    ≤ (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
          * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
        + 1 * (2 * 1 + 1)) * 1
        * (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
          * (2 * 2)) * 1
      + 2 * 1
        * (1 * 1 * ground.prodOver (fun _ => 1)
            (List.range (2 * 0 + 3)) * (1 * 1) * 1) :=
  contactdrift.level_drift 0 1 1 1 1 1 1 1 1 2 (by decide +kernel)
    (by decide +kernel)

theorem pin250 : 2 * 1
      * (1 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
          * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
        + 1 * 1 * ground.prodOver (fun _ => 1)
            (List.range (2 * 0 + 4)) * 2)
    + 2 * 1
      * (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2)) * 1 * 1
    ≤ (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
          * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
        + 1 * (2 * 1 + 1)) * 1
        * (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
          * (2 * 2)) * 1
      + 2 * 1
        * (1 * 1 * ground.prodOver (fun _ => 1)
            (List.range (2 * 0 + 3)) * (1 * 1) * 1) := by
  decide +kernel

/-! The drift close's bracket comparison, refused at the heavy
level with the scale tie decided true beside it. -/

theorem pin251 : (1 : Nat) + 1 = 2 := by decide +kernel

theorem pin252 : ¬ (100 * ground.prodOver (fun _ => 2)
      (List.range (2 * 0 + 4))
    ≤ ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 1) := by decide +kernel

theorem pin253 : ¬ (2 * 1
      * (100 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
          * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
        + 1 * 1 * ground.prodOver (fun _ => 1)
            (List.range (2 * 0 + 4)) * 2)
    + 2 * 1
      * (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2)) * 1 * 1
    ≤ (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
          * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
        + 1 * (2 * 1 + 1)) * 1
        * (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
          * (2 * 2)) * 1
      + 2 * 1
        * (1 * 1 * ground.prodOver (fun _ => 1)
            (List.range (2 * 0 + 3)) * (1 * 1) * 1)) := by
  decide +kernel

theorem pin254 : ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (3 : Pos) 2 * (1 : Pos) * ground.Pos.pow (1 : Pos) 2 :=
  contactdrift.rate_close 2 (2 : Pos) (1 : Pos) (3 : Pos) (1 : Pos) (1 : Pos) (1 : Pos) (1 : Pos)
    (by decide +kernel) (by decide +kernel)

theorem pin255 : ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (3 : Pos) 2 * (1 : Pos) * ground.Pos.pow (1 : Pos) 2 := by
  decide +kernel

/-! The move cap's two binders, each refused at its own fixture with
the co-binder decided true beside it. -/

private def dMv : Nat → Nat := ground.getAt 0 [1, 1]

private def gMv : Nat → Nat := ground.getAt 0 [0, 4]

private def nMv : Nat → Nat → Nat := fun i =>
  ground.getAt 0 (ground.getAt [] [[0, 1], [0, 0]] i)

theorem pin256 : ¬ (∀ i, i < 2 → ∀ j, j < 2 → 0 < nMv i j →
    gMv j ≤ gMv i + 2) := by decide +kernel

theorem pin257 : ∀ i, i < 2 → gMv i + 2 ≤ 4 →
    ground.famFold Nat.add 0 (fun j => nMv i j * dMv j)
        (List.range 2)
      = 1 * dMv i := by decide +kernel

theorem pin258 : ¬ (1 * 1 * 1 * contactdrift.pairFold 2 4 1 2 dMv gMv
    ≤ 2 * 2 * contactdrift.magFold 2 4 1 2 dMv gMv nMv
      + 1 * 1 * 1 * contactdrift.topFold 2 4 1 2 dMv gMv) := by
  decide +kernel

private def dDm : Nat → Nat := ground.getAt 0 [1, 1]

private def gDm : Nat → Nat := ground.getAt 0 [0, 2]

private def nDm : Nat → Nat → Nat := fun i =>
  ground.getAt 0 (ground.getAt [] [[0, 0], [0, 1]] i)

theorem pin259 : ∀ i, i < 2 → ∀ j, j < 2 → 0 < nDm i j →
    gDm j ≤ gDm i + 2 := by decide +kernel

theorem pin260 : ¬ (∀ i, i < 2 → gDm i + 2 ≤ 2 →
    ground.famFold Nat.add 0 (fun j => nDm i j * dDm j)
        (List.range 2)
      = 1 * dDm i) := by decide +kernel

theorem pin261 : ¬ (1 * 1 * 1 * contactdrift.pairFold 2 2 1 2 dDm gDm
    ≤ 2 * 2 * contactdrift.magFold 2 2 1 2 dDm gDm nDm
      + 1 * 1 * 1 * contactdrift.topFold 2 2 1 2 dDm gDm) := by
  decide +kernel

/-! The boundary cap's certificate comparison, refused at the
reversed scale pair with the per-key counts decided true. -/

private def dTp : Nat → Nat := ground.getAt 0 [5]

private def gTp : Nat → Nat := ground.getAt 0 [4]

theorem pin262 : ∀ k, k ≤ 4 →
    ground.famFold Nat.add 0
        (fun i => if gTp i == k then dTp i else 0) (List.range 1)
      ≤ 1 * ground.prodOver (fun _ => k + 1) (List.range 1) := by
  decide +kernel

theorem pin263 : ¬ (2 * 1 * (1 * 1)
    * ground.prodOver (fun _ => 4 + 1) (List.range (2 * 1))
    * ground.prodOver (fun _ => 7) (List.range (2 * 4)) * 8
  ≤ 1 * ground.prodOver (fun _ => 8) (List.range (2 * 4))) := by
  decide +kernel

theorem pin264 : ¬ (7 * 7 * 1 * contactdrift.topFold 1 4 7 8 dTp gTp
    ≤ 1 * ground.prodOver (fun _ => 8)
        (List.range (2 * 4 + 1))) := by decide +kernel

/-! The boundary cap's top-key count read, refused at the heavy
key with the under-key read and the certificate comparison decided
true. -/

private def dTc : Nat → Nat := ground.getAt 0 [1000000]

private def gTc : Nat → Nat := ground.getAt 0 [4]

theorem pin265 : ¬ (ground.famFold Nat.add 0
      (fun i => if gTc i == 4 then dTc i else 0) (List.range 1)
    ≤ 1 * ground.prodOver (fun _ => 4 + 1) (List.range 0)) := by
  decide +kernel

theorem pin266 : ground.famFold Nat.add 0
      (fun i => if gTc i == 4 - 1 then dTc i else 0) (List.range 1)
    ≤ 1 * ground.prodOver (fun _ => 4 - 1 + 1) (List.range 0) := by
  decide +kernel

theorem pin267 : 2 * 1 * (1 * 1)
    * ground.prodOver (fun _ => 4 + 1) (List.range (2 * 0))
    * ground.prodOver (fun _ => 1) (List.range (2 * 4)) * 8
  ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4)) := by
  decide +kernel

theorem pin268 : ¬ (1 * 1 * 1 * contactdrift.topFold 1 4 1 8 dTc gTc
    ≤ 7 * ground.prodOver (fun _ => 8)
        (List.range (2 * 4 + 1))) := by decide +kernel

/-! The electric cap's two binders, the Casimir comparison and the
per-key counts, each refused with the other decided true. -/

private def dEc : Nat → Nat := ground.getAt 0 [1]

private def gEc : Nat → Nat := ground.getAt 0 [0]

private def eEc : Nat → Nat := ground.getAt 0 [1000]

theorem pin269 : ¬ (∀ i, i < 1 → eEc i * 1 ≤ 1 * (gEc i * gEc i + 1)) := by
  decide +kernel

theorem pin270 : ∀ k, k ≤ 0 →
    ground.famFold Nat.add 0
        (fun i => if gEc i == k then dEc i else 0) (List.range 1)
      ≤ 1 * ground.prodOver (fun _ => k + 1) (List.range 0) := by
  decide +kernel

theorem pin271 : ¬ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3)) * 1
      * contactdrift.elecFold 1 0 1 2 dEc gEc eEc
    ≤ 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
      * ground.prodOver (fun _ => 2)
          (List.range (2 * 0 + (2 * 0 + 3)))) := by decide +kernel

private def dCt : Nat → Nat := ground.getAt 0 [1, 9]

private def gCt : Nat → Nat := ground.getAt 0 [0, 0]

private def eCt : Nat → Nat := ground.getAt 0 [1, 1]

theorem pin272 : ∀ i, i < 2 → eCt i * 1 ≤ 1 * (gCt i * gCt i + 1) := by
  decide +kernel

theorem pin273 : ¬ (∀ k, k ≤ 0 →
    ground.famFold Nat.add 0
        (fun i => if gCt i == k then dCt i else 0) (List.range 2)
      ≤ 1 * ground.prodOver (fun _ => k + 1) (List.range 0)) := by
  decide +kernel

theorem pin274 : ¬ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3)) * 1
      * contactdrift.elecFold 2 0 1 2 dCt gCt eCt
    ≤ 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
      * ground.prodOver (fun _ => 2)
          (List.range (2 * 0 + (2 * 0 + 3)))) := by decide +kernel

/-! The vacuum floor's two vacuum reads, the key and the dimension,
each refused at its own fixture. -/

private def dVk : Nat → Nat := ground.getAt 0 [1]

private def gVk : Nat → Nat := ground.getAt 0 [2]

theorem pin275 : ¬ gVk 0 = 0 := by decide +kernel

theorem pin276 : dVk 0 = 1 := by decide +kernel

theorem pin277 : ¬ (ground.prodOver (fun _ => 3) (List.range (2 * 2))
    ≤ contactdrift.pairFold 1 2 1 3 dVk gVk) := by decide +kernel

private def dVd : Nat → Nat := ground.getAt 0 [0]

private def gVd : Nat → Nat := ground.getAt 0 [0]

theorem pin278 : ¬ dVd 0 = 1 := by decide +kernel

theorem pin279 : gVd 0 = 0 := by decide +kernel

theorem pin280 : ¬ (ground.prodOver (fun _ => 3) (List.range (2 * 2))
    ≤ contactdrift.pairFold 1 2 1 3 dVd gVd) := by decide +kernel

/-! The vacuum floor's window binder: a vacuum key past the family
refuses the floor, the key and dimension reads holding at the
off-family defaults. -/

private def dVw : Nat → Nat := ground.getAt 1 [0]

private def gVw : Nat → Nat := ground.getAt 0 [5]

theorem pin281 : ¬ (1 < 1) := by decide +kernel

theorem pin282 : gVw 1 = 0 := by decide +kernel

theorem pin283 : dVw 1 = 1 := by decide +kernel

theorem pin284 : ¬ (ground.prodOver (fun _ => 3) (List.range (2 * 2))
    ≤ contactdrift.pairFold 1 2 1 3 dVw gVw) := by decide +kernel

/-! The rate close's two arithmetic binders, the drift comparison
and the bracket, each refused with the other decided true. -/

theorem pin285 : ¬ ((100 : Pos) * (1 : Pos) ≤ (1 : Pos) * (1 : Pos) * (1 : Pos)) := by
  decide +kernel

theorem pin286 : ground.Pos.pow (1 : Pos) 2 * (1 : Pos)
    ≤ (1 : Pos) * ground.Pos.pow (1 : Pos) 2 := by decide +kernel

theorem pin287 : ¬ (ground.Pos.pow (100 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (1 : Pos) 2 * (1 : Pos)
      * ground.Pos.pow (1 : Pos) 2) := by decide +kernel

theorem pin288 : (2 : Pos) * (1 : Pos) ≤ (1 : Pos) * (2 : Pos) * (1 : Pos) := by
  decide +kernel

theorem pin289 : ¬ (ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ (1 : Pos) * ground.Pos.pow (1 : Pos) 2) := by decide +kernel

theorem pin290 : ¬ (ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (1 : Pos) 2 * (1 : Pos)
      * ground.Pos.pow (1 : Pos) 2) := by decide +kernel

/-! The rate composition at the drift battery's data, the route
beside its decided conclusion. -/

theorem pin291 : (69 : Nat) + 1 * 1
    * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
    * (1 * 1) * 1
  ≤ 1 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
      * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
    + 1 * 1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 2
    + 1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (2 * 2) * 1 * 1 := by decide +kernel

theorem pin292 : ground.Pos.pow (69 : Pos) (2 * 0 + 4) * (1 : Pos)
    ≤ ground.Pos.pow (35 : Pos) (2 * 0 + 4) * (1 : Pos)
      * ground.Pos.pow (4 : Pos) (2 * 0 + 4) := by decide +kernel

theorem pin293 : ground.Pos.pow (69 : Pos) (2 * 0 + 4) * (1 : Pos)
    ≤ ground.Pos.pow (35 : Pos) (2 * 0 + 4) * (1 : Pos)
      * ground.Pos.pow (4 : Pos) (2 * 0 + 4) :=
  corner_rate 0 1 1 1 1 1 1 1 1 2 69 69 35 4 1 2 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The composition's four binders, each refused at a fixture
whose conclusion fails with the co-binders decided true: the
margin, the bracket's two sides, and the cap's atom tie. -/

theorem pin294 : ¬ ((1000000 : Nat) + 1 * 1
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (1 * 1) * 1
    ≤ 1 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
        * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
      + 1 * 1
        * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
        * 2
      + 1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2) * 1 * 1) := by
  decide +kernel

theorem pin295 : ((1 : Nat) + 1 = 2)
  ∧ ((1 : Nat) * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
    ≤ ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 1)
  ∧ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4)) * 1
    ≤ 1 * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4)))
  ∧ ((ground.BPair.ofPos (1000000 : Pos)).oneValue
    (ground.BPair.ofNat (1 * 1000000)))
  ∧ ((ground.BPair.ofPos (35 : Pos)).oneValue (ground.BPair.ofNat
    (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
        * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
      + 1 * (2 * 1 + 1))))
  ∧ ((ground.BPair.ofPos (4 : Pos)).oneValue (ground.BPair.ofNat
    (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (2 * 2) * 1)))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (2 : Pos)).oneValue (ground.BPair.ofNat 2))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1)) := by
  decide +kernel

theorem pin296 : ¬ (ground.Pos.pow (1000000 : Pos) (2 * 0 + 4) * (1 : Pos)
    ≤ ground.Pos.pow (35 : Pos) (2 * 0 + 4) * (1 : Pos)
      * ground.Pos.pow (4 : Pos) (2 * 0 + 4)) := by
  decide +kernel

theorem pin297 : ¬ ((3 : Nat) * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
    ≤ ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 1) := by
  decide +kernel

theorem pin298 : ((1 : Nat) + 1 = 2)
  ∧ ((197 : Nat) + 1 * 1
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (1 * 1) * 1
    ≤ 3 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
        * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
      + 1 * 1
        * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
        * 2
      + 1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2) * 1 * 1)
  ∧ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4)) * 1
    ≤ 3 * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4)))
  ∧ ((ground.BPair.ofPos (197 : Pos)).oneValue
    (ground.BPair.ofNat (1 * 197)))
  ∧ ((ground.BPair.ofPos (35 : Pos)).oneValue (ground.BPair.ofNat
    (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
        * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
      + 1 * (2 * 1 + 1))))
  ∧ ((ground.BPair.ofPos (4 : Pos)).oneValue (ground.BPair.ofNat
    (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (2 * 2) * 1)))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (2 : Pos)).oneValue (ground.BPair.ofNat 2))
  ∧ ((ground.BPair.ofPos (3 : Pos)).oneValue (ground.BPair.ofNat 3))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1)) := by
  decide +kernel

theorem pin299 : ¬ (ground.Pos.pow (197 : Pos) (2 * 0 + 4) * (1 : Pos)
    ≤ ground.Pos.pow (35 : Pos) (2 * 0 + 4) * (3 : Pos)
      * ground.Pos.pow (4 : Pos) (2 * 0 + 4)) := by
  decide +kernel

theorem pin300 : ¬ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4)) * 1000000
    ≤ 1 * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))) := by
  decide +kernel

theorem pin301 : ((1 : Nat) + 1 = 2)
  ∧ ((5000064 : Nat) + 1000000 * 1
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (1 * 1) * 1
    ≤ 1 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
        * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
      + 1000000 * 1
        * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
        * 2
      + 1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2) * 1000000 * 1)
  ∧ ((1 : Nat) * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
    ≤ ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 1000000)
  ∧ ((ground.BPair.ofPos (5000064 : Pos)).oneValue
    (ground.BPair.ofNat (1 * 5000064)))
  ∧ ((ground.BPair.ofPos (35 : Pos)).oneValue (ground.BPair.ofNat
    (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
        * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
      + 1 * (2 * 1 + 1))))
  ∧ ((ground.BPair.ofPos (4000000 : Pos)).oneValue (ground.BPair.ofNat
    (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (2 * 2) * 1000000)))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (2 : Pos)).oneValue (ground.BPair.ofNat 2))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (1000000 : Pos)).oneValue (ground.BPair.ofNat 1000000)) := by
  decide +kernel

theorem pin302 : ¬ (ground.Pos.pow (5000064 : Pos) (2 * 0 + 4) * (1000000 : Pos)
    ≤ ground.Pos.pow (35 : Pos) (2 * 0 + 4) * (1 : Pos)
      * ground.Pos.pow (4000000 : Pos) (2 * 0 + 4)) := by
  decide +kernel

theorem pin303 : ¬ ((ground.BPair.ofPos (17 : Pos)).oneValue (ground.BPair.ofNat
    (ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
        * (1 * (1 * 1) * ground.rise 1 (2 * 0 + 2))
      + 1 * (2 * 1 + 1)))) := by
  decide +kernel

theorem pin304 : ((1 : Nat) + 1 = 2)
  ∧ ((69 : Nat) + 1 * 1
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (1 * 1) * 1
    ≤ 1 * 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
        * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 5))
      + 1 * 1
        * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
        * 2
      + 1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
        * (2 * 2) * 1 * 1)
  ∧ ((1 : Nat) * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
    ≤ ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 1)
  ∧ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4)) * 1
    ≤ 1 * ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4)))
  ∧ ((ground.BPair.ofPos (69 : Pos)).oneValue
    (ground.BPair.ofNat (1 * 69)))
  ∧ ((ground.BPair.ofPos (4 : Pos)).oneValue (ground.BPair.ofNat
    (1 * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3))
      * (2 * 2) * 1)))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (2 : Pos)).oneValue (ground.BPair.ofNat 2))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1))
  ∧ ((ground.BPair.ofPos (1 : Pos)).oneValue (ground.BPair.ofNat 1)) := by
  decide +kernel

theorem pin305 : ¬ (ground.Pos.pow (69 : Pos) (2 * 0 + 4) * (1 : Pos)
    ≤ ground.Pos.pow (17 : Pos) (2 * 0 + 4) * (1 : Pos)
      * ground.Pos.pow (4 : Pos) (2 * 0 + 4)) := by
  decide +kernel


/-! The drift's margin comparison (`drift_margin`) at the committed
reads: the levels `⟨3 : 2⟩` and `⟨5 : 1⟩` carry the counts
`gm + GY = 1 + 2`, `GY = 2`, `X + E = 2 + 3` and `V = 1`, and the
cross-added level order prices the assembled margin at the cap's
shift, the shared grading weight cancelling. -/

theorem pin306 : 3 + 1 ≤ 3 + 2 := by decide +kernel

theorem pin307 : 3 + 1 ≤ 3 + 2 :=
  drift_margin 1 2 3 1 3 2 1 2 1 4 1 (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The order binder isolates: at reads placing the vacant level
above the occupied margin — `⟨5 : 1⟩` reading `4 + 1` against
`⟨2 : 1⟩` reading `1 + 1` — the reads hold, the strict cross-added
order refuses, and the margin comparison's conclusion refuses with
it.  The cap binder isolates at the same data with the order kept:
the second member priced beyond its cap refuses the conclusion. -/

theorem pin308 : (ground.BPair.ofPos (5 : Pos)).oneValue
    (ground.BPair.ofNat (4 + 1)) := by decide +kernel

theorem pin309 : ¬ ((5 : Pos) + 1 < (2 : Pos) + 1) := by decide +kernel

theorem pin310 : ¬ (4 + 1 ≤ 1 + 1) := by decide +kernel

theorem pin311 : ((3 : Pos) + 1 < (4 : Pos) + 1) ∧ ¬ (5 ≤ 2)
    ∧ ¬ (7 + 1 ≤ 3 + 2) := by decide +kernel

/-! The join whole at the one-place head `H = [3]` over the unit
gram: the level `⟨1 : 1⟩` reads the count nought and the level
`⟨5 : 1⟩` the count one, `count_below_occupied` holds the vacant
level strictly below the occupied margin, and `drift_margin` reads
that order back at the first occupied level `0`, the cap `1` on
the drift's second member, the margin `X = 4` at its unit shift
and the weight `V = 1` — the join's own composition read, the two
counts through the cap to the drift datum. -/

private def dmH : Mat := [[⟨4, 1⟩]]

private theorem dmVac :
    certconstruct.countAtPair dmH (idMat 1) 1 1 0 (inertia.oneSplit [⟨4, 1⟩]) := by
  decide +kernel

private theorem dmOcc :
    certconstruct.countAtPair dmH (idMat 1) 5 1 1 (inertia.oneSplit [⟨1, 2⟩]) := by
  decide +kernel

theorem pin312 : 1 + 1 ≤ 4 + 1 :=
  drift_margin 0 1 1 1 4 1 1 1 1 5 1
    (certconstruct.count_below_occupied dmH 1 1 5 1 1
      (inertia.oneSplit [⟨4, 1⟩]) (inertia.oneSplit [⟨1, 2⟩]) dmVac dmOcc (Nat.le_refl 1))
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end contactdrift
