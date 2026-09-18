import MassGap.Certconstruct
/-!
The check module for `thm:certconstruct`: the batteries re-read the
counts' identity instances by kernel `decide` at the pencil
`H = diag(1, 3)` against the unit gram — the pair-level counts at
their split certificates (`countRead` at levels two and four), the
balance-pair level's coherence with the pair level's
(`countAtPair` at `⟨3 : 1⟩` against the level two), a designation
of the jump at three (`desigRead` at the levels `[5:2]` and
`[7:2]`, counts one and two), the least root's sharpening
(`leastRead` at `[1:2]` against `[3:2]`, the lower pair positive
semidefinite), and clause (2)'s witness (`witnessRead`, the first
coordinate's vector at the exceeded read, the elimination's
lower-side column), and the shift transport
(`countAtPair_shift` at the gram-diagonal shift two, the shifted
pencil's count read at the shifted level both ways with the
unshifted level's refusal beside them), and the seam transport
(`countAtPair_scale`, `countAtPair_unscale` at the factor four, the
scaled pencil's count at the scaled level both ways with the
mismatched factor's, the unscaled member's and the moved count's
refusals beside them), and the monotone read
(`countAtPair_mono` at the pencils `diag(3, 5)` and `diag(1, 3)`
at one level and at the one pencil `diag(1, 3)` between the levels
`⟨3 : 1⟩` and `⟨5 : 1⟩` — the pencil face and the level face of the
one general — each difference site `diag(2, 2)` positive
semidefinite, with the reversed difference's positive-semidefinite
conjunct refused beside them), and the cross identity
(`countAtPair_cross` at the level `⟨3 : 1⟩` crossed by two, one
count at one split both ways, with the weight applied to one member
alone refused beside it), and the count-to-drift join
(`count_below_occupied` at the one-place head `H = [3]`, the level
`⟨1 : 1⟩` vacant against the level `⟨5 : 1⟩` occupied, with the
occupancy binder refused at two vacant levels of the failing order
and the vacancy binder refused at two occupied ones) with its two
carriers beside it — the scalar certificate at the order two and
the scalar two (`inertia.scalarSplit` at its upper-side read and
the diagonal `diag(2, 2)`'s split) and the two levels' difference
site at the pencil `diag(1, 3)` reading that scalar copy
(`siteDiff_scalar`, the cross-added level order's margin two). -/

namespace certconstruct
set_option maxHeartbeats 4000000

open ground elim inertia

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

/-! The pair-level counts at their splits: `count(2) = 1` at the
datum `diag(-1, 1)` and `count(4) = 2` at `diag(-3, -1)`. -/

theorem pin1 : countRead hD (idMat 2) 2 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) := by decide +kernel
theorem pin2 : countRead hD (idMat 2) 4 1 2 (inertia.oneSplit [⟨1, 4⟩, ⟨1, 2⟩]) := by decide +kernel

/-! The balance-pair level's coherence: `count⟨3 : 1⟩` is the
level-two count, the second member cross-added onto the pencil's
side. -/

theorem pin3 : countAtPair hD (idMat 2) 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) := by
  decide +kernel

/-! The designation of the jump at three: the levels `[5:2] < [7:2]`
at counts one and two, the gap one, the bracket's whole
verification. -/

theorem pin4 : desigRead hD (idMat 2) 5 2 7 2 1
    (inertia.oneSplit [⟨1, 4⟩, ⟨2, 1⟩]) (inertia.oneSplit [⟨1, 6⟩, ⟨1, 2⟩]) := by decide +kernel

/-! The least root's sharpening: the pair at `[1:2]` positive
semidefinite and the count at `[3:2]` occupied. -/

theorem pin5 : leastRead hD (idMat 2) 1 2 3 2
    (inertia.oneSplit [⟨2, 1⟩, ⟨6, 1⟩]) (inertia.oneSplit [⟨1, 2⟩, ⟨4, 1⟩]) := by decide +kernel

/-! Clause (2)'s witness at `(H : 2G)`: the first coordinate's
vector reads the exceeded pair, the elimination's lower-side
column. -/

theorem pin6 : witnessRead hD (matScale 2 (idMat 2)) [⟨2, 1⟩, u] := by
  decide +kernel

/-! The pair-order refusal: a mismatched pair is refused at the
leaf read's own conjuncts, the truncation's compression off the
claim. -/

theorem pin7 : ¬ countRead [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]]
    (idMat 2) 2 1 2 (inertia.oneSplit [⟨1, 2⟩, ⟨1, 2⟩]) := by decide +kernel

/-! The shift transport: the pencil shifted by twice the gram reads
its count at the level's member raised by two — the two endpoint
certificates decided, the theorem route both ways, and the
unshifted level's refusal isolating the shift. -/

theorem pin8 : countAtPair (matAdd (matScale 2 (idMat 2)) hD) (idMat 2)
    3 1 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) := by decide +kernel
theorem pin9 : countAtPair hD (idMat 2) 3 3 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) := by
  decide +kernel
theorem pin10 : countAtPair hD (idMat 2) 3 (1 + 2) 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) :=
  (countAtPair_shift hD (idMat 2) 2 3 1 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩])
    (by decide +kernel)).mp (by decide +kernel)
theorem pin11 : countAtPair (matAdd (matScale 2 (idMat 2)) hD) (idMat 2)
    3 1 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) :=
  (countAtPair_shift hD (idMat 2) 2 3 1 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩])
    (by decide +kernel)).mpr (by decide +kernel)
theorem pin12 : ¬ countAtPair hD (idMat 2) 3 1 0
    (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) := by decide +kernel

/-! The pencil-shape binder: a three-order pencil truncates to the
gram's order under the sum, so the shifted certificate holds while
the unshifted pencil refuses the order read — the binder's own
isolating record. -/

private def hT : Mat :=
  [[⟨2, 1⟩, u, u], [u, ⟨4, 1⟩, u], [u, u, ⟨6, 1⟩]]

theorem pin13 : ¬ elim.sqAt hT 2 := by decide +kernel
theorem pin14 : countAtPair (matAdd (matScale 2 (idMat 2)) hT) (idMat 2)
    3 1 0 (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) := by decide +kernel
theorem pin15 : ¬ countAtPair hT (idMat 2) 3 3 0
    (inertia.oneSplit [⟨2, 1⟩, ⟨4, 1⟩]) := by decide +kernel

/-! The seam transport (`lem:dualtrunc`): the ray's positive factor
rescales the pencil and both of the level's members together, the
reversal count blind to it.  At `c = 4` — the ray `τ = [1:2]`'s
`q²` — the pencil `4H = diag(4, 12)` at the level `⟨12 : 4⟩` reads
the level `⟨3 : 1⟩`'s own count one, its datum `diag(-4, 4)` the
unscaled datum `diag(-1, 1)` rescaled: the scaled certificate by
`decide`, then the theorem route forward, then the `σ`-side read
back at `p²σ = q²` with `p = 1`, `σ = 4`. -/

theorem pin16 : countAtPair (matScale 4 hD) (idMat 2) 12 4 1
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) := by decide +kernel

theorem pin17 : countAtPair (matScale 4 hD) (idMat 2) (4 * 3) (4 * 1) 1
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) :=
  countAtPair_scale 4 hD (idMat 2) 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩])
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) (by decide +kernel) (by decide +kernel)

theorem pin18 : countAtPair hD (idMat 2) 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) :=
  countAtPair_unscale 4 hD (idMat 2) 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩])
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) (by decide +kernel) (by decide +kernel)

/-! The factor's refusals, each isolating one binder of the
transport.  (a) The factor `c` shared by the pencil `matScale c H`
and the level's pair `(c·x, c·y)`: the pencil at `4H` against the
level scaled by three, `⟨9 : 3⟩`, reads the datum `diag(-2, 6)` and
refuses the scaled certificate.  (b) The level's second member
`c·y`, the member cross-added onto the pencil's own side: left
unscaled at `⟨12 : 1⟩` the datum is `diag(-7, 1)` and the read
refuses.  (c) The count `n`, carried from the unscaled certificate
by the reversal's blindness: the scaled datum's one negative block
refuses the count two. -/

theorem pin19 : ¬ countAtPair (matScale 4 hD) (idMat 2) 9 3 1
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) := by decide +kernel
theorem pin20 : ¬ countAtPair (matScale 4 hD) (idMat 2) 12 1 1
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) := by decide +kernel
theorem pin21 : ¬ countAtPair (matScale 4 hD) (idMat 2) 12 4 2
    (inertia.oneSplit [⟨1, 5⟩, ⟨5, 1⟩]) := by decide +kernel

/-! The pencil's order rides the scaled certificate alone: the
rescaling keeps the row count and every row's width, so the square
read reflects across it (`countAtPair_unscale`'s derivation) — the
three-order pencil's scaled read refusing here, its unscaled read
refusing at the shift battery above. -/

theorem pin22 : ¬ elim.sqAt (matScale 4 hT) 2 := by decide +kernel

/-! The count's monotone read (`countAtPair_mono`): at the gram's
unit and the level `⟨5 : 1⟩` the upper pencil `diag(3, 5)` reads the
site `diag(-1, 1)` at count one and the lower pencil `diag(1, 3)`
reads `diag(-3, -1)` at count two, their difference site
`diag(2, 2)` positive semidefinite — the upper count at or below the
lower's.  The difference's own orientation is the read's one datum:
taken the other way the site is `diag(-2, -2)` and the split's
reversal fold is two, so the positive-semidefinite conjunct
refuses. -/

private def hU : Mat := [[⟨4, 1⟩, u], [u, ⟨6, 1⟩]]

private theorem monoUp :
    countAtPair hU (idMat 2) 5 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) := by
  decide +kernel
private theorem monoLo :
    countAtPair hD (idMat 2) 5 1 2 (inertia.oneSplit [⟨1, 4⟩, ⟨1, 2⟩]) := by
  decide +kernel
private theorem monoSite : splitRead (siteDatum
    (siteDatum (matAdd hU (matScale 1 (idMat 2))) (matScale 5 (idMat 2)))
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 5 (idMat 2))))
    (inertia.oneSplit [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel
private theorem monoPsd : psdAt (inertia.oneSplit [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel

theorem pin23 : (1 : Nat) ≤ 2 :=
  countAtPair_mono hU hD (idMat 2) 5 1 5 1 1 2
    (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) (inertia.oneSplit [⟨1, 4⟩, ⟨1, 2⟩]) (inertia.oneSplit [⟨3, 1⟩, ⟨3, 1⟩])
    monoSite monoPsd monoUp monoLo

theorem pin24 : splitRead (siteDatum
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 5 (idMat 2)))
    (siteDatum (matAdd hU (matScale 1 (idMat 2))) (matScale 5 (idMat 2))))
    (inertia.oneSplit [⟨1, 3⟩, ⟨1, 3⟩]) := by decide +kernel
theorem pin25 : ¬ psdAt (inertia.oneSplit [⟨1, 3⟩, ⟨1, 3⟩]) := by decide +kernel

/-! The monotone read's level face: at the one pencil `diag(1, 3)`
the level `⟨3 : 1⟩` reads count one and the level `⟨5 : 1⟩` count
two, the difference site `diag(2, 2)` positive semidefinite — the
lower level's count at or below the higher's, the general's second
face with the pencil fixed and the level moved. -/

private theorem faceLo :
    countAtPair hD (idMat 2) 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) := by
  decide +kernel

theorem pin26 : splitRead (siteDatum
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 3 (idMat 2)))
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 5 (idMat 2))))
    (inertia.oneSplit [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel

theorem pin27 : (1 : Nat) ≤ 2 :=
  countAtPair_mono hD hD (idMat 2) 3 1 5 1 1 2
    (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) (inertia.oneSplit [⟨1, 4⟩, ⟨1, 2⟩]) (inertia.oneSplit [⟨3, 1⟩, ⟨3, 1⟩])
    (by decide +kernel) monoPsd faceLo monoLo

/-! The cross identity (`countAtPair_cross`): the level `⟨3 : 1⟩`
crossed by two on both members reads the same count at the same
split — the site matrices tie entrywise — while the weight applied
to the first member alone moves the site off the stated split, the
both-members binder's refusal. -/

theorem pin28 : countAtPair hD (idMat 2) (3 + 2) (1 + 2) 1
    (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) :=
  countAtPair_cross hD (idMat 2) 2 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) faceLo

theorem pin29 : countAtPair hD (idMat 2) (3 + 2) (1 + 2) 1
    (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) := by decide +kernel

theorem pin30 : ¬ countAtPair hD (idMat 2) (3 + 2) 1 1
    (inertia.oneSplit [⟨1, 2⟩, ⟨2, 1⟩]) := by decide +kernel

/-! The count-to-drift join at the one-place head `H = [3]` over the
unit gram (`count_below_occupied`): the level `⟨1 : 1⟩` reads the
count nought and the level `⟨5 : 1⟩` the count one, and the
cross-added order holds the vacant level strictly below the
occupied one.  Each consumed binder is refused on its own — at the two vacant
levels `⟨3 : 1⟩` and `⟨2 : 1⟩` the two counts are nought and the
cross-added order fails, the occupancy binder's own refusal; and at
the two occupied levels `⟨7 : 1⟩` and `⟨6 : 1⟩` the gap level's
count is one, its vacant read refused at the same failing order. -/

private def hO : Mat := [[⟨4, 1⟩]]

private theorem drVac : countAtPair hO (idMat 1) 1 1 0 (inertia.oneSplit [⟨4, 1⟩]) := by
  decide +kernel

private theorem drOcc : countAtPair hO (idMat 1) 5 1 1 (inertia.oneSplit [⟨1, 2⟩]) := by
  decide +kernel

theorem pin31 : (1 : Pos) + 1 < (5 : Pos) + 1 := by decide +kernel

theorem pin32 : (1 : Pos) + 1 < (5 : Pos) + 1 :=
  count_below_occupied hO 1 1 5 1 1 (inertia.oneSplit [⟨4, 1⟩]) (inertia.oneSplit [⟨1, 2⟩])
    drVac drOcc (Nat.le_refl 1)

theorem pin33 : countAtPair hO (idMat 1) 3 1 0 (inertia.oneSplit [⟨2, 1⟩]) := by decide +kernel
theorem pin34 : countAtPair hO (idMat 1) 2 1 0 (inertia.oneSplit [⟨3, 1⟩]) := by decide +kernel
theorem pin35 : ¬ (1 ≤ 0) := by decide +kernel
theorem pin36 : ¬ ((3 : Pos) + 1 < (2 : Pos) + 1) := by decide +kernel

theorem pin37 : countAtPair hO (idMat 1) 6 1 1 (inertia.oneSplit [⟨1, 3⟩]) := by decide +kernel
theorem pin38 : countAtPair hO (idMat 1) 7 1 1 (inertia.oneSplit [⟨1, 4⟩]) := by decide +kernel
theorem pin39 : ¬ countAtPair hO (idMat 1) 7 1 0 (inertia.oneSplit [⟨1, 4⟩]) := by decide +kernel
theorem pin40 : ¬ ((7 : Pos) + 1 < (6 : Pos) + 1) := by decide +kernel

/-! The scalar certificate at the order two and the scalar two
(`inertia.scalarSplit`): the identity congruence with one positive
block per key reads the upper side throughout, and every matrix of
the gram's scalar value splits at it — the diagonal `diag(2, 2)` at
the vacant off-diagonal. -/

private def hSc : Mat := [[⟨3, 1⟩, u], [u, ⟨3, 1⟩]]

theorem pin41 : psdAt (scalarSplit 2 2) := by decide +kernel
theorem pin42 : psdAt (scalarSplit 2 2) := scalarSplit_psd 2 2

theorem pin43 : splitRead hSc (scalarSplit 2 2) := by decide +kernel
theorem pin44 : splitRead hSc (scalarSplit 2 2) :=
  scalarSplit_read 2 hSc (by decide +kernel) (by decide +kernel)

/-! The scalar-copy binder isolates: a matrix off the unit gram's
scalar copy — occupied off the diagonal — refuses the scalar
certificate while its shape read holds. -/

theorem pin45 : elim.sqAt [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]] 2 := by
  decide +kernel

theorem pin46 : ¬ matOneValue [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
    (matScale 2 (idMat 2)) := by decide +kernel

theorem pin47 : ¬ splitRead [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
    (scalarSplit 2 2) := by decide +kernel

/-! The difference site at the pencil `diag(1, 3)` and the levels
`⟨1 : 1⟩` and `⟨3 : 1⟩` (`siteDiff_scalar`): the two site matrices'
own site reads the gram's scalar copy at the cross-added level
order's margin two. -/

theorem pin48 : matOneValue
    (siteDatum
      (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 1 (idMat 2)))
      (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 3 (idMat 2))))
    (matScale 2 (idMat 2)) := by decide +kernel

theorem pin49 : matOneValue
    (siteDatum
      (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 1 (idMat 2)))
      (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 3 (idMat 2))))
    (matScale 2 (idMat 2)) :=
  siteDiff_scalar (o := 2) hD (idMat 2) (by decide +kernel)
    (by decide +kernel) 1 1 3 1 2 (by decide +kernel)

/-! The margin binder isolates: at the same pencil and levels the
wrong margin's scalar copy refuses the difference-site read while
the level identity at the stated margin holds beside it. -/

theorem pin50 : (1 : Pos) + 1 + 2 = 3 + 1 := by decide +kernel

theorem pin51 : ¬ matOneValue
    (siteDatum
      (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 1 (idMat 2)))
      (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 3 (idMat 2))))
    (matScale 1 (idMat 2)) := by decide +kernel

end certconstruct
