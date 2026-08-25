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
alone refused beside it). -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

private def spLt (a b : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one a, .one b], 0, rfl⟩

/-! The pair-level counts at their splits: `count(2) = 1` at the
datum `diag(-1, 1)` and `count(4) = 2` at `diag(-3, -1)`. -/

example : countRead hD (idMat 2) 2 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel
example : countRead hD (idMat 2) 4 1 2 (spLt ⟨1, 4⟩ ⟨1, 2⟩) := by decide +kernel

/-! The balance-pair level's coherence: `count⟨3 : 1⟩` is the
level-two count, the second member cross-added onto the pencil's
side. -/

example : countAtPair hD (idMat 2) 3 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩) := by
  decide +kernel

/-! The designation of the jump at three: the levels `[5:2] < [7:2]`
at counts one and two, the gap one, the bracket's whole
verification. -/

example : desigRead hD (idMat 2) 5 2 7 2 1
    (spLt ⟨1, 4⟩ ⟨2, 1⟩) (spLt ⟨1, 6⟩ ⟨1, 2⟩) := by decide +kernel

/-! The least root's sharpening: the pair at `[1:2]` positive
semidefinite and the count at `[3:2]` occupied. -/

example : leastRead hD (idMat 2) 1 2 3 2
    (spLt ⟨2, 1⟩ ⟨6, 1⟩) (spLt ⟨1, 2⟩ ⟨4, 1⟩) := by decide +kernel

/-! Clause (2)'s witness at `(H : 2G)`: the first coordinate's
vector reads the exceeded pair, the elimination's lower-side
column. -/

example : witnessRead hD (matScale 2 (idMat 2)) [⟨2, 1⟩, u] := by
  decide +kernel

/-! The pair-order refusal: a mismatched pair is refused at the
leaf read's own conjuncts, the truncation's compression off the
claim. -/

example : ¬ countRead [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]]
    (idMat 2) 2 1 2 (spLt ⟨1, 2⟩ ⟨1, 2⟩) := by decide +kernel

/-! The shift transport: the pencil shifted by twice the gram reads
its count at the level's member raised by two — the two endpoint
certificates decided, the theorem route both ways, and the
unshifted level's refusal isolating the shift. -/

example : countAtPair (matAdd (matScale 2 (idMat 2)) hD) (idMat 2)
    3 1 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel
example : countAtPair hD (idMat 2) 3 3 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩) := by
  decide +kernel
example : countAtPair hD (idMat 2) 3 (1 + 2) 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩) :=
  (countAtPair_shift hD (idMat 2) 2 3 1 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩)
    (by decide +kernel)).mp (by decide +kernel)
example : countAtPair (matAdd (matScale 2 (idMat 2)) hD) (idMat 2)
    3 1 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩) :=
  (countAtPair_shift hD (idMat 2) 2 3 1 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩)
    (by decide +kernel)).mpr (by decide +kernel)
example : ¬ countAtPair hD (idMat 2) 3 1 0
    (spLt ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel

/-! The pencil-shape binder: a three-order pencil truncates to the
gram's order under the sum, so the shifted certificate holds while
the unshifted pencil refuses the order read — the binder's own
isolating record. -/

private def hT : Mat :=
  [[⟨2, 1⟩, u, u], [u, ⟨4, 1⟩, u], [u, u, ⟨6, 1⟩]]

example : ¬ elim.sqAt hT 2 := by decide +kernel
example : countAtPair (matAdd (matScale 2 (idMat 2)) hT) (idMat 2)
    3 1 0 (spLt ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel
example : ¬ countAtPair hT (idMat 2) 3 3 0
    (spLt ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel

/-! The seam transport (`lem:dualtrunc`): the ray's positive factor
rescales the pencil and both of the level's members together, the
reversal count blind to it.  At `c = 4` — the ray `τ = [1:2]`'s
`q²` — the pencil `4H = diag(4, 12)` at the level `⟨12 : 4⟩` reads
the level `⟨3 : 1⟩`'s own count one, its datum `diag(-4, 4)` the
unscaled datum `diag(-1, 1)` rescaled: the scaled certificate by
`decide`, then the theorem route forward, then the `σ`-side read
back at `p²σ = q²` with `p = 1`, `σ = 4`. -/

example : countAtPair (matScale 4 hD) (idMat 2) 12 4 1
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) := by decide +kernel

example : countAtPair (matScale 4 hD) (idMat 2) (4 * 3) (4 * 1) 1
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) :=
  countAtPair_scale 4 hD (idMat 2) 3 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩)
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) (by decide +kernel) (by decide +kernel)

example : countAtPair hD (idMat 2) 3 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩) :=
  countAtPair_unscale 4 hD (idMat 2) 3 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩)
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) (by decide +kernel) (by decide +kernel)

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

example : ¬ countAtPair (matScale 4 hD) (idMat 2) 9 3 1
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) := by decide +kernel
example : ¬ countAtPair (matScale 4 hD) (idMat 2) 12 1 1
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) := by decide +kernel
example : ¬ countAtPair (matScale 4 hD) (idMat 2) 12 4 2
    (spLt ⟨1, 5⟩ ⟨5, 1⟩) := by decide +kernel

/-! The pencil's order rides the scaled certificate alone: the
rescaling keeps the row count and every row's width, so the square
read reflects across it (`countAtPair_unscale`'s derivation) — the
three-order pencil's scaled read refusing here, its unscaled read
refusing at the shift battery above. -/

example : ¬ elim.sqAt (matScale 4 hT) 2 := by decide +kernel

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
    countAtPair hU (idMat 2) 5 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩) := by
  decide +kernel
private theorem monoLo :
    countAtPair hD (idMat 2) 5 1 2 (spLt ⟨1, 4⟩ ⟨1, 2⟩) := by
  decide +kernel
private theorem monoSite : splitRead (siteDatum
    (siteDatum (matAdd hU (matScale 1 (idMat 2))) (matScale 5 (idMat 2)))
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 5 (idMat 2))))
    (spLt ⟨3, 1⟩ ⟨3, 1⟩) := by decide +kernel
private theorem monoPsd : psdAt (spLt ⟨3, 1⟩ ⟨3, 1⟩) := by decide +kernel

example : (1 : Nat) ≤ 2 :=
  countAtPair_mono hU hD (idMat 2) 5 1 5 1 1 2
    (spLt ⟨1, 2⟩ ⟨2, 1⟩) (spLt ⟨1, 4⟩ ⟨1, 2⟩) (spLt ⟨3, 1⟩ ⟨3, 1⟩)
    monoSite monoPsd monoUp monoLo

example : splitRead (siteDatum
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 5 (idMat 2)))
    (siteDatum (matAdd hU (matScale 1 (idMat 2))) (matScale 5 (idMat 2))))
    (spLt ⟨1, 3⟩ ⟨1, 3⟩) := by decide +kernel
example : ¬ psdAt (spLt ⟨1, 3⟩ ⟨1, 3⟩) := by decide +kernel

/-! The monotone read's level face: at the one pencil `diag(1, 3)`
the level `⟨3 : 1⟩` reads count one and the level `⟨5 : 1⟩` count
two, the difference site `diag(2, 2)` positive semidefinite — the
lower level's count at or below the higher's, the general's second
face with the pencil fixed and the level moved. -/

private theorem faceLo :
    countAtPair hD (idMat 2) 3 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩) := by
  decide +kernel

example : splitRead (siteDatum
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 3 (idMat 2)))
    (siteDatum (matAdd hD (matScale 1 (idMat 2))) (matScale 5 (idMat 2))))
    (spLt ⟨3, 1⟩ ⟨3, 1⟩) := by decide +kernel

example : (1 : Nat) ≤ 2 :=
  countAtPair_mono hD hD (idMat 2) 3 1 5 1 1 2
    (spLt ⟨1, 2⟩ ⟨2, 1⟩) (spLt ⟨1, 4⟩ ⟨1, 2⟩) (spLt ⟨3, 1⟩ ⟨3, 1⟩)
    (by decide +kernel) monoPsd faceLo monoLo

/-! The cross identity (`countAtPair_cross`): the level `⟨3 : 1⟩`
crossed by two on both members reads the same count at the same
split — the site matrices tie entrywise — while the weight applied
to the first member alone moves the site off the stated split, the
both-members binder's refusal. -/

example : countAtPair hD (idMat 2) (3 + 2) (1 + 2) 1
    (spLt ⟨1, 2⟩ ⟨2, 1⟩) :=
  countAtPair_cross hD (idMat 2) 2 3 1 1 (spLt ⟨1, 2⟩ ⟨2, 1⟩) faceLo

example : countAtPair hD (idMat 2) (3 + 2) (1 + 2) 1
    (spLt ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel

example : ¬ countAtPair hD (idMat 2) (3 + 2) 1 1
    (spLt ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel
