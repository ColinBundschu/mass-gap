import MassGap.Corner
import MassGap.Divisorid
import MassGap.Decimation
import MassGap.Channeldiv
import MassGap.Chargedcell
/-!
The check module for `lem:corner`'s count tier: the batteries read
the corner count by kernel `decide` at the scale pair `η = [2 : 1]`
and the height `η′ = ⟨3 : 1⟩` over the unit gram, the corner data
`E = diag(1, 3)`, `M = diag(1, 2)`.  There the displayed pair's
cleared site is `4E + 2G − M − 6G = diag(-1, 6)`, its reversal count
one at the diagonal split — the anchor — with the count zero refused
beside it, and a forged two-by-three `E` refusing the order read of
the corner data's first member.  The route battery consumes
`corner_dual` in both directions at the same data: the corner count
against the seam pencil `cornerPencil E M 2 1 = 4E − M = diag(3, 2)`
at the level members `(2·1·3, 2·1·1)` (`certconstruct.countAtPair`).
The corner presentation's block reads the same tier at the
two-variable pencil over `E = diag(5, 3)`, `M = [[2, -1], [-1, 1]]`
and the unit gram at the scale `[2 : 3]` and the height `⟨5 : 7⟩`:
the double evaluation of `cornerPP` decided at the corner site
`[[14, 9], [9, 15]]` beside its `cornerPP_eval` route, the count
tie routed in both directions at the committed split — the
congruence `[[1, -9], [0, 14]]` with its adjugate clearing the site
to `diag(14, 1806)`, the count nought — and the tie's three order
binders refused one at a time at a member grown to three, where the
componentwise walk keeps the evaluated presentation's count while
the member's own order read fails.  The ray coordinate's
read-backs stand at the extent `[3 : 2]` — the ray `[2 : 1]` in it
and `[3 : 1]` off it, both coordinates' doubled representatives
routed through the two congruences — and the level's height read
at the scale `[2 : 3]`, the height `[5 : 7]`, the ray weights
`(4, 9)` and the level `[30 : 7]`, the floor `[1 : 2]` clearing
and the floor `[3 : 4]` refusing, each direction beside its
decided anchor.  The corner divisor's own block reads the toy's
two-variable minor at its primitive split — one factor at
height-degree two with the content the unit — and the crossing
read `−η⁴ (4η⁴ − 4η² + 5)` with its quartic factor the sum of
squares `(2η² − 1)² + 4`.
The shifted scaling tier's batteries stand at the electric form
`E = diag(2, 1)`, the cap's summand `S_θ = 4G − M = diag(3, 2)` and
the two scales `σ = [3 : 1]`, `σ′ = [1 : 2]` at the cross gap
`g = 5`: the comparison display (`shiftQ_split`) decided at the
literal data and taken again through the theorem, the upper side
(`shift_count_le`, counts one against two at the level `⟨12 : 1⟩`)
and the lower side (`shift_count_scale`, counts one against nought
at the same level) each at their certificates, and the corner ray's
monotone read (`dual_count_mono`) at the ray points `[3 : 1]` and
`[1 : 2]` with the gap `35`, counts one against two.  Beside each
comparison stands its isolating refusal: the two gap joins refused
at the exchanged scale pairs, and the positive-semidefinite binders
refused at an indefinite datum — `E = diag(1, -1)` for the two
electric-difference comparisons and `S_θ = diag(1, -1)` (at
`d_θ = 2` over `M = diag(1, 3)`) for the cap's — each with the two
counts that make the conclusion fail decided beside it.

The cutoff block reads the scale key and the
seed floor's window clearing: the key's
value, its own comparison and its minimality at the fixture
`η = [2 : 3]`, `ϑ = [1 : 2]`, `d_ϑ = 3`, top `⟨4 : 1⟩` — the fold
`135`, the clearance `18`, the step `32`, the key `4` — with the
two positivity binders refused at the vacant scale numerator and
the vacant level denominator; the seed floor's clearing routed at
the Casimir `5` and the level `⟨3 : 0⟩` with its three binders
refused one at a time where the conclusion fails.

The height section's block closes the file at the extent toy
`E = [[1, 1], [1, 2]]`, `M = 4E − I` over the unit gram.  The
section at the height `⟨2 : 1⟩` is the scale pencil whose
determinant is `η⁴ − 3η³ − 4η² + 10η + 5`, and the two evaluation
pins stand beside their `cornerAtHeight_eval` routes at the scale
points `[2 : 3]` and `[1 : 1]`.  On that section the emitted record
is committed whole — three cells at `η = 1/4, 1, 3` over the
clearing weight `4` with counts `2, 2, 1`, the divisor's
content-reduced Bézout certificate at the squarefree determinant, a
comparison boundary at the cutoff display `32η² − 13` and a jump
boundary at the divisor's root in `(2, 3)` — with the truncated
boundary list, a forged count and the two tag forgeries refused
beside it.  The two vacant families stand there as well: the deck
walk's three reads at the base `c₁ = 2` with the crossing pair
`[9 : 4]`, and the tension's matched-stencil read through
`chargedcell.tension_free`, each family's own display a constant
whose segment count over the record's range is nought — the
stated count and the endpoints' order each refused beside it.  The
t-section rides `deckfactor.bandClear` — vacant at a constant
display, refusing at the display `t` whose root sits inside the
crossing segment with both splits read — and the rank direction
reads the deck base as the member-key count at `d = 3`, `d = 5` and
`d = 2`, the walk's chord at that count the chord at two.
-/

namespace corner
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct


private def u : BPair := BPair.unit

private def cE : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

private def cM : Mat := [[⟨2, 1⟩, u], [u, ⟨3, 1⟩]]

/-! The corner anchor: at the scale `[2 : 1]` and the height
`⟨3 : 1⟩` the cleared display reads `diag(-1, 6)`, one negative
block, the corner count one. -/

private theorem cAnchor :
    cornerCount cE cM (idMat 2) 2 1 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) := by
  decide +kernel

private theorem cEsq : elim.sqAt cE 2 := by decide +kernel

private theorem cMsq : elim.sqAt cM 2 := by decide +kernel

/-! The count's refusal: the same certificate's reversal fold is
one, so the count zero is refused. -/

theorem pin1 : ¬ cornerCount cE cM (idMat 2) 2 1 3 1 0 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) := by
  decide +kernel

/-! The height's two members sit on the two sides they are
cross-added onto: exchanging `hp` and `hm` moves the display to
`4E + 6G − M − 2G = diag(7, 14)` and refuses the anchor's
certificate. -/

theorem pin2 : ¬ cornerCount cE cM (idMat 2) 2 1 1 3 1
    (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) := by decide +kernel

/-! The forged-shape refusal: the corner data's first member off the
gram's order — a two-by-three `E` — refuses the order conjunct at
otherwise-valid data, while the seam pencil's count stands at the
truncated assembly: the order conjunct is the refusal's own. -/

private def cEwide : Mat := [[⟨2, 1⟩, u, u], [u, ⟨4, 1⟩, u]]

theorem pin3 : ¬ elim.sqAt cEwide 2 := by decide +kernel
theorem pin4 : ¬ cornerCount cEwide cM (idMat 2) 2 1 3 1 1
    (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) := by decide +kernel
theorem pin5 : countAtPair (cornerPencil cEwide cM 2 1) (idMat 2)
    (2 * 1 * 3) (2 * 1 * 1) 1 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) := by decide +kernel

/-! The substitution's route (`corner_dual`): the corner count is
the seam pencil's count at the level members `(2·1·3, 2·1·1)`, the
iff consumed in both directions at the anchor's data. -/

theorem pin6 : countAtPair (cornerPencil cE cM 2 1) (idMat 2)
    (2 * 1 * 3) (2 * 1 * 1) 1 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) :=
  (corner_dual cE cM (idMat 2) 2 1 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩])
    cEsq cMsq).mp cAnchor

theorem pin7 : cornerCount cE cM (idMat 2) 2 1 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩]) :=
  (corner_dual cE cM (idMat 2) 2 1 3 1 1 (inertia.oneSplit [⟨1, 2⟩, ⟨7, 1⟩])
    cEsq cMsq).mpr (by decide +kernel)

/-! The corner presentation's batteries at the two-variable pencil:
the corner data `E = diag(5, 3)`, `M = [[2, -1], [-1, 1]]` over the
unit gram at the scale `[2 : 3]` and the height `⟨5 : 7⟩`.  There
the double evaluation of `cornerPP` reads the corner site
`4E + 12G − 9M = [[14, 9], [9, 15]]`, whose upper-triangular
congruence `T = [[1, -9], [0, 14]]` at the adjugate
`Tw = [[14, 9], [0, 1]]` and the determinant `14` clears to the
positive diagonal `diag(14, 1806)`, the count nought. -/

private def pE : Mat := [[⟨6, 1⟩, u], [u, ⟨4, 1⟩]]

private def pM : Mat := [[⟨3, 1⟩, ⟨1, 2⟩], [⟨1, 2⟩, ⟨2, 1⟩]]

private def pG : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]

private def pT : Mat := [[⟨2, 1⟩, ⟨1, 10⟩], [u, ⟨15, 1⟩]]

private def pTw : Mat := [[⟨15, 1⟩, ⟨10, 1⟩], [u, ⟨2, 1⟩]]

private def pSplit : Split 2 :=
  ⟨⟨pT, rfl⟩, ⟨pTw, rfl⟩, [.one ⟨15, 1⟩, .one ⟨1807, 1⟩], 0, rfl⟩

theorem pin8 : elim.matOneValue (cornerSite pE pM pG 2 3 5 7)
    [[⟨15, 1⟩, ⟨10, 1⟩], [⟨10, 1⟩, ⟨16, 1⟩]] := by decide +kernel

/-! The double evaluation's identity, decided at the fixture and
taken again through `cornerPP_eval`. -/

theorem pin9 : elim.matOneValue
    (cellcount.evalPC
      (cellcount.ppevalPC (cornerPP pE pM pG) (BPair.ofPos 2) 3 2)
      ⟨5, 7⟩ Pos.one 1)
    (cornerSite pE pM pG 2 3 5 7) := by decide +kernel

theorem pin10 : elim.matOneValue
    (cellcount.evalPC
      (cellcount.ppevalPC (cornerPP pE pM pG) (BPair.ofPos 2) 3 2)
      ⟨5, 7⟩ Pos.one 1)
    (cornerSite pE pM pG 2 3 5 7) :=
  cornerPP_eval pE pM pG 2 3 5 7

/-! The count tie's route: the height-direction count of the
evaluated presentation at the committed split, decided as the
anchor and consumed in both directions. -/

private theorem pAnchor : cellcount.countAt
    (cellcount.ppevalPC (cornerPP pE pM pG) (BPair.ofPos 2) 3 2)
    1 ⟨5, 7⟩ Pos.one 0 pSplit := by decide +kernel

private theorem pEsq : elim.sqAt pE 2 := by decide +kernel

private theorem pMsq : elim.sqAt pM 2 := by decide +kernel

private theorem pGsq : elim.sqAt pG 2 := by decide +kernel

theorem pin11 : cornerCount pE pM pG 2 3 5 7 0 pSplit :=
  (cornerPP_count pE pM pG 2 3 5 7 0 pSplit pEsq pMsq pGsq).mp pAnchor

theorem pin12 : cellcount.countAt
    (cellcount.ppevalPC (cornerPP pE pM pG) (BPair.ofPos 2) 3 2)
    1 ⟨5, 7⟩ Pos.one 0 pSplit :=
  (cornerPP_count pE pM pG 2 3 5 7 0 pSplit pEsq pMsq pGsq).mpr
    (by decide +kernel)

/-! The count tie's three order binders: an oversized member is
truncated away by the componentwise walk, so the evaluated
presentation keeps its count while the corner count refuses the
member's own order read — the tie fails at each of the three, the
other two decided at their orders. -/

private def pEw : Mat :=
  [[⟨6, 1⟩, u, u], [u, ⟨4, 1⟩, u], [u, u, u]]

private def pMw : Mat :=
  [[⟨3, 1⟩, ⟨1, 2⟩, u], [⟨1, 2⟩, ⟨2, 1⟩, u], [u, u, u]]

private def pGw : Mat :=
  [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u], [u, u, u]]

theorem pin13 : ¬ elim.sqAt pEw 2 := by decide +kernel

theorem pin14 : ¬ elim.sqAt pMw 2 := by decide +kernel

theorem pin15 : ¬ elim.sqAt pGw 2 := by decide +kernel

theorem pin16 : cellcount.countAt
    (cellcount.ppevalPC (cornerPP pEw pM pG) (BPair.ofPos 2) 3 2)
    1 ⟨5, 7⟩ Pos.one 0 pSplit := by decide +kernel

theorem pin17 : ¬ (cellcount.countAt
      (cellcount.ppevalPC (cornerPP pEw pM pG) (BPair.ofPos 2) 3 2)
      1 ⟨5, 7⟩ Pos.one 0 pSplit
    ↔ cornerCount pEw pM pG 2 3 5 7 0 pSplit) := by decide +kernel

theorem pin18 : cellcount.countAt
    (cellcount.ppevalPC (cornerPP pE pMw pG) (BPair.ofPos 2) 3 2)
    1 ⟨5, 7⟩ Pos.one 0 pSplit := by decide +kernel

theorem pin19 : ¬ (cellcount.countAt
      (cellcount.ppevalPC (cornerPP pE pMw pG) (BPair.ofPos 2) 3 2)
      1 ⟨5, 7⟩ Pos.one 0 pSplit
    ↔ cornerCount pE pMw pG 2 3 5 7 0 pSplit) := by decide +kernel

theorem pin20 : cellcount.countAt
    (cellcount.ppevalPC (cornerPP pE pM pGw) (BPair.ofPos 2) 3 2)
    1 ⟨5, 7⟩ Pos.one 0 pSplit := by decide +kernel

theorem pin21 : ¬ (cellcount.countAt
      (cellcount.ppevalPC (cornerPP pE pM pGw) (BPair.ofPos 2) 3 2)
      1 ⟨5, 7⟩ Pos.one 0 pSplit
    ↔ cornerCount pE pM pGw 2 3 5 7 0 pSplit) := by decide +kernel

/-! `lem:corner`'s ray coordinate read-backs at the extent
`η₁ = [3 : 2]`: the ray `[2 : 1]` sits in it and the ray `[3 : 1]`
does not, and the membership is one value across both coordinates'
representatives — the ray at its doubled pair and the extent at its
doubled pair — each theorem route beside its decided anchor. -/

theorem pin22 : rayInExtent 2 1 3 2 := by decide +kernel

theorem pin23 : ¬ rayInExtent 3 1 3 2 := by decide +kernel

private theorem rRay : (2 : Pos) * 2 = 4 * 1 := by decide +kernel

private theorem rExt : (3 : Pos) * 4 = 6 * 2 := by decide +kernel

theorem pin24 : rayInExtent 4 2 3 2 := by decide +kernel

theorem pin25 : rayInExtent 4 2 3 2 :=
  (rayInExtent_ray 2 1 4 2 3 2 rRay).mp (by decide +kernel)

theorem pin26 : rayInExtent 2 1 3 2 :=
  (rayInExtent_ray 2 1 4 2 3 2 rRay).mpr (by decide +kernel)

theorem pin27 : rayInExtent 2 1 6 4 := by decide +kernel

theorem pin28 : rayInExtent 2 1 6 4 :=
  (rayInExtent_ext 2 1 3 2 6 4 rExt).mp (by decide +kernel)

theorem pin29 : rayInExtent 2 1 3 2 :=
  (rayInExtent_ext 2 1 3 2 6 4 rExt).mpr (by decide +kernel)

/-! The level's height read at the scale `η = [2 : 3]`, the height
`η′ = [5 : 7]`, the ray weights `(α, β) = (4, 9)` and the level
`λ = [30 : 7]`: the scale tie `α ed² = en² β` and the cofactor
`λ (ed hd) = ld β (en hn)` carry the level's clearance to the
height's own comparison, the floor `κ = [1 : 2]` clearing it and
the floor `κ = [3 : 4]` refusing it, each side beside its decided
anchor. -/

private theorem lRay : (4 : Pos) * (3 * 3) = 2 * 2 * 9 := by
  decide +kernel

private theorem lCof : (30 : Pos) * (3 * 7) = 7 * (9 * (2 * 5)) := by
  decide +kernel

theorem pin30 : levelClears 30 7 1 2 4 9 := by decide +kernel

theorem pin31 : (1 : Pos) * 7 ≤ 5 * 2 := by decide +kernel

theorem pin32 : (1 : Pos) * 7 ≤ 5 * 2 :=
  (level_height 2 3 5 7 30 7 1 2 4 9 lRay lCof).mp (by decide +kernel)

theorem pin33 : levelClears 30 7 1 2 4 9 :=
  (level_height 2 3 5 7 30 7 1 2 4 9 lRay lCof).mpr (by decide +kernel)

theorem pin34 : ¬ levelClears 30 7 3 4 4 9 := by decide +kernel

theorem pin35 : ¬ ((3 : Pos) * 7 ≤ 5 * 4) := by decide +kernel

theorem pin36 : ¬ levelClears 30 7 3 4 4 9 :=
  fun h => (by decide +kernel : ¬ ((3 : Pos) * 7 ≤ 5 * 4))
    ((level_height 2 3 5 7 30 7 3 4 4 9 lRay lCof).mp h)

theorem pin37 : ¬ ((3 : Pos) * 7 ≤ 5 * 4) :=
  fun h => (by decide +kernel : ¬ levelClears 30 7 3 4 4 9)
    ((level_height 2 3 5 7 30 7 3 4 4 9 lRay lCof).mpr h)

/-! The corner divisor at the presentation's toy: the two-variable
minor `χ = η² x² + η (3 − 8η²) x + (15η⁴ − 11η² + 1)` is primitive
over the base at its stated top, one factor at height-degree two
with the content the unit (`divisorid.splitRead`), and the crossing
read (`thm:divisorid`) is `D = −η⁴ (4η⁴ − 4η² + 5)`, whose quartic
factor is the sum of squares `(2η² − 1)² + 4`: the vacant scale is
the divisor's every located root. -/

private def pChi : poly.PPoly := split.ppminor (cornerPP pE pM pG)

private def pDiv : poly.Poly := divisorid.crossD [pChi]

theorem pin38 : poly.ppOneValue pChi
    [[⟨2, 1⟩, u, ⟨1, 12⟩, u, ⟨16, 1⟩], [u, ⟨4, 1⟩, u, ⟨1, 9⟩],
      [u, u, ⟨2, 1⟩]] := by decide +kernel

theorem pin39 : divisorid.splitRead pChi poly.one [pChi] := by decide +kernel

private def pDivL : poly.Poly :=
  [u, u, u, u, ⟨1, 6⟩, u, ⟨5, 1⟩, u, ⟨1, 5⟩]

private theorem pDiv_pin : poly.oneValue pDiv pDivL := by
  decide +kernel

/-! The located output's leading-term radius at the presentation
toy's divisor (`thm:windowsep`'s root bound, the cell datum beside
the output): the radius reads through the pinned display
(`windowsep.radiusD_congr`) and the flat window's two heights sit
inside it. -/

theorem pin40 : windowsep.radiusD pDivL = ⟨5, 1⟩ := by decide +kernel

theorem pin41 : windowsep.radiusD pDiv = ⟨5, 1⟩ :=
  (windowsep.radiusD_congr pDiv_pin).trans (by decide +kernel)

theorem pin42 : (⟨2, 1⟩ : BPair) < windowsep.radiusD pDivL
    ∧ (⟨3, 1⟩ : BPair) < windowsep.radiusD pDivL := by decide +kernel

theorem pin43 : poly.oneValue
    (poly.add (poly.mul [⟨1, 2⟩, u, ⟨3, 1⟩] [⟨1, 2⟩, u, ⟨3, 1⟩])
      [⟨5, 1⟩])
    [⟨6, 1⟩, u, ⟨1, 5⟩, u, ⟨5, 1⟩] := by decide +kernel

/-! The flat window at the corner carrier: the toy's window at the
heights `⟨1 : 2⟩` and `⟨2 : 1⟩`, both counts one — the sites
`[[8, 9], [9, 9]]` and `[[-4, 9], [9, -3]]` at one lower-side
block each — the route beside its decided anchor, and the two
shape binders' isolating refusals at the padded members with the
co-binder decided true beside each. -/

private def cfA : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 10⟩], [u, ⟨9, 1⟩]], rfl⟩,
   ⟨[[⟨9, 1⟩, ⟨10, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨9, 1⟩, .one ⟨1, 73⟩], 0, rfl⟩

private def cfT : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 10⟩], [u, ⟨1, 5⟩]], rfl⟩,
   ⟨[[⟨1, 5⟩, ⟨10, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 5⟩, .one ⟨277, 1⟩], 0, rfl⟩

theorem pin44 : flatstep.vacFlat (corner.cornerPencil pE pM 2 3) pG
      (2 * 3 * 1) (2 * 3 * 2) (2 * 3 * 2) (2 * 3 * 1) 1 cfA cfT
    ↔ (corner.cornerCount pE pM pG 2 3 1 2 1 cfA
      ∧ corner.cornerCount pE pM pG 2 3 2 1 1 cfT
      ∧ 1 ≤ 1 ∧ (1 : Pos) + 1 < 2 + 2) :=
  corner.corner_flat pE pM pG 2 3 1 2 2 1 1 cfA cfT
    (by decide +kernel) (by decide +kernel)

theorem pin45 : flatstep.vacFlat (corner.cornerPencil pE pM 2 3) pG
      (2 * 3 * 1) (2 * 3 * 2) (2 * 3 * 2) (2 * 3 * 1) 1 cfA cfT
    ∧ corner.cornerCount pE pM pG 2 3 1 2 1 cfA
    ∧ corner.cornerCount pE pM pG 2 3 2 1 1 cfT := by
  decide +kernel

theorem pin46 : elim.sqAt pM 2 := by decide +kernel

theorem pin47 : ¬ (flatstep.vacFlat (corner.cornerPencil pEw pM 2 3) pG
      (2 * 3 * 1) (2 * 3 * 2) (2 * 3 * 2) (2 * 3 * 1) 1 cfA cfT
    ↔ (corner.cornerCount pEw pM pG 2 3 1 2 1 cfA
      ∧ corner.cornerCount pEw pM pG 2 3 2 1 1 cfT
      ∧ 1 ≤ 1 ∧ (1 : Pos) + 1 < 2 + 2)) := by decide +kernel

theorem pin48 : elim.sqAt pE 2 := by decide +kernel

theorem pin49 : ¬ (flatstep.vacFlat (corner.cornerPencil pE pMw 2 3) pG
      (2 * 3 * 1) (2 * 3 * 2) (2 * 3 * 2) (2 * 3 * 1) 1 cfA cfT
    ↔ (corner.cornerCount pE pMw pG 2 3 1 2 1 cfA
      ∧ corner.cornerCount pE pMw pG 2 3 2 1 1 cfT
      ∧ 1 ≤ 1 ∧ (1 : Pos) + 1 < 2 + 2)) := by decide +kernel

/-! The corner extent at a root-bearing head: `E = [[1,1],[1,2]]`,
`M = 4E − I` over the unit gram, where the corner divisor is
`−5η⁴(η² − 4)²` — the origin's least occupied degree four, the
cofactor `−5(η² − 4)²` at the occupied constant, its squarefree
part `−5η² + 20` with the root `η = 2` bracketed at `[1, 3]` and
the leading segment `[0, 1]` vacant — the withdrawal read routed
whole with the two off-degree refusals beside it. -/

private def fE : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]

private def fM : Mat := [[⟨4, 1⟩, ⟨5, 1⟩], [⟨5, 1⟩, ⟨8, 1⟩]]

private def xChi : poly.PPoly := split.ppminor (corner.cornerPP fE fM pG)

theorem pin50 : poly.ppOneValue xChi
    [[⟨6, 1⟩, u, ⟨1, 6⟩, u, ⟨2, 1⟩],
     [u, ⟨11, 1⟩, u, ⟨1, 4⟩],
     [u, u, ⟨2, 1⟩]] := by decide +kernel

theorem pin51 : divisorid.splitRead xChi poly.one [xChi] := by
  decide +kernel

private def xDiv : poly.Poly :=
  [u, u, u, u, ⟨1, 81⟩, u, ⟨41, 1⟩, u, ⟨1, 6⟩]

private theorem xDiv_pin : poly.oneValue (divisorid.crossD [xChi])
    xDiv := by decide +kernel

/-! The extent's leading-term radius at the corner divisor
(`thm:windowsep`'s root bound, the cell datum beside the output):
the radius reads through the pinned display
(`windowsep.radiusD_congr`) and the extent bracket's upper end
sits inside it. -/

theorem pin52 : windowsep.radiusD xDiv = ⟨6, 1⟩ := by decide +kernel

theorem pin53 : windowsep.radiusD (divisorid.crossD [xChi]) = ⟨6, 1⟩ :=
  (windowsep.radiusD_congr xDiv_pin).trans (by decide +kernel)

theorem pin54 : (⟨2, 1⟩ : BPair) < windowsep.radiusD xDiv := by
  decide +kernel

private def xCt : cellcount.DivCert :=
  ⟨[⟨1, 5⟩, ⟨1, 1⟩], [⟨21, 1⟩, ⟨1, 1⟩, ⟨1, 6⟩], [⟨1, 1⟩, ⟨1, 21⟩],
   [⟨1, 21⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨6, 1⟩], [⟨21, 1⟩, ⟨1, 1⟩, ⟨1, 6⟩],
   [⟨1, 11⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨6, 1⟩],
   1, 1, 1, 1, ⟨1, 401⟩, ⟨1, 201⟩⟩

private def xH : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨201, 1⟩], 0, rfl⟩

private def xB1 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1001, 1⟩], [u, ⟨201, 1⟩]], rfl⟩,
   ⟨[[⟨201, 1⟩, ⟨1, 1001⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨201, 1⟩, .one ⟨600000001, 1⟩], 0, rfl⟩

private def xB2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨4001, 1⟩], [u, ⟨351, 1⟩]], rfl⟩,
   ⟨[[⟨351, 1⟩, ⟨1, 4001⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨351, 1⟩, .one ⟨1, 1312500001⟩], 0, rfl⟩

theorem pin55 : contactcell.extentRead xDiv 4 xCt
    ⟨2, 1⟩ ⟨4, 1⟩ 1 xH xB1 xH xB2 := by decide +kernel

theorem pin56 : contactcell.extentRead (divisorid.crossD [xChi]) 4 xCt
    ⟨2, 1⟩ ⟨4, 1⟩ 1 xH xB1 xH xB2 :=
  (contactcell.extentRead_congr xDiv_pin 4 xCt ⟨2, 1⟩ ⟨4, 1⟩ 1
    xH xB1 xH xB2).mpr (by decide +kernel)

theorem pin57 : ¬ contactcell.extentRead xDiv 3 xCt
    ⟨2, 1⟩ ⟨4, 1⟩ 1 xH xB1 xH xB2 := by decide +kernel

theorem pin58 : ¬ contactcell.extentRead xDiv 5 xCt
    ⟨2, 1⟩ ⟨4, 1⟩ 1 xH xB1 xH xB2 := by decide +kernel

/-! The bracket conjunct isolates at a mis-set bracket `[3, 5]`:
the withdrawal's two conjuncts hold at the degree four while the
leading segment holds the root, so the located read alone
parts. -/

theorem pin59 : ¬ contactcell.extentRead xDiv 4 xCt
    ⟨4, 1⟩ ⟨6, 1⟩ 1 xH xB1 xH xB2 := by decide +kernel

theorem pin60 : poly.unitTail (xDiv.take 4)
    ∧ ¬ (ground.getAt ground.BPair.unit xDiv 4).oneValue
      ground.BPair.unit := by decide +kernel

/-! The shifted scaling tier's fixtures: the electric form
`E = diag(2, 1)` positive semidefinite, the cap's summand
`S_θ = d_θ G − M` at `d_θ = 4` over the unit gram and `M = diag(1, 2)`
reading `diag(3, 2)`, and the two scales `σ = [3 : 1]`,
`σ′ = [1 : 2]` with the cross gap `g = 5` at the order's witness
`tn·sd + g = sn·td`.  There `sd·Q(σ) = diag(9, 5)` and
`td·Q(σ′) = diag(8, 5)`. -/

private def eF : Mat := [[⟨3, 1⟩, u], [u, ⟨2, 1⟩]]

private theorem sGap : (1 : Pos) * 1 + 5 = 3 * 2 := by decide +kernel

/-! The scales' comparison display (`shiftQ_split`): at the cleared
carrier `σ σ′`'s common weight reads
`6·(td·Q(σ′)) = diag(48, 30) = 2·(sd·Q(σ)) + 10·S_θ`, the second
summand the cap's form — the identity decided at the literal data
and the theorem's own route beside it. -/

theorem pin61 : matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cM 4 1 2)
    = matAdd (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cM 4 3 1))
        (matScale (1 * 2 * 5) (stheta (idMat 2) cM 4)) := by
  decide +kernel

theorem pin62 : matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cM 4 1 2)
    = matAdd (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cM 4 3 1))
        (matScale (1 * 2 * 5) (stheta (idMat 2) cM 4)) :=
  shiftQ_split eF (idMat 2) cM 4 3 1 1 2 5 sGap

/-! The pencil is a sum of two positive-semidefinite forms
(`shiftQ_psd`): at the fixture `sd·Q(σ) = diag(9, 5)` splits
positive semidefinite from its two summands' own splits,
`3E = diag(6, 3)` and `1·S_θ = diag(3, 2)`. -/

private theorem sQe : splitRead (matScale 3 eF)
    (inertia.oneSplit [⟨7, 1⟩, ⟨4, 1⟩]) := by decide +kernel
private theorem sQePsd : psdAt (inertia.oneSplit [⟨7, 1⟩, ⟨4, 1⟩]) := by decide +kernel
private theorem sQs : splitRead (matScale 1 (stheta (idMat 2) cM 4))
    (inertia.oneSplit [⟨4, 1⟩, ⟨3, 1⟩]) := by decide +kernel
private theorem sQq : splitRead (shiftQ eF (idMat 2) cM 4 3 1)
    (inertia.oneSplit [⟨10, 1⟩, ⟨6, 1⟩]) := by decide +kernel

theorem pin63 : psdAt (inertia.oneSplit [⟨10, 1⟩, ⟨6, 1⟩]) := by decide +kernel
theorem pin64 : psdAt (inertia.oneSplit [⟨10, 1⟩, ⟨6, 1⟩]) :=
  shiftQ_psd eF (idMat 2) cM 4 3 1
    (inertia.oneSplit [⟨7, 1⟩, ⟨4, 1⟩]) (inertia.oneSplit [⟨4, 1⟩, ⟨3, 1⟩]) (inertia.oneSplit [⟨10, 1⟩, ⟨6, 1⟩])
    sQe sQePsd sQs (by decide +kernel) sQq

/-! Two equal scales read one pencil outright (`shiftQ_eq`): at the
crossed tie `4·1 = 2·2` the two cleared pencils are one matrix,
`diag(14, 8)`, decided at the literal data and through the
theorem. -/

theorem pin65 : matScale 2 (shiftQ eF (idMat 2) cM 4 2 1)
    = matScale 1 (shiftQ eF (idMat 2) cM 4 4 2) := by decide +kernel
theorem pin66 : matScale 2 (shiftQ eF (idMat 2) cM 4 2 1)
    = matScale 1 (shiftQ eF (idMat 2) cM 4 4 2) :=
  shiftQ_eq eF (idMat 2) cM 4 2 1 4 2 (by decide +kernel)

/-! The comparison's upper side (`shift_count_le`): at the level
`⟨12 : 1⟩` over the unit gram the upper scale's cleared pencil
`2·(sd·Q(σ)) = diag(18, 10)` reads the site `diag(7, -1)` at count
one and the lower scale's `1·(td·Q(σ′)) = diag(8, 5)` reads
`diag(-3, -6)` at count two, their difference the gap's electric
diagonal `5E = diag(10, 5)` positive semidefinite. -/

private theorem sleUp : countAtPair
    (matScale 2 (shiftQ eF (idMat 2) cM 4 3 1))
    (idMat 2) 12 1 1 (inertia.oneSplit [⟨8, 1⟩, ⟨1, 2⟩]) := by decide +kernel
private theorem sleLo : countAtPair
    (matScale 1 (shiftQ eF (idMat 2) cM 4 1 2))
    (idMat 2) 12 1 2 (inertia.oneSplit [⟨1, 4⟩, ⟨1, 7⟩]) := by decide +kernel
private theorem eFsplit : splitRead eF (inertia.oneSplit [⟨3, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel
private theorem eFpsd : psdAt (inertia.oneSplit [⟨3, 1⟩, ⟨2, 1⟩]) := by decide +kernel
private theorem sleScaled : splitRead (matScale 5 eF)
    (inertia.oneSplit [⟨11, 1⟩, ⟨6, 1⟩]) := by decide +kernel

theorem pin67 : (1 : Nat) ≤ 2 :=
  shift_count_le eF (idMat 2) cM 4 3 1 1 2 5 12 1 1 2
    (inertia.oneSplit [⟨8, 1⟩, ⟨1, 2⟩]) (inertia.oneSplit [⟨1, 4⟩, ⟨1, 7⟩])
    (inertia.oneSplit [⟨3, 1⟩, ⟨2, 1⟩]) (inertia.oneSplit [⟨11, 1⟩, ⟨6, 1⟩])
    sGap eFsplit eFpsd sleScaled sleUp sleLo

/-! The comparison's lower side (`shift_count_scale`): at the same
level the cofactor's scaling `2·(sd·Q(σ)) = diag(18, 10)` reads
`diag(7, -1)` at count one while `6·(td·Q(σ′)) = diag(48, 30)` reads
`diag(37, 19)` at count nought, their difference the gap's copy of
the cap's form `10·S_θ = diag(30, 20)` positive semidefinite. -/

private theorem sscUp : countAtPair
    (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cM 4 3 1))
    (idMat 2) 12 1 1 (inertia.oneSplit [⟨8, 1⟩, ⟨1, 2⟩]) := by decide +kernel
private theorem sscLo : countAtPair
    (matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cM 4 1 2))
    (idMat 2) 12 1 0 (inertia.oneSplit [⟨38, 1⟩, ⟨20, 1⟩]) := by decide +kernel
private theorem sthSplit : splitRead (stheta (idMat 2) cM 4)
    (inertia.oneSplit [⟨4, 1⟩, ⟨3, 1⟩]) := by decide +kernel
private theorem sthPsd : psdAt (inertia.oneSplit [⟨4, 1⟩, ⟨3, 1⟩]) := by decide +kernel
private theorem sscScaled : splitRead
    (matScale (1 * 2 * 5) (stheta (idMat 2) cM 4))
    (inertia.oneSplit [⟨31, 1⟩, ⟨21, 1⟩]) := by decide +kernel

theorem pin68 : (0 : Nat) ≤ 1 :=
  shift_count_scale eF (idMat 2) cM 4 3 1 1 2 5 12 1 1 0
    (inertia.oneSplit [⟨8, 1⟩, ⟨1, 2⟩]) (inertia.oneSplit [⟨38, 1⟩, ⟨20, 1⟩])
    (inertia.oneSplit [⟨4, 1⟩, ⟨3, 1⟩]) (inertia.oneSplit [⟨31, 1⟩, ⟨21, 1⟩])
    sGap sthSplit sthPsd sscScaled sscUp sscLo

/-! The scales' order is the gap join's own datum: exchanging the
two scale pairs the join reads `sn·td + g = tn·sd`, at the committed
gap `3·2 + 5 = 1·1` — refused, so the reversed comparison has no
hypothesis set. -/

theorem pin69 : ¬ ((3 : Pos) * 2 + 5 = 1 * 1) := by decide +kernel

/-! The electric form's positive semidefiniteness isolated: at the
indefinite `E = diag(1, -1)` every other hypothesis of the upper
side stands — the gap join, the two certificates, the gap's own
split — and the conclusion fails.  There
`2·(sd·Q(σ)) = diag(12, -2)` reads the site `diag(11, -3)` at count
one against `1·(td·Q(σ′)) = diag(7, 3)` at `diag(6, 2)` and count
nought, the gap's diagonal `5E = diag(5, -5)` refusing the
positive-semidefinite read. -/

private def eInd : Mat := [[⟨2, 1⟩, u], [u, ⟨1, 2⟩]]

theorem pin70 : splitRead eInd (inertia.oneSplit [⟨2, 1⟩, ⟨1, 2⟩]) := by decide +kernel
theorem pin71 : ¬ psdAt (inertia.oneSplit [⟨2, 1⟩, ⟨1, 2⟩]) := by decide +kernel
theorem pin72 : splitRead (matScale 5 eInd) (inertia.oneSplit [⟨6, 1⟩, ⟨1, 6⟩]) := by
  decide +kernel
theorem pin73 : ¬ psdAt (inertia.oneSplit [⟨6, 1⟩, ⟨1, 6⟩]) := by decide +kernel
theorem pin74 : countAtPair (matScale 2 (shiftQ eInd (idMat 2) cM 4 3 1))
    (idMat 2) 2 1 1 (inertia.oneSplit [⟨12, 1⟩, ⟨1, 4⟩]) := by decide +kernel
theorem pin75 : countAtPair (matScale 1 (shiftQ eInd (idMat 2) cM 4 1 2))
    (idMat 2) 2 1 0 (inertia.oneSplit [⟨7, 1⟩, ⟨3, 1⟩]) := by decide +kernel
theorem pin76 : ¬ ((1 : Nat) ≤ 0) := by decide +kernel

/-! The cap's positive semidefiniteness isolated at the lower side:
at `d_θ = 2` over `M = diag(1, 3)` the cap's summand is
`S_θ = diag(1, -1)`, and with the same scales
`2·(sd·Q(σ)) = diag(14, 4)` reads `diag(13, 3)` at count nought
while `6·(td·Q(σ′)) = diag(24, -6)` reads `diag(23, -7)` at count
one — the gap's copy `10·S_θ = diag(10, -10)` refusing the
positive-semidefinite read and the conclusion `n′ ≤ n` failing. -/

theorem pin77 : splitRead (stheta (idMat 2) cE 2) (inertia.oneSplit [⟨2, 1⟩, ⟨1, 2⟩]) := by
  decide +kernel
theorem pin78 : ¬ psdAt (inertia.oneSplit [⟨2, 1⟩, ⟨1, 2⟩]) := by decide +kernel
theorem pin79 : splitRead (matScale (1 * 2 * 5) (stheta (idMat 2) cE 2))
    (inertia.oneSplit [⟨11, 1⟩, ⟨1, 11⟩]) := by decide +kernel
theorem pin80 : ¬ psdAt (inertia.oneSplit [⟨11, 1⟩, ⟨1, 11⟩]) := by decide +kernel
theorem pin81 : countAtPair (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cE 2 3 1))
    (idMat 2) 2 1 0 (inertia.oneSplit [⟨14, 1⟩, ⟨4, 1⟩]) := by decide +kernel
theorem pin82 : countAtPair (matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cE 2 1 2))
    (idMat 2) 2 1 1 (inertia.oneSplit [⟨24, 1⟩, ⟨1, 8⟩]) := by decide +kernel

/-! The corner ray's counts monotone in the scale
(`dual_count_mono`): at the ray points `η = [3 : 1]` and
`η′ = [1 : 2]` with the cross gap `g = 35` at
`en′²ed² + g = en²ed′²`, the upper point's cleared pencil
`4·(9E − M) = diag(68, 28)` reads the site `diag(39, -1)` at count
one over the level `⟨30 : 1⟩` and the lower point's
`1·(E − 4M) = diag(-2, -7)` reads `diag(-31, -36)` at count two,
their difference the gap's electric diagonal `35E = diag(70, 35)`
positive semidefinite. -/

private theorem dmGap :
    (1 : Pos) * 1 * (1 * 1) + 35 = 3 * 3 * (2 * 2) := by
  decide +kernel
private theorem dmUp : countAtPair
    (matScale (1 * (2 * 2)) (cornerPencil eF cM 3 1))
    (idMat 2) 30 1 1 (inertia.oneSplit [⟨40, 1⟩, ⟨1, 2⟩]) := by decide +kernel
private theorem dmLo : countAtPair
    (matScale (1 * (1 * 1)) (cornerPencil eF cM 1 2))
    (idMat 2) 30 1 2 (inertia.oneSplit [⟨1, 32⟩, ⟨1, 37⟩]) := by decide +kernel
private theorem dmScaled : splitRead (matScale (1 * 35) eF)
    (inertia.oneSplit [⟨71, 1⟩, ⟨36, 1⟩]) := by decide +kernel

theorem pin83 : (1 : Nat) ≤ 2 :=
  dual_count_mono eF cM (idMat 2) 1 3 1 1 2 35 30 1 1 2
    (inertia.oneSplit [⟨40, 1⟩, ⟨1, 2⟩]) (inertia.oneSplit [⟨1, 32⟩, ⟨1, 37⟩])
    (inertia.oneSplit [⟨3, 1⟩, ⟨2, 1⟩]) (inertia.oneSplit [⟨71, 1⟩, ⟨36, 1⟩])
    dmGap eFsplit eFpsd dmScaled dmUp dmLo

/-! The ray's order is the gap join's own datum: exchanging the two
ray points the join reads `en²ed′² + g = en′²ed²`, at the committed
gap `3·3·(2·2) + 35 = 1·1·(1·1)` — refused. -/

theorem pin84 : ¬ ((3 : Pos) * 3 * (2 * 2) + 35 = 1 * 1 * (1 * 1)) := by
  decide +kernel

/-! The electric form's positive semidefiniteness isolated at the
ray: at `E = diag(1, -1)` the upper point's pencil
`4·(9E − M) = diag(32, -44)` reads `diag(42, -34)` at count one over
the level `⟨1 : 11⟩` while the lower point's `E − 4M = diag(-3, -9)`
reads `diag(7, 1)` at count nought — the gap's diagonal
`35E = diag(35, -35)` refusing the positive-semidefinite read and
the monotone conclusion failing. -/

theorem pin85 : countAtPair (matScale (1 * (2 * 2)) (cornerPencil eInd cM 3 1))
    (idMat 2) 1 11 1 (inertia.oneSplit [⟨43, 1⟩, ⟨1, 35⟩]) := by decide +kernel
theorem pin86 : countAtPair (matScale (1 * (1 * 1)) (cornerPencil eInd cM 1 2))
    (idMat 2) 1 11 0 (inertia.oneSplit [⟨8, 1⟩, ⟨2, 1⟩]) := by decide +kernel
theorem pin87 : splitRead (matScale (1 * 35) eInd) (inertia.oneSplit [⟨36, 1⟩, ⟨1, 36⟩]) := by
  decide +kernel
theorem pin88 : ¬ psdAt (inertia.oneSplit [⟨36, 1⟩, ⟨1, 36⟩]) := by decide +kernel

/-! `lem:corner`'s cutoff at the scale.
The scale key stands at `η = [2 : 3]`, `ϑ = [1 : 2]`, `d_ϑ = 3` and
the window's top `⟨4 : 1⟩`, where the dimension fold is `135`, the
clearance `18` and the step `32`: the key reads `4`, its own
comparison decided beside the `scaleKey_ge` route, the comparison
refused at `3` — the minimality's own witness — with the
`scaleKey_least` route at `4`, and the two positivity binders
refused at the vacant scale numerator and the vacant level
denominator, each with the co-binder decided true and the
conclusion failing beside it.  The seed floor's window clearing
runs at the same data with the cutoff `5` and the level
`⟨3 : 0⟩` below the top, the route beside its decided anchor, and
each of the three binders refused at a fixture where the
conclusion fails with the other two decided true — the key's
comparison at a vacant step multiple, the Casimir below the key,
and a level beyond the window's top.  The rate composition runs at
the drift battery's own data (`p = 0`, the counts one, `(a, b, c)
= (1, 1, 2)`, `g = 69` against `C_g = 35` and the gap `4`), the
route beside its decided conclusion, with the four binders refused
one at a time at fixtures whose conclusion fails: the margin
oversized at `10⁶`, the bracket's upper side at the level `3`, the
bracket's lower side at the margin `10⁶` against the level one,
and the cap's atom mistied at `17`. -/

/-! The scale key at the fixture: the dimension fold `135` against
the clearance `18` and the step `32`. -/

theorem pin379 : ((9 * (3 * 2 + 4 * 2 + 1) - 1 * 9 * 2
    + (4 * 2 * 2 * 2 - 1)) / (4 * 2 * 2 * 2) : Nat) = 4 := by
  decide +kernel

theorem pin380 : scaleKey 2 3 1 2 3 4 1 = 4 := by decide +kernel

theorem pin381 : (9 * (3 * 2 + 4 * 2 + 1) : Nat) ≤ 4 * 2 * 2 * 2 * 4 + 1 * 9 * 2
    ∧ ¬ ((9 * (3 * 2 + 4 * 2 + 1) : Nat)
      ≤ 4 * 2 * 2 * 2 * 3 + 1 * 9 * 2) := by decide +kernel

theorem pin382 : (3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * scaleKey 2 3 1 2 3 4 1 + 1 * (3 * 3) * 2 := by
  decide +kernel

theorem pin383 : (3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * scaleKey 2 3 1 2 3 4 1 + 1 * (3 * 3) * 2 :=
  scaleKey_ge 2 3 1 2 3 4 1 (by decide +kernel) (by decide +kernel)

theorem pin384 : ¬ ((3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * 3 + 1 * (3 * 3) * 2) := by decide +kernel

theorem pin385 : scaleKey 2 3 1 2 3 4 1 ≤ 4 :=
  scaleKey_least 2 3 1 2 3 4 1 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The key's two positivity binders, each refused at a vacant
member with its co-binder decided true. -/

theorem pin386 : (0 : Nat) < 2 := by decide +kernel

theorem pin387 : ¬ ((3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
    ≤ 4 * 0 * 0 * 2 * scaleKey 0 3 1 2 3 4 1 + 1 * (3 * 3) * 2) := by
  decide +kernel

theorem pin388 : ¬ ((3 : Nat) * 3 * (3 * 0 + 4 * 0 + 1)
    ≤ 4 * 2 * 2 * 0 * scaleKey 2 3 1 0 3 4 1 + 1 * (3 * 3) * 0) := by
  decide +kernel

/-! The seed floor's window clearing at the Casimir `5` and the
level `⟨3 : 0⟩`, the route beside its decided anchor. -/

theorem pin389 : (3 : Nat) * 3 * (3 * 2 + 3 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * 5 + 0 * (3 * 3) * 2 := by decide +kernel

theorem pin390 : (3 : Nat) * 3 * (3 * 2 + 3 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * 5 + 0 * (3 * 3) * 2 :=
  seedClears 2 3 1 2 3 4 1 3 0 5 4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The clearing's three binders, each refused where the
conclusion fails with the other two decided true.  The key's
comparison and the Casimir binder are refused at the vacant
Casimir `0`, where the routed level's own conclusion fails: the
first at the vacant step multiple `L = 0` with the Casimir read
`0 ≤ 0`, the second at the key `L = 4` — whose comparison holds —
against the Casimir below it.  The level binder is refused at the
level `⟨20 : 0⟩` beyond the window's top, at the key and the
Casimir `4`. -/

theorem pin391 : ¬ ((3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * 0 + 1 * (3 * 3) * 2) := by decide +kernel

theorem pin392 : (0 : Nat) ≤ 0 ∧ 3 + 1 ≤ 4 + 0 := by decide +kernel

theorem pin393 : ¬ ((3 : Nat) * 3 * (3 * 2 + 3 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * 0 + 0 * (3 * 3) * 2) := by decide +kernel

theorem pin394 : ¬ ((4 : Nat) ≤ 0) := by decide +kernel

theorem pin395 : ((3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
      ≤ 4 * 2 * 2 * 2 * 4 + 1 * (3 * 3) * 2)
    ∧ (3 : Nat) + 1 ≤ 4 + 0 := by decide +kernel

theorem pin396 : ¬ ((20 : Nat) + 1 ≤ 4 + 0) := by decide +kernel

theorem pin397 : ((3 : Nat) * 3 * (3 * 2 + 4 * 2 + 1)
      ≤ 4 * 2 * 2 * 2 * 4 + 1 * (3 * 3) * 2)
    ∧ (4 : Nat) ≤ 4 := by decide +kernel

theorem pin398 : ¬ ((3 : Nat) * 3 * (3 * 2 + 20 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * 4 + 0 * (3 * 3) * 2) := by decide +kernel

/-! The key's clearing at its own cutoff: the seed floor at the toy's
key `4` clears the level `⟨3 : 0⟩`, decided beside the theorem
route; at the vacant key the floor drops to the vacant read refused
above. -/

theorem pin399 : scaleKey 2 3 1 2 3 4 1 = 4 := by decide +kernel

theorem pin400 : (3 : Nat) * 3 * (3 * 2 + 3 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * scaleKey 2 3 1 2 3 4 1
      + 0 * (3 * 3) * 2 := by decide +kernel

theorem pin401 : (3 : Nat) * 3 * (3 * 2 + 3 * 2 + 1)
    ≤ 4 * 2 * 2 * 2 * scaleKey 2 3 1 2 3 4 1
      + 0 * (3 * 3) * 2 :=
  keyClears 2 3 1 2 3 4 1 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The height section at the extent toy: the presentation's height
variable substituted first, its scale evaluation the corner site
again at the two scale points `[2 : 3]` and `[1 : 1]` and the two
heights `⟨2 : 1⟩`, `⟨1 : 3⟩` — the theorem route beside each decided
anchor.  Beside them sits the cutoff display's own bracket: the
cleared comparison `32η² − 13` sits below the sum's unit at
`η = 3/5` and above it at `η = 7/10`, its root inside the
straddle's own segment. -/

theorem pin417 : elim.matOneValue
    (cellcount.evalPC (corner.cornerAtHeight fE fM pG 2 1)
      (BPair.ofPos 2) 3 2)
    (corner.cornerSite fE fM pG 2 3 2 1) := by decide +kernel

theorem pin418 : elim.matOneValue
    (cellcount.evalPC (corner.cornerAtHeight fE fM pG 2 1)
      (BPair.ofPos 2) 3 2)
    (corner.cornerSite fE fM pG 2 3 2 1) :=
  corner.cornerAtHeight_eval fE fM pG 2 3 2 1

theorem pin419 : elim.matOneValue
    (cellcount.evalPC (corner.cornerAtHeight fE fM pG 1 3)
      (BPair.ofPos 1) 1 2)
    (corner.cornerSite fE fM pG 1 1 1 3) := by decide +kernel

theorem pin420 : elim.matOneValue
    (cellcount.evalPC (corner.cornerAtHeight fE fM pG 1 3)
      (BPair.ofPos 1) 1 2)
    (corner.cornerSite fE fM pG 1 1 1 3) :=
  corner.cornerAtHeight_eval fE fM pG 1 1 1 3

theorem pin421 : poly.evalClear [⟨1, 14⟩, u, ⟨33, 1⟩] (BPair.ofPos 3) 5 2 < u
    ∧ u < poly.evalClear [⟨1, 14⟩, u, ⟨33, 1⟩] (BPair.ofPos 7) 10 2 := by
  decide +kernel


/-! `lem:corner`'s height section at the extent toy, and the record
it emits.  Over `E = [[1, 1], [1, 2]]`, `M = 4E − I` and the unit
gram the height `η′ = ⟨2 : 1⟩` sections the corner presentation to
the scale pencil `[[η² − η − 3, η² − 4], [η² − 4, 2η² − η − 7]]`,
whose determinant is `η⁴ − 3η³ − 4η² + 10η + 5` — squarefree, with
positive roots in `(2, 3)` and `(3, 4)` and two negative roots.  The
record's clearing weight is `4` and its three samples are
`η = 1/4, 1, 3`, the balance-pair numerators `1, 4, 12` over that
weight, each off the roots; their evaluated sites
`[[−51, −63], [−63, −114]]`, `[[−48, −48], [−48, −96]]` and
`[[48, 80], [80, 128]]` split at their own upper-triangular
congruences with the counts `2, 2, 1`.  The divisor's certificate is
a content-reduced Bézout pair at the determinant against its
derivative — the gcd the constant one, so the squarefree part is the
determinant itself and the content-reduced Bézout combination
`(689 + 868y − 800y²)D + (470 − 747y − 367y² + 200y³)D′ = 8145`
serves both the descent and the part — and the cleared-variable
monic is the determinant's own below-top list, the leading
magnitude one.  The shared Hermite pairing
`[[4, 3, 17, 33], [3, 17, 33, 117], [17, 33, 117, 298],
[33, 117, 298, 947]]` is positive definite, its count nought.  The
first boundary is a comparison at the cutoff display
`32η² − 13` — the scale key's cleared comparison at `d_ϑ = 3`, the
top level `⟨4 : 1⟩`, the clearance `[1 : 2]` and the key `4` — whose
root `√(13/32)` sits in the straddle `[1/4, 1]` while the record
divisor's own count is nought across it; the second is a jump at
the divisor's root in `(2, 3)`, which is the only root in the
straddle `[1, 3]`.  The whole record's read is decided, with the
truncated boundary list, a forged trailing count, the comparison
retagged as a jump and the jump retagged as the cutoff's
comparison each refused beside it. -/

private def xrS : split.PMat := corner.cornerAtHeight fE fM pG 2 1

private def xrD : poly.Poly :=
  [⟨6, 1⟩, ⟨11, 1⟩, ⟨1, 5⟩, ⟨1, 4⟩, ⟨2, 1⟩]

private def xrDp : poly.Poly := [⟨11, 1⟩, ⟨1, 9⟩, ⟨1, 10⟩, ⟨5, 1⟩]

private def xrU : poly.Poly := [⟨690, 1⟩, ⟨869, 1⟩, ⟨1, 801⟩]

private def xrV : poly.Poly :=
  [⟨471, 1⟩, ⟨1, 748⟩, ⟨1, 368⟩, ⟨201, 1⟩]

private def xrCt : cellcount.DivCert :=
  ⟨[], xrD, xrDp, xrU, xrV, xrD, xrU, xrV, 1, 1, 1, 1,
   ⟨8146, 1⟩, ⟨8146, 1⟩⟩

theorem pin422 : poly.oneValue (split.pminor xrS) xrD := by decide +kernel

/-! The section's minor is the presentation's own at the height
substitution: the record carrier's determinant reads `χ` at the
height point, the theorem route beside the decided anchor, and a
forged height point refuses. -/

theorem pin423 : poly.oneValue (split.pminor xrS)
    (poly.pevalC xChi [⟨2, 1⟩] 1 1) := by decide +kernel

theorem pin424 : poly.oneValue (split.pminor xrS)
    (poly.pevalC xChi [⟨2, 1⟩] 1 1) :=
  corner.cornerAtHeight_minor (o := 2) fE fM pG 2 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin425 : ¬ poly.oneValue (split.pminor xrS)
    (poly.pevalC xChi [⟨1, 2⟩] 1 1) := by decide +kernel

theorem pin426 : poly.oneValue (poly.deriv xrD) xrDp := by decide +kernel

theorem pin427 : cellcount.divRead (split.pminor xrS) xrCt := by decide +kernel

theorem pin428 : poly.oneValue (deckfactor.clearVarBT xrCt.sq)
    [⟨6, 1⟩, ⟨11, 1⟩, ⟨1, 5⟩, ⟨1, 4⟩] := by decide +kernel

theorem pin429 : ¬ (poly.evalClear xrD ⟨2, 1⟩ 4 4).oneValue u := by
  decide +kernel
theorem pin430 : ¬ (poly.evalClear xrD ⟨5, 1⟩ 4 4).oneValue u := by
  decide +kernel
theorem pin431 : ¬ (poly.evalClear xrD ⟨13, 1⟩ 4 4).oneValue u := by
  decide +kernel

private def xrC1 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 22⟩], [u, ⟨18, 1⟩]], rfl⟩,
   ⟨[[⟨18, 1⟩, ⟨22, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 52⟩, .one ⟨1, 10456⟩], 0, rfl⟩

private def xrC2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 49⟩, .one ⟨1, 49⟩], 0, rfl⟩

private def xrC3 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 6⟩], [u, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨4, 1⟩, ⟨6, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨49, 1⟩, .one ⟨1, 49⟩], 0, rfl⟩

private def xrHD : Split 4 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 4⟩, ⟨1, 191⟩, ⟨471, 1⟩],
     [u, ⟨5, 1⟩, ⟨1, 82⟩, ⟨1, 748⟩],
     [u, u, ⟨60, 1⟩, ⟨1, 368⟩],
     [u, u, u, ⟨201, 1⟩]], rfl⟩,
   ⟨[[⟨47201, 1⟩, ⟨35401, 1⟩, ⟨200601, 1⟩, ⟨389401, 1⟩],
     [u, ⟨11801, 1⟩, ⟨16201, 1⟩, ⟨73801, 1⟩],
     [u, u, ⟨801, 1⟩, ⟨1469, 1⟩],
     [u, u, u, ⟨237, 1⟩]], rfl⟩,
   [.one ⟨5, 1⟩, .one ⟨237, 1⟩, .one ⟨59001, 1⟩,
    .one ⟨1629001, 1⟩], 0, rfl⟩

private def xrB1 : Split 4 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 51⟩, ⟨1, 3521⟩, ⟨53171, 1⟩],
     [u, ⟨58, 1⟩, ⟨1, 1025⟩, ⟨1, 39034⟩],
     [u, u, ⟨788, 1⟩, ⟨1, 24501⟩],
     [u, u, u, ⟨10565, 1⟩]], rfl⟩,
   ⟨[[⟨473890477, 1⟩, ⟨415693401, 1⟩, ⟨2660437761, 1⟩,
      ⟨5320875521, 1⟩],
     [u, ⟨8313869, 1⟩, ⟨10817537, 1⟩, ⟨55806972, 1⟩],
     [u, u, ⟨602149, 1⟩, ⟨1396501, 1⟩],
     [u, u, u, ⟨44860, 1⟩]], rfl⟩,
   [.one ⟨229, 1⟩, .one ⟨3588721, 1⟩, .one ⟨374124061, 1⟩,
    .one ⟨127000619281, 1⟩], 0, rfl⟩

private def xrB2 : Split 4 :=
  ⟨⟨[[⟨2, 1⟩, ⟨27, 1⟩, ⟨1, 551⟩, ⟨26, 1⟩],
     [u, ⟨18, 1⟩, ⟨1, 272⟩, ⟨1, 913⟩],
     [u, u, ⟨65, 1⟩, ⟨149, 1⟩],
     [u, u, u, ⟨416, 1⟩]], rfl⟩,
   ⟨[[⟨451521, 1⟩, ⟨1, 690561⟩, ⟨956161, 1⟩, ⟨1, 1885761⟩],
     [u, ⟨26561, 1⟩, ⟨112466, 1⟩, ⟨18261, 1⟩],
     [u, u, ⟨7056, 1⟩, ⟨1, 2517⟩],
     [u, u, u, ⟨1089, 1⟩]], rfl⟩,
   [.one ⟨273, 1⟩, .one ⟨1, 17409⟩, .one ⟨6374401, 1⟩,
    .one ⟨162248401, 1⟩], 0, rfl⟩

private def xrF : poly.Poly := [⟨1, 14⟩, u, ⟨33, 1⟩]

private def xrFH : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, u], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, u], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨833, 1⟩], 0, rfl⟩

private def xrFB : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨532481, 1⟩], [u, ⟨21505, 1⟩]], rfl⟩,
   ⟨[[⟨21505, 1⟩, ⟨1, 532481⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨21505, 1⟩, .one ⟨1, 1960463592062977⟩], 0, rfl⟩

private def xrCells : List (BPair × Nat × Split 2) :=
  [(⟨2, 1⟩, 2, xrC1), (⟨5, 1⟩, 2, xrC2), (⟨13, 1⟩, 1, xrC3)]

private def xrBnds : List (decimation.Bound 4) :=
  [.cmp xrF xrB1 ⟨2, xrFH, xrFB⟩, .jump xrB2]

private def xrRec : decimation.DivRecord 2 4 :=
  ⟨xrS, 2, 4, xrCt, xrHD, xrCells, xrBnds⟩

theorem pin432 : decimation.recordRead xrRec := by decide +kernel

theorem pin433 : xrRec.cells.map (fun x => x.2.1) = [2, 2, 1] := by
  decide +kernel

/-! The record's shape refuses at the truncating fold's own law:
the boundary list dropped to one against three cells, the surviving
boundary reading its binding while the count tie parts. -/

theorem pin434 : ¬ decimation.recordRead
    (⟨xrS, 2, 4, xrCt, xrHD, xrCells, xrBnds.take 1⟩ :
      decimation.DivRecord 2 4) := by decide +kernel

/-! The count forge isolates the pointwise read: the trailing
cell's count moved to two at its own split, whose reversal fold
reads one, both boundaries beside it at their bindings. -/

theorem pin435 : ¬ decimation.recordRead
    (⟨xrS, 2, 4, xrCt, xrHD,
      xrCells.take 2 ++ [(⟨13, 1⟩, 2, xrC3)], xrBnds⟩ :
      decimation.DivRecord 2 4) := by decide +kernel

/-! The tag forgeries isolate the two bindings: the cutoff
comparison retagged as a jump demands one root of the divisor's own
cleared monic between `1/4` and `1`, where the count is nought; the
divisor's jump retagged as the cutoff's comparison demands the
divisor's count nought across `[1, 3]`, where its root sits. -/

theorem pin436 : ¬ decimation.recordRead
    (⟨xrS, 2, 4, xrCt, xrHD, xrCells, [.jump xrB1, .jump xrB2]⟩ :
      decimation.DivRecord 2 4) := by decide +kernel

theorem pin437 : ¬ decimation.recordRead
    (⟨xrS, 2, 4, xrCt, xrHD, xrCells,
      [.cmp xrF xrB1 ⟨2, xrFH, xrFB⟩,
       .cmp xrF xrB2 ⟨2, xrFH, xrFB⟩]⟩ :
      decimation.DivRecord 2 4) := by decide +kernel

/-! The divisor conjunct isolates at a forged Bézout constant: the
squarefree part is kept, so every boundary still reads its binding
at the divisor's own monic while the certificate's descent
parts. -/

theorem pin438 : ¬ decimation.recordRead
    (⟨xrS, 2, 4, ⟨[], xrD, xrDp, xrU, xrV, xrD, xrU, xrV,
      1, 1, 1, 1, ⟨8146, 1⟩, ⟨8147, 1⟩⟩, xrHD, xrCells, xrBnds⟩ :
      decimation.DivRecord 2 4) := by decide +kernel

theorem pin439 : ((List.zip (List.zip xrCells (xrCells.drop 1)) xrBnds).all
      (fun y => decide
        (decimation.boundRead xrD xrHD 4 y.1.1.1 y.1.2.1 y.2)))
    = true := by decide +kernel

/-! The comparison's own count isolates at a rootless display: the
constant display reads no root over the straddle `[1/4, 1]` where
the binding demands one, the divisor's count nought beside it at
its binding. -/

private def xrNil : Split 0 := ⟨⟨[], rfl⟩, ⟨[], rfl⟩, [], 0, rfl⟩

theorem pin440 : ¬ decimation.recordRead
    (⟨xrS, 2, 4, xrCt, xrHD, xrCells,
      [.cmp [⟨2, 1⟩] xrB1 ⟨0, xrNil, xrNil⟩, .jump xrB2]⟩ :
      decimation.DivRecord 2 4) := by decide +kernel

theorem pin441 : hermitesign.segCountRead (deckfactor.clearVarBT xrD)
    (deckfactor.clearAt xrD ⟨2, 1⟩)
    (deckfactor.clearAt xrD ⟨5, 1⟩) 4 0 xrHD xrB1 := by
  decide +kernel

/-! The emitted record's two vacant families at the toy.  The deck
family's walk datum is the corner base `c₁ = 2`: the symbol's
cross-multiplied witness, the crossing read at the pair `[9 : 4]`
and the margin's square against that pair each decide there, and
the family's t-direction display is that crossing's constant
numerator — the display's one member read back against the
crossing pair — whose cleared-variable list is empty, the segment
count nought over the record's whole range `[1/4, 3]` at the
record's clearing.  The tension family drops at the toy's
unit-class data: at a matched stencil the tension reads the
electric member alone (`chargedcell.tension_free`'s route beside
its decided anchor), its side display that member's constant
numerator — the display's one member read back against the
tension's value — again a vacant root list over the record's
range. -/

private def spNil : Split 0 := ⟨⟨[], rfl⟩, ⟨[], rfl⟩, [], 0, rfl⟩

theorem pin442 : channeldiv.symbolRead 2 := by decide +kernel
theorem pin443 : channeldiv.crossingRead 2 := by decide +kernel
theorem pin444 : channeldiv.marginRead 2 := by decide +kernel

theorem pin445 : (channeldiv.crossPair 2).oneValue
    ⟨ground.BPair.ofNat 9, 4⟩ := by decide +kernel

private def xkDeck : poly.Poly := [ground.BPair.ofNat 9]

theorem pin446 : (channeldiv.crossPair 2).oneValue
    ⟨ground.getAt u xkDeck 0, 4⟩ := by decide +kernel

theorem pin447 : deckfactor.clearVarBT xkDeck = [] := by decide +kernel

theorem pin448 : hermitesign.segCountRead (deckfactor.clearVarBT xkDeck)
    (deckfactor.clearAt xkDeck ⟨2, 1⟩)
    (deckfactor.clearAt xkDeck ⟨13, 1⟩) 4 0 spNil spNil := by
  decide +kernel

theorem pin449 : ¬ hermitesign.segCountRead (deckfactor.clearVarBT xkDeck)
    (deckfactor.clearAt xkDeck ⟨2, 1⟩)
    (deckfactor.clearAt xkDeck ⟨13, 1⟩) 4 1 spNil spNil := by
  decide +kernel

theorem pin450 : ¬ hermitesign.segCountRead (deckfactor.clearVarBT xkDeck)
    (deckfactor.clearAt xkDeck ⟨13, 1⟩)
    (deckfactor.clearAt xkDeck ⟨2, 1⟩) 4 0 spNil spNil := by
  decide +kernel

private def xkVp : ground.Pair := ⟨3, 2⟩
private def xkW : ground.Pair := ⟨2, 1⟩
private def xkAtoms : List (Pos × Pos) := [(2, 3), (1, 2)]

theorem pin451 : (chargedcell.tension xkVp xkW xkAtoms xkAtoms).oneValue
    (CPair.ofPair xkVp .one) :=
  chargedcell.tension_free xkVp xkW xkAtoms

theorem pin452 : (chargedcell.tension xkVp xkW xkAtoms xkAtoms).oneValue
    (CPair.ofPair xkVp .one) := by decide +kernel

private def xkTen : poly.Poly := [BPair.ofPos 3]

theorem pin453 : (chargedcell.tension xkVp xkW xkAtoms xkAtoms).oneValue
    ⟨ground.getAt u xkTen 0, 2⟩ := by decide +kernel

theorem pin454 : hermitesign.segCountRead (deckfactor.clearVarBT xkTen)
    (deckfactor.clearAt xkTen ⟨2, 1⟩)
    (deckfactor.clearAt xkTen ⟨13, 1⟩) 4 0 spNil spNil := by
  decide +kernel

theorem pin455 : ¬ hermitesign.segCountRead (deckfactor.clearVarBT xkTen)
    (deckfactor.clearAt xkTen ⟨2, 1⟩)
    (deckfactor.clearAt xkTen ⟨13, 1⟩) 4 1 spNil spNil := by
  decide +kernel

/-! The t-section rides `deckfactor.bandClear`: a constant
t-display is vacant across the whole crossing segment, while the
display `t` itself carries the root nought strictly inside it —
its cleared monic's Hermite pairing `[[1]]` and bracket pencil
`[[−4]]` each read their splits, so the band's stated vacancy is
the one conjunct that parts. -/

theorem pin456 : deckfactor.bandClear xkDeck spNil spNil := by decide +kernel

theorem pin457 : splitRead (hermitesign.hermite
    (deckfactor.clearVarBT [u, ⟨2, 1⟩]) poly.one) (inertia.oneSplit [⟨2, 1⟩]) := by
  decide +kernel

theorem pin458 : splitRead (hermitesign.pencilB
      (deckfactor.clearVarBT [u, ⟨2, 1⟩]) poly.one
      (deckfactor.clearAt [u, ⟨2, 1⟩] ⟨1, 3⟩)
      (deckfactor.clearAt [u, ⟨2, 1⟩] ⟨3, 1⟩) 1)
    (inertia.oneSplit [⟨1, 5⟩]) := by decide +kernel

theorem pin459 : ¬ deckfactor.bandClear [u, ⟨2, 1⟩] (inertia.oneSplit [⟨2, 1⟩])
    (inertia.oneSplit [⟨1, 5⟩]) := by decide +kernel

/-! The rank direction at the emitted record's deck base: the deck
base is the member-key count, one value at every cleared residue —
two at `d = 3` and at `d = 5` through `xfusion.c1_eq`, one at
`d = 2` through `xfusion.c1_one` — and the record's walk datum
reads that count back, the chord at the base the chord at two, the
base the deck family's own `c₁ = 2` above. -/

theorem pin460 : xfusion.c1 3 = 2 := xfusion.c1_eq 3 (by decide +kernel)
theorem pin461 : xfusion.c1 5 = 2 := xfusion.c1_eq 5 (by decide +kernel)
theorem pin462 : xfusion.c1 2 = 1 := xfusion.c1_one

theorem pin463 : ground.posOfSucc (xfusion.c1 3 - 1) = 2 := by decide +kernel
theorem pin464 : ground.posOfSucc (xfusion.c1 5 - 1) = 2 := by decide +kernel

theorem pin465 : (channeldiv.chord (ground.posOfSucc (xfusion.c1 3 - 1))).oneValue
    (channeldiv.chord 2) := by decide +kernel
theorem pin466 : (channeldiv.chord (ground.posOfSucc (xfusion.c1 5 - 1))).oneValue
    (channeldiv.chord 2) := by decide +kernel

theorem pin467 : channeldiv.chord (ground.posOfSucc (xfusion.c1 3 - 1))
    = channeldiv.chord 2 := rfl

end corner
