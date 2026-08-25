import MassGap.Corner
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

The grade-key block reads `lem:corner`'s key `G(λ) = λ(θ^∨)` at the
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

The per-key counts block closes the module: the key list's
identification over the box `[4,4,4]` at `B3`, its length cap, the
gap product's factors against the `θ` factor, the `θ` factor's own
read at `B3` and `C3`, the member dimension's cap over the box
`[2,2,2]` and the two strict per-key caps at `B2` — each beside
its theorem route — with the naming, length, shape,
positive-list and length-denominator binders refused at their own
tables, and the gap comparison's shape and dominance-join binders
refused at a length family past the rank, at the vacant rank, and
at a fold beyond the top.

The Rayleigh-close block closes the file at the dimension-weighted
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
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct corner

private def u : BPair := BPair.unit

private def cE : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

private def cM : Mat := [[⟨2, 1⟩, u], [u, ⟨3, 1⟩]]

private def spLt (a b : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one a, .one b], 0, rfl⟩

/-! The corner anchor: at the scale `[2 : 1]` and the height
`⟨3 : 1⟩` the cleared display reads `diag(-1, 6)`, one negative
block, the corner count one. -/

private theorem cAnchor :
    cornerCount cE cM (idMat 2) 2 1 3 1 1 (spLt ⟨1, 2⟩ ⟨7, 1⟩) := by
  decide +kernel

private theorem cEsq : elim.sqAt cE 2 := by decide +kernel

private theorem cMsq : elim.sqAt cM 2 := by decide +kernel

/-! The count's refusal: the same certificate's reversal fold is
one, so the count zero is refused. -/

example : ¬ cornerCount cE cM (idMat 2) 2 1 3 1 0 (spLt ⟨1, 2⟩ ⟨7, 1⟩) := by
  decide +kernel

/-! The height's two members sit on the two sides they are
cross-added onto: exchanging `hp` and `hm` moves the display to
`4E + 6G − M − 2G = diag(7, 14)` and refuses the anchor's
certificate. -/

example : ¬ cornerCount cE cM (idMat 2) 2 1 1 3 1
    (spLt ⟨1, 2⟩ ⟨7, 1⟩) := by decide +kernel

/-! The forged-shape refusal: the corner data's first member off the
gram's order — a two-by-three `E` — refuses the order conjunct at
otherwise-valid data, while the seam pencil's count stands at the
truncated assembly: the order conjunct is the refusal's own. -/

private def cEwide : Mat := [[⟨2, 1⟩, u, u], [u, ⟨4, 1⟩, u]]

example : ¬ elim.sqAt cEwide 2 := by decide +kernel
example : ¬ cornerCount cEwide cM (idMat 2) 2 1 3 1 1
    (spLt ⟨1, 2⟩ ⟨7, 1⟩) := by decide +kernel
example : countAtPair (cornerPencil cEwide cM 2 1) (idMat 2)
    (2 * 1 * 3) (2 * 1 * 1) 1 (spLt ⟨1, 2⟩ ⟨7, 1⟩) := by decide +kernel

/-! The substitution's route (`corner_dual`): the corner count is
the seam pencil's count at the level members `(2·1·3, 2·1·1)`, the
iff consumed in both directions at the anchor's data. -/

example : countAtPair (cornerPencil cE cM 2 1) (idMat 2)
    (2 * 1 * 3) (2 * 1 * 1) 1 (spLt ⟨1, 2⟩ ⟨7, 1⟩) :=
  (corner_dual cE cM (idMat 2) 2 1 3 1 1 (spLt ⟨1, 2⟩ ⟨7, 1⟩)
    cEsq cMsq).mp cAnchor

example : cornerCount cE cM (idMat 2) 2 1 3 1 1 (spLt ⟨1, 2⟩ ⟨7, 1⟩) :=
  (corner_dual cE cM (idMat 2) 2 1 3 1 1 (spLt ⟨1, 2⟩ ⟨7, 1⟩)
    cEsq cMsq).mpr (by decide +kernel)

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

example : matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cM 4 1 2)
    = matAdd (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cM 4 3 1))
        (matScale (1 * 2 * 5) (stheta (idMat 2) cM 4)) := by
  decide +kernel

example : matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cM 4 1 2)
    = matAdd (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cM 4 3 1))
        (matScale (1 * 2 * 5) (stheta (idMat 2) cM 4)) :=
  shiftQ_split eF (idMat 2) cM 4 3 1 1 2 5 sGap

/-! The pencil is a sum of two positive-semidefinite forms
(`shiftQ_psd`): at the fixture `sd·Q(σ) = diag(9, 5)` splits
positive semidefinite from its two summands' own splits,
`3E = diag(6, 3)` and `1·S_θ = diag(3, 2)`. -/

private theorem sQe : splitRead (matScale 3 eF)
    (spLt ⟨7, 1⟩ ⟨4, 1⟩) := by decide +kernel
private theorem sQePsd : psdAt (spLt ⟨7, 1⟩ ⟨4, 1⟩) := by decide +kernel
private theorem sQs : splitRead (matScale 1 (stheta (idMat 2) cM 4))
    (spLt ⟨4, 1⟩ ⟨3, 1⟩) := by decide +kernel
private theorem sQq : splitRead (shiftQ eF (idMat 2) cM 4 3 1)
    (spLt ⟨10, 1⟩ ⟨6, 1⟩) := by decide +kernel

example : psdAt (spLt ⟨10, 1⟩ ⟨6, 1⟩) := by decide +kernel
example : psdAt (spLt ⟨10, 1⟩ ⟨6, 1⟩) :=
  shiftQ_psd eF (idMat 2) cM 4 3 1
    (spLt ⟨7, 1⟩ ⟨4, 1⟩) (spLt ⟨4, 1⟩ ⟨3, 1⟩) (spLt ⟨10, 1⟩ ⟨6, 1⟩)
    sQe sQePsd sQs (by decide +kernel) sQq

/-! Two equal scales read one pencil outright (`shiftQ_eq`): at the
crossed tie `4·1 = 2·2` the two cleared pencils are one matrix,
`diag(14, 8)`, decided at the literal data and through the
theorem. -/

example : matScale 2 (shiftQ eF (idMat 2) cM 4 2 1)
    = matScale 1 (shiftQ eF (idMat 2) cM 4 4 2) := by decide +kernel
example : matScale 2 (shiftQ eF (idMat 2) cM 4 2 1)
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
    (idMat 2) 12 1 1 (spLt ⟨8, 1⟩ ⟨1, 2⟩) := by decide +kernel
private theorem sleLo : countAtPair
    (matScale 1 (shiftQ eF (idMat 2) cM 4 1 2))
    (idMat 2) 12 1 2 (spLt ⟨1, 4⟩ ⟨1, 7⟩) := by decide +kernel
private theorem eFsplit : splitRead eF (spLt ⟨3, 1⟩ ⟨2, 1⟩) := by
  decide +kernel
private theorem eFpsd : psdAt (spLt ⟨3, 1⟩ ⟨2, 1⟩) := by decide +kernel
private theorem sleScaled : splitRead (matScale 5 eF)
    (spLt ⟨11, 1⟩ ⟨6, 1⟩) := by decide +kernel

example : (1 : Nat) ≤ 2 :=
  shift_count_le eF (idMat 2) cM 4 3 1 1 2 5 12 1 1 2
    (spLt ⟨8, 1⟩ ⟨1, 2⟩) (spLt ⟨1, 4⟩ ⟨1, 7⟩)
    (spLt ⟨3, 1⟩ ⟨2, 1⟩) (spLt ⟨11, 1⟩ ⟨6, 1⟩)
    sGap eFsplit eFpsd sleScaled sleUp sleLo

/-! The comparison's lower side (`shift_count_scale`): at the same
level the cofactor's scaling `2·(sd·Q(σ)) = diag(18, 10)` reads
`diag(7, -1)` at count one while `6·(td·Q(σ′)) = diag(48, 30)` reads
`diag(37, 19)` at count nought, their difference the gap's copy of
the cap's form `10·S_θ = diag(30, 20)` positive semidefinite. -/

private theorem sscUp : countAtPair
    (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cM 4 3 1))
    (idMat 2) 12 1 1 (spLt ⟨8, 1⟩ ⟨1, 2⟩) := by decide +kernel
private theorem sscLo : countAtPair
    (matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cM 4 1 2))
    (idMat 2) 12 1 0 (spLt ⟨38, 1⟩ ⟨20, 1⟩) := by decide +kernel
private theorem sthSplit : splitRead (stheta (idMat 2) cM 4)
    (spLt ⟨4, 1⟩ ⟨3, 1⟩) := by decide +kernel
private theorem sthPsd : psdAt (spLt ⟨4, 1⟩ ⟨3, 1⟩) := by decide +kernel
private theorem sscScaled : splitRead
    (matScale (1 * 2 * 5) (stheta (idMat 2) cM 4))
    (spLt ⟨31, 1⟩ ⟨21, 1⟩) := by decide +kernel

example : (0 : Nat) ≤ 1 :=
  shift_count_scale eF (idMat 2) cM 4 3 1 1 2 5 12 1 1 0
    (spLt ⟨8, 1⟩ ⟨1, 2⟩) (spLt ⟨38, 1⟩ ⟨20, 1⟩)
    (spLt ⟨4, 1⟩ ⟨3, 1⟩) (spLt ⟨31, 1⟩ ⟨21, 1⟩)
    sGap sthSplit sthPsd sscScaled sscUp sscLo

/-! The scales' order is the gap join's own datum: exchanging the
two scale pairs the join reads `sn·td + g = tn·sd`, at the committed
gap `3·2 + 5 = 1·1` — refused, so the reversed comparison has no
hypothesis set. -/

example : ¬ ((3 : Pos) * 2 + 5 = 1 * 1) := by decide +kernel

/-! The electric form's positive semidefiniteness isolated: at the
indefinite `E = diag(1, -1)` every other hypothesis of the upper
side stands — the gap join, the two certificates, the gap's own
split — and the conclusion fails.  There
`2·(sd·Q(σ)) = diag(12, -2)` reads the site `diag(11, -3)` at count
one against `1·(td·Q(σ′)) = diag(7, 3)` at `diag(6, 2)` and count
nought, the gap's diagonal `5E = diag(5, -5)` refusing the
positive-semidefinite read. -/

private def eInd : Mat := [[⟨2, 1⟩, u], [u, ⟨1, 2⟩]]

example : splitRead eInd (spLt ⟨2, 1⟩ ⟨1, 2⟩) := by decide +kernel
example : ¬ psdAt (spLt ⟨2, 1⟩ ⟨1, 2⟩) := by decide +kernel
example : splitRead (matScale 5 eInd) (spLt ⟨6, 1⟩ ⟨1, 6⟩) := by
  decide +kernel
example : ¬ psdAt (spLt ⟨6, 1⟩ ⟨1, 6⟩) := by decide +kernel
example : countAtPair (matScale 2 (shiftQ eInd (idMat 2) cM 4 3 1))
    (idMat 2) 2 1 1 (spLt ⟨12, 1⟩ ⟨1, 4⟩) := by decide +kernel
example : countAtPair (matScale 1 (shiftQ eInd (idMat 2) cM 4 1 2))
    (idMat 2) 2 1 0 (spLt ⟨7, 1⟩ ⟨3, 1⟩) := by decide +kernel
example : ¬ ((1 : Nat) ≤ 0) := by decide +kernel

/-! The cap's positive semidefiniteness isolated at the lower side:
at `d_θ = 2` over `M = diag(1, 3)` the cap's summand is
`S_θ = diag(1, -1)`, and with the same scales
`2·(sd·Q(σ)) = diag(14, 4)` reads `diag(13, 3)` at count nought
while `6·(td·Q(σ′)) = diag(24, -6)` reads `diag(23, -7)` at count
one — the gap's copy `10·S_θ = diag(10, -10)` refusing the
positive-semidefinite read and the conclusion `n′ ≤ n` failing. -/

example : splitRead (stheta (idMat 2) cE 2) (spLt ⟨2, 1⟩ ⟨1, 2⟩) := by
  decide +kernel
example : ¬ psdAt (spLt ⟨2, 1⟩ ⟨1, 2⟩) := by decide +kernel
example : splitRead (matScale (1 * 2 * 5) (stheta (idMat 2) cE 2))
    (spLt ⟨11, 1⟩ ⟨1, 11⟩) := by decide +kernel
example : ¬ psdAt (spLt ⟨11, 1⟩ ⟨1, 11⟩) := by decide +kernel
example : countAtPair (matScale (1 * 1 * 2) (shiftQ eF (idMat 2) cE 2 3 1))
    (idMat 2) 2 1 0 (spLt ⟨14, 1⟩ ⟨4, 1⟩) := by decide +kernel
example : countAtPair (matScale (3 * 1 * 2) (shiftQ eF (idMat 2) cE 2 1 2))
    (idMat 2) 2 1 1 (spLt ⟨24, 1⟩ ⟨1, 8⟩) := by decide +kernel

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
    (matScale (2 * 2) (cornerPencil eF cM 3 1))
    (idMat 2) 30 1 1 (spLt ⟨40, 1⟩ ⟨1, 2⟩) := by decide +kernel
private theorem dmLo : countAtPair
    (matScale (1 * 1) (cornerPencil eF cM 1 2))
    (idMat 2) 30 1 2 (spLt ⟨1, 32⟩ ⟨1, 37⟩) := by decide +kernel
private theorem dmScaled : splitRead (matScale 35 eF)
    (spLt ⟨71, 1⟩ ⟨36, 1⟩) := by decide +kernel

example : (1 : Nat) ≤ 2 :=
  dual_count_mono eF cM (idMat 2) 3 1 1 2 35 30 1 1 2
    (spLt ⟨40, 1⟩ ⟨1, 2⟩) (spLt ⟨1, 32⟩ ⟨1, 37⟩)
    (spLt ⟨3, 1⟩ ⟨2, 1⟩) (spLt ⟨71, 1⟩ ⟨36, 1⟩)
    dmGap eFsplit eFpsd dmScaled dmUp dmLo

/-! The ray's order is the gap join's own datum: exchanging the two
ray points the join reads `en²ed′² + g = en′²ed²`, at the committed
gap `3·3·(2·2) + 35 = 1·1·(1·1)` — refused. -/

example : ¬ ((3 : Pos) * 3 * (2 * 2) + 35 = 1 * 1 * (1 * 1)) := by
  decide +kernel

/-! The electric form's positive semidefiniteness isolated at the
ray: at `E = diag(1, -1)` the upper point's pencil
`4·(9E − M) = diag(32, -44)` reads `diag(42, -34)` at count one over
the level `⟨1 : 11⟩` while the lower point's `E − 4M = diag(-3, -9)`
reads `diag(7, 1)` at count nought — the gap's diagonal
`35E = diag(35, -35)` refusing the positive-semidefinite read and
the monotone conclusion failing. -/

example : countAtPair (matScale (2 * 2) (cornerPencil eInd cM 3 1))
    (idMat 2) 1 11 1 (spLt ⟨43, 1⟩ ⟨1, 35⟩) := by decide +kernel
example : countAtPair (matScale (1 * 1) (cornerPencil eInd cM 1 2))
    (idMat 2) 1 11 0 (spLt ⟨8, 1⟩ ⟨2, 1⟩) := by decide +kernel
example : splitRead (matScale 35 eInd) (spLt ⟨36, 1⟩ ⟨1, 36⟩) := by
  decide +kernel
example : ¬ psdAt (spLt ⟨36, 1⟩ ⟨1, 36⟩) := by decide +kernel

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
      (matAdd dM (matScale 1 (idMat 2)))) (spLt ⟨10, 9⟩ ⟨10, 8⟩) := by
  decide +kernel
private theorem dCapPsd : psdAt (spLt ⟨10, 9⟩ ⟨10, 8⟩) := by
  decide +kernel

example : BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos (3 + 1 * 1) * quadForm (idMat 2) dpsi
    ≤ BPair.ofPos (4 + 1 * 4) * quadForm (idMat 2) dpsi :=
  drift_cap dE dM (idMat 2) dpsi 1 1 4 3 4 1 (spLt ⟨10, 9⟩ ⟨10, 8⟩)
    dLen (by decide +kernel) (by decide +kernel) dId dCapSplit dCapPsd

/-! The ground identity isolated: at the level's first member `2`
the identity's cross-add fails — `1·3 + 3·1 = 6` against
`2·1 + 1·2 = 4` — and the drift `⟨2 + 1·4 : 3 + 1·1⟩` no longer
prices the electric weight, `3 + 4 ≤ 6` refused. -/

example : ¬ (BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos 3 * quadForm (idMat 2) dpsi).oneValue
    (BPair.ofPos 2 * quadForm (idMat 2) dpsi
      + BPair.ofPos 1 * quadForm dM dpsi) := by decide +kernel
example : ¬ (BPair.ofPos 1 * quadForm dE dpsi
      + BPair.ofPos (3 + 1 * 1) * quadForm (idMat 2) dpsi
    ≤ BPair.ofPos (2 + 1 * 4) * quadForm (idMat 2) dpsi) := by
  decide +kernel

/-! The top root isolated: at the root `⟨1 : 1⟩` the magnetic form
stands above it, the cap's site `G − (M + G) = diag(-2, -1)`
reading two lower-side blocks at its diagonal split — the
positive-semidefinite read refused — and the drift `⟨4 + 1·1 :
3 + 1·1⟩` failing to price the electric weight, `3 + 4 ≤ 5`
refused. -/

example : splitRead
    (siteDatum (matScale 1 (idMat 2))
      (matAdd dM (matScale 1 (idMat 2)))) (spLt ⟨4, 6⟩ ⟨4, 5⟩) := by
  decide +kernel
example : ¬ psdAt (spLt ⟨4, 6⟩ ⟨4, 5⟩) := by decide +kernel
example : ¬ (BPair.ofPos 1 * quadForm dE dpsi
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

private def spOne (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩

private def dpsi1 : List BPair := [⟨2, 1⟩]

private def dG1 : Mat := [[⟨2, 1⟩]]

private def dM2 : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]

example : dpsi1.length = 1 := by decide +kernel
example : (BPair.ofPos 1 * quadForm dG1 dpsi1
      + BPair.ofPos 2 * quadForm dG1 dpsi1).oneValue
    (BPair.ofPos 2 * quadForm dG1 dpsi1
      + BPair.ofPos 1 * quadForm dM2 dpsi1) := by decide +kernel
example : splitRead
    (siteDatum (matScale 3 dG1) (matAdd dM2 (matScale 1 dG1)))
    (spOne ⟨8, 7⟩) := by decide +kernel
example : psdAt (spOne ⟨8, 7⟩) := by decide +kernel
example : ¬ elim.sqAt dM2 1 := by decide +kernel

example : (BPair.ofPos 1 * quadForm dM2 dpsi1
      + BPair.ofPos 2 * quadForm dM2 dpsi1).oneValue
    (BPair.ofPos 2 * quadForm dM2 dpsi1
      + BPair.ofPos 1 * quadForm dG1 dpsi1) := by decide +kernel
example : splitRead
    (siteDatum (matScale 3 dM2) (matAdd dG1 (matScale 1 dM2)))
    (spOne ⟨8, 7⟩) := by decide +kernel


/-! `lem:corner`'s grade-key anchors: the halved summands join to
the residue and the naming read holds at the classical tables at
the small ranks and at the exceptional tables. -/

example : ground.sumNat (corner.cvee (sertables.tableB 4))
    = gentable.residue (sertables.tableB 4) := by decide +kernel
example : ground.sumNat (corner.cvee (sertables.tableC 3))
    = gentable.residue (sertables.tableC 3) := by decide +kernel
example : ground.sumNat (corner.cvee (sertables.tableD 4))
    = gentable.residue (sertables.tableD 4) := by decide +kernel
example : ground.sumNat (corner.cvee (gentable.tableA 3))
    = gentable.residue (gentable.tableA 3) := by decide +kernel
example : ground.sumNat (corner.cvee sertables.tableG2)
    = gentable.residue sertables.tableG2 := by decide +kernel
example : ground.sumNat (corner.cvee sertables.tableF4)
    = gentable.residue sertables.tableF4 := by decide +kernel

example : corner.cveeRead (sertables.tableB 4) := by decide +kernel
example : corner.cveeRead (sertables.tableC 3) := by decide +kernel
example : corner.cveeRead (sertables.tableD 4) := by decide +kernel
example : corner.cveeRead (gentable.tableA 3) := by decide +kernel
example : corner.cveeRead sertables.tableG2 := by decide +kernel
example : corner.cveeRead sertables.tableF4 := by decide +kernel
example : corner.cveeRead sertables.tableE6 := by decide +kernel
example : corner.cveeRead sertables.tableE7 := by decide +kernel
example : corner.cveeRead sertables.tableE8 := by decide +kernel

/-! The displayed closed forms, each decided at its rank and taken
again through its theorem: one at the first and last keys and two
between at `B`, one at every key at `C` and at `A`, one at the
first and last two keys and two between at `D`. -/

example : corner.cvee (sertables.tableB 4)
    = (List.range 4).map (fun i =>
        if i == 0 then 1 else if i + 1 == 4 then 1 else 2) := by
  decide +kernel
example : corner.cvee (sertables.tableB 4)
    = (List.range 4).map (fun i =>
        if i == 0 then 1 else if i + 1 == 4 then 1 else 2) :=
  corner.cvee_B 4 (by decide +kernel)

example : corner.cvee (sertables.tableC 4) = List.replicate 4 1 := by
  decide +kernel
example : corner.cvee (sertables.tableC 4) = List.replicate 4 1 :=
  corner.cvee_C 4

example : corner.cvee (sertables.tableD 5)
    = (List.range 5).map (fun i =>
        if i == 0 then 1 else if 5 ≤ i + 2 then 1 else 2) := by
  decide +kernel
example : corner.cvee (sertables.tableD 5)
    = (List.range 5).map (fun i =>
        if i == 0 then 1 else if 5 ≤ i + 2 then 1 else 2) :=
  corner.cvee_D 5 (by decide +kernel)

example : corner.cvee (gentable.tableA 3) = List.replicate 3 1 := by
  decide +kernel
example : corner.cvee (gentable.tableA 3) = List.replicate 3 1 :=
  corner.cvee_A 3

/-! The sorted words' key reads: the decided value at each of the
six word-and-rank pairs, and one theorem route per series at the
sorted binder and the length frame. -/

example : corner.grade (sertables.tableB 4) (serstable.member [3, 1, 1] 4)
    = 3 + 1 := by decide +kernel
example : corner.grade (sertables.tableB 3) (serstable.member [2, 2] 3)
    = 2 + 2 := by decide +kernel
example : corner.grade (sertables.tableC 3) (serstable.member [2, 1, 1] 3)
    = 2 := by decide +kernel
example : corner.grade (sertables.tableC 4) (serstable.member [3, 1] 4)
    = 3 := by decide +kernel
example : corner.grade (sertables.tableD 5) (serstable.member [2, 2, 1] 5)
    = 2 + 2 := by decide +kernel
example : corner.grade (sertables.tableD 4) (serstable.member [3, 1] 4)
    = 3 + 1 := by decide +kernel

example : corner.grade (sertables.tableB 4) (serstable.member [3, 1, 1] 4)
    = ground.getAt 0 [3, 1, 1] 0 + ground.getAt 0 [3, 1, 1] 1
      - ground.getAt 0 [3, 1, 1] (4 - 1) :=
  corner.grade_member_B [3, 1, 1] 4 (by decide +kernel)
    (by decide +kernel)
example : corner.grade (sertables.tableC 3) (serstable.member [2, 1, 1] 3)
    = ground.getAt 0 [2, 1, 1] 0 :=
  corner.grade_member_C [2, 1, 1] 3 (by decide +kernel)
    (by decide +kernel)
example : corner.grade (sertables.tableD 5) (serstable.member [2, 2, 1] 5)
    = ground.getAt 0 [2, 2, 1] 0 + ground.getAt 0 [2, 2, 1] 1
      - ground.getAt 0 [2, 2, 1] (5 - 2) :=
  corner.grade_member_D [2, 2, 1] 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The `A`-series shape key: the full columns and the reduction
both move off the read, the key the top row's total. -/

example : corner.gradeA (labels.addFulls 2 [2, 1, 0, 1])
    = corner.gradeA [2, 1, 0, 1] := by decide +kernel
example : corner.gradeA (labels.reduce [2, 1, 0, 1])
    = corner.gradeA [2, 1, 0, 1] := by decide +kernel
example : corner.gradeA [2, 1, 0, 1] = 3 := by decide +kernel

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
example : gentable.shapeRead tKodd := by decide +kernel
example : ¬ corner.cveeRead tKodd := by decide +kernel
example : ¬ (ground.sumNat (corner.cvee tKodd)
    = gentable.residue tKodd) := by decide +kernel

/-- `shapeRead`'s refusal at `cvee_sum`: off-rank tail data — the
naming read holds at the key range while the residue fold reads the
length list and the highest root's fold past it, so the two sides
part. -/
private def tKtail : gentable.Table :=
  ⟨1, [2, 2], 1, [[ground.BPair.ofNat 2]], [[1]], [1, 8]⟩
example : ¬ gentable.shapeRead tKtail := by decide +kernel
example : corner.cveeRead tKtail := by decide +kernel
example : ¬ (ground.sumNat (corner.cvee tKtail)
    = gentable.residue tKtail) := by decide +kernel

/-- `cveeRead`'s refusal at `coeffSum_le`: a vacant halved summand,
the coefficient's weight withdrawn from the key. -/
private def tKzero : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [[1]], [1]⟩
example : ¬ corner.cveeRead tKzero := by decide +kernel
example : ¬ (ground.sumNat [5] ≤ corner.grade tKzero [5]) := by
  decide +kernel

/-! `coeffSum_le`'s length frame: a coefficient list past the key
count pairs off truncated, the tail entry dropped from the key
while the coefficient total keeps it. -/

example : ¬ (ground.sumNat [0, 5]
    ≤ corner.grade (gentable.tableA 1) [0, 5]) := by decide +kernel

/-! The word reads' sorted binder: an unsorted word's consecutive
gaps truncate at the reversed step, and the collected reads
overshoot the withdrawn top pair's sum. -/

example : ¬ (corner.grade (sertables.tableB 3)
      (serstable.member [0, 5] 3)
    = ground.getAt 0 [0, 5] 0 + ground.getAt 0 [0, 5] 1
      - ground.getAt 0 [0, 5] (3 - 1)) := by
  decide +kernel

/-! The withdrawal at full-length words: the boundary coordinate
enters the subtracted display, decided at each series' least
covered rank. -/

example : corner.grade (sertables.tableB 2)
    (serstable.member [2, 1] 2) = 2 + 1 - 1 := by decide +kernel
example : corner.grade (sertables.tableC 3)
    (serstable.member [3, 2, 1] 3) = 3 := by decide +kernel
example : corner.grade (sertables.tableD 3)
    (serstable.member [2, 1] 3) = 2 + 1 - 1 := by decide +kernel

/-! The length frames, one per series: a word past the rank feeds
the last gap an occupied entry off the member's keys, and the
subtracted display parts from the fold. -/

example : ¬ (corner.grade (sertables.tableB 3)
      (serstable.member [3, 2, 1, 1] 3)
    = ground.getAt 0 [3, 2, 1, 1] 0 + ground.getAt 0 [3, 2, 1, 1] 1
      - ground.getAt 0 [3, 2, 1, 1] (3 - 1)) := by decide +kernel
example : ¬ (corner.grade (sertables.tableC 1)
      (serstable.member [2, 1] 1)
    = ground.getAt 0 [2, 1] 0) := by decide +kernel
example : ¬ (corner.grade (sertables.tableD 3)
      (serstable.member [3, 2, 1, 1] 3)
    = ground.getAt 0 [3, 2, 1, 1] 0 + ground.getAt 0 [3, 2, 1, 1] 1
      - ground.getAt 0 [3, 2, 1, 1] (3 - 2)) := by decide +kernel

/-! `grade_member_D`'s rank binder: at rank one the fold shape
holds one doubled key, and the key reads past the vacant
subtracted display. -/

example : ¬ (corner.grade (sertables.tableD 1)
      (serstable.member [5] 1)
    = ground.getAt 0 [5] 0 + ground.getAt 0 [5] 1
      - ground.getAt 0 [5] (1 - 2)) := by decide +kernel

/-! The closed forms' rank guards: below the stated rank the
highest root's fold collapses onto the short keys and the halved
summand vanishes there, so the displayed form is refused. -/

example : ¬ (corner.cvee (sertables.tableB 1)
    = (List.range 1).map (fun i =>
        if i == 0 then 1 else if i + 1 == 1 then 1 else 2)) := by
  decide +kernel
example : ¬ (corner.cvee (sertables.tableD 2)
    = (List.range 2).map (fun i =>
        if i == 0 then 1 else if 2 ≤ i + 2 then 1 else 2)) := by
  decide +kernel


/-! `lem:corner`'s move-cap anchors: the highest root's dominant
reads and the dominance join at the top, decided at the classical
tables at the small ranks and at the exceptional tables. -/

example : corner.thetaDomRead (sertables.tableB 4) := by decide +kernel
example : corner.thetaDomRead (sertables.tableC 3) := by decide +kernel
example : corner.thetaDomRead (sertables.tableD 4) := by decide +kernel
example : corner.thetaDomRead (gentable.tableA 3) := by decide +kernel
example : corner.thetaDomRead sertables.tableG2 := by decide +kernel
example : corner.thetaDomRead sertables.tableF4 := by decide +kernel
example : corner.thetaDomRead sertables.tableE6 := by decide +kernel
example : corner.thetaDomRead sertables.tableE7 := by decide +kernel
example : corner.thetaDomRead sertables.tableE8 := by decide +kernel

example : corner.thetaTopRead (sertables.tableB 4) := by decide +kernel
example : corner.thetaTopRead (sertables.tableC 3) := by decide +kernel
example : corner.thetaTopRead (sertables.tableD 4) := by decide +kernel
example : corner.thetaTopRead (gentable.tableA 3) := by decide +kernel
example : corner.thetaTopRead sertables.tableG2 := by decide +kernel
example : corner.thetaTopRead sertables.tableF4 := by decide +kernel
example : corner.thetaTopRead sertables.tableE6 := by decide +kernel
example : corner.thetaTopRead sertables.tableE7 := by decide +kernel
example : corner.thetaTopRead sertables.tableE8 := by decide +kernel

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

example : row.thetaFamRead (sertables.tableB 2)
    (thetaL (sertables.tableB 2)) := by decide +kernel
example : row.thetaFamRead (sertables.tableC 3)
    (thetaL (sertables.tableC 3)) := by decide +kernel
example : row.thetaFamRead sertables.tableG2
    (thetaL sertables.tableG2) := by decide +kernel

example : ((thetaL (sertables.tableB 3)).all (fun nu =>
    (corner.gradeV (sertables.tableB 3) nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((corner.gradeV (sertables.tableB 3) nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel
example : ((thetaL (sertables.tableC 3)).all (fun nu =>
    (corner.gradeV (sertables.tableC 3) nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((corner.gradeV (sertables.tableC 3) nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel
example : ((thetaL (sertables.tableD 4)).all (fun nu =>
    (corner.gradeV (sertables.tableD 4) nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((corner.gradeV (sertables.tableD 4) nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel
example : ((thetaL sertables.tableG2).all (fun nu =>
    (corner.gradeV sertables.tableG2 nu ≤ ground.BPair.ofNat 2 : Bool)
    && ((corner.gradeV sertables.tableG2 nu).swap
          ≤ ground.BPair.ofNat 2))) = true := by decide +kernel

/-! The theorem routes beside the decided caps: the positive
member's two walls, a content's cap at the list membership, and the
key's move under a fused target's coroot list. -/

example : ground.BPair.unit ≤ corner.gradeV (sertables.tableB 2)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    ∧ corner.gradeV (sertables.tableB 2)
        (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
      ≤ ground.BPair.ofNat 2 :=
  corner.posGrade_cap (sertables.tableB 2) 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : corner.gradeV (sertables.tableB 2)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    ≤ ground.BPair.ofNat 2
    ∧ (corner.gradeV (sertables.tableB 2)
        (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))).swap
      ≤ ground.BPair.ofNat 2 :=
  corner.content_cap (sertables.tableB 2) (thetaL (sertables.tableB 2))
    (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 1))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (ground.mem_of_countOf_pos _ (thetaL (sertables.tableB 2))
      (by decide +kernel))

example : corner.grade (sertables.tableB 2) [1, 3]
      ≤ corner.grade (sertables.tableB 2) [1, 1] + 2
    ∧ corner.grade (sertables.tableB 2) [1, 1]
      ≤ corner.grade (sertables.tableB 2) [1, 3] + 2 :=
  corner.grade_move (sertables.tableB 2) (thetaL (sertables.tableB 2))
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
example : ¬ corner.thetaTopRead tMtop := by decide +kernel
example : gentable.shapeRead tMtop := by decide +kernel
example : gentable.symRead tMtop := by decide +kernel
example : corner.cveeRead tMtop := by decide +kernel
example : gentable.thetaNormRead tMtop := by decide +kernel
example : corner.thetaDomRead tMtop := by decide +kernel
example : ¬ (corner.gradeV tMtop
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
example : ¬ corner.thetaDomRead tMdom := by decide +kernel
example : gentable.shapeRead tMdom := by decide +kernel
example : gentable.symRead tMdom := by decide +kernel
example : gentable.thetaNormRead tMdom := by decide +kernel
example : corner.cveeRead tMdom := by decide +kernel
example : corner.thetaTopRead tMdom := by decide +kernel
example : ¬ (ground.BPair.unit ≤ corner.gradeV tMdom
    (poly.pnorm (sertables.posCorootV tMdom 1))) := by decide +kernel

/-- `thetaNormRead`'s refusal: the doubled top — its form fold
reads sixteen against the cleared four, and the simple member's key
read stands at four, off the wall the norm sets. -/
private def tMnorm : gentable.Table :=
  ⟨1, [2], 1, [[ground.BPair.ofNat 2]], [[1], [2]], [2]⟩
example : ¬ gentable.thetaNormRead tMnorm := by decide +kernel
example : gentable.shapeRead tMnorm := by decide +kernel
example : gentable.symRead tMnorm := by decide +kernel
example : corner.cveeRead tMnorm := by decide +kernel
example : corner.thetaDomRead tMnorm := by decide +kernel
example : corner.thetaTopRead tMnorm := by decide +kernel
example : ¬ (corner.gradeV tMnorm
    (poly.pnorm (sertables.posCorootV tMnorm 0))
      ≤ ground.BPair.ofNat 2) := by decide +kernel

/-- `symRead`'s refusal: the asymmetric edge at matched lengths —
the halved products' exchange breaks, so the row keys no longer
clear to the top's coroot pairs and a key read falls under the
sum's unit. -/
private def tMsym : gentable.Table :=
  ⟨2, [2, 4], 1,
   [[ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap],
    [(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2]],
   [[1, 0], [0, 1], [1, 1], [2, 1]], [2, 1]⟩
example : ¬ gentable.symRead tMsym := by decide +kernel
example : gentable.shapeRead tMsym := by decide +kernel
example : gentable.thetaNormRead tMsym := by decide +kernel
example : corner.cveeRead tMsym := by decide +kernel
example : corner.thetaDomRead tMsym := by decide +kernel
example : corner.thetaTopRead tMsym := by decide +kernel
example : ¬ (ground.BPair.unit ≤ corner.gradeV tMsym
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
example : ¬ corner.cveeRead tMcvee := by decide +kernel
example : gentable.shapeRead tMcvee := by decide +kernel
example : gentable.symRead tMcvee := by decide +kernel
example : gentable.thetaNormRead tMcvee := by decide +kernel
example : corner.thetaDomRead tMcvee := by decide +kernel
example : corner.thetaTopRead tMcvee := by decide +kernel
example : corner.cvee tMcvee = [1, 0] := by decide +kernel
example : ¬ (corner.gradeV tMcvee
    (poly.pnorm (sertables.posCorootV tMcvee 0))
      ≤ ground.BPair.ofNat 2) := by decide +kernel
example : ¬ (ground.BPair.unit ≤ corner.gradeV tMcvee
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
example : ¬ gentable.shapeRead tMshape := by decide +kernel
example : gentable.symRead tMshape := by decide +kernel
example : gentable.thetaNormRead tMshape := by decide +kernel
example : corner.cveeRead tMshape := by decide +kernel
example : corner.thetaDomRead tMshape := by decide +kernel
example : corner.thetaTopRead tMshape := by decide +kernel
example : ¬ (ground.BPair.unit ≤ corner.gradeV tMshape
    (poly.pnorm (sertables.posCorootV tMshape 0))) := by decide +kernel

/-! `content_cap`'s membership binder: a vector off the content
list breaks the cap — at `B2` the coroot list `⟨3 : 0⟩` reads its
key at three, and its count in the content list is vacant. -/

example : ¬ (corner.gradeV (sertables.tableB 2)
    [ground.BPair.ofNat 3, ground.BPair.unit]
      ≤ ground.BPair.ofNat 2) := by decide +kernel
example : ground.countOf [ground.BPair.ofNat 3, ground.BPair.unit]
    (thetaL (sertables.tableB 2)) = 0 := by decide +kernel

/-! `gradeV_add`'s order binder: at unmatched orders the join
truncates at the shorter content, so the joined key read parts from
the summands' — at `A2` the truncated join reads two against the
summands' seven. -/

example : ¬ ((corner.gradeV (gentable.tableA 2)
      (poly.pnorm (elim.vecAdd
        [ground.BPair.ofNat 1, ground.BPair.ofNat 5]
        [ground.BPair.ofNat 1]))).oneValue
    (corner.gradeV (gentable.tableA 2)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 5]
      + corner.gradeV (gentable.tableA 2)
        [ground.BPair.ofNat 1])) := by decide +kernel

/-! `grade_move`'s tie binder: a coroot list off the moved content
loses the cap — at `B2` the list `[4, 4]` reads its key at eight
against the source's one. -/

example : ¬ (corner.grade (sertables.tableB 2) [4, 4]
    ≤ corner.grade (sertables.tableB 2) [1, 0] + 2) := by decide +kernel

/-! `lem:corner`'s Casimir caps: the three series' coordinate
routes at the boxed sorted words, the `A`-series' cleared traceless
read at the reduced representative, and the fundamental display's
cap at the two exceptional Grams — each beside its theorem route
and its isolating refusals. -/

/-! The series' displayed numerators against the key's square, the
sorted words of the box `[4, 4]` at rank four: the `B` and `D` keys
the top pair's sum, the `C` key the top coordinate. -/

example : ((ground.boxAll [4, 4]).all (fun w =>
    let W := if ground.getAt 0 w 1 ≤ ground.getAt 0 w 0 then w
             else [ground.getAt 0 w 1, ground.getAt 0 w 0]
    let K := ground.getAt 0 W 0 + ground.getAt 0 W 1
    serstable.casNumB W 4 < (4 * 4 + 4) * (K * K + 1))) = true := by
  decide +kernel

example : ((ground.boxAll [4, 4]).all (fun w =>
    let W := if ground.getAt 0 w 1 ≤ ground.getAt 0 w 0 then w
             else [ground.getAt 0 w 1, ground.getAt 0 w 0]
    let K := ground.getAt 0 W 0
    serstable.casNumC W 4 < (4 * 4 + 4) * (K * K + 1))) = true := by
  decide +kernel

example : ((ground.boxAll [4, 4]).all (fun w =>
    let W := if ground.getAt 0 w 1 ≤ ground.getAt 0 w 0 then w
             else [ground.getAt 0 w 1, ground.getAt 0 w 0]
    let K := ground.getAt 0 W 0 + ground.getAt 0 W 1
    serstable.casNumD W 4 < (4 * 4 + 4) * (K * K + 1))) = true := by
  decide +kernel

example : serstable.casNumB [] 1 < (1 * 1 + 1) * (0 * 0 + 1) := by
  decide +kernel

/-! The `A`-series' cleared traceless read at the reduced
representative, the shapes of the box `[3, 3, 3]` against
`d²(d+1)(K² + 1)`. -/

example : ((ground.boxAll [3, 3, 3]).all (fun s =>
    c2hat.dfQ (labels.reduce s)
      < s.length * s.length * (s.length + 1)
        * (corner.gradeA s * corner.gradeA s + 1))) = true := by
  decide +kernel

/-! The fundamental display's cap at the two exceptional tables:
the displayed adjugate rows' Gram reads its walls at `[12, 18]`
(`G2`) and `[12, 42]` (`F4`), and every coefficient list of the
box sits below `(FN + RN)(G² + 1)`. -/

example : corner.gramCapRead sertables.tableG2
    (memberdata.gramRows sertables.tableG2 sertables.adjG2) 12 18 := by
  decide +kernel

example : ((ground.boxAll [3, 3]).all (fun m =>
    memberdata.c2M sertables.tableG2
      (memberdata.gramRows sertables.tableG2 sertables.adjG2) m
    < (12 + 18) * (corner.grade sertables.tableG2 m
        * corner.grade sertables.tableG2 m + 1))) = true := by
  decide +kernel

example : corner.gramCapRead sertables.tableF4
    (memberdata.gramRows sertables.tableF4 sertables.adjF4) 12 42 := by
  decide +kernel

example : ((ground.boxAll [2, 2, 2, 2]).all (fun m =>
    memberdata.c2M sertables.tableF4
      (memberdata.gramRows sertables.tableF4 sertables.adjF4) m
    < (12 + 42) * (corner.grade sertables.tableF4 m
        * corner.grade sertables.tableF4 m + 1))) = true := by
  decide +kernel

/-! The theorem routes at the decided anchors: the fundamental
display at `G2`'s Gram, the three series at the sorted word
`[3, 1]` at rank four, and the `A` series at the shape
`[2, 1, 0, 1]`. -/

example : memberdata.c2M sertables.tableG2
    (memberdata.gramRows sertables.tableG2 sertables.adjG2) [2, 1]
    < (12 + 18) * (corner.grade sertables.tableG2 [2, 1]
        * corner.grade sertables.tableG2 [2, 1] + 1) :=
  corner.c2M_cap sertables.tableG2
    (memberdata.gramRows sertables.tableG2 sertables.adjG2) 12 18 [2, 1]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : serstable.casNumB [3, 1] 4 < (4 * 4 + 4)
    * ((ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1)
        * (ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1) + 1) :=
  corner.casCap_B [3, 1] 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : serstable.casNumC [3, 1] 4 < (4 * 4 + 4)
    * (ground.getAt 0 [3, 1] 0 * ground.getAt 0 [3, 1] 0 + 1) :=
  corner.casCap_C [3, 1] 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : serstable.casNumD [3, 1] 4 < (4 * 4 + 4)
    * ((ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1)
        * (ground.getAt 0 [3, 1] 0 + ground.getAt 0 [3, 1] 1) + 1) :=
  corner.casCap_D [3, 1] 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : c2hat.dfQ (labels.reduce [2, 1, 0, 1])
    < [2, 1, 0, 1].length * [2, 1, 0, 1].length
      * ([2, 1, 0, 1].length + 1)
      * (corner.gradeA [2, 1, 0, 1] * corner.gradeA [2, 1, 0, 1] + 1) :=
  corner.dfQ_cap [2, 1, 0, 1] (by decide +kernel)

/-! `casCap_X`'s sorted binder: an unsorted word carries its
occupancy off the head pair, so the key `W₀ + W₁` reads vacant
while the square fold is occupied. -/

example : ¬ (serstable.casNumB [0, 0, 9] 3
    < (3 * 3 + 3) * ((0 + 0) * (0 + 0) + 1)) := by decide +kernel

/-! `casCap_X`'s clearance binder: a word past the rank collects
entries the rank's own scale never prices — twenty unit entries at
rank one read the numerator forty against the cap's ten. -/

example : ¬ (serstable.casNumB (List.replicate 20 1) 1
    < (1 * 1 + 1) * ((1 + 1) * (1 + 1) + 1)) := by decide +kernel

/-! `casCap_X`'s rank binder: at the vacant rank the cleared
factor `l(l+1)` is itself vacant, so no numerator sits below it. -/

example : ¬ (serstable.casNumB [] 0
    < (0 * 0 + 0) * ((0 + 0) * (0 + 0) + 1)) := by decide +kernel

/-! `dfQ_cap`'s width binder: at the vacant width the cleared
factor `d²(d+1)` is vacant, so the traceless read never sits below
it. -/

example : ¬ (c2hat.dfQ (labels.reduce [])
    < 0 * 0 * (0 + 1)
      * (corner.gradeA [] * corner.gradeA [] + 1)) := by decide +kernel

/-- `c2M_cap`'s naming binder: the odd-summand table — the halved
summand truncates to the count's unit, so the key reads vacant at
an occupied coefficient list while the Gram's walls hold. -/
private def tCzero : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [[1]], [1]⟩

example : corner.gramCapRead tCzero [[ground.BPair.ofNat 1]] 1 1 := by
  decide +kernel
example : ¬ corner.cveeRead tCzero := by decide +kernel
example : ¬ (memberdata.c2M tCzero [[ground.BPair.ofNat 1]] [5]
    < (1 + 1) * (corner.grade tCzero [5]
        * corner.grade tCzero [5] + 1)) := by decide +kernel

/-! `gramCapRead`'s refusal at understated walls: `G2`'s displayed
Gram carries an entry past twelve's understatement and a `ρ`-dot
past ten's. -/

example : ¬ corner.gramCapRead sertables.tableG2
    (memberdata.gramRows sertables.tableG2 sertables.adjG2) 6 10 := by
  decide +kernel

/-- `c2M_cap`'s entry binder: the naming read holds and the
`ρ`-dot wall holds at nine, while one Gram entry stands past the
base's own — and there the display sits at twenty-seven against
the cap's twenty. -/
private def tCentry : gentable.Table :=
  ⟨1, [2], 1, [[ground.BPair.ofNat 2]], [[1]], [1]⟩

example : corner.cveeRead tCentry := by decide +kernel
example : elim.dotP (ground.getAt [] [[ground.BPair.ofNat 9]] 0)
    (sertables.rhoV tCentry) ≤ ground.BPair.ofNat 9 := by decide +kernel
example : ¬ corner.gramCapRead tCentry [[ground.BPair.ofNat 9]] 1 9 := by
  decide +kernel
example : ¬ (memberdata.c2M tCentry [[ground.BPair.ofNat 9]] [1]
    < (1 + 9) * (corner.grade tCentry [1]
        * corner.grade tCentry [1] + 1)) := by decide +kernel

/-! `c2M_cap`'s two order frames are jointly load-bearing: the
pairing truncates at the shorter of the coefficient list and the
Gram, so EITHER side off the rank alone drops exactly the summands
the key drops — the four one-sided reads below hold the cap at a
coefficient list past the rank, short of it, a Gram row past the
rank and a Gram short of it — while BOTH sides past the rank keep
summands the key never reads, and the cap refuses at the committed
joint witness beneath them. -/

example : memberdata.c2M tCentry [[ground.BPair.ofNat 1]] [5, 99]
    < (1 + 1) * (corner.grade tCentry [5, 99]
        * corner.grade tCentry [5, 99] + 1) := by decide +kernel

example : ((ground.boxAll [3, 3]).all (fun m =>
    memberdata.c2M sertables.tableG2
      (memberdata.gramRows sertables.tableG2 sertables.adjG2
        ++ [[ground.BPair.ofNat 99, ground.BPair.ofNat 99]]) m
    < (12 + 18) * (corner.grade sertables.tableG2 m
        * corner.grade sertables.tableG2 m + 1))) = true := by
  decide +kernel

example : memberdata.c2M (gentable.tableA 2)
    [[ground.BPair.ofNat 1, ground.BPair.unit],
     [ground.BPair.unit, ground.BPair.ofNat 1]] [40]
    < (1 + 1) * (corner.grade (gentable.tableA 2) [40]
        * corner.grade (gentable.tableA 2) [40] + 1) := by decide +kernel

example : memberdata.c2M (gentable.tableA 2)
    [[ground.BPair.ofNat 1, ground.BPair.unit]] [5, 5]
    < (1 + 1) * (corner.grade (gentable.tableA 2) [5, 5]
        * corner.grade (gentable.tableA 2) [5, 5] + 1) := by decide +kernel

/-- The joint refusal: the coefficient list and the Gram both past
the rank — the pairing pairs the off-rank coefficient against the
off-rank row, a summand the key never reads, and the cap
refuses. -/
private def gJoint : elim.Mat :=
  [[ground.BPair.ofNat 1], [ground.BPair.ofNat 99]]

example : corner.gramCapRead tCentry gJoint 1 1 := by decide +kernel
example : corner.cveeRead tCentry := by decide +kernel
example : ¬ (([1, 99] : List Nat).length = tCentry.rank) := by
  decide +kernel
example : ¬ (gJoint.length = tCentry.rank) := by decide +kernel
example : ¬ (memberdata.c2M tCentry gJoint [1, 99]
    < (1 + 1) * (corner.grade tCentry [1, 99]
        * corner.grade tCentry [1, 99] + 1)) := by decide +kernel

/-! `lem:corner`'s per-key counts: the key list's identification at
the boxed coroot lists, its length cap, the `θ` factor's read at
the raised member with its dominance over the gap product's
factors, the member dimension's cap, and the two strict per-key
caps — each beside its theorem route, with the binders refused at
their own tables. -/

example : ((ground.boxAll [4, 4, 4]).all (fun m =>
    ground.countOf m (corner.keyAll (sertables.tableB 3) 3)
      == if m.length = 3 ∧ corner.grade (sertables.tableB 3) m = 3
         then 1 else 0)) = true := by decide +kernel

example : (corner.keyAll (sertables.tableB 3) 3).length
    ≤ ground.prodOver (fun _ => 3 + 1) (List.range 3) := by
  decide +kernel

example : ((List.range (sertables.tableB 3).posFolds.length).all
    (fun j => serstable.gapAt (sertables.tableB 3) [3, 2, 1] j
      ≤ corner.thetaGap (sertables.tableB 3) [3, 2, 1])) = true := by
  decide +kernel

example : corner.thetaGap (sertables.tableB 3) ([2, 1, 0].map (· + 1))
    = 2 * (sertables.tableB 3).lenDen
      * (corner.grade (sertables.tableB 3) [2, 1, 0]
          + gentable.residue (sertables.tableB 3)) := by decide +kernel

example : corner.thetaGap (sertables.tableC 3) ([2, 1, 0].map (· + 1))
    = 2 * (sertables.tableC 3).lenDen
      * (corner.grade (sertables.tableC 3) [2, 1, 0]
          + gentable.residue (sertables.tableC 3)) := by decide +kernel

/-! The member dimension's cap over the coefficient box `[2,2,2]`
at `B3`: every gap-product factor at or below the `θ` factor, the
`θ` factor itself the member's own `2 lenDen (G + r)`. -/

example : ((ground.boxAll [2, 2, 2]).all (fun m =>
    memberdata.dimM (sertables.tableB 3) m
      ≤ ground.prodOver
          (fun _ => 2 * (sertables.tableB 3).lenDen
            * (corner.grade (sertables.tableB 3) m
                + gentable.residue (sertables.tableB 3)))
          (List.range (sertables.tableB 3).posFolds.length))) = true := by
  decide +kernel

/-! The two strict per-key caps at `B2` and the key three. -/

example : (corner.keyAll (sertables.tableB 2) 2).length
    < corner.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (corner.capP (sertables.tableB 2))) := by
  decide +kernel

example : ground.sumNat ((corner.keyAll (sertables.tableB 2) 2).map
      (memberdata.dimM (sertables.tableB 2)))
    < corner.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (corner.capP (sertables.tableB 2))) := by
  decide +kernel

/-! The theorem routes beside the decided anchors: the
identification at an inside member and at a member off the rank,
the length cap, the `θ` factor's read, the dimension cap and the
two strict caps. -/

example : ground.countOf [1, 1] (corner.keyAll (sertables.tableB 2) 2)
    = if ([1, 1] : List Nat).length = (sertables.tableB 2).rank
        ∧ corner.grade (sertables.tableB 2) [1, 1] = 2
      then 1 else 0 :=
  corner.keyAll_countOf (sertables.tableB 2) 2 [1, 1] (by decide +kernel)

example : ground.countOf [2] (corner.keyAll (sertables.tableB 2) 2)
    = if ([2] : List Nat).length = (sertables.tableB 2).rank
        ∧ corner.grade (sertables.tableB 2) [2] = 2
      then 1 else 0 :=
  corner.keyAll_countOf (sertables.tableB 2) 2 [2] (by decide +kernel)

example : (corner.keyAll (sertables.tableB 2) 2).length
    ≤ ground.prodOver (fun _ => 2 + 1)
      (List.range (sertables.tableB 2).rank) :=
  corner.keyAll_length (sertables.tableB 2) 2

example : corner.thetaGap (sertables.tableB 3) ([2, 1, 0].map (· + 1))
    = 2 * (sertables.tableB 3).lenDen
      * (corner.grade (sertables.tableB 3) [2, 1, 0]
          + gentable.residue (sertables.tableB 3)) :=
  corner.thetaGap_read (sertables.tableB 3) [2, 1, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : memberdata.dimM (sertables.tableB 3) [2, 1, 0]
    ≤ ground.prodOver
        (fun _ => 2 * (sertables.tableB 3).lenDen
          * (corner.grade (sertables.tableB 3) [2, 1, 0]
              + gentable.residue (sertables.tableB 3)))
        (List.range (sertables.tableB 3).posFolds.length) :=
  corner.dimM_cap (sertables.tableB 3) [2, 1, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : (corner.keyAll (sertables.tableB 2) 2).length
    < corner.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (corner.capP (sertables.tableB 2))) :=
  corner.keyCount_cap (sertables.tableB 2) 2 (by decide +kernel)
    (by decide +kernel)

example : ground.sumNat ((corner.keyAll (sertables.tableB 2) 2).map
      (memberdata.dimM (sertables.tableB 2)))
    < corner.capA (sertables.tableB 2)
      * ground.prodOver (fun _ => 2 + 1)
        (List.range (corner.capP (sertables.tableB 2))) :=
  corner.keyDim_cap (sertables.tableB 2) 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! `keyAll_countOf`'s naming binder: at the odd-summand table the
halved summand truncates to the count's unit, so every coroot list
reads the key vacant while the entry bound the box carries is that
same vacant key — the solution `[7]` escapes the box and its count
falls under the identification's unit. -/

example : ground.countOf [7] (corner.keyAll tCzero 0) = 0 := by
  decide +kernel
example : ¬ (ground.countOf [7] (corner.keyAll tCzero 0)
    = if ([7] : List Nat).length = tCzero.rank
        ∧ corner.grade tCzero [7] = 0
      then 1 else 0) := by decide +kernel

/-- `thetaGap_read`'s length binder: a table at the rank one whose
halved summand is the count's unit — the vacant coroot list reads
the `θ` factor at the sum's unit while the cleared right side
carries the residue. -/
private def tDlen : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [[1]], [2]⟩

example : gentable.shapeRead tDlen := by decide +kernel
example : corner.cveeRead tDlen := by decide +kernel
example : ¬ (([] : List Nat).length = tDlen.rank) := by decide +kernel
example : ¬ (corner.thetaGap tDlen (([] : List Nat).map (· + 1))
    = 2 * tDlen.lenDen
      * (corner.grade tDlen [] + gentable.residue tDlen)) := by
  decide +kernel

/-! `thetaGap_read`'s shape binder: the off-rank tail table — the
naming read holds at the rank while the residue and the length
fold read the tail, so the two sides part at the coroot list
`[0]`. -/

example : corner.cveeRead tKtail := by decide +kernel
example : ([0] : List Nat).length = tKtail.rank := by decide +kernel
example : ¬ (corner.thetaGap tKtail (([0] : List Nat).map (· + 1))
    = 2 * tKtail.lenDen
      * (corner.grade tKtail [0] + gentable.residue tKtail)) := by
  decide +kernel

/-- `keyCount_cap`'s and `keyDim_cap`'s positive-list binder: at a
vacant positive list the base `A` is the product's own unit and
the exponent `p` the rank alone, so the cap reads one against the
vacuum's own single label. -/
private def tDnop : gentable.Table :=
  ⟨1, [1], 1, [[ground.BPair.ofNat 2]], [], [2]⟩

example : gentable.shapeRead tDnop := by decide +kernel
example : corner.cveeRead tDnop := by decide +kernel
example : (1 : Nat) ≤ tDnop.lenDen := by decide +kernel
example : ¬ (1 ≤ tDnop.posFolds.length) := by decide +kernel
example : ¬ ((corner.keyAll tDnop 0).length
    < corner.capA tDnop * ground.prodOver (fun _ => 0 + 1)
        (List.range (corner.capP tDnop))) := by decide +kernel
example : ¬ (ground.sumNat ((corner.keyAll tDnop 0).map
      (memberdata.dimM tDnop))
    < corner.capA tDnop * ground.prodOver (fun _ => 0 + 1)
        (List.range (corner.capP tDnop))) := by decide +kernel

/-- `keyCount_cap`'s and `keyDim_cap`'s length-denominator binder:
at the vacant denominator the base `A` is vacant at an occupied
positive list, so no count sits below it. -/
private def tDden : gentable.Table :=
  ⟨0, [], 0, [], [[]], []⟩

example : gentable.shapeRead tDden := by decide +kernel
example : corner.cveeRead tDden := by decide +kernel
example : (1 : Nat) ≤ tDden.posFolds.length := by decide +kernel
example : ¬ (1 ≤ tDden.lenDen) := by decide +kernel
example : corner.capA tDden = 0 := by decide +kernel
example : ¬ ((corner.keyAll tDden 0).length
    < corner.capA tDden * ground.prodOver (fun _ => 0 + 1)
        (List.range (corner.capP tDden))) := by decide +kernel
example : ¬ (ground.sumNat ((corner.keyAll tDden 0).map
      (memberdata.dimM tDden))
    < corner.capA tDden * ground.prodOver (fun _ => 0 + 1)
        (List.range (corner.capP tDden))) := by decide +kernel

/-! The gap comparison's dominance-join binder, isolated
(`gapAt_le`): at a fold beyond the top — `tMtop`'s second — the
gap product's factor overshoots the `θ` factor outright, the
join the comparison's one witness with the shape and naming reads
held beside it. -/

example : ¬ corner.thetaTopRead tMtop := by decide +kernel
example : ¬ (serstable.gapAt tMtop [1] 1
    ≤ corner.thetaGap tMtop [1]) := by decide +kernel

/-- The gap comparison's shape binder, isolated: the dominance
join reads the folds against the top at the keys below the rank
alone, so a table whose length family runs past the rank prices
gap-product entries the top never sees.  Here the length family
carries two entries at the rank one and the positive fold reads
seven at the second key: the join holds while the gap factor
stands at eight against the `θ` factor's one. -/
private def tDwide : gentable.Table :=
  ⟨1, [1, 1], 1, [[ground.BPair.ofNat 2]], [[1, 7]], [1]⟩

example : corner.thetaTopRead tDwide := by decide +kernel
example : ¬ gentable.shapeRead tDwide := by decide +kernel
example : (0 : Nat) < tDwide.posFolds.length := by decide +kernel
example : ¬ (serstable.gapAt tDwide [1, 1] 0
    ≤ corner.thetaGap tDwide [1, 1]) := by decide +kernel

/-- The same refusal at the vacant rank, where the dominance join
is vacuous: the positive fold reads five at the one key the length
family prices, the highest root's fold vacant there. -/
private def tDvac : gentable.Table :=
  ⟨0, [1], 1, [], [[5]], []⟩

example : corner.thetaTopRead tDvac := by decide +kernel
example : ¬ gentable.shapeRead tDvac := by decide +kernel
example : (0 : Nat) < tDvac.posFolds.length := by decide +kernel
example : ¬ (serstable.gapAt tDvac [1] 0
    ≤ corner.thetaGap tDvac [1]) := by decide +kernel

/-! The grade-key tier's remaining reads at their theorem routes:
the residue join, the vacuum and `ρ` keys, the `A`-series class
reads, the fold's additivity, and the gap factor's dominance —
each the theorem applied at a decided fixture, the route beside
the tier's decided anchors. -/

example : ground.sumNat (corner.cvee (sertables.tableB 4))
    = gentable.residue (sertables.tableB 4) :=
  corner.cvee_sum (sertables.tableB 4) (by decide +kernel)
    (by decide +kernel)

example : corner.grade (sertables.tableB 4)
    (List.replicate (sertables.tableB 4).rank 0) = 0 :=
  corner.grade_vac (sertables.tableB 4)

example : corner.grade (sertables.tableB 4)
    (List.replicate (sertables.tableB 4).rank 1)
    = gentable.residue (sertables.tableB 4) :=
  corner.grade_rho (sertables.tableB 4) (by decide +kernel)
    (by decide +kernel)

example : corner.gradeA (labels.addFulls 2 [2, 1, 0, 1])
    = corner.gradeA [2, 1, 0, 1] :=
  corner.gradeA_fulls 2 [2, 1, 0, 1]

example : corner.gradeA (labels.reduce [2, 1, 0, 1])
    = corner.gradeA [2, 1, 0, 1] :=
  corner.gradeA_reduce [2, 1, 0, 1]

example : (corner.gradeV (sertables.tableB 2)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
      [ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap]))).oneValue
    (corner.gradeV (sertables.tableB 2)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
      + corner.gradeV (sertables.tableB 2)
        [ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap]) :=
  corner.gradeV_add (sertables.tableB 2)
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
    [ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap] rfl

example : serstable.gapAt (sertables.tableB 3) [3, 2, 1] 0
    ≤ corner.thetaGap (sertables.tableB 3) [3, 2, 1] :=
  corner.gapAt_le (sertables.tableB 3) [3, 2, 1] 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! `lem:corner`'s Rayleigh close: the dimension-weighted family's
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

example : ground.prodOver (fun _ => 8) (List.range (2 * 4))
    ≤ corner.pairFold 3 4 1 8 dRt gRt :=
  corner.vac_floor 3 4 1 8 0 dRt gRt (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : ground.prodOver (fun _ => 8) (List.range (2 * 4))
    ≤ corner.pairFold 3 4 1 8 dRt gRt := by decide +kernel

example : 1 * 1 * 3 * corner.pairFold 3 4 1 8 dRt gRt
    ≤ 8 * 8 * corner.magFold 3 4 1 8 dRt gRt nRt
      + 1 * 1 * 3 * corner.topFold 3 4 1 8 dRt gRt :=
  corner.mag_low 3 4 1 8 3 dRt gRt nRt (by decide +kernel)
    tMove tDim

example : 1 * 1 * 3 * corner.pairFold 3 4 1 8 dRt gRt
    ≤ 8 * 8 * corner.magFold 3 4 1 8 dRt gRt nRt
      + 1 * 1 * 3 * corner.topFold 3 4 1 8 dRt gRt := by
  decide +kernel

example : 1 * 1 * 3 * corner.topFold 3 4 1 8 dRt gRt
    ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4 + 1)) :=
  corner.top_cap 3 4 1 7 8 3 2 1 dRt gRt (by decide +kernel)
    (tCnt 4 (by decide +kernel)) (tCnt (4 - 1) (by decide +kernel))
    tCert

example : 1 * 1 * 3 * corner.topFold 3 4 1 8 dRt gRt
    ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4 + 1)) := by
  decide +kernel

example : ground.prodOver (fun _ => 7) (List.range (2 * 1 + 3)) * 1
      * corner.elecFold 3 4 1 8 dRt gRt eRt
    ≤ 5 * (2 * 2) * ground.rise 1 (2 * 1 + 2)
      * ground.prodOver (fun _ => 8)
          (List.range (2 * 4 + (2 * 1 + 3))) :=
  corner.elec_cap 3 4 1 7 8 2 1 5 1 dRt gRt eRt (by decide +kernel)
    tHe tCnt

example : ground.prodOver (fun _ => 7) (List.range (2 * 1 + 3)) * 1
      * corner.elecFold 3 4 1 8 dRt gRt eRt
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

example : 1 ≤ 3 :=
  corner.family_ground 4 1 7 8 3 2 1 5 1 1 1 0 dRt gRt eRt nRt
    tSite (1007574152 : Pos) (50421 : Pos) (1 : Pos) 3 tSplit
    (by decide +kernel) tMove tDim tHe tCnt tCert
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    tCount

/-! The trial family's three quadratic reads at the toy head, the
theorem route beside its decided anchor each, and the count's
Rayleigh witness routed at the head's own site datum. -/

example : (quadForm
      (ground.matOf 3 3 (fun i j =>
        if i == j then BPair.ofNat (eRt i) else ground.BPair.unit))
      (corner.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (corner.elecFold 3 4 1 8 dRt gRt eRt)) :=
  corner.quad_diag 3 4 1 8 dRt gRt eRt

example : (quadForm
      (ground.matOf 3 3 (fun i j =>
        if i == j then BPair.ofNat (eRt i) else ground.BPair.unit))
      (corner.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (corner.elecFold 3 4 1 8 dRt gRt eRt)) := by
  decide +kernel

example : (quadForm (idMat 3)
      (corner.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (corner.pairFold 3 4 1 8 dRt gRt)) :=
  corner.quad_gram 3 4 1 8 dRt gRt

example : (quadForm (idMat 3)
      (corner.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (corner.pairFold 3 4 1 8 dRt gRt)) := by
  decide +kernel

example : (quadForm
      (ground.matOf 3 3 (fun i j => BPair.ofNat (nRt i j)))
      (corner.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (corner.magFold 3 4 1 8 dRt gRt nRt)) :=
  corner.quad_rows 3 4 1 8 dRt gRt nRt

example : (quadForm
      (ground.matOf 3 3 (fun i j => BPair.ofNat (nRt i j)))
      (corner.trialVec 3 4 1 8 dRt gRt)).oneValue
    (BPair.ofNat (corner.magFold 3 4 1 8 dRt gRt nRt)) := by
  decide +kernel

example : 1 ≤ 3 :=
  corner.rayleigh_count tSite (idMat 3)
    ((1007574152 : Pos) + (1 : Pos)) (50421 : Pos) 3 tSplit
    (corner.trialVec 3 4 1 8 dRt gRt) (by decide +kernel) tCount
    (by decide +kernel)

/-! The drift's two arithmetic closes, one decided instance each. -/

example : 2 * 1
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
  corner.level_drift 0 1 1 1 1 1 1 1 1 2 (by decide +kernel)
    (by decide +kernel)

example : 2 * 1
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

example : (1 : Nat) + 1 = 2 := by decide +kernel

example : ¬ (100 * ground.prodOver (fun _ => 2)
      (List.range (2 * 0 + 4))
    ≤ ground.prodOver (fun _ => 2) (List.range (2 * 0 + 4))
      * ground.prodOver (fun _ => 1) (List.range (2 * 0 + 4))
      * 1) := by decide +kernel

example : ¬ (2 * 1
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

example : ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (3 : Pos) 2 * (1 : Pos) * ground.Pos.pow (1 : Pos) 2 :=
  corner.rate_close 2 (2 : Pos) (1 : Pos) (3 : Pos) (1 : Pos) (1 : Pos) (1 : Pos) (1 : Pos)
    (by decide +kernel) (by decide +kernel)

example : ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (3 : Pos) 2 * (1 : Pos) * ground.Pos.pow (1 : Pos) 2 := by
  decide +kernel

/-! The move cap's two binders, each refused at its own fixture with
the co-binder decided true beside it. -/

private def dMv : Nat → Nat := ground.getAt 0 [1, 1]

private def gMv : Nat → Nat := ground.getAt 0 [0, 4]

private def nMv : Nat → Nat → Nat := fun i =>
  ground.getAt 0 (ground.getAt [] [[0, 1], [0, 0]] i)

example : ¬ (∀ i, i < 2 → ∀ j, j < 2 → 0 < nMv i j →
    gMv j ≤ gMv i + 2) := by decide +kernel

example : ∀ i, i < 2 → gMv i + 2 ≤ 4 →
    ground.famFold Nat.add 0 (fun j => nMv i j * dMv j)
        (List.range 2)
      = 1 * dMv i := by decide +kernel

example : ¬ (1 * 1 * 1 * corner.pairFold 2 4 1 2 dMv gMv
    ≤ 2 * 2 * corner.magFold 2 4 1 2 dMv gMv nMv
      + 1 * 1 * 1 * corner.topFold 2 4 1 2 dMv gMv) := by
  decide +kernel

private def dDm : Nat → Nat := ground.getAt 0 [1, 1]

private def gDm : Nat → Nat := ground.getAt 0 [0, 2]

private def nDm : Nat → Nat → Nat := fun i =>
  ground.getAt 0 (ground.getAt [] [[0, 0], [0, 1]] i)

example : ∀ i, i < 2 → ∀ j, j < 2 → 0 < nDm i j →
    gDm j ≤ gDm i + 2 := by decide +kernel

example : ¬ (∀ i, i < 2 → gDm i + 2 ≤ 2 →
    ground.famFold Nat.add 0 (fun j => nDm i j * dDm j)
        (List.range 2)
      = 1 * dDm i) := by decide +kernel

example : ¬ (1 * 1 * 1 * corner.pairFold 2 2 1 2 dDm gDm
    ≤ 2 * 2 * corner.magFold 2 2 1 2 dDm gDm nDm
      + 1 * 1 * 1 * corner.topFold 2 2 1 2 dDm gDm) := by
  decide +kernel

/-! The boundary cap's certificate comparison, refused at the
reversed scale pair with the per-key counts decided true. -/

private def dTp : Nat → Nat := ground.getAt 0 [5]

private def gTp : Nat → Nat := ground.getAt 0 [4]

example : ∀ k, k ≤ 4 →
    ground.famFold Nat.add 0
        (fun i => if gTp i == k then dTp i else 0) (List.range 1)
      ≤ 1 * ground.prodOver (fun _ => k + 1) (List.range 1) := by
  decide +kernel

example : ¬ (2 * 1 * (1 * 1)
    * ground.prodOver (fun _ => 4 + 1) (List.range (2 * 1))
    * ground.prodOver (fun _ => 7) (List.range (2 * 4)) * 8
  ≤ 1 * ground.prodOver (fun _ => 8) (List.range (2 * 4))) := by
  decide +kernel

example : ¬ (7 * 7 * 1 * corner.topFold 1 4 7 8 dTp gTp
    ≤ 1 * ground.prodOver (fun _ => 8)
        (List.range (2 * 4 + 1))) := by decide +kernel

/-! The boundary cap's top-key count read, refused at the heavy
key with the under-key read and the certificate comparison decided
true. -/

private def dTc : Nat → Nat := ground.getAt 0 [1000000]

private def gTc : Nat → Nat := ground.getAt 0 [4]

example : ¬ (ground.famFold Nat.add 0
      (fun i => if gTc i == 4 then dTc i else 0) (List.range 1)
    ≤ 1 * ground.prodOver (fun _ => 4 + 1) (List.range 0)) := by
  decide +kernel

example : ground.famFold Nat.add 0
      (fun i => if gTc i == 4 - 1 then dTc i else 0) (List.range 1)
    ≤ 1 * ground.prodOver (fun _ => 4 - 1 + 1) (List.range 0) := by
  decide +kernel

example : 2 * 1 * (1 * 1)
    * ground.prodOver (fun _ => 4 + 1) (List.range (2 * 0))
    * ground.prodOver (fun _ => 1) (List.range (2 * 4)) * 8
  ≤ 7 * ground.prodOver (fun _ => 8) (List.range (2 * 4)) := by
  decide +kernel

example : ¬ (1 * 1 * 1 * corner.topFold 1 4 1 8 dTc gTc
    ≤ 7 * ground.prodOver (fun _ => 8)
        (List.range (2 * 4 + 1))) := by decide +kernel

/-! The electric cap's two binders, the Casimir comparison and the
per-key counts, each refused with the other decided true. -/

private def dEc : Nat → Nat := ground.getAt 0 [1]

private def gEc : Nat → Nat := ground.getAt 0 [0]

private def eEc : Nat → Nat := ground.getAt 0 [1000]

example : ¬ (∀ i, i < 1 → eEc i * 1 ≤ 1 * (gEc i * gEc i + 1)) := by
  decide +kernel

example : ∀ k, k ≤ 0 →
    ground.famFold Nat.add 0
        (fun i => if gEc i == k then dEc i else 0) (List.range 1)
      ≤ 1 * ground.prodOver (fun _ => k + 1) (List.range 0) := by
  decide +kernel

example : ¬ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3)) * 1
      * corner.elecFold 1 0 1 2 dEc gEc eEc
    ≤ 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
      * ground.prodOver (fun _ => 2)
          (List.range (2 * 0 + (2 * 0 + 3)))) := by decide +kernel

private def dCt : Nat → Nat := ground.getAt 0 [1, 9]

private def gCt : Nat → Nat := ground.getAt 0 [0, 0]

private def eCt : Nat → Nat := ground.getAt 0 [1, 1]

example : ∀ i, i < 2 → eCt i * 1 ≤ 1 * (gCt i * gCt i + 1) := by
  decide +kernel

example : ¬ (∀ k, k ≤ 0 →
    ground.famFold Nat.add 0
        (fun i => if gCt i == k then dCt i else 0) (List.range 2)
      ≤ 1 * ground.prodOver (fun _ => k + 1) (List.range 0)) := by
  decide +kernel

example : ¬ (ground.prodOver (fun _ => 1) (List.range (2 * 0 + 3)) * 1
      * corner.elecFold 2 0 1 2 dCt gCt eCt
    ≤ 1 * (1 * 1) * ground.rise 1 (2 * 0 + 2)
      * ground.prodOver (fun _ => 2)
          (List.range (2 * 0 + (2 * 0 + 3)))) := by decide +kernel

/-! The vacuum floor's two vacuum reads, the key and the dimension,
each refused at its own fixture. -/

private def dVk : Nat → Nat := ground.getAt 0 [1]

private def gVk : Nat → Nat := ground.getAt 0 [2]

example : ¬ gVk 0 = 0 := by decide +kernel

example : dVk 0 = 1 := by decide +kernel

example : ¬ (ground.prodOver (fun _ => 3) (List.range (2 * 2))
    ≤ corner.pairFold 1 2 1 3 dVk gVk) := by decide +kernel

private def dVd : Nat → Nat := ground.getAt 0 [0]

private def gVd : Nat → Nat := ground.getAt 0 [0]

example : ¬ dVd 0 = 1 := by decide +kernel

example : gVd 0 = 0 := by decide +kernel

example : ¬ (ground.prodOver (fun _ => 3) (List.range (2 * 2))
    ≤ corner.pairFold 1 2 1 3 dVd gVd) := by decide +kernel

/-! The vacuum floor's window binder: a vacuum key past the family
refuses the floor, the key and dimension reads holding at the
off-family defaults. -/

private def dVw : Nat → Nat := ground.getAt 1 [0]

private def gVw : Nat → Nat := ground.getAt 0 [5]

example : ¬ (1 < 1) := by decide +kernel

example : gVw 1 = 0 := by decide +kernel

example : dVw 1 = 1 := by decide +kernel

example : ¬ (ground.prodOver (fun _ => 3) (List.range (2 * 2))
    ≤ corner.pairFold 1 2 1 3 dVw gVw) := by decide +kernel

/-! The rate close's two arithmetic binders, the drift comparison
and the bracket, each refused with the other decided true. -/

example : ¬ ((100 : Pos) * (1 : Pos) ≤ (1 : Pos) * (1 : Pos) * (1 : Pos)) := by
  decide +kernel

example : ground.Pos.pow (1 : Pos) 2 * (1 : Pos)
    ≤ (1 : Pos) * ground.Pos.pow (1 : Pos) 2 := by decide +kernel

example : ¬ (ground.Pos.pow (100 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (1 : Pos) 2 * (1 : Pos)
      * ground.Pos.pow (1 : Pos) 2) := by decide +kernel

example : (2 : Pos) * (1 : Pos) ≤ (1 : Pos) * (2 : Pos) * (1 : Pos) := by
  decide +kernel

example : ¬ (ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ (1 : Pos) * ground.Pos.pow (1 : Pos) 2) := by decide +kernel

example : ¬ (ground.Pos.pow (2 : Pos) 2 * (1 : Pos)
    ≤ ground.Pos.pow (1 : Pos) 2 * (1 : Pos)
      * ground.Pos.pow (1 : Pos) 2) := by decide +kernel
