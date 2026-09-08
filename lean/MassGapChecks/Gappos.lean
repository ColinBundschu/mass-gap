import MassGap.Gappos
/-!
The check module for `thm:gappos` clause (v): the batteries re-read
the counting sandwich and the window's transport by kernel `decide`
at order-one cells, each shared datum named once and consumed by
term at every route.

The first cell: the unit gram `G = [1]`, the coupling `v`'s pencil
`H = [5]` against the coupling `v'`'s `H' = [3]` at the site datum
`S = [2]`, the tie `H = H' + S` an entrywise read, and the width
`ρ = 2` capping `S` two-sidedly — `ρG − S` at the sum's unit, its
split the kernel block, and `ρG + S = [4]` at one positive block, so
the cap sits tight at its upper side.  The sandwich there:
`count_v⟨a : ρ⟩ ≤ count_{v'}(a)` at the levels `⟨10 : 1⟩` (one
against one) and `⟨6 : 1⟩` (naught against one, the lower comparison
strict), and `count_{v'}(a) ≤ count_v(a + ρ)` at the level `⟨6 : 1⟩`
(one against one, the tight cap's equality).  The second cell holds
the upper comparison's strict instance: the site datum `[1]` against
the pencil `[4]` at the same width caps with slack on both sides,
and at the level `⟨4 : 1⟩` the `v'`-count naught sits strictly below
the raised `v`-count one.

The transport: the coupling `v`'s flat window at the anchor
`⟨7 : 1⟩` and the top `⟨13 : 1⟩`, both counts one, whose margin
`7 + 2 + (1 + 2) = 12 < 14` absorbs the width twice over; the
crossed pair's difference read at `v'`, the margin's own distance;
and the coupling `v'`'s window at the crossed anchor `⟨9 : 1⟩` and
the crossed top `⟨13 : 3⟩`, both counts one, landed by
`flat_transport` beside its own `decide`.

The committed refusals, each named to its binder: the cap's upper
split at the site datum `[4]` against the same width, its pencil
`[7]` keeping the tie while `ρG − S` reads the lower side and the
cap refuses there, the lower split holding; the cap's lower split at
the site datum `[-4]`, its pencil `[-1]` keeping the tie and
`ρG − S = [6]` its upper side while `ρG + S = [-2]` reads the lower
side and the cap refuses — the sandwich's lower conclusion false at
the level `⟨3 : 1⟩`, one against naught; the tie at the pencil `[0]`
against `H' + S = [5]`, the cap standing while the entrywise read
refuses and the lower conclusion is false at the level `⟨4 : 1⟩`;
the margin at a window whose top is `⟨9 : 1⟩`, the two transported
counts holding at one while the crossed pair's order refuses; and
the tie at the transport, the `v'`-pencil `[9]` breaking
`H = H' + S` with every count datum standing — the crossed anchor
reads naught against the window's one and the transported window
refuses at its first conjunct.  At the unit gram the margin forces
the crossed pair's difference read, so an isolating forge of the
transport's difference binder is unconstructible at these cells —
the recorded class of `MassGapChecks/Flatstep.lean`'s joint tie.

The cell tier: one order-one cell at the free cell's carrier over
`E = [5]`, `M = [-1]` and the unit gram — the level pair
`⟨13 : 1⟩ < ⟨17 : 1⟩` at the values `12` and `16`, the carriers
`τ² − 7` and `τ² − 11` at the gap four — on the segment `[0, 1]`
from the free end, both at count one, each with its pivot cover at
the priced side read and the free end's own sample; `cellRead`,
`cellsRead` and `cellsTop` decided, the pair `[1 : 2]` under the gap
and doubled under it (`gapsAt`, read at the member through
`gapsAt_mem`) with `[2 : 1]` refused.  `point_flat` carries the
window to the point `[1 : 2]`'s ray `[4 : 1]`, the pencil `21` at
the site data `-27` and `-43`, beside its own `decide`.  The
refusals: the sample's split forged onto a positive block, the gap
one beyond the level tie, the vacant count, the foot shifted beyond
the cell's top, and the point `[3 : 1]` beyond the list's top past
the anchor carrier's root at `√7`, the anchor's count the sum's unit
there and the window false.

The ray tier at the one list: the ray `[1 : 1]` at the top `[1 : 1]`,
the cap `W = 2` and the scale `q = 48` — the neighbor `p = 47`, the
gap `95`, the width `190` and the transported gap `8836` pinned as
data, the pair `[1 : 2]` doubled under the cell's gap reading
`4·48² ≤ 2·8836` and the window at the ray's pencil scaled by `48²`
at the shifted levels, the site data `-14014` and `-22850`, through
`ray_flat` beside their own `decide`.  The refusals: the pair
`[1 : 1]` doubled beyond the gap with its scaled read false against
`8836`, and the ray `[1 : 8]` beyond the top's square, the neighbor
`135` past the list and the anchor's count the sum's unit at
`τ² = 8`, the window false; the scale's two reads and the cap are the
tex's stated frame (`thm:gappos`(v)'s `q` and `thm:truncation`'s
cap), the cap's own refusals `flat_transport`'s above.

The priced cap at the identity gram: the order-two datum
`[[0, -1], [-1, 0]]` capped entrywise at one, the scaled identity at
`ρ = 2` clearing `o·e = 2`, the sum and the site datum each positive
semidefinite through `capId_hi` and `capId_lo` beside their own
`decide`; the clearing's binder refused at `ρ = 1` against the
entries `-2`, the sum indefinite, and the cap's at the entries `-3`
against the cap one.

The cutoff's price: the two-block window `[[2,1],[1,10]]` at unit
grams, the magnetic datum `[[-1,1],[1,-1]]` capped at the width two
with the polarization tie at the cofactor `4·1 = 2²`, the removed
block's electric diagonal eleven at or above the cutoff seven with
the floor tie `1 + 4 + 2 + 1 = 7 + 1`; the head's vacant cut at the
cofactor-raised level closes the window's own cut at the level
(`truncCut`), beside its own `decide`.  The refusals, each named to
its binder with the siblings pinned holding and the conclusion
false: the compression's vacant cut at the level three, where the
head's count occupies; the polarization tie at the width four
against the witness one, `ς c_W = 1` parting from `W² = 16`; the
magnetic cap at the coupling block widened to five, `WG − M` on its
lower side while the tie and both vacant cuts stand; and the
cutoff floor at the widths four, the tie forcing the cutoff nine
while the removed diagonal three sits below it.

The window's cut: at the free window `diag(0, 12, 32)` the one
located root list reads both ways — the count identity at the
window's top level eleven, counting the ground alone, and the
diagonalizing congruence at the identity — and `windowCut`
lands the cut tie whole at the edge `[8 : 1]`, beside its own
`decide`; at the edge sixteen the top level's count reads two
against the ground's one — the top-count binder's refusal, the
spectral read false there.
-/

open ground elim inertia certconstruct flatstep gappos cellcount

/-- The unit gram at order one. -/
private def gU : Mat := [[⟨2, 1⟩]]

/-- The coupling `v`'s pencil, the level five. -/
private def hV : Mat := [[⟨6, 1⟩]]

/-- The coupling `v'`'s pencil, the level three. -/
private def hW : Mat := [[⟨4, 1⟩]]

/-- The first cell's site datum, the level two. -/
private def sD : Mat := [[⟨3, 1⟩]]

private def sp1 (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩

private def spK : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩

/-! The first cell's two standing reads, named once: the tie
`H = H' + S` entrywise and the two-sided cap at the width two, its
upper side tight — the difference at the sum's unit, read by the
kernel block. -/

private theorem tie1 : matOneValue hV (matAdd hW sD) := by decide +kernel
private theorem cap1 : capAt sD (matScale 2 gU) spK (sp1 ⟨5, 1⟩) := by
  decide +kernel

/-! The lower comparison at the level `⟨10 : 1⟩`: the count at `v`
of the level raised by the width and the count at `v'` of the level
itself both read one. -/

private theorem cVa : countAtPair hV gU 10 (1 + 2) 1 (sp1 ⟨1, 3⟩) := by
  decide +kernel
private theorem cWa : countAtPair hW gU 10 1 1 (sp1 ⟨1, 7⟩) := by
  decide +kernel

example : 1 ≤ 1 :=
  sandwich_lo hV hW sD gU 2 10 1 1 1 (sp1 ⟨1, 3⟩) (sp1 ⟨1, 7⟩) spK
    (sp1 ⟨5, 1⟩) tie1 cap1 cVa cWa

/-! The lower comparison strict at the level `⟨6 : 1⟩`: the raised
level sits above the site at `v` and reads naught, the level itself
below it at `v'` and reads one. -/

private theorem cVb : countAtPair hV gU 6 (1 + 2) 0 (sp1 ⟨3, 1⟩) := by
  decide +kernel
private theorem cWb : countAtPair hW gU 6 1 1 (sp1 ⟨1, 3⟩) := by
  decide +kernel

example : 0 ≤ 1 :=
  sandwich_lo hV hW sD gU 2 6 1 0 1 (sp1 ⟨3, 1⟩) (sp1 ⟨1, 3⟩) spK
    (sp1 ⟨5, 1⟩) tie1 cap1 cVb cWb

/-! The upper comparison at the level `⟨6 : 1⟩`: the count at `v'`
of the level and the count at `v` of the level's first member raised
by the width both read one, the tight cap's equality. -/

private theorem cVc : countAtPair hV gU (6 + 2) 1 1 (sp1 ⟨1, 3⟩) := by
  decide +kernel

example : 1 ≤ 1 :=
  sandwich_hi hV hW sD gU 2 6 1 1 1 (sp1 ⟨1, 3⟩) (sp1 ⟨1, 3⟩) spK
    (sp1 ⟨5, 1⟩) tie1 cap1 cWb cVc

/-! The second cell, the upper comparison's strict instance: the
site datum `[1]` at the pencil `[4]` caps with slack on both sides
of the same width, and at the level `⟨4 : 1⟩` the `v'`-count naught
sits strictly below the raised `v`-count one. -/

private def sD2 : Mat := [[⟨2, 1⟩]]
private def hV2 : Mat := [[⟨5, 1⟩]]

private theorem tie2 : matOneValue hV2 (matAdd hW sD2) := by decide +kernel
private theorem cap2 : capAt sD2 (matScale 2 gU) (sp1 ⟨2, 1⟩)
    (sp1 ⟨4, 1⟩) := by decide +kernel
private theorem cWd : countAtPair hW gU 4 1 0 spK := by decide +kernel
private theorem cVd : countAtPair hV2 gU (4 + 2) 1 1 (sp1 ⟨1, 2⟩) := by
  decide +kernel

example : 0 ≤ 1 :=
  sandwich_hi hV2 hW sD2 gU 2 4 1 1 0 (sp1 ⟨1, 2⟩) spK (sp1 ⟨2, 1⟩)
    (sp1 ⟨4, 1⟩) tie2 cap2 cWd cVd

/-! The coupling `v`'s flat window at the anchor `⟨7 : 1⟩` and the
top `⟨13 : 1⟩`, the crossed pair's difference read at `v'` — the
margin's own distance — and the coupling `v'`'s two crossed counts. -/

private theorem winV : vacFlat hV gU 7 1 13 1 1 (sp1 ⟨1, 2⟩)
    (sp1 ⟨1, 8⟩) := by decide +kernel

private theorem crossD : splitRead
    (siteDatum
      (siteDatum (matAdd hW (matScale 1 gU)) (matScale (7 + 2) gU))
      (siteDatum (matAdd hW (matScale (1 + 2) gU)) (matScale 13 gU)))
    (sp1 ⟨3, 1⟩) := by decide +kernel

private theorem cWanch : countAtPair hW gU (7 + 2) 1 1 (sp1 ⟨1, 6⟩) := by
  decide +kernel
private theorem cWtop : countAtPair hW gU 13 (1 + 2) 1 (sp1 ⟨1, 8⟩) := by
  decide +kernel

example : vacFlat hW gU (7 + 2) 1 13 (1 + 2) 1 (sp1 ⟨1, 6⟩) (sp1 ⟨1, 8⟩) :=
  flat_transport hV hW sD gU 2 7 1 13 1 1 1 1
    (sp1 ⟨1, 2⟩) (sp1 ⟨1, 8⟩) (sp1 ⟨1, 6⟩) (sp1 ⟨1, 8⟩) (sp1 ⟨3, 1⟩)
    spK (sp1 ⟨5, 1⟩) tie1 cap1 winV (by decide +kernel) crossD
    (by decide +kernel) cWanch cWtop

example : vacFlat hW gU (7 + 2) 1 13 (1 + 2) 1 (sp1 ⟨1, 6⟩) (sp1 ⟨1, 8⟩) := by
  decide +kernel

/-! The cap's upper binder: at the site datum `[4]` against the same
width the pencil `[7]` keeps the tie, the cap's lower split holds at
`ρG + S = [6]`, and the upper datum reads the lower side — the cap
refusing there. -/

private def sF : Mat := [[⟨5, 1⟩]]
private def hVc : Mat := [[⟨8, 1⟩]]

example : matOneValue hVc (matAdd hW sF) := by decide +kernel
example : splitRead (siteDatum (matScale 2 gU) sF) (sp1 ⟨1, 3⟩) := by
  decide +kernel
example : ¬ psdAt (sp1 ⟨1, 3⟩) := by decide +kernel
example : splitRead (matAdd (matScale 2 gU) sF) (sp1 ⟨7, 1⟩) := by
  decide +kernel
example : psdAt (sp1 ⟨7, 1⟩) := by decide +kernel
example : ¬ capAt sF (matScale 2 gU) (sp1 ⟨1, 3⟩) (sp1 ⟨7, 1⟩) := by
  decide +kernel

/-! The cap's lower binder: at the site datum `[-4]` the pencil
`[-1]` keeps the tie and `ρG − S = [6]` reads its upper side, while
`ρG + S = [-2]` reads the lower side and the cap refuses — and the
lower comparison's conclusion is false at the level `⟨3 : 1⟩`, the
`v`-count at the raised level one against the `v'`-count naught. -/

private def sD3 : Mat := [[⟨1, 5⟩]]
private def hV3 : Mat := [[⟨1, 2⟩]]

example : matOneValue hV3 (matAdd hW sD3) := by decide +kernel
example : splitRead (siteDatum (matScale 2 gU) sD3) (sp1 ⟨7, 1⟩) := by
  decide +kernel
example : psdAt (sp1 ⟨7, 1⟩) := by decide +kernel
example : splitRead (matAdd (matScale 2 gU) sD3) (sp1 ⟨1, 3⟩) := by
  decide +kernel
example : ¬ psdAt (sp1 ⟨1, 3⟩) := by decide +kernel
example : ¬ capAt sD3 (matScale 2 gU) (sp1 ⟨7, 1⟩) (sp1 ⟨1, 3⟩) := by
  decide +kernel
example : countAtPair hV3 gU 3 (1 + 2) 1 (sp1 ⟨1, 2⟩) := by decide +kernel
example : countAtPair hW gU 3 1 0 (sp1 ⟨2, 1⟩) := by decide +kernel

/-! The tie's own binder: the pencil `[0]` against `H' + S = [5]`.
The cap stands and the lower comparison's conclusion is false at the
level `⟨4 : 1⟩` — the `v`-count at the raised level one against the
`v'`-count naught — while the entrywise read refuses. -/

private def hV0 : Mat := [[⟨1, 1⟩]]

example : ¬ matOneValue hV0 (matAdd hW sD) := by decide +kernel
example : countAtPair hV0 gU 4 (1 + 2) 1 (sp1 ⟨1, 2⟩) := by decide +kernel
example : countAtPair hW gU 4 1 0 spK := by decide +kernel

/-! The margin's own binder: the window's top moved to `⟨9 : 1⟩`,
one count there and the coupling `v`'s window standing.  The two
transported counts read one at the crossed anchor and the crossed
top, while the crossed pair's order `12 < 10` refuses. -/

example : vacFlat hV gU 7 1 9 1 1 (sp1 ⟨1, 2⟩) (sp1 ⟨1, 4⟩) := by
  decide +kernel
example : countAtPair hW gU 9 (1 + 2) 1 (sp1 ⟨1, 4⟩) := by decide +kernel
example : ¬ vacFlat hW gU (7 + 2) 1 9 (1 + 2) 1 (sp1 ⟨1, 6⟩) (sp1 ⟨1, 4⟩) := by
  decide +kernel

/-! The tie's binder at the transport: the `v'`-pencil `[9]` breaks
`H = H' + S` while every count datum stands — the crossed anchor
sits above its level and reads naught against the window's one, the
crossed top reading one and the crossed pair ordered — and the
transported window refuses at its first conjunct. -/

private def hWf : Mat := [[⟨10, 1⟩]]

example : ¬ matOneValue hV (matAdd hWf sD) := by decide +kernel
example : countAtPair hWf gU (7 + 2) 1 0 (sp1 ⟨2, 1⟩) := by decide +kernel
example : countAtPair hWf gU 13 (1 + 2) 1 (sp1 ⟨1, 2⟩) := by decide +kernel
example : ¬ vacFlat hWf gU (7 + 2) 1 13 (1 + 2) 1 (sp1 ⟨2, 1⟩) (sp1 ⟨1, 2⟩) := by
  decide +kernel

/-! The cell tier's fixture: the order-one carrier at `E = [5]`,
`M = [-1]` and the unit gram — the level datum at the constant key
and the magnetic member's balance partner `+1` at the `τ²` key, so
the level-`⟨13 : 1⟩` carrier reads `τ² − 7` and the level-`⟨17 : 1⟩`
carrier `τ² − 11` — over the segment `[0, 1]` from the free end,
both carriers on their lower side there at count one, the covers one
designated entry each at the bound `[2 : 1]` and the clearing one,
the sample the free end itself. -/

private def mA : elim.Mat := [[⟨6, 1⟩]]
private def mM : elim.Mat := [[⟨1, 2⟩]]
private def gI : elim.Mat := [[⟨2, 1⟩]]

private def cfoot : CPair := ⟨BPair.unit, 1⟩
private def ctop : CPair := ⟨BPair.ofPos 1, 1⟩

private def cvL : Cover :=
  Cover.one ctop 0 false ⟨3, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

private def cellF : Cell 1 :=
  ⟨cfoot, ctop, 13, 1, 17, 1, 4, cvL, cvL, BPair.unit, 1, 1,
   inertia.mkSplit 1 (evalPC (freecell.freePMat mA mM gI 13 1) BPair.unit 1 2),
   inertia.mkSplit 1 (evalPC (freecell.freePMat mA mM gI 17 1) BPair.unit 1 2)⟩

example : cellRead mA mM gI cellF := by decide +kernel
example : cellsRead mA mM gI cfoot [cellF] := by decide +kernel
example : cellsTop cfoot [cellF] = ctop := rfl

/-! The pair against the cell's gap four at `E₀ = 4`: `[1 : 2]` under
the gap and, doubled, under half of it; `[2 : 1]` refused. -/

example : gapsAt 4 1 2 [cellF] := by decide +kernel
example : gapsAt 4 (2 * 1) 2 [cellF] := by decide +kernel
example : ¬ gapsAt 4 2 1 [cellF] := by decide +kernel
example : 4 * 1 ≤ 2 * cellF.gp := gapsAt_mem (by decide +kernel : gapsAt 4 1 2 [cellF])
  (List.Mem.head [])

/-! The root coordinate's rays read their cells directly: at the
point `[1 : 2]` the ray `[4 : 1]`'s pencil `20 + 1 = 21` reads count
one at both levels scaled by four, the site data `-27` and `-43`,
through `point_flat` beside its own `decide`. -/

private def rayF : elim.Mat := pencil.rayH mA mM (2 * 2) (1 * 1)
private def sitA : elim.Mat :=
  siteDatum (matAdd rayF (matScale (2 * 2 * 1) gI)) (matScale (2 * 2 * 13) gI)
private def sitT : elim.Mat :=
  siteDatum (matAdd rayF (matScale (2 * 2 * 1) gI)) (matScale (2 * 2 * 17) gI)

private theorem rdA : splitRead sitA (inertia.mkSplit 1 sitA) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
private theorem rdT : splitRead sitT (inertia.mkSplit 1 sitT) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

example : matOneValue rayF [[⟨22, 1⟩]] := by decide +kernel
example : matOneValue sitA [[⟨1, 28⟩]] := by decide +kernel
example : matOneValue sitT [[⟨1, 44⟩]] := by decide +kernel

example : vacFlat rayF gI (2 * 2 * 13) (2 * 2 * 1) (2 * 2 * 17) (2 * 2 * 1) 1
    (inertia.mkSplit 1 sitA) (inertia.mkSplit 1 sitT) :=
  point_flat mA mM gI (by decide +kernel) (by decide +kernel) (by decide +kernel)
    cfoot cellF [] (by decide +kernel) 1 2 (by decide +kernel) (by decide +kernel)
    _ _ rdA rdT
example : vacFlat rayF gI (2 * 2 * 13) (2 * 2 * 1) (2 * 2 * 17) (2 * 2 * 1) 1
    (inertia.mkSplit 1 sitA) (inertia.mkSplit 1 sitT) := by decide +kernel

/-! The refusals, one per binder.  The list's read: the sample's
split forged onto a positive block, the level tie at a gap one
beyond, and the vacant count; the foot shifted beyond the cell's
top; and the point beyond the list's top, `[3 : 1]` past the anchor
carrier's root at `√7`, where the anchor's count reads the sum's
unit against the window's one — the conclusion false with the
membership refused. -/

example : ¬ cellRead mA mM gI { cellF with spA := sp1 ⟨3, 1⟩ } := by
  decide +kernel
example : ¬ cellRead mA mM gI { cellF with gp := 5 } := by decide +kernel
example : ¬ cellRead mA mM gI { cellF with g := 0 } := by decide +kernel
example : ¬ cellsRead mA mM gI ⟨BPair.ofNat 2, 1⟩ [cellF] := by decide +kernel

private def rayB : elim.Mat := pencil.rayH mA mM (1 * 1) (3 * 3)
private def sitB : elim.Mat :=
  siteDatum (matAdd rayB (matScale (1 * 1 * 1) gI)) (matScale (1 * 1 * 13) gI)

example : ¬ ((⟨BPair.ofPos 3, 1⟩ : CPair) ≤ cellsTop cfoot [cellF]) := by
  decide +kernel
example : splitRead sitB (inertia.mkSplit 1 sitB) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
example : inertia.revAt (inertia.mkSplit 1 sitB) = 0 := by decide +kernel
example : ¬ vacFlat rayB gI (1 * 1 * 13) (1 * 1 * 1) (1 * 1 * 17) (1 * 1 * 1) 1
    (inertia.mkSplit 1 sitB) (inertia.mkSplit 1 sitT) := by decide +kernel

/-! The further pair rays at the same list: the ray `[1 : 1]` at the
list's top `[1 : 1]`, the magnetic cap `W = 2` against the unit
gram, and the stated scale `q = (1 + 1)·4·2·(2 + 1) = 48`.  The
neighbor `p = 47` reads `47² < 48² ≤ 48²`, the weights' gap `95`,
the width `190`, and the transported gap `4·48² − 380 = 8836`, the
pair `[1 : 2]` doubled under the cell's gap reading `4·48² ≤ 2·8836`
at the scale; the window at the ray's pencil scaled by `48²` reads
count one at the shifted levels through `ray_flat` beside its own
`decide`. -/

private def spG1 : Split 1 := inertia.mkSplit 1 gI
private theorem rdG : splitRead gI spG1 :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
private def spU1 : Split 1 := inertia.mkSplit 1 (siteDatum (matScale 2 gI) mM)
private def spL1 : Split 1 := inertia.mkSplit 1 (matAdd (matScale 2 gI) mM)
private theorem capR : capAt mM (matScale 2 gI) spU1 spL1 := by decide +kernel
private theorem cellsR : cellsRead mA mM gI cfoot [cellF] := by decide +kernel
private theorem gapsR : gapsAt 4 (2 * 1) 2 [cellF] := by decide +kernel

example : rayQ 1 2 1 = 48 ∧ rayP 1 1 48 = 47 ∧ rayGap 1 1 48 = 95
    ∧ rayRho 1 1 48 2 = 190 ∧ rayGp 1 1 48 2 cellF [] = 8836 := by
  decide +kernel

example : 4 * (1 * 1) * (rayQ 1 2 1 * rayQ 1 2 1)
    ≤ 2 * rayGp 1 1 (rayQ 1 2 1) 2 cellF [] :=
  (ray_flat mA mM gI (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    spG1 rdG (by decide +kernel) 2 spU1 spL1 capR cellF [] cellsR
    4 1 2 gapsR 1 1 rfl 1 1 (by decide +kernel)).2.1
example : 4 * (1 * 1) * (rayQ 1 2 1 * rayQ 1 2 1)
    ≤ 2 * rayGp 1 1 (rayQ 1 2 1) 2 cellF [] := by decide +kernel

private def sitRa : elim.Mat :=
  siteDatum (matAdd (matScale (rayQ 1 2 1 * rayQ 1 2 1) (pencil.rayH mA mM 1 1))
      (matScale (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ay)) gI))
    (matScale (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ax)
      + rayRho 1 1 (rayQ 1 2 1) 2) gI)
private def sitRt : elim.Mat :=
  siteDatum (matAdd (matScale (rayQ 1 2 1 * rayQ 1 2 1) (pencil.rayH mA mM 1 1))
      (matScale (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ty)
        + rayRho 1 1 (rayQ 1 2 1) 2) gI))
    (matScale (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).tx)) gI)
private theorem rdRa : splitRead sitRa (inertia.mkSplit 1 sitRa) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
private theorem rdRt : splitRead sitRt (inertia.mkSplit 1 sitRt) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

example : matOneValue sitRa [[⟨1, 14015⟩]] := by decide +kernel
example : matOneValue sitRt [[⟨1, 22851⟩]] := by decide +kernel

example : vacFlat (matScale (rayQ 1 2 1 * rayQ 1 2 1) (pencil.rayH mA mM 1 1)) gI
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ax)
      + rayRho 1 1 (rayQ 1 2 1) 2)
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ay))
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).tx))
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ty)
      + rayRho 1 1 (rayQ 1 2 1) 2)
    (rayCell 1 1 (rayQ 1 2 1) cellF []).g (inertia.mkSplit 1 sitRa) (inertia.mkSplit 1 sitRt) :=
  (ray_flat mA mM gI (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    spG1 rdG (by decide +kernel) 2 spU1 spL1 capR cellF [] cellsR
    4 1 2 gapsR 1 1 rfl 1 1 (by decide +kernel)).2.2 _ _ rdRa rdRt
example : vacFlat (matScale (rayQ 1 2 1 * rayQ 1 2 1) (pencil.rayH mA mM 1 1)) gI
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ax)
      + rayRho 1 1 (rayQ 1 2 1) 2)
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ay))
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).tx))
    (1 * (rayQ 1 2 1 * rayQ 1 2 1 * (rayCell 1 1 (rayQ 1 2 1) cellF []).ty)
      + rayRho 1 1 (rayQ 1 2 1) 2)
    (rayCell 1 1 (rayQ 1 2 1) cellF []).g (inertia.mkSplit 1 sitRa) (inertia.mkSplit 1 sitRt) := by
  decide +kernel

/-! The ray tier's refusals.  The pair's binder: `[1 : 1]` doubled
sits beyond the cell's gap, and at the scale `48²` the transported
gap `8836` sits under `4·48² = 9216`, the pair's read false.  The
ray's binder: the ray `[1 : 8]` beyond the top's square, where the
neighbor `p = 135` sits past the list and the anchor carrier reads
its upper side at `τ² = 8`, the transported anchor count the sum's
unit against the cell's one. -/

example : ¬ gapsAt 4 (2 * 1) 1 [cellF] := by decide +kernel
example : ¬ (4 * (1 * 1) * (rayQ 1 2 1 * rayQ 1 2 1)
    ≤ 1 * rayGp 1 1 (rayQ 1 2 1) 2 cellF []) := by decide +kernel

example : ¬ (8 * (1 * 1) ≤ 1 * 1 * 1) := by decide +kernel
example : rayP 1 8 48 = 135 := by decide +kernel

private def sitXa : elim.Mat :=
  siteDatum (matAdd (matScale (48 * 48) (pencil.rayH mA mM 1 8))
      (matScale (1 * (48 * 48 * (rayCell 1 8 48 cellF []).ay)) gI))
    (matScale (1 * (48 * 48 * (rayCell 1 8 48 cellF []).ax) + rayRho 1 8 48 2) gI)
private def sitXt : elim.Mat :=
  siteDatum (matAdd (matScale (48 * 48) (pencil.rayH mA mM 1 8))
      (matScale (1 * (48 * 48 * (rayCell 1 8 48 cellF []).ty) + rayRho 1 8 48 2) gI))
    (matScale (1 * (48 * 48 * (rayCell 1 8 48 cellF []).tx)) gI)

example : splitRead sitXa (inertia.mkSplit 1 sitXa) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
example : splitRead sitXt (inertia.mkSplit 1 sitXt) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
example : inertia.revAt (inertia.mkSplit 1 sitXa) = 0 := by decide +kernel
example : ¬ vacFlat (matScale (48 * 48) (pencil.rayH mA mM 1 8)) gI
    (1 * (48 * 48 * (rayCell 1 8 48 cellF []).ax) + rayRho 1 8 48 2)
    (1 * (48 * 48 * (rayCell 1 8 48 cellF []).ay))
    (1 * (48 * 48 * (rayCell 1 8 48 cellF []).tx))
    (1 * (48 * 48 * (rayCell 1 8 48 cellF []).ty) + rayRho 1 8 48 2)
    (rayCell 1 8 48 cellF []).g (inertia.mkSplit 1 sitXa) (inertia.mkSplit 1 sitXt) := by
  decide +kernel

/-! The priced cap at the identity gram (`capId_lo`, `capId_hi`):
the order-two datum `[[0, -1], [-1, 0]]` capped entrywise at one,
the scaled identity at `ρ = 2` clearing `o·e = 2`, the sum and the
site datum each positive semidefinite, through the theorems beside
their own `decide`; the clearing's binder refuses at `ρ = 1` against
the entries `-2`, the sum indefinite, and the cap's at the entries
`-3` against the cap one at `ρ = 2`. -/

private def sCap : elim.Mat := [[BPair.unit, ⟨1, 2⟩], [⟨1, 2⟩, BPair.unit]]
private def sCap2 : elim.Mat := [[BPair.unit, ⟨1, 3⟩], [⟨1, 3⟩, BPair.unit]]
private def sCap3 : elim.Mat := [[BPair.unit, ⟨1, 4⟩], [⟨1, 4⟩, BPair.unit]]

example : inertia.psdAt (inertia.mkSplit 2 (matAdd (matScale 2 (idMat 2)) sCap)) :=
  capId_hi 2 sCap ⟨2, 1⟩ 2 _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel))
example : inertia.psdAt (inertia.mkSplit 2 (matAdd (matScale 2 (idMat 2)) sCap)) := by
  decide +kernel
example : inertia.psdAt (inertia.mkSplit 2 (siteDatum (matScale 2 (idMat 2)) sCap)) :=
  capId_lo 2 sCap ⟨2, 1⟩ 2 _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel))
example : inertia.psdAt (inertia.mkSplit 2 (siteDatum (matScale 2 (idMat 2)) sCap)) := by
  decide +kernel

example : magCap ⟨3, 1⟩ sCap2 := by decide +kernel
example : ¬ (BPair.ofNat 2 * ⟨3, 1⟩ ≤ BPair.ofPos 1) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2 (matAdd (matScale 1 (idMat 2)) sCap2)) := by
  decide +kernel
example : ¬ magCap ⟨2, 1⟩ sCap3 := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2 (matAdd (matScale 2 (idMat 2)) sCap3)) := by
  decide +kernel

/-! The cutoff's price: the two-block window at unit grams, the
magnetic datum capped at the width two, the polarization tie at the
cofactor `4·1 = 2²` — the head's vacant cut at the raised level
closing the window's own. -/

private def bU : BPair := BPair.unit
private def pH : Mat := [[⟨3, 1⟩]]
private def gH : Mat := [[⟨2, 1⟩]]
private def qR : Mat := [[⟨11, 1⟩]]
private def gR : Mat := [[⟨2, 1⟩]]
private def bC : Mat := [[⟨2, 1⟩]]
private def hF : Mat := inertia.blockJoin pH bC qR
private def gF : Mat := inertia.blockJoin gH (elim.nullMat 1 1) gR
private def mH : Mat := [[⟨1, 2⟩]]
private def mR : Mat := [[⟨1, 2⟩]]
private def mF : Mat := inertia.blockJoin mH bC mR

private def tT : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [bU, ⟨4, 1⟩]], rfl⟩
private def twT : SqMat 2 := ⟨[[⟨4, 1⟩, ⟨1, 2⟩], [bU, ⟨2, 1⟩]], rfl⟩
private def spT (a b : BPair) : Split 2 :=
  ⟨tT, twT, [.one a, .one b], 0, rfl⟩
private def tSh : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 2⟩], [bU, ⟨2, 1⟩]], rfl⟩
private def twSh : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [bU, ⟨2, 1⟩]], rfl⟩
private def spShK (a : BPair) : Split 2 := ⟨tSh, twSh, [.one a], 1, rfl⟩

private theorem capF : capAt mF (matScale 2 gF) (spT ⟨4, 1⟩ ⟨25, 1⟩)
    (spShK ⟨2, 1⟩) := by decide +kernel

/-- The removed block's electric diagonal, the level eleven. -/
private def deR : Mat := [[⟨12, 1⟩]]

private def siteF : Mat :=
  siteDatum (matAdd hF (matScale 1 gF)) (matScale 1 gF)
private def siteB2 : Mat := blockJoin
  (siteDatum (matAdd pH (matScale 1 gH)) (matScale (1 + 1) gH))
  (elim.nullMat 1 1)
  (siteDatum (matAdd qR (matScale 1 gR)) (matScale (1 + 4) gR))
private def siteDf : Mat := siteDatum siteF siteB2

private theorem rdF : splitRead siteF (inertia.mkSplit 2 siteF) :=
  inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel)
private theorem rdB2 : splitRead siteB2 (inertia.mkSplit 2 siteB2) :=
  inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel)
private theorem rdDf : splitRead siteDf (inertia.mkSplit 2 siteDf) :=
  inertia.mkSplit_read 2 _ (by decide +kernel) (by decide +kernel)

example : inertia.psdAt (inertia.mkSplit 2 siteF) :=
  truncCut (k := 1) (m := 1) hF gF mF mH mR pH gH qR deR gR bC
    1 1 1 2 4 7 1
    (spT ⟨4, 1⟩ ⟨25, 1⟩) (spShK ⟨2, 1⟩)
    (inertia.mkSplit 2 siteF) (inertia.mkSplit 2 siteB2)
    (inertia.mkSplit 2 siteDf)
    (sp1 ⟨2, 1⟩) (sp1 ⟨7, 1⟩) (sp1 ⟨5, 1⟩) (sp1 ⟨2, 1⟩) (sp1 ⟨2, 1⟩)
    capF
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rdF (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rdB2 rdDf

example : inertia.psdAt (inertia.mkSplit 2 siteF) := by decide +kernel

/-! The compression binder: at the level three the head's count
occupies at the raised level, refusing the vacant cut, and the
window's own datum reads one — the conclusion false. -/

example : ¬ countAtPair pH gH (3 + 1) 1 0 (sp1 ⟨2, 1⟩) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2
    (siteDatum (matAdd hF (matScale 1 gF)) (matScale 3 gF))) := by
  decide +kernel

/-! The polarization tie's own binder: at the width four against the
witness one and the cofactor one, `ς c_W = 1` parts from `W² = 16` —
the coupling one at unit-membered pencils, the cap at the width four
and both vacant cuts standing while the tie refuses and the
conclusion is false. -/

private def pHt : Mat := [[⟨2, 1⟩]]
private def qRt : Mat := [[⟨2, 1⟩]]
private def bCt : Mat := [[⟨3, 1⟩]]
private def hFt : Mat := blockJoin pHt bCt qRt
private def mHt : Mat := [[bU]]
private def mFt : Mat := blockJoin mHt bCt mHt

example : capAt mFt (matScale 4 gF)
    (inertia.mkSplit 2 (siteDatum (matScale 4 gF) mFt))
    (inertia.mkSplit 2 (matAdd (matScale 4 gF) mFt)) := by decide +kernel
example : countAtPair pHt gH (1 + 1) 1 0 (inertia.mkSplit 1 (siteDatum
    (matAdd pHt (matScale 1 gH)) (matScale (1 + 1) gH))) := by
  decide +kernel
example : countAtPair qRt gR (1 + 1) 1 0 (inertia.mkSplit 1 (siteDatum
    (matAdd qRt (matScale 1 gR)) (matScale (1 + 1) gR))) := by
  decide +kernel
example : ¬ matOneValue (matScale 1 (siteDatum
      (siteDatum (matAdd hFt (matScale 1 gF)) (matScale 1 gF))
      (blockJoin
        (siteDatum (matAdd pHt (matScale 1 gH)) (matScale (1 + 1) gH))
        (elim.nullMat 1 1)
        (siteDatum (matAdd qRt (matScale 1 gR)) (matScale (1 + 1) gR)))))
    (truncation.shiftSite 4 1 bCt gH gR) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2
    (siteDatum (matAdd hFt (matScale 1 gF)) (matScale 1 gF))) := by
  decide +kernel

/-! The magnetic cap's own binder: the coupling block widened to
five keeps the polarization tie at the cofactor `4·1 = 2²` and both
vacant cuts, while `WG − M` reads its lower side — the cap refusing
and the conclusion false. -/

private def bCc : Mat := [[⟨6, 1⟩]]
private def hFc : Mat := blockJoin pH bCc qR
private def mFc : Mat := blockJoin mH bCc mR

example : matOneValue (matScale 4 (siteDatum
      (siteDatum (matAdd hFc (matScale 1 gF)) (matScale 1 gF))
      (blockJoin
        (siteDatum (matAdd pH (matScale 1 gH)) (matScale (1 + 1) gH))
        (elim.nullMat 1 1)
        (siteDatum (matAdd qR (matScale 1 gR)) (matScale (1 + 4) gR)))))
    (truncation.shiftSite 2 4 bCc gH gR) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2
    (siteDatum (matScale 2 gF) mFc)) := by decide +kernel
example : ¬ capAt mFc (matScale 2 gF)
    (inertia.mkSplit 2 (siteDatum (matScale 2 gF) mFc))
    (inertia.mkSplit 2 (matAdd (matScale 2 gF) mFc)) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2
    (siteDatum (matAdd hFc (matScale 1 gF)) (matScale 1 gF))) := by
  decide +kernel

/-! The cutoff floor's own binder: at the widths four the floor tie
forces the cutoff nine at the witness gap one, and the removed
block's electric diagonal three sits below it — the diagonal's
at-or-above read refusing while the cap, the tie and the head's
vacant cut stand, the conclusion false. -/

private def pHr : Mat := [[⟨5, 1⟩]]
private def qRr : Mat := [[⟨4, 1⟩]]
private def bCr : Mat := [[⟨5, 1⟩]]
private def hFr : Mat := blockJoin pHr bCr qRr
private def mFr : Mat := blockJoin mHt bCr mHt

example : capAt mFr (matScale 4 gF)
    (inertia.mkSplit 2 (siteDatum (matScale 4 gF) mFr))
    (inertia.mkSplit 2 (matAdd (matScale 4 gF) mFr)) := by decide +kernel
example : matOneValue (matScale 4 (siteDatum
      (siteDatum (matAdd hFr (matScale 1 gF)) (matScale 1 gF))
      (blockJoin
        (siteDatum (matAdd pHr (matScale 1 gH)) (matScale (1 + 4) gH))
        (elim.nullMat 1 1)
        (siteDatum (matAdd qRr (matScale 1 gR)) (matScale (1 + 4) gR)))))
    (truncation.shiftSite 4 4 bCr gH gR) := by decide +kernel
example : countAtPair pHr gH (1 + 4) 1 0 (inertia.mkSplit 1 (siteDatum
    (matAdd pHr (matScale 1 gH)) (matScale (1 + 4) gH))) := by
  decide +kernel
example : (1 : Pos) + 4 + 4 + 1 = 9 + 1 := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 1
    (siteDatum qRr (matScale 9 gR))) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 2
    (siteDatum (matAdd hFr (matScale 1 gF)) (matScale 1 gF))) := by
  decide +kernel

/-! The window's cut at the free window `diag(0, 12, 32)`: the one
root list at both reads, the window's count at the level eleven the
ground's own, and the cut tie landed whole at the edge `[8 : 1]`. -/

private def et3 : Mat :=
  [[bU, bU, bU], [bU, ⟨13, 1⟩, bU], [bU, bU, ⟨33, 1⟩]]

private def id3 : SqMat 3 := ⟨idMat 3, by decide +kernel⟩

private def l3 : List (BPair × Pos × BPair) :=
  [(bU, 1, ⟨2, 1⟩), (⟨13, 1⟩, 1, ⟨2, 1⟩), (⟨33, 1⟩, 1, ⟨2, 1⟩)]

private def spCut3 : Split 3 :=
  inertia.mkSplit 3 (siteDatum (matScale 1 (matMul et3 et3))
    (matScale (4 * 2) et3))

private def spWt : Split 3 :=
  inertia.mkSplit 3 (siteDatum (matScale 1 et3) (matScale 11 (idMat 3)))

private theorem crt : split.countRead et3 (idMat 3)
    (l3.map (fun r => (r.1, r.2.1))) 11 1 spWt := by decide +kernel

example : speccut.cutTie et3 (l3.map (fun r => (r.1, r.2.1))) 4 2 1
    spCut3 :=
  windowCut et3 id3 id3 l3 4 2 1 1 (by decide +kernel)
    (by decide +kernel) 11 1 spWt crt (by decide +kernel)
    (by decide +kernel) spCut3 (by decide +kernel)

example : speccut.cutTie et3 (l3.map (fun r => (r.1, r.2.1))) 4 2 1
    spCut3 := by decide +kernel

/-! The top-count binder: at the edge sixteen the top level's count
reads two against the ground's one, and the spectral read is false
there — the window's cut refused at the wider edge. -/

example : ¬ (inertia.revAt (inertia.mkSplit 3
    (siteDatum (matScale 1 et3) (matScale 16 (idMat 3)))) = 1) := by
  decide +kernel
example : ¬ speccut.specRead (l3.map (fun r => (r.1, r.2.1))) 4 4 1 := by
  decide +kernel
