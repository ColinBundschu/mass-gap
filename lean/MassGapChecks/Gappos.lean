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

The cell tier: one order-one cell at the carrier
`levelPMat [5] [-1] [1]` over the segment `[2, 33/16]`, three level
carriers — the window's anchor `⟨3 : 1⟩` and top `⟨9 : 1⟩` each at
count one, and the level `⟨1 : 2⟩` positive semidefinite — each with
its pivot cover at the priced side read.  `cellcount.cellCount`
carries each sampled count from the lower endpoint to an interior
point, and `cellPsd` the vacant one, each beside its own `decide`.
The refusals: a point below the segment, where the membership
refuses and the anchor's count reads naught against the window's
one; the vacant sample forged onto the anchor carrier, whose count
one refuses it and whose target split refuses the
positive-semidefinite read; and the point `5/2` beyond the cell's
top, refusing the upper membership with the count occupied there.

The chain: two cells at the shared endpoint `33/16` on the
positive-semidefinite carrier, the second running to `17/8`, each
with its cover and its vacant sample at its foot; `chainPsd` reads
the point `67/32` of the second cell from the chain, beside its own
`decide`.  The refusals: the chain extended by a third cell to
`5/2` refuses at that cell's cover at both side spellings — the
segment crosses the carrier's root, and the refusal is the root's
own, a root-free segment of the same width passing at the same
bound and cover shape while a far narrower root-containing segment
still refuses — and the point `5/2` beyond the chain's top refuses
the membership with the count occupied there, the conclusion
false.

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

/-! The cell tier's fixture: the order-one carrier
`levelPMat [5] [-1] [1]` — the level datum at the constant key, the
magnetic member at the top — over the segment `[2, 33/16]`, the
covers one designated entry each at the bound `[3 : 1]`. -/

private def mA : elim.Mat := [[⟨6, 1⟩]]
private def mB : elim.Mat := [[⟨1, 2⟩]]
private def mG : elim.Mat := [[⟨2, 1⟩]]

private def pmA : split.PMat := levelPMat mA mB mG 3 1 [BPair.unit]
private def pmT : split.PMat := levelPMat mA mB mG 9 1 [BPair.unit]
private def pmP : split.PMat := levelPMat mA mB mG 1 2 [BPair.unit]

private def clo : CPair := ⟨⟨3, 1⟩, 1⟩
private def chi : CPair := ⟨⟨34, 1⟩, 16⟩

private def cvA : Cover :=
  Cover.one chi 0 false ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done
private def cvP : Cover :=
  Cover.one chi 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

private theorem covA : coverRead pmA 1 2 clo chi cvA := by decide +kernel
private theorem covT : coverRead pmT 1 2 clo chi cvA := by decide +kernel
private theorem covP : coverRead pmP 1 2 clo chi cvP := by decide +kernel

/-! The window's two counts and the vacant count at the lower
endpoint, and the three target splits at the interior point
`65/32`. -/

private theorem smpA : countAt pmA 2 ⟨3, 1⟩ 1 1
    (inertia.mkSplit 1 (evalPC pmA ⟨3, 1⟩ 1 2)) := by decide +kernel
private theorem smpT : countAt pmT 2 ⟨3, 1⟩ 1 1
    (inertia.mkSplit 1 (evalPC pmT ⟨3, 1⟩ 1 2)) := by decide +kernel
private theorem smpP : countAt pmP 2 ⟨3, 1⟩ 1 0
    (inertia.mkSplit 1 (evalPC pmP ⟨3, 1⟩ 1 2)) := by decide +kernel

private theorem tgtA : splitRead (evalPC pmA ⟨66, 1⟩ 32 2)
    (inertia.mkSplit 1 (evalPC pmA ⟨66, 1⟩ 32 2)) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
private theorem tgtT : splitRead (evalPC pmT ⟨66, 1⟩ 32 2)
    (inertia.mkSplit 1 (evalPC pmT ⟨66, 1⟩ 32 2)) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)
private theorem tgtP : splitRead (evalPC pmP ⟨66, 1⟩ 32 2)
    (inertia.mkSplit 1 (evalPC pmP ⟨66, 1⟩ 32 2)) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

private theorem tgtA1 :
    inertia.revAt (inertia.mkSplit 1 (evalPC pmA ⟨66, 1⟩ 32 2)) = 1 :=
  cellCount pmA 2 1 clo chi cvA covA
    ⟨3, 1⟩ 1 (by decide +kernel) (by decide +kernel) _ smpA
    ⟨66, 1⟩ 32 (by decide +kernel) (by decide +kernel) _ tgtA

example : inertia.revAt (inertia.mkSplit 1 (evalPC pmT ⟨66, 1⟩ 32 2)) = 1 :=
  cellCount pmT 2 1 clo chi cvA covT
    ⟨3, 1⟩ 1 (by decide +kernel) (by decide +kernel) _ smpT
    ⟨66, 1⟩ 32 (by decide +kernel) (by decide +kernel) _ tgtT

example : inertia.revAt (inertia.mkSplit 1 (evalPC pmA ⟨66, 1⟩ 32 2)) = 1
    ∧ inertia.revAt (inertia.mkSplit 1 (evalPC pmT ⟨66, 1⟩ 32 2)) = 1 := by
  decide +kernel

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨66, 1⟩ 32 2)) :=
  cellPsd pmP 2 clo chi cvP covP
    ⟨3, 1⟩ 1 (by decide +kernel) (by decide +kernel) _ smpP
    ⟨66, 1⟩ 32 (by decide +kernel) (by decide +kernel) _ tgtP

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨66, 1⟩ 32 2)) := by
  decide +kernel

/-! The segment membership's binder: at the point one, below the
segment, the membership refuses and the anchor carrier's count reads
naught against the window's one — the transported conclusion
false. -/

example : ¬ (clo ≤ (⟨⟨2, 1⟩, 1⟩ : CPair)) := by decide +kernel
example : ¬ (inertia.revAt (inertia.mkSplit 1 (evalPC pmA ⟨2, 1⟩ 1 2))
    = 1) := by decide +kernel

/-! The vacant sample's binder: the anchor carrier reads count one
at the lower endpoint, refusing the vacant sample, and its target
split refuses the positive-semidefinite read. -/

example : ¬ countAt pmA 2 ⟨3, 1⟩ 1 0
    (inertia.mkSplit 1 (evalPC pmA ⟨3, 1⟩ 1 2)) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 1 (evalPC pmA ⟨66, 1⟩ 32 2)) :=
  fun hc => Nat.noConfusion (tgtA1.symm.trans hc)

/-! The target's upper membership: the point `5/2` beyond the cell's
top refuses it, the count occupied there. -/

example : ¬ ((⟨⟨6, 1⟩, 2⟩ : CPair) ≤ chi) := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨6, 1⟩ 2 2)) := by
  decide +kernel

/-! The chain: two cells at the shared endpoint `33/16`, the second
running to `17/8`, each with its cover and its vacant sample at its
foot. -/

private def chi2 : CPair := ⟨⟨18, 1⟩, 8⟩

private def cvP2 : Cover :=
  Cover.one chi2 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

private def cells2 :
    List (CPair × Cover × (BPair × Pos) × Split 1) :=
  [(chi, cvP, (⟨3, 1⟩, 1), inertia.mkSplit 1 (evalPC pmP ⟨3, 1⟩ 1 2)),
   (chi2, cvP2, (⟨34, 1⟩, 16),
     inertia.mkSplit 1 (evalPC pmP ⟨34, 1⟩ 16 2))]

private theorem chain2 : chainRead pmP 2 0 clo cells2 := by decide +kernel

private theorem tgt2 : splitRead (evalPC pmP ⟨68, 1⟩ 32 2)
    (inertia.mkSplit 1 (evalPC pmP ⟨68, 1⟩ 32 2)) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨68, 1⟩ 32 2)) :=
  chainPsd pmP 2 clo _ _ chain2 ⟨68, 1⟩ 32 (by decide +kernel)
    (by decide +kernel) _ tgt2

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨68, 1⟩ 32 2)) := by
  decide +kernel

/-! The chain's boundary is a located root: a third cell to `5/2`
crosses the carrier's root, its cover refusing, and the extended
chain with it; the point `5/2` beyond the standing chain's top
refuses the membership with the count occupied there. -/

private def chi3 : CPair := ⟨⟨6, 1⟩, 2⟩

private def cvP3 : Cover :=
  Cover.one chi3 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

example : ¬ coverRead pmP 1 2 chi2 chi3 cvP3 := by decide +kernel
example : ¬ coverRead pmP 1 2 chi2 chi3
    (Cover.one chi3 0 false ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done) := by
  decide +kernel

/-! The refusal is the root's, not the width's: a root-free segment
of the same width passes at the same bound and cover shape, and a
root-containing segment far narrower still refuses at both side
spellings. -/

example : coverRead pmP 1 2 (⟨⟨4, 1⟩, 2⟩ : CPair) (⟨⟨16, 1⟩, 8⟩ : CPair)
    (Cover.one ⟨⟨16, 1⟩, 8⟩ 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought
      Cover.done) := by decide +kernel
example : ¬ coverRead pmP 1 2 (⟨⟨40, 1⟩, 16⟩ : CPair) chi3
    (Cover.one chi3 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done) := by
  decide +kernel
example : ¬ coverRead pmP 1 2 (⟨⟨40, 1⟩, 16⟩ : CPair) chi3
    (Cover.one chi3 0 false ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done) := by
  decide +kernel
example : ¬ chainRead pmP 2 0 clo (cells2 ++
    [(chi3, cvP3, (⟨6, 1⟩, 2),
      inertia.mkSplit 1 (evalPC pmP ⟨6, 1⟩ 2 2))]) := by decide +kernel
example : ¬ ((⟨⟨6, 1⟩, 2⟩ : CPair) ≤ chainHi clo cells2) := by
  decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨6, 1⟩ 2 2)) := by
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

/-! The gap tier at the cell fixture: the committed gap `[2, 33/16]`
on the positive-semidefinite carrier, the anchored margin at the
lower endpoint — the level two against the margin one — the bound
pair `(8, 2)`, the derivative fold capped at sixteen, and the
clearing comparison `16 ≤ 16` at the width's own denominator. -/

private def spML : Split 1 :=
  inertia.mkSplit 1 (siteDatum (evalPC pmP ⟨3, 1⟩ 1 2)
    (matScale 1 (idMat 1)))

private theorem margL : splitRead (siteDatum (evalPC pmP ⟨3, 1⟩ 1 2)
    (matScale 1 (idMat 1))) spML :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨66, 1⟩ 32 2)) :=
  gapPsd_lo pmP ⟨3, 1⟩ 1 ⟨34, 1⟩ 16 ⟨9, 1⟩ ⟨3, 1⟩ ⟨17, 1⟩ 1 spML
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    margL (by decide +kernel) (by decide +kernel)
    ⟨66, 1⟩ 32 (by decide +kernel) (by decide +kernel) _ tgtP

/-! The upper anchor at the same gap: the margin certificate at
`33/16`'s own clearing, the level `447` against the margin `400`,
the clearing comparison `4096 ≤ 6400`. -/

private def spMH : Split 1 :=
  inertia.mkSplit 1 (siteDatum (evalPC pmP ⟨34, 1⟩ 16 2)
    (matScale 400 (idMat 1)))

private theorem margH : splitRead (siteDatum (evalPC pmP ⟨34, 1⟩ 16 2)
    (matScale 400 (idMat 1))) spMH :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨66, 1⟩ 32 2)) :=
  gapPsd_hi pmP ⟨3, 1⟩ 1 ⟨34, 1⟩ 16 ⟨9, 1⟩ ⟨3, 1⟩ ⟨17, 1⟩ 400 spMH
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    margH (by decide +kernel) (by decide +kernel)
    ⟨66, 1⟩ 32 (by decide +kernel) (by decide +kernel) _ tgtP

/-! The gap binders' refusals: the magnitude bound at a bound pair
too small, the fold cap one below the fold, the margin beyond the
anchor's level, and the clearing comparison at a cap one beyond
the priced width. -/

example : ¬ (stage.cmag (⟨⟨3, 1⟩, 1⟩ : CPair) * stage.ofB ⟨3, 1⟩
    ≤ stage.ofB ⟨2, 1⟩) := by decide +kernel
example : ¬ foldCap pmP ⟨9, 1⟩ ⟨3, 1⟩ ⟨16, 1⟩ := by decide +kernel
example : ¬ inertia.psdAt (inertia.mkSplit 1
    (siteDatum (evalPC pmP ⟨3, 1⟩ 1 2) (matScale 3 (idMat 1)))) := by
  decide +kernel
example : ¬ (BPair.ofNat 1
    * ((⟨18, 1⟩ * ((⟨34, 1⟩ : BPair).scale 1
        + ((⟨3, 1⟩ : BPair).swap).scale 16)).scale
      (ground.Pos.pow 1 2))
    ≤ (BPair.ofPos 1).scale (16 * 1)) := by decide +kernel

/-! The certificate reads: the committed gap's certificate at the
lower anchor, the zipped list read with its length refusals, and
the strict fold base's refusal at the unit base. -/

private def gcL : GapCert 1 := ⟨⟨9, 1⟩, ⟨3, 1⟩, ⟨17, 1⟩, 1, spML, true⟩

example : gapRead pmP 2 clo chi gcL := by decide +kernel

example : gapsRead pmP 2 [(clo, chi)] [gcL] := by decide +kernel
example : ¬ gapsRead pmP 2 [(clo, chi)] ([] : List (GapCert 1)) := by
  decide +kernel
example : ¬ gapsRead pmP 2 ([] : List (CPair × CPair)) [gcL] := by
  decide +kernel
example : ¬ gapRead pmP 2 clo chi
    ⟨⟨9, 1⟩, ⟨1, 1⟩, ⟨17, 1⟩, 1, spML, true⟩ := by decide +kernel

/-! The interior read at the closed union: two segments' chains, the
first ending at `33/16` and the second footed at `17/8`, the
committed gap between them at the `33/16`-anchored certificate with
margin `256` against the level `447` and the clearing at equality
`32768 = 32768`; the gap's interior point `133/64` and the second
chain's own point `17/8` each read through the theorem beside the
decide, with the anchoring and ordering refusals. -/

private def pc1 : Piece 1 :=
  Piece.seg clo [(chi, cvP, (⟨3, 1⟩, 1),
    inertia.mkSplit 1 (evalPC pmP ⟨3, 1⟩ 1 2))]

private def cvP4 : Cover :=
  Cover.one ⟨⟨10, 1⟩, 4⟩ 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

private def pc2 : Piece 1 :=
  Piece.seg chi2 [(⟨⟨10, 1⟩, 4⟩, cvP4, (⟨18, 1⟩, 8),
    inertia.mkSplit 1 (evalPC pmP ⟨18, 1⟩ 8 2))]

private def gcM : GapCert 1 :=
  ⟨⟨9, 1⟩, ⟨3, 1⟩, ⟨17, 1⟩, 256,
    inertia.mkSplit 1 (siteDatum (evalPC pmP ⟨34, 1⟩ 16 2)
      (matScale 256 (idMat 1))), true⟩

private theorem cread2 : closedRead pmP 2 clo [pc1, pc2] := by
  decide +kernel

private theorem gread2 :
    gapsRead pmP 2 (closedGaps (closedHi clo [pc1]) [pc2]) [gcM] := by
  decide +kernel

private theorem tgtG : splitRead (evalPC pmP ⟨134, 1⟩ 64 2)
    (inertia.mkSplit 1 (evalPC pmP ⟨134, 1⟩ 64 2)) :=
  inertia.mkSplit_read 1 _ (by decide +kernel) (by decide +kernel)

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨134, 1⟩ 64 2)) :=
  interiorPsd pmP clo pc1 [pc2] [gcM] (by decide +kernel)
    (by decide +kernel) (by decide +kernel) cread2 gread2
    ⟨134, 1⟩ 64 (by decide +kernel) (by decide +kernel) _ tgtG

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨134, 1⟩ 64 2)) := by
  decide +kernel

example : inertia.psdAt (inertia.mkSplit 1 (evalPC pmP ⟨68, 1⟩ 32 2)) :=
  interiorPsd pmP clo pc1 [pc2] [gcM] (by decide +kernel)
    (by decide +kernel) (by decide +kernel) cread2 gread2
    ⟨68, 1⟩ 32 (by decide +kernel) (by decide +kernel) _ tgt2

example : ¬ startsAt chi [pc1, pc2] := by decide +kernel
example : ¬ closedRead pmP 2 chi2 [pc1, pc2] := by decide +kernel
example : ¬ ((⟨⟨6, 1⟩, 2⟩ : CPair) ≤ closedHi clo [pc1, pc2]) := by
  decide +kernel

/-! The junction arm at the rational-root carrier `25 - 4t²`: the
boundary point `5/2` at its own split — the kernel's, the lower
list vacant — with the flanking positive-semidefinite sample at
`2`, the read passing at either tie side there, and refused at a
sample beyond the root. -/

private def pmJ : split.PMat :=
  levelPMat [[⟨26, 1⟩]] [[⟨1, 5⟩]] [[⟨2, 1⟩]] 1 1 [BPair.unit]

private def spbJ : Split 1 :=
  inertia.mkSplit 1 (evalPC pmJ ⟨6, 1⟩ 2 2)
private def sptJ : Split 1 :=
  inertia.mkSplit 1 (evalPC pmJ ⟨3, 1⟩ 1 2)

example : closedRead pmJ 2 ⟨⟨6, 1⟩, 2⟩
    [Piece.junc ⟨6, 1⟩ 2 spbJ ⟨3, 1⟩ 1 sptJ true ⟨9, 1⟩ ⟨3, 1⟩] := by
  decide +kernel
example : closedRead pmJ 2 ⟨⟨6, 1⟩, 2⟩
    [Piece.junc ⟨6, 1⟩ 2 spbJ ⟨3, 1⟩ 1 sptJ false ⟨9, 1⟩ ⟨3, 1⟩] := by
  decide +kernel
example : ¬ closedRead pmJ 2 ⟨⟨6, 1⟩, 2⟩
    [Piece.junc ⟨6, 1⟩ 2 spbJ ⟨7, 1⟩ 2
      (inertia.mkSplit 1 (evalPC pmJ ⟨7, 1⟩ 2 2)) true
      ⟨9, 1⟩ ⟨3, 1⟩] := by
  decide +kernel
