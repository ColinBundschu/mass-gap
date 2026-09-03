import MassGap.Continuum
/-!
The check module for `thm:continuum`: the batteries read the
continuum reads by kernel `decide` beside the theorem routes.

The site-count block reads a datum's site counts against the corner
scale at pair coordinates: the extent `[7 : 1]` against the scale
`[2 : 1]` counts three multiples, the extent `[7 : 2]` one, and the
extent `[1 : 1]` none, the occupied count's two comparisons and the
vacant count's one routed beside the decides; a two-support datum
reads its count list.  The stabilization block reads a datum whose
counts agree at the bracket ends `[2 : 1]` and `[3 : 1]` and pins
the counts at the scale `[5 : 2]` between, the route beside the
decide; the ends' agreement is isolated at a datum whose counts part
at the ends and at the middle scale, the upper end's comparison at
the scale `[4 : 1]` beyond the bracket where the counts move, and
the lower end's at the scale `[1 : 1]` below it.

The Gram block reads the two-row family's Gram at its computed split
positive semidefinite, the route beside the decide; the ragged
family's Gram, the pairing truncating at the shorter row, reads
positive semidefinite as the padded rows' own, the row width the
frame `con:coeff` states, the family's paired slots at one joined
coordinate list; and a symmetric datum off the Gram shape
counts a reversal, the read the Gram's.  The kernel count sits at or
below the count below a level, decided at the located root list
beside the route.

The cut block reads the corner cell's cut at a diagonal head
`5, 17, 37` over the unit gram with the ground level `⟨6 : 1⟩`, the
level gap `0, 12, 32` diagonalized at the identity congruence, the
line `⟨16 : 1⟩` at count one and its gap level `10`, the count
identity's certificate there, and the edge `[8 : 1]`: the cut tie is
routed through `cell_cut` (the raw tie `ChecksGappos` decides at the
free window).  The five binders are isolated at forges each parting
the conclusion: the line's gap level `20` off its tie at the edge
`[14 : 1]` beyond the root `12`; the ground tie at the forged gap
`0, 8, 28`, the ground read at `9` against the head's `5`, at the
edge `[9 : 1]`; the edge comparison at the edge `[13 : 1]` beyond
the line's gap level; the kernel count at the gap `1, 13, 33`, the
ground level `⟨5 : 1⟩` off the head's root, at the edge `[8 : 1]`;
and the count one at the line at the head `5, 9, 37`, whose gap
`0, 4, 32` ties at the ground `5` with the line counting two, at the
edge `[8 : 1]` above the root `4`.  The edge's floor clearance is
decided at the lower line `⟨10 : 1⟩` above the ground beside its
route, refused at a lower line below the ground, and refused at a
gap level off the line's tie.
-/

open ground elim inertia certconstruct continuum

/-! ## The site counts at pair coordinates -/

example : siteCount (7, 1) 2 1 = some 3 := by decide +kernel
example : siteCount (7, 2) 2 1 = some 1 := by decide +kernel
example : siteCount (1, 1) 2 1 = none := by decide +kernel
example : (2 : Pos) * 1 * 3 ≤ 7 * 1 ∧ (7 : Pos) * 1 < 2 * 1 * ground.succ 3 :=
  siteCount_read (7, 1) 2 1 3 (by decide +kernel)
example : (1 : Pos) * 1 < 2 * 1 :=
  siteCount_vac (1, 1) 2 1 (by decide +kernel)

private def dA : Datum := ⟨[(7, 1), (3, 1)], [(5, 2)], [(1, 3)]⟩

example : siteCounts dA 2 1 = [some 3, some 1] := by decide +kernel

/-! ## The stabilization across a scale bracket -/

private def dB : Datum := ⟨[(3, 1), (1, 1)], [], []⟩

example : countsStable dB 2 1 3 1 := by decide +kernel
example : siteCounts dB 5 2 = siteCounts dB 2 1 := by decide +kernel
example : siteCounts dB 5 2 = siteCounts dB 2 1 :=
  counts_stable dB 2 1 3 1 5 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The ends' agreement is load-bearing: the datum `dA` parts at the
ends and its counts move at the middle scale. -/
example : ¬ countsStable dA 2 1 3 1 := by decide +kernel
example : ¬ (siteCounts dA 5 2 = siteCounts dA 2 1) := by decide +kernel

/-- The upper end's comparison is load-bearing: beyond the bracket
the counts move. -/
example : ¬ ((4 : Pos) * 1 ≤ 3 * 1) := by decide +kernel
example : ¬ (siteCounts dB 4 1 = siteCounts dB 2 1) := by decide +kernel

/-- The lower end's comparison is load-bearing: below the bracket
the counts move. -/
example : ¬ ((2 : Pos) * 1 ≤ 1 * 1) := by decide +kernel
example : ¬ (siteCounts dB 1 1 = siteCounts dB 2 1) := by decide +kernel

/-! ## The Gram's positivity -/

private def gL : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]]

private def gSp : Split 2 := mkSplit 2 (gramM gL)

example : splitRead (gramM gL) gSp := by decide +kernel
example : psdAt gSp := by decide +kernel
example : psdAt gSp := gram_psd gL 2 (by decide +kernel) gSp (by decide +kernel)

/-- The ragged family: the pairing truncates at the shorter row, the
Gram the padded rows' own, positive semidefinite as read. -/
private def gR : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩]]

example : splitRead (gramM gR) (mkSplit 2 (gramM gR)) := by decide +kernel
example : psdAt (mkSplit 2 (gramM gR)) := by decide +kernel

/-- A symmetric datum off the Gram shape counts a reversal. -/
private def gN : Mat := [[⟨2, 1⟩, ⟨4, 1⟩], [⟨4, 1⟩, ⟨2, 1⟩]]

example : splitRead gN (mkSplit 2 gN) := by decide +kernel
example : ¬ psdAt (mkSplit 2 gN) := by decide +kernel

/-! ## The cut at the corner cell -/

private def u : BPair := BPair.unit

private def et3 : Mat :=
  [[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]]

private def h3 : Mat :=
  [[⟨6, 1⟩, u, u], [u, ⟨18, 1⟩, u], [u, u, ⟨38, 1⟩]]

private def id3 : SqMat 3 := ⟨idMat 3, by decide +kernel⟩

private def l3 : List (BPair × Pos × BPair) :=
  [(u, 1, ⟨2, 1⟩), (⟨13, 1⟩, 1, ⟨2, 1⟩), (⟨33, 1⟩, 1, ⟨2, 1⟩)]

private def roots3 : List (BPair × Pos) :=
  [(u, 1), (⟨13, 1⟩, 1), (⟨33, 1⟩, 1)]

example : l3.map (fun r => (r.1, r.2.1)) = roots3 := by decide +kernel

example : split.rootsAtKernel roots3 ≤ split.rootsBelow roots3 8 1 := by
  decide +kernel
example : split.rootsAtKernel roots3 ≤ split.rootsBelow roots3 8 1 :=
  split.kernel_le_below roots3 8 1

example : matOneValue et3
    (siteDatum (matAdd h3 (matScale 1 (idMat 3))) (matScale 6 (idMat 3))) := by
  decide +kernel
example : split.diagRead et3 (idMat 3) id3 id3 l3 := by decide +kernel
example : split.rootsAtKernel roots3 = 1 := by decide +kernel

private def spT : Split 3 :=
  mkSplit 3 (siteDatum (matAdd h3 (matScale 1 (idMat 3))) (matScale 16 (idMat 3)))

example : countAtPair h3 (idMat 3) 16 1 1 spT := by decide +kernel
example : (10 : Pos) + (1 + 6) = 16 + 1 := by decide +kernel

private def spT' : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 et3) (matScale 10 (idMat 3)))

example : split.countRead et3 (idMat 3) roots3 10 1 spT' := by decide +kernel

private def spC : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 (matMul et3 et3)) (matScale (4 * 2) et3))

example : splitRead (siteDatum (matScale 1 (matMul et3 et3))
    (matScale (4 * 2) et3)) spC := by decide +kernel

example : speccut.cutTie et3 (l3.map (fun r => (r.1, r.2.1))) 4 2 1 spC :=
  cell_cut h3 et3 6 1 (by decide +kernel) id3 id3 l3
    (by decide +kernel) (by decide +kernel) 16 1 10 spT spT'
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 4 2 1
    (by decide +kernel) spC (by decide +kernel)

/-- The line's tie is load-bearing: at the forged gap level `20` the
count identity still certifies, and the edge `[14 : 1]` beyond the
root `12` refuses the cut tie. -/
private def spT20 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 et3) (matScale 20 (idMat 3)))

example : split.countRead et3 (idMat 3) roots3 20 1 spT20 := by decide +kernel
example : ¬ ((20 : Pos) + (1 + 6) = 16 + 1) := by decide +kernel
example : (7 : Pos) * 2 * 1 ≤ 20 * 1 := by decide +kernel

private def spC14 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 (matMul et3 et3)) (matScale (7 * 2) et3))

example : splitRead (siteDatum (matScale 1 (matMul et3 et3))
    (matScale (7 * 2) et3)) spC14 := by decide +kernel
example : ¬ speccut.cutTie et3 roots3 7 2 1 spC14 := by decide +kernel

/-- The ground tie is load-bearing: the forged gap `0, 8, 28` reads
its ground at `9` against the head's `5`, every further datum holds
at it, and the edge `[9 : 1]` refuses the cut tie. -/
private def et9 : Mat :=
  [[u, u, u], [u, ⟨9, 1⟩, u], [u, u, ⟨29, 1⟩]]

private def l9 : List (BPair × Pos × BPair) :=
  [(u, 1, ⟨2, 1⟩), (⟨9, 1⟩, 1, ⟨2, 1⟩), (⟨29, 1⟩, 1, ⟨2, 1⟩)]

private def roots9 : List (BPair × Pos) :=
  [(u, 1), (⟨9, 1⟩, 1), (⟨29, 1⟩, 1)]

example : ¬ matOneValue et9
    (siteDatum (matAdd h3 (matScale 1 (idMat 3))) (matScale 6 (idMat 3))) := by
  decide +kernel
example : split.diagRead et9 (idMat 3) id3 id3 l9 := by decide +kernel
example : split.rootsAtKernel roots9 = 1 := by decide +kernel

private def spT9 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 et9) (matScale 10 (idMat 3)))

example : split.countRead et9 (idMat 3) roots9 10 1 spT9 := by decide +kernel
example : (9 : Pos) * 1 * 1 ≤ 10 * 1 := by decide +kernel

private def spC9 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 (matMul et9 et9)) (matScale (9 * 1) et9))

example : splitRead (siteDatum (matScale 1 (matMul et9 et9))
    (matScale (9 * 1) et9)) spC9 := by decide +kernel
example : ¬ speccut.cutTie et9 roots9 9 1 1 spC9 := by decide +kernel

/-- The edge comparison is load-bearing: the edge `[13 : 1]` beyond
the line's gap level refuses the cut tie. -/
example : ¬ ((13 : Pos) * 1 * 1 ≤ 10 * 1) := by decide +kernel

private def spC13 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 (matMul et3 et3)) (matScale (13 * 1) et3))

example : splitRead (siteDatum (matScale 1 (matMul et3 et3))
    (matScale (13 * 1) et3)) spC13 := by decide +kernel
example : ¬ speccut.cutTie et3 roots3 13 1 1 spC13 := by decide +kernel

/-- The kernel count is load-bearing: at the ground level `⟨5 : 1⟩`
off the head's root the gap `1, 13, 33` ties to the head, the line
counts one with its gap level `11` certified, and the edge `[8 : 1]`
refuses the cut tie, the root `1` off the kernel point and below the
edge. -/
private def et4 : Mat :=
  [[⟨2, 1⟩, u, u], [u, ⟨14, 1⟩, u], [u, u, ⟨34, 1⟩]]

private def l4 : List (BPair × Pos × BPair) :=
  [(⟨2, 1⟩, 1, ⟨2, 1⟩), (⟨14, 1⟩, 1, ⟨2, 1⟩), (⟨34, 1⟩, 1, ⟨2, 1⟩)]

private def roots4 : List (BPair × Pos) :=
  [(⟨2, 1⟩, 1), (⟨14, 1⟩, 1), (⟨34, 1⟩, 1)]

example : matOneValue et4
    (siteDatum (matAdd h3 (matScale 1 (idMat 3))) (matScale 5 (idMat 3))) := by
  decide +kernel
example : split.diagRead et4 (idMat 3) id3 id3 l4 := by decide +kernel
example : ¬ (split.rootsAtKernel roots4 = 1) := by decide +kernel
example : (11 : Pos) + (1 + 5) = 16 + 1 := by decide +kernel

private def spT4 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 et4) (matScale 11 (idMat 3)))

example : split.countRead et4 (idMat 3) roots4 11 1 spT4 := by decide +kernel
example : (4 : Pos) * 2 * 1 ≤ 11 * 1 := by decide +kernel

private def spC4 : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 (matMul et4 et4)) (matScale (4 * 2) et4))

example : splitRead (siteDatum (matScale 1 (matMul et4 et4))
    (matScale (4 * 2) et4)) spC4 := by decide +kernel
example : ¬ speccut.cutTie et4 roots4 4 2 1 spC4 := by decide +kernel

/-- The count one at the line is load-bearing: at the head
`5, 9, 37` the gap `0, 4, 32` ties at the ground `5` with the kernel
root alone, the line `⟨16 : 1⟩` counts two, every further datum holds
at the line's gap level `10`, and the edge `[8 : 1]` refuses the cut
tie, the root `4` below it. -/
private def hX : Mat :=
  [[⟨6, 1⟩, u, u], [u, ⟨10, 1⟩, u], [u, u, ⟨38, 1⟩]]

private def etX : Mat :=
  [[u, u, u], [u, ⟨5, 1⟩, u], [u, u, ⟨33, 1⟩]]

private def lX : List (BPair × Pos × BPair) :=
  [(u, 1, ⟨2, 1⟩), (⟨5, 1⟩, 1, ⟨2, 1⟩), (⟨33, 1⟩, 1, ⟨2, 1⟩)]

private def rootsX : List (BPair × Pos) :=
  [(u, 1), (⟨5, 1⟩, 1), (⟨33, 1⟩, 1)]

example : matOneValue etX
    (siteDatum (matAdd hX (matScale 1 (idMat 3))) (matScale 6 (idMat 3))) := by
  decide +kernel
example : split.diagRead etX (idMat 3) id3 id3 lX := by decide +kernel
example : split.rootsAtKernel rootsX = 1 := by decide +kernel
example : ¬ countAtPair hX (idMat 3) 16 1 1
    (mkSplit 3 (siteDatum (matAdd hX (matScale 1 (idMat 3)))
      (matScale 16 (idMat 3)))) := by
  decide +kernel

private def spTX : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 etX) (matScale 10 (idMat 3)))

example : split.countRead etX (idMat 3) rootsX 10 1 spTX := by decide +kernel

private def spCX : Split 3 :=
  mkSplit 3 (siteDatum (matScale 1 (matMul etX etX)) (matScale (4 * 2) etX))

example : splitRead (siteDatum (matScale 1 (matMul etX etX))
    (matScale (4 * 2) etX)) spCX := by decide +kernel
example : ¬ speccut.cutTie etX rootsX 4 2 1 spCX := by decide +kernel

/-! ## The edge's floor clearance -/

example : (16 : Pos) + 1 ≤ 10 + (1 + 10) := by decide +kernel
example : (16 : Pos) + 1 ≤ 10 + (1 + 10) :=
  edge_floor 6 1 10 1 16 1 10 (by decide +kernel) (by decide +kernel)

/-- The ground's side is load-bearing: at a lower line below the
ground the gap level parts from the lines' gap. -/
example : ¬ ((6 : Pos) + 1 ≤ 3 + 1) := by decide +kernel
example : ¬ ((16 : Pos) + 1 ≤ 10 + (1 + 3)) := by decide +kernel

/-- The line's tie is load-bearing: at a gap level off the tie the
lines' gap parts from it. -/
example : ¬ ((1 : Pos) + (1 + 6) = 16 + 1) := by decide +kernel
example : ¬ ((16 : Pos) + 1 ≤ 1 + (1 + 10)) := by decide +kernel
