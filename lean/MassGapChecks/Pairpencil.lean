import MassGap.Pairpencil
import MassGapChecks.Carrier
/-!
The check module for `thm:pairpencil`: the batteries re-read the
window pencil's symmetric pair matrix by kernel `decide` at the
label calculus's instantiation — the label-index magnetic matrix at
two and three letters (the fusion counts' own entries, the vacuum
defect the Kronecker delta at two labels and the diagonal the base
`c₁`), its symmetry at the self-dual `θ`, the window list's
diagonal with the unit line at its head over the committed square
and theta windows, and the pair's site datum `H([α : β])` symmetric
with pair entries at both weights.  The diagonal pins read the
committed enumerations at the carrier check module's pins, the
theta window's at the tabulated lookup route.  The pencil interface
reads at the square window over two
letters: the loop pencil — the window list's diagonal at the two
loops' contents, the identity gram, and the one plaquette term the
fusion counts capped two-sidedly at the adjoint dimension three —
passes the whole read, with the refusals isolating the gram's unit
line, the gram's block structure and its block content (the
identity refused at the clearing two, a loop block doubled
refused), a term's support (an entry
between the two loops, off every changed-edge row), the cap at a
term scaled past the dimension, and the order tie.  The gram's
block content reads at the theta graph's four-slot fiber over
three letters, the two trivalent vertices' Grams' Kronecker
product at the stated clearing, the identity gram refused there.  The window
list itself reads at the square window, every fiber at one slot
with its diagonal the window diagonal, and at the theta graph over
three letters at a fiber of four slots, the two trivalent vertices
at multiplicity two.  The magnetic entries read at the fibers'
stated lists (`con:fiber`'s magnetic read): at the square over two
and three letters the contraction reads the fusion counts, the
loop clause's coherence, with the forged support entry refused at
the entry conjunct alone; the loop fallback at unstated lists reads
the count; and at the theta window over two letters at cutoff
twenty-six, the join of the adjoint on the shared link with the
fundamental on the six further links beside the two loops and the
hexagon, the whole pencil passes at the decided entries, the
electric member the gram's form at the diagonal — the join's
own term eight, its cross entry with the hexagon the balance partner
of two at both orders, the loops' one — with the join's own entry,
the cross entry's side and the gram's join block each refused; and
the entry read at the clearing two, the gram and the term doubled
together, with either doubled alone refused.  The square's terms'
read is one theorem the pencil pass and the terms' extractions
consume, the refusals reading their refused conjunct alone. -/
set_option maxHeartbeats 16000000

open ground lattice fusion elim pairpencil

private def u : BPair := BPair.unit

/-! The label-index magnetic matrix at two letters over
`(𝟏, f, θ)`: the vacuum defect, the `f` diagonal one, and the base
`c₁ = 1`. -/

example : matOneValue (loopMag (dataA 2) [[1, 0], adjchar.theta 2])
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩]] := by
  decide +kernel

/-! At three letters the base reads `c₁ = 2`, the further entries
the counts' own. -/

example : matOneValue (loopMag (dataA 3) [[1, 0, 0], adjchar.theta 3])
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨3, 1⟩]] := by
  decide +kernel

/-! The symmetry at the self-dual `θ`, both letter counts. -/

example : symmRead (loopMag (dataA 2) [[1, 0], adjchar.theta 2]) := by
  decide +kernel
example : symmRead (loopMag (dataA 3) [[1, 0, 0], adjchar.theta 3]) := by
  decide +kernel

/-! The window list's diagonal with the unit line at its head, the
committed windows' reads: at the square over two letters and at the
theta window over the tabulated interface, every fiber at one
slot. -/

example : slotDiag (dataA 2) square (carrier.idx (dataA 2) square 32)
    = [0, 12, 32] := by
  rw [carrier.sqIx2_pin]; decide +kernel
example : slotDiag (tabulate (dataA 2) 18) thetaG
    (carrier.idx (tabulate (dataA 2) 18) thetaG 18) = [0, 12, 18, 12] := by
  rw [carrier.thIx18_pin]; decide +kernel

/-! The pair's site datum at the square's label index: symmetric
with pair entries at both weights, the displayed matrix at
`[1 : 1]`. -/

example : matOneValue
    (pencilH 1 1 [0, 12, 32] (inertia.idMat 3)
 (loopMag (dataA 2) [[1, 0], adjchar.theta 2]))
    [[u, u, ⟨1, 2⟩], [u, ⟨12, 1⟩, u], [⟨1, 2⟩, u, ⟨32, 1⟩]] := by
  decide +kernel

example : symmRead
    (pencilH 2 3 [0, 12, 32] (inertia.idMat 3)
      (loopMag (dataA 2) [[1, 0], adjchar.theta 2])) := by decide +kernel

/-! The pencil interface at the square window over two letters, the
loop pencil at cutoff thirty-two: the slot diagonal at the
fundamental and adjoint loops' contents, the identity gram at its
own split, and the one plaquette term the fusion counts with its
two cap splits at the adjoint dimension three. -/

private def mSq : Mat := loopMag (dataA 2) [[1, 0], adjchar.theta 2]
private def gSq : Mat := inertia.idMat 3
private def cSq : Mat := inertia.matScaleB (BPair.ofNat 3) gSq
/-! The square's three splits as stated data, the gram's own and the
term's two caps (`lem:inertia`'s certificate data, re-read by
`splitRead`). -/
private def spGSq : inertia.Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩]], rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨2, 1⟩, .one ⟨2, 1⟩],
   0, rfl⟩
private def spUSq : inertia.Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨19, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨55, 1⟩]], rfl⟩,
   ⟨[[⟨1, 163⟩, ⟨1, 1⟩, ⟨55, 1⟩],
     [⟨1, 1⟩, ⟨55, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 4⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨19, 1⟩, .one ⟨4861, 1⟩],
   0, rfl⟩
private def spLSq : inertia.Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 37⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨109, 1⟩]], rfl⟩,
   ⟨[[⟨1, 325⟩, ⟨1, 1⟩, ⟨1, 109⟩],
     [⟨1, 1⟩, ⟨109, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 4⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨37, 1⟩, .one ⟨42769, 1⟩],
   0, rfl⟩

example : (dataA 2).dim (adjchar.theta 2) = 3 := by decide +kernel
example : posConf (dataA 2) square (carrier.idx (dataA 2) square 32) 0
      = carrier.unitConf (dataA 2) square
    ∧ posConf (dataA 2) square (carrier.idx (dataA 2) square 32) 1
      = [[1, 0], [1, 0], [1, 0], [1, 0]]
    ∧ posConf (dataA 2) square (carrier.idx (dataA 2) square 32) 2
      = [[2, 0], [2, 0], [2, 0], [2, 0]] := by
  decide +kernel

/-! The window list at the square window: the two loops each at
one slot, the vacant key over the four vertices, the window list's
diagonal the index's contents at the unit fiber products, and the
window list's count with the unit line the window dimension. -/

example : slotList (dataA 2) square carrier.sqIx2
    = [([[1, 0], [1, 0], [1, 0], [1, 0]], [0, 0, 0, 0]),
       ([[2, 0], [2, 0], [2, 0], [2, 0]], [0, 0, 0, 0])] := by decide +kernel
example : slotDiag (dataA 2) square carrier.sqIx2 = 0 :: carrier.sqIx2.map
    (carrier.contentN (dataA 2)) :=
  slotDiag_unit (dataA 2) square carrier.sqIx2 (by decide +kernel)
example : (slotList (dataA 2) square (carrier.idx (dataA 2) square 32)).length + 1
    = windowfinite.dimSect (dataA 2) square 32 :=
  slotList_dimSect (dataA 2) square 32
example : (slotList (dataA 2) square carrier.sqIx2).length + 1 = 3 := by
  decide +kernel

/-! A fiber of four slots: the adjoint on every link of the theta
graph at three letters, the two trivalent vertices at multiplicity
two, the slot keys the digit pairs there, their count the fiber's
multiplicity product through the theorem, and a key with a digit at
the multiplicity refused. -/

private def thAll : List places.Shape := List.replicate 7 (adjchar.theta 3)

example : slotKeys (dataA 3) thetaG thAll
    = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0]] := by decide +kernel
example : windowfinite.fibProd (dataA 3) thetaG thAll = 4 := by decide +kernel
example : (slotKeys (dataA 3) thetaG thAll).length
    = windowfinite.fibProd (dataA 3) thetaG thAll :=
  length_slotKeys (dataA 3) thetaG thAll
example : ground.countOf [0, 0, 0, 2, 0, 0] (slotKeys (dataA 3) thetaG thAll) = 0
    ∧ ground.countOf [0, 0, 0, 1, 0] (slotKeys (dataA 3) thetaG thAll) = 0 := by
  decide +kernel
/-- The square's one term at its reads, the contraction the module's
pencil pass and extractions consume. -/
private def sqP0 : List (Nat × Bool) := ground.getAt [] square.plaqs 0
private def sqCap : Mat :=
  inertia.matScaleB (BPair.ofNat ((dataA 2).dim (dataA 2).theta)) gSq
private theorem sqPlaqs : square.plaqs = [sqP0] := by decide +kernel
private theorem sqSym : symmRead mSq := by decide +kernel
private theorem sqSq : sqAt mSq 3 ∧ sqAt sqCap 3 := by decide +kernel
private theorem sqLe : inertia.leAt mSq sqCap spUSq := by decide +kernel
private theorem sqLo : inertia.splitRead (matAdd sqCap mSq) spLSq := by decide +kernel
private theorem sqPsd : inertia.psdAt spLSq := by decide +kernel
private theorem sqSupp : termSupport (dataA 2) square 3 carrier.sqIx2 sqP0 mSq := by
  decide +kernel
private theorem sqEntR0 : (List.range 3).all (fun j =>
    !rowPair (dataA 2) square carrier.sqIx2 sqP0 0 j
      || entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqP0 0 j) = true := by
  decide +kernel
private theorem sqEntR1 : (List.range 3).all (fun j =>
    !rowPair (dataA 2) square carrier.sqIx2 sqP0 1 j
      || entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqP0 1 j) = true := by
  decide +kernel
private theorem sqEntR2 : (List.range 3).all (fun j =>
    !rowPair (dataA 2) square carrier.sqIx2 sqP0 2 j
      || entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqP0 2 j) = true := by
  decide +kernel
private theorem sqEnt : entriesRead (dataA 2) square 3 carrier.sqIx2 1 gSq sqP0 mSq :=
  (ground.all_range_succ_intro 2 (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl sqEntR0) sqEntR1) sqEntR2)
private theorem sqCapAt : inertia.capAt mSq sqCap spUSq spLSq :=
  ⟨sqSq.1, sqSq.2, sqLe, sqLo, sqPsd⟩
private theorem sqTerms : termsRead (dataA 2) square 3 carrier.sqIx2 1 gSq
    square.plaqs [(mSq, spUSq, spLSq)] := by
  rw [sqPlaqs]
  exact ⟨sqSym, sqCapAt, sqSupp, sqEnt, trivial⟩

example : pencilRead (dataA 2) square 32 3 carrier.sqIx2 1 (pencilE [0, 12, 32])
    gSq mSq spGSq [(mSq, spUSq, spLSq)] :=
  ⟨carrier.sqIx2_pin, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, sqTerms,
   by decide +kernel, by decide +kernel⟩

/-! The refusals, each read at its refused conjunct: the gram's unit
line at two, a gram coupling the two loops, a term with an entry
between the two loops (off every changed-edge row on the square),
the term scaled to four against the dimension three, the order tie
at two, and the magnetic member doubled against its one term's
sum. -/

example : ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2 1 (pencilE [0, 12, 32])
    gSq (inertia.matScaleB (BPair.ofNat 2) mSq) spGSq
    [(mSq, spUSq, spLSq)] :=
  fun h => absurd h.2.2.2.2.2.2.2.2.2 (by decide +kernel)

/-! The magnetic member's order isolated: the member with one row
padded by a trailing unit reads one value with the terms' sum and
is refused at the order, the padded row off the square shape. -/

private def mSqRag : Mat :=
  (List.range 3).map (fun i =>
    if i == 0 then ground.getAt [] mSq 0 ++ [BPair.unit] else ground.getAt [] mSq i)

example : matOneValue mSqRag (termSum 3 [(mSq, spUSq, spLSq)])
    ∧ ¬ sqAt mSqRag 3
    ∧ ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2 1 (pencilE [0, 12, 32])
        gSq mSqRag spGSq [(mSq, spUSq, spLSq)] :=
  ⟨by decide +kernel, by decide +kernel,
   fun h => absurd h.2.2.2.2.2.2.2.2.1 (by decide +kernel)⟩

/-! The terms' reads' two extractions at the square's one term: the
terms' count the plaquettes' and the term square at the order. -/

example : [(mSq, spUSq, spLSq)].length = square.plaqs.length :=
  termsRead_len (dataA 2) square 3 carrier.sqIx2 1 gSq _ _ sqTerms
example : sqAt mSq 3 :=
  termsRead_sq (dataA 2) square 3 carrier.sqIx2 1 gSq square.plaqs
    [(mSq, spUSq, spLSq)] sqTerms 0 (by decide)

/-! The index tie isolated: the two loops stated in the reversed
order with the pencil's data reordered beside them refuse at the
window's own enumeration, the refusal read at the tie conjunct with
the order, the electric form and the gram's block read standing. -/

private def mSqR : Mat := loopMag (dataA 2) [adjchar.theta 2, [1, 0]]
private def spUSqR : inertia.Split 3 :=
  inertia.mkSplit 3 (inertia.siteDatum cSq mSqR)
private def spLSqR : inertia.Split 3 := inertia.mkSplit 3 (matAdd cSq mSqR)

example : ¬ (carrier.idx (dataA 2) square 32 = carrier.sqIx2.reverse)
    ∧ windowfinite.dimSect (dataA 2) square 32 = 3
    ∧ matOneValue (pencilE [0, 32, 12]) (formE (slotDiag (dataA 2) square
        carrier.sqIx2.reverse) gSq)
    ∧ gramBlockRead (dataA 2) square 3 carrier.sqIx2.reverse 1 gSq := by
  decide +kernel
example : ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2.reverse 1
    (pencilE [0, 32, 12]) gSq mSqR spGSq [(mSqR, spUSqR, spLSqR)] :=
  fun h => absurd h.1 (by decide +kernel)

example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 1
    [[⟨3, 1⟩, u, u], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]] := by decide +kernel
example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 1
    [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel
example : gramBlockRead (dataA 2) square 3 carrier.sqIx2 1 gSq := by decide +kernel

/-! The block content isolated at the square: the identity gram
refused at the clearing two, and a loop block doubled at the
clearing one refused — each loop's block the four coevaluations
against the four link scales, one exactly. -/

example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 2 gSq
    ∧ ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 1
        [[⟨2, 1⟩, u, u], [u, ⟨3, 1⟩, u], [u, u, ⟨2, 1⟩]]
    ∧ fibGram (dataA 2) square [[2, 0], [2, 0], [2, 0], [2, 0]]
      = some [([[BPair.ofNat 3]], 1), ([[BPair.ofNat 3]], 1),
          ([[BPair.ofNat 3]], 1), ([[BPair.ofNat 3]], 1)]
    ∧ blockScale (dataA 2) square [[2, 0], [2, 0], [2, 0], [2, 0]] = 81 := by
  decide +kernel
example : ¬ termSupport (dataA 2) square 3 carrier.sqIx2 sqPlaq
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel
example : termSupport (dataA 2) square 3 carrier.sqIx2 sqPlaq mSq := by
  decide +kernel

/-! The magnetic entries at the square over two letters: the
contraction at the fibers' stated lists reads the fusion counts'
own entries across the changed edge — the unit against the adjoint
loop at one, the fundamental loop's own at one and the adjoint
loop's own at the base one — the loop clause's coherence, the
whole pencil's pass above its read; the fundamental loop's own
entry forged to two is refused at the entry conjunct with the
symmetry, the cap and the support standing; the read at the
clearing two, the gram and the term doubled together, passes with
either doubled alone refused; and the read's data at the window:
the letter count two, the words of the unit, the fundamental and
the adjoint, and the twelve link signatures of the window's
words. -/

private def mSqForged : Mat :=
  ground.matOf 3 3 (fun i j =>
    if i == 1 && j == 1 then ⟨3, 1⟩ else ground.getAt u (ground.getAt [] mSq i) j)

example : symmRead mSqForged
    ∧ inertia.capAt mSqForged cSq
        (inertia.mkSplit 3 (inertia.siteDatum cSq mSqForged))
        (inertia.mkSplit 3 (matAdd cSq mSqForged))
    ∧ termSupport (dataA 2) square 3 carrier.sqIx2 sqPlaq mSqForged
    ∧ entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqPlaq 1 1 = true
    ∧ entryAt (dataA 2) square carrier.sqIx2 1 gSq mSq sqPlaq 0 2 = true
    ∧ entryAt (dataA 2) square carrier.sqIx2 1 gSq mSqForged sqPlaq 1 1 = false := by
  decide +kernel

example : entryAt (dataA 2) square carrier.sqIx2 2 (inertia.matScaleB (BPair.ofNat 2) gSq)
      (inertia.matScaleB (BPair.ofNat 2) mSq) sqPlaq 1 1 = true
    ∧ entryAt (dataA 2) square carrier.sqIx2 2 (inertia.matScaleB (BPair.ofNat 2) gSq)
      (inertia.matScaleB (BPair.ofNat 2) mSq) sqPlaq 0 2 = true
    ∧ entryAt (dataA 2) square carrier.sqIx2 2 (inertia.matScaleB (BPair.ofNat 2) gSq)
      mSq sqPlaq 1 1 = false
    ∧ entryAt (dataA 2) square carrier.sqIx2 2 gSq
      (inertia.matScaleB (BPair.ofNat 2) mSq) sqPlaq 1 1 = false := by decide +kernel

example : lettersOf (dataA 2) = 2 ∧ wordOf (dataA 2) [0, 0] = (0, 0)
    ∧ wordOf (dataA 2) [1, 0] = (1, 0) ∧ wordOf (dataA 2) (adjchar.theta 2) = (2, 0)
    ∧ (linkSigs (dataA 2) carrier.sqIx2).length = 12
    ∧ linkSigAt (2, 0) true (2, 0) = [true, true, false, true, false, false]
    ∧ rowPair (dataA 2) square carrier.sqIx2 sqPlaq 0 2
    ∧ rowPair (dataA 2) square carrier.sqIx2 sqPlaq 1 1
    ∧ !rowPair (dataA 2) square carrier.sqIx2 sqPlaq 0 1 := by decide +kernel

/-! The link data at the adjoint loop's changed link over two
letters: three undaggered and three daggered slots read the direct
tag, five kernel members, and the fundamental loop's link two of
each at the symbolic tag, two wirings; the stored read is the link
data's own. -/

example : (fiber.linkList 2 [true, true, false, true, false, false]).1.length = 5
    ∧ (fiber.linkList 2 [true, false, true, false]).1.length = 2
    ∧ (fiber.linkList 2 []).1.length = 1
    ∧ (fiber.linkList 2 [true, false, true, false]).2
      = [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]] := by
  decide +kernel
example : linkDataAt (dataA 2) carrier.sqIx2 [true, false, true, false]
    = linkData 2 [true, false, true, false] :=
  linkDataAt_read (dataA 2) carrier.sqIx2 _
example : (linkDataAt (dataA 2) carrier.sqIx2 [true, false, true, false]).2.1
    = [[BPair.ofNat 4, (BPair.ofNat 2).swap], [(BPair.ofNat 2).swap, BPair.ofNat 4]] := by
  decide +kernel

/-! The boundary character's wiring at the square's first vertex:
one pass, two boundary ends at four slots, the layout the entering
head's exchanged pair then the leaving tail's, the pairing the two
ends' exchange, and the four monomials pairing the entering link's
undaggered slot with the leaving link's daggered and the leaving
link's undaggered with the entering link's daggered. -/

example : bdryEnds square sqPlaq 1 = [(0, false), (1, true)]
    ∧ passesAt square sqPlaq 1 = [((0, true), (1, true))]
    ∧ bdrySig square sqPlaq 1 = [true, false, false, true]
    ∧ bdryPerm square sqPlaq 1 = [1, 0]
    ∧ (slotpower.gMons (bdryWiring 2 square sqPlaq 1)).map Prod.fst
      = [[0, 0, 0, 0], [0, 1, 0, 1], [1, 0, 1, 0], [1, 1, 1, 1]] := by decide +kernel

/-! The square over three letters at cutoff thirty-two: the
fundamental and its dual loops, each term entry the count one, the
loop clause's coherence at the symbolic tag's two wirings per
link. -/

private def m3 : Mat := loopMag (dataA 3) [[1, 0, 0], [0, 1, 0]]
private def g3 : Mat := inertia.idMat 3
private def c3 : Mat := inertia.matScaleB (BPair.ofNat 8) g3

example : (dataA 3).dim (adjchar.theta 3) = 8
    ∧ matOneValue m3 [[u, u, u], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]] := by decide +kernel
example : pencilRead (dataA 3) square 32 3 carrier.sqIx3 1 (pencilE [0, 32, 32])
    g3 m3 (inertia.mkSplit 3 g3)
    [(m3, inertia.mkSplit 3 (inertia.siteDatum c3 m3),
      inertia.mkSplit 3 (matAdd c3 m3))] := by decide +kernel

/-! The adjoint loop over three letters at its own index: the unit
against the loop reads one, the contraction at six wirings per
link. -/

private def ixT3 : List (List places.Shape) := [List.replicate 4 (adjchar.theta 3)]

example : entryAt (dataA 3) square ixT3 1 (inertia.idMat 2)
    (loopMag (dataA 3) [adjchar.theta 3]) sqPlaq 0 1 = true := by decide +kernel

/-! The theta window over two letters at cutoff twenty-six: the two
plaquette loops, the hexagon and the join — the adjoint on the
shared link with the fundamental on the six further links, one
member at each trivalent vertex — at the gram diagonal with the
join's block twelve, the two terms decided at the contraction: the
loops' own entries one, the join's own entry eight at either
plaquette, and its cross entry with the hexagon the balance
partner of two at both orders, the two sides' contractions one
value, the second plaquette's term at its reversed shared link,
the boundary wiring's slots exchanged there; the whole pencil
passes, and the join's own entry moved to nine, the cross entry's
side flipped and the gram's join block moved to eleven are each
refused at the entry conjunct. -/

private def gTh26 : Mat := ground.matOf 5 5 (fun i j =>
  if i == j then (if i == 4 then ⟨13, 1⟩ else ⟨2, 1⟩) else u)
private def mTh0 : Mat := ground.matOf 5 5 (fun i j =>
  if i == 3 && j == 3 then ⟨2, 1⟩
  else if (i == 2 && j == 4) || (i == 4 && j == 2) then ⟨1, 3⟩
  else if i == 4 && j == 4 then ⟨9, 1⟩ else u)
private def mTh1 : Mat := ground.matOf 5 5 (fun i j =>
  if i == 1 && j == 1 then ⟨2, 1⟩
  else if (i == 2 && j == 4) || (i == 4 && j == 2) then ⟨1, 3⟩
  else if i == 4 && j == 4 then ⟨9, 1⟩ else u)
private def thP0 : List (Nat × Bool) := ground.getAt [] thetaG.plaqs 0
private def thP1 : List (Nat × Bool) := ground.getAt [] thetaG.plaqs 1
private def thCap : Mat :=
  inertia.matScaleB (BPair.ofNat ((dataA 2).dim (dataA 2).theta)) gTh26

/-! The window's five splits at the adjoint dimension three as
stated data: the gram's own and, per plaquette, the upper split at
the site datum and the lower at the sum, each the cleared
congruence with its adjugate witness at normalized
representatives, the blocks and the kernel order (`lem:inertia`'s
certificate data, re-read by `splitRead` rather than re-run); the
pencil's reads then run one kernel task per split read and per
term conjunct, assembled at `termsRead`'s own clause over the
pinned plaquette list, the entry reads one task per position row
assembled at the range fold's one-step introduction; the dimension
read rewrites through the definition's own equation and the pinned
index before deciding, where a `show` at the fold makes the
elaborator enumerate the index itself. -/

private def thG : inertia.Split 5 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩,
    .one ⟨2, 1⟩,
    .one ⟨2, 1⟩,
    .one ⟨2, 1⟩,
    .one ⟨13, 1⟩],
   0, rfl⟩
private def thU0 : inertia.Split 5 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 5403406870691968357⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨8105110306037952535, 1⟩]], rfl⟩,
   ⟨[[⟨3140085798164163223281069127, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1046695266054721074427023043⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨38766491335360039793593447, 1⟩, ⟨1, 1⟩, ⟨25844327556906693195728965, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1969541804367222465763⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨387420490, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨5083731656659, 1⟩,
    .one ⟨1751808348614470202264689898742320564161, 1⟩],
   0, rfl⟩
private def thL0 : inertia.Split 5 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨10806813741383936713, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨16210220612075905069, 1⟩]], rfl⟩,
   ⟨[[⟨6280171596328326446562138253, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 2093390532109442148854046085⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨77532982670720079587186893, 1⟩, ⟨1, 1⟩, ⟨1, 51688655113813386391457929⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 3939083608734444931525⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨387420490, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨10167463313317, 1⟩,
    .one ⟨11211573431132609294494015351950851610625, 1⟩],
   0, rfl⟩
private def thU1 : inertia.Split 5 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨55, 1⟩, ⟨1, 1⟩, ⟨1, 210832519264920577⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 472393⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨316248778897380865, 1⟩]], rfl⟩,
   ⟨[[⟨24201729692064429659283457, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 8067243230688143219761153⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨448180179482674623320065, 1⟩, ⟨1, 1⟩, ⟨298786786321783082213377, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 51232302181375699969⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨76527505, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨19, 1⟩,
    .one ⟨8749, 1⟩,
    .one ⟨669462604993, 1⟩,
    .one ⟨2667021070775586348972287975290306561, 1⟩],
   0, rfl⟩
private def thL1 : inertia.Split 5 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨109, 1⟩, ⟨1, 1⟩, ⟨107946249863639334913, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 3779137⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨161919374795459002369, 1⟩]], rfl⟩,
   ⟨[[⟨198260569637391807768850071553, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 66086856545797269256283357185⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1835746015161035257118982145, 1⟩, ⟨1, 1⟩, ⟨1, 1223830676774023504745988097⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 52461877433728716767233⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1224440065, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨37, 1⟩,
    .one ⟨34993, 1⟩,
    .one ⟨42845606719489, 1⟩,
    .one ⟨1118629714523832492583986334391203396583425, 1⟩],
   0, rfl⟩
private def thTerms : List (Mat × inertia.Split 5 × inertia.Split 5) :=
  [(mTh0, thU0, thL0), (mTh1, thU1, thL1)]
private theorem thPlaqs : thetaG.plaqs = [thP0, thP1] := by decide +kernel
private theorem thCapSq : sqAt thCap 5 := by decide +kernel
private theorem thSym0 : symmRead mTh0 := by decide +kernel
private theorem thSq0 : sqAt mTh0 5 := by decide +kernel
private theorem thLe0 : inertia.leAt mTh0 thCap thU0 := by decide +kernel
private theorem thLo0 : inertia.splitRead (matAdd thCap mTh0) thL0 := by decide +kernel
private theorem thPsd0 : inertia.psdAt thL0 := by decide +kernel
private theorem thSupp0 : termSupport (dataA 2) thetaG 5 carrier.thIx26 thP0 mTh0 := by
  decide +kernel
private theorem thEnt0R0 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP0 0 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh0 thP0 0 j) = true := by
  decide +kernel
private theorem thEnt0R1 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP0 1 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh0 thP0 1 j) = true := by
  decide +kernel
private theorem thEnt0R2 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP0 2 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh0 thP0 2 j) = true := by
  decide +kernel
private theorem thEnt0R3 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP0 3 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh0 thP0 3 j) = true := by
  decide +kernel
private theorem thEnt0R4 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP0 4 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh0 thP0 4 j) = true := by
  decide +kernel
private theorem thEnt0 : entriesRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26 thP0 mTh0 :=
  (ground.all_range_succ_intro 4 (ground.all_range_succ_intro 3 (ground.all_range_succ_intro 2 (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl thEnt0R0) thEnt0R1) thEnt0R2) thEnt0R3) thEnt0R4)
private theorem thCapAt0 : inertia.capAt mTh0 thCap thU0 thL0 :=
  ⟨thSq0, thCapSq, thLe0, thLo0, thPsd0⟩
private theorem thSym1 : symmRead mTh1 := by decide +kernel
private theorem thSq1 : sqAt mTh1 5 := by decide +kernel
private theorem thLe1 : inertia.leAt mTh1 thCap thU1 := by decide +kernel
private theorem thLo1 : inertia.splitRead (matAdd thCap mTh1) thL1 := by decide +kernel
private theorem thPsd1 : inertia.psdAt thL1 := by decide +kernel
private theorem thSupp1 : termSupport (dataA 2) thetaG 5 carrier.thIx26 thP1 mTh1 := by
  decide +kernel
private theorem thEnt1R0 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP1 0 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh1 thP1 0 j) = true := by
  decide +kernel
private theorem thEnt1R1 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP1 1 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh1 thP1 1 j) = true := by
  decide +kernel
private theorem thEnt1R2 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP1 2 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh1 thP1 2 j) = true := by
  decide +kernel
private theorem thEnt1R3 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP1 3 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh1 thP1 3 j) = true := by
  decide +kernel
private theorem thEnt1R4 : (List.range 5).all (fun j =>
    !rowPair (dataA 2) thetaG carrier.thIx26 thP1 4 j
      || entryAt (dataA 2) thetaG carrier.thIx26 1 gTh26 mTh1 thP1 4 j) = true := by
  decide +kernel
private theorem thEnt1 : entriesRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26 thP1 mTh1 :=
  (ground.all_range_succ_intro 4 (ground.all_range_succ_intro 3 (ground.all_range_succ_intro 2 (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl thEnt1R0) thEnt1R1) thEnt1R2) thEnt1R3) thEnt1R4)
private theorem thCapAt1 : inertia.capAt mTh1 thCap thU1 thL1 :=
  ⟨thSq1, thCapSq, thLe1, thLo1, thPsd1⟩
private theorem thTermsRead :
    termsRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26 thetaG.plaqs thTerms := by
  rw [thPlaqs]
  exact ⟨thSym0, thCapAt0, thSupp0, thEnt0, thSym1, thCapAt1, thSupp1, thEnt1, trivial⟩
private theorem thGram : gramBlockRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26 := by
  decide +kernel
private theorem thSpG : inertia.splitRead gTh26 thG ∧ inertia.pdAt thG := by decide +kernel

example : slotDiag (dataA 2) thetaG carrier.thIx26 = [0, 12, 18, 12, 26] := by
  decide +kernel
private theorem thDim : windowfinite.dimSect (dataA 2) thetaG 26 = 5 := by
  rw [windowfinite.dimSect, carrier.thIx26_pin]
  decide +kernel
example : pencilRead (dataA 2) thetaG 26 5 carrier.thIx26 1
    (formE [0, 12, 18, 12, 26] gTh26) gTh26 (matAdd mTh0 mTh1) thG thTerms :=
  ⟨carrier.thIx26_pin, thDim, by decide +kernel, by decide +kernel, thGram,
   thSpG.1, thSpG.2, thTermsRead, by decide +kernel, by decide +kernel⟩

private def mTh0Flip : Mat := ground.matOf 5 5 (fun i j =>
  if (i == 2 && j == 4) || (i == 4 && j == 2) then ⟨3, 1⟩
  else ground.getAt u (ground.getAt [] mTh0 i) j)
private def gTh26Eleven : Mat := ground.matOf 5 5 (fun i j =>
  if i == 4 && j == 4 then ⟨12, 1⟩ else ground.getAt u (ground.getAt [] gTh26 i) j)
private def mTh0Join9 : Mat := ground.matOf 5 5 (fun i j =>
  if i == 4 && j == 4 then ⟨10, 1⟩ else ground.getAt u (ground.getAt [] mTh0 i) j)

example : ¬ entriesRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26 thP0 mTh0Join9
    ∧ ¬ entriesRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26 thP0 mTh0Flip
    ∧ ¬ entriesRead (dataA 2) thetaG 5 carrier.thIx26 1 gTh26Eleven thP0 mTh0
    ∧ symmRead mTh0Flip
    ∧ termSupport (dataA 2) thetaG 5 carrier.thIx26 thP0 mTh0Flip := by decide +kernel

/-! The gram and the support at a fiber of four slots: the theta
graph's all-adjoint member beside the first plaquette's fundamental
loop over three letters, six positions with the unit line.  The
gram's block read admits a pairing within the four-slot fiber and
refuses one across the two members. -/

private def fLoop : List places.Shape :=
  [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
private def ix6 : List (List places.Shape) := [thAll, fLoop]
private def e6 (i j : Nat) : Mat :=
  ground.matOf 6 6 (fun a b =>
    if (a == i && b == j) || (a == j && b == i) then ⟨2, 1⟩ else u)

example : (slotList (dataA 3) thetaG ix6).length = 5 := by decide +kernel

/-! The gram's block content at the four-slot fiber: the two
trivalent vertices' Grams `[[56, -16], [-16, 56]]` at the second
member three (`con:fiber`'s symbolic tag at three adjoints over
three letters, the check module for `con:fiber` its pin), the four
two-end vertices at the coevaluation's eight, and the seven links'
scale `[1 : 8]` each, so at the clearing `9 · 8` the block is the
Kronecker product of the vertex Grams at their own eighth,
`[[7, -2], [-2, 7]]`, the loop member's block the clearing itself; the identity gram is refused there, as
is the block at the clearing one, the block with the two members
coupled, and the block with one entry moved. -/

private def vg3 : Mat :=
  [[BPair.ofNat 56, (BPair.ofNat 16).swap], [(BPair.ofNat 16).swap, BPair.ofNat 56]]
private def kron2 (A B : Mat) : Mat :=
  ground.matOf 4 4 (fun i j =>
    ground.getAt u (ground.getAt [] A (i / 2)) (j / 2)
      * ground.getAt u (ground.getAt [] B (i % 2)) (j % 2))
private def vg7 : Mat :=
  [[BPair.ofNat 7, (BPair.ofNat 2).swap], [(BPair.ofNat 2).swap, BPair.ofNat 7]]
private def cTh : Pos := 72
private def gTh : Mat :=
  ground.matOf 6 6 (fun i j =>
    if i == 0 && j == 0 then BPair.ofPos cTh
    else if i == 5 && j == 5 then BPair.ofPos cTh
    else if 1 ≤ i && i ≤ 4 && 1 ≤ j && j ≤ 4 then
      ground.getAt u (ground.getAt [] (kron2 vg7 vg7) (i - 1)) (j - 1)
    else u)

example : fibGram (dataA 3) thetaG thAll
    = some [(vg3, 3), ([[BPair.ofNat 8]], 1), ([[BPair.ofNat 8]], 1), (vg3, 3),
        ([[BPair.ofNat 8]], 1), ([[BPair.ofNat 8]], 1)]
    ∧ blockScale (dataA 3) thetaG thAll = 2097152 := by decide +kernel
example : gramBlockRead (dataA 3) thetaG 6 ix6 cTh gTh := by decide +kernel
example : ¬ gramBlockRead (dataA 3) thetaG 6 ix6 cTh (inertia.idMat 6)
    ∧ ¬ gramBlockRead (dataA 3) thetaG 6 ix6 1 gTh
    ∧ ¬ gramBlockRead (dataA 3) thetaG 6 ix6 cTh (matAdd gTh (e6 1 5))
    ∧ ¬ gramBlockRead (dataA 3) thetaG 6 ix6 cTh (matAdd gTh (e6 1 2)) := by
  decide +kernel
example : inertia.pdAt (inertia.mkSplit 6 gTh) := by decide +kernel

example : ¬ inertia.capAt (inertia.matScaleB (BPair.ofNat 4) mSq) cSq
    (inertia.mkSplit 3 (inertia.siteDatum cSq
      (inertia.matScaleB (BPair.ofNat 4) mSq)))
    (inertia.mkSplit 3 (matAdd cSq
      (inertia.matScaleB (BPair.ofNat 4) mSq))) := by
  decide +kernel
example : ¬ (windowfinite.dimSect (dataA 2) square 32 = 2) := by
  decide +kernel
